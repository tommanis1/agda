{-# OPTIONS_GHC -Wunused-imports #-}

-- | Interface for compiler backend writers.
module Agda.Compiler.Backend
  ( module Agda.Compiler.Backend.Base
  , Recompile(..), IsMain(..)
  , Flag
  , toTreeless
  , module Agda.Syntax.Treeless
  , module Agda.TypeChecking.Monad
  , module CheckResult
    -- For Agda.Main
  , backendInteraction
  , libraryInteraction
  , parseBackendOptions
    -- For InteractionTop
  , callBackend
  , callBackendInteractTop
  , callBackendInteractHole
  ) where

import Prelude hiding (null)

import Control.DeepSeq
import Control.Monad.IO.Class ( liftIO )

import Data.IORef
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set

import Agda.Utils.GetOpt

import Agda.Compiler.Backend.Base
import Agda.Compiler.Common
import Agda.Compiler.ToTreeless

import Agda.Interaction.Options
import Agda.Interaction.FindFile
import Agda.Interaction.Imports as CheckResult (CheckResult(CheckResult), crInterface, crWarnings, crMode)
import qualified Agda.Interaction.Imports as Imp

import Agda.Syntax.Common (BackendName)
import Agda.Syntax.TopLevelModuleName (projectRoot)
import Agda.Syntax.Treeless

import Agda.TypeChecking.Errors (getAllWarnings)
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Warnings

import Agda.Utils.CallStack (HasCallStack)
import Agda.Utils.FileName
import Agda.Utils.IndexedList
import Agda.Utils.List
import Agda.Utils.Monad
import Agda.Utils.Null
import Agda.Utils.Maybe
import Agda.Syntax.Common (InteractionId)
import Agda.Syntax.Position (Range)

import Agda.Interaction.Command (CommandM)

-- Public interface -------------------------------------------------------

-- | Call the 'compilerMain' function of the given backend.
callBackend :: BackendName -> IsMain -> CheckResult -> TCM ()
callBackend name iMain checkResult =
  withKnownBackend name $ \(Backend b) ->
    compilerMain b iMain checkResult

-- | Call the 'backendInteractTop' function of the given backend.
callBackendInteractTop :: BackendName -> String -> CommandM ()
callBackendInteractTop name cmd =
  withKnownBackend name $ \(Backend b) ->
    whenJust (backendInteractTop b) \bi ->
      bi cmd

-- | Call the 'backendInteractHole' function of the given backend.
callBackendInteractHole ::
  BackendName -> String -> InteractionId -> Range -> String -> CommandM ()
callBackendInteractHole name cmd ii rng s =
  withKnownBackend name $ \(Backend b) ->
    whenJust (backendInteractHole b) \bi ->
      bi cmd ii rng s

-- | Run a monadic action given an existing backend.
-- Throws an error if the user requested an unknown backend.
withKnownBackend ::
  (MonadTCError m) => BackendName -> (Backend -> m ()) -> m ()
withKnownBackend name k = ifJustM (lookupBackend name) k $ do
  backends <- useSession lensBackends
  let backendSet = otherBackends ++! [ backendName b | Backend b <- backends ]
  typeError $ UnknownBackend name (Set.fromList backendSet)

-- | Backends that are not included in the state, but still available
--   to the user.
otherBackends :: [BackendName]
otherBackends = ["GHCNoMain", "QuickLaTeX"]

-- Internals --------------------------------------------------------------

data BackendWithOpts opts where
  BackendWithOpts ::
    NFData opts =>
    Backend' opts env menv mod def ->
    BackendWithOpts opts

backendWithOpts :: Backend -> Some BackendWithOpts
backendWithOpts (Backend backend) = Some (BackendWithOpts backend)

forgetOpts :: BackendWithOpts opts -> Backend
forgetOpts (BackendWithOpts backend) = Backend backend

bOptions :: Lens' (BackendWithOpts opts) opts
bOptions f (BackendWithOpts b) = f (options b) <&> \ opts -> BackendWithOpts b{ options = opts }

embedFlag :: Lens' b a -> Flag a -> Flag b
embedFlag l flag = l flag

embedOpt :: Lens' b a -> OptDescr (Flag a) -> OptDescr (Flag b)
embedOpt l = fmap (embedFlag l)

parseBackendOptions :: [Backend] -> [String] -> CommandLineOptions -> OptM ([Backend], CommandLineOptions)
parseBackendOptions backends argv opts0 =
  case makeAll backendWithOpts backends of
    Some bs -> do
      let agdaFlags    = map' (embedOpt _2) (deadStandardOptions ++! standardOptions)
          backendFlags = do
            Some i            <- forgetAll Some $ allIndices bs
            BackendWithOpts b <- [lookupIndex bs i]
            opt               <- commandLineFlags b
            return $ embedOpt (_1 . lIndex i . bOptions) opt
      (backends, opts) <- getOptSimple (stripRTS argv)
                                       (agdaFlags ++! backendFlags) (embedFlag _2 . inputFlag)
                                       (bs, opts0)
      opts <- checkOpts opts
      return (forgetAll forgetOpts backends, opts)

backendInteraction :: AbsolutePath -> [Backend] -> TCM () -> (AbsolutePath -> TCM CheckResult) -> TCM ()
backendInteraction mainFile backends setup check = do
  setup
  whileChecking <- optCompileWhileChecking <$> commandLineOptions
  -- The compilers to run after the check: with --compile-while-checking, prepared now, the modules the check
  -- compiles left out.
  compilers <- if whileChecking
    then do
      src <- Imp.parseSource =<< srcFromPath mainFile
      compileWhileChecking backends . filePath . projectRoot mainFile =<< pure (Imp.srcModuleName src)
    else pure [ CompileAfter backend Nothing | Backend backend <- backends ]
  checkResult <- check mainFile

  -- reset warnings
  stTCWarnings `setTCLens` empty

  noMain <- optCompileNoMain <$> pragmaOptions
  let isMain | noMain    = NotMain
             | otherwise = IsMain

  sequence_ [ compilerMainAfter backend before isMain checkResult | CompileAfter backend before <- compilers ]

  -- print warnings that might have accumulated during compilation
  ws <- filter (not . isUnsolvedWarning . tcWarning) . Set.toAscList <$> getAllWarnings AllWarnings
  unless (null ws) $ alwaysReportSDoc "warning" 1 $
    -- Andreas, 2024-09-06 start warning list by a newline
    -- since type checker warnings are also newline separated.
    -- See e.g. test/Succeed/CompileBuiltinListWarning.warn.
    -- Also separate warnings by newlines (issue #6919).
    vcat $ concatMap (\ w -> [ "", prettyTCM w ]) ws


compilerMain :: Backend' opts env menv mod def -> IsMain -> CheckResult -> TCM ()
compilerMain backend = compilerMainAfter backend Nothing

-- | 'compilerMain' after a check that compiled some modules already: given the backend's environment they were
-- compiled in and their results, only the rest of the graph is compiled, and 'postCompile' gets all of them.
compilerMainAfter :: Backend' opts env menv mod def -> Maybe (env, IORef (CompiledSoFar mod)) -> IsMain -> CheckResult -> TCM ()
compilerMainAfter backend before isMain0 checkResult = inCompilerEnv checkResult $ do
  locallyTC eActiveBackendName (const $ Just $ backendName backend) $ do
    -- BEWARE: Do not use @optOnlyScopeChecking@ here; it does not authoritatively describe the type-checking mode!
    -- InteractionTop currently may invoke type-checking with scope checking regardless of that flag.
    when (not (scopeCheckingSuffices backend) && crMode checkResult == ModuleScopeChecked) $
      typeError $ BackendDoesNotSupportOnlyScopeChecking $ backendName backend

    !i <- instantiateFull $ crInterface checkResult
    -- Andreas, 2017-08-23, issue #2714
    -- If the backend is invoked from Emacs, we can only get the --no-main
    -- pragma option now, coming from the interface file.
    !isMain <- ifM (optCompileNoMain <$> pragmaOptions)
      {-then-} (return NotMain)
      {-else-} (return isMain0)

    (env, CompiledSoFar done doneNames) <- case before of
      Nothing          -> (, CompiledSoFar Map.empty Set.empty) <$> preCompile backend (options backend)
      Just (env, made) -> (env ,) <$> liftIO (readIORef made)
    mods <- (done <>) <$> doCompileAfter doneNames
        -- This inner function is called for both `Agda.Primitive` and the module in question,
        -- and all (distinct) imported modules. So avoid shadowing "isMain" or "i".
        (\ifaceIsMain iface ->
          Map.singleton (iTopLevelModuleName iface) <$>
          compileModule backend env ifaceIsMain iface)
        isMain i
    -- Note that `doCompile` calls `setInterface` for each distinct module in the graph prior to calling into
    -- `compileModule`. This last one is just to ensure it's reset to _this_ module.
    setInterface i
    postCompile backend env isMain mods

compileModule :: HasCallStack => Backend' opts env menv mod def -> env -> IsMain -> Interface -> TCM mod
compileModule backend env isMain i = do
  mName <- curMName
  -- The interface file will only exist if performing af full type-check, vs scoping.
  -- FIXME: Expecting backends to read the timestamp of the output path of the interface
  --        file for dirtiness checking is very roundabout and heavily couples backend
  --        implementations to the filesystem as the source of cache state.
  mifile <- (Just . filePath . intFilePath =<<) <$> findInterfaceFile mName
  r      <- preModule backend env isMain (iTopLevelModuleName i) mifile
  case r of
    Skip m         -> return m
    Recompile menv -> do
      defs <- map' snd . sortDefs <$> curDefs
      res  <- mapM (compileDef' backend env menv isMain) defs
      postModule backend env menv isMain (iTopLevelModuleName i) res

compileDef' :: Backend' opts env menv mod def -> env -> menv -> IsMain -> Definition -> TCM def
compileDef' backend env menv isMain def =
  setCurrentRange (defName def) $
    compileDef backend env menv isMain def

-- Compiling while checking ----------------------------------------------

-- | The modules a backend has compiled while they were checked: each one's result, and their names, which
-- 'doCompileAfter' leaves out.
data CompiledSoFar mod = CompiledSoFar (Map TopLevelModuleName mod) (Set ModuleName)

-- | A backend to run after the check, with the environment and results of what it compiled during it, if
-- anything.
data CompileAfter where
  CompileAfter :: Backend' opts env menv mod def -> Maybe (env, IORef (CompiledSoFar mod)) -> CompileAfter

-- | Prepare the backends to compile each module right after it is checked (@--compile-while-checking@): run their
-- 'preCompile' now, and set the hook that a parallel worker runs on its module before the module counts as done
-- ('Agda.Interaction.Imports.chaseModule'). So a module is compiled after its imports, as 'doCompile' orders them,
-- and in parallel with the modules it is independent of. The output directory is the one given, unless
-- @--compile-dir@ is.
compileWhileChecking :: [Backend] -> FilePath -> TCM [CompileAfter]
compileWhileChecking backends root = do
  dir <- fromMaybe root . optCompileDir <$> commandLineOptions
  compilers <- forM backends \ (Backend backend) -> do
    env  <- inCompileDir dir $ preCompile backend (options backend)
    made <- liftIO $ newIORef $ CompiledSoFar Map.empty Set.empty
    pure (CompileAfter backend (Just (env, made)), compileChecked backend env made dir)
  setSession lensModuleChecked $ Just \ mi -> mapM_ (($ mi) . snd) compilers
  pure $ map fst compilers

-- | Compile a module that has just been checked, in its worker's state, and record the result. The warnings
-- compiling it gives are printed here, since the worker's state does not outlive it.
compileChecked :: Backend' opts env menv mod def -> env -> IORef (CompiledSoFar mod) -> FilePath -> ModuleInfo -> TCM ()
compileChecked backend env made dir mi = do
  let i = miInterface mi
  -- The hook runs in the worker of a module's importer, under the environment of the import's scope checking (its
  -- opaque block, abstract mode, context). The post-check pass compiles in the top-level environment with abstract
  -- and opaque ignored ('inCompilerEnv'), so we do too: otherwise a backend reads the module's own opaque or abstract
  -- definitions as 'AbstractDefn' (agda2hs panicked on an extended lambda inside an opaque block).
  (r, ws) <- inCompileDir dir $ localTC (const initEnv) $ ignoreAbstractMode $
             locallyTC eActiveBackendName (const $ Just $ backendName backend) do
    stTCWarnings `setTCLens` empty
    setInterface i
    r  <- compileModule backend env NotMain i
    ws <- filter (not . isUnsolvedWarning . tcWarning) . Set.toAscList <$> getAllWarnings AllWarnings
    pure (r, ws)
  unless (null ws) $ alwaysReportSDoc "warning" 1 $ vcat $ concatMap (\ w -> [ "", prettyTCM w ]) ws
  liftIO $ atomicModifyIORef' made \ (CompiledSoFar m names) ->
    (CompiledSoFar (Map.insert (iTopLevelModuleName i) r m) (Set.insert (iModuleName i) names), ())

-- | Run an action with the output directory set, in a state it does not change.
inCompileDir :: FilePath -> TCM a -> TCM a
inCompileDir dir act = localTCState do
  opts <- getsTC $ stPersistentOptions . stPersistentState
  setCommandLineOptions opts { optCompileDir = Just dir }
  act

-- | @--build-library@ with backends: the library's modules are compiled as they are checked
-- (@--compile-while-checking@, which this requires), into @--compile-dir@ or the library's root, and each backend's
-- 'postCompile' runs once on all of them.
libraryInteraction :: [Backend] -> FilePath -> TCM () -> TCM ()
libraryInteraction backends root build = do
  compilers <- compileWhileChecking backends root
  build
  forM_ compilers \ (CompileAfter backend before) -> forM_ before \ (env, made) -> do
    CompiledSoFar mods _ <- liftIO $ readIORef made
    dir <- fromMaybe root . optCompileDir <$> commandLineOptions
    inCompileDir dir $ locallyTC eActiveBackendName (const $ Just $ backendName backend) $
      postCompile backend env NotMain mods
