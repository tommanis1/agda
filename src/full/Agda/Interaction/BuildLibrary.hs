-- | Type-check all files of a library (option @--build-library@).

module Agda.Interaction.BuildLibrary (buildLibrary, printAccumulatedWarnings) where

import           Control.Monad.Except             (throwError)
import           Control.Monad.IO.Class           (liftIO)

import           Data.Functor                     (void)
import           Data.List                        (sort)
import qualified Data.Set as Set

import           System.Directory                 (getCurrentDirectory)
import qualified System.FilePath.Find             as Find
import           System.FilePath                  ((</>))

import           Agda.Interaction.FindFile        (hasAgdaExtension, checkModuleName)
import           Agda.Interaction.Imports         (TCWorkers, Source, MainInterface(..))
import qualified Agda.Interaction.Imports         as Imp
import           Agda.Interaction.Library         (pattern AgdaLibFile, _libIncludes, _libPragmas, getAgdaLibFile)
import           Agda.Interaction.Options         (optOnlyScopeChecking, optBuildModules)

import           Agda.Syntax.Abstract.Name        (noModuleName)
import           Agda.Syntax.Position             (beginningOfFile)

import           Agda.TypeChecking.Monad
import           Agda.TypeChecking.Pretty         (prettyTCM, text, vsep)
import           Agda.TypeChecking.Pretty.Warning (getAllWarnings, tcWarningsToError)
import           Agda.TypeChecking.Warnings       (pattern AllWarnings, classifyWarnings)

import           Agda.Utils.FileName              (absolute)
import           Agda.Utils.Functor               ()
import           Agda.Utils.IO.Directory          (findWithInfo)
import           Agda.Utils.Monad                 (forM, forM_, unless, bracket_)
import           Agda.Utils.Null                  (unlessNullM)
import           Agda.Utils.String                (delimiter, trim)

import           Agda.Utils.Impossible            (__IMPOSSIBLE__)

-- | Find @.agda-lib@ file from current directory
--   and build all modules located in the @include@ paths
--   and their subdirectories of the library.
--
buildLibrary :: TCM ()
buildLibrary = do
  cwd <- liftIO getCurrentDirectory

  -- Read the library file.
  ls <- libToTCM $ getAgdaLibFile cwd
  libFile@AgdaLibFile{ _libIncludes = paths
                     , _libPragmas  = libOpts } <- case ls of
    [l] -> pure l
    []  -> throwError $ GenericException "No library found to build"
    _   -> __IMPOSSIBLE__

  checkAndSetOptionsFromPragma libOpts

  -- Import the primitive modules
  Imp.importPrimitiveModules

  -- The modules to build: those --build-modules lists (relative to the library root), else all modules in the
  -- include paths of the library.
  files <- optBuildModules <$> commandLineOptions >>= \case
    Just list -> liftIO $ sort . map (cwd </>) . filter (\ l -> not (null l) && take 1 l /= "#") . map trim . lines
                   <$> readFile list
    Nothing   -> sort . map Find.infoPath . concat <$> forM paths \ path -> do
      liftIO $ findWithInfo (pure True) (hasAgdaExtension <$> Find.filePath) path

  -- Call the type-checker on all these modules.
  -- (Code copied from Agda.Main.)

  opts <- commandLineOptions
  par <- Imp.wantsParallelChecking

  checks <- Imp.spawningRoots par $ forM files \ inputFile -> do

      path :: AbsolutePath
        <- liftIO (absolute inputFile)
      sf :: SourceFile
        <- srcFromPath path

      -- András, 2026-08-19: issue 8627: for some reason, checking
      -- primitive modules in the following throws coinfectivity error,
      -- but since they're already checked by importPrimitiveModules,
      -- there's no point checking them anyway.
      isBuiltinModule (srcFileId sf) >>= \case
        Just b | isPrimitiveModule b ->
          pure $ pure ()
        _ -> do
          src :: Source
            <- Imp.parseSource sf
          let
            m :: TopLevelModuleName
            m = Imp.srcModuleName src
          setCurrentRange (beginningOfFile path) do
            checkModuleName m (Imp.srcOrigin src) Nothing
            withCurrentModule noModuleName
                 $ withTopLevelModule m
                 $ checkModule par m src

  sequence_ checks
  printAccumulatedWarnings

printAccumulatedWarnings :: TCM ()
printAccumulatedWarnings = do
  unlessNullM (tcWarnings . classifyWarnings . Set.toAscList <$> getAllWarnings AllWarnings) $ \ ws -> do
    let banner = text $ "\n" ++ delimiter "All done; warnings encountered"
    alwaysReportSDoc "warning" 1 $
      vsep $ (banner :) $ map prettyTCM $ Set.toAscList ws

postCheckModule :: TopLevelModuleName -> Source -> ModuleInfo -> TCM ()
postCheckModule m src mi = do
  -- Here we ignore InfectiveImport warnings since we don't have an actual parent module that can
  -- be infected.
  let
    isInfectiveWarning InfectiveImport{} = True
    isInfectiveWarning _                 = False
    warns = filter (not . isInfectiveWarning . tcWarning) $ Set.toAscList $ miWarnings mi
  tcWarningsToError (TopLevelModuleNameWithSourceFile m (Imp.srcOrigin src)) warns

checkModule :: Maybe TCWorkers -> TopLevelModuleName -> Source -> TCM (TCM ())
checkModule (Just w) m src = bracket_ (useTC stPragmaOptions) (stPragmaOptions `setTCLens`) do
  Imp.setOptionsFromSourcePragmas True src
  mip <- Imp.chaseModule w m NotMainInterface (Just src)
  -- kept until this thread has collected it below (--evict-interfaces would release a finished root at once)
  Imp.holdRoot w m
  pure do
    -- waiting puts the module's decoded imports in this state; it reads only the warnings, so it does not
    -- keep them (with --evict-interfaces they could not be dropped otherwise)
    before <- getDecodedModules
    mip >>= postCheckModule m src
    Imp.releaseRoot w m
    setDecodedModules before

checkModule Nothing m src = do
  mi <- Imp.getNonMainModuleInfo m (Just src)
  -- with --compile-while-checking the module and its imports were compiled as they were visited
  -- ('Imp.getInterface')
  postCheckModule m src mi
  pure $ pure ()
