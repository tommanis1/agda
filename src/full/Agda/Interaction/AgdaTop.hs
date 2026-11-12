{-# OPTIONS_GHC -Wunused-imports #-}

module Agda.Interaction.AgdaTop
    ( repl
    , relocateSources
    ) where

import Control.Monad                ( unless )
import Control.Monad.IO.Class       ( MonadIO(..) )
import Control.Monad.State          ( evalStateT, runStateT )
import Control.Monad.Trans          ( lift )

import Data.Char
import Data.Functor ((<&>))
import qualified Data.List as List
import qualified Data.Map as Map
import Data.Text (Text)
import qualified Data.Text as T

import System.IO

import Agda.Interaction.Base
import Agda.Interaction.ExitCode
import Agda.Interaction.Response as R
import Agda.Interaction.InteractionTop
import Agda.Interaction.Options
import Agda.Interaction.Command ( CommandM )

import Agda.TypeChecking.Monad
import qualified Agda.TypeChecking.Monad.Benchmark as Bench

import Agda.Utils.FileId (getIdFile)
import Agda.Utils.FileName (filePath)

----------------------------------

-- | 'repl' is a fake ghci interpreter for both the Emacs the JSON frontend
repl :: InteractionOutputCallback -> String -> TCM () -> TCM ()
repl callback prompt setup = do
    liftIO $ do
      hSetBuffering stdout LineBuffering
      hSetBuffering stdin  LineBuffering
      hSetEncoding  stdout utf8
      hSetEncoding  stdin  utf8

    setInteractionOutputCallback callback

    commands <- liftIO $ initialiseCommandQueue readCommand

    handleCommand_ (lift setup) `evalStateT` initCommandState commands

    opts <- commandLineOptions
    _ <- interact' `runStateT`
           (initCommandState commands)
             { optionsOnReload = opts{ optAbsoluteIncludePaths = [] } }
    return ()
  where
  interact' :: CommandM ()
  interact' = do
    Bench.reset
    done <- Bench.billTo [] $ do

      liftIO $ do
        putStr prompt
        hFlush stdout
      r <- maybeAbort runInteraction
      case r of
        Done      -> return True -- Done.
        Command _ -> return False
        Error s   -> do
          exit <- optExitOnError <$> commandLineOptions
          if exit
            then liftIO (exitAgdaWith CommandError)
            else do
              liftIO (putStrLn s)
              return False

    lift Bench.print
    unless done interact'

  -- Reads the next command from stdin.

  readCommand :: IO Command
  readCommand = do
    done <- isEOF
    if done then
      return Done
    else do
      r <- getLine
      _ <- return $! length r     -- force to read the full input line
      case dropWhile isSpace r of
        ""          -> readCommand
        ('-':'-':_) -> readCommand
        _           -> case parseIOTCM r of
          Right cmd -> return $ Command cmd
          Left err  -> return $ Error err


-- | With @--keep-modules-by-content@ a module that was decoded under earlier include paths is used again under
--   the current ones, and the ranges in it still name the file it was decoded for. This gives, if the process
--   has used other include paths before, the function that replaces in a frontend's output every such path
--   by the path of the same module under the current include paths. The two files have the same contents (the
--   module is only used again if the hashes agree), so line and column stay right.
--
--   Paths are recognised as written by Agda: components separated by @/@, no escaping. A path that a frontend
--   writes with escapes (a quote or backslash in a directory name) is left as it is.
relocateSources :: TCM (Maybe (Text -> Text))
relocateSources = do
  earlier <- useSession lensEarlierSources
  if Map.null earlier then pure Nothing else do
    current <- useSession lensModuleToSourceId
    dict    <- useSession lensFileDict
    let
      now m = Map.lookup m current <&> \ (SourceFile i) -> T.pack (filePath (getIdFile dict i))

      -- The text is cut at every "/". A source path ends inside a piece, after the file name; the pieces
      -- before it are the directories. @before@ holds the pieces of the input so far and @out@ the pieces
      -- of the output so far, both last first.
      go _ out [] = T.intercalate "/" (reverse out)
      go before out (p : ps) = case [ (new, rest, length dirs)
                                    | (file, rest) <- fileNames p
                                    , (dirs, m)    <- maybe [] Map.toList (Map.lookup file earlier)
                                    , dirs `List.isPrefixOf` before
                                    , length dirs < length before   -- the piece that ends in the leading "/"
                                    , Just new     <- [now m]
                                    ] of
        (new, rest, n) : _ | n <= length out, Just new' <- T.stripPrefix "/" new ->
          go (p : before) ((new' <> rest) : drop n out) ps
        _ -> go (p : before) (p : out) ps

      -- The ways to read the start of a piece as the name of an Agda source file, longest first, each with
      -- what follows the name.
      fileNames p =
        [ (T.take n p, T.drop n p)
        | n <- reverse $ List.nub
            [ n
            | (pre, _) <- T.breakOnAll "agda" p
            , let k = T.length pre + 4
            , let ext = T.takeWhile isAlpha (T.drop (k + 1) p)
            , n <- k : [ k + 1 + T.length ext | T.take 1 (T.drop k p) == ".", not (T.null ext) ]
            ]
        ]
    pure $ Just \ s -> case T.splitOn "/" s of
      p : ps -> go [p] [p] ps
      []     -> s
