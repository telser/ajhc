
-- | similar to GenUtil but can rely on non-haskell 98 features
module Util.Gen(module Util.Gen, module GenUtil, intercalate) where

import Control.Monad.Writer
import Data.List
import Data.Maybe
import System.Directory
import Control.Applicative
import Text.ParserCombinators.ReadP

import GenUtil hiding(replicateM, intercalate)

mconcatMap f xs = mconcat (fmap f xs)
mintercalate x xs = mconcat (intersperse x xs)

mconcatMapM f xs = mapM f xs >>= pure . mconcat

runReadP :: Monad m => ReadP a -> String -> m a
runReadP rp s = case [ x | (x,t) <- readP_to_S rp s, ("","") <- lex t] of
    [x] -> pure x
    []  -> fail "runReadP: no parse"
    _   -> fail "runReadP: ambiguous parse"

runEither :: String -> Either String a -> a
runEither msg (Left fm) = error $ msg <> " - " <> fm
runEither _ (Right a) = a

travCollect :: Monoid w => ((a -> Writer w a) -> a -> Writer w a) -> (a -> w) -> a -> w
travCollect fn col x = execWriter (f x) where
    f x = tell (col x) >> fn f x

forMn_ xs = forM_ (zip xs [0 :: Int .. ])
forMn xs = forM (zip xs [0 :: Int .. ])

shortenPath :: String -> IO String
shortenPath x@('/':_) = do
    cd <- getCurrentDirectory
    pwd <- lookupEnv "PWD"
    h <- getHomeDirectory
    let f d = do
            '/':rest <- getPrefix d x
            pure rest
    pure . fromMaybe x $ f cd <|> (>>=f) pwd <|> fmap ("~/" ++) (f h)
shortenPath x = pure x

maybeDo :: Monad m => Maybe (m a) -> m ()
maybeDo = maybe (pure ()) (>> pure ())
