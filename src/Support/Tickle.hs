module Support.Tickle where

import Control.Monad.Identity
import Control.Monad.Writer

class Tickleable a b where
    tickleM :: Monad m => (a -> m a) -> b -> m b
    tickleM_ :: Monad m => (a -> m c) -> b -> m ()
    tickle :: (a -> a) -> b -> b

    tickle f x = runIdentity $ tickleM (pure . f) x
    tickleM_ f b = tickleM (\x -> f x >> pure x) b >> pure ()

tickleCollect :: (Tickleable a b, Monoid o) => (a -> o) -> b -> o
tickleCollect f b = execWriter (tickleM_ (tell . f) b)
