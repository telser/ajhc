module Grin.Optimize(grinPush,grinSpeculate) where

import Control.Monad.State
import Data.List
import qualified Data.Set as Set

import C.Prims
import Grin.Grin
import Grin.Noodle
import Options (verbose)
import Stats hiding(null,isEmpty)
import StringTable.Atom
import Support.CanType
import Support.FreeVars
import Util.GMap
import Util.Graph
import Util.HasSize
import Util.SetLike

data PExp = PExp {
    pexpUniq :: Int,
    pexpBind :: [Val],
    pexpExp  :: Exp,
    pexpProvides :: [Var],
    pexpDeps :: [Int]
    } deriving(Show)

instance Eq PExp where
    a == b = pexpUniq a == pexpUniq b

makeDeps :: [PExp] -> PExp -> PExp
makeDeps cs pexp = pexp { pexpProvides = freeVars (pexpBind pexp), pexpDeps = deps } where
    deps = [ pexpUniq c | c <- cs, not $ null $ fvs `intersect` pexpProvides c ]
    fvs = freeVars (pexpExp pexp)

justDeps :: [PExp] -> [Var] -> [Int]
justDeps cs fs = deps where
    deps = [ pexpUniq c | c <- cs, not $ null $ fs `intersect` pexpProvides c ]

-- | grinPush pushes the definitions of variables as far inward as they can go so
-- peephole optimizations have a better chance of firing. when the order of definitons
-- doesn't matter, it uses heuristics to decide which one to push to allow the most
-- peephole optimizations.

grinPush :: Stats -> Lam -> IO Lam
grinPush stats (l :-> e) = ans where
    ans = do
--        putStrLn "@@@ grinPush"
        e' <- evalStateT (f e) (1,[])
        pure (l :-> e')
    f (exp :>>= v :-> e2) | isOmittable exp = do
        (nn,cv) <- get
        let npexp = makeDeps cv PExp { pexpUniq = nn, pexpBind = v, pexpExp = exp, pexpDeps = undefined, pexpProvides = undefined }
        put (nn+1,npexp:cv)
        f e2
    f (exp :>>= v :-> e2) = do
        exp <- fixupLet exp
        (v',exp') <- dropAny (Just v) exp
        e2' <- f e2
        pure $ exp' :>>= v' :-> e2'
    f exp = do
        exp <- fixupLet exp
        (_,exp') <- dropAny Nothing exp
        pure exp'

    fixupLet lt@Let { expDefs = defs, expBody = b } = do
        let def = (fromList $ map funcDefName defs :: GSet Atom)
            f (e :>>= l :-> r) | isEmpty (freeVars e `intersection` def) = do
                exp <- f r
                pure (e :>>= l :-> exp)
            f r = pure $ updateLetProps lt {  expBody = r }
        f b
    fixupLet exp = pure exp
    dropAny mv (exp::Exp) = do
        (nn,xs) <- get
        let (reachable',_graph) = newGraphReachable xs pexpUniq pexpDeps
            deps = justDeps xs (freeVars exp)
            reached = reachable' deps
            --dropped = case prefered reached exp of
            --    Just (x:_) | [] <- [ r | r <- reached, pexpUniq x `elem` pexpDeps r ] -> (reverse $ topSort $ newGraph (filter (/= x) reached) pexpUniq pexpDeps) ++ [x]
            --    _ -> reverse $ topSort $ newGraph reached pexpUniq pexpDeps
            dropped =  reverse $ topSort $ newGraph reached pexpUniq pexpDeps
            ff pexp exp = pexpExp pexp :>>= pexpBind pexp :-> exp
            ebinds = [ Var v t | (v,t) <- Set.toList $ freeVars (map pexpBind dropped) ]
            (exp',mv') | Just vv <- mv = let mv' = vv ++ ebinds in (exp :>>= vv :-> Return mv',mv')
                       | otherwise = (exp,[])
        put (nn,[ x | x <- xs, pexpUniq x `notElem` (map pexpUniq reached) ])
--        when (not $ null dropped) $ lift $ do
--            putStrLn "@@@ dropped"
--            mapM_ Prelude.print dropped
        pure (mv',foldr ff exp' dropped :: Exp)
    -- | preferentially pull definitons of the variable this returns right next to it as it admits a peephole optimization
--    prefer (Store v@Var {}) = pure v
--    prefer (App fn [v@Var {}] _)  | fn == funcEval = pure v
--    prefer (App fn [v@Var {},_] _)| fn == funcApply = pure v
--    prefer (App fn [v@Var {}] _)  | fn == funcApply = pure v
--    prefer (Update _ v@Var {}) = pure v
--    prefer (Update v@Var {} _) = pure v
--    prefer _ = fail "no preference"
--    _prefered pexps exp = do
--        v <- prefer exp
--        pure [ p | p <- pexps, v == pexpBind p]

--grinPush :: Stats -> Lam -> IO Lam
--grinPush stats lam = ans where
--    ans = do
--        putStrLn "@@@ grinPush"
--        (ans,_) <- evalStateT (whiz subBlock doexp finalExp whizState lam) (1,[])
--        pure ans
--    subBlock _ action = do
--        (nn,x) <- get
--        put (nn,mempty)
--        r <- action
--        (nn,_) <- get
--        put (nn,x)
--        pure r
--    doexp (v, exp) | isOmittable exp = do
--        (nn,cv) <- get
--        let npexp = makeDeps cv PExp { pexpUniq = nn, pexpBind = v, pexpExp = exp, pexpDeps = undefined, pexpProvides = undefined }
--        put (nn+1,npexp:cv)
--        pure Nothing
--    doexp (v, exp) = do
--        exp <- fixupLet exp
--        (v',exp') <- dropAny (Just v) exp
--        pure $ Just (v',exp')
--    finalExp (exp::Exp) = do
--        exp <- fixupLet exp
--        (_,exp') <- dropAny Nothing exp
--        pure (exp'::Exp)
--    fixupLet lt@Let { expDefs = defs, expBody = b } = do
--        let def = (Set.fromList $ map funcDefName defs)
--            f (e :>>= l :-> r) | Set.null (freeVars e `Set.intersection` def) = do
--                exp <- f r
--                pure (e :>>= l :-> exp)
--            f r = pure $ updateLetProps lt {  expBody = r }
--        f b
--    fixupLet exp = pure exp
--    dropAny mv (exp::Exp) = do
--        (nn,xs) <- get
--        let graph = newGraph xs pexpUniq pexpDeps
--            deps = justDeps xs (freeVars exp)
--            reached = reachable graph deps
--            --dropped = case prefered reached exp of
--            --    Just (x:_) | [] <- [ r | r <- reached, pexpUniq x `elem` pexpDeps r ] -> (reverse $ topSort $ newGraph (filter (/= x) reached) pexpUniq pexpDeps) ++ [x]
--            --    _ -> reverse $ topSort $ newGraph reached pexpUniq pexpDeps
--            dropped =  reverse $ topSort $ newGraph reached pexpUniq pexpDeps
--            ff pexp exp = pexpExp pexp :>>= pexpBind pexp :-> exp
--            ebinds = [ Var v t | (v,t) <- Set.toList $ freeVars (map pexpBind dropped) ]
--            (exp',mv') | Just vv <- mv = let mv' = tuple $ fromTuple vv ++ ebinds in (exp :>>= vv :-> Return mv',mv')
--                       | otherwise = (exp,unit)
--        put (nn,[ x | x <- xs, pexpUniq x `notElem` (map pexpUniq reached) ])
--        when (not $ null dropped) $ lift $ do
--            putStrLn "@@@ dropped"
--            mapM_ Prelude.print dropped
--        pure (mv',foldr ff exp' dropped :: Exp)
--    -- | preferentially pull definitons of the variable this returns right next to it as it admits a peephole optimization
--    prefer (Store v@Var {}) = pure v
--    prefer (App fn [v@Var {}] _)  | fn == funcEval = pure v
--    prefer (App fn [v@Var {},_] _)| fn == funcApply = pure v
--    prefer (App fn [v@Var {}] _)  | fn == funcApply = pure v
--    prefer (Update _ v@Var {}) = pure v
--    prefer (Update v@Var {} _) = pure v
--    prefer _ = fail "no preference"
--    prefered pexps exp = do
--        v <- prefer exp
--        pure [ p | p <- pexps, v == pexpBind p]

grinSpeculate :: Grin -> IO Grin
grinSpeculate grin = do
    let ss = findSpeculatable grin
    when verbose $ putStrLn "Speculatable:"
    when verbose $ mapM_ Prelude.print ss
    let (grin',stats) = runStatM (performSpeculate ss grin)
    when verbose $ Stats.printStat "Speculate" stats
    pure grin'

performSpeculate specs grin = do
    let sset = fromList (map tagFlipFunction specs) :: GSet Tag
    let f (a,l) = mapBodyM h l  >>= \l' -> pure (a,l')
        h (BaseOp (StoreNode False) [NodeC t xs]) | t `member` sset = do
            let t' = tagFlipFunction t
            mtick $ "Optimize.speculate.store.{" ++ show t'
            pure (App t' xs [TyNode] :>>= [n1] :-> demote n1)
        h e = mapExpExp h e
    fs <- mapM f (grinFuncs grin)
    pure $ setGrinFunctions fs grin

findSpeculatable :: Grin -> [Atom]
findSpeculatable grin = ans where
    ans = [ x | Left (x,_) <- scc graph ]
    graph = newGraph [ (a,concatMap f ((freeVars l) :: [Atom])) | (a,_ :-> l) <- grinFuncs grin, isSpeculatable l, getType l == [TyNode] ] fst snd
    f t | tagIsSuspFunction t = [tagFlipFunction t]
        | tagIsFunction t = [t]
        | otherwise = []
    isSpeculatable Return {} = True
    isSpeculatable (BaseOp (StoreNode _) _) = True
    isSpeculatable (BaseOp Promote _) = True
    isSpeculatable (BaseOp Demote _) = True
    isSpeculatable (x :>>= _ :-> y) = isSpeculatable x && isSpeculatable y
    isSpeculatable (Case e as) = all isSpeculatable [ e | _ :-> e <- as]
    isSpeculatable Prim { expPrimitive = p } = primIsConstant p
    isSpeculatable _ = False

demote x = BaseOp Demote [x]
