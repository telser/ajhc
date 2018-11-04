module FrontEnd.Syn.Traverse where

import Control.Monad.Writer
import qualified Data.Set as Set
import qualified Data.Traversable as T

import FrontEnd.HsSyn
import FrontEnd.SrcLoc
import Name.Name
import Support.FreeVars

--instance FreeVars HsType (Set.Set HsName) where
--    freeVars t = execWriter (f t) where
--        f (HsTyVar v) = tell (Set.singleton v)
--        f t = traverseHsType_ f t

instance FreeVars HsType (Set.Set Name) where
    freeVars t = execWriter (f t) where
        f (HsTyVar v) = tell (Set.singleton $ toName TypeVal v)
        f (HsTyCon v) = tell (Set.singleton $ toName TypeConstructor v)
        f t = traverseHsType_ f t

traverse_ :: Monad m => (a -> m b) -> a -> m a
traverse_ fn x = fn x >> pure x

traverseHsExp_ :: MonadSetSrcLoc m => (HsExp -> m ()) -> HsExp -> m ()
traverseHsExp_ fn e = traverseHsExp (traverse_ fn) e >> pure ()

traverseHsExp :: MonadSetSrcLoc m => (HsExp -> m HsExp) -> HsExp -> m HsExp
traverseHsExp fn e = f e where
    fns = mapM fn
    f e@HsVar {} = pure e
    f e@HsCon {} = pure e
    f e@HsLit {} = pure e
    f e@HsError {} = pure e
    f (HsInfixApp hsExp1 hsExp2 hsExp3) = do
        hsExp1' <- fn hsExp1
        hsExp2' <- fn hsExp2
        hsExp3' <- fn hsExp3
        pure (HsInfixApp hsExp1' hsExp2' hsExp3')
    f (HsApp hsExp1 hsExp2)  = do
        hsExp1' <- fn hsExp1
        hsExp2' <- fn hsExp2
        pure (HsApp hsExp1' hsExp2')
    f (HsNegApp hsExp)  = do
        hsExp' <- fn hsExp
        pure (HsNegApp hsExp')
    f (HsLambda srcLoc hsPats hsExp) = withSrcLoc srcLoc $ do
        hsExp' <- fn hsExp
        pure (HsLambda srcLoc hsPats hsExp')
    f (HsIf hsExp1 hsExp2 hsExp3)  = do
        hsExp1' <- fn hsExp1
        hsExp2' <- fn hsExp2
        hsExp3' <- fn hsExp3
        pure (HsIf hsExp1' hsExp2' hsExp3')
    f (HsTuple hsExps)  = do
        hsExps' <- fns hsExps
        pure (HsTuple hsExps')
    f (HsUnboxedTuple hsExps)  = do
        hsExps' <- fns hsExps
        pure (HsUnboxedTuple hsExps')
    f (HsList hsExps)  = do
        hsExps' <- fns hsExps
        pure (HsList hsExps')
    f (HsParen hsExp)  = do
        hsExp' <- fn hsExp
        pure (HsParen hsExp')
    f (HsLeftSection hsExp1 hsExp2)  = do
        hsExp1' <- fn hsExp1
        hsExp2' <- fn hsExp2
        pure (HsLeftSection hsExp1' hsExp2')
    f (HsRightSection hsExp1 hsExp2)  = do
        hsExp1' <- fn hsExp1
        hsExp2' <- fn hsExp2
        pure (HsRightSection hsExp1' hsExp2')
    f (HsEnumFrom hsExp)  = do
        hsExp' <- fn hsExp
        pure (HsEnumFrom hsExp')
    f (HsEnumFromTo hsExp1 hsExp2)  = do
        hsExp1' <- fn hsExp1
        hsExp2' <- fn hsExp2
        pure (HsEnumFromTo hsExp1' hsExp2')
    f (HsEnumFromThen hsExp1 hsExp2)  = do
        hsExp1' <- fn hsExp1
        hsExp2' <- fn hsExp2
        pure (HsEnumFromThen hsExp1' hsExp2')
    f (HsEnumFromThenTo hsExp1 hsExp2 hsExp3)  = do
        hsExp1' <- fn hsExp1
        hsExp2' <- fn hsExp2
        hsExp3' <- fn hsExp3
        pure (HsEnumFromThenTo hsExp1' hsExp2' hsExp3')
    f (HsExpTypeSig srcLoc hsExp hsQualType)  = withSrcLoc srcLoc $ do
        hsExp' <- fn hsExp
        pure (HsExpTypeSig srcLoc hsExp' hsQualType)
    f (HsAsPat hsName hsExp)  = do
        hsExp' <- fn hsExp
        pure (HsAsPat hsName hsExp')
    f (HsWildCard x) = do pure (HsWildCard x)
    f (HsIrrPat hsExp)  = do
        hsExp' <- fnl hsExp
        pure (HsIrrPat hsExp')
    f (HsBangPat hsExp)  = do
        hsExp' <- fnl hsExp
        pure (HsBangPat hsExp')
    f (HsRecConstr n fus) = do
        fus' <- mapM fFieldUpdate fus
        pure $ HsRecConstr n fus'
    f (HsRecUpdate e fus) = do
        fus' <- mapM fFieldUpdate fus
        e' <- fn e
        pure $ HsRecUpdate e' fus'
    f (HsLocatedExp le) = HsLocatedExp `liftM` fnl le
    f (HsLet hsDecls hsExp)  = do
        ds <- mapM (traverseHsDeclHsExp fn) hsDecls
        e <- fn hsExp
        pure $ HsLet ds e
    f (HsDo hsStmts)  = HsDo `liftM` mapM (traverseHsStmtHsExp fn) hsStmts
    f _ = error "FrontEnd.Syn.Traverse.traverseHsExp f unrecognized construct"
    fFieldUpdate (HsFieldUpdate n e) = do
        e' <- fn e
        pure $ HsFieldUpdate n e'
    fnl (Located l e) = withSrcSpan l $ Located l `liftM` fn e

    {-
-- not done
    f (HsRecUpdate hsExp hsFieldUpdates)  = do
        hsExp' <- fn hsExp
        hsFieldUpdates' <- renameHsFieldUpdates hsFieldUpdates
        pure (HsRecUpdate hsExp' hsFieldUpdates')
    fn (HsRecConstr hsName hsFieldUpdates)  = do
        hsName' <- renameHsName hsName   -- do I need to change this name?
        hsFieldUpdates' <- renameHsFieldUpdates hsFieldUpdates
        pure (HsRecConstr hsName' hsFieldUpdates')
--    fn (HsCase hsExp hsAlts)  = do
--        hsExp' <- fn hsExp
--        hsAlts' <- renameHsAlts hsAlts
--        pure (HsCase hsExp' hsAlts')
--    fn (HsDo hsStmts)  = do
--        let e = doToExp hsStmts
--        fn e
        --(hsStmts',_) <- renameHsStmts hsStmts
        --pure (doToExp hsStmts')
    fn (HsListComp hsExp hsStmts)  = do
        (hsStmts',') <- renameHsStmts hsStmts
        hsExp' <- fn hsExp '
        pure (HsListComp hsExp' hsStmts')
    fn (HsLet hsDecls hsExp)  = do
        ' <- updateSubTableWithHsDecls  hsDecls LetFun
        hsDecls' <- renameHsDecls hsDecls '
        hsExp' <- fn hsExp '
        pure (HsLet hsDecls' hsExp')

-}

traverseHsType_ :: Monad m => (HsType -> m b) -> HsType -> m ()
traverseHsType_ fn p = traverseHsType (traverse_ fn) p >> pure ()

traverseHsType :: Monad m => (HsType -> m HsType) -> HsType -> m HsType
traverseHsType f (HsTyFun a b) = pure HsTyFun `ap` f a `ap` f b
traverseHsType f (HsTyTuple xs) = do
    xs <- mapM f xs
    pure $ HsTyTuple xs
traverseHsType f (HsTyUnboxedTuple xs) = do
    xs <- mapM f xs
    pure $ HsTyUnboxedTuple xs
traverseHsType f (HsTyApp a b) = pure HsTyApp `ap` f a `ap` f b
traverseHsType f (HsTyForall vs qt) = doQual HsTyForall f vs qt
traverseHsType f (HsTyExists vs qt) = doQual HsTyExists f vs qt
traverseHsType _ x@HsTyVar {} = pure x
traverseHsType _ x@HsTyCon {} = pure x
traverseHsType f HsTyExpKind { .. } = do
    hsTyLType <- T.mapM f hsTyLType
    pure HsTyExpKind { .. }
traverseHsType f (HsTyEq a b) = pure HsTyEq `ap` f a `ap` f b
traverseHsType f (HsTyStrictType a b ) = pure HsTyStrictType `ap` pure a `ap` T.mapM f b
traverseHsType _ HsTyAssoc = pure HsTyAssoc

doQual :: Monad m => (a -> HsQualType -> b) -> (HsType -> m HsType) -> a -> HsQualType -> m b
doQual hsTyForall f vs qt = do
    x <- f $ hsQualTypeType qt
    cntx <- flip mapM (hsQualTypeContext qt) $ \v -> case v of
        x@HsAsst {} -> pure x
        HsAsstEq a b -> pure HsAsstEq `ap` f a `ap` f b
    pure $ hsTyForall vs qt { hsQualTypeContext = cntx, hsQualTypeType = x }

traverseHsPat_ :: MonadSetSrcLoc m => (HsPat -> m b) -> HsPat -> m ()
traverseHsPat_ fn p = traverseHsPat (traverse_ fn) p >> pure ()

traverseHsPat :: MonadSetSrcLoc m => (HsPat -> m HsPat) -> HsPat -> m HsPat
traverseHsPat fn p = f p where
    f p@HsPVar {} = pure p
    f p@HsPLit {} = pure p
    f (HsPNeg hsPat)  = do
          hsPat' <- fn hsPat
          pure (HsPNeg hsPat')
    f (HsPInfixApp hsPat1 hsName hsPat2)  = do
          hsPat1' <- fn hsPat1
          hsPat2' <- fn hsPat2
          pure (HsPInfixApp hsPat1' hsName hsPat2')
    f (HsPApp hsName hsPats)  = do
          hsPats' <- mapM fn hsPats
          pure (HsPApp hsName hsPats')
    f (HsPTuple hsPats)  = do
          hsPats' <- mapM fn hsPats
          pure (HsPTuple hsPats')
    f (HsPUnboxedTuple hsPats)  = do
          hsPats' <- mapM fn hsPats
          pure (HsPUnboxedTuple hsPats')
    f (HsPList hsPats)  = do
          hsPats' <- mapM fn hsPats
          pure (HsPList hsPats')
    f (HsPParen hsPat)  = do
          hsPat' <- fn hsPat
          pure (HsPParen hsPat')
    f (HsPAsPat hsName hsPat)  = do
          hsPat' <- fn hsPat
          pure (HsPAsPat hsName hsPat')
    f HsPWildCard  = do pure HsPWildCard
    f (HsPIrrPat hsPat)  = do
          hsPat' <- fnl hsPat
          pure (HsPIrrPat hsPat')
    f (HsPBangPat hsPat)  = do
          hsPat' <- fnl hsPat
          pure (HsPBangPat hsPat')
    f (HsPTypeSig srcLoc hsPat qt) = withSrcLoc srcLoc $ do
          hsPat' <- fn hsPat
          pure (HsPTypeSig srcLoc hsPat' qt)
    f (HsPRec hsName hsPatFields)  = do
          hsPatFields' <- mapM fField hsPatFields
          pure (HsPRec hsName hsPatFields')
    fField (HsPFieldPat n p) = fn p >>= pure . HsPFieldPat n
    fnl (Located l e) = withSrcSpan l (Located l `liftM` fn e)

traverseHsRhsHsExp :: MonadSetSrcLoc m => (HsExp -> m HsExp) -> HsRhs -> m HsRhs
traverseHsRhsHsExp fn d = f d where
    f (HsUnGuardedRhs e) = fn e >>= pure . HsUnGuardedRhs
    f (HsGuardedRhss rs) = pure HsGuardedRhss `ap` mapM g rs
    g (HsGuardedRhs sl e1 e2) = pure (HsGuardedRhs sl) `ap` fn e1 `ap` fn e2

traverseHsStmtHsExp :: MonadSetSrcLoc m => (HsExp -> m HsExp) -> HsStmt -> m HsStmt
traverseHsStmtHsExp fn d = f d where
    f (HsGenerator sl p e) = withSrcLoc sl $ HsGenerator sl p `liftM` fn e
    f (HsQualifier e) = HsQualifier `liftM` fn e
    f (HsLetStmt ds) = HsLetStmt `liftM` mapM (traverseHsDeclHsExp fn) ds

traverseHsDeclHsExp :: MonadSetSrcLoc m => (HsExp -> m HsExp) -> HsDecl -> m HsDecl
traverseHsDeclHsExp fn d = f d where
    f (HsPatBind srcLoc hsPat hsRhs {-where-} hsDecls) = withSrcLoc srcLoc $ do
        hsDecls'  <- mapM (traverseHsDeclHsExp fn) hsDecls
        hsRhs'    <- traverseHsRhsHsExp fn hsRhs
        pure (HsPatBind srcLoc hsPat hsRhs' {-where-} hsDecls')
    f (HsActionDecl sl p e) = withSrcLoc sl $ do
        e <- fn e
        pure $ HsActionDecl sl p e
--    f (HsFunBind hsMatches)  = do
--        hsMatches'     <- mapM (traverseHsMatchHsExp fn) hsMatches
--        pure (HsFunBind hsMatches')
    f (HsClassDecl srcLoc hsQualType hsDecls)  = withSrcLoc srcLoc $ do
        hsDecls'  <- mapM (traverseHsDeclHsExp fn) hsDecls
        pure (HsClassDecl srcLoc hsQualType hsDecls')
    f decl@(HsClassAliasDecl { hsDeclSrcLoc = sl})  = withSrcLoc sl $ do
        hsDecls'  <- mapM (traverseHsDeclHsExp fn) (hsDeclDecls decl)
        pure (decl { hsDeclDecls = hsDecls' })
    f (HsInstDecl srcLoc hsQualType hsDecls)  = withSrcLoc srcLoc $ do
        hsDecls'  <- mapM (traverseHsDeclHsExp fn) hsDecls
        pure (HsInstDecl srcLoc hsQualType hsDecls')
--    f prules@HsPragmaRules { hsDeclSrcLoc = srcLoc, hsDeclFreeVars = fvs, hsDeclLeftExpr = e1, hsDeclRightExpr = e2 }  = withSrcLoc srcLoc $ do
--        fvs' <- sequence [ fmapM (`renameHsType` ) t  >>= pure . (,) n | (n,t) <- fvs]
--        e1' <- renameHsExp e1
--        e2' <- renameHsExp e2
--        pure prules {  hsDeclFreeVars = fvs', hsDeclLeftExpr = e1', hsDeclRightExpr = e2' }
    f otherHsDecl = pure otherHsDecl

getNamesFromHsPat :: HsPat -> [HsName]
getNamesFromHsPat p = execWriter (getNamesFromPat p) where
    getNamesFromPat (HsPVar hsName) = tell [toName Val hsName]
    getNamesFromPat (HsPAsPat hsName hsPat) = do
        tell [toName Val hsName]
        getNamesFromPat hsPat
    getNamesFromPat p = traverseHsPat_ getNamesFromPat p
