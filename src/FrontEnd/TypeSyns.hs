module FrontEnd.TypeSyns( expandTypeSyns, expandTypeSynsStmt ) where

import Control.Monad.State
import Control.Monad.Writer
import Data.List
import qualified Data.Traversable as T

import FrontEnd.HsSyn
import FrontEnd.SrcLoc hiding(srcLoc)
import FrontEnd.Syn.Traverse
import FrontEnd.TypeSynonyms
import FrontEnd.Warning
import Name.Name

type SubTable = ()

-- the monadic state

data ScopeState = ScopeState {
    currentModule  :: Module,
    errors         :: [Warning],
    synonyms       :: TypeSynonyms,
    srcLoc         :: !SrcLoc
    }

-- The monadic type
type ScopeSM = State ScopeState

instance MonadWarn ScopeSM where
    addWarning w = modify (\s -> s { errors = w: errors s})

instance MonadSrcLoc ScopeSM where
    getSrcLoc = gets srcLoc
instance MonadSetSrcLoc ScopeSM where
    withSrcLoc sl a = modify (\s -> s { srcLoc = sl `mappend` srcLoc s}) >> a

expandTypeSyns :: MonadWarn m => TypeSynonyms -> HsModule -> m HsModule
expandTypeSyns syns m = ans where
    startState = ScopeState {
        errors         = [],
        synonyms       =  syns,
        srcLoc         = bogusASrcLoc,
        currentModule  = hsModuleName m
        }

    (rm, fs) = runState (renameDecls m) startState
    ans = do
        mapM_ addWarning (errors fs)
        pure rm

expandTypeSynsStmt :: MonadWarn m => TypeSynonyms -> Module -> HsStmt -> m HsStmt
expandTypeSynsStmt syns mod m = ans where
    startState = ScopeState {
        errors         = [],
        synonyms       =  syns,
        srcLoc         = bogusASrcLoc,
        currentModule  = mod
        }

    (rm, fs) = runState (renameHsStmt m ()) startState
    ans = do
        mapM_ addWarning (errors fs)
        pure rm

-- This is Bryn's modification to make the code a bit easier to understand for
-- functions like renameHsNames, renameHsFileUpdates
mapRename :: (a -> SubTable -> ScopeSM a) -> [a] -> SubTable -> ScopeSM [a]
mapRename renameIndividual individuals subTable
    = mapM (`renameIndividual` subTable) individuals

renameDecls :: HsModule -> ScopeSM HsModule
renameDecls tidy = do
        decls' <- renameHsDecls (hsModuleDecls tidy) undefined
        pure tidy { hsModuleDecls = decls' }

renameHsDecls :: [HsDecl] -> SubTable -> ScopeSM ([HsDecl])
renameHsDecls decls subtable = do
    ans <- mapRename renameHsDecl (expandTypeSigs decls) subtable
    pure ans

expandTypeSigs :: [HsDecl] -> [HsDecl]
expandTypeSigs ds =  (concatMap f ds) where
    f (HsTypeSig sl ns qt) =  [ HsTypeSig sl [n] qt | n <- ns]
    f d = pure d

renameHsDecl :: HsDecl -> SubTable -> ScopeSM (HsDecl)
renameHsDecl (HsPatBind srcLoc hsPat hsRhs {-where-} hsDecls) subTable = withSrcLoc srcLoc $ do
    hsPat'    <- renameHsPat hsPat subTable
    hsDecls'  <- renameHsDecls hsDecls subTable
    hsRhs'    <- renameHsRhs hsRhs subTable
    let patbind' = (HsPatBind srcLoc hsPat' hsRhs' {-where-} hsDecls')
    pure patbind'

renameHsDecl (HsForeignDecl a b n t) subTable = withSrcLoc a $ do
    n <- renameHsName n subTable
    t <- renameHsQualType t subTable
    pure  (HsForeignDecl a b n t)

renameHsDecl (HsForeignExport a b n t) subTable = withSrcLoc a $ do
    n <- renameHsName n subTable
    t <- renameHsQualType t subTable
    pure  (HsForeignExport a b n t)

renameHsDecl (HsFunBind hsMatches) subTable = do
    hsMatches' <- renameHsMatches hsMatches subTable
    pure (HsFunBind hsMatches')

renameHsDecl (HsTypeSig srcLoc hsNames hsQualType) subTable = withSrcLoc srcLoc $ do
    hsNames' <- renameHsNames hsNames subTable
    hsQualType' <- renameHsQualType hsQualType subTable
    pure (HsTypeSig srcLoc hsNames' hsQualType')

renameHsDecl dl@HsDataDecl { hsDeclContext = hsContext, hsDeclCons = hsConDecls  } subTable = do
    hsContext' <- renameHsContext hsContext subTable
    hsConDecls' <- renameHsConDecls hsConDecls subTable
    pure dl { hsDeclContext = hsContext', hsDeclCons = hsConDecls' }
renameHsDecl (HsTypeDecl srcLoc name hsNames t) subTable = withSrcLoc srcLoc $ do
    hsName' <- renameTypeHsName name subTable
    t' <- renameHsType' False t undefined
    pure (HsTypeDecl srcLoc  hsName' hsNames t')
renameHsDecl decl@HsActionDecl { hsDeclSrcLoc = srcLoc, hsDeclExp = e }  subTable = withSrcLoc srcLoc $ do
    e <- renameHsExp e subTable
    pure decl { hsDeclExp = e }
renameHsDecl (HsClassDecl srcLoc hsQualType hsDecls) subTable = withSrcLoc srcLoc $ do
    hsQualType' <- renameHsClassHead hsQualType
    hsDecls' <- renameHsDecls hsDecls subTable
    pure (HsClassDecl srcLoc hsQualType' hsDecls')
renameHsDecl (HsInstDecl srcLoc hsQualType hsDecls) subTable = withSrcLoc srcLoc $ do
    hsQualType' <- renameHsClassHead hsQualType
    hsDecls' <- renameHsDecls hsDecls subTable
    pure (HsInstDecl srcLoc hsQualType' hsDecls')
renameHsDecl (HsInfixDecl srcLoc assoc int hsNames) subTable = withSrcLoc srcLoc $ do
    hsNames' <- renameHsNames hsNames subTable
    pure $ HsInfixDecl srcLoc assoc int hsNames'
renameHsDecl (HsPragmaRules rs) subTable = do
    rs' <- mapM (`renameHsRule` subTable) rs
    pure $ HsPragmaRules rs'
renameHsDecl prules@HsPragmaSpecialize { hsDeclSrcLoc = srcLoc, hsDeclName = n, hsDeclType = t } subTable = withSrcLoc srcLoc $ do
    t <- renameHsType t subTable
    pure prules {  hsDeclType = t }
renameHsDecl otherHsDecl _ = pure otherHsDecl

renameHsRule prules@HsRule { hsRuleSrcLoc = srcLoc, hsRuleFreeVars = fvs, hsRuleLeftExpr = e1, hsRuleRightExpr = e2 } subTable = withSrcLoc srcLoc $ do
    fvs' <- sequence [ T.mapM (`renameHsType` subTable) t  >>= pure . (,) n | (n,t) <- fvs]
    e1' <- renameHsExp e1 subTable
    e2' <- renameHsExp e2 subTable
    pure prules {  hsRuleFreeVars = fvs', hsRuleLeftExpr = e1', hsRuleRightExpr = e2' }

renameHsQualType :: HsQualType -> SubTable -> ScopeSM (HsQualType)
renameHsQualType (HsQualType hsContext hsType) subTable = do
      hsContext' <- renameHsContext hsContext subTable
      hsType' <- renameHsType hsType subTable
      pure (HsQualType hsContext' hsType')
renameHsClassHead :: HsClassHead -> ScopeSM (HsClassHead)
renameHsClassHead HsClassHead { .. }  = do
      hsClassHeadContext <- renameHsContext hsClassHeadContext ()
      hsClassHeadArgs <- mapM (flip renameHsType ()) hsClassHeadArgs
      pure HsClassHead { .. }

renameHsContext :: HsContext -> SubTable -> ScopeSM (HsContext)
renameHsContext = mapRename renameHsAsst

renameHsAsst :: HsAsst -> SubTable -> ScopeSM (HsAsst)
renameHsAsst (HsAsst hsName1  hsName2s) subTable = do
      hsName1' <- renameTypeHsName hsName1 subTable  -- for class names
      hsName2s' <- mapRename renameTypeHsName hsName2s subTable
      pure (HsAsst hsName1' hsName2s')
renameHsAsst (HsAsstEq t1 t2) subTable = do
      t1' <- renameHsType t1 subTable  -- for class names
      t2' <- renameHsType t2 subTable  -- for class names
      pure (HsAsstEq t1' t2')

renameHsConDecls :: [HsConDecl] -> SubTable -> ScopeSM ([HsConDecl])
renameHsConDecls = mapRename renameHsConDecl

renameHsConDecl :: HsConDecl -> SubTable -> ScopeSM (HsConDecl)
renameHsConDecl cd@(HsConDecl { hsConDeclSrcLoc = srcLoc, hsConDeclName = hsName, hsConDeclConArg = hsBangTypes }) subTable = withSrcLoc srcLoc $ do
    hsName' <- renameHsName hsName subTable
    hsBangTypes' <- renameHsBangTypes hsBangTypes subTable
    pure cd { hsConDeclName = hsName', hsConDeclConArg = hsBangTypes' }
renameHsConDecl cd@HsRecDecl { hsConDeclSrcLoc = srcLoc, hsConDeclName = hsName, hsConDeclRecArg = stuff} subTable = withSrcLoc srcLoc $ do
    hsName' <- renameHsName hsName subTable
    stuff' <- sequence [ do ns' <- mapRename renameHsName ns subTable; t' <- renameHsBangType t subTable; pure (ns',t')  |  (ns,t) <- stuff]
    pure cd { hsConDeclName = hsName', hsConDeclRecArg = stuff' }

renameHsBangTypes :: [HsBangType] -> SubTable -> ScopeSM ([HsBangType])
renameHsBangTypes = mapRename renameHsBangType

renameHsBangType :: HsBangType -> SubTable -> ScopeSM (HsBangType)
renameHsBangType (HsBangedTy hsType) subTable = do
    hsType' <- renameHsType hsType subTable
    pure (HsBangedTy hsType')
renameHsBangType (HsUnBangedTy hsType) subTable = do
    hsType' <- renameHsType hsType subTable
    pure (HsUnBangedTy hsType')

renameHsType = renameHsType' True

renameHsType' dovar t st = pp (rt t) where
    rt :: HsType -> ScopeSM HsType
    rt (HsTyFun hsType1 hsType2) = do
        hsType1' <- rt hsType1
        hsType2' <- rt hsType2
        pure (HsTyFun hsType1' hsType2')
    rt (HsTyTuple hsTypes) = do
        hsTypes' <- mapM rt hsTypes
        pure (HsTyTuple hsTypes')
    rt (HsTyUnboxedTuple hsTypes) = do
        hsTypes' <- mapM rt hsTypes
        pure (HsTyUnboxedTuple hsTypes')
    rt (HsTyApp hsType1 hsType2) = do
        hsType1' <- rt hsType1
        hsType2' <- rt hsType2
        pure (HsTyApp hsType1' hsType2')
    rt (HsTyVar hsName) | dovar = do
        hsName' <- renameTypeHsName hsName ()
        pure (HsTyVar hsName')
    rt (HsTyCon hsName) = do
        hsName' <- renameTypeHsName hsName  ()
        pure (HsTyCon hsName')
    rt (HsTyForall ts v) = do
        v <- renameHsQualType v  ()
        pure $ HsTyForall ts v
    rt (HsTyExists ts v) = do
        v <- renameHsQualType v  ()
        pure $ HsTyExists ts v
 --   rt (HsTyAssoc) = pure HsTyAssoc
--    rt (HsTyEq a b) = pure HsTyEq `ap` (flip rt a) `ap` (flip rt b)
 --   rt HsTyExpKind {} _subTable = error "cannot rename HsTyExpKind TypeSyns"
    rt ty = traverseHsType rt ty
    pp t | not dovar = t
    pp t = do
        t' <- t
        syns <- gets synonyms
        removeSynonymsFromType syns t'

renameHsMatches :: [HsMatch] -> SubTable -> ScopeSM [HsMatch]
renameHsMatches = mapRename renameHsMatch

-- note that for renameHsMatch, the 'wheres' dominate the 'pats'

renameHsMatch :: HsMatch -> SubTable -> ScopeSM HsMatch
renameHsMatch (HsMatch srcLoc hsName hsPats hsRhs {-where-} hsDecls) subTable = withSrcLoc srcLoc $ do
    hsName' <- renameHsName hsName subTable
    subTable' <- updateSubTableWithHsPats subTable hsPats srcLoc
    hsPats' <- renameHsPats hsPats subTable'
    subTable'' <- updateSubTableWithHsDecls subTable' hsDecls
    hsDecls' <- renameHsDecls hsDecls subTable''
    hsRhs' <- renameHsRhs hsRhs subTable''
    pure (HsMatch srcLoc hsName' hsPats' hsRhs' {-where-} hsDecls')

renameHsPats :: [HsPat] -> SubTable -> ScopeSM ([HsPat])
renameHsPats = mapRename renameHsPat

renameHsPat :: HsPat -> SubTable -> ScopeSM (HsPat)
renameHsPat (HsPTypeSig srcLoc hsPat qt) subTable = withSrcLoc srcLoc $ do
    hsQualType' <- renameHsQualType qt subTable
    hsPat' <- renameHsPat hsPat subTable
    pure (HsPTypeSig srcLoc hsPat' hsQualType')
renameHsPat p subTable = traverseHsPat (flip renameHsPat subTable) p

renameHsRhs :: HsRhs -> SubTable -> ScopeSM HsRhs
renameHsRhs (HsUnGuardedRhs hsExp) subTable = do
      hsExp' <- renameHsExp hsExp subTable
      pure (HsUnGuardedRhs hsExp')
renameHsRhs (HsGuardedRhss hsGuardedRhss) subTable = do
      hsGuardedRhss' <- renameHsGuardedRhsList hsGuardedRhss subTable
      pure (HsGuardedRhss hsGuardedRhss')

renameHsExp :: HsExp -> SubTable -> ScopeSM HsExp
renameHsExp (HsLambda srcLoc hsPats hsExp) subTable = withSrcLoc srcLoc $ do
    subTable' <- updateSubTableWithHsPats subTable hsPats srcLoc
    hsPats' <- renameHsPats hsPats subTable'
    hsExp' <- renameHsExp hsExp subTable'
    pure (HsLambda srcLoc hsPats' hsExp')
renameHsExp (HsLet hsDecls hsExp) subTable = do
    subTable' <- updateSubTableWithHsDecls subTable hsDecls
    hsDecls' <- renameHsDecls hsDecls subTable'
    hsExp' <- renameHsExp hsExp subTable'
    pure (HsLet hsDecls' hsExp')
renameHsExp (HsCase hsExp hsAlts) subTable = do
    hsExp' <- renameHsExp hsExp subTable
    hsAlts' <- renameHsAlts hsAlts subTable
    pure (HsCase hsExp' hsAlts')
renameHsExp (HsRecConstr hsName hsFieldUpdates) subTable = do
    hsName' <- renameHsName hsName subTable  -- do I need to change this name?
    hsFieldUpdates' <- renameHsFieldUpdates hsFieldUpdates subTable
    pure (HsRecConstr hsName' hsFieldUpdates')
renameHsExp (HsRecUpdate hsExp hsFieldUpdates) subTable = do
    hsExp' <- renameHsExp hsExp subTable
    hsFieldUpdates' <- renameHsFieldUpdates hsFieldUpdates subTable
    pure (HsRecUpdate hsExp' hsFieldUpdates')
renameHsExp (HsListComp hsExp hsStmts) subTable = do
    (hsStmts',subTable') <- renameHsStmts hsStmts subTable
    hsExp' <- renameHsExp hsExp subTable'
    pure (HsListComp hsExp' hsStmts')
renameHsExp (HsExpTypeSig srcLoc hsExp hsQualType) subTable = do
    hsExp' <- renameHsExp hsExp subTable
    subTable' <- updateSubTableWithHsQualType subTable hsQualType
    hsQualType' <- renameHsQualType hsQualType subTable'
    pure (HsExpTypeSig srcLoc hsExp' hsQualType')
renameHsExp e subTable = traverseHsExp (flip renameHsExp subTable) e

renameHsAlts :: [HsAlt] -> SubTable -> ScopeSM [HsAlt]
renameHsAlts = mapRename renameHsAlt

-- note for renameHsAlt, the 'wheres' dominate the 'pats'

renameHsAlt :: HsAlt -> SubTable -> ScopeSM (HsAlt)
renameHsAlt (HsAlt srcLoc hsPat hsGuardedAlts {-where-} hsDecls) subTable = withSrcLoc srcLoc $ do
    subTable' <- updateSubTableWithHsPats subTable [hsPat] srcLoc
    hsPat' <- renameHsPat hsPat subTable'
    subTable'' <- updateSubTableWithHsDecls subTable' hsDecls
    hsDecls' <- renameHsDecls hsDecls subTable''
    hsGuardedAlts' <- renameHsRhs hsGuardedAlts subTable''
    pure (HsAlt srcLoc hsPat' hsGuardedAlts' hsDecls')

renameHsGuardedRhsList :: [HsGuardedRhs] -> SubTable -> ScopeSM [HsGuardedRhs]
renameHsGuardedRhsList = mapRename renameHsGuardedRhs

renameHsGuardedRhs :: HsGuardedRhs -> SubTable -> ScopeSM HsGuardedRhs
renameHsGuardedRhs (HsGuardedRhs srcLoc hsExp1 hsExp2) subTable = withSrcLoc srcLoc $ do
    hsExp1' <- renameHsExp hsExp1 subTable
    hsExp2' <- renameHsExp hsExp2 subTable
    pure (HsGuardedRhs srcLoc hsExp1' hsExp2')

-- renameHsStmts is trickier than you would expect because
-- the statements are only in scope after they have been declared
-- and thus the subTable must be more carefully threaded through

-- the updated subTable is pureed at the end because it is needed by
-- the first section of a list comprehension.

renameHsStmts :: [HsStmt] -> SubTable -> ScopeSM (([HsStmt],SubTable))
renameHsStmts (hsStmt:hsStmts) subTable = do
      subTable' <- updateSubTableWithHsStmt subTable hsStmt
      hsStmt' <- renameHsStmt hsStmt subTable'
      (hsStmts',subTable'') <- renameHsStmts hsStmts subTable'
      pure ((hsStmt':hsStmts'),subTable'')
renameHsStmts [] subTable = do
      pure ([],subTable)

renameHsStmt :: HsStmt -> SubTable -> ScopeSM (HsStmt)
renameHsStmt (HsGenerator srcLoc hsPat hsExp) subTable = do
      hsExp' <- renameHsExp hsExp subTable
      hsPat' <- renameHsPat hsPat subTable
      pure (HsGenerator srcLoc hsPat' hsExp')
renameHsStmt (HsQualifier hsExp) subTable = do
      hsExp' <- renameHsExp hsExp subTable
      pure (HsQualifier hsExp')
renameHsStmt (HsLetStmt hsDecls) subTable = do
      hsDecls' <- renameHsDecls hsDecls subTable
      pure (HsLetStmt hsDecls')

renameHsFieldUpdates :: [HsFieldUpdate] -> SubTable -> ScopeSM ([HsFieldUpdate])
renameHsFieldUpdates = mapRename renameHsFieldUpdate

renameHsFieldUpdate :: HsFieldUpdate -> SubTable -> ScopeSM (HsFieldUpdate)
-- XXX I'm not 100% sure that this works
{-
renameHsFieldUpdate (HsFieldBind hsName) subTable
  = do
      hsName' <- renameHsName hsName subTable  -- do i need to rename this name?
      pure (HsFieldBind hsName')
-}
renameHsFieldUpdate (HsFieldUpdate hsName hsExp) subTable = do
    hsName' <- renameHsName hsName undefined
    hsExp' <- renameHsExp hsExp subTable
    pure (HsFieldUpdate hsName' hsExp')

renameHsNames :: [HsName] -> SubTable -> ScopeSM ([HsName])
renameHsNames ns _ = pure ns

-- This looks up a replacement name in the subtable.
-- Regardless of whether the name is found, if it's not qualified
-- it will be qualified with the current module's prefix.
renameHsName :: HsName -> SubTable -> ScopeSM (HsName)
renameHsName hsName _ = pure hsName

renameTypeHsName hsName subTable  =  pure hsName

---------------------------------------
-- utility functions

-- clobberHsName(s) is called by the updateSubTableWith* functions to
-- deal with newly declared identifiers

-- clobberHsName(s) adds new mappings to the SubTable.
-- If a name already appeared, it's mapping is altered to the new one.

-- clobberHsNamesAndUpdateIdentTable also adds a mapping from this
-- renamed name to its source location and binding type

clobberHsNamesAndUpdateIdentTable :: [(HsName,SrcLoc)] -> SubTable ->  ScopeSM (SubTable)
clobberHsNamesAndUpdateIdentTable ((hsName,srcLoc):hsNamesAndASrcLocs) subTable  = do
      subTable'  <- clobberHsName hsName subTable
      subTable'' <- clobberHsNamesAndUpdateIdentTable hsNamesAndASrcLocs subTable'
      pure (subTable'')
clobberHsNamesAndUpdateIdentTable [] subTable  = pure (subTable)

{-
clobberHsNameAndUpdateIdentTable :: HsName -> SrcLoc -> SubTable -> Binding -> ScopeSM (SubTable)
clobberHsNameAndUpdateIdentTable hsName srcLoc subTable binding
  = do
      unique <- getUnique
      currModule <- getCurrentModule
      let
        hsName'     = renameAndQualify hsName unique currModule
        subTable'   = addToFM (addToFM subTable hsName hsName') hsName' hsName'
      addToIdentTable hsName' (srcLoc, binding)
      incUnique
      pure (subTable')
-}

-- takes a list of names and a subtable. adds the associations
-- [name -> renamedName] to the table and pures it.
clobberHsNames :: [HsName] -> SubTable -> ScopeSM (SubTable)
clobberHsNames (hsName:hsNames) subTable
  = do
      subTable'  <- clobberHsName  hsName  subTable
      subTable'' <- clobberHsNames hsNames subTable'
      pure (subTable'')
clobberHsNames [] subTable
  = pure subTable

clobberHsName :: HsName -> SubTable -> ScopeSM (SubTable)
clobberHsName hsName subTable = pure subTable

--------------------------------------------------------
----This section of code updates the current SubTable to reflect the present scope

updateSubTableWithHsDecls :: SubTable -> [HsDecl] ->  ScopeSM (SubTable)
updateSubTableWithHsDecls subTable []  = pure subTable
updateSubTableWithHsDecls subTable (hsDecl:hsDecls) = do
    let hsNamesAndASrcLocs = getHsNamesAndASrcLocsFromHsDecl hsDecl
    subTable'  <- clobberHsNamesAndUpdateIdentTable hsNamesAndASrcLocs subTable
    subTable'' <- updateSubTableWithHsDecls subTable' hsDecls
    pure (subTable'')

updateSubTableWithHsPats :: SubTable -> [HsPat] -> SrcLoc -> ScopeSM (SubTable)
updateSubTableWithHsPats subTable (hsPat:hsPats) srcLoc  = do
    let hsNamesAndASrcLocs = zip (getNamesFromHsPat hsPat) (repeat srcLoc)
    subTable'  <- clobberHsNamesAndUpdateIdentTable hsNamesAndASrcLocs subTable
    subTable'' <- updateSubTableWithHsPats subTable' hsPats srcLoc
    pure subTable''
updateSubTableWithHsPats subTable [] _srcLoc = do pure (subTable)

-- Only one HsStmt should be added at a time because each new identifier is only valid
-- below the point at which it is defined

updateSubTableWithHsStmt :: SubTable -> HsStmt -> ScopeSM (SubTable)
updateSubTableWithHsStmt subTable hsStmt = do
    let hsNamesAndASrcLocs = getHsNamesAndASrcLocsFromHsStmt hsStmt
    subTable' <- clobberHsNamesAndUpdateIdentTable hsNamesAndASrcLocs subTable
    pure (subTable')

----------------------------------------------------------
-- the following updateSubTableWith* functions do not need to alter the identTable aswell
--

-- takes an HsQualType (a type signature) and adds the names of its variables
-- to the current subTable

updateSubTableWithHsQualType :: SubTable -> HsQualType -> ScopeSM (SubTable)
updateSubTableWithHsQualType subTable hsQualType = do
      let hsNames = nub $ getHsNamesFromHsQualType hsQualType
      subTable' <- clobberHsNames hsNames subTable
      pure (subTable')

getHsNamesAndASrcLocsFromHsDecl :: HsDecl -> [(HsName, SrcLoc)]
getHsNamesAndASrcLocsFromHsDecl (HsPatBind srcLoc (HsPVar hsName) _ _) = [(hsName, srcLoc)]
-- This will cause errors on code with PatBinds of the form (x,y) = blah...
-- and should be changed for a more general renamer (but is fine for thih)
getHsNamesAndASrcLocsFromHsDecl (HsPatBind sloc _ _ _)
  = error $ "non simple pattern binding found (sloc): " ++ show sloc
-- getHsNamesAndASrcLocsFromHsDecl (HsFunBind _ hsMatches)
getHsNamesAndASrcLocsFromHsDecl (HsFunBind hsMatches) = getHsNamesAndASrcLocsFromHsMatches hsMatches
getHsNamesAndASrcLocsFromHsDecl (HsForeignDecl a _ n _) = [(n,a)]
getHsNamesAndASrcLocsFromHsDecl _otherHsDecl = []

getHsNamesAndASrcLocsFromHsMatches :: [HsMatch] -> [(HsName, SrcLoc)]
getHsNamesAndASrcLocsFromHsMatches [] = []
getHsNamesAndASrcLocsFromHsMatches (hsMatch:_hsMatches) = getHsNamesAndASrcLocsFromHsMatch hsMatch

getHsNamesAndASrcLocsFromHsMatch :: HsMatch -> [(HsName, SrcLoc)]
getHsNamesAndASrcLocsFromHsMatch (HsMatch srcLoc hsName _ _ _)
  = [(hsName, srcLoc)]

getHsNamesAndASrcLocsFromHsStmt :: HsStmt -> [(HsName, SrcLoc)]
getHsNamesAndASrcLocsFromHsStmt (HsGenerator srcLoc hsPat _hsExp) = zip (getNamesFromHsPat hsPat) (repeat srcLoc)
getHsNamesAndASrcLocsFromHsStmt (HsQualifier _hsExp) = []
getHsNamesAndASrcLocsFromHsStmt (HsLetStmt hsDecls) = concat $ map getHsNamesAndASrcLocsFromHsDecl hsDecls

-- the getNew... functions are used only inside class declarations to avoid _re_ renaming things
-- that should be left as is.

getHsNamesFromHsQualType :: HsQualType -> [HsName]
getHsNamesFromHsQualType (HsQualType _hsContext hsType) = getHsNamesFromHsType hsType

getHsNamesFromHsType :: HsType -> [HsName]
getHsNamesFromHsType (HsTyFun hsType1 hsType2) = (getHsNamesFromHsType hsType1) ++ (getHsNamesFromHsType hsType2)
getHsNamesFromHsType (HsTyTuple hsTypes) = concat $ map getHsNamesFromHsType hsTypes
getHsNamesFromHsType (HsTyUnboxedTuple hsTypes) = concat $ map getHsNamesFromHsType hsTypes
getHsNamesFromHsType (HsTyApp hsType1 hsType2) = (getHsNamesFromHsType hsType1) ++ (getHsNamesFromHsType hsType2)
getHsNamesFromHsType (HsTyVar hsName) = [hsName]
getHsNamesFromHsType (HsTyForall vs qt) = getHsNamesFromHsQualType qt Data.List.\\ map hsTyVarBindName vs
getHsNamesFromHsType (HsTyExists vs qt) = getHsNamesFromHsQualType qt Data.List.\\ map hsTyVarBindName vs
getHsNamesFromHsType (HsTyCon _hsName) = [] -- don't rename the Constructors
getHsNamesFromHsType ty = execWriter $ traverseHsType_ f ty where
    f t = tell $ getHsNamesFromHsType t
