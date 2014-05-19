%
% (c) The University of Glasgow 2006
% (c) The GRASP/AQUA Project, Glasgow University, 1993-1998
%

This module defines interface types and binders

\begin{code}
module IfaceType (
        IfExtName, IfLclName,

        IfaceType(..), IfacePredType, IfaceKind, IfaceTyCon(..), IfaceCoercion(..),
        IfaceTyLit(..), IfaceTcArgs(..),
        IfaceContext, IfaceBndr(..), IfaceTvBndr, IfaceIdBndr,

        -- Conversion from Type -> IfaceType
        toIfaceType, toIfaceTypes, toIfaceKind,
        toIfaceContext, toIfaceBndr, toIfaceIdBndr,
        toIfaceTvBndrs, toIfaceTyCon, toIfaceTyCon_name,
        toIfaceTcArgs,

        -- Conversion from IfaceTcArgs -> IfaceType
        tcArgsIfaceTypes,

        -- Conversion from Coercion -> IfaceCoercion
        toIfaceCoercion,

        -- Printing
        pprIfaceType, pprParendIfaceType, pprIfaceContext, pprIfaceContextArr,
        pprIfaceIdBndr, pprIfaceTvBndr, pprIfaceTvBndrs,
        pprIfaceBndrs, pprIfaceTcArgs, pprParendIfaceTcArgs,
        tOP_PREC, tYCON_PREC, noParens, maybeParen, pprIfaceForAllPart,
        pprIfaceForAll, pprIfaceSigmaType, pprIfaceCoercion, pprParendIfaceCoercion,
        splitIfaceSigmaTy, pprIfaceTypeApp, pprUserIfaceForAll,

        suppressIfaceKinds,
        stripIfaceKindVars,
        stripKindArgs
    ) where

import Coercion
import DataCon ( dataConTyCon )
import TcType
import DynFlags
import TypeRep hiding( maybeParen )
import Kind ( isKind )
import Unique( hasKey )
import Util ( filterOut, lengthIs )
import TyCon hiding ( pprPromotionQuote )
import CoAxiom
import Id
import Var
import TysWiredIn
import TysPrim
import PrelNames( funTyConKey, ipClassName )
import Name
import BasicTypes
import Binary
import Outputable
import FastString
import UniqSet
\end{code}

%************************************************************************
%*                                                                      *
                Local (nested) binders
%*                                                                      *
%************************************************************************

\begin{code}
type IfLclName = FastString     -- A local name in iface syntax

type IfExtName = Name   -- An External or WiredIn Name can appear in IfaceSyn
                        -- (However Internal or System Names never should)

data IfaceBndr          -- Local (non-top-level) binders
  = IfaceIdBndr {-# UNPACK #-} !IfaceIdBndr
  | IfaceTvBndr {-# UNPACK #-} !IfaceTvBndr

type IfaceIdBndr  = (IfLclName, IfaceType)
type IfaceTvBndr  = (IfLclName, IfaceKind)

-------------------------------
type IfaceKind     = IfaceType

data IfaceType     -- A kind of universal type, used for types and kinds
  = IfaceTyVar    IfLclName               -- Type/coercion variable only, not tycon
  | IfaceAppTy    IfaceType IfaceType
  | IfaceFunTy    IfaceType IfaceType
  | IfaceDFunTy   IfaceType IfaceType
  | IfaceForAllTy IfaceTvBndr IfaceType
  | IfaceTyConApp IfaceTyCon IfaceTcArgs  -- Not necessarily saturated
                                          -- Includes newtypes, synonyms, tuples
  | IfaceLitTy IfaceTyLit

type IfacePredType = IfaceType
type IfaceContext = [IfacePredType]

data IfaceTyLit
  = IfaceNumTyLit Integer
  | IfaceStrTyLit FastString

-- We use a new list type because it'll be more compact
-- and faster to parse in interface files. Rather than two bytes
-- and two decisions (nil/cons, and type/kind) there'll just be one.
data IfaceTcArgs
  = ITC_Nil
  | ITC_Type IfaceType IfaceTcArgs
  | ITC_Kind IfaceKind IfaceTcArgs

-- Encodes type constructors, kind constructors,
-- coercion constructors, the lot.
-- We have to tag them in order to pretty print them
-- properly.
data IfaceTyCon
  = IfaceTc              { ifaceTyConName :: IfExtName }
  | IfacePromotedDataCon { ifaceTyConName :: IfExtName }
  | IfacePromotedTyCon   { ifaceTyConName :: IfExtName }

data IfaceCoercion
  = IfaceReflCo      Role IfaceType
  | IfaceFunCo       Role IfaceCoercion IfaceCoercion
  | IfaceTyConAppCo  Role IfaceTyCon [IfaceCoercion]
  | IfaceAppCo       IfaceCoercion IfaceCoercion
  | IfaceForAllCo    IfaceTvBndr IfaceCoercion
  | IfaceCoVarCo     IfLclName
  | IfaceAxiomInstCo IfExtName BranchIndex [IfaceCoercion]
  | IfaceUnivCo      Role IfaceType IfaceType
  | IfaceSymCo       IfaceCoercion
  | IfaceTransCo     IfaceCoercion IfaceCoercion
  | IfaceNthCo       Int IfaceCoercion
  | IfaceLRCo        LeftOrRight IfaceCoercion
  | IfaceInstCo      IfaceCoercion IfaceType
  | IfaceSubCo       IfaceCoercion
  | IfaceAxiomRuleCo IfLclName [IfaceType] [IfaceCoercion]
\end{code}

%************************************************************************
%*                                                                      *
                Functions over IFaceTypes
%*                                                                      *
%************************************************************************


\begin{code}
splitIfaceSigmaTy :: IfaceType -> ([IfaceTvBndr], [IfacePredType], IfaceType)
-- Mainly for printing purposes
splitIfaceSigmaTy ty
  = (tvs, theta, tau)
  where
    (tvs,   rho)   = split_foralls ty
    (theta, tau)   = split_rho rho

    split_foralls (IfaceForAllTy tv ty)
        = case split_foralls ty of { (tvs, rho) -> (tv:tvs, rho) }
    split_foralls rho = ([], rho)

    split_rho (IfaceDFunTy ty1 ty2)
        = case split_rho ty2 of { (ps, tau) -> (ty1:ps, tau) }
    split_rho tau = ([], tau)

suppressIfaceKinds :: DynFlags -> [IfaceTvBndr] -> [a] -> [a]
suppressIfaceKinds dflags tys xs
  | gopt Opt_PrintExplicitKinds dflags = xs
  | otherwise = suppress tys xs
    where
      suppress _       []      = []
      suppress []      a       = a
      suppress (k:ks) a@(_:xs)
        | isIfaceKindVar k = suppress ks xs
        | otherwise        = a

stripIfaceKindVars :: DynFlags -> [IfaceTvBndr] -> [IfaceTvBndr]
stripIfaceKindVars dflags tyvars
  | gopt Opt_PrintExplicitKinds dflags = tyvars
  | otherwise = filterOut isIfaceKindVar tyvars

isIfaceKindVar :: IfaceTvBndr -> Bool
isIfaceKindVar (_, IfaceTyConApp tc _)
  = ifaceTyConName tc == superKindTyConName
isIfaceKindVar _ = False

ifTyVarsOfType :: IfaceType -> UniqSet IfLclName
ifTyVarsOfType ty
  = case ty of
      IfaceTyVar v -> unitUniqSet v
      IfaceAppTy fun arg
        -> ifTyVarsOfType fun `unionUniqSets` ifTyVarsOfType arg
      IfaceFunTy arg res
        -> ifTyVarsOfType arg `unionUniqSets` ifTyVarsOfType res
      IfaceDFunTy arg res
        -> ifTyVarsOfType arg `unionUniqSets` ifTyVarsOfType res
      IfaceForAllTy (var,t) ty
        -> delOneFromUniqSet (ifTyVarsOfType ty) var `unionUniqSets`
           ifTyVarsOfType t
      IfaceTyConApp _ args -> ifTyVarsOfArgs args
      IfaceLitTy    _      -> emptyUniqSet

ifTyVarsOfArgs :: IfaceTcArgs -> UniqSet IfLclName
ifTyVarsOfArgs args = argv emptyUniqSet args
   where
     argv vs (ITC_Type t ts) = argv (vs `unionUniqSets` (ifTyVarsOfType t)) ts
     argv vs (ITC_Kind k ks) = argv (vs `unionUniqSets` (ifTyVarsOfType k)) ks
     argv vs ITC_Nil         = vs
\end{code}

%************************************************************************
%*                                                                      *
                Functions over IFaceTcArgs
%*                                                                      *
%************************************************************************


\begin{code}
stripKindArgs :: DynFlags -> IfaceTcArgs -> IfaceTcArgs
stripKindArgs dflags tys
  | gopt Opt_PrintExplicitKinds dflags = tys
  | otherwise = suppressKinds tys
    where
      suppressKinds c
        = case c of
            ITC_Kind _ ts -> suppressKinds ts
            _ -> c

toIfaceTcArgs :: [Type] -> IfaceTcArgs
toIfaceTcArgs [] = ITC_Nil
toIfaceTcArgs (t:ts)
  | isKind t  = ITC_Kind (toIfaceKind t) $ toIfaceTcArgs ts
  | otherwise = ITC_Type (toIfaceType t) $ toIfaceTcArgs ts

tcArgsIfaceTypes :: IfaceTcArgs -> [IfaceType]
tcArgsIfaceTypes ITC_Nil = []
tcArgsIfaceTypes (ITC_Kind t ts) = t : tcArgsIfaceTypes ts
tcArgsIfaceTypes (ITC_Type t ts) = t : tcArgsIfaceTypes ts
\end{code}

%************************************************************************
%*                                                                      *
                Functions over IFaceTyCon
%*                                                                      *
%************************************************************************

\begin{code}
isPromotedIfaceTyCon :: IfaceTyCon -> Bool
isPromotedIfaceTyCon (IfacePromotedTyCon _) = True
isPromotedIfaceTyCon _ = False
\end{code}
%************************************************************************
%*                                                                      *
                Pretty-printing
%*                                                                      *
%************************************************************************

Precedence
~~~~~~~~~~
@ppr_ty@ takes an @Int@ that is the precedence of the context.
The precedence levels are:
\begin{description}
\item[tOP_PREC]   No parens required.
\item[fUN_PREC]   Left hand argument of a function arrow.
\item[tYCON_PREC] Argument of a type constructor.
\end{description}

\begin{code}
tOP_PREC, fUN_PREC, tYCON_PREC :: Int
tOP_PREC    = 0 -- type   in ParseIface.y
fUN_PREC    = 1 -- btype  in ParseIface.y
tYCON_PREC  = 2 -- atype  in ParseIface.y

noParens :: SDoc -> SDoc
noParens pp = pp

maybeParen :: Int -> Int -> SDoc -> SDoc
maybeParen ctxt_prec inner_prec pretty
  | ctxt_prec < inner_prec = pretty
  | otherwise              = parens pretty

pprIfaceInfixApp :: Int -> (Int -> a -> SDoc) -> SDoc -> a -> a -> SDoc
pprIfaceInfixApp p pp pp_tc ty1 ty2
  = maybeParen p fUN_PREC $
    sep [pp fUN_PREC ty1, pprInfixVar True pp_tc <+> pp fUN_PREC ty2]

pprIfacePrefixApp :: Int -> SDoc -> [SDoc] -> SDoc
pprIfacePrefixApp p pp_fun pp_tys
  | null pp_tys = pp_fun
  | otherwise   = maybeParen p tYCON_PREC $
                  hang pp_fun 2 (sep pp_tys)
\end{code}


----------------------------- Printing binders ------------------------------------

\begin{code}
instance Outputable IfaceBndr where
    ppr (IfaceIdBndr bndr) = pprIfaceIdBndr bndr
    ppr (IfaceTvBndr bndr) = char '@' <+> pprIfaceTvBndr bndr

pprIfaceBndrs :: [IfaceBndr] -> SDoc
pprIfaceBndrs bs = sep (map ppr bs)

pprIfaceIdBndr :: (IfLclName, IfaceType) -> SDoc
pprIfaceIdBndr (name, ty) = hsep [ppr name, dcolon, ppr ty]

pprIfaceTvBndr :: IfaceTvBndr -> SDoc
pprIfaceTvBndr (tv, IfaceTyConApp tc ITC_Nil)
  | ifaceTyConName tc == liftedTypeKindTyConName = ppr tv
pprIfaceTvBndr (tv, kind) = parens (ppr tv <+> dcolon <+> ppr kind)

pprIfaceTvBndrs :: [IfaceTvBndr] -> SDoc
pprIfaceTvBndrs tyvars = sep (map pprIfaceTvBndr tyvars)

instance Binary IfaceBndr where
    put_ bh (IfaceIdBndr aa) = do
            putByte bh 0
            put_ bh aa
    put_ bh (IfaceTvBndr ab) = do
            putByte bh 1
            put_ bh ab
    get bh = do
            h <- getByte bh
            case h of
              0 -> do aa <- get bh
                      return (IfaceIdBndr aa)
              _ -> do ab <- get bh
                      return (IfaceTvBndr ab)
\end{code}

----------------------------- Printing IfaceType ------------------------------------

\begin{code}
---------------------------------
instance Outputable IfaceType where
  ppr ty = pprIfaceType ty

pprIfaceType, pprParendIfaceType ::IfaceType -> SDoc
pprIfaceType       = ppr_ty tOP_PREC
pprParendIfaceType = ppr_ty tYCON_PREC

ppr_ty :: Int -> IfaceType -> SDoc
ppr_ty _         (IfaceTyVar tyvar)     = ppr tyvar
ppr_ty ctxt_prec (IfaceTyConApp tc tys) = pprTyTcApp ctxt_prec tc tys
ppr_ty _         (IfaceLitTy n)         = ppr_tylit n
        -- Function types
ppr_ty ctxt_prec (IfaceFunTy ty1 ty2)
  = -- We don't want to lose synonyms, so we mustn't use splitFunTys here.
    maybeParen ctxt_prec fUN_PREC $
    sep [ppr_ty fUN_PREC ty1, sep (ppr_fun_tail ty2)]
  where
    ppr_fun_tail (IfaceFunTy ty1 ty2)
      = (arrow <+> ppr_ty fUN_PREC ty1) : ppr_fun_tail ty2
    ppr_fun_tail other_ty
      = [arrow <+> pprIfaceType other_ty]

ppr_ty ctxt_prec (IfaceAppTy ty1 ty2)
  = maybeParen ctxt_prec tYCON_PREC $
    ppr_ty fUN_PREC ty1 <+> pprParendIfaceType ty2

ppr_ty ctxt_prec ty
  = maybeParen ctxt_prec fUN_PREC (ppr_iface_sigma_type True ty)

instance Outputable IfaceTcArgs where
  ppr tca = pprIfaceTcArgs tca

pprIfaceTcArgs, pprParendIfaceTcArgs :: IfaceTcArgs -> SDoc
pprIfaceTcArgs  = ppr_tc_args tOP_PREC
pprParendIfaceTcArgs = ppr_tc_args tYCON_PREC

ppr_tc_args :: Int -> IfaceTcArgs -> SDoc
ppr_tc_args ctx_prec args
 = let pprTys t ts = ppr_ty ctx_prec t <+> ppr_tc_args ctx_prec ts
   in case args of
        ITC_Nil       -> empty
        ITC_Type t ts -> pprTys t ts
        ITC_Kind t ts -> pprTys t ts

-------------------
ppr_iface_sigma_type :: Bool -> IfaceType -> SDoc
ppr_iface_sigma_type show_foralls_unconditionally ty
  = ppr_iface_forall_part show_foralls_unconditionally tvs theta (ppr tau)
  where (tvs, theta, tau) = splitIfaceSigmaTy ty

ppr_iface_forall_part :: Outputable a
                      => Bool -> [IfaceTvBndr] -> [a] -> SDoc -> SDoc
ppr_iface_forall_part show_foralls_unconditionally tvs ctxt sdoc
  = sep [if show_foralls_unconditionally
         then pprIfaceForAll tvs
         else pprUserIfaceForAll tvs
         , pprIfaceContextArr ctxt
         , sdoc]

pprIfaceForAllPart :: Outputable a => [IfaceTvBndr] -> [a] -> SDoc -> SDoc
pprIfaceForAllPart tvs ctxt sdoc
  = sdocWithDynFlags $ \dflags ->
    ppr_iface_forall_part (gopt Opt_PrintExplicitForalls dflags) tvs ctxt sdoc

pprIfaceForAll :: [IfaceTvBndr] -> SDoc
pprIfaceForAll []  = empty
pprIfaceForAll tvs = ptext (sLit "forall") <+> pprIfaceTvBndrs tvs <> dot

pprIfaceSigmaType :: IfaceType -> SDoc
pprIfaceSigmaType ty = ppr_iface_sigma_type False ty

pprUserIfaceForAll :: [IfaceTvBndr] -> SDoc
pprUserIfaceForAll tvs
   = sdocWithDynFlags $ \dflags ->
     ppWhen ((any tv_has_kind_var) tvs || gopt Opt_PrintExplicitForalls dflags)
       $ pprIfaceForAll tvs
   where
     tv_has_kind_var (_,t) = not (isEmptyUniqSet (ifTyVarsOfType t))
-------------------

-- See equivalent function in TypeRep.lhs
pprIfaceTyList :: Int -> IfaceType -> IfaceType -> SDoc
-- Given a type-level list (t1 ': t2), see if we can print
-- it in list notation [t1, ...].
pprIfaceTyList ctxt_prec ty1 ty2
  = case gather ty2 of
      (arg_tys, Nothing)
        -> char '\'' <> brackets (fsep (punctuate comma
                        (map (ppr_ty tOP_PREC) (ty1:arg_tys))))
      (arg_tys, Just tl)
        -> maybeParen ctxt_prec fUN_PREC $ hang (ppr_ty fUN_PREC ty1)
           2 (fsep [ colon <+> ppr_ty fUN_PREC ty | ty <- arg_tys ++ [tl]])
  where
    gather :: IfaceType -> ([IfaceType], Maybe IfaceType)
     -- (gather ty) = (tys, Nothing) means ty is a list [t1, .., tn]
     --             = (tys, Just tl) means ty is of form t1:t2:...tn:tl
    gather (IfaceTyConApp tc tys)
      | tcname == consDataConName
      , (ITC_Kind _ (ITC_Type ty1 (ITC_Type ty2 ITC_Nil))) <- tys
      , (args, tl) <- gather ty2
      = (ty1:args, tl)
      | tcname == nilDataConName
      = ([], Nothing)
      where tcname = ifaceTyConName tc
    gather ty = ([], Just ty)

pprIfaceTypeApp :: IfaceTyCon -> IfaceTcArgs -> SDoc
pprIfaceTypeApp tc args = pprTyTcApp tOP_PREC tc args

pprTyTcApp :: Int -> IfaceTyCon -> IfaceTcArgs -> SDoc
pprTyTcApp ctxt_prec tc tys
  | ifaceTyConName tc == ipClassName
  , (ITC_Type (IfaceLitTy (IfaceStrTyLit n)) (ITC_Type ty ITC_Nil)) <- tys
  = char '?' <> ftext n <> ptext (sLit "::") <> ppr_ty tOP_PREC ty

  | ifaceTyConName tc == consDataConName
  , (ITC_Kind _ (ITC_Type ty1 (ITC_Type ty2 ITC_Nil))) <- tys
  = sdocWithDynFlags $ \dflags ->
    if gopt Opt_PrintExplicitKinds dflags
      then pprIfaceTyTcApp ctxt_prec tc tys
      else pprIfaceTyList ctxt_prec ty1 ty2
  | otherwise = pprIfaceTyTcApp ctxt_prec tc tys

pprIfaceTyTcApp :: Int -> IfaceTyCon -> IfaceTcArgs -> SDoc
pprIfaceTyTcApp ctxt_prec tc args
  = sdocWithDynFlags $ \dflags ->
  let tys = tcArgsIfaceTypes args
      oth = pprIfaceTcApp_help ppr_ty ctxt_prec tc tys_wo_kinds
        where
          tys_wo_kinds
            | isPromotedIfaceTyCon tc = tys
            | otherwise = tcArgsIfaceTypes $ stripKindArgs dflags args
  in ppr_iface_tc_app oth ppr_ty tc tys

pprIfaceCoTcApp :: Int -> IfaceTyCon -> [IfaceCoercion] -> SDoc
pprIfaceCoTcApp ctxt_prec tc tys
  = ppr_iface_tc_app oth ppr_co tc tys
  where oth = pprIfaceTcApp_help ppr_co ctxt_prec tc tys

ppr_iface_tc_app :: SDoc -> (Int -> a -> SDoc) -> IfaceTyCon -> [a] -> SDoc
ppr_iface_tc_app _ pp tc [ty]
  | n == listTyConName = pprPromotionQuote tc <> brackets (pp tOP_PREC ty)
  | n == parrTyConName = pprPromotionQuote tc <> paBrackets (pp tOP_PREC ty)
    where n = ifaceTyConName tc
ppr_iface_tc_app oth pp itc tys
  | Just (ATyCon tc) <- wiredInNameTyThing_maybe (ifaceTyConName itc)
  , Just sort <- tyConTuple_maybe tc
  , tyConArity tc == length tys
  = pprPromotionQuote itc
      <> tupleParens sort (sep (punctuate comma (map (pp tOP_PREC) tys)))
  | Just (ATyCon tc) <- wiredInNameTyThing_maybe (ifaceTyConName itc)
  , Just dc <- isPromotedDataCon_maybe tc
  , let dc_tc = dataConTyCon dc
  , isTupleTyCon dc_tc
  , let arity = tyConArity dc_tc
        ty_args = drop arity tys
  , ty_args `lengthIs` arity
  = pprPromotionQuote itc
      <> tupleParens (tupleTyConSort tc)
      (sep (punctuate comma (map (pp tOP_PREC) ty_args)))
  | otherwise = oth

pprIfaceTcApp_help :: (Int -> a -> SDoc) -> Int -> IfaceTyCon -> [a] -> SDoc
pprIfaceTcApp_help pp p tc tys
  | not (isSymOcc (nameOccName tcname))
  = pprIfacePrefixApp p (ppr tc) (map (pp tYCON_PREC) tys)

  | [ty1,ty2] <- tys  -- Infix, two arguments;
                      -- we know nothing of precedence though
  = pprIfaceInfixApp p pp (ppr tc) ty1 ty2

  | tcname == liftedTypeKindTyConName || tcname == unliftedTypeKindTyConName
  = ppr tc   -- Do not wrap *, # in parens

  | otherwise
  = pprIfacePrefixApp p (parens (ppr tc)) (map (pp tYCON_PREC) tys)
  where
    tcname = ifaceTyConName tc

ppr_tylit :: IfaceTyLit -> SDoc
ppr_tylit (IfaceNumTyLit n) = integer n
ppr_tylit (IfaceStrTyLit n) = text (show n)

pprIfaceCoercion, pprParendIfaceCoercion :: IfaceCoercion -> SDoc
pprIfaceCoercion = ppr_co tOP_PREC
pprParendIfaceCoercion = ppr_co tYCON_PREC

ppr_co :: Int -> IfaceCoercion -> SDoc
ppr_co _         (IfaceReflCo r ty) = angleBrackets (ppr ty) <> ppr_role r
ppr_co ctxt_prec (IfaceFunCo r co1 co2)
  = maybeParen ctxt_prec fUN_PREC $
    sep (ppr_co fUN_PREC co1 : ppr_fun_tail co2)
  where
    ppr_fun_tail (IfaceFunCo r co1 co2)
      = (arrow <> ppr_role r <+> ppr_co fUN_PREC co1) : ppr_fun_tail co2
    ppr_fun_tail other_co
      = [arrow <> ppr_role r <+> pprIfaceCoercion other_co]

ppr_co _         (IfaceTyConAppCo r tc cos)
  = parens (pprIfaceCoTcApp tOP_PREC tc cos) <> ppr_role r
ppr_co ctxt_prec (IfaceAppCo co1 co2)
  = maybeParen ctxt_prec tYCON_PREC $
    ppr_co fUN_PREC co1 <+> pprParendIfaceCoercion co2
ppr_co ctxt_prec co@(IfaceForAllCo _ _)
  = maybeParen ctxt_prec fUN_PREC (sep [ppr_tvs, pprIfaceCoercion inner_co])
  where
    (tvs, inner_co) = split_co co
    ppr_tvs = ptext (sLit "forall") <+> pprIfaceTvBndrs tvs <> dot

    split_co (IfaceForAllCo tv co')
      = let (tvs, co'') = split_co co' in (tv:tvs,co'')
    split_co co' = ([], co')

ppr_co _         (IfaceCoVarCo covar)       = ppr covar

ppr_co ctxt_prec (IfaceUnivCo r ty1 ty2)
  = maybeParen ctxt_prec tYCON_PREC $
    ptext (sLit "UnivCo") <+> ppr r <+>
    pprParendIfaceType ty1 <+> pprParendIfaceType ty2

ppr_co ctxt_prec (IfaceInstCo co ty)
  = maybeParen ctxt_prec tYCON_PREC $
    ptext (sLit "Inst") <+> pprParendIfaceCoercion co <+> pprParendIfaceType ty

ppr_co ctxt_prec (IfaceAxiomRuleCo tc tys cos)
  = maybeParen ctxt_prec tYCON_PREC
               (sep [ppr tc, nest 4 (sep (map pprParendIfaceType tys ++ map pprParendIfaceCoercion cos))])

ppr_co ctxt_prec co
  = ppr_special_co ctxt_prec doc cos
  where (doc, cos) = case co of
                     { IfaceAxiomInstCo n i cos -> (ppr n <> brackets (ppr i), cos)
                     ; IfaceSymCo co            -> (ptext (sLit "Sym"), [co])
                     ; IfaceTransCo co1 co2     -> (ptext (sLit "Trans"), [co1,co2])
                     ; IfaceNthCo d co          -> (ptext (sLit "Nth:") <> int d,
                                                    [co])
                     ; IfaceLRCo lr co          -> (ppr lr, [co])
                     ; IfaceSubCo co            -> (ptext (sLit "Sub"), [co])
                     ; _                        -> panic "pprIfaceCo" }

ppr_special_co :: Int -> SDoc -> [IfaceCoercion] -> SDoc
ppr_special_co ctxt_prec doc cos
  = maybeParen ctxt_prec tYCON_PREC
               (sep [doc, nest 4 (sep (map pprParendIfaceCoercion cos))])

ppr_role :: Role -> SDoc
ppr_role r = underscore <> pp_role
  where pp_role = case r of
                    Nominal          -> char 'N'
                    Representational -> char 'R'
                    Phantom          -> char 'P'

-------------------
instance Outputable IfaceTyCon where
  ppr tc = pprPromotionQuote tc <> ppr (ifaceTyConName tc)

pprPromotionQuote :: IfaceTyCon -> SDoc
pprPromotionQuote (IfacePromotedDataCon _ ) = char '\''
pprPromotionQuote (IfacePromotedTyCon _)    = ifPprDebug (char '\'')
pprPromotionQuote _                         = empty

instance Outputable IfaceCoercion where
  ppr = pprIfaceCoercion

instance Binary IfaceTyCon where
   put_ bh tc =
     case tc of
       IfaceTc n              -> putByte bh 0 >> put_ bh n
       IfacePromotedDataCon n -> putByte bh 1 >> put_ bh n
       IfacePromotedTyCon   n -> putByte bh 2 >> put_ bh n

   get bh =
     do tc <- getByte bh
        case tc of
          0 -> get bh >>= return . IfaceTc
          1 -> get bh >>= return . IfacePromotedDataCon
          2 -> get bh >>= return . IfacePromotedTyCon
          _ -> panic ("get IfaceTyCon " ++ show tc)

instance Outputable IfaceTyLit where
  ppr = ppr_tylit

instance Binary IfaceTyLit where
  put_ bh (IfaceNumTyLit n)  = putByte bh 1 >> put_ bh n
  put_ bh (IfaceStrTyLit n)  = putByte bh 2 >> put_ bh n

  get bh =
    do tag <- getByte bh
       case tag of
         1 -> do { n <- get bh
                 ; return (IfaceNumTyLit n) }
         2 -> do { n <- get bh
                 ; return (IfaceStrTyLit n) }
         _ -> panic ("get IfaceTyLit " ++ show tag)

instance Binary IfaceTcArgs where
  put_ bh tk =
    case tk of
      ITC_Type t ts -> putByte bh 0 >> put_ bh t >> put_ bh ts
      ITC_Kind t ts -> putByte bh 1 >> put_ bh t >> put_ bh ts
      ITC_Nil       -> putByte bh 2

  get bh =
    do c <- getByte bh
       case c of
         0 -> do
           t  <- get bh
           ts <- get bh
           return $! ITC_Type t ts
         1 -> do
           t  <- get bh
           ts <- get bh
           return $! ITC_Kind t ts
         2 -> return ITC_Nil
         _ -> panic ("get IfaceTcArgs " ++ show c)

-------------------
pprIfaceContextArr :: Outputable a => [a] -> SDoc
-- Prints "(C a, D b) =>", including the arrow
pprIfaceContextArr []    = empty
pprIfaceContextArr theta = pprIfaceContext theta <+> darrow

pprIfaceContext :: Outputable a => [a] -> SDoc
pprIfaceContext [pred] = ppr pred    -- No parens
pprIfaceContext preds  = parens (fsep (punctuate comma (map ppr preds)))

instance Binary IfaceType where
    put_ bh (IfaceForAllTy aa ab) = do
            putByte bh 0
            put_ bh aa
            put_ bh ab
    put_ bh (IfaceTyVar ad) = do
            putByte bh 1
            put_ bh ad
    put_ bh (IfaceAppTy ae af) = do
            putByte bh 2
            put_ bh ae
            put_ bh af
    put_ bh (IfaceFunTy ag ah) = do
            putByte bh 3
            put_ bh ag
            put_ bh ah
    put_ bh (IfaceDFunTy ag ah) = do
            putByte bh 4
            put_ bh ag
            put_ bh ah
    put_ bh (IfaceTyConApp tc tys)
      = do { putByte bh 5; put_ bh tc; put_ bh tys }

    put_ bh (IfaceLitTy n)
      = do { putByte bh 30; put_ bh n }

    get bh = do
            h <- getByte bh
            case h of
              0 -> do aa <- get bh
                      ab <- get bh
                      return (IfaceForAllTy aa ab)
              1 -> do ad <- get bh
                      return (IfaceTyVar ad)
              2 -> do ae <- get bh
                      af <- get bh
                      return (IfaceAppTy ae af)
              3 -> do ag <- get bh
                      ah <- get bh
                      return (IfaceFunTy ag ah)
              4 -> do ag <- get bh
                      ah <- get bh
                      return (IfaceDFunTy ag ah)
              5 -> do { tc <- get bh; tys <- get bh
                      ; return (IfaceTyConApp tc tys) }
              30 -> do n <- get bh
                       return (IfaceLitTy n)

              _  -> panic ("get IfaceType " ++ show h)

instance Binary IfaceCoercion where
  put_ bh (IfaceReflCo a b) = do
          putByte bh 1
          put_ bh a
          put_ bh b
  put_ bh (IfaceFunCo a b c) = do
          putByte bh 2
          put_ bh a
          put_ bh b
          put_ bh c
  put_ bh (IfaceTyConAppCo a b c) = do
          putByte bh 3
          put_ bh a
          put_ bh b
          put_ bh c
  put_ bh (IfaceAppCo a b) = do
          putByte bh 4
          put_ bh a
          put_ bh b
  put_ bh (IfaceForAllCo a b) = do
          putByte bh 5
          put_ bh a
          put_ bh b
  put_ bh (IfaceCoVarCo a) = do
          putByte bh 6
          put_ bh a
  put_ bh (IfaceAxiomInstCo a b c) = do
          putByte bh 7
          put_ bh a
          put_ bh b
          put_ bh c
  put_ bh (IfaceUnivCo a b c) = do
          putByte bh 8
          put_ bh a
          put_ bh b
          put_ bh c
  put_ bh (IfaceSymCo a) = do
          putByte bh 9
          put_ bh a
  put_ bh (IfaceTransCo a b) = do
          putByte bh 10
          put_ bh a
          put_ bh b
  put_ bh (IfaceNthCo a b) = do
          putByte bh 11
          put_ bh a
          put_ bh b
  put_ bh (IfaceLRCo a b) = do
          putByte bh 12
          put_ bh a
          put_ bh b
  put_ bh (IfaceInstCo a b) = do
          putByte bh 13
          put_ bh a
          put_ bh b
  put_ bh (IfaceSubCo a) = do
          putByte bh 14
          put_ bh a
  put_ bh (IfaceAxiomRuleCo a b c) = do
          putByte bh 15
          put_ bh a
          put_ bh b
          put_ bh c

  get bh = do
      tag <- getByte bh
      case tag of
           1 -> do a <- get bh
                   b <- get bh
                   return $ IfaceReflCo a b
           2 -> do a <- get bh
                   b <- get bh
                   c <- get bh
                   return $ IfaceFunCo a b c
           3 -> do a <- get bh
                   b <- get bh
                   c <- get bh
                   return $ IfaceTyConAppCo a b c
           4 -> do a <- get bh
                   b <- get bh
                   return $ IfaceAppCo a b
           5 -> do a <- get bh
                   b <- get bh
                   return $ IfaceForAllCo a b
           6 -> do a <- get bh
                   return $ IfaceCoVarCo a
           7 -> do a <- get bh
                   b <- get bh
                   c <- get bh
                   return $ IfaceAxiomInstCo a b c
           8 -> do a <- get bh
                   b <- get bh
                   c <- get bh
                   return $ IfaceUnivCo a b c
           9 -> do a <- get bh
                   return $ IfaceSymCo a
           10-> do a <- get bh
                   b <- get bh
                   return $ IfaceTransCo a b
           11-> do a <- get bh
                   b <- get bh
                   return $ IfaceNthCo a b
           12-> do a <- get bh
                   b <- get bh
                   return $ IfaceLRCo a b
           13-> do a <- get bh
                   b <- get bh
                   return $ IfaceInstCo a b
           14-> do a <- get bh
                   return $ IfaceSubCo a
           15-> do a <- get bh
                   b <- get bh
                   c <- get bh
                   return $ IfaceAxiomRuleCo a b c
           _ -> panic ("get IfaceCoercion " ++ show tag)

\end{code}

%************************************************************************
%*                                                                      *
        Conversion from Type to IfaceType
%*                                                                      *
%************************************************************************

\begin{code}
----------------
toIfaceTvBndr :: TyVar -> (IfLclName, IfaceType)
toIfaceTvBndr tyvar   = (occNameFS (getOccName tyvar), toIfaceKind (tyVarKind tyvar))
toIfaceIdBndr :: Id -> (IfLclName, IfaceType)
toIfaceIdBndr id      = (occNameFS (getOccName id),    toIfaceType (idType id))
toIfaceTvBndrs :: [TyVar] -> [(IfLclName, IfaceType)]
toIfaceTvBndrs tyvars = map toIfaceTvBndr tyvars

toIfaceBndr :: Var -> IfaceBndr
toIfaceBndr var
  | isId var  = IfaceIdBndr (toIfaceIdBndr var)
  | otherwise = IfaceTvBndr (toIfaceTvBndr var)

toIfaceKind :: Type -> IfaceType
toIfaceKind = toIfaceType

---------------------
toIfaceType :: Type -> IfaceType
-- Synonyms are retained in the interface type
toIfaceType (TyVarTy tv)      = IfaceTyVar (toIfaceTyVar tv)
toIfaceType (AppTy t1 t2)     = IfaceAppTy (toIfaceType t1) (toIfaceType t2)
toIfaceType (FunTy t1 t2)
  | isPredTy t1 = IfaceDFunTy (toIfaceType t1) (toIfaceType t2)
  | otherwise   = IfaceFunTy  (toIfaceType t1) (toIfaceType t2)
toIfaceType (TyConApp tc tys) = IfaceTyConApp (toIfaceTyCon tc) (toIfaceTcArgs tys)
toIfaceType (LitTy n)         = IfaceLitTy (toIfaceTyLit n)
toIfaceType (ForAllTy tv t)   = IfaceForAllTy (toIfaceTvBndr tv) (toIfaceType t)

toIfaceTyVar :: TyVar -> FastString
toIfaceTyVar = occNameFS . getOccName

toIfaceCoVar :: CoVar -> FastString
toIfaceCoVar = occNameFS . getOccName

----------------
toIfaceTyCon :: TyCon -> IfaceTyCon
toIfaceTyCon tc
  | isPromotedDataCon tc = IfacePromotedDataCon tc_name
  | isPromotedTyCon tc   = IfacePromotedTyCon tc_name
  | otherwise            = IfaceTc tc_name
    where tc_name = tyConName tc

toIfaceTyCon_name :: Name -> IfaceTyCon
toIfaceTyCon_name = IfaceTc

toIfaceTyLit :: TyLit -> IfaceTyLit
toIfaceTyLit (NumTyLit x) = IfaceNumTyLit x
toIfaceTyLit (StrTyLit x) = IfaceStrTyLit x

----------------
toIfaceTypes :: [Type] -> [IfaceType]
toIfaceTypes ts = map toIfaceType ts

----------------
toIfaceContext :: ThetaType -> IfaceContext
toIfaceContext = toIfaceTypes

----------------
toIfaceCoercion :: Coercion -> IfaceCoercion
toIfaceCoercion (Refl r ty)         = IfaceReflCo r (toIfaceType ty)
toIfaceCoercion (TyConAppCo r tc cos)
  | tc `hasKey` funTyConKey
  , [arg,res] <- cos                = IfaceFunCo r (toIfaceCoercion arg) (toIfaceCoercion res)
  | otherwise                       = IfaceTyConAppCo r (toIfaceTyCon tc)
                                                      (map toIfaceCoercion cos)
toIfaceCoercion (AppCo co1 co2)     = IfaceAppCo  (toIfaceCoercion co1)
                                                  (toIfaceCoercion co2)
toIfaceCoercion (ForAllCo v co)     = IfaceForAllCo (toIfaceTvBndr v)
                                                    (toIfaceCoercion co)
toIfaceCoercion (CoVarCo cv)        = IfaceCoVarCo  (toIfaceCoVar cv)
toIfaceCoercion (AxiomInstCo con ind cos)
                                    = IfaceAxiomInstCo (coAxiomName con) ind
                                                       (map toIfaceCoercion cos)
toIfaceCoercion (UnivCo r ty1 ty2)  = IfaceUnivCo r (toIfaceType ty1)
                                                  (toIfaceType ty2)
toIfaceCoercion (SymCo co)          = IfaceSymCo (toIfaceCoercion co)
toIfaceCoercion (TransCo co1 co2)   = IfaceTransCo (toIfaceCoercion co1)
                                                   (toIfaceCoercion co2)
toIfaceCoercion (NthCo d co)        = IfaceNthCo d (toIfaceCoercion co)
toIfaceCoercion (LRCo lr co)        = IfaceLRCo lr (toIfaceCoercion co)
toIfaceCoercion (InstCo co ty)      = IfaceInstCo (toIfaceCoercion co)
                                                  (toIfaceType ty)
toIfaceCoercion (SubCo co)          = IfaceSubCo (toIfaceCoercion co)

toIfaceCoercion (AxiomRuleCo co ts cs) = IfaceAxiomRuleCo
                                          (coaxrName co)
                                          (map toIfaceType ts)
                                          (map toIfaceCoercion cs)
\end{code}
