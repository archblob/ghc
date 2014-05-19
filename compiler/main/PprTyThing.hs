-----------------------------------------------------------------------------
--
-- Pretty-printing TyThings
--
-- (c) The GHC Team 2005
--
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -fno-warn-tabs #-}
-- The above warning supression flag is a temporary kludge.
-- While working on this module you are encouraged to remove it and
-- detab the module (please do the detabbing in a separate patch). See
--     http://ghc.haskell.org/trac/ghc/wiki/Commentary/CodingStyle#TabsvsSpaces
-- for details

module PprTyThing (
	pprTyThing,
	pprTyThingInContext,
	pprTyThingLoc,
	pprTyThingInContextLoc,
	pprTyThingHdr,
    pprTypeForUser
  ) where

import TypeRep ( TyThing(..) )
import HscTypes( tyThingParent_maybe )
import MkIface ( tyThingToIfaceDecl )
import Type ( tidyOpenType )
import IfaceSyn ( pprIfaceDecl, pprIfaceDeclHdr, ShowSub, showAll )
import TcType
import Name
import VarEnv( emptyTidyEnv )
import Outputable
import FastString

-- -----------------------------------------------------------------------------
-- Pretty-printing entities that we get from the GHC API

-- This should be a good source of sample code for using the GHC API to
-- inspect source code entities.

----------------------------
-- | Pretty-prints a 'TyThing' with its defining location.
pprTyThingLoc :: TyThing -> SDoc
pprTyThingLoc tyThing
  = showWithLoc (pprDefinedAt (getName tyThing)) (pprTyThing tyThing)

-- | Pretty-prints a 'TyThing'.
pprTyThing :: TyThing -> SDoc
pprTyThing thing = ppr_ty_thing (Just showAll) thing

-- | Pretty-prints a 'TyThing' in context: that is, if the entity
-- is a data constructor, record selector, or class method, then
-- the entity's parent declaration is pretty-printed with irrelevant
-- parts omitted.
pprTyThingInContext :: TyThing -> SDoc
pprTyThingInContext thing
  = go [] thing
  where
    go ss thing = case tyThingParent_maybe thing of
                    Just parent -> go (getOccName thing : ss) parent
                    Nothing     -> ppr_ty_thing (Just ss) thing

-- | Like 'pprTyThingInContext', but adds the defining location.
pprTyThingInContextLoc :: TyThing -> SDoc
pprTyThingInContextLoc tyThing
  = showWithLoc (pprDefinedAt (getName tyThing))
                (pprTyThingInContext tyThing)

-- | Pretty-prints the 'TyThing' header. For functions and data constructors
-- the function is equivalent to 'pprTyThing' but for type constructors
-- and classes it prints only the header part of the declaration.
pprTyThingHdr :: TyThing -> SDoc
pprTyThingHdr = ppr_ty_thing Nothing

------------------------
-- NOTE: We pretty-print 'TyThing' via 'IfaceDecl' so that we can reuse the
-- 'TyCon' tidying happening in 'tyThingToIfaceDecl'. See #8776 for details.
ppr_ty_thing :: Maybe ShowSub -> TyThing -> SDoc
ppr_ty_thing mss tyThing =
  let { ifaceDecl = tyThingToIfaceDecl tyThing
		  ; name = getName tyThing
  } in case mss of
       Nothing -> pprIfaceDeclHdr (Just name) ifaceDecl
       Just ss -> pprIfaceDecl (Just name) ss ifaceDecl

pprTypeForUser :: Type -> SDoc
-- We do two things here.
-- a) We tidy the type, regardless
-- b) Swizzle the foralls to the top, so that without
--    -fprint-explicit-foralls we'll suppress all the foralls
-- Prime example: a class op might have type
--	forall a. C a => forall b. Ord b => stuff
-- Then we want to display
--	(C a, Ord b) => stuff
pprTypeForUser ty
  = pprSigmaType (mkSigmaTy tvs ctxt tau)
  where
    (tvs, ctxt, tau) = tcSplitSigmaTy tidy_ty
    (_, tidy_ty)   = tidyOpenType emptyTidyEnv ty
     -- Often the types/kinds we print in ghci are fully generalised
     -- and have no free variables, but it turns out that we sometimes
     -- print un-generalised kinds (eg when doing :k T), so it's
     -- better to use tidyOpenType here

showWithLoc :: SDoc -> SDoc -> SDoc
showWithLoc loc doc
    = hang doc 2 (char '\t' <> comment <+> loc)
		-- The tab tries to make them line up a bit
  where
    comment = ptext (sLit "--")
