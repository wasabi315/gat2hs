{-# OPTIONS --show-implicit #-}

module Nf.ToSpine where

import Syntax as I
open I.Vars
import Nf.Traditional as Tr
import Nf.Spinal as Sp
open import Nf.Common

open import Haskell.Prelude using (_×_; _,_; case_of_; Type; Nat)
open import Haskell.Extra.Erase

--------------------------------------------------------------------------------

record VarSp (@0 Γ : I.Ctx) (@0 A : I.Ty Γ i) (@0 t : I.Tm Γ A) : Type where
  field
    @0 {varLvl} : Nat
    @0 {varTy}  : I.Ty Γ varLvl
    @0 {varTm}  : I.Tm Γ varTy
    var         : Var Γ varTy varTm
    spine       : Sp.Sp Γ varTy A varTm t
open VarSp public
{-# COMPILE AGDA2HS VarSp tuple #-}

toSpNf   : Tr.Nf Γ A t → Sp.Nf Γ A t
toSpNe   : Tr.Ne Γ A t → Sp.Sp Γ A B t u → VarSp Γ B u
toSpTyNf : Tr.TyNf Γ i A → Sp.TyNf Γ i A

toSpNf (Tr.lam t)      = Sp.lam (toSpNf t)
toSpNf (Tr.pair b t u) = Sp.pair (toSpTyNf b) (toSpNf t) (toSpNf u)
toSpNf (Tr.Code a)     = Sp.Code (toSpTyNf a)
toSpNf (Tr.raise t)    = Sp.raise (toSpNf t)

toSpNe (Tr.VarNe x) δ = record {var = x; spine = δ}
toSpNe (Tr.App t u) δ = toSpNe t (Sp.App (toSpNf u) Sp.,- δ)
toSpNe (Tr.Fst t)   δ = toSpNe t (Sp.Fst Sp.,- δ)
toSpNe (Tr.Snd t)   δ = toSpNe t (Sp.Snd Sp.,- δ)
toSpNe (Tr.Lower t) δ = toSpNe t (Sp.Lower Sp.,- δ)

toSpTyNf (Tr.Π a b)  = Sp.Π (toSpTyNf a) (toSpTyNf b)
toSpTyNf (Tr.Σ a b)  = Sp.Σ (toSpTyNf a) (toSpTyNf b)
toSpTyNf (Tr.U i)    = Sp.U i
toSpTyNf (Tr.Lift a) = Sp.Lift (toSpTyNf a)
toSpTyNf (Tr.El t)   = case toSpNe t Sp.[] of λ where
  record {var = x; spine = δ} → Sp.El x δ

{-# COMPILE AGDA2HS toSpNf   #-}
{-# COMPILE AGDA2HS toSpNe   #-}
{-# COMPILE AGDA2HS toSpTyNf #-}
