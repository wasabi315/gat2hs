{-# OPTIONS --show-implicit #-}

module Nf.Conv where

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

tr2SpNf   : Tr.Nf Γ A t → Sp.Nf Γ A t
tr2SpNe   : Tr.Ne Γ A t → Sp.Sp Γ A B t u → VarSp Γ B u
tr2SpTyNf : Tr.TyNf Γ i A → Sp.TyNf Γ i A

tr2SpNf (Tr.lam t)      = Sp.lam (tr2SpNf t)
tr2SpNf (Tr.pair b t u) = Sp.pair (tr2SpTyNf b) (tr2SpNf t) (tr2SpNf u)
tr2SpNf (Tr.Code a)     = Sp.Code (tr2SpTyNf a)
tr2SpNf (Tr.raise t)    = Sp.raise (tr2SpNf t)

tr2SpNe (Tr.VarNe x) δ = VarSp.constructor x δ
tr2SpNe (Tr.App t u) δ = tr2SpNe t (Sp.App (tr2SpNf u) Sp.,- δ)
tr2SpNe (Tr.Fst t)   δ = tr2SpNe t (Sp.Fst Sp.,- δ)
tr2SpNe (Tr.Snd t)   δ = tr2SpNe t (Sp.Snd Sp.,- δ)
tr2SpNe (Tr.Lower t) δ = tr2SpNe t (Sp.Lower Sp.,- δ)

tr2SpTyNf (Tr.Π a b)  = Sp.Π (tr2SpTyNf a) (tr2SpTyNf b)
tr2SpTyNf (Tr.Σ a b)  = Sp.Σ (tr2SpTyNf a) (tr2SpTyNf b)
tr2SpTyNf (Tr.U i)    = Sp.U i
tr2SpTyNf (Tr.Lift a) = Sp.Lift (tr2SpTyNf a)
tr2SpTyNf (Tr.El t)   = case tr2SpNe t Sp.[] of λ where
  (VarSp.constructor x δ) → Sp.El x δ

{-# COMPILE AGDA2HS tr2SpNf   #-}
{-# COMPILE AGDA2HS tr2SpNe   #-}
{-# COMPILE AGDA2HS tr2SpTyNf #-}

sp2TrNf   : Sp.Nf Γ A t → Tr.Nf Γ A t
sp2TrElim : Tr.Ne Γ A t → Sp.Elim Γ A B t u → Tr.Ne Γ B u
sp2TrSp   : Tr.Ne Γ A t → Sp.Sp Γ A B t u → Tr.Ne Γ B u
sp2TrTyNf : Sp.TyNf Γ i A → Tr.TyNf Γ i A

sp2TrNf (Sp.lam t)      = Tr.lam (sp2TrNf t)
sp2TrNf (Sp.pair b t u) = Tr.pair (sp2TrTyNf b) (sp2TrNf t) (sp2TrNf u)
sp2TrNf (Sp.Code a)     = Tr.Code (sp2TrTyNf a)
sp2TrNf (Sp.raise t)    = Tr.raise (sp2TrNf t)

sp2TrElim t (Sp.App u) = Tr.App t (sp2TrNf u)
sp2TrElim t Sp.Fst     = Tr.Fst t
sp2TrElim t Sp.Snd     = Tr.Snd t
sp2TrElim t Sp.Lower   = Tr.Lower t

sp2TrSp t Sp.[]       = t
sp2TrSp t (e Sp.,- δ) = sp2TrSp (sp2TrElim t e) δ

sp2TrTyNf (Sp.Π a b)   = Tr.Π (sp2TrTyNf a) (sp2TrTyNf b)
sp2TrTyNf (Sp.Σ a b)   = Tr.Σ (sp2TrTyNf a) (sp2TrTyNf b)
sp2TrTyNf (Sp.U i)     = Tr.U i
sp2TrTyNf (Sp.El x sp) = Tr.El (sp2TrSp (Tr.VarNe x) sp)
sp2TrTyNf (Sp.Lift a)  = Tr.Lift (sp2TrTyNf a)

{-# COMPILE AGDA2HS sp2TrNf   #-}
{-# COMPILE AGDA2HS sp2TrElim #-}
{-# COMPILE AGDA2HS sp2TrSp   #-}
{-# COMPILE AGDA2HS sp2TrTyNf #-}
