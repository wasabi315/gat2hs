module Fo2So where

{-# FOREIGN AGDA2HS

{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}

#-}

open import Haskell.Prelude hiding ( id; a; b; c; d; e; f; m; s; t; _,_; pi )
import Syntax as FO
import SOSyntax as SO
import SOSyntax.Tel as SO

{-# FOREIGN AGDA2HS

import Prelude hiding ( pi, id, (^) )
import Syntax qualified as FO

#-}

--------------------------------------------------------------------------------

Ctx : Type
Ctx = SO.Tel
{-# COMPILE AGDA2HS Ctx #-}

Ty : @0 Ctx → Type
Ty Γ = SO.Env Γ → SO.Ty
{-# COMPILE AGDA2HS Ty #-}

Tm : (@0 Γ : Ctx) → @0 Ty Γ → Type
Tm Γ A = (ρ : SO.Env Γ) → SO.Tm (A ρ)
{-# COMPILE AGDA2HS Tm #-}

Sub : @0 Ctx → @0 Ctx → Type
Sub Δ Γ = SO.Env Δ → SO.Env Γ
{-# COMPILE AGDA2HS Sub #-}

postulate
  fo2soCtx : FO.Ctx → Ctx
  fo2soTy  : FO.Ty FO.Γ → Ty (fo2soCtx FO.Γ)
  fo2soTm  : FO.Tm FO.Γ FO.A → Tm (fo2soCtx FO.Γ) (fo2soTy FO.A)
  fo2soSub : FO.Sub FO.Δ FO.Γ → Sub (fo2soCtx FO.Δ) (fo2soCtx FO.Γ)

{-# COMPILE AGDA2HS fo2soCtx existing #-}
{-# COMPILE AGDA2HS fo2soTy  existing #-}
{-# COMPILE AGDA2HS fo2soTm  existing #-}
{-# COMPILE AGDA2HS fo2soSub existing #-}

{-# FOREIGN AGDA2HS

fo2soCtx :: FO.Ctx -> Ctx
fo2soCtx = \case
  FO.CNil -> cnil
  FO.CSnoc g a -> fo2soCtx g ▷ fo2soTy a

fo2soTy :: FO.Ty -> Ty
fo2soTy = \case
  FO.TySub a sub -> tysub (fo2soTy a) (fo2soSub sub)
  FO.Pi a b -> pi (fo2soTy a) (fo2soTy b)

fo2soSub :: FO.Sub -> Sub
fo2soSub = \case
  FO.SNil -> ε
  FO.SId -> id
  FO.SComp sub1 sub2 -> fo2soSub sub1 ⨾ fo2soSub sub2
  FO.SSnoc sub t -> ssnoc (fo2soSub sub) (fo2soTm t)
  FO.SFst sub -> π₁ (fo2soSub sub)

fo2soTm :: FO.Tm -> Tm
fo2soTm = \case
  FO.TmSub t sub -> tmsub (fo2soTm t) (fo2soSub sub)
  FO.SSnd sub -> π₂ (fo2soSub sub)
  FO.Lam t -> lam (fo2soTm t)
  FO.App t u -> app (fo2soTm t) (fo2soTm u)

#-}

variable
  @0 Γ Δ Θ : Ctx
  @0 A B C : Ty _
  @0 t u v : Tm _ _
  @0 δ σ γ : Sub _ _

cnil : Ctx
cnil = SO.•
{-# COMPILE AGDA2HS cnil #-}
• = cnil
{-# COMPILE AGDA2HS • inline #-}

_▷_ : (Γ : Ctx) → Ty Γ → Ctx
_▷_ = SO._▷_
{-# COMPILE AGDA2HS _▷_ #-}

id : Sub Γ Γ
id = λ ρ → ρ
{-# COMPILE AGDA2HS id #-}

ε : Sub Γ •
ε = λ _ → SO.ε
{-# COMPILE AGDA2HS ε #-}

_⨾_ : Sub Δ Γ → Sub Θ Δ → Sub Θ Γ
_⨾_ δ σ = λ ρ → δ (σ ρ)
{-# COMPILE AGDA2HS _⨾_ #-}

tysub : Ty Γ → Sub Δ Γ → Ty Δ
tysub a sub = λ env → a (sub env)
{-# COMPILE AGDA2HS tysub #-}
_[_]T = tysub
{-# COMPILE AGDA2HS _[_]T inline #-}

tmsub : Tm Γ A → ∀ δ → Tm Δ (A [ δ ]T)
tmsub t sub = λ env → t (sub env)
{-# COMPILE AGDA2HS tmsub #-}
_[_] = tmsub
{-# COMPILE AGDA2HS _[_] inline #-}

_^_ : ∀ δ A → Sub (Δ ▷ (A [ δ ]T)) (Γ ▷ A)
δ ^ _ = λ ρ → δ (SO.π₁ ρ) SO., SO.π₂ ρ
{-# COMPILE AGDA2HS _^_ #-}

ssnoc : (δ : Sub Δ Γ) → Tm Δ (A [ δ ]T) → Sub Δ (Γ ▷ A)
ssnoc δ t = λ ρ → δ ρ SO., t ρ
{-# COMPILE AGDA2HS ssnoc #-}
_,_ = ssnoc
{-# COMPILE AGDA2HS _,_ inline #-}

π₁ : Sub Δ (Γ ▷ A) → Sub Δ Γ
π₁ δ = λ ρ → SO.π₁ (δ ρ)
{-# COMPILE AGDA2HS π₁ #-}

π₂ : (δ : Sub Δ (Γ ▷ A)) → Tm Δ (A [ π₁ δ ]T)
π₂ δ = λ ρ → SO.esnd (δ ρ)
{-# COMPILE AGDA2HS π₂ #-}

pi : ∀ A → Ty (Γ ▷ A) → Ty Γ
pi a b = λ ρ → SO.Π (a ρ) λ τ → b (ρ SO., τ)
{-# COMPILE AGDA2HS pi #-}
Π = pi
{-# COMPILE AGDA2HS Π inline #-}

lam : Tm (Γ ▷ A) B → Tm Γ (Π A B)
lam t = λ ρ → SO.lam λ τ → t (ρ SO., τ)
{-# COMPILE AGDA2HS lam #-}

app : Tm Γ (Π A B) → (u : Tm Γ A) → Tm Γ (B [ id , u ]T)
app t u = λ ρ → SO.app (t ρ) (u ρ)
{-# COMPILE AGDA2HS app #-}
