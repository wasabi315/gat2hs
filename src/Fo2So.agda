{-# OPTIONS --local-rewriting #-}

module Fo2So where

{-# FOREIGN AGDA2HS

{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}

#-}

open import Haskell.Prelude hiding ( id; a; b; c; d; e; f; m; s; t; _,_; pi; fst; snd )
import Syntax as FO
open import Syntax.StrictElim
open import SOSyntax as SO using (i)
import SOSyntax.Tel as SO

{-# FOREIGN AGDA2HS

import Prelude hiding ( pi, id, (^), fst, snd )
import Syntax qualified as FO

#-}

--------------------------------------------------------------------------------

Ctx : Type
Ctx = SO.Tel
{-# COMPILE AGDA2HS Ctx #-}

Ty : @0 Ctx → @0 Nat → Type
Ty Γ i = SO.Env Γ → SO.Ty i
{-# COMPILE AGDA2HS Ty #-}

Tm : (@0 Γ : Ctx) → @0 Ty Γ SO.i → Type
Tm Γ A = (ρ : SO.Env Γ) → SO.Tm (A ρ)
{-# COMPILE AGDA2HS Tm #-}

Sub : @0 Ctx → @0 Ctx → Type
Sub Δ Γ = SO.Env Δ → SO.Env Γ
{-# COMPILE AGDA2HS Sub #-}

variable
  @0 Γ Δ Θ : Ctx
  @0 A B C : Ty Γ i
  @0 t u v : Tm Γ A
  @0 δ σ γ : Sub Δ Γ

cnil : Ctx
cnil = SO.•
{-# COMPILE AGDA2HS cnil #-}
• = cnil
{-# COMPILE AGDA2HS • inline #-}

_▷_ : (Γ : Ctx) → Ty Γ i → Ctx
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

tysub : Ty Γ i → Sub Δ Γ → Ty Δ i
tysub a sub = λ env → a (sub env)
{-# COMPILE AGDA2HS tysub #-}
_[_]T = tysub
{-# COMPILE AGDA2HS _[_]T inline #-}

tmsub : Tm Γ A → ∀ δ → Tm Δ (A [ δ ]T)
tmsub t sub = λ env → t (sub env)
{-# COMPILE AGDA2HS tmsub #-}
_[_] = tmsub
{-# COMPILE AGDA2HS _[_] inline #-}

_^_ : ∀ δ (A : Ty Γ i) → Sub (Δ ▷ (A [ δ ]T)) (Γ ▷ A)
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

_ : {δ : Sub Δ Γ} {t : Tm Δ (A [ δ ]T)} → π₁ {A = A} (δ , t) ≡ δ
_ = refl

π₂ : (δ : Sub Δ (Γ ▷ A)) → Tm Δ (A [ π₁ δ ]T)
π₂ δ = λ ρ → SO.π₂ (δ ρ)
{-# COMPILE AGDA2HS π₂ #-}

_ : {δ : Sub Δ Γ} {A : Ty Γ i} {t : Tm Δ (A [ δ ]T)} → π₂ {A = A} (δ , t) ≡ t
_ = refl

pi : (A : Ty Γ i) → Ty (Γ ▷ A) i → Ty Γ i
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

postulate
  •η : {δ : Sub Γ •} → δ ≡ ε
  Πη : {t : Tm {i} Γ (Π A B)} → _≡_ {A = Tm Γ (Π A B)} t (λ ρ → SO.lam (SO.app (t ρ)))

_ : {t : Tm {i} (Γ ▷ A) B} {u : Tm Γ A}
  → app {B = B} (lam t) u ≡ λ ρ → SO.app (SO.lam (λ τ → t (ρ SO., τ))) (u ρ)
_ = refl

sigma : (A : Ty Γ i) → Ty (Γ ▷ A) i → Ty Γ i
sigma a b = λ ρ → SO.Σ (a ρ) λ τ → b (ρ SO., τ)
{-# COMPILE AGDA2HS sigma #-}
Σ = sigma
{-# COMPILE AGDA2HS Σ inline #-}

pair : (@0 B : Ty (Γ ▷ A) i) → (t : Tm Γ A) → Tm Γ (B [ id , t ]T) → Tm Γ (Σ A B)
pair B t u = λ ρ → SO.pair (t ρ) (u ρ)
{-# COMPILE AGDA2HS pair #-}

fst : Tm {i} Γ (Σ A B) → Tm Γ A
fst t = λ ρ → SO.fst (t ρ)
{-# COMPILE AGDA2HS fst #-}

snd : (t : Tm {i} Γ (Σ A B)) → Tm Γ (B [ id , fst t ]T)
snd t = λ ρ → SO.snd (t ρ)
{-# COMPILE AGDA2HS snd #-}

_U : ∀ (@0 i) → Ty Γ (suc i)
_U i = λ ρ → SO.U i
{-# COMPILE AGDA2HS _U #-}

el : Tm Γ (_U i) → Ty Γ i
el t = λ ρ → SO.El (t ρ)
{-# COMPILE AGDA2HS el #-}

code : Ty Γ i → Tm Γ (_U i)
code a = λ ρ → SO.Code (a ρ)
{-# COMPILE AGDA2HS code #-}

module Fo2So =
  Elim Ctx Sub Ty Tm
       id _⨾_ refl refl refl
       tysub tmsub refl refl refl refl
       • _▷_
       -- TODO: For some reason, it appears we have to eta-expand '_,_' here
       -- to generate correct Haskell code. Is this an agda2hs bug?
       ε (λ δ t → δ , t) π₁ π₂ •η refl refl refl refl refl refl
       Π lam app refl refl refl refl Πη
       Σ pair fst snd refl refl refl refl refl refl refl
       _U el code refl refl refl refl refl

fo2soCtx : FO.Ctx → Ctx
fo2soCtx = Fo2So.elimCtx
{-# COMPILE AGDA2HS fo2soCtx #-}

fo2soSub : FO.Sub FO.Δ FO.Γ → Sub (fo2soCtx FO.Δ) (fo2soCtx FO.Γ)
fo2soSub = Fo2So.elimSub
{-# COMPILE AGDA2HS fo2soSub #-}

fo2soTy : FO.Ty FO.Γ i → Ty (fo2soCtx FO.Γ) i
fo2soTy = Fo2So.elimTy
{-# COMPILE AGDA2HS fo2soTy #-}

fo2soTm  : FO.Tm FO.Γ FO.A → Tm (fo2soCtx FO.Γ) (fo2soTy FO.A)
fo2soTm = Fo2So.elimTm
{-# COMPILE AGDA2HS fo2soTm #-}
