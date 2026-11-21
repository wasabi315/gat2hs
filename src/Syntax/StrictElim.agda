{-# OPTIONS --local-rewriting #-}

module Syntax.StrictElim where

open import Agda.Builtin.Equality.Rewrite renaming ( primRewriteNoMatch to ⟨_⟩ )
open import Haskell.Prelude hiding ( id; a; b; c; d; e; f; m; s; t; _,_; pi )
import Syntax as FO

--------------------------------------------------------------------------------

module _
  (ctx : Type) (sub : @0 ctx → @0 ctx → Type)
  (ty : @0 ctx → Type) (tm : (@0 Γ : ctx) → @0 ty Γ → Type)

  (id   : ∀ {@0 Γ} → sub Γ Γ)
  (comp : ∀ {@0 Δ Γ Θ} → sub Δ Γ → sub Θ Δ → sub Θ Γ)
  (let _⨾_ = comp)
  (@0 @rewrite id⨾ : ∀ {@0 Δ Γ} {@0 δ : sub Δ Γ} → id ⨾ δ ≡ δ)
  (@0 @rewrite ⨾id : ∀ {@0 Δ Γ} {@0 δ : sub Δ Γ} → δ ⨾ id ≡ δ)
  (@0 @rewrite ⨾⨾  : ∀ {@0 Δ Γ Θ Λ} {@0 δ : sub Δ Γ} {@0 σ : sub Θ Δ} {@0 γ : sub Λ Θ}
    → (δ ⨾ σ) ⨾ γ ≡ δ ⨾ (σ ⨾ γ))

  (tysub : ∀ {@0 Γ Δ} → ty Γ → sub Δ Γ → ty Δ)
  (tmsub : ∀ {@0 Γ Δ A} → tm Γ A → ∀ δ → tm Δ (tysub A δ))
  (let _[_]T = tysub; _[_] = tmsub)
  (@0 @rewrite [id]T : ∀ {@0 Γ} {@0 A : ty Γ} → A [ id ]T ≡ A)
  (@0 @rewrite [id]  : ∀ {@0 Γ A} {@0 t : tm Γ A} → t [ id ] ≡ t)
  (@0 @rewrite [][]T : ∀ {@0 Δ Γ Θ A} {@0 δ : sub Δ Γ} {@0 σ : sub Θ Δ}
    → A [ δ ]T [ σ ]T ≡ A [ δ ⨾ σ ]T)
  (@0 @rewrite [][]  : ∀ {@0 Δ Γ Θ A} {@0 t : tm Γ A} {@0 δ : sub Δ Γ} {@0 σ : sub Θ Δ}
    → _[_] {A = ⟨ _ ⟩} (t [ δ ]) σ ≡ t [ δ ⨾ σ ])

  (cnil : ctx) (csnoc : (Γ : ctx) → ty Γ → ctx)
  (let • = cnil; _▷_ = csnoc)

  (snil  : ∀ {@0 Δ} → sub Δ •)
  (ssnoc : ∀ {@0 Δ Γ A} (δ : sub Δ Γ) → tm Δ (A [ δ ]T) → sub Δ (Γ ▷ A))
  (let ε = snil; _,_ = ssnoc)
  (sfst  : ∀ {@0 Δ Γ A} → sub Δ (Γ ▷ A) → sub Δ Γ)
  (let π₁ = sfst)
  (ssnd  : ∀ {@0 Δ Γ A} (δ : sub Δ (Γ ▷ A)) → tm Δ (A [ π₁ δ ]T))
  (let π₂ = ssnd)
  (@0 •η : ∀ {@0 Δ} {@0 δ : sub Δ cnil} → δ ≡ ε)
  (@0 @rewrite ,⨾ : ∀ {@0 Δ Γ Θ A} {@0 δ : sub Δ Γ} {@0 σ : sub Θ Δ} {@0 t : tm Δ (A [ δ ]T)}
    → _≡_ {A = sub Θ (Γ ▷ A)} ((δ , t) ⨾ σ) ((δ ⨾ σ) , (t [ σ ])))
  (@0 @rewrite ▷β₁ : ∀ {@0 Δ Γ A} {@0 δ : sub Δ Γ} {@0 t : tm Δ (A [ δ ]T)}
    → π₁ {A = A} (δ , t) ≡ δ)
  (@0 @rewrite ▷β₂ : ∀ {@0 Δ Γ A} {@0 δ : sub Δ Γ} {@0 t : tm Δ (A [ δ ]T)}
    → π₂ {A = A} (δ , t) ≡ t)
  (@0 @rewrite π₁⨾ : ∀ {@0 Δ Γ Θ A} {@0 δ : sub Δ (Γ ▷ A)} {@0 σ : sub Θ Δ}
    → π₁ δ ⨾ σ ≡ π₁ (δ ⨾ σ))
  (@0 @rewrite π₂⨾ : ∀ {@0 Δ Γ Θ A} {@0 δ : sub Δ (Γ ▷ A)} {@0 σ : sub Θ Δ}
    → _[_] {A = ⟨ _ ⟩} (π₂ δ) σ ≡ π₂ (δ ⨾ σ))
  (@0 @rewrite ▷η : ∀ {@0 Δ Γ A} {@0 δ : sub Δ (Γ ▷ A)} → π₁ δ , π₂ δ ≡ δ)

  (pi : ∀ {@0 Γ} → ∀ A → ty (Γ ▷ A) → ty Γ)
  (let Π = pi)
  (lam : ∀ {@0 Γ A B} → tm (Γ ▷ A) B → tm Γ (Π A B))
  (app : ∀ {@0 Γ A B} → tm Γ (Π A B) → (u : tm Γ A) → tm Γ (B [ id , u ]T))

  (let wk : ∀ {@0 Γ A} → sub (Γ ▷ A) Γ
       wk = π₁ id
       vz : ∀ {@0 Γ A} → tm (Γ ▷ A) (A [ wk ]T)
       vz = π₂ id
       _^_ : ∀ {@0 Δ Γ} δ A → sub (Δ ▷ (A [ δ ]T)) (Γ ▷ A)
       δ ^ _ = (δ ⨾ wk) , vz)

  (@0 @rewrite Π[] : ∀ {@0 Δ Γ A B} {@0 δ : sub Δ Γ}
    → Π A B [ δ ]T ≡ Π (A [ δ ]T) (B [ δ ^ A ]T))
  (@0 @rewrite lam[] : ∀ {@0 Δ Γ A B} {@0 t : tm (Γ ▷ A) B} {@0 δ : sub Δ Γ}
    → lam t [ δ ] ≡ lam (t [ δ ^ A ]))
  (@0 @rewrite app[] : ∀ {@0 Δ Γ A B} {@0 t : tm Γ (Π A B)} {@0 u : tm Γ A} {@0 δ : sub Δ Γ}
    → _[_] {A = ⟨ _ ⟩} (app t u) δ ≡ app (t [ δ ]) (u [ δ ]))

  (@0 @rewrite Πβ : ∀ {@0 Γ A B} {@0 t : tm (Γ ▷ A) B} {@0 u : tm Γ A}
    → app (lam t) u ≡ t [ id , u ])
  (@0 Πη : ∀ {@0 Γ A B} {@0 t : tm Γ (Π A B)}
    → t ≡ lam (app (t [ wk ]) vz))
  where
