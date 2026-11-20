{-# OPTIONS --local-confluence-check #-}

module Syntax where

{-# FOREIGN AGDA2HS

{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}

#-}

open import Agda.Builtin.Equality.Rewrite renaming ( primRewriteNoMatch to ⟨_⟩ )
open import Haskell.Prelude hiding ( id; a; b; c; d; e; f; m; s; t; _,_; pi )

{-# FOREIGN AGDA2HS
import Prelude hiding ( pi, (^) )
#-}

--------------------------------------------------------------------------------

data Ctx : Type

postulate
  Sub : @0 Ctx → @0 Ctx → Type
  Ty  : @0 Ctx → Type
  Tm  : (@0 Γ : Ctx) → @0 Ty Γ → Type

variable
  @0 Γ Δ Θ Λ Γ₁ Γ₂ Δ₁ Δ₂ Θ₁ Θ₂ : Ctx
  @0 A B C D A₁ A₂ A₃ B₁ B₂ B₃  : Ty _
  @0 t u v t₁ t₂ t₃ u₁ u₂ u₃ : Tm _ _
  @0 δ σ γ δ₁ δ₂ : Sub _ _

postulate
  sid   : Sub Γ Γ
  scomp : Sub Δ Γ → Sub Θ Δ → Sub Θ Γ
syntax sid = id
syntax scomp δ σ = δ ⨾ σ

postulate
  id⨾ : id ⨾ δ ≡ δ
  {-# REWRITE id⨾ #-}
  ⨾id : δ ⨾ id ≡ δ
  {-# REWRITE ⨾id #-}
  ⨾⨾  : (δ ⨾ σ) ⨾ γ ≡ δ ⨾ (σ ⨾ γ)
  {-# REWRITE ⨾⨾ #-}

postulate
  tysub : Ty Γ → Sub Δ Γ → Ty Δ
  tmsub : Tm Γ A → ∀ δ → Tm Δ (A [ δ ]T)
syntax tysub A δ = A [ δ ]T
syntax tmsub t δ = t [ δ ]

postulate
  [id]T : A [ id ]T ≡ A
  {-# REWRITE [id]T  #-}
  [id]  : t [ id ] ≡ t
  {-# REWRITE [id] #-}

  [][]T : A [ δ ]T [ σ ]T ≡ A [ δ ⨾ σ ]T
  {-# REWRITE [][]T #-}
  [][] : tmsub {A = ⟨ _ ⟩} (t [ δ ]) σ ≡ t [ δ ⨾ σ ]
  {-# REWRITE [][] #-}

data Ctx where
  CNil  : Ctx
  CSnoc : (Γ : Ctx) → Ty Γ → Ctx

syntax CNil = •
syntax CSnoc Γ A = Γ ▷ A

-- Context comprehension
postulate
  snil  : Sub Δ •
syntax snil = ε
postulate
  •η : δ ≡ ε

  ssnoc : (δ : Sub Δ Γ) → Tm Δ (A [ δ ]T) → Sub Δ (Γ ▷ A)
syntax ssnoc δ t = δ , t

postulate
  sfst  : Sub Δ (Γ ▷ A) → Sub Δ Γ
π₁ = sfst
{-# COMPILE AGDA2HS π₁ inline #-}

postulate
  ssnd  : (δ : Sub Δ (Γ ▷ A)) → Tm Δ (A [ π₁ δ ]T)
π₂ = ssnd
{-# COMPILE AGDA2HS π₂ inline #-}

postulate
  ,⨾  : (δ , t) ⨾ σ ≡ (δ ⨾ σ) , (t [ σ ])
  {-# REWRITE ,⨾ #-}
  ▷β₁ : sfst (δ , t) ≡ δ
  {-# REWRITE ▷β₁ #-}
  ▷β₂ : ssnd (δ , t) ≡ t
  {-# REWRITE ▷β₂ #-}

  π₁⨾ : sfst δ ⨾ σ ≡ π₁ (δ ⨾ σ)
  {-# REWRITE π₁⨾ #-}
  π₂[] : tmsub {A = ⟨ _ ⟩} (ssnd δ) σ ≡ π₂ (δ ⨾ σ)
  {-# REWRITE π₂[] #-}

  ▷η : sfst δ , ssnd δ ≡ δ
  {-# REWRITE ▷η #-}


-- Dependent functions
-- We use binary application because it behaves better with rewriting
postulate
  pi    : ∀ A → Ty (Γ ▷ A) → Ty Γ
  lam   : Tm (Γ ▷ A) B → Tm Γ (Π A B)
  app   : Tm Γ (Π A B) → (u : Tm Γ A) → Tm Γ (B [ id , u ]T)

syntax pi = Π

wk : Sub (Γ ▷ A) Γ
wk = π₁ id
{-# COMPILE AGDA2HS wk #-}

vz : Tm (Γ ▷ A) (A [ wk ]T)
vz = π₂ id
{-# COMPILE AGDA2HS vz #-}

_^_ : ∀ δ A → Sub (Δ ▷ (A [ δ ]T)) (Γ ▷ A)
δ ^ _ = (δ ⨾ wk) , vz
{-# COMPILE AGDA2HS _^_ #-}

postulate
  Π[]   : Π A B [ δ ]T ≡ Π (A [ δ ]T) (B [ δ ^ A ]T)
  {-# REWRITE Π[] #-}
  lam[] : lam t [ δ ] ≡ lam (t [ δ ^ A ])
  {-# REWRITE lam[] #-}
  -- Unlike with unary application, we cannot derive naturality
  app[] : tmsub {A = ⟨ _ ⟩} (app t u) δ ≡ app (t [ δ ]) (u [ δ ])
  {-# REWRITE app[] #-}

  Πβ : app (lam t) u ≡ t [ id , u ]
  {-# REWRITE Πβ #-}
  Πη : {t : Tm Γ (Π A B)} → t ≡ lam (app (t [ wk ]) vz)

{-# FOREIGN AGDA2HS

data Sub
  = SNil
  | SId
  | SComp Sub Sub
  | SSnoc Sub Tm
  | SFst Sub

data Ty
  = TySub Ty Sub
  | Pi Ty Ty

data Tm
  = TmSub Tm Sub
  | SSnd Sub
  | Lam Tm
  | App Tm Tm

snil = SNil
sid = SId
scomp = SComp
ssnoc = SSnoc
sfst = SFst
ssnd = SSnd
tysub = TySub
tmsub = TmSub
pi = Pi
lam = Lam
app = App

#-}

{-# COMPILE AGDA2HS Ctx            #-}
{-# COMPILE AGDA2HS Sub   existing #-}
{-# COMPILE AGDA2HS Ty    existing #-}
{-# COMPILE AGDA2HS Tm    existing #-}
{-# COMPILE AGDA2HS sid   existing #-}
{-# COMPILE AGDA2HS scomp existing #-}
{-# COMPILE AGDA2HS ssnoc existing #-}
{-# COMPILE AGDA2HS sfst  existing #-}
{-# COMPILE AGDA2HS ssnd  existing #-}
{-# COMPILE AGDA2HS tysub existing #-}
{-# COMPILE AGDA2HS tmsub existing #-}
{-# COMPILE AGDA2HS pi    existing #-}
{-# COMPILE AGDA2HS lam   existing #-}
{-# COMPILE AGDA2HS app   existing #-}
