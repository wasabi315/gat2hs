{-# OPTIONS --local-confluence-check #-}

module Syntax where

{-# FOREIGN AGDA2HS

{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}

#-}

open import Agda.Builtin.Equality.Rewrite renaming ( primRewriteNoMatch to ⟨_⟩ )
open import Haskell.Prelude hiding ( id; a; b; c; d; e; f; m; s; t; _,_; fst; snd )

{-# FOREIGN AGDA2HS
import Prelude hiding ( (^) )
#-}

--------------------------------------------------------------------------------

variable
  @0 i : Nat

data Ctx : Type

postulate
  Sub : @0 Ctx → @0 Ctx → Type
  Ty  : @0 Ctx → @0 Nat → Type
  Tm  : (@0 Γ : Ctx) → @0 Ty Γ i → Type

data Ctx where
  CNil  : Ctx
  CSnoc : (Γ : Ctx) → Ty Γ i → Ctx
pattern • = CNil
pattern _▷_ Γ A = CSnoc Γ A

variable
  @0 Γ Δ Θ Λ Γ₁ Γ₂ Δ₁ Δ₂ Θ₁ Θ₂ : Ctx
  @0 A B C D A₁ A₂ A₃ B₁ B₂ B₃ : Ty Γ i
  @0 t u v t₁ t₂ t₃ u₁ u₂ u₃ : Tm Γ A
  @0 δ σ γ δ₁ δ₂ : Sub Δ Γ

postulate
  SId   : Sub Γ Γ
  SComp : Sub Δ Γ → Sub Θ Δ → Sub Θ Γ

id  = SId; {-# INLINE id #-}
_⨾_ = SComp; {-# INLINE _⨾_ #-}

postulate
  id⨾ : id ⨾ δ ≡ δ
  {-# REWRITE id⨾ #-}
  ⨾id : δ ⨾ id ≡ δ
  {-# REWRITE ⨾id #-}
  ⨾⨾  : (δ ⨾ σ) ⨾ γ ≡ δ ⨾ (σ ⨾ γ)
  {-# REWRITE ⨾⨾ #-}

postulate
  TySub : Ty Γ i → Sub Δ Γ → Ty Δ i
_[_]T = TySub; {-# INLINE _[_]T #-}

postulate
  TmSub : Tm Γ A → ∀ δ → Tm Δ (A [ δ ]T)
_[_] = TmSub; {-# INLINE _[_] #-}

postulate
  [id]T : A [ id ]T ≡ A
  {-# REWRITE [id]T  #-}
  [id]  : t [ id ] ≡ t
  {-# REWRITE [id] #-}

  [][]T : A [ δ ]T [ σ ]T ≡ A [ δ ⨾ σ ]T
  {-# REWRITE [][]T #-}

  [][] : TmSub {A = ⟨ _ ⟩} (t [ δ ]) σ ≡ t [ δ ⨾ σ ]
  {-# REWRITE [][] #-}

-- Context comprehension
postulate
  SNil : Sub Δ •
ε = SNil; {-# INLINE ε #-}

postulate
  •η : δ ≡ ε

postulate
  SSnoc : (δ : Sub Δ Γ) → Tm Δ (A [ δ ]T) → Sub Δ (Γ ▷ A)
_,_ = SSnoc; {-# INLINE _,_ #-}

postulate
  SFst : Sub Δ (Γ ▷ A) → Sub Δ Γ
π₁ = SFst; {-# INLINE π₁ #-}

postulate
  SSnd : (δ : Sub Δ (Γ ▷ A)) → Tm Δ (A [ π₁ δ ]T)
π₂ = SSnd; {-# INLINE π₂ #-}

postulate
  ,⨾  : (δ , t) ⨾ σ ≡ (δ ⨾ σ) , (t [ σ ])
  {-# REWRITE ,⨾ #-}
  ▷β₁ : SFst (δ , t) ≡ δ
  {-# REWRITE ▷β₁ #-}
  ▷β₂ : SSnd (δ , t) ≡ t
  {-# REWRITE ▷β₂ #-}

  π₁⨾ : π₁ δ ⨾ σ ≡ π₁ (δ ⨾ σ)
  {-# REWRITE π₁⨾ #-}
  π₂[] : TmSub {A = ⟨ _ ⟩} (π₂ δ) σ ≡ π₂ (δ ⨾ σ)
  {-# REWRITE π₂[] #-}

  ▷η : π₁ δ , π₂ δ ≡ δ
  {-# REWRITE ▷η #-}

-- Dependent functions
-- We use binary application because it behaves better with rewriting
postulate
  Pi : (A : Ty Γ i) → Ty (Γ ▷ A) i → Ty Γ i
Π = Pi; {-# INLINE Π #-}

postulate
  Lam : Tm (Γ ▷ A) B → Tm Γ (Π A B)
  App : Tm Γ (Π A B) → (u : Tm Γ A) → Tm Γ (B [ id , u ]T)
lam = Lam; {-# INLINE lam #-}
app = App; {-# INLINE app #-}

wk : Sub (Γ ▷ A) Γ
wk = π₁ id
{-# COMPILE AGDA2HS wk #-}

vz : Tm (Γ ▷ A) (A [ wk ]T)
vz = π₂ id
{-# COMPILE AGDA2HS vz #-}

_^_ : ∀ δ (A : Ty Γ i) → Sub (Δ ▷ (A [ δ ]T)) (Γ ▷ A)
δ ^ _ = (δ ⨾ wk) , vz
{-# COMPILE AGDA2HS _^_ #-}

postulate
  Π[]   : Π A B [ δ ]T ≡ Π (A [ δ ]T) (B [ δ ^ A ]T)
  {-# REWRITE Π[] #-}
  lam[] : lam t [ δ ] ≡ lam (t [ δ ^ A ])
  {-# REWRITE lam[] #-}
  -- Unlike with unary Application, we cannot derive naturality
  app[] : TmSub {A = ⟨ _ ⟩} (app t u) δ ≡ app (t [ δ ]) (u [ δ ])
  {-# REWRITE app[] #-}

  Πβ : app (lam t) u ≡ t [ id , u ]
  {-# REWRITE Πβ #-}
  Πη : {t : Tm {i} Γ (Π A B)} → t ≡ lam (app (t [ wk ]) vz)

-- Dependent pairs
postulate
  Sigma : (A : Ty Γ i) → Ty (Γ ▷ A) i → Ty Γ i
Σ = Sigma; {-# INLINE Σ #-}

postulate
  Pair : (@0 B : Ty (Γ ▷ A) i) → (t : Tm Γ A) → Tm Γ (B [ id , t ]T) → Tm Γ (Σ A B)
  Fst  : Tm Γ (Σ A B) → Tm Γ A
  Snd  : (t : Tm Γ (Σ A B)) → Tm Γ (B [ id , Fst t ]T)
pair = Pair; {-# INLINE pair #-}
fst  = Fst;  {-# INLINE fst  #-}
snd  = Snd;  {-# INLINE snd  #-}

postulate
  Σ[]  : Σ A B [ δ ]T ≡ Σ (A [ δ ]T) (B [ δ ^ A ]T)
  {-# REWRITE Σ[] #-}
  pair[] : {δ : Sub Δ Γ}
         → pair B t u [ δ ] ≡ pair (B [ δ ^ A ]T) (t [ δ ]) (u [ δ ])
  {-# REWRITE pair[] #-}
  fst[] : fst {B = B} t [ δ ] ≡ fst (t [ δ ])
  {-# REWRITE fst[] #-}
  snd[] : {δ : Sub Δ Γ} → _[_] {A = ⟨ _ ⟩} (snd t) δ ≡ snd (t [ δ ])
  {-# REWRITE snd[] #-}

  Σβ₁ : fst (pair B t u) ≡ t
  {-# REWRITE Σβ₁ #-}
  Σβ₂ : snd (pair B t u) ≡ u
  {-# REWRITE Σβ₂ #-}
  Ση : pair B (fst t) (snd t) ≡ t
  {-# REWRITE Ση #-}

-- Universe
postulate
  U    : ∀ (@0 i) → Ty Γ (suc i)
  El   : Tm Γ (U i) → Ty Γ i
  Code : Ty Γ i → Tm Γ (U i)

  U[] : U i [ δ ]T ≡ U i
  {-# REWRITE U[] #-}
  El[] : El t [ δ ]T ≡ El (t [ δ ])
  {-# REWRITE El[] #-}
  Code[] : Code A [ δ ] ≡ Code (A [ δ ]T)
  {-# REWRITE Code[] #-}

  Uβ : El (Code A) ≡ A
  {-# REWRITE Uβ #-}
  Uη : Code (El t) ≡ t
  {-# REWRITE Uη #-}

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
  | Sigma Ty Ty
  | U
  | El Tm

data Tm
  = TmSub Tm Sub
  | SSnd Sub
  | Lam Tm
  | App Tm Tm
  | Pair Tm Tm
  | Fst Tm
  | Snd Tm
  | Code Ty

#-}

{-# COMPILE AGDA2HS Ctx            #-}
{-# COMPILE AGDA2HS Sub   existing #-}
{-# COMPILE AGDA2HS Ty    existing #-}
{-# COMPILE AGDA2HS Tm    existing #-}
{-# COMPILE AGDA2HS SId   existing #-}
{-# COMPILE AGDA2HS SNil  existing #-}
{-# COMPILE AGDA2HS SComp existing #-}
{-# COMPILE AGDA2HS SSnoc existing #-}
{-# COMPILE AGDA2HS SFst  existing #-}
{-# COMPILE AGDA2HS SSnd  existing #-}
{-# COMPILE AGDA2HS TySub existing #-}
{-# COMPILE AGDA2HS TmSub existing #-}
{-# COMPILE AGDA2HS Pi    existing #-}
{-# COMPILE AGDA2HS Lam   existing #-}
{-# COMPILE AGDA2HS App   existing #-}
{-# COMPILE AGDA2HS Sigma existing #-}
{-# COMPILE AGDA2HS Pair  existing #-}
{-# COMPILE AGDA2HS Fst   existing #-}
{-# COMPILE AGDA2HS Snd   existing #-}
{-# COMPILE AGDA2HS U     existing #-}
{-# COMPILE AGDA2HS El    existing #-}
{-# COMPILE AGDA2HS Code  existing #-}

{-# COMPILE AGDA2HS id    inline #-}
{-# COMPILE AGDA2HS _⨾_   inline #-}
{-# COMPILE AGDA2HS _[_]T inline #-}
{-# COMPILE AGDA2HS _[_]  inline #-}
{-# COMPILE AGDA2HS ε     inline #-}
{-# COMPILE AGDA2HS _,_   inline #-}
{-# COMPILE AGDA2HS π₁    inline #-}
{-# COMPILE AGDA2HS π₂    inline #-}
{-# COMPILE AGDA2HS Π     inline #-}
{-# COMPILE AGDA2HS lam   inline #-}
{-# COMPILE AGDA2HS app   inline #-}
{-# COMPILE AGDA2HS Σ     inline #-}
{-# COMPILE AGDA2HS pair  inline #-}
{-# COMPILE AGDA2HS fst   inline #-}
{-# COMPILE AGDA2HS snd   inline #-}
