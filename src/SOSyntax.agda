module SOSyntax where

{-# FOREIGN AGDA2HS

{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}

#-}

open import Utils
open import Agda.Builtin.Equality.Rewrite
open import Haskell.Prelude hiding ( id; a; b; c; d; e; f; m; s; t; _,_; fst; snd )

{-# FOREIGN AGDA2HS
import Prelude hiding ( (^) )
#-}

--------------------------------------------------------------------------------

postulate
  Ty : Type
  Tm : @0 Ty → Type

private variable
  ？ : Set _

variable
  @0 A B C D A₁ A₂ A₃ B₁ B₂ B₃  : Ty
  @0 t u v t₁ t₂ t₃ u₁ u₂ u₃ : Tm _
  @0 A[_] B[_] : ？ → Ty
  @0 t[_] u[_] : (□ : ？) → Tm A[ □ ]

-- Dependent functions
-- We use binary application because it behaves better with rewriting
postulate
  Pi    : (A : Ty) → (Tm A → Ty) → Ty
Π = Pi; {-# INLINE Π #-}

postulate
  Lam   : ((t : Tm A) → Tm (B[ t ])) → Tm (Π A B[_])
  App   : Tm (Π A B[_]) → (u : Tm A) → Tm (B[ u ])
lam = Lam; {-# INLINE lam #-}
app = App; {-# INLINE app #-}

postulate
  Πβ : app (lam t[_]) u ≡ t[ u ]
  {-# REWRITE Πβ #-}
  Πη : {t : Tm (Π A B[_])} → t ≡ lam λ u → app t u

postulate
  Sigma : (A : Ty) → (Tm A → Ty) → Ty
Σ = Sigma; {-# INLINE Π #-}

postulate
  Pair : (t : Tm A) → Tm B[ t ] → Tm (Σ A B[_])
  Fst  : Tm (Σ A B[_]) → Tm A
  Snd  : (t : Tm (Σ A B[_])) → Tm B[ Fst t ]
pair = Pair; {-# INLINE pair #-}
fst  = Fst;  {-# INLINE fst  #-}
snd  = Snd;  {-# INLINE snd  #-}

postulate
  Σβ₁ : fst (pair t u) ≡ t
  {-# REWRITE Σβ₁ #-}
  Σβ₂ : snd (pair t u) ≡ u
  {-# REWRITE Σβ₂ #-}
  Ση : pair (fst t) (snd t) ≡ t
  {-# REWRITE Ση #-}

{-# FOREIGN AGDA2HS

data Ty
  = Pi Ty (Tm -> Ty)
  | Sigma Ty (Tm -> Ty)

data Tm
  = Lam (Tm -> Tm)
  | App Tm Tm
  | Pair Tm Tm
  | Fst Tm
  | Snd Tm

#-}

{-# COMPILE AGDA2HS Ty    existing #-}
{-# COMPILE AGDA2HS Tm    existing #-}
{-# COMPILE AGDA2HS Pi    existing #-}
{-# COMPILE AGDA2HS Lam   existing #-}
{-# COMPILE AGDA2HS App   existing #-}
{-# COMPILE AGDA2HS Sigma existing #-}
{-# COMPILE AGDA2HS Pair  existing #-}
{-# COMPILE AGDA2HS Fst   existing #-}
{-# COMPILE AGDA2HS Snd   existing #-}

{-# COMPILE AGDA2HS Π    inline #-}
{-# COMPILE AGDA2HS lam  inline #-}
{-# COMPILE AGDA2HS app  inline #-}
{-# COMPILE AGDA2HS Σ    inline #-}
{-# COMPILE AGDA2HS pair inline #-}
{-# COMPILE AGDA2HS fst  inline #-}
{-# COMPILE AGDA2HS snd  inline #-}
