{-# OPTIONS --show-implicit #-}

module Nf.FromSpine where

import Syntax as I
open I.Vars
import Nf.Traditional as Tr
import Nf.Spinal as Sp
open import Nf.Common

open import Haskell.Prelude using (_×_; _,_; case_of_; Type; Nat)
open import Haskell.Extra.Erase

--------------------------------------------------------------------------------

fromSpNf   : Sp.Nf Γ A t → Tr.Nf Γ A t
fromSpElim : Tr.Ne Γ A t → Sp.Elim Γ A B t u → Tr.Ne Γ B u
fromSpSp   : Tr.Ne Γ A t → Sp.Sp Γ A B t u → Tr.Ne Γ B u
fromSpTyNf : Sp.TyNf Γ i A → Tr.TyNf Γ i A

fromSpNf (Sp.lam t)      = Tr.lam (fromSpNf t)
fromSpNf (Sp.pair b t u) = Tr.pair (fromSpTyNf b) (fromSpNf t) (fromSpNf u)
fromSpNf (Sp.Code a)     = Tr.Code (fromSpTyNf a)
fromSpNf (Sp.raise t)    = Tr.raise (fromSpNf t)

fromSpElim t (Sp.App u) = Tr.App t (fromSpNf u)
fromSpElim t Sp.Fst     = Tr.Fst t
fromSpElim t Sp.Snd     = Tr.Snd t
fromSpElim t Sp.Lower   = Tr.Lower t

fromSpSp t Sp.[]       = t
fromSpSp t (e Sp.,- δ) = fromSpSp (fromSpElim t e) δ

fromSpTyNf (Sp.Π a b)   = Tr.Π (fromSpTyNf a) (fromSpTyNf b)
fromSpTyNf (Sp.Σ a b)   = Tr.Σ (fromSpTyNf a) (fromSpTyNf b)
fromSpTyNf (Sp.U i)     = Tr.U i
fromSpTyNf (Sp.El x sp) = Tr.El (fromSpSp (Tr.VarNe x) sp)
fromSpTyNf (Sp.Lift a)  = Tr.Lift (fromSpTyNf a)

{-# COMPILE AGDA2HS fromSpNf   #-}
{-# COMPILE AGDA2HS fromSpElim #-}
{-# COMPILE AGDA2HS fromSpSp   #-}
{-# COMPILE AGDA2HS fromSpTyNf #-}
