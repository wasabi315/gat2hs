{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}

module Syntax (Ctx (..), Sub (..), Ty (..), Tm (..), sid, scomp, tysub, tmsub, ssnoc, sfst, ssnd, pi, lam, app, wk, vz, (^)) where

import Prelude hiding (pi, (^))

data Ctx
  = CNil
  | CSnoc Ctx Ty

wk :: Sub
wk = sfst sid

vz :: Tm
vz = ssnd sid

(^) :: Sub -> Ty -> Sub
δ ^ _ = ssnoc (scomp δ wk) vz

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
