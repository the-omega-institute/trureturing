/- GID: D5/S3/Observer/CubicGain/RegularReadJacobian
   generality: I
   mirror-B: D5/B/S3/Observer/CubicGain/RegularReadJacobian
   mirror-E: none(waiver:actual-original-read-local-inverse)
   anchors: [mathlib/module/Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff]
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Observer/CubicGain/RegularReadInverse.actual_local_source_inverse; premises=D5/S3/Observer/CubicGain/RegularParentChart.strip_denominator
   digest: The actual fifth and eighth read pair has an invertible derivative throughout a source strip. -/

import D5.S3.Observer.CubicGain.RegularParentChart
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! The derivative belongs to the actual read map of the original whole world. -/

set_option maxRecDepth 4000
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Observer.CubicGain.RegularReadJacobian

open D5.S3.Observer.CubicGain RegularParentChart
open CommonWordSensitivity Module

private def row (a b : ℝ) : (ℝ × ℝ) →L[ℝ] ℝ :=
  a • ContinuousLinearMap.fst ℝ ℝ ℝ+b • ContinuousLinearMap.snd ℝ ℝ ℝ

private def dDt (x : ℝ × ℝ) : ℝ :=
    20*x.1^3*x.2^4 + 160*x.1^3*x.2^3 + 80*x.1^3*x.2^2 - 15*x.1^2*x.2^4 +
    -150*x.1^2*x.2^3 - 300*x.1^2*x.2^2 - 120*x.1^2*x.2 - 20*x.1*x.2^4 +
    -70*x.1*x.2^3 + 130*x.1*x.2^2 + 160*x.1*x.2 + 40*x.1 +
    5*x.2^4 + 30*x.2^3 + 30*x.2^2 - 30*x.2 +
    -20

private def dDb (x : ℝ × ℝ) : ℝ :=
    20*x.1^4*x.2^3 + 120*x.1^4*x.2^2 + 40*x.1^4*x.2 - 20*x.1^3*x.2^3 +
    -150*x.1^3*x.2^2 - 200*x.1^3*x.2 - 40*x.1^3 - 40*x.1^2*x.2^3 +
    -105*x.1^2*x.2^2 + 130*x.1^2*x.2 + 80*x.1^2 + 20*x.1*x.2^3 +
    90*x.1*x.2^2 + 60*x.1*x.2 - 30*x.1 + 20*x.2^3 +
    -80*x.2 - 20

private theorem derivative_D (x : ℝ × ℝ) :
    HasFDerivAt circuitD (row (dDt x) (dDb x)) x := by
  have h := (((((((hasFDerivAt_fst (𝕜 := ℝ) (p := x)).pow 4).mul ((hasFDerivAt_snd (𝕜 := ℝ) (p := x)).pow 4)).const_mul (5:ℝ)).add ((((hasFDerivAt_fst (𝕜 := ℝ) (p := x)).pow 4).mul ((hasFDerivAt_snd (𝕜 := ℝ) (p := x)).pow 3)).const_mul (40:ℝ))).add (((((hasFDerivAt_fst (𝕜 := ℝ) (p := x)).pow 4).mul ((hasFDerivAt_snd (𝕜 := ℝ) (p := x)).pow 2)).const_mul (20:ℝ)).add (((((hasFDerivAt_fst (𝕜 := ℝ) (p := x)).pow 3).mul ((hasFDerivAt_snd (𝕜 := ℝ) (p := x)).pow 4)).const_mul (-5:ℝ)).add ((((hasFDerivAt_fst (𝕜 := ℝ) (p := x)).pow 3).mul ((hasFDerivAt_snd (𝕜 := ℝ) (p := x)).pow 3)).const_mul (-50:ℝ))))).add ((((((hasFDerivAt_fst (𝕜 := ℝ) (p := x)).pow 3).mul ((hasFDerivAt_snd (𝕜 := ℝ) (p := x)).pow 2)).const_mul (-100:ℝ)).add ((((hasFDerivAt_fst (𝕜 := ℝ) (p := x)).pow 3).mul ((hasFDerivAt_snd (𝕜 := ℝ) (p := x)).pow 1)).const_mul (-40:ℝ))).add (((((hasFDerivAt_fst (𝕜 := ℝ) (p := x)).pow 2).mul ((hasFDerivAt_snd (𝕜 := ℝ) (p := x)).pow 4)).const_mul (-10:ℝ)).add (((((hasFDerivAt_fst (𝕜 := ℝ) (p := x)).pow 2).mul ((hasFDerivAt_snd (𝕜 := ℝ) (p := x)).pow 3)).const_mul (-35:ℝ)).add ((((hasFDerivAt_fst (𝕜 := ℝ) (p := x)).pow 2).mul ((hasFDerivAt_snd (𝕜 := ℝ) (p := x)).pow 2)).const_mul (65:ℝ)))))).add (((((((hasFDerivAt_fst (𝕜 := ℝ) (p := x)).pow 2).mul ((hasFDerivAt_snd (𝕜 := ℝ) (p := x)).pow 1)).const_mul (80:ℝ)).add ((((hasFDerivAt_fst (𝕜 := ℝ) (p := x)).pow 2).mul ((hasFDerivAt_snd (𝕜 := ℝ) (p := x)).pow 0)).const_mul (20:ℝ))).add (((((hasFDerivAt_fst (𝕜 := ℝ) (p := x)).pow 1).mul ((hasFDerivAt_snd (𝕜 := ℝ) (p := x)).pow 4)).const_mul (5:ℝ)).add (((((hasFDerivAt_fst (𝕜 := ℝ) (p := x)).pow 1).mul ((hasFDerivAt_snd (𝕜 := ℝ) (p := x)).pow 3)).const_mul (30:ℝ)).add ((((hasFDerivAt_fst (𝕜 := ℝ) (p := x)).pow 1).mul ((hasFDerivAt_snd (𝕜 := ℝ) (p := x)).pow 2)).const_mul (30:ℝ))))).add ((((((hasFDerivAt_fst (𝕜 := ℝ) (p := x)).pow 1).mul ((hasFDerivAt_snd (𝕜 := ℝ) (p := x)).pow 1)).const_mul (-30:ℝ)).add ((((hasFDerivAt_fst (𝕜 := ℝ) (p := x)).pow 1).mul ((hasFDerivAt_snd (𝕜 := ℝ) (p := x)).pow 0)).const_mul (-20:ℝ))).add (((((hasFDerivAt_fst (𝕜 := ℝ) (p := x)).pow 0).mul ((hasFDerivAt_snd (𝕜 := ℝ) (p := x)).pow 4)).const_mul (5:ℝ)).add (((((hasFDerivAt_fst (𝕜 := ℝ) (p := x)).pow 0).mul ((hasFDerivAt_snd (𝕜 := ℝ) (p := x)).pow 2)).const_mul (-40:ℝ)).add ((((hasFDerivAt_fst (𝕜 := ℝ) (p := x)).pow 0).mul ((hasFDerivAt_snd (𝕜 := ℝ) (p := x)).pow 1)).const_mul (-20:ℝ))))))
  convert h using 1
  · funext y
    dsimp [circuitD,circuitN,circuitJ]
    ring
  · apply ContinuousLinearMap.ext
    intro y
    simp [row,dDt,dDb,smul_eq_mul,nsmul_eq_mul]
    ring

private def dPt (x : ℝ × ℝ) : ℝ :=
    -4608*x.1^5*x.2^4 + 576*x.1^5*x.2^3 + 7680*x.1^4*x.2^4 + 10560*x.1^4*x.2^3 +
    -1440*x.1^4*x.2^2 + 8928*x.1^3*x.2^4 - 9504*x.1^3*x.2^3 - 5760*x.1^3*x.2^2 +
    1152*x.1^3*x.2 - 10944*x.1^2*x.2^4 - 16533*x.1^2*x.2^3 - 810*x.1^2*x.2^2 +
    -1152*x.1^2*x.2 - 288*x.1^2 - 2736*x.1*x.2^4 + 9738*x.1*x.2^3 +
    8448*x.1*x.2^2 + 3000*x.1*x.2 + 960*x.1 + 1872*x.2^4 +
    1437*x.2^3 - 1917*x.2^2 - 1125*x.2 - 390

private def dPb (x : ℝ × ℝ) : ℝ :=
    -3072*x.1^6*x.2^3 + 288*x.1^6*x.2^2 + 6144*x.1^5*x.2^3 + 6336*x.1^5*x.2^2 +
    -576*x.1^5*x.2 + 8928*x.1^4*x.2^3 - 7128*x.1^4*x.2^2 - 2880*x.1^4*x.2 +
    288*x.1^4 - 14592*x.1^3*x.2^3 - 16533*x.1^3*x.2^2 - 540*x.1^3*x.2 +
    -384*x.1^3 - 5472*x.1^2*x.2^3 + 14607*x.1^2*x.2^2 + 8448*x.1^2*x.2 +
    1500*x.1^2 + 7488*x.1*x.2^3 + 4311*x.1*x.2^2 - 3834*x.1*x.2 +
    -1125*x.1 - 864*x.2^3 - 6714*x.2^2 - 2790*x.2 +
    -390

private theorem derivative_P (x : ℝ × ℝ) :
    HasFDerivAt circuitP (row (dPt x) (dPb x)) x := by
  have h := (((((((hasFDerivAt_fst (𝕜 := ℝ) (p := x)).pow 6).mul ((hasFDerivAt_snd (𝕜 := ℝ) (p := x)).pow 4)).const_mul (-768:ℝ)).add (((((hasFDerivAt_fst (𝕜 := ℝ) (p := x)).pow 6).mul ((hasFDerivAt_snd (𝕜 := ℝ) (p := x)).pow 3)).const_mul (96:ℝ)).add ((((hasFDerivAt_fst (𝕜 := ℝ) (p := x)).pow 5).mul ((hasFDerivAt_snd (𝕜 := ℝ) (p := x)).pow 4)).const_mul (1536:ℝ)))).add ((((((hasFDerivAt_fst (𝕜 := ℝ) (p := x)).pow 5).mul ((hasFDerivAt_snd (𝕜 := ℝ) (p := x)).pow 3)).const_mul (2112:ℝ)).add ((((hasFDerivAt_fst (𝕜 := ℝ) (p := x)).pow 5).mul ((hasFDerivAt_snd (𝕜 := ℝ) (p := x)).pow 2)).const_mul (-288:ℝ))).add (((((hasFDerivAt_fst (𝕜 := ℝ) (p := x)).pow 4).mul ((hasFDerivAt_snd (𝕜 := ℝ) (p := x)).pow 4)).const_mul (2232:ℝ)).add ((((hasFDerivAt_fst (𝕜 := ℝ) (p := x)).pow 4).mul ((hasFDerivAt_snd (𝕜 := ℝ) (p := x)).pow 3)).const_mul (-2376:ℝ))))).add ((((((hasFDerivAt_fst (𝕜 := ℝ) (p := x)).pow 4).mul ((hasFDerivAt_snd (𝕜 := ℝ) (p := x)).pow 2)).const_mul (-1440:ℝ)).add (((((hasFDerivAt_fst (𝕜 := ℝ) (p := x)).pow 4).mul ((hasFDerivAt_snd (𝕜 := ℝ) (p := x)).pow 1)).const_mul (288:ℝ)).add ((((hasFDerivAt_fst (𝕜 := ℝ) (p := x)).pow 3).mul ((hasFDerivAt_snd (𝕜 := ℝ) (p := x)).pow 4)).const_mul (-3648:ℝ)))).add ((((((hasFDerivAt_fst (𝕜 := ℝ) (p := x)).pow 3).mul ((hasFDerivAt_snd (𝕜 := ℝ) (p := x)).pow 3)).const_mul (-5511:ℝ)).add ((((hasFDerivAt_fst (𝕜 := ℝ) (p := x)).pow 3).mul ((hasFDerivAt_snd (𝕜 := ℝ) (p := x)).pow 2)).const_mul (-270:ℝ))).add (((((hasFDerivAt_fst (𝕜 := ℝ) (p := x)).pow 3).mul ((hasFDerivAt_snd (𝕜 := ℝ) (p := x)).pow 1)).const_mul (-384:ℝ)).add ((((hasFDerivAt_fst (𝕜 := ℝ) (p := x)).pow 3).mul ((hasFDerivAt_snd (𝕜 := ℝ) (p := x)).pow 0)).const_mul (-96:ℝ)))))).add (((((((hasFDerivAt_fst (𝕜 := ℝ) (p := x)).pow 2).mul ((hasFDerivAt_snd (𝕜 := ℝ) (p := x)).pow 4)).const_mul (-1368:ℝ)).add (((((hasFDerivAt_fst (𝕜 := ℝ) (p := x)).pow 2).mul ((hasFDerivAt_snd (𝕜 := ℝ) (p := x)).pow 3)).const_mul (4869:ℝ)).add ((((hasFDerivAt_fst (𝕜 := ℝ) (p := x)).pow 2).mul ((hasFDerivAt_snd (𝕜 := ℝ) (p := x)).pow 2)).const_mul (4224:ℝ)))).add ((((((hasFDerivAt_fst (𝕜 := ℝ) (p := x)).pow 2).mul ((hasFDerivAt_snd (𝕜 := ℝ) (p := x)).pow 1)).const_mul (1500:ℝ)).add ((((hasFDerivAt_fst (𝕜 := ℝ) (p := x)).pow 2).mul ((hasFDerivAt_snd (𝕜 := ℝ) (p := x)).pow 0)).const_mul (480:ℝ))).add (((((hasFDerivAt_fst (𝕜 := ℝ) (p := x)).pow 1).mul ((hasFDerivAt_snd (𝕜 := ℝ) (p := x)).pow 4)).const_mul (1872:ℝ)).add ((((hasFDerivAt_fst (𝕜 := ℝ) (p := x)).pow 1).mul ((hasFDerivAt_snd (𝕜 := ℝ) (p := x)).pow 3)).const_mul (1437:ℝ))))).add ((((((hasFDerivAt_fst (𝕜 := ℝ) (p := x)).pow 1).mul ((hasFDerivAt_snd (𝕜 := ℝ) (p := x)).pow 2)).const_mul (-1917:ℝ)).add (((((hasFDerivAt_fst (𝕜 := ℝ) (p := x)).pow 1).mul ((hasFDerivAt_snd (𝕜 := ℝ) (p := x)).pow 1)).const_mul (-1125:ℝ)).add ((((hasFDerivAt_fst (𝕜 := ℝ) (p := x)).pow 1).mul ((hasFDerivAt_snd (𝕜 := ℝ) (p := x)).pow 0)).const_mul (-390:ℝ)))).add ((((((hasFDerivAt_fst (𝕜 := ℝ) (p := x)).pow 0).mul ((hasFDerivAt_snd (𝕜 := ℝ) (p := x)).pow 4)).const_mul (-216:ℝ)).add ((((hasFDerivAt_fst (𝕜 := ℝ) (p := x)).pow 0).mul ((hasFDerivAt_snd (𝕜 := ℝ) (p := x)).pow 3)).const_mul (-2238:ℝ))).add (((((hasFDerivAt_fst (𝕜 := ℝ) (p := x)).pow 0).mul ((hasFDerivAt_snd (𝕜 := ℝ) (p := x)).pow 2)).const_mul (-1395:ℝ)).add ((((hasFDerivAt_fst (𝕜 := ℝ) (p := x)).pow 0).mul ((hasFDerivAt_snd (𝕜 := ℝ) (p := x)).pow 1)).const_mul (-390:ℝ))))))
  convert h using 1
  · funext y
    dsimp [circuitP ,circuitC,circuitA,circuitD,circuitN,circuitJ]
    ring
  · apply ContinuousLinearMap.ext
    intro y
    simp [row,dPt,dPb,smul_eq_mul,nsmul_eq_mul]
    ring

private def dMt (x : ℝ × ℝ) : ℝ :=
    -71190*x.1^5*x.2^4 - 16380*x.1^5*x.2^3 + 59325*x.1^4*x.2^4 + 191625*x.1^4*x.2^3 +
    40950*x.1^4*x.2^2 + 424680*x.1^3*x.2^4 + 102960*x.1^3*x.2^3 - 140460*x.1^3*x.2^2 +
    -32760*x.1^3*x.2 - 313155*x.1^2*x.2^4 - 801936*x.1^2*x.2^3 - 282573*x.1^2*x.2^2 +
    8145*x.1^2*x.2 + 8190*x.1^2 - 178770*x.1*x.2^4 + 304998*x.1*x.2^3 +
    425820*x.1*x.2^2 + 130548*x.1*x.2 + 11880*x.1 + 75720*x.2^4 +
    91107*x.2^3 - 70998*x.2^2 - 56688*x.2 - 8688

private def dMb (x : ℝ × ℝ) : ℝ :=
    -47460*x.1^6*x.2^3 - 8190*x.1^6*x.2^2 + 47460*x.1^5*x.2^3 + 114975*x.1^5*x.2^2 +
    16380*x.1^5*x.2 + 424680*x.1^4*x.2^3 + 77220*x.1^4*x.2^2 - 70230*x.1^4*x.2 +
    -8190*x.1^4 - 417540*x.1^3*x.2^3 - 801936*x.1^3*x.2^2 - 188382*x.1^3*x.2 +
    2715*x.1^3 - 357540*x.1^2*x.2^3 + 457497*x.1^2*x.2^2 + 425820*x.1^2*x.2 +
    65274*x.1^2 + 302880*x.1*x.2^3 + 273321*x.1*x.2^2 - 141996*x.1*x.2 +
    -56688*x.1 - 19680*x.2^3 - 284562*x.2^2 - 115416*x.2 +
    -8688

private theorem derivative_M (x : ℝ × ℝ) :
    HasFDerivAt circuitM (row (dMt x) (dMb x)) x := by
  have h := (((((((hasFDerivAt_fst (𝕜 := ℝ) (p := x)).pow 6).mul ((hasFDerivAt_snd (𝕜 := ℝ) (p := x)).pow 4)).const_mul (-11865:ℝ)).add (((((hasFDerivAt_fst (𝕜 := ℝ) (p := x)).pow 6).mul ((hasFDerivAt_snd (𝕜 := ℝ) (p := x)).pow 3)).const_mul (-2730:ℝ)).add ((((hasFDerivAt_fst (𝕜 := ℝ) (p := x)).pow 5).mul ((hasFDerivAt_snd (𝕜 := ℝ) (p := x)).pow 4)).const_mul (11865:ℝ)))).add ((((((hasFDerivAt_fst (𝕜 := ℝ) (p := x)).pow 5).mul ((hasFDerivAt_snd (𝕜 := ℝ) (p := x)).pow 3)).const_mul (38325:ℝ)).add ((((hasFDerivAt_fst (𝕜 := ℝ) (p := x)).pow 5).mul ((hasFDerivAt_snd (𝕜 := ℝ) (p := x)).pow 2)).const_mul (8190:ℝ))).add (((((hasFDerivAt_fst (𝕜 := ℝ) (p := x)).pow 4).mul ((hasFDerivAt_snd (𝕜 := ℝ) (p := x)).pow 4)).const_mul (106170:ℝ)).add ((((hasFDerivAt_fst (𝕜 := ℝ) (p := x)).pow 4).mul ((hasFDerivAt_snd (𝕜 := ℝ) (p := x)).pow 3)).const_mul (25740:ℝ))))).add ((((((hasFDerivAt_fst (𝕜 := ℝ) (p := x)).pow 4).mul ((hasFDerivAt_snd (𝕜 := ℝ) (p := x)).pow 2)).const_mul (-35115:ℝ)).add (((((hasFDerivAt_fst (𝕜 := ℝ) (p := x)).pow 4).mul ((hasFDerivAt_snd (𝕜 := ℝ) (p := x)).pow 1)).const_mul (-8190:ℝ)).add ((((hasFDerivAt_fst (𝕜 := ℝ) (p := x)).pow 3).mul ((hasFDerivAt_snd (𝕜 := ℝ) (p := x)).pow 4)).const_mul (-104385:ℝ)))).add ((((((hasFDerivAt_fst (𝕜 := ℝ) (p := x)).pow 3).mul ((hasFDerivAt_snd (𝕜 := ℝ) (p := x)).pow 3)).const_mul (-267312:ℝ)).add ((((hasFDerivAt_fst (𝕜 := ℝ) (p := x)).pow 3).mul ((hasFDerivAt_snd (𝕜 := ℝ) (p := x)).pow 2)).const_mul (-94191:ℝ))).add (((((hasFDerivAt_fst (𝕜 := ℝ) (p := x)).pow 3).mul ((hasFDerivAt_snd (𝕜 := ℝ) (p := x)).pow 1)).const_mul (2715:ℝ)).add ((((hasFDerivAt_fst (𝕜 := ℝ) (p := x)).pow 3).mul ((hasFDerivAt_snd (𝕜 := ℝ) (p := x)).pow 0)).const_mul (2730:ℝ)))))).add (((((((hasFDerivAt_fst (𝕜 := ℝ) (p := x)).pow 2).mul ((hasFDerivAt_snd (𝕜 := ℝ) (p := x)).pow 4)).const_mul (-89385:ℝ)).add (((((hasFDerivAt_fst (𝕜 := ℝ) (p := x)).pow 2).mul ((hasFDerivAt_snd (𝕜 := ℝ) (p := x)).pow 3)).const_mul (152499:ℝ)).add ((((hasFDerivAt_fst (𝕜 := ℝ) (p := x)).pow 2).mul ((hasFDerivAt_snd (𝕜 := ℝ) (p := x)).pow 2)).const_mul (212910:ℝ)))).add ((((((hasFDerivAt_fst (𝕜 := ℝ) (p := x)).pow 2).mul ((hasFDerivAt_snd (𝕜 := ℝ) (p := x)).pow 1)).const_mul (65274:ℝ)).add ((((hasFDerivAt_fst (𝕜 := ℝ) (p := x)).pow 2).mul ((hasFDerivAt_snd (𝕜 := ℝ) (p := x)).pow 0)).const_mul (5940:ℝ))).add (((((hasFDerivAt_fst (𝕜 := ℝ) (p := x)).pow 1).mul ((hasFDerivAt_snd (𝕜 := ℝ) (p := x)).pow 4)).const_mul (75720:ℝ)).add ((((hasFDerivAt_fst (𝕜 := ℝ) (p := x)).pow 1).mul ((hasFDerivAt_snd (𝕜 := ℝ) (p := x)).pow 3)).const_mul (91107:ℝ))))).add ((((((hasFDerivAt_fst (𝕜 := ℝ) (p := x)).pow 1).mul ((hasFDerivAt_snd (𝕜 := ℝ) (p := x)).pow 2)).const_mul (-70998:ℝ)).add (((((hasFDerivAt_fst (𝕜 := ℝ) (p := x)).pow 1).mul ((hasFDerivAt_snd (𝕜 := ℝ) (p := x)).pow 1)).const_mul (-56688:ℝ)).add ((((hasFDerivAt_fst (𝕜 := ℝ) (p := x)).pow 1).mul ((hasFDerivAt_snd (𝕜 := ℝ) (p := x)).pow 0)).const_mul (-8688:ℝ)))).add ((((((hasFDerivAt_fst (𝕜 := ℝ) (p := x)).pow 0).mul ((hasFDerivAt_snd (𝕜 := ℝ) (p := x)).pow 4)).const_mul (-4920:ℝ)).add ((((hasFDerivAt_fst (𝕜 := ℝ) (p := x)).pow 0).mul ((hasFDerivAt_snd (𝕜 := ℝ) (p := x)).pow 3)).const_mul (-94854:ℝ))).add (((((hasFDerivAt_fst (𝕜 := ℝ) (p := x)).pow 0).mul ((hasFDerivAt_snd (𝕜 := ℝ) (p := x)).pow 2)).const_mul (-57708:ℝ)).add ((((hasFDerivAt_fst (𝕜 := ℝ) (p := x)).pow 0).mul ((hasFDerivAt_snd (𝕜 := ℝ) (p := x)).pow 1)).const_mul (-8688:ℝ))))))
  convert h using 1
  · funext y
    dsimp [circuitM ,circuitC,circuitA,circuitD,circuitN,circuitJ]
    ring
  · apply ContinuousLinearMap.ext
    intro y
    simp [row,dMt,dMb,smul_eq_mul,nsmul_eq_mul]
    ring

private def termSum (cs : List (ℤ × ℕ × ℕ)) (u v : ℝ) : ℝ :=
  (cs.map (fun c => (c.1:ℝ)*u^c.2.1*v^c.2.2)).sum

private theorem termSum_upper (cs : List (ℤ × ℕ × ℕ)) (u v : ℝ)
    (hu : 0 ≤ u) (hu' : u ≤ 1) (hv : 0 ≤ v) (hv' : v ≤ 1) :
    termSum cs u v ≤ ((cs.map (fun c => max c.1 0)).sum : ℤ) := by
  induction cs with
  | nil => simp [termSum]
  | cons c cs ih =>
    have hp0 : 0 ≤ u^c.2.1*v^c.2.2 := mul_nonneg (pow_nonneg hu _) (pow_nonneg hv _)
    have hp1 : u^c.2.1*v^c.2.2 ≤ 1 :=
      mul_le_one₀ (pow_le_one₀ hu hu') (pow_nonneg hv _) (pow_le_one₀ hv hv')
    have hc : (c.1:ℝ)*u^c.2.1*v^c.2.2 ≤ (max c.1 0:ℤ) := by
      rw [mul_assoc]
      by_cases hz : 0 ≤ c.1
      · rw [max_eq_left hz]
        exact mul_le_of_le_one_right (by exact_mod_cast hz) hp1
      · rw [max_eq_right (le_of_not_ge hz),Int.cast_zero]
        change (c.1:ℝ)*(u^c.2.1*v^c.2.2) ≤ 0
        exact mul_nonpos_of_nonpos_of_nonneg (by exact_mod_cast le_of_not_ge hz) hp0
    simpa only [termSum,List.map_cons,List.sum_cons,Int.cast_add] using add_le_add hc ih

private def jacobianTerms : List (ℤ × ℕ × ℕ) := [
  (-89880000000000000000,15,2), (-74197378080000000000000000,15,1), (-4527180690772320000000000000000,15,0),
  (134288000000000000000,14,3), (37397397912000000000000000,14,2), (-2002973583916704000000000000000,14,1),
  (-248799763730098544544000000000000000,14,0), (-126084700000000000000,13,4), (-10677426250400000000000000,13,3),
  (1607350500109015200000000000000,13,2), (19742696003265612854400000000000000,13,1), (-5536100928843540254746411200000000000000,13,0),
  (34889247750000000000,12,5), (-1908256566527500000000000,12,4), (-596513021045953690000000000000,12,3),
  (22326181177051659418980000000000000,12,2), (1417682302233559254135957420000000000000,12,1), (-60922056226040172365622042952728000000000000,12,0),
  (-1498649175000000000,11,6), (1291482154817100000000000,11,5), (49477817872960579500000000000,11,4),
  (-10696607461700949949452000000000000,11,3), (51422352753469798252613238000000000000,11,2), (22577111780088657218468062677201600000000000,11,1),
  (-287842964227989948153603602497421611200000000000,11,0), (-664795670000000000,10,7), (-119428787134645000000000,10,6),
  (17773693854338517520000000000,10,5), (1490714773848029674991100000000000,10,4), (-89923328828537831811265511200000000000,10,3),
  (-1701564775173792751332962665115760000000000,10,2), (164283394927984942452064448206283792640000000000,10,1), (384591569163217308745553128157558855012160000000000,10,0),
  (78959890250000000,9,8), (-13768726095024000000000,9,7), (-2657352984710747797000000000,9,6),
  (119570152985827349103748000000000,9,5), (15238530229669650198521659980000000000,9,4), (-375541277359830014815206590292128000000000,9,3),
  (-19087136281950952768838481596135182512000000000,9,2), (450478855712447255182491209935918622036544000000000,9,1), (9371782310753994349288195591317243665115404544000000000,9,0),
  (1854498325000000,8,9), (1901053049484400000000,8,8), (-137699666068247139200000000,8,7),
  (-30987697624153387173753400000000,8,6), (461929128271874645738745349200000000,8,5), (80831119184509261709831021180913600000000,8,4),
  (-936255939837092465955659747402721820800000000,8,3), (-91336285425549244812896744347173306064905600000000,8,2), (-1102502251567562931344237014843247409323852851200000000,8,1),
  (21090818171634324337854683769153821644977299576985600000000,8,0), (-602592285000000,7,10), (54335260612700000000,7,9),
  (21523902190388807700000000,7,8), (-1529874445530742812958400000000,7,7), (-273363944052357586622714451600000000,7,6),
  (-563920660080467322392394816941760000000,7,5), (270713642380761762173573176368450145600000000,7,4), (-3056752939903393824836739998874787334310400000000,7,3),
  (-266107384194115857618715677434805691067449459200000000,7,2), (-9831290390263347118854629550943705061140859177932800000000,7,1), (-87298770950360289831250200874156383616487995416362403840000000,7,0),
  (15905506250000,6,11), (-6375375523862500000,6,10), (1909496492513833375000000,6,9),
  (305058136394828996551250000000,6,8), (-7461167146373879607230491000000000,6,7), (-1756834861043193141806949705970400000000,6,6),
  (-33263091398201273274517346725974736800000000,6,5), (497337176230785705567230954844192921632000000000,6,4), (-647235111603797373005981252936688082343480000000000,6,3),
  (-499716508367986527857954487171236775553057184688000000000,6,2), (-14318389664438316295363174598319069692930734396664505600000000,6,1), (-290849307534985519815129909778753110498437449999706291827200000000,6,0),
  (432256775000,5,12), (-641855824087100000,5,11), (-126452253040728157400000,5,10),
  (19000991781076352243386000000,5,9), (3246474719364020269429076198000000,5,8), (68721284727459031666697675908534400000,5,7),
  (-4271364238734307764460985684832483145600000,5,6), (-181263669945979546474792680030871759316198400000,5,5), (-472553447115077363543894870355679645602616992000000,5,4),
  (96022190046215401536389608729250931096798221651584000000,5,3), (1446046785582463719704296711650457785201492763402568601600000,5,2), (38403642155150789942880359930243768980747492285187753439129600000,5,1),
  (499443101765410455030828904790589685413805817361716904282973286400000,5,0), (6875930000,4,13), (21140870788595000,4,12),
  (-11454987608778468690000,4,11), (-1865524557041019911650740000,4,10), (33342580155166652425078310200000,4,9),
  (15887276085895703331427991945746880000,4,8), (813544601422032113132784895166062486720000,4,7), (17697020154111329773280721309613433416053760000,4,6),
  (224182886317574326444448000176374081119263282560000,4,5), (6846757614818310108286944276631211882078611556633600000,4,4), (454491222194665756802902003632156381191798820953813547520000,4,3),
  (11919404852969046073157484278386534463730976857116991350983680000,4,2), (134435479260667684660479221461349352514735771473895139554903818240000,4,1), (1198041249125259334705574991814767266133354075167620708217224873635840000,4,0),
  (3945847750,3,14), (3572149506923000,3,13), (726986635602449571000,3,12),
  (-14357825523940554897328000,3,11), (-7415174007987985119108217916000,3,10), (-37371543846733044851414249663856000,3,9),
  (42221785770060488292452962448140557328000,3,8), (2977060828860479839444256911621855004397056000,3,7), (113366006772309247056005047128092857311713489792000,3,6),
  (3236308075965106819655475617153527413551997433601024000,3,5), (68139561584703530356934322106508850755610556073663159296000,3,4), (880460032566405780561625779598823949843045677527721500260352000,3,3),
  (10614686456458727424878826843994967015219183468500767203808405504000,3,2), (9334826851867590908192682873182731959210086130792124630428341526528000,3,1), (-2109166135071667096245440738079730719560318049297550082170370876583542784000,3,0),
  (-504284925,2,15), (-165931386631000,2,14), (-4882505949575663500,2,13),
  (572767088576384278812000,2,12), (-211402172457202453287418492000,2,11), (-31295019200701590859388253050207200,2,10),
  (-818498076636140953037481635790870736000,2,9), (57256512101785543480429290086656066846704000,2,8), (4568105789253644121486673440284753517159398112000,2,7),
  (141739610174230728967017562953537084186073246840128000,2,6), (2321969014895084230879898736419784852243736834890066150400,2,5), (17437254554177559390126248772504174329208291066715368330496000,2,4),
  (-715194863367600534485487379041826969345181063442095046124539904000,2,3), (-35663244575633625692261292848239508733393565078481844218403260393472000,2,2), (-380510255709201438365964953598667804954409720187373555613860486673522688000,2,1),
  (455663638672234018442764585441401009469890293387334833446591999889659143782400,2,0), (9885645,1,16), (1350762443310,1,15),
  (335409995933462350,1,14), (96187950533772855874400,1,13), (5192523638966696818979214400,1,12),
  (-1016672407929724335848556390627520,1,11), (-166049209777514397149798272431371428960,1,10), (-11089463263243057290661411549888241174582400,1,9),
  (-459168253265986747620347167551768352215565161600,1,8), (-15309496373255712663082534407036028720670503370713600,1,7), (-513315867299661471560431765890378298389284763226976348160,1,6),
  (-16906012589555274879624750384400473372105941619342385249658880,1,5), (-426687231045955515655503637767687393681073393332486069110212249600,1,4), (-6244407355774742431096449414951606601993095035994493144697144417894400,1,3),
  (-34902126968484170658429619728672664157790321623974171315126032439060070400,1,2), (40864454257376505963585688420929555180750324504062440378361688244695570186240,1,1), (-6370735328567323736650324454711245616086767011512299916358202722763131458682880,1,0),
  (244206,0,17), (-9471454259,0,16), (-7584881433187301,0,15),
  (1001007183228161056460,0,14), (435999324090778906112351380,0,13), (45407128562834460986889237090104,0,12),
  (1180084978323060984195710309326424064,0,11), (-173587012789315173758113596184529389013024,0,10), (-22867860171557221613280316593189536578732514240,0,9),
  (-1484031495824335135564777359879499746997068089585920,0,8), (-63057105837280179750064384661971925724742775548566930688,0,7), (-1804208532567530221606621899086708592229969425784022682254848,0,6),
  (-33128546103154272705410058751713986242743343070782755574754926592,0,5), (-347767261358594818819165916848552719034495523053047418358453163919360,0,4), (-1554114103666492318831037920399205686745110015048384210133809673189703680,0,3),
  (140994113379722523693743517617405413072040978106453383039919011789866893312,0,2), (-626525120983823919663324587924848970556751025503446985907751600922522826047488,0,1)
]

private def jacobianConstant : ℤ := -17363682599213667759388570078413802375620887361457856838728078795232967825293312
private def jacobianScale : ℝ := 1250000000000000000000000000000000000000000000000000000000000000000000000000000000000

private def core (x : ℝ × ℝ) : ℝ :=
  ((jacobianConstant : ℝ)+termSum jacobianTerms
    (10000*(x.1*x.2)-9005) (100000*x.2-12758))/jacobianScale

private theorem core_negative (x : ℝ × ℝ)
    (hr : 9005/10000 ≤ x.1*x.2) (hr' : x.1*x.2 ≤ 9006/10000)
    (hb : 12758/100000 ≤ x.2) (hb' : x.2 ≤ 12759/100000) : core x < 0 := by
  have h := termSum_upper jacobianTerms (10000*(x.1*x.2)-9005)
    (100000*x.2-12758) (by linarith) (by linarith) (by linarith) (by linarith)
  have hn : (jacobianConstant:ℝ)+termSum jacobianTerms
      (10000*(x.1*x.2)-9005) (100000*x.2-12758) < 0 := by
    norm_num [jacobianTerms,jacobianConstant] at h ⊢
    linarith
  exact div_neg_of_neg_of_pos hn (by norm_num [jacobianScale])

private theorem core_identity (x : ℝ × ℝ) :
    x.2^7*((circuitD x*dPt x-circuitP x*dDt x)*
      (circuitD x*dMb x-circuitM x*dDb x)-
      (circuitD x*dPb x-circuitP x*dDb x)*
      (circuitD x*dMt x-circuitM x*dDt x)) = 45*circuitD x*core x := by
  norm_num [core,jacobianConstant,jacobianScale,termSum,jacobianTerms,
    circuitD,circuitP,circuitM,circuitC,circuitA,circuitJ,circuitN,dPt,dPb,dMt,dMb,dDt,dDb]
  ring

private def qPt (x : ℝ × ℝ) : ℝ :=
  (circuitD x*dPt x-circuitP x*dDt x)/(circuitD x)^2
private def qPb (x : ℝ × ℝ) : ℝ :=
  (circuitD x*dPb x-circuitP x*dDb x)/(circuitD x)^2
private def qMt (x : ℝ × ℝ) : ℝ :=
  (circuitD x*dMt x-circuitM x*dDt x)/(circuitD x)^2
private def qMb (x : ℝ × ℝ) : ℝ :=
  (circuitD x*dMb x-circuitM x*dDb x)/(circuitD x)^2

private def readDerivative (x : ℝ × ℝ) : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  (row (qPt x) (qPb x)).prod (row (qMt x) (qMb x))

private theorem rational_derivative (x : ℝ × ℝ) (hd : circuitD x ≠ 0) :
    HasFDerivAt (fun y => (circuitP y/circuitD y,circuitM y/circuitD y))
      (readDerivative x) x := by
  have hi := (hasDerivAt_inv hd).comp_hasFDerivAt x (derivative_D x)
  have hp := (derivative_P x).mul hi
  have hm := (derivative_M x).mul hi
  have hp' : HasFDerivAt (fun y => circuitP y/circuitD y) (row (qPt x) (qPb x)) x := by
    convert hp using 1
    · funext y
      exact div_eq_mul_inv _ _
    · apply ContinuousLinearMap.ext
      intro y
      simp [row,qPt,qPb]
      field_simp [hd]
      <;> ring
  have hm' : HasFDerivAt (fun y => circuitM y/circuitD y) (row (qMt x) (qMb x)) x := by
    convert hm using 1
    · funext y
      exact div_eq_mul_inv _ _
    · apply ContinuousLinearMap.ext
      intro y
      simp [row,qMt,qMb]
      field_simp [hd]
      <;> ring
  exact hp'.prodMk hm'

private theorem actual_derivative (x : ℝ × ℝ)
    (hr : 0 < x.1*x.2) (hr' : x.1*x.2 < 1) (hb : 0 < x.2)
    (hl : parentLambda (x.1*x.2) x.2 ≠ 0) :
    HasFDerivAt chartRead (readDerivative x) x := by
  obtain ⟨hj,hn,ht,hu⟩ := source_positivity (x.1*x.2) x.2 hr.le hr'.le hb
  have hJ : ContinuousAt (fun y : ℝ × ℝ => sourceJ (y.1*y.2) y.2) x := by
    unfold sourceJ
    fun_prop (disch := exact ne_of_gt hb)
  have hN : ContinuousAt (fun y : ℝ × ℝ => sourceN (y.1*y.2) y.2) x := by
    unfold sourceN
    fun_prop
  have hL : ContinuousAt (fun y : ℝ × ℝ => parentLambda (y.1*y.2) y.2) x := by
    unfold parentLambda
    fun_prop (disch := first | exact ne_of_gt hj | exact ne_of_gt hn | exact ne_of_gt ht | exact ne_of_gt hu)
  have hc : ContinuousAt (fun y : ℝ × ℝ => y.1*y.2) x := by fun_prop
  have heq : chartRead =ᶠ[nhds x] (fun y => (circuitP y/circuitD y,circuitM y/circuitD y)) := by
    filter_upwards [continuousAt_const.eventually_lt hc hr,
      hc.eventually_lt continuousAt_const hr',
      continuousAt_const.eventually_lt continuousAt_snd hb,hL.eventually_ne hl]
      with y hyr hyr' hyb hyl
    exact regular_actual_read_correspondence y hyr hyr' hyb hyl
  exact (rational_derivative x (regular_whole_gain_correspondence x hr hr' hb hl).1).congr_of_eventuallyEq heq

/-- The derivative of the actual original read pair is invertible on the full
closed source strip. Its determinant is proved from the polynomial circuit,
not assumed as a condition and not replaced by a univariate root derivative. -/
theorem actual_jacobian_nonsingular (x : ℝ × ℝ)
    (hr : 9005/10000 ≤ x.1*x.2) (hr' : x.1*x.2 ≤ 9006/10000)
    (hb : 12758/100000 ≤ x.2) (hb' : x.2 ≤ 12759/100000) :
    (fderiv ℝ chartRead x).det ≠ 0 ∧
    ∃ e : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ), HasFDerivAt chartRead (e : _ →L[ℝ] _) x := by
  have hr0 : 0 < x.1*x.2 := by linarith
  have hr1 : x.1*x.2 < 1 := by linarith
  have hb0 : 0 < x.2 := by linarith
  have hl := ne_of_lt (strip_denominator _ _ hr hr' hb hb')
  have hd := (regular_whole_gain_correspondence x hr0 hr1 hb0 hl).1
  have hk := core_negative x hr hr' hb hb'
  have hn : (circuitD x*dPt x-circuitP x*dDt x)*
      (circuitD x*dMb x-circuitM x*dDb x)-
      (circuitD x*dPb x-circuitP x*dDb x)*
      (circuitD x*dMt x-circuitM x*dDt x) ≠ 0 := by
    intro hz
    have he := core_identity x
    rw [hz,mul_zero] at he
    exact (mul_ne_zero (mul_ne_zero (by norm_num) hd) (ne_of_lt hk)) he.symm
  have hq : qPt x*qMb x-qPb x*qMt x ≠ 0 := by
    have he : qPt x*qMb x-qPb x*qMt x =
        ((circuitD x*dPt x-circuitP x*dDt x)*
          (circuitD x*dMb x-circuitM x*dDb x)-
          (circuitD x*dPb x-circuitP x*dDb x)*
          (circuitD x*dMt x-circuitM x*dDt x))/(circuitD x)^4 := by
      unfold qPt qPb qMt qMb
      field_simp [hd]
      <;> ring
    rw [he]
    exact div_ne_zero hn (pow_ne_zero _ hd)
  have hm : readDerivative x =
      (Matrix.toLin (Basis.finTwoProd ℝ) (Basis.finTwoProd ℝ)
        !![qPt x,qPb x;qMt x,qMb x]).toContinuousLinearMap := by
    symm
    exact Matrix.toLin_finTwoProd_toContinuousLinearMap _ _ _ _
  have hdet : (readDerivative x).det ≠ 0 := by
    rw [hm]
    change (Matrix.toLin (Basis.finTwoProd ℝ) (Basis.finTwoProd ℝ)
      !![qPt x,qPb x;qMt x,qMb x]).det ≠ 0
    simpa [LinearMap.det_toLin, Matrix.det_fin_two] using hq
  have hactual := actual_derivative x hr0 hr1 hb0 hl
  refine ⟨by simpa only [hactual.fderiv] using hdet,?_⟩
  let e := (readDerivative x).toContinuousLinearEquivOfDetNeZero hdet
  refine ⟨e,?_⟩
  simpa only [e,ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero] using hactual

#print axioms actual_jacobian_nonsingular

end D5.S3.Observer.CubicGain.RegularReadJacobian
