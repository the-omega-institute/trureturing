/- GID: D5/S3/Analytic/GaussZeroBalanced/ParamDeriv
   generality: G
   mirror-B: D5/B/S3/Analytic/GaussZeroBalanced/ParamDeriv
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Calculus.Deriv.Inv, mathlib/module/Mathlib.Tactic]
   utility: none
   digest: Parameter quotient differentiation and the differentiated Riccati identity. -/

import D5.S3.Analytic.GaussZeroBalanced.Series
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic

noncomputable section
open Set Filter
open scoped Topology
open D5.S3.Analytic.GaussZeroBalanced.Defs
open D5.S3.Analytic.GaussZeroBalanced.Series

namespace D5.S3.Analytic.GaussZeroBalanced.ParamDeriv

/-! The quotient rule in the parameter is isolated so that the two Gauss
parameter series can be supplied by the eventual termwise parameter proof. -/
theorem hasDerivAt_f_param_of_gauss {a b x dN dD : ℝ}
    (hN : HasDerivAt (fun β : ℝ => gauss a β (a + β + 1) x) dN b)
    (hD : HasDerivAt (fun β : ℝ => gauss a β (a + β) x) dD b)
    (hD0 : gauss a b (a + b) x ≠ 0) :
    HasDerivAt (fun β : ℝ => f a β x)
      ((dN * gauss a b (a + b) x -
          gauss a b (a + b + 1) x * dD) /
        (gauss a b (a + b) x) ^ 2) b := by
  change HasDerivAt
    ((fun β : ℝ => gauss a β (a + β + 1) x) /
      (fun β : ℝ => gauss a β (a + β) x)) _ b
  exact hN.div hD hD0

/-! Differentiating the Riccati relation is a local algebraic step.  The
identity is stated for arbitrary functions; this keeps the parameter-series
argument separate from the calculus used by the classification. -/
theorem parameter_riccati_deriv {a b x : ℝ} {F K : ℝ → ℝ}
    (ha : 0 < a) (hb : 0 < b) (hx : x ≠ 1)
    (hF : HasDerivAt F (deriv F b) b)
    (hK : HasDerivAt K (deriv K b) b)
    (hEq : ∀ β : ℝ,
      x * K β = (a + β) * (1 - F β) -
        (a * β / (a + β)) * (x / (1 - x)) * (F β) ^ 2) :
    x * deriv K b +
        ((a + b) + 2 * (a * b / (a + b)) * (x / (1 - x)) * F b) * deriv F b =
      (1 - F b) - (a ^ 2 / (a + b) ^ 2) * (x / (1 - x)) * (F b) ^ 2 := by
  have hab : a + b ≠ 0 := by positivity
  have h1 : 1 - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  have hc : HasDerivAt (fun β : ℝ => a + β) 1 b := by
    convert (hasDerivAt_const b a).add (hasDerivAt_id b) using 1
    · funext β
      rfl
    · norm_num
  have h1F : HasDerivAt (fun β : ℝ => 1 - F β) (-deriv F b) b := by
    convert (hasDerivAt_const b (1 : ℝ)).sub hF using 1
    ring
  have hleft : HasDerivAt (fun β : ℝ => x * K β) (x * deriv K b) b :=
    hK.const_mul x
  have hcoef : HasDerivAt (fun β : ℝ => a * β / (a + β))
      (a ^ 2 / (a + b) ^ 2) b := by
    have hn : HasDerivAt (fun β : ℝ => a * β) a b := by
      convert (hasDerivAt_const b a).mul (hasDerivAt_id b) using 1
      · funext β
        rfl
      · ring
    have hd := hn.div hc hab
    convert hd using 1
    field_simp <;> ring
  have hsq : HasDerivAt (fun β => (F β) ^ 2) (2 * F b * deriv F b) b := by
    convert hF.pow 2 using 1 <;> ring
  have hright : HasDerivAt
      (fun β => (a + β) * (1 - F β) -
        (a * β / (a + β)) * (x / (1 - x)) * (F β) ^ 2)
      ((1 - F b) - (a + b) * deriv F b -
        (a ^ 2 / (a + b) ^ 2) * (x / (1 - x)) * (F b) ^ 2 -
        (a * b / (a + b)) * (x / (1 - x)) * (2 * F b * deriv F b)) b := by
    have hp := hc.mul h1F
    have hq := (hcoef.const_mul (x / (1 - x))).mul hsq
    have hs := hp.sub hq
    convert hs using 1
    · funext β
      dsimp
      ring
    · ring
  have heq : (fun β => x * K β) =ᶠ[𝓝 b]
      (fun β => (a + β) * (1 - F β) -
        (a * β / (a + β)) * (x / (1 - x)) * (F β) ^ 2) :=
    Filter.Eventually.of_forall (fun β => hEq β)
  have hder := hleft.congr_of_eventuallyEq heq.symm
  have hder' := hder.deriv
  rw [hright.deriv] at hder'
  linear_combination -hder'

end D5.S3.Analytic.GaussZeroBalanced.ParamDeriv
