/- GID: D5/S3/Quantum/Analysis/RefinedBMVExtremeDerivatives
   generality: G
   mirror-B: none(waiver:internal-analytic-identity)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact square-root derivative identities for the extreme centered BMV kernel. -/

import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Set

open Filter
open scoped Topology

namespace RefinedBMV.Extreme

noncomputable section

private theorem hasDerivAt_div_sqrt {f r : ℝ → ℝ} {df dr x : ℝ}
    (hf : HasDerivAt f df x) (hr : HasDerivAt r dr x) (hrx : 0 < r x) :
    HasDerivAt (fun u ↦ f u / Real.sqrt (r u))
      ((2 * r x * df - dr * f x) / (2 * r x * Real.sqrt (r x))) x := by
  have hs : Real.sqrt (r x) ≠ 0 := (Real.sqrt_pos.2 hrx).ne'
  refine (hf.fun_div (hr.sqrt hrx.ne') hs).congr_deriv ?_
  set s := Real.sqrt (r x)
  have hsquare : s ^ 2 = r x := Real.sq_sqrt hrx.le
  rw [← hsquare]
  field_simp [hs] <;> ring

private theorem hasDerivAt_sqrt_reciprocal {f q : ℝ → ℝ} {df dq x : ℝ}
    (hf : HasDerivAt f df x) (hq : HasDerivAt q dq x) (hqx : 0 < q x) :
    HasDerivAt (fun u ↦ f u / Real.sqrt (q u))
      (df / Real.sqrt (q x) - f x * dq / (2 * (Real.sqrt (q x))^3)) x := by
  have hs : Real.sqrt (q x) ≠ 0 := (Real.sqrt_pos.2 hqx).ne'
  refine (hf.fun_div (hq.sqrt hqx.ne') hs).congr_deriv ?_
  field_simp [hs] <;> ring

/-- The remainder kernel normalized by its two diagonal weights. -/
def normalized (r h : ℝ → ℝ) (d q : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  ((d x y - Real.sqrt (q x y)) / Real.sqrt (r x)) / Real.sqrt (h y)

private theorem numerator_derivative {r d q : ℝ → ℝ} {dr dd dq x : ℝ}
    (hr : HasDerivAt r dr x) (hd : HasDerivAt d dd x)
    (hq : HasDerivAt q dq x) (hrx : 0 < r x) (hqx : 0 < q x) :
    HasDerivAt (fun u ↦ (d u - Real.sqrt (q u)) / Real.sqrt (r u))
      ((2 * r x * dd - dr * d x - (r x * dq - dr * q x) / Real.sqrt (q x)) /
        (2 * r x * Real.sqrt (r x))) x := by
  refine (hasDerivAt_div_sqrt (hd.sub (hq.sqrt hqx.ne')) hr hrx).congr_deriv ?_
  set s := Real.sqrt (q x)
  have hs : s ≠ 0 := (Real.sqrt_pos.2 hqx).ne'
  have hsquare : s ^ 2 = q x := Real.sq_sqrt hqx.le
  change (2 * r x * (dd - dq / (2 * s)) - dr * (d x - s)) /
    (2 * r x * Real.sqrt (r x)) = _
  rw [← hsquare]
  field_simp [hs, hrx.ne', (Real.sqrt_pos.2 hrx).ne'] <;> ring

/-- The left partial derivative of the normalized kernel. -/
theorem normalized_dx {r h : ℝ → ℝ} {d q : ℝ → ℝ → ℝ}
    {x y rx dx qx : ℝ}
    (hr : HasDerivAt r rx x) (hd : HasDerivAt (fun u ↦ d u y) dx x)
    (hq : HasDerivAt (fun u ↦ q u y) qx x)
    (hrx : 0 < r x) (hqx : 0 < q x y) :
    HasDerivAt (fun u ↦ normalized r h d q u y)
      (((2 * r x * dx - rx * d x y - (r x * qx - rx * q x y) /
        Real.sqrt (q x y)) / (2 * r x * Real.sqrt (r x))) / Real.sqrt (h y)) x :=
  (numerator_derivative hr hd hq hrx hqx).div_const _

/-- The right partial derivative of the normalized kernel. -/
theorem normalized_dy {r h : ℝ → ℝ} {d q : ℝ → ℝ → ℝ}
    {x y hy dy qy : ℝ}
    (hh : HasDerivAt h hy y) (hd : HasDerivAt (d x) dy y)
    (hq : HasDerivAt (q x) qy y)
    (hhy : 0 < h y) (hqx : 0 < q x y) :
    HasDerivAt (normalized r h d q x)
      (((2 * h y * dy - hy * d x y - (h y * qy - hy * q x y) /
        Real.sqrt (q x y)) / (2 * h y * Real.sqrt (h y))) / Real.sqrt (r x)) y := by
  have h := (numerator_derivative hh hd hq hhy hqx).div_const (Real.sqrt (r x))
  refine h.congr_of_eventuallyEq (Eventually.of_forall fun u ↦ ?_)
  exact div_right_comm _ _ _

/-- The mixed derivative of the normalized kernel, with the rational square-root
numerator factored as in the polynomial sign certificate. -/
theorem normalized_dxy
    {r h : ℝ → ℝ} {d q : ℝ → ℝ → ℝ} {dRight qRight : ℝ → ℝ}
    {x y rx hy dx qx dxy qxy : ℝ}
    (hr : HasDerivAt r rx x) (hh : HasDerivAt h hy y)
    (hd : HasDerivAt (fun u ↦ d u y) dx x)
    (hq : HasDerivAt (fun u ↦ q u y) qx x)
    (hdRight : HasDerivAt dRight dxy x) (hqRight : HasDerivAt qRight qxy x)
    (hdAt : ∀ᶠ u in nhds x, HasDerivAt (d u) (dRight u) y)
    (hqAt : ∀ᶠ u in nhds x, HasDerivAt (q u) (qRight u) y)
    (hrx : 0 < r x) (hhy : 0 < h y) (hqx : 0 < q x y) :
    let z := 4 * r x * h y * dxy - 2 * r x * hy * dx -
      2 * h y * rx * dRight x + rx * hy * d x y
    let p := r x * h y * (2 * q x y * qxy - qx * qRight x) -
      r x * hy * q x y * qx - h y * rx * q x y * qRight x +
      rx * hy * (q x y)^2
    HasDerivAt (fun u ↦ deriv (normalized r h d q u) y)
      ((z - p / (Real.sqrt (q x y))^3) /
        (4 * r x * Real.sqrt (r x) * h y * Real.sqrt (h y))) x := by
  dsimp only
  let g (u : ℝ) := 2 * h y * dRight u - hy * d u y
  let j (u : ℝ) := h y * qRight u - hy * q u y
  let dg := 2 * h y * dxy - hy * dx
  let dj := h y * qxy - hy * qx
  have hg : HasDerivAt g dg x :=
    (hdRight.const_mul (2 * h y)).sub (hd.const_mul hy)
  have hj : HasDerivAt j dj x :=
    (hqRight.const_mul (h y)).sub (hq.const_mul hy)
  have hpos : ∀ᶠ u in nhds x, 0 < q u y :=
    hq.continuousAt.tendsto.eventually (eventually_gt_nhds hqx)
  have hlocal :
      (fun u ↦ deriv (normalized r h d q u) y) =ᶠ[nhds x]
        (fun u ↦ ((g u - j u / Real.sqrt (q u y)) / Real.sqrt (r u)) /
          (2 * h y * Real.sqrt (h y))) := by
    filter_upwards [hdAt, hqAt, hpos] with u hdu hqu hu
    change deriv (normalized r h d q u) y = _
    rw [(normalized_dy hh hdu hqu hhy hu).deriv]
    exact div_right_comm _ _ _
  apply HasDerivAt.congr_of_eventuallyEq _ hlocal
  have hcalc := hasDerivAt_div_sqrt (hg.sub (hasDerivAt_sqrt_reciprocal hj hq hqx)) hr hrx
  refine (hcalc.div_const (2 * h y * Real.sqrt (h y))).congr_deriv ?_
  simp only [Pi.sub_apply, g, j, dg, dj]
  set s := Real.sqrt (q x y)
  have hs : s ≠ 0 := (Real.sqrt_pos.2 hqx).ne'
  have hsquare : s ^ 2 = q x y := Real.sq_sqrt hqx.le
  rw [← hsquare]
  field_simp [hs, hrx.ne', hhy.ne', (Real.sqrt_pos.2 hrx).ne', (Real.sqrt_pos.2 hhy).ne'] <;> ring

private theorem hasDerivAt_first {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : ℝ × ℝ → E} {x y : ℝ} (hF : DifferentiableAt ℝ F (x, y)) :
    HasDerivAt (fun t ↦ F (t, y)) (fderiv ℝ F (x, y) (1, 0)) x := by
  have hline : HasDerivAt (fun t ↦ (t, y)) (1, 0) x := by
    simpa only [id_eq] using (hasDerivAt_id x).prodMk (hasDerivAt_const x y)
  exact hF.hasFDerivAt.comp_hasDerivAt (f := fun t ↦ (t, y)) x hline

private theorem hasDerivAt_second {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : ℝ × ℝ → E} {x y : ℝ} (hF : DifferentiableAt ℝ F (x, y)) :
    HasDerivAt (fun t ↦ F (x, t)) (fderiv ℝ F (x, y) (0, 1)) y := by
  have hline : HasDerivAt (fun t ↦ (x, t)) (0, 1) y := by
    simpa only [id_eq] using (hasDerivAt_const y x).prodMk (hasDerivAt_id y)
  exact hF.hasFDerivAt.comp_hasDerivAt (f := fun t ↦ (x, t)) y hline

/-- The first derivative of the second partial, expressed through the Fréchet derivative. -/
theorem hasDerivAt_deriv_second {f : ℝ → ℝ → ℝ} {x y : ℝ}
    (hf : ContDiffAt ℝ 2 (Function.uncurry f) (x, y)) :
    HasDerivAt (fun t ↦ deriv (f t) y)
      (fderiv ℝ (fderiv ℝ (Function.uncurry f)) (x, y) (1, 0) (0, 1)) x := by
  have hdiff : DifferentiableAt ℝ (fderiv ℝ (Function.uncurry f)) (x, y) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hnear := hf.eventually (by simp)
  have hline : ContinuousAt (fun t : ℝ ↦ (t, y)) x := by fun_prop
  have h := ((hasDerivAt_first hdiff).clm_apply (hasDerivAt_const x ((0, 1) : ℝ × ℝ)))
  simp only [map_zero, add_zero] at h
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [hline.tendsto.eventually hnear] with t ht
  exact (hasDerivAt_second (ht.differentiableAt two_ne_zero)).deriv

/-- The mixed partial in either order agrees wherever the kernel is twice continuously differentiable. -/
theorem hasDerivAt_deriv_first_of_second {f : ℝ → ℝ → ℝ} {x y m : ℝ}
    (hf : ContDiffAt ℝ 2 (Function.uncurry f) (x, y))
    (hm : HasDerivAt (fun t ↦ deriv (f t) y) m x) :
    HasDerivAt (fun t ↦ deriv (fun u ↦ f u t) x) m y := by
  have hdiff : DifferentiableAt ℝ (fderiv ℝ (Function.uncurry f)) (x, y) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hnear := hf.eventually (by simp)
  have hline : ContinuousAt (fun t : ℝ ↦ (x, t)) y := by fun_prop
  have hm' := (hasDerivAt_deriv_second hf).unique hm
  have hs := (hf.isSymmSndFDerivAt (by simp)).eq (1, 0) (0, 1)
  have h := ((hasDerivAt_second hdiff).clm_apply (hasDerivAt_const y ((1, 0) : ℝ × ℝ)))
  simp only [map_zero, add_zero] at h
  refine (h.congr_deriv (hs.symm.trans hm')).congr_of_eventuallyEq ?_
  filter_upwards [hline.tendsto.eventually hnear] with t ht
  exact (hasDerivAt_first (ht.differentiableAt two_ne_zero)).deriv

end

end RefinedBMV.Extreme
