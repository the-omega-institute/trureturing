/- GID: D5/S3/Quantum/Analysis/RefinedBMVExtremeAnalytic
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/RefinedBMVExtremeAnalytic
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Scalar derivative signs and the finite interval proof for the extreme BMV kernel. -/

import D5.S3.Quantum.Analysis.RefinedBMVExtremeCertificate
import D5.S3.Quantum.Analysis.RefinedBMVExtremeDerivatives
import D5.S3.Quantum.Analysis.RefinedBMVExtremeWalk
import D5.S3.Quantum.Analysis.RefinedBMVIntervalKernel
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Positivity

/-! # The unrestricted refined BMV comparison for (5,3)

The exact derivative signs give positive semidefiniteness on every finite
sample, and the centered walks yield the two matrix inequalities.
-/

open Matrix NormedSpace Set
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

noncomputable section

namespace RefinedBMV.Extreme

open DimThree (defect gaps defect_cycle defect_diag defect_nonneg)
open ExtremeCertificate (q Z P)

private theorem five_gaps :
    gaps 5 = [(0, 0, 5), (0, 1, 4), (0, 2, 3), (0, 3, 2), (0, 4, 1), (0, 5, 0),
      (1, 0, 4), (1, 1, 3), (1, 2, 2), (1, 3, 1), (1, 4, 0),
      (2, 0, 3), (2, 1, 2), (2, 2, 1), (2, 3, 0),
      (3, 0, 2), (3, 1, 1), (3, 2, 0), (4, 0, 1), (4, 1, 0), (5, 0, 0)] := by
  decide

private theorem defect_repeat_large (s t : ℝ) :
    defect 5 s (s + t) (s + t) =
      t ^ 2 * (210 * s ^ 13 + 1708 * s ^ 12 * t + 6804 * s ^ 11 * t ^ 2 +
        17208 * s ^ 10 * t ^ 3 + 30579 * s ^ 9 * t ^ 4 + 40194 * s ^ 8 * t ^ 5 +
        40176 * s ^ 7 * t ^ 6 + 30924 * s ^ 6 * t ^ 7 + 18327 * s ^ 5 * t ^ 8 +
        8250 * s ^ 4 * t ^ 9 + 2735 * s ^ 3 * t ^ 10 + 630 * s ^ 2 * t ^ 11 +
        90 * s * t ^ 12 + 6 * t ^ 13) := by
  norm_num [defect, five_gaps]
  ring

private theorem defect_repeat_small (s t : ℝ) :
    defect 5 s s (s + t) =
      t ^ 2 * (210 * s ^ 13 + 1022 * s ^ 12 * t + 2688 * s ^ 11 * t ^ 2 +
        4968 * s ^ 10 * t ^ 3 + 7109 * s ^ 9 * t ^ 4 + 8127 * s ^ 8 * t ^ 5 +
        7452 * s ^ 7 * t ^ 6 + 5448 * s ^ 6 * t ^ 7 + 3135 * s ^ 5 * t ^ 8 +
        1389 * s ^ 4 * t ^ 9 + 457 * s ^ 3 * t ^ 10 + 105 * s ^ 2 * t ^ 11 +
        15 * s * t ^ 12 + t ^ 13) := by
  norm_num [defect, five_gaps]
  ring

private theorem five_scope : (5 : ℕ) = 5 ∨ 5 = 6 ∨ 5 = 7 := Or.inl rfl

/-- The repeated-root defect is strictly positive for distinct nonnegative roots. -/
theorem defect_repeat_pos {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s ≠ t) :
    0 < defect 5 s s t := by
  rcases lt_or_gt_of_ne hst with h | h
  · have hgap : 0 < t - s := sub_pos.mpr h
    rw [← show s + (t - s) = t by ring, defect_repeat_small]
    positivity
  · have hgap : 0 < s - t := sub_pos.mpr h
    rw [defect_cycle five_scope t s s]
    rw [← show t + (s - t) = s by ring, defect_repeat_large]
    positivity

private def weight (a x : ℝ) : ℝ := defect 5 a x x

private theorem weight_pos {a x : ℝ} (ha : 0 ≤ a) (hx : a < x) : 0 < weight a x := by
  rw [weight, ← defect_cycle five_scope a x x]
  exact defect_repeat_pos (ha.trans hx.le) ha hx.ne'

private theorem radicand_pos {a x y : ℝ} (ha : 0 ≤ a) (hx : a < x) (hxy : x < y) :
    0 < q 5 a x y :=
  mul_pos (defect_repeat_pos ha (ha.trans (hx.trans hxy).le) (hx.trans hxy).ne)
    (defect_repeat_pos (ha.trans hx.le) (ha.trans (hx.trans hxy).le) hxy.ne)

private theorem contDiff_list_sum {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ι → E → ℝ} (l : List ι) (hf : ∀ i, ContDiff ℝ 2 (f i)) :
    ContDiff ℝ 2 (fun z ↦ (l.map fun i ↦ f i z).sum) := by
  induction l with
  | nil => exact contDiff_const
  | cons i l ih => exact (hf i).add ih

private theorem contDiff_defect {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g h : E → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (hh : ContDiff ℝ 2 h) :
    ContDiff ℝ 2 (fun z ↦ defect 5 (f z) (g z) (h z)) := by
  unfold defect
  exact (contDiff_list_sum (gaps 5) fun i ↦
    (((hf.pow 3).pow i.1).mul ((hg.pow 3).pow i.2.1)).mul ((hh.pow 3).pow i.2.2)).sub
    (contDiff_const.mul (((hf.mul hg).mul hh).pow 5))

private theorem weight_smooth (a : ℝ) : ContDiff ℝ 2 (weight a) :=
  contDiff_defect contDiff_const contDiff_id contDiff_id

private theorem defect_smooth (a : ℝ) : ContDiff ℝ 2 (Function.uncurry (defect 5 a)) :=
  contDiff_defect contDiff_const contDiff_fst contDiff_snd

private theorem q_smooth (a : ℝ) : ContDiff ℝ 2 (Function.uncurry (q 5 a)) :=
  (contDiff_defect contDiff_const contDiff_const contDiff_snd).mul
    (contDiff_defect contDiff_fst contDiff_fst contDiff_snd)

private theorem slice_x_smooth {f : ℝ → ℝ → ℝ}
    (hf : ContDiff ℝ 2 (Function.uncurry f)) (y : ℝ) :
    ContDiff ℝ 2 (fun x ↦ f x y) :=
  hf.comp (contDiff_id.prodMk contDiff_const)

private theorem slice_y_smooth {f : ℝ → ℝ → ℝ}
    (hf : ContDiff ℝ 2 (Function.uncurry f)) (x : ℝ) :
    ContDiff ℝ 2 (f x) :=
  hf.comp (contDiff_const.prodMk contDiff_id)

/-- The normalized upper-triangular kernel for the (5,3) defect. -/
def kernel (a : ℝ) : ℝ → ℝ → ℝ :=
  normalized (weight a) (weight a) (defect 5 a) (q 5 a)

/-- Its continuous diagonal value, for every point above a nonnegative center. -/
theorem kernel_diagonal {a x : ℝ} (ha : 0 ≤ a) (hx : a < x) : kernel a x x = 1 := by
  have hw := weight_pos ha hx
  unfold kernel normalized
  rw [q, defect_diag five_scope, mul_zero, Real.sqrt_zero, sub_zero, div_div,
    Real.mul_self_sqrt hw.le]
  exact div_self hw.ne'

private theorem kernel_continuousAt {a x y : ℝ} (ha : 0 ≤ a) (hx : a < x) (hy : a < y) :
    ContinuousAt (Function.uncurry (kernel a)) (x, y) := by
  have hr := ((weight_smooth a).comp contDiff_fst).continuous.continuousAt (x := (x, y))
  have hh := ((weight_smooth a).comp contDiff_snd).continuous.continuousAt (x := (x, y))
  have hd := (defect_smooth a).continuous.continuousAt (x := (x, y))
  have hq := (q_smooth a).continuous.continuousAt (x := (x, y))
  exact ((hd.sub hq.sqrt).div hr.sqrt (Real.sqrt_pos.2 (weight_pos ha hx)).ne').div
    hh.sqrt (Real.sqrt_pos.2 (weight_pos ha hy)).ne'

private theorem kernel_continuousOn_left {a y : ℝ} (ha : 0 ≤ a) (hy : a < y) :
    ContinuousOn (fun x ↦ kernel a x y) (Ioc a y) := by
  intro x hx
  have hline : ContinuousAt (fun t : ℝ ↦ (t, y)) x := by fun_prop
  have h := (kernel_continuousAt ha hx.1 hy).comp (f := fun t : ℝ ↦ (t, y)) hline
  exact h.continuousWithinAt

private theorem kernel_continuousOn_right {a x : ℝ} (ha : 0 ≤ a) (hx : a < x) :
    ContinuousOn (kernel a x) (Ici x) := by
  intro y hy
  have hline : ContinuousAt (fun t : ℝ ↦ (x, t)) y := by fun_prop
  exact ((kernel_continuousAt ha hx (hx.trans_le hy)).comp hline).continuousWithinAt

private theorem kernel_smooth {a x y : ℝ} (ha : 0 ≤ a) (hx : a < x) (hxy : x < y) :
    ContDiffAt ℝ 2 (Function.uncurry (kernel a)) (x, y) := by
  have hr := ((weight_smooth a).comp contDiff_fst).contDiffAt (x := (x, y))
  have hh := ((weight_smooth a).comp contDiff_snd).contDiffAt (x := (x, y))
  have hd := (defect_smooth a).contDiffAt (x := (x, y))
  have hq := (q_smooth a).contDiffAt (x := (x, y))
  have hr' := weight_pos ha hx
  have hh' := weight_pos ha (hx.trans hxy)
  exact ((hd.sub (hq.sqrt (radicand_pos ha hx hxy).ne')).div (hr.sqrt hr'.ne')
    (Real.sqrt_pos.2 hr').ne').div (hh.sqrt hh'.ne') (Real.sqrt_pos.2 hh').ne'

/-- The polynomial bounds for the two edges and the corner of the interval sum. -/
structure FiveEdgeSigns : Prop where
  gap : ∀ a x y : ℝ, 0 ≤ a → a < x → x < y → q 5 a x y ≤ defect 5 a x y ^ 2
  left : ∀ a x y : ℝ, 0 ≤ a → a < x → x < y →
    U a x y ≤ 0 ∧ X a x y ^ 2 * q 5 a x y ≤ U a x y ^ 2
  right : ∀ a x y : ℝ, 0 ≤ a → a < x → x < y →
    0 ≤ V a x y ∧ Y a x y ^ 2 * q 5 a x y ≤ V a x y ^ 2

private theorem fiveEdgeSigns : FiveEdgeSigns where
  gap a x y ha hx hy := (ExtremeCertificate.ordered_edges_five a x y ha hx.le hy.le).1
  left a x y ha hx hy := by
    obtain ⟨_, hu, hsq, _, _⟩ := ExtremeCertificate.ordered_edges_five a x y ha hx.le hy.le
    exact ⟨hu, hsq⟩
  right a x y ha hx hy := (ExtremeCertificate.ordered_edges_five a x y ha hx.le hy.le).2.2.2

private theorem kernel_dx {a x y : ℝ} (ha : 0 ≤ a) (hx : a < x) (hxy : x < y) :
    HasDerivAt (fun t ↦ kernel a t y)
      (((X a x y - U a x y / Real.sqrt (q 5 a x y)) /
        (2 * weight a x * Real.sqrt (weight a x))) / Real.sqrt (weight a y)) x :=
  normalized_dx ((weight_smooth a).differentiable two_ne_zero x).hasDerivAt
    ((slice_x_smooth (defect_smooth a) y).differentiable two_ne_zero x).hasDerivAt
    ((slice_x_smooth (q_smooth a) y).differentiable two_ne_zero x).hasDerivAt
    (weight_pos ha hx) (radicand_pos ha hx hxy)

private theorem kernel_dy {a x y : ℝ} (ha : 0 ≤ a) (hx : a < x) (hxy : x < y) :
    HasDerivAt (kernel a x)
      (((Y a x y - V a x y / Real.sqrt (q 5 a x y)) /
        (2 * weight a y * Real.sqrt (weight a y))) / Real.sqrt (weight a x)) y :=
  normalized_dy ((weight_smooth a).differentiable two_ne_zero y).hasDerivAt
    ((slice_y_smooth (defect_smooth a) x).differentiable two_ne_zero y).hasDerivAt
    ((slice_y_smooth (q_smooth a) x).differentiable two_ne_zero y).hasDerivAt
    (weight_pos ha (hx.trans hxy)) (radicand_pos ha hx hxy)

private theorem le_div_sqrt_of_square {b c q₀ : ℝ} (hq : 0 < q₀) (hc : 0 ≤ c)
    (h : b ^ 2 * q₀ ≤ c ^ 2) : b ≤ c / Real.sqrt q₀ :=
  (le_div_iff₀ (Real.sqrt_pos.2 hq)).2 <| le_of_sq_le_sq
    (by simpa only [mul_pow, Real.sq_sqrt hq.le] using h) hc

/-- Nonnegativity on the ordered chamber, including the continuous diagonal. -/
theorem kernel_nonneg (signs : FiveEdgeSigns) {a x y : ℝ}
    (ha : 0 ≤ a) (hx : a < x) (hxy : x ≤ y) : 0 ≤ kernel a x y := by
  rcases hxy.eq_or_lt with rfl | hxy
  · rw [kernel_diagonal ha hx]
    exact zero_le_one
  have hd := defect_nonneg five_scope a x y ha (ha.trans hx.le) (ha.trans (hx.trans hxy).le)
  have h := (Real.sqrt_le_left hd).2 (signs.gap a x y ha hx hxy)
  exact div_nonneg (div_nonneg (sub_nonneg.mpr h) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)

/-- The first partial derivative is nonnegative on the strict ordered chamber. -/
theorem kernel_deriv_left_nonneg (signs : FiveEdgeSigns) {a x y : ℝ}
    (ha : 0 ≤ a) (hx : a < x) (hxy : x < y) : 0 ≤ deriv (fun t ↦ kernel a t y) x := by
  obtain ⟨hu, hsq⟩ := signs.left a x y ha hx hxy
  have h := le_div_sqrt_of_square (b := -X a x y) (c := -U a x y)
    (radicand_pos ha hx hxy) (neg_nonneg.mpr hu) (by simpa only [neg_sq] using hsq)
  rw [neg_div, neg_le_neg_iff] at h
  rw [(kernel_dx ha hx hxy).deriv]
  have hr := (weight_pos ha hx).le
  exact div_nonneg (div_nonneg (sub_nonneg.mpr h) (by positivity)) (Real.sqrt_nonneg _)

/-- The second partial derivative is nonpositive on the strict ordered chamber. -/
theorem kernel_deriv_right_nonpos (signs : FiveEdgeSigns) {a x y : ℝ}
    (ha : 0 ≤ a) (hx : a < x) (hxy : x < y) : deriv (kernel a x) y ≤ 0 := by
  obtain ⟨hv, hsq⟩ := signs.right a x y ha hx hxy
  have h := le_div_sqrt_of_square (radicand_pos ha hx hxy) hv hsq
  rw [(kernel_dy ha hx hxy).deriv]
  have hh := (weight_pos ha (hx.trans hxy)).le
  exact div_nonpos_of_nonpos_of_nonneg
    (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr h) (by positivity)) (Real.sqrt_nonneg _)

private def mixedValue (a x y : ℝ) : ℝ :=
  (Z 5 a x y - P 5 a x y / (Real.sqrt (q 5 a x y)) ^ 3) /
    (4 * weight a x * Real.sqrt (weight a x) * weight a y * Real.sqrt (weight a y))

set_option maxHeartbeats 800000 in
-- Comparing the expanded mixed numerator with the named polynomials requires extra reduction.
private theorem kernel_dxy {a x y : ℝ} (ha : 0 ≤ a) (hx : a < x) (hxy : x < y) :
    HasDerivAt (fun t ↦ deriv (kernel a t) y) (mixedValue a x y) x := by
  have dr (u : ℝ) := ((weight_smooth a).differentiable two_ne_zero u).hasDerivAt
  have dx := ((slice_x_smooth (defect_smooth a) y).differentiable two_ne_zero x).hasDerivAt
  have qx := ((slice_x_smooth (q_smooth a) y).differentiable two_ne_zero x).hasDerivAt
  have dy (u : ℝ) := ((slice_y_smooth (defect_smooth a) u).differentiable two_ne_zero y).hasDerivAt
  have qy (u : ℝ) := ((slice_y_smooth (q_smooth a) u).differentiable two_ne_zero y).hasDerivAt
  have dxy := (hasDerivAt_deriv_second (f := defect 5 a)
    ((defect_smooth a).contDiffAt (x := (x, y)))).differentiableAt.hasDerivAt
  have qxy := (hasDerivAt_deriv_second (f := q 5 a)
    ((q_smooth a).contDiffAt (x := (x, y)))).differentiableAt.hasDerivAt
  have h := normalized_dxy (r := weight a) (h := weight a) (d := defect 5 a) (q := q 5 a)
    (dRight := fun t ↦ deriv (defect 5 a t) y) (qRight := fun t ↦ deriv (q 5 a t) y)
    (dr x) (dr y) dx qx dxy qxy (Filter.Eventually.of_forall dy)
    (Filter.Eventually.of_forall qy) (weight_pos ha hx) (weight_pos ha (hx.trans hxy))
    (radicand_pos ha hx hxy)
  have hw : weight a = fun t ↦ defect 5 a t t := rfl
  simpa only [kernel, mixedValue, Z, P, hw] using h

private theorem mixedValue_nonpos {a x y : ℝ} (ha : 0 ≤ a) (hx : a < x) (hxy : x < y) :
    mixedValue a x y ≤ 0 := by
  obtain ⟨hz, _, hsq⟩ := ExtremeCertificate.ordered_five a x y ha hx.le hxy.le
  have hq := radicand_pos ha hx hxy
  let s := Real.sqrt (q 5 a x y) ^ 3
  have hs : 0 < s := pow_pos (Real.sqrt_pos.2 hq) _
  have hs2 : s ^ 2 = q 5 a x y ^ 3 := by
    dsimp only [s]
    rw [← pow_mul, show (3 * 2 : ℕ) = 2 * 3 by decide, pow_mul, Real.sq_sqrt hq.le]
  have hdom : -P 5 a x y ≤ -Z 5 a x y * s :=
    le_of_sq_le_sq (by simpa only [mul_pow, neg_sq, hs2] using hsq)
      (mul_nonneg (neg_nonneg.mpr hz) hs.le)
  have hdiff : Z 5 a x y - P 5 a x y / s ≤ 0 := sub_nonpos.mpr <|
    (le_div_iff₀ hs).2 (by simpa only [neg_mul, neg_le_neg_iff] using hdom)
  unfold mixedValue
  have hr := (weight_pos ha hx).le
  have hh := (weight_pos ha (hx.trans hxy)).le
  exact div_nonpos_of_nonpos_of_nonneg hdiff (by positivity)

/-- The differentiated left partial is nonpositive in the second coordinate. -/
theorem kernel_deriv_left_deriv_right_nonpos {a x y : ℝ}
    (ha : 0 ≤ a) (hx : a < x) (hxy : x < y) :
    DifferentiableAt ℝ (fun t ↦ deriv (fun u ↦ kernel a u t) x) y ∧
      deriv (fun t ↦ deriv (fun u ↦ kernel a u t) x) y ≤ 0 := by
  have hm := hasDerivAt_deriv_first_of_second (kernel_smooth ha hx hxy) (kernel_dxy ha hx hxy)
  exact ⟨hm.differentiableAt, hm.deriv.trans_le (mixedValue_nonpos ha hx hxy)⟩

private theorem kernel_left_monotone (signs : FiveEdgeSigns) {a y : ℝ}
    (ha : 0 ≤ a) (hy : a < y) : MonotoneOn (fun x ↦ kernel a x y) (Ioc a y) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ioc a y) (kernel_continuousOn_left ha hy)
  · intro x hx
    rw [interior_Ioc] at hx
    exact (kernel_dx ha hx.1 hx.2).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Ioc] at hx
    exact kernel_deriv_left_nonneg signs ha hx.1 hx.2

private theorem kernel_right_antitone (signs : FiveEdgeSigns) {a x : ℝ}
    (ha : 0 ≤ a) (hx : a < x) : AntitoneOn (kernel a x) (Ici x) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici x) (kernel_continuousOn_right ha hx)
  · intro y hy
    rw [interior_Ici] at hy
    exact (kernel_dy ha hx hy).differentiableAt.differentiableWithinAt
  · intro y hy
    rw [interior_Ici] at hy
    exact kernel_deriv_right_nonpos signs ha hx hy

private theorem kernel_rectangle {a l u v w : ℝ}
    (ha : 0 ≤ a) (hal : a < l) (hlu : l ≤ u) (huv : u ≤ v) (hvw : v ≤ w) :
    0 ≤ (kernel a u v - kernel a l v) - (kernel a u w - kernel a l w) := by
  exact IntervalKernel.rectangle_nonneg_of_mixed_deriv_nonpos
    (fun _ hy ↦ kernel_continuousOn_left ha hy)
    (fun _ _ hx hxy ↦ by
      have h := kernel_dx ha hx hxy
      exact h.congr_deriv h.deriv.symm)
    (fun _ _ hx hxy ↦ kernel_deriv_left_deriv_right_nonpos ha hx hxy)
    hal hlu huv hvw

private theorem kernel_rescale {a x y : ℝ} (ha : 0 ≤ a) (hx : a < x) (hy : a < y) :
    Real.sqrt (weight a x) * kernel a (min x y) (max x y) * Real.sqrt (weight a y) =
      ExtremeWalk.upperKernel 5 a x y := by
  have hs := (Real.sqrt_pos.2 (weight_pos ha hx)).ne'
  have ht := (Real.sqrt_pos.2 (weight_pos ha hy)).ne'
  rcases le_total x y with h | h
  · simp only [min_eq_left h, max_eq_right h, kernel, normalized, ExtremeWalk.upperKernel, q]
    field_simp [hs, ht]
  · simp only [min_eq_right h, max_eq_left h, kernel, normalized, ExtremeWalk.upperKernel, q]
    field_simp [hs, ht]

universe u

private theorem kernel_gram_posSemidef (signs : FiveEdgeSigns) {a : ℝ} (ha : 0 ≤ a)
    {ι : Type u} [Fintype ι] (x : ι → ℝ) (hx : ∀ i, a < x i) :
    (Matrix.of fun i j ↦ kernel a (min (x i) (x j)) (max (x i) (x j))).PosSemidef := by
  let n := Fintype.card ι
  let e := (Fintype.equivFin ι).symm
  let order : Fin n ≃ ι := (Tuple.sort (x ∘ e)).trans e
  let y := x ∘ order
  have hmono : Monotone y := Tuple.monotone_sort (x ∘ e)
  apply (Matrix.posSemidef_submatrix_equiv order).mp
  change (Matrix.of fun i j ↦ kernel a (min (y i) (y j)) (max (y i) (y j))).PosSemidef
  let z (i : ℕ) := if h : i < n then y ⟨i, h⟩ else 0
  -- The sample occupies rows and columns 1 through n. The outer row and column are virtual.
  let A (i j : ℕ) := if i = 0 ∨ n < j then 0 else kernel a (z (i - 1)) (z (j - 1))
  have hz (i : ℕ) (hi : i < n) : a < z i := by
    simpa only [z, dite_eq_left hi, y, Function.comp_apply] using hx (order ⟨i, hi⟩)
  have hle (i j : ℕ) (hij : i ≤ j) (hj : j < n) : z i ≤ z j := by
    have hi := hij.trans_lt hj
    simpa [z, hi, hj] using hmono (show (⟨i, hi⟩ : Fin n) ≤ ⟨j, hj⟩ from hij)
  have hinside (i j : ℕ) (hj : j < n) : A (i + 1) (j + 1) = kernel a (z i) (z j) := by
    simp [A, show ¬ n < j + 1 by omega]
  have hrow (j : ℕ) : A 0 j = 0 := by simp [A]
  have hcol (i : ℕ) : A i (n + 1) = 0 := by simp [A]
  have hrect (i j : ℕ) (hij : i ≤ j) (hj : j < n) :
      0 ≤ (A (i + 1) (j + 1) - A i (j + 1)) - (A (i + 1) (j + 2) - A i (j + 2)) := by
    rw [hinside i j hj]
    by_cases hj' : j + 1 < n
    · rw [hinside i (j + 1) hj']
      cases i with
      | zero =>
        simp only [hrow, sub_zero, sub_nonneg]
        exact kernel_right_antitone signs ha (hz 0 (by omega))
          (hle 0 j (Nat.zero_le _) hj) (hle 0 (j + 1) (Nat.zero_le _) hj') (hle j (j + 1) (Nat.le_succ _) hj')
      | succ i =>
        rw [hinside i j hj, hinside i (j + 1) hj']
        exact kernel_rectangle ha (hz i (by omega)) (hle i (i + 1) (Nat.le_succ _) (hij.trans_lt hj))
          (hle (i + 1) j hij hj) (hle j (j + 1) (Nat.le_succ _) hj')
    · have he : j + 2 = n + 1 := by omega
      simp only [he, hcol, sub_zero]
      cases i with
      | zero =>
        rw [hrow, sub_zero]
        exact kernel_nonneg signs ha (hz 0 (by omega)) (hle 0 j (Nat.zero_le _) hj)
      | succ i =>
        rw [hinside i j hj, sub_nonneg]
        have hi : i + 1 < n := hij.trans_lt hj
        exact kernel_left_monotone signs ha (hz j hj)
          ⟨hz i (by omega), hle i j (Nat.le_of_succ_le hij) hj⟩ ⟨hz (i + 1) hi, hle (i + 1) j hij hj⟩
          (hle i (i + 1) (Nat.le_succ _) hi)
  have hPSD := IntervalKernel.posSemidef_truncation (𝕜 := ℝ) A hrect
  convert hPSD using 1
  ext i j
  have hmax : max i.val j.val < n := max_lt_iff.2 ⟨i.isLt, j.isLt⟩
  have hzmin : z (min i.val j.val) = min (y i) (y j) := by
    rcases le_total i j with h | h
    · simp [z, min_eq_left (show i.val ≤ j.val from h), min_eq_left (hmono h), i.isLt]
    · simp [z, min_eq_right (show j.val ≤ i.val from h), min_eq_right (hmono h), j.isLt]
  have hzmax : z (max i.val j.val) = max (y i) (y j) := by
    rcases le_total i j with h | h
    · simp [z, max_eq_right (show i.val ≤ j.val from h), max_eq_right (hmono h), j.isLt]
    · simp [z, max_eq_left (show j.val ≤ i.val from h), max_eq_left (hmono h), i.isLt]
  simp [Matrix.of_apply, hinside _ _ hmax, hrow, hcol, hzmin, hzmax]

/-- The upper block for the (5,3) defect is PSD on every finite sample. -/
theorem upperPSD_five : ExtremeWalk.UpperPSD.{u} 5 := by
  classical
  intro a ha ι _ x hx
  let w (i : ι) := Real.sqrt (weight a (x i))
  let A : Matrix ι ι ℝ := Matrix.of fun i j ↦ kernel a (min (x i) (x j)) (max (x i) (x j))
  have hw : (Matrix.diagonal w)ᴴ = Matrix.diagonal w := by
    simpa only [star_trivial] using Matrix.diagonal_conjTranspose w
  have h :=
    (kernel_gram_posSemidef fiveEdgeSigns ha x hx).conjTranspose_mul_mul_same (Matrix.diagonal w)
  rw [hw] at h
  change (Matrix.diagonal w * A * Matrix.diagonal w).PosSemidef at h
  have hmat : Matrix.diagonal w * A * Matrix.diagonal w =
      Matrix.of (fun i j ↦ ExtremeWalk.upperKernel 5 a (x i) (x j)) := by
    ext i j
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.of_apply, A, w]
    exact kernel_rescale ha (hx i) (hx j)
  exact hmat ▸ h

variable {n : Type u} [Fintype n]

local instance : DecidableEq n := Classical.decEq n

/-- Product comparison for arbitrary finite complex matrices with PSD factors. -/
theorem product_bound_five (A B : Matrix n n ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    trace (((A ^ (5 / 3 : ℝ)) * B) ^ 3) ≤ DimThree.wordMean 5 A B := by
  simpa using ExtremeWalk.product_bound five_scope upperPSD_five A B hA hB

/-- Exponential comparison for arbitrary finite complex matrices with Hermitian factors. -/
theorem exponential_bound_five (H K : Matrix n n ℂ)
    (hH : H.IsHermitian) (hK : K.IsHermitian) :
    trace (exp ((5 : ℝ) • H + (3 : ℝ) • K)) ≤ DimThree.wordMean 5 (exp H) (exp K) := by
  simpa using ExtremeWalk.exponential_bound five_scope upperPSD_five H K hH hK

#print axioms upperPSD_five
#print axioms product_bound_five
#print axioms exponential_bound_five

end RefinedBMV.Extreme
