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
import D5.S3.Quantum.Analysis.RefinedBMVPositiveCenter
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Positivity

/-! # The unrestricted refined BMV comparison at degrees five through ten

The exact derivative signs give positive semidefiniteness on every finite
sample, and the centered walks yield the two matrix inequalities.
-/

open Filter Matrix NormedSpace Set
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Topology

noncomputable section

namespace RefinedBMV.Extreme

open DimThree (defect gaps defect_corner defect_corner_eq_iff)
open UniformThreeSpectrum (defect_cycle_all defect_diag_all defect_nonneg_all)
open ExtremeCertificate (q Z P)

private theorem defect_repeat_pos_at {p : ℕ} (hp : 0 < p) {s t : ℝ}
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s ≠ t) : 0 < defect p s s t := by
  rw [← defect_cycle_all p s s t]
  refine (Real.sqrt_nonneg _).trans_lt (lt_of_le_of_ne (defect_corner p hs ht hs) ?_)
  intro h
  exact ((defect_corner_eq_iff p hs ht hs).mp h).elim hp.ne' hst

/-- The repeated-root defect is strictly positive for distinct nonnegative roots. -/
theorem defect_repeat_pos {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s ≠ t) :
    0 < defect 5 s s t :=
  defect_repeat_pos_at (by decide) hs ht hst

variable {p : ℕ}

private def weight (p : ℕ) (a x : ℝ) : ℝ := defect p a x x

private theorem weight_pos (hp : 0 < p) {a x : ℝ} (ha : 0 ≤ a) (hx : a < x) : 0 < weight p a x := by
  rw [weight, ← defect_cycle_all p a x x]
  exact defect_repeat_pos_at hp (ha.trans hx.le) ha hx.ne'

private theorem radicand_pos (hp : 0 < p) {a x y : ℝ} (ha : 0 ≤ a) (hx : a < x) (hxy : x < y) :
    0 < q p a x y :=
  mul_pos (defect_repeat_pos_at hp ha (ha.trans (hx.trans hxy).le) (hx.trans hxy).ne)
    (defect_repeat_pos_at hp (ha.trans hx.le) (ha.trans (hx.trans hxy).le) hxy.ne)

private theorem contDiff_list_sum {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ι → E → ℝ} (l : List ι) (hf : ∀ i, ContDiff ℝ 2 (f i)) :
    ContDiff ℝ 2 (fun z ↦ (l.map fun i ↦ f i z).sum) := by
  induction l with
  | nil => exact contDiff_const
  | cons i l ih => exact (hf i).add ih

private theorem contDiff_defect (p : ℕ) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g h : E → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (hh : ContDiff ℝ 2 h) :
    ContDiff ℝ 2 (fun z ↦ defect p (f z) (g z) (h z)) := by
  unfold defect
  exact (contDiff_list_sum (gaps p) fun i ↦
    (((hf.pow 3).pow i.1).mul ((hg.pow 3).pow i.2.1)).mul ((hh.pow 3).pow i.2.2)).sub
    (contDiff_const.mul (((hf.mul hg).mul hh).pow p))

private theorem weight_smooth (p : ℕ) (a : ℝ) : ContDiff ℝ 2 (weight p a) :=
  contDiff_defect p contDiff_const contDiff_id contDiff_id

private theorem defect_smooth (p : ℕ) (a : ℝ) : ContDiff ℝ 2 (Function.uncurry (defect p a)) :=
  contDiff_defect p contDiff_const contDiff_fst contDiff_snd

private theorem q_smooth (p : ℕ) (a : ℝ) : ContDiff ℝ 2 (Function.uncurry (q p a)) :=
  (contDiff_defect p contDiff_const contDiff_const contDiff_snd).mul
    (contDiff_defect p contDiff_fst contDiff_fst contDiff_snd)

private theorem slice_x_smooth {f : ℝ → ℝ → ℝ}
    (hf : ContDiff ℝ 2 (Function.uncurry f)) (y : ℝ) :
    ContDiff ℝ 2 (fun x ↦ f x y) :=
  hf.comp (contDiff_id.prodMk contDiff_const)

private theorem slice_y_smooth {f : ℝ → ℝ → ℝ}
    (hf : ContDiff ℝ 2 (Function.uncurry f)) (x : ℝ) :
    ContDiff ℝ 2 (f x) :=
  hf.comp (contDiff_const.prodMk contDiff_id)

/-- The normalized upper-triangular kernel at degree p. -/
private def kernelAt (p : ℕ) (a : ℝ) : ℝ → ℝ → ℝ :=
  normalized (weight p a) (weight p a) (defect p a) (q p a)

/-- Its continuous diagonal value, for every point above a nonnegative center. -/
private theorem kernel_diagonal_at (hp : 0 < p) {a x : ℝ} (ha : 0 ≤ a) (hx : a < x) : kernelAt p a x x = 1 := by
  have hw := weight_pos hp ha hx
  unfold kernelAt normalized
  rw [q, defect_diag_all, mul_zero, Real.sqrt_zero, sub_zero, div_div,
    Real.mul_self_sqrt hw.le]
  exact div_self hw.ne'

private theorem kernel_continuousAt (hp : 0 < p) {a x y : ℝ} (ha : 0 ≤ a) (hx : a < x) (hy : a < y) :
    ContinuousAt (Function.uncurry (kernelAt p a)) (x, y) := by
  have hr := ((weight_smooth p a).comp contDiff_fst).continuous.continuousAt (x := (x, y))
  have hh := ((weight_smooth p a).comp contDiff_snd).continuous.continuousAt (x := (x, y))
  have hd := (defect_smooth p a).continuous.continuousAt (x := (x, y))
  have hq := (q_smooth p a).continuous.continuousAt (x := (x, y))
  exact ((hd.sub hq.sqrt).div hr.sqrt (Real.sqrt_pos.2 (weight_pos hp ha hx)).ne').div
    hh.sqrt (Real.sqrt_pos.2 (weight_pos hp ha hy)).ne'

private theorem kernel_continuousOn_left (hp : 0 < p) {a y : ℝ} (ha : 0 ≤ a) (hy : a < y) :
    ContinuousOn (fun x ↦ kernelAt p a x y) (Ioc a y) := by
  intro x hx
  have hline : ContinuousAt (fun t : ℝ ↦ (t, y)) x := by fun_prop
  have h := (kernel_continuousAt hp ha hx.1 hy).comp (f := fun t : ℝ ↦ (t, y)) hline
  exact h.continuousWithinAt

private theorem kernel_continuousOn_right (hp : 0 < p) {a x : ℝ} (ha : 0 ≤ a) (hx : a < x) :
    ContinuousOn (kernelAt p a x) (Ici x) := by
  intro y hy
  have hline : ContinuousAt (fun t : ℝ ↦ (x, t)) y := by fun_prop
  exact ((kernel_continuousAt hp ha hx (hx.trans_le hy)).comp hline).continuousWithinAt

private theorem kernel_smooth (hp : 0 < p) {a x y : ℝ} (ha : 0 ≤ a) (hx : a < x) (hxy : x < y) :
    ContDiffAt ℝ 2 (Function.uncurry (kernelAt p a)) (x, y) := by
  have hr := ((weight_smooth p a).comp contDiff_fst).contDiffAt (x := (x, y))
  have hh := ((weight_smooth p a).comp contDiff_snd).contDiffAt (x := (x, y))
  have hd := (defect_smooth p a).contDiffAt (x := (x, y))
  have hq := (q_smooth p a).contDiffAt (x := (x, y))
  have hr' := weight_pos hp ha hx
  have hh' := weight_pos hp ha (hx.trans hxy)
  exact ((hd.sub (hq.sqrt (radicand_pos hp ha hx hxy).ne')).div (hr.sqrt hr'.ne')
    (Real.sqrt_pos.2 hr').ne').div (hh.sqrt hh'.ne') (Real.sqrt_pos.2 hh').ne'

/-- The polynomial bounds for the two edges and the corner of the interval sum. -/
private structure EdgeSigns (p : ℕ) : Prop where
  gap : ∀ a x y : ℝ, 0 ≤ a → a < x → x < y → q p a x y ≤ defect p a x y ^ 2
  left : ∀ a x y : ℝ, 0 ≤ a → a < x → x < y →
    UAt p a x y ≤ 0 ∧ XAt p a x y ^ 2 * q p a x y ≤ UAt p a x y ^ 2
  right : ∀ a x y : ℝ, 0 ≤ a → a < x → x < y →
    0 ≤ VAt p a x y ∧ YAt p a x y ^ 2 * q p a x y ≤ VAt p a x y ^ 2

private def MixedSigns (p : ℕ) : Prop :=
  ∀ a x y : ℝ, 0 ≤ a → a ≤ x → x ≤ y →
    Z p a x y ≤ 0 ∧ P p a x y ≤ 0 ∧ P p a x y ^ 2 ≤ Z p a x y ^ 2 * q p a x y ^ 3

private theorem kernel_dx (hp : 0 < p) {a x y : ℝ} (ha : 0 ≤ a) (hx : a < x) (hxy : x < y) :
    HasDerivAt (fun t ↦ kernelAt p a t y)
      (((XAt p a x y - UAt p a x y / Real.sqrt (q p a x y)) /
        (2 * weight p a x * Real.sqrt (weight p a x))) / Real.sqrt (weight p a y)) x :=
  normalized_dx ((weight_smooth p a).differentiable two_ne_zero x).hasDerivAt
    ((slice_x_smooth (defect_smooth p a) y).differentiable two_ne_zero x).hasDerivAt
    ((slice_x_smooth (q_smooth p a) y).differentiable two_ne_zero x).hasDerivAt
    (weight_pos hp ha hx) (radicand_pos hp ha hx hxy)

private theorem kernel_dy (hp : 0 < p) {a x y : ℝ} (ha : 0 ≤ a) (hx : a < x) (hxy : x < y) :
    HasDerivAt (kernelAt p a x)
      (((YAt p a x y - VAt p a x y / Real.sqrt (q p a x y)) /
        (2 * weight p a y * Real.sqrt (weight p a y))) / Real.sqrt (weight p a x)) y :=
  normalized_dy ((weight_smooth p a).differentiable two_ne_zero y).hasDerivAt
    ((slice_y_smooth (defect_smooth p a) x).differentiable two_ne_zero y).hasDerivAt
    ((slice_y_smooth (q_smooth p a) x).differentiable two_ne_zero y).hasDerivAt
    (weight_pos hp ha (hx.trans hxy)) (radicand_pos hp ha hx hxy)

private theorem le_div_sqrt_of_square {b c q₀ : ℝ} (hq : 0 < q₀) (hc : 0 ≤ c)
    (h : b ^ 2 * q₀ ≤ c ^ 2) : b ≤ c / Real.sqrt q₀ :=
  (le_div_iff₀ (Real.sqrt_pos.2 hq)).2 <| le_of_sq_le_sq
    (by simpa only [mul_pow, Real.sq_sqrt hq.le] using h) hc

/-- Nonnegativity on the ordered chamber, including the continuous diagonal. -/
private theorem kernel_nonneg_at (hp : 0 < p) (signs : EdgeSigns p) {a x y : ℝ}
    (ha : 0 ≤ a) (hx : a < x) (hxy : x ≤ y) : 0 ≤ kernelAt p a x y := by
  rcases hxy.eq_or_lt with rfl | hxy
  · rw [kernel_diagonal_at hp ha hx]
    exact zero_le_one
  have hd := defect_nonneg_all p a x y ha (ha.trans hx.le) (ha.trans (hx.trans hxy).le)
  have h := (Real.sqrt_le_left hd).2 (signs.gap a x y ha hx hxy)
  exact div_nonneg (div_nonneg (sub_nonneg.mpr h) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)

/-- The first partial derivative is nonnegative on the strict ordered chamber. -/
private theorem kernel_deriv_left_nonneg_at (hp : 0 < p) (signs : EdgeSigns p) {a x y : ℝ}
    (ha : 0 ≤ a) (hx : a < x) (hxy : x < y) : 0 ≤ deriv (fun t ↦ kernelAt p a t y) x := by
  obtain ⟨hu, hsq⟩ := signs.left a x y ha hx hxy
  have h := le_div_sqrt_of_square (b := -XAt p a x y) (c := -UAt p a x y)
    (radicand_pos hp ha hx hxy) (neg_nonneg.mpr hu) (by simpa only [neg_sq] using hsq)
  rw [neg_div, neg_le_neg_iff] at h
  rw [(kernel_dx hp ha hx hxy).deriv]
  have hr := (weight_pos hp ha hx).le
  exact div_nonneg (div_nonneg (sub_nonneg.mpr h) (by positivity)) (Real.sqrt_nonneg _)

/-- The second partial derivative is nonpositive on the strict ordered chamber. -/
private theorem kernel_deriv_right_nonpos_at (hp : 0 < p) (signs : EdgeSigns p) {a x y : ℝ}
    (ha : 0 ≤ a) (hx : a < x) (hxy : x < y) : deriv (kernelAt p a x) y ≤ 0 := by
  obtain ⟨hv, hsq⟩ := signs.right a x y ha hx hxy
  have h := le_div_sqrt_of_square (radicand_pos hp ha hx hxy) hv hsq
  rw [(kernel_dy hp ha hx hxy).deriv]
  have hh := (weight_pos hp ha (hx.trans hxy)).le
  exact div_nonpos_of_nonpos_of_nonneg
    (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr h) (by positivity)) (Real.sqrt_nonneg _)

private def mixedValue (p : ℕ) (a x y : ℝ) : ℝ :=
  (Z p a x y - P p a x y / (Real.sqrt (q p a x y)) ^ 3) /
    (4 * weight p a x * Real.sqrt (weight p a x) * weight p a y * Real.sqrt (weight p a y))

set_option maxHeartbeats 800000 in
-- The expanded mixed numerator is definitionally equal to the named polynomials.
private theorem kernel_dxy (hp : 0 < p) {a x y : ℝ} (ha : 0 ≤ a) (hx : a < x) (hxy : x < y) :
    HasDerivAt (fun t ↦ deriv (kernelAt p a t) y) (mixedValue p a x y) x := by
  have dr (u : ℝ) := ((weight_smooth p a).differentiable two_ne_zero u).hasDerivAt
  have dx := ((slice_x_smooth (defect_smooth p a) y).differentiable two_ne_zero x).hasDerivAt
  have qx := ((slice_x_smooth (q_smooth p a) y).differentiable two_ne_zero x).hasDerivAt
  have dy (u : ℝ) := ((slice_y_smooth (defect_smooth p a) u).differentiable two_ne_zero y).hasDerivAt
  have qy (u : ℝ) := ((slice_y_smooth (q_smooth p a) u).differentiable two_ne_zero y).hasDerivAt
  have dxy := (hasDerivAt_deriv_second (f := defect p a)
    ((defect_smooth p a).contDiffAt (x := (x, y)))).differentiableAt.hasDerivAt
  have qxy := (hasDerivAt_deriv_second (f := q p a)
    ((q_smooth p a).contDiffAt (x := (x, y)))).differentiableAt.hasDerivAt
  have h := normalized_dxy (r := weight p a) (h := weight p a) (d := defect p a) (q := q p a)
    (dRight := fun t ↦ deriv (defect p a t) y) (qRight := fun t ↦ deriv (q p a t) y)
    (dr x) (dr y) dx qx dxy qxy (Filter.Eventually.of_forall dy)
    (Filter.Eventually.of_forall qy) (weight_pos hp ha hx) (weight_pos hp ha (hx.trans hxy))
    (radicand_pos hp ha hx hxy)
  have hw : weight p a = fun t ↦ defect p a t t := rfl
  simpa only [kernelAt, mixedValue, Z, P, hw] using h

private theorem mixedValue_nonpos (hp : 0 < p) (mixed : MixedSigns p) {a x y : ℝ} (ha : 0 ≤ a) (hx : a < x) (hxy : x < y) :
    mixedValue p a x y ≤ 0 := by
  obtain ⟨hz, _, hsq⟩ := mixed a x y ha hx.le hxy.le
  have hq := radicand_pos hp ha hx hxy
  let s := Real.sqrt (q p a x y) ^ 3
  have hs : 0 < s := pow_pos (Real.sqrt_pos.2 hq) _
  have hs2 : s ^ 2 = q p a x y ^ 3 := by
    dsimp only [s]
    rw [← pow_mul, show (3 * 2 : ℕ) = 2 * 3 by decide, pow_mul, Real.sq_sqrt hq.le]
  have hdom : -P p a x y ≤ -Z p a x y * s :=
    le_of_sq_le_sq (by simpa only [mul_pow, neg_sq, hs2] using hsq)
      (mul_nonneg (neg_nonneg.mpr hz) hs.le)
  have hdiff : Z p a x y - P p a x y / s ≤ 0 := sub_nonpos.mpr <|
    (le_div_iff₀ hs).2 (by simpa only [neg_mul, neg_le_neg_iff] using hdom)
  unfold mixedValue
  have hr := (weight_pos hp ha hx).le
  have hh := (weight_pos hp ha (hx.trans hxy)).le
  exact div_nonpos_of_nonpos_of_nonneg hdiff (by positivity)

/-- The differentiated left partial is nonpositive in the second coordinate. -/
private theorem kernel_deriv_left_deriv_right_nonpos_at (hp : 0 < p) (mixed : MixedSigns p) {a x y : ℝ}
    (ha : 0 ≤ a) (hx : a < x) (hxy : x < y) :
    DifferentiableAt ℝ (fun t ↦ deriv (fun u ↦ kernelAt p a u t) x) y ∧
      deriv (fun t ↦ deriv (fun u ↦ kernelAt p a u t) x) y ≤ 0 := by
  have hm := hasDerivAt_deriv_first_of_second (kernel_smooth hp ha hx hxy) (kernel_dxy hp ha hx hxy)
  exact ⟨hm.differentiableAt, hm.deriv.trans_le (mixedValue_nonpos hp mixed ha hx hxy)⟩

private theorem kernel_left_monotone (hp : 0 < p) (signs : EdgeSigns p) {a y : ℝ}
    (ha : 0 ≤ a) (hy : a < y) : MonotoneOn (fun x ↦ kernelAt p a x y) (Ioc a y) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ioc a y) (kernel_continuousOn_left hp ha hy)
  · intro x hx
    rw [interior_Ioc] at hx
    exact (kernel_dx hp ha hx.1 hx.2).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Ioc] at hx
    exact kernel_deriv_left_nonneg_at hp signs ha hx.1 hx.2

private theorem kernel_right_antitone (hp : 0 < p) (signs : EdgeSigns p) {a x : ℝ}
    (ha : 0 ≤ a) (hx : a < x) : AntitoneOn (kernelAt p a x) (Ici x) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici x) (kernel_continuousOn_right hp ha hx)
  · intro y hy
    rw [interior_Ici] at hy
    exact (kernel_dy hp ha hx hy).differentiableAt.differentiableWithinAt
  · intro y hy
    rw [interior_Ici] at hy
    exact kernel_deriv_right_nonpos_at hp signs ha hx hy

private theorem kernel_rectangle (hp : 0 < p) (mixed : MixedSigns p) {a l u v w : ℝ}
    (ha : 0 ≤ a) (hal : a < l) (hlu : l ≤ u) (huv : u ≤ v) (hvw : v ≤ w) :
    0 ≤ (kernelAt p a u v - kernelAt p a l v) - (kernelAt p a u w - kernelAt p a l w) := by
  exact IntervalKernel.rectangle_nonneg_of_mixed_deriv_nonpos
    (fun _ hy ↦ kernel_continuousOn_left hp ha hy)
    (fun _ _ hx hxy ↦ by
      have h := kernel_dx hp ha hx hxy
      exact h.congr_deriv h.deriv.symm)
    (fun _ _ hx hxy ↦ kernel_deriv_left_deriv_right_nonpos_at hp mixed ha hx hxy)
    hal hlu huv hvw

private theorem kernel_rescale (hp : 0 < p) {a x y : ℝ} (ha : 0 ≤ a) (hx : a < x) (hy : a < y) :
    Real.sqrt (weight p a x) * kernelAt p a (min x y) (max x y) * Real.sqrt (weight p a y) =
      ExtremeWalk.upperKernel p a x y := by
  have hs := (Real.sqrt_pos.2 (weight_pos hp ha hx)).ne'
  have ht := (Real.sqrt_pos.2 (weight_pos hp ha hy)).ne'
  rcases le_total x y with h | h
  · simp only [min_eq_left h, max_eq_right h, kernelAt, normalized, ExtremeWalk.upperKernel, q]
    field_simp [hs, ht]
  · simp only [min_eq_right h, max_eq_left h, kernelAt, normalized, ExtremeWalk.upperKernel, q]
    field_simp [hs, ht]

universe u

private theorem kernel_gram_posSemidef {a : ℝ} {K : ℝ → ℝ → ℝ}
    (hnonneg : ∀ ⦃x y : ℝ⦄, a < x → x ≤ y → 0 ≤ K x y)
    (hleft : ∀ y > a, MonotoneOn (fun x ↦ K x y) (Ioc a y))
    (hright : ∀ x > a, AntitoneOn (K x) (Ici x))
    (hrectangle : ∀ ⦃l u v w : ℝ⦄, a < l → l ≤ u → u ≤ v → v ≤ w →
      0 ≤ (K u v - K l v) - (K u w - K l w))
    {ι : Type u} [Fintype ι] (x : ι → ℝ) (hx : ∀ i, a < x i) :
    (Matrix.of fun i j ↦ K (min (x i) (x j)) (max (x i) (x j))).PosSemidef := by
  let n := Fintype.card ι
  let e := (Fintype.equivFin ι).symm
  let order : Fin n ≃ ι := (Tuple.sort (x ∘ e)).trans e
  let y := x ∘ order
  have hmono : Monotone y := Tuple.monotone_sort (x ∘ e)
  apply (Matrix.posSemidef_submatrix_equiv order).mp
  change (Matrix.of fun i j ↦ K (min (y i) (y j)) (max (y i) (y j))).PosSemidef
  let z (i : ℕ) := if h : i < n then y ⟨i, h⟩ else 0
  -- The sample occupies rows and columns 1 through n. The outer row and column are virtual.
  let A (i j : ℕ) := if i = 0 ∨ n < j then 0 else K (z (i - 1)) (z (j - 1))
  have hz (i : ℕ) (hi : i < n) : a < z i := by
    simpa only [z, dite_eq_left hi, y, Function.comp_apply] using hx (order ⟨i, hi⟩)
  have hle (i j : ℕ) (hij : i ≤ j) (hj : j < n) : z i ≤ z j := by
    have hi := hij.trans_lt hj
    simpa [z, hi, hj] using hmono (show (⟨i, hi⟩ : Fin n) ≤ ⟨j, hj⟩ from hij)
  have hinside (i j : ℕ) (hj : j < n) : A (i + 1) (j + 1) = K (z i) (z j) := by
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
        exact hright _ (hz 0 (by omega))
          (hle 0 j (Nat.zero_le _) hj) (hle 0 (j + 1) (Nat.zero_le _) hj') (hle j (j + 1) (Nat.le_succ _) hj')
      | succ i =>
        rw [hinside i j hj, hinside i (j + 1) hj']
        exact hrectangle (hz i (by omega)) (hle i (i + 1) (Nat.le_succ _) (hij.trans_lt hj))
          (hle (i + 1) j hij hj) (hle j (j + 1) (Nat.le_succ _) hj')
    · have he : j + 2 = n + 1 := by omega
      simp only [he, hcol, sub_zero]
      cases i with
      | zero =>
        rw [hrow, sub_zero]
        exact hnonneg (hz 0 (by omega)) (hle 0 j (Nat.zero_le _) hj)
      | succ i =>
        rw [hinside i j hj, sub_nonneg]
        have hi : i + 1 < n := hij.trans_lt hj
        exact hleft _ (hz j hj)
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

private theorem upperKernel_posSemidef_of_gram (hp : 0 < p) {a : ℝ} (ha : 0 ≤ a)
    {ι : Type u} [Fintype ι] (x : ι → ℝ) (hx : ∀ i, a < x i)
    (hGram : (Matrix.of fun i j ↦ kernelAt p a (min (x i) (x j)) (max (x i) (x j))).PosSemidef) :
    (Matrix.of fun i j ↦ ExtremeWalk.upperKernel p a (x i) (x j)).PosSemidef := by
  classical
  let w (i : ι) := Real.sqrt (weight p a (x i))
  let A : Matrix ι ι ℝ := Matrix.of fun i j ↦ kernelAt p a (min (x i) (x j)) (max (x i) (x j))
  have hw : (Matrix.diagonal w)ᴴ = Matrix.diagonal w := by
    simpa only [star_trivial] using Matrix.diagonal_conjTranspose w
  have h := hGram.conjTranspose_mul_mul_same (Matrix.diagonal w)
  rw [hw] at h
  change (Matrix.diagonal w * A * Matrix.diagonal w).PosSemidef at h
  have hmat : Matrix.diagonal w * A * Matrix.diagonal w =
      Matrix.of (fun i j ↦ ExtremeWalk.upperKernel p a (x i) (x j)) := by
    ext i j
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.of_apply, A, w]
    exact kernel_rescale hp ha (hx i) (hx j)
  exact hmat ▸ h

private theorem upperPSD_of_signs (hp : 0 < p) (signs : EdgeSigns p) (mixed : MixedSigns p) :
    ExtremeWalk.UpperPSD.{u} p := by
  intro a ha ι _ x hx
  exact upperKernel_posSemidef_of_gram hp ha x hx
    (kernel_gram_posSemidef (K := kernelAt p a)
      (fun {_ _} hax hxy ↦ kernel_nonneg_at hp signs ha hax hxy)
      (fun _ hy ↦ kernel_left_monotone hp signs ha hy)
      (fun _ hax ↦ kernel_right_antitone hp signs ha hax)
      (fun {_ _ _ _} hal hlu huv hvw ↦ kernel_rectangle hp mixed ha hal hlu huv hvw) x hx)

private def logRoot (p : ℕ) (a t : ℝ) : ℝ := a * Real.exp (t / (p : ℝ))

/-- The normalized upper kernel in coordinates `u = p * log (x / a)` and
`v = p * log (y / a)`, for a positive center `a`. -/
def logKernelAt (p : ℕ) (a u v : ℝ) : ℝ :=
  kernelAt p a (logRoot p a u) (logRoot p a v)

/-- The positive-center parametrization has exactly the composition moment kernel. -/
theorem logKernelAt_eq_logKernel {p : ℕ} (hp : 0 < p) {a : ℝ} (ha : 0 < a) (u v : ℝ) :
    logKernelAt p a u v = PositiveCenter.logKernel p u v := by
  have hu : 0 < logRoot p a u := mul_pos ha (Real.exp_pos _)
  have hv : 0 < logRoot p a v := mul_pos ha (Real.exp_pos _)
  have hc (t : ℝ) : PositiveCenter.logCoordinate p a (logRoot p a t) = t :=
    PositiveCenter.logCoordinate_mul_exp hp ha t
  have h := PositiveCenter.normalized_eq_logKernel hp ha hu hv
  rw [hc u, hc v] at h
  exact h

private theorem logRoot_smooth (p : ℕ) (a : ℝ) : ContDiff ℝ 2 (logRoot p a) :=
  contDiff_const.mul (Real.contDiff_exp.comp (contDiff_id.div_const (p : ℝ)))

private theorem logRoot_strictMono (hp : 0 < p) {a : ℝ} (ha : 0 < a) :
    StrictMono (logRoot p a) := by
  have hp' : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  intro u v huv
  exact mul_lt_mul_of_pos_left (Real.exp_lt_exp.mpr (div_lt_div_of_pos_right huv hp')) ha

private theorem logRoot_above (hp : 0 < p) {a t : ℝ} (ha : 0 < a) (ht : 0 < t) :
    a < logRoot p a t := by
  have h := logRoot_strictMono hp ha ht
  simpa only [logRoot, zero_div, Real.exp_zero, mul_one] using h

/-- The mixed sign and the two edge limits give the upper block at a positive center.
The ordered rectangles include their diagonal endpoint by continuity. -/
theorem upperKernel_posSemidef_of_positive_center_mixed (hp : 0 < p) {a : ℝ} (ha : 0 < a)
    (hmixed : ∀ u v : ℝ, 0 < u → u < v →
      deriv (fun t ↦ deriv (fun s ↦ logKernelAt p a s t) u) v ≤ 0)
    (hzero : ∀ v > 0, Tendsto (fun u ↦ logKernelAt p a u v) (𝓝[>] 0) (𝓝 0))
    (hinfty : ∀ u > 0, Tendsto (logKernelAt p a u) atTop (𝓝 0))
    {ι : Type u} [Fintype ι] (x : ι → ℝ) (hx : ∀ i, a < x i) :
    (Matrix.of fun i j ↦ ExtremeWalk.upperKernel p a (x i) (x j)).PosSemidef := by
  have hroot := logRoot_strictMono hp ha
  have hpair : ContDiff ℝ 2 (fun z : ℝ × ℝ ↦ (logRoot p a z.1, logRoot p a z.2)) :=
    ((logRoot_smooth p a).comp contDiff_fst).prodMk ((logRoot_smooth p a).comp contDiff_snd)
  have hslice (v : ℝ) : ContDiff ℝ 2 (fun t ↦ (logRoot p a t, logRoot p a v)) :=
    (logRoot_smooth p a).prodMk contDiff_const
  have hrect : ∀ ⦃l u v w : ℝ⦄, 0 < l → l ≤ u → u ≤ v → v ≤ w →
      0 ≤ (logKernelAt p a u v - logKernelAt p a l v) -
        (logKernelAt p a u w - logKernelAt p a l w) := by
    intro l u v w hl hlu huv hvw
    refine IntervalKernel.rectangle_nonneg_of_mixed_deriv_nonpos
      (K := logKernelAt p a) (D := fun u v ↦ deriv (fun t ↦ logKernelAt p a t v) u)
      ?_ ?_ ?_ hl hlu huv hvw
    · intro v hv u hu
      have hInner : ContinuousAt (fun t ↦ (logRoot p a t, logRoot p a v)) u :=
        (hslice v).continuous.continuousAt
      have hOuter := kernel_continuousAt hp ha.le (logRoot_above hp ha hu.1)
        (logRoot_above hp ha hv)
      have h := ContinuousAt.comp (f := fun t : ℝ ↦ (logRoot p a t, logRoot p a v))
        (g := Function.uncurry (kernelAt p a)) hOuter hInner
      exact h.continuousWithinAt
    · intro u v hu huv
      have hInner : ContDiffAt ℝ 2 (fun t ↦ (logRoot p a t, logRoot p a v)) u :=
        (hslice v).contDiffAt
      have hOuter := kernel_smooth hp ha.le (logRoot_above hp ha hu) (hroot huv)
      have hc := ContDiffAt.comp (f := fun t : ℝ ↦ (logRoot p a t, logRoot p a v))
        (g := Function.uncurry (kernelAt p a)) u hOuter hInner
      have hs : ContDiffAt ℝ 2 (fun t ↦ logKernelAt p a t v) u := hc
      exact (hs.differentiableAt two_ne_zero).hasDerivAt
    · intro u v hu huv
      have hInner : ContDiffAt ℝ 2
          (fun z : ℝ × ℝ ↦ (logRoot p a z.1, logRoot p a z.2)) (u, v) :=
        hpair.contDiffAt
      have hOuter := kernel_smooth hp ha.le (logRoot_above hp ha hu) (hroot huv)
      have hc := ContDiffAt.comp
        (f := fun z : ℝ × ℝ ↦ (logRoot p a z.1, logRoot p a z.2))
        (g := Function.uncurry (kernelAt p a)) (u, v) hOuter hInner
      have hs : ContDiffAt ℝ 2 (Function.uncurry (logKernelAt p a)) (u, v) := hc
      exact ⟨(hasDerivAt_deriv_first_of_second hs (hasDerivAt_deriv_second hs)).differentiableAt,
        hmixed u v hu huv⟩
  obtain ⟨hnonneg, hleft, hright⟩ :=
    IntervalKernel.edge_inequalities_of_rectangle_limits hrect hzero hinfty
  let s (i : ι) := (p : ℝ) * Real.log (x i / a)
  have hp' : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hs (i : ι) : 0 < s i :=
    mul_pos hp' (Real.log_pos ((one_lt_div₀ ha).2 (hx i)))
  have hxs (i : ι) : logRoot p a (s i) = x i := by
    have hratio : 0 < x i / a := div_pos (ha.trans (hx i)) ha
    have hcoord : s i / (p : ℝ) = Real.log (x i / a) :=
      mul_div_cancel_left₀ _ hp'.ne'
    rw [logRoot, hcoord, Real.exp_log hratio, mul_comm a, div_mul_cancel₀ _ ha.ne']
  have hGram := kernel_gram_posSemidef (K := logKernelAt p a) hnonneg hleft hright hrect s hs
  have hmat :
      (Matrix.of fun i j ↦ logKernelAt p a (min (s i) (s j)) (max (s i) (s j))) =
        (Matrix.of fun i j ↦ kernelAt p a (min (x i) (x j)) (max (x i) (x j))) := by
    ext i j
    simp only [Matrix.of_apply, logKernelAt, hroot.monotone.map_min, hroot.monotone.map_max, hxs]
  exact upperKernel_posSemidef_of_gram hp ha.le x hx (hmat ▸ hGram)

private theorem upperKernel_continuous_center (p : ℕ) (x y : ℝ) :
    Continuous (fun a ↦ ExtremeWalk.upperKernel p a x y) := by
  have hdefect : Continuous (fun a : ℝ ↦ defect p a (min x y) (max x y)) :=
    (contDiff_defect p contDiff_id contDiff_const contDiff_const).continuous
  have hcenter : Continuous (fun a : ℝ ↦ defect p a a (max x y)) :=
    (contDiff_defect p contDiff_id contDiff_id contDiff_const).continuous
  have hrepeat : Continuous (fun _ : ℝ ↦ defect p (min x y) (min x y) (max x y)) :=
    continuous_const
  exact hdefect.sub (hcenter.mul hrepeat).sqrt

private theorem upperPSD_of_positive_centers
    (hpos : ∀ a : ℝ, 0 < a → ∀ {ι : Type u} [Fintype ι] (x : ι → ℝ),
      (∀ i, a < x i) → (Matrix.of fun i j ↦ ExtremeWalk.upperKernel p a (x i) (x j)).PosSemidef) :
    ExtremeWalk.UpperPSD.{u} p := by
  intro a ha ι _ x hx
  rcases ha.eq_or_lt with rfl | ha
  · let A (b : ℝ) : Matrix ι ι ℝ := Matrix.of fun i j ↦ ExtremeWalk.upperKernel p b (x i) (x j)
    have hA : Continuous A :=
      continuous_matrix fun i j ↦ upperKernel_continuous_center p (x i) (x j)
    have ht : Tendsto A (𝓝[>] (0 : ℝ)) (𝓝 (A 0)) :=
      (hA.tendsto 0).mono_left nhdsWithin_le_nhds
    change A 0 ∈ {M : Matrix ι ι ℝ | M.PosSemidef}
    refine Matrix.posSemidef_is_closed.mem_of_tendsto ht ?_
    have hsmall : ∀ᶠ b : ℝ in 𝓝[>] (0 : ℝ), ∀ i, b < x i := by
      rw [Filter.eventually_all]
      intro i
      exact nhdsWithin_le_nhds (eventually_lt_nhds (hx i))
    have habove : ∀ᶠ b : ℝ in 𝓝[>] (0 : ℝ), 0 < b := self_mem_nhdsWithin
    filter_upwards [habove, hsmall] with b hb hbx
    exact hpos b hb x hbx
  · exact hpos a ha x hx

/-- The positive-center mixed sign and edge limits imply the upper-block condition
at every nonnegative center. At zero, the unnormalized entries converge on the fixed sample. -/
theorem upperPSD_of_positive_center_mixed (hp : 0 < p)
    (hmixed : ∀ a > 0, ∀ u v : ℝ, 0 < u → u < v →
      deriv (fun t ↦ deriv (fun s ↦ logKernelAt p a s t) u) v ≤ 0)
    (hzero : ∀ a > 0, ∀ v > 0, Tendsto (fun u ↦ logKernelAt p a u v) (𝓝[>] 0) (𝓝 0))
    (hinfty : ∀ a > 0, ∀ u > 0, Tendsto (logKernelAt p a u) atTop (𝓝 0)) :
    ExtremeWalk.UpperPSD.{u} p := by
  apply upperPSD_of_positive_centers
  intro a ha ι _ x hx
  exact upperKernel_posSemidef_of_positive_center_mixed hp ha (hmixed a ha) (hzero a ha) (hinfty a ha) x hx

/-- The normalized upper-triangular kernel for the (5,3) defect. -/
def kernel (a : ℝ) : ℝ → ℝ → ℝ := kernelAt 5 a

/-- The polynomial bounds for the two edges and the corner of the interval sum. -/
structure FiveEdgeSigns : Prop where
  gap : ∀ a x y : ℝ, 0 ≤ a → a < x → x < y → q 5 a x y ≤ defect 5 a x y ^ 2
  left : ∀ a x y : ℝ, 0 ≤ a → a < x → x < y →
    U a x y ≤ 0 ∧ X a x y ^ 2 * q 5 a x y ≤ U a x y ^ 2
  right : ∀ a x y : ℝ, 0 ≤ a → a < x → x < y →
    0 ≤ V a x y ∧ Y a x y ^ 2 * q 5 a x y ≤ V a x y ^ 2

private theorem FiveEdgeSigns.toEdgeSigns (signs : FiveEdgeSigns) : EdgeSigns 5 :=
  ⟨signs.gap, signs.left, signs.right⟩

private theorem edgeSigns_of_ordered
    (ordered : ∀ a x y : ℝ, 0 ≤ a → a ≤ x → x ≤ y →
      q p a x y ≤ defect p a x y ^ 2 ∧
      UAt p a x y ≤ 0 ∧ XAt p a x y ^ 2 * q p a x y ≤ UAt p a x y ^ 2 ∧
      0 ≤ VAt p a x y ∧ YAt p a x y ^ 2 * q p a x y ≤ VAt p a x y ^ 2) :
    EdgeSigns p where
  gap a x y ha hx hy := (ordered a x y ha hx.le hy.le).1
  left a x y ha hx hy := by
    obtain ⟨_, hu, hsq, _, _⟩ := ordered a x y ha hx.le hy.le
    exact ⟨hu, hsq⟩
  right a x y ha hx hy := (ordered a x y ha hx.le hy.le).2.2.2

/-- Its continuous diagonal value, for every point above a nonnegative center. -/
theorem kernel_diagonal {a x : ℝ} (ha : 0 ≤ a) (hx : a < x) : kernel a x x = 1 :=
  kernel_diagonal_at (p := 5) (by decide) ha hx

/-- Nonnegativity on the ordered chamber, including the continuous diagonal. -/
theorem kernel_nonneg (signs : FiveEdgeSigns) {a x y : ℝ}
    (ha : 0 ≤ a) (hx : a < x) (hxy : x ≤ y) : 0 ≤ kernel a x y :=
  kernel_nonneg_at (by decide) signs.toEdgeSigns ha hx hxy

/-- The first partial derivative is nonnegative on the strict ordered chamber. -/
theorem kernel_deriv_left_nonneg (signs : FiveEdgeSigns) {a x y : ℝ}
    (ha : 0 ≤ a) (hx : a < x) (hxy : x < y) : 0 ≤ deriv (fun t ↦ kernel a t y) x :=
  kernel_deriv_left_nonneg_at (by decide) signs.toEdgeSigns ha hx hxy

/-- The second partial derivative is nonpositive on the strict ordered chamber. -/
theorem kernel_deriv_right_nonpos (signs : FiveEdgeSigns) {a x y : ℝ}
    (ha : 0 ≤ a) (hx : a < x) (hxy : x < y) : deriv (kernel a x) y ≤ 0 :=
  kernel_deriv_right_nonpos_at (by decide) signs.toEdgeSigns ha hx hxy

/-- The differentiated left partial is nonpositive in the second coordinate. -/
theorem kernel_deriv_left_deriv_right_nonpos {a x y : ℝ}
    (ha : 0 ≤ a) (hx : a < x) (hxy : x < y) :
    DifferentiableAt ℝ (fun t ↦ deriv (fun u ↦ kernel a u t) x) y ∧
      deriv (fun t ↦ deriv (fun u ↦ kernel a u t) x) y ≤ 0 :=
  kernel_deriv_left_deriv_right_nonpos_at (p := 5) (by decide)
    ExtremeCertificate.ordered_five ha hx hxy

/-- The upper block for the (5,3) defect is PSD on every finite sample. -/
theorem upperPSD_five : ExtremeWalk.UpperPSD.{u} 5 :=
  upperPSD_of_signs (by decide) (edgeSigns_of_ordered ExtremeCertificate.ordered_edges_five)
    ExtremeCertificate.ordered_five

/-- The upper block for the (6,3) defect is PSD on every finite sample. -/
theorem upperPSD_six : ExtremeWalk.UpperPSD.{u} 6 :=
  upperPSD_of_signs (by decide) (edgeSigns_of_ordered ExtremeCertificate.ordered_edges_six)
    ExtremeCertificate.ordered_six

/-- The upper block for the (7,3) defect is PSD on every finite sample. -/
theorem upperPSD_seven : ExtremeWalk.UpperPSD.{u} 7 :=
  upperPSD_of_signs (by decide) (edgeSigns_of_ordered ExtremeCertificate.ordered_edges_seven)
    ExtremeCertificate.ordered_seven

/-- The upper block for the (8,3) defect is PSD on every finite sample. -/
theorem upperPSD_eight : ExtremeWalk.UpperPSD.{u} 8 :=
  upperPSD_of_signs (by decide) (edgeSigns_of_ordered ExtremeCertificate.ordered_edges_eight)
    ExtremeCertificate.ordered_eight

/-- The upper block for the (9,3) defect is PSD on every finite sample. -/
theorem upperPSD_nine : ExtremeWalk.UpperPSD.{u} 9 :=
  upperPSD_of_signs (by decide) (edgeSigns_of_ordered ExtremeCertificate.ordered_edges_nine)
    ExtremeCertificate.ordered_nine

/-- The upper block for the (10,3) defect is PSD on every finite sample. -/
theorem upperPSD_ten : ExtremeWalk.UpperPSD.{u} 10 :=
  upperPSD_of_signs (by decide) (edgeSigns_of_ordered ExtremeCertificate.ordered_edges_ten)
    ExtremeCertificate.ordered_ten

variable {n : Type u} [Fintype n]

local instance : DecidableEq n := Classical.decEq n

/-- Product comparison for arbitrary finite complex matrices with PSD factors. -/
theorem product_bound_five (A B : Matrix n n ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    trace (((A ^ (5 / 3 : ℝ)) * B) ^ 3) ≤ DimThree.wordMean 5 A B := by
  simpa using ExtremeWalk.product_bound_all upperPSD_five A B hA hB

/-- Exponential comparison for arbitrary finite complex matrices with Hermitian factors. -/
theorem exponential_bound_five (H K : Matrix n n ℂ)
    (hH : H.IsHermitian) (hK : K.IsHermitian) :
    trace (exp ((5 : ℝ) • H + (3 : ℝ) • K)) ≤ DimThree.wordMean 5 (exp H) (exp K) := by
  simpa using ExtremeWalk.exponential_bound_all upperPSD_five H K hH hK

/-- Product comparison at degree six for arbitrary finite complex matrices with PSD factors. -/
theorem product_bound_six (A B : Matrix n n ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    trace (((A ^ (6 / 3 : ℝ)) * B) ^ 3) ≤ DimThree.wordMean 6 A B := by
  simpa using ExtremeWalk.product_bound_all upperPSD_six A B hA hB

/-- Exponential comparison at degree six for arbitrary finite complex matrices with Hermitian factors. -/
theorem exponential_bound_six (H K : Matrix n n ℂ)
    (hH : H.IsHermitian) (hK : K.IsHermitian) :
    trace (exp ((6 : ℝ) • H + (3 : ℝ) • K)) ≤ DimThree.wordMean 6 (exp H) (exp K) := by
  simpa using ExtremeWalk.exponential_bound_all upperPSD_six H K hH hK

/-- Product comparison at degree seven for arbitrary finite complex matrices with PSD factors. -/
theorem product_bound_seven (A B : Matrix n n ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    trace (((A ^ (7 / 3 : ℝ)) * B) ^ 3) ≤ DimThree.wordMean 7 A B := by
  simpa using ExtremeWalk.product_bound_all upperPSD_seven A B hA hB

/-- Exponential comparison at degree seven for arbitrary finite complex matrices with Hermitian factors. -/
theorem exponential_bound_seven (H K : Matrix n n ℂ)
    (hH : H.IsHermitian) (hK : K.IsHermitian) :
    trace (exp ((7 : ℝ) • H + (3 : ℝ) • K)) ≤ DimThree.wordMean 7 (exp H) (exp K) := by
  simpa using ExtremeWalk.exponential_bound_all upperPSD_seven H K hH hK

/-- Product comparison at degree eight for arbitrary finite complex matrices with PSD factors. -/
theorem product_bound_eight (A B : Matrix n n ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    trace (((A ^ (8 / 3 : ℝ)) * B) ^ 3) ≤ DimThree.wordMean 8 A B := by
  simpa using ExtremeWalk.product_bound_all upperPSD_eight A B hA hB

/-- Exponential comparison at degree eight for finite complex Hermitian matrices. -/
theorem exponential_bound_eight (H K : Matrix n n ℂ)
    (hH : H.IsHermitian) (hK : K.IsHermitian) :
    trace (exp ((8 : ℝ) • H + (3 : ℝ) • K)) ≤ DimThree.wordMean 8 (exp H) (exp K) := by
  simpa using ExtremeWalk.exponential_bound_all upperPSD_eight H K hH hK

/-- Product comparison at degree nine for arbitrary finite complex matrices with PSD factors. -/
theorem product_bound_nine (A B : Matrix n n ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    trace (((A ^ (9 / 3 : ℝ)) * B) ^ 3) ≤ DimThree.wordMean 9 A B := by
  simpa using ExtremeWalk.product_bound_all upperPSD_nine A B hA hB

/-- Exponential comparison at degree nine for finite complex Hermitian matrices. -/
theorem exponential_bound_nine (H K : Matrix n n ℂ)
    (hH : H.IsHermitian) (hK : K.IsHermitian) :
    trace (exp ((9 : ℝ) • H + (3 : ℝ) • K)) ≤ DimThree.wordMean 9 (exp H) (exp K) := by
  simpa using ExtremeWalk.exponential_bound_all upperPSD_nine H K hH hK

/-- Product comparison at degree ten for arbitrary finite complex matrices with PSD factors. -/
theorem product_bound_ten (A B : Matrix n n ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    trace (((A ^ (10 / 3 : ℝ)) * B) ^ 3) ≤ DimThree.wordMean 10 A B := by
  simpa using ExtremeWalk.product_bound_all upperPSD_ten A B hA hB

/-- Exponential comparison at degree ten for finite complex Hermitian matrices. -/
theorem exponential_bound_ten (H K : Matrix n n ℂ)
    (hH : H.IsHermitian) (hK : K.IsHermitian) :
    trace (exp ((10 : ℝ) • H + (3 : ℝ) • K)) ≤ DimThree.wordMean 10 (exp H) (exp K) := by
  simpa using ExtremeWalk.exponential_bound_all upperPSD_ten H K hH hK

#print axioms upperPSD_five
#print axioms product_bound_five
#print axioms exponential_bound_five
#print axioms upperPSD_six
#print axioms product_bound_six
#print axioms exponential_bound_six
#print axioms upperPSD_seven
#print axioms product_bound_seven
#print axioms exponential_bound_seven
#print axioms upperPSD_eight
#print axioms product_bound_eight
#print axioms exponential_bound_eight
#print axioms upperPSD_nine
#print axioms product_bound_nine
#print axioms exponential_bound_nine
#print axioms upperPSD_ten
#print axioms product_bound_ten
#print axioms exponential_bound_ten

end RefinedBMV.Extreme
