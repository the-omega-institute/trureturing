/- GID: D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter
   generality: G
   mirror-B: D5/B/S3/Analytic/XuYangMillsRemainder/GeneralParameter
   mirror-E: none
   anchors: [D5/S3/Analytic/XuYangMillsRemainder/Result]
   utility: none
   digest: Exact original Theorem 2.1 target with compiled sign and endpoint-limit partial results.

This module is an unfrozen checkpoint for the general-parameter Mills
classification.  It keeps the original normalization from `Result.D` and
records the complete theorem statement verbatim as a proposition.  The
general-parameter coefficient representation, strict adjacent-moment
comparison, and the two endpoint asymptotics are still open here.
-/

import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import D5.S3.Analytic.XuYangMillsRemainder.Result

open Set Filter Real MeasureTheory
open scoped Topology
noncomputable section

namespace D5.S3.Analytic.XuYangMillsRemainder.GeneralParameter

open D5.S3.Analytic.XuYangMillsRemainder.Result

/-! The original source normalization. -/

def F (n : ℕ) (a x : ℝ) : ℝ := (-1 : ℝ) ^ n * D n x a

def I (j : ℕ) : ℝ := ∫ v in (0 : ℝ)..1, (1 + v ^ 2) ^ j

def B (j : ℕ) : ℝ := ∫ v in (0 : ℝ)..1, v ^ 2 * (1 + v ^ 2) ^ j

def theta (j : ℕ) : ℝ := (1 - I j / B j) / 2

def globalNonnegative (n : ℕ) (a : ℝ) : Prop :=
  ∀ x : ℝ, 0 < x → 0 ≤ F n a x

def globalNonpositive (n : ℕ) (a : ℝ) : Prop :=
  ∀ x : ℝ, 0 < x → 0 ≤ -F n a x

def completelyMonotone (n : ℕ) (a : ℝ) : Prop :=
  CompletelyMonotoneOn (F n a)

def theorem21 : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ a : ℝ,
    ((globalNonnegative n a ↔ completelyMonotone n a) ∧
      (completelyMonotone n a ↔ a ≤ theta (n - 2))) ∧
    ((globalNonpositive n a ↔ CompletelyMonotoneOn (fun x => -F n a x)) ∧
      (CompletelyMonotoneOn (fun x => -F n a x) ↔ a ≥ theta (n - 1)))

/-! Smoothness of the original Gaussian normalization, before any sign argument. -/

private theorem gaussian_integrable : Integrable (fun t : ℝ => exp (-t ^ 2 / 2)) := by
  convert integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2) using 1
  ext t
  congr 1
  ring

private theorem mills_primitive (x : ℝ) :
    millsRatio x = exp (x ^ 2 / 2) *
      ((∫ t in Ioi (0 : ℝ), exp (-t ^ 2 / 2)) - ∫ t in (0 : ℝ)..x, exp (-t ^ 2 / 2)) := by
  rw [millsRatio]
  congr 1
  have h := intervalIntegral.integral_Ioi_sub_Ioi'
    (gaussian_integrable.integrableOn (s := Ioi (0 : ℝ)))
    (gaussian_integrable.integrableOn (s := Ioi x))
  linarith

private theorem mills_smooth : ContDiff ℝ ∞ millsRatio := by
  have hg : ContDiff ℝ ∞ (fun t : ℝ => exp (-t ^ 2 / 2)) := by fun_prop
  have hp : ContDiff ℝ ∞ (fun x : ℝ => ∫ t in (0 : ℝ)..x, exp (-t ^ 2 / 2)) := by
    apply contDiff_infty_iff_deriv.mpr
    constructor
    · intro x
      exact (hg.continuous.integral_hasStrictDerivAt 0 x).hasDerivAt.differentiableAt
    · convert hg using 1
      ext x
      exact hg.continuous.deriv_integral _ 0 x
  simp_rw [mills_primitive]
  exact (by fun_prop : ContDiff ℝ ∞ (fun x : ℝ => exp (x ^ 2 / 2))).mul
    (contDiff_const.sub hp)

private theorem F_smooth (n : ℕ) (a : ℝ) : ContDiffOn ℝ ∞ (F n a) (Ioi 0) := by
  have hm := mills_smooth.contDiffOn (s := Ioi (0 : ℝ))
  unfold F D Y
  apply contDiffOn_const.mul
  apply ContDiffOn.sub
  · fun_prop
  · apply contDiffOn_const.add
    apply ContDiffOn.sum
    intro k _
    apply contDiffOn_const.div (by fun_prop)
    intro x hx
    exact pow_ne_zero _ (ne_of_gt hx)

/-! The exact finite truncation has a removable singularity after rescaling. -/

private theorem rescaled_F (n : ℕ) (a : ℝ) {x : ℝ} (hx : x ≠ 0) :
    x ^ (2 * n) * F n a x = (-1 : ℝ) ^ n *
      (x ^ (2 * n) * (Y a (a - 2) x - (a - 1)) -
        ∑ k ∈ Finset.Icc 1 n, (-1 : ℝ) ^ k * u k a (a - 2) * x ^ (2 * (n - k))) := by
  have hterm (k : ℕ) (hk : k ∈ Finset.Icc 1 n) :
      x ^ (2 * n) * ((-1 : ℝ) ^ k * u k a (a - 2) / x ^ (2 * k)) =
        (-1 : ℝ) ^ k * u k a (a - 2) * x ^ (2 * (n - k)) := by
    have hn : 2 * n = 2 * k + 2 * (n - k) := by
      have := (Finset.mem_Icc.mp hk).2
      omega
    rw [hn, pow_add]
    field_simp
  simp only [F, D]
  rw [mul_left_comm, mul_sub, mul_add, Finset.mul_sum]
  simp_rw [hterm]
  ring

private theorem zero_endpoint (n : ℕ) (hn : 2 ≤ n) (a : ℝ) :
    Tendsto (fun x : ℝ => x ^ (2 * n) * F n a x) (𝓝[>] (0 : ℝ))
      (𝓝 (-u n a (a - 2))) := by
  let P : ℝ → ℝ := fun x => (-1 : ℝ) ^ n *
      (x ^ (2 * n) * (Y a (a - 2) x - (a - 1)) -
        ∑ k ∈ Finset.Icc 1 n, (-1 : ℝ) ^ k * u k a (a - 2) * x ^ (2 * (n - k)))
  have hY : Continuous (Y a (a - 2)) := by
    have hm := mills_smooth.continuous
    unfold Y
    fun_prop
  have hP : Continuous P := by dsimp [P]; fun_prop
  have hz : P 0 = -u n a (a - 2) := by
    have hs : (∑ k ∈ Finset.Icc 1 n,
        (-1 : ℝ) ^ k * u k a (a - 2) * (0 : ℝ) ^ (2 * (n - k))) =
        (-1 : ℝ) ^ n * u n a (a - 2) := by
      apply Finset.sum_eq_single n
      · intro k hk hkn
        have hklt : k < n := lt_of_le_of_ne (Finset.mem_Icc.mp hk).2 hkn
        simp [zero_pow (by omega : 2 * (n - k) ≠ 0)]
      · intro h
        exact (h (Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩)).elim
      · simp
    dsimp [P]
    rw [zero_pow (by omega : 2 * n ≠ 0), zero_mul, zero_sub, hs]
    have hsgn : (-1 : ℝ) ^ n * (-1 : ℝ) ^ n = 1 := by
      rw [← mul_pow]
      norm_num
    linear_combination -u n a (a - 2) * hsgn
  rw [← hz]
  apply (hP.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact (rescaled_F n a (ne_of_gt hx)).symm

/-! A complete-monotonicity predicate contains the zeroth-order sign. -/

private theorem completelyMonotone_zero_sign {f : ℝ → ℝ}
    (hf : CompletelyMonotoneOn f) : ∀ x : ℝ, 0 < x → 0 ≤ f x := by
  intro x hx
  have h := hf.2 0 x hx
  simpa using h

private theorem cm_sign_projections (n : ℕ) (a : ℝ) :
    completelyMonotone n a → globalNonnegative n a := by
  intro h
  exact completelyMonotone_zero_sign h

private theorem neg_cm_sign_projection (n : ℕ) (a : ℝ) :
    CompletelyMonotoneOn (fun x => -F n a x) → globalNonpositive n a := by
  intro h
  exact completelyMonotone_zero_sign h

/-! Endpoint signs forced by a finite one-sided asymptotic limit. -/

private theorem nonnegative_sign_forces_nonpositive_limit {f : ℝ → ℝ}
    {p : ℕ} {u : ℝ}
    (hlim : Tendsto (fun x : ℝ => x ^ p * f x) (𝓝[>] (0 : ℝ)) (𝓝 (-u)))
    (hpos : ∀ x : ℝ, 0 < x → 0 ≤ f x) :
    u ≤ 0 := by
  have hev : ∀ᶠ x in 𝓝[>] (0 : ℝ), x ^ p * f x ∈ Ici (0 : ℝ) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact mul_nonneg (pow_nonneg hx.le p) (hpos x hx)
  have hclosed : -u ∈ Ici (0 : ℝ) := isClosed_Ici.mem_of_tendsto hlim hev
  change 0 ≤ -u at hclosed
  linarith

private theorem nonpositive_sign_forces_nonnegative_limit {f : ℝ → ℝ}
    {p : ℕ} {u : ℝ}
    (hlim : Tendsto (fun x : ℝ => x ^ p * f x) atTop (𝓝 (-u)))
    (hneg : ∀ x : ℝ, 0 < x → 0 ≤ -f x) :
    0 ≤ u := by
  have hev : ∀ᶠ x in atTop, x ^ p * (-f x) ∈ Ici (0 : ℝ) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact mul_nonneg (pow_nonneg (le_of_lt hx) p) (hneg x hx)
  have hlim' : Tendsto (fun x : ℝ => x ^ p * (-f x)) atTop (𝓝 u) := by
    have h := hlim.neg
    have hfun : (fun x : ℝ => -(x ^ p * f x)) = (fun x => x ^ p * (-f x)) := by
      funext x
      ring
    rw [hfun] at h
    simpa using h
  have hclosed : u ∈ Ici (0 : ℝ) := isClosed_Ici.mem_of_tendsto hlim' hev
  exact hclosed

/-! The exact source clauses are retained as a named checkpoint. -/

private theorem positive_sign_necessary (n : ℕ) (hn : 2 ≤ n) (a : ℝ)
    (h : globalNonnegative n a) : u n a (a - 2) ≤ 0 :=
  nonnegative_sign_forces_nonpositive_limit (zero_endpoint n hn a) h

private theorem positive_cm_necessary (n : ℕ) (hn : 2 ≤ n) (a : ℝ)
    (h : completelyMonotone n a) : u n a (a - 2) ≤ 0 :=
  positive_sign_necessary n hn a (cm_sign_projections n a h)

end D5.S3.Analytic.XuYangMillsRemainder.GeneralParameter
