/- GID: D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter
   generality: G
   mirror-B: D5/B/S3/Analytic/XuYangMillsRemainder/GeneralParameter
   mirror-E: none(waiver:kernel-checked-analytic-proof-no-external-evidence)
   anchors: [mathlib/module/Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas, mathlib/module/Mathlib.Analysis.Calculus.ContDiff.Deriv]
   utility: none
   digest: Complete original Mills sign and complete-monotonicity classification. -/

/-
The general-parameter Mills definitions retain the original normalization from
`Result.D`. Both complete equivalence chains are recorded as a proposition.
The Gamma coefficient correspondence identifies the sharp positive-branch
origin obstruction. Absolute signed-kernel moments, finite subtraction and the
Gaussian Laplace identity give the exact signed Laplace representation and
every ordinary derivative of the original F. The original finite recurrence gives the infinity
asymptotic and both complete classification chains.
-/

import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import D5.S3.Analytic.XuYangMillsRemainder.Result
import D5.S3.Analytic.IncompleteBeta.Comparison
import D5.S3.Analytic.XuYangMillsRemainder.NormalizedRemainderOrders
import D5.S3.Analytic.XuYangMillsRemainder.GaussianLaplace

/-! The original general-parameter target and its analytic proof obligations. -/

open Set Filter Real MeasureTheory
open scoped Topology ContDiff
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
  have hm : millsRatio = fun x : ℝ => exp (x ^ 2 / 2) *
      ((∫ t in Ioi (0 : ℝ), exp (-t ^ 2 / 2)) - ∫ t in (0 : ℝ)..x, exp (-t ^ 2 / 2)) :=
    funext mills_primitive
  rw [hm]
  exact (by fun_prop : ContDiff ℝ ∞ (fun x : ℝ => exp (x ^ 2 / 2))).mul
    (contDiff_const.sub hp)

/-! The exact finite truncation has a removable singularity after rescaling. -/

private theorem coefficient_one_zero (a : ℝ) : u 1 a (a - 2) = 0 := by
  have hc1 := coeff_factorial 0
  norm_num at hc1
  have hc0 := coeff_sum 0
  norm_num [intPow, hc1] at hc0
  have hu : u 1 a (a - 2) = (a - 1) * coeff 1 + (1 - a) * coeff 0 := by
    norm_num [u, coeff, Finset.sum_range_succ]
    ring
  rw [hu, hc0, hc1]
  ring

private theorem rescaled_f (n : ℕ) (a : ℝ) {x : ℝ} (hx : x ≠ 0) :
    x ^ (2 * n) * F n a x = (-1 : ℝ) ^ n *
      (x ^ (2 * n) * (Y a (a - 2) x - (a - 1)) -
        ∑ k ∈ Finset.Icc 2 n, (-1 : ℝ) ^ k * u k a (a - 2) * x ^ (2 * (n - k))) := by
  have hterm (k : ℕ) (hk : k ∈ Finset.Icc 1 n) :
      x ^ (2 * n) * ((-1 : ℝ) ^ k * u k a (a - 2) / x ^ (2 * k)) =
        (-1 : ℝ) ^ k * u k a (a - 2) * x ^ (2 * (n - k)) := by
    have hn : 2 * n = 2 * k + 2 * (n - k) := by
      have := (Finset.mem_Icc.mp hk).2
      omega
    rw [hn, pow_add]
    field_simp
  have hsum : x ^ (2 * n) *
      (∑ k ∈ Finset.Icc 1 n, (-1 : ℝ) ^ k * u k a (a - 2) / x ^ (2 * k)) =
      ∑ k ∈ Finset.Icc 1 n, (-1 : ℝ) ^ k * u k a (a - 2) * x ^ (2 * (n - k)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl hterm
  have hdrop : (∑ k ∈ Finset.Icc 1 n,
      (-1 : ℝ) ^ k * u k a (a - 2) * x ^ (2 * (n - k))) =
      ∑ k ∈ Finset.Icc 2 n,
        (-1 : ℝ) ^ k * u k a (a - 2) * x ^ (2 * (n - k)) := by
    symm
    apply Finset.sum_subset
    · intro k hk
      obtain ⟨hk0, hk1⟩ := Finset.mem_Icc.mp hk
      exact Finset.mem_Icc.mpr ⟨by omega, hk1⟩
    · intro k hk hk'
      have hk1 : k = 1 := by
        simp only [Finset.mem_Icc] at hk hk'
        omega
      subst k
      simp [coefficient_one_zero]
  unfold F D
  calc
    _ = (-1 : ℝ) ^ n * (x ^ (2 * n) * (Y a (a - 2) x - (a - 1)) -
        x ^ (2 * n) *
          (∑ k ∈ Finset.Icc 1 n, (-1 : ℝ) ^ k * u k a (a - 2) / x ^ (2 * k))) := by ring
    _ = _ := by rw [hsum, hdrop]

private theorem zero_endpoint (n : ℕ) (hn : 2 ≤ n) (a : ℝ) :
    Tendsto (fun x : ℝ => x ^ (2 * n) * F n a x) (𝓝[>] (0 : ℝ))
      (𝓝 (-u n a (a - 2))) := by
  let P : ℝ → ℝ := fun x => (-1 : ℝ) ^ n *
      (x ^ (2 * n) * (Y a (a - 2) x - (a - 1)) -
        ∑ k ∈ Finset.Icc 2 n, (-1 : ℝ) ^ k * u k a (a - 2) * x ^ (2 * (n - k)))
  have hY : Continuous (Y a (a - 2)) := by
    have hm := mills_smooth.continuous
    unfold Y
    fun_prop
  have hP : Continuous P := by dsimp [P]; fun_prop
  have hz : P 0 = -u n a (a - 2) := by
    have hs : (∑ k ∈ Finset.Icc 2 n,
        (-1 : ℝ) ^ k * u k a (a - 2) * (0 : ℝ) ^ (2 * (n - k))) =
        (-1 : ℝ) ^ n * u n a (a - 2) := by
      calc
        _ = (-1 : ℝ) ^ n * u n a (a - 2) * (0 : ℝ) ^ (2 * (n - n)) := by
          apply Finset.sum_eq_single n
          · intro k hk hkn
            have hklt : k < n := lt_of_le_of_ne (Finset.mem_Icc.mp hk).2 hkn
            simp [zero_pow (by omega : 2 * (n - k) ≠ 0)]
          · intro h
            exact (h (Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩)).elim
        _ = _ := by simp
    dsimp [P]
    rw [zero_pow (by omega : 2 * n ≠ 0), zero_mul, zero_sub, hs]
    have hsgn : (-1 : ℝ) ^ n * (-1 : ℝ) ^ n = 1 := by
      rw [← mul_pow]
      norm_num
    linear_combination -u n a (a - 2) * hsgn
  rw [← hz]
  apply (hP.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact (rescaled_f n a (ne_of_gt hx)).symm

private theorem regularity_and_origin (n : ℕ) (hn : 2 ≤ n) (a : ℝ) :
    ContDiffOn ℝ ∞ (F n a) (Ioi 0) ∧
      Tendsto (fun x : ℝ => x ^ (2 * n) * F n a x) (𝓝[>] (0 : ℝ))
        (𝓝 (-u n a (a - 2))) := by
  refine ⟨?_, zero_endpoint n hn a⟩
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

/-! Strict moment comparison for the original signed Taylor remainder. -/

/-- The source remainder of order r+1. -/
def E (r : ℕ) (y : ℝ) : ℝ :=
  (-1 : ℝ) ^ (r + 1) * D5.S3.Analytic.ExpRemainderDifferences.R r (-y)

def M0 (r : ℕ) (z : ℝ) : ℝ := ∫ v in (0 : ℝ)..1, E r (z * (1 + v ^ 2))

def M2 (r : ℕ) (z : ℝ) : ℝ := ∫ v in (0 : ℝ)..1, v ^ 2 * E r (z * (1 + v ^ 2))

private theorem e_original (r : ℕ) (y : ℝ) : E r y = expRemainder (r + 1) y := by
  rw [expRemainder_eq]
  rfl

private theorem e_continuous (r : ℕ) : Continuous (E r) := by
  exact (expRemainderContinuous (r + 1)).congr (fun y => (e_original r y).symm)

private theorem e_pos (r : ℕ) {y : ℝ} (hy : 0 < y) : 0 < E r y := by
  have hi : 0 < ∫ s in (0 : ℝ)..1, (1 - s) ^ r * exp (-s * y) := by
    apply intervalIntegral.intervalIntegral_pos_of_pos_on
      (by apply Continuous.intervalIntegrable; fun_prop) _ (by norm_num)
    intro s hs
    exact mul_pos (pow_pos (sub_pos.mpr hs.2) _) (exp_pos _)
  have h := normalized_exp_remainder r hy
  change E r y / y ^ (r + 1) = _ at h
  have hd : 0 < E r y / y ^ (r + 1) := by rw [h]; positivity
  exact (div_pos_iff_of_pos_right (pow_pos hy (r + 1))).mp hd

private theorem moments_pos (r : ℕ) {z : ℝ} (hz : 0 < z) :
    0 < M0 r z ∧ 0 < M2 r z := by
  have he (v : ℝ) : 0 < E r (z * (1 + v ^ 2)) := e_pos r (by positivity)
  have hc : Continuous (fun v : ℝ => E r (z * (1 + v ^ 2))) :=
    (e_continuous r).comp (by fun_prop)
  constructor
  · apply intervalIntegral.intervalIntegral_pos_of_pos_on
      (hc.intervalIntegrable 0 1) _ (by norm_num)
    intro v _
    exact he v
  · apply intervalIntegral.intervalIntegral_pos_of_pos_on
      (((continuous_id.pow 2).mul hc).intervalIntegrable 0 1)
      _ (by norm_num)
    intro v hv
    exact mul_pos (sq_pos_of_pos hv.1) (he v)

private theorem moment_ratio_bounds (r : ℕ) {z : ℝ} (hz : 0 < z) :
    B r / I r < M2 r z / M0 r z ∧
      M2 r z / M0 r z < B (r + 1) / I (r + 1) := by
  have hA (v : ℝ) : 0 < 1 + v ^ 2 := by positivity
  have he (v : ℝ) : 0 < E r (z * (1 + v ^ 2)) := e_pos r (by positivity)
  have hc : Continuous (fun v : ℝ => E r (z * (1 + v ^ 2))) :=
    (e_continuous r).comp (by fun_prop)
  have hW : StrictMonoOn (fun v : ℝ => v ^ 2) (Ioo 0 1) := by
    intro v hv w hw hvw
    exact sq_lt_sq₀ hv.1.le hw.1.le |>.mpr hvw
  have harg {v w : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1) (hw : w ∈ Ioo (0 : ℝ) 1)
      (hvw : v < w) : z * (1 + v ^ 2) < z * (1 + w ^ 2) := by
    exact mul_lt_mul_of_pos_left (add_lt_add_right (hW hv hw hvw) 1) hz
  have hupper : StrictAntiOn
      (fun v : ℝ => E r (z * (1 + v ^ 2)) / (1 + v ^ 2) ^ (r + 1)) (Ioo 0 1) := by
    intro v hv w hw hvw
    have h := exp_remainder_ratio_strict_anti r
      (show z * (1 + v ^ 2) ∈ Ioi (0 : ℝ) by exact mul_pos hz (hA _))
      (show z * (1 + w ^ 2) ∈ Ioi (0 : ℝ) by exact mul_pos hz (hA _)) (harg hv hw hvw)
    change E r (z * (1 + w ^ 2)) / (z * (1 + w ^ 2)) ^ (r + 1) <
      E r (z * (1 + v ^ 2)) / (z * (1 + v ^ 2)) ^ (r + 1) at h
    simpa only [mul_pow, div_mul_eq_div_div_swap,
      div_lt_div_iff_of_pos_right (pow_pos hz _)] using h
  have hlower : StrictMonoOn
      (fun v : ℝ => E r (z * (1 + v ^ 2)) / (1 + v ^ 2) ^ r) (Ioo 0 1) := by
    intro v hv w hw hvw
    have h := exp_remainder_ratio_strict_mono r
      (show z * (1 + v ^ 2) ∈ Ioi (0 : ℝ) by exact mul_pos hz (hA _))
      (show z * (1 + w ^ 2) ∈ Ioi (0 : ℝ) by exact mul_pos hz (hA _)) (harg hv hw hvw)
    change E r (z * (1 + v ^ 2)) / (z * (1 + v ^ 2)) ^ r <
      E r (z * (1 + w ^ 2)) / (z * (1 + w ^ 2)) ^ r at h
    simpa only [mul_pow, div_mul_eq_div_div_swap,
      div_lt_div_iff_of_pos_right (pow_pos hz _)] using h
  have hinverse : StrictAntiOn
      (fun v : ℝ => (1 + v ^ 2) ^ r / E r (z * (1 + v ^ 2))) (Ioo 0 1) := by
    intro v hv w hw hvw
    have h := hlower hv hw hvw
    apply (div_lt_div_iff₀ (he w) (he v)).mpr
    have H := (div_lt_div_iff₀ (pow_pos (hA v) r) (pow_pos (hA w) r)).mp h
    nlinarith
  constructor
  · have h := D5.S3.Analytic.IncompleteBeta.Comparison.weighted_means_lt
      (p := fun v => E r (z * (1 + v ^ 2)))
      (q := fun v => (1 + v ^ 2) ^ r) (W := fun v => v ^ 2)
      (by norm_num : (0 : ℝ) < 1) (hc.intervalIntegrable 0 1)
      (by apply Continuous.intervalIntegrable; fun_prop)
      ((hc.mul (continuous_id.pow 2)).intervalIntegrable 0 1)
      (by apply Continuous.intervalIntegrable; fun_prop)
      (fun v _ => he v) (fun v _ => pow_pos (hA v) r) hW hinverse
    simpa only [M0, M2, I, B, mul_comm] using h
  · have h := D5.S3.Analytic.IncompleteBeta.Comparison.weighted_means_lt
      (p := fun v => (1 + v ^ 2) ^ (r + 1))
      (q := fun v => E r (z * (1 + v ^ 2))) (W := fun v => v ^ 2)
      (by norm_num : (0 : ℝ) < 1)
      (by apply Continuous.intervalIntegrable; fun_prop) (hc.intervalIntegrable 0 1)
      (by apply Continuous.intervalIntegrable; fun_prop)
      ((hc.mul (continuous_id.pow 2)).intervalIntegrable 0 1)
      (fun v _ => pow_pos (hA v) (r + 1)) (fun v _ => he v) hW hupper
    simpa only [M0, M2, I, B, mul_comm] using h

private theorem polynomial_moments_pos (j : ℕ) : 0 < I j ∧ 0 < B j := by
  constructor
  · apply intervalIntegral.intervalIntegral_pos_of_pos_on
      (by apply Continuous.intervalIntegrable; fun_prop) _ (by norm_num)
    intro v _
    exact pow_pos (by positivity) _
  · apply intervalIntegral.intervalIntegral_pos_of_pos_on
      (by apply Continuous.intervalIntegrable; fun_prop) _ (by norm_num)
    intro v hv
    exact mul_pos (sq_pos_of_pos hv.1) (pow_pos (by positivity) _)

def innerTheta (r : ℕ) (z : ℝ) : ℝ := (1 - M0 r z / M2 r z) / 2

private theorem inner_threshold_bounds (r : ℕ) {z : ℝ} (hz : 0 < z) :
    theta r < innerTheta r z ∧ innerTheta r z < theta (r + 1) := by
  obtain ⟨hM0, hM2⟩ := moments_pos r hz
  obtain ⟨hI0, hB0⟩ := polynomial_moments_pos r
  obtain ⟨hI1, hB1⟩ := polynomial_moments_pos (r + 1)
  obtain ⟨hl, hu⟩ := moment_ratio_bounds r hz
  have hl' : M0 r z / M2 r z < I r / B r := by
    apply (div_lt_div_iff₀ hM2 hB0).mpr
    have H := (div_lt_div_iff₀ hI0 hM0).mp hl
    nlinarith
  have hu' : I (r + 1) / B (r + 1) < M0 r z / M2 r z := by
    apply (div_lt_div_iff₀ hB1 hM2).mpr
    have H := (div_lt_div_iff₀ hM0 hI1).mp hu
    nlinarith
  dsimp [theta, innerTheta]
  constructor <;> linarith

/-- The signed kernel in (2.5), with source remainder order r+1 and n=r+2. -/
def L (r : ℕ) (a t : ℝ) : ℝ := t ^ 3 / 4 *
  ∫ v in (0 : ℝ)..1, ((1 - 2 * a) * v ^ 2 - 1) * E r (t ^ 2 / 4 * (1 + v ^ 2))

private theorem kernel_moment_identity (r : ℕ) (a t : ℝ) :
    L r a t = t ^ 3 / 4 * (2 * M2 r (t ^ 2 / 4) *
      (innerTheta r (t ^ 2 / 4) - a)) := by
  by_cases ht : t = 0
  · simp [L, ht]
  have hz : 0 < t ^ 2 / 4 := by positivity
  have hM2 := (moments_pos r hz).2
  have hc : Continuous (fun v : ℝ => E r (t ^ 2 / 4 * (1 + v ^ 2))) :=
    (e_continuous r).comp (by fun_prop)
  have hi : (∫ v in (0 : ℝ)..1,
      ((1 - 2 * a) * v ^ 2 - 1) * E r (t ^ 2 / 4 * (1 + v ^ 2))) =
      (1 - 2 * a) * M2 r (t ^ 2 / 4) - M0 r (t ^ 2 / 4) := by
    calc
      _ = ∫ v in (0 : ℝ)..1, (1 - 2 * a) *
          (v ^ 2 * E r (t ^ 2 / 4 * (1 + v ^ 2))) -
            E r (t ^ 2 / 4 * (1 + v ^ 2)) := by
        apply intervalIntegral.integral_congr
        intro v _
        ring
      _ = _ := by
        rw [intervalIntegral.integral_sub
          (show IntervalIntegrable (fun v : ℝ => (1 - 2 * a) *
              (v ^ 2 * E r (t ^ 2 / 4 * (1 + v ^ 2)))) volume 0 1 from
            (continuous_const.mul ((continuous_id.pow 2).mul hc)).intervalIntegrable 0 1)
          (hc.intervalIntegrable 0 1), intervalIntegral.integral_const_mul]
        rfl
  unfold L
  rw [hi]
  dsimp [innerTheta]
  field_simp [ne_of_gt hM2]
  <;> ring

private theorem kernel_closed_ranges (r : ℕ) (a : ℝ) {t : ℝ} (ht : 0 < t) :
    (a ≤ theta r → 0 < L r a t) ∧
      (theta (r + 1) ≤ a → L r a t < 0) := by
  have hz : 0 < t ^ 2 / 4 := by positivity
  obtain ⟨hl, hu⟩ := inner_threshold_bounds r hz
  have hm := (moments_pos r hz).2
  rw [kernel_moment_identity]
  constructor
  · intro ha
    exact mul_pos (by positivity) (mul_pos (by positivity) (sub_pos.mpr (ha.trans_lt hl)))
  · intro ha
    exact mul_neg_of_pos_of_neg (by positivity)
      (mul_neg_of_pos_of_neg (by positivity) (sub_neg.mpr (hu.trans_le ha)))

/-! Exact original Gamma coefficients and the sharp origin obstruction. -/

private theorem moment_difference (r : ℕ) : B r = I (r + 1) - I r := by
  unfold B I
  rw [← intervalIntegral.integral_sub
    (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop)]
  apply intervalIntegral.integral_congr
  intro v _
  dsimp only
  rw [pow_succ]
  ring

private theorem coefficient_identity (r : ℕ) (a : ℝ) :
    u (r + 2) a (a - 2) =
      (2 * r + 3).factorial / ((4 : ℝ) ^ (r + 1) * r.factorial) *
        (I r + (2 * a - 1) * B r) := by
  have hs : (∑ j ∈ Finset.range (r + 2), coeff j / j.factorial) =
      coeff (r + 2) / ((2 : ℝ) ^ (r + 1) * (r + 1).factorial) * I (r + 1) := by
    simpa only [I, intPow, Nat.add_assoc] using coeff_sum (r + 1)
  have hr : (2 * (r : ℝ) + 3) * I (r + 1) - 2 * (r + 1) * I r =
      (2 : ℝ) ^ (r + 1) := intPow_rec r
  have hd : (2 : ℝ) ^ (r + 1) ≠ 0 := by positivity
  have hfac : ((r + 1).factorial : ℝ) ≠ 0 := by positivity
  have hfr : (r.factorial : ℝ) ≠ 0 := by positivity
  have hfa : ((r + 1).factorial : ℝ) = ((r : ℝ) + 1) * r.factorial := by
    simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have hu : u (r + 2) a (a - 2) = (a - 1) * coeff (r + 2) +
      ((r : ℝ) + 2 - a) * (r + 1).factorial *
        (coeff (r + 2) / ((2 : ℝ) ^ (r + 1) * (r + 1).factorial) * I (r + 1)) := by
    have hsum : (∑ j ∈ Finset.range (r + 2),
        (2 : ℝ) ^ j * Gamma (j + 1 / 2) / (Gamma (1 / 2) * j.factorial)) =
        ∑ j ∈ Finset.range (r + 2), coeff j / j.factorial := by
      apply Finset.sum_congr rfl
      intro j _
      dsimp [coeff]
      ring
    unfold u
    rw [hsum, hs]
    simp only [show r + 2 - 1 = r + 1 by omega]
    dsimp [coeff]
    push_cast
    ring
  have hc : coeff (r + 2) =
      (2 * r + 3).factorial / ((2 : ℝ) ^ (r + 1) * (r + 1).factorial) := by
    apply (eq_div_iff (mul_ne_zero hd hfac)).mpr
    convert coeff_factorial (r + 1) using 1 <;> congr 2 <;> omega
  have hbr : (a - 1) * (2 : ℝ) ^ (r + 1) + ((r : ℝ) + 2 - a) * I (r + 1) =
      ((r : ℝ) + 1) * (I r + (2 * a - 1) * B r) := by
    rw [moment_difference]
    linear_combination (1 - a) * hr
  have hp : (4 : ℝ) ^ (r + 1) = (2 : ℝ) ^ (r + 1) * 2 ^ (r + 1) := by
    rw [← mul_pow]; norm_num
  calc
    _ = coeff (r + 2) / (2 : ℝ) ^ (r + 1) *
        ((a - 1) * 2 ^ (r + 1) + ((r : ℝ) + 2 - a) * I (r + 1)) := by
      rw [hu]
      field_simp [hd, hfac]
      <;> ring
    _ = coeff (r + 2) / (2 : ℝ) ^ (r + 1) *
        (((r : ℝ) + 1) * (I r + (2 * a - 1) * B r)) := by rw [hbr]
    _ = _ := by
      rw [hc, hp]
      simp only [hfa]
      field_simp [hd, hfr, show (r : ℝ) + 1 ≠ 0 by positivity]
      <;> ring

private theorem coefficient_threshold_signs (r : ℕ) (a : ℝ) :
    (u (r + 2) a (a - 2) ≤ 0 ↔ a ≤ theta r) ∧
      (0 ≤ u (r + 2) a (a - 2) ↔ theta r ≤ a) := by
  have hB := (polynomial_moments_pos r).2
  have hc : 0 < ((2 * r + 3).factorial : ℝ) /
      ((4 : ℝ) ^ (r + 1) * r.factorial) := by positivity
  rw [coefficient_identity]
  have hi : I r + (2 * a - 1) * B r = 2 * B r * (a - theta r) := by
    dsimp [theta]
    field_simp [ne_of_gt hB]
    <;> ring
  rw [hi]
  constructor
  · constructor
    · intro h
      by_contra H
      have hp := mul_pos hc (mul_pos (show 0 < 2 * B r by positivity)
        (sub_pos.mpr (lt_of_not_ge H)))
      linarith
    · intro h
      exact mul_nonpos_of_nonneg_of_nonpos hc.le
        (mul_nonpos_of_nonneg_of_nonpos (by positivity) (sub_nonpos.mpr h))
  · rw [mul_nonneg_iff_of_pos_left hc, mul_nonneg_iff_of_pos_left (by positivity)]
    exact sub_nonneg

private theorem positive_sign_necessary (n : ℕ) (hn : 2 ≤ n) (a : ℝ)
    (h : globalNonnegative n a) : a ≤ theta (n - 2) := by
  have he : n - 2 + 2 = n := by omega
  have hs := (coefficient_threshold_signs (n - 2) a).1
  rw [he] at hs
  exact hs.mp (nonnegative_sign_forces_nonpositive_limit (zero_endpoint n hn a) h)

private theorem positive_cm_necessary (n : ℕ) (hn : 2 ≤ n) (a : ℝ)
    (h : completelyMonotone n a) : a ≤ theta (n - 2) :=
  positive_sign_necessary n hn a (cm_sign_projections n a h)

/-! Absolute Laplace control and exact finite subtraction for every real parameter. -/

private theorem kernel_continuous (r : ℕ) (a : ℝ) : Continuous (L r a) := by
  have hc : Continuous (fun p : ℝ × ℝ =>
      ((1 - 2 * a) * p.2 ^ 2 - 1) * E r (p.1 ^ 2 / 4 * (1 + p.2 ^ 2))) :=
    (by fun_prop : Continuous (fun p : ℝ × ℝ => (1 - 2 * a) * p.2 ^ 2 - 1)).mul
      ((e_continuous r).comp (by fun_prop))
  have hi := continuous_parametric_integral_of_continuous (μ := volume)
    (f := fun t v : ℝ => ((1 - 2 * a) * v ^ 2 - 1) *
      E r (t ^ 2 / 4 * (1 + v ^ 2))) hc (s := Icc (0 : ℝ) 1) isCompact_Icc
  simp_rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hi
  exact (by fun_prop : Continuous (fun t : ℝ => t ^ 3 / 4)).mul hi

private theorem kernel_polynomial_bound (r : ℕ) (a : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    ‖L r a t‖ ≤ (|1 - 2 * a| + 1) * t ^ (2 * r + 5) := by
  have hb (v : ℝ) (hv : v ∈ Icc (0 : ℝ) 1) :
      ‖((1 - 2 * a) * v ^ 2 - 1) * E r (t ^ 2 / 4 * (1 + v ^ 2))‖ ≤
        (|1 - 2 * a| + 1) * t ^ (2 * (r + 1)) := by
    have hv2 : v ^ 2 ≤ 1 := by nlinarith [hv.1, hv.2]
    have hy : 0 ≤ t ^ 2 / 4 * (1 + v ^ 2) := by positivity
    have hyt : t ^ 2 / 4 * (1 + v ^ 2) ≤ t ^ 2 := by nlinarith [sq_nonneg t]
    have he := expRemainderBounds (r + 1) hy
    rw [← e_original] at he
    have he' : E r (t ^ 2 / 4 * (1 + v ^ 2)) ≤ t ^ (2 * (r + 1)) := by
      calc
        _ ≤ (t ^ 2 / 4 * (1 + v ^ 2)) ^ (r + 1) / (r + 1).factorial := he.2
        _ ≤ (t ^ 2) ^ (r + 1) :=
          (div_le_self (by positivity)
            (by exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos (r + 1)))).trans
              (pow_le_pow_left₀ hy hyt _)
        _ = _ := by rw [← pow_mul]
    have hw : ‖(1 - 2 * a) * v ^ 2 - 1‖ ≤ |1 - 2 * a| + 1 := by
      calc
        _ ≤ ‖(1 - 2 * a) * v ^ 2‖ + ‖(1 : ℝ)‖ := norm_sub_le _ _
        _ ≤ _ := by
          rw [norm_mul, Real.norm_of_nonneg (sq_nonneg v), norm_one, Real.norm_eq_abs]
          nlinarith [mul_le_of_le_one_right (abs_nonneg (1 - 2 * a)) hv2]
    rw [norm_mul, Real.norm_of_nonneg he.1]
    exact mul_le_mul hw he' he.1 (by positivity)
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 1) (C := (|1 - 2 * a| + 1) * t ^ (2 * (r + 1)))
    (fun v hv => hb v (Ioc_subset_Icc_self
      (by simpa only [uIoc_of_le zero_le_one] using hv)))
  simp only [sub_zero, abs_one, mul_one] at hi
  unfold L
  rw [norm_mul, Real.norm_of_nonneg (by positivity : 0 ≤ t ^ 3 / 4)]
  calc
    _ ≤ t ^ 3 / 4 * ((|1 - 2 * a| + 1) * t ^ (2 * (r + 1))) :=
      mul_le_mul_of_nonneg_left hi (by positivity)
    _ ≤ (|1 - 2 * a| + 1) * t ^ (2 * r + 5) := by
      rw [show 2 * r + 5 = 3 + 2 * (r + 1) by omega, pow_add]
      nlinarith [mul_nonneg (pow_nonneg ht 3)
        (mul_nonneg (by positivity : 0 ≤ |1 - 2 * a| + 1)
          (pow_nonneg ht (2 * (r + 1))))]

private theorem kernel_exponential_moments (r m : ℕ) (a : ℝ) {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun t : ℝ => t ^ m * exp (-x * t) * L r a t) (Ioi 0) := by
  have he := (TwoScaleEndpointMoments.exponential_moment x hx (m + 2 * r + 5)).1
  simp only [← neg_mul] at he
  apply (he.const_mul (|1 - 2 * a| + 1)).mono'
    (((by fun_prop : Continuous (fun t : ℝ => t ^ m * exp (-x * t))).mul
      (kernel_continuous r a)).aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  change ‖t ^ m * exp (-x * t) * L r a t‖ ≤ _
  rw [norm_mul, Real.norm_of_nonneg (mul_nonneg (pow_nonneg ht.le _) (exp_nonneg _))]
  calc
    _ ≤ t ^ m * exp (-x * t) * ((|1 - 2 * a| + 1) * t ^ (2 * r + 5)) :=
      mul_le_mul_of_nonneg_left (kernel_polynomial_bound r a ht.le)
        (mul_nonneg (pow_nonneg ht.le _) (exp_nonneg _))
    _ = _ := by
      rw [show m + 2 * r + 5 = m + (2 * r + 5) by omega, pow_add]
      ring

private theorem kernel_rec (r : ℕ) (a t : ℝ) :
    L (r + 1) a t =
      -(t ^ (2 * r + 5) / ((4 : ℝ) ^ (r + 2) * (r + 1).factorial) *
        (I (r + 1) + (2 * a - 1) * B (r + 1))) - L r a t := by
  have he (y : ℝ) : E (r + 1) y = y ^ (r + 1) / (r + 1).factorial - E r y := by
    simpa only [e_original] using expRemainderRec (r + 1) y
  have hc : Continuous (fun v : ℝ => ((1 - 2 * a) * v ^ 2 - 1) *
      E r (t ^ 2 / 4 * (1 + v ^ 2))) :=
    (by fun_prop : Continuous (fun v : ℝ => (1 - 2 * a) * v ^ 2 - 1)).mul
      ((e_continuous r).comp (by fun_prop))
  have hid (v : ℝ) : ((1 - 2 * a) * v ^ 2 - 1) *
      E (r + 1) (t ^ 2 / 4 * (1 + v ^ 2)) =
      -(t ^ (2 * (r + 1)) / ((4 : ℝ) ^ (r + 1) * (r + 1).factorial)) *
        ((1 + v ^ 2) ^ (r + 1) + (2 * a - 1) * (v ^ 2 * (1 + v ^ 2) ^ (r + 1))) -
      ((1 - 2 * a) * v ^ 2 - 1) * E r (t ^ 2 / 4 * (1 + v ^ 2)) := by
    rw [he, mul_pow, div_pow, ← pow_mul]
    ring
  unfold L
  simp_rw [hid]
  rw [intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop)
      (hc.intervalIntegrable _ _), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop), intervalIntegral.integral_const_mul]
  change t ^ 3 / 4 * (_ * (I (r + 1) + (2 * a - 1) * B (r + 1)) - _) = _
  rw [show 2 * r + 5 = 3 + 2 * (r + 1) by omega, pow_add,
    show r + 2 = (r + 1) + 1 by omega, pow_succ (4 : ℝ)]
  ring

private theorem kernel_laplace_rec (r : ℕ) (a : ℝ) {x : ℝ} (hx : 0 < x) :
    (∫ t in Ioi (0 : ℝ), exp (-x * t) * L (r + 1) a t) =
      -u (r + 3) a (a - 2) / x ^ (2 * r + 6) -
        ∫ t in Ioi (0 : ℝ), exp (-x * t) * L r a t := by
  have hk : IntegrableOn (fun t : ℝ => exp (-x * t) * L r a t) (Ioi 0) := by
    simpa only [pow_zero, one_mul] using kernel_exponential_moments r 0 a hx
  have hm := TwoScaleEndpointMoments.exponential_moment x hx (2 * r + 5)
  simp only [← neg_mul] at hm
  let c := -(I (r + 1) + (2 * a - 1) * B (r + 1)) /
    ((4 : ℝ) ^ (r + 2) * (r + 1).factorial)
  calc
    _ = ∫ t in Ioi (0 : ℝ), (t ^ (2 * r + 5) * exp (-x * t)) * c -
        exp (-x * t) * L r a t := by
      apply integral_congr_ae
      filter_upwards with t
      rw [kernel_rec]
      dsimp [c]
      ring
    _ = (∫ t in Ioi (0 : ℝ), t ^ (2 * r + 5) * exp (-x * t)) * c -
        ∫ t in Ioi (0 : ℝ), exp (-x * t) * L r a t := by
      rw [integral_sub (hm.1.mul_const c) hk, integral_mul_const]
    _ = _ := by
      rw [hm.2, show r + 3 = (r + 1) + 2 by omega, coefficient_identity]
      dsimp [c]
      simp only [show 2 * (r + 1) + 3 = 2 * r + 5 by omega,
        show 2 * r + 5 + 1 = 2 * r + 6 by omega,
        show r + 1 + 1 = r + 2 by omega]
      ring

private theorem kernel_zero (a t : ℝ) :
    L 0 a t = G a t - t ^ 3 / 4 * (I 0 + (2 * a - 1) * B 0) := by
  have he (y : ℝ) : E 0 y = 1 - exp (-y) := by
    rw [e_original, expRemainder_eq]
    norm_num
  rw [gaussian_kernel_identity]
  unfold L
  simp_rw [he]
  have hi : (∫ v in (0 : ℝ)..1, ((1 - 2 * a) * v ^ 2 - 1) *
      (1 - exp (-(t ^ 2 / 4 * (1 + v ^ 2)))) ) =
      (∫ v in (0 : ℝ)..1, (1 + (2 * a - 1) * v ^ 2) *
        exp (-(1 + v ^ 2) * t ^ 2 / 4)) - (I 0 + (2 * a - 1) * B 0) := by
    rw [show I 0 + (2 * a - 1) * B 0 =
        ∫ v in (0 : ℝ)..1, 1 + (2 * a - 1) * v ^ 2 by
      simp only [I, B, pow_zero, mul_one]
      rw [intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
        (by apply Continuous.intervalIntegrable; fun_prop), intervalIntegral.integral_const_mul]]
    rw [← intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop)]
    apply intervalIntegral.integral_congr
    intro v _
    dsimp only
    rw [show -(t ^ 2 / 4 * (1 + v ^ 2)) = -(1 + v ^ 2) * t ^ 2 / 4 by ring]
    ring
  rw [hi]
  ring

private theorem gaussian_exponential_integrable (a : ℝ) {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun t : ℝ => exp (-x * t) * G a t) (Ioi 0) := by
  have hk : IntegrableOn (fun t : ℝ => exp (-x * t) * L 0 a t) (Ioi 0) := by
    simpa only [pow_zero, one_mul] using kernel_exponential_moments 0 0 a hx
  have hm := (TwoScaleEndpointMoments.exponential_moment x hx 3).1
  simp only [← neg_mul] at hm
  apply (hk.add (hm.mul_const ((I 0 + (2 * a - 1) * B 0) / 4))).congr
  filter_upwards with t
  dsimp only [Pi.add_apply]
  rw [kernel_zero]
  ring

private theorem kernel_laplace_zero (a : ℝ) {x : ℝ} (hx : 0 < x) :
    (∫ t in Ioi (0 : ℝ), exp (-x * t) * L 0 a t) =
      (∫ t in Ioi (0 : ℝ), exp (-x * t) * G a t) - u 2 a (a - 2) / x ^ 4 := by
  have hm := TwoScaleEndpointMoments.exponential_moment x hx 3
  simp only [← neg_mul] at hm
  calc
    _ = ∫ t in Ioi (0 : ℝ), exp (-x * t) * G a t -
        (t ^ 3 * exp (-x * t)) * ((I 0 + (2 * a - 1) * B 0) / 4) := by
      apply integral_congr_ae
      filter_upwards with t
      rw [kernel_zero]
      ring
    _ = _ := by
      rw [integral_sub (gaussian_exponential_integrable a hx) (hm.1.mul_const _),
        integral_mul_const, hm.2]
      have hu := coefficient_identity 0 a
      norm_num at hu
      rw [hu]
      ring

private theorem laplace_finite_subtraction (r : ℕ) (a : ℝ) {x : ℝ} (hx : 0 < x) :
    (∫ t in Ioi (0 : ℝ), exp (-x * t) * L r a t) =
      (-1 : ℝ) ^ (r + 2) *
        ((∫ t in Ioi (0 : ℝ), exp (-x * t) * G a t) -
          ∑ k ∈ Finset.Icc 1 (r + 2), (-1 : ℝ) ^ k * u k a (a - 2) / x ^ (2 * k)) := by
  induction r with
  | zero =>
    simpa [show Finset.Icc 1 2 = {1, 2} by decide, coefficient_one_zero]
      using kernel_laplace_zero a hx
  | succ r ih =>
    rw [kernel_laplace_rec r a hx, ih,
      show r + 1 + 2 = (r + 2) + 1 by omega,
      Finset.sum_Icc_succ_top (by omega : 1 ≤ (r + 2) + 1), pow_succ]
    have hs : (-1 : ℝ) ^ (r + 2) * (-1 : ℝ) ^ (r + 2) = 1 := by
      rw [← mul_pow]
      norm_num
    have hp : 2 * (r + 2 + 1) = 2 * r + 6 := by omega
    simp only [pow_succ, hp]
    linear_combination (u (r + 3) a (a - 2) / x ^ (2 * r + 6)) * hs

private theorem f_laplace_defect (r : ℕ) (a : ℝ) {x : ℝ} (hx : 0 < x) :
    F (r + 2) a x - (∫ t in Ioi (0 : ℝ), exp (-x * t) * L r a t) =
      (-1 : ℝ) ^ (r + 2) *
        (Y a (a - 2) x - (a - 1) - ∫ t in Ioi (0 : ℝ), exp (-x * t) * G a t) := by
  rw [laplace_finite_subtraction r a hx]
  unfold F D
  ring

/-! Differentiation of the actual signed kernel requires no parameter sign premise. -/

private theorem signed_kernel_moment_deriv (r m : ℕ) (a : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (moment (L r a) m) (moment (L r a) (m + 1) x) x := by
  have hint : IntegrableOn (fun t : ℝ => (-t) ^ m * exp (-x * t) * L r a t) (Ioi 0) := by
    apply ((kernel_exponential_moments r m a hx).const_mul ((-1 : ℝ) ^ m)).congr
    filter_upwards with t
    rw [neg_eq_neg_one_mul, mul_pow]
    ring
  have hb := (TwoScaleEndpointMoments.exponential_moment (x / 2) (half_pos hx)
    (m + 1 + 2 * r + 5)).1.const_mul (|1 - 2 * a| + 1)
  simp only [← neg_mul] at hb
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun y t : ℝ => (-t) ^ m * exp (-y * t) * L r a t)
    (F' := fun y t : ℝ => (-t) ^ (m + 1) * exp (-y * t) * L r a t)
    (s := Ioi (x / 2))
    (bound := fun t : ℝ => (|1 - 2 * a| + 1) *
      (t ^ (m + 1 + 2 * r + 5) * exp (-(x / 2) * t)))
    (Ioi_mem_nhds (by linarith : x / 2 < x))
    (Eventually.of_forall (fun y =>
      (((by fun_prop : Continuous (fun t : ℝ => (-t) ^ m * exp (-y * t))).mul
        (kernel_continuous r a)).aestronglyMeasurable))) hint
    (((by fun_prop : Continuous (fun t : ℝ => (-t) ^ (m + 1) * exp (-x * t))).mul
      (kernel_continuous r a)).aestronglyMeasurable)
    ?_ hb ?_).2
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    intro y hy
    have hex : exp (-y * t) ≤ exp (-(x / 2) * t) := by
      apply exp_le_exp.mpr
      change x / 2 < y at hy
      change 0 < t at ht
      nlinarith
    simp only [norm_mul, norm_pow, norm_neg, Real.norm_of_nonneg ht.le,
      Real.norm_of_nonneg (exp_nonneg _)]
    calc
      _ ≤ t ^ (m + 1) * exp (-(x / 2) * t) * ‖L r a t‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hex (pow_nonneg ht.le _)) (norm_nonneg _)
      _ ≤ t ^ (m + 1) * exp (-(x / 2) * t) *
          ((|1 - 2 * a| + 1) * t ^ (2 * r + 5)) :=
        mul_le_mul_of_nonneg_left (kernel_polynomial_bound r a ht.le)
          (mul_nonneg (pow_nonneg ht.le _) (exp_nonneg _))
      _ = _ := by
        rw [show m + 1 + 2 * r + 5 = (m + 1) + (2 * r + 5) by omega, pow_add]
        ring
  · filter_upwards with t
    intro y _
    convert ((((hasDerivAt_id y).neg.mul_const t).exp).const_mul
      ((-t) ^ m)).mul_const (L r a t) using 1 <;>
      simp only [Pi.neg_apply, id_eq, pow_succ] <;> ring

private theorem signed_kernel_moment_iterated (r : ℕ) (a : ℝ) (m : ℕ) :
    EqOn (iteratedDeriv m (moment (L r a) 0)) (moment (L r a) m) (Ioi 0) := by
  induction m with
  | zero => intro x _; rfl
  | succ m ih =>
    intro x hx
    rw [iteratedDeriv_succ]
    have he : iteratedDeriv m (moment (L r a) 0) =ᶠ[𝓝 x] moment (L r a) m := by
      filter_upwards [Ioi_mem_nhds hx] with y hy
      exact ih hy
    exact he.deriv_eq.trans (signed_kernel_moment_deriv r m a hx).deriv

/-! The Gaussian identity removes the defect and leaves the actual original F. -/

private theorem actual_f_laplace (r : ℕ) (a : ℝ) {x : ℝ} (hx : 0 < x) :
    F (r + 2) a x = ∫ t in Ioi (0 : ℝ), exp (-x * t) * L r a t := by
  have h := f_laplace_defect r a hx
  rw [gaussian_laplace_identity a hx] at h
  linarith

private theorem actual_f_iterated_deriv (r m : ℕ) (a : ℝ) {x : ℝ} (hx : 0 < x) :
    iteratedDeriv m (F (r + 2) a) x =
      ∫ t in Ioi (0 : ℝ), (-t) ^ m * exp (-x * t) * L r a t := by
  have he : EqOn (F (r + 2) a) (moment (L r a) 0) (Ioi 0) := by
    intro y hy
    simpa only [moment, pow_zero, one_mul] using actual_f_laplace r a hy
  have hd := he.iteratedDeriv_of_isOpen isOpen_Ioi m hx
  rw [signed_kernel_moment_iterated r a m hx] at hd
  exact hd

private theorem positive_cm_sufficiency (n : ℕ) (hn : 2 ≤ n) (a : ℝ)
    (ha : a ≤ theta (n - 2)) : completelyMonotone n a := by
  let r : ℕ := n - 2
  have hnr : n = r + 2 := by
    dsimp [r]
    omega
  have ha' : a ≤ theta r := by
    simpa [r] using ha
  rw [hnr]
  refine ⟨(regularity_and_origin (r + 2) (by omega) a).1, ?_⟩
  intro m x hx
  rw [actual_f_iterated_deriv r m a hx, ← integral_const_mul]
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : 0 < t := ht
  have hs : (-1 : ℝ) ^ m * (-t) ^ m = t ^ m := by
    rw [← mul_pow]
    congr 1
    ring
  rw [← mul_assoc, ← mul_assoc, hs]
  exact mul_nonneg
    (mul_nonneg (pow_nonneg ht.le _) (exp_nonneg _))
    ((kernel_closed_ranges r a ht).1 ha').le

private theorem negative_cm_sufficiency (n : ℕ) (hn : 2 ≤ n) (a : ℝ)
    (ha : theta (n - 1) ≤ a) :
    CompletelyMonotoneOn (fun x => -F n a x) := by
  let r : ℕ := n - 2
  have hnr : n = r + 2 := by
    dsimp [r]
    omega
  have hna : n - 1 = r + 1 := by
    dsimp [r]
    omega
  have ha' : theta (r + 1) ≤ a := by
    rw [← hna]
    exact ha
  rw [hnr]
  refine ⟨(regularity_and_origin (r + 2) (by omega) a).1.neg, ?_⟩
  intro m x hx
  have hfun : (fun x : ℝ => -F (r + 2) a x) = -(F (r + 2) a) := by
    rfl
  rw [hfun, iteratedDeriv_neg, actual_f_iterated_deriv r m a hx]
  rw [← integral_neg, ← integral_const_mul]
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : 0 < t := ht
  have hs : (-1 : ℝ) ^ m * (-(-t) ^ m) = -t ^ m := by
    calc
      (-1 : ℝ) ^ m * (-(-t) ^ m) = -(((-1 : ℝ) ^ m) * (-t) ^ m) := by ring
      _ = -t ^ m := by
        rw [← mul_pow]
        norm_num
  calc
    0 ≤ ((-t ^ m) * exp (-x * t)) * L r a t := by
      have htm : -t ^ m ≤ 0 := neg_nonpos.mpr (pow_nonneg ht0.le _)
      have hfirst : (-t ^ m) * exp (-x * t) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg htm (exp_nonneg _)
      exact mul_nonneg_of_nonpos_of_nonpos hfirst
        ((kernel_closed_ranges r a ht0).2 ha').le
    _ = (-1 : ℝ) ^ m * (-((-t) ^ m * exp (-x * t) * L r a t)) := by
      rw [← hs]
      ring

private theorem positive_chain (n : ℕ) (hn : 2 ≤ n) (a : ℝ) :
    (globalNonnegative n a ↔ completelyMonotone n a) ∧
      (completelyMonotone n a ↔ a ≤ theta (n - 2)) := by
  constructor
  · constructor
    · intro h
      exact positive_cm_sufficiency n hn a (positive_sign_necessary n hn a h)
    · exact cm_sign_projections n a
  · constructor
    · exact positive_cm_necessary n hn a
    · exact positive_cm_sufficiency n hn a

/-! A quantitative next-remainder bound gives the original infinity limit. -/

private theorem actual_f_bound (r : ℕ) (a : ℝ) {x : ℝ} (hx : 0 < x) :
    ‖F (r + 2) a x‖ ≤
      (|1 - 2 * a| + 1) * (2 * r + 5).factorial / x ^ (2 * r + 6) := by
  have hm := TwoScaleEndpointMoments.exponential_moment x hx (2 * r + 5)
  simp only [← neg_mul] at hm
  rw [actual_f_laplace r a hx]
  calc
    _ ≤ ∫ t in Ioi (0 : ℝ),
        (|1 - 2 * a| + 1) * (t ^ (2 * r + 5) * exp (-x * t)) := by
      apply norm_integral_le_of_norm_le (hm.1.const_mul _)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [norm_mul, Real.norm_of_nonneg (exp_nonneg _)]
      calc
        _ ≤ exp (-x * t) * ((|1 - 2 * a| + 1) * t ^ (2 * r + 5)) :=
          mul_le_mul_of_nonneg_left (kernel_polynomial_bound r a ht.le) (exp_nonneg _)
        _ = _ := by ring
    _ = _ := by
      rw [integral_const_mul, hm.2]
      simp only [show 2 * r + 5 + 1 = 2 * r + 6 by omega]
      ring

private theorem rescaled_f_vanishes_at_infinity (r : ℕ) (a : ℝ) :
    Tendsto (fun x : ℝ => x ^ (2 * r + 4) * F (r + 2) a x) atTop (𝓝 0) := by
  have hb : ∀ᶠ x : ℝ in atTop,
      ‖x ^ (2 * r + 4) * F (r + 2) a x‖ ≤
        ((|1 - 2 * a| + 1) * (2 * r + 5).factorial) * (x⁻¹) ^ 2 := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [norm_mul, Real.norm_of_nonneg (pow_nonneg hx.le _)]
    calc
      _ ≤ x ^ (2 * r + 4) *
          ((|1 - 2 * a| + 1) * (2 * r + 5).factorial / x ^ (2 * r + 6)) :=
        mul_le_mul_of_nonneg_left (actual_f_bound r a hx) (pow_nonneg hx.le _)
      _ = _ := by
        rw [show 2 * r + 6 = (2 * r + 4) + 2 by omega, pow_add]
        field_simp
        simp only [pow_add]
        ring
  apply squeeze_zero_norm' hb
  simpa using (tendsto_const_nhds (x :=
    (|1 - 2 * a| + 1) * ((2 * r + 5).factorial : ℝ))).mul
      ((tendsto_inv_atTop_zero : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0)).pow 2)

private theorem infinity_endpoint (n : ℕ) (hn : 2 ≤ n) (a : ℝ) :
    Tendsto (fun x : ℝ => x ^ (2 * n + 2) * F n a x) atTop
      (𝓝 (-u (n + 1) a (a - 2))) := by
  let r := n - 2
  have hnr : n = r + 2 := by dsimp [r]; omega
  rw [hnr]
  have hl := (tendsto_const_nhds (x := -u (r + 3) a (a - 2))).sub
    (rescaled_f_vanishes_at_infinity (r + 1) a)
  simp only [sub_zero] at hl
  apply hl.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have hr := kernel_laplace_rec r a hx
  rw [← actual_f_laplace (r + 1) a hx, ← actual_f_laplace r a hx] at hr
  have hp : x ^ (2 * r + 6) ≠ 0 := pow_ne_zero _ hx.ne'
  have he : x ^ (2 * r + 6) * F (r + 2) a x =
      -u (r + 3) a (a - 2) - x ^ (2 * r + 6) * F (r + 3) a x := by
    have hh := (eq_div_iff hp).mp (show F (r + 2) a x + F (r + 3) a x =
        -u (r + 3) a (a - 2) / x ^ (2 * r + 6) by
      simpa only [show r + 1 + 2 = r + 3 by omega] using (by linarith :
        F (r + 2) a x + F (r + 1 + 2) a x =
          -u (r + 3) a (a - 2) / x ^ (2 * r + 6)))
    nlinarith [hh]
  simpa only [show 2 * (r + 2) + 2 = 2 * r + 6 by omega,
    show 2 * (r + 1) + 4 = 2 * r + 6 by omega,
    show r + 1 + 2 = r + 3 by omega, show r + 2 + 1 = r + 3 by omega] using he.symm

private theorem negative_sign_sharp_necessary (n : ℕ) (hn : 2 ≤ n) (a : ℝ)
    (h : globalNonpositive n a) : theta (n - 1) ≤ a := by
  have hl := (infinity_endpoint n hn a).neg
  have hev : ∀ᶠ x : ℝ in atTop, -(x ^ (2 * n + 2) * F n a x) ∈ Ici (0 : ℝ) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    change 0 ≤ -(x ^ (2 * n + 2) * F n a x)
    rw [neg_mul_eq_mul_neg]
    exact mul_nonneg (pow_nonneg hx.le _) (h x hx)
  have hu : 0 ≤ u (n + 1) a (a - 2) := by
    simpa only [neg_neg, mem_Ici] using isClosed_Ici.mem_of_tendsto hl hev
  have hs := (coefficient_threshold_signs (n - 1) a).2
  rw [show n - 1 + 2 = n + 1 by omega] at hs
  exact hs.mp hu

private theorem negative_chain (n : ℕ) (hn : 2 ≤ n) (a : ℝ) :
    (globalNonpositive n a ↔ CompletelyMonotoneOn (fun x => -F n a x)) ∧
      (CompletelyMonotoneOn (fun x => -F n a x) ↔ theta (n - 1) ≤ a) := by
  constructor
  · exact ⟨fun h => negative_cm_sufficiency n hn a
      (negative_sign_sharp_necessary n hn a h), neg_cm_sign_projection n a⟩
  · exact ⟨fun h => negative_sign_sharp_necessary n hn a
      (neg_cm_sign_projection n a h), negative_cm_sufficiency n hn a⟩

theorem result : theorem21 := by
  intro n hn a
  exact ⟨positive_chain n hn a, negative_chain n hn a⟩

end D5.S3.Analytic.XuYangMillsRemainder.GeneralParameter
