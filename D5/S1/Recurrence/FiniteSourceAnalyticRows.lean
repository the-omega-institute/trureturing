/- GID: D5/S1/Recurrence/FiniteSourceAnalyticRows
   generality: G
   mirror-B: D5/B/S1/Recurrence/FiniteSourceAnalyticRows
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Finite-boundary rows are Taylor series of explicit rational functions. -/

import D5.S1.Recurrence.Algebraic.RecursiveBoundaryRowSeries
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Tactic

set_option autoImplicit false

open Finset PowerSeries Filter
open scoped Topology NNReal ENNReal

namespace D5.S1.Recurrence.FiniteSourceAnalyticRows

open Algebraic.RecursiveBoundaryRowSeries

variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K] [CharZero K]

/-- The finite source polynomial, normalized to have constant coefficient one. -/
def finiteSource (b : ℕ → K) (M : ℕ) (z : K) : K :=
  1 + z * ∑ i ∈ range (M + 1), b i * z ^ i

/-- The finite polynomial formed from the boundary starting at row n. -/
def finiteTail (b : ℕ → K) (M n : ℕ) (z : K) : K :=
  ∑ j ∈ range (M + 1), b (n + j) * z ^ j

/-- The rational row, considered as a germ at zero. -/
def rationalRow (b : ℕ → K) (M n : ℕ) (z : K) : K :=
  (finiteSource b M z)⁻¹ * finiteTail b M n (z / finiteSource b M z)

/-- Every normalized derivative of a finite-source rational row is its actual recursive
array entry, and these entries form a convergent power-series germ. -/
theorem result (b : ℕ → K) (M : ℕ) (hs : ∀ i, M < i → b i = 0) :
    (∀ n k, iteratedDeriv k (rationalRow b M n) 0 / (k.factorial : K) = array b n k) ∧
    ∀ n, HasFPowerSeriesAt (rationalRow b M n)
      (FormalMultilinearSeries.ofScalars K (array b n)) 0 := by
  classical
  let Rep := fun (f : K → K) (p : PowerSeries K) =>
    HasFPowerSeriesAt f (FormalMultilinearSeries.ofScalars K (fun k => coeff k p)) 0
  have hrep : ∀ f p, Rep f p ↔
      ∀ᶠ z in 𝓝 (0 : K), HasSum (fun k => coeff k p * z ^ k) (f z) := by
    intro f p
    simp only [Rep, hasFPowerSeriesAt_iff, FormalMultilinearSeries.coeff_ofScalars,
      zero_add, smul_eq_mul, mul_comm]
  have hc : ∀ c : K, Rep (fun _ => c) (C c) := by
    intro c
    rw [hrep]
    refine Eventually.of_forall fun z => ?_
    convert (hasSum_ite_eq (0 : ℕ) c) using 1
    ext k
    by_cases hk : k = 0 <;> simp [coeff_C, hk]
  have hx : Rep (fun z : K => z) X := by
    rw [hrep]
    refine Eventually.of_forall fun z => ?_
    convert (hasSum_ite_eq (1 : ℕ) z) using 1
    ext k
    by_cases hk : k = 1 <;> simp [coeff_X, hk]
  have hadd : ∀ f g p q, Rep f p → Rep g q → Rep (fun z => f z + g z) (p + q) := by
    intro f g p q hf hg
    rw [hrep] at hf hg ⊢
    filter_upwards [hf, hg] with z hf hg
    simpa [add_mul] using hf.add hg
  have hmul : ∀ f g p q, Rep f p → Rep g q → Rep (fun z => f z * g z) (p * q) := by
    intro f g p q hf hg
    have habs : ∀ f p, Rep f p → ∀ᶠ z in 𝓝 (0 : K),
        Summable (fun k => ‖coeff k p * z ^ k‖) := by
      intro f p ⟨r, hr⟩
      filter_upwards [Metric.eball_mem_nhds (0 : K) hr.r_pos] with z hz
      have hz' : (‖z‖₊ : ℝ≥0∞) < r := by simpa [enorm_eq_nnnorm] using hz
      simpa [norm_mul, norm_pow, mul_comm, FormalMultilinearSeries.ofScalars_norm] using
        (FormalMultilinearSeries.ofScalars K (fun k => coeff k p)).summable_norm_mul_pow
          (hz'.trans_le hr.r_le)
    have hfabs := habs f p hf
    have hgabs := habs g q hg
    rw [hrep] at hf hg ⊢
    filter_upwards [hf, hg, hfabs, hgabs] with z hf hg hfabs hgabs
    have h := hasSum_sum_range_mul_of_summable_norm hfabs hgabs
    rw [hf.tsum_eq, hg.tsum_eq] at h
    convert h using 1
    ext k
    rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, sum_mul]
    apply sum_congr rfl
    intro j hj
    have hjk : j + (k - j) = k := Nat.add_sub_of_le (Nat.le_of_lt_succ (mem_range.mp hj))
    rw [show z ^ k = z ^ j * z ^ (k - j) by rw [← pow_add, hjk]]
    ring
  have hB : Rep (fun z => ∑ i ∈ range (M + 1), b i * z ^ i) (mk b) := by
    rw [hrep]
    refine Eventually.of_forall fun z => ?_
    simp only [coeff_mk]
    exact hasSum_sum_of_ne_finset_zero (fun i hi => by
      rw [hs i (by simpa using hi), zero_mul])
  have hF : Rep (finiteSource b M) (source b) := by
    exact hadd _ _ _ _ (hc 1) (hmul _ _ _ _ hx hB)
  have hF0 : finiteSource b M 0 = 1 := by simp [finiteSource]
  have hFa : AnalyticAt K (finiteSource b M) 0 := hF.analyticAt
  have hFne : ∀ᶠ z in 𝓝 (0 : K), finiteSource b M z ≠ 0 :=
    hFa.continuousAt.eventually_ne (by rw [hF0]; exact one_ne_zero)
  have hra : ∀ n, AnalyticAt K (rationalRow b M n) 0 := by
    intro n
    unfold rationalRow finiteTail
    apply (hFa.inv (by rw [hF0]; exact one_ne_zero)).mul
    apply Finset.analyticAt_fun_sum
    intro j hj
    exact analyticAt_const.mul ((analyticAt_id.div hFa (by rw [hF0]; exact one_ne_zero)).pow j)
  have htail : ∀ n z, finiteTail b M n z = b n + z * finiteTail b M (n + 1) z := by
    intro n z
    unfold finiteTail
    have hend : b (n + (M + 1)) = 0 := hs _ (by omega)
    have he := sum_range_succ' (fun j => b (n + j) * z ^ j) (M + 1)
    rw [sum_range_succ, hend, zero_mul, add_zero] at he
    rw [he]
    simp only [Nat.add_zero, pow_zero, mul_one]
    rw [mul_sum, add_comm]
    congr 1
    apply sum_congr rfl
    intro j hj
    rw [pow_succ]
    simp only [show n + (j + 1) = n + 1 + j by omega]
    ring
  have hrow : ∀ n, ∀ᶠ z in 𝓝 (0 : K),
      finiteSource b M z * rationalRow b M n z =
        b n + z * rationalRow b M (n + 1) z := by
    intro n
    filter_upwards [hFne] with z hz
    unfold rationalRow
    rw [← mul_assoc, mul_inv_cancel₀ hz, one_mul, htail]
    rw [div_eq_mul_inv, mul_assoc]
  let T : ℕ → ℕ → K := fun n k => iteratedDeriv k (rationalRow b M n) 0 / (k.factorial : K)
  have hT : ∀ n, Rep (rationalRow b M n) (row T n) := by
    intro n
    simpa only [Rep, row, coeff_mk] using (hra n).hasFPowerSeriesAt
  have heq : ∀ n, source b * row T n = C (b n) + X * row T (n + 1) := by
    intro n
    have hp := hmul _ _ _ _ hF (hT n)
    have hq := hadd _ _ _ _ (hc (b n)) (hmul _ _ _ _ hx (hT (n + 1)))
    have he := hp.eq_formalMultilinearSeries_of_eventually hq (hrow n)
    ext k
    simpa only [FormalMultilinearSeries.coeff_ofScalars] using
      congrArg (fun p : FormalMultilinearSeries K K K => p.coeff k) he
  have hTE : IsExtension b T := by
    constructor
    · intro n
      simpa [source, row] using congrArg (coeff 0) (heq n)
    · intro n k
      have h := congrArg (coeff (k + 1)) (heq n)
      change coeff (k + 1) ((1 + X * mk b) * row T n) = _ at h
      rw [add_mul, one_mul, mul_assoc, map_add, coeff_succ_X_mul,
        map_add, coeff_succ_X_mul, mul_comm (mk b) (row T n)] at h
      simp only [row, coeff_mk, coeff_C, Nat.add_eq_zero_iff, one_ne_zero,
        and_false, ↓reduceIte, zero_add] at h
      rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
      simp only [coeff_mk] at h
      exact eq_sub_of_add_eq h
  have hTa : T = array b := (Algebraic.RecursiveBoundaryRowSeries.result b).2.1 T hTE
  refine ⟨fun n k => congrFun (congrFun hTa n) k, ?_⟩
  intro n
  simpa only [Rep, row, coeff_mk, hTa] using hT n

/-- The critical amplitude leaves a strict finite-polynomial margin. This yields a
larger zero-free disk, the actual row expansions on that disk, and Cauchy's estimate. -/
theorem critical_radius (b : ℕ → ℂ) (M : ℕ) (hs : ∀ i, M < i → b i = 0)
    (A ρ : ℝ) (hA : 0 < A) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hcrit : A * ρ = (1 - ρ) ^ 2) (hb : ∀ i, ‖b i‖ ≤ A) :
    ∃ R : ℝ, ρ < R ∧ R < 1 ∧
      (∀ z : ℂ, ‖z‖ ≤ R → ρ < ‖finiteSource b M z‖) ∧
      (∀ n, HasFPowerSeriesOnBall (rationalRow b M n)
        (FormalMultilinearSeries.ofScalars ℂ (array b n)) 0 (ENNReal.ofReal R)) ∧
      ∀ n k, ‖array b n k‖ ≤
        Real.circleAverage (fun z => ‖rationalRow b M n z‖) 0 R * R⁻¹ ^ k := by
  classical
  let Q : ℝ → ℝ := fun r => A * r * ∑ i ∈ range (M + 1), r ^ i
  have hQr : Q ρ = (1 - ρ) * (1 - ρ ^ (M + 1)) := by
    dsimp [Q]
    rw [hcrit, ← geom_sum_mul_neg ρ (M + 1)]
    ring
  have hmargin : Q ρ < 1 - ρ := by
    rw [hQr]
    have hp := mul_pos (sub_pos.mpr hρ1) (pow_pos hρ (M + 1))
    nlinarith
  have hQc : Continuous Q := by dsimp [Q]; fun_prop
  have hnear : ∀ᶠ r in 𝓝 ρ, Q r < 1 - ρ ∧ r < 1 :=
    (hQc.continuousAt.eventually (gt_mem_nhds hmargin)).and (gt_mem_nhds hρ1)
  have hright : ∀ᶠ r in 𝓝[>] ρ, Q r < 1 - ρ ∧ r < 1 :=
    hnear.filter_mono nhdsWithin_le_nhds
  obtain ⟨R, ⟨hQR, hR1⟩, hR⟩ := (hright.and self_mem_nhdsWithin).exists
  have hRpos : 0 < R := hρ.trans hR
  have hbound : ∀ z : ℂ, ‖z‖ ≤ R → ρ < ‖finiteSource b M z‖ := by
    intro z hz
    have hsum : ‖∑ i ∈ range (M + 1), b i * z ^ i‖ ≤
        A * ∑ i ∈ range (M + 1), R ^ i := by
      calc
        _ ≤ ∑ i ∈ range (M + 1), ‖b i * z ^ i‖ := norm_sum_le _ _
        _ ≤ ∑ i ∈ range (M + 1), A * R ^ i := by
          apply sum_le_sum
          intro i hi
          rw [norm_mul, norm_pow]
          exact mul_le_mul (hb i) (pow_le_pow_left₀ (norm_nonneg z) hz i)
            (pow_nonneg (norm_nonneg z) i) hA.le
        _ = _ := (mul_sum _ _ _).symm
    have hu : ‖z * ∑ i ∈ range (M + 1), b i * z ^ i‖ ≤ Q R := by
      rw [norm_mul]
      exact (mul_le_mul hz hsum (norm_nonneg _) hRpos.le).trans_eq (by dsimp [Q]; ring)
    have hlo := norm_sub_norm_le (1 : ℂ)
      (-(z * ∑ i ∈ range (M + 1), b i * z ^ i))
    simp only [norm_one, norm_neg, sub_neg_eq_add] at hlo
    change ρ < ‖1 + z * ∑ i ∈ range (M + 1), b i * z ^ i‖
    linarith
  have hnonzero : ∀ z : ℂ, ‖z‖ ≤ R → finiteSource b M z ≠ 0 := by
    intro z hz
    exact norm_pos_iff.mp (hρ.trans (hbound z hz))
  have hFa : ∀ z : ℂ, AnalyticAt ℂ (finiteSource b M) z := by
    intro z
    unfold finiteSource
    fun_prop
  have hdiff : ∀ n, DifferentiableOn ℂ (rationalRow b M n) (Metric.closedBall 0 R) := by
    intro n z hz
    have hne := hnonzero z (by simpa using hz)
    apply DifferentiableAt.differentiableWithinAt
    apply AnalyticAt.differentiableAt
    unfold rationalRow finiteTail
    apply ((hFa z).inv hne).mul
    apply Finset.analyticAt_fun_sum
    intro j hj
    exact analyticAt_const.mul ((analyticAt_id.div (hFa z) hne).pow j)
  let r : ℝ≥0 := ⟨R, hRpos.le⟩
  have hC : ∀ n, HasFPowerSeriesOnBall (rationalRow b M n)
      (cauchyPowerSeries (rationalRow b M n) 0 R) 0 (ENNReal.ofReal R) := by
    intro n
    have he : ENNReal.ofReal R = (r : ℝ≥0∞) :=
      ENNReal.ofReal_eq_coe_nnreal hRpos.le
    rw [he]
    exact (hdiff n).hasFPowerSeriesOnBall (R := r) (show 0 < r from hRpos)
  have hcoeff : ∀ n, FormalMultilinearSeries.ofScalars ℂ (array b n) =
      cauchyPowerSeries (rationalRow b M n) 0 R := by
    intro n
    exact ((result b M hs).2 n).eq_formalMultilinearSeries (hC n).hasFPowerSeriesAt
  refine ⟨R, hR, hR1, hbound, ?_, ?_⟩
  · intro n
    rw [hcoeff]
    exact hC n
  · intro n k
    have hn := norm_cauchyPowerSeries_le (rationalRow b M n) 0 R k
    rw [← hcoeff] at hn
    simpa [FormalMultilinearSeries.ofScalars_norm, abs_of_pos hRpos,
      Real.circleAverage, smul_eq_mul] using hn

end D5.S1.Recurrence.FiniteSourceAnalyticRows
