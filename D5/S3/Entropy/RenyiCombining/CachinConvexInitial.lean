/- GID: D5/S3/Entropy/RenyiCombining/CachinConvexInitial
   generality: G
   mirror-B: D5/B/S3/Entropy/RenyiCombining/CachinConvexInitial
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Analytic initial jets of the binary Renyi Riccati quotient. -/

import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Tactic

/-! A removable quotient in the bias variable supplies the initial curvature data. -/

open Set Filter
open scoped Topology

namespace D5.S3.Entropy.RenyiCombining.CachinConvexInitial

noncomputable def H (n t : ℝ) : ℝ :=
  dslope (fun s : ℝ => (1 + s) ^ n - (1 - s) ^ n) 0 t
noncomputable def K (n t : ℝ) : ℝ := (1 + t) ^ n + (1 - t) ^ n
noncomputable def Q (n t : ℝ) : ℝ := n * K n t / H n t

private noncomputable def pneg (n : ℝ) : FormalMultilinearSeries ℝ ℝ ℝ :=
  (binomialSeries ℝ n).compContinuousLinearMap (-ContinuousLinearMap.id ℝ ℝ)

private theorem neg_series (n : ℝ) :
    HasFPowerSeriesAt (fun t : ℝ => (1 - t) ^ n) (pneg n) 0 := by
  have hp : HasFPowerSeriesAt (fun t : ℝ => (1 + t) ^ n) (binomialSeries ℝ n)
      ((-ContinuousLinearMap.id ℝ ℝ) (0 : ℝ)) := by
    simpa using (Real.one_add_rpow_hasFPowerSeriesAt_zero (a := n))
  simpa [pneg, sub_eq_add_neg, Function.comp_def] using hp.compContinuousLinearMap

private theorem H_series (n : ℝ) :
    HasFPowerSeriesAt (H n) ((binomialSeries ℝ n - pneg n).fslope) 0 := by
  exact ((Real.one_add_rpow_hasFPowerSeriesAt_zero (a := n)).sub
    (neg_series n)).has_fpower_series_dslope_fslope

private theorem K_series (n : ℝ) :
    HasFPowerSeriesAt (K n) (binomialSeries ℝ n + pneg n) 0 := by
  exact (Real.one_add_rpow_hasFPowerSeriesAt_zero (a := n)).add (neg_series n)

private theorem iteratedDeriv_of_series {f : ℝ → ℝ}
    {p : FormalMultilinearSeries ℝ ℝ ℝ} (hp : HasFPowerSeriesAt f p 0) (k : ℕ) :
    iteratedDeriv k f 0 = (k.factorial : ℝ) * p.coeff k := by
  have he := congrArg (fun q : FormalMultilinearSeries ℝ ℝ ℝ => q.coeff k)
    (hp.eq_formalMultilinearSeries hp.analyticAt.hasFPowerSeriesAt)
  simp only [FormalMultilinearSeries.coeff_ofScalars] at he
  have hf : (k.factorial : ℝ) ≠ 0 := by positivity
  rw [eq_div_iff hf] at he
  nlinarith [he]

private theorem H_deriv (n : ℝ) (k : ℕ) :
    iteratedDeriv k (H n) 0 = (k.factorial : ℝ) *
      (Ring.choose n (k + 1) - (-1 : ℝ) ^ (k + 1) * Ring.choose n (k + 1)) := by
  rw [iteratedDeriv_of_series (H_series n), FormalMultilinearSeries.coeff_fslope]
  simp [pneg, binomialSeries, FormalMultilinearSeries.ofScalars_comp_neg_id,
    FormalMultilinearSeries.coeff, FormalMultilinearSeries.ofScalars, List.prod_ofFn]

private theorem K_deriv (n : ℝ) (k : ℕ) :
    iteratedDeriv k (K n) 0 = (k.factorial : ℝ) *
      (Ring.choose n k + (-1 : ℝ) ^ k * Ring.choose n k) := by
  rw [iteratedDeriv_of_series (K_series n)]
  simp [pneg, binomialSeries, FormalMultilinearSeries.ofScalars_comp_neg_id,
    FormalMultilinearSeries.coeff, FormalMultilinearSeries.ofScalars, List.prod_ofFn]

theorem H_zero (n : ℝ) : H n 0 = 2 * n := by
  have h := H_deriv n 0
  simp [Ring.choose_one_right] at h
  linarith

theorem Q_analyticAt_zero {n : ℝ} (hn : n ≠ 0) : AnalyticAt ℝ (Q n) 0 := by
  exact ((show AnalyticAt ℝ (fun _ : ℝ => n) 0 from analyticAt_const).mul
    (K_series n).analyticAt).div (H_series n).analyticAt
    (by rw [H_zero]; exact mul_ne_zero (by norm_num) hn)

theorem Q_zero {n : ℝ} (hn : n ≠ 0) : Q n 0 = 1 := by
  norm_num [Q, K, H_zero]
  field_simp

/-- The desingularized quotient agrees with the elementary real-power formula away from zero. -/
theorem Q_eq {n t : ℝ} (ht : t ≠ 0) :
    Q n t = n * t * ((1 + t) ^ n + (1 - t) ^ n) /
      ((1 + t) ^ n - (1 - t) ^ n) := by
  simp only [Q, K, H, dslope_of_ne _ ht, slope_def_field, sub_zero, add_zero, Real.one_rpow, sub_self]
  rw [div_div_eq_mul_div]
  ring

private theorem H_jets (n : ℝ) :
    iteratedDeriv 1 (H n) 0 = 0 ∧
    iteratedDeriv 2 (H n) 0 = 2 * n * (n - 1) * (n - 2) / 3 ∧
    iteratedDeriv 3 (H n) 0 = 0 ∧
    iteratedDeriv 4 (H n) 0 = 2 * n * (n - 1) * (n - 2) * (n - 3) * (n - 4) / 5 := by
  simp only [H_deriv]
  norm_num [Ring.choose_eq_smul, descPochhammer_succ_left, descPochhammer_zero,
    Polynomial.smeval_mul, Polynomial.smeval_sub, Polynomial.smeval_X,
    Polynomial.smeval_natCast, smul_eq_mul]
  <;> ring_nf <;> norm_num

private theorem K_jets (n : ℝ) :
    K n 0 = 2 ∧ iteratedDeriv 1 (K n) 0 = 0 ∧
    iteratedDeriv 2 (K n) 0 = 2 * n * (n - 1) ∧
    iteratedDeriv 3 (K n) 0 = 0 ∧
    iteratedDeriv 4 (K n) 0 = 2 * n * (n - 1) * (n - 2) * (n - 3) := by
  simp only [K_deriv]
  norm_num [K, Ring.choose_eq_smul, descPochhammer_succ_left, descPochhammer_zero,
    Polynomial.smeval_mul, Polynomial.smeval_sub, Polynomial.smeval_X,
    Polynomial.smeval_natCast, smul_eq_mul]
  <;> ring_nf <;> norm_num

theorem Q_jets {n : ℝ} (hn : n ≠ 0) :
    iteratedDeriv 1 (Q n) 0 = 0 ∧
    iteratedDeriv 2 (Q n) 0 = 2 * (n ^ 2 - 1) / 3 ∧
    iteratedDeriv 3 (Q n) 0 = 0 ∧
    iteratedDeriv 4 (Q n) 0 = -8 * (1 - n ^ 2) * (4 - n ^ 2) / 15 := by
  have ha := Q_analyticAt_zero hn
  have hh := (H_series n).analyticAt
  have hk := (K_series n).analyticAt
  have hne : H n 0 ≠ 0 := by rw [H_zero]; exact mul_ne_zero (by norm_num) hn
  have he : (fun t => Q n t * H n t) =ᶠ[𝓝 0] (fun t => n * K n t) := by
    filter_upwards [hh.continuousAt.eventually_ne hne] with t ht
    simp [Q, ht]
  have hrecur (k : ℕ) :
      (∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) *
        iteratedDeriv i (Q n) 0 * iteratedDeriv (k - i) (H n) 0) =
        n * iteratedDeriv k (K n) 0 := by
    have h := he.iteratedDeriv_eq k
    rw [iteratedDeriv_fun_mul ha.contDiffAt hh.contDiffAt,
      iteratedDeriv_const_mul_field] at h
    exact h
  obtain ⟨hH1, hH2, hH3, hH4⟩ := H_jets n
  obtain ⟨hK0, hK1, hK2, hK3, hK4⟩ := K_jets n
  have h1 := hrecur 1
  have h2 := hrecur 2
  have h3 := hrecur 3
  have h4 := hrecur 4
  norm_num [Finset.sum_range_succ, H_zero, Q_zero hn, hH1, hH2, hH3, hH4,
    hK0, hK1, hK2, hK3, hK4, Nat.choose] at h1 h2 h3 h4
  have hQ1 : deriv (Q n) 0 = 0 := h1.resolve_right hn
  have hQ2 : iteratedDeriv 2 (Q n) 0 = 2 * (n ^ 2 - 1) / 3 := by
    have : n * (iteratedDeriv 2 (Q n) 0 - 2 * (n ^ 2 - 1) / 3) = 0 := by
      nlinarith [h2]
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hn)
  have hQ3 : iteratedDeriv 3 (Q n) 0 = 0 := by
    rw [hQ1] at h3
    exact (mul_eq_zero.mp (by nlinarith [h3] : n * iteratedDeriv 3 (Q n) 0 = 0)).resolve_left hn
  refine ⟨by simpa using hQ1, hQ2, hQ3, ?_⟩
  rw [hQ2] at h4
  have : n * (iteratedDeriv 4 (Q n) 0 -
      (-8 * (1 - n ^ 2) * (4 - n ^ 2) / 15)) = 0 := by nlinarith [h4]
  exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hn)

theorem Q_local_derivatives {n : ℝ} (hn : n ≠ 0) :
    ∃ a : ℝ, 0 < a ∧
      (∀ t ∈ Icc 0 a, ∀ k : ℕ,
        HasDerivAt (iteratedDeriv k (Q n)) (iteratedDeriv (k + 1) (Q n) t) t) ∧
      ContinuousAt (iteratedDeriv 4 (Q n)) 0 := by
  have ha := Q_analyticAt_zero hn
  obtain ⟨ε, hε, he⟩ := Metric.eventually_nhds_iff.mp ha.eventually_analyticAt
  refine ⟨ε / 2, by linarith, ?_, ?_⟩
  · intro t ht k
    have hat : AnalyticAt ℝ (Q n) t := he (by
      simp only [Real.dist_eq, sub_zero, abs_of_nonneg ht.1]
      linarith [ht.2])
    have hak : AnalyticAt ℝ (iteratedDeriv k (Q n)) t := by
      simpa only [iteratedDeriv_eq_iterate] using hat.iterated_deriv k
    simpa only [iteratedDeriv_succ] using hak.differentiableAt.hasDerivAt
  · have hak : AnalyticAt ℝ (iteratedDeriv 4 (Q n)) 0 := by
      simpa only [iteratedDeriv_eq_iterate] using ha.iterated_deriv 4
    exact hak.differentiableAt.continuousAt

end D5.S3.Entropy.RenyiCombining.CachinConvexInitial
