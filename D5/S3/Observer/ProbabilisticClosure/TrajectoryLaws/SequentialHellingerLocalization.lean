/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/SequentialHellingerLocalization
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/SequentialHellingerLocalization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Predictable energy localization gives the sequential Hellinger dichotomy. -/

import Mathlib.Probability.Martingale.Convergence
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.Probability.CondVar
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.HistoricalDepthBudgetJointExtremum
import D5.S3.TotalVariation.Bhattacharyya
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.MeasureTheory.Function.ConditionalExpectation.RadonNikodym
import Mathlib.Data.Fin.Tuple.Take
import Mathlib.Tactic

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter Finset
open scoped BigOperators ENNReal NNReal Topology ProbabilityTheory

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.SequentialHellingerLocalization

/-- Truncation uses energy strictly before the current increment. -/
def energyCut {Ω : Type*} (e : ℕ → Ω → ℝ) (K : ℝ) (n : ℕ) : Set Ω :=
  {ω | ∑ i ∈ range n, e i ω ≤ K}

private lemma cut_energy_bound (e : ℕ → ℝ) (he : ∀ i, 0 ≤ e i)
    (he1 : ∀ i, e i ≤ 1) (K : ℝ) (hK : 0 ≤ K) (n : ℕ) :
    (∑ i ∈ range n, if (∑ j ∈ range i, e j) ≤ K then e i else 0) ≤ K + 1 := by
  induction n with
  | zero => simpa using (by linarith : (0 : ℝ) ≤ K + 1)
  | succ n ih =>
    rw [sum_range_succ]
    split_ifs with hn
    · have hle : (∑ i ∈ range n, if (∑ j ∈ range i, e j) ≤ K then e i else 0) ≤
          ∑ i ∈ range n, e i := by
        exact sum_le_sum fun i _ => by split_ifs <;> simp_all
      linarith [he1 n]
    · simpa using ih

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {ℱ : Filtration ℕ m0}

private lemma cut_measurable {e : ℕ → Ω → ℝ} (he : StronglyAdapted ℱ e)
    (K : ℝ) (n : ℕ) : MeasurableSet[ℱ n] (energyCut e K n) := by
  apply measurableSet_le _ measurable_const
  exact (show StronglyMeasurable[ℱ n] (fun ω => ∑ i ∈ range n, e i ω) from by
    simpa only [Finset.sum_apply] using (Finset.stronglyMeasurable_fun_sum (range n) fun i hi =>
      (he i).mono (ℱ.mono (Nat.le_of_lt (mem_range.mp hi))))).measurable

private lemma partial_adapted {d : ℕ → Ω → ℝ}
    (hd : ∀ n, StronglyMeasurable[ℱ (n + 1)] (d n)) :
    StronglyAdapted ℱ (fun n ω => ∑ i ∈ range n, d i ω) := by
  intro n
  simpa only [Finset.sum_apply] using (Finset.stronglyMeasurable_fun_sum (range n) fun i hi =>
    (hd i).mono (ℱ.mono (Nat.succ_le_of_lt (mem_range.mp hi))))

private lemma partial_martingale {d : ℕ → Ω → ℝ}
    (hd : ∀ n, StronglyMeasurable[ℱ (n + 1)] (d n))
    (hi : ∀ n, Integrable (d n) μ) (hc : ∀ n, μ[d n | ℱ n] =ᵐ[μ] 0) :
    Martingale (fun n ω => ∑ i ∈ range n, d i ω) ℱ μ := by
  have hs n : Integrable (fun ω => ∑ i ∈ range n, d i ω) μ :=
    integrable_finsetSum _ fun i _ => hi i
  apply martingale_nat (partial_adapted hd) hs
  intro n
  have heq : (fun ω => ∑ i ∈ range (n + 1), d i ω) =
      (fun ω => ∑ i ∈ range n, d i ω) + d n := by
    ext ω; simp [sum_range_succ]
  rw [heq]
  filter_upwards [condExp_add (hs n) (hi n) (ℱ n), hc n] with ω h1 h2
  rw [h1, Pi.add_apply, h2, Pi.zero_apply, add_zero,
    condExp_of_stronglyMeasurable (ℱ.le n) (partial_adapted hd n) (hs n)]

private lemma partial_square_integral {d : ℕ → Ω → ℝ}
    (hd : ∀ n, StronglyMeasurable[ℱ (n + 1)] (d n))
    (hi : ∀ n, MemLp (d n) 2 μ) (hc : ∀ n, μ[d n | ℱ n] =ᵐ[μ] 0) (n : ℕ) :
    (∫ ω, (∑ i ∈ range n, d i ω) ^ 2 ∂μ) =
      ∑ i ∈ range n, ∫ ω, (d i ω) ^ 2 ∂μ := by
  have hs n : MemLp (fun ω => ∑ i ∈ range n, d i ω) 2 μ :=
    memLp_finsetSum _ fun i _ => hi i
  induction n with
  | zero => simp
  | succ n ih =>
    have hprod : Integrable ((fun ω => ∑ i ∈ range n, d i ω) * d n) μ :=
      (hs n).integrable_mul (hi n)
    have hcross : (∫ ω, (∑ i ∈ range n, d i ω) * d n ω ∂μ) = 0 := by
      rw [← integral_condExp (ℱ.le n)]
      have hp := condExp_mul_of_stronglyMeasurable_left
        (partial_adapted hd n) hprod ((hi n).integrable (by norm_num))
      calc
        _ = ∫ ω, (∑ i ∈ range n, d i ω) * (0 : ℝ) ∂μ := by
          apply integral_congr_ae
          filter_upwards [hp, hc n] with ω h1 h2
          simpa only [Pi.mul_def, h2, Pi.zero_apply, mul_zero] using h1
        _ = 0 := by simp
    simp only [sum_range_succ]
    have heq : (fun ω => ((∑ i ∈ range n, d i ω) + d n ω) ^ 2) =
        (fun ω => (∑ i ∈ range n, d i ω) ^ 2) +
        (fun ω => 2 * ((∑ i ∈ range n, d i ω) * d n ω)) +
        (fun ω => (d n ω) ^ 2) := by ext ω; simp only [Pi.add_apply]; ring
    simp only [Pi.mul_def] at hprod
    rw [heq]
    simp only [Pi.add_def]
    have hplus : Integrable (fun ω => (∑ i ∈ range n, d i ω) ^ 2 +
        2 * ((∑ i ∈ range n, d i ω) * d n ω)) μ :=
      (hs n).integrable_sq.add (hprod.const_mul 2)
    rw [integral_add hplus (hi n).integrable_sq,
      integral_add (hs n).integrable_sq (hprod.const_mul 2),
      integral_const_mul, hcross, ih]
    ring

private lemma cut_integral_bound {e z : ℕ → Ω → ℝ}
    (he : StronglyAdapted ℱ e) (hei : ∀ n, Integrable (e n) μ)
    (hz : ∀ n, Integrable (z n) μ)
    (hc : ∀ n, μ[z n | ℱ n] ≤ᵐ[μ] fun ω => 2 * e n ω)
    (K : ℝ) (n : ℕ) :
    (∫ ω, (energyCut e K n).indicator (z n) ω ∂μ) ≤
      2 * ∫ ω, (energyCut e K n).indicator (e n) ω ∂μ := by
  have hm := cut_measurable he K n
  rw [integral_indicator (ℱ.le n _ hm), integral_indicator (ℱ.le n _ hm),
    ← setIntegral_condExp (ℱ.le n) (hz n) hm, ← integral_const_mul]
  exact integral_mono_ae integrable_condExp.integrableOn
    ((hei n).const_mul 2).integrableOn (ae_restrict_of_ae (hc n))

/-- The same predictable cuts control a centered sum and a nonnegative error sum.
On a single full-measure set both conclusions hold at every finite-energy path.
Only the natural-order partial sums of the centered increments are asserted to converge. -/
theorem common_energy_localization
    (e d y : ℕ → Ω → ℝ)
    (he : StronglyAdapted ℱ e) (hei : ∀ n, Integrable (e n) μ)
    (he0 : ∀ n ω, 0 ≤ e n ω) (he1 : ∀ n ω, e n ω ≤ 1)
    (hd : ∀ n, StronglyMeasurable[ℱ (n + 1)] (d n))
    (hd2 : ∀ n, MemLp (d n) 2 μ)
    (hd0 : ∀ n, μ[d n | ℱ n] =ᵐ[μ] 0)
    (hdv : ∀ n, μ[fun ω => (d n ω) ^ 2 | ℱ n] ≤ᵐ[μ] fun ω => 2 * e n ω)
    (hy : ∀ n, StronglyMeasurable[ℱ (n + 1)] (y n))
    (hyi : ∀ n, Integrable (y n) μ)
    (hy0 : ∀ n ω, 0 ≤ y n ω)
    (hyc : ∀ n, μ[y n | ℱ n] ≤ᵐ[μ] fun ω => 2 * e n ω) :
    (∀ K : ℕ, ∀ n : ℕ,
      (∫ ω, (∑ i ∈ range n, (energyCut e K i).indicator (d i) ω) ^ 2 ∂μ)
          ≤ 2 * (K + 1) ∧
      (∫ ω, (∑ i ∈ range n, (energyCut e K i).indicator (y i) ω) ∂μ)
          ≤ 2 * (K + 1)) ∧
    (∀ᵐ ω ∂μ, Summable (fun n => e n ω) →
      (∃ l : ℝ, Tendsto (fun n => ∑ i ∈ range n, d i ω) atTop (𝓝 l)) ∧
      Summable (fun n => y n ω)) := by
  classical
  let D (K n : ℕ) := (energyCut e K n).indicator (d n)
  let Y (K n : ℕ) := (energyCut e K n).indicator (y n)
  let E (K n : ℕ) := (energyCut e K n).indicator (e n)
  have hDa K n : StronglyMeasurable[ℱ (n + 1)] (D K n) :=
    (hd n).indicator (ℱ.mono (Nat.le_succ n) _ (cut_measurable he K n))
  have hD2 K n : MemLp (D K n) 2 μ :=
    (hd2 n).indicator (ℱ.le n _ (cut_measurable he K n))
  have hD0 K n : μ[D K n | ℱ n] =ᵐ[μ] 0 := by
    filter_upwards [condExp_indicator ((hd2 n).integrable (by norm_num))
      (cut_measurable he K n), hd0 n] with ω h1 h2
    simpa [D, Set.indicator_apply, h2] using h1
  have hYa K n : StronglyMeasurable[ℱ (n + 1)] (Y K n) :=
    (hy n).indicator (ℱ.mono (Nat.le_succ n) _ (cut_measurable he K n))
  have hYi K n : Integrable (Y K n) μ :=
    (hyi n).indicator (ℱ.le n _ (cut_measurable he K n))
  have hY0 K n ω : 0 ≤ Y K n ω := by
    dsimp [Y]; exact Set.indicator_nonneg (fun ω _ => hy0 n ω) ω
  have hEi K n : Integrable (E K n) μ :=
    (hei n).indicator (ℱ.le n _ (cut_measurable he K n))
  have hEb K n ω : (∑ i ∈ range n, E K i ω) ≤ (K : ℝ) + 1 := by
    simpa [E, Set.indicator_apply, energyCut] using
      cut_energy_bound (fun i => e i ω) (fun i => he0 i ω) (fun i => he1 i ω)
        K (Nat.cast_nonneg K) n
  have hEv K n : (∑ i ∈ range n, ∫ ω, E K i ω ∂μ) ≤ (K : ℝ) + 1 := by
    rw [← integral_finsetSum _ (fun i _ => hEi K i)]
    calc
      _ ≤ ∫ _ : Ω, (K : ℝ) + 1 ∂μ := integral_mono
        (integrable_finsetSum _ (fun i _ => hEi K i)) (integrable_const _) (hEb K n)
      _ = (K : ℝ) + 1 := by simp
  have hDv K n : (∫ ω, (D K n ω) ^ 2 ∂μ) ≤ 2 * ∫ ω, E K n ω ∂μ := by
    have hi := cut_integral_bound he hei (fun n => (hd2 n).integrable_sq) hdv (K : ℝ) n
    convert hi using 1
    apply integral_congr_ae
    filter_upwards [] with ω
    simp only [D, Set.indicator_apply]
    split_ifs <;> simp
  have hYv K n : (∫ ω, Y K n ω ∂μ) ≤ 2 * ∫ ω, E K n ω ∂μ :=
    cut_integral_bound he hei hyi hyc (K : ℝ) n
  have hjoint K n :
      (∫ ω, (∑ i ∈ range n, D K i ω) ^ 2 ∂μ) ≤ 2 * ((K : ℝ) + 1) ∧
      (∫ ω, (∑ i ∈ range n, Y K i ω) ∂μ) ≤ 2 * ((K : ℝ) + 1) := by
    constructor
    · rw [partial_square_integral (hDa K) (hD2 K) (hD0 K)]
      calc
        _ ≤ ∑ i ∈ range n, 2 * ∫ ω, E K i ω ∂μ := sum_le_sum fun i _ => hDv K i
        _ = 2 * ∑ i ∈ range n, ∫ ω, E K i ω ∂μ := by rw [mul_sum]
        _ ≤ 2 * ((K : ℝ) + 1) := mul_le_mul_of_nonneg_left (hEv K n) (by norm_num)
    · rw [integral_finsetSum _ (fun i _ => hYi K i)]
      calc
        _ ≤ ∑ i ∈ range n, 2 * ∫ ω, E K i ω ∂μ := sum_le_sum fun i _ => hYv K i
        _ = 2 * ∑ i ∈ range n, ∫ ω, E K i ω ∂μ := by rw [mul_sum]
        _ ≤ 2 * ((K : ℝ) + 1) := mul_le_mul_of_nonneg_left (hEv K n) (by norm_num)
  refine ⟨hjoint, ?_⟩
  have hconv (K : ℕ) : ∀ᵐ ω ∂μ,
      (∃ l : ℝ, Tendsto (fun n => ∑ i ∈ range n, D K i ω) atTop (𝓝 l)) ∧
      Summable (fun n => Y K n ω) := by
    have hmi := partial_martingale (hDa K)
      (fun n => (hD2 K n).integrable (by norm_num)) (hD0 K)
    have hsi n : Integrable (fun ω => ∑ i ∈ range n, Y K i ω) μ :=
      integrable_finsetSum _ fun i _ => hYi K i
    have hsm : Submartingale (fun n ω => ∑ i ∈ range n, Y K i ω) ℱ μ := by
      apply submartingale_of_setIntegral_le_succ (partial_adapted (hYa K)) hsi
      intro n s _
      apply integral_mono (hsi n).integrableOn (hsi (n + 1)).integrableOn
      intro ω
      simp only [sum_range_succ]
      exact le_add_of_nonneg_right (hY0 K n ω)
    let RD : ℝ≥0 := ⟨2 * ((K : ℝ) + 1) + 1, by positivity⟩
    let RY : ℝ≥0 := ⟨2 * ((K : ℝ) + 1), by positivity⟩
    have hbD n : eLpNorm (fun ω => ∑ i ∈ range n, D K i ω) 1 μ ≤
        (RD : ℝ≥0∞) := by
      rw [eLpNorm_one_eq_lintegral_enorm,
        ← ofReal_integral_norm_eq_lintegral_enorm (hmi.integrable n)]
      rw [← ENNReal.ofReal_coe_nnreal]
      change ENNReal.ofReal _ ≤ ENNReal.ofReal (2 * ((K : ℝ) + 1) + 1)
      apply ENNReal.ofReal_le_ofReal
      have hs2 := (memLp_finsetSum (range n) (fun i _ => hD2 K i)).integrable_sq
      calc
        _ ≤ ∫ ω, (∑ i ∈ range n, D K i ω) ^ 2 + 1 ∂μ :=
          integral_mono (hmi.integrable n).norm (hs2.add (integrable_const 1))
            (fun ω => by
              rw [Real.norm_eq_abs]
              have h := sq_nonneg (|∑ i ∈ range n, D K i ω| - 1)
              nlinarith [abs_nonneg (∑ i ∈ range n, D K i ω),
                sq_abs (∑ i ∈ range n, D K i ω)])
        _ = (∫ ω, (∑ i ∈ range n, D K i ω) ^ 2 ∂μ) + 1 := by
          rw [integral_add hs2 (integrable_const 1)]; simp
        _ ≤ _ := by linarith [(hjoint K n).1]
    have hbY n : eLpNorm (fun ω => ∑ i ∈ range n, Y K i ω) 1 μ ≤
        (RY : ℝ≥0∞) := by
      rw [eLpNorm_one_eq_lintegral_enorm,
        ← ofReal_integral_norm_eq_lintegral_enorm (hsi n)]
      rw [← ENNReal.ofReal_coe_nnreal]
      change ENNReal.ofReal _ ≤ ENNReal.ofReal (2 * ((K : ℝ) + 1))
      apply ENNReal.ofReal_le_ofReal
      simpa only [Real.norm_eq_abs, abs_of_nonneg (sum_nonneg (fun i _ => hY0 K i _))]
        using (hjoint K n).2
    filter_upwards [hmi.submartingale.exists_ae_tendsto_of_bdd hbD,
      hsm.exists_ae_tendsto_of_bdd hbY] with ω hdlim hylim
    refine ⟨hdlim, ?_⟩
    obtain ⟨l, hl⟩ := hylim
    obtain ⟨b, hb⟩ := hl.bddAbove_range
    exact summable_of_sum_range_le (fun n => hY0 K n ω) (fun n => hb ⟨n, rfl⟩)
  have hall : ∀ᵐ ω ∂μ, ∀ K : ℕ,
      (∃ l : ℝ, Tendsto (fun n => ∑ i ∈ range n, D K i ω) atTop (𝓝 l)) ∧
      Summable (fun n => Y K n ω) := ae_all_iff.mpr hconv
  filter_upwards [hall] with ω hω hefin
  obtain ⟨K, hK⟩ := exists_nat_gt (∑' n, e n ω)
  have hmem n : ω ∈ energyCut e K n :=
    (hefin.sum_le_tsum (range n) (fun i _ => he0 i ω)).trans hK.le
  have hDeq n : D K n ω = d n ω := Set.indicator_of_mem (hmem n) _
  have hYeq n : Y K n ω = y n ω := Set.indicator_of_mem (hmem n) _
  simpa only [hDeq, hYeq] using hω K

private lemma positive_product_of_centered_convergence (r : ℕ → ℝ)
    (hr : ∀ n, 0 < r n) (hsq : Summable (fun n => (r n - 1) ^ 2))
    (hc : ∃ a : ℝ, Tendsto (fun n => ∑ i ∈ range n, (r i - 1)) atTop (𝓝 a)) :
    ∃ l : ℝ, 0 < l ∧ Tendsto (fun n => ∏ i ∈ range n, r i) atTop (𝓝 l) := by
  have habs : Tendsto (fun n => |r n - 1|) atTop (𝓝 0) := by
    simpa only [Real.sqrt_sq_eq_abs, Real.sqrt_zero] using hsq.tendsto_atTop_zero.sqrt
  have hsmall : ∀ᶠ n in atTop, |r n - 1| < (1 / 2 : ℝ) :=
    habs.eventually (gt_mem_nhds (by norm_num))
  have hrem : Summable (fun n => Real.log (r n) - (r n - 1)) := by
    apply (hsq.mul_left 2).of_norm_bounded_eventually_nat
    filter_upwards [hsmall] with n hn
    have h := Real.abs_log_sub_add_sum_range_le
      (x := -(r n - 1)) (by rw [abs_neg]; exact hn.trans (by norm_num : (1 / 2 : ℝ) < 1)) 1
    have hlog : (1 : ℝ) - -(r n - 1) = r n := by ring
    simp only [sum_range_one, zero_add, pow_one, hlog,
      abs_neg, Nat.reduceAdd, Nat.cast_zero, zero_add, div_one] at h
    rw [Real.norm_eq_abs]
    calc
      |Real.log (r n) - (r n - 1)| = |-(r n - 1) + Real.log (r n)| := by congr 1; ring
      _ ≤ |r n - 1| ^ 2 / (1 - |r n - 1|) := h
      _ ≤ 2 * (r n - 1) ^ 2 := by
        rw [sq_abs, div_le_iff₀ (by linarith : 0 < 1 - |r n - 1|)]
        nlinarith [sq_nonneg (r n - 1), abs_nonneg (r n - 1)]
  obtain ⟨a, ha⟩ := hc
  have hlogs : Tendsto (fun n => ∑ i ∈ range n, Real.log (r i)) atTop
      (𝓝 (a + ∑' i, (Real.log (r i) - (r i - 1)))) := by
    convert ha.add hrem.hasSum.tendsto_sum_nat using 1
    ext n
    rw [← sum_add_distrib]
    congr 1
    ext i
    ring
  refine ⟨Real.exp (a + ∑' i, (Real.log (r i) - (r i - 1))), Real.exp_pos _, ?_⟩
  have hprod n : Real.exp (∑ i ∈ range n, Real.log (r i)) = ∏ i ∈ range n, r i := by
    rw [Real.exp_sum]
    exact prod_congr rfl fun i _ => Real.exp_log (hr i)
  simpa only [hprod] using hlogs.rexp

/-- Positive root-likelihood increments have a strictly positive finite product limit
on the finite conditional-energy event. The conclusion uses natural-order products. -/
theorem finite_energy_positive_product
    (e r : ℕ → Ω → ℝ)
    (he : StronglyAdapted ℱ e)
    (he0 : ∀ n ω, 0 ≤ e n ω) (he1 : ∀ n ω, e n ω ≤ 1)
    (hr : ∀ n, StronglyMeasurable[ℱ (n + 1)] (r n))
    (hr2 : ∀ n, MemLp (r n) 2 μ)
    (hr0 : ∀ n ω, 0 < r n ω)
    (hrmean : ∀ n, μ[r n | ℱ n] =ᵐ[μ] fun ω => 1 - e n ω)
    (hrsq : ∀ n, μ[fun ω => (r n ω - 1) ^ 2 | ℱ n] ≤ᵐ[μ] fun ω => 2 * e n ω) :
    ∀ᵐ ω ∂μ, Summable (fun n => e n ω) →
      ∃ l : ℝ, 0 < l ∧ Tendsto (fun n => ∏ i ∈ range n, r i ω) atTop (𝓝 l) := by
  let X n ω := r n ω - 1
  let d n ω := X n ω - (μ[X n | ℱ n]) ω
  have hX2 n : MemLp (X n) 2 μ := (hr2 n).sub (memLp_const 1)
  have hei n : Integrable (e n) μ :=
    Integrable.of_bound ((he n).mono (ℱ.le n)).aestronglyMeasurable 1
      (ae_of_all _ fun ω => by simpa [Real.norm_eq_abs, abs_of_nonneg (he0 n ω)] using he1 n ω)
  have hd n : StronglyMeasurable[ℱ (n + 1)] (d n) :=
    ((hr n).sub stronglyMeasurable_const).sub
      (stronglyMeasurable_condExp.mono (ℱ.mono (Nat.le_succ n)))
  have hd2 n : MemLp (d n) 2 μ := (hX2 n).sub ((hX2 n).condExp (by norm_num))
  have hd0 n : μ[d n | ℱ n] =ᵐ[μ] 0 := by
    filter_upwards [condExp_sub ((hX2 n).integrable (by norm_num))
      (integrable_condExp (f := X n) (m := ℱ n)) (ℱ n)] with ω hω
    simpa only [d, Pi.sub_def, Pi.sub_apply, Pi.zero_apply,
      condExp_of_stronglyMeasurable (ℱ.le n) stronglyMeasurable_condExp integrable_condExp,
      sub_self] using hω
  have hdv n : μ[fun ω => (d n ω) ^ 2 | ℱ n] ≤ᵐ[μ] fun ω => 2 * e n ω := by
    have h := ProbabilityTheory.condVar_ae_le_condExp_sq (ℱ.le n) (hX2 n)
    exact h.trans (hrsq n)
  have hy n : StronglyMeasurable[ℱ (n + 1)] (fun ω => (r n ω - 1) ^ 2) :=
    ((hr n).sub stronglyMeasurable_const).pow 2
  have hloc := (common_energy_localization e d (fun n ω => (r n ω - 1) ^ 2)
    he hei he0 he1 hd hd2 hd0 hdv hy (fun n => (hX2 n).integrable_sq)
    (fun n ω => sq_nonneg _) hrsq).2
  have hmean n : μ[X n | ℱ n] =ᵐ[μ] fun ω => -e n ω := by
    filter_upwards [condExp_sub ((hr2 n).integrable (by norm_num)) (integrable_const 1) (ℱ n),
      hrmean n] with ω h1 h2
    simpa only [X, Pi.sub_def, Pi.sub_apply, condExp_const (ℱ.le n), h2,
      sub_sub_cancel_left] using h1
  have hall : ∀ᵐ ω ∂μ, ∀ n, (μ[X n | ℱ n]) ω = -e n ω := ae_all_iff.mpr hmean
  filter_upwards [hloc, hall] with ω hω hm hefin
  obtain ⟨⟨a, ha⟩, hs⟩ := hω hefin
  apply positive_product_of_centered_convergence (fun n => r n ω) (fun n => hr0 n ω) hs
  refine ⟨a - ∑' n, e n ω, ?_⟩
  convert ha.sub hefin.hasSum.tendsto_sum_nat using 1
  ext n
  rw [← sum_sub_distrib]
  apply sum_congr rfl
  intro i _
  dsimp [d, X]
  rw [hm i]
  ring

private lemma normalized_product_zero
    (r ρ : ℕ → Ω → ℝ) (hr : ∀ n ω, 0 < r n ω)
    (hρ : ∀ n ω, 0 < ρ n ω) (hρ1 : ∀ n ω, ρ n ω ≤ 1)
    (hm : Martingale (fun n ω => ∏ i ∈ range n, r i ω / ρ i ω) ℱ μ) :
    ∀ᵐ ω ∂μ, ¬ Summable (fun n => 1 - ρ n ω) →
      Tendsto (fun n => ∏ i ∈ range n, r i ω) atTop (𝓝 0) := by
  have hnonneg n ω : 0 ≤ ∏ i ∈ range n, r i ω / ρ i ω :=
    prod_nonneg (fun i _ => (div_pos (hr i ω) (hρ i ω)).le)
  have hint n : (∫ ω, (∏ i ∈ range n, r i ω / ρ i ω) ∂μ) = 1 := by
    have heq := hm.setIntegral_eq (i := 0) (j := n) (Nat.zero_le n) MeasurableSet.univ
    simpa using heq.symm
  have hb n : eLpNorm (fun ω => ∏ i ∈ range n, r i ω / ρ i ω) 1 μ ≤ (1 : ℝ≥0) := by
    rw [eLpNorm_one_eq_lintegral_enorm,
      ← ofReal_integral_norm_eq_lintegral_enorm (hm.integrable n)]
    simp only [Real.norm_eq_abs, abs_of_nonneg (hnonneg n _), hint, ENNReal.ofReal_one]
    exact le_rfl
  filter_upwards [hm.submartingale.exists_ae_tendsto_of_bdd hb] with ω hω he
  obtain ⟨l, hl⟩ := hω
  have hs : Tendsto (fun n => ∑ i ∈ range n, (1 - ρ i ω)) atTop atTop :=
    (not_summable_iff_tendsto_nat_atTop_of_nonneg (fun n => sub_nonneg.mpr (hρ1 n ω))).mp he
  have hexp : Tendsto (fun n => Real.exp (-(∑ i ∈ range n, (1 - ρ i ω)))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hs)
  have hdecay : Tendsto (fun n => ∏ i ∈ range n, ρ i ω) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => prod_nonneg (fun i _ => (hρ i ω).le)) _ hexp
    intro n
    calc
      _ ≤ ∏ i ∈ range n, Real.exp (-(1 - ρ i ω)) := by
        apply prod_le_prod (fun i _ => (hρ i ω).le)
        intro i _
        have h := Real.add_one_le_exp (ρ i ω - 1)
        simpa only [sub_add_cancel, neg_sub] using h
      _ = _ := by rw [← Real.exp_sum, sum_neg_distrib]
  convert hl.mul hdecay using 1
  · ext n
    rw [← prod_mul_distrib]
    exact prod_congr rfl fun i _ => (div_mul_cancel₀ _ (hρ i ω).ne').symm
  · simp

open Preorder ProbabilityTheory
open HistoricalDepthBudgetJointExtremum
open D5.S3.TotalVariation.Bhattacharyya

private lemma finite_readout_memLp {B W : Type*} [Fintype B]
    [MeasurableSpace B] [MeasurableSingletonClass B] [MeasurableSpace W]
    {ν : Measure W} [IsFiniteMeasure ν] {s : ℝ≥0∞} (f : B → ℝ) (z : W → B)
    (hz : Measurable z) : MemLp (fun ω => f (z ω)) s ν := by
  classical
  apply MemLp.of_bound ((measurable_of_countable f).comp hz).aestronglyMeasurable
    (∑ b, |f b|)
  exact ae_of_all _ fun ω => by
    rw [Real.norm_eq_abs]
    exact single_le_sum (fun b _ => abs_nonneg (f b)) (mem_univ (z ω))

private lemma next_condexp {A : Type*} [Fintype A] [Nonempty A]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (p : List A → A → ℝ) (hp : NormalizedRows p) (n : ℕ)
    (g : (Iic n → A) → A → ℝ) :
    (trajectoryLaw p hp)[fun x => g (frestrictLe n x) (x (n + 1)) | Filtration.piLE n]
      =ᵐ[trajectoryLaw p hp] fun x => ∑ a,
        p (List.ofFn (fun i : Fin (n + 1) => x i)) a * g (frestrictLe n x) a := by
  classical
  let row (v : List A) : PMF A := PMF.ofFintype (fun a => ENNReal.ofReal (p v a)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => hp.1 v a), hp.2 v]; simp)
  let κ (k : ℕ) : Kernel (Iic k → A) A := Kernel.ofFunOfCountable
    (fun u => (row (List.ofFn (fun i : Fin (k + 1) =>
      u ⟨i, mem_Iic.mpr (Nat.le_of_lt_succ i.2)⟩))).toMeasure)
  letI : ∀ k, IsMarkovKernel (κ k) := fun k =>
    ⟨fun _ => inferInstanceAs (IsProbabilityMeasure (row _).toMeasure)⟩
  let P := Kernel.trajMeasure (X := fun _ => A) (row []).toMeasure κ
  letI : IsProbabilityMeasure P := inferInstanceAs (IsProbabilityMeasure (Kernel.trajMeasure _ _))
  change P[fun x => g (frestrictLe n x) (x (n + 1)) | Filtration.piLE n] =ᵐ[P] _
  rw [Filtration.piLE_eq_comap_frestrictLe]
  have hcond := condExp_prod_ae_eq_integral_condDistrib
    (μ := P) (X := frestrictLe n) (Y := fun x : ℕ → A => x (n + 1))
    (f := fun z => g z.1 z.2) (measurable_frestrictLe n)
    (measurable_pi_apply (n + 1)).aemeasurable
    (measurable_of_countable _).stronglyMeasurable
    ((finite_readout_memLp (ν := P) (s := 2) (fun z : (Iic n → A) × A => g z.1 z.2)
      (fun x => (frestrictLe n x, x (n + 1))) (by fun_prop)).integrable (by norm_num))
  have hk := Kernel.condDistrib_trajMeasure (X := fun _ => A)
    (μ₀ := (row []).toMeasure) (κ := κ) (a := n)
  have hk' : ∀ᵐ x ∂P, condDistrib (fun x : ℕ → A => x (n + 1)) (frestrictLe n) P
      (frestrictLe n x) = κ n (frestrictLe n x) :=
    ae_of_ae_map (measurable_frestrictLe n).aemeasurable hk
  filter_upwards [hcond, hk'] with x hx hkx
  rw [hx, hkx]
  change (∫ a, g (frestrictLe n x) a ∂(row _).toMeasure) = _
  rw [PMF.integral_eq_sum]
  apply sum_congr rfl
  intro a _
  simp [row, PMF.ofFintype_apply, ENNReal.toReal_ofReal (hp.1 _ _), smul_eq_mul]

private lemma prefix_readout_stronglyMeasurable {A : Type*} [Fintype A]
    [MeasurableSpace A] [MeasurableSingletonClass A] (n : ℕ) (g : (Iic n → A) → ℝ) :
    StronglyMeasurable[Filtration.piLE n] (fun x : ℕ → A => g (frestrictLe n x)) := by
  rw [Filtration.piLE_eq_comap_frestrictLe]
  exact (measurable_of_countable g).stronglyMeasurable.comp_measurable
    (Measurable.of_comap_le le_rfl)

private lemma row_root_moments {A : Type*} [Fintype A] (p q : A → ℝ)
    (hp : ∀ a, 0 < p a) (hq : ∀ a, 0 < q a)
    (hps : ∑ a, p a = 1) (hqs : ∑ a, q a = 1) :
    (∑ a, p a * Real.sqrt (q a / p a)) = bhattacharyya p q ∧
    (∑ a, p a * (Real.sqrt (q a / p a) - 1) ^ 2) = 2 * (1 - bhattacharyya p q) := by
  have hs a : p a * Real.sqrt (q a / p a) ^ 2 = q a := by
    rw [Real.sq_sqrt (div_pos (hq a) (hp a)).le]
    exact mul_div_cancel₀ _ (hp a).ne'
  have hw a : p a * Real.sqrt (q a / p a) = Real.sqrt (p a * q a) := by
    symm
    apply (Real.sqrt_eq_iff_eq_sq (mul_pos (hp a) (hq a)).le
      (mul_nonneg (hp a).le (Real.sqrt_nonneg _))).2
    calc
      p a * q a = p a * (p a * Real.sqrt (q a / p a) ^ 2) := by rw [hs]
      _ = _ := by ring
  refine ⟨sum_congr rfl (fun a _ => hw a), ?_⟩
  calc
    _ = ∑ a, (q a - 2 * Real.sqrt (p a * q a) + p a) := by
      apply sum_congr rfl
      intro a _
      nlinarith [hs a, hw a]
    _ = _ := by rw [sum_add_distrib, sum_sub_distrib, ← mul_sum, hps, hqs, bhattacharyya]; ring

/-- Actual full-history likelihoods have positive finite limits on finite energy and
vanish on infinite energy, almost surely under the first trajectory law. -/
theorem trajectory_hellinger_likelihood_limits
    {A : Type*} [Fintype A] [Nonempty A]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (p q : List A → A → ℝ) (hp : NormalizedRows p) (hq : NormalizedRows q)
    (hp0 : ∀ h a, 0 < p h a) (hq0 : ∀ h a, 0 < q h a) :
    let H := fun (n : ℕ) (x : ℕ → A) => List.ofFn (fun i : Fin n => x i)
    ∀ᵐ x ∂trajectoryLaw p hp,
      (Summable (fun n => 1 - bhattacharyya (p (H n x)) (q (H n x))) →
      ∃ l : ℝ, 0 < l ∧
        Tendsto (fun n => ∏ i ∈ range n, q (H i x) (x i) / p (H i x) (x i)) atTop (𝓝 l)) ∧
      (¬ Summable (fun n => 1 - bhattacharyya (p (H n x)) (q (H n x))) →
        Tendsto (fun n => ∏ i ∈ range n, q (H i x) (x i) / p (H i x) (x i)) atTop (𝓝 0)) := by
  classical
  intro H
  let P := trajectoryLaw p hp
  letI : IsProbabilityMeasure P := by
    dsimp [P, trajectoryLaw]
    infer_instance
  let F : Filtration ℕ (inferInstance : MeasurableSpace (ℕ → A)) := Filtration.piLE
  let h n (u : Iic n → A) := List.ofFn (fun i : Fin (n + 1) =>
    u ⟨i, mem_Iic.mpr (Nat.le_of_lt_succ i.2)⟩)
  let R (n : ℕ) (x : ℕ → A) := Real.sqrt (q (H n x) (x n) / p (H n x) (x n))
  let e (n : ℕ) (x : ℕ → A) := 1 - bhattacharyya (p (H (n + 1) x)) (q (H (n + 1) x))
  let r (n : ℕ) := R (n + 1)
  have he : StronglyAdapted F e := fun n =>
    prefix_readout_stronglyMeasurable n (fun u => 1 - bhattacharyya (p (h n u)) (q (h n u)))
  have he0 n x : 0 ≤ e n x := sub_nonneg.mpr <|
    bhattacharyya_le_one _ _ ⟨hp.1 _, hp.2 _⟩ ⟨hq.1 _, hq.2 _⟩
  have he1 n x : e n x ≤ 1 := by
    have ha : 0 ≤ bhattacharyya (p (H (n + 1) x)) (q (H (n + 1) x)) :=
      sum_nonneg fun a _ => Real.sqrt_nonneg _
    dsimp [e]; linarith
  let f (n : ℕ) (u : Iic (n + 1) → A) :=
    Real.sqrt (q (h n (fun i => u ⟨i, mem_Iic.mpr ((mem_Iic.mp i.2).trans (Nat.le_succ n))⟩))
      (u ⟨n + 1, mem_Iic.mpr le_rfl⟩) /
      p (h n (fun i => u ⟨i, mem_Iic.mpr ((mem_Iic.mp i.2).trans (Nat.le_succ n))⟩))
      (u ⟨n + 1, mem_Iic.mpr le_rfl⟩))
  have hr n : StronglyMeasurable[F (n + 1)] (r n) :=
    prefix_readout_stronglyMeasurable (n + 1) (f n)
  have hr2 n : MemLp (r n) 2 P :=
    finite_readout_memLp (ν := P) (f n) (frestrictLe (n + 1))
      (measurable_frestrictLe (n + 1))
  have hr0 n x : 0 < r n x := Real.sqrt_pos.mpr (div_pos (hq0 _ _) (hp0 _ _))
  have hrmean n : P[r n | F n] =ᵐ[P] fun x => 1 - e n x := by
    have hc := next_condexp p hp n (fun u a => Real.sqrt (q (h n u) a / p (h n u) a))
    filter_upwards [hc] with x hx
    change (P[r n | F n]) x = _ at hx ⊢
    rw [hx]
    have hm := (row_root_moments (p (H (n + 1) x)) (q (H (n + 1) x))
      (hp0 _) (hq0 _) (hp.2 _) (hq.2 _)).1
    rw [show h n (frestrictLe n x) = H (n + 1) x from rfl]
    simpa only [e, sub_sub_cancel] using hm
  have hrsq n : P[fun x => (r n x - 1) ^ 2 | F n] ≤ᵐ[P] fun x => 2 * e n x := by
    have hc := next_condexp p hp n
      (fun u a => (Real.sqrt (q (h n u) a / p (h n u) a) - 1) ^ 2)
    filter_upwards [hc] with x hx
    change (P[fun x => (r n x - 1) ^ 2 | F n]) x = _ at hx
    rw [hx]
    exact (row_root_moments (p (H (n + 1) x)) (q (H (n + 1) x))
      (hp0 _) (hq0 _) (hp.2 _) (hq.2 _)).2.le
  have hlim := finite_energy_positive_product (μ := P) (ℱ := F)
    e r he he0 he1 hr hr2 hr0 hrmean hrsq
  let ρ n x := 1 - e n x
  let W n x := r n x / ρ n x
  let Z n x := ∏ i ∈ range n, W i x
  have hρ n x : 0 < ρ n x := by
    dsimp [ρ, e]
    rw [sub_sub_cancel]
    exact sum_pos (fun a _ => Real.sqrt_pos.mpr (mul_pos (hp0 _ _) (hq0 _ _))) univ_nonempty
  have hWa n : StronglyMeasurable[F (n + 1)] (W n) :=
    (hr n).div ((stronglyMeasurable_const.sub (he n)).mono (F.mono (Nat.le_succ n)))
  have hWtop n : MemLp (W n) ∞ P := by
    let g (u : Iic (n + 1) → A) := f n u /
      bhattacharyya
        (p (h n (fun i => u ⟨i, mem_Iic.mpr ((mem_Iic.mp i.2).trans (Nat.le_succ n))⟩)))
        (q (h n (fun i => u ⟨i, mem_Iic.mpr ((mem_Iic.mp i.2).trans (Nat.le_succ n))⟩)))
    simpa only [g, W, ρ, e, r, R, f, h, H, sub_sub_cancel, frestrictLe_apply] using
      (finite_readout_memLp (ν := P) (s := ∞) g (frestrictLe (n + 1))
        (measurable_frestrictLe (n + 1)))
  have hZa : StronglyAdapted F Z := fun n => by
    simpa only [Z, Finset.prod_apply] using
      (Finset.stronglyMeasurable_fun_prod (range n) fun i hi =>
        (hWa i).mono (F.mono (Nat.succ_le_of_lt (mem_range.mp hi))))
  have hZtop n : MemLp (Z n) ∞ P := by
    induction n with
    | zero => simpa [Z] using (memLp_top_const (1 : ℝ) (μ := P))
    | succ n ih =>
      simpa only [Z, prod_range_succ, Pi.mul_def] using
        ((hWtop n).mul ih : MemLp (Z n * W n) ∞ P)
  have hWmean n : P[W n | F n] =ᵐ[P] 1 := by
    have hwi : Integrable (r n * (fun x => (ρ n x)⁻¹)) P := by
      simpa only [W, div_eq_mul_inv, Pi.mul_def] using (hWtop n).integrable le_top
    have hinv : StronglyMeasurable[F n] (fun x => (ρ n x)⁻¹) :=
      (stronglyMeasurable_const.sub (he n)).measurable.inv.stronglyMeasurable
    have h := condExp_mul_of_stronglyMeasurable_right hinv hwi
      ((hr2 n).integrable (by norm_num))
    filter_upwards [h, hrmean n] with x hx hxmean
    change P[fun x => r n x / ρ n x | F n] x = 1
    simp only [div_eq_mul_inv]
    change P[r n * (fun x => (ρ n x)⁻¹) | F n] x = 1
    rw [hx]
    change (P[r n | F n]) x * (ρ n x)⁻¹ = 1
    rw [hxmean]
    exact mul_inv_cancel₀ (hρ n x).ne'
  have hm : Martingale Z F P := by
    apply martingale_nat hZa (fun n => (hZtop n).integrable le_top)
    intro n
    have heq : Z (n + 1) = Z n * W n := by ext x; simp [Z, prod_range_succ]
    rw [heq]
    have h := condExp_mul_of_stronglyMeasurable_left (hZa n)
      (by simpa only [← heq] using (hZtop (n + 1)).integrable le_top)
      ((hWtop n).integrable le_top)
    filter_upwards [h, hWmean n] with x hx hw
    simpa only [Pi.mul_apply, hw, Pi.one_apply, mul_one] using hx.symm
  have hzero := normalized_product_zero (μ := P) (ℱ := F) r ρ hr0 hρ
    (fun n x => by dsimp [ρ]; linarith [he0 n x]) hm
  filter_upwards [hlim, hzero] with x hx hz
  constructor
  · intro hefin
    have hefin' : Summable (fun n => e n x) := (summable_nat_add_iff 1).mpr hefin
    obtain ⟨a, ha, hat⟩ := hx hefin'
    have hR0 : 0 < R 0 x := Real.sqrt_pos.mpr (div_pos (hq0 _ _) (hp0 _ _))
    have hprod : Tendsto (fun n => ∏ i ∈ range n, R i x) atTop (𝓝 (R 0 x * a)) := by
      apply (tendsto_add_atTop_iff_nat 1).mp
      simpa only [prod_range_succ', r, mul_comm] using hat.const_mul (R 0 x)
    refine ⟨(R 0 x * a) ^ 2, sq_pos_of_pos (mul_pos hR0 ha), ?_⟩
    convert hprod.pow 2 using 1
    ext n
    rw [← prod_pow]
    exact prod_congr rfl fun i _ =>
      (Real.sq_sqrt (div_pos (hq0 _ _) (hp0 _ _)).le).symm
  · intro heinf
    have heinf' : ¬ Summable (fun n => e n x) := fun h =>
      heinf ((summable_nat_add_iff 1).mp h)
    have hzero' := hz (by simpa only [ρ, sub_sub_cancel] using heinf')
    have hprod : Tendsto (fun n => ∏ i ∈ range n, R i x) atTop (𝓝 0) := by
      apply (tendsto_add_atTop_iff_nat 1).mp
      simpa only [prod_range_succ', r, mul_comm, mul_zero, zero_mul] using hzero'.const_mul (R 0 x)
    convert hprod.pow 2 using 1
    · ext n
      rw [← prod_pow]
      exact prod_congr rfl fun i _ =>
        (Real.sq_sqrt (div_pos (hq0 _ _) (hp0 _ _)).le).symm
    · norm_num

private lemma trajectory_prefix_mass {A : Type*} [Fintype A] [Nonempty A]
    [MeasurableSpace A] [MeasurableSingletonClass A] (hd : 2 ≤ Fintype.card A)
    (p : List A → A → ℝ) (hp : NormalizedRows p) (n : ℕ) (x : ℕ → A) :
    ((trajectoryLaw p hp).map (frestrictLe n)) {frestrictLe n x} =
      ENNReal.ofReal (∏ i ∈ range (n + 1), p (List.ofFn (fun j : Fin i => x j)) (x i)) := by
  classical
  have hcard : (0 : ℝ) < Fintype.card A := by exact_mod_cast Fintype.card_pos
  have laws := (historical_depth_budget_joint_extremum (Classical.arbitrary A)
    (1 / (Fintype.card A : ℝ)) (by positivity) hd le_rfl (fun _ => 0)
    (fun _ => linearOrderOfSTO (@WellOrderingRel (List A)))).2.1 p hp
  let w := List.ofFn (fun i : Fin (n + 1) => x i)
  have hc : (fun y : ℕ → A => frestrictLe n y) ⁻¹' {frestrictLe n x} = wordCylinder w := by
    ext y
    simp only [Set.mem_preimage, Set.mem_singleton_iff, wordCylinder, Set.mem_ofPred_eq]
    constructor
    · intro hy i
      have hval := congrFun hy ⟨i, mem_Iic.mpr (by have hi := i.2; simpa [w] using hi)⟩
      change y i = x i at hval
      simpa only [w, List.get_ofFn, Fin.val_cast] using hval
    · intro hy
      funext i
      have hval := hy ⟨i, by simpa [w] using Nat.lt_succ_of_le (mem_Iic.mp i.2)⟩
      change y i = x i
      simpa only [w, List.get_ofFn, Fin.val_cast] using hval
  rw [Measure.map_apply (measurable_frestrictLe n) (measurableSet_singleton _), hc, laws.2]
  congr 1
  calc
    (∏ i : Fin w.length, p (w.take i) (w.get i)) =
        ∏ i : Fin w.length, p (List.ofFn (fun j : Fin i => x j)) (x i) := by
      apply prod_congr rfl
      intro i _
      have ht : w.take i = List.ofFn (fun j : Fin i => x j) :=
        (Fin.ofFn_take_eq_take_ofFn (by simpa only [w, List.length_ofFn] using i.isLt.le)
          (fun j : Fin (n + 1) => x j)).symm
      rw [ht]
      congr 1
      simp only [w, List.get_ofFn, Fin.val_cast]
    _ = _ := by
      rw [← Finset.prod_range (fun i : ℕ => p (List.ofFn (fun j : Fin i => x j)) (x i))]
      simp only [w, List.length_ofFn]

private lemma finite_observation_density {W B : Type*} [MeasurableSpace W]
    [MeasurableSpace B] [MeasurableSingletonClass B]
    (P Q : Measure W) [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (z : W → B) (hz : Measurable z)
    (hpos : ∀ x, 0 < ((P.map z) {z x}).toReal) :
    (P + Q)[fun x => (Q.rnDeriv (P + Q) x).toReal | MeasurableSpace.comap z inferInstance]
      =ᵐ[P + Q] fun x => ((Q.map z) {z x}).toReal /
        (((P.map z) {z x}).toReal + ((Q.map z) {z x}).toReal) := by
  have hQ : Q ≪ P + Q := (Measure.le_add_left le_rfl).absolutelyContinuous
  filter_upwards [toReal_rnDeriv_map hQ hz] with x hx
  rw [← hx]
  have h := Measure.setLIntegral_rnDeriv (hQ.map hz) {z x}
  rw [lintegral_singleton] at h
  have ht := congrArg ENNReal.toReal h
  rw [ENNReal.toReal_mul] at ht
  have hm : (((P + Q).map z) {z x}).toReal =
      ((P.map z) {z x}).toReal + ((Q.map z) {z x}).toReal := by
    rw [Measure.map_add _ _ hz, Measure.add_apply,
      ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
  rw [hm] at ht
  apply (eq_div_iff (by linarith [hpos x, (ENNReal.toReal_nonneg (a := (Q.map z) {z x}))])).2
  exact ht

private lemma full_prefix_filtration {A : Type*} [MeasurableSpace A] :
    (⨆ n : ℕ, (Filtration.piLE (X := fun _ : ℕ => A)) n) =
      (inferInstance : MeasurableSpace (ℕ → A)) := by
  apply le_antisymm (iSup_le (fun n => Filtration.piLE.le n))
  have hi : @Measurable (ℕ → A) (ℕ → A)
      (⨆ n : ℕ, (Filtration.piLE (X := fun _ : ℕ => A)) n) inferInstance id := by
    letI : MeasurableSpace (ℕ → A) :=
      ⨆ n : ℕ, (Filtration.piLE (X := fun _ : ℕ => A)) n
    apply measurable_pi_lambda
    intro n
    have hc : Measurable[Filtration.piLE (X := fun _ : ℕ => A) n]
        (fun x : ℕ → A => x n) := by
      rw [Filtration.piLE_eq_comap_frestrictLe]
      exact (measurable_pi_apply (X := fun _ : Iic n => A) ⟨n, mem_Iic.mpr le_rfl⟩).comp
        (Measurable.of_comap_le le_rfl)
    exact hc.mono (le_iSup (fun n => (Filtration.piLE (X := fun _ : ℕ => A)) n) n) le_rfl
  simpa only [MeasurableSpace.comap_id] using hi.comap_le

private lemma restrict_ac_of_density_positive {W : Type*} [MeasurableSpace W]
    (P Q : Measure W) [IsFiniteMeasure P] [IsFiniteMeasure Q] {C : Set W}
    (hC : MeasurableSet C)
    (hpos : ∀ᵐ x ∂P, x ∈ C → Q.rnDeriv (P + Q) x ≠ 0) :
    P.restrict C ≪ Q.restrict C := by
  have hP : P ≪ P + Q := (Measure.le_add_right le_rfl).absolutelyContinuous
  have hQ : Q ≪ P + Q := (Measure.le_add_left le_rfl).absolutelyContinuous
  apply Measure.ae_le_iff_absolutelyContinuous.mp
  intro s hs
  change (∀ᵐ x ∂Q.restrict C, x ∈ s) at hs
  change ∀ᵐ x ∂P.restrict C, x ∈ s
  rw [ae_restrict_iff' hC] at hs ⊢
  have hs' : ∀ᵐ x ∂(P + Q).withDensity (Q.rnDeriv (P + Q)), x ∈ C → x ∈ s := by
    rw [Measure.withDensity_rnDeriv_eq Q (P + Q) hQ]
    exact hs
  have hμ := (ae_withDensity_iff (Measure.measurable_rnDeriv Q (P + Q))).mp hs'
  filter_upwards [hP.ae_le hμ, hpos] with x hx hp hc
  exact hx (hp hc) hc

private lemma trajectory_restrict_ac_of_positive_limit
    {A : Type*} [Fintype A] [Nonempty A]
    [MeasurableSpace A] [MeasurableSingletonClass A] (hd : 2 ≤ Fintype.card A)
    (p q : List A → A → ℝ) (hp : NormalizedRows p) (hq : NormalizedRows q)
    (hp0 : ∀ h a, 0 < p h a) {C : Set (ℕ → A)} (hC : MeasurableSet C)
    (hlim : ∀ᵐ x ∂trajectoryLaw p hp, x ∈ C → ∃ l : ℝ, 0 < l ∧
      Tendsto (fun n => ∏ i ∈ range n,
        q (List.ofFn (fun j : Fin i => x j)) (x i) /
        p (List.ofFn (fun j : Fin i => x j)) (x i)) atTop (𝓝 l)) :
    (trajectoryLaw p hp).restrict C ≪ (trajectoryLaw q hq).restrict C := by
  classical
  let P := trajectoryLaw p hp
  let Q := trajectoryLaw q hq
  letI : IsProbabilityMeasure P := by dsimp [P, trajectoryLaw]; infer_instance
  letI : IsProbabilityMeasure Q := by dsimp [Q, trajectoryLaw]; infer_instance
  let L (n : ℕ) (x : ℕ → A) := ∏ i ∈ range n,
    q (List.ofFn (fun j : Fin i => x j)) (x i) /
    p (List.ofFn (fun j : Fin i => x j)) (x i)
  let f (x : ℕ → A) := (Q.rnDeriv (P + Q) x).toReal
  have hP : P ≪ P + Q := (Measure.le_add_right le_rfl).absolutelyContinuous
  have hfinite n : (P + Q)[f | Filtration.piLE n] =ᵐ[P + Q]
      fun x => L (n + 1) x / (1 + L (n + 1) x) := by
    have hpref (x : ℕ → A) : 0 < ((P.map (frestrictLe n)) {frestrictLe n x}).toReal := by
      rw [trajectory_prefix_mass hd p hp]
      rw [ENNReal.toReal_ofReal (prod_nonneg (fun i _ => hp.1 _ _))]
      exact prod_pos (fun i _ => hp0 _ _)
    have hobs := finite_observation_density P Q (frestrictLe n)
      (measurable_frestrictLe n) hpref
    rw [Filtration.piLE_eq_comap_frestrictLe]
    filter_upwards [hobs] with x hx
    rw [hx, trajectory_prefix_mass hd p hp, trajectory_prefix_mass hd q hq,
      ENNReal.toReal_ofReal (prod_nonneg (fun i _ => hp.1 _ _)),
      ENNReal.toReal_ofReal (prod_nonneg (fun i _ => hq.1 _ _))]
    dsimp [L]
    rw [prod_div_distrib]
    have hpp : (∏ i ∈ range (n + 1), p (List.ofFn (fun j : Fin i => x j)) (x i)) ≠ 0 :=
      (prod_pos (fun i _ => hp0 _ _)).ne'
    field_simp
  have hsm : StronglyMeasurable[⨆ n : ℕ, (Filtration.piLE (X := fun _ : ℕ => A)) n] f := by
    rw [full_prefix_filtration]
    exact (Measure.measurable_rnDeriv Q (P + Q)).ennreal_toReal.stronglyMeasurable
  have hconv := (Measure.integrable_toReal_rnDeriv (μ := Q) (ν := P + Q)).tendsto_ae_condExp hsm
  apply restrict_ac_of_density_positive P Q hC
  filter_upwards [hP.ae_le hconv, hP.ae_le (ae_all_iff.mpr hfinite), hlim] with x hx he hl hc
  obtain ⟨l, hlpos, hlt⟩ := hl hc
  have hshift : Tendsto (fun n => L (n + 1) x) atTop (𝓝 l) :=
    (tendsto_add_atTop_iff_nat 1).mpr hlt
  have ht : Tendsto (fun n => L (n + 1) x / (1 + L (n + 1) x)) atTop (𝓝 (l / (1 + l))) :=
    hshift.div (tendsto_const_nhds.add hshift) (by linarith)
  change Tendsto (fun n => ((P + Q)[f | Filtration.piLE n]) x) atTop (𝓝 (f x)) at hx
  have heq : f x = l / (1 + l) := tendsto_nhds_unique (by simpa only [he] using hx) ht
  intro hz
  have hfzero : f x = 0 := by simp [f, hz]
  have : 0 < f x := heq ▸ div_pos hlpos (by linarith)
  linarith

private lemma singular_of_reciprocal_limits {W : Type*} [MeasurableSpace W]
    (P Q : Measure W) (L : ℕ → W → ℝ) (hL : ∀ n x, L n x ≠ 0)
    (hP : ∀ᵐ x ∂P, Tendsto (fun n => L n x) atTop (𝓝 0))
    (hQ : ∀ᵐ x ∂Q, Tendsto (fun n => (L n x)⁻¹) atTop (𝓝 0)) : P ⟂ₘ Q := by
  apply Measure.mutuallySingular_iff_disjoint_ae.mpr
  apply Filter.disjoint_iff.mpr
  refine ⟨{x | Tendsto (fun n => L n x) atTop (𝓝 0)}, hP,
    {x | Tendsto (fun n => (L n x)⁻¹) atTop (𝓝 0)}, hQ, ?_⟩
  apply Set.disjoint_left.mpr
  intro x hx hy
  have heq n : L n x * (L n x)⁻¹ = 1 := mul_inv_cancel₀ (hL n x)
  have h : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 0) := by
    simpa only [heq, mul_zero] using hx.mul hy
  have h01 : (0 : ℝ) = 1 := tendsto_nhds_unique h tendsto_const_nhds
  norm_num at h01

/-- Finite Hellinger energy gives equivalent restrictions; infinite energy gives singular
restrictions. Almost-sure log-affinity divergence under both laws gives global singularity. -/
theorem trajectory_hellinger_dichotomy
    {A : Type*} [Fintype A] [Nonempty A]
    [MeasurableSpace A] [MeasurableSingletonClass A] (hd : 2 ≤ Fintype.card A)
    (p q : List A → A → ℝ) (hp : NormalizedRows p) (hq : NormalizedRows q)
    (hp0 : ∀ h a, 0 < p h a) (hq0 : ∀ h a, 0 < q h a) :
    let H := fun (n : ℕ) (x : ℕ → A) => List.ofFn (fun i : Fin n => x i)
    let C := {x : ℕ → A | (∑' n, ENNReal.ofReal
      (1 - bhattacharyya (p (H n x)) (q (H n x)))) < ∞}
    let J := fun (n : ℕ) (x : ℕ → A) => ∑ i ∈ range n,
      -Real.log (bhattacharyya (p (H i x)) (q (H i x)))
    ((trajectoryLaw p hp).restrict C ≪ (trajectoryLaw q hq).restrict C ∧
      (trajectoryLaw q hq).restrict C ≪ (trajectoryLaw p hp).restrict C) ∧
    ((trajectoryLaw p hp).restrict Cᶜ ⟂ₘ (trajectoryLaw q hq).restrict Cᶜ) ∧
    ((∀ᵐ x ∂trajectoryLaw p hp, Tendsto (fun n => J n x) atTop atTop) →
      (∀ᵐ x ∂trajectoryLaw q hq, Tendsto (fun n => J n x) atTop atTop) →
      trajectoryLaw p hp ⟂ₘ trajectoryLaw q hq) := by
  classical
  intro H C J
  have hm n : Measurable (fun x : ℕ → A =>
      1 - bhattacharyya (p (H n x)) (q (H n x))) :=
    (measurable_of_countable (fun u : Fin n → A =>
      1 - bhattacharyya (p (List.ofFn u)) (q (List.ofFn u)))).comp
        (measurable_pi_lambda _ (fun i => measurable_pi_apply (i : ℕ)))
  have hC : MeasurableSet C :=
    measurableSet_lt (Measurable.ennreal_tsum (fun n => (hm n).ennreal_ofReal)) measurable_const
  have hsum x (hx : x ∈ C) : Summable (fun n =>
      1 - bhattacharyya (p (H n x)) (q (H n x))) := by
    have h := ENNReal.summable_toReal hx.ne
    simpa only [ENNReal.toReal_ofReal (sub_nonneg.mpr
      (bhattacharyya_le_one _ _ ⟨hp.1 _, hp.2 _⟩ ⟨hq.1 _, hq.2 _⟩))] using h
  let P := trajectoryLaw p hp
  let Q := trajectoryLaw q hq
  let L (n : ℕ) (x : ℕ → A) := ∏ i ∈ range n, q (H i x) (x i) / p (H i x) (x i)
  have hL n x : L n x ≠ 0 := (prod_pos (fun i _ => div_pos (hq0 _ _) (hp0 _ _))).ne'
  have hinv n x : (L n x)⁻¹ = ∏ i ∈ range n, p (H i x) (x i) / q (H i x) (x i) := by
    simp only [L, ← prod_inv_distrib, inv_div]
  have hP := trajectory_hellinger_likelihood_limits p q hp hq hp0 hq0
  have hQ := trajectory_hellinger_likelihood_limits q p hq hp hq0 hp0
  have hinf x (hx : x ∈ Cᶜ) : ¬ Summable (fun n =>
      1 - bhattacharyya (p (H n x)) (q (H n x))) := fun hs => hx hs.tsum_ofReal_lt_top
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · apply trajectory_restrict_ac_of_positive_limit hd p q hp hq hp0 hC
    filter_upwards [hP] with x hx hc
    exact hx.1 (hsum x hc)
  · apply trajectory_restrict_ac_of_positive_limit hd q p hq hp hq0 hC
    filter_upwards [hQ] with x hx hc
    apply hx.1
    simpa only [bhattacharyya, mul_comm] using hsum x hc
  · apply singular_of_reciprocal_limits (P.restrict Cᶜ) (Q.restrict Cᶜ) L hL
    · rw [ae_restrict_iff' hC.compl]
      filter_upwards [hP] with x hx hc
      exact hx.2 (hinf x hc)
    · rw [ae_restrict_iff' hC.compl]
      filter_upwards [hQ] with x hx hc
      simpa only [hinv] using hx.2 (by
        simpa only [bhattacharyya, mul_comm] using hinf x hc)
  · intro hJP hJQ
    have hlog x (hx : Tendsto (fun n => J n x) atTop atTop) :
        ¬ Summable (fun n => 1 - bhattacharyya (p (H n x)) (q (H n x))) := by
      intro hs
      have hlogs : Summable (fun n => -Real.log (bhattacharyya (p (H n x)) (q (H n x)))) := by
        have ht := (Real.summable_log_one_add_of_summable hs.neg).neg
        apply ht.congr
        intro n
        congr 2
        ring
      exact not_tendsto_nhds_of_tendsto_atTop hx _ hlogs.hasSum.tendsto_sum_nat
    apply singular_of_reciprocal_limits P Q L hL
    · filter_upwards [hP, hJP] with x hx hdiv
      exact hx.2 (hlog x hdiv)
    · filter_upwards [hQ, hJQ] with x hx hdiv
      simpa only [hinv] using hx.2 (by
        simpa only [bhattacharyya, mul_comm] using hlog x hdiv)

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.SequentialHellingerLocalization
