/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/SequentialHellingerLocalization
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/SequentialHellingerLocalization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Predictable energy truncations give a common almost-sure convergence set. -/

import Mathlib.Probability.Martingale.Convergence
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
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
    (∫ ω, (∑ i ∈ range n, d i ω)^2 ∂μ) =
      ∑ i ∈ range n, ∫ ω, (d i ω)^2 ∂μ := by
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
    have heq : (fun ω => ((∑ i ∈ range n, d i ω) + d n ω)^2) =
        (fun ω => (∑ i ∈ range n, d i ω)^2) +
        (fun ω => 2 * ((∑ i ∈ range n, d i ω) * d n ω)) +
        (fun ω => (d n ω)^2) := by ext ω; simp only [Pi.add_apply]; ring
    simp only [Pi.mul_def] at hprod
    rw [heq]
    simp only [Pi.add_def]
    have hplus : Integrable (fun ω => (∑ i ∈ range n, d i ω)^2 +
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
    (hdv : ∀ n, μ[fun ω => (d n ω)^2 | ℱ n] ≤ᵐ[μ] fun ω => 2 * e n ω)
    (hy : ∀ n, StronglyMeasurable[ℱ (n + 1)] (y n))
    (hyi : ∀ n, Integrable (y n) μ)
    (hy0 : ∀ n ω, 0 ≤ y n ω)
    (hyc : ∀ n, μ[y n | ℱ n] ≤ᵐ[μ] fun ω => 2 * e n ω) :
    (∀ K : ℕ, ∀ n : ℕ,
      (∫ ω, (∑ i ∈ range n, (energyCut e K i).indicator (d i) ω)^2 ∂μ)
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
  have hDv K n : (∫ ω, (D K n ω)^2 ∂μ) ≤ 2 * ∫ ω, E K n ω ∂μ := by
    have hi := cut_integral_bound he hei (fun n => (hd2 n).integrable_sq) hdv (K : ℝ) n
    convert hi using 1
    apply integral_congr_ae
    filter_upwards [] with ω
    simp only [D, Set.indicator_apply]
    split_ifs <;> simp
  have hYv K n : (∫ ω, Y K n ω ∂μ) ≤ 2 * ∫ ω, E K n ω ∂μ :=
    cut_integral_bound he hei hyi hyc (K : ℝ) n
  have hjoint K n :
      (∫ ω, (∑ i ∈ range n, D K i ω)^2 ∂μ) ≤ 2 * ((K : ℝ) + 1) ∧
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
        _ ≤ ∫ ω, (∑ i ∈ range n, D K i ω)^2 + 1 ∂μ :=
          integral_mono (hmi.integrable n).norm (hs2.add (integrable_const 1))
            (fun ω => by
              rw [Real.norm_eq_abs]
              have h := sq_nonneg (|∑ i ∈ range n, D K i ω| - 1)
              nlinarith [abs_nonneg (∑ i ∈ range n, D K i ω),
                sq_abs (∑ i ∈ range n, D K i ω)])
        _ = (∫ ω, (∑ i ∈ range n, D K i ω)^2 ∂μ) + 1 := by
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

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.SequentialHellingerLocalization
