/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/CriticalRenewalPaths
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/CriticalRenewalPaths
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Stopped drift and exit risks with the exact same-history paid execution. -/

import Mathlib.Probability.Martingale.OptionalStopping
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.Topology.Instances.ENNReal.ENatENNReal
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution.CriticalRenewalTable

section
noncomputable section
open MeasureTheory Filter Finset
open scoped ENNReal BigOperators Topology
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace D5.S3.Estimation.SequentialDecisionRisk.CriticalRenewalStoppedDrift
variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- First completed-block threshold exit. Index zero is excluded. -/
def exitTime (S : ℕ → Ω → ℝ) (b : ℝ) : Ω → WithTop ℕ :=
  hittingAfter S {x | b ≤ |x|} 1

/-- Real value of the bounded block clock, including infinite-exit paths. -/
def cappedTime (S : ℕ → Ω → ℝ) (b : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ((min (n : WithTop ℕ) (exitTime S b ω)).untopA : ℕ)

private lemma exit_stopping {ℱ : Filtration ℕ mΩ} {S : ℕ → Ω → ℝ}
    (hS : StronglyAdapted ℱ S) (b : ℝ) : IsStoppingTime ℱ (exitTime S b) :=
  hS.adapted.isStoppingTime_hittingAfter (n := 1)
    (measurableSet_le measurable_const (show Measurable (fun x : ℝ => |x|) from measurable_norm))

private lemma cappedTime_nonneg (S : ℕ → Ω → ℝ) (b : ℝ) (n : ℕ) (ω : Ω) :
    0 ≤ cappedTime S b n ω := by unfold cappedTime; positivity

private lemma cappedTime_le (S : ℕ → Ω → ℝ) (b : ℝ) (n : ℕ) (ω : Ω) :
    cappedTime S b n ω ≤ n := by
  unfold cappedTime
  exact_mod_cast (WithTop.untopA_le_iff (by simp : min (n : WithTop ℕ) (exitTime S b ω) ≠ ⊤)).mpr (min_le_left _ _)

private lemma cappedTime_measurable {ℱ : Filtration ℕ mΩ} {S : ℕ → Ω → ℝ}
    (hS : StronglyAdapted ℱ S) (b : ℝ) (n : ℕ) : StronglyMeasurable (cappedTime S b n) := by
  exact (show StronglyAdapted ℱ (fun k (_ : Ω) => (k : ℝ)) from
    fun _ => stronglyMeasurable_const).stronglyMeasurable_stoppedProcess_of_discrete
      (exit_stopping hS b) n

private lemma cappedTime_integrable {ℱ : Filtration ℕ mΩ} {S : ℕ → Ω → ℝ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] (hS : StronglyAdapted ℱ S) (b : ℝ) (n : ℕ) :
    Integrable (cappedTime S b n) μ := by
  apply Integrable.of_bound (cappedTime_measurable hS b n).aestronglyMeasurable (n : ℝ)
  exact ae_of_all _ fun ω => by rw [Real.norm_eq_abs, abs_of_nonneg (cappedTime_nonneg ..)]; exact cappedTime_le ..

private lemma score_bound {S : ℕ → Ω → ℝ} (hzero : ∀ ω, S 0 ω = 0)
    (hstep : ∀ n ω, |S (n + 1) ω - S n ω| ≤ 1) : ∀ n ω, |S n ω| ≤ n := by
  intro n ω
  have h := dist_le_range_sum_of_dist_le (f := fun k => S k ω)
    (d := fun _ => (1 : ℝ)) n (fun {k} _ => by
      simpa only [Real.dist_eq, abs_sub_comm] using hstep k ω)
  simpa only [hzero, Real.dist_eq, zero_sub, abs_neg, sum_const, card_range,
    nsmul_eq_mul, mul_one] using h

private lemma score_integrable {ℱ : Filtration ℕ mΩ} {S : ℕ → Ω → ℝ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] (hS : StronglyAdapted ℱ S)
    (hzero : ∀ ω, S 0 ω = 0) (hstep : ∀ n ω, |S (n + 1) ω - S n ω| ≤ 1) (n : ℕ) :
    Integrable (S n) μ := by
  exact Integrable.of_bound ((hS n).mono (ℱ.le n)).aestronglyMeasurable n
    (ae_of_all _ fun ω => by simpa only [Real.norm_eq_abs] using score_bound hzero hstep n ω)

private lemma stopped_bound {S : ℕ → Ω → ℝ} {b : ℝ} (hb : 0 < b)
    (hzero : ∀ ω, S 0 ω = 0) (hstep : ∀ n ω, |S (n + 1) ω - S n ω| ≤ 1)
    (n : ℕ) (ω : Ω) : |stoppedProcess S (exitTime S b) n ω| ≤ b + 1 := by
  let k := (min (n : WithTop ℕ) (exitTime S b ω)).untopA
  have hk : (k : WithTop ℕ) ≤ exitTime S b ω := by
    have ht : min (n : WithTop ℕ) (exitTime S b ω) ≠ ⊤ := by simp
    have he : ((min (n : WithTop ℕ) (exitTime S b ω)).untopA : WithTop ℕ) =
        min (n : WithTop ℕ) (exitTime S b ω) := by
      rw [WithTop.untopA_eq_untop ht]
      exact WithTop.coe_untop _ ht
    exact he ▸ min_le_right _ _
  change |S k ω| ≤ b + 1
  by_cases hk0 : k = 0
  · rw [hk0, hzero, abs_zero]; linarith
  · let j := k - 1
    have hjk : j + 1 = k := by dsimp [j]; omega
    have hj : (j : WithTop ℕ) < exitTime S b ω :=
      lt_of_lt_of_le (by exact_mod_cast (show j < k by omega)) hk
    have hpre : |S j ω| < b := by
      by_cases hj0 : j = 0
      · simp [hj0, hzero, hb]
      · have hh := notMem_of_lt_hittingAfter (u := S) (s := {x | b ≤ |x|})
          (n := 1) hj (show 1 ≤ j from Nat.one_le_iff_ne_zero.mpr hj0)
        exact lt_of_not_ge hh
    rw [← hjk]
    calc |S (j + 1) ω| = |S j ω + (S (j + 1) ω - S j ω)| := by congr 1; ring
      _ ≤ |S j ω| + |S (j + 1) ω - S j ω| := abs_add_le _ _
      _ ≤ b + 1 := add_le_add hpre.le (hstep j ω)

/-- Predictability, overshoot and exact finite stopped drift, without assuming
finiteness or integrability of the unbounded exit time. -/
theorem finite_stopped_drift {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ mΩ} {S : ℕ → Ω → ℝ} {b d : ℝ}
    (hS : StronglyAdapted ℱ S) (hb : 0 < b)
    (hzero : ∀ ω, S 0 ω = 0) (hstep : ∀ n ω, |S (n + 1) ω - S n ω| ≤ 1)
    (hmean : ∀ n, μ[fun ω => S (n + 1) ω - S n ω | ℱ n] =ᵐ[μ] fun _ => d) :
    (∀ n, MeasurableSet[ℱ n] {ω | (n : WithTop ℕ) < exitTime S b ω}) ∧
    (∀ n ω, |stoppedProcess S (exitTime S b) n ω| ≤ b + 1) ∧
    (∀ n, (∫ ω, stoppedProcess S (exitTime S b) n ω ∂μ) =
      d * ∫ ω, cappedTime S b n ω ∂μ) := by
  have hG := exit_stopping hS b
  refine ⟨fun n => by
      convert (hG n).compl using 1
      ext ω
      simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le]
      rfl,
    stopped_bound hb hzero hstep, ?_⟩
  let M : ℕ → Ω → ℝ := fun n ω => S n ω - d * n
  have hi := score_integrable hS hzero hstep (μ := μ)
  have hM : Martingale M ℱ μ := by
    apply martingale_of_condExp_sub_eq_zero_nat
      (show StronglyAdapted ℱ M from fun n => (hS n).sub stronglyMeasurable_const)
      (fun n => (hi n).sub (integrable_const _))
    intro n
    have heq : (M (n + 1) - M n) = (fun ω => (S (n + 1) ω - S n ω) - d) := by
      funext ω; dsimp [M]; push_cast; ring
    rw [heq]
    filter_upwards [condExp_sub ((hi (n + 1)).sub (hi n)) (integrable_const d) (ℱ n), hmean n] with ω hω hm
    simp only [Pi.sub_apply, condExp_const (ℱ.le n)] at hω
    change μ[S (n + 1) - S n | ℱ n] ω = d at hm
    rw [hm, sub_self] at hω
    exact hω
  intro n
  have hp := hM.submartingale.stoppedProcess hG
  have hn := hM.neg.submartingale.stoppedProcess hG
  have hlow := hp.setIntegral_le (Nat.zero_le n) MeasurableSet.univ
  have hupp := hn.setIntegral_le (Nat.zero_le n) MeasurableSet.univ
  have hZint : Integrable (stoppedProcess S (exitTime S b) n) μ :=
    integrable_stoppedProcess hG hi n
  have htint := cappedTime_integrable (μ := μ) hS b n
  have heq : stoppedProcess M (exitTime S b) n =
      (fun ω => stoppedProcess S (exitTime S b) n ω - d * cappedTime S b n ω) := rfl
  have hz : stoppedProcess M (exitTime S b) 0 = 0 := by
    ext ω; simp [stoppedProcess, M, hzero]
  simp only [setIntegral_univ, stoppedProcess_neg, Pi.neg_apply, integral_neg, hz, Pi.zero_apply, integral_zero] at hlow hupp
  rw [heq, integral_sub hZint (htint.const_mul _), integral_const_mul] at hlow
  rw [heq, integral_sub hZint (htint.const_mul _), integral_const_mul] at hupp
  linarith



private lemma cappedTime_mono (S : ℕ → Ω → ℝ) (b : ℝ) (ω : Ω) :
    Monotone (fun n => cappedTime S b n ω) := by
  intro i j hij
  dsimp only [cappedTime]
  exact Nat.cast_le.mpr (WithTop.untopA_mono (by simp)
    (min_le_min (WithTop.coe_le_coe.mpr hij) le_rfl))

private lemma clock_sup_finite (S : ℕ → Ω → ℝ) (b : ℝ) (ω : Ω)
    (hfin : exitTime S b ω ≠ ⊤) :
    (⨆ n, ENNReal.ofReal (cappedTime S b n ω)) =
      ENNReal.ofReal ((exitTime S b ω).untopA : ℝ) := by
  have hle : ∀ n, cappedTime S b n ω ≤ ((exitTime S b ω).untopA : ℝ) := by
    intro n
    unfold cappedTime
    exact_mod_cast WithTop.untopA_mono hfin (min_le_right (n : WithTop ℕ) _)
  have heq : cappedTime S b (exitTime S b ω).untopA ω =
      ((exitTime S b ω).untopA : ℝ) := by
    have hh : ((exitTime S b ω).untopA : WithTop ℕ) = exitTime S b ω := by
      rw [WithTop.untopA_eq_untop hfin]
      exact WithTop.coe_untop _ hfin
    unfold cappedTime
    rw [hh, min_self]
  apply le_antisymm (iSup_le fun n => ENNReal.ofReal_le_ofReal (hle n))
  rw [← heq]
  exact le_iSup (fun n => ENNReal.ofReal (cappedTime S b n ω)) _

/-- Monotone convergence of the finite clocks proves finite mean and almost-sure
termination before any infinite-horizon stopped-score argument. -/
theorem integrable_exit {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ mΩ} {S : ℕ → Ω → ℝ} {b d : ℝ}
    (hS : StronglyAdapted ℱ S) (hb : 0 < b) (hd : 0 < d)
    (hzero : ∀ ω, S 0 ω = 0) (hstep : ∀ n ω, |S (n + 1) ω - S n ω| ≤ 1)
    (hmean : ∀ n, μ[fun ω => S (n + 1) ω - S n ω | ℱ n] =ᵐ[μ] fun _ => d) :
    (∫⁻ ω, ⨆ n, ENNReal.ofReal (cappedTime S b n ω) ∂μ) ≤
      ENNReal.ofReal ((b + 1) / d) ∧
    (∀ᵐ ω ∂μ, exitTime S b ω ≠ ⊤) ∧
    Integrable (fun ω => ((exitTime S b ω).untopA : ℝ)) μ ∧
    (∫ ω, ((exitTime S b ω).untopA : ℝ) ∂μ) ≤ (b + 1) / d := by
  obtain ⟨_, hbound, hid⟩ := finite_stopped_drift hS hb hzero hstep hmean
  have hG := exit_stopping hS b
  have hti := cappedTime_integrable (μ := μ) hS b
  have hsi := integrable_stoppedProcess hG (score_integrable hS hzero hstep (μ := μ))
  have hfinite : ∀ n, (∫ ω, cappedTime S b n ω ∂μ) ≤ (b + 1) / d := by
    intro n
    apply (le_div_iff₀ hd).mpr
    have hi := integral_mono (hsi n) (integrable_const (b + 1))
      (fun ω => (le_abs_self _).trans (hbound n ω))
    rw [integral_const, probReal_univ, smul_eq_mul, one_mul, hid n] at hi
    linarith
  have hmeas : ∀ n, Measurable (fun ω => ENNReal.ofReal (cappedTime S b n ω)) :=
    fun n => (cappedTime_measurable hS b n).measurable.ennreal_ofReal
  let F : Ω → ℝ≥0∞ := fun ω => ⨆ n, ENNReal.ofReal (cappedTime S b n ω)
  have hFm : Measurable F := Measurable.iSup hmeas
  have hlim : (∫⁻ ω, F ω ∂μ) ≤ ENNReal.ofReal ((b + 1) / d) := by
    rw [show (∫⁻ ω, F ω ∂μ) = ⨆ n, ∫⁻ ω, ENNReal.ofReal (cappedTime S b n ω) ∂μ from
      lintegral_iSup hmeas (fun i j hij ω => ENNReal.ofReal_le_ofReal
        (cappedTime_mono S b ω hij))]
    apply iSup_le
    intro n
    rw [← ofReal_integral_eq_lintegral_ofReal (hti n)
      (ae_of_all _ (cappedTime_nonneg S b n))]
    exact ENNReal.ofReal_le_ofReal (hfinite n)
  have hFfin : ∀ᵐ ω ∂μ, F ω < ⊤ :=
    ae_lt_top hFm (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hlim)
  have hGfin : ∀ᵐ ω ∂μ, exitTime S b ω ≠ ⊤ := by
    filter_upwards [hFfin] with ω hω
    intro hg
    have htop : F ω = ⊤ := by
      dsimp [F]
      simp only [cappedTime, hg, min_eq_left le_top, WithTop.untopD_coe,
        ENNReal.ofReal_natCast]
      exact ENNReal.iSup_natCast
    rw [htop] at hω
    exact (lt_irrefl _ hω)
  have hEq : (fun ω => (F ω).toReal) =ᵐ[μ] fun ω => ((exitTime S b ω).untopA : ℝ) := by
    filter_upwards [hGfin] with ω hω
    rw [show F ω = ENNReal.ofReal ((exitTime S b ω).untopA : ℝ) from
      clock_sup_finite S b ω hω, ENNReal.toReal_ofReal (by positivity)]
  have hFi := integrable_toReal_of_lintegral_ne_top hFm.aemeasurable
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hlim)
  refine ⟨hlim, hGfin, hFi.congr hEq, ?_⟩
  rw [← integral_congr_ae hEq, integral_toReal hFm.aemeasurable hFfin]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hlim).trans_eq
    (ENNReal.toReal_ofReal (by positivity))

private lemma exp_quadratic {u lam : ℝ} (hu : |u| ≤ 1) (hlam : 0 ≤ lam) (hlam1 : lam ≤ 1) :
    Real.exp (lam * u) ≤ 1 + lam * u + (Real.exp 1 / 2) * lam ^ 2 * u ^ 2 := by
  have hx : |lam * u| ≤ 1 := by rw [abs_mul, abs_of_nonneg hlam]; nlinarith [abs_nonneg u]
  have ht := (le_abs_self (Real.exp (lam * u) - 1 - lam * u)).trans
    (Real.abs_exp_sub_one_sub_id_le hx)
  have he : 2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  nlinarith [mul_nonneg (sub_nonneg.mpr he) (sq_nonneg (lam * u))]

private lemma exp_integrable {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f : Ω → ℝ} {R lam : ℝ} (hf : StronglyMeasurable f) (hbound : ∀ ω, |f ω| ≤ R) :
    Integrable (fun ω => Real.exp (-lam * f ω)) μ := by
  apply Integrable.of_bound
    (Real.continuous_exp.comp_stronglyMeasurable (hf.const_mul (-lam))).aestronglyMeasurable
    (Real.exp (|lam| * R))
  filter_upwards with ω
  simp only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  calc -lam * f ω ≤ |-lam * f ω| := le_abs_self _
    _ = |lam| * |f ω| := by rw [abs_mul, abs_neg]
    _ ≤ |lam| * R := mul_le_mul_of_nonneg_left (hbound ω) (abs_nonneg _)

private lemma one_step_exponential {μ : Measure Ω} [IsProbabilityMeasure μ]
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ) {U : Ω → ℝ} {d v lam : ℝ}
    (hU : StronglyMeasurable[mΩ] U) (hbound : ∀ ω, |U ω| ≤ 1)
    (hmean : μ[U | m] =ᵐ[μ] fun _ => d)
    (hsecond : μ[fun ω => U ω ^ 2 | m] ≤ᵐ[μ] fun _ => v)
    (hlam : 0 < lam) (hlam1 : lam ≤ 1) (hsmall : (Real.exp 1 / 2) * lam * v ≤ d / 2) :
    μ[fun ω => Real.exp (-lam * U ω) | m] ≤ᵐ[μ] fun _ => 1 - lam * d / 2 := by
  have hi : Integrable U μ := Integrable.of_bound hU.aestronglyMeasurable 1
    (ae_of_all _ fun ω => by simpa only [Real.norm_eq_abs] using hbound ω)
  have hi2 : Integrable (fun ω => U ω ^ 2) μ := by
    apply Integrable.of_bound (hU.pow 2).aestronglyMeasurable 1
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    change U ω ^ 2 ≤ 1
    nlinarith [(abs_le.mp (hbound ω)).1, (abs_le.mp (hbound ω)).2]
  let a := (Real.exp 1 / 2) * lam ^ 2
  let Q : Ω → ℝ := ((fun _ => 1) + (-lam) • U) + a • (fun ω => U ω ^ 2)
  have hiL : Integrable ((fun _ => (1 : ℝ)) + (-lam) • U) μ :=
    (integrable_const 1).add (hi.smul (-lam))
  have hiQ : Integrable Q μ := hiL.add (hi2.smul a)
  have hcmp := condExp_mono (m := m) (exp_integrable hU hbound) hiQ
    (ae_of_all _ fun ω => by
      have ht := exp_quadratic (u := -U ω) (by simpa using hbound ω) hlam.le hlam1
      dsimp [Q, a]
      simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, neg_sq, mul_neg,
        neg_mul] using ht)
  have hqid : μ[Q | m] =ᵐ[μ]
      fun ω => 1 - lam * μ[U | m] ω + a * μ[fun ω => U ω ^ 2 | m] ω := by
    filter_upwards [condExp_add hiL (hi2.smul a) m,
      condExp_add (integrable_const (1 : ℝ)) (hi.smul (-lam)) m,
      condExp_smul (-lam) U m, condExp_smul a (fun ω => U ω ^ 2) m] with ω hq hl hu hv
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, condExp_const hm] at hq hl hu hv
    rw [hl, hu, hv] at hq
    simpa only [neg_mul, sub_eq_add_neg] using hq
  filter_upwards [hcmp, hqid, hmean, hsecond] with ω hc hq hm' hv
  rw [hq, hm'] at hc
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hav := mul_le_mul_of_nonneg_left hv ha
  have hs := mul_le_mul_of_nonneg_left hsmall hlam.le
  dsimp [a] at hc hav
  nlinarith

private lemma exponential_supermartingale {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ mΩ} {S : ℕ → Ω → ℝ} {d v lam : ℝ}
    (hS : StronglyAdapted ℱ S) (hzero : ∀ ω, S 0 ω = 0)
    (hstep : ∀ n ω, |S (n + 1) ω - S n ω| ≤ 1)
    (hmean : ∀ n, μ[fun ω => S (n + 1) ω - S n ω | ℱ n] =ᵐ[μ] fun _ => d)
    (hsecond : ∀ n, μ[fun ω => (S (n + 1) ω - S n ω)^2 | ℱ n] ≤ᵐ[μ] fun _ => v)
    (hd : 0 < d) (hlam : 0 < lam) (hlam1 : lam ≤ 1)
    (hsmall : (Real.exp 1 / 2) * lam * v ≤ d / 2) :
    Supermartingale (fun n ω => Real.exp (-lam * S n ω)) ℱ μ := by
  let E : ℕ → Ω → ℝ := fun n ω => Real.exp (-lam * S n ω)
  have he : StronglyAdapted ℱ E := fun n =>
    Real.continuous_exp.comp_stronglyMeasurable ((hS n).const_mul (-lam))
  have hei : ∀ n, Integrable (E n) μ := fun n =>
    exp_integrable ((hS n).mono (ℱ.le n)) (score_bound hzero hstep n)
  apply supermartingale_nat he hei
  intro n
  let U : Ω → ℝ := fun ω => S (n + 1) ω - S n ω
  have hU : StronglyMeasurable U :=
    ((hS (n + 1)).mono (ℱ.le (n + 1))).sub ((hS n).mono (ℱ.le n))
  have hUbound : ∀ ω, |U ω| ≤ 1 := hstep n
  have hmgf := one_step_exponential (ℱ.le n) hU hUbound (hmean n) (hsecond n)
    hlam hlam1 hsmall
  have heq : E (n + 1) = E n * (fun ω => Real.exp (-lam * U ω)) := by
    funext ω
    dsimp [E, U]
    rw [← Real.exp_add]
    congr 1
    ring
  rw [heq]
  have hiProd : Integrable (E n * (fun ω => Real.exp (-lam * U ω))) μ := heq ▸ hei (n + 1)
  filter_upwards [condExp_mul_of_stronglyMeasurable_left (he n) hiProd
    (exp_integrable hU hUbound), hmgf] with ω hp hm
  simp only [Pi.mul_apply] at hp
  rw [hp]
  have hmgf1 : μ[fun ω => Real.exp (-lam * U ω) | ℱ n] ω ≤ 1 := by
    linarith [mul_pos hlam hd]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hmgf1 (Real.exp_nonneg _)

private lemma stopped_exponential_risk {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ mΩ} {S : ℕ → Ω → ℝ} {b d v lam : ℝ}
    (hS : StronglyAdapted ℱ S) (hb : 0 < b)
    (hzero : ∀ ω, S 0 ω = 0) (hstep : ∀ n ω, |S (n + 1) ω - S n ω| ≤ 1)
    (hmean : ∀ n, μ[fun ω => S (n + 1) ω - S n ω | ℱ n] =ᵐ[μ] fun _ => d)
    (hsecond : ∀ n, μ[fun ω => (S (n + 1) ω - S n ω)^2 | ℱ n] ≤ᵐ[μ] fun _ => v)
    (hd : 0 < d) (hlam : 0 < lam) (hlam1 : lam ≤ 1)
    (hsmall : (Real.exp 1 / 2) * lam * v ≤ d / 2) :
    (∀ n, (∫ ω, Real.exp (-lam * stoppedProcess S (exitTime S b) n ω) ∂μ) ≤ 1) ∧
    (∫ ω, Real.exp (-lam * stoppedValue S (exitTime S b) ω) ∂μ) ≤ 1 ∧
    μ.real {ω | stoppedValue S (exitTime S b) ω ≤ -b} ≤ Real.exp (-lam * b) := by
  -- Termination is obtained solely from the finite drift, before taking this limit.
  have hfin := (integrable_exit hS hb hd hzero hstep hmean).2.1
  have hG := exit_stopping hS b
  have hE := exponential_supermartingale hS hzero hstep hmean hsecond hd hlam hlam1 hsmall
  have hbound := stopped_bound hb hzero hstep
  let Z : ℕ → Ω → ℝ := fun n ω => Real.exp (-lam * stoppedProcess S (exitTime S b) n ω)
  let Y : Ω → ℝ := fun ω => Real.exp (-lam * stoppedValue S (exitTime S b) ω)
  have hsm : ∀ n, StronglyMeasurable (Z n) := fun n =>
    Real.continuous_exp.comp_stronglyMeasurable
      ((hS.stronglyMeasurable_stoppedProcess_of_discrete hG n).const_mul (-lam))
  have hzbound : ∀ n ω, ‖Z n ω‖ ≤ Real.exp (lam * (b + 1)) := by
    intro n ω
    dsimp [Z]
    simp only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    have hs := (abs_le.mp (hbound n ω)).1
    nlinarith
  have hzi : ∀ n, Integrable (Z n) μ := fun n =>
    Integrable.of_bound (hsm n).aestronglyMeasurable _ (ae_of_all _ (hzbound n))
  have hbounded : ∀ n, (∫ ω, Z n ω ∂μ) ≤ 1 := by
    intro n
    have hh := (hE.neg.stoppedProcess hG).setIntegral_le (Nat.zero_le n) MeasurableSet.univ
    simp only [setIntegral_univ, stoppedProcess_neg, Pi.neg_apply, integral_neg,
      stoppedProcess_comp] at hh
    have hz : stoppedProcess (fun n ω => Real.exp (-lam * S n ω)) (exitTime S b) 0 =
        (fun _ => (1 : ℝ)) := by
      ext ω
      simp [stoppedProcess, hzero]
    change -(∫ ω, Z 0 ω ∂μ) ≤ -(∫ ω, Z n ω ∂μ) at hh
    have hz' : Z 0 = fun _ => (1 : ℝ) := hz
    rw [hz'] at hh
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hh
    linarith
  have hconv : ∀ᵐ ω ∂μ, Tendsto (fun n => Z n ω) atTop (𝓝 (Y ω)) := by
    filter_upwards [hfin] with ω hω
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (exitTime S b ω).untopA] with n hn
    have hh : ((exitTime S b ω).untopA : WithTop ℕ) = exitTime S b ω := by
      rw [WithTop.untopA_eq_untop hω]
      exact WithTop.coe_untop _ hω
    have hle : exitTime S b ω ≤ (n : WithTop ℕ) := by
      rw [← hh]
      exact WithTop.coe_le_coe.mpr hn
    dsimp [Z, Y]
    rw [stoppedProcess_eq_of_ge (u := S) (i := n) hle]
    rfl
  have hlim := tendsto_integral_of_dominated_convergence
    (fun _ => Real.exp (lam * (b + 1)))
    (fun n => (hsm n).aestronglyMeasurable) (integrable_const _)
    (fun n => ae_of_all _ (hzbound n)) hconv
  have hEY : (∫ ω, Y ω ∂μ) ≤ 1 := le_of_tendsto hlim (Eventually.of_forall hbounded)
  have hYm : StronglyMeasurable Y :=
    Real.continuous_exp.comp_stronglyMeasurable
      (((measurable_stoppedValue hS.isStronglyProgressive_of_discrete hG).mono
        hG.measurableSpace_le le_rfl).stronglyMeasurable.const_mul (-lam))
  have hYi : Integrable Y μ := by
    apply Integrable.of_bound hYm.aestronglyMeasurable (Real.exp (lam * (b + 1)))
    filter_upwards [hfin] with ω hω
    have hs : |stoppedValue S (exitTime S b) ω| ≤ b + 1 := by
      have hh : ((exitTime S b ω).untopA : WithTop ℕ) = exitTime S b ω := by
        rw [WithTop.untopA_eq_untop hω]
        exact WithTop.coe_untop _ hω
      have hv : stoppedProcess S (exitTime S b) (exitTime S b ω).untopA ω =
          stoppedValue S (exitTime S b) ω := by
        unfold stoppedProcess stoppedValue
        apply congrArg (fun k => S k ω)
        apply congrArg WithTop.untopA
        exact min_eq_right hh.symm.le
      rw [← hv]
      exact hbound _ ω
    dsimp [Y]
    simp only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    nlinarith [(abs_le.mp hs).1]
  refine ⟨hbounded, hEY, ?_⟩
  have hmark := mul_meas_ge_le_integral_of_nonneg
    (f := Y) (ae_of_all μ fun ω => Real.exp_nonneg _) hYi (Real.exp (lam * b))
  have hsub : {ω | stoppedValue S (exitTime S b) ω ≤ -b} ⊆
      {ω | Real.exp (lam * b) ≤ Y ω} := by
    intro ω hω
    apply Real.exp_le_exp.mpr
    dsimp only [Set.mem_ofPred_eq] at hω
    nlinarith
  have hprob := measureReal_mono hsub (μ := μ)
  have hmult := mul_le_mul_of_nonneg_left hprob (Real.exp_nonneg (lam * b))
  have hrisk : μ.real {ω | stoppedValue S (exitTime S b) ω ≤ -b} ≤
      1 / Real.exp (lam * b) := (le_div_iff₀ (Real.exp_pos _)).mpr (by linarith)
  simpa only [one_div, ← Real.exp_neg, neg_mul] using hrisk

/-- The two proof orientations of the critical renewal controller share one score
path and one threshold. Source-specific conditional moments remain explicit:
this theorem supplies no source law or bit-table realization. -/
theorem critical_renewal_stopping_risks
    {μ : Bool → Measure Ω} [∀ i, IsProbabilityMeasure (μ i)]
    {ℱ : Filtration ℕ mΩ} {S : ℕ → Ω → ℝ} {D₀ V₀ I Δ α δ : ℝ}
    (hS : StronglyAdapted ℱ S) (hzero : ∀ ω, S 0 ω = 0)
    (hstep : ∀ n ω, |S (n + 1) ω - S n ω| ≤ 1)
    (hD : 0 < D₀) (hV : 0 < V₀) (hI : 0 < I) (hΔ : D₀ * I ≤ Δ)
    (hα : 0 < α) (hαhalf : α < 1 / 2) (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2)
    (hmean : ∀ (i : Bool) n,
      (μ i)[fun ω => S (n + 1) ω - S n ω | ℱ n] =ᵐ[μ i]
        fun _ => (if i then (1 : ℝ) else -1) * Δ / 2)
    (hsecond : ∀ (i : Bool) n,
      (μ i)[fun ω => (S (n + 1) ω - S n ω)^2 | ℱ n] ≤ᵐ[μ i] fun _ => V₀ * I) :
    let lam := min 1 (D₀ / (2 * Real.exp 1 * V₀))
    let A := Real.log (1 / α) / lam
    let b := (⌈A / δ⌉ : ℝ) * δ
    (∀ n ω, |stoppedProcess S (exitTime S b) n ω| ≤ b + 1 ∧ b + 1 ≤ A + 3 / 2) ∧
    ∀ i : Bool,
      let sig : ℝ := if i then 1 else -1
      (∀ n, MeasurableSet[ℱ n] {ω | (n : WithTop ℕ) < exitTime S b ω}) ∧
      (∀ n, (∫ ω, sig * stoppedProcess S (exitTime S b) n ω ∂(μ i)) =
        (Δ / 2) * ∫ ω, cappedTime S b n ω ∂(μ i)) ∧
      (∀ᵐ ω ∂(μ i), exitTime S b ω ≠ ⊤) ∧
      Integrable (fun ω => ((exitTime S b ω).untopA : ℝ)) (μ i) ∧
      (∫ ω, ((exitTime S b ω).untopA : ℝ) ∂(μ i)) ≤ 2 * (A + 3 / 2) / Δ ∧
      (∀ n, (∫ ω, Real.exp (-lam * (sig * stoppedProcess S (exitTime S b) n ω))
        ∂(μ i)) ≤ 1) ∧
      (∫ ω, Real.exp (-lam * (sig * stoppedValue S (exitTime S b) ω)) ∂(μ i)) ≤ 1 ∧
      (μ i).real {ω | sig * stoppedValue S (exitTime S b) ω ≤ -b} ≤
        Real.exp (-lam * b) ∧ Real.exp (-lam * b) ≤ α := by
  classical
  intro lam A b
  have hΔpos : 0 < Δ := lt_of_lt_of_le (mul_pos hD hI) hΔ
  have hlam : 0 < lam := lt_min zero_lt_one (div_pos hD (by positivity))
  have hlam1 : lam ≤ 1 := min_le_left _ _
  have hlamD : lam * (2 * Real.exp 1 * V₀) ≤ D₀ :=
    (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
  have hlog : 0 < Real.log (1 / α) := Real.log_pos ((one_lt_div hα).mpr (by linarith))
  have hA : 0 < A := div_pos hlog hlam
  have hlA : lam * A = Real.log (1 / α) := by dsimp [A]; field_simp
  have hbLower : A ≤ b := by
    have hh := mul_le_mul_of_nonneg_right (Int.le_ceil (A / δ)) hδ.le
    dsimp [b]
    rw [div_mul_cancel₀ _ hδ.ne'] at hh
    exact hh
  have hbUpper : b ≤ A + 1 / 2 := by
    have hh := mul_le_mul_of_nonneg_right (Int.ceil_lt_add_one (A / δ)).le hδ.le
    dsimp [b]
    rw [add_mul, div_mul_cancel₀ _ hδ.ne', one_mul] at hh
    linarith
  have hb : 0 < b := hA.trans_le hbLower
  have hbb : b + 1 ≤ A + 3 / 2 := by linarith
  have hsmall : (Real.exp 1 / 2) * lam * (V₀ * I) ≤ (Δ / 2) / 2 := by
    have hh := mul_le_mul_of_nonneg_right hlamD hI.le
    nlinarith
  have halpha : Real.exp (-lam * b) ≤ α := by
    calc Real.exp (-lam * b) ≤ Real.exp (-Real.log (1 / α)) :=
          Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left hbLower hlam.le])
      _ = α := by
        rw [Real.exp_neg, Real.exp_log (by positivity)]
        field_simp
  refine ⟨fun n ω => ⟨stopped_bound hb hzero hstep n ω, hbb⟩, ?_⟩
  intro i
  let sig : ℝ := if i then 1 else -1
  let X : ℕ → Ω → ℝ := fun n ω => sig * S n ω
  have hsig : |sig| = 1 := by cases i <;> norm_num [sig]
  have hsig2 : sig * sig = 1 := by cases i <;> norm_num [sig]
  have hXS : StronglyAdapted ℱ X := fun n => (hS n).const_mul sig
  have hX0 : ∀ ω, X 0 ω = 0 := fun ω => by simp [X, hzero]
  have hXstep : ∀ n ω, |X (n + 1) ω - X n ω| ≤ 1 := by
    intro n ω
    dsimp [X]
    rw [← mul_sub, abs_mul, hsig, one_mul]
    exact hstep n ω
  have hXmean : ∀ n, (μ i)[fun ω => X (n + 1) ω - X n ω | ℱ n] =ᵐ[μ i]
      fun _ => Δ / 2 := by
    intro n
    have he : (fun ω => X (n + 1) ω - X n ω) =
        sig • (fun ω => S (n + 1) ω - S n ω) := by
      funext ω
      dsimp [X]
      ring
    rw [he]
    filter_upwards [condExp_smul sig (fun ω => S (n + 1) ω - S n ω) (ℱ n),
      hmean i n] with ω he hm
    change (μ i)[sig • (fun ω => S (n + 1) ω - S n ω) | ℱ n] ω =
      sig * (μ i)[fun ω => S (n + 1) ω - S n ω | ℱ n] ω at he
    rw [he, hm]
    change sig * (sig * Δ / 2) = Δ / 2
    nlinarith [hsig2]
  have hXsecond : ∀ n, (μ i)[fun ω => (X (n + 1) ω - X n ω)^2 | ℱ n] ≤ᵐ[μ i]
      fun _ => V₀ * I := by
    intro n
    have he : (fun ω => (X (n + 1) ω - X n ω)^2) =
        (fun ω => (S (n + 1) ω - S n ω)^2) := by
      funext ω
      dsimp [X]
      rw [← mul_sub, mul_pow]
      have hs : sig ^ 2 = 1 := by nlinarith [hsig2]
      rw [hs, one_mul]
    rw [he]
    exact hsecond i n
  have hGX : exitTime X b = exitTime S b := by
    funext ω
    have habs : ∀ j, |X j ω| = |S j ω| := fun j => by
      dsimp [X]
      rw [abs_mul, hsig, one_mul]
    have he : (∃ j, 1 ≤ j ∧ X j ω ∈ {x | b ≤ |x|}) =
        (∃ j, 1 ≤ j ∧ S j ω ∈ {x | b ≤ |x|}) := by
      apply propext
      simp only [Set.mem_ofPred_eq, habs]
    unfold exitTime hittingAfter
    rw [he]
    simp_rw [Set.mem_ofPred_eq, habs]
  have hstop : ∀ n ω, stoppedProcess X (exitTime X b) n ω =
      sig * stoppedProcess S (exitTime S b) n ω := by intro n ω; rw [hGX]; rfl
  have hvalue : ∀ ω, stoppedValue X (exitTime X b) ω =
      sig * stoppedValue S (exitTime S b) ω := by
    intro ω
    rw [hGX]
    rfl
  have htime : cappedTime X b = cappedTime S b := by unfold cappedTime; rw [hGX]
  obtain ⟨hpred, _, hid⟩ := finite_stopped_drift hXS hb hX0 hXstep hXmean
  obtain ⟨_, hfin, hint, hmeanbound⟩ :=
    integrable_exit hXS hb (by positivity : 0 < Δ / 2) hX0 hXstep hXmean
  obtain ⟨hbounded, hlimit, hrisk⟩ := stopped_exponential_risk hXS hb hX0 hXstep hXmean
    hXsecond (by positivity : 0 < Δ / 2) hlam hlam1 hsmall
  simp only [hGX] at hpred hfin hint hmeanbound
  simp_rw [hstop, htime] at hid
  simp_rw [hstop] at hbounded
  simp_rw [hvalue] at hlimit hrisk
  refine ⟨hpred, hid, hfin, hint, ?_, hbounded, hlimit, hrisk, halpha⟩
  calc (∫ ω, ((exitTime S b ω).untopA : ℝ) ∂(μ i)) ≤ (b + 1) / (Δ / 2) := hmeanbound
    _ = 2 * (b + 1) / Δ := by field_simp
    _ ≤ 2 * (A + 3 / 2) / Δ :=
      div_le_div_of_nonneg_right (by linarith) hΔpos.le

end D5.S3.Estimation.SequentialDecisionRisk.CriticalRenewalStoppedDrift

end
end

section
/-! Exact finite and infinite execution of one counted renewal table on one bit history. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Classical Finset
open scoped BigOperators

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution.CriticalRenewalPaths
open CriticalRenewalTable

def evidence {J : ℕ} (t : Tick J) (blocks : ℕ → Block) (n : ℕ) : ℤ :=
  ∑ k ∈ range n, increment t (blocks k)

/-- The ordinary real partial sum of the marks on grid spacing delta. -/
def score {J : ℕ} (δ : ℝ) (t : Tick J) (blocks : ℕ → Block) (n : ℕ) : ℝ :=
  ∑ k ∈ range n, (increment t (blocks k) : ℝ) * δ

def inside (H : ℕ) (u : ℤ) : Prop := -(H : ℤ) < u ∧ u < H

def clock (τ : ℕ) (blocks : ℕ → Block) (n : ℕ) : ℕ :=
  τ + 1 + ∑ k ∈ range n, ((blocks k).zeros.length + 1)

private lemma clock_succ (τ : ℕ) (blocks : ℕ → Block) (n : ℕ) :
    clock τ blocks (n+1) = clock τ blocks n + (blocks n).zeros.length + 1 := by
  simp only [clock, sum_range_succ]
  omega

private lemma clock_strict (τ : ℕ) (blocks : ℕ → Block) : StrictMono (clock τ blocks) := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [clock_succ]
  omega

private lemma clock_ge (τ : ℕ) (blocks : ℕ → Block) (n : ℕ) : n ≤ clock τ blocks n := by
  induction n with
  | zero => omega
  | succ n ih => rw [clock_succ]; omega

private lemma clock_unbounded (τ : ℕ) (blocks : ℕ → Block) (m : ℕ) :
    ∃ n, m < clock τ blocks (n+1) := ⟨m, by have := clock_ge τ blocks (m+1); omega⟩

/-- Locate proof coordinates in one uninterrupted bit history. -/
def blockIndex (τ : ℕ) (blocks : ℕ → Block) (m : ℕ) : ℕ :=
  Nat.find (clock_unbounded τ blocks m)

/-- An actual bit and the fresh outcome used for its single row transition. -/
def event (τ : ℕ) (blocks : ℕ → Block) (m : ℕ) : Bool × Bool :=
  if m < τ then (false,false)
  else if m = τ then (true,false)
  else
    let n := blockIndex τ blocks m
    let k := m - clock τ blocks n
    if k < (blocks n).zeros.length then (false, (blocks n).zeros[k]?.getD false)
    else (true, (blocks n).tick)

private lemma blockIndex_local (τ : ℕ) (blocks : ℕ → Block) (n k : ℕ)
    (hk : k ≤ (blocks n).zeros.length) :
    blockIndex τ blocks (clock τ blocks n + k) = n := by
  apply (Nat.find_eq_iff (clock_unbounded τ blocks (clock τ blocks n + k))).mpr
  constructor
  · rw [clock_succ]; omega
  · intro m hm
    have := (clock_strict τ blocks).monotone (show m+1 ≤ n by omega)
    omega

theorem consecutive_block_event (τ : ℕ) (blocks : ℕ → Block) (n k : ℕ)
    (hk : k ≤ (blocks n).zeros.length) :
    event τ blocks (clock τ blocks n + k) =
      if k < (blocks n).zeros.length then (false, (blocks n).zeros[k]?.getD false)
      else (true, (blocks n).tick) := by
  have ht : τ < clock τ blocks n + k := by dsimp [clock]; omega
  simp [event, not_lt.mpr ht.le, ne_of_gt ht, blockIndex_local τ blocks n k hk]

/-- Only the current counted state, next actual bit and fresh coin enter next. -/
def run {H J : ℕ} (hH : 0 < H) (t : Tick J) (τ : ℕ) (blocks : ℕ → Block) : ℕ → State H J
  | 0 => wait
  | m+1 => next hH t (run hH t τ blocks m) (event τ blocks m).1 (event τ blocks m).2

private lemma wait_prefix {H J : ℕ} (hH : 0 < H) (t : Tick J)
    (τ : ℕ) (blocks : ℕ → Block) (m : ℕ) (hm : m ≤ τ) :
    run hH t τ blocks m = wait := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have hh : m < τ := by omega
    simp [run, ih (by omega), event, hh, next, wait]

private lemma first_tick {H J : ℕ} (hH : 0 < H) (t : Tick J)
    (τ : ℕ) (blocks : ℕ → Block) :
    run hH t τ blocks (clock τ blocks 0) = active (initialEvidence hH) (Phase.first J) := by
  simp only [clock, range_zero, sum_empty, add_zero]
  simp [run, wait_prefix hH t τ blocks τ le_rfl, event, next, wait]

private lemma gap_prefix {H J : ℕ} (hH : 0 < H) (t : Tick J)
    (τ : ℕ) (blocks : ℕ → Block) (n : ℕ) (e : Evidence H)
    (hstart : run hH t τ blocks (clock τ blocks n) = active e (Phase.first J))
    (k : ℕ) (hk : k ≤ (blocks n).zeros.length) :
    run hH t τ blocks (clock τ blocks n + k) = active e (phaseAt J (blocks n) k) := by
  induction k with
  | zero => simpa [phaseAt] using hstart
  | succ k ih =>
    have hlt : k < (blocks n).zeros.length := by omega
    rw [Nat.add_succ, run, consecutive_block_event τ blocks n k hlt.le, if_pos hlt]
    simp only [Prod.fst, Prod.snd, ih (by omega), next, active, phaseAt]

private lemma gap_tick {H J : ℕ} (hH : 0 < H) (t : Tick J)
    (τ : ℕ) (blocks : ℕ → Block) (n : ℕ) (e : Evidence H)
    (hstart : run hH t τ blocks (clock τ blocks n) = active e (Phase.first J)) :
    run hH t τ blocks (clock τ blocks (n+1)) = target H J (e.val + increment t (blocks n)) := by
  rw [clock_succ, run, consecutive_block_event τ blocks n _ le_rfl, if_neg (lt_irrefl _)]
  rw [gap_prefix hH t τ blocks n e hstart _ le_rfl]
  rfl

private lemma target_inside {H J : ℕ} (u : ℤ) (hu : inside H u) :
    target H J u = active ⟨u, Finset.mem_Ioo.mpr hu⟩ (Phase.first J) := by
  simp [target, not_le.mpr hu.2, not_le.mpr hu.1]

private lemma run_endpoint {H J : ℕ} (hH : 0 < H) (t : Tick J)
    (τ : ℕ) (blocks : ℕ → Block) (n : ℕ)
    (hprev : ∀ m < n, inside H (evidence t blocks m)) :
    run hH t τ blocks (clock τ blocks n) = target H J (evidence t blocks n) := by
  induction n with
  | zero =>
    rw [first_tick]
    rw [show evidence t blocks 0 = 0 by simp [evidence], target,
      dif_neg (by omega : ¬ (H : ℤ) ≤ 0), dif_neg (by omega : ¬ (0 : ℤ) ≤ -(H : ℤ))]
    rfl
  | succ n ih =>
    have hnow := hprev n (by omega)
    have he := (ih (fun m hm => hprev m (by omega))).trans (target_inside _ hnow)
    rw [gap_tick hH t τ blocks n _ he]
    simp [evidence, sum_range_succ]

/-- Labels have no further reads in the paid run. The total trace only keeps
    their value fixed on the unused suffix. -/
def isLabel {H J : ℕ} : State H J → Prop
  | some (.inl _) => True
  | _ => False

private lemma target_label {H J : ℕ} (u : ℤ) :
    isLabel (target H J u) ↔ ¬ inside H u := by
  unfold target inside
  split <;> rename_i h
  · simp only [label, isLabel, true_iff]; omega
  · split <;> simp_all [label, active, isLabel] <;> omega

private lemma no_label_before {H J : ℕ} (hH : 0 < H) (t : Tick J)
    (τ : ℕ) (blocks : ℕ → Block) (g : ℕ)
    (hprev : ∀ n < g, inside H (evidence t blocks n))
    (m : ℕ) (hm : m < clock τ blocks g) : ¬ isLabel (run hH t τ blocks m) := by
  by_cases ht : m ≤ τ
  · rw [wait_prefix hH t τ blocks m ht]; simp [wait, isLabel]
  · let n := blockIndex τ blocks m
    have hu : m < clock τ blocks (n+1) := Nat.find_spec (clock_unbounded τ blocks m)
    have hl : clock τ blocks n ≤ m := by
      by_cases hn : n = 0
      · rw [hn]; simp only [clock, range_zero, sum_empty, add_zero]; omega
      · have hp := Nat.find_min (clock_unbounded τ blocks m) (show n-1 < n by omega)
        have hn' : n-1+1=n := by omega
        rw [hn'] at hp
        omega
    have hng : n < g := by
      by_contra hh
      have := (clock_strict τ blocks).monotone (show g ≤ n by omega)
      omega
    have he : run hH t τ blocks (clock τ blocks n) =
        active ⟨evidence t blocks n, Finset.mem_Ioo.mpr (hprev n hng)⟩ (Phase.first J) :=
      (run_endpoint hH t τ blocks n (fun a ha => hprev a (by omega))).trans
        (target_inside _ (hprev n hng))
    have hk : m - clock τ blocks n ≤ (blocks n).zeros.length := by
      rw [clock_succ] at hu; omega
    have hr := gap_prefix hH t τ blocks n _ he _ hk
    have eqm : clock τ blocks n + (m - clock τ blocks n) = m := by omega
    rw [eqm] at hr
    rw [hr]; simp [active, isLabel]

/-- The first threshold crossing in completed gaps, including the infinite case. -/
def gapStop {J : ℕ} (H : ℕ) (t : Tick J) (blocks : ℕ → Block) : ℕ∞ :=
  if h : ∃ n, ¬ inside H (evidence t blocks n) then (Nat.find h : ℕ∞) else ⊤

/-- First entry into either internally emitted label, measured in paid reads. -/
def paidStop {H J : ℕ} (hH : 0 < H) (t : Tick J) (τ : ℕ) (blocks : ℕ → Block) : ℕ∞ :=
  if h : ∃ m, isLabel (run hH t τ blocks m) then (Nat.find h : ℕ∞) else ⊤

/-- Finite threshold exit is the very same run's first label, with exact payment.
    Every suffix after phase death and the terminal closing tick remain charged. -/
theorem stopped_prefix_payment {H J : ℕ} (hH : 0 < H) (t : Tick J)
    (τ : ℕ) (blocks : ℕ → Block) (g : ℕ)
    (hexit : ¬ inside H (evidence t blocks g))
    (hprev : ∀ n < g, inside H (evidence t blocks n)) :
    gapStop H t blocks = (g : ℕ∞) ∧
    paidStop hH t τ blocks =
      ((1 + τ + ∑ n ∈ range g, ((blocks n).zeros.length + 1) : ℕ) : ℕ∞) ∧
    run hH t τ blocks (clock τ blocks g) = target H J (evidence t blocks g) ∧
    (∀ m < clock τ blocks g, ¬ isLabel (run hH t τ blocks m)) ∧
    (∀ n (hn : n < g) k, k ≤ (blocks n).zeros.length →
      run hH t τ blocks (clock τ blocks n + k) =
        active ⟨evidence t blocks n, Finset.mem_Ioo.mpr (hprev n hn)⟩ (phaseAt J (blocks n) k)) ∧
    (∀ (δ : ℝ), δ ≠ 0 → ∀ n, (evidence t blocks n : ℝ) = score δ t blocks n / δ) ∧
    (run hH t τ blocks (clock τ blocks g) = label true ↔ (H : ℤ) ≤ evidence t blocks g) ∧
    (run hH t τ blocks (clock τ blocks g) = label false ↔ evidence t blocks g ≤ -(H : ℤ)) ∧
    Fintype.card (State H J) = 3 + (2 * H - 1) * (J + 1) := by
  have hE : ∃ n, ¬ inside H (evidence t blocks n) := ⟨g,hexit⟩
  have hg : Nat.find hE = g := (Nat.find_eq_iff hE).mpr ⟨hexit, by simpa using hprev⟩
  have hend := run_endpoint hH t τ blocks g hprev
  have hlab : isLabel (run hH t τ blocks (clock τ blocks g)) := by
    rw [hend]; exact target_label _ |>.mpr hexit
  have hP : ∃ m, isLabel (run hH t τ blocks m) := ⟨_,hlab⟩
  have hp : Nat.find hP = clock τ blocks g := (Nat.find_eq_iff hP).mpr
    ⟨hlab, no_label_before hH t τ blocks g hprev⟩
  refine ⟨by simp [gapStop, hE, hg], ?_, hend, no_label_before hH t τ blocks g hprev,
    ?_, ?_, ?_, ?_, full_state_count H J hH⟩
  · simp [paidStop, hP, hp, clock, Nat.add_comm 1 τ]
  · intro n hn k hk
    exact gap_prefix hH t τ blocks n _
      ((run_endpoint hH t τ blocks n (fun m hm => hprev m (by omega))).trans
        (target_inside _ (hprev n hn))) k hk
  · intro δ hδ n
    simp only [score, ← sum_mul, evidence, Int.cast_sum]
    exact (mul_div_cancel_right₀ _ hδ).symm
  · rw [hend]
    unfold target
    split
    · simp_all [label]
    · split <;> simp_all [label, active]
  · rw [hend]
    unfold target
    split
    · have hn : ¬ evidence t blocks g ≤ -(H : ℤ) := by omega
      simp_all [label]
    · split <;> simp_all [label, active]

/-- If no completed-gap threshold is reached, no finite actual bit prefix emits
    a label. Infinite stopping is preserved, rather than assigned a default label. -/
theorem infinite_prefix {H J : ℕ} (hH : 0 < H) (t : Tick J)
    (τ : ℕ) (blocks : ℕ → Block)
    (h : ∀ n, inside H (evidence t blocks n)) :
    gapStop H t blocks = ⊤ ∧ paidStop hH t τ blocks = ⊤ := by
  have hp : ¬ ∃ m, isLabel (run hH t τ blocks m) := by
    rintro ⟨m,hm⟩
    exact no_label_before hH t τ blocks (m+1) (fun n _ => h n) m
      (by have := clock_ge τ blocks (m+1); omega) hm
  simp [gapStop, paidStop, h, hp]

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution.CriticalRenewalPaths

end
end
