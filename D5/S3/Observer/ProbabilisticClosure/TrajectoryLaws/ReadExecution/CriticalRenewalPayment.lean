/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/CriticalRenewalPayment
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/CriticalRenewalPayment
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Stopped drift, exit risks and exact payment on the actual renewal execution. -/

import Mathlib.Probability.Martingale.OptionalStopping
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.Topology.Instances.ENNReal.ENatENNReal
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution.CriticalRenewalFreshBlocks
import Mathlib.Probability.Independence.Integration

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
/-! Payment includes the initial wait and tick and every zero through the last closing tick. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Classical MeasureTheory ProbabilityTheory Finset
open scoped ENNReal BigOperators

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution.CriticalRenewalPayment
open CriticalRenewalTable CriticalRenewalPaths CriticalRenewalFreshBlocks

/-- Inclusion of zero-indexed block n depends only on the first n completed blocks. -/
def survives {J : ℕ} (H : ℕ) (t : Tick J) (n : ℕ) (bs : ℕ → Block) : Prop :=
  ∀ m ≤ n, inside H (evidence t bs m)

private lemma survives_iff {J : ℕ} (H : ℕ) (t : Tick J) (n : ℕ) (bs : ℕ → Block) :
    survives H t n bs ↔ (n : ℕ∞) < gapStop H t bs := by
  unfold gapStop
  split_ifs with h
  · simpa [survives, Nat.lt_find_iff]
  · have hh : ∀ m, inside H (evidence t bs m) := by simpa using h
    simp [survives, hh]

private lemma measurable_evidence {J : ℕ} (t : Tick J) (n : ℕ) :
    Measurable (fun ω : ℕ × (ℕ → Block) => evidence t ω.2 n) := by
  unfold evidence
  fun_prop

private lemma measurable_survives {J : ℕ} (H : ℕ) (t : Tick J) (n : ℕ) :
    MeasurableSet {ω : ℕ × (ℕ → Block) | survives H t n ω.2} := by
  simp only [survives, Set.ofPred_forall]
  exact MeasurableSet.iInter fun m => MeasurableSet.iInter fun _ =>
    (Set.to_countable {u : ℤ | inside H u}).measurableSet.preimage (measurable_evidence t m)

/-- An extended nonnegative cost on each included block. -/
def includedCost {J : ℕ} (H : ℕ) (t : Tick J) (n : ℕ)
    (ω : ℕ × (ℕ → Block)) : ℝ≥0∞ :=
  if survives H t n ω.2 then ((ω.2 n).zeros.length + 1 : ℕ) else 0

private lemma predictable_duration {J : ℕ} (H : ℕ) (t : Tick J)
    (w f : PMF ℕ) (n : ℕ) :
    (∫⁻ ω, includedCost H t n ω ∂sourceLaw w f t) =
      (∫⁻ k : ℕ, (k + 1 : ℕ) ∂f.toMeasure) *
        (sourceLaw w f t) {ω | survives H t n ω.2} := by
  let pair (k : ℕ) (ω : ℕ × (ℕ → Block)) :=
    ((ω.2 k).zeros.length, increment t (ω.2 k))
  let past (v : (k : range n) → ℕ × ℤ) : ℝ≥0∞ :=
    if ∀ m ≤ n, inside H (∑ k ∈ range m,
      if hk : k < n then (v ⟨k,mem_range.mpr hk⟩).2 else 0) then 1 else 0
  let duration (v : (k : ({n} : Finset ℕ)) → ℕ × ℤ) : ℝ≥0∞ :=
    ((v ⟨n,mem_singleton_self n⟩).1 + 1 : ℕ)
  have hdis : Disjoint (range n) {n} := by simp
  have hind := (fresh_same_source w f t).1.indepFun_finset (range n) {n} hdis
    (fun k => (measurable_of_countable (fun b : Block =>
      (b.zeros.length, increment t b))).comp ((measurable_pi_apply k).comp measurable_snd))
  -- Orient the disjoint tuples with the next duration first.
  have hind' := hind.symm.comp (measurable_of_countable duration) (measurable_of_countable past)
  have hpast (ω : ℕ × (ℕ → Block)) :
      past (fun k : range n => pair k ω) = if survives H t n ω.2 then 1 else 0 := by
    have he (m : ℕ) (hm : m ≤ n) :
        (∑ k ∈ range m, if hk : k < n then (pair k ω).2 else 0) =
          evidence t ω.2 m := by
      apply sum_congr rfl
      intro k hk
      simp [pair, show k < n by have := mem_range.mp hk; omega]
    dsimp only [past, survives]
    congr 1
    apply propext
    constructor <;> intro h m hm
    · simpa only [he m hm] using h m hm
    · simpa only [he m hm] using h m hm
  change IndepFun (fun ω : ℕ × (ℕ → Block) =>
      (((ω.2 n).zeros.length + 1 : ℕ) : ℝ≥0∞))
    (fun ω => past (fun k : range n => pair k ω)) (sourceLaw w f t) at hind'
  simp_rw [hpast] at hind'
  have hblock : Measurable (fun ω : ℕ × (ℕ → Block) => ω.2 n) :=
    (measurable_pi_apply n).comp measurable_snd
  have hmDur : Measurable (fun ω : ℕ × (ℕ → Block) =>
      (((ω.2 n).zeros.length + 1 : ℕ) : ℝ≥0∞)) :=
    (measurable_of_countable (fun b : Block => ((b.zeros.length+1 : ℕ) : ℝ≥0∞))).comp hblock
  have hmPast : Measurable (fun ω : ℕ × (ℕ → Block) =>
      if survives H t n ω.2 then (1 : ℝ≥0∞) else 0) :=
    measurable_const.ite (measurable_survives H t n) measurable_const
  have hfactor := lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun
    hmDur hmPast hind'
  have hduration : (sourceLaw w f t).map (fun ω => (ω.2 n).zeros.length) = f.toMeasure := by
    have hh := congrArg (fun μ : Measure (ℕ × (ℕ → ℕ)) =>
      μ.map (fun ω => ω.2 n)) (fresh_same_source w f t).2.2.2.1
    rw [Measure.map_map (by fun_prop) (by
      exact measurable_fst.prodMk (measurable_pi_iff.mpr fun k =>
        (measurable_of_countable (fun b : Block => b.zeros.length)).comp
          ((measurable_pi_apply k).comp measurable_snd)))] at hh
    have hm : (w.toMeasure.prod (Measure.infinitePi fun _ : ℕ => f.toMeasure)).map
        (fun ω => ω.2 n) = f.toMeasure := by
      change (w.toMeasure.prod (Measure.infinitePi fun _ : ℕ => f.toMeasure)).map
        ((fun bs : ℕ → ℕ => bs n) ∘ Prod.snd) = _
      rw [← Measure.map_map (measurable_pi_apply n) measurable_snd,
        Measure.map_snd_prod, measure_univ, one_smul, Measure.infinitePi_map_eval]
    exact hh.trans hm
  have hmean : (∫⁻ ω : ℕ × (ℕ → Block),
      (((ω.2 n).zeros.length + 1 : ℕ) : ℝ≥0∞) ∂sourceLaw w f t) =
      ∫⁻ k : ℕ, (k+1 : ℕ) ∂f.toMeasure := by
    rw [← hduration]
    exact (lintegral_map (measurable_of_countable (fun k : ℕ => ((k+1 : ℕ) : ℝ≥0∞)))
      ((measurable_of_countable (fun b : Block => b.zeros.length)).comp hblock)).symm
  rw [hmean] at hfactor
  have hi : (fun ω : ℕ × (ℕ → Block) =>
      if survives H t n ω.2 then (1 : ℝ≥0∞) else 0) =
      Set.indicator {ω | survives H t n ω.2} (fun _ => 1) := rfl
  rw [hi, lintegral_indicator (measurable_survives H t n), setLIntegral_one] at hfactor
  convert hfactor using 1
  apply lintegral_congr
  intro ω
  by_cases h : survives H t n ω.2 <;> simp [includedCost, h]

private lemma measurable_cost {J : ℕ} (H : ℕ) (t : Tick J) (n : ℕ) :
    Measurable (includedCost H t n) :=
  ((measurable_of_countable (fun b : Block => ((b.zeros.length+1 : ℕ) : ℝ≥0∞))).comp
    ((measurable_pi_apply n).comp measurable_snd)).ite
      (measurable_survives H t n) measurable_const

private lemma payment_series {J : ℕ} (H : ℕ) (t : Tick J) (w f : PMF ℕ) :
    (∫⁻ ω, ∑' n, includedCost H t n ω ∂sourceLaw w f t) =
      (∫⁻ k : ℕ, (k+1 : ℕ) ∂f.toMeasure) *
        ∫⁻ ω, ∑' n, (if survives H t n ω.2 then (1 : ℝ≥0∞) else 0)
          ∂sourceLaw w f t := by
  rw [lintegral_tsum (fun n => (measurable_cost H t n).aemeasurable)]
  simp_rw [predictable_duration H t w f]
  rw [ENNReal.tsum_mul_left,
    lintegral_tsum (fun n => (measurable_const.ite
      (measurable_survives H t n) measurable_const).aemeasurable)]
  congr 1
  apply tsum_congr
  intro n
  simpa only [one_mul, Set.indicator_apply, Set.mem_setOf_eq] using
    (lintegral_indicator_const (measurable_survives H t n) 1).symm

private lemma finite_payment {H J : ℕ} (hH : 0 < H) (t : Tick J)
    (ω : ℕ × (ℕ → Block)) (hfinite : gapStop H t ω.2 ≠ ⊤) :
    paidStop hH t ω.1 ω.2 ≠ ⊤ ∧
    (∑' n, if survives H t n ω.2 then (1 : ℝ≥0∞) else 0) =
      ((gapStop H t ω.2).toNat : ℝ≥0∞) ∧
    ((paidStop hH t ω.1 ω.2).toNat : ℝ≥0∞) =
      1 + (ω.1 : ℝ≥0∞) + ∑' n, includedCost H t n ω := by
  have hexists : ∃ g, ¬ inside H (evidence t ω.2 g) := by
    by_contra hh
    simp [gapStop, hh] at hfinite
  let g := Nat.find hexists
  have hg : ¬ inside H (evidence t ω.2 g) := Nat.find_spec hexists
  have hp : ∀ n < g, inside H (evidence t ω.2 n) := by
    intro n hn
    exact not_not.mp (Nat.find_min hexists hn)
  have hpath := stopped_prefix_payment hH t ω.1 ω.2 g hg hp
  have hinc (n : ℕ) : survives H t n ω.2 ↔ n < g := by
    rw [survives_iff, hpath.1]
    exact ENat.natCast_lt_natCast
  have hcount : (∑' n, if survives H t n ω.2 then (1 : ℝ≥0∞) else 0) = g := by
    simp_rw [hinc]
    rw [tsum_eq_sum (s := range g)]
    · calc
        _ = ∑ _n ∈ range g, (1 : ℝ≥0∞) :=
          sum_congr rfl (fun n hn => if_pos (mem_range.mp hn))
        _ = _ := by simp
    · intro n hn
      simp [mem_range.not.mp hn]
  have hcost : (∑' n, includedCost H t n ω) =
      ((∑ n ∈ range g, ((ω.2 n).zeros.length+1) : ℕ) : ℝ≥0∞) := by
    simp only [includedCost, hinc]
    rw [tsum_eq_sum (s := range g)]
    · simp only [Nat.cast_sum]
      apply sum_congr rfl
      intro n hn
      rw [if_pos (mem_range.mp hn)]
    · intro n hn
      simp [mem_range.not.mp hn]
  refine ⟨by rw [hpath.2.1]; exact ENat.natCast_ne_top _, ?_, ?_⟩
  · simpa [hpath.1] using hcount
  · rw [hpath.2.1, ENat.toNat_natCast, hcost]
    simp

/-- Exact paid expectation for both derived equilibrium renewal laws and the same
    actual bit table. Almost-sure gap exit and integrability remain explicit inputs. -/
theorem actual_source_payment (r : ℕ) (hr : 1 ≤ r) (c : ℝ) (hc : 0 < c)
    (s : ℝ) (hs : 0 < s) {H J : ℕ} (hH : 0 < H) (t : Tick J)
    (hfinite : ∀ i : Bool, ∀ᵐ ω ∂sourceLaw
      (CriticalRenewalSource.waitLaw r hr c hc i s hs)
      (CriticalRenewalSource.gapLaw r hr c hc i s hs) t, gapStop H t ω.2 ≠ ⊤)
    (hG : ∀ i : Bool, Integrable (fun ω : ℕ × (ℕ → Block) =>
      ((gapStop H t ω.2).toNat : ℝ)) (sourceLaw
        (CriticalRenewalSource.waitLaw r hr c hc i s hs)
        (CriticalRenewalSource.gapLaw r hr c hc i s hs) t)) :
    ∀ i : Bool,
      (∀ᵐ ω ∂sourceLaw (CriticalRenewalSource.waitLaw r hr c hc i s hs)
        (CriticalRenewalSource.gapLaw r hr c hc i s hs) t,
          paidStop hH t ω.1 ω.2 ≠ ⊤) ∧
      Integrable (fun ω : ℕ × (ℕ → Block) => ((paidStop hH t ω.1 ω.2).toNat : ℝ))
        (sourceLaw (CriticalRenewalSource.waitLaw r hr c hc i s hs)
          (CriticalRenewalSource.gapLaw r hr c hc i s hs) t) ∧
      (∫ ω : ℕ × (ℕ → Block), ((paidStop hH t ω.1 ω.2).toNat : ℝ)
        ∂sourceLaw (CriticalRenewalSource.waitLaw r hr c hc i s hs)
          (CriticalRenewalSource.gapLaw r hr c hc i s hs) t) =
        1 + CriticalRenewalSource.beta r c i s + CriticalRenewalSource.mean r c i s *
          ∫ ω : ℕ × (ℕ → Block), ((gapStop H t ω.2).toNat : ℝ)
            ∂sourceLaw (CriticalRenewalSource.waitLaw r hr c hc i s hs)
              (CriticalRenewalSource.gapLaw r hr c hc i s hs) t := by
  intro i
  let w := CriticalRenewalSource.waitLaw r hr c hc i s hs
  let f := CriticalRenewalSource.gapLaw r hr c hc i s hs
  let μ := sourceLaw w f t
  let N (ω : ℕ × (ℕ → Block)) : ℝ := (gapStop H t ω.2).toNat
  let T (ω : ℕ × (ℕ → Block)) : ℝ := (paidStop hH t ω.1 ω.2).toNat
  let total (ω : ℕ × (ℕ → Block)) : ℝ≥0∞ :=
    1 + (ω.1 : ℝ≥0∞) + ∑' n, includedCost H t n ω
  have hpath := (hfinite i).mono (fun ω hω => finite_payment hH t ω hω)
  have hcount : (∫⁻ ω, ∑' n, (if survives H t n ω.2 then (1 : ℝ≥0∞) else 0) ∂μ) =
      ENNReal.ofReal (∫ ω, N ω ∂μ) := by
    calc
      _ = ∫⁻ ω, ((gapStop H t ω.2).toNat : ℝ≥0∞) ∂μ :=
        lintegral_congr_ae (hpath.mono fun _ hω => hω.2.1)
      _ = ∫⁻ ω, ENNReal.ofReal (N ω) ∂μ := by simp [N]
      _ = _ := (ofReal_integral_eq_lintegral_ofReal (hG i)
        (Filter.Eventually.of_forall fun _ => Nat.cast_nonneg _)).symm
  have hsrc := CriticalRenewalSource.source_laws r hr c hc s hs
  have hk : Integrable (fun k : ℕ => (k : ℝ)) f.toMeasure := by
    simpa only [pow_one] using (hsrc.2.1 i 1).1
  have hk1 : Integrable (fun k : ℕ => (k : ℝ)+1) f.toMeasure := hk.add (integrable_const 1)
  have hkm : (∫ k : ℕ, (k : ℝ)+1 ∂f.toMeasure) = CriticalRenewalSource.mean r c i s := by
    rw [integral_add hk (integrable_const 1)]
    have hfirst := (hsrc.2.1 i 1).2
    simp only [pow_one] at hfirst
    change (∫ k : ℕ, (k : ℝ) ∂f.toMeasure) = _ at hfirst
    simp only [integral_const, probReal_univ, one_smul, CriticalRenewalSource.mean]
    exact congrArg (fun x : ℝ => x+1) hfirst
  have hmean : (∫⁻ k : ℕ, (k+1 : ℕ) ∂f.toMeasure) =
      ENNReal.ofReal (CriticalRenewalSource.mean r c i s) := by
    calc
      _ = ∫⁻ k : ℕ, ENNReal.ofReal ((k : ℝ)+1) ∂f.toMeasure := by
        congr 1
        funext k
        rw [ENNReal.ofReal_add (Nat.cast_nonneg k) (by norm_num)]
        simp
      _ = ENNReal.ofReal (∫ k : ℕ, (k : ℝ)+1 ∂f.toMeasure) :=
        (ofReal_integral_eq_lintegral_ofReal hk1 (Filter.Eventually.of_forall
          fun k => by positivity)).symm
      _ = _ := congrArg ENNReal.ofReal hkm
  have hwait : (∫⁻ ω : ℕ × (ℕ → Block), (ω.1 : ℝ≥0∞) ∂μ) =
      ENNReal.ofReal (CriticalRenewalSource.beta r c i s) := by
    have hm : μ.map Prod.fst = w.toMeasure := by
      simp only [μ, sourceLaw, Measure.map_fst_prod, measure_univ, one_smul]
    calc
      _ = ∫⁻ u : ℕ, (u : ℝ≥0∞) ∂w.toMeasure := by
        rw [← hm]
        exact (lintegral_map (measurable_of_countable _) measurable_fst).symm
      _ = ∫⁻ u : ℕ, ENNReal.ofReal (u : ℝ) ∂w.toMeasure := by simp
      _ = ENNReal.ofReal (∫ u : ℕ, (u : ℝ) ∂w.toMeasure) :=
        (ofReal_integral_eq_lintegral_ofReal (hsrc.2.2 i).1
          (Filter.Eventually.of_forall fun _ => Nat.cast_nonneg _)).symm
      _ = _ := congrArg ENNReal.ofReal (hsrc.2.2 i).2
  have hmWait : Measurable (fun ω : ℕ × (ℕ → Block) => (ω.1 : ℝ≥0∞)) :=
    (measurable_of_countable (fun u : ℕ => (u : ℝ≥0∞))).comp measurable_fst
  have hmSeries := Measurable.ennreal_tsum (fun n => measurable_cost H t n)
  have hmTotal : Measurable total := (measurable_const.add hmWait).add hmSeries
  have hext : (∫⁻ ω, total ω ∂μ) = 1 + ENNReal.ofReal (CriticalRenewalSource.beta r c i s) +
      ENNReal.ofReal (CriticalRenewalSource.mean r c i s) * ENNReal.ofReal (∫ ω, N ω ∂μ) := by
    dsimp only [total]
    rw [lintegral_add_left (f := fun ω : ℕ × (ℕ → Block) => 1 + (ω.1 : ℝ≥0∞))
      (measurable_const.add hmWait) (fun ω => ∑' n, includedCost H t n ω),
      lintegral_add_left (f := fun _ : ℕ × (ℕ → Block) => (1 : ℝ≥0∞))
        measurable_const (fun ω => (ω.1 : ℝ≥0∞)),
      lintegral_const, measure_univ, mul_one, hwait, payment_series H t w f, hmean, hcount]
  have htotal : (∫⁻ ω, total ω ∂μ) ≠ ⊤ := by rw [hext]; finiteness
  have htotalFinite : ∀ᵐ ω ∂μ, total ω < ⊤ := by
    filter_upwards [hpath] with ω hω
    dsimp only [total]
    rw [← hω.2.2]
    exact ENNReal.natCast_lt_top _
  have hreal : (fun ω => (total ω).toReal) =ᵐ[μ] T := by
    filter_upwards [hpath] with ω hω
    dsimp only [total]
    rw [← hω.2.2]
    simp [T]
  refine ⟨hpath.mono (fun _ hω => hω.1),
    (integrable_toReal_of_lintegral_ne_top hmTotal.aemeasurable htotal).congr hreal, ?_⟩
  change (∫ ω, T ω ∂μ) = _
  rw [← integral_congr_ae hreal, integral_toReal hmTotal.aemeasurable htotalFinite, hext]
  have hb : 0 ≤ CriticalRenewalSource.beta r c i s := by
    rw [← (hsrc.2.2 i).2]
    exact integral_nonneg (fun _ => Nat.cast_nonneg _)
  have hm := (hsrc.1.1 i).mean_positive.le
  have hn : 0 ≤ ∫ ω, N ω ∂μ := integral_nonneg (fun _ => Nat.cast_nonneg _)
  rw [ENNReal.toReal_add (by finiteness) (by finiteness),
    ENNReal.toReal_add (by finiteness) (by finiteness), ENNReal.toReal_one,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal hb, ENNReal.toReal_ofReal hm,
    ENNReal.toReal_ofReal hn]

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution.CriticalRenewalPayment

end
end
