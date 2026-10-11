/- GID: D5/S3/Estimation/SequentialDecisionRisk/StoppedLikelihoodAbsorption
   generality: G
   mirror-B: D5/B/S3/Estimation/SequentialDecisionRisk/StoppedLikelihoodAbsorption
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite martingale maximal moments and stopped likelihood absorption. -/

import Mathlib.Probability.Martingale.OptionalStopping
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

noncomputable section

open MeasureTheory Filter Finset
open scoped BigOperators ENNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace D5.S3.Estimation.SequentialDecisionRisk.StoppedLikelihoodAbsorption

local notation "PMax" => fun (f : ℕ → ℝ) (n : ℕ) =>
  (range (n + 1)).sup' nonempty_range_add_one f

private lemma prefix_max_zero (f : ℕ → ℝ) : PMax f 0 = f 0 := by
  simp

private lemma prefix_max_succ (f : ℕ → ℝ) (n : ℕ) :
    PMax f (n + 1) = max (PMax f n) (f (n + 1)) := by
  calc
    PMax f (n + 1) = f (n + 1) ⊔ PMax f n := by
      simpa only [range_add_one] using
        (sup'_insert (s := range (n + 1)) nonempty_range_add_one f (b := n + 1))
    _ = _ := max_comm _ _

private lemma pathwise_max_sq (f : ℕ → ℝ) (n : ℕ) :
    (PMax f n) ^ 2 ≤ 2 * PMax f n * f n -
      2 * ∑ i ∈ range n, PMax f i * (f (i + 1) - f i) := by
  induction n with
  | zero => simp; nlinarith [sq_nonneg (f 0)]
  | succ n ih =>
    rw [prefix_max_succ, sum_range_succ]
    by_cases h : f (n + 1) ≤ PMax f n
    · rw [max_eq_left h]
      nlinarith
    · rw [max_eq_right (le_of_not_ge h)]
      nlinarith [sq_nonneg (f (n + 1) - PMax f n)]

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  [IsFiniteMeasure μ] {ℱ : Filtration ℕ mΩ}

private lemma martingale_abs_submartingale {f : ℕ → Ω → ℝ}
    (hf : Martingale f ℱ μ) : Submartingale (fun n ω => |f n ω|) ℱ μ := by
  refine ⟨fun n => ?_, ?_, fun n => (hf.integrable n).abs⟩
  · simpa only [Real.norm_eq_abs] using (hf.stronglyMeasurable n).norm
  · intro i j hij
    filter_upwards [hf.condExp_ae_eq hij,
      norm_condExp_le (m := ℱ i) (μ := μ) (f j)] with ω hω hle
    simpa only [Real.norm_eq_abs, hω] using hle

private lemma submartingale_integral_nonneg {f : ℕ → Ω → ℝ}
    (hf : Submartingale f ℱ μ) (hzero : f 0 = 0) (n : ℕ) :
    0 ≤ ∫ ω, f n ω ∂μ := by
  have h := hf.setIntegral_le (i := 0) (j := n) (Nat.zero_le n)
    (s := Set.univ) MeasurableSet.univ
  simpa [hzero] using h

private lemma prefix_max_adapted {f : ℕ → Ω → ℝ}
    (hf : StronglyAdapted ℱ f) :
    StronglyAdapted ℱ (fun n ω => PMax (fun i => f i ω) n) := by
  intro n
  induction n with
  | zero => simpa only [prefix_max_zero] using hf 0
  | succ n ih =>
    have heq : (fun ω => PMax (fun i => f i ω) (n + 1)) =
        (fun ω => max (PMax (fun i => f i ω) n) (f (n + 1) ω)) := by
      funext ω
      exact prefix_max_succ _ _
    change StronglyMeasurable[ℱ (n + 1)] (fun ω => PMax (fun i => f i ω) (n + 1))
    rw [heq]
    exact @StronglyMeasurable.sup Ω ℝ _ _ (ℱ (n + 1)) _ _ _
      (ih.mono (ℱ.mono (Nat.le_succ n))) (hf (n + 1))

private lemma pathwise_max_pow (f : ℕ → ℝ) (hf : ∀ i, 0 ≤ f i) (k n : ℕ) :
    (k + 1 : ℝ) * (PMax f n) ^ (k + 2) ≤
      (k + 2 : ℝ) * (PMax f n) ^ (k + 1) * f n -
      (k + 2 : ℝ) * ∑ i ∈ range n,
        (PMax f i) ^ (k + 1) * (f (i + 1) - f i) := by
  induction n with
  | zero =>
    simp only [prefix_max_zero, range_zero, sum_empty, mul_zero, sub_zero]
    have hpow := pow_nonneg (hf 0) (k + 2)
    rw [show k + 2 = (k + 1) + 1 by omega, pow_succ] at hpow ⊢
    nlinarith
  | succ n ih =>
    rw [prefix_max_succ, sum_range_succ]
    by_cases h : f (n + 1) ≤ PMax f n
    · rw [max_eq_left h]
      nlinarith
    · have ha : 0 ≤ PMax f n :=
        (hf 0).trans (le_sup' f (mem_range.mpr (by omega)))
      have h' : PMax f n ≤ f (n + 1) := le_of_not_ge h
      have ht := pow_add_mul_le_add_pow ha
        (show 0 ≤ 2 * PMax f n + (f (n + 1) - PMax f n) by linarith) (k + 2)
      simp only [add_sub_cancel, show k + 2 - 1 = k + 1 by omega,
        Nat.cast_add, Nat.cast_ofNat] at ht
      rw [max_eq_right h']
      simp only [show k + 2 = (k + 1) + 1 by omega, pow_succ] at ih ht ⊢
      nlinarith

private lemma pathwise_doob_pow (f : ℕ → ℝ) (hf : ∀ i, 0 ≤ f i) (k n : ℕ) :
    (k + 1 : ℝ) * (PMax f n) ^ (k + 2) ≤
      (2 : ℝ) ^ (k + 2) * (f n) ^ (k + 2) -
      2 * (k + 2 : ℝ) * ∑ i ∈ range n,
        (PMax f i) ^ (k + 1) * (f (i + 1) - f i) := by
  have ha : 0 ≤ PMax f n :=
    (hf 0).trans (le_sup' f (mem_range.mpr (by omega)))
  have ht := pow_add_mul_le_add_pow ha
    (show 0 ≤ 2 * PMax f n + (2 * f n - PMax f n) by nlinarith [hf n]) (k + 2)
  simp only [add_sub_cancel, show k + 2 - 1 = k + 1 by omega,
    Nat.cast_add, Nat.cast_ofNat] at ht
  rw [mul_pow] at ht
  have hpath := pathwise_max_pow f hf k n
  simp only [show k + 2 = (k + 1) + 1 by omega, pow_succ] at ht hpath ⊢
  nlinarith

private lemma doob_power_bound {f : ℕ → Ω → ℝ} (hf : Submartingale f ℱ μ)
    (hnonneg : ∀ i ω, 0 ≤ f i ω) {R : ℝ} (hbdd : ∀ i ω, f i ω ≤ R) (k n : ℕ) :
    (k + 1 : ℝ) * (∫ ω, (PMax (fun i => f i ω) n) ^ (k + 2) ∂μ) ≤
      (2 : ℝ) ^ (k + 2) * ∫ ω, (f n ω) ^ (k + 2) ∂μ := by
  let maxF : ℕ → Ω → ℝ := fun n ω => PMax (fun i => f i ω) n
  have hmax : StronglyAdapted ℱ maxF := prefix_max_adapted hf.stronglyAdapted
  have hmax0 : ∀ i ω, 0 ≤ maxF i ω := fun i ω =>
    (hnonneg 0 ω).trans (le_sup' (fun j => f j ω) (mem_range.mpr (by omega)))
  have hmaxR : ∀ i ω, maxF i ω ≤ R := fun i ω =>
    sup'_le _ _ (fun j _ => hbdd j ω)
  have hmaxpow : ∀ i, Integrable (fun ω => maxF i ω ^ (k + 2)) μ := fun i =>
    ⟨((hmax i).mono (ℱ.le i)).pow _ |>.aestronglyMeasurable,
      HasFiniteIntegral.of_bounded (ae_of_all μ (fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (hmax0 i ω) _)]
        exact pow_le_pow_left₀ (hmax0 i ω) (hmaxR i ω) _))⟩
  have hfnpow : Integrable (fun ω => f n ω ^ (k + 2)) μ :=
    ⟨((hf.stronglyMeasurable n).mono (ℱ.le n)).pow _ |>.aestronglyMeasurable,
      HasFiniteIntegral.of_bounded (ae_of_all μ (fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (hnonneg n ω) _)]
        exact pow_le_pow_left₀ (hnonneg n ω) (hbdd n ω) _))⟩
  have hsum := hf.sum_mul_sub (fun i => (hmax i).pow (k + 1))
    (fun i ω => pow_le_pow_left₀ (hmax0 i ω) (hmaxR i ω) (k + 1))
    (fun i ω => pow_nonneg (hmax0 i ω) (k + 1))
  have hsum0 : 0 ≤ ∫ ω, ∑ i ∈ range n,
      maxF i ω ^ (k + 1) * (f (i + 1) ω - f i ω) ∂μ := by
    simpa only [Finset.sum_apply, Pi.mul_apply, Pi.sub_apply, Pi.pow_apply] using
      submartingale_integral_nonneg hsum (by ext ω; simp) n
  have hsumint : Integrable (fun ω => ∑ i ∈ range n,
      maxF i ω ^ (k + 1) * (f (i + 1) ω - f i ω)) μ := by
    convert hsum.integrable n using 1
    ext ω
    simp only [Finset.sum_apply, Pi.mul_apply, Pi.sub_apply, Pi.pow_apply]
  have hrightint : Integrable (fun ω => (2 : ℝ) ^ (k + 2) * f n ω ^ (k + 2) -
      2 * (k + 2 : ℝ) * ∑ i ∈ range n,
        maxF i ω ^ (k + 1) * (f (i + 1) ω - f i ω)) μ :=
    (hfnpow.const_mul _).sub (hsumint.const_mul _)
  have hineq := integral_mono ((hmaxpow n).const_mul (k + 1 : ℝ))
    hrightint
    (fun ω => pathwise_doob_pow (fun i => f i ω) (fun i => hnonneg i ω) k n)
  rw [integral_sub (hfnpow.const_mul _) (hsumint.const_mul _),
    integral_const_mul, integral_const_mul, integral_const_mul] at hineq
  change (k + 1 : ℝ) * (∫ ω, maxF n ω ^ (k + 2) ∂μ) ≤ _ at hineq
  have hk : 0 ≤ (k + 2 : ℝ) := by positivity
  nlinarith

end D5.S3.Estimation.SequentialDecisionRisk.StoppedLikelihoodAbsorption
