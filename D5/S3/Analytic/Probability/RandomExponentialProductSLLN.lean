/- GID: D5/S3/Analytic/Probability/RandomExponentialProductSLLN
   generality: G
   mirror-B: D5/B/S3/Analytic/Probability/RandomExponentialProductSLLN
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Bounded iid operator exponentials satisfy the strong law on every Banach space. -/

import D5.S3.Quantum.AURICOmega.ExponentialTail
import Mathlib.Probability.StrongLaw
import Mathlib.Analysis.SpecialFunctions.Exponential

/-! Products of bounded iid operator exponentials and their deterministic Abel estimate. -/

noncomputable section

open Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators

namespace D5.S3.Analytic.Probability.RandomExponentialProductSLLN

/-- The factors are multiplied from left to right in increasing index order. -/
def randomProduct {𝕜 e α : Type} [RCLike 𝕜] [NormedAddCommGroup e]
    [NormedSpace 𝕜 e] (a : ℕ → α → e →L[𝕜] e) (n : ℕ) (t : ℝ) (ω : α) :
    e →L[𝕜] e :=
  (List.ofFn fun i : Fin n => NormedSpace.exp (((t / n : ℝ) : 𝕜) • a i ω)).prod

/-- Almost sure convergence in the strong operator topology, uniformly on compact time intervals. -/
def claim : Prop :=
  ∀ (𝕜 e α : Type) [RCLike 𝕜] [NormedAddCommGroup e] [NormedSpace 𝕜 e]
    [CompleteSpace e] [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ],
    letI := NormedAlgebra.restrictScalars ℝ 𝕜 (e →L[𝕜] e)
    letI : MeasurableSpace (e →L[𝕜] e) := borel (e →L[𝕜] e)
    ∀ (a : ℕ → α → e →L[𝕜] e),
      (∀ i, AEStronglyMeasurable (a i) μ) →
      Pairwise (fun i j => IndepFun (a i) (a j) μ) →
      (∀ i, IdentDistrib (a i) (a 0) μ μ) →
      ∀ (m : ℝ), (∀ i, ∀ᵐ ω ∂μ, ‖a i ω‖ ≤ m) →
      ∀ (x : e) (t : ℝ), 0 ≤ t → ∀ᵐ ω ∂μ,
        ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ s ∈ Set.Icc (0 : ℝ) t,
          ‖(randomProduct a n s ω -
            NormedSpace.exp (((s : ℝ) : 𝕜) • ∫ z, a 0 z ∂μ)) x‖ < ε

private def eulerProduct {e : Type*} [Ring e] [Module ℝ e]
    (a : ℕ → e) (h : ℝ) (n : ℕ) : e :=
  (List.ofFn fun i : Fin n => 1 + h • a i).prod

private def centeredSum {e : Type*} [AddCommGroup e] (a : ℕ → e) (b : e) (n : ℕ) : e :=
  ∑ i ∈ Finset.range n, (a i - b)

private lemma euler_succ {e : Type*} [Ring e] [Module ℝ e]
    (a : ℕ → e) (h : ℝ) (n : ℕ) :
    eulerProduct a h (n + 1) = eulerProduct a h n * (1 + h • a n) := by
  change (List.ofFn fun i : Fin (n + 1) => 1 + h • a i).prod = _
  rw [List.ofFn_succ', List.prod_concat]
  rfl

private lemma centered_succ {e : Type*} [AddCommGroup e] (a : ℕ → e) (b : e) (n : ℕ) :
    centeredSum a b (n + 1) = centeredSum a b n + (a n - b) := by
  exact Finset.sum_range_succ (fun i => a i - b) n

private lemma euler_norm {e : Type*} [NormedRing e] [NormedAlgebra ℝ e]
    [NormOneClass e] (a : ℕ → e) (m h : ℝ) (n : ℕ)
    (hm : 0 ≤ m) (hh : 0 ≤ h) (ha : ∀ i < n, ‖a i‖ ≤ m) :
    ‖eulerProduct a h n‖ ≤ (1 + h * m) ^ n := by
  induction n with
  | zero => change ‖(1 : e)‖ ≤ (1 + h * m) ^ 0; rw [norm_one, pow_zero]
  | succ n ih =>
    rw [euler_succ, pow_succ]
    have hf : ‖1 + h • a n‖ ≤ 1 + h * m := by
      calc
        _ ≤ ‖(1 : e)‖ + ‖h • a n‖ := norm_add_le _ _
        _ = 1 + h * ‖a n‖ := by rw [norm_one, norm_smul, Real.norm_eq_abs, abs_of_nonneg hh]
        _ ≤ _ := by gcongr; exact ha n (by omega)
    exact (norm_mul_le _ _).trans
      (mul_le_mul (ih (fun i hi => ha i (by omega))) hf (norm_nonneg _) (by positivity))

private lemma abel_step {e : Type*} [Ring e] [Algebra ℝ e]
    (a : ℕ → e) (b : e) (h : ℝ) (n : ℕ) :
    eulerProduct a h (n + 1) - (1 + h • b) ^ (n + 1) -
        h • (eulerProduct a h (n + 1) * centeredSum a b (n + 1)) =
      (eulerProduct a h n - (1 + h • b) ^ n -
        h • (eulerProduct a h n * centeredSum a b n)) * (1 + h • b) +
      h ^ 2 • (eulerProduct a h n *
        (centeredSum a b n * b - a n * centeredSum a b (n + 1))) := by
  rw [euler_succ, pow_succ, centered_succ]
  simp only [mul_add, add_mul, sub_mul, mul_sub, mul_smul_comm, smul_mul_assoc,
    smul_add, smul_sub, smul_smul, one_mul, mul_one, mul_assoc]
  module

private lemma euler_abel_bound {e : Type*} [NormedRing e] [NormedAlgebra ℝ e]
    [NormOneClass e] (a : ℕ → e) (b : e) (m h r : ℝ) (n : ℕ)
    (hm : 0 ≤ m) (hh : 0 ≤ h) (hr : 0 ≤ r)
    (ha : ∀ i < n, ‖a i‖ ≤ m) (hb : ‖b‖ ≤ m)
    (hs : ∀ k ≤ n, ‖centeredSum a b k‖ ≤ r) :
    ‖eulerProduct a h n - (1 + h • b) ^ n‖ ≤
      h * Real.exp (h * m * n) * (1 + 2 * h * m * n) * r := by
  let l := 1 + h * m
  have hl : 1 ≤ l := by dsimp [l]; nlinarith
  have hq : ‖1 + h • b‖ ≤ l := by
    calc
      _ ≤ ‖(1 : e)‖ + ‖h • b‖ := norm_add_le _ _
      _ = 1 + h * ‖b‖ := by rw [norm_one, norm_smul, Real.norm_eq_abs, abs_of_nonneg hh]
      _ ≤ l := by dsimp [l]; gcongr
  have he : ∀ k ≤ n,
      ‖eulerProduct a h k - (1 + h • b) ^ k - h • (eulerProduct a h k * centeredSum a b k)‖ ≤
        2 * k * h ^ 2 * m * r * l ^ k := by
    intro k hk
    induction k with
    | zero =>
      unfold eulerProduct centeredSum
      rw [List.ofFn_zero, List.prod_nil, Finset.sum_range_zero, pow_zero]
      simp only [sub_self, mul_zero, smul_zero, sub_zero, norm_zero,
        Nat.cast_zero, mul_zero, zero_mul, pow_zero, le_refl]
    | succ k ih =>
      rw [abel_step]
      have hp := euler_norm a m h k hm hh (fun i hi => ha i (by omega))
      have hterm : ‖centeredSum a b k * b - a k * centeredSum a b (k + 1)‖ ≤ 2 * m * r := by
        calc
          _ ≤ ‖centeredSum a b k * b‖ + ‖a k * centeredSum a b (k + 1)‖ := norm_sub_le _ _
          _ ≤ r * m + m * r := add_le_add
            ((norm_mul_le _ _).trans (mul_le_mul (hs k (by omega)) hb (norm_nonneg _) hr))
            ((norm_mul_le _ _).trans (mul_le_mul (ha k (by omega))
              (hs (k + 1) hk) (norm_nonneg _) hm))
          _ = _ := by ring
      have hpow : l ^ k ≤ l ^ (k + 1) := pow_le_pow_right₀ hl (by omega)
      calc
        _ ≤ ‖(eulerProduct a h k - (1 + h • b) ^ k -
            h • (eulerProduct a h k * centeredSum a b k)) * (1 + h • b)‖ +
            ‖h ^ 2 • (eulerProduct a h k *
              (centeredSum a b k * b - a k * centeredSum a b (k + 1)))‖ := norm_add_le _ _
        _ ≤ (2 * k * h ^ 2 * m * r * l ^ k) * l + h ^ 2 * (l ^ k * (2 * m * r)) := by
          apply add_le_add
          · exact (norm_mul_le _ _).trans
              (mul_le_mul (ih (by omega)) hq (norm_nonneg _) (by positivity))
          · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg h)]
            gcongr
            exact (norm_mul_le _ _).trans (mul_le_mul hp hterm (norm_nonneg _) (by positivity))
        _ ≤ (2 * k * h ^ 2 * m * r * l ^ k) * l + h ^ 2 * (l ^ (k + 1) * (2 * m * r)) := by
          gcongr
        _ = 2 * (k + 1 : ℕ) * h ^ 2 * m * r * l ^ (k + 1) := by
          rw [pow_succ l k, Nat.cast_add, Nat.cast_one]
          ring
  have hp := euler_norm a m h n hm hh ha
  have hp_exp : l ^ n ≤ Real.exp (h * m * n) := by
    calc
      l ^ n ≤ (Real.exp (h * m)) ^ n := by
        gcongr
        simpa only [l, add_comm] using Real.add_one_le_exp (h * m)
      _ = Real.exp (h * m * n) := by rw [← Real.exp_nat_mul]; congr 1; ring
  calc
    _ ≤ ‖eulerProduct a h n - (1 + h • b) ^ n - h • (eulerProduct a h n * centeredSum a b n)‖ +
        ‖h • (eulerProduct a h n * centeredSum a b n)‖ := norm_le_norm_sub_add _ _
    _ ≤ 2 * n * h ^ 2 * m * r * l ^ n + h * (l ^ n * r) := by
      apply add_le_add (he n le_rfl)
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hh]
      gcongr
      exact (norm_mul_le _ _).trans (mul_le_mul hp (hs n le_rfl) (norm_nonneg _) (by positivity))
    _ = h * l ^ n * (1 + 2 * h * m * n) * r := by ring
    _ ≤ _ := by gcongr


private lemma exponential_euler_bound {e : Type*} [NormedRing e] [NormedAlgebra ℝ e]
    [NormOneClass e] [CompleteSpace e] (a : ℕ → e) (m t : ℝ) (n : ℕ)
    (hm : 0 ≤ m) (ht : 0 ≤ t) (hn : 0 < n)
    (ha : ∀ i < n, ‖a i‖ ≤ m) (hsmall : t / n * m ≤ 1) :
    ‖(List.ofFn fun i : Fin n => NormedSpace.exp ((t / n) • a i)).prod -
      eulerProduct a (t / n) n‖ ≤
      (3 / 4 : ℝ) * m ^ 2 * t ^ 2 * Real.exp (m * t) / n := by
  sorry

private lemma centered_max_sublinear {e : Type*} [NormedAddCommGroup e]
    [NormedSpace ℝ e] (a : ℕ → e) (b : e)
    (hav : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, a i)
      atTop (𝓝 b)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      ∀ k ≤ n, ‖centeredSum a b k‖ ≤ ε * n := by
  sorry

private lemma deterministic_uniform {e : Type*} [NormedRing e] [NormedAlgebra ℝ e]
    [NormOneClass e] [CompleteSpace e] (a : ℕ → e) (b : e) (m : ℝ)
    (hm : 0 ≤ m) (ha : ∀ i, ‖a i‖ ≤ m) (hb : ‖b‖ ≤ m)
    (hav : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, a i)
      atTop (𝓝 b)) :
    ∀ t : ℝ, 0 ≤ t → ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      ∀ s ∈ Set.Icc (0 : ℝ) t,
        ‖(List.ofFn fun i : Fin n => NormedSpace.exp ((s / n) • a i)).prod -
          NormedSpace.exp (s • b)‖ < ε := by
  have hab := euler_abel_bound a b m
  have hex := exponential_euler_bound a m
  have hmax := centered_max_sublinear a b hav
  sorry

private lemma operator_uniform_to_sot {𝕜 e α : Type} [RCLike 𝕜]
    [NormedAddCommGroup e] [NormedSpace 𝕜 e] [CompleteSpace e]
    [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (a : ℕ → α → e →L[𝕜] e)
    (hsm : ∀ i, AEStronglyMeasurable (a i) μ)
    (hind : letI : MeasurableSpace (e →L[𝕜] e) := borel (e →L[𝕜] e)
      Pairwise (fun i j => IndepFun (a i) (a j) μ))
    (hid : letI : MeasurableSpace (e →L[𝕜] e) := borel (e →L[𝕜] e)
      ∀ i, IdentDistrib (a i) (a 0) μ μ)
    (m : ℝ) (ha : ∀ i, ∀ᵐ ω ∂μ, ‖a i ω‖ ≤ m) :
    letI := NormedAlgebra.restrictScalars ℝ 𝕜 (e →L[𝕜] e)
    ∀ (x : e) (t : ℝ), 0 ≤ t → ∀ᵐ ω ∂μ,
      ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ s ∈ Set.Icc (0 : ℝ) t,
        ‖(randomProduct a n s ω -
          NormedSpace.exp (((s : ℝ) : 𝕜) • ∫ z, a 0 z ∂μ)) x‖ < ε := by
  have hd := @deterministic_uniform.{0}
  sorry

theorem result : claim := by
  intro 𝕜 e α _ _ _ _ _ μ _
  letI := NormedAlgebra.restrictScalars ℝ 𝕜 (e →L[𝕜] e)
  letI : MeasurableSpace (e →L[𝕜] e) := borel (e →L[𝕜] e)
  intro a hsm hind hid m ha
  exact operator_uniform_to_sot μ a hsm hind hid m ha

end D5.S3.Analytic.Probability.RandomExponentialProductSLLN
