/- GID: D5/S3/Observer/LinearMemory/EpsilonSelfDimension
   generality: G
   mirror-B: D5/B/S3/Observer/LinearMemory/EpsilonSelfDimension
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Epsilon self-dimension is the count of singular values strictly above epsilon. -/

import Mathlib.Data.Nat.Find
import Mathlib.Order.Interval.Set.Nat
import Mathlib.Tactic

/- Library-search audit trail (2026-09-01):
   * Repository searches for `selfDimension`, `EckartYoung`, `lowRank`,
     `singularValue`, and the body shape "first threshold index equals prefix
     cardinality" found no equivalent D5 theorem. The adjacent
     `HankelGramianSingularValues` supplies singular-value semantics but not
     this order-theoretic threshold count.
   * Pinned Mathlib supplies `Nat.find_spec`, `Nat.find_min`, and
     `Set.ncard_Iio_nat`. Searches for `EckartYoung`, `Mirsky`, SVD, and best
     low-rank approximation found no Eckart-Young-Mirsky theorem.
   * The external `YuanheZ/lean-stat-learning-theory` release `v4.31.0`
     contains `Matrix.eckartYoungMirsky_hdp` and pins the same Mathlib rev,
     `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`. Spec A17's dependency
     admission predicates remain open, so the external theorem is represented
     below only by the explicit hypothesis `hEY`; it is neither recopied nor
     reproved. -/

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.LinearMemory.EpsilonSelfDimension

/-- Let `bestRankApproxError k` be the best error among approximants of rank at
most `k`. If the zero-indexed Eckart-Young value is `sigma k`, then the first
rank whose error is at most `epsilon` equals the number of singular values
strictly greater than `epsilon`.

The existence premise prevents the empty-threshold convention from silently
turning the minimum into zero. Under zero-based indexing, `sigma k` here is the
source's one-based `sigma_(k+1)`. -/
theorem epsilon_self_dimension_eq_threshold_count
    (sigma bestRankApproxError : ℕ → ℝ) (epsilon : ℝ)
    (hAnti : Antitone sigma)
    (_hNonneg : ∀ i, 0 ≤ sigma i)
    (hEventually : ∃ k, bestRankApproxError k ≤ epsilon)
    (hEY : ∀ k, bestRankApproxError k = sigma k) :
    Nat.find hEventually = Set.ncard {i | epsilon < sigma i} := by
  let d := Nat.find hEventually
  have hAt : sigma d ≤ epsilon := by
    rw [← hEY d]
    exact Nat.find_spec hEventually
  have hBefore (i : ℕ) (hi : i < d) : epsilon < sigma i := by
    have hNot : ¬bestRankApproxError i ≤ epsilon :=
      Nat.find_min hEventually hi
    rw [hEY i] at hNot
    exact lt_of_not_ge hNot
  have hPrefix : {i | epsilon < sigma i} = Set.Iio d := by
    ext i
    simp only [Set.mem_setOf_eq, Set.mem_Iio]
    constructor
    · intro hi
      by_contra hilt
      have hdle : d ≤ i := Nat.le_of_not_gt hilt
      have hle : sigma i ≤ epsilon := (hAnti hdle).trans hAt
      exact (not_lt_of_ge hle) hi
    · exact hBefore i
  rw [hPrefix, Set.ncard_Iio_nat]

/-- A concrete finite singular-value profile used to check indexing and all
threshold boundary conventions. -/
def sampleSingularValues (i : ℕ) : ℝ :=
  if i = 0 then 3 else if i = 1 then 2 else if i = 2 then 1 else 0

theorem sampleSingularValues_antitone : Antitone sampleSingularValues := by
  intro i j hij
  simp only [sampleSingularValues]
  split_ifs <;> norm_num <;> omega

theorem sampleSingularValues_nonneg (i : ℕ) : 0 ≤ sampleSingularValues i := by
  simp only [sampleSingularValues]
  split_ifs <;> norm_num

theorem sampleEventuallyThreeHalves :
    ∃ k, sampleSingularValues k ≤ (3 / 2 : ℝ) :=
  ⟨2, by norm_num [sampleSingularValues]⟩

/-- At `epsilon = 3/2`, exactly `3` and `2` lie strictly above the threshold,
and the first acceptable rank is zero-based index `2`. -/
theorem sample_epsilon_three_halves :
    Nat.find sampleEventuallyThreeHalves = 2 ∧
      Set.ncard {i | (3 / 2 : ℝ) < sampleSingularValues i} = 2 := by
  have hFind : Nat.find sampleEventuallyThreeHalves = 2 :=
    (Nat.find_eq_iff sampleEventuallyThreeHalves).2 ⟨by
      norm_num [sampleSingularValues], by
      intro n hn
      interval_cases n <;> norm_num [sampleSingularValues]⟩
  have hCount := epsilon_self_dimension_eq_threshold_count
    sampleSingularValues sampleSingularValues (3 / 2 : ℝ)
    sampleSingularValues_antitone sampleSingularValues_nonneg
    sampleEventuallyThreeHalves (fun _ ↦ rfl)
  exact ⟨hFind, by rw [← hCount, hFind]⟩

theorem sampleEventuallyTwo : ∃ k, sampleSingularValues k ≤ (2 : ℝ) :=
  ⟨1, by norm_num [sampleSingularValues]⟩

/-- Equality with a singular value is accepted by `≤` and excluded by the
strict count: at `epsilon = 2`, both sides are `1`. -/
theorem sample_epsilon_two :
    Nat.find sampleEventuallyTwo = 1 ∧
      Set.ncard {i | (2 : ℝ) < sampleSingularValues i} = 1 := by
  have hFind : Nat.find sampleEventuallyTwo = 1 :=
    (Nat.find_eq_iff sampleEventuallyTwo).2 ⟨by
      norm_num [sampleSingularValues], by
      intro n hn
      interval_cases n
      norm_num [sampleSingularValues]⟩
  have hCount := epsilon_self_dimension_eq_threshold_count
    sampleSingularValues sampleSingularValues (2 : ℝ)
    sampleSingularValues_antitone sampleSingularValues_nonneg
    sampleEventuallyTwo (fun _ ↦ rfl)
  exact ⟨hFind, by rw [← hCount, hFind]⟩

theorem sampleEventuallyZero : ∃ k, sampleSingularValues k ≤ (0 : ℝ) :=
  ⟨3, by norm_num [sampleSingularValues]⟩

/-- At the lower extreme `epsilon = 0`, the three positive values are counted
and the first zero is at index `3`. -/
theorem sample_epsilon_zero :
    Nat.find sampleEventuallyZero = 3 ∧
      Set.ncard {i | (0 : ℝ) < sampleSingularValues i} = 3 := by
  have hFind : Nat.find sampleEventuallyZero = 3 :=
    (Nat.find_eq_iff sampleEventuallyZero).2 ⟨by
      norm_num [sampleSingularValues], by
      intro n hn
      interval_cases n <;> norm_num [sampleSingularValues]⟩
  have hCount := epsilon_self_dimension_eq_threshold_count
    sampleSingularValues sampleSingularValues (0 : ℝ)
    sampleSingularValues_antitone sampleSingularValues_nonneg
    sampleEventuallyZero (fun _ ↦ rfl)
  exact ⟨hFind, by rw [← hCount, hFind]⟩

theorem sampleEventuallyFour : ∃ k, sampleSingularValues k ≤ (4 : ℝ) :=
  ⟨0, by norm_num [sampleSingularValues]⟩

/-- Above the entire profile, the strict count and the first acceptable rank
are both zero. -/
theorem sample_epsilon_four :
    Nat.find sampleEventuallyFour = 0 ∧
      Set.ncard {i | (4 : ℝ) < sampleSingularValues i} = 0 := by
  have hFind : Nat.find sampleEventuallyFour = 0 :=
    (Nat.find_eq_iff sampleEventuallyFour).2 ⟨by
      norm_num [sampleSingularValues], by
      intro n hn
      omega⟩
  have hCount := epsilon_self_dimension_eq_threshold_count
    sampleSingularValues sampleSingularValues (4 : ℝ)
    sampleSingularValues_antitone sampleSingularValues_nonneg
    sampleEventuallyFour (fun _ ↦ rfl)
  exact ⟨hFind, by rw [← hCount, hFind]⟩

#print axioms epsilon_self_dimension_eq_threshold_count
#print axioms sample_epsilon_three_halves
#print axioms sample_epsilon_two
#print axioms sample_epsilon_zero
#print axioms sample_epsilon_four

end D5.S3.Observer.LinearMemory.EpsilonSelfDimension
