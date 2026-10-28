/- GID: D5/S3/Combinatorics/Graph/LegalWords/SupportSizeCount
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/LegalWords/SupportSizeCount
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual nonadjacent support size fibers have a uniform binomial count. -/

import D5.S3.Combinatorics.Graph.LegalWords.EdgeCount

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.LegalWords.SupportSizeCount

open scoped BigOperators
open D5.S1.Words.AdmissibleWords.AdmissibleCount
open D5.S3.Quantum.FockSpace.ForbiddenNeighbourDeterminant
open D5.S3.Combinatorics.Graph.LegalWords.EdgeCount

/-- The cardinality of every actual occupation fiber, including empty fibers. -/
theorem support_count_eq_choose (n k : ℕ) :
    supportCount n k = Nat.choose ((n + 1) - k) k := by
  classical
  have hc (m j : ℕ) :
      (forbiddenPartition (fun _ : Fin m => (1 : ℝ))).coeff j =
        (supportCount m j : ℝ) := by
    simp only [forbiddenPartition, one_pow, Finset.prod_const_one, Polynomial.C_1,
      mul_one, Polynomial.finsetSum_coeff, Polynomial.coeff_X_pow]
    simp only [supportCount, Finset.card_eq_sum_ones, Finset.sum_filter, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro b _
    by_cases hb : occupationCount b.val = j
    · simp [hb]
    · simp [hb, Ne.symm hb]
  have hr (m : ℕ) :
      forbiddenPartition (fun _ : Fin (m + 2) => (1 : ℝ)) =
        forbiddenPartition (fun _ : Fin (m + 1) => (1 : ℝ)) +
          Polynomial.X * forbiddenPartition (fun _ : Fin m => (1 : ℝ)) := by
    simpa using
      (forbidden_neighbour_determinant (d := 1) (by decide)
        (fun _ => (1 : ℝ)) (by simp)).2.2.2.2.2.2.2.1 m (fun _ => 1)
  have hstep (m j : ℕ) :
      supportCount (m + 2) (j + 1) =
        supportCount (m + 1) (j + 1) + supportCount m j := by
    have h := congrArg (fun P : Polynomial ℝ => P.coeff (j + 1)) (hr m)
    simp only [Polynomial.coeff_add, Polynomial.coeff_X_mul] at h
    rw [hc, hc, hc] at h
    exact_mod_cast h
  have hzero (m : ℕ) : supportCount m 0 = 1 := by
    induction m using Nat.twoStepInduction with
    | zero => decide
    | one => decide
    | more m ih ih1 =>
      have h := congrArg (fun P : Polynomial ℝ => P.coeff 0) (hr m)
      simp only [Polynomial.coeff_add, Polynomial.coeff_X_mul_zero, add_zero] at h
      rw [hc, hc] at h
      exact_mod_cast h.trans (congrArg (fun a : ℕ => (a : ℝ)) ih1)
  induction n using Nat.twoStepInduction generalizing k with
  | zero =>
    cases k with
    | zero => simpa using hzero 0
    | succ k => simp [supportCount, occupationCount]
  | one =>
    cases k with
    | zero => simpa using hzero 1
    | succ k =>
      cases k with
      | zero => decide
      | succ k =>
        rw [Nat.choose_eq_zero_of_lt (by omega : 1 + 1 - (k + 1 + 1) < k + 1 + 1)]
        unfold supportCount
        apply Finset.card_eq_zero.mpr
        apply Finset.filter_eq_empty_iff.mpr
        intro b _ hb
        have h := (D5.S3.Combinatorics.Graph.LegalWordDegree.flippable_bound_and_equality 1 b).1
        omega
  | more n ih ih1 =>
    cases k with
    | zero => simpa using hzero (n + 2)
    | succ k =>
      rw [hstep, ih1, ih]
      by_cases hk : k ≤ n + 1
      · have he : n + 2 + 1 - (k + 1) = (n + 1 - k) + 1 := by omega
        have he1 : n + 1 + 1 - (k + 1) = n + 1 - k := by omega
        rw [he, he1, Nat.choose_succ_succ']
        omega
      · rw [Nat.choose_eq_zero_of_lt (by omega : n + 1 + 1 - (k + 1) < k + 1),
          Nat.choose_eq_zero_of_lt (by omega : n + 1 - k < k),
          Nat.choose_eq_zero_of_lt (by omega : n + 2 + 1 - (k + 1) < k + 1)]

#print axioms support_count_eq_choose
#check support_count_eq_choose

end D5.S3.Combinatorics.Graph.LegalWords.SupportSizeCount
