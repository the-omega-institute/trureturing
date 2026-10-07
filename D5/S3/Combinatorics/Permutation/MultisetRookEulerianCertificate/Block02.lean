/- GID: D5/S3/Combinatorics/Permutation/MultisetRookEulerianCertificate/Block02
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Permutation/MultisetRookEulerianCertificate/Block02
   mirror-E: none(waiver:exact-finite-certificate)
   anchors: []
   utility: none
   digest: Exact residual-content certificates dag_0064 through dag_0092. -/

import D5.S3.Combinatorics.Permutation.MultisetRookEulerianWordRecurrence
import D5.S3.Combinatorics.Permutation.MultisetRookEulerianCertificate.Block01

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace D5.S3.Combinatorics.Permutation.MultisetRookEulerianCertificate.Block02

open Polynomial
open D5.S3.Combinatorics.Permutation.MultisetRookEulerianWordRecurrence

theorem dag_0064 :
    dp [6, 6, 6, 6, 6, 6] [6, 6, 6, 6, 6, 6] (some 4) =
      (X : ℝ[X]) := by
  have erase_0 : ([6, 6, 6, 6, 6, 6] : List ℕ).erase 6 = [6, 6, 6, 6, 6] := by decide
  have hallowed : ([6, 6, 6, 6, 6, 6] : List ℕ).toFinset.filter (fun a => 0 < a ∧ a ≤ 6) = ([6] : List ℕ).toFinset := by decide
  let coefficients : ℕ → ℝ[X] := fun a => if a = 6 then (1 : ℝ[X]) else 0
  have hchildren : ∀ a ∈ ([6] : List ℕ).toFinset,
      dp [6, 6, 6, 6, 6] ([6, 6, 6, 6, 6, 6].erase a) (some a) = coefficients a := by
    intro a ha
    have hcases : a = 6 := by simpa using ha
    rcases hcases with rfl
    · change dp [6, 6, 6, 6, 6] ([6, 6, 6, 6, 6, 6].erase 6) (some 6) = (1 : ℝ[X])
      rw [erase_0]
      exact D5.S3.Combinatorics.Permutation.MultisetRookEulerianCertificate.Block01.dag_0055
  rw [dp_cons_eq_sum_of_children 6 [6, 6, 6, 6, 6] [6, 6, 6, 6, 6, 6] (some 4) ([6] : List ℕ).toFinset coefficients hallowed hchildren]
  norm_num [coefficients, List.toFinset_cons, List.toFinset_nil, Finset.sum_insert, Finset.sum_empty, beq_iff_eq]
  <;> ring

theorem dag_0065 :
    dp [6, 6, 6, 6, 6, 6] [6, 6, 6, 6, 6, 6] (some 5) =
      (X : ℝ[X]) := by
  have erase_0 : ([6, 6, 6, 6, 6, 6] : List ℕ).erase 6 = [6, 6, 6, 6, 6] := by decide
  have hallowed : ([6, 6, 6, 6, 6, 6] : List ℕ).toFinset.filter (fun a => 0 < a ∧ a ≤ 6) = ([6] : List ℕ).toFinset := by decide
  let coefficients : ℕ → ℝ[X] := fun a => if a = 6 then (1 : ℝ[X]) else 0
  have hchildren : ∀ a ∈ ([6] : List ℕ).toFinset,
      dp [6, 6, 6, 6, 6] ([6, 6, 6, 6, 6, 6].erase a) (some a) = coefficients a := by
    intro a ha
    have hcases : a = 6 := by simpa using ha
    rcases hcases with rfl
    · change dp [6, 6, 6, 6, 6] ([6, 6, 6, 6, 6, 6].erase 6) (some 6) = (1 : ℝ[X])
      rw [erase_0]
      exact D5.S3.Combinatorics.Permutation.MultisetRookEulerianCertificate.Block01.dag_0055
  rw [dp_cons_eq_sum_of_children 6 [6, 6, 6, 6, 6] [6, 6, 6, 6, 6, 6] (some 5) ([6] : List ℕ).toFinset coefficients hallowed hchildren]
  norm_num [coefficients, List.toFinset_cons, List.toFinset_nil, Finset.sum_insert, Finset.sum_empty, beq_iff_eq]
  <;> ring

theorem dag_0066 :
    dp [6, 6, 6, 6, 6, 6] [6, 6, 6, 6, 6, 6] (some 6) =
      (1 : ℝ[X]) := by
  have erase_0 : ([6, 6, 6, 6, 6, 6] : List ℕ).erase 6 = [6, 6, 6, 6, 6] := by decide
  have hallowed : ([6, 6, 6, 6, 6, 6] : List ℕ).toFinset.filter (fun a => 0 < a ∧ a ≤ 6) = ([6] : List ℕ).toFinset := by decide
  let coefficients : ℕ → ℝ[X] := fun a => if a = 6 then (1 : ℝ[X]) else 0
  have hchildren : ∀ a ∈ ([6] : List ℕ).toFinset,
      dp [6, 6, 6, 6, 6] ([6, 6, 6, 6, 6, 6].erase a) (some a) = coefficients a := by
    intro a ha
    have hcases : a = 6 := by simpa using ha
    rcases hcases with rfl
    · change dp [6, 6, 6, 6, 6] ([6, 6, 6, 6, 6, 6].erase 6) (some 6) = (1 : ℝ[X])
      rw [erase_0]
      exact D5.S3.Combinatorics.Permutation.MultisetRookEulerianCertificate.Block01.dag_0055
  rw [dp_cons_eq_sum_of_children 6 [6, 6, 6, 6, 6] [6, 6, 6, 6, 6, 6] (some 6) ([6] : List ℕ).toFinset coefficients hallowed hchildren]
  norm_num [coefficients, List.toFinset_cons, List.toFinset_nil, Finset.sum_insert, Finset.sum_empty, beq_iff_eq]
  <;> ring

theorem dag_0067 :
    dp [6, 6, 6, 6, 6, 6] [5, 6, 6, 6, 6, 6] (some 6) =
      (1 + 5 * X : ℝ[X]) := by
  have erase_0 : ([5, 6, 6, 6, 6, 6] : List ℕ).erase 5 = [6, 6, 6, 6, 6] := by decide
  have erase_1 : ([5, 6, 6, 6, 6, 6] : List ℕ).erase 6 = [5, 6, 6, 6, 6] := by decide
  have hallowed : ([5, 6, 6, 6, 6, 6] : List ℕ).toFinset.filter (fun a => 0 < a ∧ a ≤ 6) = ([5, 6] : List ℕ).toFinset := by decide
  let coefficients : ℕ → ℝ[X] := fun a => if a = 5 then (X : ℝ[X]) else if a = 6 then (1 + 4 * X : ℝ[X]) else 0
  have hchildren : ∀ a ∈ ([5, 6] : List ℕ).toFinset,
      dp [6, 6, 6, 6, 6] ([5, 6, 6, 6, 6, 6].erase a) (some a) = coefficients a := by
    intro a ha
    have hcases : a = 5 ∨ a = 6 := by simpa using ha
    rcases hcases with rfl | rfl
    · change dp [6, 6, 6, 6, 6] ([5, 6, 6, 6, 6, 6].erase 5) (some 5) = (X : ℝ[X])
      rw [erase_0]
      exact D5.S3.Combinatorics.Permutation.MultisetRookEulerianCertificate.Block01.dag_0054
    · change dp [6, 6, 6, 6, 6] ([5, 6, 6, 6, 6, 6].erase 6) (some 6) = (1 + 4 * X : ℝ[X])
      rw [erase_1]
      exact D5.S3.Combinatorics.Permutation.MultisetRookEulerianCertificate.Block01.dag_0056
  rw [dp_cons_eq_sum_of_children 6 [6, 6, 6, 6, 6] [5, 6, 6, 6, 6, 6] (some 6) ([5, 6] : List ℕ).toFinset coefficients hallowed hchildren]
  norm_num [coefficients, List.toFinset_cons, List.toFinset_nil, Finset.sum_insert, Finset.sum_empty, beq_iff_eq]
  <;> ring

theorem dag_0068 :
    dp [6, 6, 6, 6, 6, 6] [4, 6, 6, 6, 6, 6] (some 6) =
      (1 + 5 * X : ℝ[X]) := by
  have erase_0 : ([4, 6, 6, 6, 6, 6] : List ℕ).erase 4 = [6, 6, 6, 6, 6] := by decide
  have erase_1 : ([4, 6, 6, 6, 6, 6] : List ℕ).erase 6 = [4, 6, 6, 6, 6] := by decide
  have hallowed : ([4, 6, 6, 6, 6, 6] : List ℕ).toFinset.filter (fun a => 0 < a ∧ a ≤ 6) = ([4, 6] : List ℕ).toFinset := by decide
  let coefficients : ℕ → ℝ[X] := fun a => if a = 4 then (X : ℝ[X]) else if a = 6 then (1 + 4 * X : ℝ[X]) else 0
  have hchildren : ∀ a ∈ ([4, 6] : List ℕ).toFinset,
      dp [6, 6, 6, 6, 6] ([4, 6, 6, 6, 6, 6].erase a) (some a) = coefficients a := by
    intro a ha
    have hcases : a = 4 ∨ a = 6 := by simpa using ha
    rcases hcases with rfl | rfl
    · change dp [6, 6, 6, 6, 6] ([4, 6, 6, 6, 6, 6].erase 4) (some 4) = (X : ℝ[X])
      rw [erase_0]
      exact D5.S3.Combinatorics.Permutation.MultisetRookEulerianCertificate.Block01.dag_0053
    · change dp [6, 6, 6, 6, 6] ([4, 6, 6, 6, 6, 6].erase 6) (some 6) = (1 + 4 * X : ℝ[X])
      rw [erase_1]
      exact D5.S3.Combinatorics.Permutation.MultisetRookEulerianCertificate.Block01.dag_0057
  rw [dp_cons_eq_sum_of_children 6 [6, 6, 6, 6, 6] [4, 6, 6, 6, 6, 6] (some 6) ([4, 6] : List ℕ).toFinset coefficients hallowed hchildren]
  norm_num [coefficients, List.toFinset_cons, List.toFinset_nil, Finset.sum_insert, Finset.sum_empty, beq_iff_eq]
  <;> ring

theorem dag_0069 :
    dp [6, 6, 6, 6, 6, 6] [3, 6, 6, 6, 6, 6] (some 6) =
      (1 + 5 * X : ℝ[X]) := by
  have erase_0 : ([3, 6, 6, 6, 6, 6] : List ℕ).erase 3 = [6, 6, 6, 6, 6] := by decide
  have erase_1 : ([3, 6, 6, 6, 6, 6] : List ℕ).erase 6 = [3, 6, 6, 6, 6] := by decide
  have hallowed : ([3, 6, 6, 6, 6, 6] : List ℕ).toFinset.filter (fun a => 0 < a ∧ a ≤ 6) = ([3, 6] : List ℕ).toFinset := by decide
  let coefficients : ℕ → ℝ[X] := fun a => if a = 3 then (X : ℝ[X]) else if a = 6 then (1 + 4 * X : ℝ[X]) else 0
  have hchildren : ∀ a ∈ ([3, 6] : List ℕ).toFinset,
      dp [6, 6, 6, 6, 6] ([3, 6, 6, 6, 6, 6].erase a) (some a) = coefficients a := by
    intro a ha
    have hcases : a = 3 ∨ a = 6 := by simpa using ha
    rcases hcases with rfl | rfl
    · change dp [6, 6, 6, 6, 6] ([3, 6, 6, 6, 6, 6].erase 3) (some 3) = (X : ℝ[X])
      rw [erase_0]
      exact D5.S3.Combinatorics.Permutation.MultisetRookEulerianCertificate.Block01.dag_0052
    · change dp [6, 6, 6, 6, 6] ([3, 6, 6, 6, 6, 6].erase 6) (some 6) = (1 + 4 * X : ℝ[X])
      rw [erase_1]
      exact D5.S3.Combinatorics.Permutation.MultisetRookEulerianCertificate.Block01.dag_0058
  rw [dp_cons_eq_sum_of_children 6 [6, 6, 6, 6, 6] [3, 6, 6, 6, 6, 6] (some 6) ([3, 6] : List ℕ).toFinset coefficients hallowed hchildren]
  norm_num [coefficients, List.toFinset_cons, List.toFinset_nil, Finset.sum_insert, Finset.sum_empty, beq_iff_eq]
  <;> ring

theorem dag_0070 :
    dp [6, 6, 6, 6, 6, 6] [2, 6, 6, 6, 6, 6] (some 6) =
      (1 + 5 * X : ℝ[X]) := by
  have erase_0 : ([2, 6, 6, 6, 6, 6] : List ℕ).erase 2 = [6, 6, 6, 6, 6] := by decide
  have erase_1 : ([2, 6, 6, 6, 6, 6] : List ℕ).erase 6 = [2, 6, 6, 6, 6] := by decide
  have hallowed : ([2, 6, 6, 6, 6, 6] : List ℕ).toFinset.filter (fun a => 0 < a ∧ a ≤ 6) = ([2, 6] : List ℕ).toFinset := by decide
  let coefficients : ℕ → ℝ[X] := fun a => if a = 2 then (X : ℝ[X]) else if a = 6 then (1 + 4 * X : ℝ[X]) else 0
  have hchildren : ∀ a ∈ ([2, 6] : List ℕ).toFinset,
      dp [6, 6, 6, 6, 6] ([2, 6, 6, 6, 6, 6].erase a) (some a) = coefficients a := by
    intro a ha
    have hcases : a = 2 ∨ a = 6 := by simpa using ha
    rcases hcases with rfl | rfl
    · change dp [6, 6, 6, 6, 6] ([2, 6, 6, 6, 6, 6].erase 2) (some 2) = (X : ℝ[X])
      rw [erase_0]
      exact D5.S3.Combinatorics.Permutation.MultisetRookEulerianCertificate.Block01.dag_0051
    · change dp [6, 6, 6, 6, 6] ([2, 6, 6, 6, 6, 6].erase 6) (some 6) = (1 + 4 * X : ℝ[X])
      rw [erase_1]
      exact D5.S3.Combinatorics.Permutation.MultisetRookEulerianCertificate.Block01.dag_0059
  rw [dp_cons_eq_sum_of_children 6 [6, 6, 6, 6, 6] [2, 6, 6, 6, 6, 6] (some 6) ([2, 6] : List ℕ).toFinset coefficients hallowed hchildren]
  norm_num [coefficients, List.toFinset_cons, List.toFinset_nil, Finset.sum_insert, Finset.sum_empty, beq_iff_eq]
  <;> ring

theorem dag_0071 :
    dp [6, 6, 6, 6, 6, 6] [1, 6, 6, 6, 6, 6] (some 6) =
      (1 + 5 * X : ℝ[X]) := by
  have erase_0 : ([1, 6, 6, 6, 6, 6] : List ℕ).erase 1 = [6, 6, 6, 6, 6] := by decide
  have erase_1 : ([1, 6, 6, 6, 6, 6] : List ℕ).erase 6 = [1, 6, 6, 6, 6] := by decide
  have hallowed : ([1, 6, 6, 6, 6, 6] : List ℕ).toFinset.filter (fun a => 0 < a ∧ a ≤ 6) = ([1, 6] : List ℕ).toFinset := by decide
  let coefficients : ℕ → ℝ[X] := fun a => if a = 1 then (X : ℝ[X]) else if a = 6 then (1 + 4 * X : ℝ[X]) else 0
  have hchildren : ∀ a ∈ ([1, 6] : List ℕ).toFinset,
      dp [6, 6, 6, 6, 6] ([1, 6, 6, 6, 6, 6].erase a) (some a) = coefficients a := by
    intro a ha
    have hcases : a = 1 ∨ a = 6 := by simpa using ha
    rcases hcases with rfl | rfl
    · change dp [6, 6, 6, 6, 6] ([1, 6, 6, 6, 6, 6].erase 1) (some 1) = (X : ℝ[X])
      rw [erase_0]
      exact D5.S3.Combinatorics.Permutation.MultisetRookEulerianCertificate.Block01.dag_0050
    · change dp [6, 6, 6, 6, 6] ([1, 6, 6, 6, 6, 6].erase 6) (some 6) = (1 + 4 * X : ℝ[X])
      rw [erase_1]
      exact D5.S3.Combinatorics.Permutation.MultisetRookEulerianCertificate.Block01.dag_0060
  rw [dp_cons_eq_sum_of_children 6 [6, 6, 6, 6, 6] [1, 6, 6, 6, 6, 6] (some 6) ([1, 6] : List ℕ).toFinset coefficients hallowed hchildren]
  norm_num [coefficients, List.toFinset_cons, List.toFinset_nil, Finset.sum_insert, Finset.sum_empty, beq_iff_eq]
  <;> ring

theorem dag_0072 :
    dp [6, 6, 6, 6, 6, 6, 6] [6, 6, 6, 6, 6, 6, 6] (some 1) =
      (X : ℝ[X]) := by
  have erase_0 : ([6, 6, 6, 6, 6, 6, 6] : List ℕ).erase 6 = [6, 6, 6, 6, 6, 6] := by decide
  have hallowed : ([6, 6, 6, 6, 6, 6, 6] : List ℕ).toFinset.filter (fun a => 0 < a ∧ a ≤ 6) = ([6] : List ℕ).toFinset := by decide
  let coefficients : ℕ → ℝ[X] := fun a => if a = 6 then (1 : ℝ[X]) else 0
  have hchildren : ∀ a ∈ ([6] : List ℕ).toFinset,
      dp [6, 6, 6, 6, 6, 6] ([6, 6, 6, 6, 6, 6, 6].erase a) (some a) = coefficients a := by
    intro a ha
    have hcases : a = 6 := by simpa using ha
    rcases hcases with rfl
    · change dp [6, 6, 6, 6, 6, 6] ([6, 6, 6, 6, 6, 6, 6].erase 6) (some 6) = (1 : ℝ[X])
      rw [erase_0]
      exact dag_0066
  rw [dp_cons_eq_sum_of_children 6 [6, 6, 6, 6, 6, 6] [6, 6, 6, 6, 6, 6, 6] (some 1) ([6] : List ℕ).toFinset coefficients hallowed hchildren]
  norm_num [coefficients, List.toFinset_cons, List.toFinset_nil, Finset.sum_insert, Finset.sum_empty, beq_iff_eq]
  <;> ring

theorem dag_0073 :
    dp [6, 6, 6, 6, 6, 6, 6] [6, 6, 6, 6, 6, 6, 6] (some 2) =
      (X : ℝ[X]) := by
  have erase_0 : ([6, 6, 6, 6, 6, 6, 6] : List ℕ).erase 6 = [6, 6, 6, 6, 6, 6] := by decide
  have hallowed : ([6, 6, 6, 6, 6, 6, 6] : List ℕ).toFinset.filter (fun a => 0 < a ∧ a ≤ 6) = ([6] : List ℕ).toFinset := by decide
  let coefficients : ℕ → ℝ[X] := fun a => if a = 6 then (1 : ℝ[X]) else 0
  have hchildren : ∀ a ∈ ([6] : List ℕ).toFinset,
      dp [6, 6, 6, 6, 6, 6] ([6, 6, 6, 6, 6, 6, 6].erase a) (some a) = coefficients a := by
    intro a ha
    have hcases : a = 6 := by simpa using ha
    rcases hcases with rfl
    · change dp [6, 6, 6, 6, 6, 6] ([6, 6, 6, 6, 6, 6, 6].erase 6) (some 6) = (1 : ℝ[X])
      rw [erase_0]
      exact dag_0066
  rw [dp_cons_eq_sum_of_children 6 [6, 6, 6, 6, 6, 6] [6, 6, 6, 6, 6, 6, 6] (some 2) ([6] : List ℕ).toFinset coefficients hallowed hchildren]
  norm_num [coefficients, List.toFinset_cons, List.toFinset_nil, Finset.sum_insert, Finset.sum_empty, beq_iff_eq]
  <;> ring

theorem dag_0074 :
    dp [6, 6, 6, 6, 6, 6, 6] [6, 6, 6, 6, 6, 6, 6] (some 3) =
      (X : ℝ[X]) := by
  have erase_0 : ([6, 6, 6, 6, 6, 6, 6] : List ℕ).erase 6 = [6, 6, 6, 6, 6, 6] := by decide
  have hallowed : ([6, 6, 6, 6, 6, 6, 6] : List ℕ).toFinset.filter (fun a => 0 < a ∧ a ≤ 6) = ([6] : List ℕ).toFinset := by decide
  let coefficients : ℕ → ℝ[X] := fun a => if a = 6 then (1 : ℝ[X]) else 0
  have hchildren : ∀ a ∈ ([6] : List ℕ).toFinset,
      dp [6, 6, 6, 6, 6, 6] ([6, 6, 6, 6, 6, 6, 6].erase a) (some a) = coefficients a := by
    intro a ha
    have hcases : a = 6 := by simpa using ha
    rcases hcases with rfl
    · change dp [6, 6, 6, 6, 6, 6] ([6, 6, 6, 6, 6, 6, 6].erase 6) (some 6) = (1 : ℝ[X])
      rw [erase_0]
      exact dag_0066
  rw [dp_cons_eq_sum_of_children 6 [6, 6, 6, 6, 6, 6] [6, 6, 6, 6, 6, 6, 6] (some 3) ([6] : List ℕ).toFinset coefficients hallowed hchildren]
  norm_num [coefficients, List.toFinset_cons, List.toFinset_nil, Finset.sum_insert, Finset.sum_empty, beq_iff_eq]
  <;> ring

theorem dag_0075 :
    dp [6, 6, 6, 6, 6, 6, 6] [6, 6, 6, 6, 6, 6, 6] (some 4) =
      (X : ℝ[X]) := by
  have erase_0 : ([6, 6, 6, 6, 6, 6, 6] : List ℕ).erase 6 = [6, 6, 6, 6, 6, 6] := by decide
  have hallowed : ([6, 6, 6, 6, 6, 6, 6] : List ℕ).toFinset.filter (fun a => 0 < a ∧ a ≤ 6) = ([6] : List ℕ).toFinset := by decide
  let coefficients : ℕ → ℝ[X] := fun a => if a = 6 then (1 : ℝ[X]) else 0
  have hchildren : ∀ a ∈ ([6] : List ℕ).toFinset,
      dp [6, 6, 6, 6, 6, 6] ([6, 6, 6, 6, 6, 6, 6].erase a) (some a) = coefficients a := by
    intro a ha
    have hcases : a = 6 := by simpa using ha
    rcases hcases with rfl
    · change dp [6, 6, 6, 6, 6, 6] ([6, 6, 6, 6, 6, 6, 6].erase 6) (some 6) = (1 : ℝ[X])
      rw [erase_0]
      exact dag_0066
  rw [dp_cons_eq_sum_of_children 6 [6, 6, 6, 6, 6, 6] [6, 6, 6, 6, 6, 6, 6] (some 4) ([6] : List ℕ).toFinset coefficients hallowed hchildren]
  norm_num [coefficients, List.toFinset_cons, List.toFinset_nil, Finset.sum_insert, Finset.sum_empty, beq_iff_eq]
  <;> ring

theorem dag_0076 :
    dp [6, 6, 6, 6, 6, 6, 6] [6, 6, 6, 6, 6, 6, 6] (some 5) =
      (X : ℝ[X]) := by
  have erase_0 : ([6, 6, 6, 6, 6, 6, 6] : List ℕ).erase 6 = [6, 6, 6, 6, 6, 6] := by decide
  have hallowed : ([6, 6, 6, 6, 6, 6, 6] : List ℕ).toFinset.filter (fun a => 0 < a ∧ a ≤ 6) = ([6] : List ℕ).toFinset := by decide
  let coefficients : ℕ → ℝ[X] := fun a => if a = 6 then (1 : ℝ[X]) else 0
  have hchildren : ∀ a ∈ ([6] : List ℕ).toFinset,
      dp [6, 6, 6, 6, 6, 6] ([6, 6, 6, 6, 6, 6, 6].erase a) (some a) = coefficients a := by
    intro a ha
    have hcases : a = 6 := by simpa using ha
    rcases hcases with rfl
    · change dp [6, 6, 6, 6, 6, 6] ([6, 6, 6, 6, 6, 6, 6].erase 6) (some 6) = (1 : ℝ[X])
      rw [erase_0]
      exact dag_0066
  rw [dp_cons_eq_sum_of_children 6 [6, 6, 6, 6, 6, 6] [6, 6, 6, 6, 6, 6, 6] (some 5) ([6] : List ℕ).toFinset coefficients hallowed hchildren]
  norm_num [coefficients, List.toFinset_cons, List.toFinset_nil, Finset.sum_insert, Finset.sum_empty, beq_iff_eq]
  <;> ring

theorem dag_0077 :
    dp [6, 6, 6, 6, 6, 6, 6] [6, 6, 6, 6, 6, 6, 6] (some 6) =
      (1 : ℝ[X]) := by
  have erase_0 : ([6, 6, 6, 6, 6, 6, 6] : List ℕ).erase 6 = [6, 6, 6, 6, 6, 6] := by decide
  have hallowed : ([6, 6, 6, 6, 6, 6, 6] : List ℕ).toFinset.filter (fun a => 0 < a ∧ a ≤ 6) = ([6] : List ℕ).toFinset := by decide
  let coefficients : ℕ → ℝ[X] := fun a => if a = 6 then (1 : ℝ[X]) else 0
  have hchildren : ∀ a ∈ ([6] : List ℕ).toFinset,
      dp [6, 6, 6, 6, 6, 6] ([6, 6, 6, 6, 6, 6, 6].erase a) (some a) = coefficients a := by
    intro a ha
    have hcases : a = 6 := by simpa using ha
    rcases hcases with rfl
    · change dp [6, 6, 6, 6, 6, 6] ([6, 6, 6, 6, 6, 6, 6].erase 6) (some 6) = (1 : ℝ[X])
      rw [erase_0]
      exact dag_0066
  rw [dp_cons_eq_sum_of_children 6 [6, 6, 6, 6, 6, 6] [6, 6, 6, 6, 6, 6, 6] (some 6) ([6] : List ℕ).toFinset coefficients hallowed hchildren]
  norm_num [coefficients, List.toFinset_cons, List.toFinset_nil, Finset.sum_insert, Finset.sum_empty, beq_iff_eq]
  <;> ring

theorem dag_0078 :
    dp [6, 6, 6, 6, 6, 6, 6] [5, 6, 6, 6, 6, 6, 6] (some 6) =
      (1 + 6 * X : ℝ[X]) := by
  have erase_0 : ([5, 6, 6, 6, 6, 6, 6] : List ℕ).erase 5 = [6, 6, 6, 6, 6, 6] := by decide
  have erase_1 : ([5, 6, 6, 6, 6, 6, 6] : List ℕ).erase 6 = [5, 6, 6, 6, 6, 6] := by decide
  have hallowed : ([5, 6, 6, 6, 6, 6, 6] : List ℕ).toFinset.filter (fun a => 0 < a ∧ a ≤ 6) = ([5, 6] : List ℕ).toFinset := by decide
  let coefficients : ℕ → ℝ[X] := fun a => if a = 5 then (X : ℝ[X]) else if a = 6 then (1 + 5 * X : ℝ[X]) else 0
  have hchildren : ∀ a ∈ ([5, 6] : List ℕ).toFinset,
      dp [6, 6, 6, 6, 6, 6] ([5, 6, 6, 6, 6, 6, 6].erase a) (some a) = coefficients a := by
    intro a ha
    have hcases : a = 5 ∨ a = 6 := by simpa using ha
    rcases hcases with rfl | rfl
    · change dp [6, 6, 6, 6, 6, 6] ([5, 6, 6, 6, 6, 6, 6].erase 5) (some 5) = (X : ℝ[X])
      rw [erase_0]
      exact dag_0065
    · change dp [6, 6, 6, 6, 6, 6] ([5, 6, 6, 6, 6, 6, 6].erase 6) (some 6) = (1 + 5 * X : ℝ[X])
      rw [erase_1]
      exact dag_0067
  rw [dp_cons_eq_sum_of_children 6 [6, 6, 6, 6, 6, 6] [5, 6, 6, 6, 6, 6, 6] (some 6) ([5, 6] : List ℕ).toFinset coefficients hallowed hchildren]
  norm_num [coefficients, List.toFinset_cons, List.toFinset_nil, Finset.sum_insert, Finset.sum_empty, beq_iff_eq]
  <;> ring

theorem dag_0079 :
    dp [6, 6, 6, 6, 6, 6, 6] [4, 6, 6, 6, 6, 6, 6] (some 6) =
      (1 + 6 * X : ℝ[X]) := by
  have erase_0 : ([4, 6, 6, 6, 6, 6, 6] : List ℕ).erase 4 = [6, 6, 6, 6, 6, 6] := by decide
  have erase_1 : ([4, 6, 6, 6, 6, 6, 6] : List ℕ).erase 6 = [4, 6, 6, 6, 6, 6] := by decide
  have hallowed : ([4, 6, 6, 6, 6, 6, 6] : List ℕ).toFinset.filter (fun a => 0 < a ∧ a ≤ 6) = ([4, 6] : List ℕ).toFinset := by decide
  let coefficients : ℕ → ℝ[X] := fun a => if a = 4 then (X : ℝ[X]) else if a = 6 then (1 + 5 * X : ℝ[X]) else 0
  have hchildren : ∀ a ∈ ([4, 6] : List ℕ).toFinset,
      dp [6, 6, 6, 6, 6, 6] ([4, 6, 6, 6, 6, 6, 6].erase a) (some a) = coefficients a := by
    intro a ha
    have hcases : a = 4 ∨ a = 6 := by simpa using ha
    rcases hcases with rfl | rfl
    · change dp [6, 6, 6, 6, 6, 6] ([4, 6, 6, 6, 6, 6, 6].erase 4) (some 4) = (X : ℝ[X])
      rw [erase_0]
      exact dag_0064
    · change dp [6, 6, 6, 6, 6, 6] ([4, 6, 6, 6, 6, 6, 6].erase 6) (some 6) = (1 + 5 * X : ℝ[X])
      rw [erase_1]
      exact dag_0068
  rw [dp_cons_eq_sum_of_children 6 [6, 6, 6, 6, 6, 6] [4, 6, 6, 6, 6, 6, 6] (some 6) ([4, 6] : List ℕ).toFinset coefficients hallowed hchildren]
  norm_num [coefficients, List.toFinset_cons, List.toFinset_nil, Finset.sum_insert, Finset.sum_empty, beq_iff_eq]
  <;> ring

theorem dag_0080 :
    dp [6, 6, 6, 6, 6, 6, 6] [3, 6, 6, 6, 6, 6, 6] (some 6) =
      (1 + 6 * X : ℝ[X]) := by
  have erase_0 : ([3, 6, 6, 6, 6, 6, 6] : List ℕ).erase 3 = [6, 6, 6, 6, 6, 6] := by decide
  have erase_1 : ([3, 6, 6, 6, 6, 6, 6] : List ℕ).erase 6 = [3, 6, 6, 6, 6, 6] := by decide
  have hallowed : ([3, 6, 6, 6, 6, 6, 6] : List ℕ).toFinset.filter (fun a => 0 < a ∧ a ≤ 6) = ([3, 6] : List ℕ).toFinset := by decide
  let coefficients : ℕ → ℝ[X] := fun a => if a = 3 then (X : ℝ[X]) else if a = 6 then (1 + 5 * X : ℝ[X]) else 0
  have hchildren : ∀ a ∈ ([3, 6] : List ℕ).toFinset,
      dp [6, 6, 6, 6, 6, 6] ([3, 6, 6, 6, 6, 6, 6].erase a) (some a) = coefficients a := by
    intro a ha
    have hcases : a = 3 ∨ a = 6 := by simpa using ha
    rcases hcases with rfl | rfl
    · change dp [6, 6, 6, 6, 6, 6] ([3, 6, 6, 6, 6, 6, 6].erase 3) (some 3) = (X : ℝ[X])
      rw [erase_0]
      exact D5.S3.Combinatorics.Permutation.MultisetRookEulerianCertificate.Block01.dag_0063
    · change dp [6, 6, 6, 6, 6, 6] ([3, 6, 6, 6, 6, 6, 6].erase 6) (some 6) = (1 + 5 * X : ℝ[X])
      rw [erase_1]
      exact dag_0069
  rw [dp_cons_eq_sum_of_children 6 [6, 6, 6, 6, 6, 6] [3, 6, 6, 6, 6, 6, 6] (some 6) ([3, 6] : List ℕ).toFinset coefficients hallowed hchildren]
  norm_num [coefficients, List.toFinset_cons, List.toFinset_nil, Finset.sum_insert, Finset.sum_empty, beq_iff_eq]
  <;> ring

theorem dag_0081 :
    dp [6, 6, 6, 6, 6, 6, 6] [2, 6, 6, 6, 6, 6, 6] (some 6) =
      (1 + 6 * X : ℝ[X]) := by
  have erase_0 : ([2, 6, 6, 6, 6, 6, 6] : List ℕ).erase 2 = [6, 6, 6, 6, 6, 6] := by decide
  have erase_1 : ([2, 6, 6, 6, 6, 6, 6] : List ℕ).erase 6 = [2, 6, 6, 6, 6, 6] := by decide
  have hallowed : ([2, 6, 6, 6, 6, 6, 6] : List ℕ).toFinset.filter (fun a => 0 < a ∧ a ≤ 6) = ([2, 6] : List ℕ).toFinset := by decide
  let coefficients : ℕ → ℝ[X] := fun a => if a = 2 then (X : ℝ[X]) else if a = 6 then (1 + 5 * X : ℝ[X]) else 0
  have hchildren : ∀ a ∈ ([2, 6] : List ℕ).toFinset,
      dp [6, 6, 6, 6, 6, 6] ([2, 6, 6, 6, 6, 6, 6].erase a) (some a) = coefficients a := by
    intro a ha
    have hcases : a = 2 ∨ a = 6 := by simpa using ha
    rcases hcases with rfl | rfl
    · change dp [6, 6, 6, 6, 6, 6] ([2, 6, 6, 6, 6, 6, 6].erase 2) (some 2) = (X : ℝ[X])
      rw [erase_0]
      exact D5.S3.Combinatorics.Permutation.MultisetRookEulerianCertificate.Block01.dag_0062
    · change dp [6, 6, 6, 6, 6, 6] ([2, 6, 6, 6, 6, 6, 6].erase 6) (some 6) = (1 + 5 * X : ℝ[X])
      rw [erase_1]
      exact dag_0070
  rw [dp_cons_eq_sum_of_children 6 [6, 6, 6, 6, 6, 6] [2, 6, 6, 6, 6, 6, 6] (some 6) ([2, 6] : List ℕ).toFinset coefficients hallowed hchildren]
  norm_num [coefficients, List.toFinset_cons, List.toFinset_nil, Finset.sum_insert, Finset.sum_empty, beq_iff_eq]
  <;> ring

theorem dag_0082 :
    dp [6, 6, 6, 6, 6, 6, 6] [1, 6, 6, 6, 6, 6, 6] (some 6) =
      (1 + 6 * X : ℝ[X]) := by
  have erase_0 : ([1, 6, 6, 6, 6, 6, 6] : List ℕ).erase 1 = [6, 6, 6, 6, 6, 6] := by decide
  have erase_1 : ([1, 6, 6, 6, 6, 6, 6] : List ℕ).erase 6 = [1, 6, 6, 6, 6, 6] := by decide
  have hallowed : ([1, 6, 6, 6, 6, 6, 6] : List ℕ).toFinset.filter (fun a => 0 < a ∧ a ≤ 6) = ([1, 6] : List ℕ).toFinset := by decide
  let coefficients : ℕ → ℝ[X] := fun a => if a = 1 then (X : ℝ[X]) else if a = 6 then (1 + 5 * X : ℝ[X]) else 0
  have hchildren : ∀ a ∈ ([1, 6] : List ℕ).toFinset,
      dp [6, 6, 6, 6, 6, 6] ([1, 6, 6, 6, 6, 6, 6].erase a) (some a) = coefficients a := by
    intro a ha
    have hcases : a = 1 ∨ a = 6 := by simpa using ha
    rcases hcases with rfl | rfl
    · change dp [6, 6, 6, 6, 6, 6] ([1, 6, 6, 6, 6, 6, 6].erase 1) (some 1) = (X : ℝ[X])
      rw [erase_0]
      exact D5.S3.Combinatorics.Permutation.MultisetRookEulerianCertificate.Block01.dag_0061
    · change dp [6, 6, 6, 6, 6, 6] ([1, 6, 6, 6, 6, 6, 6].erase 6) (some 6) = (1 + 5 * X : ℝ[X])
      rw [erase_1]
      exact dag_0071
  rw [dp_cons_eq_sum_of_children 6 [6, 6, 6, 6, 6, 6] [1, 6, 6, 6, 6, 6, 6] (some 6) ([1, 6] : List ℕ).toFinset coefficients hallowed hchildren]
  norm_num [coefficients, List.toFinset_cons, List.toFinset_nil, Finset.sum_insert, Finset.sum_empty, beq_iff_eq]
  <;> ring

theorem dag_0083 :
    dp [6, 6, 6, 6, 6, 6, 6, 6] [6, 6, 6, 6, 6, 6, 6, 6] (some 1) =
      (X : ℝ[X]) := by
  have erase_0 : ([6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).erase 6 = [6, 6, 6, 6, 6, 6, 6] := by decide
  have hallowed : ([6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).toFinset.filter (fun a => 0 < a ∧ a ≤ 6) = ([6] : List ℕ).toFinset := by decide
  let coefficients : ℕ → ℝ[X] := fun a => if a = 6 then (1 : ℝ[X]) else 0
  have hchildren : ∀ a ∈ ([6] : List ℕ).toFinset,
      dp [6, 6, 6, 6, 6, 6, 6] ([6, 6, 6, 6, 6, 6, 6, 6].erase a) (some a) = coefficients a := by
    intro a ha
    have hcases : a = 6 := by simpa using ha
    rcases hcases with rfl
    · change dp [6, 6, 6, 6, 6, 6, 6] ([6, 6, 6, 6, 6, 6, 6, 6].erase 6) (some 6) = (1 : ℝ[X])
      rw [erase_0]
      exact dag_0077
  rw [dp_cons_eq_sum_of_children 6 [6, 6, 6, 6, 6, 6, 6] [6, 6, 6, 6, 6, 6, 6, 6] (some 1) ([6] : List ℕ).toFinset coefficients hallowed hchildren]
  norm_num [coefficients, List.toFinset_cons, List.toFinset_nil, Finset.sum_insert, Finset.sum_empty, beq_iff_eq]
  <;> ring

theorem dag_0084 :
    dp [6, 6, 6, 6, 6, 6, 6, 6] [6, 6, 6, 6, 6, 6, 6, 6] (some 2) =
      (X : ℝ[X]) := by
  have erase_0 : ([6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).erase 6 = [6, 6, 6, 6, 6, 6, 6] := by decide
  have hallowed : ([6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).toFinset.filter (fun a => 0 < a ∧ a ≤ 6) = ([6] : List ℕ).toFinset := by decide
  let coefficients : ℕ → ℝ[X] := fun a => if a = 6 then (1 : ℝ[X]) else 0
  have hchildren : ∀ a ∈ ([6] : List ℕ).toFinset,
      dp [6, 6, 6, 6, 6, 6, 6] ([6, 6, 6, 6, 6, 6, 6, 6].erase a) (some a) = coefficients a := by
    intro a ha
    have hcases : a = 6 := by simpa using ha
    rcases hcases with rfl
    · change dp [6, 6, 6, 6, 6, 6, 6] ([6, 6, 6, 6, 6, 6, 6, 6].erase 6) (some 6) = (1 : ℝ[X])
      rw [erase_0]
      exact dag_0077
  rw [dp_cons_eq_sum_of_children 6 [6, 6, 6, 6, 6, 6, 6] [6, 6, 6, 6, 6, 6, 6, 6] (some 2) ([6] : List ℕ).toFinset coefficients hallowed hchildren]
  norm_num [coefficients, List.toFinset_cons, List.toFinset_nil, Finset.sum_insert, Finset.sum_empty, beq_iff_eq]
  <;> ring

theorem dag_0085 :
    dp [6, 6, 6, 6, 6, 6, 6, 6] [6, 6, 6, 6, 6, 6, 6, 6] (some 3) =
      (X : ℝ[X]) := by
  have erase_0 : ([6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).erase 6 = [6, 6, 6, 6, 6, 6, 6] := by decide
  have hallowed : ([6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).toFinset.filter (fun a => 0 < a ∧ a ≤ 6) = ([6] : List ℕ).toFinset := by decide
  let coefficients : ℕ → ℝ[X] := fun a => if a = 6 then (1 : ℝ[X]) else 0
  have hchildren : ∀ a ∈ ([6] : List ℕ).toFinset,
      dp [6, 6, 6, 6, 6, 6, 6] ([6, 6, 6, 6, 6, 6, 6, 6].erase a) (some a) = coefficients a := by
    intro a ha
    have hcases : a = 6 := by simpa using ha
    rcases hcases with rfl
    · change dp [6, 6, 6, 6, 6, 6, 6] ([6, 6, 6, 6, 6, 6, 6, 6].erase 6) (some 6) = (1 : ℝ[X])
      rw [erase_0]
      exact dag_0077
  rw [dp_cons_eq_sum_of_children 6 [6, 6, 6, 6, 6, 6, 6] [6, 6, 6, 6, 6, 6, 6, 6] (some 3) ([6] : List ℕ).toFinset coefficients hallowed hchildren]
  norm_num [coefficients, List.toFinset_cons, List.toFinset_nil, Finset.sum_insert, Finset.sum_empty, beq_iff_eq]
  <;> ring

theorem dag_0086 :
    dp [6, 6, 6, 6, 6, 6, 6, 6] [6, 6, 6, 6, 6, 6, 6, 6] (some 4) =
      (X : ℝ[X]) := by
  have erase_0 : ([6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).erase 6 = [6, 6, 6, 6, 6, 6, 6] := by decide
  have hallowed : ([6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).toFinset.filter (fun a => 0 < a ∧ a ≤ 6) = ([6] : List ℕ).toFinset := by decide
  let coefficients : ℕ → ℝ[X] := fun a => if a = 6 then (1 : ℝ[X]) else 0
  have hchildren : ∀ a ∈ ([6] : List ℕ).toFinset,
      dp [6, 6, 6, 6, 6, 6, 6] ([6, 6, 6, 6, 6, 6, 6, 6].erase a) (some a) = coefficients a := by
    intro a ha
    have hcases : a = 6 := by simpa using ha
    rcases hcases with rfl
    · change dp [6, 6, 6, 6, 6, 6, 6] ([6, 6, 6, 6, 6, 6, 6, 6].erase 6) (some 6) = (1 : ℝ[X])
      rw [erase_0]
      exact dag_0077
  rw [dp_cons_eq_sum_of_children 6 [6, 6, 6, 6, 6, 6, 6] [6, 6, 6, 6, 6, 6, 6, 6] (some 4) ([6] : List ℕ).toFinset coefficients hallowed hchildren]
  norm_num [coefficients, List.toFinset_cons, List.toFinset_nil, Finset.sum_insert, Finset.sum_empty, beq_iff_eq]
  <;> ring

theorem dag_0087 :
    dp [6, 6, 6, 6, 6, 6, 6, 6] [6, 6, 6, 6, 6, 6, 6, 6] (some 5) =
      (X : ℝ[X]) := by
  have erase_0 : ([6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).erase 6 = [6, 6, 6, 6, 6, 6, 6] := by decide
  have hallowed : ([6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).toFinset.filter (fun a => 0 < a ∧ a ≤ 6) = ([6] : List ℕ).toFinset := by decide
  let coefficients : ℕ → ℝ[X] := fun a => if a = 6 then (1 : ℝ[X]) else 0
  have hchildren : ∀ a ∈ ([6] : List ℕ).toFinset,
      dp [6, 6, 6, 6, 6, 6, 6] ([6, 6, 6, 6, 6, 6, 6, 6].erase a) (some a) = coefficients a := by
    intro a ha
    have hcases : a = 6 := by simpa using ha
    rcases hcases with rfl
    · change dp [6, 6, 6, 6, 6, 6, 6] ([6, 6, 6, 6, 6, 6, 6, 6].erase 6) (some 6) = (1 : ℝ[X])
      rw [erase_0]
      exact dag_0077
  rw [dp_cons_eq_sum_of_children 6 [6, 6, 6, 6, 6, 6, 6] [6, 6, 6, 6, 6, 6, 6, 6] (some 5) ([6] : List ℕ).toFinset coefficients hallowed hchildren]
  norm_num [coefficients, List.toFinset_cons, List.toFinset_nil, Finset.sum_insert, Finset.sum_empty, beq_iff_eq]
  <;> ring

theorem dag_0088 :
    dp [6, 6, 6, 6, 6, 6, 6, 6] [6, 6, 6, 6, 6, 6, 6, 6] (some 6) =
      (1 : ℝ[X]) := by
  have erase_0 : ([6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).erase 6 = [6, 6, 6, 6, 6, 6, 6] := by decide
  have hallowed : ([6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).toFinset.filter (fun a => 0 < a ∧ a ≤ 6) = ([6] : List ℕ).toFinset := by decide
  let coefficients : ℕ → ℝ[X] := fun a => if a = 6 then (1 : ℝ[X]) else 0
  have hchildren : ∀ a ∈ ([6] : List ℕ).toFinset,
      dp [6, 6, 6, 6, 6, 6, 6] ([6, 6, 6, 6, 6, 6, 6, 6].erase a) (some a) = coefficients a := by
    intro a ha
    have hcases : a = 6 := by simpa using ha
    rcases hcases with rfl
    · change dp [6, 6, 6, 6, 6, 6, 6] ([6, 6, 6, 6, 6, 6, 6, 6].erase 6) (some 6) = (1 : ℝ[X])
      rw [erase_0]
      exact dag_0077
  rw [dp_cons_eq_sum_of_children 6 [6, 6, 6, 6, 6, 6, 6] [6, 6, 6, 6, 6, 6, 6, 6] (some 6) ([6] : List ℕ).toFinset coefficients hallowed hchildren]
  norm_num [coefficients, List.toFinset_cons, List.toFinset_nil, Finset.sum_insert, Finset.sum_empty, beq_iff_eq]
  <;> ring

theorem dag_0089 :
    dp [6, 6, 6, 6, 6, 6, 6, 6] [5, 6, 6, 6, 6, 6, 6, 6] (some 6) =
      (1 + 7 * X : ℝ[X]) := by
  have erase_0 : ([5, 6, 6, 6, 6, 6, 6, 6] : List ℕ).erase 5 = [6, 6, 6, 6, 6, 6, 6] := by decide
  have erase_1 : ([5, 6, 6, 6, 6, 6, 6, 6] : List ℕ).erase 6 = [5, 6, 6, 6, 6, 6, 6] := by decide
  have hallowed : ([5, 6, 6, 6, 6, 6, 6, 6] : List ℕ).toFinset.filter (fun a => 0 < a ∧ a ≤ 6) = ([5, 6] : List ℕ).toFinset := by decide
  let coefficients : ℕ → ℝ[X] := fun a => if a = 5 then (X : ℝ[X]) else if a = 6 then (1 + 6 * X : ℝ[X]) else 0
  have hchildren : ∀ a ∈ ([5, 6] : List ℕ).toFinset,
      dp [6, 6, 6, 6, 6, 6, 6] ([5, 6, 6, 6, 6, 6, 6, 6].erase a) (some a) = coefficients a := by
    intro a ha
    have hcases : a = 5 ∨ a = 6 := by simpa using ha
    rcases hcases with rfl | rfl
    · change dp [6, 6, 6, 6, 6, 6, 6] ([5, 6, 6, 6, 6, 6, 6, 6].erase 5) (some 5) = (X : ℝ[X])
      rw [erase_0]
      exact dag_0076
    · change dp [6, 6, 6, 6, 6, 6, 6] ([5, 6, 6, 6, 6, 6, 6, 6].erase 6) (some 6) = (1 + 6 * X : ℝ[X])
      rw [erase_1]
      exact dag_0078
  rw [dp_cons_eq_sum_of_children 6 [6, 6, 6, 6, 6, 6, 6] [5, 6, 6, 6, 6, 6, 6, 6] (some 6) ([5, 6] : List ℕ).toFinset coefficients hallowed hchildren]
  norm_num [coefficients, List.toFinset_cons, List.toFinset_nil, Finset.sum_insert, Finset.sum_empty, beq_iff_eq]
  <;> ring

theorem dag_0090 :
    dp [6, 6, 6, 6, 6, 6, 6, 6] [4, 6, 6, 6, 6, 6, 6, 6] (some 6) =
      (1 + 7 * X : ℝ[X]) := by
  have erase_0 : ([4, 6, 6, 6, 6, 6, 6, 6] : List ℕ).erase 4 = [6, 6, 6, 6, 6, 6, 6] := by decide
  have erase_1 : ([4, 6, 6, 6, 6, 6, 6, 6] : List ℕ).erase 6 = [4, 6, 6, 6, 6, 6, 6] := by decide
  have hallowed : ([4, 6, 6, 6, 6, 6, 6, 6] : List ℕ).toFinset.filter (fun a => 0 < a ∧ a ≤ 6) = ([4, 6] : List ℕ).toFinset := by decide
  let coefficients : ℕ → ℝ[X] := fun a => if a = 4 then (X : ℝ[X]) else if a = 6 then (1 + 6 * X : ℝ[X]) else 0
  have hchildren : ∀ a ∈ ([4, 6] : List ℕ).toFinset,
      dp [6, 6, 6, 6, 6, 6, 6] ([4, 6, 6, 6, 6, 6, 6, 6].erase a) (some a) = coefficients a := by
    intro a ha
    have hcases : a = 4 ∨ a = 6 := by simpa using ha
    rcases hcases with rfl | rfl
    · change dp [6, 6, 6, 6, 6, 6, 6] ([4, 6, 6, 6, 6, 6, 6, 6].erase 4) (some 4) = (X : ℝ[X])
      rw [erase_0]
      exact dag_0075
    · change dp [6, 6, 6, 6, 6, 6, 6] ([4, 6, 6, 6, 6, 6, 6, 6].erase 6) (some 6) = (1 + 6 * X : ℝ[X])
      rw [erase_1]
      exact dag_0079
  rw [dp_cons_eq_sum_of_children 6 [6, 6, 6, 6, 6, 6, 6] [4, 6, 6, 6, 6, 6, 6, 6] (some 6) ([4, 6] : List ℕ).toFinset coefficients hallowed hchildren]
  norm_num [coefficients, List.toFinset_cons, List.toFinset_nil, Finset.sum_insert, Finset.sum_empty, beq_iff_eq]
  <;> ring

theorem dag_0091 :
    dp [6, 6, 6, 6, 6, 6, 6, 6] [3, 6, 6, 6, 6, 6, 6, 6] (some 6) =
      (1 + 7 * X : ℝ[X]) := by
  have erase_0 : ([3, 6, 6, 6, 6, 6, 6, 6] : List ℕ).erase 3 = [6, 6, 6, 6, 6, 6, 6] := by decide
  have erase_1 : ([3, 6, 6, 6, 6, 6, 6, 6] : List ℕ).erase 6 = [3, 6, 6, 6, 6, 6, 6] := by decide
  have hallowed : ([3, 6, 6, 6, 6, 6, 6, 6] : List ℕ).toFinset.filter (fun a => 0 < a ∧ a ≤ 6) = ([3, 6] : List ℕ).toFinset := by decide
  let coefficients : ℕ → ℝ[X] := fun a => if a = 3 then (X : ℝ[X]) else if a = 6 then (1 + 6 * X : ℝ[X]) else 0
  have hchildren : ∀ a ∈ ([3, 6] : List ℕ).toFinset,
      dp [6, 6, 6, 6, 6, 6, 6] ([3, 6, 6, 6, 6, 6, 6, 6].erase a) (some a) = coefficients a := by
    intro a ha
    have hcases : a = 3 ∨ a = 6 := by simpa using ha
    rcases hcases with rfl | rfl
    · change dp [6, 6, 6, 6, 6, 6, 6] ([3, 6, 6, 6, 6, 6, 6, 6].erase 3) (some 3) = (X : ℝ[X])
      rw [erase_0]
      exact dag_0074
    · change dp [6, 6, 6, 6, 6, 6, 6] ([3, 6, 6, 6, 6, 6, 6, 6].erase 6) (some 6) = (1 + 6 * X : ℝ[X])
      rw [erase_1]
      exact dag_0080
  rw [dp_cons_eq_sum_of_children 6 [6, 6, 6, 6, 6, 6, 6] [3, 6, 6, 6, 6, 6, 6, 6] (some 6) ([3, 6] : List ℕ).toFinset coefficients hallowed hchildren]
  norm_num [coefficients, List.toFinset_cons, List.toFinset_nil, Finset.sum_insert, Finset.sum_empty, beq_iff_eq]
  <;> ring

theorem dag_0092 :
    dp [6, 6, 6, 6, 6, 6, 6, 6] [2, 6, 6, 6, 6, 6, 6, 6] (some 6) =
      (1 + 7 * X : ℝ[X]) := by
  have erase_0 : ([2, 6, 6, 6, 6, 6, 6, 6] : List ℕ).erase 2 = [6, 6, 6, 6, 6, 6, 6] := by decide
  have erase_1 : ([2, 6, 6, 6, 6, 6, 6, 6] : List ℕ).erase 6 = [2, 6, 6, 6, 6, 6, 6] := by decide
  have hallowed : ([2, 6, 6, 6, 6, 6, 6, 6] : List ℕ).toFinset.filter (fun a => 0 < a ∧ a ≤ 6) = ([2, 6] : List ℕ).toFinset := by decide
  let coefficients : ℕ → ℝ[X] := fun a => if a = 2 then (X : ℝ[X]) else if a = 6 then (1 + 6 * X : ℝ[X]) else 0
  have hchildren : ∀ a ∈ ([2, 6] : List ℕ).toFinset,
      dp [6, 6, 6, 6, 6, 6, 6] ([2, 6, 6, 6, 6, 6, 6, 6].erase a) (some a) = coefficients a := by
    intro a ha
    have hcases : a = 2 ∨ a = 6 := by simpa using ha
    rcases hcases with rfl | rfl
    · change dp [6, 6, 6, 6, 6, 6, 6] ([2, 6, 6, 6, 6, 6, 6, 6].erase 2) (some 2) = (X : ℝ[X])
      rw [erase_0]
      exact dag_0073
    · change dp [6, 6, 6, 6, 6, 6, 6] ([2, 6, 6, 6, 6, 6, 6, 6].erase 6) (some 6) = (1 + 6 * X : ℝ[X])
      rw [erase_1]
      exact dag_0081
  rw [dp_cons_eq_sum_of_children 6 [6, 6, 6, 6, 6, 6, 6] [2, 6, 6, 6, 6, 6, 6, 6] (some 6) ([2, 6] : List ℕ).toFinset coefficients hallowed hchildren]
  norm_num [coefficients, List.toFinset_cons, List.toFinset_nil, Finset.sum_insert, Finset.sum_empty, beq_iff_eq]
  <;> ring

end D5.S3.Combinatorics.Permutation.MultisetRookEulerianCertificate.Block02
