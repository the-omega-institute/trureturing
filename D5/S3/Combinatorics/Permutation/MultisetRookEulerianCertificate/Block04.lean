/- GID: D5/S3/Combinatorics/Permutation/MultisetRookEulerianCertificate/Block04
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Permutation/MultisetRookEulerianCertificate/Block04
   mirror-E: none(waiver:exact-finite-certificate)
   anchors: []
   utility: none
   digest: Exact residual-content certificates dag_0123 through dag_0151. -/

import D5.S3.Combinatorics.Permutation.MultisetRookEulerianWordRecurrence
import D5.S3.Combinatorics.Permutation.MultisetRookEulerianCertificate.Block03

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace D5.S3.Combinatorics.Permutation.MultisetRookEulerianCertificate.Block04

open Polynomial
open D5.S3.Combinatorics.Permutation.MultisetRookEulerianWordRecurrence

theorem dag_0123 :
    dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] [4, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] (some 6) =
      (1 + 10 * X : ℝ[X]) := by
  have erase_0 : ([4, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).erase 4 = [6, 6, 6, 6, 6, 6, 6, 6, 6, 6] := by decide
  have erase_1 : ([4, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).erase 6 = [4, 6, 6, 6, 6, 6, 6, 6, 6, 6] := by decide
  have hallowed : ([4, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).toFinset.filter (fun a => 0 < a ∧ a ≤ 6) = ([4, 6] : List ℕ).toFinset := by decide
  let coefficients : ℕ → ℝ[X] := fun a => if a = 4 then (X : ℝ[X]) else if a = 6 then (1 + 9 * X : ℝ[X]) else 0
  have hchildren : ∀ a ∈ ([4, 6] : List ℕ).toFinset,
      dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([4, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase a) (some a) = coefficients a := by
    intro a ha
    have hcases : a = 4 ∨ a = 6 := by simpa using ha
    rcases hcases with rfl | rfl
    · change dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([4, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase 4) (some 4) = (X : ℝ[X])
      rw [erase_0]
      exact D5.S3.Combinatorics.Permutation.MultisetRookEulerianCertificate.Block03.dag_0108
    · change dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([4, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase 6) (some 6) = (1 + 9 * X : ℝ[X])
      rw [erase_1]
      exact D5.S3.Combinatorics.Permutation.MultisetRookEulerianCertificate.Block03.dag_0112
  rw [dp_cons_eq_sum_of_children 6 [6, 6, 6, 6, 6, 6, 6, 6, 6, 6] [4, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] (some 6) ([4, 6] : List ℕ).toFinset coefficients hallowed hchildren]
  norm_num [coefficients, List.toFinset_cons, List.toFinset_nil, Finset.sum_insert, Finset.sum_empty, beq_iff_eq]
  <;> ring

theorem dag_0124 :
    dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] [3, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] (some 6) =
      (1 + 10 * X : ℝ[X]) := by
  have erase_0 : ([3, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).erase 3 = [6, 6, 6, 6, 6, 6, 6, 6, 6, 6] := by decide
  have erase_1 : ([3, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).erase 6 = [3, 6, 6, 6, 6, 6, 6, 6, 6, 6] := by decide
  have hallowed : ([3, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).toFinset.filter (fun a => 0 < a ∧ a ≤ 6) = ([3, 6] : List ℕ).toFinset := by decide
  let coefficients : ℕ → ℝ[X] := fun a => if a = 3 then (X : ℝ[X]) else if a = 6 then (1 + 9 * X : ℝ[X]) else 0
  have hchildren : ∀ a ∈ ([3, 6] : List ℕ).toFinset,
      dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([3, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase a) (some a) = coefficients a := by
    intro a ha
    have hcases : a = 3 ∨ a = 6 := by simpa using ha
    rcases hcases with rfl | rfl
    · change dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([3, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase 3) (some 3) = (X : ℝ[X])
      rw [erase_0]
      exact D5.S3.Combinatorics.Permutation.MultisetRookEulerianCertificate.Block03.dag_0107
    · change dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([3, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase 6) (some 6) = (1 + 9 * X : ℝ[X])
      rw [erase_1]
      exact D5.S3.Combinatorics.Permutation.MultisetRookEulerianCertificate.Block03.dag_0113
  rw [dp_cons_eq_sum_of_children 6 [6, 6, 6, 6, 6, 6, 6, 6, 6, 6] [3, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] (some 6) ([3, 6] : List ℕ).toFinset coefficients hallowed hchildren]
  norm_num [coefficients, List.toFinset_cons, List.toFinset_nil, Finset.sum_insert, Finset.sum_empty, beq_iff_eq]
  <;> ring

theorem dag_0125 :
    dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] [2, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] (some 6) =
      (1 + 10 * X : ℝ[X]) := by
  have erase_0 : ([2, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).erase 2 = [6, 6, 6, 6, 6, 6, 6, 6, 6, 6] := by decide
  have erase_1 : ([2, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).erase 6 = [2, 6, 6, 6, 6, 6, 6, 6, 6, 6] := by decide
  have hallowed : ([2, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).toFinset.filter (fun a => 0 < a ∧ a ≤ 6) = ([2, 6] : List ℕ).toFinset := by decide
  let coefficients : ℕ → ℝ[X] := fun a => if a = 2 then (X : ℝ[X]) else if a = 6 then (1 + 9 * X : ℝ[X]) else 0
  have hchildren : ∀ a ∈ ([2, 6] : List ℕ).toFinset,
      dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([2, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase a) (some a) = coefficients a := by
    intro a ha
    have hcases : a = 2 ∨ a = 6 := by simpa using ha
    rcases hcases with rfl | rfl
    · change dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([2, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase 2) (some 2) = (X : ℝ[X])
      rw [erase_0]
      exact D5.S3.Combinatorics.Permutation.MultisetRookEulerianCertificate.Block03.dag_0106
    · change dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([2, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase 6) (some 6) = (1 + 9 * X : ℝ[X])
      rw [erase_1]
      exact D5.S3.Combinatorics.Permutation.MultisetRookEulerianCertificate.Block03.dag_0114
  rw [dp_cons_eq_sum_of_children 6 [6, 6, 6, 6, 6, 6, 6, 6, 6, 6] [2, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] (some 6) ([2, 6] : List ℕ).toFinset coefficients hallowed hchildren]
  norm_num [coefficients, List.toFinset_cons, List.toFinset_nil, Finset.sum_insert, Finset.sum_empty, beq_iff_eq]
  <;> ring

theorem dag_0126 :
    dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] [1, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] (some 6) =
      (1 + 10 * X : ℝ[X]) := by
  have erase_0 : ([1, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).erase 1 = [6, 6, 6, 6, 6, 6, 6, 6, 6, 6] := by decide
  have erase_1 : ([1, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).erase 6 = [1, 6, 6, 6, 6, 6, 6, 6, 6, 6] := by decide
  have hallowed : ([1, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).toFinset.filter (fun a => 0 < a ∧ a ≤ 6) = ([1, 6] : List ℕ).toFinset := by decide
  let coefficients : ℕ → ℝ[X] := fun a => if a = 1 then (X : ℝ[X]) else if a = 6 then (1 + 9 * X : ℝ[X]) else 0
  have hchildren : ∀ a ∈ ([1, 6] : List ℕ).toFinset,
      dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([1, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase a) (some a) = coefficients a := by
    intro a ha
    have hcases : a = 1 ∨ a = 6 := by simpa using ha
    rcases hcases with rfl | rfl
    · change dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([1, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase 1) (some 1) = (X : ℝ[X])
      rw [erase_0]
      exact D5.S3.Combinatorics.Permutation.MultisetRookEulerianCertificate.Block03.dag_0105
    · change dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([1, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase 6) (some 6) = (1 + 9 * X : ℝ[X])
      rw [erase_1]
      exact D5.S3.Combinatorics.Permutation.MultisetRookEulerianCertificate.Block03.dag_0115
  rw [dp_cons_eq_sum_of_children 6 [6, 6, 6, 6, 6, 6, 6, 6, 6, 6] [1, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] (some 6) ([1, 6] : List ℕ).toFinset coefficients hallowed hchildren]
  norm_num [coefficients, List.toFinset_cons, List.toFinset_nil, Finset.sum_insert, Finset.sum_empty, beq_iff_eq]
  <;> ring

theorem dag_0127 :
    dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] (some 1) =
      (X : ℝ[X]) := by
  have erase_0 : ([6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).erase 6 = [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] := by decide
  have hallowed : ([6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).toFinset.filter (fun a => 0 < a ∧ a ≤ 6) = ([6] : List ℕ).toFinset := by decide
  let coefficients : ℕ → ℝ[X] := fun a => if a = 6 then (1 : ℝ[X]) else 0
  have hchildren : ∀ a ∈ ([6] : List ℕ).toFinset,
      dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase a) (some a) = coefficients a := by
    intro a ha
    have hcases : a = 6 := by simpa using ha
    rcases hcases with rfl
    · change dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase 6) (some 6) = (1 : ℝ[X])
      rw [erase_0]
      exact D5.S3.Combinatorics.Permutation.MultisetRookEulerianCertificate.Block03.dag_0121
  rw [dp_cons_eq_sum_of_children 6 [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] (some 1) ([6] : List ℕ).toFinset coefficients hallowed hchildren]
  norm_num [coefficients, List.toFinset_cons, List.toFinset_nil, Finset.sum_insert, Finset.sum_empty, beq_iff_eq]
  <;> ring

theorem dag_0128 :
    dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] (some 2) =
      (X : ℝ[X]) := by
  have erase_0 : ([6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).erase 6 = [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] := by decide
  have hallowed : ([6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).toFinset.filter (fun a => 0 < a ∧ a ≤ 6) = ([6] : List ℕ).toFinset := by decide
  let coefficients : ℕ → ℝ[X] := fun a => if a = 6 then (1 : ℝ[X]) else 0
  have hchildren : ∀ a ∈ ([6] : List ℕ).toFinset,
      dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase a) (some a) = coefficients a := by
    intro a ha
    have hcases : a = 6 := by simpa using ha
    rcases hcases with rfl
    · change dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase 6) (some 6) = (1 : ℝ[X])
      rw [erase_0]
      exact D5.S3.Combinatorics.Permutation.MultisetRookEulerianCertificate.Block03.dag_0121
  rw [dp_cons_eq_sum_of_children 6 [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] (some 2) ([6] : List ℕ).toFinset coefficients hallowed hchildren]
  norm_num [coefficients, List.toFinset_cons, List.toFinset_nil, Finset.sum_insert, Finset.sum_empty, beq_iff_eq]
  <;> ring

theorem dag_0129 :
    dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] (some 3) =
      (X : ℝ[X]) := by
  have erase_0 : ([6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).erase 6 = [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] := by decide
  have hallowed : ([6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).toFinset.filter (fun a => 0 < a ∧ a ≤ 6) = ([6] : List ℕ).toFinset := by decide
  let coefficients : ℕ → ℝ[X] := fun a => if a = 6 then (1 : ℝ[X]) else 0
  have hchildren : ∀ a ∈ ([6] : List ℕ).toFinset,
      dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase a) (some a) = coefficients a := by
    intro a ha
    have hcases : a = 6 := by simpa using ha
    rcases hcases with rfl
    · change dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase 6) (some 6) = (1 : ℝ[X])
      rw [erase_0]
      exact D5.S3.Combinatorics.Permutation.MultisetRookEulerianCertificate.Block03.dag_0121
  rw [dp_cons_eq_sum_of_children 6 [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] (some 3) ([6] : List ℕ).toFinset coefficients hallowed hchildren]
  norm_num [coefficients, List.toFinset_cons, List.toFinset_nil, Finset.sum_insert, Finset.sum_empty, beq_iff_eq]
  <;> ring

theorem dag_0130 :
    dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] (some 4) =
      (X : ℝ[X]) := by
  have erase_0 : ([6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).erase 6 = [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] := by decide
  have hallowed : ([6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).toFinset.filter (fun a => 0 < a ∧ a ≤ 6) = ([6] : List ℕ).toFinset := by decide
  let coefficients : ℕ → ℝ[X] := fun a => if a = 6 then (1 : ℝ[X]) else 0
  have hchildren : ∀ a ∈ ([6] : List ℕ).toFinset,
      dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase a) (some a) = coefficients a := by
    intro a ha
    have hcases : a = 6 := by simpa using ha
    rcases hcases with rfl
    · change dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase 6) (some 6) = (1 : ℝ[X])
      rw [erase_0]
      exact D5.S3.Combinatorics.Permutation.MultisetRookEulerianCertificate.Block03.dag_0121
  rw [dp_cons_eq_sum_of_children 6 [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] (some 4) ([6] : List ℕ).toFinset coefficients hallowed hchildren]
  norm_num [coefficients, List.toFinset_cons, List.toFinset_nil, Finset.sum_insert, Finset.sum_empty, beq_iff_eq]
  <;> ring

theorem dag_0131 :
    dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] (some 5) =
      (X : ℝ[X]) := by
  have erase_0 : ([6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).erase 6 = [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] := by decide
  have hallowed : ([6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).toFinset.filter (fun a => 0 < a ∧ a ≤ 6) = ([6] : List ℕ).toFinset := by decide
  let coefficients : ℕ → ℝ[X] := fun a => if a = 6 then (1 : ℝ[X]) else 0
  have hchildren : ∀ a ∈ ([6] : List ℕ).toFinset,
      dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase a) (some a) = coefficients a := by
    intro a ha
    have hcases : a = 6 := by simpa using ha
    rcases hcases with rfl
    · change dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase 6) (some 6) = (1 : ℝ[X])
      rw [erase_0]
      exact D5.S3.Combinatorics.Permutation.MultisetRookEulerianCertificate.Block03.dag_0121
  rw [dp_cons_eq_sum_of_children 6 [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] (some 5) ([6] : List ℕ).toFinset coefficients hallowed hchildren]
  norm_num [coefficients, List.toFinset_cons, List.toFinset_nil, Finset.sum_insert, Finset.sum_empty, beq_iff_eq]
  <;> ring

theorem dag_0132 :
    dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] (some 6) =
      (1 : ℝ[X]) := by
  have erase_0 : ([6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).erase 6 = [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] := by decide
  have hallowed : ([6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).toFinset.filter (fun a => 0 < a ∧ a ≤ 6) = ([6] : List ℕ).toFinset := by decide
  let coefficients : ℕ → ℝ[X] := fun a => if a = 6 then (1 : ℝ[X]) else 0
  have hchildren : ∀ a ∈ ([6] : List ℕ).toFinset,
      dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase a) (some a) = coefficients a := by
    intro a ha
    have hcases : a = 6 := by simpa using ha
    rcases hcases with rfl
    · change dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase 6) (some 6) = (1 : ℝ[X])
      rw [erase_0]
      exact D5.S3.Combinatorics.Permutation.MultisetRookEulerianCertificate.Block03.dag_0121
  rw [dp_cons_eq_sum_of_children 6 [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] (some 6) ([6] : List ℕ).toFinset coefficients hallowed hchildren]
  norm_num [coefficients, List.toFinset_cons, List.toFinset_nil, Finset.sum_insert, Finset.sum_empty, beq_iff_eq]
  <;> ring

theorem dag_0133 :
    dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] (some 6) =
      (1 + 11 * X : ℝ[X]) := by
  have erase_0 : ([5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).erase 5 = [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] := by decide
  have erase_1 : ([5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).erase 6 = [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] := by decide
  have hallowed : ([5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).toFinset.filter (fun a => 0 < a ∧ a ≤ 6) = ([5, 6] : List ℕ).toFinset := by decide
  let coefficients : ℕ → ℝ[X] := fun a => if a = 5 then (X : ℝ[X]) else if a = 6 then (1 + 10 * X : ℝ[X]) else 0
  have hchildren : ∀ a ∈ ([5, 6] : List ℕ).toFinset,
      dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase a) (some a) = coefficients a := by
    intro a ha
    have hcases : a = 5 ∨ a = 6 := by simpa using ha
    rcases hcases with rfl | rfl
    · change dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase 5) (some 5) = (X : ℝ[X])
      rw [erase_0]
      exact D5.S3.Combinatorics.Permutation.MultisetRookEulerianCertificate.Block03.dag_0120
    · change dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase 6) (some 6) = (1 + 10 * X : ℝ[X])
      rw [erase_1]
      exact D5.S3.Combinatorics.Permutation.MultisetRookEulerianCertificate.Block03.dag_0122
  rw [dp_cons_eq_sum_of_children 6 [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] (some 6) ([5, 6] : List ℕ).toFinset coefficients hallowed hchildren]
  norm_num [coefficients, List.toFinset_cons, List.toFinset_nil, Finset.sum_insert, Finset.sum_empty, beq_iff_eq]
  <;> ring

theorem dag_0134 :
    dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] [4, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] (some 6) =
      (1 + 11 * X : ℝ[X]) := by
  have erase_0 : ([4, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).erase 4 = [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] := by decide
  have erase_1 : ([4, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).erase 6 = [4, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] := by decide
  have hallowed : ([4, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).toFinset.filter (fun a => 0 < a ∧ a ≤ 6) = ([4, 6] : List ℕ).toFinset := by decide
  let coefficients : ℕ → ℝ[X] := fun a => if a = 4 then (X : ℝ[X]) else if a = 6 then (1 + 10 * X : ℝ[X]) else 0
  have hchildren : ∀ a ∈ ([4, 6] : List ℕ).toFinset,
      dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([4, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase a) (some a) = coefficients a := by
    intro a ha
    have hcases : a = 4 ∨ a = 6 := by simpa using ha
    rcases hcases with rfl | rfl
    · change dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([4, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase 4) (some 4) = (X : ℝ[X])
      rw [erase_0]
      exact D5.S3.Combinatorics.Permutation.MultisetRookEulerianCertificate.Block03.dag_0119
    · change dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([4, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase 6) (some 6) = (1 + 10 * X : ℝ[X])
      rw [erase_1]
      exact dag_0123
  rw [dp_cons_eq_sum_of_children 6 [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] [4, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] (some 6) ([4, 6] : List ℕ).toFinset coefficients hallowed hchildren]
  norm_num [coefficients, List.toFinset_cons, List.toFinset_nil, Finset.sum_insert, Finset.sum_empty, beq_iff_eq]
  <;> ring

theorem dag_0135 :
    dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] [3, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] (some 6) =
      (1 + 11 * X : ℝ[X]) := by
  have erase_0 : ([3, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).erase 3 = [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] := by decide
  have erase_1 : ([3, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).erase 6 = [3, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] := by decide
  have hallowed : ([3, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).toFinset.filter (fun a => 0 < a ∧ a ≤ 6) = ([3, 6] : List ℕ).toFinset := by decide
  let coefficients : ℕ → ℝ[X] := fun a => if a = 3 then (X : ℝ[X]) else if a = 6 then (1 + 10 * X : ℝ[X]) else 0
  have hchildren : ∀ a ∈ ([3, 6] : List ℕ).toFinset,
      dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([3, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase a) (some a) = coefficients a := by
    intro a ha
    have hcases : a = 3 ∨ a = 6 := by simpa using ha
    rcases hcases with rfl | rfl
    · change dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([3, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase 3) (some 3) = (X : ℝ[X])
      rw [erase_0]
      exact D5.S3.Combinatorics.Permutation.MultisetRookEulerianCertificate.Block03.dag_0118
    · change dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([3, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase 6) (some 6) = (1 + 10 * X : ℝ[X])
      rw [erase_1]
      exact dag_0124
  rw [dp_cons_eq_sum_of_children 6 [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] [3, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] (some 6) ([3, 6] : List ℕ).toFinset coefficients hallowed hchildren]
  norm_num [coefficients, List.toFinset_cons, List.toFinset_nil, Finset.sum_insert, Finset.sum_empty, beq_iff_eq]
  <;> ring

theorem dag_0136 :
    dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] [2, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] (some 6) =
      (1 + 11 * X : ℝ[X]) := by
  have erase_0 : ([2, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).erase 2 = [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] := by decide
  have erase_1 : ([2, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).erase 6 = [2, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] := by decide
  have hallowed : ([2, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).toFinset.filter (fun a => 0 < a ∧ a ≤ 6) = ([2, 6] : List ℕ).toFinset := by decide
  let coefficients : ℕ → ℝ[X] := fun a => if a = 2 then (X : ℝ[X]) else if a = 6 then (1 + 10 * X : ℝ[X]) else 0
  have hchildren : ∀ a ∈ ([2, 6] : List ℕ).toFinset,
      dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([2, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase a) (some a) = coefficients a := by
    intro a ha
    have hcases : a = 2 ∨ a = 6 := by simpa using ha
    rcases hcases with rfl | rfl
    · change dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([2, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase 2) (some 2) = (X : ℝ[X])
      rw [erase_0]
      exact D5.S3.Combinatorics.Permutation.MultisetRookEulerianCertificate.Block03.dag_0117
    · change dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([2, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase 6) (some 6) = (1 + 10 * X : ℝ[X])
      rw [erase_1]
      exact dag_0125
  rw [dp_cons_eq_sum_of_children 6 [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] [2, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] (some 6) ([2, 6] : List ℕ).toFinset coefficients hallowed hchildren]
  norm_num [coefficients, List.toFinset_cons, List.toFinset_nil, Finset.sum_insert, Finset.sum_empty, beq_iff_eq]
  <;> ring

theorem dag_0137 :
    dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] [1, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] (some 6) =
      (1 + 11 * X : ℝ[X]) := by
  have erase_0 : ([1, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).erase 1 = [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] := by decide
  have erase_1 : ([1, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).erase 6 = [1, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] := by decide
  have hallowed : ([1, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).toFinset.filter (fun a => 0 < a ∧ a ≤ 6) = ([1, 6] : List ℕ).toFinset := by decide
  let coefficients : ℕ → ℝ[X] := fun a => if a = 1 then (X : ℝ[X]) else if a = 6 then (1 + 10 * X : ℝ[X]) else 0
  have hchildren : ∀ a ∈ ([1, 6] : List ℕ).toFinset,
      dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([1, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase a) (some a) = coefficients a := by
    intro a ha
    have hcases : a = 1 ∨ a = 6 := by simpa using ha
    rcases hcases with rfl | rfl
    · change dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([1, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase 1) (some 1) = (X : ℝ[X])
      rw [erase_0]
      exact D5.S3.Combinatorics.Permutation.MultisetRookEulerianCertificate.Block03.dag_0116
    · change dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([1, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase 6) (some 6) = (1 + 10 * X : ℝ[X])
      rw [erase_1]
      exact dag_0126
  rw [dp_cons_eq_sum_of_children 6 [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] [1, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] (some 6) ([1, 6] : List ℕ).toFinset coefficients hallowed hchildren]
  norm_num [coefficients, List.toFinset_cons, List.toFinset_nil, Finset.sum_insert, Finset.sum_empty, beq_iff_eq]
  <;> ring

theorem dag_0138 :
    dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] (some 1) =
      (X : ℝ[X]) := by
  have erase_0 : ([6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).erase 6 = [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] := by decide
  have hallowed : ([6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).toFinset.filter (fun a => 0 < a ∧ a ≤ 6) = ([6] : List ℕ).toFinset := by decide
  let coefficients : ℕ → ℝ[X] := fun a => if a = 6 then (1 : ℝ[X]) else 0
  have hchildren : ∀ a ∈ ([6] : List ℕ).toFinset,
      dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase a) (some a) = coefficients a := by
    intro a ha
    have hcases : a = 6 := by simpa using ha
    rcases hcases with rfl
    · change dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase 6) (some 6) = (1 : ℝ[X])
      rw [erase_0]
      exact dag_0132
  rw [dp_cons_eq_sum_of_children 6 [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] (some 1) ([6] : List ℕ).toFinset coefficients hallowed hchildren]
  norm_num [coefficients, List.toFinset_cons, List.toFinset_nil, Finset.sum_insert, Finset.sum_empty, beq_iff_eq]
  <;> ring

theorem dag_0139 :
    dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] (some 2) =
      (X : ℝ[X]) := by
  have erase_0 : ([6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).erase 6 = [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] := by decide
  have hallowed : ([6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).toFinset.filter (fun a => 0 < a ∧ a ≤ 6) = ([6] : List ℕ).toFinset := by decide
  let coefficients : ℕ → ℝ[X] := fun a => if a = 6 then (1 : ℝ[X]) else 0
  have hchildren : ∀ a ∈ ([6] : List ℕ).toFinset,
      dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase a) (some a) = coefficients a := by
    intro a ha
    have hcases : a = 6 := by simpa using ha
    rcases hcases with rfl
    · change dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase 6) (some 6) = (1 : ℝ[X])
      rw [erase_0]
      exact dag_0132
  rw [dp_cons_eq_sum_of_children 6 [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] (some 2) ([6] : List ℕ).toFinset coefficients hallowed hchildren]
  norm_num [coefficients, List.toFinset_cons, List.toFinset_nil, Finset.sum_insert, Finset.sum_empty, beq_iff_eq]
  <;> ring

theorem dag_0140 :
    dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] (some 3) =
      (X : ℝ[X]) := by
  have erase_0 : ([6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).erase 6 = [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] := by decide
  have hallowed : ([6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).toFinset.filter (fun a => 0 < a ∧ a ≤ 6) = ([6] : List ℕ).toFinset := by decide
  let coefficients : ℕ → ℝ[X] := fun a => if a = 6 then (1 : ℝ[X]) else 0
  have hchildren : ∀ a ∈ ([6] : List ℕ).toFinset,
      dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase a) (some a) = coefficients a := by
    intro a ha
    have hcases : a = 6 := by simpa using ha
    rcases hcases with rfl
    · change dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase 6) (some 6) = (1 : ℝ[X])
      rw [erase_0]
      exact dag_0132
  rw [dp_cons_eq_sum_of_children 6 [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] (some 3) ([6] : List ℕ).toFinset coefficients hallowed hchildren]
  norm_num [coefficients, List.toFinset_cons, List.toFinset_nil, Finset.sum_insert, Finset.sum_empty, beq_iff_eq]
  <;> ring

theorem dag_0141 :
    dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] (some 4) =
      (X : ℝ[X]) := by
  have erase_0 : ([6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).erase 6 = [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] := by decide
  have hallowed : ([6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).toFinset.filter (fun a => 0 < a ∧ a ≤ 6) = ([6] : List ℕ).toFinset := by decide
  let coefficients : ℕ → ℝ[X] := fun a => if a = 6 then (1 : ℝ[X]) else 0
  have hchildren : ∀ a ∈ ([6] : List ℕ).toFinset,
      dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase a) (some a) = coefficients a := by
    intro a ha
    have hcases : a = 6 := by simpa using ha
    rcases hcases with rfl
    · change dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase 6) (some 6) = (1 : ℝ[X])
      rw [erase_0]
      exact dag_0132
  rw [dp_cons_eq_sum_of_children 6 [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] (some 4) ([6] : List ℕ).toFinset coefficients hallowed hchildren]
  norm_num [coefficients, List.toFinset_cons, List.toFinset_nil, Finset.sum_insert, Finset.sum_empty, beq_iff_eq]
  <;> ring

theorem dag_0142 :
    dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] (some 5) =
      (X : ℝ[X]) := by
  have erase_0 : ([6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).erase 6 = [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] := by decide
  have hallowed : ([6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).toFinset.filter (fun a => 0 < a ∧ a ≤ 6) = ([6] : List ℕ).toFinset := by decide
  let coefficients : ℕ → ℝ[X] := fun a => if a = 6 then (1 : ℝ[X]) else 0
  have hchildren : ∀ a ∈ ([6] : List ℕ).toFinset,
      dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase a) (some a) = coefficients a := by
    intro a ha
    have hcases : a = 6 := by simpa using ha
    rcases hcases with rfl
    · change dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase 6) (some 6) = (1 : ℝ[X])
      rw [erase_0]
      exact dag_0132
  rw [dp_cons_eq_sum_of_children 6 [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] (some 5) ([6] : List ℕ).toFinset coefficients hallowed hchildren]
  norm_num [coefficients, List.toFinset_cons, List.toFinset_nil, Finset.sum_insert, Finset.sum_empty, beq_iff_eq]
  <;> ring

theorem dag_0143 :
    dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] (some 6) =
      (1 : ℝ[X]) := by
  have erase_0 : ([6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).erase 6 = [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] := by decide
  have hallowed : ([6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).toFinset.filter (fun a => 0 < a ∧ a ≤ 6) = ([6] : List ℕ).toFinset := by decide
  let coefficients : ℕ → ℝ[X] := fun a => if a = 6 then (1 : ℝ[X]) else 0
  have hchildren : ∀ a ∈ ([6] : List ℕ).toFinset,
      dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase a) (some a) = coefficients a := by
    intro a ha
    have hcases : a = 6 := by simpa using ha
    rcases hcases with rfl
    · change dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase 6) (some 6) = (1 : ℝ[X])
      rw [erase_0]
      exact dag_0132
  rw [dp_cons_eq_sum_of_children 6 [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] (some 6) ([6] : List ℕ).toFinset coefficients hallowed hchildren]
  norm_num [coefficients, List.toFinset_cons, List.toFinset_nil, Finset.sum_insert, Finset.sum_empty, beq_iff_eq]
  <;> ring

theorem dag_0144 :
    dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] (some 6) =
      (1 + 12 * X : ℝ[X]) := by
  have erase_0 : ([5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).erase 5 = [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] := by decide
  have erase_1 : ([5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).erase 6 = [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] := by decide
  have hallowed : ([5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).toFinset.filter (fun a => 0 < a ∧ a ≤ 6) = ([5, 6] : List ℕ).toFinset := by decide
  let coefficients : ℕ → ℝ[X] := fun a => if a = 5 then (X : ℝ[X]) else if a = 6 then (1 + 11 * X : ℝ[X]) else 0
  have hchildren : ∀ a ∈ ([5, 6] : List ℕ).toFinset,
      dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase a) (some a) = coefficients a := by
    intro a ha
    have hcases : a = 5 ∨ a = 6 := by simpa using ha
    rcases hcases with rfl | rfl
    · change dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase 5) (some 5) = (X : ℝ[X])
      rw [erase_0]
      exact dag_0131
    · change dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase 6) (some 6) = (1 + 11 * X : ℝ[X])
      rw [erase_1]
      exact dag_0133
  rw [dp_cons_eq_sum_of_children 6 [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] (some 6) ([5, 6] : List ℕ).toFinset coefficients hallowed hchildren]
  norm_num [coefficients, List.toFinset_cons, List.toFinset_nil, Finset.sum_insert, Finset.sum_empty, beq_iff_eq]
  <;> ring

theorem dag_0145 :
    dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] [4, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] (some 6) =
      (1 + 12 * X : ℝ[X]) := by
  have erase_0 : ([4, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).erase 4 = [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] := by decide
  have erase_1 : ([4, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).erase 6 = [4, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] := by decide
  have hallowed : ([4, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).toFinset.filter (fun a => 0 < a ∧ a ≤ 6) = ([4, 6] : List ℕ).toFinset := by decide
  let coefficients : ℕ → ℝ[X] := fun a => if a = 4 then (X : ℝ[X]) else if a = 6 then (1 + 11 * X : ℝ[X]) else 0
  have hchildren : ∀ a ∈ ([4, 6] : List ℕ).toFinset,
      dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([4, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase a) (some a) = coefficients a := by
    intro a ha
    have hcases : a = 4 ∨ a = 6 := by simpa using ha
    rcases hcases with rfl | rfl
    · change dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([4, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase 4) (some 4) = (X : ℝ[X])
      rw [erase_0]
      exact dag_0130
    · change dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([4, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase 6) (some 6) = (1 + 11 * X : ℝ[X])
      rw [erase_1]
      exact dag_0134
  rw [dp_cons_eq_sum_of_children 6 [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] [4, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] (some 6) ([4, 6] : List ℕ).toFinset coefficients hallowed hchildren]
  norm_num [coefficients, List.toFinset_cons, List.toFinset_nil, Finset.sum_insert, Finset.sum_empty, beq_iff_eq]
  <;> ring

theorem dag_0146 :
    dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] [3, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] (some 6) =
      (1 + 12 * X : ℝ[X]) := by
  have erase_0 : ([3, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).erase 3 = [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] := by decide
  have erase_1 : ([3, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).erase 6 = [3, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] := by decide
  have hallowed : ([3, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).toFinset.filter (fun a => 0 < a ∧ a ≤ 6) = ([3, 6] : List ℕ).toFinset := by decide
  let coefficients : ℕ → ℝ[X] := fun a => if a = 3 then (X : ℝ[X]) else if a = 6 then (1 + 11 * X : ℝ[X]) else 0
  have hchildren : ∀ a ∈ ([3, 6] : List ℕ).toFinset,
      dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([3, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase a) (some a) = coefficients a := by
    intro a ha
    have hcases : a = 3 ∨ a = 6 := by simpa using ha
    rcases hcases with rfl | rfl
    · change dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([3, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase 3) (some 3) = (X : ℝ[X])
      rw [erase_0]
      exact dag_0129
    · change dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([3, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase 6) (some 6) = (1 + 11 * X : ℝ[X])
      rw [erase_1]
      exact dag_0135
  rw [dp_cons_eq_sum_of_children 6 [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] [3, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] (some 6) ([3, 6] : List ℕ).toFinset coefficients hallowed hchildren]
  norm_num [coefficients, List.toFinset_cons, List.toFinset_nil, Finset.sum_insert, Finset.sum_empty, beq_iff_eq]
  <;> ring

theorem dag_0147 :
    dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] [2, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] (some 6) =
      (1 + 12 * X : ℝ[X]) := by
  have erase_0 : ([2, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).erase 2 = [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] := by decide
  have erase_1 : ([2, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).erase 6 = [2, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] := by decide
  have hallowed : ([2, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).toFinset.filter (fun a => 0 < a ∧ a ≤ 6) = ([2, 6] : List ℕ).toFinset := by decide
  let coefficients : ℕ → ℝ[X] := fun a => if a = 2 then (X : ℝ[X]) else if a = 6 then (1 + 11 * X : ℝ[X]) else 0
  have hchildren : ∀ a ∈ ([2, 6] : List ℕ).toFinset,
      dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([2, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase a) (some a) = coefficients a := by
    intro a ha
    have hcases : a = 2 ∨ a = 6 := by simpa using ha
    rcases hcases with rfl | rfl
    · change dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([2, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase 2) (some 2) = (X : ℝ[X])
      rw [erase_0]
      exact dag_0128
    · change dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([2, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase 6) (some 6) = (1 + 11 * X : ℝ[X])
      rw [erase_1]
      exact dag_0136
  rw [dp_cons_eq_sum_of_children 6 [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] [2, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] (some 6) ([2, 6] : List ℕ).toFinset coefficients hallowed hchildren]
  norm_num [coefficients, List.toFinset_cons, List.toFinset_nil, Finset.sum_insert, Finset.sum_empty, beq_iff_eq]
  <;> ring

theorem dag_0148 :
    dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] [1, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] (some 6) =
      (1 + 12 * X : ℝ[X]) := by
  have erase_0 : ([1, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).erase 1 = [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] := by decide
  have erase_1 : ([1, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).erase 6 = [1, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] := by decide
  have hallowed : ([1, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).toFinset.filter (fun a => 0 < a ∧ a ≤ 6) = ([1, 6] : List ℕ).toFinset := by decide
  let coefficients : ℕ → ℝ[X] := fun a => if a = 1 then (X : ℝ[X]) else if a = 6 then (1 + 11 * X : ℝ[X]) else 0
  have hchildren : ∀ a ∈ ([1, 6] : List ℕ).toFinset,
      dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([1, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase a) (some a) = coefficients a := by
    intro a ha
    have hcases : a = 1 ∨ a = 6 := by simpa using ha
    rcases hcases with rfl | rfl
    · change dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([1, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase 1) (some 1) = (X : ℝ[X])
      rw [erase_0]
      exact dag_0127
    · change dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([1, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase 6) (some 6) = (1 + 11 * X : ℝ[X])
      rw [erase_1]
      exact dag_0137
  rw [dp_cons_eq_sum_of_children 6 [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] [1, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] (some 6) ([1, 6] : List ℕ).toFinset coefficients hallowed hchildren]
  norm_num [coefficients, List.toFinset_cons, List.toFinset_nil, Finset.sum_insert, Finset.sum_empty, beq_iff_eq]
  <;> ring

theorem dag_0149 :
    dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] (some 1) =
      (X : ℝ[X]) := by
  have erase_0 : ([6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).erase 6 = [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] := by decide
  have hallowed : ([6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).toFinset.filter (fun a => 0 < a ∧ a ≤ 6) = ([6] : List ℕ).toFinset := by decide
  let coefficients : ℕ → ℝ[X] := fun a => if a = 6 then (1 : ℝ[X]) else 0
  have hchildren : ∀ a ∈ ([6] : List ℕ).toFinset,
      dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase a) (some a) = coefficients a := by
    intro a ha
    have hcases : a = 6 := by simpa using ha
    rcases hcases with rfl
    · change dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase 6) (some 6) = (1 : ℝ[X])
      rw [erase_0]
      exact dag_0143
  rw [dp_cons_eq_sum_of_children 6 [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] (some 1) ([6] : List ℕ).toFinset coefficients hallowed hchildren]
  norm_num [coefficients, List.toFinset_cons, List.toFinset_nil, Finset.sum_insert, Finset.sum_empty, beq_iff_eq]
  <;> ring

theorem dag_0150 :
    dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] (some 2) =
      (X : ℝ[X]) := by
  have erase_0 : ([6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).erase 6 = [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] := by decide
  have hallowed : ([6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).toFinset.filter (fun a => 0 < a ∧ a ≤ 6) = ([6] : List ℕ).toFinset := by decide
  let coefficients : ℕ → ℝ[X] := fun a => if a = 6 then (1 : ℝ[X]) else 0
  have hchildren : ∀ a ∈ ([6] : List ℕ).toFinset,
      dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase a) (some a) = coefficients a := by
    intro a ha
    have hcases : a = 6 := by simpa using ha
    rcases hcases with rfl
    · change dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase 6) (some 6) = (1 : ℝ[X])
      rw [erase_0]
      exact dag_0143
  rw [dp_cons_eq_sum_of_children 6 [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] (some 2) ([6] : List ℕ).toFinset coefficients hallowed hchildren]
  norm_num [coefficients, List.toFinset_cons, List.toFinset_nil, Finset.sum_insert, Finset.sum_empty, beq_iff_eq]
  <;> ring

theorem dag_0151 :
    dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] (some 3) =
      (X : ℝ[X]) := by
  have erase_0 : ([6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).erase 6 = [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] := by decide
  have hallowed : ([6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).toFinset.filter (fun a => 0 < a ∧ a ≤ 6) = ([6] : List ℕ).toFinset := by decide
  let coefficients : ℕ → ℝ[X] := fun a => if a = 6 then (1 : ℝ[X]) else 0
  have hchildren : ∀ a ∈ ([6] : List ℕ).toFinset,
      dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase a) (some a) = coefficients a := by
    intro a ha
    have hcases : a = 6 := by simpa using ha
    rcases hcases with rfl
    · change dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase 6) (some 6) = (1 : ℝ[X])
      rw [erase_0]
      exact dag_0143
  rw [dp_cons_eq_sum_of_children 6 [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] (some 3) ([6] : List ℕ).toFinset coefficients hallowed hchildren]
  norm_num [coefficients, List.toFinset_cons, List.toFinset_nil, Finset.sum_insert, Finset.sum_empty, beq_iff_eq]
  <;> ring

end D5.S3.Combinatorics.Permutation.MultisetRookEulerianCertificate.Block04
