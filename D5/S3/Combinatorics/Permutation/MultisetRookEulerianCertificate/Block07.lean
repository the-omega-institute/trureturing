/- GID: D5/S3/Combinatorics/Permutation/MultisetRookEulerianCertificate/Block07
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Permutation/MultisetRookEulerianCertificate/Block07
   mirror-E: none(waiver:exact-finite-certificate)
   anchors: []
   utility: none
   digest: Exact residual-content certificates dag_0211 through dag_0239. -/

import D5.S3.Combinatorics.Permutation.MultisetRookEulerianWordRecurrence
import D5.S3.Combinatorics.Permutation.MultisetRookEulerianCertificate.Block06

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace D5.S3.Combinatorics.Permutation.MultisetRookEulerianCertificate.Block07

open Polynomial
open D5.S3.Combinatorics.Permutation.MultisetRookEulerianWordRecurrence

theorem dag_0211 :
    dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] [4, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] (some 6) =
      (1 + 18 * X : ℝ[X]) := by
  have erase_0 : ([4, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).erase 4 = [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] := by decide
  have erase_1 : ([4, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).erase 6 = [4, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] := by decide
  have hallowed : ([4, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).toFinset.filter (fun a => 0 < a ∧ a ≤ 6) = ([4, 6] : List ℕ).toFinset := by decide
  let coefficients : ℕ → ℝ[X] := fun a => if a = 4 then (X : ℝ[X]) else if a = 6 then (1 + 17 * X : ℝ[X]) else 0
  have hchildren : ∀ a ∈ ([4, 6] : List ℕ).toFinset,
      dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([4, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase a) (some a) = coefficients a := by
    intro a ha
    have hcases : a = 4 ∨ a = 6 := by simpa using ha
    rcases hcases with rfl | rfl
    · change dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([4, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase 4) (some 4) = (X : ℝ[X])
      rw [erase_0]
      exact D5.S3.Combinatorics.Permutation.MultisetRookEulerianCertificate.Block06.dag_0196
    · change dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([4, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase 6) (some 6) = (1 + 17 * X : ℝ[X])
      rw [erase_1]
      exact D5.S3.Combinatorics.Permutation.MultisetRookEulerianCertificate.Block06.dag_0200
  rw [dp_cons_eq_sum_of_children 6 [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] [4, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] (some 6) ([4, 6] : List ℕ).toFinset coefficients hallowed hchildren]
  norm_num [coefficients, List.toFinset_cons, List.toFinset_nil, Finset.sum_insert, Finset.sum_empty, beq_iff_eq]
  <;> ring

theorem dag_0212 :
    dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] [3, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] (some 6) =
      (1 + 18 * X : ℝ[X]) := by
  have erase_0 : ([3, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).erase 3 = [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] := by decide
  have erase_1 : ([3, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).erase 6 = [3, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] := by decide
  have hallowed : ([3, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).toFinset.filter (fun a => 0 < a ∧ a ≤ 6) = ([3, 6] : List ℕ).toFinset := by decide
  let coefficients : ℕ → ℝ[X] := fun a => if a = 3 then (X : ℝ[X]) else if a = 6 then (1 + 17 * X : ℝ[X]) else 0
  have hchildren : ∀ a ∈ ([3, 6] : List ℕ).toFinset,
      dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([3, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase a) (some a) = coefficients a := by
    intro a ha
    have hcases : a = 3 ∨ a = 6 := by simpa using ha
    rcases hcases with rfl | rfl
    · change dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([3, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase 3) (some 3) = (X : ℝ[X])
      rw [erase_0]
      exact D5.S3.Combinatorics.Permutation.MultisetRookEulerianCertificate.Block06.dag_0195
    · change dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([3, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase 6) (some 6) = (1 + 17 * X : ℝ[X])
      rw [erase_1]
      exact D5.S3.Combinatorics.Permutation.MultisetRookEulerianCertificate.Block06.dag_0201
  rw [dp_cons_eq_sum_of_children 6 [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] [3, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] (some 6) ([3, 6] : List ℕ).toFinset coefficients hallowed hchildren]
  norm_num [coefficients, List.toFinset_cons, List.toFinset_nil, Finset.sum_insert, Finset.sum_empty, beq_iff_eq]
  <;> ring

theorem dag_0213 :
    dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] [2, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] (some 6) =
      (1 + 18 * X : ℝ[X]) := by
  have erase_0 : ([2, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).erase 2 = [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] := by decide
  have erase_1 : ([2, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).erase 6 = [2, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] := by decide
  have hallowed : ([2, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).toFinset.filter (fun a => 0 < a ∧ a ≤ 6) = ([2, 6] : List ℕ).toFinset := by decide
  let coefficients : ℕ → ℝ[X] := fun a => if a = 2 then (X : ℝ[X]) else if a = 6 then (1 + 17 * X : ℝ[X]) else 0
  have hchildren : ∀ a ∈ ([2, 6] : List ℕ).toFinset,
      dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([2, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase a) (some a) = coefficients a := by
    intro a ha
    have hcases : a = 2 ∨ a = 6 := by simpa using ha
    rcases hcases with rfl | rfl
    · change dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([2, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase 2) (some 2) = (X : ℝ[X])
      rw [erase_0]
      exact D5.S3.Combinatorics.Permutation.MultisetRookEulerianCertificate.Block06.dag_0194
    · change dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([2, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase 6) (some 6) = (1 + 17 * X : ℝ[X])
      rw [erase_1]
      exact D5.S3.Combinatorics.Permutation.MultisetRookEulerianCertificate.Block06.dag_0202
  rw [dp_cons_eq_sum_of_children 6 [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] [2, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] (some 6) ([2, 6] : List ℕ).toFinset coefficients hallowed hchildren]
  norm_num [coefficients, List.toFinset_cons, List.toFinset_nil, Finset.sum_insert, Finset.sum_empty, beq_iff_eq]
  <;> ring

theorem dag_0214 :
    dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] [1, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] (some 6) =
      (1 + 18 * X : ℝ[X]) := by
  have erase_0 : ([1, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).erase 1 = [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] := by decide
  have erase_1 : ([1, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).erase 6 = [1, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] := by decide
  have hallowed : ([1, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).toFinset.filter (fun a => 0 < a ∧ a ≤ 6) = ([1, 6] : List ℕ).toFinset := by decide
  let coefficients : ℕ → ℝ[X] := fun a => if a = 1 then (X : ℝ[X]) else if a = 6 then (1 + 17 * X : ℝ[X]) else 0
  have hchildren : ∀ a ∈ ([1, 6] : List ℕ).toFinset,
      dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([1, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase a) (some a) = coefficients a := by
    intro a ha
    have hcases : a = 1 ∨ a = 6 := by simpa using ha
    rcases hcases with rfl | rfl
    · change dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([1, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase 1) (some 1) = (X : ℝ[X])
      rw [erase_0]
      exact D5.S3.Combinatorics.Permutation.MultisetRookEulerianCertificate.Block06.dag_0193
    · change dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([1, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase 6) (some 6) = (1 + 17 * X : ℝ[X])
      rw [erase_1]
      exact D5.S3.Combinatorics.Permutation.MultisetRookEulerianCertificate.Block06.dag_0203
  rw [dp_cons_eq_sum_of_children 6 [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] [1, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] (some 6) ([1, 6] : List ℕ).toFinset coefficients hallowed hchildren]
  norm_num [coefficients, List.toFinset_cons, List.toFinset_nil, Finset.sum_insert, Finset.sum_empty, beq_iff_eq]
  <;> ring

theorem dag_0215 :
    dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] (some 1) =
      (X : ℝ[X]) := by
  have erase_0 : ([6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).erase 6 = [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] := by decide
  have hallowed : ([6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).toFinset.filter (fun a => 0 < a ∧ a ≤ 6) = ([6] : List ℕ).toFinset := by decide
  let coefficients : ℕ → ℝ[X] := fun a => if a = 6 then (1 : ℝ[X]) else 0
  have hchildren : ∀ a ∈ ([6] : List ℕ).toFinset,
      dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase a) (some a) = coefficients a := by
    intro a ha
    have hcases : a = 6 := by simpa using ha
    rcases hcases with rfl
    · change dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase 6) (some 6) = (1 : ℝ[X])
      rw [erase_0]
      exact D5.S3.Combinatorics.Permutation.MultisetRookEulerianCertificate.Block06.dag_0209
  rw [dp_cons_eq_sum_of_children 6 [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] (some 1) ([6] : List ℕ).toFinset coefficients hallowed hchildren]
  norm_num [coefficients, List.toFinset_cons, List.toFinset_nil, Finset.sum_insert, Finset.sum_empty, beq_iff_eq]
  <;> ring

theorem dag_0216 :
    dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] (some 2) =
      (X : ℝ[X]) := by
  have erase_0 : ([6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).erase 6 = [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] := by decide
  have hallowed : ([6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).toFinset.filter (fun a => 0 < a ∧ a ≤ 6) = ([6] : List ℕ).toFinset := by decide
  let coefficients : ℕ → ℝ[X] := fun a => if a = 6 then (1 : ℝ[X]) else 0
  have hchildren : ∀ a ∈ ([6] : List ℕ).toFinset,
      dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase a) (some a) = coefficients a := by
    intro a ha
    have hcases : a = 6 := by simpa using ha
    rcases hcases with rfl
    · change dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase 6) (some 6) = (1 : ℝ[X])
      rw [erase_0]
      exact D5.S3.Combinatorics.Permutation.MultisetRookEulerianCertificate.Block06.dag_0209
  rw [dp_cons_eq_sum_of_children 6 [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] (some 2) ([6] : List ℕ).toFinset coefficients hallowed hchildren]
  norm_num [coefficients, List.toFinset_cons, List.toFinset_nil, Finset.sum_insert, Finset.sum_empty, beq_iff_eq]
  <;> ring

theorem dag_0217 :
    dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] (some 3) =
      (X : ℝ[X]) := by
  have erase_0 : ([6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).erase 6 = [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] := by decide
  have hallowed : ([6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).toFinset.filter (fun a => 0 < a ∧ a ≤ 6) = ([6] : List ℕ).toFinset := by decide
  let coefficients : ℕ → ℝ[X] := fun a => if a = 6 then (1 : ℝ[X]) else 0
  have hchildren : ∀ a ∈ ([6] : List ℕ).toFinset,
      dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase a) (some a) = coefficients a := by
    intro a ha
    have hcases : a = 6 := by simpa using ha
    rcases hcases with rfl
    · change dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase 6) (some 6) = (1 : ℝ[X])
      rw [erase_0]
      exact D5.S3.Combinatorics.Permutation.MultisetRookEulerianCertificate.Block06.dag_0209
  rw [dp_cons_eq_sum_of_children 6 [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] (some 3) ([6] : List ℕ).toFinset coefficients hallowed hchildren]
  norm_num [coefficients, List.toFinset_cons, List.toFinset_nil, Finset.sum_insert, Finset.sum_empty, beq_iff_eq]
  <;> ring

theorem dag_0218 :
    dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] (some 4) =
      (X : ℝ[X]) := by
  have erase_0 : ([6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).erase 6 = [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] := by decide
  have hallowed : ([6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).toFinset.filter (fun a => 0 < a ∧ a ≤ 6) = ([6] : List ℕ).toFinset := by decide
  let coefficients : ℕ → ℝ[X] := fun a => if a = 6 then (1 : ℝ[X]) else 0
  have hchildren : ∀ a ∈ ([6] : List ℕ).toFinset,
      dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase a) (some a) = coefficients a := by
    intro a ha
    have hcases : a = 6 := by simpa using ha
    rcases hcases with rfl
    · change dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase 6) (some 6) = (1 : ℝ[X])
      rw [erase_0]
      exact D5.S3.Combinatorics.Permutation.MultisetRookEulerianCertificate.Block06.dag_0209
  rw [dp_cons_eq_sum_of_children 6 [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] (some 4) ([6] : List ℕ).toFinset coefficients hallowed hchildren]
  norm_num [coefficients, List.toFinset_cons, List.toFinset_nil, Finset.sum_insert, Finset.sum_empty, beq_iff_eq]
  <;> ring

theorem dag_0219 :
    dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] (some 5) =
      (X : ℝ[X]) := by
  have erase_0 : ([6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).erase 6 = [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] := by decide
  have hallowed : ([6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).toFinset.filter (fun a => 0 < a ∧ a ≤ 6) = ([6] : List ℕ).toFinset := by decide
  let coefficients : ℕ → ℝ[X] := fun a => if a = 6 then (1 : ℝ[X]) else 0
  have hchildren : ∀ a ∈ ([6] : List ℕ).toFinset,
      dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase a) (some a) = coefficients a := by
    intro a ha
    have hcases : a = 6 := by simpa using ha
    rcases hcases with rfl
    · change dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase 6) (some 6) = (1 : ℝ[X])
      rw [erase_0]
      exact D5.S3.Combinatorics.Permutation.MultisetRookEulerianCertificate.Block06.dag_0209
  rw [dp_cons_eq_sum_of_children 6 [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] (some 5) ([6] : List ℕ).toFinset coefficients hallowed hchildren]
  norm_num [coefficients, List.toFinset_cons, List.toFinset_nil, Finset.sum_insert, Finset.sum_empty, beq_iff_eq]
  <;> ring

theorem dag_0220 :
    dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] (some 6) =
      (1 : ℝ[X]) := by
  have erase_0 : ([6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).erase 6 = [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] := by decide
  have hallowed : ([6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).toFinset.filter (fun a => 0 < a ∧ a ≤ 6) = ([6] : List ℕ).toFinset := by decide
  let coefficients : ℕ → ℝ[X] := fun a => if a = 6 then (1 : ℝ[X]) else 0
  have hchildren : ∀ a ∈ ([6] : List ℕ).toFinset,
      dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase a) (some a) = coefficients a := by
    intro a ha
    have hcases : a = 6 := by simpa using ha
    rcases hcases with rfl
    · change dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase 6) (some 6) = (1 : ℝ[X])
      rw [erase_0]
      exact D5.S3.Combinatorics.Permutation.MultisetRookEulerianCertificate.Block06.dag_0209
  rw [dp_cons_eq_sum_of_children 6 [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] (some 6) ([6] : List ℕ).toFinset coefficients hallowed hchildren]
  norm_num [coefficients, List.toFinset_cons, List.toFinset_nil, Finset.sum_insert, Finset.sum_empty, beq_iff_eq]
  <;> ring

theorem dag_0221 :
    dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] (some 6) =
      (1 + 19 * X : ℝ[X]) := by
  have erase_0 : ([5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).erase 5 = [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] := by decide
  have erase_1 : ([5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).erase 6 = [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] := by decide
  have hallowed : ([5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).toFinset.filter (fun a => 0 < a ∧ a ≤ 6) = ([5, 6] : List ℕ).toFinset := by decide
  let coefficients : ℕ → ℝ[X] := fun a => if a = 5 then (X : ℝ[X]) else if a = 6 then (1 + 18 * X : ℝ[X]) else 0
  have hchildren : ∀ a ∈ ([5, 6] : List ℕ).toFinset,
      dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase a) (some a) = coefficients a := by
    intro a ha
    have hcases : a = 5 ∨ a = 6 := by simpa using ha
    rcases hcases with rfl | rfl
    · change dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase 5) (some 5) = (X : ℝ[X])
      rw [erase_0]
      exact D5.S3.Combinatorics.Permutation.MultisetRookEulerianCertificate.Block06.dag_0208
    · change dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase 6) (some 6) = (1 + 18 * X : ℝ[X])
      rw [erase_1]
      exact D5.S3.Combinatorics.Permutation.MultisetRookEulerianCertificate.Block06.dag_0210
  rw [dp_cons_eq_sum_of_children 6 [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] (some 6) ([5, 6] : List ℕ).toFinset coefficients hallowed hchildren]
  norm_num [coefficients, List.toFinset_cons, List.toFinset_nil, Finset.sum_insert, Finset.sum_empty, beq_iff_eq]
  <;> ring

theorem dag_0222 :
    dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] [4, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] (some 6) =
      (1 + 19 * X : ℝ[X]) := by
  have erase_0 : ([4, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).erase 4 = [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] := by decide
  have erase_1 : ([4, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).erase 6 = [4, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] := by decide
  have hallowed : ([4, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).toFinset.filter (fun a => 0 < a ∧ a ≤ 6) = ([4, 6] : List ℕ).toFinset := by decide
  let coefficients : ℕ → ℝ[X] := fun a => if a = 4 then (X : ℝ[X]) else if a = 6 then (1 + 18 * X : ℝ[X]) else 0
  have hchildren : ∀ a ∈ ([4, 6] : List ℕ).toFinset,
      dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([4, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase a) (some a) = coefficients a := by
    intro a ha
    have hcases : a = 4 ∨ a = 6 := by simpa using ha
    rcases hcases with rfl | rfl
    · change dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([4, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase 4) (some 4) = (X : ℝ[X])
      rw [erase_0]
      exact D5.S3.Combinatorics.Permutation.MultisetRookEulerianCertificate.Block06.dag_0207
    · change dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([4, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase 6) (some 6) = (1 + 18 * X : ℝ[X])
      rw [erase_1]
      exact dag_0211
  rw [dp_cons_eq_sum_of_children 6 [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] [4, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] (some 6) ([4, 6] : List ℕ).toFinset coefficients hallowed hchildren]
  norm_num [coefficients, List.toFinset_cons, List.toFinset_nil, Finset.sum_insert, Finset.sum_empty, beq_iff_eq]
  <;> ring

theorem dag_0223 :
    dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] [3, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] (some 6) =
      (1 + 19 * X : ℝ[X]) := by
  have erase_0 : ([3, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).erase 3 = [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] := by decide
  have erase_1 : ([3, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).erase 6 = [3, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] := by decide
  have hallowed : ([3, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).toFinset.filter (fun a => 0 < a ∧ a ≤ 6) = ([3, 6] : List ℕ).toFinset := by decide
  let coefficients : ℕ → ℝ[X] := fun a => if a = 3 then (X : ℝ[X]) else if a = 6 then (1 + 18 * X : ℝ[X]) else 0
  have hchildren : ∀ a ∈ ([3, 6] : List ℕ).toFinset,
      dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([3, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase a) (some a) = coefficients a := by
    intro a ha
    have hcases : a = 3 ∨ a = 6 := by simpa using ha
    rcases hcases with rfl | rfl
    · change dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([3, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase 3) (some 3) = (X : ℝ[X])
      rw [erase_0]
      exact D5.S3.Combinatorics.Permutation.MultisetRookEulerianCertificate.Block06.dag_0206
    · change dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([3, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase 6) (some 6) = (1 + 18 * X : ℝ[X])
      rw [erase_1]
      exact dag_0212
  rw [dp_cons_eq_sum_of_children 6 [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] [3, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] (some 6) ([3, 6] : List ℕ).toFinset coefficients hallowed hchildren]
  norm_num [coefficients, List.toFinset_cons, List.toFinset_nil, Finset.sum_insert, Finset.sum_empty, beq_iff_eq]
  <;> ring

theorem dag_0224 :
    dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] [2, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] (some 6) =
      (1 + 19 * X : ℝ[X]) := by
  have erase_0 : ([2, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).erase 2 = [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] := by decide
  have erase_1 : ([2, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).erase 6 = [2, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] := by decide
  have hallowed : ([2, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).toFinset.filter (fun a => 0 < a ∧ a ≤ 6) = ([2, 6] : List ℕ).toFinset := by decide
  let coefficients : ℕ → ℝ[X] := fun a => if a = 2 then (X : ℝ[X]) else if a = 6 then (1 + 18 * X : ℝ[X]) else 0
  have hchildren : ∀ a ∈ ([2, 6] : List ℕ).toFinset,
      dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([2, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase a) (some a) = coefficients a := by
    intro a ha
    have hcases : a = 2 ∨ a = 6 := by simpa using ha
    rcases hcases with rfl | rfl
    · change dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([2, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase 2) (some 2) = (X : ℝ[X])
      rw [erase_0]
      exact D5.S3.Combinatorics.Permutation.MultisetRookEulerianCertificate.Block06.dag_0205
    · change dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([2, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase 6) (some 6) = (1 + 18 * X : ℝ[X])
      rw [erase_1]
      exact dag_0213
  rw [dp_cons_eq_sum_of_children 6 [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] [2, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] (some 6) ([2, 6] : List ℕ).toFinset coefficients hallowed hchildren]
  norm_num [coefficients, List.toFinset_cons, List.toFinset_nil, Finset.sum_insert, Finset.sum_empty, beq_iff_eq]
  <;> ring

theorem dag_0225 :
    dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] [1, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] (some 6) =
      (1 + 19 * X : ℝ[X]) := by
  have erase_0 : ([1, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).erase 1 = [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] := by decide
  have erase_1 : ([1, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).erase 6 = [1, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] := by decide
  have hallowed : ([1, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).toFinset.filter (fun a => 0 < a ∧ a ≤ 6) = ([1, 6] : List ℕ).toFinset := by decide
  let coefficients : ℕ → ℝ[X] := fun a => if a = 1 then (X : ℝ[X]) else if a = 6 then (1 + 18 * X : ℝ[X]) else 0
  have hchildren : ∀ a ∈ ([1, 6] : List ℕ).toFinset,
      dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([1, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase a) (some a) = coefficients a := by
    intro a ha
    have hcases : a = 1 ∨ a = 6 := by simpa using ha
    rcases hcases with rfl | rfl
    · change dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([1, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase 1) (some 1) = (X : ℝ[X])
      rw [erase_0]
      exact D5.S3.Combinatorics.Permutation.MultisetRookEulerianCertificate.Block06.dag_0204
    · change dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([1, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase 6) (some 6) = (1 + 18 * X : ℝ[X])
      rw [erase_1]
      exact dag_0214
  rw [dp_cons_eq_sum_of_children 6 [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] [1, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] (some 6) ([1, 6] : List ℕ).toFinset coefficients hallowed hchildren]
  norm_num [coefficients, List.toFinset_cons, List.toFinset_nil, Finset.sum_insert, Finset.sum_empty, beq_iff_eq]
  <;> ring

theorem dag_0226 :
    dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] (some 1) =
      (X : ℝ[X]) := by
  have erase_0 : ([6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).erase 6 = [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] := by decide
  have hallowed : ([6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).toFinset.filter (fun a => 0 < a ∧ a ≤ 6) = ([6] : List ℕ).toFinset := by decide
  let coefficients : ℕ → ℝ[X] := fun a => if a = 6 then (1 : ℝ[X]) else 0
  have hchildren : ∀ a ∈ ([6] : List ℕ).toFinset,
      dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase a) (some a) = coefficients a := by
    intro a ha
    have hcases : a = 6 := by simpa using ha
    rcases hcases with rfl
    · change dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase 6) (some 6) = (1 : ℝ[X])
      rw [erase_0]
      exact dag_0220
  rw [dp_cons_eq_sum_of_children 6 [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] (some 1) ([6] : List ℕ).toFinset coefficients hallowed hchildren]
  norm_num [coefficients, List.toFinset_cons, List.toFinset_nil, Finset.sum_insert, Finset.sum_empty, beq_iff_eq]
  <;> ring

theorem dag_0227 :
    dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] (some 2) =
      (X : ℝ[X]) := by
  have erase_0 : ([6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).erase 6 = [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] := by decide
  have hallowed : ([6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).toFinset.filter (fun a => 0 < a ∧ a ≤ 6) = ([6] : List ℕ).toFinset := by decide
  let coefficients : ℕ → ℝ[X] := fun a => if a = 6 then (1 : ℝ[X]) else 0
  have hchildren : ∀ a ∈ ([6] : List ℕ).toFinset,
      dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase a) (some a) = coefficients a := by
    intro a ha
    have hcases : a = 6 := by simpa using ha
    rcases hcases with rfl
    · change dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase 6) (some 6) = (1 : ℝ[X])
      rw [erase_0]
      exact dag_0220
  rw [dp_cons_eq_sum_of_children 6 [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] (some 2) ([6] : List ℕ).toFinset coefficients hallowed hchildren]
  norm_num [coefficients, List.toFinset_cons, List.toFinset_nil, Finset.sum_insert, Finset.sum_empty, beq_iff_eq]
  <;> ring

theorem dag_0228 :
    dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] (some 3) =
      (X : ℝ[X]) := by
  have erase_0 : ([6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).erase 6 = [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] := by decide
  have hallowed : ([6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).toFinset.filter (fun a => 0 < a ∧ a ≤ 6) = ([6] : List ℕ).toFinset := by decide
  let coefficients : ℕ → ℝ[X] := fun a => if a = 6 then (1 : ℝ[X]) else 0
  have hchildren : ∀ a ∈ ([6] : List ℕ).toFinset,
      dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase a) (some a) = coefficients a := by
    intro a ha
    have hcases : a = 6 := by simpa using ha
    rcases hcases with rfl
    · change dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase 6) (some 6) = (1 : ℝ[X])
      rw [erase_0]
      exact dag_0220
  rw [dp_cons_eq_sum_of_children 6 [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] (some 3) ([6] : List ℕ).toFinset coefficients hallowed hchildren]
  norm_num [coefficients, List.toFinset_cons, List.toFinset_nil, Finset.sum_insert, Finset.sum_empty, beq_iff_eq]
  <;> ring

theorem dag_0229 :
    dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] (some 4) =
      (X : ℝ[X]) := by
  have erase_0 : ([6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).erase 6 = [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] := by decide
  have hallowed : ([6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).toFinset.filter (fun a => 0 < a ∧ a ≤ 6) = ([6] : List ℕ).toFinset := by decide
  let coefficients : ℕ → ℝ[X] := fun a => if a = 6 then (1 : ℝ[X]) else 0
  have hchildren : ∀ a ∈ ([6] : List ℕ).toFinset,
      dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase a) (some a) = coefficients a := by
    intro a ha
    have hcases : a = 6 := by simpa using ha
    rcases hcases with rfl
    · change dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase 6) (some 6) = (1 : ℝ[X])
      rw [erase_0]
      exact dag_0220
  rw [dp_cons_eq_sum_of_children 6 [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] (some 4) ([6] : List ℕ).toFinset coefficients hallowed hchildren]
  norm_num [coefficients, List.toFinset_cons, List.toFinset_nil, Finset.sum_insert, Finset.sum_empty, beq_iff_eq]
  <;> ring

theorem dag_0230 :
    dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] (some 5) =
      (X : ℝ[X]) := by
  have erase_0 : ([6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).erase 6 = [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] := by decide
  have hallowed : ([6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).toFinset.filter (fun a => 0 < a ∧ a ≤ 6) = ([6] : List ℕ).toFinset := by decide
  let coefficients : ℕ → ℝ[X] := fun a => if a = 6 then (1 : ℝ[X]) else 0
  have hchildren : ∀ a ∈ ([6] : List ℕ).toFinset,
      dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase a) (some a) = coefficients a := by
    intro a ha
    have hcases : a = 6 := by simpa using ha
    rcases hcases with rfl
    · change dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase 6) (some 6) = (1 : ℝ[X])
      rw [erase_0]
      exact dag_0220
  rw [dp_cons_eq_sum_of_children 6 [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] (some 5) ([6] : List ℕ).toFinset coefficients hallowed hchildren]
  norm_num [coefficients, List.toFinset_cons, List.toFinset_nil, Finset.sum_insert, Finset.sum_empty, beq_iff_eq]
  <;> ring

theorem dag_0231 :
    dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] (some 6) =
      (1 : ℝ[X]) := by
  have erase_0 : ([6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).erase 6 = [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] := by decide
  have hallowed : ([6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).toFinset.filter (fun a => 0 < a ∧ a ≤ 6) = ([6] : List ℕ).toFinset := by decide
  let coefficients : ℕ → ℝ[X] := fun a => if a = 6 then (1 : ℝ[X]) else 0
  have hchildren : ∀ a ∈ ([6] : List ℕ).toFinset,
      dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase a) (some a) = coefficients a := by
    intro a ha
    have hcases : a = 6 := by simpa using ha
    rcases hcases with rfl
    · change dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase 6) (some 6) = (1 : ℝ[X])
      rw [erase_0]
      exact dag_0220
  rw [dp_cons_eq_sum_of_children 6 [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] (some 6) ([6] : List ℕ).toFinset coefficients hallowed hchildren]
  norm_num [coefficients, List.toFinset_cons, List.toFinset_nil, Finset.sum_insert, Finset.sum_empty, beq_iff_eq]
  <;> ring

theorem dag_0232 :
    dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] (some 6) =
      (1 + 20 * X : ℝ[X]) := by
  have erase_0 : ([5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).erase 5 = [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] := by decide
  have erase_1 : ([5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).erase 6 = [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] := by decide
  have hallowed : ([5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).toFinset.filter (fun a => 0 < a ∧ a ≤ 6) = ([5, 6] : List ℕ).toFinset := by decide
  let coefficients : ℕ → ℝ[X] := fun a => if a = 5 then (X : ℝ[X]) else if a = 6 then (1 + 19 * X : ℝ[X]) else 0
  have hchildren : ∀ a ∈ ([5, 6] : List ℕ).toFinset,
      dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase a) (some a) = coefficients a := by
    intro a ha
    have hcases : a = 5 ∨ a = 6 := by simpa using ha
    rcases hcases with rfl | rfl
    · change dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase 5) (some 5) = (X : ℝ[X])
      rw [erase_0]
      exact dag_0219
    · change dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase 6) (some 6) = (1 + 19 * X : ℝ[X])
      rw [erase_1]
      exact dag_0221
  rw [dp_cons_eq_sum_of_children 6 [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] (some 6) ([5, 6] : List ℕ).toFinset coefficients hallowed hchildren]
  norm_num [coefficients, List.toFinset_cons, List.toFinset_nil, Finset.sum_insert, Finset.sum_empty, beq_iff_eq]
  <;> ring

theorem dag_0233 :
    dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] [4, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] (some 6) =
      (1 + 20 * X : ℝ[X]) := by
  have erase_0 : ([4, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).erase 4 = [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] := by decide
  have erase_1 : ([4, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).erase 6 = [4, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] := by decide
  have hallowed : ([4, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).toFinset.filter (fun a => 0 < a ∧ a ≤ 6) = ([4, 6] : List ℕ).toFinset := by decide
  let coefficients : ℕ → ℝ[X] := fun a => if a = 4 then (X : ℝ[X]) else if a = 6 then (1 + 19 * X : ℝ[X]) else 0
  have hchildren : ∀ a ∈ ([4, 6] : List ℕ).toFinset,
      dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([4, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase a) (some a) = coefficients a := by
    intro a ha
    have hcases : a = 4 ∨ a = 6 := by simpa using ha
    rcases hcases with rfl | rfl
    · change dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([4, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase 4) (some 4) = (X : ℝ[X])
      rw [erase_0]
      exact dag_0218
    · change dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([4, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase 6) (some 6) = (1 + 19 * X : ℝ[X])
      rw [erase_1]
      exact dag_0222
  rw [dp_cons_eq_sum_of_children 6 [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] [4, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] (some 6) ([4, 6] : List ℕ).toFinset coefficients hallowed hchildren]
  norm_num [coefficients, List.toFinset_cons, List.toFinset_nil, Finset.sum_insert, Finset.sum_empty, beq_iff_eq]
  <;> ring

theorem dag_0234 :
    dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] [3, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] (some 6) =
      (1 + 20 * X : ℝ[X]) := by
  have erase_0 : ([3, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).erase 3 = [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] := by decide
  have erase_1 : ([3, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).erase 6 = [3, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] := by decide
  have hallowed : ([3, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).toFinset.filter (fun a => 0 < a ∧ a ≤ 6) = ([3, 6] : List ℕ).toFinset := by decide
  let coefficients : ℕ → ℝ[X] := fun a => if a = 3 then (X : ℝ[X]) else if a = 6 then (1 + 19 * X : ℝ[X]) else 0
  have hchildren : ∀ a ∈ ([3, 6] : List ℕ).toFinset,
      dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([3, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase a) (some a) = coefficients a := by
    intro a ha
    have hcases : a = 3 ∨ a = 6 := by simpa using ha
    rcases hcases with rfl | rfl
    · change dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([3, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase 3) (some 3) = (X : ℝ[X])
      rw [erase_0]
      exact dag_0217
    · change dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([3, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase 6) (some 6) = (1 + 19 * X : ℝ[X])
      rw [erase_1]
      exact dag_0223
  rw [dp_cons_eq_sum_of_children 6 [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] [3, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] (some 6) ([3, 6] : List ℕ).toFinset coefficients hallowed hchildren]
  norm_num [coefficients, List.toFinset_cons, List.toFinset_nil, Finset.sum_insert, Finset.sum_empty, beq_iff_eq]
  <;> ring

theorem dag_0235 :
    dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] [2, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] (some 6) =
      (1 + 20 * X : ℝ[X]) := by
  have erase_0 : ([2, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).erase 2 = [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] := by decide
  have erase_1 : ([2, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).erase 6 = [2, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] := by decide
  have hallowed : ([2, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).toFinset.filter (fun a => 0 < a ∧ a ≤ 6) = ([2, 6] : List ℕ).toFinset := by decide
  let coefficients : ℕ → ℝ[X] := fun a => if a = 2 then (X : ℝ[X]) else if a = 6 then (1 + 19 * X : ℝ[X]) else 0
  have hchildren : ∀ a ∈ ([2, 6] : List ℕ).toFinset,
      dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([2, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase a) (some a) = coefficients a := by
    intro a ha
    have hcases : a = 2 ∨ a = 6 := by simpa using ha
    rcases hcases with rfl | rfl
    · change dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([2, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase 2) (some 2) = (X : ℝ[X])
      rw [erase_0]
      exact dag_0216
    · change dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([2, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase 6) (some 6) = (1 + 19 * X : ℝ[X])
      rw [erase_1]
      exact dag_0224
  rw [dp_cons_eq_sum_of_children 6 [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] [2, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] (some 6) ([2, 6] : List ℕ).toFinset coefficients hallowed hchildren]
  norm_num [coefficients, List.toFinset_cons, List.toFinset_nil, Finset.sum_insert, Finset.sum_empty, beq_iff_eq]
  <;> ring

theorem dag_0236 :
    dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] [1, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] (some 6) =
      (1 + 20 * X : ℝ[X]) := by
  have erase_0 : ([1, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).erase 1 = [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] := by decide
  have erase_1 : ([1, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).erase 6 = [1, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] := by decide
  have hallowed : ([1, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).toFinset.filter (fun a => 0 < a ∧ a ≤ 6) = ([1, 6] : List ℕ).toFinset := by decide
  let coefficients : ℕ → ℝ[X] := fun a => if a = 1 then (X : ℝ[X]) else if a = 6 then (1 + 19 * X : ℝ[X]) else 0
  have hchildren : ∀ a ∈ ([1, 6] : List ℕ).toFinset,
      dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([1, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase a) (some a) = coefficients a := by
    intro a ha
    have hcases : a = 1 ∨ a = 6 := by simpa using ha
    rcases hcases with rfl | rfl
    · change dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([1, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase 1) (some 1) = (X : ℝ[X])
      rw [erase_0]
      exact dag_0215
    · change dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([1, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase 6) (some 6) = (1 + 19 * X : ℝ[X])
      rw [erase_1]
      exact dag_0225
  rw [dp_cons_eq_sum_of_children 6 [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] [1, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] (some 6) ([1, 6] : List ℕ).toFinset coefficients hallowed hchildren]
  norm_num [coefficients, List.toFinset_cons, List.toFinset_nil, Finset.sum_insert, Finset.sum_empty, beq_iff_eq]
  <;> ring

theorem dag_0237 :
    dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] (some 1) =
      (X : ℝ[X]) := by
  have erase_0 : ([6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).erase 6 = [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] := by decide
  have hallowed : ([6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).toFinset.filter (fun a => 0 < a ∧ a ≤ 6) = ([6] : List ℕ).toFinset := by decide
  let coefficients : ℕ → ℝ[X] := fun a => if a = 6 then (1 : ℝ[X]) else 0
  have hchildren : ∀ a ∈ ([6] : List ℕ).toFinset,
      dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase a) (some a) = coefficients a := by
    intro a ha
    have hcases : a = 6 := by simpa using ha
    rcases hcases with rfl
    · change dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase 6) (some 6) = (1 : ℝ[X])
      rw [erase_0]
      exact dag_0231
  rw [dp_cons_eq_sum_of_children 6 [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] (some 1) ([6] : List ℕ).toFinset coefficients hallowed hchildren]
  norm_num [coefficients, List.toFinset_cons, List.toFinset_nil, Finset.sum_insert, Finset.sum_empty, beq_iff_eq]
  <;> ring

theorem dag_0238 :
    dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] (some 2) =
      (X : ℝ[X]) := by
  have erase_0 : ([6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).erase 6 = [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] := by decide
  have hallowed : ([6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).toFinset.filter (fun a => 0 < a ∧ a ≤ 6) = ([6] : List ℕ).toFinset := by decide
  let coefficients : ℕ → ℝ[X] := fun a => if a = 6 then (1 : ℝ[X]) else 0
  have hchildren : ∀ a ∈ ([6] : List ℕ).toFinset,
      dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase a) (some a) = coefficients a := by
    intro a ha
    have hcases : a = 6 := by simpa using ha
    rcases hcases with rfl
    · change dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase 6) (some 6) = (1 : ℝ[X])
      rw [erase_0]
      exact dag_0231
  rw [dp_cons_eq_sum_of_children 6 [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] (some 2) ([6] : List ℕ).toFinset coefficients hallowed hchildren]
  norm_num [coefficients, List.toFinset_cons, List.toFinset_nil, Finset.sum_insert, Finset.sum_empty, beq_iff_eq]
  <;> ring

theorem dag_0239 :
    dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] (some 3) =
      (X : ℝ[X]) := by
  have erase_0 : ([6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).erase 6 = [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] := by decide
  have hallowed : ([6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ).toFinset.filter (fun a => 0 < a ∧ a ≤ 6) = ([6] : List ℕ).toFinset := by decide
  let coefficients : ℕ → ℝ[X] := fun a => if a = 6 then (1 : ℝ[X]) else 0
  have hchildren : ∀ a ∈ ([6] : List ℕ).toFinset,
      dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase a) (some a) = coefficients a := by
    intro a ha
    have hcases : a = 6 := by simpa using ha
    rcases hcases with rfl
    · change dp [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ([6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6].erase 6) (some 6) = (1 : ℝ[X])
      rw [erase_0]
      exact dag_0231
  rw [dp_cons_eq_sum_of_children 6 [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] (some 3) ([6] : List ℕ).toFinset coefficients hallowed hchildren]
  norm_num [coefficients, List.toFinset_cons, List.toFinset_nil, Finset.sum_insert, Finset.sum_empty, beq_iff_eq]
  <;> ring

end D5.S3.Combinatorics.Permutation.MultisetRookEulerianCertificate.Block07
