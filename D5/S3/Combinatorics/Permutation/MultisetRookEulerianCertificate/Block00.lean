/- GID: D5/S3/Combinatorics/Permutation/MultisetRookEulerianCertificate/Block00
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Permutation/MultisetRookEulerianCertificate/Block00
   mirror-E: none(waiver:exact-finite-certificate)
   anchors: []
   utility: none
   digest: Exact residual-content certificates dag_0000 through dag_0034. -/

import D5.S3.Combinatorics.Permutation.MultisetRookEulerianWordRecurrence

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace D5.S3.Combinatorics.Permutation.MultisetRookEulerianCertificate.Block00

open Polynomial
open D5.S3.Combinatorics.Permutation.MultisetRookEulerianWordRecurrence

theorem dag_0000 :
    dp [] [] (some 1) =
      (1 : ℝ[X]) := by
  rfl

theorem dag_0001 :
    dp [] [] (some 2) =
      (1 : ℝ[X]) := by
  rfl

theorem dag_0002 :
    dp [] [] (some 3) =
      (1 : ℝ[X]) := by
  rfl

theorem dag_0003 :
    dp [] [] (some 4) =
      (1 : ℝ[X]) := by
  rfl

theorem dag_0004 :
    dp [] [] (some 5) =
      (1 : ℝ[X]) := by
  rfl

theorem dag_0005 :
    dp [] [] (some 6) =
      (1 : ℝ[X]) := by
  rfl

theorem dag_0006 :
    dp [6] [6] (some 1) =
      (X : ℝ[X]) := by
  have erase_0 : ([6] : List ℕ).erase 6 = [] := by decide
  have hallowed : ([6] : List ℕ).toFinset.filter (fun a => 0 < a ∧ a ≤ 6) = ([6] : List ℕ).toFinset := by decide
  let coefficients : ℕ → ℝ[X] := fun a => if a = 6 then (1 : ℝ[X]) else 0
  have hchildren : ∀ a ∈ ([6] : List ℕ).toFinset,
      dp [] ([6].erase a) (some a) = coefficients a := by
    intro a ha
    have hcases : a = 6 := by simpa using ha
    rcases hcases with rfl
    · change dp [] ([6].erase 6) (some 6) = (1 : ℝ[X])
      rw [erase_0]
      exact dag_0005
  rw [dp_cons_eq_sum_of_children 6 [] [6] (some 1) ([6] : List ℕ).toFinset coefficients hallowed hchildren]
  norm_num [coefficients, List.toFinset_cons, List.toFinset_nil, Finset.sum_insert, Finset.sum_empty, beq_iff_eq]
  <;> ring

theorem dag_0007 :
    dp [6] [6] (some 2) =
      (X : ℝ[X]) := by
  have erase_0 : ([6] : List ℕ).erase 6 = [] := by decide
  have hallowed : ([6] : List ℕ).toFinset.filter (fun a => 0 < a ∧ a ≤ 6) = ([6] : List ℕ).toFinset := by decide
  let coefficients : ℕ → ℝ[X] := fun a => if a = 6 then (1 : ℝ[X]) else 0
  have hchildren : ∀ a ∈ ([6] : List ℕ).toFinset,
      dp [] ([6].erase a) (some a) = coefficients a := by
    intro a ha
    have hcases : a = 6 := by simpa using ha
    rcases hcases with rfl
    · change dp [] ([6].erase 6) (some 6) = (1 : ℝ[X])
      rw [erase_0]
      exact dag_0005
  rw [dp_cons_eq_sum_of_children 6 [] [6] (some 2) ([6] : List ℕ).toFinset coefficients hallowed hchildren]
  norm_num [coefficients, List.toFinset_cons, List.toFinset_nil, Finset.sum_insert, Finset.sum_empty, beq_iff_eq]
  <;> ring

theorem dag_0008 :
    dp [6] [6] (some 3) =
      (X : ℝ[X]) := by
  have erase_0 : ([6] : List ℕ).erase 6 = [] := by decide
  have hallowed : ([6] : List ℕ).toFinset.filter (fun a => 0 < a ∧ a ≤ 6) = ([6] : List ℕ).toFinset := by decide
  let coefficients : ℕ → ℝ[X] := fun a => if a = 6 then (1 : ℝ[X]) else 0
  have hchildren : ∀ a ∈ ([6] : List ℕ).toFinset,
      dp [] ([6].erase a) (some a) = coefficients a := by
    intro a ha
    have hcases : a = 6 := by simpa using ha
    rcases hcases with rfl
    · change dp [] ([6].erase 6) (some 6) = (1 : ℝ[X])
      rw [erase_0]
      exact dag_0005
  rw [dp_cons_eq_sum_of_children 6 [] [6] (some 3) ([6] : List ℕ).toFinset coefficients hallowed hchildren]
  norm_num [coefficients, List.toFinset_cons, List.toFinset_nil, Finset.sum_insert, Finset.sum_empty, beq_iff_eq]
  <;> ring

theorem dag_0009 :
    dp [6] [6] (some 4) =
      (X : ℝ[X]) := by
  have erase_0 : ([6] : List ℕ).erase 6 = [] := by decide
  have hallowed : ([6] : List ℕ).toFinset.filter (fun a => 0 < a ∧ a ≤ 6) = ([6] : List ℕ).toFinset := by decide
  let coefficients : ℕ → ℝ[X] := fun a => if a = 6 then (1 : ℝ[X]) else 0
  have hchildren : ∀ a ∈ ([6] : List ℕ).toFinset,
      dp [] ([6].erase a) (some a) = coefficients a := by
    intro a ha
    have hcases : a = 6 := by simpa using ha
    rcases hcases with rfl
    · change dp [] ([6].erase 6) (some 6) = (1 : ℝ[X])
      rw [erase_0]
      exact dag_0005
  rw [dp_cons_eq_sum_of_children 6 [] [6] (some 4) ([6] : List ℕ).toFinset coefficients hallowed hchildren]
  norm_num [coefficients, List.toFinset_cons, List.toFinset_nil, Finset.sum_insert, Finset.sum_empty, beq_iff_eq]
  <;> ring

theorem dag_0010 :
    dp [6] [6] (some 5) =
      (X : ℝ[X]) := by
  have erase_0 : ([6] : List ℕ).erase 6 = [] := by decide
  have hallowed : ([6] : List ℕ).toFinset.filter (fun a => 0 < a ∧ a ≤ 6) = ([6] : List ℕ).toFinset := by decide
  let coefficients : ℕ → ℝ[X] := fun a => if a = 6 then (1 : ℝ[X]) else 0
  have hchildren : ∀ a ∈ ([6] : List ℕ).toFinset,
      dp [] ([6].erase a) (some a) = coefficients a := by
    intro a ha
    have hcases : a = 6 := by simpa using ha
    rcases hcases with rfl
    · change dp [] ([6].erase 6) (some 6) = (1 : ℝ[X])
      rw [erase_0]
      exact dag_0005
  rw [dp_cons_eq_sum_of_children 6 [] [6] (some 5) ([6] : List ℕ).toFinset coefficients hallowed hchildren]
  norm_num [coefficients, List.toFinset_cons, List.toFinset_nil, Finset.sum_insert, Finset.sum_empty, beq_iff_eq]
  <;> ring

theorem dag_0011 :
    dp [6] [6] (some 6) =
      (1 : ℝ[X]) := by
  have erase_0 : ([6] : List ℕ).erase 6 = [] := by decide
  have hallowed : ([6] : List ℕ).toFinset.filter (fun a => 0 < a ∧ a ≤ 6) = ([6] : List ℕ).toFinset := by decide
  let coefficients : ℕ → ℝ[X] := fun a => if a = 6 then (1 : ℝ[X]) else 0
  have hchildren : ∀ a ∈ ([6] : List ℕ).toFinset,
      dp [] ([6].erase a) (some a) = coefficients a := by
    intro a ha
    have hcases : a = 6 := by simpa using ha
    rcases hcases with rfl
    · change dp [] ([6].erase 6) (some 6) = (1 : ℝ[X])
      rw [erase_0]
      exact dag_0005
  rw [dp_cons_eq_sum_of_children 6 [] [6] (some 6) ([6] : List ℕ).toFinset coefficients hallowed hchildren]
  norm_num [coefficients, List.toFinset_cons, List.toFinset_nil, Finset.sum_insert, Finset.sum_empty, beq_iff_eq]
  <;> ring

theorem dag_0012 :
    dp [6] [5] (some 6) =
      (1 : ℝ[X]) := by
  have erase_0 : ([5] : List ℕ).erase 5 = [] := by decide
  have hallowed : ([5] : List ℕ).toFinset.filter (fun a => 0 < a ∧ a ≤ 6) = ([5] : List ℕ).toFinset := by decide
  let coefficients : ℕ → ℝ[X] := fun a => if a = 5 then (1 : ℝ[X]) else 0
  have hchildren : ∀ a ∈ ([5] : List ℕ).toFinset,
      dp [] ([5].erase a) (some a) = coefficients a := by
    intro a ha
    have hcases : a = 5 := by simpa using ha
    rcases hcases with rfl
    · change dp [] ([5].erase 5) (some 5) = (1 : ℝ[X])
      rw [erase_0]
      exact dag_0004
  rw [dp_cons_eq_sum_of_children 6 [] [5] (some 6) ([5] : List ℕ).toFinset coefficients hallowed hchildren]
  norm_num [coefficients, List.toFinset_cons, List.toFinset_nil, Finset.sum_insert, Finset.sum_empty, beq_iff_eq]
  <;> ring

theorem dag_0013 :
    dp [6] [4] (some 6) =
      (1 : ℝ[X]) := by
  have erase_0 : ([4] : List ℕ).erase 4 = [] := by decide
  have hallowed : ([4] : List ℕ).toFinset.filter (fun a => 0 < a ∧ a ≤ 6) = ([4] : List ℕ).toFinset := by decide
  let coefficients : ℕ → ℝ[X] := fun a => if a = 4 then (1 : ℝ[X]) else 0
  have hchildren : ∀ a ∈ ([4] : List ℕ).toFinset,
      dp [] ([4].erase a) (some a) = coefficients a := by
    intro a ha
    have hcases : a = 4 := by simpa using ha
    rcases hcases with rfl
    · change dp [] ([4].erase 4) (some 4) = (1 : ℝ[X])
      rw [erase_0]
      exact dag_0003
  rw [dp_cons_eq_sum_of_children 6 [] [4] (some 6) ([4] : List ℕ).toFinset coefficients hallowed hchildren]
  norm_num [coefficients, List.toFinset_cons, List.toFinset_nil, Finset.sum_insert, Finset.sum_empty, beq_iff_eq]
  <;> ring

theorem dag_0014 :
    dp [6] [3] (some 6) =
      (1 : ℝ[X]) := by
  have erase_0 : ([3] : List ℕ).erase 3 = [] := by decide
  have hallowed : ([3] : List ℕ).toFinset.filter (fun a => 0 < a ∧ a ≤ 6) = ([3] : List ℕ).toFinset := by decide
  let coefficients : ℕ → ℝ[X] := fun a => if a = 3 then (1 : ℝ[X]) else 0
  have hchildren : ∀ a ∈ ([3] : List ℕ).toFinset,
      dp [] ([3].erase a) (some a) = coefficients a := by
    intro a ha
    have hcases : a = 3 := by simpa using ha
    rcases hcases with rfl
    · change dp [] ([3].erase 3) (some 3) = (1 : ℝ[X])
      rw [erase_0]
      exact dag_0002
  rw [dp_cons_eq_sum_of_children 6 [] [3] (some 6) ([3] : List ℕ).toFinset coefficients hallowed hchildren]
  norm_num [coefficients, List.toFinset_cons, List.toFinset_nil, Finset.sum_insert, Finset.sum_empty, beq_iff_eq]
  <;> ring

theorem dag_0015 :
    dp [6] [2] (some 6) =
      (1 : ℝ[X]) := by
  have erase_0 : ([2] : List ℕ).erase 2 = [] := by decide
  have hallowed : ([2] : List ℕ).toFinset.filter (fun a => 0 < a ∧ a ≤ 6) = ([2] : List ℕ).toFinset := by decide
  let coefficients : ℕ → ℝ[X] := fun a => if a = 2 then (1 : ℝ[X]) else 0
  have hchildren : ∀ a ∈ ([2] : List ℕ).toFinset,
      dp [] ([2].erase a) (some a) = coefficients a := by
    intro a ha
    have hcases : a = 2 := by simpa using ha
    rcases hcases with rfl
    · change dp [] ([2].erase 2) (some 2) = (1 : ℝ[X])
      rw [erase_0]
      exact dag_0001
  rw [dp_cons_eq_sum_of_children 6 [] [2] (some 6) ([2] : List ℕ).toFinset coefficients hallowed hchildren]
  norm_num [coefficients, List.toFinset_cons, List.toFinset_nil, Finset.sum_insert, Finset.sum_empty, beq_iff_eq]
  <;> ring

theorem dag_0016 :
    dp [6] [1] (some 6) =
      (1 : ℝ[X]) := by
  have erase_0 : ([1] : List ℕ).erase 1 = [] := by decide
  have hallowed : ([1] : List ℕ).toFinset.filter (fun a => 0 < a ∧ a ≤ 6) = ([1] : List ℕ).toFinset := by decide
  let coefficients : ℕ → ℝ[X] := fun a => if a = 1 then (1 : ℝ[X]) else 0
  have hchildren : ∀ a ∈ ([1] : List ℕ).toFinset,
      dp [] ([1].erase a) (some a) = coefficients a := by
    intro a ha
    have hcases : a = 1 := by simpa using ha
    rcases hcases with rfl
    · change dp [] ([1].erase 1) (some 1) = (1 : ℝ[X])
      rw [erase_0]
      exact dag_0000
  rw [dp_cons_eq_sum_of_children 6 [] [1] (some 6) ([1] : List ℕ).toFinset coefficients hallowed hchildren]
  norm_num [coefficients, List.toFinset_cons, List.toFinset_nil, Finset.sum_insert, Finset.sum_empty, beq_iff_eq]
  <;> ring

theorem dag_0017 :
    dp [6, 6] [6, 6] (some 1) =
      (X : ℝ[X]) := by
  have erase_0 : ([6, 6] : List ℕ).erase 6 = [6] := by decide
  have hallowed : ([6, 6] : List ℕ).toFinset.filter (fun a => 0 < a ∧ a ≤ 6) = ([6] : List ℕ).toFinset := by decide
  let coefficients : ℕ → ℝ[X] := fun a => if a = 6 then (1 : ℝ[X]) else 0
  have hchildren : ∀ a ∈ ([6] : List ℕ).toFinset,
      dp [6] ([6, 6].erase a) (some a) = coefficients a := by
    intro a ha
    have hcases : a = 6 := by simpa using ha
    rcases hcases with rfl
    · change dp [6] ([6, 6].erase 6) (some 6) = (1 : ℝ[X])
      rw [erase_0]
      exact dag_0011
  rw [dp_cons_eq_sum_of_children 6 [6] [6, 6] (some 1) ([6] : List ℕ).toFinset coefficients hallowed hchildren]
  norm_num [coefficients, List.toFinset_cons, List.toFinset_nil, Finset.sum_insert, Finset.sum_empty, beq_iff_eq]
  <;> ring

theorem dag_0018 :
    dp [6, 6] [6, 6] (some 2) =
      (X : ℝ[X]) := by
  have erase_0 : ([6, 6] : List ℕ).erase 6 = [6] := by decide
  have hallowed : ([6, 6] : List ℕ).toFinset.filter (fun a => 0 < a ∧ a ≤ 6) = ([6] : List ℕ).toFinset := by decide
  let coefficients : ℕ → ℝ[X] := fun a => if a = 6 then (1 : ℝ[X]) else 0
  have hchildren : ∀ a ∈ ([6] : List ℕ).toFinset,
      dp [6] ([6, 6].erase a) (some a) = coefficients a := by
    intro a ha
    have hcases : a = 6 := by simpa using ha
    rcases hcases with rfl
    · change dp [6] ([6, 6].erase 6) (some 6) = (1 : ℝ[X])
      rw [erase_0]
      exact dag_0011
  rw [dp_cons_eq_sum_of_children 6 [6] [6, 6] (some 2) ([6] : List ℕ).toFinset coefficients hallowed hchildren]
  norm_num [coefficients, List.toFinset_cons, List.toFinset_nil, Finset.sum_insert, Finset.sum_empty, beq_iff_eq]
  <;> ring

theorem dag_0019 :
    dp [6, 6] [6, 6] (some 3) =
      (X : ℝ[X]) := by
  have erase_0 : ([6, 6] : List ℕ).erase 6 = [6] := by decide
  have hallowed : ([6, 6] : List ℕ).toFinset.filter (fun a => 0 < a ∧ a ≤ 6) = ([6] : List ℕ).toFinset := by decide
  let coefficients : ℕ → ℝ[X] := fun a => if a = 6 then (1 : ℝ[X]) else 0
  have hchildren : ∀ a ∈ ([6] : List ℕ).toFinset,
      dp [6] ([6, 6].erase a) (some a) = coefficients a := by
    intro a ha
    have hcases : a = 6 := by simpa using ha
    rcases hcases with rfl
    · change dp [6] ([6, 6].erase 6) (some 6) = (1 : ℝ[X])
      rw [erase_0]
      exact dag_0011
  rw [dp_cons_eq_sum_of_children 6 [6] [6, 6] (some 3) ([6] : List ℕ).toFinset coefficients hallowed hchildren]
  norm_num [coefficients, List.toFinset_cons, List.toFinset_nil, Finset.sum_insert, Finset.sum_empty, beq_iff_eq]
  <;> ring

theorem dag_0020 :
    dp [6, 6] [6, 6] (some 4) =
      (X : ℝ[X]) := by
  have erase_0 : ([6, 6] : List ℕ).erase 6 = [6] := by decide
  have hallowed : ([6, 6] : List ℕ).toFinset.filter (fun a => 0 < a ∧ a ≤ 6) = ([6] : List ℕ).toFinset := by decide
  let coefficients : ℕ → ℝ[X] := fun a => if a = 6 then (1 : ℝ[X]) else 0
  have hchildren : ∀ a ∈ ([6] : List ℕ).toFinset,
      dp [6] ([6, 6].erase a) (some a) = coefficients a := by
    intro a ha
    have hcases : a = 6 := by simpa using ha
    rcases hcases with rfl
    · change dp [6] ([6, 6].erase 6) (some 6) = (1 : ℝ[X])
      rw [erase_0]
      exact dag_0011
  rw [dp_cons_eq_sum_of_children 6 [6] [6, 6] (some 4) ([6] : List ℕ).toFinset coefficients hallowed hchildren]
  norm_num [coefficients, List.toFinset_cons, List.toFinset_nil, Finset.sum_insert, Finset.sum_empty, beq_iff_eq]
  <;> ring

theorem dag_0021 :
    dp [6, 6] [6, 6] (some 5) =
      (X : ℝ[X]) := by
  have erase_0 : ([6, 6] : List ℕ).erase 6 = [6] := by decide
  have hallowed : ([6, 6] : List ℕ).toFinset.filter (fun a => 0 < a ∧ a ≤ 6) = ([6] : List ℕ).toFinset := by decide
  let coefficients : ℕ → ℝ[X] := fun a => if a = 6 then (1 : ℝ[X]) else 0
  have hchildren : ∀ a ∈ ([6] : List ℕ).toFinset,
      dp [6] ([6, 6].erase a) (some a) = coefficients a := by
    intro a ha
    have hcases : a = 6 := by simpa using ha
    rcases hcases with rfl
    · change dp [6] ([6, 6].erase 6) (some 6) = (1 : ℝ[X])
      rw [erase_0]
      exact dag_0011
  rw [dp_cons_eq_sum_of_children 6 [6] [6, 6] (some 5) ([6] : List ℕ).toFinset coefficients hallowed hchildren]
  norm_num [coefficients, List.toFinset_cons, List.toFinset_nil, Finset.sum_insert, Finset.sum_empty, beq_iff_eq]
  <;> ring

theorem dag_0022 :
    dp [6, 6] [6, 6] (some 6) =
      (1 : ℝ[X]) := by
  have erase_0 : ([6, 6] : List ℕ).erase 6 = [6] := by decide
  have hallowed : ([6, 6] : List ℕ).toFinset.filter (fun a => 0 < a ∧ a ≤ 6) = ([6] : List ℕ).toFinset := by decide
  let coefficients : ℕ → ℝ[X] := fun a => if a = 6 then (1 : ℝ[X]) else 0
  have hchildren : ∀ a ∈ ([6] : List ℕ).toFinset,
      dp [6] ([6, 6].erase a) (some a) = coefficients a := by
    intro a ha
    have hcases : a = 6 := by simpa using ha
    rcases hcases with rfl
    · change dp [6] ([6, 6].erase 6) (some 6) = (1 : ℝ[X])
      rw [erase_0]
      exact dag_0011
  rw [dp_cons_eq_sum_of_children 6 [6] [6, 6] (some 6) ([6] : List ℕ).toFinset coefficients hallowed hchildren]
  norm_num [coefficients, List.toFinset_cons, List.toFinset_nil, Finset.sum_insert, Finset.sum_empty, beq_iff_eq]
  <;> ring

theorem dag_0023 :
    dp [6, 6] [5, 6] (some 6) =
      (1 + X : ℝ[X]) := by
  have erase_0 : ([5, 6] : List ℕ).erase 5 = [6] := by decide
  have erase_1 : ([5, 6] : List ℕ).erase 6 = [5] := by decide
  have hallowed : ([5, 6] : List ℕ).toFinset.filter (fun a => 0 < a ∧ a ≤ 6) = ([5, 6] : List ℕ).toFinset := by decide
  let coefficients : ℕ → ℝ[X] := fun a => if a = 5 then (X : ℝ[X]) else if a = 6 then (1 : ℝ[X]) else 0
  have hchildren : ∀ a ∈ ([5, 6] : List ℕ).toFinset,
      dp [6] ([5, 6].erase a) (some a) = coefficients a := by
    intro a ha
    have hcases : a = 5 ∨ a = 6 := by simpa using ha
    rcases hcases with rfl | rfl
    · change dp [6] ([5, 6].erase 5) (some 5) = (X : ℝ[X])
      rw [erase_0]
      exact dag_0010
    · change dp [6] ([5, 6].erase 6) (some 6) = (1 : ℝ[X])
      rw [erase_1]
      exact dag_0012
  rw [dp_cons_eq_sum_of_children 6 [6] [5, 6] (some 6) ([5, 6] : List ℕ).toFinset coefficients hallowed hchildren]
  norm_num [coefficients, List.toFinset_cons, List.toFinset_nil, Finset.sum_insert, Finset.sum_empty, beq_iff_eq]
  <;> ring

theorem dag_0024 :
    dp [6, 6] [4, 6] (some 6) =
      (1 + X : ℝ[X]) := by
  have erase_0 : ([4, 6] : List ℕ).erase 4 = [6] := by decide
  have erase_1 : ([4, 6] : List ℕ).erase 6 = [4] := by decide
  have hallowed : ([4, 6] : List ℕ).toFinset.filter (fun a => 0 < a ∧ a ≤ 6) = ([4, 6] : List ℕ).toFinset := by decide
  let coefficients : ℕ → ℝ[X] := fun a => if a = 4 then (X : ℝ[X]) else if a = 6 then (1 : ℝ[X]) else 0
  have hchildren : ∀ a ∈ ([4, 6] : List ℕ).toFinset,
      dp [6] ([4, 6].erase a) (some a) = coefficients a := by
    intro a ha
    have hcases : a = 4 ∨ a = 6 := by simpa using ha
    rcases hcases with rfl | rfl
    · change dp [6] ([4, 6].erase 4) (some 4) = (X : ℝ[X])
      rw [erase_0]
      exact dag_0009
    · change dp [6] ([4, 6].erase 6) (some 6) = (1 : ℝ[X])
      rw [erase_1]
      exact dag_0013
  rw [dp_cons_eq_sum_of_children 6 [6] [4, 6] (some 6) ([4, 6] : List ℕ).toFinset coefficients hallowed hchildren]
  norm_num [coefficients, List.toFinset_cons, List.toFinset_nil, Finset.sum_insert, Finset.sum_empty, beq_iff_eq]
  <;> ring

theorem dag_0025 :
    dp [6, 6] [3, 6] (some 6) =
      (1 + X : ℝ[X]) := by
  have erase_0 : ([3, 6] : List ℕ).erase 3 = [6] := by decide
  have erase_1 : ([3, 6] : List ℕ).erase 6 = [3] := by decide
  have hallowed : ([3, 6] : List ℕ).toFinset.filter (fun a => 0 < a ∧ a ≤ 6) = ([3, 6] : List ℕ).toFinset := by decide
  let coefficients : ℕ → ℝ[X] := fun a => if a = 3 then (X : ℝ[X]) else if a = 6 then (1 : ℝ[X]) else 0
  have hchildren : ∀ a ∈ ([3, 6] : List ℕ).toFinset,
      dp [6] ([3, 6].erase a) (some a) = coefficients a := by
    intro a ha
    have hcases : a = 3 ∨ a = 6 := by simpa using ha
    rcases hcases with rfl | rfl
    · change dp [6] ([3, 6].erase 3) (some 3) = (X : ℝ[X])
      rw [erase_0]
      exact dag_0008
    · change dp [6] ([3, 6].erase 6) (some 6) = (1 : ℝ[X])
      rw [erase_1]
      exact dag_0014
  rw [dp_cons_eq_sum_of_children 6 [6] [3, 6] (some 6) ([3, 6] : List ℕ).toFinset coefficients hallowed hchildren]
  norm_num [coefficients, List.toFinset_cons, List.toFinset_nil, Finset.sum_insert, Finset.sum_empty, beq_iff_eq]
  <;> ring

theorem dag_0026 :
    dp [6, 6] [2, 6] (some 6) =
      (1 + X : ℝ[X]) := by
  have erase_0 : ([2, 6] : List ℕ).erase 2 = [6] := by decide
  have erase_1 : ([2, 6] : List ℕ).erase 6 = [2] := by decide
  have hallowed : ([2, 6] : List ℕ).toFinset.filter (fun a => 0 < a ∧ a ≤ 6) = ([2, 6] : List ℕ).toFinset := by decide
  let coefficients : ℕ → ℝ[X] := fun a => if a = 2 then (X : ℝ[X]) else if a = 6 then (1 : ℝ[X]) else 0
  have hchildren : ∀ a ∈ ([2, 6] : List ℕ).toFinset,
      dp [6] ([2, 6].erase a) (some a) = coefficients a := by
    intro a ha
    have hcases : a = 2 ∨ a = 6 := by simpa using ha
    rcases hcases with rfl | rfl
    · change dp [6] ([2, 6].erase 2) (some 2) = (X : ℝ[X])
      rw [erase_0]
      exact dag_0007
    · change dp [6] ([2, 6].erase 6) (some 6) = (1 : ℝ[X])
      rw [erase_1]
      exact dag_0015
  rw [dp_cons_eq_sum_of_children 6 [6] [2, 6] (some 6) ([2, 6] : List ℕ).toFinset coefficients hallowed hchildren]
  norm_num [coefficients, List.toFinset_cons, List.toFinset_nil, Finset.sum_insert, Finset.sum_empty, beq_iff_eq]
  <;> ring

theorem dag_0027 :
    dp [6, 6] [1, 6] (some 6) =
      (1 + X : ℝ[X]) := by
  have erase_0 : ([1, 6] : List ℕ).erase 1 = [6] := by decide
  have erase_1 : ([1, 6] : List ℕ).erase 6 = [1] := by decide
  have hallowed : ([1, 6] : List ℕ).toFinset.filter (fun a => 0 < a ∧ a ≤ 6) = ([1, 6] : List ℕ).toFinset := by decide
  let coefficients : ℕ → ℝ[X] := fun a => if a = 1 then (X : ℝ[X]) else if a = 6 then (1 : ℝ[X]) else 0
  have hchildren : ∀ a ∈ ([1, 6] : List ℕ).toFinset,
      dp [6] ([1, 6].erase a) (some a) = coefficients a := by
    intro a ha
    have hcases : a = 1 ∨ a = 6 := by simpa using ha
    rcases hcases with rfl | rfl
    · change dp [6] ([1, 6].erase 1) (some 1) = (X : ℝ[X])
      rw [erase_0]
      exact dag_0006
    · change dp [6] ([1, 6].erase 6) (some 6) = (1 : ℝ[X])
      rw [erase_1]
      exact dag_0016
  rw [dp_cons_eq_sum_of_children 6 [6] [1, 6] (some 6) ([1, 6] : List ℕ).toFinset coefficients hallowed hchildren]
  norm_num [coefficients, List.toFinset_cons, List.toFinset_nil, Finset.sum_insert, Finset.sum_empty, beq_iff_eq]
  <;> ring

theorem dag_0028 :
    dp [6, 6, 6] [6, 6, 6] (some 1) =
      (X : ℝ[X]) := by
  have erase_0 : ([6, 6, 6] : List ℕ).erase 6 = [6, 6] := by decide
  have hallowed : ([6, 6, 6] : List ℕ).toFinset.filter (fun a => 0 < a ∧ a ≤ 6) = ([6] : List ℕ).toFinset := by decide
  let coefficients : ℕ → ℝ[X] := fun a => if a = 6 then (1 : ℝ[X]) else 0
  have hchildren : ∀ a ∈ ([6] : List ℕ).toFinset,
      dp [6, 6] ([6, 6, 6].erase a) (some a) = coefficients a := by
    intro a ha
    have hcases : a = 6 := by simpa using ha
    rcases hcases with rfl
    · change dp [6, 6] ([6, 6, 6].erase 6) (some 6) = (1 : ℝ[X])
      rw [erase_0]
      exact dag_0022
  rw [dp_cons_eq_sum_of_children 6 [6, 6] [6, 6, 6] (some 1) ([6] : List ℕ).toFinset coefficients hallowed hchildren]
  norm_num [coefficients, List.toFinset_cons, List.toFinset_nil, Finset.sum_insert, Finset.sum_empty, beq_iff_eq]
  <;> ring

theorem dag_0029 :
    dp [6, 6, 6] [6, 6, 6] (some 2) =
      (X : ℝ[X]) := by
  have erase_0 : ([6, 6, 6] : List ℕ).erase 6 = [6, 6] := by decide
  have hallowed : ([6, 6, 6] : List ℕ).toFinset.filter (fun a => 0 < a ∧ a ≤ 6) = ([6] : List ℕ).toFinset := by decide
  let coefficients : ℕ → ℝ[X] := fun a => if a = 6 then (1 : ℝ[X]) else 0
  have hchildren : ∀ a ∈ ([6] : List ℕ).toFinset,
      dp [6, 6] ([6, 6, 6].erase a) (some a) = coefficients a := by
    intro a ha
    have hcases : a = 6 := by simpa using ha
    rcases hcases with rfl
    · change dp [6, 6] ([6, 6, 6].erase 6) (some 6) = (1 : ℝ[X])
      rw [erase_0]
      exact dag_0022
  rw [dp_cons_eq_sum_of_children 6 [6, 6] [6, 6, 6] (some 2) ([6] : List ℕ).toFinset coefficients hallowed hchildren]
  norm_num [coefficients, List.toFinset_cons, List.toFinset_nil, Finset.sum_insert, Finset.sum_empty, beq_iff_eq]
  <;> ring

theorem dag_0030 :
    dp [6, 6, 6] [6, 6, 6] (some 3) =
      (X : ℝ[X]) := by
  have erase_0 : ([6, 6, 6] : List ℕ).erase 6 = [6, 6] := by decide
  have hallowed : ([6, 6, 6] : List ℕ).toFinset.filter (fun a => 0 < a ∧ a ≤ 6) = ([6] : List ℕ).toFinset := by decide
  let coefficients : ℕ → ℝ[X] := fun a => if a = 6 then (1 : ℝ[X]) else 0
  have hchildren : ∀ a ∈ ([6] : List ℕ).toFinset,
      dp [6, 6] ([6, 6, 6].erase a) (some a) = coefficients a := by
    intro a ha
    have hcases : a = 6 := by simpa using ha
    rcases hcases with rfl
    · change dp [6, 6] ([6, 6, 6].erase 6) (some 6) = (1 : ℝ[X])
      rw [erase_0]
      exact dag_0022
  rw [dp_cons_eq_sum_of_children 6 [6, 6] [6, 6, 6] (some 3) ([6] : List ℕ).toFinset coefficients hallowed hchildren]
  norm_num [coefficients, List.toFinset_cons, List.toFinset_nil, Finset.sum_insert, Finset.sum_empty, beq_iff_eq]
  <;> ring

theorem dag_0031 :
    dp [6, 6, 6] [6, 6, 6] (some 4) =
      (X : ℝ[X]) := by
  have erase_0 : ([6, 6, 6] : List ℕ).erase 6 = [6, 6] := by decide
  have hallowed : ([6, 6, 6] : List ℕ).toFinset.filter (fun a => 0 < a ∧ a ≤ 6) = ([6] : List ℕ).toFinset := by decide
  let coefficients : ℕ → ℝ[X] := fun a => if a = 6 then (1 : ℝ[X]) else 0
  have hchildren : ∀ a ∈ ([6] : List ℕ).toFinset,
      dp [6, 6] ([6, 6, 6].erase a) (some a) = coefficients a := by
    intro a ha
    have hcases : a = 6 := by simpa using ha
    rcases hcases with rfl
    · change dp [6, 6] ([6, 6, 6].erase 6) (some 6) = (1 : ℝ[X])
      rw [erase_0]
      exact dag_0022
  rw [dp_cons_eq_sum_of_children 6 [6, 6] [6, 6, 6] (some 4) ([6] : List ℕ).toFinset coefficients hallowed hchildren]
  norm_num [coefficients, List.toFinset_cons, List.toFinset_nil, Finset.sum_insert, Finset.sum_empty, beq_iff_eq]
  <;> ring

theorem dag_0032 :
    dp [6, 6, 6] [6, 6, 6] (some 5) =
      (X : ℝ[X]) := by
  have erase_0 : ([6, 6, 6] : List ℕ).erase 6 = [6, 6] := by decide
  have hallowed : ([6, 6, 6] : List ℕ).toFinset.filter (fun a => 0 < a ∧ a ≤ 6) = ([6] : List ℕ).toFinset := by decide
  let coefficients : ℕ → ℝ[X] := fun a => if a = 6 then (1 : ℝ[X]) else 0
  have hchildren : ∀ a ∈ ([6] : List ℕ).toFinset,
      dp [6, 6] ([6, 6, 6].erase a) (some a) = coefficients a := by
    intro a ha
    have hcases : a = 6 := by simpa using ha
    rcases hcases with rfl
    · change dp [6, 6] ([6, 6, 6].erase 6) (some 6) = (1 : ℝ[X])
      rw [erase_0]
      exact dag_0022
  rw [dp_cons_eq_sum_of_children 6 [6, 6] [6, 6, 6] (some 5) ([6] : List ℕ).toFinset coefficients hallowed hchildren]
  norm_num [coefficients, List.toFinset_cons, List.toFinset_nil, Finset.sum_insert, Finset.sum_empty, beq_iff_eq]
  <;> ring

theorem dag_0033 :
    dp [6, 6, 6] [6, 6, 6] (some 6) =
      (1 : ℝ[X]) := by
  have erase_0 : ([6, 6, 6] : List ℕ).erase 6 = [6, 6] := by decide
  have hallowed : ([6, 6, 6] : List ℕ).toFinset.filter (fun a => 0 < a ∧ a ≤ 6) = ([6] : List ℕ).toFinset := by decide
  let coefficients : ℕ → ℝ[X] := fun a => if a = 6 then (1 : ℝ[X]) else 0
  have hchildren : ∀ a ∈ ([6] : List ℕ).toFinset,
      dp [6, 6] ([6, 6, 6].erase a) (some a) = coefficients a := by
    intro a ha
    have hcases : a = 6 := by simpa using ha
    rcases hcases with rfl
    · change dp [6, 6] ([6, 6, 6].erase 6) (some 6) = (1 : ℝ[X])
      rw [erase_0]
      exact dag_0022
  rw [dp_cons_eq_sum_of_children 6 [6, 6] [6, 6, 6] (some 6) ([6] : List ℕ).toFinset coefficients hallowed hchildren]
  norm_num [coefficients, List.toFinset_cons, List.toFinset_nil, Finset.sum_insert, Finset.sum_empty, beq_iff_eq]
  <;> ring

theorem dag_0034 :
    dp [6, 6, 6] [5, 6, 6] (some 6) =
      (1 + 2 * X : ℝ[X]) := by
  have erase_0 : ([5, 6, 6] : List ℕ).erase 5 = [6, 6] := by decide
  have erase_1 : ([5, 6, 6] : List ℕ).erase 6 = [5, 6] := by decide
  have hallowed : ([5, 6, 6] : List ℕ).toFinset.filter (fun a => 0 < a ∧ a ≤ 6) = ([5, 6] : List ℕ).toFinset := by decide
  let coefficients : ℕ → ℝ[X] := fun a => if a = 5 then (X : ℝ[X]) else if a = 6 then (1 + X : ℝ[X]) else 0
  have hchildren : ∀ a ∈ ([5, 6] : List ℕ).toFinset,
      dp [6, 6] ([5, 6, 6].erase a) (some a) = coefficients a := by
    intro a ha
    have hcases : a = 5 ∨ a = 6 := by simpa using ha
    rcases hcases with rfl | rfl
    · change dp [6, 6] ([5, 6, 6].erase 5) (some 5) = (X : ℝ[X])
      rw [erase_0]
      exact dag_0021
    · change dp [6, 6] ([5, 6, 6].erase 6) (some 6) = (1 + X : ℝ[X])
      rw [erase_1]
      exact dag_0023
  rw [dp_cons_eq_sum_of_children 6 [6, 6] [5, 6, 6] (some 6) ([5, 6] : List ℕ).toFinset coefficients hallowed hchildren]
  norm_num [coefficients, List.toFinset_cons, List.toFinset_nil, Finset.sum_insert, Finset.sum_empty, beq_iff_eq]
  <;> ring

end D5.S3.Combinatorics.Permutation.MultisetRookEulerianCertificate.Block00
