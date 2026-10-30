/- GID: D5/S3/Quantum/Contextuality/EighteenModeBosonicAssignmentParity
   generality: I
   mirror-B: D5/B/S3/Quantum/Contextuality/EighteenModeBosonicAssignmentParity
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Eighteen-mode bosonic occupation assignments exist exactly for even particle counts. -/

import D5.S3.Combinatorics.Graph.BipartiteSubgraphDensity

/-! Occupation assignments for the eighteen-mode set in Kurzyński,
    arXiv:1609.01250v1, Eq. (1) and the nine contexts.
    Only the existence of natural-valued, context-independent occupations is asserted. -/

set_option autoImplicit false

open scoped BigOperators
open D5.S3.Combinatorics.Graph.BipartiteSubgraphDensity (incident)

namespace D5.S3.Quantum.Contextuality.EighteenModeBosonicAssignmentParity

/-- A mode is labelled by the two contexts in which it occurs. -/
def modes : Finset (ℕ × ℕ) :=
  {(1, 2), (1, 6), (1, 7), (1, 8), (2, 3), (2, 8), (2, 9), (3, 4), (3, 7),
    (3, 9), (4, 5), (4, 7), (4, 8), (5, 6), (5, 8), (5, 9), (6, 7), (6, 9)}

/-- One natural occupation per mode, with particle number conserved in every context. -/
def IsNoncontextualAssignment (n : ℕ) (v : ℕ × ℕ → ℕ) : Prop :=
  ∀ i ∈ Finset.Icc 1 9, ∑ p ∈ incident modes Prod.fst Prod.snd i, v p = n

/-- The occupation-assignment model admits precisely the even particle numbers. -/
def claim : Prop :=
  ∀ n : ℕ, (∃ v, IsNoncontextualAssignment n v) ↔ Even n

private theorem incidence_double_count (v : ℕ × ℕ → ℕ) :
    (∑ i ∈ Finset.Icc 1 9, ∑ p ∈ incident modes Prod.fst Prod.snd i, v p) =
      2 * ∑ p ∈ modes, v p := by
  have hincidence : ∀ p ∈ modes,
      (∑ i ∈ Finset.Icc 1 9, if p ∈ incident modes Prod.fst Prod.snd i then 1 else 0 : ℕ) =
        2 := by
    intro p hp
    have hend : p.1 ∈ Finset.Icc 1 9 ∧ p.2 ∈ Finset.Icc 1 9 ∧ p.1 ≠ p.2 := by
      change p ∈ ({(1, 2), (1, 6), (1, 7), (1, 8), (2, 3), (2, 8), (2, 9),
        (3, 4), (3, 7), (3, 9), (4, 5), (4, 7), (4, 8), (5, 6), (5, 8),
        (5, 9), (6, 7), (6, 9)} : Finset (ℕ × ℕ)) at hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have hmem (i : ℕ) : p ∈ incident modes Prod.fst Prod.snd i ↔ p.1 = i ∨ p.2 = i := by
      change p ∈ modes.filter (fun q => q.1 = i ∨ q.2 = i) ↔ _
      simp only [Finset.mem_filter, hp, true_and]
    have hsplit (i : ℕ) : (if p ∈ incident modes Prod.fst Prod.snd i then 1 else 0 : ℕ) =
        (if p.1 = i then 1 else 0) + (if p.2 = i then 1 else 0) := by
      simp only [hmem i]
      by_cases hf : p.1 = i
      · have hs : p.2 ≠ i := fun hs => hend.2.2 (hf.trans hs.symm)
        simp only [hf, hs, true_or, ite_true, ite_false, add_zero]
      · simp only [hf, false_or, ite_false, zero_add]
    simp_rw [hsplit]
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq, ite_eq_left hend.1, ite_eq_left hend.2.1]
  have hcontext (i : ℕ) :
      (∑ p ∈ incident modes Prod.fst Prod.snd i, v p) =
        ∑ p ∈ modes, if p ∈ incident modes Prod.fst Prod.snd i then v p else 0 := by
    have hsub : incident modes Prod.fst Prod.snd i ⊆ modes := Finset.filter_subset _ _
    have hs : modes.filter (fun p => p ∈ incident modes Prod.fst Prod.snd i) =
        incident modes Prod.fst Prod.snd i :=
      Finset.filter_mem_eq_of_subset hsub
    rw [← Finset.sum_filter, hs]
  calc
    (∑ i ∈ Finset.Icc 1 9, ∑ p ∈ incident modes Prod.fst Prod.snd i, v p) =
        ∑ i ∈ Finset.Icc 1 9, ∑ p ∈ modes,
          if p ∈ incident modes Prod.fst Prod.snd i then v p else 0 :=
      Finset.sum_congr rfl fun i _ => hcontext i
    _ = ∑ p ∈ modes, ∑ i ∈ Finset.Icc 1 9,
        if p ∈ incident modes Prod.fst Prod.snd i then v p else 0 := Finset.sum_comm
    _ = ∑ p ∈ modes,
        (∑ i ∈ Finset.Icc 1 9, if p ∈ incident modes Prod.fst Prod.snd i then 1 else 0) *
          v p := by
      apply Finset.sum_congr rfl
      intro p _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      split_ifs <;> simp only [one_mul, zero_mul]
    _ = ∑ p ∈ modes, 2 * v p := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [hincidence p hp]
    _ = 2 * ∑ p ∈ modes, v p := (Finset.mul_sum _ _ _).symm

private theorem assignment_even (n : ℕ) (v : ℕ × ℕ → ℕ)
    (h : IsNoncontextualAssignment n v) : Even n := by
  have htotal : 9 * n = 2 * ∑ p ∈ modes, v p := by
    calc
      9 * n = ∑ i ∈ Finset.Icc 1 9, n := by simp
      _ = ∑ i ∈ Finset.Icc 1 9, ∑ p ∈ incident modes Prod.fst Prod.snd i, v p :=
        Finset.sum_congr rfl fun i hi => (h i hi).symm
      _ = 2 * ∑ p ∈ modes, v p := incidence_double_count v
  have heven : Even (9 * n) := even_iff_exists_two_mul.mpr ⟨_, htotal⟩
  exact (Nat.even_mul.mp heven).resolve_left (by decide)

private theorem even_assignment (m : ℕ) :
    ∃ v, IsNoncontextualAssignment (2 * m) v := by
  let v : ℕ × ℕ → ℕ := fun p =>
    if p ∈ ({(1, 2), (1, 6), (2, 8), (3, 7), (3, 9), (4, 7), (4, 8),
      (5, 6), (5, 9)} : Finset (ℕ × ℕ)) then m else 0
  refine ⟨v, ?_⟩
  intro i hi
  have hcount : ∀ j ∈ Finset.Icc 1 9,
      (∑ p ∈ incident modes Prod.fst Prod.snd j,
        if p ∈ ({(1, 2), (1, 6), (2, 8), (3, 7), (3, 9), (4, 7), (4, 8),
          (5, 6), (5, 9)} : Finset (ℕ × ℕ)) then 1 else 0 : ℕ) = 2 := by
    intro j hj
    obtain ⟨hl, hu⟩ := Finset.mem_Icc.mp hj
    interval_cases j <;> decide
  change (∑ p ∈ incident modes Prod.fst Prod.snd i,
    if p ∈ ({(1, 2), (1, 6), (2, 8), (3, 7), (3, 9), (4, 7), (4, 8),
      (5, 6), (5, 9)} : Finset (ℕ × ℕ)) then m else 0) = 2 * m
  calc
    _ = (∑ p ∈ incident modes Prod.fst Prod.snd i,
        if p ∈ ({(1, 2), (1, 6), (2, 8), (3, 7), (3, 9), (4, 7), (4, 8),
          (5, 6), (5, 9)} : Finset (ℕ × ℕ)) then 1 else 0) * m := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro p _
      split_ifs <;> simp only [one_mul, zero_mul]
    _ = 2 * m := by rw [hcount i hi]

/-- Kurzyński's eighteen-mode occupation question has an assignment exactly for even `n`. -/
theorem result : claim := by
  intro n
  constructor
  · rintro ⟨v, h⟩
    exact assignment_even n v h
  · intro h
    obtain ⟨m, hm⟩ := even_iff_exists_two_mul.mp h
    rw [hm]
    exact even_assignment m

end D5.S3.Quantum.Contextuality.EighteenModeBosonicAssignmentParity
