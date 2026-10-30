/- GID: D5/S3/Quantum/Contextuality/EighteenModeBosonicAssignmentParity
   generality: I
   mirror-B: D5/B/S3/Quantum/Contextuality/EighteenModeBosonicAssignmentParity
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The eighteen-mode bosonic occupation assignments exist exactly for even particle counts. -/

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Ring.Parity
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

/-! Occupation assignments for the eighteen-mode set in Kurzyński,
    arXiv:1609.01250v1, Eq. (1) and the nine contexts.
    Only the existence of natural-valued, context-independent occupations is asserted. -/

set_option autoImplicit false

open scoped BigOperators

namespace D5.S3.Quantum.Contextuality.EighteenModeBosonicAssignmentParity

/-- A mode is labelled by the two contexts in which it occurs. -/
def modes : Finset (ℕ × ℕ) :=
  {(1, 2), (1, 6), (1, 7), (1, 8), (2, 3), (2, 8), (2, 9), (3, 4), (3, 7),
    (3, 9), (4, 5), (4, 7), (4, 8), (5, 6), (5, 8), (5, 9), (6, 7), (6, 9)}

/-- The modes occurring in the context with label `i`. -/
def context (i : ℕ) : Finset (ℕ × ℕ) :=
  modes.filter (fun p => p.1 = i ∨ p.2 = i)

/-- One natural occupation per mode, with particle number conserved in every context. -/
def IsNoncontextualAssignment (n : ℕ) (v : ℕ × ℕ → ℕ) : Prop :=
  ∀ i ∈ Finset.Icc 1 9, ∑ p ∈ context i, v p = n

/-- The occupation-assignment model admits precisely the even particle numbers. -/
def claim : Prop :=
  ∀ n : ℕ, (∃ v, IsNoncontextualAssignment n v) ↔ Even n

private theorem incidence_double_count (v : ℕ × ℕ → ℕ) :
    (∑ i ∈ Finset.Icc 1 9, ∑ p ∈ context i, v p) =
      2 * ∑ p ∈ modes, v p := by
  sorry

private theorem assignment_even (n : ℕ) (v : ℕ × ℕ → ℕ)
    (h : IsNoncontextualAssignment n v) : Even n := by
  sorry

private theorem even_assignment (m : ℕ) :
    ∃ v, IsNoncontextualAssignment (2 * m) v := by
  sorry

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
