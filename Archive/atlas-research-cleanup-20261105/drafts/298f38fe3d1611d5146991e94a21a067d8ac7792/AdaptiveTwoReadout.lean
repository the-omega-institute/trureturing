/-
  Research candidate: deterministic adaptive two-readout strategies.
  This file is intentionally uncompiled.  Every `sorry` marks a named
  combinatorial obligation, not a proved theorem.
-/

import D5.S3.Combinatorics.CircularWords.PairedDeletionFiber

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.CircularWords.AdaptiveTwoReadout

open D5.S3.Combinatorics.CircularWords.CircularDeletionTransport
open D5.S3.Combinatorics.CircularWords.CyclicInsertionGap
open D5.S3.Combinatorics.CircularWords.DeletionReadoutReconstruction
open D5.S3.Combinatorics.CircularWords.PairedDeletionFiber

universe u
variable {α : Type u} [DecidableEq α]

abbrev SupportedCircle (A : Finset α) :=
  D5.S3.Combinatorics.CircularWords.DeletionReadoutReconstruction.SupportedCircle A

/-- A policy sees the first labelled residual and returns the second label in
    the fixed support. Repetition is allowed because `σ y` may equal `x`.
    Restricting the codomain to `A` is essential: an ambient label absent from
    the support would make deletion the identity and reveal the whole circle. -/
def adaptiveTrace (A : Finset α) (x : A) (σ : Cycle α → A)
    (C : SupportedCircle A) : A × Cycle α × A × Cycle α :=
  (x, delete x.1 C.1, σ (delete x.1 C.1),
    delete (σ (delete x.1 C.1)).1 C.1)

/- Existence of a supported residual.  The canonical witness is
   `(A.erase x).toList` viewed as a cycle; the proof is a finite-set/list
   support calculation. -/
theorem exists_supported_residual
    {A : Finset α} {x : α} (hx : x ∈ A) (hA : 3 ≤ A.card) :
    ∃ B : Cycle α, B.Nodup ∧ B.toFinset = A.erase x := by
  sorry

/- Two distinct insertions of `x` into a residual with at least two labels. -/
theorem two_gap_collision
    {A : Finset α} {x : α} (hx : x ∈ A) (hA : 3 ≤ A.card)
    {B : Cycle α} (hB : B.Nodup) (sB : B.toFinset = A.erase x) :
    ∃ C D : Cycle α,
      C.Nodup ∧ D.Nodup ∧ C.toFinset = A ∧ D.toFinset = A ∧
      C ≠ D ∧ delete x C = B ∧ delete x D = B := by
  sorry

/- If the policy returns z ≠ x, put x immediately before/after z in the
   rooted residual word.  The two cycles have both labelled deletions equal. -/
theorem adjacent_pair_collision
    {A : Finset α} {x z : α} (hx : x ∈ A) (hz : z ∈ A) (hxz : x ≠ z)
    {B : Cycle α} (hB : B.Nodup) (sB : B.toFinset = A.erase x) :
    ∃ C D : Cycle α,
      C.Nodup ∧ D.Nodup ∧ C.toFinset = A ∧ D.toFinset = A ∧
      C ≠ D ∧ delete x C = B ∧ delete x D = B ∧
      delete z C = delete z D := by
  sorry

/- The branchwise lemma includes repeated selection (`z=x`). -/
theorem adaptive_branch_collision
    {A : Finset α} (hA : 3 ≤ A.card) {x : α} (hx : x ∈ A)
    {B : Cycle α} (hB : B.Nodup) (sB : B.toFinset = A.erase x)
    (σ : Cycle α → A) :
    ∃ C D : Cycle α,
      C.Nodup ∧ D.Nodup ∧ C.toFinset = A ∧ D.toFinset = A ∧
      C ≠ D ∧ delete x C = B ∧ delete x D = B ∧
      delete (σ B).1 C = delete (σ B).1 D := by
  sorry

/-- No deterministic second-label policy can make two retained labelled
    readouts injective once the fixed support has at least three labels. -/
theorem no_adaptive_two_reconstruction
    {A : Finset α} (hA : 3 ≤ A.card) :
    ∀ (x : A) (σ : Cycle α → A),
      ¬ Function.Injective (adaptiveTrace A x σ) := by
  sorry

/-- Small-support boundary.  With one or two labels the supported-circle
    subtype is a subsingleton, hence every legal trace is injective.  With
    three or more labels the preceding theorem applies. -/
theorem adaptive_two_iff_small_support
    {A : Finset α} (hA0 : 0 < A.card) :
    (∃ (x : A) (σ : Cycle α → A),
      Function.Injective (adaptiveTrace A x σ)) ↔ A.card ≤ 2 := by
  sorry

end D5.S3.Combinatorics.CircularWords.AdaptiveTwoReadout
