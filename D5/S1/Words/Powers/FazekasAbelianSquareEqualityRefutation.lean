/- GID: D5/S1/Words/Powers/FazekasAbelianSquareEqualityRefutation
   generality: I
   mirror-B: D5/B/S1/Words/Powers/FazekasAbelianSquareEqualityRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: [mathlib/module/Mathlib.Data.Finset.Card]
   utility: kind=certified-instance; basis=refutes=gid:D5/S1/Words/Powers/FazekasAbelianSquareEqualityRefutation.claim; result=D5/S1/Words/Powers/FazekasAbelianSquareEqualityRefutation.result; claim=D5/S1/Words/Powers/FazekasAbelianSquareEqualityRefutation.claim
   digest: The word abab refutes Conjecture 4 on equality-case trivial abelian squares. -/

/- proof_shape: result: bind-only
   escape_witness: none
   admission_basis: open-problem-resolution (issue #8589)
   Direct frozen dependencies: none (pinned Mathlib only). -/

import Mathlib.Data.Finset.Card

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.Powers.FazekasAbelianSquareEqualityRefutation

/-- Letters `a ↦ false`, `b ↦ true`; a binary word is a `List Bool`.
`u` is an abelian square: an even-length word whose two halves have equal Parikh vectors. -/
def IsAbelianSquare (u : List Bool) : Prop :=
  let p := u.length / 2
  0 < p ∧ u.length = 2 * p ∧
    (u.take p).count false = (u.drop p).count false ∧
      (u.take p).count true = (u.drop p).count true

private instance isAbelianSquareDecidable : DecidablePred IsAbelianSquare :=
  fun u => inferInstanceAs (Decidable (
    let p := u.length / 2
    0 < p ∧ u.length = 2 * p ∧
      (u.take p).count false = (u.drop p).count false ∧
        (u.take p).count true = (u.drop p).count true))

/-- The abelian squares of `w`: its distinct factors (prefixes of suffixes)
that are abelian squares. -/
def abelianSquares (w : List Bool) : Finset (List Bool) :=
  (w.tails.flatMap List.inits).toFinset.filter IsAbelianSquare

/-- Trivial: a positive even power of a single letter. -/
def IsTrivial (u : List Bool) : Prop :=
  ∃ m : ℕ, 0 < m ∧ (u = List.replicate (2 * m) false ∨ u = List.replicate (2 * m) true)

/-- Conjecture 4 of arXiv:2604.23188v1. -/
def claim : Prop :=
  ∀ w : List Bool, w.length / 4 ≤ (abelianSquares w).card ∧
    ((abelianSquares w).card = w.length / 4 → ∀ u ∈ abelianSquares w, IsTrivial u)

/-- Conjecture 4 is false at `abab`. -/
theorem result : ¬ claim := by
  intro h
  have htrivial : IsTrivial [false, true, false, true] :=
    (h [false, true, false, true]).2 (by decide)
      [false, true, false, true] (by decide)
  rcases htrivial with ⟨m, hm, hfalse | htrue⟩
  · have hlen : 4 = 2 * m := by
      simpa using congrArg List.length hfalse
    have : m = 2 := by
      have hmul : 2 * 2 = 2 * m := by simpa using hlen
      exact (Nat.mul_left_cancel (by decide) hmul).symm
    subst m
    simp at hfalse
  · have hlen : 4 = 2 * m := by
      simpa using congrArg List.length htrue
    have : m = 2 := by
      have hmul : 2 * 2 = 2 * m := by simpa using hlen
      exact (Nat.mul_left_cancel (by decide) hmul).symm
    subst m
    simp at htrue

example : abelianSquares [false, true, false, true] =
    {[false, true, false, true]} := by
  decide

example : (abelianSquares [false, true, false, false, true, false, true, false]).card = 6 := by
  decide

example : IsTrivial [true, true] := by
  exact ⟨1, by decide, by simp⟩

#print axioms result

end D5.S1.Words.Powers.FazekasAbelianSquareEqualityRefutation
