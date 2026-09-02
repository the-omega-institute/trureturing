/- GID: D5/S3/Quantum/Matrix/MonomialGram
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/MonomialGram
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   digest: A monomial conjugate of a diagonal is diagonal with squared row scales. -/

/- Library-search audit trail (2026-09-03). Commands reproduced literally as run, each ending in
   `wc -l`; none truncated. Declaration patterns are the wide form, so attribute-prefixed,
   private and `def` forms are included.

   P='^(@\[[^]]*\][[:space:]]*)?(private )?(noncomputable )?(theorem|lemma|def|abbrev) '

   git grep -hoE "${P}[A-Za-z0-9_']*monomial[A-Za-z0-9_']*(gram|transpose|mul|diagonal)
     [A-Za-z0-9_']*" origin/dev -- 'D5/**/*.lean' | wc -l                                    -> 4
     All four opened:
       `monomial_eq_diagonal_mul` and `isDiag_monomial_mul_diagonal_mul_transpose` in the frozen
       D5/S3/Quantum/Matrix/MonomialDiagonalPreserving, which this module imports;
       `normalizedCircleHaar_monomial_gram`, private in
       D5/S3/Weil/TestFunctions/ToeplitzContactSupport, and
       `normalized_circle_haar_monomial_gram`, private in
       D5/S3/Weil/TestFunctions/ExactTruncatedHaarFloor — two different files. Both compute
       `integral z^k * star (z^j) = if j = k then 1 else 0` for scalar monomials on the circle.
       They carry `monomial` and `gram` in their names and concern a different object.
   The reversed word order returns 0.

   git grep -clE 'monomial [a-z]+ [a-z]+ \*.*transpose' origin/dev -- 'D5/**/*.lean' | wc -l  -> 1
     That one file is the frozen MonomialDiagonalPreserving itself, holding the `IsDiag`
     statement this module sharpens.

   grep -rlE "theorem.*(monomial|permutation).*(transpose|conjTranspose).*diagonal"
     .lake/packages/mathlib --include='*.lean' | wc -l                                       -> 0
   grep -rlE "toMatrix.*mul.*transpose|transpose.*toMatrix" .lake/packages/mathlib
     --include='*.lean' | wc -l                                                              -> 9
     Opened. The relevant one is Mathlib/Data/Matrix/PEquiv.lean, which supplies
     `toMatrix_toPEquiv_mul` and `mul_toMatrix_toPEquiv` expressing multiplication by a
     permutation matrix as a `submatrix`. It carries no law for `P * diagonal d * transpose P`,
     and the targeted search for one returns 0 (line above), so the identity is proved here from
     the entrywise definition rather than assembled from upstream.

   Batteries, CSLib and TauCeti were searched for earlier nodes of this family and returned
   nothing; no separate query was issued here, so those are carried negatives rather than fresh
   ones. Zulip was not queried, so that domain is absent rather than negative.

   Relation to the frozen result. `isDiag_monomial_mul_diagonal_mul_transpose` asserts only that
   the conjugate `.IsDiag`; it gives no entry values. This module computes those entries. The
   frozen statement is neither restated nor amended, and its file is untouched; the proof here
   reuses its `@[simp] monomial_apply` and follows its case split.
-/

import D5.S3.Quantum.Matrix.MonomialDiagonalPreserving

/-!
# The Gram form of a monomial matrix

A monomial matrix has at most one nonzero entry per row — exactly one where the row scale is a
unit, and none at all where it vanishes. Conjugating a diagonal matrix by it therefore cannot
mix indices, and the surviving entry at index `i` is the diagonal weight read at the
permuted position, times the square of the row scale.

The frozen node in this family records that the conjugate is diagonal. Here that is sharpened
from a property to a value: the diagonal is exactly `fun i => d (sigma i) * c i ^ 2`. The
special case `d = 1` gives the Gram matrix of the monomial matrix itself.
-/

namespace D5.S3.Quantum.Matrix.MonomialGram

open D5.S3.Quantum.Matrix.MonomialDiagonalPreserving

variable {n : Type*} [DecidableEq n] [Fintype n] {R : Type*} [CommRing R]

/-- Conjugating a diagonal matrix by a monomial matrix yields the diagonal matrix whose entry at
`i` is the weight at `sigma i` scaled by the square of the row scale. -/
theorem monomial_mul_diagonal_mul_transpose (sigma : Equiv.Perm n) (c d : n → R) :
    monomial sigma c * Matrix.diagonal d * _root_.Matrix.transpose (monomial sigma c)
      = Matrix.diagonal (fun i => d (sigma i) * c i ^ 2) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, monomial_apply,
    Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl, Finset.sum_eq_single (sigma i)]
    · simp [sq]
      ring
    · intro x _ hx
      simp [hx]
    · intro hx
      exact absurd (Finset.mem_univ (sigma i)) hx
  · rw [if_neg hij]
    have hi : (sigma i) ≠ (sigma j) := fun h => hij (sigma.injective h)
    refine Finset.sum_eq_zero fun x _ => ?_
    rcases eq_or_ne x (sigma i) with hx | hx
    · subst hx
      simp [hi]
    · simp [hx]

/-- The Gram matrix of a monomial matrix is diagonal with the squared row scales. -/
theorem monomial_mul_transpose (sigma : Equiv.Perm n) (c : n → R) :
    monomial sigma c * _root_.Matrix.transpose (monomial sigma c)
      = Matrix.diagonal (fun i => c i ^ 2) := by
  have h := monomial_mul_diagonal_mul_transpose sigma c 1
  simpa using h

end D5.S3.Quantum.Matrix.MonomialGram
