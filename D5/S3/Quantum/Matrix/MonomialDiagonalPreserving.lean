/- GID: D5/S3/Quantum/Matrix/MonomialDiagonalPreserving
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/MonomialDiagonalPreserving
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   digest: Conjugating a diagonal matrix by a monomial matrix leaves it diagonal. -/

/- Library-search audit trail (2026-09-02). Commands reproduced literally as run, each with the
   count it returned. Paths are relative to the delivery worktree.

   grep -ril "monomial matrix"                .lake/packages/mathlib --include='*.lean' | wc -l -> 0
   grep -ril "generalized permutation matrix" .lake/packages/mathlib --include='*.lean' | wc -l -> 0
   grep -ril "diagonal preserving"            .lake/packages/mathlib --include='*.lean' | wc -l -> 0
   grep -ril "phase times permutation"        .lake/packages/mathlib --include='*.lean' | wc -l -> 0
     The same four over .lake/packages/batteries                                          -> 0 each
   grep -ril "IsDiag.*conj" .lake/packages/mathlib --include='*.lean' | wc -l              -> 1
     That file is Mathlib/LinearAlgebra/Matrix/IsDiag.lean, whose `IsDiag.conjTranspose` is a
     closure property of the predicate, not a statement about which matrices preserve diagonality.

   gh search prs --repo leanprover-community/mathlib4 --state open "monomial matrix" --limit 20
                                                                                           -> 0
   gh search prs --repo leanprover-community/mathlib4 --state open
     "generalized permutation matrix" --limit 20                                           -> 0
   gh search prs --repo leanprover-community/mathlib4 --state open
     "diagonal preserving unitary" --limit 20                                              -> 0
   gh search code --repo leanprover/cslib "monomial matrix" --limit 5                      -> 0
   gh search code --repo leanprover/cslib "IsDiag" --limit 5                               -> 0

   gh search code --repo TauCetiProject/TauCeti "monomial matrix" --limit 5                -> 1
   gh search code --repo TauCetiProject/TauCeti "IsDiag" --limit 8                         -> 5
     Both hit sets were opened and read. They are adjacent and are listed here so a reader can
     judge the overlap rather than take a bare count.
     * `TauCeti/LinearAlgebra/Matrix/GeneralLinearGroup/Diagonal/Bruhat.lean` aligns
       upper-triangular Bruhat data with the normalizer of the diagonal torus in `GL n`, where an
       upper-triangular monomial matrix is shown to be diagonal. That is a statement inside a
       group-theoretic decomposition, not a criterion for preserving diagonality under conjugation.
     * `TauCeti/RepresentationTheory/SU2/TorusConjugacy.lean` carries
       `isDiag_star_left_conjugate_of_eq_smul_one_add_smul`, which is specific to `SU 2`, runs
       through the Hermitian spectral theorem, and takes diagonality of `star U * H * U` as a
       hypothesis. Its implication runs in the opposite direction to the one proved here, and only
       in dimension two.

   git grep -Eil 'unitary.*diagonal' origin/dev -- 'D5/*.lean'                              -> 3
     All three were opened by digest: a logarithmic-derivative trace identity, a Cayley
     star-unitarity defect, and projected unitary dynamics inducing a doubly stochastic law.
     None concerns which conjugations preserve diagonality.
   git grep -Eil 'diagonal.*unitary|permutation.*phase' origin/dev -- 'D5/*.lean'           -> 0
   git ls-tree -r --name-only origin/dev -- D5 | grep -iE 'monomial|permut'                 -> 4
     All four opened by digest: three are observer-distance and horizon results about permutation
     readouts, and `UnimodularMonomialSubstitution` is the explicit inverse of a determinant-one
     monomial substitution on nonzero pairs, a number-theoretic object rather than a matrix class.

   The upstream results used rather than reproved are `Matrix.IsDiag`, `Matrix.diagonal_mul`,
   `Matrix.mul_diagonal` and the permutation-matrix API.
-/

import Mathlib

/-!
# Monomial matrices preserve diagonality

A monomial matrix, also called a generalized permutation matrix, carries exactly one nonzero entry
in each row and column: it is a permutation matrix with a nonzero scalar attached to each column.
Conjugating a diagonal matrix by such a matrix permutes and rescales the diagonal entries, so the
result is again diagonal.

Only that direction is proved here. The converse — that a matrix preserving diagonality under
conjugation must be monomial — is not proved and is not claimed, so nothing below should be read
as a characterization.
-/

namespace D5.S3.Quantum.Matrix.MonomialDiagonalPreserving

variable {n : Type*} [DecidableEq n] [Fintype n] {R : Type*} [CommRing R]

/-- The monomial matrix attached to a permutation and a family of scalars: the permutation matrix
of `sigma` with the scalar `c i` placed on the entry of row `i`. -/
def monomial (sigma : Equiv.Perm n) (c : n → R) : Matrix n n R :=
  Matrix.of fun i j => if j = sigma i then c i else 0

omit [Fintype n] in
@[simp] theorem monomial_apply (sigma : Equiv.Perm n) (c : n → R) (i j : n) :
    monomial sigma c i j = if j = sigma i then c i else 0 := by
  rfl

/-- A monomial matrix is the permutation matrix rescaled row by row. -/
theorem monomial_eq_diagonal_mul (sigma : Equiv.Perm n) (c : n → R) :
    monomial sigma c = Matrix.diagonal c * (Equiv.toPEquiv sigma).toMatrix := by
  ext i j
  simp [monomial, Matrix.diagonal_mul, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
    eq_comm]

/-- Conjugating a diagonal matrix by a monomial matrix keeps it diagonal. -/
theorem isDiag_monomial_mul_diagonal_mul_transpose
    (sigma : Equiv.Perm n) (c : n → R) (d : n → R) :
    (monomial sigma c * Matrix.diagonal d * _root_.Matrix.transpose (monomial sigma c)).IsDiag := by
  intro i j hij
  simp only [Matrix.mul_apply, Matrix.transpose_apply, monomial_apply,
    Matrix.diagonal_apply]
  by_cases hi : (sigma i) = (sigma j)
  · exact absurd (sigma.injective hi) hij
  · refine Finset.sum_eq_zero fun x _ => ?_
    rcases eq_or_ne x (sigma i) with hx | hx
    · subst hx
      simp [hi]
    · simp [hx]

end D5.S3.Quantum.Matrix.MonomialDiagonalPreserving
