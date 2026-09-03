/- GID: D5/S3/Quantum/Matrix/MonomialColumnGram
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/MonomialColumnGram
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   digest: Transposing a monomial matrix inverts its permutation, which gives the column Gram. -/

/- Library-search audit trail (2026-09-03). Commands reproduced literally as run, each ending in
   `wc -l`; none truncated. Declaration patterns are the wide form, so attribute-prefixed,
   private and `def` forms are included. Where a hit is reported, its file is named from
   `git grep -l` rather than from memory.

   P='^(@\[[^]]*\][[:space:]]*)?(private )?(noncomputable )?(theorem|lemma|def|abbrev) '

   git grep -hoE "${P}[A-Za-z0-9_']*monomial[A-Za-z0-9_']*(transpose|gram|column|symm)
     [A-Za-z0-9_']*" origin/dev -- 'D5/**/*.lean' | wc -l                                    -> 5
     All five opened, with their files taken from `git grep -l`. The five are exactly:
       `isDiag_monomial_mul_diagonal_mul_transpose` in
         D5/S3/Quantum/Matrix/MonomialDiagonalPreserving.lean;
       `monomial_mul_diagonal_mul_transpose` and `monomial_mul_transpose` in
         D5/S3/Quantum/Matrix/MonomialGram.lean — the row-side results this module builds on;
       `normalizedCircleHaar_monomial_gram` in
         D5/S3/Weil/TestFunctions/ToeplitzContactSupport.lean and
       `normalized_circle_haar_monomial_gram` in
         D5/S3/Weil/TestFunctions/ExactTruncatedHaarFloor.lean — two different files, both
         private, computing Fourier orthogonality for scalar monomials on the circle. They carry
         `monomial` and `gram` in their names and concern a different object.
     None of the five transposes the constructor or states a column-side product.

   git grep -clE '_root_\.Matrix\.transpose \(monomial [a-z]+ [a-z]+\) \*' origin/dev
     -- 'D5/**/*.lean' | wc -l                                                               -> 0
     No file matches that pattern. The pattern is an exact spelling, so this is a negative for
     the pattern, not a semantic guarantee about every way the product could be written.
   git grep -clE 'sigma\.symm' origin/dev -- 'D5/S3/Quantum/Matrix/*.lean' | wc -l           -> 0
     The inverse permutation does not appear in this directory at all, which is what the first
     result below supplies.

   grep -rlE "theorem.*transpose.*(PEquiv|Equiv.*toMatrix|permutation)" .lake/packages/mathlib
     --include='*.lean' | wc -l                                                              -> 1
     Opened: Mathlib/Data/Matrix/PEquiv.lean, whose `@[simp] transpose_toMatrix_toPEquiv_apply`
     gives `(f.toPEquiv.toMatrix)ᵀ j = Pi.single (f.symm j) 1`, and line 81 gives
     `PEquiv.toMatrix_symm`. Those are the permutation-matrix half of the first result below.
     Searching mathlib for a matrix constructor of this kind:
       grep -rhoE "^(noncomputable )?def [A-Za-z0-9_']*[Mm]onomial[A-Za-z0-9_']*"
         Mathlib/Data/Matrix Mathlib/LinearAlgebra/Matrix --include='*.lean' | wc -l        -> 0
       the same pattern over all of Mathlib                                                 -> 8
     The eight are polynomial-side (`monomial`, `monomialOneHom`, `basisMonomials`,
     `MonomialOrder`, `evalPrettyMonomial`, …); none is under a matrix directory. So the
     constructor this module transposes is the repository's own, and the statement is not
     available upstream — though, as noted in the module docstring, it is reachable from the
     frozen factorization plus the mathlib lemmas just cited.

   Batteries, CSLib and TauCeti were searched for earlier nodes of this family and returned
   nothing; no separate query was issued here, so those are carried negatives rather than fresh
   ones. Zulip was not queried, so that domain is absent rather than negative.
-/

import D5.S3.Quantum.Matrix.MonomialGram

/-!
# Transposing a monomial matrix, and the column Gram form

The first result is an API lemma: transposing a monomial matrix gives a monomial matrix again,
for the inverse permutation, with the scales relabelled along that inverse. It is not new
mathematics. The frozen factorization `monomial_eq_diagonal_mul` together with mathlib's
`PEquiv.toMatrix_symm` and `Matrix.diagonal_transpose` already reach it in a few rewrites; the
entrywise proof below is a direct route to the same statement, which no file states by name.

Given it, the column-side conjugate needs no new computation: it is the row-side identity of the
frozen sibling read at `sigma⁻¹`. The two identities are different statements — the row form is
indexed by `sigma i`, the column form by `sigma⁻¹ j` — but the second costs no mathematics once
the first is available. What this module contributes is the named lemma and the two identities
it makes immediate, not new structure.
-/

namespace D5.S3.Quantum.Matrix.MonomialColumnGram

open D5.S3.Quantum.Matrix.MonomialDiagonalPreserving
open D5.S3.Quantum.Matrix.MonomialGram

variable {n : Type*} [DecidableEq n] [Fintype n] {R : Type*} [CommRing R]

omit [Fintype n] in
/-- Transposing a monomial matrix inverts its permutation and relabels the scales along that
inverse. -/
theorem monomial_transpose (sigma : Equiv.Perm n) (c : n → R) :
    _root_.Matrix.transpose (monomial sigma c)
      = monomial sigma.symm (fun j => c (sigma.symm j)) := by
  ext j i
  simp only [_root_.Matrix.transpose_apply, monomial_apply]
  by_cases h : j = sigma i
  · subst h
    simp [Equiv.symm_apply_apply]
  · have h' : i ≠ sigma.symm j := fun hi => h (by rw [hi, Equiv.apply_symm_apply])
    simp [h, h']

/-- The column-side conjugate of a diagonal matrix by a monomial matrix, indexed by the inverse
permutation. -/
theorem transpose_mul_diagonal_mul_monomial (sigma : Equiv.Perm n) (c d : n → R) :
    _root_.Matrix.transpose (monomial sigma c) * Matrix.diagonal d * monomial sigma c
      = Matrix.diagonal (fun j => d (sigma.symm j) * c (sigma.symm j) ^ 2) := by
  have hback : monomial sigma c
      = _root_.Matrix.transpose (monomial sigma.symm (fun j => c (sigma.symm j))) := by
    rw [monomial_transpose]
    ext i j
    simp [Equiv.symm_apply_apply]
  conv_lhs => rw [monomial_transpose, hback]
  exact monomial_mul_diagonal_mul_transpose sigma.symm (fun j => c (sigma.symm j)) d

/-- The column Gram matrix of a monomial matrix, the case `d = 1`. -/
theorem transpose_mul_monomial (sigma : Equiv.Perm n) (c : n → R) :
    _root_.Matrix.transpose (monomial sigma c) * monomial sigma c
      = Matrix.diagonal (fun j => c (sigma.symm j) ^ 2) := by
  have h := transpose_mul_diagonal_mul_monomial sigma c 1
  simpa using h

end D5.S3.Quantum.Matrix.MonomialColumnGram
