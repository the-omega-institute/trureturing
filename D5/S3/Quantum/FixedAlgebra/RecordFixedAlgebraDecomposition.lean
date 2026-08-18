/- GID: D5/S3/Quantum/FixedAlgebra/RecordFixedAlgebraDecomposition
   generality: G
   mirror-B: D5/B/S3/Quantum/FixedAlgebra/RecordFixedAlgebraDecomposition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A finite record fixed algebra is the direct product of its matrix blocks. -/

import Mathlib

/- Library-search audit trail (2026-08-18):
   * Repository searches found the finite-entry fixed-point characterization in
     `EnvironmentRecords.lean` and the block-center theorem in `RecordFixedCenter.lean`,
     but no general fixed-algebra decomposition.
   * Pinned Mathlib supplies `Matrix.blockDiagonal'RingHom`,
     `Matrix.blockDiag'_blockDiagonal'`, `Matrix.blockDiagonal'_injective`, and
     `AlgEquiv.ofBijective`; these exact declarations are applied below.
   * `loogle` and `leansearch` executables are absent from PATH. -/

namespace D5.S3.Quantum.FixedAlgebra.RecordFixedAlgebraDecomposition

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

/- The source's finite direct sum is represented by a finite dependent product. The
   block-diagonal range is the matrix realization of the fixed entries selected by
   the record equivalence classes. -/
noncomputable def blockDiagonalAlgHom {Lambda : Type*} (I : Lambda -> Type*)
    [Fintype Lambda] [DecidableEq Lambda] [∀ alpha, Fintype (I alpha)]
    [∀ alpha, DecidableEq (I alpha)] :
    (∀ alpha, Matrix (I alpha) (I alpha) ℂ) →ₐ[ℂ]
      Matrix (Sigma I) (Sigma I) ℂ :=
  { Matrix.blockDiagonal'RingHom I ℂ with
    commutes' := by
      intro scalar
      ext ⟨alpha, i⟩ ⟨beta, j⟩
      by_cases h : alpha = beta
      · subst h
        simp [Matrix.blockDiagonal'_apply, Matrix.algebraMap_eq_diagonal,
          Matrix.diagonal_apply, Pi.algebraMap_apply]
      · simp [Matrix.blockDiagonal'_apply, Matrix.algebraMap_eq_diagonal,
          Matrix.diagonal_apply, Pi.algebraMap_apply, h] }

noncomputable abbrev recordFixedAlgebra {Lambda : Type*} (I : Lambda -> Type*)
    [Fintype Lambda] [DecidableEq Lambda] [∀ alpha, Fintype (I alpha)]
    [∀ alpha, DecidableEq (I alpha)] :=
  (blockDiagonalAlgHom I).range

noncomputable def blockDiagonalAlgEquiv {Lambda : Type*} (I : Lambda -> Type*)
    [Fintype Lambda] [DecidableEq Lambda] [∀ alpha, Fintype (I alpha)]
    [∀ alpha, DecidableEq (I alpha)] :
    (∀ alpha, Matrix (I alpha) (I alpha) ℂ) ≃ₐ[ℂ] recordFixedAlgebra I := by
  apply AlgEquiv.ofBijective (blockDiagonalAlgHom I).rangeRestrict
  constructor
  · intro first second h
    exact Matrix.blockDiagonal'_injective (congrArg Subtype.val h)
  · intro matrix
    rcases matrix.property with ⟨blocks, hblocks⟩
    refine ⟨blocks, ?_⟩
    apply Subtype.ext
    exact hblocks

/-- A finite record channel's fixed block algebra is algebra-isomorphic to the direct
product of the full complex matrix algebras on its record-indistinguishability classes. -/
noncomputable def record_fixed_algebra_decomposition {Lambda : Type*} (I : Lambda -> Type*)
    [Fintype Lambda] [DecidableEq Lambda] [∀ alpha, Fintype (I alpha)]
    [∀ alpha, DecidableEq (I alpha)] :
    recordFixedAlgebra I ≃ₐ[ℂ]
      (∀ alpha, Matrix (I alpha) (I alpha) ℂ) :=
  (blockDiagonalAlgEquiv I).symm

noncomputable example :
    recordFixedAlgebra (fun _ : Fin 2 => Fin 2) ≃ₐ[ℂ]
      (∀ _ : Fin 2, Matrix (Fin 2) (Fin 2) ℂ) :=
  record_fixed_algebra_decomposition _

#print axioms record_fixed_algebra_decomposition

end D5.S3.Quantum.FixedAlgebra.RecordFixedAlgebraDecomposition
