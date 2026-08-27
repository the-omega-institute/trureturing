/- GID: D5/S3/Quantum/FixedAlgebra/ChannelFixedBlockDecomposition
   generality: G
   mirror-B: D5/B/S3/Quantum/FixedAlgebra/ChannelFixedBlockDecomposition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Identify record-channel fixed matrices with their canonical full class blocks. -/

/- Library-search audit trail (2026-08-27):
   * `SingletonRecordClassicality.recordGram` and `recordChannel` are the
     canonical record-semantics primitives and are imported rather than copied.
   * `RecordFixedAlgebraDecomposition.blockDiagonalAlgHom` is the canonical
     finite dependent block embedding. Its range-defined `recordFixedAlgebra`
     is not used as the channel fixed algebra.
   * Pinned Mathlib supplies `Equiv.sigmaFiberEquiv`,
     `Matrix.reindexAlgEquiv`, `Subalgebra.equivOfEq`, and
     `AlgEquiv.ofBijective`. No exact channel-fixed decomposition was found. -/

import D5.S3.Quantum.FixedAlgebra.SingletonRecordClassicality
import D5.S3.Quantum.FixedAlgebra.RecordFixedAlgebraDecomposition

namespace D5.S3.Quantum.FixedAlgebra.ChannelFixedBlockDecomposition

open D5.S3.Quantum.FixedAlgebra.SingletonRecordClassicality
open D5.S3.Quantum.FixedAlgebra.RecordFixedAlgebraDecomposition

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Matrices supported inside the fibers of `classOf`. This subalgebra is
defined from the source class relation, independently of the channel and the
block-diagonal embedding. -/
def classBlockSubalgebra {d : Nat} {Lambda : Type*} [DecidableEq Lambda]
    (classOf : Fin d -> Lambda) : Subalgebra ℂ (Matrix (Fin d) (Fin d) ℂ) where
  carrier := {rho | ∀ i j, classOf i ≠ classOf j -> rho i j = 0}
  zero_mem' := by
    intro i j hij
    rfl
  add_mem' := by
    intro rho sigma hrho hsigma i j hij
    simp [hrho i j hij, hsigma i j hij]
  mul_mem' := by
    intro rho sigma hrho hsigma i j hij
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro k hk
    by_cases hik : classOf i = classOf k
    · have hkj : classOf k ≠ classOf j := by
        intro hkj
        exact hij (hik.trans hkj)
      rw [hsigma k j hkj, mul_zero]
    · rw [hrho i k hik, zero_mul]
  one_mem' := by
    intro i j hij
    have hne : i ≠ j := by
      intro hij'
      exact hij (congrArg classOf hij')
    simp [hne]
  algebraMap_mem' := by
    intro scalar i j hij
    have hne : i ≠ j := by
      intro hij'
      exact hij (congrArg classOf hij')
    simp [Matrix.algebraMap_eq_diagonal, hne]

/-- Embed the full matrix algebra on every class fiber, then canonically
reindex the sigma of those fibers back to the original address type. -/
noncomputable def classifiedBlockAlgHom
    {d : Nat} {Lambda : Type*} [Fintype Lambda] [DecidableEq Lambda]
    (classOf : Fin d -> Lambda) :
    (∀ alpha, Matrix {i : Fin d // classOf i = alpha}
        {i : Fin d // classOf i = alpha} ℂ) →ₐ[ℂ]
      Matrix (Fin d) (Fin d) ℂ :=
  (Matrix.reindexAlgEquiv ℂ ℂ (Equiv.sigmaFiberEquiv classOf)).toAlgHom.comp
    (blockDiagonalAlgHom (fun alpha => {i : Fin d // classOf i = alpha}))

private theorem classified_block_alg_hom_same_class
    {d : Nat} {Lambda : Type*} [Fintype Lambda] [DecidableEq Lambda]
    (classOf : Fin d -> Lambda)
    (blocks : ∀ alpha, Matrix {i : Fin d // classOf i = alpha}
      {i : Fin d // classOf i = alpha} ℂ)
    (alpha : Lambda) (i j : {i : Fin d // classOf i = alpha}) :
    classifiedBlockAlgHom classOf blocks i.1 j.1 = blocks alpha i j := by
  have hi : (Equiv.sigmaFiberEquiv classOf).symm i.1 = ⟨alpha, i⟩ := by
    apply (Equiv.sigmaFiberEquiv classOf).injective
    simp
  have hj : (Equiv.sigmaFiberEquiv classOf).symm j.1 = ⟨alpha, j⟩ := by
    apply (Equiv.sigmaFiberEquiv classOf).injective
    simp
  change Matrix.blockDiagonal' blocks
      ((Equiv.sigmaFiberEquiv classOf).symm i.1)
      ((Equiv.sigmaFiberEquiv classOf).symm j.1) = blocks alpha i j
  rw [hi, hj, Matrix.blockDiagonal'_apply_eq]

private theorem classified_block_alg_hom_off_class
    {d : Nat} {Lambda : Type*} [Fintype Lambda] [DecidableEq Lambda]
    (classOf : Fin d -> Lambda)
    (blocks : ∀ alpha, Matrix {i : Fin d // classOf i = alpha}
      {i : Fin d // classOf i = alpha} ℂ)
    (i j : Fin d) (hij : classOf i ≠ classOf j) :
    classifiedBlockAlgHom classOf blocks i j = 0 := by
  simp [classifiedBlockAlgHom, blockDiagonalAlgHom, Matrix.blockDiagonal'_apply, hij]

private theorem classified_block_range_eq_class_block
    {d : Nat} {Lambda : Type*} [Fintype Lambda] [DecidableEq Lambda]
    (classOf : Fin d -> Lambda) :
    (classifiedBlockAlgHom classOf).range = classBlockSubalgebra classOf := by
  ext rho
  constructor
  · rintro ⟨blocks, rfl⟩ i j hij
    exact classified_block_alg_hom_off_class classOf blocks i j hij
  · intro hrho
    let blocks : ∀ alpha, Matrix {i : Fin d // classOf i = alpha}
        {i : Fin d // classOf i = alpha} ℂ :=
      fun _ i j => rho i.1 j.1
    refine ⟨blocks, ?_⟩
    ext i j
    change classifiedBlockAlgHom classOf blocks i j = rho i j
    by_cases hij : classOf i = classOf j
    · let ii : {k : Fin d // classOf k = classOf i} := ⟨i, rfl⟩
      let jj : {k : Fin d // classOf k = classOf i} := ⟨j, hij.symm⟩
      simpa [blocks, ii, jj] using
        classified_block_alg_hom_same_class classOf blocks (classOf i) ii jj
    · rw [classified_block_alg_hom_off_class classOf blocks i j hij]
      exact (hrho i j hij).symm

/-- The canonical block-diagonal map, with the canonical sigma-fiber
reindexing, is an algebra equivalence onto the independently defined
class-supported subalgebra. -/
noncomputable def classifiedBlockAlgEquiv
    {d : Nat} {Lambda : Type*} [Fintype Lambda] [DecidableEq Lambda]
    (classOf : Fin d -> Lambda) :
    (∀ alpha, Matrix {i : Fin d // classOf i = alpha}
        {i : Fin d // classOf i = alpha} ℂ) ≃ₐ[ℂ]
      classBlockSubalgebra classOf := by
  let hom := classifiedBlockAlgHom classOf
  let toRange :
      (∀ alpha, Matrix {i : Fin d // classOf i = alpha}
          {i : Fin d // classOf i = alpha} ℂ) ≃ₐ[ℂ] hom.range := by
    apply AlgEquiv.ofBijective hom.rangeRestrict
    constructor
    · intro first second h
      have hval : hom first = hom second := congrArg Subtype.val h
      change
        Matrix.reindexAlgEquiv ℂ ℂ (Equiv.sigmaFiberEquiv classOf)
            (Matrix.blockDiagonal' first) =
          Matrix.reindexAlgEquiv ℂ ℂ (Equiv.sigmaFiberEquiv classOf)
            (Matrix.blockDiagonal' second) at hval
      exact Matrix.blockDiagonal'_injective
        ((Matrix.reindexAlgEquiv ℂ ℂ
          (Equiv.sigmaFiberEquiv classOf)).injective hval)
    · intro rho
      rcases rho.property with ⟨blocks, hblocks⟩
      exact ⟨blocks, Subtype.ext hblocks⟩
  exact toRange.trans
    (Subalgebra.equivOfEq hom.range (classBlockSubalgebra classOf)
      (classified_block_range_eq_class_block classOf))

/-- A record channel fixes exactly the class-supported matrices, and the
canonical block algebra equivalence recovers every within-class matrix entry.
Thus its fixed algebra is the direct product of the full matrix algebras on
the record classes. -/
theorem channel_fixed_block_decomposition
    {d e : Nat} {Lambda : Type*} [Fintype Lambda] [DecidableEq Lambda]
    (record : Fin d -> Fin e -> ℂ) (classOf : Fin d -> Lambda)
    (hClasses : ∀ i j, recordGram record i j = 1 ↔ classOf i = classOf j) :
    (∀ rho : Matrix (Fin d) (Fin d) ℂ,
      recordChannel record rho = rho ↔ rho ∈ classBlockSubalgebra classOf) ∧
    (∀ (blocks : ∀ alpha, Matrix {i : Fin d // classOf i = alpha}
          {i : Fin d // classOf i = alpha} ℂ)
        (alpha : Lambda) (i j : {i : Fin d // classOf i = alpha}),
      ((classifiedBlockAlgEquiv classOf blocks : classBlockSubalgebra classOf) :
          Matrix (Fin d) (Fin d) ℂ) i.1 j.1 = blocks alpha i j) := by
  constructor
  · intro rho
    constructor
    · intro hFixed i j hij
      have hEntry := congrArg (fun matrix : Matrix (Fin d) (Fin d) ℂ => matrix i j) hFixed
      have hProduct : (recordGram record i j - 1) * rho i j = 0 := by
        calc
          (recordGram record i j - 1) * rho i j =
              recordGram record i j * rho i j - rho i j := by ring
          _ = 0 := sub_eq_zero.mpr hEntry
      have hGram : recordGram record i j - 1 ≠ 0 :=
        sub_ne_zero.mpr (fun h => hij ((hClasses i j).mp h))
      exact (mul_eq_zero.mp hProduct).resolve_left hGram
    · intro hSupported
      ext i j
      change recordGram record i j * rho i j = rho i j
      by_cases hij : classOf i = classOf j
      · rw [(hClasses i j).mpr hij]
        simp
      · rw [hSupported i j hij]
        simp
  · intro blocks alpha i j
    change classifiedBlockAlgHom classOf blocks i.1 j.1 = blocks alpha i j
    exact classified_block_alg_hom_same_class classOf blocks alpha i j

#print axioms channel_fixed_block_decomposition

end D5.S3.Quantum.FixedAlgebra.ChannelFixedBlockDecomposition
