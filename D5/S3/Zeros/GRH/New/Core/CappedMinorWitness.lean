/- GID: D5/S3/Zeros/GRH/New/Core/CappedMinorWitness
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Core/CappedMinorWitness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Integral column factorization and a capped minor bound under a low-rank correction. -/

import D5.S3.Zeros.GRH.New.Core.MaximalMinors
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Matrix.Adjugate
import OmegaBuild.Commands

/-! Integral column factorization and a capped minor bound over a valuation domain. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Zeros.GRH.New.Core

open Matrix

/-- The columns of a divisibility-minimal nonzero full minor generate every column. -/
theorem exists_maximal_minor_factorization
    {O ι κ : Type*} [CommRing O] [IsDomain O] [ValuationRing O]
    [Fintype ι] [DecidableEq ι] [Finite κ]
    (A : Matrix ι κ O)
    (hA : ∃ s : ι ↪ κ, (A.submatrix id s).det ≠ 0) :
    ∃ (s : ι ↪ κ) (P : Matrix ι κ O),
      (A.submatrix id s).det ≠ 0 ∧ A = A.submatrix id s * P := by
  classical
  let := Fintype.ofFinite κ
  obtain ⟨s, hs, hD⟩ := exists_maximal_minor_dvd_det_mul A hA
  let D : Matrix ι ι O := A.submatrix id s
  have hcramer (i : ι) (j : κ) : D.det ∣ D.cramer (A.col j) i := by
    let t : ι → κ := Function.update (s : ι → κ) i j
    let S : Matrix κ ι O := Matrix.of fun k l => if k = t l then 1 else 0
    have hselect : A * S = D.updateCol i (A.col j) := by
      ext r l
      have hentry : (A * S) r l = A r (t l) := by
        simp [Matrix.mul_apply, S, mul_ite]
      rw [hentry]
      by_cases h : l = i
      · subst l
        simp [t]
      · simp [t, D, h]
    rw [Matrix.cramer_apply, ← hselect]
    exact hD S
  choose p hp using hcramer
  let P : Matrix ι κ O := Matrix.of p
  refine ⟨s, P, hs, ?_⟩
  change A = D * P
  ext r j
  have hcol : D.cramer (A.col j) = D.det • P.col j := by
    funext i
    exact hp i j
  have hvec := Matrix.mulVec_cramer D (A.col j)
  rw [hcol, Matrix.mulVec_smul] at hvec
  apply mul_left_cancel₀ hs
  exact (congrFun hvec r).symm

/-- A unit-determinant correction yields an actual nonzero full minor of the capped matrix
whose determinant divides the stated product. -/
theorem exists_capped_minor_dvd_of_low_rank_correction
    {O ι ν : Type*} [CommRing O] [IsDomain O] [ValuationRing O]
    [Fintype ι] [DecidableEq ι] [Fintype ν]
    (A X U : Matrix ι ι O) (B : Matrix ι ν O) (C : Matrix ν ι O) (a z : O)
    (hcorrection : A * X + B * C = a • U) (hU : IsUnit U.det)
    (hz : z ≠ 0) :
    ∃ s : ι ↪ ι ⊕ ι,
      ((Matrix.fromCols A (z • (1 : Matrix ι ι O))).submatrix id s).det ≠ 0 ∧
      ((Matrix.fromCols A (z • (1 : Matrix ι ι O))).submatrix id s).det ∣
        a ^ Fintype.card ι * z ^ Fintype.card ν := by
  classical
  let Z := Matrix.fromCols A (z • (1 : Matrix ι ι O))
  have hZ : ∃ s : ι ↪ ι ⊕ ι, (Z.submatrix id s).det ≠ 0 := by
    let s : ι ↪ ι ⊕ ι := ⟨Sum.inr, Sum.inr_injective⟩
    have hright : Z.submatrix id s = z • (1 : Matrix ι ι O) := rfl
    exact ⟨s, by rw [hright, Matrix.det_smul, Matrix.det_one, mul_one]; exact pow_ne_zero _ hz⟩
  obtain ⟨s, P, hs, hZfactor⟩ := exists_maximal_minor_factorization Z hZ
  let D := Z.submatrix id s
  change Z = D * P at hZfactor
  let E0 := Matrix.fromBlocks (A * X) B C (-1 : Matrix ν ν O)
  let R := Matrix.fromBlocks (1 : Matrix ι ι O) (0 : Matrix ι ν O) C (1 : Matrix ν ν O)
  have hE0R : E0 * R = Matrix.fromBlocks (a • U) B (0 : Matrix ν ι O)
      (-1 : Matrix ν ν O) := by
    simp [E0, R, Matrix.fromBlocks_multiply, hcorrection]
  have hdetE0 : E0.det = (a • U).det * (-1 : Matrix ν ν O).det := by
    have h := congrArg Matrix.det hE0R
    simpa only [Matrix.det_mul, R, Matrix.det_fromBlocks_zero₁₂, Matrix.det_fromBlocks_zero₂₁,
      Matrix.det_one, mul_one] using h
  let E := E0 * Matrix.fromBlocks (1 : Matrix ι ι O) (0 : Matrix ι ν O)
    (0 : Matrix ν ι O) (z • (1 : Matrix ν ν O))
  have hE : E = Matrix.fromBlocks (A * X) (z • B) C (-(z • (1 : Matrix ν ν O))) := by
    simp [E, E0, Matrix.fromBlocks_multiply, Matrix.mul_smul]
  have hdetE : E.det = (a ^ Fintype.card ι * z ^ Fintype.card ν) *
      (U.det * (-1 : O) ^ Fintype.card ν) := by
    simp only [E, Matrix.det_mul, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one,
      one_mul, Matrix.det_smul, mul_one, hdetE0, Matrix.det_neg]
    ac_rfl
  -- This selector gives the two top blocks of E from the columns of Z.
  let T := Matrix.fromBlocks X (0 : Matrix ι ν O) (0 : Matrix ι ι O) B
  have htop : Z * T = Matrix.fromCols (A * X) (z • B) := by
    ext i (j | j)
    · simp [Z, T, Matrix.mul_apply, Fintype.sum_sum_type]
    · calc
        (Z * T) i (Sum.inr j) = ((z • (1 : Matrix ι ι O)) * B) i j := by
          simp [Z, T, Matrix.mul_apply, Fintype.sum_sum_type]
        _ = _ := by rw [Matrix.smul_mul, Matrix.one_mul]; rfl
  let Q := P * T
  have htopFactor : D * Q = Matrix.fromCols (A * X) (z • B) := by
    change D * (P * T) = _
    rw [← Matrix.mul_assoc, ← hZfactor, htop]
  let Q₁ := Q.submatrix id Sum.inl
  let Q₂ := Q.submatrix id Sum.inr
  have hleft : D * Q₁ = A * X := by
    ext i j
    exact congrFun (congrFun htopFactor i) (Sum.inl j)
  have hright : D * Q₂ = z • B := by
    ext i j
    exact congrFun (congrFun htopFactor i) (Sum.inr j)
  have hfactor : E = Matrix.fromBlocks D (0 : Matrix ι ν O) (0 : Matrix ν ι O) 1 *
      Matrix.fromBlocks Q₁ Q₂ C (-(z • (1 : Matrix ν ν O))) := by
    rw [hE, Matrix.fromBlocks_multiply]
    simp [hleft, hright]
  have hdiv : D.det ∣ E.det := by
    rw [hfactor, Matrix.det_mul, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one]
    exact dvd_mul_right _ _
  have hunit : IsUnit (U.det * (-1 : O) ^ Fintype.card ν) :=
    hU.mul (isUnit_one.neg.pow _)
  rw [hdetE] at hdiv
  exact ⟨s, hs, hunit.dvd_mul_right.mp hdiv⟩

end D5.S3.Zeros.GRH.New.Core
