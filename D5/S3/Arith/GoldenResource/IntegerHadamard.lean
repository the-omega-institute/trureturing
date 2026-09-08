/- GID: D5/S3/Arith/GoldenResource/IntegerHadamard
   generality: G
   mirror-B: D5/B/S3/Arith/GoldenResource/IntegerHadamard
   mirror-E: none(waiver:general-matrix-inequality)
   anchors: []
   utility: none
   digest: Positive definite integer matrices satisfy the diagonal determinant bound with equality precisely on diagonal matrices. -/

import D5.S3.Resource.LogDetDivergenceEquality

namespace D5.S3.Arith.GoldenResource.IntegerHadamard

open Matrix
open scoped ComplexOrder MatrixOrder
open D5.S3.Resource.LogDetDivergence

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

private theorem complex_posDef {A : Matrix n n ℝ} (hA : A.PosDef) :
    (A.map Complex.ofReal).PosDef := by
  have hsemi : (A.map Complex.ofReal).PosSemidef := by
    obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.posSemidef.nonneg
    have hmap : A.map Complex.ofReal =
        (B.map Complex.ofReal)ᴴ * B.map Complex.ofReal := by
      ext i j
      simp [hB, Matrix.mul_apply, Matrix.star_eq_conjTranspose]
    rw [hmap]
    exact Matrix.posSemidef_conjTranspose_mul_self _
  apply hsemi.posDef_iff_det_ne_zero.mpr
  have hd : (A.map Complex.ofReal).det = (A.det : ℂ) := by
    simpa [Complex.ofRealHom] using (Complex.ofRealHom.map_det A).symm
  rw [hd]
  exact_mod_cast ne_of_gt hA.det_pos

private theorem complex_hadamard {A : Matrix n n ℂ} (hA : A.PosDef) :
    A.det.re ≤ ∏ i, (A i i).re ∧
      (A.det.re = ∏ i, (A i i).re ↔ A = diagonal A.diag) := by
  let B := diagonal A.diag
  have hB : B.PosDef := Matrix.posDef_diagonal_iff.mpr fun i => hA.diag_pos
  have hdiag (i : n) : A i i = ((A i i).re : ℂ) :=
    Complex.ext rfl (hA.diag_pos (i := i)).2.symm
  have hprod : 0 < ∏ i, (A i i).re :=
    Finset.prod_pos fun i _ => (hA.diag_pos (i := i)).1
  have hdet : B.det.re = ∏ i, (A i i).re := by
    simp only [B, Matrix.det_diagonal, Matrix.diag]
    have h := congrArg Complex.re (Finset.prod_congr (s₁ := Finset.univ) rfl
      (fun i _ => hdiag i))
    simpa only [← Complex.ofReal_prod, Complex.ofReal_re] using h
  have htrace : (B⁻¹ * (A - B)).trace.re = 0 := by
    simp [B, Matrix.inv_diagonal, Matrix.trace, Matrix.diagonal_mul]
  have hdiv : logDetDivergence A B =
      Real.log (∏ i, (A i i).re) - Real.log A.det.re := by
    rw [barrier_bregman_link A B hA hB, barrierHeight, barrierHeight, htrace, hdet]
    ring
  have hnonneg := logDetDivergence_nonneg A B hA.posSemidef hA.isUnit
    hB.posSemidef hB.isUnit
  constructor
  · apply (Real.log_le_log_iff hA.det_pos.1 hprod).mp
    rw [hdiv] at hnonneg
    linarith
  · rw [← logDetDivergence_eq_zero_iff A B hA.posSemidef hA.isUnit
      hB.posSemidef hB.isUnit, hdiv, sub_eq_zero]
    exact ⟨fun h => congrArg Real.log h.symm,
      fun h => (Real.log_injOn_pos hprod hA.det_pos.1 h).symm⟩

/-- A real positive definite integer matrix has positive integer diagonal and determinant.
Its determinant is bounded by the diagonal product, with equality exactly for a diagonal matrix. -/
theorem integer_posDef_hadamard (T : Matrix n n ℤ)
    (hT : (T.map fun z => (z : ℝ)).PosDef) :
    (∀ i, 0 < T i i) ∧ 0 < T.det ∧ T.det ≤ ∏ i, T i i ∧
      (T.det = ∏ i, T i i ↔ T = diagonal T.diag) := by
  have hdiag (i : n) : 0 < T i i := by
    have h : (0 : ℝ) < (T i i : ℝ) := hT.diag_pos
    exact_mod_cast h
  have hdet : 0 < T.det := by
    have h := hT.det_pos
    rw [← Int.cast_det] at h
    exact_mod_cast h
  have hcomplex : (T.map fun z => (z : ℂ)).PosDef := by
    simpa [Matrix.map_map, Function.comp_def] using complex_posDef hT
  obtain ⟨hle, heq⟩ := complex_hadamard hcomplex
  have hdetC : (T.map fun z => (z : ℂ)).det.re = (T.det : ℝ) := by
    rw [← Int.cast_det]
    simp
  have hprodC : (∏ i, ((T.map fun z => (z : ℂ)) i i).re) =
      ((∏ i, T i i : ℤ) : ℝ) := by simp
  rw [hdetC, hprodC] at hle heq
  refine ⟨hdiag, hdet, by exact_mod_cast hle, ?_⟩
  constructor
  · intro h
    have hc := heq.mp (by exact_mod_cast h)
    ext i j
    have hij := congrArg (fun M : Matrix n n ℂ => M i j) hc
    by_cases h' : i = j
    · subst j
      simp
    · simpa [Matrix.diagonal_apply, h'] using hij
  · intro h
    conv_lhs => rw [h]
    simp only [Matrix.det_diagonal, Matrix.diag]

/-- For a nondiagonal positive definite integer matrix, the determinant loses at least one. -/
theorem nondiagonal_integer_det_gap (T : Matrix n n ℤ)
    (hT : (T.map fun z => (z : ℝ)).PosDef) (hoff : T ≠ diagonal T.diag) :
    T.det + 1 ≤ ∏ i, T i i := by
  obtain ⟨_, _, hle, heq⟩ := integer_posDef_hadamard T hT
  have hne := mt heq.mp hoff
  omega

-- The integer matrix with rows (2, 1) and (1, 2) satisfies both hypotheses.
example : ∃ T : Matrix (Fin 2) (Fin 2) ℤ,
    (T.map fun z => (z : ℝ)).PosDef ∧ T ≠ diagonal T.diag := by
  let T : Matrix (Fin 2) (Fin 2) ℤ :=
    1 + vecMulVec (fun _ => 1) (fun _ => 1)
  refine ⟨T, ?_, ?_⟩
  · have h := (Matrix.PosDef.one (n := Fin 2) (R := ℝ)).add_posSemidef
      (Matrix.posSemidef_vecMulVec_self_star (fun _ : Fin 2 => (1 : ℝ)))
    convert h using 1 <;> ext i j <;>
      simp [T, Matrix.map, Matrix.vecMulVec, Matrix.one_apply]
  · intro h
    have h01 := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℤ => A 0 1) h
    norm_num [T, Matrix.one_apply, Matrix.diagonal, Matrix.vecMulVec] at h01

#print axioms integer_posDef_hadamard
#print axioms nondiagonal_integer_det_gap

end
end D5.S3.Arith.GoldenResource.IntegerHadamard
