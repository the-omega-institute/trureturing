import CFMPStrictAngleCofactors297Transient
import D5.S3.Geometry.Hyperideal.LengthGramBody
import Mathlib.LinearAlgebra.Matrix.Adjugate

noncomputable section
set_option autoImplicit false
open scoped BigOperators Matrix
open CFMPStrictAngleCofactors297Transient
open D5.S3.Geometry.Hyperideal.ActualCornerTransport (endpoints)
open D5.S3.Geometry.Hyperideal.LengthGramBody (lengthGram)

namespace CFMPCofactorLengthGram303Transient

/-- The actual diagonal congruence of the original cofactor matrix. -/
def cofactorScale (G : Matrix (Fin 4) (Fin 4) ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.diagonal (fun i => (Real.sqrt (-G.adjugate i i))⁻¹)

def cofactorGram (G : Matrix (Fin 4) (Fin 4) ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  -(cofactorScale G * G.adjugate * cofactorScale G)

private theorem cofactorGram_entry (G : Matrix (Fin 4) (Fin 4) ℝ)
    (hd : ∀ i, G.adjugate i i < 0) (i j : Fin 4) :
    cofactorGram G i j = -G.adjugate i j /
      Real.sqrt (G.adjugate i i * G.adjugate j j) := by
  have hs : Real.sqrt (G.adjugate i i * G.adjugate j j) =
      Real.sqrt (-G.adjugate i i) * Real.sqrt (-G.adjugate j j) := by
    simpa only [neg_mul_neg] using
      Real.sqrt_mul (neg_nonneg.mpr (hd i).le) (-G.adjugate j j)
  rw [hs]
  simp [cofactorGram, cofactorScale, Matrix.mul_diagonal, Matrix.diagonal_mul,
    div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]

private theorem cofactorGram_diag (G : Matrix (Fin 4) (Fin 4) ℝ)
    (hd : ∀ i, G.adjugate i i < 0) (i : Fin 4) :
    cofactorGram G i i = 1 := by
  rw [cofactorGram_entry G hd, Real.sqrt_mul_self_eq_abs, abs_of_neg (hd i)]
  exact div_self (neg_ne_zero.mpr (hd i).ne)

/-- A negative original determinant and negative principal cofactors give
negative determinant after the actual cofactor congruence. -/
theorem cofactorGram_det_neg (G : Matrix (Fin 4) (Fin 4) ℝ)
    (hG : G.det < 0) (hd : ∀ i, G.adjugate i i < 0) :
    (cofactorGram G).det < 0 := by
  have hS : 0 < (cofactorScale G).det := by
    rw [cofactorScale, Matrix.det_diagonal]
    exact Finset.prod_pos (fun i _ => inv_pos.mpr (Real.sqrt_pos.mpr (neg_pos.mpr (hd i))))
  have hcube : G.det ^ 3 < 0 := by
    calc
      G.det ^ 3 = G.det ^ 2 * G.det := by ring
      _ < 0 := mul_neg_of_pos_of_neg (sq_pos_of_ne_zero hG.ne) hG
  have heq : (cofactorGram G).det =
      (cofactorScale G).det * G.det ^ 3 * (cofactorScale G).det := by
    simp only [cofactorGram, Matrix.det_neg, Matrix.det_mul, Matrix.det_adjugate]
    norm_num
  rw [heq]
  exact mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hS hcube) hS

/-- All six cofactor lengths form exactly the original length Gram matrix,
including its original endpoint order and unit diagonal. -/
theorem cofactor_lengthGram_eq (G : Matrix (Fin 4) (Fin 4) ℝ)
    (hG : G.IsSymm) (hd : ∀ i, G.adjugate i i < 0)
    (hg : ∀ i j, i ≠ j → 0 < G.adjugate i j ∧
      G.adjugate i i * G.adjugate j j < (G.adjugate i j)^2) :
    lengthGram (cofactorLength G) = cofactorGram G := by
  have hc := cofactor_lengths_positive G hd hg
  have hedge (q : Fin 6) :
      cofactorGram G (endpoints q).1 (endpoints q).2 =
        -Real.cosh (cofactorLength G q) := by
    rw [cofactorGram_entry G hd, (hc q).2]
    exact neg_div _ _
  have hs (i j : Fin 4) : cofactorGram G j i = cofactorGram G i j := by
    rw [cofactorGram_entry G hd, cofactorGram_entry G hd, hG.adjugate.apply i j,
      mul_comm (G.adjugate j j) (G.adjugate i i)]
  have h01 : cofactorGram G 0 1 = -Real.cosh (cofactorLength G 0) := by simpa [endpoints] using hedge 0
  have h02 : cofactorGram G 0 2 = -Real.cosh (cofactorLength G 1) := by simpa [endpoints] using hedge 1
  have h03 : cofactorGram G 0 3 = -Real.cosh (cofactorLength G 2) := by simpa [endpoints] using hedge 2
  have h23 : cofactorGram G 2 3 = -Real.cosh (cofactorLength G 3) := by simpa [endpoints] using hedge 3
  have h13 : cofactorGram G 1 3 = -Real.cosh (cofactorLength G 4) := by simpa [endpoints] using hedge 4
  have h12 : cofactorGram G 1 2 = -Real.cosh (cofactorLength G 5) := by simpa [endpoints] using hedge 5
  symm
  ext i j
  fin_cases i <;> fin_cases j
  · exact cofactorGram_diag G hd 0
  · exact h01
  · exact h02
  · exact h03
  · exact (hs 0 1).trans h01
  · exact cofactorGram_diag G hd 1
  · exact h12
  · exact h13
  · exact (hs 0 2).trans h02
  · exact (hs 1 2).trans h12
  · exact cofactorGram_diag G hd 2
  · exact h23
  · exact (hs 0 3).trans h03
  · exact (hs 1 3).trans h13
  · exact (hs 2 3).trans h23
  · exact cofactorGram_diag G hd 3

/-- The constructed positive lengths satisfy the negative determinant
criterion before any prescribed-angle identification is used. -/
theorem cofactor_lengths_det_neg (G : Matrix (Fin 4) (Fin 4) ℝ)
    (hG : G.IsSymm) (hdet : G.det < 0) (hd : ∀ i, G.adjugate i i < 0)
    (hg : ∀ i j, i ≠ j → 0 < G.adjugate i j ∧
      G.adjugate i i * G.adjugate j j < (G.adjugate i j)^2) :
    (∀ q, 0 < cofactorLength G q) ∧ (lengthGram (cofactorLength G)).det < 0 := by
  refine ⟨fun q => (cofactor_lengths_positive G hd hg q).1, ?_⟩
  rw [cofactor_lengthGram_eq G hG hd hg]
  exact cofactorGram_det_neg G hdet hd

end CFMPCofactorLengthGram303Transient

run_cmd do
  let env := (← Lean.getEnv).setExporting false
  for name in [``CFMPCofactorLengthGram303Transient.cofactorGram_det_neg,
      ``CFMPCofactorLengthGram303Transient.cofactor_lengthGram_eq,
      ``CFMPCofactorLengthGram303Transient.cofactor_lengths_det_neg] do
    unless (env.checked.get.find? name).isSome do
      Lean.throwError m!"CFMP303 cofactor Gram theorem absent: {name}"
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        Lean.throwError m!"CFMP303 disallowed axiom {ax}"
    Lean.logInfo m!"CFMP303 CHECKED {name} axioms={axioms}"
