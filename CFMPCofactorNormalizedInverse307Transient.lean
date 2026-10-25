import CFMPCofactorLengthGram303Transient
import CFMPNormalizedInverseInvolution298Transient

noncomputable section
set_option autoImplicit false
open CFMPNormalizedInverseTangent107
open CFMPNormalizedInverseInvolution298Transient
open CFMPStrictAngleCofactors297Transient
open CFMPCofactorLengthGram303Transient
open D5.S3.Geometry.Hyperideal.LengthGramBody (lengthGram)

namespace CFMPCofactorNormalizedInverse307Transient

/-- Cofactor normalization is exactly the original normalized inverse,
with the sign of det(G) retained in the square-root cancellation. -/
theorem cofactorGram_eq_normalizedInverse (G : Matrix (Fin 4) (Fin 4) ℝ)
    (hdet : G.det < 0) (hd : ∀ i, G.adjugate i i < 0) :
    cofactorGram G = normalizedInverse G := by
  have hinv (i j : Fin 4) : G⁻¹ i j = G.adjugate i j / G.det := by
    simp [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul,
      div_eq_mul_inv, mul_comm]
  have hs (i : Fin 4) : Real.sqrt (G⁻¹ i i) =
      Real.sqrt (-G.adjugate i i) / Real.sqrt (-G.det) := by
    rw [hinv]
    have heq : G.adjugate i i / G.det = (-G.adjugate i i) / (-G.det) := by ring
    rw [heq, Real.sqrt_div (neg_nonneg.mpr (hd i).le)]
  have hcoef : Real.sqrt (-G.det) * Real.sqrt (-G.det) / G.det = -1 := by
    rw [Real.mul_self_sqrt (neg_nonneg.mpr hdet.le), neg_div, div_self hdet.ne]
  ext i j
  simp only [cofactorGram, cofactorScale, normalizedInverse, normalScale,
    Matrix.neg_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]
  rw [hinv i j, hs i, hs j]
  simp only [inv_div]
  calc
    -((Real.sqrt (-G.adjugate i i))⁻¹ * G.adjugate i j *
        (Real.sqrt (-G.adjugate j j))⁻¹) =
        -1 * (G.adjugate i j /
          (Real.sqrt (-G.adjugate i i) * Real.sqrt (-G.adjugate j j))) := by ring
    _ = (Real.sqrt (-G.det) * Real.sqrt (-G.det) / G.det) *
        (G.adjugate i j /
          (Real.sqrt (-G.adjugate i i) * Real.sqrt (-G.adjugate j j))) := by rw [hcoef]
    _ = _ := by ring

/-- The normalized inverse of the constructed original length matrix
recovers the original unit-diagonal matrix itself. -/
theorem normalizedInverse_lengthGram_cofactorLength
    (G : Matrix (Fin 4) (Fin 4) ℝ) (hG : G.IsSymm)
    (hdet : G.det < 0) (hdiag : ∀ i, G i i = 1)
    (hd : ∀ i, G.adjugate i i < 0)
    (hg : ∀ i j, i ≠ j → 0 < G.adjugate i j ∧
      G.adjugate i i * G.adjugate j j < (G.adjugate i j)^2) :
    normalizedInverse (lengthGram (cofactorLength G)) = G := by
  rw [cofactor_lengthGram_eq G hG hd hg, cofactorGram_eq_normalizedInverse G hdet hd]
  apply normalizedInverse_involutive G (isUnit_iff_ne_zero.mpr hdet.ne) hdiag
  intro i
  rw [Matrix.inv_def]
  simp only [Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  exact mul_pos_of_neg_of_neg (inv_neg''.mpr hdet) (hd i)

end CFMPCofactorNormalizedInverse307Transient

run_cmd do
  let env := (← Lean.getEnv).setExporting false
  for name in [``CFMPCofactorNormalizedInverse307Transient.cofactorGram_eq_normalizedInverse,
      ``CFMPCofactorNormalizedInverse307Transient.normalizedInverse_lengthGram_cofactorLength] do
    unless (env.checked.get.find? name).isSome do
      Lean.throwError m!"CFMP307 normalized cofactor bridge absent: {name}"
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        Lean.throwError m!"CFMP307 disallowed axiom {ax}"
    Lean.logInfo m!"CFMP307 CHECKED {name} axioms={axioms}"
