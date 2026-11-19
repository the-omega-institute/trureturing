/- GID: D5/S3/Quantum/Semigroups/WuRankOneEndpointClifford
   generality: I
   mirror-B: D5/B/S3/Quantum/Semigroups/WuRankOneEndpointClifford
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The signed endpoint acts diagonally on two-mode Pauli words. -/

import D5.S3.Quantum.Semigroups.WuRankOneEndpointFloor

/-! Pauli coordinates of the signed two-mode Clifford noise operator. -/

noncomputable section

open Matrix Kronecker
open D5.S3.Quantum.FiniteDimensional
open D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence

namespace WuRankOneEndpointFloor

def pauliWord (p q : Pauli) : TwoMode := pauliMatrix p ⊗ₖ pauliMatrix q

/-- Clifford degree in the order IX, IY, XZ, YZ for the generators. -/
def cliffordDegree : Pauli → Pauli → ℕ
  | .I, .I => 0
  | .I, .Z => 2
  | .Z, .I => 2
  | .Z, .Z => 4
  | .I, _ => 1
  | .Z, _ => 3
  | _, .I => 3
  | _, .Z => 1
  | _, _ => 2

private theorem lambda_pow_two : (lambda : ℂ) ^ 2 = 2 / 3 := by
  have h : lambda ^ 2 = 2 / 3 := Real.sq_sqrt (by norm_num)
  rw [← Complex.ofReal_pow, h]
  norm_num [Complex.ofReal_div]

set_option maxHeartbeats 3000000 in
/-- The actual signed factorization has the Clifford degree multiplier on each Pauli word. -/
theorem A₁_pauliWord (p q : Pauli) :
    A₁ (pauliWord p q) = ((lambda : ℂ) ^ cliffordDegree p q) • pauliWord p q := by
  have h3 : (lambda : ℂ) ^ 3 = (2 / 3 : ℂ) * lambda := by
    rw [pow_succ, lambda_pow_two]
  have h4 : (lambda : ℂ) ^ 4 = (4 / 9 : ℂ) := by
    rw [show (4 : ℕ) = 2 + 2 by decide, pow_add, lambda_pow_two]
    norm_num
  ext ⟨i,k⟩ ⟨j,l⟩
  rw [A₁_apply]
  cases p <;> cases q <;> fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num [pauliWord, cliffordDegree, pauliMatrix, qubitX, qubitZ, Matrix.one_apply,
      Matrix.kroneckerMap_apply, Matrix.mul_apply, Fin.sum_univ_two, Fin.rev,
      lambda_pow_two, h3, h4, -one_div, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring <;> simp

#print axioms A₁_pauliWord

end WuRankOneEndpointFloor
