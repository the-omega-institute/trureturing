import D5.S3.Quantum.Information.ActualPureQubitGeometry
import D5.S3.Quantum.Information.QubitNormalFormState
import D5.S3.QuantumBounds.CHSHWitness

/-! Transient exact checks of the source construction, with no retention claim. -/

open Matrix
open scoped BigOperators ComplexOrder Kronecker

noncomputable section
namespace V92IsotropicExactCheck

abbrev Q := Fin 2
abbrev Pair := Q × Q
abbrev Triple := Q × (Q × Q)
abbrev M2 := Matrix Q Q ℂ
abbrev M4 := Matrix Pair Pair ℂ
abbrev M8 := Matrix Triple Triple ℂ

def bell : M4 := D5.S3.QuantumBounds.CHSHWitness.bellDensity
def sigma (v : ℝ) : M4 := (v : ℂ) • bell + (((1-v)/4 : ℝ) : ℂ) • 1
def ab (ρ : M8) : M4 := fun p q => ∑ k : Q, ρ (p.1,p.2,k) (q.1,q.2,k)
def bc (ρ : M8) : M4 :=
  D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceLeft ρ

def g (b : Q) : Triple → ℂ := fun p =>
  if p.1 = p.2.1 ∧ p.2.2 = b then 1 / (Real.sqrt 2 : ℂ) else 0
def h (b : Q) : Triple → ℂ := fun p =>
  if p.1 = b ∧ p.2.1 = p.2.2 then 1 / (Real.sqrt 2 : ℂ) else 0
def f (b : Q) : Triple → ℂ := fun p => (2 * h b p - g b p) / (Real.sqrt 3 : ℂ)
def V (b : Q) : Matrix Triple Q ℂ := fun p i => if i = 0 then g b p else f b p
def chi (η : M2) : M8 := ∑ b : Q, (1/2 : ℝ) • (V b * η * (V b)ᴴ)
def eta (a : ℝ) (c : ℂ) : M2 := !![(a : ℂ), c; star c, (1-a : ℝ)]

example (η : M2) (hη : η.PosSemidef) : (chi η).PosSemidef := by
  apply Matrix.posSemidef_sum
  intro b _
  exact (hη.mul_mul_conjTranspose_same (V b)).smul (by norm_num : (0:ℝ) ≤ 1/2)

private theorem sqrt_two_sq : (Real.sqrt 2 : ℂ)^2 = 2 := by
  norm_cast
  exact Real.sq_sqrt (by norm_num)
private theorem sqrt_three_sq : (Real.sqrt 3 : ℂ)^2 = 3 := by
  norm_cast
  exact Real.sq_sqrt (by norm_num)

set_option maxHeartbeats 2000000 in
private theorem source_marginals (a : ℝ) (c : ℂ) :
    ab (chi (eta a c)) = (a : ℂ) • bell + (((1-a)/3 : ℝ) : ℂ) • (1-bell) ∧
    bc (chi (eta a c)) =
      (((2/3*(1-a)+2*c.re/Real.sqrt 3 : ℝ) : ℂ)) • bell +
      (((((1+2*a)/12)-c.re/(2*Real.sqrt 3) : ℝ) : ℂ)) • 1 := by
  have hs2 : (Real.sqrt 2 : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0:ℝ)<2)))
  have hs3 : (Real.sqrt 3 : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0:ℝ)<3)))
  have hc : (c.re : ℂ) = (c + star c)/2 := by
    apply Complex.ext <;> simp <;> ring
  constructor <;> ext ⟨i,j⟩ ⟨k,l⟩ <;>
    fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [ab, bc, D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceLeft,
      chi, V, eta, g, h, f, bell,
      D5.S3.QuantumBounds.CHSHWitness.bellDensity,
      D5.S3.QuantumBounds.CHSHWitness.bellVector,
      D5.S3.Quantum.QubitWitnesses.bellCoefficients,
      Matrix.vecMulVec_apply,
      D5.S3.QuantumBounds.CHSHWitness.complex_sqrt_two_inv_mul_self,
      Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_two, Fintype.sum_prod_type, Matrix.one_apply, hc] <;>
    push_cast <;> field_simp <;> ring_nf <;>
    simp [sqrt_two_sq, sqrt_three_sq] <;> ring

#print axioms source_marginals

end V92IsotropicExactCheck
