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

private theorem chi_psd (η : M2) (hη : η.PosSemidef) : (chi η).PosSemidef := by
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
    simp [sqrt_two_sq, sqrt_three_sq] <;> norm_num [map_ofNat] <;> ring

#print axioms source_marginals

private theorem trace_ab (ρ : M8) : Matrix.trace (ab ρ) = Matrix.trace ρ := by
  simp [Matrix.trace, ab, Fintype.sum_prod_type]

private theorem chi_trace (a : ℝ) (c : ℂ) : Matrix.trace (chi (eta a c)) = 1 := by
  rw [← trace_ab, (source_marginals a c).1]
  norm_num [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_sub, bell,
    D5.S3.QuantumBounds.CHSHWitness.bell_density_is_state.2]
  push_cast
  ring

private theorem ellipse_construction (v w : ℝ) (hE : v^2+w^2+v*w ≤ v+w) :
    ∃ ρ : M8, ρ.PosSemidef ∧ Matrix.trace ρ = 1 ∧ ab ρ = sigma v ∧ bc ρ = sigma w := by
  let x := Real.sqrt 3 / 2 * (v+2*w-1)
  let z := (3*v-1)/2
  let a := (1+z)/2
  let c : ℂ := ((x/2 : ℝ) : ℂ)
  have hs3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hid : x^2+z^2 = 3*(v^2+w^2+v*w-v-w)+1 := by
    dsimp [x, z]
    ring_nf
    rw [hs3]
    ring
  have hd : x^2+z^2 ≤ 1 := by rw [hid]; linarith
  have hm : eta a c =
      D5.S3.Quantum.Information.QubitNormalFormState.qubitMatrix x z := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [eta, D5.S3.Quantum.Information.QubitNormalFormState.qubitMatrix, a, c] <;>
      push_cast <;> ring
  have hp := D5.S3.Quantum.Information.PartialTraceMutualInformation.density_posSemidef
    (D5.S3.Quantum.Information.QubitNormalFormState.qubitState x z hd)
  change (D5.S3.Quantum.Information.QubitNormalFormState.qubitMatrix x z).PosSemidef at hp
  rw [← hm] at hp
  refine ⟨chi (eta a c), chi_psd _ hp, chi_trace a c, ?_, ?_⟩
  · have ha : a-(1-a)/3 = v := by dsimp [a, z]; ring
    have hu : (1-a)/3 = (1-v)/4 := by dsimp [a, z]; ring
    rw [(source_marginals a c).1]
    calc
      _ = (((a-(1-a)/3 : ℝ) : ℂ)) • bell + (((1-a)/3 : ℝ) : ℂ) • 1 := by
        push_cast
        module
      _ = sigma v := by rw [ha, hu]; rfl
  · have hn : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0:ℝ)<3))
    have hw : 2/3*(1-a)+2*c.re/Real.sqrt 3 = w := by
      simp only [c, Complex.ofReal_re]
      dsimp [a, z, x]
      field_simp
      ring
    have hi : (1+2*a)/12-c.re/(2*Real.sqrt 3) = (1-w)/4 := by
      simp only [c, Complex.ofReal_re]
      dsimp [a, z, x]
      field_simp
      ring
    rw [(source_marginals a c).2, hw, hi]
    rfl

#print axioms ellipse_construction

end V92IsotropicExactCheck
