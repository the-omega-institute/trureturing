import D5.S3.Quantum.Information.ActualPureQubitGeometry
import D5.S3.Quantum.Information.QubitNormalFormState
import D5.S3.QuantumBounds.CHSHWitness
import D5.S3.Quantum.Entanglement.BellPureStateMixedMarginal

/-! Transient exact checks of the source construction, with no retention claim. -/

open Matrix
open D5.S3.Quantum.Information.ActualPureQubitCostInfimum
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

def kernelVector : Fin 4 → Triple → ℂ := ![
  (fun p => if p = (0,1,0) then 1 else 0),
  (fun p => if p = (1,0,1) then 1 else 0),
  (fun p => ((if p = (0,0,0) then 1 else 0) -
    (if p = (0,1,1) then 1 else 0) -
    (if p = (1,1,0) then 1 else 0)) / (Real.sqrt 3 : ℂ)),
  (fun p => ((if p = (1,1,1) then 1 else 0) -
    (if p = (0,0,1) then 1 else 0) -
    (if p = (1,0,0) then 1 else 0)) / (Real.sqrt 3 : ℂ))]

def kernel : M8 := ∑ j : Fin 4, Matrix.vecMulVec (kernelVector j) (star (kernelVector j))
def tau0 : M8 := (1/4 : ℝ) • kernel
def support : M8 := ∑ b : Q, V b * (V b)ᴴ
def compression (ρ : M8) : M2 := ∑ b : Q, (V b)ᴴ * ρ * V b
def rightReadout (M : M2) : ℂ :=
  M 0 0 / 4 + (Real.sqrt 3 : ℂ) / 4 * (M 0 1 + M 1 0) + 3 * M 1 1 / 4

private theorem kernel_psd : kernel.PosSemidef := by
  apply Matrix.posSemidef_sum
  intro j _
  exact Matrix.posSemidef_vecMulVec_self_star _

private theorem compression_psd (ρ : M8) (hp : ρ.PosSemidef) :
    (compression ρ).PosSemidef := by
  apply Matrix.posSemidef_sum
  intro b _
  exact hp.conjTranspose_mul_mul_same _

set_option maxHeartbeats 2000000 in
private theorem orthoblocks (b c : Q) : (V b)ᴴ * V c = if b=c then 1 else 0 := by
  have hs2 : (Real.sqrt 2 : ℂ) ≠ 0 :=
    D5.S3.QuantumBounds.CHSHWitness.complex_sqrt_two_ne_zero
  have hs3 : (Real.sqrt 3 : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0:ℝ)<3)))
  fin_cases b <;> fin_cases c <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [V, g, h, f, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two] <;>
    field_simp <;> ring_nf <;>
    simp [sqrt_two_sq, sqrt_three_sq] <;> norm_num [map_ofNat] <;> ring

set_option maxHeartbeats 2000000 in
private theorem support_kernel : support + kernel = 1 := by
  have hs2 : (Real.sqrt 2 : ℂ) ≠ 0 :=
    D5.S3.QuantumBounds.CHSHWitness.complex_sqrt_two_ne_zero
  have hs3 : (Real.sqrt 3 : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0:ℝ)<3)))
  ext ⟨a,b,c⟩ ⟨d,e,f'⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    fin_cases d <;> fin_cases e <;> fin_cases f' <;>
    norm_num [support, kernel, kernelVector, V, g, h, f,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.vecMulVec_apply,
      Fin.sum_univ_succ] <;>
    field_simp <;> ring_nf <;>
    simp [sqrt_two_sq, sqrt_three_sq] <;> norm_num [map_ofNat] <;> ring

private theorem compression_trace (ρ : M8) :
    Matrix.trace (compression ρ) = Matrix.trace (ρ * support) := by
  simp only [compression, support, Matrix.trace_sum, Matrix.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [Matrix.trace_mul_cycle, Matrix.trace_mul_comm]

set_option maxHeartbeats 2000000 in
private theorem compression_readouts (ρ : M8) :
    (compression ρ) 0 0 = Matrix.trace (ab ρ * bell) ∧
    rightReadout (compression ρ) = Matrix.trace (bc ρ * bell) := by
  have hs2 : (Real.sqrt 2 : ℂ) ≠ 0 :=
    D5.S3.QuantumBounds.CHSHWitness.complex_sqrt_two_ne_zero
  have hs3 : (Real.sqrt 3 : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0:ℝ)<3)))
  constructor <;>
    simp [compression, rightReadout, ab, bc,
      D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceLeft,
      V, g, h, f, bell,
      D5.S3.QuantumBounds.CHSHWitness.bellDensity,
      D5.S3.QuantumBounds.CHSHWitness.bellVector,
      D5.S3.Quantum.QubitWitnesses.bellCoefficients,
      D5.S3.QuantumBounds.CHSHWitness.complex_sqrt_two_inv_mul_self,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.vecMulVec_apply,
      Matrix.trace, Fintype.sum_prod_type, Fin.sum_univ_two] <;>
    field_simp <;> ring_nf <;>
    simp [sqrt_two_sq, sqrt_three_sq] <;> norm_num [map_ofNat] <;> ring

private theorem sigma_bell_readout (v : ℝ) :
    Matrix.trace (sigma v * bell) = (((1+3*v)/4 : ℝ) : ℂ) := by
  have hi : bell * bell = bell :=
    D5.S3.Quantum.Entanglement.BellPureStateMixedMarginal.
      bell_pure_state_has_maximally_mixed_marginal.2.2.2.2.1
  have ht : Matrix.trace bell = 1 :=
    D5.S3.QuantumBounds.CHSHWitness.bell_density_is_state.2
  simp only [sigma, add_mul, Matrix.smul_mul, one_mul,
    Matrix.trace_add, Matrix.trace_smul, hi, ht, smul_eq_mul, mul_one]
  push_cast
  ring

set_option maxHeartbeats 2000000 in
private theorem kernel_marginals :
    ab kernel = (4/3 : ℂ) • (1-bell) ∧ bc kernel = (4/3 : ℂ) • (1-bell) := by
  have hs2 : (Real.sqrt 2 : ℂ) ≠ 0 :=
    D5.S3.QuantumBounds.CHSHWitness.complex_sqrt_two_ne_zero
  have hs3 : (Real.sqrt 3 : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0:ℝ)<3)))
  constructor <;> ext ⟨i,j⟩ ⟨k,l⟩ <;>
    fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num [ab, bc, D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceLeft,
      kernel, kernelVector, Matrix.vecMulVec_apply, bell,
      D5.S3.QuantumBounds.CHSHWitness.bellDensity,
      D5.S3.QuantumBounds.CHSHWitness.bellVector,
      D5.S3.Quantum.QubitWitnesses.bellCoefficients,
      D5.S3.QuantumBounds.CHSHWitness.complex_sqrt_two_inv_mul_self,
      Fin.sum_univ_succ] <;>
    field_simp <;> ring_nf <;>
    simp [sqrt_two_sq, sqrt_three_sq] <;> norm_num [map_ofNat] <;> ring

private theorem marginal_linear (a b : ℝ) (ρ σ : M8) :
    ab (a • ρ + b • σ) = a • ab ρ + b • ab σ ∧
    bc (a • ρ + b • σ) = a • bc ρ + b • bc σ := by
  constructor <;> ext p q <;>
    simp [ab, bc, D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceLeft,
      Finset.sum_add_distrib, Finset.smul_sum]

private theorem corner_construction :
    tau0.PosSemidef ∧ Matrix.trace tau0 = 1 ∧
      ab tau0 = sigma (-1/3) ∧ bc tau0 = sigma (-1/3) := by
  have htr : Matrix.trace kernel = 4 := by
    rw [← trace_ab, kernel_marginals.1]
    norm_num [Matrix.trace_smul, Matrix.trace_sub, bell,
      D5.S3.QuantumBounds.CHSHWitness.bell_density_is_state.2]
  have hl := (marginal_linear (1/4) 0 kernel 0).1
  have hr := (marginal_linear (1/4) 0 kernel 0).2
  simp only [zero_smul, add_zero] at hl hr
  refine ⟨kernel_psd.smul (by norm_num : (0:ℝ) ≤ 1/4), ?_, ?_, ?_⟩
  · norm_num [tau0, Matrix.trace_smul, htr]
  · change ab ((1/4 : ℝ) • kernel) = _
    rw [hl, kernel_marginals.1]
    ext p q
    simp [sigma, Matrix.smul_apply, Matrix.sub_apply, Complex.real_smul]
    ring
  · change bc ((1/4 : ℝ) • kernel) = _
    rw [hr, kernel_marginals.2]
    ext p q
    simp [sigma, Matrix.smul_apply, Matrix.sub_apply, Complex.real_smul]
    ring

def ellipse : Set (ℝ × ℝ) := {p | p.1^2+p.2^2+p.1*p.2 ≤ p.1+p.2}
def pminus : ℝ × ℝ := (-1/3,-1/3)
def Compatible (p : ℝ × ℝ) : Prop :=
  ∃ ρ : M8, ρ.PosSemidef ∧ Matrix.trace ρ = 1 ∧ ab ρ = sigma p.1 ∧ bc ρ = sigma p.2

private theorem sigma_affine (v w a b : ℝ) (hab : a+b=1) :
    a • sigma v + b • sigma w = sigma (a*v+b*w) := by
  have hI : a*((1-v)/4)+b*((1-w)/4) = (1-(a*v+b*w))/4 := by
    linear_combination hab / 4
  have hs (r : ℝ) (M : M4) : r • M = (r : ℂ) • M := by
    ext p q
    simp [Complex.real_smul]
  rw [hs, hs]
  calc
    _ = (((a*v+b*w : ℝ) : ℂ)) • bell +
        (((a*((1-v)/4)+b*((1-w)/4) : ℝ) : ℂ)) • 1 := by
      unfold sigma
      push_cast
      module
    _ = sigma (a*v+b*w) := by rw [hI]; rfl

private theorem compatible_convex : Convex ℝ {p | Compatible p} := by
  rintro p ⟨ρ, hp, ht, hAB, hBC⟩ q ⟨σ, hq, hs, hAB', hBC'⟩ a b ha hb hab
  refine ⟨a • ρ + b • σ, (hp.smul ha).add (hq.smul hb), ?_, ?_, ?_⟩
  · rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, ht, hs]
    simpa [Complex.real_smul, ← Complex.ofReal_add] using congrArg Complex.ofReal hab
  · change ab (a • ρ + b • σ) = sigma (a*p.1+b*q.1)
    rw [(marginal_linear a b ρ σ).1, hAB, hAB', sigma_affine _ _ _ _ hab]
  · change bc (a • ρ + b • σ) = sigma (a*p.2+b*q.2)
    rw [(marginal_linear a b ρ σ).2, hBC, hBC', sigma_affine _ _ _ _ hab]

private theorem hull_sufficiency (p : ℝ × ℝ)
    (hp : p ∈ convexHull ℝ (insert pminus ellipse)) : Compatible p := by
  apply convexHull_min (t := {p | Compatible p}) ?_ compatible_convex hp
  intro q hq
  rcases Set.mem_insert_iff.mp hq with hq | hq
  · subst q
    exact ⟨tau0, corner_construction⟩
  · exact ellipse_construction q.1 q.2 hq

#print axioms hull_sufficiency

private theorem hull_necessity (p : ℝ × ℝ) (hp : Compatible p) :
    p ∈ convexHull ℝ (insert pminus ellipse) := by
  rcases p with ⟨v,w⟩
  obtain ⟨ρ, hρ, htr, hAB, hBC⟩ := hp
  let M := compression ρ
  have hM : M.PosSemidef := compression_psd ρ hρ
  let t := (Matrix.trace M).re
  have htreal : Matrix.trace M = (t : ℂ) := by
    apply Complex.ext
    · rfl
    · simpa using (Complex.nonneg_iff.mp hM.trace_nonneg).2
  have ht0 : 0 ≤ t := (Complex.nonneg_iff.mp hM.trace_nonneg).1
  have ht1 : t ≤ 1 := by
    have hk := RHLinalg.trace_mul_nonneg_of_posSemidef hρ kernel_psd
    have he : Matrix.trace (ρ * support) + Matrix.trace (ρ * kernel) = 1 := by
      rw [← Matrix.trace_add, ← Matrix.mul_add, support_kernel, mul_one, htr]
    have her := congrArg Complex.re he
    rw [← compression_trace] at her
    change t + (Matrix.trace (ρ * kernel)).re = 1 at her
    linarith
  have hread := compression_readouts ρ
  rw [hAB, hBC, sigma_bell_readout, sigma_bell_readout] at hread
  change M 0 0 = (((1+3*v)/4 : ℝ) : ℂ) ∧
    rightReadout M = (((1+3*w)/4 : ℝ) : ℂ) at hread
  by_cases ht : t=0
  · have hMz : M=0 := hM.trace_eq_zero_iff.mp (by rw [htreal, ht]; simp)
    have hv : v = -1/3 := by
      have h := congrArg Complex.re hread.1
      simp [hMz] at h
      linarith
    have hw : w = -1/3 := by
      have h := congrArg Complex.re hread.2
      simp [hMz, rightReadout] at h
      linarith
    have he : (v,w) = pminus := Prod.ext hv hw
    rw [he]
    exact subset_convexHull ℝ _ (Set.mem_insert _ _)
  · have htpos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm ht)
    let N : M2 := (1/t : ℝ) • M
    have hN : N.PosSemidef := hM.smul (by positivity : (0:ℝ) ≤ 1/t)
    have hNt : Matrix.trace N = 1 := by
      dsimp [N]
      rw [Matrix.trace_smul, htreal]
      simp [Complex.real_smul, ← Complex.ofReal_mul, ht]
    let r := bloch N
    have hn := norm_bloch_le_trace_of_posSemidef N hN
    rw [hNt] at hn
    norm_num at hn
    have hnorm : ‖r‖^2 ≤ 1 := by
      dsimp [r]
      nlinarith [norm_nonneg (bloch N)]
    rw [EuclideanSpace.real_norm_sq_eq] at hnorm
    simp only [Fin.sum_univ_three] at hnorm
    have hxz : (r 0)^2+(r 2)^2 ≤ 1 := by nlinarith [sq_nonneg (r 1)]
    have heN : N = blochMatrix 1 r := by
      simpa only [hNt, Complex.one_re] using
        (bloch_geometry_of_isHermitian N hN.isHermitian).1
    have hLN : (N 0 0).re = (1+r 2)/2 := by
      rw [heN]
      simp [blochMatrix]
    have hRN : (rightReadout N).re = (2-r 2+Real.sqrt 3*r 0)/4 := by
      rw [heN]
      norm_num [rightReadout, blochMatrix, Complex.mul_re, Complex.div_re]
      ring
    have hscaleL : (N 0 0).re = (M 0 0).re/t := by
      simp [N, Matrix.smul_apply, Complex.real_smul, div_eq_mul_inv, mul_comm]
    have hrlin : rightReadout N = (1/t : ℝ) • rightReadout M := by
      simp only [N, rightReadout, Matrix.smul_apply, Complex.real_smul]
      ring
    have hscaleR : (rightReadout N).re = (rightReadout M).re/t := by
      rw [hrlin]
      simp [Complex.real_smul, div_eq_mul_inv, mul_comm]
    have hL := congrArg Complex.re hread.1
    have hR := congrArg Complex.re hread.2
    simp only [Complex.ofReal_re] at hL hR
    rw [hLN, hL] at hscaleL
    rw [hRN, hR] at hscaleR
    have hFL : (1+3*v)/4 = t*((1+r 2)/2) := by
      simpa [mul_comm] using (div_eq_iff ht).mp hscaleL.symm
    have hFR : (1+3*w)/4 = t*((2-r 2+Real.sqrt 3*r 0)/4) := by
      simpa [mul_comm] using (div_eq_iff ht).mp hscaleR.symm
    let q : ℝ × ℝ := ((1+2*r 2)/3, (1-r 2+Real.sqrt 3*r 0)/3)
    have hq : q ∈ ellipse := by
      have hs3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
      have hi : q.1^2+q.2^2+q.1*q.2-q.1-q.2 = ((r 0)^2+(r 2)^2-1)/3 := by
        dsimp [q]
        ring_nf
        simp only [hs3]
        ring
      change q.1^2+q.2^2+q.1*q.2 ≤ q.1+q.2
      linarith
    have he : (v,w) = (1-t) • pminus + t • q := by
      apply Prod.ext
      · change v = (1-t)*(-1/3)+t*((1+2*r 2)/3)
        nlinarith [hFL]
      · change w = (1-t)*(-1/3)+t*((1-r 2+Real.sqrt 3*r 0)/3)
        nlinarith [hFR]
    rw [he]
    exact (convex_convexHull ℝ _)
      (subset_convexHull ℝ _ (Set.mem_insert _ _))
      (subset_convexHull ℝ _ (Set.mem_insert_of_mem _ hq))
      (sub_nonneg.mpr ht1) ht0 (by ring)

private theorem full_compatibility (v w : ℝ) :
    (∃ ρ : M8, ρ.PosSemidef ∧ Matrix.trace ρ = 1 ∧ ab ρ = sigma v ∧ bc ρ = sigma w) ↔
      (v,w) ∈ convexHull ℝ (insert pminus ellipse) :=
  ⟨hull_necessity (v,w), hull_sufficiency (v,w)⟩

#print axioms full_compatibility

end V92IsotropicExactCheck
