/- GID: D5/S3/Quantum/Gauge/DiracLandauEulerHeisenberg4D
   generality: G
   mirror-B: D5/B/S3/Quantum/Gauge/DiracLandauEulerHeisenberg4D
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Dirac level pairing, Euler–Heisenberg invariants, and polarization Hessians. -/

import OmegaBuild.Commands
import OmegaMath.Analysis.HermiteOscillator
import OmegaMath.Analysis.EulerHeisenbergProperTime
import D5.S3.Geometry.Lorentz.DiracCliffordSpinors4D
import D5.S3.Geometry.Lorentz.MaxwellRainichStressEnergy4D
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-! The gauge sign fixes the Pauli Zeeman term. The spin label in the energy
formula is minus one half of the corresponding standard Pauli eigenvalue. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix
open _root_.D5.S3.Geometry.Lorentz.DiracCliffordSpinors4D (γ)

namespace D5.S3.Quantum.Gauge.DiracLandauEulerHeisenberg4D

open D5.S3.Geometry.Lorentz.MaxwellRainichStressEnergy4D

def landauEnergySq (m pz qB g : ℝ) (n : ℕ) (σ : ℝ) : ℝ :=
  m ^ 2 + pz ^ 2 + qB * (2 * (n : ℝ) + 1 - g * σ)

theorem dirac_g2_zero_mode_iff (m pz qB g : ℝ) (hq : 0 < qB) :
    (qB * (2 * (0 : ℝ) + 1 - g * (1 / 2)) = 0 ↔ g = 2) ∧
    (landauEnergySq m pz qB g 0 (1 / 2) = m ^ 2 + pz ^ 2 ↔ g = 2) := by
  have hzero : qB * (2 * (0 : ℝ) + 1 - g * (1 / 2)) = 0 ↔ g = 2 := by
    rw [mul_eq_zero, or_iff_right hq.ne']
    constructor <;> intro h <;> linarith
  refine ⟨hzero, ?_⟩
  rw [← hzero]
  simp [landauEnergySq]

/-- Every spectral level has exactly the displayed spin and oscillator labels. -/
theorem dirac_landau_exact_twofold_degeneracy (m pz qB : ℝ) (hq : 0 < qB)
    (k n : ℕ) (σ : ℝ) (hσ : σ = 1 / 2 ∨ σ = -(1 / 2)) :
    landauEnergySq m pz qB 2 n σ = m ^ 2 + pz ^ 2 + 2 * (k : ℝ) * qB ↔
      (n = k ∧ σ = 1 / 2) ∨ (0 < k ∧ n = k - 1 ∧ σ = -(1 / 2)) := by
  have h : landauEnergySq m pz qB 2 n σ = m ^ 2 + pz ^ 2 + 2 * (k : ℝ) * qB ↔
      2 * (n : ℝ) + 1 - 2 * σ = 2 * (k : ℝ) := by
    unfold landauEnergySq
    rw [add_right_inj, mul_comm (2 * (k : ℝ)) qB, mul_right_inj' hq.ne']
  rw [h]
  rcases hσ with rfl | rfl
  · have hlabels : (2 * (n : ℝ) + 1 - 2 * (1 / 2) = 2 * (k : ℝ)) ↔ n = k := by
      constructor
      · intro h
        exact_mod_cast (show (n : ℝ) = k by linarith)
      · rintro rfl
        ring
    rw [hlabels]
    norm_num
  · have hlabels : (2 * (n : ℝ) + 1 - 2 * -(1 / 2) = 2 * (k : ℝ)) ↔ n + 1 = k := by
      constructor
      · intro h
        exact_mod_cast (show (n : ℝ) + 1 = k by linarith)
      · intro h
        have hc : (n : ℝ) + 1 = k := by exact_mod_cast h
        linarith
    rw [hlabels]
    norm_num
    omega

def pauliX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
def pauliY : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]
def pauliZ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- A Pauli matrix tensored with a scalar operator. -/
def pauliTensor {A : Type*} [Ring A] [Algebra ℂ A]
    (S : Matrix (Fin 2) (Fin 2) ℂ) (p : A) : Matrix (Fin 2) (Fin 2) A :=
  Matrix.of fun i j => S i j • p

def pauliOperator {A : Type*} [Ring A] [Algebra ℂ A] (px py : A) : Matrix (Fin 2) (Fin 2) A :=
  pauliTensor pauliX px + pauliTensor pauliY py

def pauliSquareTerm {A : Type*} [Ring A] [Algebra ℂ A] (πx πy : A) (qB : ℝ) :
    Matrix (Fin 2) (Fin 2) A :=
  pauliTensor 1 (πx ^ 2 + πy ^ 2) +
    pauliTensor pauliZ (algebraMap ℂ A (qB : ℂ))

private theorem pauli_square {A : Type*} [Ring A] [Algebra ℂ A] (πx πy : A) (qB : ℝ)
    (h : πx * πy - πy * πx = algebraMap ℂ A (-Complex.I * (qB : ℂ))) :
    pauliOperator πx πy ^ 2 = pauliSquareTerm πx πy qB := by
  have hI : Complex.I • (πx * πy - πy * πx) = algebraMap ℂ A (qB : ℂ) := by
    rw [h, Algebra.smul_def, ← map_mul]
    congr 1
    rw [← mul_assoc, mul_neg, Complex.I_mul_I, neg_neg, one_mul]
  have hII : Complex.I • (Complex.I • (πy * πy)) = -(πy * πy) := by
    rw [smul_smul, Complex.I_mul_I, neg_one_smul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliOperator, pauliSquareTerm, pauliTensor, pauliX, pauliY, pauliZ, pow_two,
      Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_two,
      add_mul, mul_add, mul_smul_comm, smul_mul_assoc, hII] <;>
    rw [← hI, smul_sub] <;> abel

/-- The transverse gauge is represented after Fourier transformation in the second coordinate. -/
def magneticMomentumX : Module.End ℂ (Polynomial ℂ) :=
  -Complex.I • Polynomial.derivative

def magneticMomentumY (ky qB : ℝ) : Module.End ℂ (Polynomial ℂ) where
  toFun p := (Polynomial.C (ky : ℂ) + Polynomial.C (qB : ℂ) * Polynomial.X) * p
  map_add' p q := mul_add _ p q
  map_smul' r p := by simp

private theorem magnetic_commutator (ky qB : ℝ) :
    magneticMomentumX * magneticMomentumY ky qB -
        magneticMomentumY ky qB * magneticMomentumX =
      algebraMap ℂ (Module.End ℂ (Polynomial ℂ)) (-Complex.I * (qB : ℂ)) := by
  apply LinearMap.ext
  intro p
  change -Complex.I • Polynomial.derivative
      ((Polynomial.C (ky : ℂ) + Polynomial.C (qB : ℂ) * Polynomial.X) * p) -
    (Polynomial.C (ky : ℂ) + Polynomial.C (qB : ℂ) * Polynomial.X) *
      (-Complex.I • Polynomial.derivative p) = (-Complex.I * (qB : ℂ)) • p
  rw [Polynomial.derivative_mul, Polynomial.derivative_add, Polynomial.derivative_C,
    Polynomial.derivative_C_mul, Polynomial.derivative_X, mul_one, zero_add, smul_add,
    mul_smul_comm, add_sub_cancel_right, ← Polynomial.smul_eq_C_mul, smul_smul]

private theorem dirac_pauli_blocks (i : Fin 3) :
    (γ i.succ).submatrix (Fin.castAdd 2) (Fin.natAdd 2) =
      (![pauliX, pauliY, pauliZ] : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ) i := by
  ext a b
  fin_cases i <;> fin_cases a <;> fin_cases b <;>
    simp [γ, pauliX, pauliY, pauliZ, Matrix.submatrix_apply] <;>
    change GaussianInt.toComplex _ = _ <;>
    apply Complex.ext <;>
    simp only [← GaussianInt.intCast_re, ← GaussianInt.intCast_im] <;>
    first
    | change ((0 : ℤ) : ℝ) = _
      norm_num
    | change ((1 : ℤ) : ℝ) = _
      norm_num
    | change ((-1 : ℤ) : ℝ) = _
      norm_num

/-- The Pauli square follows from the canonical relations in any complex algebra.
The polynomial representation verifies those relations through the product rule. -/
theorem dirac_pauli_square_identity (qB : ℝ) :
    (∀ i : Fin 3,
      (γ i.succ).submatrix (Fin.castAdd 2) (Fin.natAdd 2) =
        (![pauliX, pauliY, pauliZ] : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ) i) ∧
    (∀ (A : Type) [Ring A] [Algebra ℂ A] (px py x : A),
      px * py = py * px →
      px * x - x * px = algebraMap ℂ A (-Complex.I) →
      let πy := py + (qB : ℂ) • x
      pauliOperator px πy ^ 2 = pauliSquareTerm px πy qB) ∧
    (∀ ky : ℝ, pauliOperator magneticMomentumX (magneticMomentumY ky qB) ^ 2 =
      pauliSquareTerm magneticMomentumX (magneticMomentumY ky qB) qB) := by
  refine ⟨dirac_pauli_blocks, ?_, fun ky => pauli_square _ _ _ (magnetic_commutator ky qB)⟩
  intro A _ _ px py x hpy hx
  dsimp
  apply pauli_square
  rw [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, add_sub_add_comm, hpy,
    sub_self, zero_add, ← smul_sub, hx]
  rw [Algebra.smul_def, IsScalarTower.algebraMap_apply ℝ ℂ A, ← map_mul, mul_comm]
  rfl

/-- The energy label uses the opposite sign from the Pauli eigenvalue. -/
def magneticSpinProjection (i : Fin 2) : ℝ := if i = 0 then -(1 / 2) else 1 / 2

/-- The squared differential operator on one spin component in the transverse gauge. -/
def landauSquaredOperator (m pz qB ky : ℝ) (i : Fin 2) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  -deriv (deriv f) x + (ky + qB * x) ^ 2 * f x +
    (m ^ 2 + pz ^ 2 + (pauliZ i i).re * qB) * f x

theorem dirac_landau_squared_energy_modes (m pz qB ky : ℝ) (hq : 0 < qB)
    (n : ℕ) (i : Fin 2) :
    let f := Omega.Analysis.HermiteOscillator.mode qB ky n
    f ≠ 0 ∧ (pauliZ i i).re = -2 * magneticSpinProjection i ∧
      ∀ x : ℝ, landauSquaredOperator m pz qB ky i f x =
        landauEnergySq m pz qB 2 n (magneticSpinProjection i) * f x := by
  dsimp only
  obtain ⟨hnonzero, heigen⟩ := Omega.Analysis.HermiteOscillator.mode_oscillator qB ky hq n
  have hspin : (pauliZ i i).re = -2 * magneticSpinProjection i := by
    fin_cases i <;> norm_num [pauliZ, magneticSpinProjection]
  refine ⟨hnonzero, hspin, fun x => ?_⟩
  rw [landauSquaredOperator, hspin, heigen x]
  unfold landauEnergySq
  ring

/-- Invariants in the sign and orientation conventions of the Maxwell module. -/
def I1 (E B : V3) : ℝ := spatialNormSq B - spatialNormSq E

def I2 (E B : V3) : ℝ := spatialDot E B

def eulerHeisenbergQuartic (E B : V3) : ℝ := I1 E B ^ 2 + 7 * I2 E B ^ 2

def eulerHeisenbergCoefficient (α m : ℝ) : ℝ := 2 * α ^ 2 / (45 * m ^ 4)

def eulerHeisenbergLagrangian (α m : ℝ) (E B : V3) : ℝ :=
  -(1 / 2) * I1 E B + eulerHeisenbergCoefficient α m * eulerHeisenbergQuartic E B

theorem euler_heisenberg_lorentz_and_cp_invariance (α m : ℝ) (E B : V3) :
    (∀ Λ : M4, Λᵀ * eta4 * Λ = eta4 → Λ.det = 1 →
      let EB := fieldOfTensor (Λᵀ * fieldTensor E B * Λ)
      eulerHeisenbergLagrangian α m EB.1 EB.2 = eulerHeisenbergLagrangian α m E B) ∧
    eulerHeisenbergLagrangian α m (-E) B = eulerHeisenbergLagrangian α m E B ∧
    eulerHeisenbergLagrangian α m E (-B) = eulerHeisenbergLagrangian α m E B ∧
    (I1 E B = 0 → I2 E B = 0 → eulerHeisenbergLagrangian α m E B = 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro Λ hΛ hdet
    have h := maxwell_invariants_lorentz_invariant Λ E B hΛ hdet
    dsimp only at h ⊢
    simp only [eulerHeisenbergLagrangian, eulerHeisenbergQuartic, I1, I2, h.2.1, h.2.2.2]
  · simp only [eulerHeisenbergLagrangian, eulerHeisenbergQuartic, I1, I2,
      spatialNormSq, spatialDot, Pi.neg_apply]
    ring
  · simp only [eulerHeisenbergLagrangian, eulerHeisenbergQuartic, I1, I2,
      spatialNormSq, spatialDot, Pi.neg_apply]
    ring
  · intro h₁ h₂
    simp [eulerHeisenbergLagrangian, eulerHeisenbergQuartic, h₁, h₂]

def dualityRotate (E B : V3) (θ : ℝ) : V3 × V3 :=
  (Real.cos θ • E + Real.sin θ • B, -Real.sin θ • E + Real.cos θ • B)

private theorem rotate_invariants (E B : V3) (θ : ℝ) :
    let EB := dualityRotate E B θ
    I1 EB.1 EB.2 = Real.cos (2 * θ) * I1 E B - 2 * Real.sin (2 * θ) * I2 E B ∧
    I2 EB.1 EB.2 = Real.cos (2 * θ) * I2 E B + Real.sin (2 * θ) * I1 E B / 2 := by
  constructor <;>
    simp [dualityRotate, I1, I2, spatialNormSq, spatialDot, Pi.add_apply, Pi.smul_apply,
      Real.cos_two_mul', Real.sin_two_mul] <;> ring

private theorem rotate_quartic_difference (E B : V3) (θ : ℝ) :
    let EB := dualityRotate E B θ
    eulerHeisenbergQuartic EB.1 EB.2 - eulerHeisenbergQuartic E B =
      3 / 4 * (I1 E B ^ 2 - 4 * I2 E B ^ 2) * Real.sin (2 * θ) ^ 2 +
        3 * I1 E B * I2 E B * Real.sin (2 * θ) * Real.cos (2 * θ) := by
  dsimp only
  obtain ⟨h₁, h₂⟩ := rotate_invariants E B θ
  rw [eulerHeisenbergQuartic, eulerHeisenbergQuartic, h₁, h₂]
  linear_combination (I1 E B ^ 2 + 7 * I2 E B ^ 2) * Real.sin_sq_add_cos_sq (2 * θ)

theorem euler_heisenberg_breaks_em_duality (E B : V3) :
    (∀ θ : ℝ, let EB := dualityRotate E B θ
      maxwellStressCov EB.1 EB.2 = maxwellStressCov E B ∧
      I1 EB.1 EB.2 = Real.cos (2 * θ) * I1 E B - 2 * Real.sin (2 * θ) * I2 E B ∧
      I2 EB.1 EB.2 = Real.cos (2 * θ) * I2 E B + Real.sin (2 * θ) * I1 E B / 2 ∧
      eulerHeisenbergQuartic EB.1 EB.2 - eulerHeisenbergQuartic E B =
        3 / 4 * (I1 E B ^ 2 - 4 * I2 E B ^ 2) * Real.sin (2 * θ) ^ 2 +
          3 * I1 E B * I2 E B * Real.sin (2 * θ) * Real.cos (2 * θ)) ∧
    ((∃ θ : ℝ, let EB := dualityRotate E B θ
      eulerHeisenbergQuartic EB.1 EB.2 ≠ eulerHeisenbergQuartic E B) ↔
        I1 E B ≠ 0 ∨ I2 E B ≠ 0) ∧
    (let EB := dualityRotate 0 B (Real.pi / 4)
     eulerHeisenbergQuartic EB.1 EB.2 = (7 / 4) * eulerHeisenbergQuartic 0 B ∧
     -(1 / 2) * I1 EB.1 EB.2 = 0) := by
  have hquarter : 2 * (Real.pi / 4) = Real.pi / 2 := by ring
  have heighth : 2 * (Real.pi / 8) = Real.pi / 4 := by ring
  refine ⟨?_, ?_, ?_⟩
  · intro θ
    exact ⟨(maxwell_duality_rotation_invariant E B θ).2, (rotate_invariants E B θ).1,
      (rotate_invariants E B θ).2, rotate_quartic_difference E B θ⟩
  · constructor
    · rintro ⟨θ, hθ⟩
      by_contra! h
      apply hθ
      have hd := rotate_quartic_difference E B θ
      simp [h.1, h.2] at hd
      exact sub_eq_zero.mp hd
    · intro h
      by_contra! hall
      have h₁ := rotate_quartic_difference E B (Real.pi / 4)
      have h₂ := rotate_quartic_difference E B (Real.pi / 8)
      dsimp only at h₁ h₂
      rw [not_ne_iff.mp (hall (Real.pi / 4)), sub_self, hquarter, Real.sin_pi_div_two, Real.cos_pi_div_two] at h₁
      have hsq : I1 E B ^ 2 - 4 * I2 E B ^ 2 = 0 := by linarith
      simp only [not_ne_iff.mp (hall (Real.pi / 8)), sub_self, hsq, mul_zero, zero_mul, zero_add,
        heighth, Real.sin_pi_div_four, Real.cos_pi_div_four] at h₂
      have hp : I1 E B = 0 ∨ I2 E B = 0 := by
        have hs : Real.sqrt 2 / 2 ≠ 0 := by positivity
        have hprod := mul_eq_zero.mp h₂.symm
        rcases hprod with hprod | hprod
        · rcases mul_eq_zero.mp hprod with hprod | hprod
          · rcases mul_eq_zero.mp hprod with hprod | hprod
            · exact Or.inl ((mul_eq_zero.mp hprod).resolve_left (by norm_num))
            · exact Or.inr hprod
          · exact (hs hprod).elim
        · exact (hs hprod).elim
      rcases hp with hp | hp
      · have hb : I2 E B = 0 := by nlinarith
        exact h.elim (fun hn => hn hp) (fun hn => hn hb)
      · have he : I1 E B = 0 := by nlinarith
        exact h.elim (fun hn => hn he) (fun hn => hn hp)
  · obtain ⟨h₁, h₂⟩ := rotate_invariants 0 B (Real.pi / 4)
    have hzero : I2 0 B = 0 := by simp [I2, spatialDot]
    rw [hquarter, Real.sin_pi_div_two, Real.cos_pi_div_two, hzero] at h₁ h₂
    dsimp only
    unfold eulerHeisenbergQuartic
    rw [h₁, h₂, hzero]
    ring_nf
    simp

def parallelProbe (α m B e b a : ℝ) : ℝ :=
  eulerHeisenbergLagrangian α m ![0, 0, a * e] ![0, a * b, B]

def perpendicularProbe (α m B e b a : ℝ) : ℝ :=
  eulerHeisenbergLagrangian α m ![a * e, 0, 0] ![0, 0, B + a * b]

def parallelPhaseSpeedSq (u : ℝ) : ℝ := (1 - 4 * u) / (1 + 10 * u)

def perpendicularPhaseSpeedSq (u : ℝ) : ℝ := (1 - 12 * u) / (1 - 4 * u)

def parallelRefractiveIndex (u : ℝ) : ℝ := Real.sqrt ((1 + 10 * u) / (1 - 4 * u))

def perpendicularRefractiveIndex (u : ℝ) : ℝ := Real.sqrt ((1 - 4 * u) / (1 - 12 * u))

private theorem second_derivative_quartic (f : ℝ → ℝ) (c₀ c₁ c₂ c₃ c₄ : ℝ)
    (h : ∀ x, f x = c₀ + c₁ * x + c₂ * x ^ 2 + c₃ * x ^ 3 + c₄ * x ^ 4) :
    HasDerivAt (deriv f) (2 * c₂) 0 := by
  have hderiv (x : ℝ) :
      deriv f x = c₁ + c₂ * (2 * x) + c₃ * (3 * x ^ 2) + c₄ * (4 * x ^ 3) := by
    have hx := hasDerivAt_id x
    have hd := HasDerivAt.fun_add
      (HasDerivAt.fun_add
        (HasDerivAt.fun_add
          (HasDerivAt.fun_add (hasDerivAt_const x c₀) (HasDerivAt.const_mul c₁ hx))
          (HasDerivAt.const_mul c₂ (hx.pow 2)))
        (HasDerivAt.const_mul c₃ (hx.pow 3)))
      (HasDerivAt.const_mul c₄ (hx.pow 4))
    rw [show f = fun x => c₀ + c₁ * x + c₂ * x ^ 2 + c₃ * x ^ 3 + c₄ * x ^ 4 from
      funext h]
    simpa [id, Pi.pow_apply] using HasDerivAt.deriv hd
  rw [show deriv f = _ from funext hderiv]
  have hx := hasDerivAt_id (0 : ℝ)
  have hd := HasDerivAt.fun_add
    (HasDerivAt.fun_add
      (HasDerivAt.fun_add (hasDerivAt_const (0 : ℝ) c₁)
        (HasDerivAt.const_mul c₂ (HasDerivAt.const_mul 2 hx)))
      (HasDerivAt.const_mul c₃ (HasDerivAt.const_mul 3 (hx.pow 2))))
    (HasDerivAt.const_mul c₄ (HasDerivAt.const_mul 4 (hx.pow 3)))
  simpa [id, Pi.pow_apply, Pi.add_apply, mul_comm] using hd

private theorem probe_parallel (α m B e b : ℝ) :
    HasDerivAt (deriv (parallelProbe α m B e b))
      ((1 + 10 * (eulerHeisenbergCoefficient α m * B ^ 2)) * e ^ 2 -
       (1 - 4 * (eulerHeisenbergCoefficient α m * B ^ 2)) * b ^ 2) 0 := by
  let c := eulerHeisenbergCoefficient α m
  have h := second_derivative_quartic (parallelProbe α m B e b)
    (-(1 / 2) * B ^ 2 + c * B ^ 4) 0
    (((1 + 10 * (c * B ^ 2)) * e ^ 2 - (1 - 4 * (c * B ^ 2)) * b ^ 2) / 2)
    0 (c * (b ^ 2 - e ^ 2) ^ 2) (by
      intro x
      simp [parallelProbe, eulerHeisenbergLagrangian, eulerHeisenbergQuartic, I1, I2,
        spatialNormSq, spatialDot, c]
      ring)
  convert h using 1
  ring

private theorem probe_perpendicular (α m B e b : ℝ) :
    HasDerivAt (deriv (perpendicularProbe α m B e b))
      ((1 - 4 * (eulerHeisenbergCoefficient α m * B ^ 2)) * e ^ 2 -
       (1 - 12 * (eulerHeisenbergCoefficient α m * B ^ 2)) * b ^ 2) 0 := by
  let c := eulerHeisenbergCoefficient α m
  have h := second_derivative_quartic (perpendicularProbe α m B e b)
    (-(1 / 2) * B ^ 2 + c * B ^ 4) ((-B + 4 * c * B ^ 3) * b)
    (((1 - 4 * (c * B ^ 2)) * e ^ 2 - (1 - 12 * (c * B ^ 2)) * b ^ 2) / 2)
    (4 * c * B * b * (b ^ 2 - e ^ 2)) (c * (b ^ 2 - e ^ 2) ^ 2) (by
      intro x
      simp [perpendicularProbe, eulerHeisenbergLagrangian, eulerHeisenbergQuartic, I1, I2,
        spatialNormSq, spatialDot, c]
      ring)
  convert h using 1
  ring

private theorem refractive_derivative (a b : ℝ) :
    HasDerivAt (fun u : ℝ => Real.sqrt ((1 + a * u) / (1 + b * u))) ((a - b) / 2) 0 := by
  have hx := hasDerivAt_id (0 : ℝ)
  have ha := HasDerivAt.fun_add (hasDerivAt_const (0 : ℝ) (1 : ℝ)) (HasDerivAt.const_mul a hx)
  have hb := HasDerivAt.fun_add (hasDerivAt_const (0 : ℝ) (1 : ℝ)) (HasDerivAt.const_mul b hx)
  have hd := HasDerivAt.fun_div ha hb (by simp [id])
  simpa [id] using HasDerivAt.sqrt hd (by simp [id])

/-- The two Hessians yield reciprocal squared indices and the first-order index shifts.
The strict ordering of the exact squared speeds has a separate threshold. -/
theorem vacuum_birefringence_indices_and_subluminality
    (α m e B : ℝ) (hα : 0 < α) (hm : 0 < m) (hB : 0 < B) (he : α = e ^ 2 / (4 * Real.pi)) :
    let u := eulerHeisenbergCoefficient α m * B ^ 2
    (∀ x y,
      HasDerivAt (deriv (parallelProbe α m B x y))
        ((1 + 10 * u) * x ^ 2 - (1 - 4 * u) * y ^ 2) 0 ∧
      HasDerivAt (deriv (perpendicularProbe α m B x y))
        ((1 - 4 * u) * x ^ 2 - (1 - 12 * u) * y ^ 2) 0) ∧
    parallelPhaseSpeedSq u =
      -deriv (deriv (parallelProbe α m B 0 1)) 0 /
        deriv (deriv (parallelProbe α m B 1 0)) 0 ∧
    perpendicularPhaseSpeedSq u =
      -deriv (deriv (perpendicularProbe α m B 0 1)) 0 /
        deriv (deriv (perpendicularProbe α m B 1 0)) 0 ∧
    HasDerivAt parallelRefractiveIndex 7 0 ∧
    HasDerivAt perpendicularRefractiveIndex 4 0 ∧
    7 * u = (7 * α / (90 * Real.pi)) * (e * B / m ^ 2) ^ 2 ∧
    4 * u = (4 * α / (90 * Real.pi)) * (e * B / m ^ 2) ^ 2 ∧
    (7 * u) / (4 * u) = 7 / 4 ∧
    (u < 1 / 12 →
      0 < parallelPhaseSpeedSq u ∧ parallelPhaseSpeedSq u < 1 ∧
      0 < perpendicularPhaseSpeedSq u ∧ perpendicularPhaseSpeedSq u < 1 ∧
      (parallelPhaseSpeedSq u < perpendicularPhaseSpeedSq u ↔ u < 3 / 68)) := by
  let u := eulerHeisenbergCoefficient α m * B ^ 2
  change _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ 7 * u = _ ∧ 4 * u = _ ∧ _ ∧ _
  have hu : 0 < u := by unfold u eulerHeisenbergCoefficient; positivity
  have hpar : HasDerivAt parallelRefractiveIndex 7 0 := by
    have h := refractive_derivative 10 (-4)
    norm_num at h
    have heq : parallelRefractiveIndex = fun t => Real.sqrt ((1 + 10 * t) / (1 + -(4 * t))) := by
      funext t
      simp [parallelRefractiveIndex, sub_eq_add_neg]
    rwa [heq]
  have hperp : HasDerivAt perpendicularRefractiveIndex 4 0 := by
    have h := refractive_derivative (-4) (-12)
    norm_num at h
    have heq : perpendicularRefractiveIndex =
        fun t => Real.sqrt ((1 + -(4 * t)) / (1 + -(12 * t))) := by
      funext t
      simp [perpendicularRefractiveIndex, sub_eq_add_neg]
    rwa [heq]
  have hcharge : e ^ 2 = 4 * Real.pi * α := by
    have hn : (4 * Real.pi) ≠ 0 := by positivity
    rw [eq_div_iff hn] at he
    linarith only [he]
  have hcoupling : u = (α / (90 * Real.pi)) * (e * B / m ^ 2) ^ 2 := by
    simp only [u, eulerHeisenbergCoefficient, div_pow, mul_pow, hcharge]
    field_simp [hm.ne', Real.pi_ne_zero]
    <;> ring
  refine ⟨fun x y => ⟨probe_parallel α m B x y, probe_perpendicular α m B x y⟩, ?_, ?_,
    hpar, hperp, ?_, ?_, ?_, ?_⟩
  · rw [(probe_parallel α m B 0 1).deriv, (probe_parallel α m B 1 0).deriv]
    simp [parallelPhaseSpeedSq]
  · rw [(probe_perpendicular α m B 0 1).deriv, (probe_perpendicular α m B 1 0).deriv]
    simp [perpendicularPhaseSpeedSq]
  · rw [hcoupling]
    ring
  · rw [hcoupling]
    ring
  · have h4u : 4 * u ≠ 0 := by positivity
    exact (div_eq_iff h4u).2 (by ring)
  · intro hweak
    have h₁ : 0 < 1 + 10 * u := by linarith
    have h₂ : 0 < 1 - 4 * u := by linarith
    have h₃ : 0 < 1 - 12 * u := by linarith
    refine ⟨div_pos h₂ h₁, (div_lt_one h₁).2 (by linarith),
      div_pos h₃ h₂, (div_lt_one h₂).2 (by linarith), ?_⟩
    unfold parallelPhaseSpeedSq perpendicularPhaseSpeedSq
    rw [div_lt_div_iff₀ h₁ h₂]
    have hidentity : (1 - 12 * u) * (1 + 10 * u) - (1 - 4 * u) * (1 - 4 * u) =
        u * (6 - 136 * u) := by ring
    rw [← sub_pos, hidentity, mul_pos_iff_of_pos_left hu]
    constructor <;> intro h <;> linarith

section ProperTime

open Filter MeasureTheory Set
open scoped Topology

def magneticProperTimeMoment (m : ℝ) : ℝ :=
  ∫ s in Ioi (0 : ℝ), s * Real.exp (-(m ^ 2) * s)

def cothQuarticQuotient (x : ℝ) : ℝ :=
  (x * Real.cosh x - Real.sinh x - (x ^ 2 / 3) * Real.sinh x) /
    (x ^ 4 * Real.sinh x)

theorem euler_heisenberg_coth_quartic_limit :
    Tendsto cothQuarticQuotient (𝓝[≠] 0) (𝓝 (-(1 / 45))) := by
  unfold cothQuarticQuotient
  have hx : Tendsto (fun x : ℝ => x) (𝓝[≠] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  have hs := Omega.EulerHeisenbergProperTime.sinhTaylor5.mono_left (nhdsWithin_le_nhds (s := {0}ᶜ))
  have hc := Omega.EulerHeisenbergProperTime.coshTaylor4.mono_left (nhdsWithin_le_nhds (s := {0}ᶜ))
  have hfac := (hx.pow 2 |>.div_const 3).const_add 1
  have hr := ((hc.sub (hfac.mul hs)).sub (hx.pow 2 |>.div_const 360)).sub_const (1 / 45)
  have hd := hr.div Omega.EulerHeisenbergProperTime.sinhDiv one_ne_zero
  simp only [zero_pow (by decide : 2 ≠ 0), zero_div, add_zero, mul_zero,
    sub_zero, zero_sub, div_one] at hd
  refine hd.congr' ?_
  filter_upwards [self_mem_nhdsWithin (a := (0 : ℝ)) (s := {0}ᶜ)] with x hx
  change x ≠ 0 at hx
  have hsx := Real.sinh_ne_zero.mpr hx
  simp only [Pi.div_apply]
  field_simp [hx, hsx]
  ring

theorem euler_heisenberg_proper_time_quartic_coeff (e m B : ℝ) (hm : 0 < m) :
    magneticProperTimeMoment m = 1 / m ^ 4 ∧
    let α := e ^ 2 / (4 * Real.pi)
    let C := ((e * B) ^ 4 / (360 * Real.pi ^ 2)) * magneticProperTimeMoment m
    C = (2 * α ^ 2 / (45 * m ^ 4)) * B ^ 4 ∧
    eulerHeisenbergLagrangian α m (0 : V3) ![0, 0, B] = -(B ^ 2) / 2 + C := by
  have h := Omega.EulerHeisenbergProperTime.magneticQuarticCoefficient e m B hm
  change ((e * B) ^ 4 / (360 * Real.pi ^ 2)) * magneticProperTimeMoment m = _ at h
  refine ⟨Omega.EulerHeisenbergProperTime.properTimeMoment m hm, h, ?_⟩
  rw [h]
  simp [eulerHeisenbergLagrangian, eulerHeisenbergQuartic, eulerHeisenbergCoefficient, I1, I2,
    spatialNormSq, spatialDot]
  ring

def schwingerSummand (e m E : ℝ) (n : ℕ) : ℝ :=
  (1 / ((n : ℝ) + 1) ^ 2) * Real.exp (-(((n : ℝ) + 1) * Real.pi * m ^ 2 / (e * E)))

def schwingerRate (e m E : ℝ) : ℝ :=
  ((e * E) ^ 2 / (4 * Real.pi ^ 3)) * ∑' n : ℕ, schwingerSummand e m E n

private theorem schwingerSeries_eq (e m E : ℝ) :
    (∑' n : ℕ, schwingerSummand e m E n) =
      Omega.EulerHeisenbergProperTime.electricSeries (Real.pi * m ^ 2 / (e * E)) := by
  unfold Omega.EulerHeisenbergProperTime.electricSeries
  congr 1
  funext n
  simp only [schwingerSummand, Omega.EulerHeisenbergProperTime.electricTerm,
    mul_div_assoc, mul_assoc]

private theorem schwinger_summable (e m E : ℝ) (he : 0 < e) (hm : 0 < m) (hE : 0 < E) :
    Summable (schwingerSummand e m E) := by
  have h := Omega.EulerHeisenbergProperTime.electricTermSummable
    (Real.pi * m ^ 2 / (e * E)) (by positivity)
  convert h using 1
  funext n
  simp only [schwingerSummand, Omega.EulerHeisenbergProperTime.electricTerm,
    mul_div_assoc, mul_assoc]

private theorem schwinger_bounds (e m E : ℝ) (he : 0 < e) (hm : 0 < m) (hE : 0 < E) :
    ((e * E) ^ 2 / (4 * Real.pi ^ 3)) * Real.exp (-(Real.pi * m ^ 2 / (e * E))) ≤
      schwingerRate e m E ∧
    schwingerRate e m E ≤
      ((e * E) ^ 2 / (24 * Real.pi)) * Real.exp (-(Real.pi * m ^ 2 / (e * E))) := by
  have h := Omega.EulerHeisenbergProperTime.electricSeries_bounds (Real.pi * m ^ 2 / (e * E))
    (by positivity)
  have hc : 0 ≤ (e * E) ^ 2 / (4 * Real.pi ^ 3) := by positivity
  unfold schwingerRate
  rw [schwingerSeries_eq]
  refine ⟨mul_le_mul_of_nonneg_left h.1 hc, (mul_le_mul_of_nonneg_left h.2 hc).trans_eq ?_⟩
  field_simp [Real.pi_ne_zero]
  ring

theorem schwinger_pair_production_series_and_essential_singularity
    (e m : ℝ) (he : 0 < e) (hm : 0 < m) :
    (∀ E : ℝ, 0 < E →
      Summable (schwingerSummand e m E) ∧
      ((e * E) ^ 2 / (4 * Real.pi ^ 3)) * Real.exp (-(Real.pi * m ^ 2 / (e * E))) ≤
        schwingerRate e m E ∧
      schwingerRate e m E ≤
        ((e * E) ^ 2 / (24 * Real.pi)) * Real.exp (-(Real.pi * m ^ 2 / (e * E)))) ∧
    ∀ k : ℕ, Tendsto (fun E => schwingerRate e m E / E ^ k) (𝓝[>] 0) (𝓝 0) := by
  refine ⟨fun E hE => ⟨schwinger_summable e m E he hm hE, schwinger_bounds e m E he hm hE⟩, ?_⟩
  intro k
  have ha : 0 < Real.pi * m ^ 2 / e := by positivity
  have hf := Omega.EulerHeisenbergProperTime.exponentialFlat (Real.pi * m ^ 2 / e) ha k
  have hx : Tendsto (fun E : ℝ => E) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  have hpre := ((hx.const_mul e).pow 2).div_const (24 * Real.pi)
  have hupper : Tendsto (fun E : ℝ =>
      ((e * E) ^ 2 / (24 * Real.pi)) * Real.exp (-(Real.pi * m ^ 2 / (e * E))) / E ^ k)
      (𝓝[>] 0) (𝓝 0) := by
    have h := hpre.mul hf
    simpa only [mul_zero, mul_div_assoc, div_div] using h
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
  · filter_upwards [self_mem_nhdsWithin (a := (0 : ℝ)) (s := Ioi 0)] with E hE
    apply div_nonneg _ (pow_nonneg hE.le k)
    exact (by positivity : 0 ≤ ((e * E) ^ 2 / (4 * Real.pi ^ 3)) *
      Real.exp (-(Real.pi * m ^ 2 / (e * E)))).trans (schwinger_bounds e m E he hm hE).1
  · filter_upwards [self_mem_nhdsWithin (a := (0 : ℝ)) (s := Ioi 0)] with E hE
    exact div_le_div_of_nonneg_right (schwinger_bounds e m E he hm hE).2 (pow_nonneg hE.le k)

end ProperTime

end D5.S3.Quantum.Gauge.DiracLandauEulerHeisenberg4D
