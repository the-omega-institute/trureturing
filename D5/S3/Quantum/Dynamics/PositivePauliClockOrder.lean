/- GID: D5/S3/Quantum/Dynamics/PositivePauliClockOrder
   generality: I
   mirror-B: D5/B/S3/Quantum/Dynamics/PositivePauliClockOrder
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=terminal=atom:fe5b36d38c2fac1015344a14352d6ff7cd82263ac5c41117b9b858bdc3012968
   digest: Positive Pauli clock propagators and their implemented order comparison. -/

import D5.S3.Quantum.Matrix.SpectralPower
import D5.S3.Quantum.Dynamics.ProjectionProbabilityFlow
import D5.S3.Quantum.EnvironmentRecords
import D5.S3.Quantum.Foundation.FiniteStateChannel
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/- Source: QUANTUM-REALITY sections 85, 101, 103, 106, and theorem 107.2.
   Ordered library search found no complete existing theorem. Reuse includes
   qubit_weyl_star, hamiltonianPropagator, traceEnvironment, DensityState,
   CFC.sqrt_eq_iff, Matrix positivity, map_exp, and exp_diagonal.
   All declarations are conservatively bind-only. Admission is the preregistered
   atom-required bridge from the positive response to actual propagators and
   from implemented mixed controlled evolution to its trace overlap.
   The known Physlib Hadamard hit is unused: the exponential proof applies
   Mathlib map_exp to the two-coordinate algebra map, without conjugation. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix NormedSpace
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace D5.S3.Quantum.Dynamics.PositivePauliClockOrder
open D5.S3.Quantum.Matrix.SpectralPower (posDef_two)

open D5.S3.Quantum.FiniteDimensional
open D5.S3.Quantum.EnvironmentRecords
open D5.S3.Quantum.Dynamics.ProjectionProbabilityFlow
open D5.S3.Quantum.Foundation.FiniteStateChannel

local instance (priority := 2000) {n : Type*} [Fintype n] [DecidableEq n] :
    NormedRing (Matrix n n ℂ) := Matrix.instL2OpNormedRing
local instance (priority := 2000) {n : Type*} [Fintype n] [DecidableEq n] :
    NormedAlgebra ℂ (Matrix n n ℂ) := Matrix.instL2OpNormedAlgebra
local instance (priority := 2000) {n : Type*} [Fintype n] [DecidableEq n] :
    NormedAlgebra ℚ (Matrix n n ℂ) := NormedAlgebra.restrictScalars ℚ ℂ _

/-- The response polynomial of source (107.2), on the canonical qubit algebra. -/
def response (v : ℝ) : QubitMatrix :=
  ((3 / 2 - v ^ 2 / 4 : ℝ) : ℂ) • 1 +
    (((1 - v) / 2 : ℝ) : ℂ) • qubitX + (((1 + v) / 2 : ℝ) : ℂ) • qubitZ

/-- The positive functional-calculus root, not a spectral ansatz. -/
def speed (v : ℝ) : QubitMatrix := CFC.sqrt (response v)

def coefficientA : QubitMatrix := (3 / 2 : ℂ) • 1 + (1 / 2 : ℂ) • (qubitX + qubitZ)
def coefficientB : QubitMatrix := (1 / 4 : ℂ) • (qubitZ - qubitX)
def coefficientC : QubitMatrix := (1 / 4 : ℂ) • 1

private lemma response_entries (v : ℝ) : response v =
    !![((2 + v / 2 - v ^ 2 / 4 : ℝ) : ℂ), (((1 - v) / 2 : ℝ) : ℂ);
      (((1 - v) / 2 : ℝ) : ℂ), ((1 - v / 2 - v ^ 2 / 4 : ℝ) : ℂ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [response, qubitX, qubitZ, Complex.ofReal_add, Complex.ofReal_sub,
      Complex.ofReal_div, Complex.ofReal_pow] <;> ring

/-- Positivity holds throughout the source's open velocity interval. -/
theorem positive_clock_model (v : ℝ) (hv : |v| < Real.sqrt (3 / 2)) :
    (response v).PosDef := by
  have hv2 : v ^ 2 < 3 / 2 := by
    simpa only [sq_abs] using (Real.lt_sqrt (abs_nonneg v)).mp hv
  have hdet : 1 / 64 < (3 / 2 - v ^ 2 / 4) ^ 2 -
      ((1 - v) / 2) ^ 2 - ((1 + v) / 2) ^ 2 := by
    nlinarith [sq_nonneg (v ^ 2 - 3 / 2)]
  rw [response_entries]
  apply posDef_two
  · nlinarith [sq_nonneg (v + 1)]
  · nlinarith

theorem special_directions_mem : |(1 : ℝ)| < Real.sqrt (3 / 2) ∧
    |(-1 : ℝ)| < Real.sqrt (3 / 2) := by
  constructor <;> norm_num only [abs_one, abs_neg] <;>
    exact (Real.lt_sqrt (by norm_num)).mpr (by norm_num)

/-- Strict positivity of the response gives an invertible positive square root. -/
theorem positive_clock_speed (v : ℝ) (hv : |v| < Real.sqrt (3 / 2)) :
    (speed v).PosDef := by
  have h := positive_clock_model v hv
  apply (CFC.sqrt_nonneg (response v)).posSemidef.posDef_iff_isUnit.mpr
  exact (CFC.isUnit_sqrt_iff (response v) h.posSemidef.nonneg).mpr h.isUnit

private lemma special_candidates :
    (1 + (1 / 2 : ℂ) • qubitZ).PosDef ∧ (1 + (1 / 2 : ℂ) • qubitX).PosDef := by
  constructor
  · convert posDef_two (3/2) 0 (1/2) (by norm_num) (by norm_num) using 1
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [qubitZ]
  · convert posDef_two 1 (1/2) 1 (by norm_num) (by norm_num) using 1
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [qubitX]

/-- Both special roots are derived from positivity and their exact squares. -/
theorem positive_clock_special_roots :
    speed 1 = 1 + (1 / 2 : ℂ) • qubitZ ∧
    speed (-1) = 1 + (1 / 2 : ℂ) • qubitX ∧
    (1 + (1 / 2 : ℂ) • qubitZ).PosDef ∧ (1 + (1 / 2 : ℂ) • qubitX).PosDef ∧
    (1 + (1 / 2 : ℂ) • qubitZ) ^ 2 = response 1 ∧
    (1 + (1 / 2 : ℂ) • qubitX) ^ 2 = response (-1) := by
  have hz : (1 + (1 / 2 : ℂ) • qubitZ) ^ 2 = response 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [response, qubitX, qubitZ, pow_two, Matrix.mul_apply, Fin.sum_univ_two]
  have hx : (1 + (1 / 2 : ℂ) • qubitX) ^ 2 = response (-1) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [response, qubitX, qubitZ, pow_two, Matrix.mul_apply, Fin.sum_univ_two]
  refine ⟨?_, ?_, special_candidates.1, special_candidates.2, hz, hx⟩
  · exact (CFC.sqrt_eq_iff _ _
      (positive_clock_model 1 special_directions_mem.1).posSemidef.nonneg
      special_candidates.1.posSemidef.nonneg).mpr (by simpa [pow_two] using hz)
  · exact (CFC.sqrt_eq_iff _ _
      (positive_clock_model (-1) special_directions_mem.2).posSemidef.nonneg
      special_candidates.2.posSemidef.nonneg).mpr (by simpa [pow_two] using hx)

/-- Explicit witnesses for the standing coefficient assumptions of section 103. -/
theorem positive_clock_coefficients :
    coefficientA.IsHermitian ∧ coefficientB.IsHermitian ∧ coefficientC.IsHermitian ∧
    (1 / 2 : ℂ) • (1 : QubitMatrix) ≤ coefficientA ∧
    (∀ v : ℝ, response v = coefficientA + ((2 * v : ℝ) : ℂ) • coefficientB -
      ((v ^ 2 : ℝ) : ℂ) • coefficientC) ∧
    (∀ ξ : ℝ, ((ξ ^ 2 : ℝ) : ℂ) • coefficientC = ((ξ ^ 2 / 4 : ℝ) : ℂ) • 1) := by
  have hA : (coefficientA - (1 / 2 : ℂ) • 1).PosDef := by
    convert posDef_two (3/2) (1/2) (1/2) (by norm_num) (by norm_num) using 1
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [coefficientA, qubitX, qubitZ]
  refine ⟨?_, ?_, ?_, hA.posSemidef, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> norm_num [coefficientA, qubitX, qubitZ]
  · ext i j
    fin_cases i <;> fin_cases j <;> norm_num [coefficientB, qubitX, qubitZ]
  · ext i j
    fin_cases i <;> fin_cases j <;> norm_num [coefficientC]
  · intro v
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [response, coefficientA, coefficientB, coefficientC, qubitX, qubitZ,
        Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_mul,
        Complex.ofReal_div, Complex.ofReal_pow] <;> ring
  · intro ξ
    simp [coefficientC, smul_smul, Complex.ofReal_pow, div_eq_mul_inv]

def sigma : QubitMatrix := (1 / 2 : ℂ) • 1

lemma sigma_posDef : sigma.PosDef := by
  convert posDef_two (1/2) 0 (1/2) (by norm_num) (by norm_num) using 1
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [sigma]

/-- The source's maximally mixed structure state in the current density carrier. -/
def mixedState : DensityState (Fin 2) :=
  ⟨CStarMatrix.ofMatrix sigma,
    by
      have heq : CStarMatrix.ofMatrix sigma =
          (1 / 2 : ℝ) • (1 : CStarMatrix (Fin 2) (Fin 2) ℂ) := by
        ext i j
        fin_cases i <;> fin_cases j <;> norm_num [sigma, CStarMatrix.ofMatrix_apply]
      rw [heq]
      exact smul_nonneg (by norm_num) zero_le_one,
    by change Matrix.trace sigma = 1; norm_num [sigma, Matrix.trace]⟩

theorem mixed_state_full_support : CStarMatrix.ofMatrix.symm mixedState.1 = sigma ∧
    Function.Surjective (Matrix.mulVec sigma) :=
  ⟨rfl, Matrix.mulVec_surjective_iff_isUnit.mpr sigma_posDef.isUnit⟩

/-- The normalized source Hamiltonian, using the existing propagator owner. -/
def pulse (v ω t : ℝ) : QubitMatrix := hamiltonianPropagator ((ω : ℂ) • speed v) t

theorem pulse_eq_exp (v ω t : ℝ) :
    pulse v ω t = exp ((-Complex.I * ((ω * t : ℝ) : ℂ)) • speed v) := by
  unfold pulse hamiltonianPropagator hamiltonianGenerator
  congr 1
  ext i j
  simp [Matrix.smul_apply, Complex.real_smul, Complex.ofReal_mul]
  ring

/-- The actual structure evolution is unitary throughout the positive domain. -/
theorem clock_propagators (v ω t : ℝ) (hv : |v| < Real.sqrt (3 / 2)) :
    pulse v ω t ∈ unitary QubitMatrix := by
  rw [pulse_eq_exp]
  apply exp_mem_unitary_of_mem_skewAdjoint
  rw [skewAdjoint.mem_iff]
  have hs : star (speed v) = speed v := (positive_clock_speed v hv).isHermitian
  simp [star_smul, hs, star_neg, star_mul, neg_smul, mul_comm]

private def xCoordinates : (ℂ × ℂ) →ₐ[ℂ] QubitMatrix where
  toFun z := !![(z.1 + z.2) / 2, (z.1 - z.2) / 2;
    (z.1 - z.2) / 2, (z.1 + z.2) / 2]
  map_zero' := by ext i j; fin_cases i <;> fin_cases j <;> norm_num
  map_one' := by ext i j; fin_cases i <;> fin_cases j <;> norm_num
  map_add' z w := by ext i j; fin_cases i <;> fin_cases j <;> simp <;> ring
  map_mul' z w := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  commutes' z := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Algebra.algebraMap_eq_smul_one]

private lemma scalar_pulse_factors (θ : ℝ) :
    Complex.exp (-Complex.I * (θ : ℂ) * (3/2)) =
      Complex.exp (-Complex.I * θ) *
        ((Real.cos (θ/2) : ℂ) - Complex.I * Real.sin (θ/2)) ∧
    Complex.exp (-Complex.I * (θ : ℂ) / 2) =
      Complex.exp (-Complex.I * θ) *
        ((Real.cos (θ/2) : ℂ) + Complex.I * Real.sin (θ/2)) := by
  have hminus := Complex.cos_sub_sin_I ((θ/2 : ℝ) : ℂ)
  have hplus := Complex.cos_add_sin_I ((θ/2 : ℝ) : ℂ)
  simp only [← Complex.ofReal_cos, ← Complex.ofReal_sin] at hminus hplus
  constructor
  · rw [show -Complex.I * (θ : ℂ) * (3/2) =
      -Complex.I * θ + (-((θ/2 : ℝ) : ℂ) * Complex.I) by push_cast; ring,
      Complex.exp_add, ← hminus]
    ring
  · rw [show -Complex.I * (θ : ℂ) / 2 =
      -Complex.I * θ + (((θ/2 : ℝ) : ℂ) * Complex.I) by push_cast; ring,
      Complex.exp_add, ← hplus]
    ring

/-- The actual exponentials retain the common global phase. -/
theorem clock_pulse_special_directions (ω t : ℝ) :
    pulse 1 ω t = Complex.exp (-Complex.I * ((ω*t : ℝ) : ℂ)) •
      (((Real.cos (ω*t/2) : ℝ) : ℂ) • 1 -
        (Complex.I * Real.sin (ω*t/2)) • qubitZ) ∧
    pulse (-1) ω t = Complex.exp (-Complex.I * ((ω*t : ℝ) : ℂ)) •
      (((Real.cos (ω*t/2) : ℝ) : ℂ) • 1 -
        (Complex.I * Real.sin (ω*t/2)) • qubitX) := by
  let θ := ω*t
  obtain ⟨h3, h1⟩ := scalar_pulse_factors θ
  simp only [Complex.ofReal_mul, neg_mul, Complex.ofReal_cos, Complex.ofReal_div,
    Complex.ofReal_ofNat, Complex.ofReal_sin] at h3 h1
  constructor
  · rw [pulse_eq_exp, positive_clock_special_roots.1]
    have hdiag : (-Complex.I * (θ : ℂ)) • (1 + (1/2 : ℂ) • qubitZ) =
        Matrix.diagonal ![-Complex.I * θ * (3/2), -Complex.I * θ / 2] := by
      ext i j
      fin_cases i <;> fin_cases j <;> norm_num [qubitZ] <;> ring
    change exp ((-Complex.I * (θ : ℂ)) • _) = _
    rw [hdiag, Matrix.exp_diagonal]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Pi.exp_def, ← Complex.exp_eq_exp_ℂ, qubitZ, h3, h1] <;> simp [θ]
  · rw [pulse_eq_exp, positive_clock_special_roots.2.1]
    have himage : xCoordinates (-Complex.I * θ * (3/2), -Complex.I * θ / 2) =
        (-Complex.I * (θ : ℂ)) • (1 + (1/2 : ℂ) • qubitX) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [xCoordinates, qubitX] <;> ring
    change exp ((-Complex.I * (θ : ℂ)) • _) = _
    rw [← himage, ← map_exp xCoordinates xCoordinates.toLinearMap.continuous_of_finiteDimensional]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [xCoordinates, Prod.fst_exp, Prod.snd_exp, ← Complex.exp_eq_exp_ℂ,
        qubitX, h3, h1] <;> simp [θ] <;> ring

/-- Branch zero implements Q; branch one implements P, as in source 85. -/
def controlled (Q P : QubitMatrix) : JointQubitEnvironmentMatrix :=
  (Matrix.blockDiagonal ![Q, P]).submatrix Prod.swap Prod.swap

lemma controlled_unitary (Q P : QubitMatrix)
    (hQ : Q ∈ unitary QubitMatrix) (hP : P ∈ unitary QubitMatrix) :
    controlled Q P ∈ unitary JointQubitEnvironmentMatrix := by
  have h : ∀ i : Fin 2, (![Q, P] i) ∈ unitary QubitMatrix := by
    intro i
    fin_cases i <;> assumption
  rw [Unitary.mem_iff]
  constructor
  all_goals simp only [controlled, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_submatrix]
  all_goals
    rw [← Matrix.submatrix_mul _ _ Prod.swap Prod.swap Prod.swap
      (Function.Involutive.bijective Prod.swap_swap)]
    rw [Matrix.blockDiagonal_conjTranspose, ← Matrix.blockDiagonal_mul]
  · have heq : (fun i => (![Q, P] i).conjTranspose * ![Q, P] i) = 1 := by
      funext i
      exact Unitary.star_mul_self_of_mem (h i)
    rw [heq, Matrix.blockDiagonal_one]
    simpa using (Matrix.submatrix_one_equiv (α := ℂ) (Equiv.prodComm (Fin 2) (Fin 2)))
  · have heq : (fun i => ![Q, P] i * (![Q, P] i).conjTranspose) = 1 := by
      funext i
      exact Unitary.mul_star_self_of_mem (h i)
    rw [heq, Matrix.blockDiagonal_one]
    simpa using (Matrix.submatrix_one_equiv (α := ℂ) (Equiv.prodComm (Fin 2) (Fin 2)))

/-- Source (101.2), including the action of its excited-clock branch. -/
theorem controlled_clock_evolution (v ω t : ℝ) (hv : |v| < Real.sqrt (3 / 2)) :
    controlled 1 (pulse v ω t) ∈ unitary JointQubitEnvironmentMatrix ∧
    controlled 1 (pulse v ω t) =
      Matrix.kronecker (Matrix.single 0 0 (1 : ℂ)) (1 : QubitMatrix) +
        Matrix.kronecker (Matrix.single 1 1 (1 : ℂ)) (pulse v ω t) ∧
    (∀ a b : Fin 2, controlled 1 (pulse v ω t) (1,a) (1,b) = pulse v ω t a b) := by
  refine ⟨controlled_unitary _ _ (by simp) (clock_propagators v ω t hv), ?_, ?_⟩
  · ext ⟨i,a⟩ ⟨j,b⟩
    fin_cases i <;> fin_cases j <;>
      simp [controlled, Matrix.blockDiagonal_apply, Matrix.single]
  · intro a b
    rfl

/-- A single mixed controlled-block identity, used by both source experiments. -/
theorem controlled_partial_trace (Q P rho : QubitMatrix) (i j : Fin 2) :
    traceEnvironment (controlled Q P * Matrix.kronecker rho sigma *
      (controlled Q P).conjTranspose) i j =
    rho i j * Matrix.trace (sigma * ((![Q,P] j).conjTranspose * ![Q,P] i)) := by
  fin_cases i <;> fin_cases j <;>
    simp [traceEnvironment, controlled, sigma, Matrix.mul_apply,
      Matrix.blockDiagonal_apply, Matrix.trace,
      Matrix.conjTranspose_apply, Fintype.sum_prod_type, Fin.sum_univ_two] <;> ring

def channel (v ω t : ℝ) (rho : QubitMatrix) : QubitMatrix :=
  traceEnvironment (controlled 1 (pulse v ω t) * Matrix.kronecker rho sigma *
    (controlled 1 (pulse v ω t)).conjTranspose)

def coherence (v ω t : ℝ) : ℂ := Matrix.trace (sigma * pulse v ω t)

private lemma overlap_conj (Q P : QubitMatrix) :
    Matrix.trace (sigma * (P.conjTranspose * Q)) =
      star (Matrix.trace (sigma * (Q.conjTranspose * P))) := by
  simp [sigma, Matrix.trace, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two]
  ring

theorem clock_reduced_entries (v ω t : ℝ) (hv : |v| < Real.sqrt (3 / 2))
    (rho : QubitMatrix) :
    channel v ω t rho 0 0 = rho 0 0 ∧ channel v ω t rho 1 1 = rho 1 1 ∧
    channel v ω t rho 1 0 = coherence v ω t * rho 1 0 ∧
    channel v ω t rho 0 1 = star (coherence v ω t) * rho 0 1 := by
  have hu := Unitary.star_mul_self_of_mem (clock_propagators v ω t hv)
  have hc := overlap_conj (1 : QubitMatrix) (pulse v ω t)
  simp only [Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one] at hc
  simp only [channel, controlled_partial_trace]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.mul_one, ← Matrix.star_eq_conjTranspose, hu]
  simp only [Matrix.star_eq_conjTranspose, hc]
  simp [coherence, sigma, Matrix.trace, Fin.sum_univ_two, mul_comm]

theorem isolated_clock_coherence (ω t : ℝ) :
    coherence 1 ω t = Complex.exp (-Complex.I * ((ω*t : ℝ) : ℂ)) * Real.cos (ω*t/2) ∧
    coherence (-1) ω t = Complex.exp (-Complex.I * ((ω*t : ℝ) : ℂ)) * Real.cos (ω*t/2) := by
  simp only [coherence, (clock_pulse_special_directions ω t).1, (clock_pulse_special_directions ω t).2]
  constructor <;> simp [sigma, Matrix.trace, qubitZ, qubitX] <;> ring

/-- Equality is on the actual reduced maps, for every canonical density state. -/
theorem isolated_clock_channels_equal (ω t : ℝ) (rho : DensityState (Fin 2)) :
    channel 1 ω t (CStarMatrix.ofMatrix.symm rho.1) =
      channel (-1) ω t (CStarMatrix.ofMatrix.symm rho.1) := by
  have hp := clock_reduced_entries 1 ω t special_directions_mem.1 (CStarMatrix.ofMatrix.symm rho.1)
  have hm := clock_reduced_entries (-1) ω t special_directions_mem.2 (CStarMatrix.ofMatrix.symm rho.1)
  have hc := (isolated_clock_coherence ω t).1.trans (isolated_clock_coherence ω t).2.symm
  ext i j
  fin_cases i <;> fin_cases j <;> simp_all

theorem pi_clock_pulses (ω t : ℝ) (hπ : ω*t = Real.pi) :
    pulse 1 ω t = Complex.I • qubitZ ∧ pulse (-1) ω t = Complex.I • qubitX := by
  have hp := clock_pulse_special_directions ω t
  rw [hπ] at hp
  have he : Complex.exp (-Complex.I * (Real.pi : ℂ)) = -1 := by
    rw [neg_mul, Complex.exp_neg, mul_comm, Complex.exp_pi_mul_I]
    norm_num
  rw [he] at hp
  simpa [Real.cos_pi_div_two, Real.sin_pi_div_two, smul_smul] using hp

theorem pi_clock_orders_anticommute (ω t : ℝ) (hπ : ω*t = Real.pi) :
    pulse (-1) ω t * pulse 1 ω t = -(pulse 1 ω t * pulse (-1) ω t) := by
  rw [(pi_clock_pulses ω t hπ).1, (pi_clock_pulses ω t hπ).2]
  simpa [smul_mul, mul_smul, smul_smul, ← pow_two] using qubit_weyl_star.1.symm

def orderP (ω tPlus tMinus : ℝ) : QubitMatrix := pulse (-1) ω tMinus * pulse 1 ω tPlus
def orderQ (ω tPlus tMinus : ℝ) : QubitMatrix := pulse 1 ω tPlus * pulse (-1) ω tMinus
def orderHolonomy (ω tPlus tMinus : ℝ) : QubitMatrix :=
  (orderQ ω tPlus tMinus).conjTranspose * orderP ω tPlus tMinus

/-- Source 85's operator expectation; no interference polynomial occurs here. -/
def gammaOrder (ω tPlus tMinus : ℝ) : ℂ := Matrix.trace (sigma * orderHolonomy ω tPlus tMinus)
def rhoPlus : QubitMatrix := (1 / 2 : ℂ) • !![1,1;1,1]
def orderControl (ω tPlus tMinus : ℝ) : QubitMatrix :=
  traceEnvironment (controlled (orderQ ω tPlus tMinus) (orderP ω tPlus tMinus) *
    Matrix.kronecker rhoPlus sigma *
      (controlled (orderQ ω tPlus tMinus) (orderP ω tPlus tMinus)).conjTranspose)

private lemma order_unitaries (ω tPlus tMinus : ℝ) :
    orderQ ω tPlus tMinus ∈ unitary QubitMatrix ∧ orderP ω tPlus tMinus ∈ unitary QubitMatrix :=
  ⟨(unitary QubitMatrix).mul_mem (clock_propagators 1 ω tPlus special_directions_mem.1)
      (clock_propagators (-1) ω tMinus special_directions_mem.2),
    (unitary QubitMatrix).mul_mem (clock_propagators (-1) ω tMinus special_directions_mem.2)
      (clock_propagators 1 ω tPlus special_directions_mem.1)⟩

/-- The actual implemented branches realize the source's complex overlap. -/
theorem order_control_marginal (ω tPlus tMinus : ℝ) :
    orderControl ω tPlus tMinus =
      (1 / 2 : ℂ) • !![1, star (gammaOrder ω tPlus tMinus); gammaOrder ω tPlus tMinus, 1] := by
  have hQ := Unitary.star_mul_self_of_mem (order_unitaries ω tPlus tMinus).1
  have hP := Unitary.star_mul_self_of_mem (order_unitaries ω tPlus tMinus).2
  simp only [Matrix.star_eq_conjTranspose] at hQ hP
  have hc := overlap_conj (orderQ ω tPlus tMinus) (orderP ω tPlus tMinus)
  ext i j
  simp only [orderControl, controlled_partial_trace]
  fin_cases i <;> fin_cases j
  · change ((1/2 : ℂ)*1) * Matrix.trace (sigma * ((orderQ ω tPlus tMinus).conjTranspose *
      orderQ ω tPlus tMinus)) = (1/2)*1
    rw [hQ]
    norm_num [sigma, Matrix.trace]
  · change ((1/2 : ℂ)*1) * Matrix.trace (sigma * ((orderP ω tPlus tMinus).conjTranspose *
      orderQ ω tPlus tMinus)) = (1/2)*star (gammaOrder ω tPlus tMinus)
    rw [hc]
    simp [gammaOrder, orderHolonomy]
  · change ((1/2 : ℂ)*1) * gammaOrder ω tPlus tMinus = (1/2)*gammaOrder ω tPlus tMinus
    rw [mul_one]
  · change ((1/2 : ℂ)*1) * Matrix.trace (sigma * ((orderP ω tPlus tMinus).conjTranspose *
      orderP ω tPlus tMinus)) = (1/2)*1
    rw [hP]
    norm_num [sigma, Matrix.trace]

private lemma phase_unit (θ : ℝ) :
    star (Complex.exp (-Complex.I * (θ : ℂ))) * Complex.exp (-Complex.I * θ) = 1 := by
  change (starRingEnd ℂ) _ * _ = _
  rw [← Complex.exp_conj, ← Complex.exp_add]
  simp

private lemma phase_pair_unit (θ φ : ℝ) :
    star (Complex.exp (-Complex.I * (θ : ℂ)) * Complex.exp (-Complex.I * (φ : ℂ))) *
      (Complex.exp (-Complex.I * (φ : ℂ)) * Complex.exp (-Complex.I * (θ : ℂ))) = 1 := by
  rw [star_mul]
  calc
    _ = (star (Complex.exp (-Complex.I * (θ : ℂ))) * Complex.exp (-Complex.I * θ)) *
        (star (Complex.exp (-Complex.I * (φ : ℂ))) * Complex.exp (-Complex.I * φ)) := by ring
    _ = 1 := by rw [phase_unit, phase_unit, one_mul]

set_option maxRecDepth 2000 in
/-- General pulse durations, calculated from the actual relative operator. -/
theorem order_interference_formula (ω tPlus tMinus : ℝ) :
    gammaOrder ω tPlus tMinus =
      ((1 - 2 * Real.sin (ω*tPlus/2)^2 * Real.sin (ω*tMinus/2)^2 : ℝ) : ℂ) := by
  unfold gammaOrder orderHolonomy orderP orderQ
  rw [(clock_pulse_special_directions ω tPlus).1, (clock_pulse_special_directions ω tMinus).2]
  simp only [smul_mul_smul_comm, Matrix.conjTranspose_smul, phase_pair_unit, one_smul]
  simp [sigma, Matrix.trace, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Fin.sum_univ_two, qubitX, qubitZ]
  ring_nf
  norm_num [← Complex.cos_conj, ← Complex.sin_conj, Complex.I_sq, Complex.conj_ofNat]
  ring_nf
  simp only [Complex.cos_sq']
  ring

theorem pi_order_relative_phase (ω t : ℝ) (hπ : ω*t = Real.pi) :
    orderHolonomy ω t t = -1 ∧ gammaOrder ω t t = -1 ∧
    orderControl ω t t = (1 / 2 : ℂ) • !![1,-1;-1,1] := by
  have hH : orderHolonomy ω t t = -1 := by
    unfold orderHolonomy orderP
    rw [pi_clock_orders_anticommute ω t hπ]
    change (orderQ ω t t).conjTranspose * (-orderQ ω t t) = -1
    rw [Matrix.mul_neg, ← Matrix.star_eq_conjTranspose,
      Unitary.star_mul_self_of_mem (order_unitaries ω t t).1]
  have hg : gammaOrder ω t t = -1 := by simp [gammaOrder, hH, sigma, Matrix.trace]
  refine ⟨hH, hg, ?_⟩
  rw [order_control_marginal, hg]
  norm_num

def scalarPhase (ω t rate : ℝ) : ℂ := Complex.exp (-Complex.I * ((ω*t*rate : ℝ) : ℂ))

/-- Both phases read one fixed label in each run. -/
theorem fixed_scalar_clock_order {Λ : Type*} (nPlus nMinus : Λ → ℝ)
    (ω tPlus tMinus : ℝ) (label : Λ) :
    scalarPhase ω tMinus (nMinus label) * scalarPhase ω tPlus (nPlus label) =
      scalarPhase ω tPlus (nPlus label) * scalarPhase ω tMinus (nMinus label) ∧
    star (scalarPhase ω tPlus (nPlus label) * scalarPhase ω tMinus (nMinus label)) *
      (scalarPhase ω tMinus (nMinus label) * scalarPhase ω tPlus (nPlus label)) = 1 ∧
    star (scalarPhase ω tPlus (nPlus label) * scalarPhase ω tMinus (nMinus label)) *
      (scalarPhase ω tMinus (nMinus label) * scalarPhase ω tPlus (nPlus label)) ≠ -1 := by
  have h := phase_pair_unit (ω*tPlus*nPlus label) (ω*tMinus*nMinus label)
  exact ⟨mul_comm _ _, h, by simpa only [scalarPhase, h] using (by norm_num : (1 : ℂ) ≠ -1)⟩

open MeasureTheory in
/-- Normalized averaging of relative coherence preserves one, even for arbitrary rates. -/
theorem averaged_fixed_scalar_clock_order {Λ : Type*} [MeasurableSpace Λ]
    (μ : Measure Λ) [IsProbabilityMeasure μ] (nPlus nMinus : Λ → ℝ) (ω tPlus tMinus : ℝ) :
    (∫ label, star (scalarPhase ω tPlus (nPlus label) * scalarPhase ω tMinus (nMinus label)) *
      (scalarPhase ω tMinus (nMinus label) * scalarPhase ω tPlus (nPlus label)) ∂μ) = 1 ∧
    (∫ label, star (scalarPhase ω tPlus (nPlus label) * scalarPhase ω tMinus (nMinus label)) *
      (scalarPhase ω tMinus (nMinus label) * scalarPhase ω tPlus (nPlus label)) ∂μ) ≠ -1 ∧
    (∫ label, scalarPhase ω tMinus (nMinus label) * scalarPhase ω tPlus (nPlus label) ∂μ) =
      ∫ label, scalarPhase ω tPlus (nPlus label) * scalarPhase ω tMinus (nMinus label) ∂μ := by
  have h : ∀ label, star (scalarPhase ω tPlus (nPlus label) * scalarPhase ω tMinus (nMinus label)) *
      (scalarPhase ω tMinus (nMinus label) * scalarPhase ω tPlus (nPlus label)) = 1 :=
    fun label => (fixed_scalar_clock_order nPlus nMinus ω tPlus tMinus label).2.1
  simp only [h]
  norm_num [mul_comm]

/-- The source's positive-frequency experiment has equal isolated channels but
an implemented relative minus sign at a pi pulse. The classical comparison is
restricted to one fixed label and commuting scalar phases within each run. -/
theorem positive_pauli_clock_order_separation (ω : ℝ) (hω : 0 < ω) :
    (∀ v : ℝ, |v| < Real.sqrt (3 / 2) →
      (response v).PosDef ∧ (speed v).PosDef ∧ speed v ^ 2 = response v) ∧
    (coefficientA.IsHermitian ∧ coefficientB.IsHermitian ∧ coefficientC.IsHermitian ∧
      (1 / 2 : ℂ) • (1 : QubitMatrix) ≤ coefficientA ∧
      (∀ v : ℝ, response v = coefficientA + ((2*v : ℝ) : ℂ) • coefficientB -
        ((v^2 : ℝ) : ℂ) • coefficientC) ∧
      ∀ ξ : ℝ, ((ξ^2 : ℝ) : ℂ) • coefficientC = ((ξ^2/4 : ℝ) : ℂ) • 1) ∧
    (speed 1 = 1 + (1 / 2 : ℂ) • qubitZ ∧ speed (-1) = 1 + (1 / 2 : ℂ) • qubitX) ∧
    (CStarMatrix.ofMatrix.symm mixedState.1 = sigma ∧ Function.Surjective (Matrix.mulVec sigma)) ∧
    (∀ v t : ℝ, |v| < Real.sqrt (3 / 2) →
      controlled 1 (pulse v ω t) ∈ unitary JointQubitEnvironmentMatrix) ∧
    (∀ t : ℝ,
      coherence 1 ω t = Complex.exp (-Complex.I * ((ω*t : ℝ) : ℂ)) * Real.cos (ω*t/2) ∧
      coherence (-1) ω t = Complex.exp (-Complex.I * ((ω*t : ℝ) : ℂ)) * Real.cos (ω*t/2) ∧
      ∀ rho : DensityState (Fin 2), channel 1 ω t (CStarMatrix.ofMatrix.symm rho.1) =
        channel (-1) ω t (CStarMatrix.ofMatrix.symm rho.1)) ∧
    (∀ tPlus tMinus : ℝ,
      gammaOrder ω tPlus tMinus =
        ((1-2*Real.sin (ω*tPlus/2)^2*Real.sin (ω*tMinus/2)^2 : ℝ) : ℂ) ∧
      orderControl ω tPlus tMinus = (1/2 : ℂ) •
        !![1, star (gammaOrder ω tPlus tMinus); gammaOrder ω tPlus tMinus, 1]) ∧
    (∀ t : ℝ, ω*t = Real.pi →
      pulse 1 ω t = Complex.I • qubitZ ∧ pulse (-1) ω t = Complex.I • qubitX ∧
      pulse (-1) ω t * pulse 1 ω t = -(pulse 1 ω t * pulse (-1) ω t) ∧
      orderHolonomy ω t t = -1 ∧ gammaOrder ω t t = -1 ∧
      orderControl ω t t = (1/2 : ℂ) • !![1,-1;-1,1]) ∧
    (ω * (Real.pi/ω) = Real.pi) ∧
    (∀ {Λ : Type*} [MeasurableSpace Λ] (μ : MeasureTheory.Measure Λ)
      [MeasureTheory.IsProbabilityMeasure μ] (nPlus nMinus : Λ → ℝ) (tPlus tMinus : ℝ),
      (∫ label, star (scalarPhase ω tPlus (nPlus label) * scalarPhase ω tMinus (nMinus label)) *
        (scalarPhase ω tMinus (nMinus label) * scalarPhase ω tPlus (nPlus label)) ∂μ) = 1 ∧
      (∫ label, star (scalarPhase ω tPlus (nPlus label) * scalarPhase ω tMinus (nMinus label)) *
        (scalarPhase ω tMinus (nMinus label) * scalarPhase ω tPlus (nPlus label)) ∂μ) ≠ -1 ∧
      (∫ label, scalarPhase ω tMinus (nMinus label) * scalarPhase ω tPlus (nPlus label) ∂μ) =
        ∫ label, scalarPhase ω tPlus (nPlus label) * scalarPhase ω tMinus (nMinus label) ∂μ) := by
  refine ⟨?_, positive_clock_coefficients,
    ⟨positive_clock_special_roots.1, positive_clock_special_roots.2.1⟩,
    mixed_state_full_support, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v hv
    refine ⟨positive_clock_model v hv, positive_clock_speed v hv, ?_⟩
    exact CFC.sq_sqrt (response v) (positive_clock_model v hv).posSemidef.nonneg
  · exact fun v t hv => (controlled_clock_evolution v ω t hv).1
  · intro t
    exact ⟨(isolated_clock_coherence ω t).1, (isolated_clock_coherence ω t).2,
      isolated_clock_channels_equal ω t⟩
  · exact fun tPlus tMinus => ⟨order_interference_formula ω tPlus tMinus,
      order_control_marginal ω tPlus tMinus⟩
  · intro t ht
    exact ⟨(pi_clock_pulses ω t ht).1, (pi_clock_pulses ω t ht).2,
      pi_clock_orders_anticommute ω t ht, pi_order_relative_phase ω t ht⟩
  · exact mul_div_cancel₀ Real.pi (ne_of_gt hω)
  · intro Λ _ μ _ nPlus nMinus tPlus tMinus
    exact averaged_fixed_scalar_clock_order μ nPlus nMinus ω tPlus tMinus

example : orderControl 1 Real.pi Real.pi = (1/2 : ℂ) • !![1,-1;-1,1] :=
  (pi_order_relative_phase 1 Real.pi (by ring)).2.2

#print axioms positive_pauli_clock_order_separation
#print axioms controlled_partial_trace
#print axioms positive_clock_special_roots
#print axioms clock_pulse_special_directions

end D5.S3.Quantum.Dynamics.PositivePauliClockOrder
