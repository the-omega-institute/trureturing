/- GID: D5/S3/Quantum/Dynamics/ProjectionProbabilityFlow
   generality: G
   mirror-B: D5/B/S3/Quantum/Dynamics/ProjectionProbabilityFlow
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Hamiltonian evolution differentiates projection probabilities by the commutator trace. -/

/- Library-search audit trail (2026-08-22):
   * The current tree's exact source-semantic primitives `DensityState`, `unitaryEvolution`,
     and `bornProbability` are imported and reused below.
   * Pinned Mathlib exact hits `hasDerivAt_exp_smul_const`, `HasDerivAt.star`,
     `HasDerivAt.mul`, `Matrix.trace_mul_comm`, and `is_const_of_deriv_eq_zero`
     are applied directly.
   * Searches for a packaged finite-dimensional projection-probability flow theorem returned
     no hit. -/

import D5.S3.Quantum.Decoherence.ProjectedUnistochasticDynamics
import D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition
import D5.S3.Quantum.FiniteDimensional
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.CStarAlgebra.Projection
import Mathlib.Analysis.SpecialFunctions.Exponential

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix NormedSpace
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace D5.S3.Quantum.Dynamics.ProjectionProbabilityFlow

open D5.S3.Quantum.Decoherence.ProjectedUnistochasticDynamics
open D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition
open D5.S3.Quantum.FiniteDimensional

variable {n : Type*} [Fintype n] [DecidableEq n]

local instance (priority := 2000) : NormedAddCommGroup (Matrix n n ℂ) :=
  Matrix.instL2OpNormedAddCommGroup

local instance (priority := 2000) : NormedSpace ℂ (Matrix n n ℂ) :=
  Matrix.instL2OpNormedSpace

local instance (priority := 2000) : NormedRing (Matrix n n ℂ) :=
  Matrix.instL2OpNormedRing

local instance (priority := 2000) : NormedAlgebra ℂ (Matrix n n ℂ) :=
  Matrix.instL2OpNormedAlgebra

/-- The canonical density-state carrier viewed on the source's ordinary matrix algebra. -/
def densityMatrix (rho : DensityState n) : Matrix n n ℂ :=
  CStarMatrix.ofMatrix.symm rho.1

/-- The source Hamiltonian generator `-i H`. -/
def hamiltonianGenerator (H : Matrix n n ℂ) : Matrix n n ℂ :=
  (-Complex.I) • H

/-- The source propagator `U_t = exp (-i t H)`. -/
def hamiltonianPropagator (H : Matrix n n ℂ) (t : ℝ) : Matrix n n ℂ :=
  exp (t • hamiltonianGenerator H)

/-- The source evolved density `rho_t = U_t rho U_t^*`. -/
def evolvedDensity (H : Matrix n n ℂ) (rho : DensityState n) (t : ℝ) :
    Matrix n n ℂ :=
  unitaryEvolution (hamiltonianPropagator H t) (densityMatrix rho)

/-- The real projection probability obtained from the source Born trace weight. -/
def projectionProbability (H : Matrix n n ℂ) (rho : DensityState n)
    (P : Matrix n n ℂ) (t : ℝ) : ℝ :=
  (bornProbability (evolvedDensity H rho t) P).re

omit [Fintype n] [DecidableEq n] in
private lemma star_hamiltonianGenerator (H : Matrix n n ℂ) (hH : H.IsHermitian) :
    star (hamiltonianGenerator H) = -hamiltonianGenerator H := by
  simp [hamiltonianGenerator, Matrix.star_eq_conjTranspose, hH.eq]

private lemma densityMatrix_hermitian (rho : DensityState n) :
    (densityMatrix rho).IsHermitian := by
  rw [Matrix.IsHermitian]
  ext i j
  exact CStarMatrix.star_apply_of_isSelfAdjoint rho.2.1.isSelfAdjoint

private lemma evolvedDensity_hermitian (H : Matrix n n ℂ) (rho : DensityState n) (t : ℝ) :
    (evolvedDensity H rho t).IsHermitian := by
  simpa [evolvedDensity, unitaryEvolution, Matrix.star_eq_conjTranspose] using
    Matrix.isHermitian_mul_mul_conjTranspose (hamiltonianPropagator H t)
      (densityMatrix_hermitian rho)

omit [DecidableEq n] in
private lemma trace_hermitian_product_real (A B : Matrix n n ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (Matrix.trace (A * B)).im = 0 := by
  have hStar : star (Matrix.trace (A * B)) = Matrix.trace (A * B) := by
    calc
      star (Matrix.trace (A * B)) = Matrix.trace ((A * B)ᴴ) :=
        (Matrix.trace_conjTranspose (A * B)).symm
      _ = Matrix.trace (B * A) := by rw [Matrix.conjTranspose_mul, hA.eq, hB.eq]
      _ = Matrix.trace (A * B) := Matrix.trace_mul_comm B A
  have hIm := congrArg Complex.im hStar
  simp only [Complex.star_def, Complex.conj_im] at hIm
  linarith

private lemma projectionProbability_eq_bornProbability (H P : Matrix n n ℂ)
    (rho : DensityState n) (hP : IsStarProjection P) (t : ℝ) :
    (projectionProbability H rho P t : ℂ) = bornProbability (evolvedDensity H rho t) P := by
  have hPHermitian : P.IsHermitian := by
    rw [Matrix.IsHermitian]
    exact hP.isSelfAdjoint.star_eq
  have hIm := trace_hermitian_product_real (evolvedDensity H rho t) P
    (evolvedDensity_hermitian H rho t) hPHermitian
  apply Complex.ext <;> simp [projectionProbability, bornProbability, hIm]

private lemma hamiltonian_commutes_propagator (H : Matrix n n ℂ) (t : ℝ) :
    Commute H (hamiltonianPropagator H t) := by
  apply Commute.exp_right
  exact ((Commute.refl H).smul_right (-Complex.I)).smul_right t

private lemma hasDerivAt_hamiltonianPropagator (H : Matrix n n ℂ) (t : ℝ) :
    HasDerivAt (hamiltonianPropagator H)
      (hamiltonianPropagator H t * hamiltonianGenerator H) t := by
  exact hasDerivAt_exp_smul_const (hamiltonianGenerator H) t

omit [DecidableEq n] in
private lemma trace_flow_identity (H S P : Matrix n n ℂ) :
    Matrix.trace (((-Complex.I) • (H * S - S * H)) * P) =
      Complex.I * Matrix.trace (S * (H * P - P * H)) := by
  have hCycle : Matrix.trace (H * S * P) = Matrix.trace (S * P * H) := by
    simpa only [Matrix.mul_assoc] using Matrix.trace_mul_comm H (S * P)
  simp only [smul_mul_assoc, Matrix.trace_smul, sub_mul, Matrix.trace_sub,
    Matrix.mul_sub]
  rw [hCycle]
  simp only [Matrix.mul_assoc]
  ring

private lemma flow_value_eq_ofReal (H P : Matrix n n ℂ) (rho : DensityState n)
    (hH : H.IsHermitian) (hP : IsStarProjection P) (t : ℝ) :
    ((Complex.I * Matrix.trace
      (evolvedDensity H rho t * (H * P - P * H))).re : ℂ) =
      Complex.I * Matrix.trace (evolvedDensity H rho t * (H * P - P * H)) := by
  have hPHermitian : P.IsHermitian := by
    rw [Matrix.IsHermitian]
    exact hP.isSelfAdjoint.star_eq
  let C := H * P - P * H
  have hCStar : Cᴴ = -C := by
    dsimp [C]
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      hH.eq, hPHermitian.eq]
    module
  let z := Matrix.trace (evolvedDensity H rho t * C)
  have hzStar : star z = -z := by
    dsimp [z]
    calc
      star (Matrix.trace (evolvedDensity H rho t * C)) =
          Matrix.trace ((evolvedDensity H rho t * C)ᴴ) :=
        (Matrix.trace_conjTranspose (evolvedDensity H rho t * C)).symm
      _ = Matrix.trace ((-C) * evolvedDensity H rho t) := by
        rw [Matrix.conjTranspose_mul, hCStar, (evolvedDensity_hermitian H rho t).eq]
      _ = -Matrix.trace (C * evolvedDensity H rho t) := by simp
      _ = -Matrix.trace (evolvedDensity H rho t * C) := by
        rw [Matrix.trace_mul_comm C]
  have hzRe := congrArg Complex.re hzStar
  simp only [Complex.star_def, Complex.conj_re, Complex.neg_re] at hzRe
  have hzReZero : z.re = 0 := by linarith
  have hFlowIm : (Complex.I * z).im = 0 := by
    rw [Complex.mul_im]
    norm_num [hzReZero]
  change (((Complex.I * z).re : ℝ) : ℂ) = Complex.I * z
  apply Complex.ext <;> simp [hFlowIm]

private lemma hasDerivAt_projectionProbability (H P : Matrix n n ℂ)
    (rho : DensityState n) (hH : H.IsHermitian) (t : ℝ) :
    HasDerivAt (projectionProbability H rho P)
      (Complex.re (Complex.I *
        Matrix.trace (evolvedDensity H rho t * (H * P - P * H)))) t := by
  let U := hamiltonianPropagator H t
  have hU := hasDerivAt_hamiltonianPropagator H t
  have hRaw := (hU.mul_const (densityMatrix rho)).mul hU.star
  have hHU : H * U = U * H := (hamiltonian_commutes_propagator H t).eq
  have hStarH : star H = H := by
    simpa [Matrix.star_eq_conjTranspose] using hH.eq
  have hUstarH : star U * H = H * star U := by
    have h := congrArg star hHU
    simpa [star_mul, hStarH] using h
  have hDerivative :
      U * hamiltonianGenerator H * densityMatrix rho * star U +
          U * densityMatrix rho * star (U * hamiltonianGenerator H) =
        (-Complex.I) •
          (H * (U * densityMatrix rho * star U) -
            (U * densityMatrix rho * star U) * H) := by
    symm
    rw [star_mul, star_hamiltonianGenerator H hH]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc H U]
    rw [hHU]
    rw [hUstarH]
    simp only [hamiltonianGenerator, smul_sub, neg_smul, neg_mul, mul_neg,
      neg_neg, smul_mul_assoc, mul_smul_comm]
    simp only [Matrix.mul_assoc]
    module
  have hState := (hRaw.congr_deriv hDerivative).mul_const P
  let traceComplex : Matrix n n ℂ →L[ℝ] ℂ :=
    (Matrix.traceLinearMap n ℝ ℂ).toContinuousLinearMap
  have hTrace := traceComplex.hasFDerivAt.comp_hasDerivAt t hState
  have hReal := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hTrace
  change HasDerivAt (projectionProbability H rho P)
    (Complex.re (Matrix.trace (((-Complex.I) •
      (H * evolvedDensity H rho t - evolvedDensity H rho t * H)) * P))) t at hReal
  apply hReal.congr_deriv
  exact congrArg Complex.re (trace_flow_identity H (evolvedDensity H rho t) P)

/-- In finite dimension, Hamiltonian conjugation differentiates every projection probability by
the commutator trace. If the projection commutes with the Hamiltonian, that probability is
constant for all real times. -/
theorem projection_probability_flow (H P : Matrix n n ℂ) (rho : DensityState n)
    (hH : H.IsHermitian) (hP : IsStarProjection P) :
    (∀ t : ℝ, (projectionProbability H rho P t : ℂ) =
      bornProbability (evolvedDensity H rho t) P) ∧
      (∀ t : ℝ,
        HasDerivAt (projectionProbability H rho P)
          (Complex.re (Complex.I * Matrix.trace
            (evolvedDensity H rho t * (H * P - P * H)))) t ∧
        ((Complex.I * Matrix.trace
          (evolvedDensity H rho t * (H * P - P * H))).re : ℂ) =
            Complex.I * Matrix.trace
              (evolvedDensity H rho t * (H * P - P * H))) ∧
      (H * P - P * H = 0 →
        ∀ t : ℝ, projectionProbability H rho P t = projectionProbability H rho P 0) := by
  have hFlowReal := hasDerivAt_projectionProbability H P rho hH
  refine ⟨projectionProbability_eq_bornProbability H P rho hP,
    fun t => ⟨hFlowReal t, flow_value_eq_ofReal H P rho hH hP t⟩, ?_⟩
  intro hComm
  have hZero (t : ℝ) : HasDerivAt (projectionProbability H rho P) 0 t := by
    simpa [hComm] using hFlowReal t
  have hDifferentiable : Differentiable ℝ (projectionProbability H rho P) :=
    fun t => (hZero t).differentiableAt
  intro t
  exact is_const_of_deriv_eq_zero hDifferentiable (fun s => (hZero s).deriv) t 0

/- A one-dimensional stationary state supplies a concrete inhabited source domain. -/
example :
    let rho : DensityState (Fin 1) :=
      ⟨CStarMatrix.ofMatrix (1 : Matrix (Fin 1) (Fin 1) ℂ),
        by
          change (0 : CStarMatrix (Fin 1) (Fin 1) ℂ) ≤ 1
          simpa only [star_one, one_mul] using
            star_mul_self_nonneg (1 : CStarMatrix (Fin 1) (Fin 1) ℂ),
        by
          change Matrix.trace (1 : Matrix (Fin 1) (Fin 1) ℂ) = 1
          simp⟩
    let H : Matrix (Fin 1) (Fin 1) ℂ := 0
    let P : Matrix (Fin 1) (Fin 1) ℂ := 1
    projectionProbability H rho P 1 = projectionProbability H rho P 0 := by
  dsimp
  exact (projection_probability_flow 0 1 _ (by simp) (by simp)).2.2 (by simp) 1

#print axioms projection_probability_flow

end D5.S3.Quantum.Dynamics.ProjectionProbabilityFlow
