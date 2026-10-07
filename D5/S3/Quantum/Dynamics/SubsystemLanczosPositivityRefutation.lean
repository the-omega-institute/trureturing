/- GID: D5/S3/Quantum/Dynamics/SubsystemLanczosPositivityRefutation
   generality: G
   mirror-B: D5/B/S3/Quantum/Dynamics/SubsystemLanczosPositivityRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Dynamics/SubsystemLanczosPositivityRefutation.claim; result=D5/S3/Quantum/Dynamics/SubsystemLanczosPositivityRefutation.result; claim=D5/S3/Quantum/Dynamics/SubsystemLanczosPositivityRefutation.claim
   digest: An entangled two-qubit state refutes subsystem Lanczos positivity. -/

/-
proof_shape: result: bind-only
escape_witness: none
admission_basis: open-problem-resolution (#13270; Refuted)
Direct frozen dependencies:
  D5/S3/Quantum/Information/PartialTraceMutualInformation.partialTraceRight_add
    statement_id: sha256:b9bdbbf9eb046a8b8b45384527347b653edead7fd52e914aa4b6ebbd144f8a39
  D5/S3/Quantum/PureState/PureStateHandshake.rankOneDensity
    statement_id: sha256:e18ab4fd557d4917e344a15c06172fc321b99eb187307a88fe4c7fa4f8a28bf3
  D5/S3/Quantum/Information/PartialTraceMutualInformation.partialTraceRight
    statement_id: sha256:8fd00cbe799f3e8a3163a296b2ad235e0a251e3e79b744b52197ba12d0343f77
  D5/S3/Quantum/Dynamics/ProjectionProbabilityFlow.hamiltonianPropagator
    statement_id: sha256:cda9b54324a60c3d19d82ae43fd312bec7fd42bc7d2748ad663e34115d863ceb
  D5/S3/Quantum/Dynamics/ProjectionProbabilityFlow.hamiltonianGenerator
    statement_id: sha256:4c0ebd78b0aa0a551d6207706ae2d39b87a3d18687dc8dcb29e00bd4e58a735a
  D5/S3/Quantum/FiniteDimensional.qubitX
    statement_id: sha256:cfaddf4a17693b52013e93be8cd6559e7021ed57ca0305492712468b57f882f7
  D5/S3/Quantum/Decoherence/ProjectedUnistochasticDynamics.basisProjector
    statement_id: sha256:f27898d5132f8421278f0ef62dcd324ce16233ccb31048095ccf39e51f01ecbd
Information-escape registration is paused under CLAUDE.md §3.9.
-/

import D5.S3.Quantum.Information.PartialTraceMutualInformation
import D5.S3.Quantum.PureState.PureStateHandshake
import D5.S3.Quantum.Dynamics.ProjectionProbabilityFlow

noncomputable section
open Matrix NormedSpace
open scoped BigOperators Matrix.Norms.L2Operator
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.Quantum.PureState.PureStateHandshake
open D5.S3.Quantum.Dynamics.ProjectionProbabilityFlow
open D5.S3.Quantum.FiniteDimensional
open D5.S3.Quantum.Decoherence.ProjectedUnistochasticDynamics

namespace D5.S3.Quantum.Dynamics.SubsystemLanczosPositivityRefutation

def rho {a b : ℕ} (ψ : EuclideanSpace ℂ (Fin a × Fin b))
    (H : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)
    (t : ℝ) : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ :=
  hamiltonianPropagator H t * rankOneDensity ψ * (hamiltonianPropagator H t)ᴴ
def rhoA {a b : ℕ} (ψ : EuclideanSpace ℂ (Fin a × Fin b))
    (H : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (t : ℝ) : Matrix (Fin a) (Fin a) ℂ :=
  partialTraceRight (rho ψ H t)
def returnAmplitude {a b : ℕ} (ψ : EuclideanSpace ℂ (Fin a × Fin b))
    (H : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (t : ℝ) : ℝ :=
  (Matrix.trace (rhoA ψ H t * rhoA ψ H 0)).re /
    (Matrix.trace (rhoA ψ H 0 * rhoA ψ H 0)).re
def moment {a b : ℕ} (ψ : EuclideanSpace ℂ (Fin a × Fin b))
    (H : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (n : ℕ) : ℝ :=
  iteratedDeriv n (returnAmplitude ψ H) 0
def claim : Prop := ∀ (a b : ℕ) (ψ : EuclideanSpace ℂ (Fin a × Fin b))
    (H : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ),
  ‖ψ‖ = 1 → H.IsHermitian → 0 < (moment ψ H 1)^2 - moment ψ H 2

theorem result : ¬ claim := by
  have propagator_source {a b : ℕ}
      (H : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (t : ℝ) :
      hamiltonianPropagator H t = NormedSpace.exp ((-(t : ℂ) * Complex.I) • H) := by
    simp only [hamiltonianPropagator, hamiltonianGenerator,
      RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul, mul_neg, neg_mul]
    rfl

  have propagator_zero {a b : ℕ}
      (H : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) : hamiltonianPropagator H 0 = 1 := by
    simp [hamiltonianPropagator]

  have propagator_deriv {a b : ℕ} (H : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (t : ℝ) :
      HasDerivAt (hamiltonianPropagator H) (hamiltonianPropagator H t * hamiltonianGenerator H) t := by
    exact hasDerivAt_exp_smul_const (hamiltonianGenerator H) t

  let readout {a b : ℕ} (ψ : EuclideanSpace ℂ (Fin a × Fin b))
      (H : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) :
      Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ →L[ℝ] ℝ :=
    Complex.reCLM.comp (({
      toFun := fun X => Matrix.trace (partialTraceRight X * rhoA ψ H 0)
      map_add' := by
        intro X Y
        simp [partialTraceRight_add, add_mul, Matrix.trace_add]
      map_smul' := by
        intro c X
        have hs : partialTraceRight (c • X) = c • partialTraceRight X := by
          ext i j
          simp [partialTraceRight, Finset.smul_sum]
        rw [hs, smul_mul_assoc, Matrix.trace_smul]
        rfl
      } : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ →ₗ[ℝ] ℂ).toContinuousLinearMap)

  let purity {a b : ℕ} (ψ : EuclideanSpace ℂ (Fin a × Fin b))
      (H : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) : ℝ :=
    (Matrix.trace (rhoA ψ H 0 * rhoA ψ H 0)).re
  let rhoPrime {a b : ℕ} (ψ : EuclideanSpace ℂ (Fin a × Fin b))
      (H : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)
      (t : ℝ) : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ :=
    (hamiltonianPropagator H t * hamiltonianGenerator H) * rankOneDensity ψ * star (hamiltonianPropagator H t) +
    hamiltonianPropagator H t * rankOneDensity ψ * star (hamiltonianPropagator H t * hamiltonianGenerator H)
  let rhoSecond {a b : ℕ} (ψ : EuclideanSpace ℂ (Fin a × Fin b))
      (H : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)
      (t : ℝ) : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ :=
    ((hamiltonianPropagator H t * hamiltonianGenerator H) * hamiltonianGenerator H) *
      rankOneDensity ψ * star (hamiltonianPropagator H t) +
    (hamiltonianPropagator H t * hamiltonianGenerator H) * rankOneDensity ψ *
      star (hamiltonianPropagator H t * hamiltonianGenerator H) +
    ((hamiltonianPropagator H t * hamiltonianGenerator H) * rankOneDensity ψ *
      star (hamiltonianPropagator H t * hamiltonianGenerator H) +
    hamiltonianPropagator H t * rankOneDensity ψ *
      star ((hamiltonianPropagator H t * hamiltonianGenerator H) * hamiltonianGenerator H))

  have rho_deriv {a b : ℕ} (ψ : EuclideanSpace ℂ (Fin a × Fin b))
      (H : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (t : ℝ) :
      HasDerivAt (rho ψ H) (rhoPrime ψ H t) t := by
    have source_evolution : rho ψ H = fun s : ℝ =>
        NormedSpace.exp ((-(s : ℂ) * Complex.I) • H) * rankOneDensity ψ *
          (NormedSpace.exp ((-(s : ℂ) * Complex.I) • H))ᴴ := by
      funext s
      simp only [rho, propagator_source]
    have source_deriv :
        HasDerivAt (fun s : ℝ => NormedSpace.exp ((-(s : ℂ) * Complex.I) • H))
          (NormedSpace.exp ((-(t : ℂ) * Complex.I) • H) * hamiltonianGenerator H) t := by
      have source_function : hamiltonianPropagator H =
          fun s : ℝ => NormedSpace.exp ((-(s : ℂ) * Complex.I) • H) :=
        funext (propagator_source H)
      simpa only [source_function] using propagator_deriv H t
    rw [source_evolution]
    simp only [rhoPrime, propagator_source]
    exact (source_deriv.mul_const (rankOneDensity ψ)).mul source_deriv.star

  have rhoPrime_deriv {a b : ℕ} (ψ : EuclideanSpace ℂ (Fin a × Fin b))
      (H : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (t : ℝ) :
      HasDerivAt (rhoPrime ψ H) (rhoSecond ψ H t) t := by
    have hU := propagator_deriv H t
    have hUG := hU.mul_const (hamiltonianGenerator H)
    exact ((hUG.mul_const (rankOneDensity ψ)).mul hU.star).add
      ((hU.mul_const (rankOneDensity ψ)).mul hUG.star)

  have amplitude_deriv {a b : ℕ} (ψ : EuclideanSpace ℂ (Fin a × Fin b))
      (H : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (t : ℝ) :
      HasDerivAt (returnAmplitude ψ H)
        (readout ψ H (rhoPrime ψ H t) / purity ψ H) t := by
    exact ((readout ψ H).hasFDerivAt.comp_hasDerivAt t (rho_deriv ψ H t)).div_const _

  have amplitude_second {a b : ℕ} (ψ : EuclideanSpace ℂ (Fin a × Fin b))
      (H : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (t : ℝ) :
      HasDerivAt (deriv (returnAmplitude ψ H))
        (readout ψ H (rhoSecond ψ H t) / purity ψ H) t := by
    have hfun : deriv (returnAmplitude ψ H) =
        fun s => readout ψ H (rhoPrime ψ H s) / purity ψ H :=
      funext fun s => (amplitude_deriv ψ H s).deriv
    rw [hfun]
    exact ((readout ψ H).hasFDerivAt.comp_hasDerivAt t (rhoPrime_deriv ψ H t)).div_const _

  let psi : EuclideanSpace ℂ (Fin 2 × Fin 2) := WithLp.toLp 2 (fun p =>
    if p = (0,0) then (3/5 : ℂ) else if p = (1,1) then (4/5 : ℂ) else 0)
  let hamiltonian : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
    Matrix.kronecker qubitX (basisProjector (0 : Fin 2))

  have psi_normalized : ‖psi‖ = 1 := by
    have hs : ‖psi‖ ^ 2 = 1 := by
      rw [EuclideanSpace.norm_sq_eq]
      norm_num [psi, Fintype.sum_prod_type, Fin.sum_univ_two, ← Complex.normSq_eq_norm_sq,
        Complex.normSq]
    have hn := norm_nonneg psi
    nlinarith

  have hamiltonian_hermitian : hamiltonian.IsHermitian := by
    apply Matrix.IsHermitian.ext
    intro p q
    rcases p with ⟨a,b⟩
    rcases q with ⟨c,d⟩
    fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
      norm_num [hamiltonian, qubitX, basisProjector, Matrix.single, Matrix.kronecker_apply]

  have purity_witness : purity psi hamiltonian = 337/625 := by
    norm_num [purity, rhoA, rho, propagator_zero, rankOneDensity, psi,
      partialTraceRight, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.vecMulVec_apply,
      Pi.star_apply, Complex.star_def, map_ofNat, Matrix.conjTranspose_apply]

  have first_readout : readout psi hamiltonian (rhoPrime psi hamiltonian 0) = 0 := by
    simp only [readout, rhoPrime, rhoA, rho, propagator_zero,
      Matrix.conjTranspose_one, star_one, one_mul, mul_one]
    norm_num [readout, rhoPrime, hamiltonianGenerator, propagator_zero,
      rhoA, rho, rankOneDensity, psi, hamiltonian, qubitX, basisProjector, Matrix.single,
          Matrix.kronecker_apply,
      partialTraceRight, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.vecMulVec_apply,
      Pi.star_apply, Complex.star_def, map_ofNat, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_apply, Matrix.smul_apply, smul_eq_mul,
      Complex.mul_re, Complex.mul_im]

  have second_readout : readout psi hamiltonian (rhoSecond psi hamiltonian 0) = 126/625 := by
    simp only [readout, rhoSecond, rhoA, rho, propagator_zero,
      Matrix.conjTranspose_one, star_one, one_mul, mul_one]
    norm_num [readout, rhoSecond, hamiltonianGenerator, propagator_zero,
      rhoA, rho, rankOneDensity, psi, hamiltonian, qubitX, basisProjector, Matrix.single,
          Matrix.kronecker_apply,
      partialTraceRight, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.vecMulVec_apply,
      Pi.star_apply, Complex.star_def, map_ofNat, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_apply, Matrix.smul_apply, smul_eq_mul,
      Complex.mul_re, Complex.mul_im]

  have first_moment : moment psi hamiltonian 1 = 0 := by
    unfold moment
    rw [iteratedDeriv_one, (amplitude_deriv psi hamiltonian 0).deriv,
      first_readout]
    simp

  have second_moment : moment psi hamiltonian 2 = 126/337 := by
    unfold moment
    rw [iteratedDeriv_succ (n := 1), iteratedDeriv_one,
      (amplitude_second psi hamiltonian 0).deriv, second_readout, purity_witness]
    norm_num

  have witness_coefficient :
      (moment psi hamiltonian 1)^2 - moment psi hamiltonian 2 = -126/337 := by
    rw [first_moment, second_moment]
    norm_num

  intro h
  have hpos := h 2 2 psi hamiltonian psi_normalized hamiltonian_hermitian
  rw [witness_coefficient] at hpos
  norm_num at hpos


#print axioms result

end D5.S3.Quantum.Dynamics.SubsystemLanczosPositivityRefutation
