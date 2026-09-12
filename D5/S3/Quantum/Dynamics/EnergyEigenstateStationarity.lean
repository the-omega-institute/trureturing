/- GID: D5/S3/Quantum/Dynamics/EnergyEigenstateStationarity
   generality: G
   mirror-B: D5/B/S3/Quantum/Dynamics/EnergyEigenstateStationarity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Matrix exponentials preserve eigenlines; real-energy pure states are stationary and have zero energy variance. -/

import D5.S3.Quantum.PureState.PureStateHandshake
import D5.S3.Quantum.Information.CovarianceSumBound
import Mathlib.Analysis.Normed.Algebra.MatrixExponential

set_option autoImplicit false
noncomputable section
namespace D5.S3.Quantum.Dynamics.EnergyEigenstateStationarity
open Matrix
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open D5.S3.Quantum.PureState.PureStateHandshake
open D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition
open D5.S3.Quantum.Information.CovarianceSumBound
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The matrix exponential acts on every eigenvector by the scalar exponential. -/
theorem exp_mulVec_of_eigenvector (A : Matrix n n ℂ) (v : n → ℂ) (μ : ℂ) (hv : A *ᵥ v = μ • v) :
    NormedSpace.exp A *ᵥ v = Complex.exp μ • v := by
  have hp (k : ℕ) : A ^ k *ᵥ v = μ ^ k • v := by
    by_cases hz : v = 0
    · simp [hz]
    · have he : Module.End.HasEigenvector A.toLin' μ v :=
        ⟨Module.End.mem_eigenspace_iff.mpr hv, hz⟩
      simpa only [← Matrix.toLin'_pow, Matrix.toLin'_apply] using Module.End.HasEigenvector.pow_apply he k
  let L : Matrix n n ℂ →L[ℂ] (n → ℂ) :=
    { toLinearMap := (Matrix.mulVecBilin ℂ ℂ).flip v
      cont := continuous_id.matrix_mulVec continuous_const }
  have hsum := L.hasSum (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) A)
  have hscalar := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) μ).smul_const v
  rw [← Complex.exp_eq_exp_ℂ] at hscalar
  apply HasSum.unique hsum
  change HasSum (fun k : ℕ => ((k.factorial : ℂ)⁻¹ • A ^ k) *ᵥ v) _
  simpa only [smul_mulVec, hp, smul_smul, smul_eq_mul] using hscalar

/-- The existing rank-one matrix, regarded as a positive trace-one density state. -/
def pureDensityState (v : n → ℂ) (hv : star v ⬝ᵥ v = 1) : DensityState n :=
  ⟨CStarMatrix.ofMatrix (rankOneDensity v),
    map_nonneg CStarMatrix.ofMatrixStarAlgEquiv
      (Matrix.posSemidef_vecMulVec_self_star v).nonneg,
    by
      change trace (rankOneDensity v) = 1
      rw [rankOneDensity, trace_vecMulVec, dotProduct_comm]
      exact hv⟩

/-- In units with hbar = 1, every real-time exponential of a Hermitian Hamiltonian is
unitary, and a normalized energy eigenstate has a constant density matrix. -/
theorem energy_eigenstate_stationary (H : Matrix n n ℂ) (hH : H.IsHermitian)
    (v : n → ℂ) (hv : star v ⬝ᵥ v = 1) (E t : ℝ) (he : H *ᵥ v = (E : ℂ) • v) :
    let U := NormedSpace.exp ((-Complex.I * (t : ℂ)) • H)
    let ρ := CStarMatrix.ofMatrix.symm (pureDensityState v hv).1
    U ∈ unitary (Matrix n n ℂ) ∧ U * ρ * star U = ρ := by
  dsimp only
  have hphase : NormedSpace.exp ((-Complex.I * (t : ℂ)) • H) *ᵥ v =
      Complex.exp (-Complex.I * (t : ℂ) * (E : ℂ)) • v := by
    apply exp_mulVec_of_eigenvector
    rw [smul_mulVec, he, smul_smul]
  have hc : Complex.exp (-Complex.I * (t : ℂ) * (E : ℂ)) *
      star (Complex.exp (-Complex.I * (t : ℂ) * (E : ℂ))) = 1 := by
    rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
    have hz : -Complex.I * (t : ℂ) * (E : ℂ) +
        (starRingEnd ℂ) (-Complex.I * (t : ℂ) * (E : ℂ)) = 0 := by
      simp only [map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal]
      ring
    rw [hz, Complex.exp_zero]
  constructor
  · let : NormedAlgebra ℚ (Matrix n n ℂ) := NormedAlgebra.restrictScalars ℚ ℂ _
    apply NormedSpace.exp_mem_unitary_of_mem_skewAdjoint
    apply IsSelfAdjoint.smul_mem_skewAdjoint _ hH.isSelfAdjoint
    change star (-Complex.I * (t : ℂ)) = -(-Complex.I * (t : ℂ))
    simp [Complex.star_def]
  · change NormedSpace.exp ((-Complex.I * (t : ℂ)) • H) * rankOneDensity v *
        star (NormedSpace.exp ((-Complex.I * (t : ℂ)) • H)) = rankOneDensity v
    rw [rankOneDensity, star_eq_conjTranspose, mul_vecMulVec, vecMulVec_mul,
      ← star_mulVec, hphase]
    ext i j
    simp only [vecMulVec_apply, Pi.smul_apply, Pi.star_apply, star_mul, smul_eq_mul]
    calc
      _ = (Complex.exp (-Complex.I * (t : ℂ) * (E : ℂ)) *
          star (Complex.exp (-Complex.I * (t : ℂ) * (E : ℂ)))) *
          (v i * star (v j)) := by ring
      _ = _ := by rw [hc, one_mul]

private theorem expectation_eigenvector (v : n → ℂ) (hv : star v ⬝ᵥ v = 1)
    (A : Matrix n n ℂ) (μ : ℂ) (he : A *ᵥ v = μ • v) :
    expectation (pureDensityState v hv) A = μ.re := by
  change (trace (rankOneDensity v * A)).re = μ.re
  rw [trace_mul_comm, ← (pure_state_handshake v hv A).2.2,
    he, dotProduct_smul, hv, smul_eq_mul, mul_one]

/-- The energy observable has zero variance in the same normalized pure eigenstate. -/
theorem energy_eigenstate_variance_zero (H : Matrix n n ℂ)
    (v : n → ℂ) (hv : star v ⬝ᵥ v = 1) (E : ℝ) (he : H *ᵥ v = (E : ℂ) • v) :
    variance (pureDensityState v hv) H = 0 := by
  have he2 : (H * H) *ᵥ v = ((E : ℂ) ^ 2) • v := by
    rw [← mulVec_mulVec, he, mulVec_smul, he, smul_smul, pow_two]
  rw [variance, expectation_eigenvector v hv (H * H) _ he2,
    expectation_eigenvector v hv H _ he]
  simp only [← Complex.ofReal_pow, Complex.ofReal_re, sub_self]

#print axioms exp_mulVec_of_eigenvector
#print axioms energy_eigenstate_stationary
#print axioms energy_eigenstate_variance_zero
end D5.S3.Quantum.Dynamics.EnergyEigenstateStationarity
