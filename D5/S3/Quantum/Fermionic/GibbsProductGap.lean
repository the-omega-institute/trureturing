/- GID: D5/S3/Quantum/Fermionic/GibbsProductGap
   generality: I
   mirror-B: D5/B/S3/Quantum/Fermionic/GibbsProductGap
   mirror-E: none(waiver:uniform-Gibbs-product-estimates)
   anchors: []
   utility: none
   digest: Physical Gibbs marginals yield the entropy-budget lower bound on the free gap. -/

/-
gibbs_product_free_bound:
  proof_shape: content
  escape_witness: project the exponential onto a physical ground sector and its
    positive complement, then use local parity of the actual partial traces.
admission_basis: escape-witness
Same-delivery inlined content: PhysicalSiteProducts, and local declarations.
Direct frozen public dependencies after inlining same-delivery content:
  GID: D5/S3/Entropy/MaxEntropy.entropy_le_log_card
    statement_id: sha256:2036c3d1e460f61aa9db5be6bee1f085a8eb400f9dccacc5244afc890263d5b5
  GID: D5/S3/Entropy/MaxEntropy.shannonEntropy
    statement_id: sha256:0b9b0250c925b41ffab4b8ab0b198871ccb0bb46dd401760ec0158c98ad42e87
  GID: D5/S3/Quantum/Divergence/GibbsVariationalIdentity.gibbsState
    statement_id: sha256:f892a87bde5011f4627a32ee2080dbc7463d33d90133420b234b8da2d2c4d7da
  GID: D5/S3/Quantum/Divergence/GibbsVariationalIdentity.gibbs_variational_identity
    statement_id: sha256:895916cae977ded768955734c3e815db72f7049759d4a7a6a6149251df958326
  GID: D5/S3/Quantum/Divergence/GibbsVariationalIdentity.partitionFunction
    statement_id: sha256:0a01d1cd9d793907eb4414251b21f716dd8fe57b344c4e234875502c8938d9a2
  GID: D5/S3/Quantum/Divergence/QuantumRelativeEntropyDefectComposition.DensityState
    statement_id: sha256:b8e1957ba4f81600248989dc21f0a107bcdd5ce2e68546c38b9164c4a09ac337
  GID: D5/S3/Quantum/Divergence/QuantumRelativeEntropyDefectComposition.quantumRelativeEntropy
    statement_id: sha256:1fde73d469bc7e293eef439b271276205450d8758cb7358eaadae794794d8f0a
  GID: D5/S3/Quantum/Divergence/VonNeumannEntropyPinching.vonNeumannEntropy
    statement_id: sha256:9cf1e21822d8f3f61a5d349f41c4287a3ef43a0e8a600534b28ab8d06f437cd1
  GID: D5/S3/Quantum/Dynamics/EnergyEigenstateStationarity.exp_mulVec_of_eigenvector
    statement_id: sha256:4c9f2eff40b9ab9a5dd6bf3511ef67bd738e5144793aa9213135c3c33bf35942
  GID: D5/S3/Quantum/Dynamics/ProjectionProbabilityFlow.densityMatrix
    statement_id: sha256:e8ba081c519bb0c785f070157864cb2f6eecf4b55d1e6b6b8c50a07b3fb988a6
  GID: D5/S3/Quantum/FiniteDimensional.qubitZ
    statement_id: sha256:381a2bec567456715f58fe6c0c413d59d37882b8499fc81a486c49e7c081d78c
  GID: D5/S3/Quantum/FockSpace/ForbiddenNeighbourDeterminant.occupationCount
    statement_id: sha256:97804cfc85a668f345a5b3e2421ba02e5e6203f36590508faccac8726341bc0a
  GID: D5/S3/Quantum/Information/CorrelatedGibbsEnergyIdentity.meanEnergy
    statement_id: sha256:9968a03e56960da489176141fea72cbed63e67cc32e2fe1378c92e3fed11906b
  GID: D5/S3/Quantum/Information/CorrelatedGibbsEnergyIdentity.thermalState
    statement_id: sha256:c2e22ee34d0f1ca2980b540f9d8f8f13364fa370def51a817c01961207ed18c1
  GID: D5/S3/Quantum/Information/PartialTraceMutualInformation.marginalRight
    statement_id: sha256:bb5bad02426b231285a1d49fbc7f66f6f971cf3cd7ef3ee92fc2c21793f14ae7
  GID: D5/S3/Quantum/Sharpness/FreeNegentropyBudget.free_negentropy_budget
    statement_id: sha256:0b886ab8a8eb94b90ce39b027be67936f47de33369529a5679075100a0c83f4b
  GID: D5/S3/Quantum/Sharpness/FreeNegentropyBudget.stateSpectrum
    statement_id: sha256:38e1263bbbed60675d6786fa06658d9d5a3c26885815452280ecf9b8fafbd141
  GID: D5/S3/Quantum/Sharpness/FreeNegentropyBudget.von_neumann_entropy_eq_shannon_state_spectrum
    statement_id: sha256:418a3458d7e30f3b6473c08140a6b2fe6d7de5cfc410395fca6ee760d8ec80bd
  GID: D5/S3/Quantum/Sharpness/SpectralPairingCapacity.spectralPairingCapacity
    statement_id: sha256:d4afa8ecdad28cf3ab52fa0d495db95b1e14c30a3244dbfc4ff876e5b48677b4
  GID: D5/S3/Quantum/Sharpness/SpectralSharpness.spectralSharpness
    statement_id: sha256:297963932869a2d0947ffa0785c89eb0afa76eb964ab29d3f88738daffab84d2
  GID: D5/S3/Quantum/SpinChains/SupersymmetricFermion/JordanWigner.FullOperator
    statement_id: sha256:d0e241c65c207456599a205d965adefde23f6764456a0c5a832a08a676fadfb3
  GID: D5/S3/Quantum/SpinChains/SupersymmetricFermion/JordanWigner.Local
    statement_id: sha256:cea3034ad5d4c2d36ac899cc7964a23cdad5b9a52b0410ee01f4b03ffd41f349
  GID: D5/S3/Quantum/SpinChains/SupersymmetricFermion/JordanWigner.fermionWord
    statement_id: sha256:d1484b5db3ace7148c685690abf5667976f26043e824bad34ea4385d5015100d
  GID: D5/S3/Quantum/SpinChains/SupersymmetricFermion/JordanWigner.fullC
    statement_id: sha256:e5eb14acc0a2901b62190a83ed2543f27309f7f32708edd35fa0376362ebfe97
  GID: D5/S3/TotalVariation/Asymptotics/SymmetricBernoulliSecondOrder.positiveBiasLaw
    statement_id: sha256:473a802511d0e55f9584e9c1920f5e9c930ab5cc45d69cab1814325c649297b6
  GID: D5/S3/TotalVariation/Pinsker.totalVariation
    statement_id: sha256:417383b2f5f4a4f7c56881e521c516e431c6f287d2d24996ca4ec3797e2e61f3
  GID: D5/S3/Quantum/Dynamics/ClauseHamiltonian.Assignment
    statement_id: sha256:186896178b3ea09d109f4546cae53a1b2c485c3990a05a1b88d8deaaae3e423f
computational_content.kind: none; finite systems of arbitrary site and mode counts.
Four-slot escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/15194.
-/

import D5.S3.Quantum.Fermionic.PhysicalSiteProducts
import D5.S3.Quantum.Dynamics.EnergyEigenstateStationarity
import D5.S3.Quantum.Sharpness.FreeNegentropyBudget

open Matrix NormedSpace
open scoped BigOperators ComplexOrder MatrixOrder CStarAlgebra Matrix.Norms.L2Operator
open PredictiveThermodynamic.Physical (Assignment)
open D5.S3.Quantum.Divergence.GibbsVariationalIdentity
open D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition
open D5.S3.Quantum.Divergence.VonNeumannEntropyPinching
open D5.S3.Quantum.Information.CorrelatedGibbsEnergyIdentity
open D5.S3.Quantum.Fermionic.FockMajoranaCarrier
open D5.S3.Quantum.Fermionic.CoordinateEdgeHamiltonian
open D5.S3.Quantum.Fermionic.PhysicalSiteProducts
open D5.S3.Quantum.Sharpness.FreeNegentropyBudget
open D5.S3.Entropy.MaxEntropy

noncomputable section
namespace D5.S3.Quantum.Fermionic.GibbsProductGap

def energyGap {n m : ℕ}
    (H : CStarMatrix (Assignment (n*m)) (Assignment (n*m)) ℂ) : ℝ :=
  sInf {x : ℝ | ∃ rho : DensityState (Assignment (n*m)),
    physicalProduct rho ∧ x = meanEnergy H rho} -
  sInf {x : ℝ | ∃ rho : DensityState (Assignment (n*m)),
    physicalState rho ∧ x = meanEnergy H rho}

def freeEnergy {n m : ℕ}
    (H : CStarMatrix (Assignment (n*m)) (Assignment (n*m)) ℂ)
    (beta : ℝ) (rho : DensityState (Assignment (n*m))) : ℝ :=
  meanEnergy H rho - vonNeumannEntropy rho / beta

def freeGap {n m : ℕ}
    (H : CStarMatrix (Assignment (n*m)) (Assignment (n*m)) ℂ)
    (hH : IsSelfAdjoint H) (beta : ℝ) : ℝ :=
  let rho := thermalState H hH beta
  let sigma := siteProduct n m (fun v => oneSiteMarginal n m v rho)
  freeEnergy H beta sigma - freeEnergy H beta rho

theorem gibbs_product_free_bound {n m : ℕ} (G : SimpleGraph (Fin n))
    (K : G.edgeSet → Matrix (Fin m × Bool) (Fin m × Bool) ℝ)
    (had : admissibleEdges G K) (hH : IsSelfAdjoint (averagedHamiltonian G K))
    (ground : DensityState (Assignment (n*m)))
    (hproj : IsStarProjection (CStarMatrix.ofMatrix.symm ground.val))
    (E : ℝ) (heig : CStarMatrix.ofMatrix.symm (averagedHamiltonian G K) *
      CStarMatrix.ofMatrix.symm ground.val =
        (E : ℂ) • CStarMatrix.ofMatrix.symm ground.val)
    (beta : ℝ) (hbeta : 0 < beta) :
    physicalProduct (siteProduct n m (fun v => oneSiteMarginal n m v
      (thermalState (averagedHamiltonian G K) hH beta))) ∧
    freeGap (averagedHamiltonian G K) hH beta ≥
      -E - Real.log (Fintype.card (Assignment (n*m))) / beta := by
  classical
  let H := averagedHamiltonian G K
  have hcomm : Commute H (CStarMatrix.ofMatrix (numberParity (n*m))) := by
    unfold H averagedHamiltonian
    apply Commute.smul_left
    apply Commute.sum_left
    intro z _
    exact (had z).2.2
  let rho := thermalState H hH beta
  have hrho : physicalState rho := by
    change Commute ((partitionFunction ((-beta) • H))⁻¹ • exp ((-beta) • H)) _
    exact ((hcomm.smul_left (-beta)).exp_left).smul_left _
  let sigma := siteProduct n m (fun v => oneSiteMarginal n m v rho)
  have hsigma : physicalProduct sigma :=
    ⟨(fun v => oneSiteMarginal n m v rho),
      (fun v => one_site_marginal_physical n m v rho hrho),rfl⟩
  have hzero : meanEnergy H sigma = 0 := physical_products_zero G K sigma hsigma
  have hent : vonNeumannEntropy sigma ≤ Real.log (Fintype.card (Assignment (n*m))) := by
    have hp := (free_negentropy_budget sigma).1
    rw [von_neumann_entropy_eq_shannon_state_spectrum]
    simpa using entropy_le_log_card (stateSpectrum sigma) hp
  have hpartition : Real.exp (-beta * E) ≤ partitionFunction ((-beta) • H) := by
    let R := CStarMatrix.ofMatrix.symm ground.val
    have htraceone : Matrix.trace R = 1 := ground.property.2
    let : NormedAlgebra ℚ (CStarMatrix (Assignment (n*m)) (Assignment (n*m)) ℂ) := .restrictScalars ℚ ℂ _
    let X := (-beta) • H
    let A := CStarMatrix.ofMatrix.symm (exp X)
    have hAR : A * R = (Real.exp (-beta * E) : ℂ) • R := by
      have hx : CStarMatrix.ofMatrix.symm X * R = ((-beta * E : ℝ) : ℂ) • R := by
        change ((-beta) • CStarMatrix.ofMatrix.symm H) * R = _
        rw [Matrix.smul_mul, heig]
        ext i j
        simp only [Matrix.smul_apply, smul_eq_mul, Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_neg]
        ring
      have he : A = exp (CStarMatrix.ofMatrix.symm X) := by
        exact NormedSpace.map_exp CStarMatrix.ofMatrixStarAlgEquiv.symm
          CStarMatrix.ofMatrixL.symm.continuous X
      rw [he]
      apply Matrix.ext
      intro i j
      have hv : (CStarMatrix.ofMatrix.symm X) *ᵥ (fun t => R t j) =
          ((-beta * E : ℝ) : ℂ) • (fun t => R t j) := by
        funext t
        exact congrArg (fun M : Matrix (Assignment (n*m)) (Assignment (n*m)) ℂ => M t j) hx
      have h := D5.S3.Quantum.Dynamics.EnergyEigenstateStationarity.exp_mulVec_of_eigenvector
        (CStarMatrix.ofMatrix.symm X) (fun t => R t j) ((-beta * E : ℝ) : ℂ) hv
      have hi := congrFun h i
      simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using hi
    have hApos : A.PosSemidef := by
      have hX : IsSelfAdjoint X := (IsSelfAdjoint.all (-beta)).smul hH
      exact Matrix.nonneg_iff_posSemidef.mp
        (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm hX.exp_nonneg)
    have hp : R * R = R := hproj.1.eq
    have hpadj : Rᴴ = R := hproj.2.star_eq
    have hcomplement : Matrix.trace ((1-R)ᴴ * A * (1-R)) =
        Matrix.trace A - (Real.exp (-beta * E) : ℂ) := by
      rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hpadj]
      have heq : (1-R)*A*(1-R) = A - R*A - A*R + R*A*R := by noncomm_ring
      rw [heq, Matrix.trace_add, Matrix.trace_sub, Matrix.trace_sub]
      have hprojA : Matrix.trace (R*A) = (Real.exp (-beta * E) : ℂ) := by
        rw [Matrix.trace_mul_comm, hAR, Matrix.trace_smul, htraceone]
        simp
      have hARA : Matrix.trace (A*R) = (Real.exp (-beta * E) : ℂ) := by
        rw [hAR, Matrix.trace_smul, htraceone]
        simp
      have hprojAR : Matrix.trace (R*A*R) = (Real.exp (-beta * E) : ℂ) := by
        rw [Matrix.mul_assoc, hAR, Matrix.mul_smul, hp, Matrix.trace_smul, htraceone]
        simp
      rw [hprojA,hARA,hprojAR]
      ring
    have hnonneg := (hApos.conjTranspose_mul_mul_same (1-R)).trace_nonneg
    rw [hcomplement] at hnonneg
    have hr : 0 ≤ (Matrix.trace A).re - Real.exp (-beta * E) :=
      (Complex.nonneg_iff.mp hnonneg).1
    change Real.exp (-beta * E) ≤ (Matrix.trace A).re
    linarith
  have hself : quantumRelativeEntropy rho rho = 0 := by
    simp only [quantumRelativeEntropy, sub_self, mul_zero]
    change (Matrix.trace (0 : Matrix (Assignment (n*m)) (Assignment (n*m)) ℂ)).re = 0
    simp
  have hid := gibbs_variational_identity ((-beta) • H)
    ((IsSelfAdjoint.all (-beta)).smul hH) rho
  have htr : (Matrix.trace (CStarMatrix.ofMatrix.symm (((-beta) • H) * rho.val))).re =
      -beta * meanEnergy H rho := by
    change (Matrix.trace (((-beta) • CStarMatrix.ofMatrix.symm H) *
      CStarMatrix.ofMatrix.symm rho.val)).re = _
    rw [Matrix.smul_mul, Matrix.trace_smul, Complex.smul_re]
    rfl
  change Real.log (partitionFunction ((-beta) • H)) = _ + _ +
    quantumRelativeEntropy rho rho at hid
  rw [htr, hself, add_zero] at hid
  have hlog : -beta * E ≤ Real.log (partitionFunction ((-beta) • H)) := by
    have hp := Real.exp_pos (-beta * E)
    have hz := hp.trans_le hpartition
    exact (Real.le_log_iff_exp_le hz).mpr hpartition
  have hrho : meanEnergy H rho - vonNeumannEntropy rho / beta ≤ E := by
    apply (mul_le_mul_iff_right₀ hbeta).mp
    have heq : (meanEnergy H rho - vonNeumannEntropy rho / beta) * beta =
        -Real.log (partitionFunction ((-beta) • H)) := by
      rw [sub_mul, div_mul_cancel₀ _ hbeta.ne']
      linarith
    rw [mul_comm beta (meanEnergy H rho - vonNeumannEntropy rho / beta), heq]
    nlinarith
  have hbudget : -Real.log (Fintype.card (Assignment (n*m))) / beta ≤
      meanEnergy H sigma - vonNeumannEntropy sigma / beta := by
    rw [hzero, zero_sub, neg_div]
    exact neg_le_neg (div_le_div_of_nonneg_right hent hbeta.le)
  refine ⟨hsigma,?_⟩
  change (meanEnergy H sigma - vonNeumannEntropy sigma / beta) -
    (meanEnergy H rho - vonNeumannEntropy rho / beta) ≥ _
  simp only [neg_div] at hbudget
  linarith

end D5.S3.Quantum.Fermionic.GibbsProductGap
