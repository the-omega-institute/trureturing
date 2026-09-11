/- GID: D5/S3/Quantum/Information/CorrelatedGibbsEnergyIdentity
   generality: G
   mirror-B: D5/B/S3/Quantum/Information/CorrelatedGibbsEnergyIdentity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Gibbs marginals link energy changes to relative entropy and correlation changes. -/

import D5.S3.Quantum.Divergence.GibbsVariationalIdentity
import D5.S3.Quantum.Information.PartialTraceMutualInformation
import D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.Information.CorrelatedGibbsEnergyIdentity

open scoped ComplexOrder CStarAlgebra MatrixOrder
open D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition
open D5.S3.Quantum.Divergence.VonNeumannEntropyPinching
open D5.S3.Quantum.Divergence.GibbsVariationalIdentity
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity
open D5.S3.Quantum.Dynamics.ProjectionProbabilityFlow
open D5.S3.Quantum.Decoherence.ProjectedUnistochasticDynamics

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The mean energy of a density state for the physical Hamiltonian H. -/
def meanEnergy (H : CStarMatrix n n ℂ) (rho : DensityState n) : ℝ :=
  (Matrix.trace (CStarMatrix.ofMatrix.symm (H * rho.1))).re

/-- The existing Gibbs state evaluated at the dimensionless generator -beta H. -/
def thermalState [Nonempty n] (H : CStarMatrix n n ℂ) (hH : IsSelfAdjoint H)
    (beta : ℝ) : DensityState n :=
  gibbsState ((-beta) • H) ((IsSelfAdjoint.all (-beta)).smul hH)

/-- A thermal initial state converts relative entropy into beta times energy change
minus entropy change. The final state need not commute with the Hamiltonian. -/
theorem gibbs_relative_entropy_energy_difference [Nonempty n]
    (H : CStarMatrix n n ℂ) (hH : IsSelfAdjoint H) (beta : ℝ)
    (initial final : DensityState n) (hInitial : initial = thermalState H hH beta) :
    quantumRelativeEntropy final (thermalState H hH beta) =
      beta * (meanEnergy H final - meanEnergy H initial) -
        (vonNeumannEntropy final - vonNeumannEntropy initial) := by
  subst initial
  have hf := gibbs_variational_identity ((-beta) • H)
    ((IsSelfAdjoint.all (-beta)).smul hH) final
  have hi := gibbs_variational_identity ((-beta) • H)
    ((IsSelfAdjoint.all (-beta)).smul hH) (thermalState H hH beta)
  have hSelf : quantumRelativeEntropy (thermalState H hH beta)
      (thermalState H hH beta) = 0 := by
    simp only [quantumRelativeEntropy, sub_self, mul_zero]
    change (Matrix.trace (0 : Matrix n n ℂ)).re = 0
    simp
  have hTrace (sigma : DensityState n) :
      (Matrix.trace (CStarMatrix.ofMatrix.symm (((-beta) • H) * sigma.1))).re =
        -beta * meanEnergy H sigma := by
    change (Matrix.trace (((-beta) • CStarMatrix.ofMatrix.symm H) *
      CStarMatrix.ofMatrix.symm sigma.1)).re = _
    rw [Matrix.smul_mul, Matrix.trace_smul, Complex.smul_re]
    rfl
  change _ = _ + _ + quantumRelativeEntropy final (thermalState H hH beta) at hf
  change _ = _ + _ + quantumRelativeEntropy (thermalState H hH beta)
    (thermalState H hH beta) at hi
  rw [hTrace] at hf
  rw [hTrace, hSelf] at hi
  linarith

private theorem unitary_state_one (rho : DensityState n) :
    unitaryConjugateState 1 (Matrix.unitaryGroup n ℂ).one_mem rho = rho := by
  apply Subtype.ext
  change CStarMatrix.ofMatrix (1 * densityMatrix rho * star (1 : Matrix n n ℂ)) = _
  simp only [star_one, Matrix.one_mul, Matrix.mul_one]
  rfl

private theorem pinching_after_unitary (U : Matrix n n ℂ)
    (hU : U ∈ Matrix.unitaryGroup n ℂ) (rho : DensityState n) :
    vonNeumannEntropy (basisPinchingState (unitaryConjugateState U hU rho)) -
      vonNeumannEntropy rho = quantumRelativeEntropy (unitaryConjugateState U hU rho)
        (basisPinchingState (unitaryConjugateState U hU rho)) := by
  let step : DensityState n → DensityState n :=
    fun sigma => basisPinchingState (unitaryConjugateState U hU sigma)
  have h := (entropy_production_coherence_deletion_identity U hU
    (fun k => (step^[k]) rho) (fun k => Function.iterate_succ_apply' step k rho)).1 0 |>.1
  simpa only [Function.iterate_zero_apply, Function.iterate_one, zero_add, step] using h

/-- Unitary conjugation preserves total entropy, including for singular density states. -/
theorem von_neumann_entropy_unitary (U : Matrix n n ℂ)
    (hU : U ∈ Matrix.unitaryGroup n ℂ) (rho : DensityState n) :
    vonNeumannEntropy (unitaryConjugateState U hU rho) = vonNeumannEntropy rho := by
  have h := pinching_after_unitary U hU rho
  have hOne := pinching_after_unitary 1 (Matrix.unitaryGroup n ℂ).one_mem
    (unitaryConjugateState U hU rho)
  rw [unitary_state_one] at hOne
  linarith

variable {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-- Under a joint unitary, the two marginal entropy changes sum to the change of
mutual information. Initial correlations are retained. -/
theorem marginal_entropy_change_eq_mutual_information_change
    (U : Matrix (A × B) (A × B) ℂ) (hU : U ∈ Matrix.unitaryGroup (A × B) ℂ)
    (rho : DensityState (A × B)) :
    let final := unitaryConjugateState U hU rho
    (vonNeumannEntropy (marginalRight final) - vonNeumannEntropy (marginalRight rho)) +
      (vonNeumannEntropy (marginalLeft final) - vonNeumannEntropy (marginalLeft rho)) =
        quantumMutualInformation final - quantumMutualInformation rho := by
  dsimp only
  unfold quantumMutualInformation
  rw [von_neumann_entropy_unitary]
  ring

/-- Exact energy-information balance for thermal marginals and arbitrary joint unitary
evolution. The initial joint state is not required to be a product state. -/
theorem energy_information_identity [Nonempty A] [Nonempty B]
    (HA : CStarMatrix A A ℂ) (hHA : IsSelfAdjoint HA) (betaA : ℝ)
    (HB : CStarMatrix B B ℂ) (hHB : IsSelfAdjoint HB) (betaB : ℝ)
    (rho : DensityState (A × B))
    (hA : marginalRight rho = thermalState HA hHA betaA)
    (hB : marginalLeft rho = thermalState HB hHB betaB)
    (U : Matrix (A × B) (A × B) ℂ) (hU : U ∈ Matrix.unitaryGroup (A × B) ℂ) :
    let final := unitaryConjugateState U hU rho
    betaA * (meanEnergy HA (marginalRight final) - meanEnergy HA (marginalRight rho)) +
      betaB * (meanEnergy HB (marginalLeft final) - meanEnergy HB (marginalLeft rho)) =
        quantumRelativeEntropy (marginalRight final) (thermalState HA hHA betaA) +
          quantumRelativeEntropy (marginalLeft final) (thermalState HB hHB betaB) +
            quantumMutualInformation final - quantumMutualInformation rho := by
  dsimp only
  have hLeft := gibbs_relative_entropy_energy_difference HA hHA betaA
    (marginalRight rho) (marginalRight (unitaryConjugateState U hU rho)) hA
  have hRight := gibbs_relative_entropy_energy_difference HB hHB betaB
    (marginalLeft rho) (marginalLeft (unitaryConjugateState U hU rho)) hB
  have hInfo := marginal_entropy_change_eq_mutual_information_change U hU rho
  dsimp only at hInfo
  linarith

#print axioms gibbs_relative_entropy_energy_difference
#print axioms von_neumann_entropy_unitary
#print axioms marginal_entropy_change_eq_mutual_information_change
#print axioms energy_information_identity

end D5.S3.Quantum.Information.CorrelatedGibbsEnergyIdentity
