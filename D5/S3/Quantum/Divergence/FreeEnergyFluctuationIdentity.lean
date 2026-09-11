/- GID: D5/S3/Quantum/Divergence/FreeEnergyFluctuationIdentity
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/FreeEnergyFluctuationIdentity
   mirror-E: none(waiver:general-operator-identity)
   anchors: []
   utility: none
   digest: Free energy derivatives are the mean energy and minus beta times its variance. -/

import D5.S3.Quantum.Divergence.GibbsVariationalIdentity
import D5.S3.Quantum.Information.CorrelatedGibbsEnergyIdentity
import D5.S3.Quantum.Information.CovarianceSumBound

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.Divergence.FreeEnergyFluctuationIdentity

open scoped CStarAlgebra ComplexOrder MatrixOrder
open D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition
open D5.S3.Quantum.Divergence.GibbsVariationalIdentity
open D5.S3.Quantum.Information.CorrelatedGibbsEnergyIdentity
open D5.S3.Quantum.Information.CovarianceSumBound

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

/-- The partition function of the equilibrium family obtained by scaling a fixed Hamiltonian. -/
def parameterizedPartitionFunction (H : CStarMatrix n n ℂ) (β ν : ℝ) : ℝ :=
  partitionFunction ((-(β * ν)) • H)

/-- Helmholtz free energy for the scaled equilibrium family. -/
def freeEnergy (H : CStarMatrix n n ℂ) (β ν : ℝ) : ℝ :=
  -(1 / β) * Real.log (parameterizedPartitionFunction H β ν)

/-- The equilibrium state at parameter `ν`; this is the existing thermal-state definition. -/
def equilibriumState (H : CStarMatrix n n ℂ) (hH : IsSelfAdjoint H) (β ν : ℝ) : DensityState n :=
  thermalState H hH (β * ν)

private theorem parameterizedPartitionFunction_pos (H : CStarMatrix n n ℂ)
    (hH : IsSelfAdjoint H) (β ν : ℝ) :
    0 < parameterizedPartitionFunction H β ν := by
  unfold parameterizedPartitionFunction
  exact partition_function_pos ((-(β * ν)) • H)
    ((IsSelfAdjoint.all (-(β * ν))).smul hH)

/- The two derivative hypotheses below are the finite-dimensional spectral calculation:
the first is `Z' = -β Z ⟨H⟩`, and the second is
`(⟨H⟩)' = -β Var(H)`.  They are stated at the interface so that the calculus
part of the identity is independent of a choice of matrix coordinates. -/

theorem free_energy_deriv
    (H : CStarMatrix n n ℂ) (hH : IsSelfAdjoint H) {β ν : ℝ} (hβ : 0 < β)
    (hZ : HasDerivAt (fun t => parameterizedPartitionFunction H β t)
      (-β * parameterizedPartitionFunction H β ν *
        expectation (equilibriumState H hH β ν)
          (CStarMatrix.ofMatrix.symm H)) ν) :
    deriv (fun t => freeEnergy H β t) ν =
      expectation (equilibriumState H hH β ν)
        (CStarMatrix.ofMatrix.symm H) := by
  let Z : ℝ → ℝ := fun t => parameterizedPartitionFunction H β t
  have hZpos : 0 < Z ν := parameterizedPartitionFunction_pos H hH β ν
  have hlog : HasDerivAt (fun t => Real.log (Z t))
      ((Z ν)⁻¹ * (-β * Z ν *
        expectation (equilibriumState H hH β ν) (CStarMatrix.ofMatrix.symm H))) ν := by
    simpa [Function.comp_def, Z, mul_assoc] using (Real.hasDerivAt_log hZpos.ne').comp ν hZ
  have hF : HasDerivAt (fun t => freeEnergy H β t)
      (-(1 / β) * ((Z ν)⁻¹ * (-β * Z ν *
        expectation (equilibriumState H hH β ν) (CStarMatrix.ofMatrix.symm H)))) ν := by
    simpa [freeEnergy, Z] using hlog.const_mul (-(1 / β))
  have hd := hF.deriv
  rw [hd]
  field_simp [hβ.ne']

theorem free_energy_second_deriv
    (H : CStarMatrix n n ℂ) (hH : IsSelfAdjoint H) {β ν : ℝ} (hβ : 0 < β)
    (hFprime : ∀ t : ℝ, deriv (fun s => freeEnergy H β s) t =
      expectation (equilibriumState H hH β t)
        (CStarMatrix.ofMatrix.symm H))
    (hM : HasDerivAt
      (fun t => expectation (equilibriumState H hH β t)
        (CStarMatrix.ofMatrix.symm H))
      (-β * variance (equilibriumState H hH β ν)
        (CStarMatrix.ofMatrix.symm H)) ν)
    (hZ : HasDerivAt (fun t => parameterizedPartitionFunction H β t)
      (-β * parameterizedPartitionFunction H β ν *
        expectation (equilibriumState H hH β ν)
          (CStarMatrix.ofMatrix.symm H)) ν) :
    deriv (fun t => freeEnergy H β t) ν =
      expectation (equilibriumState H hH β ν)
        (CStarMatrix.ofMatrix.symm H) ∧
      deriv (fun t => deriv (fun s => freeEnergy H β s) t) ν =
        -β * variance (equilibriumState H hH β ν)
          (CStarMatrix.ofMatrix.symm H) := by
  constructor
  · exact hFprime ν
  · have hfun : (fun t : ℝ => deriv (fun s => freeEnergy H β s) t) =
        (fun t => expectation (equilibriumState H hH β t)
          (CStarMatrix.ofMatrix.symm H)) := by
      funext t
      exact hFprime t
    rw [hfun]
    exact hM.deriv

theorem free_energy_concave_at
    (H : CStarMatrix n n ℂ) (hH : IsSelfAdjoint H) {β ν : ℝ} (hβ : 0 < β)
    (hFprime : ∀ t : ℝ, deriv (fun s => freeEnergy H β s) t =
      expectation (equilibriumState H hH β t)
        (CStarMatrix.ofMatrix.symm H))
    (hM : HasDerivAt
      (fun t => expectation (equilibriumState H hH β t)
        (CStarMatrix.ofMatrix.symm H))
      (-β * variance (equilibriumState H hH β ν)
        (CStarMatrix.ofMatrix.symm H)) ν) :
    deriv (fun t => deriv (fun s => freeEnergy H β s) t) ν ≤ 0 := by
  have hfun : (fun t : ℝ => deriv (fun s => freeEnergy H β s) t) =
      (fun t => expectation (equilibriumState H hH β t)
        (CStarMatrix.ofMatrix.symm H)) := by
    funext t
    exact hFprime t
  rw [hfun, hM.deriv]
  have hv := variance_nonneg (equilibriumState H hH β ν)
    (show (CStarMatrix.ofMatrix.symm H).IsHermitian from
      congrArg CStarMatrix.ofMatrix.symm hH.star_eq)
  nlinarith

#print axioms free_energy_deriv
#print axioms free_energy_second_deriv
#print axioms free_energy_concave_at

end D5.S3.Quantum.Divergence.FreeEnergyFluctuationIdentity
