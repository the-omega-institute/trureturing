/- GID: D5/S3/Quantum/Information/StrongSubadditivity
   generality: G
   mirror-B: D5/B/S3/Quantum/Information/StrongSubadditivity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Strong subadditivity for actual density states and their partial traces. -/

import D5.S3.Quantum.Information.StrongSubadditivity.Physlib.Entropy.SSA
import D5.S3.Quantum.Information.OrthogonalRecordEntropy
import D5.S3.Quantum.Foundation.FiniteDensityPurification

/- The supplier is Physlib Sᵥₙ_strong_subadditivity at revision
2725b6f621901d4cd330869e9b77105045c1582e. Its retained source closure
preserves the original Apache-2.0 notices and proofs. The receiving bridge
below uses the same matrix, coordinate partial traces, and natural logarithm.
It does not require invertibility or support assumptions. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped MatrixOrder ComplexOrder CStarAlgebra
open D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition
open D5.S3.Quantum.Divergence.VonNeumannEntropyPinching
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.Quantum.Foundation.FiniteDensityPurification (toMState toDensity)

namespace D5.S3.Quantum.Information.StrongSubadditivity

variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

local instance : ContinuousFunctionalCalculus ℝ (CStarMatrix n n ℂ) IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus

@[simp] theorem toMState_matrix (rho : DensityState n) :
    (toMState rho).m = CStarMatrix.ofMatrix.symm rho.1 := rfl

@[simp] theorem toMState_toDensity (rho : MState n) :
    toMState (toDensity rho) = rho := MState.ext_m (toMState_matrix _)

/-- A finite basis relabeling; the matrix entry at i,j is rho(e i,e j). -/
noncomputable def relabelState (e : m ≃ n) (rho : DensityState n) : DensityState m :=
  toDensity ((toMState rho).relabel e)

@[simp] theorem relabelState_matrix (e : m ≃ n) (rho : DensityState n) (i j : m) :
    CStarMatrix.ofMatrix.symm (relabelState e rho).1 i j =
      CStarMatrix.ofMatrix.symm rho.1 (e i) (e j) := rfl

@[simp] theorem toMState_marginalLeft (rho : DensityState (n × m)) :
    toMState (marginalLeft rho) = (toMState rho).traceLeft := MState.ext_m rfl

@[simp] theorem toMState_marginalRight (rho : DensityState (n × m)) :
    toMState (marginalRight rho) = (toMState rho).traceRight := MState.ext_m rfl

/-- The natural-log entropy bridge, valid also on zero eigenvalues. -/
theorem entropy_toMState (rho : DensityState n) :
    Sᵥₙ (toMState rho) = vonNeumannEntropy rho := by
  rw [Sᵥₙ_eq_trace_cfc_negMulLog, HermitianMat.trace_eq_re_trace, HermitianMat.mat_cfc,
    OrthogonalRecordEntropy.entropy_eq_trace_cfc]
  unfold OrthogonalRecordEntropy.realTrace
  have hmap : CStarMatrix.ofMatrix
      (cfc Real.negMulLog (CStarMatrix.ofMatrix.symm rho.1)) =
      cfc Real.negMulLog rho.1 :=
    StarAlgHomClass.map_cfc CStarMatrix.ofMatrixStarAlgEquiv
      Real.negMulLog (CStarMatrix.ofMatrix.symm rho.1)
      ((CStarMatrix.ofMatrix.symm rho.1).finite_real_spectrum.continuousOn _)
      CStarMatrix.ofMatrixL.continuous (density_posSemidef rho).isHermitian
      (by exact (density_posSemidef rho).isHermitian)
  exact congrArg (fun M : CStarMatrix n n ℂ => (Matrix.trace M).re) hmap

@[simp] theorem entropy_relabelState (e : m ≃ n) (rho : DensityState n) :
    vonNeumannEntropy (relabelState e rho) = vonNeumannEntropy rho := by
  rw [← entropy_toMState, relabelState, toMState_toDensity, Sᵥₙ_relabel,
    entropy_toMState]

/-- Actual-marginal SSA on every finite density state, including singular states. -/
theorem strong_subadditivity
    {A B C : Type*} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]
    (rho : DensityState (A × (B × C))) :
    vonNeumannEntropy rho + vonNeumannEntropy (marginalRight (marginalLeft rho)) ≤
      vonNeumannEntropy (marginalRight (relabelState (Equiv.prodAssoc A B C) rho)) +
        vonNeumannEntropy (marginalLeft rho) := by
  have h := Sᵥₙ_strong_subadditivity (toMState rho)
  change Sᵥₙ (toMState rho) + Sᵥₙ (toMState rho).traceLeft.traceRight ≤
    Sᵥₙ (toMState rho).assoc'.traceRight + Sᵥₙ (toMState rho).traceLeft at h
  have hassoc : toMState (relabelState (Equiv.prodAssoc A B C) rho) =
      (toMState rho).assoc' := MState.ext_m rfl
  simpa only [← toMState_marginalLeft, ← toMState_marginalRight, ← hassoc,
    entropy_toMState] using h

#print axioms strong_subadditivity
#print axioms entropy_toMState

end D5.S3.Quantum.Information.StrongSubadditivity
