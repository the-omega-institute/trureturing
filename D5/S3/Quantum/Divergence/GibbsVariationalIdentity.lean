/- GID: D5/S3/Quantum/Divergence/GibbsVariationalIdentity
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/GibbsVariationalIdentity
   mirror-E: none(waiver:general-operator-identity)
   anchors: [mathlib/module/Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic]
   utility: none
   digest: The normalized matrix exponential gives the Gibbs entropy decomposition. -/

import D5.S3.Quantum.Divergence.VonNeumannEntropyPinching
import Mathlib.Analysis.Matrix.Order

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.Divergence.GibbsVariationalIdentity

open scoped CStarAlgebra ComplexOrder MatrixOrder
open NormedSpace
open D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition
open D5.S3.Quantum.Divergence.VonNeumannEntropyPinching

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

/-- The real trace of the ordinary matrix exponential. -/
def partitionFunction (H : CStarMatrix n n ℂ) : ℝ :=
  (Matrix.trace (CStarMatrix.ofMatrix.symm (exp H))).re

omit [Nonempty n] in
private theorem exp_strictly_positive (H : CStarMatrix n n ℂ) (hH : IsSelfAdjoint H) :
    IsStrictlyPositive (exp H) := by
  let : NormedAlgebra ℚ (CStarMatrix n n ℂ) := .restrictScalars ℚ ℂ _
  exact (isUnit_exp H).isStrictlyPositive hH.exp_nonneg

omit [Nonempty n] in
private theorem posDef_of_strictly_positive {A : CStarMatrix n n ℂ}
    (hA : IsStrictlyPositive A) : (CStarMatrix.ofMatrix.symm A).PosDef := by
  have hn : 0 ≤ CStarMatrix.ofMatrix.symm A :=
    map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm hA.nonneg
  apply (Matrix.nonneg_iff_posSemidef.mp hn).posDef_iff_isUnit.mpr
  exact hA.isUnit.map CStarMatrix.ofMatrixRingEquiv.symm.toMonoidHom

/-- The partition function of a Hermitian matrix is strictly positive. -/
theorem partition_function_pos (H : CStarMatrix n n ℂ) (hH : IsSelfAdjoint H) :
    0 < partitionFunction H := by
  have hp : (CStarMatrix.ofMatrix.symm (exp H)).PosDef := by
    exact posDef_of_strictly_positive (exp_strictly_positive H hH)
  exact (Complex.pos_iff.mp hp.trace_pos).1

private theorem trace_exp_eq (H : CStarMatrix n n ℂ) (hH : IsSelfAdjoint H) :
    Matrix.trace (CStarMatrix.ofMatrix.symm (exp H)) = (partitionFunction H : ℂ) := by
  have hp : (CStarMatrix.ofMatrix.symm (exp H)).PosDef := by
    exact posDef_of_strictly_positive (exp_strictly_positive H hH)
  apply Complex.ext
  · rfl
  · exact (Complex.pos_iff.mp hp.trace_pos).2.symm

/-- The Gibbs state uses scalar normalization, with no commutation assumption on other states. -/
def gibbsState (H : CStarMatrix n n ℂ) (hH : IsSelfAdjoint H) : DensityState n :=
  ⟨(partitionFunction H)⁻¹ • exp H,
    (IsStrictlyPositive.smul (inv_pos.mpr (partition_function_pos H hH))
      (exp_strictly_positive H hH)).nonneg, by
    change Matrix.trace ((partitionFunction H)⁻¹ • CStarMatrix.ofMatrix.symm (exp H)) = 1
    rw [Matrix.trace_smul, trace_exp_eq H hH]
    simp [Complex.real_smul, ne_of_gt (partition_function_pos H hH)]⟩

/-- The Gibbs density is positive definite. -/
theorem gibbs_state_posDef (H : CStarMatrix n n ℂ) (hH : IsSelfAdjoint H) :
    (CStarMatrix.ofMatrix.symm (gibbsState H hH).1).PosDef := by
  apply posDef_of_strictly_positive
  exact IsStrictlyPositive.smul (inv_pos.mpr (partition_function_pos H hH))
    (exp_strictly_positive H hH)

/-- Spectral logarithm of the normalized exponential, using Mathlib's CFC logarithm. -/
theorem log_gibbs_state (H : CStarMatrix n n ℂ) (hH : IsSelfAdjoint H) :
    CFC.log (gibbsState H hH).1 = H - Real.log (partitionFunction H) • 1 := by
  change CFC.log ((partitionFunction H)⁻¹ • exp H) = _
  erw [CFC.log_smul' (A := CStarMatrix n n ℂ) (exp H) (inv_pos.mpr (partition_function_pos H hH))
    (exp_strictly_positive H hH), CFC.log_exp H hH, Real.log_inv]
  simp [Algebra.algebraMap_eq_smul_one, sub_eq_add_neg, add_comm]

/-- The Gibbs variational identity in nats. It holds for every density state, in particular
for every positive definite density matrix, even when it does not commute with `H`. -/
theorem gibbs_variational_identity (H : CStarMatrix n n ℂ) (hH : IsSelfAdjoint H)
    (rho : DensityState n) :
    Real.log (partitionFunction H) = (Matrix.trace (CStarMatrix.ofMatrix.symm (H * rho.1))).re +
      vonNeumannEntropy rho + quantumRelativeEntropy rho (gibbsState H hH) := by
  rw [quantum_relative_entropy_eq_neg_entropy_sub_cross, log_gibbs_state]
  have htr : Matrix.trace (CStarMatrix.ofMatrix.symm rho.1) = 1 := rho.2.2
  change Real.log (partitionFunction H) =
    (Matrix.trace (CStarMatrix.ofMatrix.symm H * CStarMatrix.ofMatrix.symm rho.1)).re +
      vonNeumannEntropy rho + (-vonNeumannEntropy rho -
        (Matrix.trace (CStarMatrix.ofMatrix.symm rho.1 *
          (CStarMatrix.ofMatrix.symm H - Real.log (partitionFunction H) • 1))).re)
  have hcross : (Matrix.trace (CStarMatrix.ofMatrix.symm rho.1 *
      (CStarMatrix.ofMatrix.symm H - Real.log (partitionFunction H) • 1))).re =
      (Matrix.trace (CStarMatrix.ofMatrix.symm H * CStarMatrix.ofMatrix.symm rho.1)).re -
        Real.log (partitionFunction H) := by
    rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_sub,
      Matrix.trace_smul, htr, Complex.sub_re, Complex.smul_re]
    simp only [Complex.one_re, smul_eq_mul, mul_one]
    rw [Matrix.trace_mul_comm]
  rw [hcross]
  ring

/-- At zero Hamiltonian the partition function is the dimension. -/
theorem partition_function_zero :
    partitionFunction (0 : CStarMatrix n n ℂ) = Fintype.card n := by
  unfold partitionFunction
  rw [exp_zero]
  change (Matrix.trace (1 : Matrix n n ℂ)).re = _
  simp

/-- At zero Hamiltonian the Gibbs density is the maximally mixed matrix `I/d`. -/
theorem gibbs_state_zero :
    (gibbsState (0 : CStarMatrix n n ℂ) (IsSelfAdjoint.zero _)).1 =
      (Fintype.card n : ℝ)⁻¹ • (1 : CStarMatrix n n ℂ) := by
  simp [gibbsState, partition_function_zero]

/-- Entropy plus relative entropy to the maximally mixed state equals log dimension. -/
theorem entropy_uniform_identity (rho : DensityState n) :
    vonNeumannEntropy rho +
      quantumRelativeEntropy rho (gibbsState (0 : CStarMatrix n n ℂ) (IsSelfAdjoint.zero _)) =
        Real.log (Fintype.card n) := by
  have h := gibbs_variational_identity (0 : CStarMatrix n n ℂ) (IsSelfAdjoint.zero _) rho
  rw [partition_function_zero] at h
  simpa only [zero_mul, show CStarMatrix.ofMatrix.symm (0 : CStarMatrix n n ℂ) =
    (0 : Matrix n n ℂ) from rfl, Matrix.trace_zero, Complex.zero_re, zero_add] using h.symm

#print axioms gibbs_variational_identity
#print axioms entropy_uniform_identity

end D5.S3.Quantum.Divergence.GibbsVariationalIdentity
