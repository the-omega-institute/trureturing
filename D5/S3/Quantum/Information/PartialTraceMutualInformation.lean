/- GID: D5/S3/Quantum/Information/PartialTraceMutualInformation
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=bridge; basis=atom-required-bridge; consumer=correlation-tax-identity
   digest: Finite matrix partial traces and mutual information form reusable bipartite
   infrastructure. -/

import D5.S3.Quantum.Divergence.VonNeumannEntropyPinching

/- Library-search audit trail (2026-09-11):
   * Repository search found only the fixed two-qubit `traceFirstFactor` in
     `LocalMarginalCorrelationBlindSpot` and the fixed two-qubit `traceEnvironment`.
   * Pinned Mathlib search found `Matrix.kroneckerMap_apply`,
     `Matrix.trace_kronecker`, and `Matrix.kronecker`; no generic partial-trace
     definition or mutual-information theorem was found.
   * Third-party GitHub code search was queried for `partialTrace Matrix Lean`
     and `mutualInformation DensityState Lean`; no exact reusable declaration
     was admitted, so this module supplies the bridge definitions below.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Information.PartialTraceMutualInformation

open scoped BigOperators ComplexOrder Kronecker Matrix
open D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition
open D5.S3.Quantum.Divergence.VonNeumannEntropyPinching

noncomputable def partialTraceLeft {A B : Type*} [Fintype A]
    (joint : Matrix (A × B) (A × B) ℂ) : Matrix B B ℂ :=
  fun b d => ∑ a, joint (a, b) (a, d)

noncomputable def partialTraceRight {A B : Type*} [Fintype B]
    (joint : Matrix (A × B) (A × B) ℂ) : Matrix A A ℂ :=
  fun a c => ∑ b, joint (a, b) (c, b)

theorem partialTraceLeft_add {A B : Type*} [Fintype A]
    (x y : Matrix (A × B) (A × B) ℂ) :
    partialTraceLeft (x + y) = partialTraceLeft x + partialTraceLeft y := by
  ext b d
  simp [partialTraceLeft, Finset.sum_add_distrib]

theorem partialTraceRight_add {A B : Type*} [Fintype B]
    (x y : Matrix (A × B) (A × B) ℂ) :
    partialTraceRight (x + y) = partialTraceRight x + partialTraceRight y := by
  ext a c
  simp [partialTraceRight, Finset.sum_add_distrib]

theorem partialTraceLeft_kronecker {A B : Type*} [Fintype A]
    (x : Matrix A A ℂ) (y : Matrix B B ℂ) :
    partialTraceLeft (Matrix.kronecker x y) = Matrix.trace x • y := by
  ext b d
  simp [partialTraceLeft, Matrix.trace, Finset.mul_sum, mul_comm]

theorem partialTraceRight_kronecker {A B : Type*} [Fintype B]
    (x : Matrix A A ℂ) (y : Matrix B B ℂ) :
    partialTraceRight (Matrix.kronecker x y) = Matrix.trace y • x := by
  ext a c
  simp [partialTraceRight, Matrix.trace, Finset.mul_sum, mul_comm]

noncomputable def quantumMutualInformation
    {A B : Type*} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    (rhoA : DensityState A) (rhoB : DensityState B)
    (rhoAB : DensityState (A × B)) : ℝ :=
  vonNeumannEntropy rhoA + vonNeumannEntropy rhoB - vonNeumannEntropy rhoAB

theorem quantum_mutual_information_formula
    {A B : Type*} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    (rhoA : DensityState A) (rhoB : DensityState B)
    (rhoAB : DensityState (A × B)) :
    quantumMutualInformation rhoA rhoB rhoAB =
      vonNeumannEntropy rhoA + vonNeumannEntropy rhoB - vonNeumannEntropy rhoAB := by
  rfl

end D5.S3.Quantum.Information.PartialTraceMutualInformation
