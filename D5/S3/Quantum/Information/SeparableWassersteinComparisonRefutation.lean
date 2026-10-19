/- GID: D5/S3/Quantum/Information/SeparableWassersteinComparisonRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Information/SeparableWassersteinComparisonRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Information/SeparableWassersteinComparisonRefutation.claim; result=D5/S3/Quantum/Information/SeparableWassersteinComparisonRefutation.result; claim=D5/S3/Quantum/Information/SeparableWassersteinComparisonRefutation.claim
   digest: Modified separable quantum transport can exceed unrestricted quantum transport. -/

import D5.S3.Quantum.QuantumChannels.QubitWassersteinCouplings
import D5.S3.Quantum.QuantumChannels.IptPptSquaredEquivalence
import D5.S3.Quantum.Matrix.PartialTransposeTrace
import D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitMaximumPurity

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option linter.style.longLine false

noncomputable section
set_option maxHeartbeats 1600000
open Matrix
open scoped BigOperators Kronecker ComplexOrder
open D5.S3.QuantumChannels.CoPRelativeQuantumnessRefutation (IsDensity)
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.Quantum.QuantumChannels.IptPptSquaredEquivalence (IsSeparable)
open D5.S3.Quantum.Dynamics.KickedIsingNegativityRefutation (partialTranspose)

namespace D5.S3.Quantum.Information.SeparableWassersteinComparisonRefutation

def quantumCouplings {d : ℕ} (ρ σ : Matrix (Fin d) (Fin d) ℂ) :=
  D5.S3.Quantum.QuantumChannels.QubitWassersteinCouplings.couplings ρ σ

def separableCouplings {d : ℕ} (ρ σ : Matrix (Fin d) (Fin d) ℂ) :
    Set (Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :=
  {γ | (γ.PosSemidef ∧ γ.trace = 1) ∧ IsSeparable γ ∧
    partialTraceLeft γ = ρ ∧ partialTraceRight γ = σ}

def quantumCostOperator {d N : ℕ} (H : Fin N → Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  (1 / 2 : ℂ) • ∑ n, ((H n).transpose ⊗ₖ 1 - 1 ⊗ₖ H n) ^ 2

def separableCostOperator {d N : ℕ} (H : Fin N → Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  (1 / 2 : ℂ) • ∑ n, (H n ⊗ₖ 1 - 1 ⊗ₖ H n) ^ 2

def quantumCost {d N : ℕ} (H : Fin N → Matrix (Fin d) (Fin d) ℂ)
    (γ : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) : ℝ :=
  (quantumCostOperator H * γ).trace.re

def separableCost {d N : ℕ} (H : Fin N → Matrix (Fin d) (Fin d) ℂ)
    (γ : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) : ℝ :=
  (separableCostOperator H * γ).trace.re

def quantumSquared {d N : ℕ} (H : Fin N → Matrix (Fin d) (Fin d) ℂ)
    (ρ σ : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  sInf (quantumCost H '' quantumCouplings ρ σ)

def separableSquared {d N : ℕ} (H : Fin N → Matrix (Fin d) (Fin d) ℂ)
    (ρ σ : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  sInf (separableCost H '' separableCouplings ρ σ)

def modifiedQuantumSquared {d N : ℕ} (H : Fin N → Matrix (Fin d) (Fin d) ℂ)
    (ρ σ : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  quantumSquared H ρ σ - (quantumSquared H ρ ρ + quantumSquared H σ σ) / 2

def modifiedSeparableSquared {d N : ℕ} (H : Fin N → Matrix (Fin d) (Fin d) ℂ)
    (ρ σ : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  separableSquared H ρ σ - (separableSquared H ρ ρ + separableSquared H σ σ) / 2

def claim : Prop :=
  ∀ (d N : ℕ) (H : Fin N → Matrix (Fin d) (Fin d) ℂ),
    (∀ n, (H n).IsHermitian) → ∀ ρ σ, IsDensity ρ → IsDensity σ →
      modifiedSeparableSquared H ρ σ ≤ modifiedQuantumSquared H ρ σ

private abbrev L := Fin 4
private abbrev J := L × L
private abbrev M := Matrix L L ℂ
private abbrev K := Matrix J J ℂ

private def hOne : M := !![0,2,0,0; 2,0,0,0; 0,0,0,1; 0,0,1,0]
private def hTwo : M := diagonal ![1,-1,2,-2]
private def swapBlocks : M := !![0,0,1,0; 0,0,0,1; 1,0,0,0; 0,1,0,0]
private def observables : Fin 3 → M := ![hOne, hTwo, (1/4 : ℂ) • swapBlocks]
private def rho : M := diagonal ![3/8,3/8,1/8,1/8]
private def sigma : M := diagonal ![1/8,1/8,3/8,3/8]

private theorem observables_hermitian : ∀ n, (observables n).IsHermitian := by
  sorry

private theorem rho_density : IsDensity rho := by
  sorry

private theorem sigma_density : IsDensity sigma := by
  sorry

private def gram (v : J → ℂ) : K := vecMulVec v (star v)
private def ket (i j : L) : J → ℂ := Pi.single (i,j) 1
private def aVec : J → ℂ := ket 0 0 - ket 1 1
private def bVec : Fin 4 → J → ℂ :=
  ![ket 0 1 - ket 1 0, ket 0 3 - ket 1 2,
    ket 2 1 - ket 3 0, ket 2 3 - ket 3 2]
private def aWitness : K :=
  (3 : ℂ) • gram aVec + (4 : ℂ) • gram (bVec 0) +
  (2 : ℂ) • gram (bVec 1) + (2 : ℂ) • gram (bVec 2) +
  (6 : ℂ) • gram (ket 2 3) + (6 : ℂ) • gram (ket 3 2) + gram (bVec 3)
private def bWeights : Fin 4 → ℝ := ![1,2,2,1]
private def bWitness : K := ∑ i, (bWeights i : ℂ) • gram (bVec i)
private def crossProjection : K := diagonal (fun p => if p.1.val / 2 = p.2.val / 2
  then 0 else 1)
private def baseCost : K := (5 : ℂ) • 1 - hOne ⊗ₖ hOne - hTwo ⊗ₖ hTwo
private def thirdCost : K :=
  (1/16 : ℂ) • (1 - swapBlocks ⊗ₖ swapBlocks)

private theorem separable_ppt {γ : K} (hγ : IsSeparable γ) :
    (partialTranspose γ).PosSemidef := by
  sorry

private theorem aWitness_psd : aWitness.PosSemidef := by
  sorry

private theorem decomposable_identity :
    baseCost - 1 - (2 : ℂ) • crossProjection =
      aWitness + partialTranspose bWitness := by
  sorry

private theorem bWitness_pair_nonneg {γ : K}
    (hγ : (partialTranspose γ).PosSemidef) :
    0 ≤ (partialTranspose bWitness * γ).trace.re := by
  sorry

set_option maxHeartbeats 4000000 in
private theorem cost_matrices :
    separableCostOperator observables = baseCost + thirdCost ∧
      quantumCostOperator observables = baseCost + thirdCost := by
  sorry

private theorem thirdCost_psd : thirdCost.PosSemidef := by
  sorry

private theorem totalCost_psd : (separableCostOperator observables).PosSemidef := by
  sorry

private theorem cross_mass {γ : K} (hγ : γ ∈ separableCouplings rho sigma) :
    1/2 ≤ (crossProjection * γ).trace.re := by
  sorry

private theorem separable_cross_lower {γ : K}
    (hγ : γ ∈ separableCouplings rho sigma) : 2 ≤ separableCost observables γ := by
  sorry

private theorem fixed_quantum_nonneg {γ : K} (hγ : γ.PosSemidef) :
    0 ≤ quantumCost observables γ := by
  sorry

private theorem fixed_separable_nonneg {γ : K} (hγ : γ.PosSemidef) :
    0 ≤ separableCost observables γ :=
  RHLinalg.trace_mul_nonneg_of_posSemidef totalCost_psd hγ

private theorem quantum_self_nonneg {ρ : M} (hρ : IsDensity ρ) :
    0 ≤ quantumSquared observables ρ ρ := by
  sorry

private def localVectors : Fin 4 → L → ℂ :=
  ![![1,1,0,0], ![1,-1,0,0], ![0,0,1,0], ![0,0,0,1]]
private def localScales : Fin 4 → ℝ := ![1/2,1/2,1,1]
private def localStates (i : Fin 4) : M :=
  (localScales i : ℂ) • vecMulVec (localVectors i) (star (localVectors i))
private def selfWeights (t : Bool) : Fin 4 → ℝ :=
  if t then ![1/8,1/8,3/8,3/8] else ![3/8,3/8,1/8,1/8]
private def selfCoupling (t : Bool) : K :=
  ∑ i, (selfWeights t i : ℂ) • (localStates i ⊗ₖ localStates i)
private def selfState (t : Bool) : M := if t then sigma else rho

private theorem localStates_density (i : Fin 4) : IsDensity (localStates i) := by
  sorry

private theorem selfCoupling_separable (t : Bool) : IsSeparable (selfCoupling t) := by
  sorry

private theorem selfCoupling_psd (t : Bool) : (selfCoupling t).PosSemidef := by
  sorry

private theorem selfCoupling_marginals (t : Bool) :
    partialTraceLeft (selfCoupling t) = selfState t ∧
      partialTraceRight (selfCoupling t) = selfState t := by
  sorry

private theorem selfCoupling_mem (t : Bool) :
    selfCoupling t ∈ separableCouplings (selfState t) (selfState t) := by
  sorry

private def bellMatrices : Fin 3 → M :=
  ![!![1,0,0,0; 0,1,0,0; 0,0,0,0; 0,0,0,0],
    !![0,0,0,0; 0,0,0,0; 1,0,0,0; 0,1,0,0],
    !![0,0,0,0; 0,0,0,0; 0,0,1,0; 0,0,0,1]]
private def bellWeights : Fin 3 → ℝ := ![1/8,1/4,1/8]
private def bellCoupling : K := ∑ i, (bellWeights i : ℂ) •
  D5.S3.Quantum.QuantumChannels.QubitWassersteinCouplings.pureCoupling (bellMatrices i)

private theorem bellCoupling_psd : bellCoupling.PosSemidef := by
  sorry

private theorem bellCoupling_marginals :
    partialTraceLeft bellCoupling = rho.transpose ∧ partialTraceRight bellCoupling = sigma := by
  sorry

private theorem bellCoupling_mem : bellCoupling ∈ quantumCouplings rho sigma := by
  sorry

private theorem selfCoupling_cost (t : Bool) :
    separableCost observables (selfCoupling t) = 17/16 := by
  sorry

private theorem bellCoupling_cost : quantumCost observables bellCoupling = 9/16 := by
  sorry

private theorem self_inf_upper (t : Bool) :
    separableSquared observables (selfState t) (selfState t) ≤ 17/16 := by
  sorry

private theorem quantum_inf_upper : quantumSquared observables rho sigma ≤ 9/16 := by
  sorry

private theorem separable_inf_lower : 2 ≤ separableSquared observables rho sigma := by
  sorry

theorem result : ¬ claim := by
  sorry

end D5.S3.Quantum.Information.SeparableWassersteinComparisonRefutation
