/- GID: D5/S3/Quantum/Information/SeparableWassersteinComparisonRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Information/SeparableWassersteinComparisonRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Information/SeparableWassersteinComparisonRefutation.claim; result=D5/S3/Quantum/Information/SeparableWassersteinComparisonRefutation.result; claim=D5/S3/Quantum/Information/SeparableWassersteinComparisonRefutation.claim
   digest: Modified separable quantum transport can exceed unrestricted quantum transport. -/

import D5.S3.Quantum.QuantumChannels.QubitWassersteinCouplings
import D5.S3.Quantum.Matrix.PartialTransposeTrace
import D5.S3.Quantum.QuantumChannels.LogNegativityCapacityResourceDependence
import D5.S3.QuantumContext.RankOfContextualityNonPowerTwo

/-! Modified transport costs for a four-dimensional pair of density matrices. -/

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
open D5.S3.Quantum.QuantumChannels.QubitWassersteinCouplings (couplings)
open D5.S3.Quantum.PureState.PureStateHandshake (rankOneDensity)
open D5.S3.Quantum.QuantumChannels.LogNegativityCapacityResourceDependence.Conditional
  (separable_ppt)
open D5.S3.QuantumContext.RankOfContextualityNonPowerTwo.Matrices (obs XITable obs_herm_sq)

namespace D5.S3.Quantum.Information.SeparableWassersteinComparisonRefutation

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
  sInf (quantumCost H '' couplings ρ σ)

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

private def hOne : Matrix (Fin 4) (Fin 4) ℂ := !![0,2,0,0; 2,0,0,0; 0,0,0,1; 0,0,1,0]
private def hTwo : Matrix (Fin 4) (Fin 4) ℂ := diagonal ![1,-1,2,-2]
private def observables : Fin 3 → Matrix (Fin 4) (Fin 4) ℂ := ![hOne, hTwo, (1/4 : ℂ) • (obs 4)]
private def rho : Matrix (Fin 4) (Fin 4) ℂ := diagonal ![3/8,3/8,1/8,1/8]
private def sigma : Matrix (Fin 4) (Fin 4) ℂ := diagonal ![1/8,1/8,3/8,3/8]

private theorem observables_hermitian : ∀ n, (observables n).IsHermitian := by
  intro n
  fin_cases n
  · apply Matrix.IsHermitian.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      norm_num [observables, hOne, Matrix.conjTranspose_apply]
  · apply Matrix.IsHermitian.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      norm_num [observables, hTwo, Matrix.conjTranspose_apply, Matrix.diagonal]
  · exact (obs_herm_sq 4).1.smul (by norm_num : star (1/4 : ℂ) = 1/4)

private theorem rho_density : IsDensity rho := by
  constructor
  · apply Matrix.PosSemidef.diagonal
    intro i
    fin_cases i <;> norm_num [Complex.le_def]
  · norm_num [rho, Matrix.trace, Fin.sum_univ_succ]

private theorem sigma_density : IsDensity sigma := by
  constructor
  · apply Matrix.PosSemidef.diagonal
    intro i
    fin_cases i <;> norm_num [Complex.le_def]
  · norm_num [sigma, Matrix.trace, Fin.sum_univ_succ]

private def aVec : (Fin 4 × Fin 4) → ℂ := Pi.single (0, 0) 1 - Pi.single (1, 1) 1
private def bVec : Fin 4 → (Fin 4 × Fin 4) → ℂ :=
  ![Pi.single (0, 1) 1 - Pi.single (1, 0) 1, Pi.single (0, 3) 1 - Pi.single (1, 2) 1,
    Pi.single (2, 1) 1 - Pi.single (3, 0) 1, Pi.single (2, 3) 1 - Pi.single (3, 2) 1]
private def aWitness : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℂ :=
  (3 : ℂ) • rankOneDensity aVec + (4 : ℂ) • rankOneDensity (bVec 0) +
  (2 : ℂ) • rankOneDensity (bVec 1) + (2 : ℂ) • rankOneDensity (bVec 2) +
  (6 : ℂ) • rankOneDensity (Pi.single (2, 3) 1) + (6 : ℂ) • rankOneDensity (Pi.single (3, 2) 1) + rankOneDensity (bVec 3)
private def bWeights : Fin 4 → ℝ := ![1,2,2,1]
private def bWitness : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℂ := ∑ i, (bWeights i : ℂ) • rankOneDensity (bVec i)
private def crossProjection : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℂ := diagonal (fun p => if p.1.val / 2 = p.2.val / 2
  then 0 else 1)
private def baseCost : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℂ := (5 : ℂ) • 1 - hOne ⊗ₖ hOne - hTwo ⊗ₖ hTwo
private def thirdCost : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℂ :=
  (1/16 : ℂ) • (1 - (obs 4) ⊗ₖ (obs 4))

private theorem aWitness_psd : aWitness.PosSemidef := by
  unfold aWitness
  repeat' apply Matrix.PosSemidef.add
  all_goals first
    | exact Matrix.posSemidef_vecMulVec_self_star _
    | exact (Matrix.posSemidef_vecMulVec_self_star _).smul (by norm_num)

private theorem decomposable_identity :
    baseCost - 1 - (2 : ℂ) • crossProjection =
      aWitness + partialTranspose bWitness := by
  ext ⟨i,j⟩ ⟨k,l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num [baseCost, aWitness, bWitness, bWeights, crossProjection,
      partialTranspose, rankOneDensity, aVec, bVec, hOne, hTwo,
      Matrix.vecMulVec_apply, Pi.single_apply, Fin.sum_univ_succ, Matrix.one_apply]

private theorem bWitness_pair_nonneg {γ : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℂ}
    (hγ : (partialTranspose γ).PosSemidef) :
    0 ≤ (partialTranspose bWitness * γ).trace.re := by
  have hterm (i : Fin 4) : 0 ≤ (partialTranspose (rankOneDensity (bVec i)) * γ).trace.re := by
    rw [Matrix.trace_mul_comm]
    change 0 ≤ (γ * partialTranspose (vecMulVec (bVec i) (star (bVec i)))).trace.re
    rw [← D5.S3.Quantum.Matrix.PartialTransposeTrace.partial_transpose_trace_duality
      γ (bVec i)]
    exact (hγ.dotProduct_mulVec_nonneg _).1
  have he : partialTranspose bWitness =
      ∑ i, (bWeights i : ℂ) • partialTranspose (rankOneDensity (bVec i)) := by
    ext p q
    simp [bWitness, partialTranspose, Matrix.sum_apply]
  rw [he, Matrix.sum_mul, Matrix.trace_sum, Complex.re_sum]
  apply Finset.sum_nonneg
  intro i _
  simpa only [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul,
    Complex.re_ofReal_mul] using
    mul_nonneg (show 0 ≤ bWeights i by fin_cases i <;> norm_num [bWeights]) (hterm i)

set_option maxHeartbeats 4000000 in
private theorem cost_matrices :
    separableCostOperator observables = baseCost + thirdCost ∧
      quantumCostOperator observables = baseCost + thirdCost := by
  have ht : ∀ n, (observables n).transpose = observables n := by
    intro n
    ext i j
    fin_cases n <;> fin_cases i <;> fin_cases j <;>
      norm_num [observables, hOne, hTwo, XITable, Matrix.transpose_apply]
  have hq : quantumCostOperator observables = separableCostOperator observables := by
    simp only [quantumCostOperator, separableCostOperator, ht]
  have hs : separableCostOperator observables = baseCost + thirdCost := by
    ext ⟨i,j⟩ ⟨k,l⟩
    fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
      norm_num [separableCostOperator, observables, baseCost, thirdCost,
        hOne, hTwo, XITable, pow_two, Matrix.mul_apply, Matrix.smul_apply,
        smul_eq_mul, Matrix.one_apply, Fintype.sum_prod_type, Fin.sum_univ_succ,
        Finset.filter_singleton]
  exact ⟨hs, hq.trans hs⟩

private theorem thirdCost_psd : thirdCost.PosSemidef := by
  have he : thirdCost = (1/32 : ℂ) •
      ((1 - (obs 4) ⊗ₖ (obs 4)) *
        (1 - (obs 4) ⊗ₖ (obs 4)).conjTranspose) := by
    ext ⟨i,j⟩ ⟨k,l⟩
    fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
      norm_num [thirdCost, XITable, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Matrix.one_apply, Fintype.sum_prod_type, Fin.sum_univ_succ, Finset.filter_singleton]
  rw [he]
  exact (Matrix.posSemidef_self_mul_conjTranspose _).smul (by norm_num [Complex.le_def])

private theorem totalCost_psd : (separableCostOperator observables).PosSemidef := by
  apply Matrix.PosSemidef.smul _ (by norm_num [Complex.le_def] : (0 : ℂ) ≤ 1/2)
  apply Matrix.posSemidef_sum
  intro n _
  let B : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℂ := observables n ⊗ₖ 1 - 1 ⊗ₖ observables n
  have hB : B.IsHermitian :=
    (isHermitian_kronecker (observables_hermitian n) Matrix.isHermitian_one).sub
      (isHermitian_kronecker Matrix.isHermitian_one (observables_hermitian n))
  change (B ^ 2).PosSemidef
  simpa only [pow_two, hB.eq] using Matrix.posSemidef_conjTranspose_mul_self B

private theorem cross_mass {γ : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℂ} (hγ : γ ∈ separableCouplings rho sigma) :
    1/2 ≤ (crossProjection * γ).trace.re := by
  have he : (crossProjection * γ).trace.re =
      ((partialTraceLeft γ) 0 0 + (partialTraceLeft γ) 1 1).re -
      ((partialTraceRight γ) 0 0 + (partialTraceRight γ) 1 1).re +
      2 * (γ (0,2) (0,2) + γ (0,3) (0,3) +
        γ (1,2) (1,2) + γ (1,3) (1,3)).re := by
    simp [crossProjection, Matrix.trace, Matrix.diagonal_mul,
      partialTraceLeft, partialTraceRight, Fintype.sum_prod_type, Fin.sum_univ_succ,
      Complex.add_re]
    ring
  rw [hγ.2.2.1, hγ.2.2.2] at he
  norm_num [rho, sigma] at he
  have h02 := (hγ.1.1.diag_nonneg (i := (0,2))).1
  have h03 := (hγ.1.1.diag_nonneg (i := (0,3))).1
  have h12 := (hγ.1.1.diag_nonneg (i := (1,2))).1
  have h13 := (hγ.1.1.diag_nonneg (i := (1,3))).1
  simp only [Complex.zero_re] at h02 h03 h12 h13
  linarith

private theorem separable_cross_lower {γ : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℂ}
    (hγ : γ ∈ separableCouplings rho sigma) : 2 ≤ separableCost observables γ := by
  have ha := RHLinalg.trace_mul_nonneg_of_posSemidef aWitness_psd hγ.1.1
  have hb := bWitness_pair_nonneg (separable_ppt γ hγ.2.1)
  have ht := RHLinalg.trace_mul_nonneg_of_posSemidef thirdCost_psd hγ.1.1
  change 0 ≤ (aWitness * γ).trace.re at ha
  change 0 ≤ (thirdCost * γ).trace.re at ht
  have hm := cross_mass hγ
  have he := congrArg (fun X : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℂ => (X * γ).trace.re) decomposable_identity
  simp only [sub_mul, add_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.trace_sub,
    Matrix.trace_add, Matrix.trace_smul, smul_eq_mul, Complex.sub_re, Complex.add_re,
    Complex.mul_re] at he
  rw [hγ.1.2] at he
  change 2 ≤ (separableCostOperator observables * γ).trace.re
  rw [cost_matrices.1, add_mul, Matrix.trace_add, Complex.add_re]
  norm_num at he
  linarith

private theorem quantum_self_nonneg {ρ : Matrix (Fin 4) (Fin 4) ℂ} (hρ : IsDensity ρ) :
    0 ≤ quantumSquared observables ρ ρ := by
  apply le_csInf ((D5.S3.Quantum.QuantumChannels.QubitWassersteinCouplings.couplings_nonempty
    hρ hρ).image _)
  rintro _ ⟨γ,hγ,rfl⟩
  unfold quantumCost
  rw [cost_matrices.2, ← cost_matrices.1]
  exact RHLinalg.trace_mul_nonneg_of_posSemidef totalCost_psd hγ.1.1

private def localVectors : Fin 4 → Fin 4 → ℂ :=
  ![![1,1,0,0], ![1,-1,0,0], ![0,0,1,0], ![0,0,0,1]]
private def localScales : Fin 4 → ℝ := ![1/2,1/2,1,1]
private def localStates (i : Fin 4) : Matrix (Fin 4) (Fin 4) ℂ :=
  (localScales i : ℂ) • rankOneDensity (localVectors i)
private def selfWeights (t : Bool) : Fin 4 → ℝ :=
  if t then ![1/8,1/8,3/8,3/8] else ![3/8,3/8,1/8,1/8]
private def selfCoupling (t : Bool) : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℂ :=
  ∑ i, (selfWeights t i : ℂ) • (localStates i ⊗ₖ localStates i)
private def selfState (t : Bool) : Matrix (Fin 4) (Fin 4) ℂ := if t then sigma else rho

private theorem localStates_density (i : Fin 4) : IsDensity (localStates i) := by
  constructor
  · exact (Matrix.posSemidef_vecMulVec_self_star _).smul
      (Complex.zero_le_real.mpr (by fin_cases i <;> norm_num [localScales]))
  · rw [localStates, Matrix.trace_smul, rankOneDensity, Matrix.trace_vecMulVec]
    fin_cases i <;> norm_num [localScales, localVectors, dotProduct,
      Pi.star_apply, Fin.sum_univ_succ]

private theorem selfCoupling_separable (t : Bool) : IsSeparable (selfCoupling t) := by
  refine ⟨4, selfWeights t, localStates, localStates, ?_, ?_, ?_, rfl⟩
  · intro i
    cases t <;> fin_cases i <;> norm_num [selfWeights]
  · cases t <;> norm_num [selfWeights, Fin.sum_univ_succ]
  · intro i
    exact ⟨localStates_density i, localStates_density i⟩

private theorem selfCoupling_psd (t : Bool) : (selfCoupling t).PosSemidef := by
  apply Matrix.posSemidef_sum
  intro i _
  exact ((localStates_density i).1.kronecker (localStates_density i).1).smul
    (Complex.zero_le_real.mpr (by cases t <;> fin_cases i <;> norm_num [selfWeights]))

private theorem selfCoupling_marginals (t : Bool) :
    partialTraceLeft (selfCoupling t) = selfState t ∧
      partialTraceRight (selfCoupling t) = selfState t := by
  constructor <;> ext i j <;> cases t <;> fin_cases i <;> fin_cases j <;>
    norm_num [selfCoupling, selfWeights, selfState, localStates, localScales,
      localVectors, rho, sigma, partialTraceLeft, partialTraceRight, rankOneDensity, Matrix.vecMulVec_apply,
      Pi.star_apply, Matrix.sum_apply, Fin.sum_univ_succ]

private theorem selfCoupling_mem (t : Bool) :
    selfCoupling t ∈ separableCouplings (selfState t) (selfState t) := by
  refine ⟨⟨selfCoupling_psd t, ?_⟩, selfCoupling_separable t,
    (selfCoupling_marginals t).1, (selfCoupling_marginals t).2⟩
  rw [← trace_partialTraceLeft, (selfCoupling_marginals t).1]
  cases t
  · exact rho_density.2
  · exact sigma_density.2

private def bellMatrices : Fin 3 → Matrix (Fin 4) (Fin 4) ℂ :=
  ![!![1,0,0,0; 0,1,0,0; 0,0,0,0; 0,0,0,0],
    !![0,0,0,0; 0,0,0,0; 1,0,0,0; 0,1,0,0],
    !![0,0,0,0; 0,0,0,0; 0,0,1,0; 0,0,0,1]]
private def bellWeights : Fin 3 → ℝ := ![1/8,1/4,1/8]
private def bellCoupling : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℂ := ∑ i, (bellWeights i : ℂ) •
  D5.S3.Quantum.QuantumChannels.QubitWassersteinCouplings.pureCoupling (bellMatrices i)

private theorem bellCoupling_psd : bellCoupling.PosSemidef := by
  apply Matrix.posSemidef_sum
  intro i _
  exact (D5.S3.Quantum.QuantumChannels.QubitWassersteinCouplings.pureCoupling_psd _).smul
    (Complex.zero_le_real.mpr (by fin_cases i <;> norm_num [bellWeights]))

private theorem bellCoupling_marginals :
    partialTraceLeft bellCoupling = rho.transpose ∧ partialTraceRight bellCoupling = sigma := by
  have hl : partialTraceLeft bellCoupling = ∑ i, (bellWeights i : ℂ) •
      partialTraceLeft
        (D5.S3.Quantum.QuantumChannels.QubitWassersteinCouplings.pureCoupling
          (bellMatrices i)) := by
    ext i j
    simp only [bellCoupling, partialTraceLeft, Matrix.sum_apply, Matrix.smul_apply,
      smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
  have hr : partialTraceRight bellCoupling = ∑ i, (bellWeights i : ℂ) •
      partialTraceRight
        (D5.S3.Quantum.QuantumChannels.QubitWassersteinCouplings.pureCoupling
          (bellMatrices i)) := by
    ext i j
    simp only [bellCoupling, partialTraceRight, Matrix.sum_apply, Matrix.smul_apply,
      smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
  rw [hl, hr]
  simp_rw [D5.S3.Quantum.QuantumChannels.QubitWassersteinCouplings.ptrace1_pure,
    D5.S3.Quantum.QuantumChannels.QubitWassersteinCouplings.ptrace2_pure]
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [bellMatrices, bellWeights, rho, sigma, Matrix.conjTranspose_apply,
      Matrix.mul_apply, Matrix.sum_apply, Fin.sum_univ_succ]

private theorem bellCoupling_mem : bellCoupling ∈ couplings rho sigma := by
  refine ⟨⟨bellCoupling_psd, ?_⟩, bellCoupling_marginals.2, bellCoupling_marginals.1⟩
  rw [← trace_partialTraceLeft, bellCoupling_marginals.1, Matrix.trace_transpose]
  exact rho_density.2

private theorem selfCoupling_cost (t : Bool) :
    separableCost observables (selfCoupling t) = 17/16 := by
  unfold separableCost
  rw [cost_matrices.1]
  simp only [baseCost, thirdCost, selfCoupling, Matrix.trace, Matrix.diag_apply,
    Matrix.mul_apply, Matrix.sum_apply, Matrix.add_apply, Matrix.sub_apply,
    Matrix.smul_apply, Matrix.kroneckerMap_apply, localStates, rankOneDensity, Matrix.vecMulVec_apply,
    Pi.star_apply, smul_eq_mul]
  cases t <;>
    norm_num [selfWeights, localScales, localVectors, hOne, hTwo, XITable, Matrix.one_apply,
      Fintype.sum_prod_type, Fin.sum_univ_succ]

private theorem bellCoupling_cost : quantumCost observables bellCoupling = 9/16 := by
  unfold quantumCost
  rw [cost_matrices.2]
  norm_num [baseCost, thirdCost, bellCoupling, bellMatrices, bellWeights,
    D5.S3.Quantum.QuantumChannels.QubitWassersteinCouplings.pureCoupling,
    D5.S3.Quantum.PureState.PureStateHandshake.rankOneDensity,
    hOne, hTwo, XITable, Matrix.trace, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Matrix.vecMulVec_apply,
    Pi.star_apply, Matrix.one_apply, Matrix.sum_apply, Function.uncurry,
    Fintype.sum_prod_type, Fin.sum_univ_succ]

private theorem self_inf_upper (t : Bool) :
    separableSquared observables (selfState t) (selfState t) ≤ 17/16 := by
  rw [← selfCoupling_cost t]
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro _ ⟨γ,hγ,rfl⟩
    exact RHLinalg.trace_mul_nonneg_of_posSemidef totalCost_psd hγ.1.1
  · exact ⟨_, selfCoupling_mem t, rfl⟩

private theorem quantum_inf_upper : quantumSquared observables rho sigma ≤ 9/16 := by
  rw [← bellCoupling_cost]
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro _ ⟨γ,hγ,rfl⟩
    unfold quantumCost
    rw [cost_matrices.2, ← cost_matrices.1]
    exact RHLinalg.trace_mul_nonneg_of_posSemidef totalCost_psd hγ.1.1
  · exact ⟨_, bellCoupling_mem, rfl⟩

private theorem separable_inf_lower : 2 ≤ separableSquared observables rho sigma := by
  have hproduct : sigma ⊗ₖ rho ∈ separableCouplings rho sigma := by
    refine ⟨⟨sigma_density.1.kronecker rho_density.1, ?_⟩, ?_, ?_, ?_⟩
    · rw [Matrix.trace_kronecker, rho_density.2, sigma_density.2, mul_one]
    · refine ⟨1, fun _ => 1, fun _ => sigma, fun _ => rho, by simp, by simp,
        fun _ => ⟨sigma_density, rho_density⟩, ?_⟩
      simp
    · change partialTraceLeft (Matrix.kronecker sigma rho) = rho
      rw [partialTraceLeft_kronecker, sigma_density.2, one_smul]
    · change partialTraceRight (Matrix.kronecker sigma rho) = sigma
      rw [partialTraceRight_kronecker, rho_density.2, one_smul]
  apply le_csInf (Set.Nonempty.image _ ⟨_, hproduct⟩)
  rintro _ ⟨γ,hγ,rfl⟩
  exact separable_cross_lower hγ

theorem result : ¬ claim := by
  intro h
  have hc := h 4 3 observables observables_hermitian rho sigma rho_density sigma_density
  have hs := separable_inf_lower
  have hr := self_inf_upper false
  have ht := self_inf_upper true
  have hq := quantum_inf_upper
  have hqr := quantum_self_nonneg rho_density
  have hqs := quantum_self_nonneg sigma_density
  change separableSquared observables rho rho ≤ 17/16 at hr
  change separableSquared observables sigma sigma ≤ 17/16 at ht
  unfold modifiedSeparableSquared modifiedQuantumSquared at hc
  linarith

#check claim
#check result
#print axioms result

end D5.S3.Quantum.Information.SeparableWassersteinComparisonRefutation
