/- GID: D5/S3/Quantum/Decoherence/FourLevelBathEntropyBudget
   generality: I
   mirror-B: D5/B/S3/Quantum/Decoherence/FourLevelBathEntropyBudget
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact marginal entropy and information of a qutrit coupled to a purified Gibbs bath. -/

import D5.S3.Quantum.Decoherence.FourLevelBathObserverFourier
import D5.S3.Quantum.Decoherence.LabelResetSupport
import D5.S3.Quantum.Information.CorrelatedGibbsEnergyIdentity
import D5.S3.Quantum.Information.StrongSubadditivity
import D5.S3.Quantum.Measurement.Auric.CoordinatePinchingEntropy
import Batteries.Tactic.OpenPrivate

/-!
# Entropy budgets for the purified four-level Gibbs pinching

The qutrit has zero Hamiltonian and the four bath energies are distinct.
For finite real inverse temperature, fix their Gibbs law. Prepare the qutrit
independently of the coherent Gibbs purification on BR and act with a phase
unitary on SB tensored with the identity on R. The weighted phase columns
are orthonormal. The input is any positive semidefinite trace-one qutrit,
including singular matrices and matrices with off-diagonal entries.
The label decoders use access to B and R with phase-sensitive readout.
Entropies use natural logs and allow zero weights.
-/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Quantum.Decoherence.FourLevelBathEntropyBudget

open Matrix _root_.D5.S3.Quantum.Decoherence.FourLevelBathPhysical
open _root_.D5.S3.Quantum.Decoherence.FourLevelBathObserver
open private purification_normalized liftToReference_isometry recordEmbedding_entry
  recordEmbedding_isometry record_orthonormal conditionalRecord_state
  from D5.S3.Quantum.Decoherence.FourLevelBathObserver
open scoped BigOperators Kronecker ComplexOrder CStarAlgebra MatrixOrder
open GibbsBathBandwidth (diagonalReal gibbsWeight gibbsWeight_pos sum_gibbsWeight)
open D5.S3.Entropy.MaxEntropy (shannonEntropy)
open D5.S3.QuantumChannels.CoolingMapThermalOperationRefutation (IsEnergyConserving)
open D5.S3.QuantumChannels.ThermalOperationDegeneracyRefutation (operation)
open D5.S3.Quantum.Decoherence.ProjectedUnistochasticDynamics (basisProjector projectiveReadout)
open D5.S3.Quantum.Divergence.VonNeumannEntropyPinching (vonNeumannEntropy)
open D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity
  (basisPinchingState cfc_diagonal unitaryConjugateState)
open D5.S3.Quantum.Foundation.FiniteDensityPurification (toMState)
open D5.S3.Quantum.Foundation.FiniteStateChannel (DensityState)
open D5.S3.Quantum.Information.CoherentCopyCorrelationTax
  (coherentCopyState copyIsometry copyMatrix
    marginalLeft_coherentCopyState marginalRight_coherentCopyState
    vonNeumannEntropy_coherentCopyState)
open D5.S3.Quantum.Information.CorrelatedGibbsEnergyIdentity (von_neumann_entropy_unitary)
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.Quantum.Information.OrthogonalRecordEntropy
  (entropy_eq_trace_cfc entropy_pointerState entropy_recordState marginalLeft_mixture
    marginalRight_mixture mixtureState orthogonal_mixture_entropy
    orthogonal_record_trace_gives_sbs_consensus pointerState pointerState_orthogonal realTrace)
open D5.S3.Quantum.Information.StrongSubadditivity
  (entropy_toMState relabelState toMState_marginalLeft toMState_marginalRight)
open D5.S3.Quantum.Measurement.Auric.CoordinatePinchingEntropy (pure_entropy)
open D5.S3.Quantum.PureState.PureStateHandshake (rankOneDensity)

local notation "S" => vonNeumannEntropy
local notation "H" => shannonEntropy

private abbrev mat {n : Type*} [Fintype n] [DecidableEq n]
    (ρ : DensityState n) : Matrix n n ℂ := CStarMatrix.ofMatrix.symm ρ.1

/-- The qutrit's coordinate Born law, including zero diagonal entries. -/
def populations (ρ : DensityState System) (i : System) : ℝ :=
  (inputMatrix ρ i i).re

theorem populations_nonneg (ρ : DensityState System) (i : System) :
    0 ≤ populations ρ i :=
  (Complex.nonneg_iff.mp ((density_posSemidef ρ).diag_nonneg (i := i))).1

private theorem entry_eq_populations (ρ : DensityState System) (i : System) :
    inputMatrix ρ i i = (populations ρ i : ℂ) := by
  have h : 0 ≤ inputMatrix ρ i i := (density_posSemidef ρ).diag_nonneg
  apply Complex.ext
  · rfl
  · simpa using (Complex.nonneg_iff.mp h).2.symm

theorem sum_populations (ρ : DensityState System) : ∑ i, populations ρ i = 1 := by
  have htrace : Matrix.trace (inputMatrix ρ) = 1 := ρ.trace_eq_one
  have h := congrArg Complex.re htrace
  simpa only [Matrix.trace, Matrix.diag_apply, Complex.re_sum, Complex.one_re, populations]
    using h

private theorem entropy_of_diagonal {n : Type*} [Fintype n] [DecidableEq n]
    (ρ : DensityState n) (a : n → ℝ) (ha : mat ρ = diagonalReal a) :
    S ρ = H a := by
  let : ContinuousFunctionalCalculus ℝ (CStarMatrix n n ℂ) IsSelfAdjoint :=
    IsSelfAdjoint.instContinuousFunctionalCalculus
  have hmap : CStarMatrix.ofMatrix (cfc Real.negMulLog (mat ρ)) =
      cfc Real.negMulLog ρ.1 :=
    StarAlgHomClass.map_cfc CStarMatrix.ofMatrixStarAlgEquiv Real.negMulLog (mat ρ)
      ((mat ρ).finite_real_spectrum.continuousOn _) CStarMatrix.ofMatrixL.continuous
      (density_posSemidef ρ).isHermitian (by exact (density_posSemidef ρ).isHermitian)
  calc
    S ρ = realTrace (cfc Real.negMulLog ρ.1) := entropy_eq_trace_cfc ρ
    _ = H a := by
      rw [← hmap]
      change (Matrix.trace (cfc Real.negMulLog (mat ρ))).re = H a
      rw [ha, diagonalReal, cfc_diagonal, Matrix.trace_diagonal, Complex.re_sum, shannonEntropy]
      simp only [Complex.ofReal_re]

theorem pinching_matrix (ρ : DensityState System) :
    projectiveReadout (inputMatrix ρ) = diagonalReal (populations ρ) := by
  unfold projectiveReadout diagonalReal
  exact congrArg Matrix.diagonal (funext (entry_eq_populations ρ))

private theorem pinching_entropy (ρ : DensityState System) :
    S (basisPinchingState ρ) = H (populations ρ) :=
  entropy_of_diagonal (basisPinchingState ρ) (populations ρ) (pinching_matrix ρ)

/-- The density of the original mixed bath, in the physical bath coordinates. -/
def bathState (p : Bath → ℝ) (hp : ∀ b, 0 ≤ p b) (hsum : ∑ b, p b = 1) :
    DensityState Bath :=
  marginalRight (purifiedBath p hp hsum)

theorem bathState_matrix (p : Bath → ℝ) (hp : ∀ b, 0 ≤ p b) (hsum : ∑ b, p b = 1) :
    mat (bathState p hp hsum) = diagonalReal p :=
  (purifiedBath_marginals p hp hsum).1

private theorem referenceLift_mem_unitary (U : Joint)
    (hU : U ∈ Matrix.unitaryGroup (System × Bath) ℂ) :
    liftToReference U ∈ Matrix.unitaryGroup (System × BathReference) ℂ := by
  apply Matrix.mem_unitaryGroup_iff'.mpr
  rw [Matrix.star_eq_conjTranspose]
  apply liftToReference_isometry
  simpa only [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.mp hU

/-- The actual density after coupling S to B with R a spectator. -/
def outputState (p : Bath → ℝ) (hp : ∀ b, 0 ≤ p b) (hsum : ∑ b, p b = 1)
    (U : Joint) (hU : U ∈ Matrix.unitaryGroup (System × Bath) ℂ) (ρ : DensityState System) :
    DensityState (System × BathReference) :=
  unitaryConjugateState (liftToReference U) (referenceLift_mem_unitary U hU)
    (productState ρ (purifiedBath p hp hsum))

theorem outputState_matrix (p : Bath → ℝ) (hp : ∀ b, 0 ≤ p b) (hsum : ∑ b, p b = 1)
    (U : Joint) (hU : U ∈ Matrix.unitaryGroup (System × Bath) ℂ) (ρ : DensityState System) :
    mat (outputState p hp hsum U hU ρ) = purifiedOutput p U (inputMatrix ρ) := by
  change liftToReference U * (inputMatrix ρ ⊗ₖ rankOneDensity (purificationVector p)) *
    star (liftToReference U) = _
  rw [Matrix.star_eq_conjTranspose, purifiedOutput]

/-- Trace out R by grouping the original S and B labels together. -/
def systemBathMarginal (ω : DensityState (System × BathReference)) :
    DensityState (System × Bath) :=
  marginalRight (relabelState (Equiv.prodAssoc System Bath Bath) ω)

/-- Trace out B by grouping the original S and R labels together. -/
def systemReferenceMarginal (ω : DensityState (System × BathReference)) :
    DensityState (System × Bath) :=
  marginalRight (relabelState ((Equiv.prodAssoc System Bath Bath).trans
    ((Equiv.refl System).prodCongr (Equiv.prodComm Bath Bath))) ω)

theorem systemBathMarginal_entry (ω : DensityState (System × BathReference))
    (i j : System) (b c : Bath) :
    mat (systemBathMarginal ω) (i, b) (j, c) =
      ∑ r : Bath, mat ω (i, (b, r)) (j, (c, r)) := rfl

theorem systemReferenceMarginal_entry (ω : DensityState (System × BathReference))
    (i j : System) (r s : Bath) :
    mat (systemReferenceMarginal ω) (i, r) (j, s) =
      ∑ b : Bath, mat ω (i, (b, r)) (j, (b, s)) := rfl

private theorem phaseJoint_entry (p : Bath → ℝ) (z : Bath → System → ℂ) (X : Qutrit)
    (i j : System) (b c : Bath) :
    jointOutput p (phaseUnitary z) X (i, b) (j, c) =
      z b i * (X i j * diagonalReal p b c) * star (z c j) := by
  rw [jointOutput, phaseUnitary, Matrix.blockDiagonal_diagonal, Matrix.diagonal_conjTranspose,
    Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.kronecker_apply]
  rfl

private theorem weighted_cross (p : Bath → ℝ) (hp : ∀ b, 0 ≤ p b)
    (z : Bath → System → ℂ) (i j : System) (b : Bath) :
    weightedColumns p z b i * star (weightedColumns p z b j) =
      (p b : ℂ) * (z b i * star (z b j)) := by
  have hroot : (Real.sqrt (p b) : ℂ) * (Real.sqrt (p b) : ℂ) = (p b : ℂ) := by
    rw [← Complex.ofReal_mul, ← pow_two, Real.sq_sqrt (hp b)]
  have hstar : star (Real.sqrt (p b) : ℂ) = (Real.sqrt (p b) : ℂ) := by
    rw [Complex.star_def, Complex.conj_ofReal]
  simp only [weightedColumns, star_mul, hstar]
  calc
    _ = ((Real.sqrt (p b) : ℂ) * (Real.sqrt (p b) : ℂ)) * (z b i * star (z b j)) := by
      ring
    _ = _ := by rw [hroot]

private theorem trace_reference_entry (p : Bath → ℝ) (hp : ∀ b, 0 ≤ p b)
    (z : Bath → System → ℂ) (X : Qutrit) (i j : System) (b c : Bath) :
    (∑ r : Bath, purifiedOutput p (phaseUnitary z) X (i, (b, r)) (j, (c, r))) =
      jointOutput p (phaseUnitary z) X (i, b) (j, c) := by
  rw [Finset.sum_eq_single b, phaseJoint_entry]
  · rw [purifiedOutput_entry]
    by_cases hbc : b = c
    · subst c
      simp only [recordVector, correlatedVector, eq_self, ite_true,
        weighted_cross p hp, diagonalReal, Matrix.diagonal_apply_eq]
      ring
    · simp [recordVector, correlatedVector, diagonalReal, hbc, Ne.symm hbc]
  · intro r _ hr
    simp [purifiedOutput_entry, recordVector, correlatedVector, Ne.symm hr]
  · simp

private theorem recordVector_swap (p : Bath → ℝ) (z : Bath → System → ℂ)
    (i : System) (b r : Bath) :
    recordVector p z i (r, b) = recordVector p z i (b, r) := by
  by_cases h : b = r
  · subst r
    rfl
  · simp [recordVector, correlatedVector, h, Ne.symm h]

/-- The physical output is the coherent copy followed by a local rectangular
record embedding on the second wire. The formula retains every off-diagonal
entry of the input. -/
theorem purifiedOutput_isometricCopy (p : Bath → ℝ) (z : Bath → System → ℂ)
    (hGram : (weightedColumns p z)ᴴ * weightedColumns p z = 1) (X : Qutrit) :
    let V := (1 : Qutrit) ⊗ₖ recordEmbedding p z
    Vᴴ * V = 1 ∧ purifiedOutput p (phaseUnitary z) X = V * copyMatrix X * Vᴴ := by
  dsimp only
  let V := (1 : Qutrit) ⊗ₖ recordEmbedding p z
  change Vᴴ * V = 1 ∧ purifiedOutput p (phaseUnitary z) X = V * copyMatrix X * Vᴴ
  constructor
  · dsimp only [V]
    rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul,
      Matrix.one_mul, recordEmbedding_isometry p z hGram, Matrix.one_kronecker_one]
  · let C : Matrix (System × System) System ℂ := copyIsometry
    have hVC (i : System) (x : BathReference) (k : System) :
        (V * C) (i, x) k = if i = k then recordVector p z i x else 0 := by
      rw [Matrix.mul_apply, Fintype.sum_prod_type, Finset.sum_eq_single i]
      · rw [Finset.sum_eq_single i]
        · by_cases hik : i = k <;>
            simp [V, C, copyIsometry, recordEmbedding_entry, hik]
        · intro b _ hb
          simp [V, C, copyIsometry, Ne.symm hb]
        · simp
      · intro a _ ha
        simp [V, Ne.symm ha]
      · simp
    change purifiedOutput p (phaseUnitary z) X = V * (C * X * Cᴴ) * Vᴴ
    have hfactor : V * (C * X * Cᴴ) * Vᴴ = (V * C) * X * (V * C)ᴴ := by
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [hfactor]
    apply Matrix.ext
    rintro ⟨i, x⟩ ⟨j, y⟩
    have hleft (k : System) : ((V * C) * X) (i, x) k = recordVector p z i x * X i k := by
      rw [Matrix.mul_apply, Finset.sum_eq_single i]
      · simp [hVC]
      · intro a _ ha
        simp [hVC, Ne.symm ha]
      · simp
    rw [purifiedOutput_entry, Matrix.mul_apply, Finset.sum_eq_single j]
    · simp only [Matrix.conjTranspose_apply, hVC, hleft, eq_self, ite_true]
      ring
    · intro k _ hk
      simp [Matrix.conjTranspose_apply, hVC, Ne.symm hk]
    · simp

/-- The two actual two-factor density marginals agree on the shared labels.
The SB marginal is the ordinary mixed Gibbs bath evolution. -/
theorem system_marginals (p : Bath → ℝ) (hp : ∀ b, 0 ≤ p b) (hsum : ∑ b, p b = 1)
    (z : Bath → System → ℂ) (hU : phaseUnitary z ∈ Matrix.unitaryGroup (System × Bath) ℂ)
    (ρ : DensityState System) :
    let ω := outputState p hp hsum (phaseUnitary z) hU ρ
    systemBathMarginal ω =
      unitaryConjugateState (phaseUnitary z) hU (productState ρ (bathState p hp hsum)) ∧
    systemReferenceMarginal ω = systemBathMarginal ω := by
  let ω := outputState p hp hsum (phaseUnitary z) hU ρ
  change systemBathMarginal ω = _ ∧ systemReferenceMarginal ω = systemBathMarginal ω
  constructor
  · apply Subtype.ext
    apply CStarMatrix.ofMatrix.symm.injective
    apply Matrix.ext
    rintro ⟨i, b⟩ ⟨j, c⟩
    refine (systemBathMarginal_entry ω i j b c).trans ?_
    change (∑ r : Bath, mat (outputState p hp hsum (phaseUnitary z) hU ρ)
      (i, (b, r)) (j, (c, r))) =
      (phaseUnitary z * (inputMatrix ρ ⊗ₖ mat (bathState p hp hsum)) *
        star (phaseUnitary z)) (i, b) (j, c)
    rw [outputState_matrix, bathState_matrix, Matrix.star_eq_conjTranspose]
    exact trace_reference_entry p hp z (inputMatrix ρ) i j b c
  · apply Subtype.ext
    apply CStarMatrix.ofMatrix.symm.injective
    apply Matrix.ext
    rintro ⟨i, b⟩ ⟨j, c⟩
    refine (systemReferenceMarginal_entry ω i j b c).trans
      (Eq.trans ?_ (systemBathMarginal_entry ω i j b c).symm)
    dsimp only [ω]
    simp only [outputState_matrix, purifiedOutput_entry]
    apply Finset.sum_congr rfl
    intro r _
    rw [recordVector_swap p z i b r, recordVector_swap p z j c r]

private theorem record_orthogonal (p : Bath → ℝ) (z : Bath → System → ℂ)
    (hGram : (weightedColumns p z)ᴴ * weightedColumns p z = 1) :
    Pairwise (fun i j : System =>
      (recordState p z hGram i).1 * (recordState p z hGram j).1 = 0) := by
  intro i j hij
  change rankOneDensity (recordVector p z i) * rankOneDensity (recordVector p z j) = 0
  simp only [rankOneDensity]
  rw [Matrix.vecMulVec_mul_vecMulVec,
    record_orthonormal p z hGram, ite_eq_right hij, zero_smul, Matrix.vecMulVec_zero]

/-- The BR marginal is the mixture of the physical conditional record densities,
with the Born weights of the original input. -/
theorem record_marginal (p : Bath → ℝ) (hp : ∀ b, 0 ≤ p b) (hsum : ∑ b, p b = 1)
    (z : Bath → System → ℂ) (hU : phaseUnitary z ∈ Matrix.unitaryGroup (System × Bath) ℂ)
    (hGram : (weightedColumns p z)ᴴ * weightedColumns p z = 1) (ρ : DensityState System) :
    marginalLeft (outputState p hp hsum (phaseUnitary z) hU ρ) =
      mixtureState (populations ρ) (populations_nonneg ρ) (sum_populations ρ)
        (recordState p z hGram) := by
  apply Subtype.ext
  apply CStarMatrix.ofMatrix.symm.injective
  change partialTraceLeft (mat (outputState p hp hsum (phaseUnitary z) hU ρ)) =
    ∑ i, populations ρ i • mat (recordState p z hGram i)
  rw [outputState_matrix]
  apply Matrix.ext
  intro x y
  simp only [partialTraceLeft, purifiedOutput_entry, Matrix.sum_apply, Matrix.smul_apply]
  apply Finset.sum_congr rfl
  intro i _
  change inputMatrix ρ i i * (recordVector p z i x * star (recordVector p z i y)) =
    populations ρ i • (recordVector p z i x * star (recordVector p z i y))
  rw [entry_eq_populations, Complex.real_smul]

/-- BR is the rectangular image of the qutrit pinching in the verification's
physical record columns. This equality holds in the original BR coordinates. -/
theorem record_marginal_embedding (p : Bath → ℝ) (hp : ∀ b, 0 ≤ p b)
    (hsum : ∑ b, p b = 1) (z : Bath → System → ℂ)
    (hU : phaseUnitary z ∈ Matrix.unitaryGroup (System × Bath) ℂ)
    (hGram : (weightedColumns p z)ᴴ * weightedColumns p z = 1) (ρ : DensityState System) :
    mat (marginalLeft (outputState p hp hsum (phaseUnitary z) hU ρ)) =
      LabelResetBandwidth.pad (recordEmbedding p z) (projectiveReadout (inputMatrix ρ)) := by
  let V := recordEmbedding p z
  change partialTraceLeft (mat (outputState p hp hsum (phaseUnitary z) hU ρ)) =
    LabelResetBandwidth.pad V (projectiveReadout (inputMatrix ρ))
  rw [outputState_matrix, (purifiedOutput_isometricCopy p z hGram (inputMatrix ρ)).2]
  change partialTraceLeft
      (LabelResetBandwidth.pad ((1 : Qutrit) ⊗ₖ V) (copyMatrix (inputMatrix ρ))) =
    LabelResetBandwidth.pad V (projectiveReadout (inputMatrix ρ))
  rw [LabelResetBandwidth.partialTrace_pad]
  have hcopy : partialTraceLeft (copyMatrix (inputMatrix ρ)) =
      projectiveReadout (inputMatrix ρ) :=
    congrArg (fun σ : DensityState System => mat σ) (marginalLeft_coherentCopyState ρ)
  rw [hcopy]

private theorem record_local_marginals (p : Bath → ℝ) (hp : ∀ b, 0 ≤ p b)
    (hsum : ∑ b, p b = 1) (z : Bath → System → ℂ)
    (hz : ∀ b i, Complex.normSq (z b i) = 1)
    (hGram : (weightedColumns p z)ᴴ * weightedColumns p z = 1) (i : System) :
    marginalRight (recordState p z hGram i) = bathState p hp hsum ∧
    marginalLeft (recordState p z hGram i) = bathState p hp hsum := by
  have h := conditionalRecord_marginals p hp z hz i
  have hrecord : mat (recordState p z hGram i) = conditionalRecord p (phaseUnitary z) i :=
    (conditionalRecord_state p z hGram i).symm
  constructor
  · apply Subtype.ext
    apply CStarMatrix.ofMatrix.symm.injective
    change partialTraceRight (mat (recordState p z hGram i)) = mat (bathState p hp hsum)
    rw [hrecord, bathState_matrix]
    exact h.1
  · apply Subtype.ext
    apply CStarMatrix.ofMatrix.symm.injective
    change partialTraceLeft (mat (recordState p z hGram i)) = mat (bathState p hp hsum)
    rw [hrecord, bathState_matrix]
    exact h.2

private theorem constant_mixture (ρ : DensityState System) {n : Type*}
    [Fintype n] [DecidableEq n] (τ : DensityState n) :
    mixtureState (populations ρ) (populations_nonneg ρ) (sum_populations ρ) (fun _ => τ) = τ := by
  apply Subtype.ext
  change (∑ i, populations ρ i • τ.1) = τ.1
  rw [← Finset.sum_smul, sum_populations, one_smul]

private theorem record_mixture_local (p : Bath → ℝ) (hp : ∀ b, 0 ≤ p b)
    (hsum : ∑ b, p b = 1) (z : Bath → System → ℂ)
    (hz : ∀ b i, Complex.normSq (z b i) = 1)
    (hGram : (weightedColumns p z)ᴴ * weightedColumns p z = 1) (ρ : DensityState System) :
    let σ := mixtureState (populations ρ) (populations_nonneg ρ) (sum_populations ρ)
      (recordState p z hGram)
    marginalRight σ = bathState p hp hsum ∧ marginalLeft σ = bathState p hp hsum := by
  dsimp only
  constructor
  · erw [marginalRight_mixture]
    simp only [fun i => (record_local_marginals p hp hsum z hz hGram i).1]
    exact constant_mixture ρ _
  · erw [marginalLeft_mixture]
    simp only [fun i => (record_local_marginals p hp hsum z hz hGram i).2]
    exact constant_mixture ρ _

private theorem system_marginal_consistency (ω : DensityState (System × BathReference)) :
    marginalRight (systemBathMarginal ω) = marginalRight ω := by
  apply Subtype.ext
  apply CStarMatrix.ofMatrix.symm.injective
  apply Matrix.ext
  intro i j
  change (∑ b : Bath, mat (systemBathMarginal ω) (i, b) (j, b)) =
    ∑ x : BathReference, mat ω (i, x) (j, x)
  simp only [systemBathMarginal_entry, Fintype.sum_prod_type]

private theorem bath_marginal_consistency (ω : DensityState (System × BathReference)) :
    marginalLeft (systemBathMarginal ω) = marginalRight (marginalLeft ω) := by
  apply Subtype.ext
  apply CStarMatrix.ofMatrix.symm.injective
  apply Matrix.ext
  intro b c
  change (∑ i : System, mat (systemBathMarginal ω) (i, b) (i, c)) =
    ∑ r : Bath, ∑ i : System, mat ω (i, (b, r)) (i, (c, r))
  simp only [systemBathMarginal_entry]
  exact Finset.sum_comm

private theorem conditional_information_entropy (ω : DensityState (System × BathReference)) :
    qcmi (toMState ω) =
      S (systemBathMarginal ω) + S (marginalLeft ω) -
        S (marginalLeft (systemBathMarginal ω)) - S ω := by
  have hassoc : (toMState ω).assoc' =
      toMState (relabelState (Equiv.prodAssoc System Bath Bath) ω) :=
    MState.ext_m rfl
  unfold qcmi qConditionalEnt
  rw [hassoc]
  change Sᵥₙ (toMState (systemBathMarginal ω)) -
    Sᵥₙ (toMState (marginalLeft (systemBathMarginal ω))) -
    (Sᵥₙ (toMState ω) - Sᵥₙ (toMState (marginalLeft ω))) = _
  erw [entropy_toMState, entropy_toMState, entropy_toMState, entropy_toMState]
  ring

private theorem coherent_copy_information_formula (ρ : DensityState System) :
    quantumMutualInformation (coherentCopyState ρ) = 2 * H (populations ρ) - S ρ := by
  have hRight : S (marginalRight (coherentCopyState ρ)) = H (populations ρ) :=
    (congrArg (fun σ : DensityState System => S σ) (marginalRight_coherentCopyState ρ)).trans
      (pinching_entropy ρ)
  have hLeft : S (marginalLeft (coherentCopyState ρ)) = H (populations ρ) :=
    (congrArg (fun σ : DensityState System => S σ) (marginalLeft_coherentCopyState ρ)).trans
      (pinching_entropy ρ)
  have hTotal : S (coherentCopyState ρ) = S ρ := vonNeumannEntropy_coherentCopyState ρ
  change S (marginalRight (coherentCopyState ρ)) + S (marginalLeft (coherentCopyState ρ)) -
    S (coherentCopyState ρ) = _
  rw [hRight, hLeft, hTotal]
  ring

/-- Entropy and information of the unmeasured physical output, together with
the exact density identifications used to compute them. -/
structure PurifiedBudgets (p : Bath → ℝ) (ρ : DensityState System)
    (ω : DensityState (System × BathReference)) (τ : DensityState Bath)
    (records : DensityState BathReference) (mixedOutput : DensityState (System × Bath)) : Prop where
  system_eq : marginalRight ω = basisPinchingState ρ
  bath_eq : marginalRight (marginalLeft ω) = τ
  reference_eq : marginalLeft (marginalLeft ω) = τ
  bath_reference_eq : marginalLeft ω = records
  system_bath_eq : systemBathMarginal ω = mixedOutput
  system_reference_eq : systemReferenceMarginal ω = systemBathMarginal ω
  system_entropy : S (marginalRight ω) = H (populations ρ)
  bath_entropy : S τ = H p
  bath_reference_entropy : S (marginalLeft ω) = H (populations ρ)
  system_bath_entropy : S (systemBathMarginal ω) = S ρ + H p
  system_reference_entropy : S (systemReferenceMarginal ω) = S ρ + H p
  total_entropy : S ω = S ρ
  system_bath_information :
    quantumMutualInformation (systemBathMarginal ω) = H (populations ρ) - S ρ
  system_reference_information :
    quantumMutualInformation (systemReferenceMarginal ω) = H (populations ρ) - S ρ
  system_bath_reference_information : quantumMutualInformation ω = 2 * H (populations ρ) - S ρ
  system_reference_given_bath : qcmi (toMState ω) = H (populations ρ)
  coherent_copy_information :
    quantumMutualInformation ω = quantumMutualInformation (coherentCopyState ρ)

/-- For the fixed Gibbs law and its orthogonal weighted phase witness, the same
energy-conserving interaction gives these budgets for every qutrit density.
Singular and coherent inputs are allowed. -/
theorem gibbs_phase_budgets (β : ℝ) (E : Bath → ℝ) (hE : Function.Injective E)
    (z : Bath → System → ℂ) (hz : ∀ b i, Complex.normSq (z b i) = 1)
    (hGram : (weightedColumns (gibbsWeight β E) z)ᴴ *
      weightedColumns (gibbsWeight β E) z = 1) (ρ : DensityState System) :
    let p := gibbsWeight β E
    let hp := fun b => (gibbsWeight_pos β E b).le
    let hsum := sum_gibbsWeight β E
    ∃ hU : phaseUnitary z ∈ Matrix.unitaryGroup (System × Bath) ℂ,
      IsEnergyConserving (fun _ => 0) E (phaseUnitary z) ∧
      PurifiedBudgets p ρ (outputState p hp hsum (phaseUnitary z) hU ρ)
        (bathState p hp hsum)
        (mixtureState (populations ρ) (populations_nonneg ρ) (sum_populations ρ)
          (recordState p z hGram))
        (unitaryConjugateState (phaseUnitary z) hU (productState ρ (bathState p hp hsum))) := by
  dsimp only
  let p := gibbsWeight β E
  have hp (b : Bath) : 0 ≤ p b := (gibbsWeight_pos β E b).le
  have hsum : ∑ b, p b = 1 := sum_gibbsWeight β E
  obtain ⟨hU, henergy, hpinch, _⟩ := phase_realization β E hE z hz hGram
  refine ⟨hU, henergy, ?_⟩
  let ω := outputState p hp hsum (phaseUnitary z) hU ρ
  let τ := bathState p hp hsum
  let records := mixtureState (populations ρ) (populations_nonneg ρ) (sum_populations ρ)
    (recordState p z hGram)
  let mixedOutput := unitaryConjugateState (phaseUnitary z) hU (productState ρ τ)
  change PurifiedBudgets p ρ ω τ records mixedOutput
  have hSB : systemBathMarginal ω = mixedOutput := (system_marginals p hp hsum z hU ρ).1
  have hSR : systemReferenceMarginal ω = systemBathMarginal ω :=
    (system_marginals p hp hsum z hU ρ).2
  have hBR : marginalLeft ω = records := record_marginal p hp hsum z hU hGram ρ
  have hB : marginalRight (marginalLeft ω) = τ := by
    rw [hBR]
    exact (record_mixture_local p hp hsum z hz hGram ρ).1
  have hR : marginalLeft (marginalLeft ω) = τ := by
    rw [hBR]
    exact (record_mixture_local p hp hsum z hz hGram ρ).2
  have hBathSB : marginalLeft (systemBathMarginal ω) = τ :=
    (bath_marginal_consistency ω).trans hB
  have hS : marginalRight ω = basisPinchingState ρ := by
    rw [← system_marginal_consistency ω, hSB]
    apply Subtype.ext
    apply CStarMatrix.ofMatrix.symm.injective
    change partialTraceRight (phaseUnitary z * (inputMatrix ρ ⊗ₖ mat τ) *
      star (phaseUnitary z)) = projectiveReadout (inputMatrix ρ)
    rw [show mat τ = diagonalReal p from bathState_matrix p hp hsum,
      Matrix.star_eq_conjTranspose]
    exact hpinch _
  have hEntropyS : S (marginalRight ω) = H (populations ρ) :=
    (congrArg vonNeumannEntropy hS).trans (pinching_entropy ρ)
  have hEntropyB : S τ = H p :=
    entropy_of_diagonal τ p (bathState_matrix p hp hsum)
  have hEntropyBR : S (marginalLeft ω) = H (populations ρ) := by
    rw [hBR]
    change S (mixtureState (populations ρ) (populations_nonneg ρ) (sum_populations ρ)
      (recordState p z hGram)) = _
    rw [orthogonal_mixture_entropy _ _ _ _ (record_orthogonal p z hGram)]
    have hpure (i : System) : S (recordState p z hGram i) = 0 :=
      pure_entropy (recordVector p z i) (by simp [record_orthonormal p z hGram])
    simp only [hpure, mul_zero, Finset.sum_const_zero, add_zero]
  have hEntropySB : S (systemBathMarginal ω) = S ρ + H p := by
    rw [hSB]
    change S (unitaryConjugateState (phaseUnitary z) hU (productState ρ τ)) = _
    rw [von_neumann_entropy_unitary]
    exact (vonNeumannEntropy_productState ρ τ).trans (congrArg (S ρ + ·) hEntropyB)
  have hEntropyTotal : S ω = S ρ := by
    change S (unitaryConjugateState (liftToReference (phaseUnitary z))
      (referenceLift_mem_unitary (phaseUnitary z) hU) (productState ρ (purifiedBath p hp hsum))) = _
    have hPure : S (purifiedBath p hp hsum) = 0 :=
      pure_entropy (purificationVector p) (purification_normalized p hp hsum)
    rw [von_neumann_entropy_unitary]
    calc
      _ = S ρ + S (purifiedBath p hp hsum) := vonNeumannEntropy_productState _ _
      _ = S ρ := by rw [hPure, add_zero]
  have hInfoSB : quantumMutualInformation (systemBathMarginal ω) = H (populations ρ) - S ρ := by
    change S (marginalRight (systemBathMarginal ω)) + S (marginalLeft (systemBathMarginal ω)) -
      S (systemBathMarginal ω) = _
    rw [system_marginal_consistency, hEntropyS, hBathSB, hEntropyB, hEntropySB]
    ring
  have hInfoTotal : quantumMutualInformation ω = 2 * H (populations ρ) - S ρ := by
    change S (marginalRight ω) + S (marginalLeft ω) - S ω = _
    rw [hEntropyS, hEntropyBR, hEntropyTotal]
    ring
  refine ⟨hS, hB, hR, hBR, hSB, hSR, hEntropyS, hEntropyB, hEntropyBR,
    hEntropySB, ?_, hEntropyTotal, hInfoSB, ?_, hInfoTotal, ?_,
    hInfoTotal.trans (coherent_copy_information_formula ρ).symm⟩
  · rw [hSR, hEntropySB]
  · rw [hSR, hInfoSB]
  · rw [conditional_information_entropy, hEntropySB, hEntropyBR, hBathSB, hEntropyB, hEntropyTotal]
    ring

/-- The verified row cap and cubic guard supply one physical interaction before
the arbitrary qutrit input is chosen. -/
theorem gibbs_cubic_budgets (β : ℝ) (E : Bath → ℝ) (hE : Function.Injective E)
    (hcap : ∀ b, gibbsWeight β E b ≤ 1 / 3) (t : ℝ) (ht : 0 < t) (ht' : t ≤ 1)
    (hguard : ∀ b,
      D5.S3.Quantum.Measurements.ThreeDistinguishabilityCubic.q (gibbsWeight β E) b ^ 2 * t ≥
      D5.S3.Quantum.Measurements.ThreeDistinguishabilityCubic.d (gibbsWeight β E) b ^ 2)
    (hroot :
      D5.S3.Quantum.Measurements.ThreeDistinguishabilityCubic.phaseCubic (gibbsWeight β E) t = 0) :
    let p := gibbsWeight β E
    let hp := fun b => (gibbsWeight_pos β E b).le
    let hsum := sum_gibbsWeight β E
    ∃ (z : Bath → System → ℂ)
        (hGram : (weightedColumns p z)ᴴ * weightedColumns p z = 1)
        (hU : phaseUnitary z ∈ Matrix.unitaryGroup (System × Bath) ℂ),
      IsEnergyConserving (fun _ => 0) E (phaseUnitary z) ∧
      (∀ X : Qutrit, operation β E (phaseUnitary z) X = projectiveReadout X) ∧
      Nonempty (BasisObservation p (phaseUnitary z)) ∧
      ∀ ρ : DensityState System,
        PurifiedBudgets p ρ (outputState p hp hsum (phaseUnitary z) hU ρ)
          (bathState p hp hsum)
          (mixtureState (populations ρ) (populations_nonneg ρ) (sum_populations ρ)
            (recordState p z hGram))
          (unitaryConjugateState (phaseUnitary z) hU (productState ρ (bathState p hp hsum))) := by
  dsimp only
  have hFeasible := (fixed_bath_pinching_iff_cubic β E hE).mpr
    ⟨hcap, t, ht, ht', hguard, hroot⟩
  obtain ⟨z, hz, hGram⟩ := (fixed_bath_pinching_iff β E hE).mp hFeasible
  obtain ⟨hU, henergy, hpinch, _⟩ := phase_realization β E hE z hz hGram
  refine ⟨z, hGram, hU, henergy, hpinch, ⟨basisObservation _
    (fun b => (gibbsWeight_pos β E b).le) (sum_gibbsWeight β E) z hz hGram⟩, ?_⟩
  intro ρ
  obtain ⟨_, _, hbudget⟩ := gibbs_phase_budgets β E hE z hz hGram ρ
  exact hbudget

/-- Basis-label laws from the actual output. The coordinate law is independent
of the label, the phase-sensitive joint decoder recovers it, and the one-way
Fourier protocol recovers it in each reference branch. -/
theorem basis_readout_comparison (p : Bath → ℝ) (hp : ∀ b, 0 ≤ p b)
    (z : Bath → System → ℂ) (hz : ∀ b i, Complex.normSq (z b i) = 1)
    (hGram : (weightedColumns p z)ᴴ * weightedColumns p z = 1) :
    (∀ i : System, partialTraceRight (conditionalRecord p (phaseUnitary z) i) = diagonalReal p ∧
      partialTraceLeft (conditionalRecord p (phaseUnitary z) i) = diagonalReal p) ∧
    (∀ (i : System) (b r : Bath),
      (Matrix.trace (basisProjector (b, r) * conditionalRecord p (phaseUnitary z) i)).re =
        if b = r then p b else 0) ∧
    (∀ (i : System) (o : Option System),
      (Matrix.trace (orthogonalReadout (recordEmbedding p z) o *
        conditionalRecord p (phaseUnitary z) i)).re = if o = some i then 1 else 0) ∧
    (∀ (i : System) (k : Bath),
      (Matrix.trace (referenceEffect k *
        partialTraceLeft (conditionalRecord p (phaseUnitary z) i))).re = 1 / 4) ∧
    (∀ (i : System) (k : Bath) (o : Option System),
      (Matrix.trace (orthogonalReadout (fourierColumns p z k) o *
        fourierBranch p (phaseUnitary z) i k)).re = if o = some i then 1 / 4 else 0) :=
  ⟨conditionalRecord_marginals p hp z hz, joint_basis_born p hp z hz,
    joint_decoder_born p z hGram, fourier_outcome_uniform p z hGram,
    fourier_decoder_born p z hGram⟩

/-- The CQ state for the classical coordinate label, using the Born prior of ρ. -/
def labelState {n : Type*} [Fintype n] [DecidableEq n] (ρ : DensityState System)
    (f : System → DensityState n) : DensityState (System × n) :=
  D5.S3.Quantum.Information.OrthogonalRecordEntropy.recordState
    (populations ρ) (populations_nonneg ρ) (sum_populations ρ) f

private theorem constant_label_information (ρ : DensityState System) (τ : DensityState Bath) :
    quantumMutualInformation (labelState ρ (fun _ => τ)) = 0 := by
  have hPointer : S (mixtureState (populations ρ) (populations_nonneg ρ)
      (sum_populations ρ) (pointerState (n := System))) = H (populations ρ) := by
    rw [orthogonal_mixture_entropy _ _ _ _ pointerState_orthogonal]
    simp only [entropy_pointerState, mul_zero, Finset.sum_const_zero, add_zero]
  unfold quantumMutualInformation labelState
  erw [entropy_recordState]
  unfold D5.S3.Quantum.Information.OrthogonalRecordEntropy.recordState
  erw [marginalRight_mixture, marginalLeft_mixture]
  have hRight (i : System) :
      marginalRight (productState (pointerState i) τ) = pointerState i :=
    marginalRight_productState _ _
  have hLeft (i : System) : marginalLeft (productState (pointerState i) τ) = τ :=
    marginalLeft_productState _ _
  simp only [hRight, hLeft]
  erw [hPointer, constant_mixture, ← Finset.sum_mul, sum_populations, one_mul]
  ring

/-- X is a classical input label with the input qutrit's Born prior. The
records here are the conditional physical output given that label. -/
theorem basis_label_budgets (p : Bath → ℝ) (hp : ∀ b, 0 ≤ p b)
    (hsum : ∑ b, p b = 1) (z : Bath → System → ℂ)
    (hz : ∀ b i, Complex.normSq (z b i) = 1)
    (hGram : (weightedColumns p z)ᴴ * weightedColumns p z = 1) (ρ : DensityState System) :
    quantumMutualInformation (labelState ρ (fun i => marginalRight (recordState p z hGram i))) = 0 ∧
    quantumMutualInformation (labelState ρ (fun i => marginalLeft (recordState p z hGram i))) = 0 ∧
    quantumMutualInformation (labelState ρ (recordState p z hGram)) = H (populations ρ) := by
  refine ⟨?_, ?_, orthogonal_record_trace_gives_sbs_consensus _ _ _ _ (record_orthogonal p z hGram)⟩
  · simpa only [fun i => (record_local_marginals p hp hsum z hz hGram i).1]
      using constant_label_information ρ (bathState p hp hsum)
  · simpa only [fun i => (record_local_marginals p hp hsum z hz hGram i).2]
      using constant_label_information ρ (bathState p hp hsum)

end D5.S3.Quantum.Decoherence.FourLevelBathEntropyBudget
