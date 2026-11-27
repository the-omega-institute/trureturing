/- GID: D5/S3/Quantum/Decoherence/FourLevelBathObserver
   generality: I
   mirror-B: D5/B/S3/Quantum/Decoherence/FourLevelBathObserver
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual purified Gibbs bath records hide the label in each margin and permit exact joint readout. -/

import D5.S3.Quantum.Decoherence.FourLevelBathCubic
import D5.S3.Quantum.Information.CoherentCopyCorrelationTax
import D5.S3.Quantum.PureState.JointRecordDecoding

/-!
# Observing the record of a purified fixed Gibbs bath

The preparation supplies a separate coherent reference in the same coordinate
labels as the bath. In the dynamics the reference is a spectator. The readout
uses phase-sensitive effects on the bath and the reference. Energy conservation
here is a condition on the interaction on the system and bath.
-/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Quantum.Decoherence.FourLevelBathObserver

open Matrix _root_.D5.S3.Quantum.Decoherence.FourLevelBathPhysical
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
open GibbsBathBandwidth (diagonalReal gibbsWeight gibbsWeight_pos sum_gibbsWeight)
open D5.S3.QuantumChannels.CoolingMapThermalOperationRefutation (IsEnergyConserving)
open D5.S3.QuantumChannels.ThermalOperationDegeneracyRefutation (operation)
open D5.S3.Quantum.Decoherence.ProjectedUnistochasticDynamics
  (basisProjector projectiveReadout)
open D5.S3.Quantum.Foundation.FiniteStateChannel (DensityState)
open D5.S3.Quantum.Information.CoherentCopyCorrelationTax
  (copyIsometry copyIsometry_star_mul)
open D5.S3.Quantum.Information.PartialTraceMutualInformation
  (partialTraceLeft partialTraceRight)
open D5.S3.Quantum.PureState.PureStateHandshake (rankOneDensity)

abbrev BathReference := Bath × Bath
abbrev Tripartite := Matrix (System × BathReference) (System × BathReference) ℂ

/-- Amplitudes in the correlated basis `|b,b⟩` of the bath and reference. -/
def correlatedVector (v : Bath → ℂ) (x : BathReference) : ℂ :=
  if x.1 = x.2 then v x.1 else 0

private theorem correlated_inner (u v : Bath → ℂ) :
    star (correlatedVector u) ⬝ᵥ correlatedVector v = star u ⬝ᵥ v := by
  simp only [dotProduct, Pi.star_apply, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.sum_eq_single b]
  · simp [correlatedVector]
  · intro c _ hcb
    simp [correlatedVector, Ne.symm hcb]
  · simp

/-- The separately prepared vector `∑ b, √p_b |b,b⟩`. -/
def purificationVector (p : Bath → ℝ) : BathReference → ℂ :=
  correlatedVector (fun b => (Real.sqrt (p b) : ℂ))

private theorem sqrt_normSq (t : ℝ) (ht : 0 ≤ t) :
    Complex.normSq (Real.sqrt t : ℂ) = t := by
  rw [Complex.normSq_ofReal, ← pow_two, Real.sq_sqrt ht]

private theorem purification_normalized (p : Bath → ℝ) (hp : ∀ b, 0 ≤ p b)
    (hsum : ∑ b, p b = 1) :
    star (purificationVector p) ⬝ᵥ purificationVector p = 1 := by
  unfold purificationVector
  rw [correlated_inner]
  calc
    _ = (((∑ b, p b) : ℝ) : ℂ) := by
      rw [Complex.ofReal_sum]
      apply Finset.sum_congr rfl
      intro b _
      change star (Real.sqrt (p b) : ℂ) * (Real.sqrt (p b) : ℂ) = (p b : ℂ)
      rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, sqrt_normSq _ (hp b)]
    _ = 1 := by rw [hsum, Complex.ofReal_one]

/-- The canonical density value of the specified coherent input on BR. -/
def purifiedBath (p : Bath → ℝ) (hp : ∀ b, 0 ≤ p b)
    (hsum : ∑ b, p b = 1) : DensityState BathReference :=
  JointRecordDecoding.pureState _ (purification_normalized p hp hsum)

private theorem correlated_marginals (v : Bath → ℂ) (p : Bath → ℝ)
    (hweight : ∀ b, v b * star (v b) = (p b : ℂ)) :
    partialTraceRight (rankOneDensity (correlatedVector v)) = diagonalReal p ∧
      partialTraceLeft (rankOneDensity (correlatedVector v)) = diagonalReal p := by
  constructor
  · apply Matrix.ext
    intro b c
    change (∑ r : Bath, correlatedVector v (b, r) * star (correlatedVector v (c, r))) =
      diagonalReal p b c
    rw [Finset.sum_eq_single b]
    · by_cases h : b = c
      · subst c
        simpa [correlatedVector, diagonalReal] using hweight b
      · simp [correlatedVector, diagonalReal, h, Ne.symm h]
    · intro r _ hr
      simp [correlatedVector, Ne.symm hr]
    · simp
  · apply Matrix.ext
    intro b c
    change (∑ a : Bath, correlatedVector v (a, b) * star (correlatedVector v (a, c))) =
      diagonalReal p b c
    rw [Finset.sum_eq_single b]
    · by_cases h : b = c
      · subst c
        simpa [correlatedVector, diagonalReal] using hweight b
      · simp [correlatedVector, diagonalReal, h]
    · intro a _ ha
      simp [correlatedVector, ha]
    · simp

theorem purifiedBath_marginals (p : Bath → ℝ) (hp : ∀ b, 0 ≤ p b)
    (hsum : ∑ b, p b = 1) :
    let Ω := CStarMatrix.ofMatrix.symm (purifiedBath p hp hsum).1
    partialTraceRight Ω = diagonalReal p ∧ partialTraceLeft Ω = diagonalReal p := by
  change partialTraceRight (rankOneDensity (purificationVector p)) = diagonalReal p ∧
    partialTraceLeft (rankOneDensity (purificationVector p)) = diagonalReal p
  exact correlated_marginals _ p (fun b => by
    rw [Complex.star_def, Complex.mul_conj, sqrt_normSq _ (hp b)])

private def associateWires : (System × BathReference) ≃ ((System × Bath) × Bath) :=
  (Equiv.prodAssoc System Bath Bath).symm

/-- The actual `U_SB ⊗ I_R`, grouped with S as the left factor for partial trace. -/
def liftToReference (U : Joint) : Tripartite :=
  (U ⊗ₖ (1 : Matrix Bath Bath ℂ)).submatrix associateWires associateWires

private theorem liftToReference_isometry (U : Joint) (hU : Uᴴ * U = 1) :
    (liftToReference U)ᴴ * liftToReference U = 1 := by
  rw [liftToReference, Matrix.conjTranspose_submatrix, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_one,
    Matrix.submatrix_mul_equiv _ _ _ associateWires _,
    ← Matrix.mul_kronecker_mul, hU, Matrix.one_mul, Matrix.one_kronecker_one,
    Matrix.submatrix_one_equiv]

/-- Evolve the density matrix of the product of the independent system and the
specified coherent bath purification. -/
def purifiedOutput (p : Bath → ℝ) (U : Joint) (X : Qutrit) : Tripartite :=
  liftToReference U * (X ⊗ₖ rankOneDensity (purificationVector p)) * (liftToReference U)ᴴ

theorem purifiedOutput_density (p : Bath → ℝ) (hp : ∀ b, 0 ≤ p b)
    (hsum : ∑ b, p b = 1) (U : Joint) (hU : Uᴴ * U = 1) (ρ : DensityState System) :
    (purifiedOutput p U (inputMatrix ρ)).PosSemidef ∧
      (purifiedOutput p U (inputMatrix ρ)).trace = 1 := by
  have hΩ : (rankOneDensity (purificationVector p)).trace = 1 :=
    (purifiedBath p hp hsum).trace_eq_one
  have hρ :=
    D5.S3.Quantum.Information.PartialTraceMutualInformation.density_posSemidef ρ
  constructor
  · apply Matrix.PosSemidef.mul_mul_conjTranspose_same
    exact hρ.kronecker (Matrix.posSemidef_vecMulVec_self_star (purificationVector p))
  · rw [purifiedOutput, Matrix.trace_mul_cycle, liftToReference_isometry U hU,
      Matrix.one_mul, Matrix.trace_kronecker, hΩ, mul_one]
    exact ρ.trace_eq_one

/-- The matrix obtained by tracing S out of the evolved basis input. -/
def conditionalRecord (p : Bath → ℝ) (U : Joint) (i : System) :
    Matrix BathReference BathReference ℂ :=
  partialTraceLeft (purifiedOutput p U (basisProjector i))

def recordVector (p : Bath → ℝ) (z : Bath → System → ℂ) (i : System) :
    BathReference → ℂ :=
  correlatedVector (fun b => weightedColumns p z b i)

/-- Embed the weighted columns into the correlated BR coordinate subspace
using the existing coherent-copy isometry. -/
def recordEmbedding (p : Bath → ℝ) (z : Bath → System → ℂ) :
    Matrix BathReference System ℂ :=
  @HMul.hMul _ _ _ Matrix.instHMulOfFintypeOfMulOfAddCommMonoid
    (copyIsometry (n := Bath)) (weightedColumns p z)

private theorem recordEmbedding_entry (p : Bath → ℝ) (z : Bath → System → ℂ)
    (x : BathReference) (i : System) :
    recordEmbedding p z x i = recordVector p z i x := by
  rcases x with ⟨b, r⟩
  by_cases h : b = r
  · subst r
    rw [recordEmbedding, Matrix.mul_apply, Finset.sum_eq_single b]
    · simp [copyIsometry, recordVector, correlatedVector]
    · intro c _ hc
      simp [copyIsometry, Matrix.one_apply, hc, Ne.symm hc]
    · simp
  · simp [recordEmbedding, Matrix.mul_apply, copyIsometry, recordVector, correlatedVector, h]

private theorem recordEmbedding_isometry (p : Bath → ℝ) (z : Bath → System → ℂ)
    (hGram : (weightedColumns p z)ᴴ * weightedColumns p z = 1) :
    (recordEmbedding p z)ᴴ * recordEmbedding p z = 1 := by
  rw [recordEmbedding, Matrix.conjTranspose_mul, Matrix.mul_assoc,
    ← Matrix.mul_assoc (copyIsometry (n := Bath))ᴴ, copyIsometry_star_mul,
    Matrix.one_mul, hGram]

private theorem lifted_phase_diagonal (z : Bath → System → ℂ) :
    liftToReference (phaseUnitary z) =
      Matrix.diagonal (fun x : System × BathReference => z x.2.1 x.1) := by
  apply Matrix.ext
  rintro ⟨i, b, r⟩ ⟨j, c, s⟩
  change (phaseUnitary z) (i, b) (j, c) * (1 : Matrix Bath Bath ℂ) r s =
    Matrix.diagonal (fun x : System × BathReference => z x.2.1 x.1) (i, b, r) (j, c, s)
  by_cases hij : i = j <;> by_cases hbc : b = c <;> by_cases hrs : r = s <;>
    simp [phaseUnitary, Matrix.blockDiagonal_diagonal, Matrix.one_apply,
      Prod.mk.injEq, hij, hbc, hrs]

/-- The entries of the physical output on every system matrix, including coherent inputs. -/
theorem purifiedOutput_entry (p : Bath → ℝ) (z : Bath → System → ℂ) (X : Qutrit)
    (i j : System) (x y : BathReference) :
    purifiedOutput p (phaseUnitary z) X (i, x) (j, y) =
      X i j * (recordVector p z i x * star (recordVector p z j y)) := by
  rcases x with ⟨b, r⟩
  rcases y with ⟨c, s⟩
  rw [purifiedOutput, lifted_phase_diagonal, Matrix.diagonal_conjTranspose,
    Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.kronecker_apply]
  by_cases hbr : b = r <;> by_cases hcs : c = s <;>
    simp only [rankOneDensity, Matrix.vecMulVec_apply, Pi.star_apply, purificationVector,
      recordVector, correlatedVector, hbr, hcs, ite_true, ite_false, weightedColumns,
      star_mul, zero_mul, mul_zero, star_zero]
  ring

/-- The conditional BR density is the rank-one operator of the actual evolved record. -/
theorem conditionalRecord_eq (p : Bath → ℝ) (z : Bath → System → ℂ) (i : System) :
    conditionalRecord p (phaseUnitary z) i = rankOneDensity (recordVector p z i) := by
  apply Matrix.ext
  intro x y
  change (∑ j : System, purifiedOutput p (phaseUnitary z) (basisProjector i) (j, x) (j, y)) =
    rankOneDensity (recordVector p z i) x y
  rw [Finset.sum_eq_single i]
  · simp [purifiedOutput_entry, basisProjector, rankOneDensity, Matrix.vecMulVec_apply]
  · intro j _ hj
    simp [purifiedOutput_entry, basisProjector, Ne.symm hj]
  · simp

private theorem weighted_entry_mass (p : Bath → ℝ) (hp : ∀ b, 0 ≤ p b)
    (z : Bath → System → ℂ) (hz : ∀ b i, Complex.normSq (z b i) = 1)
    (i : System) (b : Bath) :
    weightedColumns p z b i * star (weightedColumns p z b i) = (p b : ℂ) := by
  rw [Complex.star_def, Complex.mul_conj]
  simp only [weightedColumns, Complex.normSq_mul, sqrt_normSq _ (hp b), hz, mul_one]

theorem conditionalRecord_marginals (p : Bath → ℝ) (hp : ∀ b, 0 ≤ p b)
    (z : Bath → System → ℂ) (hz : ∀ b i, Complex.normSq (z b i) = 1) (i : System) :
    partialTraceRight (conditionalRecord p (phaseUnitary z) i) = diagonalReal p ∧
      partialTraceLeft (conditionalRecord p (phaseUnitary z) i) = diagonalReal p := by
  rw [conditionalRecord_eq]
  exact correlated_marginals _ p (weighted_entry_mass p hp z hz i)

/-- Actual Born law for the joint coordinate readout using the bath energy labels
and the corresponding reference coordinates. -/
theorem joint_basis_born (p : Bath → ℝ) (hp : ∀ b, 0 ≤ p b)
    (z : Bath → System → ℂ) (hz : ∀ b i, Complex.normSq (z b i) = 1)
    (i : System) (b r : Bath) :
    (Matrix.trace (basisProjector (b, r) * conditionalRecord p (phaseUnitary z) i)).re =
      if b = r then p b else 0 := by
  rw [basisProjector, Matrix.trace_single_mul, one_smul, conditionalRecord_eq]
  change (recordVector p z i (b, r) * star (recordVector p z i (b, r))).re = _
  by_cases h : b = r
  · subst r
    simp only [recordVector, correlatedVector, Prod.fst, Prod.snd, eq_self, ite_true,
      weighted_entry_mass p hp z hz, Complex.ofReal_re]
  · simp [recordVector, correlatedVector, h]

/-- All observables diagonal in the joint readout basis have a common expectation. -/
theorem diagonal_observable_expectation (p : Bath → ℝ) (hp : ∀ b, 0 ≤ p b)
    (z : Bath → System → ℂ) (hz : ∀ b i, Complex.normSq (z b i) = 1)
    (i : System) (d : BathReference → ℂ) :
    Matrix.trace (Matrix.diagonal d * conditionalRecord p (phaseUnitary z) i) =
      ∑ b, d (b, b) * (p b : ℂ) := by
  rw [conditionalRecord_eq]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.diagonal_mul, rankOneDensity,
    Matrix.vecMulVec_apply, Pi.star_apply, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.sum_eq_single b]
  · simp only [recordVector, correlatedVector, Prod.fst, Prod.snd, eq_self, ite_true,
      weighted_entry_mass p hp z hz]
  · intro r _ hr
    simp [recordVector, correlatedVector, Ne.symm hr]
  · simp

section Readout

variable {H J : Type*} [Fintype H] [DecidableEq H] [Fintype J] [DecidableEq J]

private def columnProjector (V : Matrix H J ℂ) (j : J) : Matrix H H ℂ :=
  rankOneDensity (fun h => V h j)

omit [DecidableEq H] [Fintype J] in
private theorem column_inner (V : Matrix H J ℂ) (hV : Vᴴ * V = 1) (i j : J) :
    star (fun h => V h i) ⬝ᵥ (fun h => V h j) = if i = j then 1 else 0 := by
  simpa only [dotProduct, Pi.star_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.one_apply] using congrArg (fun M : Matrix J J ℂ => M i j) hV

omit [DecidableEq H] [Fintype J] in
private theorem columnProjector_mul (V : Matrix H J ℂ) (hV : Vᴴ * V = 1) (i j : J) :
    columnProjector V i * columnProjector V j =
      if i = j then columnProjector V j else 0 := by
  unfold columnProjector rankOneDensity
  rw [Matrix.vecMulVec_mul_vecMulVec, column_inner V hV]
  by_cases h : i = j
  · subst j
    simp
  · simp [h]

omit [Fintype H] [DecidableEq H] [DecidableEq J] in
private theorem sum_columnProjector (V : Matrix H J ℂ) :
    (∑ j, columnProjector V j) = V * Vᴴ := by
  apply Matrix.ext
  intro x y
  simp only [Matrix.sum_apply, columnProjector, rankOneDensity, Matrix.vecMulVec_apply,
    Pi.star_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]

/-- The projective readout consists of the column projectors and the orthogonal complement. -/
def orthogonalReadout (V : Matrix H J ℂ) : Option J → Matrix H H ℂ
  | none => 1 - V * Vᴴ
  | some j => columnProjector V j

theorem orthogonalReadout_projection (V : Matrix H J ℂ) (hV : Vᴴ * V = 1) (o : Option J) :
    IsStarProjection (orthogonalReadout V o) := by
  cases o with
  | none =>
    change IsStarProjection (1 - V * Vᴴ)
    apply IsStarProjection.one_sub
    apply isStarProjection_iff'.mpr
    constructor
    · rw [Matrix.mul_assoc, ← Matrix.mul_assoc Vᴴ V, hV, Matrix.one_mul]
    · simp [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul]
  | some j =>
    change IsStarProjection (columnProjector V j)
    apply isStarProjection_iff'.mpr
    constructor
    · simpa using columnProjector_mul V hV j j
    · exact (Matrix.posSemidef_vecMulVec_self_star (fun h => V h j)).isHermitian.isSelfAdjoint

theorem orthogonalReadout_complete (V : Matrix H J ℂ) :
    (∑ o, orthogonalReadout V o) = 1 := by
  rw [Fintype.sum_option]
  change (1 - V * Vᴴ) + (∑ j, columnProjector V j) = 1
  rw [sum_columnProjector, sub_add_cancel]

theorem orthogonalReadout_born (V : Matrix H J ℂ) (hV : Vᴴ * V = 1)
    (j : J) (o : Option J) :
    (Matrix.trace (orthogonalReadout V o * rankOneDensity (fun h => V h j))).re =
      if o = some j then 1 else 0 := by
  have htrace : (columnProjector V j).trace = 1 := by
    rw [columnProjector, rankOneDensity, Matrix.trace_vecMulVec, dotProduct_comm,
      column_inner V hV, ite_eq_left rfl]
  cases o with
  | none =>
    have hspan : (V * Vᴴ) * columnProjector V j = columnProjector V j := by
      rw [← sum_columnProjector, Matrix.sum_mul, Finset.sum_eq_single j]
      · simpa using columnProjector_mul V hV j j
      · intro i _ hij
        simp [columnProjector_mul V hV, hij]
      · simp
    change (Matrix.trace ((1 - V * Vᴴ) * columnProjector V j)).re = _
    simp [Matrix.sub_mul, hspan]
  | some i =>
    change (Matrix.trace (columnProjector V i * columnProjector V j)).re = _
    by_cases h : i = j <;> simp [columnProjector_mul V hV, htrace, h]

end Readout

private theorem record_orthonormal (p : Bath → ℝ) (z : Bath → System → ℂ)
    (hGram : (weightedColumns p z)ᴴ * weightedColumns p z = 1) (i j : System) :
    star (recordVector p z i) ⬝ᵥ recordVector p z j = if i = j then 1 else 0 := by
  simpa only [recordEmbedding_entry] using
    column_inner (recordEmbedding p z) (recordEmbedding_isometry p z hGram) i j

/-- Canonical pure density of the conditional record. -/
def recordState (p : Bath → ℝ) (z : Bath → System → ℂ)
    (hGram : (weightedColumns p z)ᴴ * weightedColumns p z = 1) (i : System) :
    DensityState BathReference :=
  JointRecordDecoding.pureState (recordVector p z i) (by simp [record_orthonormal p z hGram])

private theorem conditionalRecord_state (p : Bath → ℝ) (z : Bath → System → ℂ)
    (hGram : (weightedColumns p z)ᴴ * weightedColumns p z = 1) (i : System) :
    conditionalRecord p (phaseUnitary z) i =
      CStarMatrix.ofMatrix.symm (recordState p z hGram i).1 :=
  conditionalRecord_eq p z i

/-- The phase-sensitive measurement applied to the physical BR output recovers every
basis label with unit probability. The complementary outcome has probability zero. -/
theorem joint_decoder_born (p : Bath → ℝ) (z : Bath → System → ℂ)
    (hGram : (weightedColumns p z)ᴴ * weightedColumns p z = 1)
    (i : System) (o : Option System) :
    (Matrix.trace (orthogonalReadout (recordEmbedding p z) o *
      conditionalRecord p (phaseUnitary z) i)).re = if o = some i then 1 else 0 := by
  rw [conditionalRecord_eq]
  simpa only [recordEmbedding_entry] using
    orthogonalReadout_born (recordEmbedding p z) (recordEmbedding_isometry p z hGram) i o

/-- An observable bridge for one Gibbs preparation and one permitted physical interaction. -/
structure BasisObservation (p : Bath → ℝ) (U : Joint) where
  preparation : DensityState BathReference
  preparation_eq : CStarMatrix.ofMatrix.symm preparation.1 = rankOneDensity (purificationVector p)
  record : System → DensityState BathReference
  fromOutput : ∀ i, conditionalRecord p U i = CStarMatrix.ofMatrix.symm (record i).1
  localMarginals : ∀ i,
    partialTraceRight (conditionalRecord p U i) = diagonalReal p ∧
      partialTraceLeft (conditionalRecord p U i) = diagonalReal p
  energyReadout : ∀ (i : System) (b r : Bath),
    (Matrix.trace (basisProjector (b, r) * conditionalRecord p U i)).re =
      if b = r then p b else 0
  effect : Option System → Matrix BathReference BathReference ℂ
  effect_projection : ∀ o, IsStarProjection (effect o)
  effect_complete : ∑ o, effect o = 1
  labelReadout : ∀ i o,
    (Matrix.trace (effect o * conditionalRecord p U i)).re = if o = some i then 1 else 0

/-- The bridge uses only normalized nonnegative weights, unit phases and the
weighted Gram identity. Gibbs feasibility supplies these hypotheses below. -/
def basisObservation (p : Bath → ℝ) (hp : ∀ b, 0 ≤ p b) (hsum : ∑ b, p b = 1)
    (z : Bath → System → ℂ) (hz : ∀ b i, Complex.normSq (z b i) = 1)
    (hGram : (weightedColumns p z)ᴴ * weightedColumns p z = 1) :
    BasisObservation p (phaseUnitary z) where
  preparation := purifiedBath p hp hsum
  preparation_eq := rfl
  record := recordState p z hGram
  fromOutput := conditionalRecord_state p z hGram
  localMarginals := conditionalRecord_marginals p hp z hz
  energyReadout := joint_basis_born p hp z hz
  effect := orthogonalReadout (recordEmbedding p z)
  effect_projection := orthogonalReadout_projection _ (recordEmbedding_isometry p z hGram)
  effect_complete := orthogonalReadout_complete _
  labelReadout := joint_decoder_born p z hGram

/-- At any feasible fixed Gibbs law there is a single phase unitary giving both
the mixed-bath pinching and the purified-bath basis observation. -/
theorem fixed_bath_observable_bridge (β : ℝ) (E : Bath → ℝ) (hE : Function.Injective E)
    (hFeasible : ∃ U : Matrix.unitaryGroup (System × Bath) ℂ,
      IsEnergyConserving (fun _ => 0) E (U : Joint) ∧
      ∀ ρ : DensityState System,
        operation β E (U : Joint) (inputMatrix ρ) = projectiveReadout (inputMatrix ρ)) :
    ∃ U : Matrix.unitaryGroup (System × Bath) ℂ,
      IsEnergyConserving (fun _ => 0) E (U : Joint) ∧
      (∀ X : Qutrit, operation β E (U : Joint) X = projectiveReadout X) ∧
      Nonempty (BasisObservation (gibbsWeight β E) (U : Joint)) := by
  obtain ⟨z, hz, hGram⟩ := (fixed_bath_pinching_iff β E hE).mp hFeasible
  obtain ⟨hU, henergy, hpinch, _⟩ := phase_realization β E hE z hz hGram
  exact ⟨⟨phaseUnitary z, hU⟩, henergy, hpinch,
    ⟨basisObservation _ (fun b => (gibbsWeight_pos β E b).le)
      (sum_gibbsWeight β E) z hz hGram⟩⟩

/-- The verified cubic example `(29,27,25,19)/100` yields the observable
bridge with one fixed injective energy list for each positive inverse temperature. -/
theorem feasible_gibbs_observer (β : ℝ) (hβ : 0 < β) :
    ∃ E : Bath → ℝ, Function.Injective E ∧ gibbsWeight β E = D5.S3.Quantum.Measurements.ThreeDistinguishabilityCubic.feasibleWeights ∧
      ∃ U : Matrix.unitaryGroup (System × Bath) ℂ,
        IsEnergyConserving (fun _ => 0) E (U : Joint) ∧
        (∀ X : Qutrit, operation β E (U : Joint) X = projectiveReadout X) ∧
        Nonempty (BasisObservation (gibbsWeight β E) (U : Joint)) := by
  obtain ⟨E, hE, hweights, hFeasible⟩ := feasible_fixed_bath_example β hβ
  exact ⟨E, hE, hweights, fixed_bath_observable_bridge β E hE hFeasible⟩

end D5.S3.Quantum.Decoherence.FourLevelBathObserver
