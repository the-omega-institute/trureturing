/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveControlledRecord
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveControlledRecord
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [lake/module/D5.S3.Quantum.EnvironmentRecords.ControlledPureRecord, lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPS.Records.PrimitiveComplementaryRecordRate]
   utility: none
   digest: Exact controlled-channel distance at the primitive periodic two-site collision. -/

import D5.S3.Quantum.EnvironmentRecords.ControlledPureRecord
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Records.PrimitiveComplementaryRecordRate

/-!
# Controlled record channel of the primitive periodic collision

The address controls the two literal normalized ring vectors. The visible
register consists of sites zero and one, and `m` counts the hidden sites.
-/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Quantum.TensorNetworks.PrimitiveControlledRecord

open _root_.Matrix
open scoped CStarAlgebra _root_.Matrix
open D5.S3.Quantum.EnvironmentRecords.ControlledPureRecord
open D5.S3.Quantum.Foundation.FiniteDiamondDistance (diamondDistance)
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Foundation.FiniteTraceDistance (traceNorm)
open D5.S3.Quantum.Information.PartialTraceMutualInformation (partialTraceLeft partialTraceRight)
open PeriodicMPSParentIntersection (Word)
open PeriodicMPSPrimitiveCollision
open ComplementaryRecordRate (collisionFlattening collisionFlattening_cross
  collisionFlattening_common_visible collisionFlattening_overlap)

private abbrev Pair := Fin 2 × Fin 2

/-- The periodic amplitudes in the address order zero, one. -/
def records (m : ℕ) : Records Pair (Word m) :=
  fun i => collisionFlattening (finTwoEquiv i) m

theorem records_common_visible (m : ℕ) (hm : 5 ≤ m) (i : Address) :
    records m i * (records m i)ᴴ = collisionMarginal :=
  collisionFlattening_common_visible (finTwoEquiv i) m hm

theorem records_normalized (m : ℕ) (hm : 5 ≤ m) : Normalized (records m) := by
  intro i
  rw [records_common_visible m hm i, collision_marginal_trace]

theorem records_cross (m : ℕ) : cross (records m) = collisionNormalizedCross m :=
  collisionFlattening_cross m

/-- The ordinary channel retaining the address and the adjacent visible pair. -/
def jointChannel (m : ℕ) (hm : 5 ≤ m) : QuantumChannel Address (Address × Pair) :=
  readoutChannel (records m) (records_normalized m hm)

/-- The ordinary channel that completely dephases the address and attaches
the same adjacent-pair state for both address values. -/
def dephasedChannel (m : ℕ) (hm : 5 ≤ m) : QuantumChannel Address (Address × Pair) :=
  readoutChannel (withHiddenAddress (records m))
    (withHiddenAddress_normalized (records m) (records_normalized m hm))

theorem jointChannel_eq_partialTrace (m : ℕ) (hm : 5 ≤ m) (X : Matrix Address Address ℂ) :
    CStarMatrix.ofMatrix.symm
      ((jointChannel m hm).toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) =
        partialTraceRight
          (controlledIsometry (records m) * X * (controlledIsometry (records m))ᴴ) := by
  rw [jointChannel, readoutChannel_apply, readoutMap_eq_partialTrace]

theorem dephasedChannel_apply (m : ℕ) (hm : 5 ≤ m) (X : Matrix Address Address ℂ)
    (i j : Address) (p q : Pair) :
    CStarMatrix.ofMatrix.symm
      ((dephasedChannel m hm).toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) (i, p) (j, q) =
      if i = j then collisionMarginal p q * X i i else 0 := by
  rw [dephasedChannel, readoutChannel_apply]
  exact dephased_apply (records m) collisionMarginal (records_common_visible m hm) X i j p q

theorem jointChannel_coherence (m : ℕ) (hm : 5 ≤ m) (X : Matrix Address Address ℂ)
    (p q : Pair) :
    CStarMatrix.ofMatrix.symm
      ((jointChannel m hm).toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) (0, p) (1, q) =
      collisionNormalizedCross m p q * X 0 1 := by
  rw [jointChannel, readoutChannel_apply, readoutMap_apply, ← records_cross m] <;> rfl

/-- For every address input, the two channels have the same state on the
observed pair whenever the input has trace one. -/
theorem visible_pair_agrees (m : ℕ) (hm : 5 ≤ m) (X : Matrix Address Address ℂ) :
    partialTraceLeft (readoutMap (records m) X) = X.trace • collisionMarginal ∧
    partialTraceLeft (readoutMap (withHiddenAddress (records m)) X) =
      X.trace • collisionMarginal :=
  visible_agreement (records m) collisionMarginal (records_common_visible m hm) X

/-- Discarding the visible pair retains only the actual global-record overlap. -/
theorem address_coherence (m : ℕ) (X : Matrix Address Address ℂ) :
    partialTraceRight (readoutMap (records m) X) 0 1 =
      collisionNormalizedOverlap (2 + m) * X 0 1 := by
  rw [trace_visible_apply]
  change (collisionFlattening false m * (collisionFlattening true m)ᴴ).trace * X 0 1 = _
  rw [collisionFlattening_overlap]

theorem amplified_bound (m : ℕ) (hm : 5 ≤ m) {r : Type} [Fintype r] [DecidableEq r]
    (X : Matrix (r × Address) (r × Address) ℂ) :
    traceNorm (referenceDifference (records m) (records_normalized m hm) X) ≤
      traceNorm (collisionNormalizedCross m) * traceNorm X := by
  simpa only [records_cross] using
    referenceDifference_le (records m) (records_normalized m hm) X

theorem product_attains (m : ℕ) (hm : 5 ≤ m) {r : Type} [Fintype r] [DecidableEq r]
    (σ : DensityState r) :
    traceNorm (referenceDifference (records m) (records_normalized m hm)
      (CStarMatrix.ofMatrix.symm (productInput σ).1)) = traceNorm (collisionNormalizedCross m) := by
  simpa only [records_cross] using
    referenceDifference_product (records m) (records_normalized m hm) σ

theorem plus_attains (m : ℕ) :
    let X := CStarMatrix.ofMatrix.symm plusState.1
    traceNorm (readoutMap (records m) X - readoutMap (withHiddenAddress (records m)) X) =
      traceNorm (collisionNormalizedCross m) := by
  simpa only [records_cross] using readoutDifference_plus (records m)

theorem reconstruction_lower (m : ℕ) (Y : Matrix (Address × Pair) (Address × Pair) ℂ) :
    let X := CStarMatrix.ofMatrix.symm plusState.1
    traceNorm (collisionNormalizedCross m) / 2 ≤
      max (traceNorm (readoutMap (records m) X - Y))
        (traceNorm (readoutMap (withHiddenAddress (records m)) X - Y)) := by
  simpa only [records_cross] using
    D5.S3.Quantum.EnvironmentRecords.ControlledPureRecord.reconstruction_lower (records m) Y

/-- The exact finite-length unhalved diamond distance for every ring of length at least seven. -/
theorem jointChannel_distance (m : ℕ) (hm : 5 ≤ m) :
    diamondDistance (jointChannel m hm) (dephasedChannel m hm) =
      traceNorm (collisionNormalizedCross m) := by
  unfold jointChannel dephasedChannel
  rw [diamondDistance_readout_dephased, records_cross]

end D5.S3.Quantum.TensorNetworks.PrimitiveControlledRecord
