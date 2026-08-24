/- GID: D5/S3/ConceptDynamics/DefinitionEscape/WeightedResidualCoverage
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite weighted residual capture is a normalized monotone submodular set function with exact and approximate cover boundaries. -/

import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.Omega

/- Library-search audit trail (2026-08-24):
   * DECT identifies finite definition selection with weighted coverage of target
     residual pairs.
   * Repository search found no Lean theorem packaging the weighted partition
     identity, insertion law, diminishing returns, and normalized
     submodularity for an arbitrary finite separation relation.
   * This unit is pure finite combinatorics. It contains no allocation policy,
     proposal type, workflow stage, or scientific-worth interpretation. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.DefinitionEscape.WeightedResidualCoverage

/-- A residual witness is covered when some selected definition separates it. -/
def CoveredBy
    {Definition Residual : Type*} [DecidableEq Definition]
    (separates : Definition → Residual → Bool)
    (chosen : Finset Definition) (residual : Residual) : Bool :=
  chosen.any (fun definition => separates definition residual)

/-- The finite residual universe is covered pointwise. -/
def ExactCover
    {Definition Residual : Type*} [DecidableEq Definition]
    (residuals : Finset Residual)
    (separates : Definition → Residual → Bool)
    (chosen : Finset Definition) : Prop :=
  ∀ residual ∈ residuals, CoveredBy separates chosen residual = true

/-- Total weight of residual witnesses captured by a definition set. -/
def WeightedGain
    {Definition Residual : Type*} [DecidableEq Definition]
    (residuals : Finset Residual) (weight : Residual → Nat)
    (separates : Definition → Residual → Bool)
    (chosen : Finset Definition) : Nat :=
  ∑ residual in residuals,
    if CoveredBy separates chosen residual then weight residual else 0

/-- Total weight left uncovered. -/
def UncoveredWeight
    {Definition Residual : Type*} [DecidableEq Definition]
    (residuals : Finset Residual) (weight : Residual → Nat)
    (separates : Definition → Residual → Bool)
    (chosen : Finset Definition) : Nat :=
  ∑ residual in residuals,
    if CoveredBy separates chosen residual then 0 else weight residual

/-- Marginal weighted capture of one additional definition. -/
def MarginalGain
    {Definition Residual : Type*} [DecidableEq Definition]
    (residuals : Finset Residual) (weight : Residual → Nat)
    (separates : Definition → Residual → Bool)
    (chosen : Finset Definition) (definition : Definition) : Nat :=
  ∑ residual in residuals,
    if (!CoveredBy separates chosen residual) &&
        separates definition residual then
      weight residual
    else 0

/-- Approximate cover leaves at most the declared residual mass. -/
def ApproximateCover
    {Definition Residual : Type*} [DecidableEq Definition]
    (residuals : Finset Residual) (weight : Residual → Nat)
    (separates : Definition → Residual → Bool)
    (chosen : Finset Definition) (tolerance : Nat) : Prop :=
  UncoveredWeight residuals weight separates chosen ≤ tolerance

/-- Boolean coverage is equivalent to existential separation by a selected
definition. -/
theorem coveredBy_eq_true_iff
    {Definition Residual : Type*} [DecidableEq Definition]
    (separates : Definition → Residual → Bool)
    (chosen : Finset Definition) (residual : Residual) :
    CoveredBy separates chosen residual = true ↔
      ∃ definition ∈ chosen, separates definition residual = true := by
  simp [CoveredBy]

/-- Enlarging a definition set preserves every covered residual. -/
theorem coveredBy_mono
    {Definition Residual : Type*} [DecidableEq Definition]
    (separates : Definition → Residual → Bool)
    {smaller larger : Finset Definition} (subset : smaller ⊆ larger)
    (residual : Residual)
    (covered : CoveredBy separates smaller residual = true) :
    CoveredBy separates larger residual = true := by
  rw [coveredBy_eq_true_iff] at covered ⊢
  rcases covered with ⟨definition, inSmaller, separatesResidual⟩
  exact ⟨definition, subset inSmaller, separatesResidual⟩

/-- If an enlarged set does not cover a residual, neither did the smaller set. -/
theorem coveredBy_eq_false_of_subset
    {Definition Residual : Type*} [DecidableEq Definition]
    (separates : Definition → Residual → Bool)
    {smaller larger : Finset Definition} (subset : smaller ⊆ larger)
    (residual : Residual)
    (notCovered : CoveredBy separates larger residual = false) :
    CoveredBy separates smaller residual = false := by
  cases smallerCovered : CoveredBy separates smaller residual with
  | false => rfl
  | true =>
      have largerCovered :=
        coveredBy_mono separates subset residual smallerCovered
      simp [notCovered] at largerCovered

/-- Captured and uncaptured weights partition the residual universe. -/
theorem weightedGain_add_uncoveredWeight
    {Definition Residual : Type*} [DecidableEq Definition]
    (residuals : Finset Residual) (weight : Residual → Nat)
    (separates : Definition → Residual → Bool)
    (chosen : Finset Definition) :
    WeightedGain residuals weight separates chosen +
        UncoveredWeight residuals weight separates chosen =
      ∑ residual in residuals, weight residual := by
  rw [WeightedGain, UncoveredWeight, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro residual inResiduals
  cases covered : CoveredBy separates chosen residual <;> simp [covered]

/-- Weighted capture is monotone under inclusion. -/
theorem weightedGain_mono
    {Definition Residual : Type*} [DecidableEq Definition]
    (residuals : Finset Residual) (weight : Residual → Nat)
    (separates : Definition → Residual → Bool)
    {smaller larger : Finset Definition} (subset : smaller ⊆ larger) :
    WeightedGain residuals weight separates smaller ≤
      WeightedGain residuals weight separates larger := by
  apply Finset.sum_le_sum
  intro residual inResiduals
  cases smallerCovered : CoveredBy separates smaller residual with
  | false => simp [WeightedGain, smallerCovered]
  | true =>
      have largerCovered :=
        coveredBy_mono separates subset residual smallerCovered
      simp [WeightedGain, smallerCovered, largerCovered]

/-- Remaining residual weight is antitone under inclusion. -/
theorem uncoveredWeight_antitone
    {Definition Residual : Type*} [DecidableEq Definition]
    (residuals : Finset Residual) (weight : Residual → Nat)
    (separates : Definition → Residual → Bool)
    {smaller larger : Finset Definition} (subset : smaller ⊆ larger) :
    UncoveredWeight residuals weight separates larger ≤
      UncoveredWeight residuals weight separates smaller := by
  apply Finset.sum_le_sum
  intro residual inResiduals
  cases largerCovered : CoveredBy separates larger residual with
  | true => simp [UncoveredWeight, largerCovered]
  | false =>
      have smallerNotCovered :=
        coveredBy_eq_false_of_subset separates subset residual largerCovered
      simp [UncoveredWeight, largerCovered, smallerNotCovered]

/-- Inserting one definition adds exactly its marginal gain. -/
theorem weightedGain_insert
    {Definition Residual : Type*} [DecidableEq Definition]
    (residuals : Finset Residual) (weight : Residual → Nat)
    (separates : Definition → Residual → Bool)
    (chosen : Finset Definition) (definition : Definition) :
    WeightedGain residuals weight separates (insert definition chosen) =
      WeightedGain residuals weight separates chosen +
        MarginalGain residuals weight separates chosen definition := by
  rw [WeightedGain, WeightedGain, MarginalGain,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro residual inResiduals
  cases oldCovered : CoveredBy separates chosen residual <;>
    cases definitionSeparates : separates definition residual <;>
      simp [CoveredBy, oldCovered, definitionSeparates]

/-- Diminishing returns: the same definition cannot capture more after the
selected set has grown. -/
theorem marginalGain_antitone
    {Definition Residual : Type*} [DecidableEq Definition]
    (residuals : Finset Residual) (weight : Residual → Nat)
    (separates : Definition → Residual → Bool)
    {smaller larger : Finset Definition} (subset : smaller ⊆ larger)
    (definition : Definition) :
    MarginalGain residuals weight separates larger definition ≤
      MarginalGain residuals weight separates smaller definition := by
  apply Finset.sum_le_sum
  intro residual inResiduals
  cases largerCovered : CoveredBy separates larger residual with
  | true => simp [MarginalGain, largerCovered]
  | false =>
      have smallerNotCovered :=
        coveredBy_eq_false_of_subset separates subset residual largerCovered
      simp [MarginalGain, largerCovered, smallerNotCovered]

/-- Normalized submodularity in four-term form. -/
theorem weightedGain_submodular_insert
    {Definition Residual : Type*} [DecidableEq Definition]
    (residuals : Finset Residual) (weight : Residual → Nat)
    (separates : Definition → Residual → Bool)
    {smaller larger : Finset Definition} (subset : smaller ⊆ larger)
    (definition : Definition) :
    WeightedGain residuals weight separates (insert definition larger) +
        WeightedGain residuals weight separates smaller ≤
      WeightedGain residuals weight separates (insert definition smaller) +
        WeightedGain residuals weight separates larger := by
  rw [weightedGain_insert, weightedGain_insert]
  have diminishing :=
    marginalGain_antitone residuals weight separates subset definition
  omega

/-- Exact pointwise coverage has zero uncovered weight. -/
theorem exactCover_uncoveredWeight_eq_zero
    {Definition Residual : Type*} [DecidableEq Definition]
    (residuals : Finset Residual) (weight : Residual → Nat)
    (separates : Definition → Residual → Bool)
    (chosen : Finset Definition)
    (exact : ExactCover residuals separates chosen) :
    UncoveredWeight residuals weight separates chosen = 0 := by
  unfold UncoveredWeight
  apply Finset.sum_eq_zero
  intro residual inResiduals
  simp [exact residual inResiduals]

/-- Exact coverage is approximate at every tolerance. -/
theorem exactCover_implies_approximate
    {Definition Residual : Type*} [DecidableEq Definition]
    (residuals : Finset Residual) (weight : Residual → Nat)
    (separates : Definition → Residual → Bool)
    (chosen : Finset Definition) (tolerance : Nat)
    (exact : ExactCover residuals separates chosen) :
    ApproximateCover residuals weight separates chosen tolerance := by
  unfold ApproximateCover
  rw [exactCover_uncoveredWeight_eq_zero
    residuals weight separates chosen exact]
  exact Nat.zero_le tolerance

/-- Approximate coverage is monotone in its tolerance. -/
theorem approximateCover_mono_tolerance
    {Definition Residual : Type*} [DecidableEq Definition]
    (residuals : Finset Residual) (weight : Residual → Nat)
    (separates : Definition → Residual → Bool)
    (chosen : Finset Definition) {smaller larger : Nat}
    (toleranceMono : smaller ≤ larger)
    (approximate :
      ApproximateCover residuals weight separates chosen smaller) :
    ApproximateCover residuals weight separates chosen larger :=
  le_trans approximate toleranceMono

example :
    let residuals : Finset Bool := {false, true}
    let weight : Bool → Nat := fun residual => if residual then 3 else 1
    let separates : Bool → Bool → Bool :=
      fun definition residual => definition == residual
    WeightedGain residuals weight separates {true} = 3 := by
  decide

#print axioms weightedGain_submodular_insert
#print axioms weightedGain_insert
#print axioms exactCover_implies_approximate

end D5.S3.ConceptDynamics.DefinitionEscape.WeightedResidualCoverage
