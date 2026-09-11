/- GID: D5/S3/ConceptDynamics/CausalMoments/MediatorPricingRestriction
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/CausalMoments/MediatorPricingRestriction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Fixing selected outcome-response coordinates preserves the actual mediator pricing objective as an explicit constant plus a normalized residual-coupling pricing problem. -/

import D5.S3.ConceptDynamics.CausalMoments.BipartiteMediatorPricing

/-!
The input mediator law is fixed. K selects coordinates of a deterministic
outcome response table, not observed events on which the source law is
conditioned. Removed pairs are redirected to diagonal pairs to retain the
existing normalized law API; all their actual objective contributions are
retained by the offset and multiplier correction. The residual law is a
computational representation and is never substituted for the original SCM.

The proof reuses the merged BipartiteMediatorPricing, the original rational
pushforward, and pushforward_linearObjective. The finite conditioning idea is
standard in graph-cut/modulator algorithms; the original coefficient identity
and full response reconstruction are the additional causal obligations here.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.CausalMoments.MediatorPricingRestriction

open scoped BigOperators
open D5.S0.Certificates.LinearObjectiveDual
open D5.S3.ConceptDynamics.PartialIdentification.MarkovianResponseLawFactorization
open D5.S3.ConceptDynamics.CausalMoments.FiniteMomentSparseLaw
open D5.S3.ConceptDynamics.CausalMoments.CompleteMediatorCutSharpBounds
open D5.S3.ConceptDynamics.CausalMoments.BipartiteMediatorPricing

variable {M : Type*} [Fintype M] [DecidableEq M]

/-- Extend a branch assignment by false outside its selected coordinate set. -/
def pinTable (K : Finset M) (branch : K → Bool) : M → Bool :=
  fun i => if hi : i ∈ K then branch ⟨i, hi⟩ else false

/-- Reassemble one original complete outcome-response table. -/
def clampTable (K : Finset M) (branch : K → Bool) (table : M → Bool) : M → Bool :=
  fun i => if i ∈ K then pinTable K branch i else table i

/-- Every original column occurs in the branch determined by its own restriction. -/
theorem clampTable_restrict (K : Finset M) (table : M → Bool) :
    clampTable K (fun i : K => table i.1) table = table := by
  funext i
  by_cases hi : i ∈ K <;> simp [clampTable, pinTable, hi]

/-- Preserve free/free pairs; redirect all other mass to a harmless diagonal. -/
def absorbPair (K : Finset M) (pair : M × M) : M × M :=
  if pair.1 ∉ K ∧ pair.2 ∉ K then pair else (pair.1, pair.1)

/-- A normalized computational law on the unchanged mediator-pair carrier. -/
noncomputable def residualCoupling (coupling : FiniteResponseLaw (M × M)) (K : Finset M) :
    FiniteResponseLaw (M × M) :=
  pushforwardResponseLaw coupling (absorbPair K)

private theorem absorbPair_eq_offDiagonal (K : Finset M) (i j : M) (different : i ≠ j)
    (pair : M × M) :
    absorbPair K pair = (i, j) ↔ pair = (i, j) ∧ i ∉ K ∧ j ∉ K := by
  unfold absorbPair
  split_ifs with free
  · constructor
    · intro equal
      subst pair
      exact ⟨rfl, free⟩
    · rintro ⟨equal, _⟩
      exact equal
  · constructor
    · intro equal
      have same : i = j := (congrArg Prod.fst equal).symm.trans (congrArg Prod.snd equal)
      exact (different same).elim
    · rintro ⟨equal, hi, hj⟩
      subst pair
      exact (free ⟨hi, hj⟩).elim

/-- Off-diagonal residual masses are exactly the original free/free masses. -/
theorem residualCoupling_offDiagonal (coupling : FiniteResponseLaw (M × M))
    (K : Finset M) (i j : M) (different : i ≠ j) :
    (residualCoupling coupling K).mass (i, j) =
      if i ∉ K ∧ j ∉ K then coupling.mass (i, j) else 0 := by
  change (∑ pair : M × M, if absorbPair K pair = (i, j) then coupling.mass pair else 0) = _
  simp_rw [absorbPair_eq_offDiagonal K i j different]
  by_cases free : i ∉ K ∧ j ∉ K <;> simp [free]

/-- Exact graph contract: only the off-diagonal support outside K must be bipartite. -/
theorem residualCoupling_bipartite_iff (coupling : FiniteResponseLaw (M × M))
    (K : Finset M) (color : M → Bool) :
    OffDiagonalBipartite (residualCoupling coupling K) color ↔
      ∀ i j, i ∉ K → j ∉ K → i ≠ j → coupling.mass (i, j) ≠ 0 → color i ≠ color j := by
  constructor
  · intro h i j hi hj different active
    apply h i j different
    rw [residualCoupling_offDiagonal coupling K i j different, if_pos (And.intro hi hj)]
    exact active
  · intro h i j different active
    rw [residualCoupling_offDiagonal coupling K i j different] at active
    by_cases free : i ∉ K ∧ j ∉ K
    · exact h i j free.1 free.2 different (by simpa only [if_pos free] using active)
    · simp only [if_neg free, ne_eq, not_true_eq_false] at active

private def bit (value : Bool) : ℚ := if value then 1 else 0
private def edge (first second : Bool) : ℚ :=
  if first = false ∧ second = true then 1 else 0
private def edgeSum (coupling : FiniteResponseLaw (M × M)) (table : M → Bool) : ℚ :=
  linearObjective (fun pair => edge (table pair.1) (table pair.2)) coupling.mass

private def incomingFixedZero (coupling : FiniteResponseLaw (M × M))
    (K : Finset M) (branch : K → Bool) (i : M) : ℚ :=
  ∑ j, if j ∈ K ∧ i ∉ K ∧ pinTable K branch j = false then coupling.mass (j, i) else 0

private def outgoingFixedOne (coupling : FiniteResponseLaw (M × M))
    (K : Finset M) (branch : K → Bool) (i : M) : ℚ :=
  ∑ j, if i ∉ K ∧ j ∈ K ∧ pinTable K branch j = true then coupling.mass (i, j) else 0

/-- Original multiplier plus the two oriented fixed/free edge corrections. -/
def branchMultiplier (coupling : FiniteResponseLaw (M × M)) (K : Finset M)
    (branch : K → Bool) (multiplier : M → ℚ) (i : M) : ℚ :=
  (if i ∈ K then 0 else multiplier i) + outgoingFixedOne coupling K branch i -
    incomingFixedZero coupling K branch i

/-- The offset is the actual original price with all free coordinates false. -/
def branchOffset (coupling : FiniteResponseLaw (M × M)) (K : Finset M)
    (branch : K → Bool) (multiplier : M → ℚ) : ℚ :=
  completeMediatorPricingScore coupling multiplier (pinTable K branch)

private theorem edge_restriction (K : Finset M) (branch : K → Bool) (table : M → Bool)
    (i j : M) :
    edge (clampTable K branch table i) (clampTable K branch table j) =
      edge (pinTable K branch i) (pinTable K branch j) +
      edge (table (absorbPair K (i, j)).1) (table (absorbPair K (i, j)).2) +
      (if i ∈ K ∧ j ∉ K ∧ pinTable K branch i = false then bit (table j) else 0) -
      (if i ∉ K ∧ j ∈ K ∧ pinTable K branch j = true then bit (table i) else 0) := by
  have outside_i : i ∉ K → pinTable K branch i = false := by
    intro hi
    simp [pinTable, hi]
  have outside_j : j ∉ K → pinTable K branch j = false := by
    intro hj
    simp [pinTable, hj]
  by_cases hi : i ∈ K <;> by_cases hj : j ∈ K <;>
    cases hp : pinTable K branch i <;> cases hq : pinTable K branch j <;>
    cases ht : table i <;> cases hu : table j <;>
    simp_all [clampTable, absorbPair, edge, bit]

private theorem edgeSum_restriction (coupling : FiniteResponseLaw (M × M))
    (K : Finset M) (branch : K → Bool) (table : M → Bool) :
    edgeSum coupling (clampTable K branch table) =
      edgeSum coupling (pinTable K branch) + edgeSum (residualCoupling coupling K) table +
      (∑ i, incomingFixedZero coupling K branch i * bit (table i)) -
      (∑ i, outgoingFixedOne coupling K branch i * bit (table i)) := by
  have residual : edgeSum (residualCoupling coupling K) table =
      ∑ i, ∑ j, edge (table (absorbPair K (i, j)).1)
        (table (absorbPair K (i, j)).2) * coupling.mass (i, j) := by
    unfold edgeSum residualCoupling
    rw [pushforward_linearObjective]
    simp only [linearObjective, Fintype.sum_prod_type]
  have incoming : (∑ i, incomingFixedZero coupling K branch i * bit (table i)) =
      ∑ i, ∑ j, (if i ∈ K ∧ j ∉ K ∧ pinTable K branch i = false
        then bit (table j) else 0) * coupling.mass (i, j) := by
    unfold incomingFixedZero
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> ring
  have outgoing : (∑ i, outgoingFixedOne coupling K branch i * bit (table i)) =
      ∑ i, ∑ j, (if i ∉ K ∧ j ∈ K ∧ pinTable K branch j = true
        then bit (table i) else 0) * coupling.mass (i, j) := by
    unfold outgoingFixedOne
    simp_rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> ring
  rw [residual, incoming, outgoing]
  unfold edgeSum linearObjective
  simp only [Fintype.sum_prod_type]
  simp_rw [edge_restriction K branch table]
  simp only [add_mul, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib]

/-- Exact branch equality on every original table, with no bipartite premise.
There is no discarded probability mass or branch-dependent renormalization. -/
theorem pricing_restriction_identity (coupling : FiniteResponseLaw (M × M))
    (K : Finset M) (branch : K → Bool) (multiplier : M → ℚ) (table : M → Bool) :
    completeMediatorPricingScore coupling multiplier (clampTable K branch table) =
      branchOffset coupling K branch multiplier +
      completeMediatorPricingScore (residualCoupling coupling K)
        (branchMultiplier coupling K branch multiplier) table := by
  have unary : (∑ i, multiplier i * bit (clampTable K branch table i)) =
      (∑ i, multiplier i * bit (pinTable K branch i)) +
      ∑ i, (if i ∈ K then 0 else multiplier i) * bit (table i) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i ∈ K <;> simp [clampTable, pinTable, bit, hi]
  have correction : (∑ i, branchMultiplier coupling K branch multiplier i * bit (table i)) =
      (∑ i, (if i ∈ K then 0 else multiplier i) * bit (table i)) +
      (∑ i, outgoingFixedOne coupling K branch i * bit (table i)) -
      (∑ i, incomingFixedZero coupling K branch i * bit (table i)) := by
    simp only [branchMultiplier, add_mul, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  change edgeSum coupling (clampTable K branch table) -
      (∑ i, multiplier i * bit (clampTable K branch table i)) =
    (edgeSum coupling (pinTable K branch) - (∑ i, multiplier i * bit (pinTable K branch i))) +
      (edgeSum (residualCoupling coupling K) table -
        (∑ i, branchMultiplier coupling K branch multiplier i * bit (table i)))
  rw [edgeSum_restriction, unary, correction]
  ring

#print axioms residualCoupling_bipartite_iff
#print axioms pricing_restriction_identity

end D5.S3.ConceptDynamics.CausalMoments.MediatorPricingRestriction
