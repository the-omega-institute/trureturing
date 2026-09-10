/- GID: D5/S3/ConceptDynamics/CausalMoments/SeparatorMediatorPricing
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/CausalMoments/SeparatorMediatorPricing
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Complete certificates over all separator assignments turn the existing bipartite min-cut oracle into exact pricing and full causal master bounds on non-bipartite mediator supports. -/

import D5.S3.ConceptDynamics.CausalMoments.MediatorPricingRestriction

/-!
There are exactly 2^K.card branches, including the unique empty assignment when
K is empty. Each branch carries the existing rational flow/cut data. The checker
quantifies over the complete function carrier K -> Bool, not a producer-selected
list of branches. A supplied best branch must dominate every recomputed branch
value, and its cut is lifted to an original complete outcome response table.

The graph search is a standard modulator construction. Jaffke--Morelle--Sau--
Thilikos (IPEC 2023; JCSS 156, 103722, 2026) studies the broader bipartite-treewidth
framework for Maximum Weighted Cut. Here the substantive interface is exact
reassembly into the fixed-coupling causal pricing/master problem from Arroyo et
al.'s column-generation direction. No general unknown-coupling optimum, optimal
separator search, or polynomial bound on column-generation iterations is claimed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.CausalMoments.SeparatorMediatorPricing

open scoped BigOperators
open D5.S0.Certificates.LinearObjectiveDual
open D5.S0.Certificates.RationalSTCutCertificate
open D5.S3.ConceptDynamics.PartialIdentification.MarkovianResponseLawFactorization
open D5.S3.ConceptDynamics.CausalMoments.CompleteMediatorCutSharpBounds
open D5.S3.ConceptDynamics.CausalMoments.BipartiteMediatorPricing
open D5.S3.ConceptDynamics.CausalMoments.MediatorPricingRestriction

variable {M : Type*} [Fintype M] [DecidableEq M]

/-- Raw total family of flow certificates. Its type cannot omit a separator assignment. -/
structure SeparatorPricingCertificate (M : Type*) (K : Finset M) where
  color : M → Bool
  flows : (K → Bool) → STCutCertificate M
  winner : K → Bool

/-- Original-scale value of one branch, including its fixed-coordinate offset. -/
noncomputable def branchValue (coupling : FiniteResponseLaw (M × M)) (K : Finset M)
    (multiplier : M → ℚ) (certificate : SeparatorPricingCertificate M K)
    (branch : K → Bool) : ℚ :=
  branchOffset coupling K branch multiplier +
    certifiedPricingValue (residualCoupling coupling K) certificate.color
      (branchMultiplier coupling K branch multiplier) (certificate.flows branch)

/-- Validate every full branch and compare the proposed winner with every value. -/
noncomputable def checkSeparatorPricing (coupling : FiniteResponseLaw (M × M)) (K : Finset M)
    (multiplier : M → ℚ) (certificate : SeparatorPricingCertificate M K) : Bool :=
  @decide
    ((∀ branch : K → Bool,
      checkBipartitePricing (residualCoupling coupling K) certificate.color
        (branchMultiplier coupling K branch multiplier) (certificate.flows branch) = true) ∧
    (∀ branch : K → Bool,
      branchValue coupling K multiplier certificate branch ≤
        branchValue coupling K multiplier certificate certificate.winner))
    (by infer_instance)

/-- Reassemble the maximizing branch and its flipped residual minimum cut. -/
def winningTable (K : Finset M) (certificate : SeparatorPricingCertificate M K) : M → Bool :=
  clampTable K certificate.winner
    (flipTable certificate.color (certificate.flows certificate.winner).side)

/-- Acceptance produces an attaining original column and bounds every original
column. The proof selects each competitor's actual restriction to K. -/
theorem checkSeparatorPricing_sound (coupling : FiniteResponseLaw (M × M))
    (K : Finset M) (multiplier : M → ℚ) (certificate : SeparatorPricingCertificate M K)
    (accepted : checkSeparatorPricing coupling K multiplier certificate = true) :
    completeMediatorPricingScore coupling multiplier (winningTable K certificate) =
      branchValue coupling K multiplier certificate certificate.winner ∧
    IsGreatest (Set.range (completeMediatorPricingScore coupling multiplier))
      (branchValue coupling K multiplier certificate certificate.winner) := by
  have checks :
      (∀ branch : K → Bool,
        checkBipartitePricing (residualCoupling coupling K) certificate.color
          (branchMultiplier coupling K branch multiplier) (certificate.flows branch) = true) ∧
      (∀ branch : K → Bool, branchValue coupling K multiplier certificate branch ≤
        branchValue coupling K multiplier certificate certificate.winner) := by
    exact of_decide_eq_true accepted
  have each (branch : K → Bool) :=
    checked_pricing_isGreatest (residualCoupling coupling K) certificate.color
      (branchMultiplier coupling K branch multiplier) (certificate.flows branch) (checks.1 branch)
  have attains : completeMediatorPricingScore coupling multiplier (winningTable K certificate) =
      branchValue coupling K multiplier certificate certificate.winner := by
    unfold winningTable branchValue
    rw [pricing_restriction_identity, (each certificate.winner).1]
  refine ⟨attains, ⟨winningTable K certificate, attains⟩, ?_⟩
  rintro value ⟨table, rfl⟩
  let branch : K → Bool := fun i => table i.1
  have covered : clampTable K branch table = table := clampTable_restrict K table
  have localBound := (each branch).2.2 ⟨table, rfl⟩
  calc
    completeMediatorPricingScore coupling multiplier table =
        branchOffset coupling K branch multiplier +
          completeMediatorPricingScore (residualCoupling coupling K)
            (branchMultiplier coupling K branch multiplier) table := by
      exact (congrArg (completeMediatorPricingScore coupling multiplier) covered).symm.trans
        (pricing_restriction_identity coupling K branch multiplier table)
    _ ≤ branchValue coupling K multiplier certificate branch :=
      add_le_add le_rfl localBound
    _ ≤ branchValue coupling K multiplier certificate certificate.winner := checks.2 branch

/-- Exact no-improving-column condition over the full canonical response family. -/
theorem checked_separator_stopping_iff (coupling : FiniteResponseLaw (M × M))
    (K : Finset M) (multiplier : M → ℚ) (certificate : SeparatorPricingCertificate M K)
    (threshold : ℚ) (accepted : checkSeparatorPricing coupling K multiplier certificate = true) :
    (∀ table, completeMediatorPricingScore coupling multiplier table ≤ threshold) ↔
      branchValue coupling K multiplier certificate certificate.winner ≤ threshold := by
  obtain ⟨attains, greatest⟩ := checkSeparatorPricing_sound coupling K multiplier certificate accepted
  constructor
  · intro bound
    rw [← attains]
    exact bound _
  · intro bound table
    exact (greatest.2 ⟨table, rfl⟩).trans bound

/-- Even before master optimality, checked global pricing gives an exact upper
bound for every law satisfying all the original outcome-marginal constraints. -/
theorem checked_separator_causal_bound (coupling : FiniteResponseLaw (M × M))
    (K : Finset M) (multiplier probability : M → ℚ)
    (certificate : SeparatorPricingCertificate M K)
    (accepted : checkSeparatorPricing coupling K multiplier certificate = true)
    (law : FiniteResponseLaw (M → Bool))
    (marginals : ∀ i, linearObjective (fun table => if table i then 1 else 0) law.mass = probability i) :
    completeMediatorBenefit coupling law ≤
      branchValue coupling K multiplier certificate certificate.winner +
        ∑ i, multiplier i * probability i := by
  have greatest := (checkSeparatorPricing_sound coupling K multiplier certificate accepted).2
  exact pricing_bound_implies_causal_bound coupling multiplier probability _
    (fun table => greatest.2 ⟨table, rfl⟩) law marginals

/-- An actual feasible restricted-master witness with matching dual value is a
sharp upper endpoint of the full original causal law family, including odd cycles. -/
theorem checked_separator_master_isGreatest (coupling : FiniteResponseLaw (M × M))
    (K : Finset M) (multiplier probability : M → ℚ)
    (certificate : SeparatorPricingCertificate M K) (threshold : ℚ)
    (accepted : checkSeparatorPricing coupling K multiplier certificate = true)
    (stopped : branchValue coupling K multiplier certificate certificate.winner ≤ threshold)
    (candidate : FiniteResponseLaw (M → Bool))
    (marginals : ∀ i, linearObjective (fun table => if table i then 1 else 0) candidate.mass = probability i)
    (contact : completeMediatorBenefit coupling candidate = threshold + ∑ i, multiplier i * probability i) :
    IsGreatest {value : ℚ | ∃ law : FiniteResponseLaw (M → Bool),
      (∀ i, linearObjective (fun table => if table i then 1 else 0) law.mass = probability i) ∧
        completeMediatorBenefit coupling law = value}
      (completeMediatorBenefit coupling candidate) := by
  constructor
  · exact ⟨candidate, marginals, rfl⟩
  · rintro value ⟨law, means, rfl⟩
    have bound := checked_separator_causal_bound coupling K multiplier probability certificate
      accepted law means
    rw [contact]
    exact bound.trans (add_le_add stopped le_rfl)

#print axioms checkSeparatorPricing_sound
#print axioms checked_separator_causal_bound
#print axioms checked_separator_master_isGreatest

end D5.S3.ConceptDynamics.CausalMoments.SeparatorMediatorPricing
