/- GID: D5/S3/ConceptDynamics/CausalMoments/BipartiteMediatorPricing
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/CausalMoments/BipartiteMediatorPricing
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Complete-mediator column pricing on bipartite off-diagonal coupling support is exactly a nonnegative s-t cut problem; checked flows give actual maximizing columns and global restricted-master stopping certificates. -/

import D5.S0.Certificates.RationalSTCutCertificate
import D5.S3.ConceptDynamics.CausalMoments.CompleteMediatorCutSharpBounds

/-!
The mediator coupling is fixed. Its off-diagonal positive support, not the
causal DAG, must admit the supplied two-coloring. Loops are allowed and never
contribute to complete-mediation benefit. Multipliers and prescribed outcome
marginals are arbitrary rationals; no fairness, stationarity or symmetry is
assumed. All returned columns are actual complete Boolean response tables.

This is the classical binary gauge/submodular graph-cut construction applied
to the previously proved actual pricing coefficient. Hammer (1965) and
Kolmogorov--Zabih (2004) are prior owners of graph-representable binary energy
minimization. The open algorithmic target is the multi-intervention extension
and graph-based acceleration in Arroyo et al., arXiv:2509.03548, Section 6.
This is a tractable fixed-component pricing class and a global stopping bridge,
not a general multi-component optimizer or a new max-flow algorithm.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.CausalMoments.BipartiteMediatorPricing

open scoped BigOperators
open D5.S0.Certificates.LinearObjectiveDual
open D5.S0.Certificates.RationalSTCutCertificate
open D5.S3.ConceptDynamics.PartialIdentification.MarkovianResponseLawFactorization
open D5.S3.ConceptDynamics.CausalMoments.CompleteMediatorCutSharpBounds

variable {Mediator : Type*} [Fintype Mediator] [DecidableEq Mediator]

/-- Structural property of the actual coupling support. Loops are harmless. -/
def OffDiagonalBipartite (coupling : FiniteResponseLaw (Mediator × Mediator))
    (color : Mediator → Bool) : Prop :=
  ∀ i j, i ≠ j → coupling.mass (i, j) ≠ 0 → color i ≠ color j

/-- Flip exactly one color class; the map is an involution on complete tables. -/
def flipTable (color table : Mediator → Bool) : Mediator → Bool :=
  fun i => if color i then !(table i) else table i

theorem flipTable_involutive (color table : Mediator → Bool) :
    flipTable color (flipTable color table) = table := by
  funext i
  cases hc : color i <;> cases ht : table i <;> simp [flipTable, hc, ht]

/-- The diagonal is excluded from the constant cut contribution. -/
def offDiagonalMass (coupling : FiniteResponseLaw (Mediator × Mediator)) : ℚ :=
  ∑ pair, if pair.1 ≠ pair.2 then coupling.mass pair else 0

/-- The actual vertex field in twice the existing pricing score. -/
def pricingField (coupling : FiniteResponseLaw (Mediator × Mediator))
    (multiplier : Mediator → ℚ) (i : Mediator) : ℚ :=
  rightResponseMarginal coupling.mass i - leftResponseMarginal coupling.mass i - 2 * multiplier i

/-- Vertex field after the color-class flip. -/
def switchedField (coupling : FiniteResponseLaw (Mediator × Mediator))
    (color : Mediator → Bool) (multiplier : Mediator → ℚ) (i : Mediator) : ℚ :=
  if color i then -(pricingField coupling multiplier i) else pricingField coupling multiplier i

/-- Both directions of a mediator pair become a nonnegative internal capacity. -/
def pricingCapacity (coupling : FiniteResponseLaw (Mediator × Mediator))
    (i j : Mediator) : ℚ := coupling.mass (i, j) + coupling.mass (j, i)

/-- Nonnegative source-terminal capacity. -/
def pricingSourceCapacity (coupling : FiniteResponseLaw (Mediator × Mediator))
    (color : Mediator → Bool) (multiplier : Mediator → ℚ) (i : Mediator) : ℚ :=
  max 0 (switchedField coupling color multiplier i)

/-- Nonnegative sink-terminal capacity. -/
def pricingSinkCapacity (coupling : FiniteResponseLaw (Mediator × Mediator))
    (color : Mediator → Bool) (multiplier : Mediator → ℚ) (i : Mediator) : ℚ :=
  max 0 (-switchedField coupling color multiplier i)

/-- All constant terms are retained, including arbitrary signed multiplier terms. -/
def pricingOffset (coupling : FiniteResponseLaw (Mediator × Mediator))
    (color : Mediator → Bool) (multiplier : Mediator → ℚ) : ℚ :=
  offDiagonalMass coupling + (∑ i, if color i then pricingField coupling multiplier i else 0) +
    ∑ i, pricingSourceCapacity coupling color multiplier i

private theorem cut_flip_identity
    (coupling : FiniteResponseLaw (Mediator × Mediator)) (color table : Mediator → Bool)
    (bipartite : OffDiagonalBipartite coupling color) :
    mediatorCutMass coupling (flipTable color table) =
      offDiagonalMass coupling - mediatorCutMass coupling table := by
  unfold mediatorCutMass linearObjective offDiagonalMass
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  rintro ⟨i, j⟩ _
  by_cases same : i = j
  · subst j
    simp
  · by_cases zero : coupling.mass (i, j) = 0
    · simp [zero]
    · have different := bipartite i j same zero
      cases hc : color i <;> cases hd : color j <;>
        cases ht : table i <;> cases hu : table j <;>
        simp_all [flipTable] <;> ring

private theorem directed_cut_eq
    (coupling : FiniteResponseLaw (Mediator × Mediator)) (table : Mediator → Bool) :
    (∑ i, ∑ j, if table i = true ∧ table j = false then pricingCapacity coupling i j else 0) =
      mediatorCutMass coupling table := by
  have reverse : (∑ i, ∑ j, if table i = true ∧ table j = false then coupling.mass (j, i) else 0) =
      ∑ i, ∑ j, if table j = true ∧ table i = false then coupling.mass (i, j) else 0 :=
    Finset.sum_comm
  unfold pricingCapacity
  have split (i j : Mediator) :
      (if table i = true ∧ table j = false then coupling.mass (i, j) + coupling.mass (j, i) else 0) =
        (if table i = true ∧ table j = false then coupling.mass (i, j) else 0) +
        (if table i = true ∧ table j = false then coupling.mass (j, i) else 0) := by
    split_ifs <;> ring
  simp_rw [split, Finset.sum_add_distrib]
  rw [reverse, ← Finset.sum_add_distrib]
  unfold mediatorCutMass linearObjective
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  cases hi : table i <;> cases hj : table j <;> simp [hi, hj]

/-- Exact coefficient-level reduction on every Boolean table. The transformed
energy is the cut of an explicit graph with nonnegative capacities. -/
theorem pricing_cut_identity (coupling : FiniteResponseLaw (Mediator × Mediator))
    (color table : Mediator → Bool) (multiplier : Mediator → ℚ)
    (bipartite : OffDiagonalBipartite coupling color) :
    2 * completeMediatorPricingScore coupling multiplier (flipTable color table) =
      pricingOffset coupling color multiplier -
        stCutValue (pricingCapacity coupling) (pricingSourceCapacity coupling color multiplier)
          (pricingSinkCapacity coupling color multiplier) table := by
  have unary (i : Mediator) :
      pricingField coupling multiplier i * (if flipTable color table i then (1 : ℚ) else 0) =
      (if color i then pricingField coupling multiplier i else 0) +
        pricingSourceCapacity coupling color multiplier i -
          (if table i then pricingSinkCapacity coupling color multiplier i else
            pricingSourceCapacity coupling color multiplier i) := by
    cases hc : color i <;> cases ht : table i <;>
      simp [flipTable, pricingSourceCapacity, pricingSinkCapacity, switchedField, hc, ht, max_def] <;>
      split_ifs <;> linarith
  have identity := completeMediatorPricingScore_graph_identity coupling multiplier (flipTable color table)
  change 2 * completeMediatorPricingScore coupling multiplier (flipTable color table) =
    mediatorCutMass coupling (flipTable color table) +
      ∑ i, pricingField coupling multiplier i * (if flipTable color table i then 1 else 0) at identity
  simp_rw [unary] at identity
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, cut_flip_identity coupling color table bipartite] at identity
  unfold pricingOffset stCutValue
  rw [directed_cut_eq]
  linarith

/-- Check the support coloring and the actual flow/cut certificate together. -/
def checkBipartitePricing (coupling : FiniteResponseLaw (Mediator × Mediator))
    (color : Mediator → Bool) (multiplier : Mediator → ℚ)
    (certificate : STCutCertificate Mediator) : Bool :=
  (@decide (OffDiagonalBipartite coupling color) (by unfold OffDiagonalBipartite; infer_instance)) &&
    checkSTCutCertificate (pricingCapacity coupling) (pricingSourceCapacity coupling color multiplier)
      (pricingSinkCapacity coupling color multiplier) certificate

/-- Certified global pricing value in the original objective normalization. -/
def certifiedPricingValue (coupling : FiniteResponseLaw (Mediator × Mediator))
    (color : Mediator → Bool) (multiplier : Mediator → ℚ)
    (certificate : STCutCertificate Mediator) : ℚ :=
  (pricingOffset coupling color multiplier - flowValue certificate) / 2

/-- The flipped cut is an actual globally maximizing complete outcome column.
No fairness hypothesis or enumeration of all columns is supplied. -/
theorem checked_pricing_isGreatest (coupling : FiniteResponseLaw (Mediator × Mediator))
    (color : Mediator → Bool) (multiplier : Mediator → ℚ)
    (certificate : STCutCertificate Mediator)
    (accepted : checkBipartitePricing coupling color multiplier certificate = true) :
    completeMediatorPricingScore coupling multiplier (flipTable color certificate.side) =
        certifiedPricingValue coupling color multiplier certificate ∧
    IsGreatest (Set.range (completeMediatorPricingScore coupling multiplier))
      (certifiedPricingValue coupling color multiplier certificate) := by
  have parts : OffDiagonalBipartite coupling color ∧
      checkSTCutCertificate (pricingCapacity coupling) (pricingSourceCapacity coupling color multiplier)
        (pricingSinkCapacity coupling color multiplier) certificate = true := by
    simpa only [checkBipartitePricing, Bool.and_eq_true, decide_eq_true_eq] using accepted
  obtain ⟨contact, lower⟩ := checkSTCutCertificate_sound _ _ _ certificate parts.2
  have exact_value : completeMediatorPricingScore coupling multiplier (flipTable color certificate.side) =
      certifiedPricingValue coupling color multiplier certificate := by
    have identity := pricing_cut_identity coupling color certificate.side multiplier parts.1
    rw [contact] at identity
    unfold certifiedPricingValue
    linarith
  refine ⟨exact_value, ⟨flipTable color certificate.side, exact_value⟩, ?_⟩
  rintro value ⟨table, rfl⟩
  have identity := pricing_cut_identity coupling color (flipTable color table) multiplier parts.1
  rw [flipTable_involutive] at identity
  have bound := lower (flipTable color table)
  unfold certifiedPricingValue
  linarith

/-- Exact stopping test: no original column has positive reduced cost precisely
when the certified maximum is below the normalization multiplier. -/
theorem checked_no_improving_column_iff (coupling : FiniteResponseLaw (Mediator × Mediator))
    (color : Mediator → Bool) (multiplier : Mediator → ℚ)
    (certificate : STCutCertificate Mediator) (normalizationMultiplier : ℚ)
    (accepted : checkBipartitePricing coupling color multiplier certificate = true) :
    (∀ table, completeMediatorPricingScore coupling multiplier table ≤ normalizationMultiplier) ↔
      certifiedPricingValue coupling color multiplier certificate ≤ normalizationMultiplier := by
  obtain ⟨attains, greatest⟩ := checked_pricing_isGreatest coupling color multiplier certificate accepted
  constructor
  · intro all
    rw [← attains]
    exact all _
  · intro bound table
    exact (greatest.2 ⟨table, rfl⟩).trans bound

/-- The original causal objective decomposes into expected pricing score and
all original outcome-marginal rows. This identity holds on arbitrary couplings. -/
theorem completeMediatorBenefit_eq_pricing_expectation
    (coupling : FiniteResponseLaw (Mediator × Mediator)) (multiplier : Mediator → ℚ)
    (law : FiniteResponseLaw (Mediator → Bool)) :
    completeMediatorBenefit coupling law =
      linearObjective (completeMediatorPricingScore coupling multiplier) law.mass +
        ∑ i, multiplier i * linearObjective (fun table => if table i then 1 else 0) law.mass := by
  let mean := fun i => linearObjective (fun table : Mediator → Bool => if table i then 1 else 0) law.mass
  have drift : (∑ pair, coupling.mass pair * (mean pair.2 - mean pair.1)) =
      ∑ i, (rightResponseMarginal coupling.mass i - leftResponseMarginal coupling.mass i) * mean i := by
    unfold rightResponseMarginal leftResponseMarginal
    simp only [Fintype.sum_prod_type, mul_sub, Finset.sum_sub_distrib, sub_mul, Finset.sum_mul]
    rw [Finset.sum_comm (f := fun i j => coupling.mass (i, j) * mean j)]
  have graph_mean : 2 * linearObjective (completeMediatorPricingScore coupling multiplier) law.mass =
      linearObjective (mediatorCutMass coupling) law.mass +
        ∑ i, pricingField coupling multiplier i * mean i := by
    calc
      _ = ∑ table, (2 * completeMediatorPricingScore coupling multiplier table) * law.mass table := by
        unfold linearObjective
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro table _
        ring
      _ = _ := by
        simp_rw [completeMediatorPricingScore_graph_identity, add_mul, Finset.sum_add_distrib]
        congr 1
        simp_rw [Finset.sum_mul]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        unfold mean linearObjective pricingField
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro table _
        ring
  have original := completeMediatorBenefit_cut_identity coupling law
  change 2 * completeMediatorBenefit coupling law = linearObjective (mediatorCutMass coupling) law.mass +
    ∑ pair, coupling.mass pair * (mean pair.2 - mean pair.1) at original
  rw [drift] at original
  have fields : (∑ i, pricingField coupling multiplier i * mean i) =
      (∑ i, (rightResponseMarginal coupling.mass i - leftResponseMarginal coupling.mass i) * mean i) -
        2 * ∑ i, multiplier i * mean i := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    unfold pricingField
    ring
  rw [fields] at graph_mean
  change completeMediatorBenefit coupling law =
    linearObjective (completeMediatorPricingScore coupling multiplier) law.mass +
      ∑ i, multiplier i * mean i
  linarith

/-- A global pricing bound controls every full outcome law with the original
prescribed marginal rows. The law need not use the current restricted columns. -/
theorem pricing_bound_implies_causal_bound
    (coupling : FiniteResponseLaw (Mediator × Mediator)) (multiplier probability : Mediator → ℚ)
    (bound : ℚ) (global : ∀ table, completeMediatorPricingScore coupling multiplier table ≤ bound)
    (law : FiniteResponseLaw (Mediator → Bool))
    (marginals : ∀ i, linearObjective (fun table => if table i then 1 else 0) law.mass = probability i) :
    completeMediatorBenefit coupling law ≤ bound + ∑ i, multiplier i * probability i := by
  rw [completeMediatorBenefit_eq_pricing_expectation (multiplier := multiplier)]
  simp_rw [marginals]
  have key :
      linearObjective (completeMediatorPricingScore coupling multiplier) law.mass ≤ bound := by
    calc
      linearObjective (completeMediatorPricingScore coupling multiplier) law.mass ≤
          ∑ table, bound * law.mass table :=
        Finset.sum_le_sum
          (fun table _ => mul_le_mul_of_nonneg_right (global table) (law.nonnegative table))
      _ = bound := by rw [← Finset.mul_sum, law.total, mul_one]
  linarith [key]

/-- A feasible restricted-master law, its exact primal/dual equality, and a
checked absence of improving columns certify the full canonical sharp upper
endpoint. No conclusion about optimizing an unknown mediator coupling follows. -/
theorem checked_restricted_master_isGreatest
    (coupling : FiniteResponseLaw (Mediator × Mediator)) (color : Mediator → Bool)
    (multiplier probability : Mediator → ℚ) (normalizationMultiplier : ℚ)
    (certificate : STCutCertificate Mediator)
    (accepted : checkBipartitePricing coupling color multiplier certificate = true)
    (noImprovement : certifiedPricingValue coupling color multiplier certificate ≤ normalizationMultiplier)
    (candidate : FiniteResponseLaw (Mediator → Bool))
    (marginals : ∀ i, linearObjective (fun table => if table i then 1 else 0) candidate.mass = probability i)
    (contact : completeMediatorBenefit coupling candidate =
      normalizationMultiplier + ∑ i, multiplier i * probability i) :
    IsGreatest {value : ℚ | ∃ law : FiniteResponseLaw (Mediator → Bool),
      (∀ i, linearObjective (fun table => if table i then 1 else 0) law.mass = probability i) ∧
        completeMediatorBenefit coupling law = value}
      (completeMediatorBenefit coupling candidate) := by
  have global := (checked_no_improving_column_iff coupling color multiplier certificate
    normalizationMultiplier accepted).mpr noImprovement
  constructor
  · exact ⟨candidate, marginals, rfl⟩
  · rintro value ⟨law, means, rfl⟩
    rw [contact]
    exact pricing_bound_implies_causal_bound coupling multiplier probability normalizationMultiplier global law means

#print axioms pricing_cut_identity
#print axioms checked_pricing_isGreatest
#print axioms checked_no_improving_column_iff
#print axioms completeMediatorBenefit_eq_pricing_expectation
#print axioms checked_restricted_master_isGreatest

end D5.S3.ConceptDynamics.CausalMoments.BipartiteMediatorPricing
