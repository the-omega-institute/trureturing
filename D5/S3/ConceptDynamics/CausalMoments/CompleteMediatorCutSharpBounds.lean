/- GID: D5/S3/ConceptDynamics/CausalMoments/CompleteMediatorCutSharpBounds
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/CausalMoments/CompleteMediatorCutSharpBounds
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Under complete mediation and fair outcome-response marginals, the exact fixed-coupling benefit interval is half the weighted maximum cut, with explicit common-noise attaining laws. -/

import D5.S3.ConceptDynamics.CausalMoments.PartialMediatorTransportReduction
import Mathlib.Data.Fintype.Lattice
import Mathlib.Tactic.FinCases

/-!
Research target: determine which response restrictions preserve tractable
mediator bounds in Xie--Li (arXiv:2602.14503), and identify the graph optimization
needed by multi-component methods in Arroyo et al. (arXiv:2509.03548).

The mediator response coupling is FIXED. It is not identified from its two
marginals by this theorem. The outcome equation ignores treatment: both worlds
read one table y : Mediator -> Bool. The resulting law is embedded into the
existing partial-mediator evaluator. Equal intervention-success numbers alone
do not impose this no-direct-effect restriction.

Library audit (2026-09-06): reuse FiniteResponseLaw, pushforward_linearObjective,
productResponseLaw, partialMediatorBenefit and its original-response identity,
and Finite.exists_max. The previous mediator ledger states the cut reduction
on paper; the searched source has no matching complete-mediation cut owner.
A maximum is obtained on all Boolean tables, not assumed or found on a sample.
No efficient general MaxCut algorithm or first-discovery claim is made.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.ConceptDynamics.CausalMoments.CompleteMediatorCutSharpBounds

open scoped BigOperators
open D5.S0.Certificates.LinearObjectiveDual
open D5.S3.ConceptDynamics.PartialIdentification.MarkovianResponseLawFactorization
open D5.S3.ConceptDynamics.PartialIdentification.MarkovianBenefitIdentificationBoundary
open D5.S3.ConceptDynamics.CausalMoments.FiniteMomentSparseLaw
open D5.S3.ConceptDynamics.CausalMoments.SharedThresholdResponseCoupling
open D5.S3.ConceptDynamics.CausalMoments.PartialMediatorTransportReduction

variable {Mediator : Type*} [Fintype Mediator] [DecidableEq Mediator]

/-- Embed a single outcome-response table into both treatment worlds. -/
def completeOutcomeLaw (law : FiniteResponseLaw (Mediator → Bool)) :
    FiniteResponseLaw ((Bool × Mediator) → Bool) :=
  pushforwardResponseLaw law (fun table index => table index.2)

/-- Both structural intervention rows have exactly the same coordinate. -/
theorem completeOutcomeLaw_success (law : FiniteResponseLaw (Mediator → Bool))
    (a : Bool) (m : Mediator) :
    outcomeSuccess (completeOutcomeLaw law) a m =
      linearObjective (fun table => if table m then 1 else 0) law.mass := by
  unfold outcomeSuccess completeOutcomeLaw
  exact pushforward_linearObjective law _ _

/-- Every outcome intervention succeeds with probability one half. -/
def FairCompleteOutcome (law : FiniteResponseLaw (Mediator → Bool)) : Prop :=
  ∀ m, linearObjective (fun table => if table m then 1 else 0) law.mass = 1 / 2

/-- Fairness is the same prescribed kernel used by the existing mediator API. -/
theorem completeOutcomeLaw_fair_kernel (law : FiniteResponseLaw (Mediator → Bool))
    (fair : FairCompleteOutcome law) :
    HasOutcomeKernel (completeOutcomeLaw law) (fun _ => 1 / 2) := by
  intro a m
  rw [completeOutcomeLaw_success, fair m]

/-- Benefit uses the existing actual independent mediator/outcome source law. -/
def completeMediatorBenefit (coupling : FiniteResponseLaw (Mediator × Mediator))
    (law : FiniteResponseLaw (Mediator → Bool)) : ℚ :=
  partialMediatorBenefit coupling (completeOutcomeLaw law)

/-- Bind the complete-mediation query to the existing causal response cell. -/
theorem completeMediatorBenefit_actual_response
    (coupling : FiniteResponseLaw (Mediator × Mediator))
    (law : FiniteResponseLaw (Mediator → Bool)) :
    completeMediatorBenefit coupling law =
      benefitResponseMass (partialMediatorResponseLaw coupling (completeOutcomeLaw law)).mass :=
  partialMediatorBenefit_actual_response coupling (completeOutcomeLaw law)

/-- Weight of directed mediator pairs separated by a Boolean partition.
Both directions contribute their own masses; no symmetry is assumed. -/
def mediatorCutMass (coupling : FiniteResponseLaw (Mediator × Mediator))
    (table : Mediator → Bool) : ℚ :=
  linearObjective (fun pair => if table pair.1 ≠ table pair.2 then 1 else 0) coupling.mass

private def assignmentBenefit (coupling : FiniteResponseLaw (Mediator × Mediator))
    (table : Mediator → Bool) : ℚ :=
  linearObjective (fun pair => if table pair.1 = false ∧ table pair.2 = true then 1 else 0)
    coupling.mass

private theorem benefit_expectation
    (coupling : FiniteResponseLaw (Mediator × Mediator))
    (law : FiniteResponseLaw (Mediator → Bool)) :
    completeMediatorBenefit coupling law = linearObjective (assignmentBenefit coupling) law.mass := by
  unfold completeMediatorBenefit
  rw [partialMediatorBenefit_eq_cells]
  have cell (pair : Mediator × Mediator) :
      outcomeBenefitCell (completeOutcomeLaw law) pair.1 pair.2 =
        linearObjective (fun table => if table pair.1 = false ∧ table pair.2 = true
          then 1 else 0) law.mass := by
    unfold outcomeBenefitCell completeOutcomeLaw
    exact pushforward_linearObjective law _ _
  simp_rw [cell]
  unfold assignmentBenefit linearObjective
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro table _
  apply Finset.sum_congr rfl
  intro pair _
  ring

private theorem assignment_cut_identity
    (coupling : FiniteResponseLaw (Mediator × Mediator)) (table : Mediator → Bool) :
    2 * assignmentBenefit coupling table = mediatorCutMass coupling table +
      ∑ pair, coupling.mass pair *
        ((if table pair.2 then (1 : ℚ) else 0) - (if table pair.1 then 1 else 0)) := by
  unfold assignmentBenefit mediatorCutMass linearObjective
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro pair _
  cases h0 : table pair.1 <;> cases h1 : table pair.2 <;> simp [h0, h1] <;> ring

/-- The exact cut identity holds with the actual intervention-mean drift.
Fairness is only used later to cancel this drift. -/
theorem completeMediatorBenefit_cut_identity
    (coupling : FiniteResponseLaw (Mediator × Mediator))
    (law : FiniteResponseLaw (Mediator → Bool)) :
    2 * completeMediatorBenefit coupling law =
      linearObjective (mediatorCutMass coupling) law.mass +
      ∑ pair, coupling.mass pair *
        (linearObjective (fun table => if table pair.2 then 1 else 0) law.mass -
          linearObjective (fun table => if table pair.1 then 1 else 0) law.mass) := by
  have drift :
      (∑ table, (∑ pair, coupling.mass pair *
        ((if table pair.2 then (1 : ℚ) else 0) - (if table pair.1 then 1 else 0))) * law.mass table) =
      ∑ pair, coupling.mass pair *
        (linearObjective (fun table => if table pair.2 then 1 else 0) law.mass -
          linearObjective (fun table => if table pair.1 then 1 else 0) law.mass) := by
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro pair _
    unfold linearObjective
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro table _
    ring
  calc
    2 * completeMediatorBenefit coupling law =
        ∑ table, (2 * assignmentBenefit coupling table) * law.mass table := by
      rw [benefit_expectation]
      unfold linearObjective
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro table _
      ring
    _ = linearObjective (mediatorCutMass coupling) law.mass +
        ∑ table, (∑ pair, coupling.mass pair *
          ((if table pair.2 then (1 : ℚ) else 0) - (if table pair.1 then 1 else 0))) * law.mass table := by
      simp_rw [assignment_cut_identity, add_mul, Finset.sum_add_distrib]
      rfl
    _ = _ := by rw [drift]

/-- Reduced cost for one deterministic complete-outcome column, before the
constant multiplier for probability normalization is subtracted. -/
def completeMediatorPricingScore (coupling : FiniteResponseLaw (Mediator × Mediator))
    (multiplier : Mediator → ℚ) (table : Mediator → Bool) : ℚ :=
  assignmentBenefit coupling table -
    ∑ m, multiplier m * (if table m then 1 else 0)

/-- The actual column-pricing problem is weighted cut plus vertex fields.
This identity covers arbitrary directed coupling and arbitrary rational dual
multipliers; it does not assume fair marginals or a stationary mediator law. -/
theorem completeMediatorPricingScore_graph_identity
    (coupling : FiniteResponseLaw (Mediator × Mediator))
    (multiplier : Mediator → ℚ) (table : Mediator → Bool) :
    2 * completeMediatorPricingScore coupling multiplier table =
      mediatorCutMass coupling table +
      ∑ m, (rightResponseMarginal coupling.mass m -
        leftResponseMarginal coupling.mass m - 2 * multiplier m) * (if table m then 1 else 0) := by
  have drift : (∑ pair, coupling.mass pair *
      ((if table pair.2 then (1 : ℚ) else 0) - (if table pair.1 then 1 else 0))) =
      ∑ m, (rightResponseMarginal coupling.mass m - leftResponseMarginal coupling.mass m) *
        (if table m then 1 else 0) := by
    unfold rightResponseMarginal leftResponseMarginal
    simp only [Fintype.sum_prod_type, mul_sub, Finset.sum_sub_distrib, sub_mul, Finset.sum_mul]
    rw [Finset.sum_comm (f := fun i j => coupling.mass (i, j) * (if table j then (1 : ℚ) else 0))]
  have identity := assignment_cut_identity coupling table
  rw [drift] at identity
  have fields : (∑ m, (rightResponseMarginal coupling.mass m -
      leftResponseMarginal coupling.mass m - 2 * multiplier m) * (if table m then (1 : ℚ) else 0)) =
      (∑ m, (rightResponseMarginal coupling.mass m - leftResponseMarginal coupling.mass m) *
        (if table m then 1 else 0)) - 2 * (∑ m, multiplier m * (if table m then 1 else 0)) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro m _
    ring
  rw [fields]
  unfold completeMediatorPricingScore
  linarith

/-- At fair response marginals, benefit is exactly half the expected cut. -/
theorem fair_completeMediatorBenefit_eq_half_cut
    (coupling : FiniteResponseLaw (Mediator × Mediator))
    (law : FiniteResponseLaw (Mediator → Bool)) (fair : FairCompleteOutcome law) :
    completeMediatorBenefit coupling law =
      linearObjective (mediatorCutMass coupling) law.mass / 2 := by
  have identity := completeMediatorBenefit_cut_identity coupling law
  unfold FairCompleteOutcome at fair
  simp only [fair, sub_self, mul_zero, Finset.sum_const_zero, add_zero] at identity
  linarith

/-- One fair bit selects a complete response table or its complement.
The same bit controls every mediator coordinate. -/
def complementOutcomeLaw (table : Mediator → Bool) : FiniteResponseLaw (Mediator → Bool) :=
  pushforwardResponseLaw (uniformThresholdLaw 2 (by decide))
    (fun bit => if bit = 0 then table else fun m => !(table m))

private theorem complement_expectation (table : Mediator → Bool)
    (query : (Mediator → Bool) → ℚ) :
    linearObjective query (complementOutcomeLaw table).mass =
      (query table + query (fun m => !(table m))) / 2 := by
  unfold complementOutcomeLaw
  rw [pushforward_linearObjective]
  norm_num [linearObjective, uniformThresholdLaw, Fin.sum_univ_two] <;> ring

/-- Complement symmetrization realizes every fair coordinate simultaneously. -/
theorem complementOutcomeLaw_fair (table : Mediator → Bool) :
    FairCompleteOutcome (complementOutcomeLaw table) := by
  intro m
  rw [complement_expectation]
  cases h : table m <;> norm_num [h]

/-- Complementing the whole assignment leaves every cut edge unchanged. -/
theorem mediatorCutMass_complement (coupling : FiniteResponseLaw (Mediator × Mediator))
    (table : Mediator → Bool) :
    mediatorCutMass coupling (fun m => !(table m)) = mediatorCutMass coupling table := by
  unfold mediatorCutMass linearObjective
  apply Finset.sum_congr rfl
  intro pair _
  cases h0 : table pair.1 <;> cases h1 : table pair.2 <;> simp [h0, h1]

/-- Every deterministic cut has a fair original-mechanism attaining law. -/
theorem complementOutcomeLaw_benefit
    (coupling : FiniteResponseLaw (Mediator × Mediator)) (table : Mediator → Bool) :
    completeMediatorBenefit coupling (complementOutcomeLaw table) = mediatorCutMass coupling table / 2 := by
  rw [fair_completeMediatorBenefit_eq_half_cut coupling _ (complementOutcomeLaw_fair table),
    complement_expectation, mediatorCutMass_complement]
  ring

/-- Finite maximization is over every complete Boolean response assignment.
The returned cut supplies a greatest attainable causal benefit, without an
optimizer hypothesis or independent pairwise response choices. -/
theorem complete_mediator_maxcut_sharp
    (coupling : FiniteResponseLaw (Mediator × Mediator)) :
    ∃ best : Mediator → Bool,
      (∀ table, mediatorCutMass coupling table ≤ mediatorCutMass coupling best) ∧
      IsGreatest
        {value : ℚ | ∃ law : FiniteResponseLaw (Mediator → Bool),
          FairCompleteOutcome law ∧ completeMediatorBenefit coupling law = value}
        (mediatorCutMass coupling best / 2) := by
  obtain ⟨best, maximal⟩ := Finite.exists_max (mediatorCutMass coupling)
  refine ⟨best, maximal, ?_, ?_⟩
  · exact ⟨complementOutcomeLaw best, complementOutcomeLaw_fair best,
      complementOutcomeLaw_benefit coupling best⟩
  · rintro value ⟨law, fair, rfl⟩
    rw [fair_completeMediatorBenefit_eq_half_cut coupling law fair]
    apply div_le_div_of_nonneg_right _ (by norm_num)
    calc
      linearObjective (mediatorCutMass coupling) law.mass ≤
          ∑ table, mediatorCutMass coupling best * law.mass table :=
        Finset.sum_le_sum (fun table _ => mul_le_mul_of_nonneg_right (maximal table) (law.nonnegative table))
      _ = mediatorCutMass coupling best := by rw [← Finset.mul_sum, law.total, mul_one]

private def outcomeMixture (first second : FiniteResponseLaw (Mediator → Bool))
    (t : ℚ) (ht : 0 ≤ t ∧ t ≤ 1) : FiniteResponseLaw (Mediator → Bool) where
  mass := fun table => (1 - t) * first.mass table + t * second.mass table
  nonnegative := fun table => add_nonneg
    (mul_nonneg (sub_nonneg.mpr ht.2) (first.nonnegative table))
    (mul_nonneg ht.1 (second.nonnegative table))
  total := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, first.total, second.total]
    ring

private theorem expectation_mixture (first second : FiniteResponseLaw (Mediator → Bool))
    (t : ℚ) (ht : 0 ≤ t ∧ t ≤ 1) (query : (Mediator → Bool) → ℚ) :
    linearObjective query (outcomeMixture first second t ht).mass =
      (1 - t) * linearObjective query first.mass + t * linearObjective query second.mass := by
  unfold linearObjective outcomeMixture
  simp_rw [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro table _ <;> ring

/-- The entire rational query interval is attained while keeping the mediator
coupling fixed. Interpolation occurs only inside the outcome disturbance. -/
theorem complete_mediator_cut_interval
    (coupling : FiniteResponseLaw (Mediator × Mediator)) :
    ∃ best : Mediator → Bool,
      (∀ table, mediatorCutMass coupling table ≤ mediatorCutMass coupling best) ∧
      ∀ target : ℚ,
        (∃ law : FiniteResponseLaw (Mediator → Bool),
          FairCompleteOutcome law ∧ completeMediatorBenefit coupling law = target) ↔
        (0 ≤ target ∧ target ≤ mediatorCutMass coupling best / 2) := by
  obtain ⟨best, maximal, greatest⟩ := complete_mediator_maxcut_sharp coupling
  let bottom := complementOutcomeLaw (fun _ : Mediator => false)
  let top := complementOutcomeLaw best
  have bottom_fair : FairCompleteOutcome bottom := complementOutcomeLaw_fair _
  have top_fair : FairCompleteOutcome top := complementOutcomeLaw_fair _
  have bottom_value : completeMediatorBenefit coupling bottom = 0 := by
    rw [complementOutcomeLaw_benefit]
    simp [mediatorCutMass, linearObjective]
  have top_value : completeMediatorBenefit coupling top = mediatorCutMass coupling best / 2 :=
    complementOutcomeLaw_benefit coupling best
  refine ⟨best, maximal, ?_⟩
  intro target
  constructor
  · rintro ⟨law, fair, value⟩
    refine ⟨?_, greatest.2 ⟨law, fair, value⟩⟩
    rw [← value, benefit_expectation]
    unfold linearObjective assignmentBenefit
    apply Finset.sum_nonneg
    intro table _
    apply mul_nonneg _ (law.nonnegative table)
    apply Finset.sum_nonneg
    intro pair _
    by_cases event : table pair.1 = false ∧ table pair.2 = true
    · simpa only [if_pos event, one_mul] using coupling.nonnegative pair
    · simp only [if_neg event, zero_mul, le_refl]
  · rintro ⟨nonnegative, bounded⟩
    by_cases zero : mediatorCutMass coupling best / 2 = 0
    · have target_zero : target = 0 := by linarith
      exact ⟨bottom, bottom_fair, bottom_value.trans target_zero.symm⟩
    · have positive : 0 < mediatorCutMass coupling best / 2 :=
        lt_of_le_of_ne (nonnegative.trans bounded) (Ne.symm zero)
      let t := target / (mediatorCutMass coupling best / 2)
      have ht : 0 ≤ t ∧ t ≤ 1 :=
        ⟨div_nonneg nonnegative positive.le, (div_le_one positive).mpr bounded⟩
      refine ⟨outcomeMixture bottom top t ht, ?_, ?_⟩
      · intro m
        rw [expectation_mixture, bottom_fair m, top_fair m]
        ring
      · rw [benefit_expectation, expectation_mixture, ← benefit_expectation, ← benefit_expectation,
          bottom_value, top_value]
        simp only [mul_zero, zero_add]
        exact div_mul_cancel₀ target (ne_of_gt positive)

/-- A weighted cut has full mass precisely when all positive mediator pairs
cross the partition. This exposes the compatibility condition behind the
cellwise upper bound, with loops and directed pairs handled explicitly. -/
theorem mediatorCutMass_eq_one_iff
    (coupling : FiniteResponseLaw (Mediator × Mediator)) (table : Mediator → Bool) :
    mediatorCutMass coupling table = 1 ↔
      ∀ pair, coupling.mass pair ≠ 0 → table pair.1 ≠ table pair.2 := by
  have defect : 1 - mediatorCutMass coupling table =
      ∑ pair, if table pair.1 = table pair.2 then coupling.mass pair else 0 := by
    change 1 - (∑ pair, (if table pair.1 ≠ table pair.2 then (1 : ℚ) else 0) * coupling.mass pair) = _
    calc
      _ = (∑ pair, coupling.mass pair) -
          ∑ pair, (if table pair.1 ≠ table pair.2 then (1 : ℚ) else 0) * coupling.mass pair := by rw [coupling.total]
      _ = _ := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro pair _
        by_cases same : table pair.1 = table pair.2 <;> simp [same]
  constructor
  · intro full pair active same
    have bound : (if table pair.1 = table pair.2 then coupling.mass pair else 0) ≤
        ∑ other, if table other.1 = table other.2 then coupling.mass other else 0 := by
      exact Finset.single_le_sum (s := Finset.univ) (a := pair)
        (f := fun other : Mediator × Mediator =>
          if table other.1 = table other.2 then coupling.mass other else 0)
        (fun other _ => by
          split
          · exact coupling.nonnegative other
          · exact le_rfl)
        (Finset.mem_univ pair)
    rw [if_pos same, ← defect, full, sub_self] at bound
    exact active (le_antisymm bound (coupling.nonnegative pair))
  · intro separated
    have zero : (∑ pair, if table pair.1 = table pair.2 then coupling.mass pair else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro pair _
      by_cases active : coupling.mass pair = 0
      · simp [active]
      · simp [separated pair active]
    rw [zero] at defect
    linarith

/-- Complete mediation can attain the pairwise ceiling one half exactly when
the positive mediator-response pairs admit one simultaneous two-coloring. -/
theorem complete_mediator_half_attainable_iff
    (coupling : FiniteResponseLaw (Mediator × Mediator)) :
    (∃ law : FiniteResponseLaw (Mediator → Bool),
      FairCompleteOutcome law ∧ completeMediatorBenefit coupling law = 1 / 2) ↔
    ∃ table : Mediator → Bool,
      ∀ pair, coupling.mass pair ≠ 0 → table pair.1 ≠ table pair.2 := by
  constructor
  · rintro ⟨law, fair, value⟩
    obtain ⟨best, _, greatest⟩ := complete_mediator_maxcut_sharp coupling
    have upper := greatest.2 (show (1 / 2 : ℚ) ∈
        {value : ℚ | ∃ law : FiniteResponseLaw (Mediator → Bool),
          FairCompleteOutcome law ∧ completeMediatorBenefit coupling law = value} from ⟨law, fair, value⟩)
    have cut_le : mediatorCutMass coupling best ≤ 1 := by
      calc
        mediatorCutMass coupling best ≤ ∑ pair, coupling.mass pair := by
          unfold mediatorCutMass linearObjective
          apply Finset.sum_le_sum
          intro pair _
          by_cases diff : best pair.1 ≠ best pair.2
          · simp [diff]
          · simpa [diff] using coupling.nonnegative pair
        _ = 1 := coupling.total
    refine ⟨best, (mediatorCutMass_eq_one_iff coupling best).mp ?_⟩
    linarith
  · rintro ⟨table, separated⟩
    refine ⟨complementOutcomeLaw table, complementOutcomeLaw_fair table, ?_⟩
    rw [complementOutcomeLaw_benefit, (mediatorCutMass_eq_one_iff coupling table).mpr separated]

/-- A fixed directed three-cycle mediator coupling, with uniform marginals. -/
def threeCycleCoupling : FiniteResponseLaw (Fin 3 × Fin 3) where
  mass := fun pair => if pair = (0, 1) ∨ pair = (1, 2) ∨ pair = (2, 0) then 1 / 3 else 0
  nonnegative := fun pair => by split <;> norm_num
  total := by
    norm_num [Fintype.sum_prod_type, Fin.sum_univ_succ, Fin.ext_iff, -Fin.val_eq_zero_iff]

private theorem threeCycle_cut_le (table : Fin 3 → Bool) :
    mediatorCutMass threeCycleCoupling table ≤ 2 / 3 := by
  have expand : mediatorCutMass threeCycleCoupling table =
      ((if table 0 ≠ table 1 then (1 : ℚ) else 0) +
        (if table 1 ≠ table 2 then 1 else 0) + (if table 2 ≠ table 0 then 1 else 0)) / 3 := by
    norm_num [mediatorCutMass, linearObjective, threeCycleCoupling,
      Fintype.sum_prod_type, Fin.sum_univ_succ, Fin.ext_iff, -Fin.val_eq_zero_iff]
    split_ifs <;> norm_num
  rw [expand]
  cases h0 : table 0 <;> cases h1 : table 1 <;> cases h2 : table 2 <;> norm_num [h0, h1, h2]

/-- Three pairwise upper cells of one half are incompatible with one complete
response table on an odd cycle. The true upper endpoint is exactly one third. -/
theorem three_cycle_complete_mediation_sharp :
    IsGreatest
      {value : ℚ | ∃ law : FiniteResponseLaw (Fin 3 → Bool),
        FairCompleteOutcome law ∧ completeMediatorBenefit threeCycleCoupling law = value}
      (1 / 3) := by
  let table : Fin 3 → Bool := fun m => decide (m = 2)
  have cut : mediatorCutMass threeCycleCoupling table = 2 / 3 := by
    norm_num [mediatorCutMass, linearObjective, threeCycleCoupling, table,
      Fintype.sum_prod_type, Fin.sum_univ_succ, Fin.ext_iff, -Fin.val_eq_zero_iff]
  constructor
  · refine ⟨complementOutcomeLaw table, complementOutcomeLaw_fair table, ?_⟩
    rw [complementOutcomeLaw_benefit, cut]
    norm_num
  · rintro value ⟨law, fair, rfl⟩
    rw [fair_completeMediatorBenefit_eq_half_cut threeCycleCoupling law fair]
    have bound : linearObjective (mediatorCutMass threeCycleCoupling) law.mass ≤ 2 / 3 := by
      calc
        _ ≤ ∑ y, (2 / 3 : ℚ) * law.mass y :=
          Finset.sum_le_sum (fun y _ => mul_le_mul_of_nonneg_right (threeCycle_cut_le y) (law.nonnegative y))
        _ = 2 / 3 := by rw [← Finset.mul_sum, law.total, mul_one]
    linarith

#print axioms completeMediatorBenefit_actual_response
#print axioms completeMediatorBenefit_cut_identity
#print axioms completeMediatorPricingScore_graph_identity
#print axioms complete_mediator_maxcut_sharp
#print axioms complete_mediator_cut_interval
#print axioms three_cycle_complete_mediation_sharp
#print axioms complete_mediator_half_attainable_iff

end D5.S3.ConceptDynamics.CausalMoments.CompleteMediatorCutSharpBounds
