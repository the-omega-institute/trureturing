/- GID: D5/S3/ConceptDynamics/CausalMoments/UnknownCouplingFairMediation
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/CausalMoments/UnknownCouplingFairMediation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: With fair complete-outcome coordinates and only the two mediator marginals fixed, joint sharp benefit is exactly a weighted partition optimum; the unknown mediator coupling and outcome law are both constructed. -/

import D5.S3.ConceptDynamics.CausalMoments.CompleteMediatorCutSharpBounds
import D5.S3.ConceptDynamics.CausalMoments.FiniteCouplingPushforwardLift

/-!
This solves the unknown-coupling outer optimization for the fair-kernel,
marginal-only finite subclass. Both source laws vary and remain independent.
No fixed mediator coupling, optimal transport plan, or precomputed cut is a
premise. Additional restrictions on mediator pairs or outcome tables are not
silently dropped: they are outside this precise model family.

The graph/partition and disaggregation tools are classical. The objective is
the existing original causal benefit, with its existing no-direct-effect
embedding. Generic nonfair kernels and mixed observational rows remain separate
problems in the multi-component direction of Arroyo et al., arXiv:2509.03548.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.CausalMoments.UnknownCouplingFairMediation

open scoped BigOperators
open D5.S0.Certificates.LinearObjectiveDual
open D5.S3.ConceptDynamics.PartialIdentification.MarkovianResponseLawFactorization
open D5.S3.ConceptDynamics.PartialIdentification.MarkovianBenefitIdentificationBoundary
open D5.S3.ConceptDynamics.CausalMoments.FiniteMomentSparseLaw
open D5.S3.ConceptDynamics.CausalMoments.PartialMediatorTransportReduction
open D5.S3.ConceptDynamics.CausalMoments.CompleteMediatorCutSharpBounds
open D5.S3.ConceptDynamics.CausalMoments.FiniteCouplingPushforwardLift

variable {M : Type*} [Fintype M] [DecidableEq M]

/-- Total mass selected by a Boolean partition in both original mediator marginals. -/
def partitionWeight (control treated : FiniteResponseLaw M) (table : M → Bool) : ℚ :=
  linearObjective (fun i => if table i then 1 else 0) control.mass +
    linearObjective (fun i => if table i then 1 else 0) treated.mass

/-- Maximum crossing mass permitted by the two coarse marginal totals. -/
def partitionScore (control treated : FiniteResponseLaw M) (table : M → Bool) : ℚ :=
  1 - |partitionWeight control treated table - 1|

private theorem score_eq_min (x : ℚ) : 1 - |x - 1| = min x (2 - x) := by
  by_cases h : x ≤ 1
  · rw [abs_of_nonpos (by linarith), min_eq_left (by linarith)]
    ring
  · rw [abs_of_nonneg (by linarith), min_eq_right (by linarith)]
    ring

private theorem bool_push_true (law : FiniteResponseLaw M) (table : M → Bool) :
    (pushforwardResponseLaw law table).mass true =
      linearObjective (fun i => if table i then 1 else 0) law.mass := by
  have h := pushforward_linearObjective law table (fun b : Bool => if b then (1 : ℚ) else 0)
  simpa [linearObjective, Fintype.sum_bool] using h

private theorem marginal_partition_identity
    (coupling : FiniteResponseLaw (M × M)) (control treated : FiniteResponseLaw M)
    (marginals : HasMediatorMarginals coupling control treated) (table : M → Bool) :
    linearObjective (fun pair => (if table pair.1 then (1 : ℚ) else 0) +
      (if table pair.2 then 1 else 0)) coupling.mass = partitionWeight control treated table := by
  unfold partitionWeight linearObjective
  simp only [Fintype.sum_prod_type, add_mul, Finset.sum_add_distrib]
  have left_eq : (∑ i, ∑ j, (if table i then (1 : ℚ) else 0) * coupling.mass (i, j)) =
      ∑ i, (if table i then (1 : ℚ) else 0) * control.mass i := by
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.mul_sum]
    exact congrArg (fun x : ℚ => (if table i then 1 else 0) * x) (marginals.1 i)
  have right_eq : (∑ i, ∑ j, (if table j then (1 : ℚ) else 0) * coupling.mass (i, j)) =
      ∑ j, (if table j then (1 : ℚ) else 0) * treated.mass j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [← Finset.mul_sum]
    exact congrArg (fun x : ℚ => (if table j then 1 else 0) * x) (marginals.2 j)
  rw [left_eq, right_eq]

/-- A bound uniform over every mediator coupling with the specified original
marginals. No support graph or fixed-coupling hypothesis is supplied. -/
theorem mediatorCutMass_le_partitionScore
    (coupling : FiniteResponseLaw (M × M)) (control treated : FiniteResponseLaw M)
    (marginals : HasMediatorMarginals coupling control treated) (table : M → Bool) :
    mediatorCutMass coupling table ≤ partitionScore control treated table := by
  let degree : M × M → ℚ := fun pair =>
    (if table pair.1 then 1 else 0) + (if table pair.2 then 1 else 0)
  have first : mediatorCutMass coupling table ≤ linearObjective degree coupling.mass := by
    apply Finset.sum_le_sum
    intro pair _
    apply mul_le_mul_of_nonneg_right _ (coupling.nonnegative pair)
    cases h0 : table pair.1 <;> cases h1 : table pair.2 <;> norm_num [degree, h0, h1]
  have second : mediatorCutMass coupling table ≤
      linearObjective (fun pair => 2 - degree pair) coupling.mass := by
    apply Finset.sum_le_sum
    intro pair _
    apply mul_le_mul_of_nonneg_right _ (coupling.nonnegative pair)
    cases h0 : table pair.1 <;> cases h1 : table pair.2 <;> norm_num [degree, h0, h1]
  have sum_eq : linearObjective degree coupling.mass = partitionWeight control treated table :=
    marginal_partition_identity coupling control treated marginals table
  have complement_eq : linearObjective (fun pair => 2 - degree pair) coupling.mass =
      2 - linearObjective degree coupling.mass := by
    simp only [linearObjective, sub_mul, Finset.sum_sub_distrib]
    rw [← Finset.mul_sum, coupling.total, mul_one]
  rw [sum_eq] at first
  rw [complement_eq, sum_eq] at second
  rw [partitionScore, score_eq_min]
  exact le_min first second

/-- For each partition, construct a full mediator coupling attaining its bound.
All individual mediator probabilities survive the coarse two-cell optimization. -/
theorem exists_partition_attaining_coupling (control treated : FiniteResponseLaw M)
    (table : M → Bool) :
    ∃ coupling : FiniteResponseLaw (M × M),
      HasMediatorMarginals coupling control treated ∧
        mediatorCutMass coupling table = partitionScore control treated table := by
  let p := linearObjective (fun i => if table i then (1 : ℚ) else 0) control.mass
  let q := linearObjective (fun i => if table i then (1 : ℚ) else 0) treated.mass
  have cp : (pushforwardResponseLaw control table).mass true = p := bool_push_true control table
  have cq : (pushforwardResponseLaw treated table).mass true = q := bool_push_true treated table
  have tp := (pushforwardResponseLaw control table).total
  have tq := (pushforwardResponseLaw treated table).total
  simp only [Fintype.sum_bool, cp, cq] at tp tq
  have p0 : 0 ≤ p := by rw [← cp]; exact (pushforwardResponseLaw control table).nonnegative true
  have q0 : 0 ≤ q := by rw [← cq]; exact (pushforwardResponseLaw treated table).nonnegative true
  have p1 : p ≤ 1 := by linarith [(pushforwardResponseLaw control table).nonnegative false]
  have q1 : q ≤ 1 := by linarith [(pushforwardResponseLaw treated table).nonnegative false]
  have lower : max 0 (q - p) ≤ min q (1 - p) := by
    apply max_le
    · exact le_min q0 (sub_nonneg.mpr p1)
    · apply le_min <;> linarith
  let coarse := benefitResponseLaw p q (min q (1 - p)) lower le_rfl
  have hl : ∀ a, leftResponseMarginal coarse.mass a = (pushforwardResponseLaw control table).mass a := by
    intro a
    cases a <;>
      simp [coarse, benefitResponseLaw, benefitResponseVector, leftResponseMarginal,
        Fintype.sum_bool, cp] <;> linarith
  have hr : ∀ b, rightResponseMarginal coarse.mass b = (pushforwardResponseLaw treated table).mass b := by
    intro b
    cases b <;>
      simp [coarse, benefitResponseLaw, benefitResponseVector, rightResponseMarginal,
        Fintype.sum_bool, cq] <;> linarith
  let coupling := liftCoarseCoupling control treated table table coarse hl hr
  refine ⟨coupling, liftCoarseCoupling_marginals control treated table table coarse hl hr, ?_⟩
  have expectation := liftCoarseCoupling_expectation control treated table table coarse hl hr
    (fun pair : Bool × Bool => if pair.1 ≠ pair.2 then (1 : ℚ) else 0)
  change mediatorCutMass coupling table = _ at expectation
  rw [expectation]
  change linearObjective (fun pair : Bool × Bool => if pair.1 ≠ pair.2 then (1 : ℚ) else 0)
    coarse.mass = 1 - |p + q - 1|
  simp only [linearObjective, Fintype.sum_prod_type, Fintype.sum_bool]
  norm_num [coarse, benefitResponseLaw, benefitResponseVector]
  by_cases small : q ≤ 1 - p
  · rw [min_eq_left small, abs_of_nonpos (by linarith)]
    ring
  · rw [min_eq_right (le_of_not_ge small), abs_of_nonneg (by linarith)]
    ring

/-- Full rational identified image when BOTH independent mechanism laws vary.
A finite optimal partition is obtained rather than assumed. One constructed
mediator coupling already attains every target in the final interval. -/
theorem unknown_coupling_fair_interval (control treated : FiniteResponseLaw M) :
    ∃ best : M → Bool,
      (∀ table, partitionScore control treated table ≤ partitionScore control treated best) ∧
      ∀ target : ℚ,
        (∃ coupling : FiniteResponseLaw (M × M), ∃ law : FiniteResponseLaw (M → Bool),
          HasMediatorMarginals coupling control treated ∧ FairCompleteOutcome law ∧
            completeMediatorBenefit coupling law = target) ↔
        (0 ≤ target ∧ target ≤ partitionScore control treated best / 2) := by
  classical
  obtain ⟨best, maximal⟩ := Finite.exists_max (partitionScore control treated)
  obtain ⟨coupling, marginals, cut_eq⟩ := exists_partition_attaining_coupling control treated best
  obtain ⟨fixedBest, fixedMaximal, fixedInterval⟩ := complete_mediator_cut_interval coupling
  have fixedValue : mediatorCutMass coupling fixedBest = partitionScore control treated best := by
    apply le_antisymm
    · exact (mediatorCutMass_le_partitionScore coupling control treated marginals fixedBest).trans
        (maximal fixedBest)
    · rw [← cut_eq]
      exact fixedMaximal best
  refine ⟨best, maximal, ?_⟩
  intro target
  constructor
  · rintro ⟨other, law, otherMarginals, fair, value⟩
    obtain ⟨_, _, otherInterval⟩ := complete_mediator_cut_interval other
    have nonnegative := ((otherInterval target).mp ⟨law, fair, value⟩).1
    refine ⟨nonnegative, ?_⟩
    rw [← value, fair_completeMediatorBenefit_eq_half_cut other law fair]
    apply div_le_div_of_nonneg_right _ (by norm_num)
    calc
      linearObjective (mediatorCutMass other) law.mass ≤
          ∑ table, partitionScore control treated best * law.mass table :=
        Finset.sum_le_sum (fun table _ => mul_le_mul_of_nonneg_right
          ((mediatorCutMass_le_partitionScore other control treated otherMarginals table).trans
            (maximal table)) (law.nonnegative table))
      _ = partitionScore control treated best := by rw [← Finset.mul_sum, law.total, mul_one]
  · intro bounds
    have fixedBounds : 0 ≤ target ∧ target ≤ mediatorCutMass coupling fixedBest / 2 := by
      simpa only [fixedValue] using bounds
    obtain ⟨law, fair, value⟩ := (fixedInterval target).mpr fixedBounds
    exact ⟨coupling, law, marginals, fair, value⟩

/-- The ordinary one-half benefit ceiling is attainable precisely when the
combined mediator masses admit a subset with total one. -/
theorem unknown_coupling_half_iff_partition (control treated : FiniteResponseLaw M) :
    (∃ coupling : FiniteResponseLaw (M × M), ∃ law : FiniteResponseLaw (M → Bool),
      HasMediatorMarginals coupling control treated ∧ FairCompleteOutcome law ∧
        completeMediatorBenefit coupling law = 1 / 2) ↔
    ∃ table : M → Bool, partitionWeight control treated table = 1 := by
  obtain ⟨best, maximal, interval⟩ := unknown_coupling_fair_interval control treated
  constructor
  · intro attained
    have bound := ((interval (1 / 2)).mp attained).2
    unfold partitionScore at bound
    have zero : |partitionWeight control treated best - 1| = 0 :=
      le_antisymm (by linarith) (abs_nonneg _)
    exact ⟨best, sub_eq_zero.mp (abs_eq_zero.mp zero)⟩
  · rintro ⟨table, balanced⟩
    apply (interval (1 / 2)).mpr
    have bestBound := maximal table
    have score : partitionScore control treated table = 1 := by simp [partitionScore, balanced]
    rw [score] at bestBound
    constructor <;> linarith

#print axioms exists_partition_attaining_coupling
#print axioms unknown_coupling_fair_interval
#print axioms unknown_coupling_half_iff_partition

end D5.S3.ConceptDynamics.CausalMoments.UnknownCouplingFairMediation
