/- GID: D5/S3/ConceptDynamics/PartialIdentification/PartialMediatorTransportReduction
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/PartialIdentification/PartialMediatorTransportReduction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [D5/S3/ConceptDynamics/PartialIdentification/SharedThresholdResponseCoupling]
   utility: none
   digest: Binary-treatment binary-outcome partial mediation with independent mechanisms has an exact transportation-LP query image, including every rational target and simultaneous structural witnesses. -/

import D5.S3.ConceptDynamics.PartialIdentification.SharedThresholdResponseCoupling
import D5.S3.ConceptDynamics.PartialIdentification.ProductLawMomentSparsification
import D5.S3.ConceptDynamics.PartIdentification.MarkovianBenefitIdentificationBoundary

/-!
The model is M=f_M(A,U_M), Y=f_Y(A,M,U_Y), with U_M independent of
U_Y. The treatment-to-outcome bypass is allowed. Complete outcome response
coordinates may have arbitrary dependence. The inputs are the full mediator
intervention marginals and success kernels P(Y_(a,m)=1). Interpreting the latter
as observational conditional probabilities requires the appropriate graphical
independence and positivity facts; this module does not infer them from data.

The source spaces are the existing mediator-pair law and the complete outcome
table law, combined with productResponseLaw. The shared-threshold theorem is
what makes all local Frechet cells jointly attainable. No independent outcome
noise is introduced for different mediator values or different worlds.

This resolves a tractable subclass of the mediator-program simplification
question in Xie--Li, arXiv:2602.14503, and the broader scaling problem discussed
by Arroyo et al., arXiv:2509.03548. It is not a solution for arbitrary confounded
mediators, multiple nested interventions, or extra response-table restrictions.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.ConceptDynamics.PartialIdentification.PartialMediatorTransportReduction

open scoped BigOperators
open D5.S0.Certificates.LinearObjectiveDual
open D5.S3.ConceptDynamics.PartialIdentification.MarkovianResponseLawFactorization
open D5.S3.ConceptDynamics.PartialIdentification.MarkovianBenefitIdentificationBoundary
open D5.S3.ConceptDynamics.PartialIdentification.FiniteMomentSparseLaw
open D5.S3.ConceptDynamics.PartialIdentification.ProductLawMomentSparsification
open D5.S3.ConceptDynamics.PartialIdentification.SharedThresholdResponseCoupling

variable {Mediator : Type*} [Fintype Mediator] [DecidableEq Mediator]

/-- All rows and columns constrain the same complete mediator-response law. -/
def HasMediatorMarginals (coupling : FiniteResponseLaw (Mediator × Mediator))
    (control treated : FiniteResponseLaw Mediator) : Prop :=
  (∀ m, leftResponseMarginal coupling.mass m = control.mass m) ∧
  (∀ m, rightResponseMarginal coupling.mass m = treated.mass m)

/-- The prescribed intervention-success kernel of the outcome mechanism. -/
def HasOutcomeKernel (law : FiniteResponseLaw ((Bool × Mediator) → Bool))
    (probability : Bool × Mediator → ℚ) : Prop :=
  ∀ a m, outcomeSuccess law a m = probability (a, m)

/-- The actual two-world outcome response law, obtained from independent
complete disturbances and one structural evaluation in each treatment world. -/
def partialMediatorResponseLaw (coupling : FiniteResponseLaw (Mediator × Mediator))
    (outcome : FiniteResponseLaw ((Bool × Mediator) → Bool)) :
    FiniteResponseLaw (Bool × Bool) :=
  pushforwardResponseLaw (productResponseLaw coupling outcome)
    (fun source => (source.2 (false, source.1.1), source.2 (true, source.1.2)))

/-- Probability of benefit under the actual independent source product. -/
def partialMediatorBenefit (coupling : FiniteResponseLaw (Mediator × Mediator))
    (outcome : FiniteResponseLaw ((Bool × Mediator) → Bool)) : ℚ :=
  linearObjective (fun source =>
    if source.2 (false, source.1.1) = false ∧ source.2 (true, source.1.2) = true
      then 1 else 0) (productResponseLaw coupling outcome).mass

/-- The finite objective is exactly the existing causal benefit readout. -/
theorem partialMediatorBenefit_actual_response
    (coupling : FiniteResponseLaw (Mediator × Mediator))
    (outcome : FiniteResponseLaw ((Bool × Mediator) → Bool)) :
    partialMediatorBenefit coupling outcome =
      benefitResponseMass (partialMediatorResponseLaw coupling outcome).mass := by
  have h := pushforward_linearObjective (productResponseLaw coupling outcome)
    (fun source => (source.2 (false, source.1.1), source.2 (true, source.1.2)))
    (fun pair : Bool × Bool => if pair = (false, true) then (1 : ℚ) else 0)
  have select (mass : Bool × Bool → ℚ) :
      linearObjective (fun pair => if pair = (false, true) then 1 else 0) mass =
        benefitResponseMass mass := by
    simp [linearObjective, benefitResponseMass]
  rw [select] at h
  simpa only [partialMediatorBenefit, partialMediatorResponseLaw, Prod.mk.injEq] using h.symm

/-- Independence gives the bilinear objective on the original two mechanisms. -/
theorem partialMediatorBenefit_eq_cells
    (coupling : FiniteResponseLaw (Mediator × Mediator))
    (outcome : FiniteResponseLaw ((Bool × Mediator) → Bool)) :
    partialMediatorBenefit coupling outcome =
      linearObjective (fun pair => outcomeBenefitCell outcome pair.1 pair.2) coupling.mass := by
  unfold partialMediatorBenefit
  rw [product_linearObjective_eq_left]
  simp only [outcomeBenefitCell, linearObjective, mul_comm]

/-- Lower transportation cost on a complete mediator response pair. -/
def lowerTransportCost (probability : Bool × Mediator → ℚ)
    (pair : Mediator × Mediator) : ℚ :=
  max 0 (probability (true, pair.2) - probability (false, pair.1))

/-- Upper transportation cost, with no separate cellwise mediator relaxation. -/
def upperTransportCost (probability : Bool × Mediator → ℚ)
    (pair : Mediator × Mediator) : ℚ :=
  min (1 - probability (false, pair.1)) (probability (true, pair.2))

/-- Every admitted model lies between the two linear costs evaluated at its
own complete mediator coupling. -/
theorem partialMediatorBenefit_transport_bounds
    (probability : Bool × Mediator → ℚ)
    (coupling : FiniteResponseLaw (Mediator × Mediator))
    (outcome : FiniteResponseLaw ((Bool × Mediator) → Bool))
    (kernel : HasOutcomeKernel outcome probability) :
    linearObjective (lowerTransportCost probability) coupling.mass ≤
        partialMediatorBenefit coupling outcome ∧
      partialMediatorBenefit coupling outcome ≤
        linearObjective (upperTransportCost probability) coupling.mass := by
  have cell (pair : Mediator × Mediator) := outcomeBenefitCell_bounds outcome pair.1 pair.2
  simp only [kernel] at cell
  rw [partialMediatorBenefit_eq_cells]
  constructor
  · exact Finset.sum_le_sum (fun pair _ =>
      mul_le_mul_of_nonneg_right (cell pair).1 (coupling.nonnegative pair))
  · exact Finset.sum_le_sum (fun pair _ =>
      mul_le_mul_of_nonneg_right (cell pair).2 (coupling.nonnegative pair))

/-- Two outcome mechanisms attain the two linear costs for every coupling.
Each mechanism is chosen before the mediator coupling is quantified. -/
theorem simultaneous_transport_endpoint_mechanisms
    (probability : Bool × Mediator → ℚ)
    (valid : ∀ index, 0 ≤ probability index ∧ probability index ≤ 1) :
    ∃ lower upper : FiniteResponseLaw ((Bool × Mediator) → Bool),
      HasOutcomeKernel lower probability ∧ HasOutcomeKernel upper probability ∧
      ∀ coupling : FiniteResponseLaw (Mediator × Mediator),
        partialMediatorBenefit coupling lower =
          linearObjective (lowerTransportCost probability) coupling.mass ∧
        partialMediatorBenefit coupling upper =
          linearObjective (upperTransportCost probability) coupling.mass := by
  obtain ⟨lower, upper, hl, hu, cells_l, cells_u⟩ :=
    simultaneous_frechet_outcome_laws probability valid
  refine ⟨lower, upper, hl, hu, ?_⟩
  intro coupling
  constructor
  · rw [partialMediatorBenefit_eq_cells]
    simp only [cells_l, lowerTransportCost]
  · rw [partialMediatorBenefit_eq_cells]
    simp only [cells_u, upperTransportCost]

private def mixtureLaw {Atom : Type*} [Fintype Atom]
    (first second : FiniteResponseLaw Atom) (t : ℚ) (ht : 0 ≤ t ∧ t ≤ 1) :
    FiniteResponseLaw Atom where
  mass := fun i => (1 - t) * first.mass i + t * second.mass i
  nonnegative := fun i => add_nonneg
    (mul_nonneg (sub_nonneg.mpr ht.2) (first.nonnegative i))
    (mul_nonneg ht.1 (second.nonnegative i))
  total := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, first.total, second.total]
    ring

private theorem objective_mixture {Atom : Type*} [Fintype Atom]
    (first second : FiniteResponseLaw Atom) (coefficient : Atom → ℚ)
    (t : ℚ) (ht : 0 ≤ t ∧ t ≤ 1) :
    linearObjective coefficient (mixtureLaw first second t ht).mass =
      (1 - t) * linearObjective coefficient first.mass +
        t * linearObjective coefficient second.mass := by
  unfold linearObjective mixtureLaw
  calc
    _ = ∑ i, ((1 - t) * (coefficient i * first.mass i) +
        t * (coefficient i * second.mass i)) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

private theorem kernel_mixture
    (first second : FiniteResponseLaw ((Bool × Mediator) → Bool))
    (probability : Bool × Mediator → ℚ)
    (hf : HasOutcomeKernel first probability) (hs : HasOutcomeKernel second probability)
    (t : ℚ) (ht : 0 ≤ t ∧ t ≤ 1) :
    HasOutcomeKernel (mixtureLaw first second t ht) probability := by
  intro a m
  unfold outcomeSuccess
  rw [objective_mixture]
  change (1 - t) * outcomeSuccess first a m + t * outcomeSuccess second a m = _
  rw [hf a m, hs a m]
  ring

private theorem benefit_mixture
    (coupling : FiniteResponseLaw (Mediator × Mediator))
    (first second : FiniteResponseLaw ((Bool × Mediator) → Bool))
    (t : ℚ) (ht : 0 ≤ t ∧ t ≤ 1) :
    partialMediatorBenefit coupling (mixtureLaw first second t ht) =
      (1 - t) * partialMediatorBenefit coupling first + t * partialMediatorBenefit coupling second := by
  unfold partialMediatorBenefit
  rw [product_linearObjective_eq_right, objective_mixture,
    product_linearObjective_eq_right coupling first, product_linearObjective_eq_right coupling second]

/-- For a fixed mediator coupling the exact rational query image is the full
interval between the lower and upper transport costs. Only the outcome law is
mixed, so independence of the two mechanisms is preserved throughout. -/
theorem fixed_coupling_benefit_sharp_iff
    (probability : Bool × Mediator → ℚ)
    (valid : ∀ index, 0 ≤ probability index ∧ probability index ≤ 1)
    (coupling : FiniteResponseLaw (Mediator × Mediator)) (target : ℚ) :
    (∃ outcome : FiniteResponseLaw ((Bool × Mediator) → Bool),
      HasOutcomeKernel outcome probability ∧ partialMediatorBenefit coupling outcome = target) ↔
    (linearObjective (lowerTransportCost probability) coupling.mass ≤ target ∧
      target ≤ linearObjective (upperTransportCost probability) coupling.mass) := by
  constructor
  · rintro ⟨outcome, kernel, value⟩
    simpa only [value] using partialMediatorBenefit_transport_bounds probability coupling outcome kernel
  · intro bounds
    obtain ⟨lower, upper, hl, hu, endpoint⟩ :=
      simultaneous_transport_endpoint_mechanisms probability valid
    let lo := linearObjective (lowerTransportCost probability) coupling.mass
    let hi := linearObjective (upperTransportCost probability) coupling.mass
    have hlow : partialMediatorBenefit coupling lower = lo := (endpoint coupling).1
    have hupp : partialMediatorBenefit coupling upper = hi := (endpoint coupling).2
    change lo ≤ target ∧ target ≤ hi at bounds
    by_cases equal : lo = hi
    · refine ⟨lower, hl, ?_⟩
      rw [hlow]
      linarith
    · have gap : 0 < hi - lo := by
        have ordered : lo ≤ hi := bounds.1.trans bounds.2
        exact sub_pos.mpr (lt_of_le_of_ne ordered equal)
      let t := (target - lo) / (hi - lo)
      have t0 : 0 ≤ t := div_nonneg (sub_nonneg.mpr bounds.1) gap.le
      have t1 : t ≤ 1 := by
        apply (div_le_iff₀ gap).mpr
        linarith [bounds.2]
      have identity : t * (hi - lo) = target - lo :=
        div_mul_cancel₀ _ (ne_of_gt gap)
      refine ⟨mixtureLaw lower upper t ⟨t0, t1⟩,
        kernel_mixture lower upper probability hl hu t ⟨t0, t1⟩, ?_⟩
      rw [benefit_mixture, hlow, hupp]
      nlinarith [identity]

/-- Exact linearization of every rational benefit target in partial mediation.
The right side uses one nonnegative normalized m-by-m transport matrix, its
row/column equalities, and two linear target inequalities. No outcome-response
optimization or global optimizer hypothesis remains on the right side. -/
theorem partial_mediator_target_iff_transport
    (control treated : FiniteResponseLaw Mediator)
    (probability : Bool × Mediator → ℚ)
    (valid : ∀ index, 0 ≤ probability index ∧ probability index ≤ 1) (target : ℚ) :
    (∃ coupling : FiniteResponseLaw (Mediator × Mediator),
      ∃ outcome : FiniteResponseLaw ((Bool × Mediator) → Bool),
        HasMediatorMarginals coupling control treated ∧ HasOutcomeKernel outcome probability ∧
        partialMediatorBenefit coupling outcome = target) ↔
    (∃ coupling : FiniteResponseLaw (Mediator × Mediator),
      HasMediatorMarginals coupling control treated ∧
      linearObjective (lowerTransportCost probability) coupling.mass ≤ target ∧
      target ≤ linearObjective (upperTransportCost probability) coupling.mass) := by
  constructor
  · rintro ⟨coupling, outcome, marginals, kernel, value⟩
    exact ⟨coupling, marginals,
      (fixed_coupling_benefit_sharp_iff probability valid coupling target).mp
        ⟨outcome, kernel, value⟩⟩
  · rintro ⟨coupling, marginals, bounds⟩
    obtain ⟨outcome, kernel, value⟩ :=
      (fixed_coupling_benefit_sharp_iff probability valid coupling target).mpr bounds
    exact ⟨coupling, outcome, marginals, kernel, value⟩

/-- Two standard transportation endpoint certificates imply valid and attained
bounds for the original independent-mechanism causal model. Their existence is
a finite LP problem; no unproved strong-duality theorem is postulated here. -/
theorem transport_endpoints_are_causal_sharp
    (control treated : FiniteResponseLaw Mediator)
    (probability : Bool × Mediator → ℚ)
    (valid : ∀ index, 0 ≤ probability index ∧ probability index ≤ 1)
    (lower upper : ℚ)
    (lowerCoupling upperCoupling : FiniteResponseLaw (Mediator × Mediator))
    (lower_marginals : HasMediatorMarginals lowerCoupling control treated)
    (upper_marginals : HasMediatorMarginals upperCoupling control treated)
    (lower_value : linearObjective (lowerTransportCost probability) lowerCoupling.mass = lower)
    (upper_value : linearObjective (upperTransportCost probability) upperCoupling.mass = upper)
    (bounds : ∀ coupling, HasMediatorMarginals coupling control treated →
      lower ≤ linearObjective (lowerTransportCost probability) coupling.mass ∧
      linearObjective (upperTransportCost probability) coupling.mass ≤ upper) :
    (∀ coupling outcome, HasMediatorMarginals coupling control treated →
      HasOutcomeKernel outcome probability →
      lower ≤ partialMediatorBenefit coupling outcome ∧ partialMediatorBenefit coupling outcome ≤ upper) ∧
    (∃ outcome, HasOutcomeKernel outcome probability ∧
      partialMediatorBenefit lowerCoupling outcome = lower) ∧
    (∃ outcome, HasOutcomeKernel outcome probability ∧
      partialMediatorBenefit upperCoupling outcome = upper) := by
  obtain ⟨lowerOutcome, upperOutcome, hl, hu, endpoints⟩ :=
    simultaneous_transport_endpoint_mechanisms probability valid
  refine ⟨?_, ⟨lowerOutcome, hl, (endpoints lowerCoupling).1.trans lower_value⟩,
    ⟨upperOutcome, hu, (endpoints upperCoupling).2.trans upper_value⟩⟩
  intro coupling outcome hm hk
  have h := partialMediatorBenefit_transport_bounds probability coupling outcome hk
  exact ⟨(bounds coupling hm).1.trans h.1, h.2.trans (bounds coupling hm).2⟩

/-- Cost identities exposing one-dimensional absolute-distance transport.
The two means below are evaluated at the actual coupling; prescribed mediator
marginals make them fixed. No Wasserstein API or sorting algorithm is assumed. -/
theorem transport_cost_absolute_distance_identities
    (probability : Bool × Mediator → ℚ)
    (coupling : FiniteResponseLaw (Mediator × Mediator)) :
    2 * linearObjective (lowerTransportCost probability) coupling.mass =
      linearObjective (fun pair => probability (true, pair.2)) coupling.mass -
      linearObjective (fun pair => probability (false, pair.1)) coupling.mass +
      linearObjective (fun pair => |probability (true, pair.2) - probability (false, pair.1)|) coupling.mass ∧
    2 * linearObjective (upperTransportCost probability) coupling.mass =
      1 - linearObjective (fun pair => probability (false, pair.1)) coupling.mass +
      linearObjective (fun pair => probability (true, pair.2)) coupling.mass -
      linearObjective (fun pair => |1 - probability (false, pair.1) - probability (true, pair.2)|) coupling.mass := by
  have lo (pair : Mediator × Mediator) :
      2 * lowerTransportCost probability pair =
        probability (true, pair.2) - probability (false, pair.1) +
          |probability (true, pair.2) - probability (false, pair.1)| := by
    unfold lowerTransportCost
    by_cases h : 0 ≤ probability (true, pair.2) - probability (false, pair.1)
    · rw [max_eq_right h, abs_of_nonneg h]
      ring
    · rw [max_eq_left (le_of_lt (lt_of_not_ge h)), abs_of_nonpos (le_of_lt (lt_of_not_ge h))]
      ring
  have hi (pair : Mediator × Mediator) :
      2 * upperTransportCost probability pair =
        1 - probability (false, pair.1) + probability (true, pair.2) -
          |1 - probability (false, pair.1) - probability (true, pair.2)| := by
    unfold upperTransportCost
    by_cases h : 1 - probability (false, pair.1) ≤ probability (true, pair.2)
    · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]
      ring
    · rw [min_eq_right (le_of_lt (lt_of_not_ge h)), abs_of_nonneg (sub_nonneg.mpr (le_of_lt (lt_of_not_ge h)))]
      ring
  constructor
  · unfold linearObjective
    rw [Finset.mul_sum]
    calc
      _ = ∑ pair, (probability (true, pair.2) - probability (false, pair.1) +
          |probability (true, pair.2) - probability (false, pair.1)|) * coupling.mass pair := by
        apply Finset.sum_congr rfl
        intro pair _
        rw [← lo pair]
        ring
      _ = _ := by simp only [add_mul, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  · unfold linearObjective
    rw [Finset.mul_sum]
    calc
      _ = ∑ pair, (1 - probability (false, pair.1) + probability (true, pair.2) -
          |1 - probability (false, pair.1) - probability (true, pair.2)|) * coupling.mass pair := by
        apply Finset.sum_congr rfl
        intro pair _
        rw [← hi pair]
        ring
      _ = _ := by
        simp only [add_mul, sub_mul, one_mul, Finset.sum_add_distrib,
          Finset.sum_sub_distrib, coupling.total]

#print axioms partialMediatorBenefit_actual_response
#print axioms fixed_coupling_benefit_sharp_iff
#print axioms partial_mediator_target_iff_transport
#print axioms transport_endpoints_are_causal_sharp
#print axioms transport_cost_absolute_distance_identities

end D5.S3.ConceptDynamics.PartialIdentification.PartialMediatorTransportReduction
