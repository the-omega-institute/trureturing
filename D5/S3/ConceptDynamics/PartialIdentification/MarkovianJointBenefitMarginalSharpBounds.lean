/- GID: D5/S3/ConceptDynamics/PartialIdentification/MarkovianJointBenefitMarginalSharpBounds
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/PartialIdentification/MarkovianJointBenefitMarginalSharpBounds
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Four interventional marginals sharply identify joint benefit across two independent complete response mechanisms to the product of their local benefit intervals, with rational attaining witnesses and an observation-kernel obstruction to point identification. -/

import D5.S3.ConceptDynamics.PartialIdentification.MarkovianJointMechanismBenefitSharpBounds

/- Library-search audit (2026-09-05): reuse FiniteResponseLaw,
   benefitResponseLaw, markovian_benefit_target_feasible_iff, and the existing
   MarkovianJointMechanismModel. The predecessor already contains the
   fixed-benefit singleton theorem. The new statement instead fixes the four
   single-world marginals and quantifies over both remaining internal couplings.
   Rational targets are realized by a two-edge path in the parameter rectangle;
   no convex mixture of product laws or real intermediate-value argument is used.
   The final witness uses the existing full model carrier, not a finite sample
   arena. It is a strict kernel-refinement witness, not a catalog admission claim.
   Local compiler availability and root sealing are recorded in the ledger. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.PartialIdentification.MarkovianJointBenefitMarginalSharpBounds

open D5.S3.ConceptDynamics.PartialIdentification.MarkovianResponseLawFactorization
open D5.S3.ConceptDynamics.PartialIdentification.MarkovianBenefitIdentificationBoundary
open D5.S3.ConceptDynamics.PartialIdentification.MarkovianJointMechanismBenefitSharpBounds

/-- Every rational value between the products of nonnegative interval endpoints
is itself a product of rational values in the two intervals. The construction
moves along two edges of the parameter rectangle, staying in the product family. -/
theorem nonnegative_product_interval_iff
    (l1 u1 l2 u2 q : ℚ)
    (hl1 : 0 ≤ l1) (h1 : l1 ≤ u1)
    (hl2 : 0 ≤ l2) (h2 : l2 ≤ u2) :
    (l1 * l2 ≤ q ∧ q ≤ u1 * u2) ↔
      ∃ x y : ℚ,
        l1 ≤ x ∧ x ≤ u1 ∧ l2 ≤ y ∧ y ≤ u2 ∧ x * y = q := by
  constructor
  · rintro ⟨lower, upper⟩
    by_cases firstEdge : q ≤ u1 * l2
    · by_cases zero : l2 = 0
      · refine ⟨l1, l2, le_rfl, h1, le_rfl, h2, ?_⟩
        rw [zero] at lower firstEdge ⊢
        nlinarith
      · have positive : 0 < l2 := lt_of_le_of_ne hl2 (Ne.symm zero)
        exact ⟨q / l2, l2,
          (le_div_iff₀ positive).2 lower,
          (div_le_iff₀ positive).2 firstEdge,
          le_rfl, h2, div_mul_cancel₀ q zero⟩
    · have nonnegative : 0 ≤ u1 := hl1.trans h1
      have positive : 0 < u1 := by
        by_contra h
        have zero : u1 = 0 := by linarith
        rw [zero] at firstEdge upper
        simp only [zero_mul] at firstEdge upper
        exact firstEdge upper
      refine ⟨u1, q / u1, h1, le_rfl, ?_, ?_, ?_⟩
      · apply (le_div_iff₀ positive).2
        nlinarith
      · apply (div_le_iff₀ positive).2
        nlinarith
      · field_simp [ne_of_gt positive] <;> ring
  · rintro ⟨x, y, xl, xu, yl, yu, product⟩
    have lower := mul_le_mul xl yl hl2 (hl1.trans xl)
    have upper := mul_le_mul xu yu (hl2.trans yl) (hl1.trans h1)
    rw [product] at lower upper
    exact ⟨lower, upper⟩

/-- Recover the local benefit interval directly from an existing complete
response law, by reusing the assignment-outcome sharpness theorem. -/
theorem outcomeLaw_benefit_bounds
    (law : FiniteResponseLaw (Bool × Bool))
    (p0 p1 : ℚ)
    (control : controlSuccessMarginal law.mass = p0)
    (treated : treatmentSuccessMarginal law.mass = p1) :
    max 0 (p1 - p0) ≤ benefitResponseMass law.mass ∧
      benefitResponseMass law.mass ≤ min p1 (1 - p0) := by
  apply (markovian_benefit_target_feasible_iff
    p0 p1 (benefitResponseMass law.mass)).mpr
  refine ⟨{ assignmentLaw := boolPointLaw false, outcomeLaw := law },
    control, treated, ?_⟩
  exact markovianBenefitMass_product (boolPointLaw false) law.mass

/-- Exact joint-benefit range given four interventional marginals. Nonempty
local intervals express compatibility of those marginals. Every rational target
in the product interval has an explicit independent-mechanism realization. -/
theorem four_marginal_joint_benefit_sharp_iff
    (p10 p11 p20 p21 target : ℚ)
    (first_compatible : max 0 (p11 - p10) ≤ min p11 (1 - p10))
    (second_compatible : max 0 (p21 - p20) ≤ min p21 (1 - p20)) :
    (max 0 (p11 - p10) * max 0 (p21 - p20) ≤ target ∧
        target ≤ min p11 (1 - p10) * min p21 (1 - p20)) ↔
      ∃ model : MarkovianJointMechanismModel,
        controlSuccessMarginal model.firstLaw.mass = p10 ∧
        treatmentSuccessMarginal model.firstLaw.mass = p11 ∧
        controlSuccessMarginal model.secondLaw.mass = p20 ∧
        treatmentSuccessMarginal model.secondLaw.mass = p21 ∧
        jointMechanismBenefitMass (markovianJointResponseMass model) = target := by
  have products := nonnegative_product_interval_iff
    (max 0 (p11 - p10)) (min p11 (1 - p10))
    (max 0 (p21 - p20)) (min p21 (1 - p20)) target
    (le_max_left _ _) first_compatible
    (le_max_left _ _) second_compatible
  constructor
  · intro bounds
    rcases products.mp bounds with ⟨b1, b2, b1l, b1u, b2l, b2u, product⟩
    refine ⟨{
      firstLaw := benefitResponseLaw p10 p11 b1 b1l b1u
      secondLaw := benefitResponseLaw p20 p21 b2 b2l b2u },
      ?_, ?_, ?_, ?_, ?_⟩
    · exact benefitResponseLaw_controlMarginal p10 p11 b1 b1l b1u
    · exact benefitResponseLaw_treatmentMarginal p10 p11 b1 b1l b1u
    · exact benefitResponseLaw_controlMarginal p20 p21 b2 b2l b2u
    · exact benefitResponseLaw_treatmentMarginal p20 p21 b2 b2l b2u
    · change b1 * b2 = target
      exact product
  · rintro ⟨model, p10_eq, p11_eq, p20_eq, p21_eq, target_eq⟩
    have b1 := outcomeLaw_benefit_bounds model.firstLaw p10 p11 p10_eq p11_eq
    have b2 := outcomeLaw_benefit_bounds model.secondLaw p20 p21 p20_eq p21_eq
    apply products.mpr
    refine ⟨benefitResponseMass model.firstLaw.mass,
      benefitResponseMass model.secondLaw.mass,
      b1.1, b1.2, b2.1, b2.2, ?_⟩
    exact (markovianJointBenefit_eq_product model).symm.trans target_eq

/-- Four balanced interventional marginals leave the whole interval [0,1/4]
feasible, even though the two complete mechanisms are independent. -/
theorem balanced_four_marginal_sharp_interval (target : ℚ) :
    (0 ≤ target ∧ target ≤ (1 / 4 : ℚ)) ↔
      ∃ model : MarkovianJointMechanismModel,
        controlSuccessMarginal model.firstLaw.mass = (1 / 2 : ℚ) ∧
        treatmentSuccessMarginal model.firstLaw.mass = (1 / 2 : ℚ) ∧
        controlSuccessMarginal model.secondLaw.mass = (1 / 2 : ℚ) ∧
        treatmentSuccessMarginal model.secondLaw.mass = (1 / 2 : ℚ) ∧
        jointMechanismBenefitMass (markovianJointResponseMass model) = target := by
  have result := four_marginal_joint_benefit_sharp_iff
    (1 / 2 : ℚ) (1 / 2 : ℚ) (1 / 2 : ℚ) (1 / 2 : ℚ) target
    (by norm_num) (by norm_num)
  norm_num at result
  exact result

/-- The single-world data readout on the existing complete model carrier. -/
def fourMarginalReadout (model : MarkovianJointMechanismModel) :
    (ℚ × ℚ) × (ℚ × ℚ) :=
  ((controlSuccessMarginal model.firstLaw.mass,
    treatmentSuccessMarginal model.firstLaw.mass),
   (controlSuccessMarginal model.secondLaw.mass,
    treatmentSuccessMarginal model.secondLaw.mass))

/-- Two full Markovian models in one data fiber have different joint-benefit
values. This is a strict kernel-refinement witness on the full rational model
space; it is not a finite-arena escape rate or a maximal-catalog certificate. -/
theorem joint_benefit_strictly_refines_four_marginal_kernel :
    ∃ first second : MarkovianJointMechanismModel,
      fourMarginalReadout first = fourMarginalReadout second ∧
      jointMechanismBenefitMass (markovianJointResponseMass first) ≠
        jointMechanismBenefitMass (markovianJointResponseMass second) := by
  rcases (balanced_four_marginal_sharp_interval 0).mp (by norm_num) with
    ⟨first, f0, f1, f2, f3, fq⟩
  rcases (balanced_four_marginal_sharp_interval (1 / 4 : ℚ)).mp
    (by norm_num) with ⟨second, s0, s1, s2, s3, sq⟩
  refine ⟨first, second, ?_, ?_⟩
  · simp only [fourMarginalReadout, f0, f1, f2, f3, s0, s1, s2, s3]
  · rw [fq, sq]
    norm_num

/-- No function of the four interventional marginals recovers joint benefit on
all independent complete-mechanism models. -/
theorem no_joint_benefit_reconstruction_from_four_marginals :
    ¬ ∃ recover : ((ℚ × ℚ) × (ℚ × ℚ)) → ℚ,
      ∀ model : MarkovianJointMechanismModel,
        recover (fourMarginalReadout model) =
          jointMechanismBenefitMass (markovianJointResponseMass model) := by
  rintro ⟨recover, recovers⟩
  rcases joint_benefit_strictly_refines_four_marginal_kernel with
    ⟨first, second, same, different⟩
  apply different
  calc
    jointMechanismBenefitMass (markovianJointResponseMass first) =
        recover (fourMarginalReadout first) := (recovers first).symm
    _ = recover (fourMarginalReadout second) := congrArg recover same
    _ = jointMechanismBenefitMass (markovianJointResponseMass second) := recovers second

#print axioms nonnegative_product_interval_iff
#print axioms four_marginal_joint_benefit_sharp_iff
#print axioms balanced_four_marginal_sharp_interval
#print axioms joint_benefit_strictly_refines_four_marginal_kernel
#print axioms no_joint_benefit_reconstruction_from_four_marginals

end D5.S3.ConceptDynamics.PartialIdentification.MarkovianJointBenefitMarginalSharpBounds
