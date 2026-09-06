/- GID: D5/S3/ConceptDynamics/PartialIdentification/ConditionalMarkovianBenefitBoundary
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/PartialIdentification/ConditionalMarkovianBenefitBoundary
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Conditional product response laws aggregate to a weighted product query; an exact covariance certificate and independent-noise shared-root witness delimit unconditional benefit factorization. -/

import D5.S3.ConceptDynamics.CausalMoments.MarkovianJointBenefitMarginalSharpBounds

/- Library-search audit (2026-09-05): product_pushforward_factorizes requires
   coordinatewise response maps. It does not apply to two maps sharing a random
   parent. CovariateSharpAggregation and CovariateSharedParameterObstruction
   already separate valid stratum aggregation from simultaneous attainability.
   This module records conditional product evaluation and supplies a concrete
   shared-root counterexample. It does not infer c-components from a graph or
   claim arbitrary conditional kernels have a fixed-noise Markovian realization.
   In the counterexample the three independent source laws are explicit. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.PartialIdentification.ConditionalMarkovianBenefitBoundary

open scoped BigOperators
open D5.S3.ConceptDynamics.PartialIdentification.CanonicalResponseSignature
open D5.S3.ConceptDynamics.PartialIdentification.MarkovianResponseLawFactorization
open D5.S3.ConceptDynamics.PartialIdentification.MarkovianBenefitIdentificationBoundary
open D5.S3.ConceptDynamics.CausalMoments.MarkovianJointMechanismBenefitSharpBounds

/-- Joint benefit after averaging independent-mechanism models conditional on
one finite observed covariate. The model family makes conditional independence
explicit without asserting marginal independence after mixing. -/
def conditionalJointBenefit
    {Covariate : Type*} [Fintype Covariate]
    (weight : FiniteResponseLaw Covariate)
    (model : Covariate → MarkovianJointMechanismModel) : ℚ :=
  ∑ c, weight.mass c *
    jointMechanismBenefitMass (markovianJointResponseMass (model c))

/-- Conditional independence gives an average of products. -/
theorem conditional_joint_benefit_eq_weighted_products
    {Covariate : Type*} [Fintype Covariate]
    (weight : FiniteResponseLaw Covariate)
    (model : Covariate → MarkovianJointMechanismModel) :
    conditionalJointBenefit weight model =
      ∑ c, weight.mass c *
        (benefitResponseMass (model c).firstLaw.mass *
          benefitResponseMass (model c).secondLaw.mass) := by
  unfold conditionalJointBenefit
  apply Finset.sum_congr rfl
  intro c _
  rw [markovianJointBenefit_eq_product]

/-- Exact polynomial certificate for the difference between an average of
products and a product of averages in two strata. No probability assumptions
are needed for the identity itself. -/
theorem binary_mixture_covariance_certificate
    (w x0 x1 y0 y1 : ℚ) :
    ((1 - w) * (x0 * y0) + w * (x1 * y1)) -
      (((1 - w) * x0 + w * x1) * ((1 - w) * y0 + w * y1)) =
        w * (1 - w) * ((x1 - x0) * (y1 - y0)) := by
  ring

/-- With two positive-probability strata, the marginal product formula holds
exactly when at least one mechanism's conditional benefit rate is constant. -/
theorem binary_mixture_factorizes_iff
    (w x0 x1 y0 y1 : ℚ) (w_positive : 0 < w) (w_lt_one : w < 1) :
    ((1 - w) * (x0 * y0) + w * (x1 * y1) =
      ((1 - w) * x0 + w * x1) * ((1 - w) * y0 + w * y1)) ↔
        x1 = x0 ∨ y1 = y0 := by
  have coefficient_ne : w * (1 - w) ≠ 0 :=
    ne_of_gt (mul_pos w_positive (sub_pos.mpr w_lt_one))
  have certificate := binary_mixture_covariance_certificate w x0 x1 y0 y1
  constructor
  · intro factorized
    have zero : w * (1 - w) * ((x1 - x0) * (y1 - y0)) = 0 := by
      rw [← certificate, factorized, sub_self]
    have zero_product : (x1 - x0) * (y1 - y0) = 0 :=
      (mul_eq_zero.mp zero).resolve_left coefficient_ne
    rcases mul_eq_zero.mp zero_product with first | second
    · exact Or.inl (sub_eq_zero.mp first)
    · exact Or.inr (sub_eq_zero.mp second)
  · rintro (first | second)
    · rw [first]
      ring
    · rw [second]
      ring

/-- An explicit fair covariate law. -/
def balancedCovariateLaw : FiniteResponseLaw Bool where
  mass := fun _ => 1 / 2
  nonnegative := by intro c; norm_num
  total := by norm_num [Fintype.sum_bool]

/-- Three mutually independent exogenous variables: a fair shared root and
one degenerate local disturbance for each of the two outcome equations. -/
def sharedRootSourceLaw : FiniteResponseLaw (Bool × (Bool × Bool)) :=
  productResponseLaw balancedCovariateLaw
    (productResponseLaw (boolPointLaw false) (boolPointLaw false))

/-- The equations Y_i(a,c,u_i) = a AND c yield response pair (false,c).
The two maps share the root c, although their local disturbances are independent. -/
def sharedRootResponse (source : Bool × (Bool × Bool)) :
    (Bool × Bool) × (Bool × Bool) :=
  ((false, source.1), (false, source.1))

/-- The complete response law obtained by evaluating the shared-root equations
under the explicitly product-factorized exogenous law. -/
noncomputable def sharedRootJointLaw :
    FiniteResponseLaw ((Bool × Bool) × (Bool × Bool)) :=
  pushforwardResponseLaw sharedRootSourceLaw sharedRootResponse

/-- The pushforward has equal mass on the two diagonal response states. -/
theorem sharedRootJointLaw_mass
    (response : (Bool × Bool) × (Bool × Bool)) :
    sharedRootJointLaw.mass response =
      (if response = ((false, false), (false, false)) then 1 / 2 else 0) +
      (if response = ((false, true), (false, true)) then 1 / 2 else 0) := by
  rcases response with ⟨⟨a, b⟩, ⟨c, d⟩⟩
  cases a <;> cases b <;> cases c <;> cases d <;>
    norm_num [sharedRootJointLaw, pushforwardResponseLaw,
      pushforwardSignatureMass, sharedRootSourceLaw, productResponseLaw,
      productResponseMass, balancedCovariateLaw, boolPointLaw, boolPointMass,
      sharedRootResponse, Fintype.sum_prod_type, Fintype.sum_bool]

/-- Both benefit rates and their intersection equal one half in the shared-root
SCM. Thus the joint benefit differs from the product one quarter. -/
theorem independent_local_noise_shared_root_counterexample :
    leftResponseMarginal sharedRootJointLaw.mass (false, true) = (1 / 2 : ℚ) ∧
    rightResponseMarginal sharedRootJointLaw.mass (false, true) = (1 / 2 : ℚ) ∧
    jointMechanismBenefitMass sharedRootJointLaw.mass = (1 / 2 : ℚ) := by
  constructor
  · norm_num [leftResponseMarginal, sharedRootJointLaw_mass,
      Fintype.sum_prod_type, Fintype.sum_bool]
  constructor
  · norm_num [rightResponseMarginal, sharedRootJointLaw_mass,
      Fintype.sum_prod_type, Fintype.sum_bool]
  · norm_num [jointMechanismBenefitMass, sharedRootJointLaw_mass]

/-- Independent local equation noises do not force the evaluated complete
responses to factorize when a random ancestor is shared. This does not contradict
product_pushforward_factorizes, whose componentwise-map hypothesis fails here. -/
theorem shared_root_responses_do_not_factorize :
    ¬ IsMarkovianTwoComponentLaw sharedRootJointLaw.mass := by
  rintro ⟨first, second, factorized⟩
  rcases independent_local_noise_shared_root_counterexample with
    ⟨left, right, joint⟩
  rw [factorized, leftResponseMarginal_productResponseMass,
    second.total, mul_one] at left
  rw [factorized, rightResponseMarginal_productResponseMass,
    first.total, one_mul] at right
  rw [factorized] at joint
  change first.mass (false, true) * second.mass (false, true) = (1 / 2 : ℚ) at joint
  rw [left, right] at joint
  norm_num at joint

#print axioms conditional_joint_benefit_eq_weighted_products
#print axioms binary_mixture_covariance_certificate
#print axioms binary_mixture_factorizes_iff
#print axioms independent_local_noise_shared_root_counterexample
#print axioms shared_root_responses_do_not_factorize

end D5.S3.ConceptDynamics.PartialIdentification.ConditionalMarkovianBenefitBoundary
