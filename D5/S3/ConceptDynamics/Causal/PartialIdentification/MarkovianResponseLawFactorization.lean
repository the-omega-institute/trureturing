/- GID: D5/S3/ConceptDynamics/Causal/PartialIdentification/MarkovianResponseLawFactorization
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Causal/PartialIdentification/MarkovianResponseLawFactorization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Independent finite exogenous components induce product response laws; counterfactual events are multilinear and become exact LP objectives when all but one component law are fixed. -/

import D5.S0.Certificates.LinearObjectiveDual
import D5.S3.ConceptDynamics.Causal.PartialIdentification.CanonicalResponseSignature
import Mathlib.Tactic

/- Library-search audit trail (2026-09-04):
   * `MarkovDataProcessing` supplies finite single-world Markov factorization
     and data processing, but does not constrain cross-world response laws.
   * `PositivePriorConditionalIndependence` identifies kernel descent with
     conditional independence under positive priors, and
     `StochasticDescentEquivalence` handles quotient kernels and lumpability.
   * `CanonicalResponseSignature` supplies deterministic response carriers and
     exact pushforward of finite exogenous laws.
   * `LinearObjectiveDual` supplies exact rational primal-dual certificates for
     a finite linear objective.
   * Repository searches found no causal truth source proving that independent
     exogenous components remain product-factorized after deterministic
     response pushforward, or isolating the fixed-component LP slice of the
     resulting multilinear counterfactual query.
   * The two components below may represent individual Markovian disturbances
     or whole quasi-Markovian confounded components. No graph-to-component
     compiler or general multilinear optimizer is claimed. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Causal.PartialIdentification.MarkovianResponseLawFactorization

open scoped BigOperators
open D5.S0.Certificates.RationalFarkas
open D5.S0.Certificates.LinearObjectiveDual
open D5.S3.ConceptDynamics.Causal.PartialIdentification.CanonicalResponseSignature

/-- A normalized nonnegative rational law on a finite response carrier. -/
structure FiniteResponseLaw (Response : Type*) [Fintype Response] where
  mass : Response → ℚ
  nonnegative : ∀ response, 0 ≤ mass response
  total : ∑ response, mass response = 1

/-- Product mass of two response-component laws. This is the finite
cross-world factorization induced by independent exogenous components. -/
def productResponseMass
    {Left Right : Type*}
    (leftMass : Left → ℚ)
    (rightMass : Right → ℚ) :
    Left × Right → ℚ :=
  fun response => leftMass response.1 * rightMass response.2

/-- Product response masses are nonnegative when both component masses are
nonnegative. -/
theorem productResponseMass_nonnegative
    {Left Right : Type*}
    (leftMass : Left → ℚ)
    (rightMass : Right → ℚ)
    (left_nonnegative : ∀ left, 0 ≤ leftMass left)
    (right_nonnegative : ∀ right, 0 ≤ rightMass right)
    (response : Left × Right) :
    0 ≤ productResponseMass leftMass rightMass response := by
  exact mul_nonneg
    (left_nonnegative response.1)
    (right_nonnegative response.2)

/-- Total mass of a finite product law factors as the product of the two total
masses. -/
theorem productResponseMass_total
    {Left Right : Type*} [Fintype Left] [Fintype Right]
    (leftMass : Left → ℚ)
    (rightMass : Right → ℚ) :
    (∑ response : Left × Right,
        productResponseMass leftMass rightMass response) =
      (∑ left, leftMass left) * (∑ right, rightMass right) := by
  classical
  simp only [productResponseMass, Fintype.sum_prod_type]
  calc
    (∑ left, ∑ right, leftMass left * rightMass right) =
        ∑ left, leftMass left * (∑ right, rightMass right) := by
      apply Finset.sum_congr rfl
      intro left _
      rw [Finset.mul_sum]
    _ = (∑ left, leftMass left) * (∑ right, rightMass right) := by
      rw [Finset.sum_mul]

/-- Independent component laws combine into a normalized joint response law. -/
def productResponseLaw
    {Left Right : Type*} [Fintype Left] [Fintype Right]
    (leftLaw : FiniteResponseLaw Left)
    (rightLaw : FiniteResponseLaw Right) :
    FiniteResponseLaw (Left × Right) where
  mass := productResponseMass leftLaw.mass rightLaw.mass
  nonnegative := productResponseMass_nonnegative
    leftLaw.mass rightLaw.mass leftLaw.nonnegative rightLaw.nonnegative
  total := by
    rw [productResponseMass_total, leftLaw.total, rightLaw.total]
    norm_num

/-- Left marginal of a two-component response mass. -/
def leftResponseMarginal
    {Left Right : Type*} [Fintype Right]
    (jointMass : Left × Right → ℚ)
    (left : Left) : ℚ :=
  ∑ right, jointMass (left, right)

/-- Right marginal of a two-component response mass. -/
def rightResponseMarginal
    {Left Right : Type*} [Fintype Left]
    (jointMass : Left × Right → ℚ)
    (right : Right) : ℚ :=
  ∑ left, jointMass (left, right)

/-- Marginalizing a product mass on the right multiplies the left coordinate by
the total right mass. -/
theorem leftResponseMarginal_productResponseMass
    {Left Right : Type*} [Fintype Right]
    (leftMass : Left → ℚ)
    (rightMass : Right → ℚ)
    (left : Left) :
    leftResponseMarginal
        (productResponseMass leftMass rightMass) left =
      leftMass left * (∑ right, rightMass right) := by
  unfold leftResponseMarginal productResponseMass
  rw [Finset.mul_sum]

/-- The left marginal of a normalized product response law is exactly its left
component law. -/
theorem leftResponseMarginal_productResponseLaw
    {Left Right : Type*} [Fintype Left] [Fintype Right]
    (leftLaw : FiniteResponseLaw Left)
    (rightLaw : FiniteResponseLaw Right)
    (left : Left) :
    leftResponseMarginal (productResponseLaw leftLaw rightLaw).mass left =
      leftLaw.mass left := by
  rw [leftResponseMarginal_productResponseMass, rightLaw.total, mul_one]

/-- Marginalizing a product mass on the left multiplies the right coordinate by
the total left mass. -/
theorem rightResponseMarginal_productResponseMass
    {Left Right : Type*} [Fintype Left]
    (leftMass : Left → ℚ)
    (rightMass : Right → ℚ)
    (right : Right) :
    rightResponseMarginal
        (productResponseMass leftMass rightMass) right =
      (∑ left, leftMass left) * rightMass right := by
  unfold rightResponseMarginal productResponseMass
  rw [Finset.sum_mul]

/-- The right marginal of a normalized product response law is exactly its
right component law. -/
theorem rightResponseMarginal_productResponseLaw
    {Left Right : Type*} [Fintype Left] [Fintype Right]
    (leftLaw : FiniteResponseLaw Left)
    (rightLaw : FiniteResponseLaw Right)
    (right : Right) :
    rightResponseMarginal (productResponseLaw leftLaw rightLaw).mass right =
      rightLaw.mass right := by
  rw [rightResponseMarginal_productResponseMass, leftLaw.total, one_mul]

/-- Push a normalized finite law through a deterministic response map. -/
noncomputable def pushforwardResponseLaw
    {Source Response : Type*}
    [Fintype Source] [Fintype Response] [DecidableEq Response]
    (law : FiniteResponseLaw Source)
    (responseOf : Source → Response) :
    FiniteResponseLaw Response where
  mass := pushforwardSignatureMass law.mass responseOf
  nonnegative := fun response =>
    pushforwardSignatureMass_nonnegative
      law.mass law.nonnegative responseOf response
  total := by
    calc
      (∑ response,
          pushforwardSignatureMass law.mass responseOf response) =
        ∑ source, law.mass source :=
          pushforwardSignatureMass_total law.mass responseOf
      _ = 1 := law.total

/-- Deterministic coordinatewise response maps preserve product
factorization. This is the finite response-law form of independent exogenous
components remaining independent after componentwise deterministic maps. -/
theorem product_pushforward_factorizes
    {LeftSource RightSource LeftResponse RightResponse : Type*}
    [Fintype LeftSource] [Fintype RightSource]
    [Fintype LeftResponse] [Fintype RightResponse]
    [DecidableEq LeftResponse] [DecidableEq RightResponse]
    (leftMass : LeftSource → ℚ)
    (rightMass : RightSource → ℚ)
    (leftResponseOf : LeftSource → LeftResponse)
    (rightResponseOf : RightSource → RightResponse) :
    pushforwardSignatureMass
        (productResponseMass leftMass rightMass)
        (fun source : LeftSource × RightSource =>
          (leftResponseOf source.1, rightResponseOf source.2)) =
      productResponseMass
        (pushforwardSignatureMass leftMass leftResponseOf)
        (pushforwardSignatureMass rightMass rightResponseOf) := by
  classical
  funext response
  rcases response with ⟨leftResponse, rightResponse⟩
  unfold pushforwardSignatureMass productResponseMass
  simp only [Fintype.sum_prod_type]
  calc
    (∑ leftSource, ∑ rightSource,
        if (leftResponseOf leftSource, rightResponseOf rightSource) =
            (leftResponse, rightResponse)
        then leftMass leftSource * rightMass rightSource
        else 0) =
      ∑ leftSource, ∑ rightSource,
        (if leftResponseOf leftSource = leftResponse then
          leftMass leftSource else 0) *
        (if rightResponseOf rightSource = rightResponse then
          rightMass rightSource else 0) := by
      apply Finset.sum_congr rfl
      intro leftSource _
      apply Finset.sum_congr rfl
      intro rightSource _
      by_cases left_eq : leftResponseOf leftSource = leftResponse
      · by_cases right_eq : rightResponseOf rightSource = rightResponse
        · simp [left_eq, right_eq]
        · simp [left_eq, right_eq]
      · simp [left_eq]
    _ = ∑ leftSource,
        (if leftResponseOf leftSource = leftResponse then
          leftMass leftSource else 0) *
        (∑ rightSource,
          if rightResponseOf rightSource = rightResponse then
            rightMass rightSource else 0) := by
      apply Finset.sum_congr rfl
      intro leftSource _
      rw [Finset.mul_sum]
    _ =
      (∑ leftSource,
        if leftResponseOf leftSource = leftResponse then
          leftMass leftSource else 0) *
      (∑ rightSource,
        if rightResponseOf rightSource = rightResponse then
          rightMass rightSource else 0) := by
      rw [Finset.sum_mul]

/-- A two-component response law is Markovian at the chosen component
resolution when it is the product of two normalized local response laws. A
component may itself contain unrestricted internal confounding. -/
def IsMarkovianTwoComponentLaw
    {Left Right : Type*} [Fintype Left] [Fintype Right]
    (jointMass : Left × Right → ℚ) : Prop :=
  ∃ leftLaw : FiniteResponseLaw Left,
    ∃ rightLaw : FiniteResponseLaw Right,
      jointMass = productResponseMass leftLaw.mass rightLaw.mass

/-- Independent exogenous component laws, followed by componentwise
deterministic response maps, induce a Markovian response law. -/
theorem independent_exogenous_components_induce_markovian_response_law
    {LeftSource RightSource LeftResponse RightResponse : Type*}
    [Fintype LeftSource] [Fintype RightSource]
    [Fintype LeftResponse] [Fintype RightResponse]
    [DecidableEq LeftResponse] [DecidableEq RightResponse]
    (leftLaw : FiniteResponseLaw LeftSource)
    (rightLaw : FiniteResponseLaw RightSource)
    (leftResponseOf : LeftSource → LeftResponse)
    (rightResponseOf : RightSource → RightResponse) :
    IsMarkovianTwoComponentLaw
      (pushforwardResponseLaw
        (productResponseLaw leftLaw rightLaw)
        (fun source : LeftSource × RightSource =>
          (leftResponseOf source.1, rightResponseOf source.2))).mass := by
  refine
    ⟨pushforwardResponseLaw leftLaw leftResponseOf,
      pushforwardResponseLaw rightLaw rightResponseOf, ?_⟩
  simpa [pushforwardResponseLaw, productResponseLaw] using
    product_pushforward_factorizes
      leftLaw.mass rightLaw.mass leftResponseOf rightResponseOf

/-- Probability of a Boolean counterfactual event under a two-component
response mass. -/
def responseEventMass
    {Left Right : Type*} [Fintype Left] [Fintype Right]
    (jointMass : Left × Right → ℚ)
    (event : Left × Right → Bool) : ℚ :=
  ∑ response, if event response then jointMass response else 0

/-- With the right response law fixed, a Boolean event induces one exact linear
coefficient for every left response state. -/
def fixedRightEventCoefficient
    {Left Right : Type*} [Fintype Right]
    (rightMass : Right → ℚ)
    (event : Left × Right → Bool)
    (left : Left) : ℚ :=
  ∑ right,
    if event (left, right) then rightMass right else 0

/-- A product-law event probability is linear in the left component law when
the right component law is fixed. -/
theorem responseEventMass_product_eq_left_linearObjective
    {Left Right : Type*} [Fintype Left] [Fintype Right]
    (leftMass : Left → ℚ)
    (rightMass : Right → ℚ)
    (event : Left × Right → Bool) :
    responseEventMass
        (productResponseMass leftMass rightMass) event =
      linearObjective
        (fixedRightEventCoefficient rightMass event) leftMass := by
  classical
  unfold responseEventMass linearObjective fixedRightEventCoefficient
  simp only [productResponseMass, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro left _
  calc
    (∑ right,
        if event (left, right) then
          leftMass left * rightMass right else 0) =
      ∑ right,
        leftMass left *
          (if event (left, right) then rightMass right else 0) := by
      apply Finset.sum_congr rfl
      intro right _
      cases event_value : event (left, right) <;>
        simp [event_value]
    _ = leftMass left *
        (∑ right,
          if event (left, right) then rightMass right else 0) := by
      rw [Finset.mul_sum]
    _ =
      (∑ right,
        if event (left, right) then rightMass right else 0) *
        leftMass left := by
      ring

/-- Exact rational dual certificates for the fixed-right LP slice bound the
original Markovian counterfactual event probability. -/
theorem response_event_bounds_of_fixed_right_certificates
    {Left Right Constraint : Type*}
    [Fintype Left] [Fintype Right] [Fintype Constraint]
    (A : Constraint → Left → ℚ)
    (b : Constraint → ℚ)
    (rightMass : Right → ℚ)
    (event : Left × Right → Bool)
    (lower upper : ℚ)
    (lowerCertificate :
      LowerBoundCertificate
        A b (fixedRightEventCoefficient rightMass event) lower)
    (upperCertificate :
      UpperBoundCertificate
        A b (fixedRightEventCoefficient rightMass event) upper)
    (leftMass : Left → ℚ)
    (feasible : LinearFeasible A b leftMass) :
    lower ≤ responseEventMass
        (productResponseMass leftMass rightMass) event ∧
      responseEventMass
          (productResponseMass leftMass rightMass) event ≤ upper := by
  rw [responseEventMass_product_eq_left_linearObjective]
  exact
    ⟨lower_bound_of_certificate
        A b (fixedRightEventCoefficient rightMass event)
        lower lowerCertificate leftMass feasible,
      upper_bound_of_certificate
        A b (fixedRightEventCoefficient rightMass event)
        upper upperCertificate leftMass feasible⟩

/-- Every product mass on two Boolean response components has zero two-by-two
determinant. -/
theorem productResponseMass_determinant
    (leftMass rightMass : Bool → ℚ) :
    productResponseMass leftMass rightMass (true, true) *
        productResponseMass leftMass rightMass (false, false) =
      productResponseMass leftMass rightMass (true, false) *
        productResponseMass leftMass rightMass (false, true) := by
  simp [productResponseMass]
  ring

/-- Every Markovian two-component Boolean response law satisfies the same
polynomial determinant equation. -/
theorem markovianTwoComponent_determinant_zero
    (jointMass : Bool × Bool → ℚ)
    (markovian : IsMarkovianTwoComponentLaw jointMass) :
    jointMass (true, true) * jointMass (false, false) =
      jointMass (true, false) * jointMass (false, true) := by
  rcases markovian with ⟨leftLaw, rightLaw, rfl⟩
  exact productResponseMass_determinant leftLaw.mass rightLaw.mass

/-- Unit mass on one Boolean component state. -/
def boolPointMass (chosen value : Bool) : ℚ :=
  if value = chosen then 1 else 0

/-- A Boolean point mass is a normalized finite response law. -/
def boolPointLaw (chosen : Bool) : FiniteResponseLaw Bool where
  mass := boolPointMass chosen
  nonnegative := by
    intro value
    by_cases same : value = chosen <;>
      simp [boolPointMass, same]
  total := by
    rw [Fintype.sum_bool]
    cases chosen <;> norm_num [boolPointMass]

/-- Pointwise midpoint of two joint response masses. -/
def midpointResponseMass
    {Left Right : Type*}
    (first second : Left × Right → ℚ) :
    Left × Right → ℚ :=
  fun response => (first response + second response) / 2

/-- The family of Markovian two-component response laws is globally nonconvex.
Two degenerate independent response laws have a midpoint with correlated
component responses and a nonzero determinant. -/
theorem markovian_response_laws_not_closed_under_midpoint :
    ∃ first second : Bool × Bool → ℚ,
      IsMarkovianTwoComponentLaw first ∧
        IsMarkovianTwoComponentLaw second ∧
        ¬IsMarkovianTwoComponentLaw
          (midpointResponseMass first second) := by
  let falseLaw : FiniteResponseLaw Bool := boolPointLaw false
  let trueLaw : FiniteResponseLaw Bool := boolPointLaw true
  let first : Bool × Bool → ℚ :=
    productResponseMass falseLaw.mass falseLaw.mass
  let second : Bool × Bool → ℚ :=
    productResponseMass trueLaw.mass trueLaw.mass
  refine ⟨first, second, ?_, ?_, ?_⟩
  · exact ⟨falseLaw, falseLaw, rfl⟩
  · exact ⟨trueLaw, trueLaw, rfl⟩
  · intro midpoint_markovian
    have determinant :=
      markovianTwoComponent_determinant_zero
        (midpointResponseMass first second) midpoint_markovian
    norm_num [midpointResponseMass, first, second,
      falseLaw, trueLaw, boolPointLaw, boolPointMass,
      productResponseMass] at determinant

#print axioms productResponseMass_total
#print axioms product_pushforward_factorizes
#print axioms independent_exogenous_components_induce_markovian_response_law
#print axioms responseEventMass_product_eq_left_linearObjective
#print axioms response_event_bounds_of_fixed_right_certificates
#print axioms markovian_response_laws_not_closed_under_midpoint

end D5.S3.ConceptDynamics.Causal.PartialIdentification.MarkovianResponseLawFactorization
