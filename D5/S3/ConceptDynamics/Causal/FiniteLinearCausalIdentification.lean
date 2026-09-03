/- GID: D5/S3/ConceptDynamics/Causal/FiniteLinearCausalIdentification
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Causal/FiniteLinearCausalIdentification
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite causal response models compile layered assumptions and scalar queries to exact rational linear certificates. -/

import D5.S0.Certificates.LinearObjectiveDual

/- Library-search audit trail (2026-09-03):
   * `LinearObjectiveDual` supplies the generic rational primal-dual certificate
     layer independently of causal semantics.
   * The causal lane contains concrete response-type and coupling models, but no
     reusable object that records finite response types, layered causal
     constraints, and a scalar query as one exact linear system.
   * This module is a semantic adapter. It does not claim that every causal
     assumption is linear; cross-world factorization belongs to the separate
     nonlinear lane. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Causal.FiniteLinearCausalIdentification

open D5.S0.Certificates.RationalFarkas
open D5.S0.Certificates.LinearObjectiveDual

/-- Provenance of a compiled causal constraint. The label has no effect on
soundness, but prevents data, structural, and sensitivity assumptions from
being silently conflated. -/
inductive ConstraintLayer where
  | data
  | structural
  | sensitivity
  deriving DecidableEq, Repr

/-- A finite response-type causal identification problem compiled to exact
rational inequalities. Equalities are represented by paired inequalities and
probability nonnegativity is represented by explicit rows. -/
structure FiniteLinearCausalProblem
    (Response Constraint : Type*)
    [Fintype Response] [Fintype Constraint] where
  layer : Constraint -> ConstraintLayer
  row : Constraint -> Response -> ℚ
  rhs : Constraint -> ℚ
  queryCoefficient : Response -> ℚ

/-- Feasibility of a response-type mass vector under all compiled assumptions. -/
def Feasible
    {Response Constraint : Type*}
    [Fintype Response] [Fintype Constraint]
    (problem : FiniteLinearCausalProblem Response Constraint)
    (mass : Response -> ℚ) : Prop :=
  LinearFeasible problem.row problem.rhs mass

/-- The scalar counterfactual query evaluated on a response-type mass vector. -/
def Query
    {Response Constraint : Type*}
    [Fintype Response] [Fintype Constraint]
    (problem : FiniteLinearCausalProblem Response Constraint)
    (mass : Response -> ℚ) : ℚ :=
  linearObjective problem.queryCoefficient mass

/-- A lower dual certificate for the compiled causal query. -/
abbrev LowerCertificate
    {Response Constraint : Type*}
    [Fintype Response] [Fintype Constraint]
    (problem : FiniteLinearCausalProblem Response Constraint)
    (lower : ℚ) :=
  LowerBoundCertificate
    problem.row problem.rhs problem.queryCoefficient lower

/-- An upper dual certificate for the compiled causal query. -/
abbrev UpperCertificate
    {Response Constraint : Type*}
    [Fintype Response] [Fintype Constraint]
    (problem : FiniteLinearCausalProblem Response Constraint)
    (upper : ℚ) :=
  UpperBoundCertificate
    problem.row problem.rhs problem.queryCoefficient upper

/-- A feasible response-type distribution attaining an exact query value. -/
abbrev QueryWitness
    {Response Constraint : Type*}
    [Fintype Response] [Fintype Constraint]
    (problem : FiniteLinearCausalProblem Response Constraint)
    (value : ℚ) :=
  PrimalWitness
    problem.row problem.rhs problem.queryCoefficient value

/-- Exact lower endpoint of the compiled causal query. -/
def IsExactLowerEndpoint
    {Response Constraint : Type*}
    [Fintype Response] [Fintype Constraint]
    (problem : FiniteLinearCausalProblem Response Constraint)
    (lower : ℚ) : Prop :=
  IsExactLowerBound
    problem.row problem.rhs problem.queryCoefficient lower

/-- Exact upper endpoint of the compiled causal query. -/
def IsExactUpperEndpoint
    {Response Constraint : Type*}
    [Fintype Response] [Fintype Constraint]
    (problem : FiniteLinearCausalProblem Response Constraint)
    (upper : ℚ) : Prop :=
  IsExactUpperBound
    problem.row problem.rhs problem.queryCoefficient upper

/-- Replaying a lower certificate proves the causal query bound for every
feasible response-type mass vector. -/
theorem query_lower_bound_of_certificate
    {Response Constraint : Type*}
    [Fintype Response] [Fintype Constraint]
    (problem : FiniteLinearCausalProblem Response Constraint)
    (lower : ℚ)
    (certificate : LowerCertificate problem lower)
    (mass : Response -> ℚ)
    (feasible : Feasible problem mass) :
    lower <= Query problem mass := by
  exact lower_bound_of_certificate
    problem.row problem.rhs problem.queryCoefficient lower
    certificate mass feasible

/-- Replaying an upper certificate proves the causal query bound for every
feasible response-type mass vector. -/
theorem query_upper_bound_of_certificate
    {Response Constraint : Type*}
    [Fintype Response] [Fintype Constraint]
    (problem : FiniteLinearCausalProblem Response Constraint)
    (upper : ℚ)
    (certificate : UpperCertificate problem upper)
    (mass : Response -> ℚ)
    (feasible : Feasible problem mass) :
    Query problem mass <= upper := by
  exact upper_bound_of_certificate
    problem.row problem.rhs problem.queryCoefficient upper
    certificate mass feasible

/-- A matching lower dual certificate and primal response-type witness prove
that the proposed causal lower bound is exact. -/
theorem exact_lower_endpoint_of_certificate_and_witness
    {Response Constraint : Type*}
    [Fintype Response] [Fintype Constraint]
    (problem : FiniteLinearCausalProblem Response Constraint)
    (lower : ℚ)
    (certificate : LowerCertificate problem lower)
    (witness : QueryWitness problem lower) :
    IsExactLowerEndpoint problem lower := by
  exact exact_lower_bound_of_certificate_and_witness
    problem.row problem.rhs problem.queryCoefficient lower
    certificate witness

/-- A matching upper dual certificate and primal response-type witness prove
that the proposed causal upper bound is exact. -/
theorem exact_upper_endpoint_of_certificate_and_witness
    {Response Constraint : Type*}
    [Fintype Response] [Fintype Constraint]
    (problem : FiniteLinearCausalProblem Response Constraint)
    (upper : ℚ)
    (certificate : UpperCertificate problem upper)
    (witness : QueryWitness problem upper) :
    IsExactUpperEndpoint problem upper := by
  exact exact_upper_bound_of_certificate_and_witness
    problem.row problem.rhs problem.queryCoefficient upper
    certificate witness

/-- A complete rational primal-dual payload proves both exact endpoints of a
finite linear causal query. -/
theorem exact_endpoints_of_primal_dual_payload
    {Response Constraint : Type*}
    [Fintype Response] [Fintype Constraint]
    (problem : FiniteLinearCausalProblem Response Constraint)
    (lower upper : ℚ)
    (lowerCertificate : LowerCertificate problem lower)
    (upperCertificate : UpperCertificate problem upper)
    (lowerWitness : QueryWitness problem lower)
    (upperWitness : QueryWitness problem upper) :
    IsExactLowerEndpoint problem lower /\
      IsExactUpperEndpoint problem upper := by
  exact
    ⟨exact_lower_endpoint_of_certificate_and_witness
        problem lower lowerCertificate lowerWitness,
      exact_upper_endpoint_of_certificate_and_witness
        problem upper upperCertificate upperWitness⟩

/-- Every constraint can be audited at its declared semantic layer without
changing the matrix consumed by the certificate checker. -/
theorem constraint_layer_is_exhaustive
    {Response Constraint : Type*}
    [Fintype Response] [Fintype Constraint]
    (problem : FiniteLinearCausalProblem Response Constraint)
    (constraint : Constraint) :
    problem.layer constraint = ConstraintLayer.data \/
      problem.layer constraint = ConstraintLayer.structural \/
      problem.layer constraint = ConstraintLayer.sensitivity := by
  cases problem.layer constraint <;> simp

#print axioms query_lower_bound_of_certificate
#print axioms query_upper_bound_of_certificate
#print axioms exact_endpoints_of_primal_dual_payload

end D5.S3.ConceptDynamics.Causal.FiniteLinearCausalIdentification
