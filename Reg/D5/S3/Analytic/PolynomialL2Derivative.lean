import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.PolynomialL2Derivative
import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout

open _root_.D5.S3.Analytic.PolynomialL2Derivative
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Polynomial MeasureTheory Set
open scoped Interval ComplexConjugate

namespace Reg.D5.S3.Analytic.PolynomialL2Derivative
noncomputable section

/-- The source coordinates are d and p, packed in their lexical order.
The false role observes the derivative value; the true role observes the polynomial value.
The Boolean role dictionary fixes that same order for source selection. -/
abbrev signature : Signature where
  Params := Σ _d : ℕ, ℂ[X]
  State _ := ℝ
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

/-- Both observations are the native operands, over all complex polynomials. -/
def actual : Realization signature :=
  realize signature
    (fun i q x => if i then q.2.eval (x : ℂ) else q.2.derivative.eval (x : ℂ))
    (fun e => nomatch e)

/-- Change only the derivative observation, keeping the value observation. -/
private def derivativeChanged : Realization signature :=
  realize signature
    (fun i q x => if i then q.2.eval (x : ℂ) else 1)
    (fun e => nomatch e)

/-- Change only the value observation, keeping the derivative observation. -/
private def valueChanged : Realization signature :=
  realize signature
    (fun i q x => if i then 0 else q.2.derivative.eval (x : ℂ))
    (fun e => nomatch e)

/-- The entire degree theorem, including its WithBot degree premise and d=0.
No analytic premise or source parameter is replaced by an assumed estimate. -/
def degreeArena : Arena where
  signature := signature
  Law R := ∀ (d : ℕ) (p : ℂ[X]) (_hp : p.degree < (d : WithBot ℕ)),
    (∫ x : ℝ in 0..1, ‖R.readout false ⟨d, p⟩ x‖ ^ 2) ≤
      (d : ℝ) ^ 4 * (∫ x : ℝ in 0..1, ‖R.readout true ⟨d, p⟩ x‖ ^ 2)

/-- The entire natDegree theorem, retaining even the explicit 1 <= d binder. -/
def natDegreeArena : Arena where
  signature := signature
  Law R := ∀ (d : ℕ) (_hd : 1 ≤ d) (p : ℂ[X]) (_hp : p.natDegree < d),
    (∫ x : ℝ in 0..1, ‖R.readout false ⟨d, p⟩ x‖ ^ 2) ≤
      (d : ℝ) ^ 4 * (∫ x : ℝ in 0..1, ‖R.readout true ⟨d, p⟩ x‖ ^ 2)

private theorem degree_derivativeChanged : ¬ degreeArena.Law derivativeChanged := by
  intro h
  have hf := h 0 (0 : ℂ[X]) (by simp)
  norm_num [derivativeChanged, realize] at hf

private theorem degree_valueChanged : ¬ degreeArena.Law valueChanged := by
  intro h
  have hf := h 2 (X : ℂ[X]) (by norm_num)
  norm_num [valueChanged, realize] at hf

private theorem natDegree_derivativeChanged : ¬ natDegreeArena.Law derivativeChanged := by
  intro h
  have hf := h 1 (by norm_num) (0 : ℂ[X]) (by norm_num)
  norm_num [derivativeChanged, realize] at hf

private theorem natDegree_valueChanged : ¬ natDegreeArena.Law valueChanged := by
  intro h
  have hf := h 2 (by norm_num) (X : ℂ[X]) (by norm_num)
  norm_num [valueChanged, realize] at hf

/-- Each intervention is in the same family; the other role and every anchor
are held fixed. The supplied failures concern the full varied law. -/
private theorem sensitivity_of_failures (law : Realization signature → Prop)
    (hd : ¬ law derivativeChanged) (hv : ¬ law valueChanged) :
    Sensitivity ⟨signature, law⟩ actual := by
  constructor
  · intro i
    cases i
    · refine ⟨derivativeChanged, ?_, rfl, hd⟩
      intro j hj
      cases j
      · exact (hj rfl).elim
      · rfl
    · refine ⟨valueChanged, ?_, rfl, hv⟩
      intro j hj
      cases j
      · rfl
      · exact (hj rfl).elim
  · intro e
    exact nomatch e

/-- Actual observations vary with the real state, even in admissible fibers:
d=3,p=X*X for the derivative and d=2,p=X for the value. -/
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  · refine ⟨⟨3, (X : ℂ[X]) * X⟩, 0, 1, ?_⟩
    norm_num [actual, realize, Polynomial.derivative_mul]
  · refine ⟨⟨2, (X : ℂ[X])⟩, 0, 1, ?_⟩
    norm_num [actual, realize]

/-- Clause-complete source type <-> actual law, actual positivity, variation,
role sensitivity, and genuine observational dependence. -/
def degreeRegistration : Registration degreeArena
    (type_of% (@complex_polynomial_derivative_l2_of_degree)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨complex_polynomial_derivative_l2_of_degree,
    derivativeChanged, degree_derivativeChanged⟩
  sensitivity := sensitivity_of_failures degreeArena.Law
    degree_derivativeChanged degree_valueChanged
  dependence := actual_dependence

def natDegreeRegistration : Registration natDegreeArena
    (type_of% (@complex_polynomial_derivative_l2)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨complex_polynomial_derivative_l2,
    derivativeChanged, natDegree_derivativeChanged⟩
  sensitivity := sensitivity_of_failures natDegreeArena.Law
    natDegree_derivativeChanged natDegree_valueChanged
  dependence := actual_dependence

/-- Target GID: D5/S3/Analytic/PolynomialL2Derivative.complex_polynomial_derivative_l2_of_degree.
The target operand binds the original unapplied theorem. The readout is an
application of the existing enrolled DependentFamily.realize template. -/
def registration_of_degree : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@complex_polynomial_derivative_l2_of_degree)
    (type_of% (realize signature
      (fun i q x => if i then q.2.eval (x : ℂ) else q.2.derivative.eval (x : ℂ))
      (fun e => nomatch e))) Unit Unit where
  unitName := `D5.S3.Analytic.PolynomialL2Derivative.complex_polynomial_derivative_l2_of_degree.audit
  realizationName := `Reg.D5.S3.Analytic.PolynomialL2Derivative.degreeRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨degreeArena⟩
  objectArena := .source ⟨degreeArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source degreeArena ⟨degreeRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun i q x => if i then q.2.eval (x : ℂ) else q.2.derivative.eval (x : ℂ))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.PolynomialL2Derivative
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "fn", "fn", "fn", "arg",
        "body", "fn", "arg", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }, {
      path := #["body", "body", "body", "arg", "arg", "fn", "fn", "fn", "arg",
        "body", "fn", "arg", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

/-- Target GID: D5/S3/Analytic/PolynomialL2Derivative.complex_polynomial_derivative_l2.
The source telescope has d, hd, p, hp, followed by each integral's own x. -/
def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@complex_polynomial_derivative_l2)
    (type_of% (realize signature
      (fun i q x => if i then q.2.eval (x : ℂ) else q.2.derivative.eval (x : ℂ))
      (fun e => nomatch e))) Unit Unit where
  unitName := `D5.S3.Analytic.PolynomialL2Derivative.complex_polynomial_derivative_l2.audit
  realizationName := `Reg.D5.S3.Analytic.PolynomialL2Derivative.natDegreeRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨natDegreeArena⟩
  objectArena := .source ⟨natDegreeArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source natDegreeArena ⟨natDegreeRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun i q x => if i then q.2.eval (x : ℂ) else q.2.derivative.eval (x : ℂ))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.PolynomialL2Derivative
    definition := none
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "fn", "fn", "fn", "arg",
        "body", "fn", "arg", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }, {
      path := #["body", "body", "body", "body", "arg", "arg", "fn", "fn", "fn", "arg",
        "body", "fn", "arg", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]


private lemma legendre_zero : legendreC 0 = (1 : ℂ[X]) := by
  ext k
  cases k <;> simp [legendreC, Polynomial.coeff_shiftedLegendre, Polynomial.coeff_one]

namespace Expansion
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ (fun _ => ℕ → ℂ) (fun _ => ℂ[X])
def actual : Realization signature :=
  realize signature (fun _ d a => expansion d a) (fun e => nomatch e)
private def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ (d : ℕ) (p : ℂ[X]) (_hp : p.degree < (d : WithBot ℕ)),
    ∃ a : ℕ → ℂ, R.readout () d a = p
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hf := h 1 (1 : ℂ[X]) (by norm_num)
  obtain ⟨a, ha⟩ := hf
  exact zero_ne_one (show (0 : ℂ[X]) = 1 from ha)
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, (fun _ => 0), (fun _ => 1), ?_⟩
  norm_num [actual, realize, expansion, legendre_zero]
def family : Registration arena (type_of% (@exists_expansion)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exists_expansion, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@exists_expansion) (Realization signature) Unit Unit where
  unitName := `D5.S3.Analytic.PolynomialL2Derivative.exists_expansion.audit
  realizationName := `Reg.D5.S3.Analytic.PolynomialL2Derivative.Expansion.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ d a => expansion d a) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.PolynomialL2Derivative
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "arg", "body", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Expansion

namespace Mixed
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature
    (Σ _d : ℕ, ℕ → ℂ) (fun _ => ℕ → ℂ) (fun _ => ℂ)
def actual : Realization signature :=
  realize signature (fun _ p b => moment (expansion p.1 p.2) ((expansion p.1 b).map (starRingEnd ℂ))) (fun e => nomatch e)
private def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ (d : ℕ) (a b : ℕ → ℂ),
    R.readout () ⟨d, a⟩ b =
      ∑ n ∈ Finset.range d, a n * conj (b n) / (2 * (n : ℂ) + 1)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hf := h 0 (fun _ => 0) (fun _ => 0)
  norm_num [rejected, realize] at hf
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨1, (fun _ => 1)⟩, (fun _ => 0), (fun _ => 1), ?_⟩
  norm_num [actual, realize, moment, expansion, legendre_zero]
def family : Registration arena (type_of% (@mixed_expansion)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@mixed_expansion, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@mixed_expansion) (Realization signature) Unit Unit where
  unitName := `D5.S3.Analytic.PolynomialL2Derivative.mixed_expansion.audit
  realizationName := `Reg.D5.S3.Analytic.PolynomialL2Derivative.Mixed.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p b => moment (expansion p.1 p.2) ((expansion p.1 b).map (starRingEnd ℂ))) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.PolynomialL2Derivative
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Mixed

namespace Primitive
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ z => ‖z‖) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

/-- The complete finite telescope, with arbitrary complex coefficients and
the empty expansion. One common family varies both native norm operations. -/
def arena : Arena where
  signature := signature
  Law R := ∀ (d q : ℕ) (hq : 1 ≤ q) (a : ℕ → ℂ)
    (ha : ∀ n < q, a n = 0),
    (∫ x in Icc (0 : ℝ) 1,
      (R.readout () () (∫ t in (0 : ℝ)..x, (expansion d a).eval (t : ℂ))) ^ 2) ≤
      (1 / (4 * (q : ℝ) * ((q : ℝ) + 1))) *
        (∫ x in Icc (0 : ℝ) 1, (R.readout () () ((expansion d a).eval (x : ℂ))) ^ 2)


/-- At d=0,q=1,a=0 the constant-one observation demands 1≤1/8. -/
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hf := h 0 1 (by norm_num) (fun _ => 0) (by intro n hn; rfl)
  norm_num [rejected, realize, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hf

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  change ‖(0 : ℂ)‖ ≠ ‖(1 : ℂ)‖
  norm_num

def family : Registration arena (type_of% @complex_legendre_primitive_gap) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@complex_legendre_primitive_gap, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

/-- Both source occurrences select the native norm function. -/
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@complex_legendre_primitive_gap) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Analytic.PolynomialL2Derivative.complex_legendre_primitive_gap.audit
  realizationName := `Reg.D5.S3.Analytic.PolynomialL2Derivative.Primitive.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => ‖z‖) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.PolynomialL2Derivative
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body",
        "fn", "arg", "arg", "body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }, {
      path := #["body", "body", "body", "body", "body",
        "arg", "arg", "arg", "body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Primitive

end
end Reg.D5.S3.Analytic.PolynomialL2Derivative
