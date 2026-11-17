import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSQuotient
import Reg.Support.SingleDependentReadout

set_option autoImplicit false
noncomputable section
namespace Reg.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSQuotient
open _root_.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSQuotient
open _root_.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSMarginalBirationality
open _root_.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSDensityRecovery
open _root_.D5.S3.Quantum.TensorNetworks.PeriodicMPSParentIntersection (Bond Word)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Algebra
open Matrix MvPolynomial

private abbrev Observation := Matrix (Word 3) (Word 3) ℂ
private def witness (m : ℕ) : Word (3 + m) → ℂ :=
  mpsState (3 + m)
    (_root_.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSTwoSiteMinimality.originalCore 0)
    (_root_.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSTwoSiteMinimality.originalCore 1)
    ![1,0] ![1,2]

namespace Witness
abbrev signature : Signature where
  Params := ℕ
  State _ := ∀ m : ℕ, MvPolynomial (ObservationIndex ⊕ ObservationIndex) ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := MvPolynomial (ObservationIndex ⊕ ObservationIndex) ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ m family => family m)
  (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => 0)
  (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ m : ℕ,
    let ψ := mpsState (3 + m)
      (_root_.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSTwoSiteMinimality.originalCore 0)
      (_root_.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSTwoSiteMinimality.originalCore 1)
      ![1, 0] ![1, 2]
    ψ ∈ openBoundaryMPS (3 + m) ∧
    eval (_root_.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSDensityGenericity.realCoordinates
      (fun ij => rawPrefix 3 m ψ ij.1 ij.2))
      (R.readout () m quotientLocusPolynomial) ≠ 0 ∧
    eval (_root_.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSDensityGenericity.realCoordinates
      (_root_.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSDensityGenericity.fixedTensor
        (rawPrefix 3 m ψ)))
      _root_.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSDensityGenericity.recoveryPolynomial ≠ 0 ∧
    boundaryGram m (rawPrefix 3 m ψ) 0 0 ≠ 0
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hn := (h 0).2.1
  exact hn (map_zero _)
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨0, (fun _ => 0), (fun _ => 1), ?_⟩
  intro he
  exact zero_ne_one he
def family : Registration arena (type_of% (@quotient_locus_witness)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨quotient_locus_witness, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@quotient_locus_witness) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSQuotient.Witness.unit
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSQuotient.Witness.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ m family => family m) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSQuotient
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "arg", "fn", "arg", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end Witness
namespace Gram
abbrev signature : Signature where
  Params := ℕ
  State _ := ∀ m : ℕ, Observation → Bond
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Observation → Bond
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ m family => family m)
  (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ _ => Complex.I • (1 : Bond)) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (m : ℕ) (ψ : Word (3 + m) → ℂ),
    ψ ∈ openBoundaryMPS (3 + m) →
    eval (_root_.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSDensityGenericity.realCoordinates
      (_root_.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSDensityGenericity.fixedTensor
        (rawPrefix 3 m ψ)))
      _root_.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSDensityGenericity.recoveryPolynomial ≠ 0 →
    let t := _root_.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSDensityGenericity.fixedTensor
      (rawPrefix 3 m ψ)
    ∃ q : Fin 2 → ℂ,
      ψ = mpsState (3 + m) (canonicalCore t 0) (canonicalCore t 1) (reconstructedLeft t) q ∧
      R.readout () m boundaryGram (rawPrefix 3 m ψ) = vecMulVec q (star q)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨q,_,hq⟩ := h 0 (witness 0) (quotient_locus_witness 0).1
    (quotient_locus_witness 0).2.2.1
  have he := congrFun (congrFun hq 0) 0
  simp only [rejected, realize, vecMulVec_apply, Pi.star_apply,
    Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at he
  change Complex.I = q 0 * (starRingEnd ℂ) (q 0) at he
  rw [Complex.mul_conj] at he
  have hi := congrArg Complex.im he
  norm_num at hi
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨0, (fun _ _ => 0), (fun _ _ => 1), ?_⟩
  intro he
  have hh := congrFun (congrFun (congrFun he 0) 0) 0
  exact zero_ne_one hh

def family : Registration arena (type_of% (@actual_boundary_gram)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_boundary_gram,rejected,rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@actual_boundary_gram) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSQuotient.Gram.unit
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSQuotient.Gram.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ m family => family m) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSQuotient
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "body", "arg", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end Gram
namespace Representative
abbrev signature : Signature where
  Params := ℕ
  State _ := ∀ m : ℕ, Observation → Quotient
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Observation → Quotient
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ m family => family m)
  (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ _ => (0,-1,0)) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (m : ℕ) (ψ : Word (3 + m) → ℂ),
    ψ ∈ openBoundaryMPS (3 + m) →
    eval (_root_.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSDensityGenericity.realCoordinates
      (_root_.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSDensityGenericity.fixedTensor
        (rawPrefix 3 m ψ)))
      _root_.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSDensityGenericity.recoveryPolynomial ≠ 0 →
    boundaryGram m (rawPrefix 3 m ψ) 0 0 ≠ 0 →
    let p := R.readout () m quotientCoordinates (rawPrefix 3 m ψ)
    0 < p.2.1 ∧ ∃ z : ℂ, ‖z‖ = 1 ∧
      ψ = z • mpsState (3 + m)
        (_root_.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSTwoSiteMinimality.core p 0)
        (_root_.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSTwoSiteMinimality.core p 1)
        (_root_.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSTwoSiteMinimality.left p)
        (positiveBoundary p)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := (h 0 (witness 0) (quotient_locus_witness 0).1
    (quotient_locus_witness 0).2.2.1 (quotient_locus_witness 0).2.2.2).1
  norm_num [rejected, realize] at hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨0, (fun _ _ => (0,0,0)), (fun _ _ => (0,1,0)), ?_⟩
  intro he
  have hh := congrArg (fun f : Observation → Quotient => (f 0).2.1) he
  exact zero_ne_one hh

def family : Registration arena (type_of% (@actual_quotient_representative)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_quotient_representative,rejected,rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@actual_quotient_representative) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSQuotient.Representative.unit
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSQuotient.Representative.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ m family => family m) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSQuotient
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "value", "fn"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end Representative
namespace Retraction
abbrev signature : Signature where
  Params := ℕ
  State _ := ∀ m : ℕ, Observation → Quotient
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Observation → Quotient
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ m family => family m)
  (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ _ => (0,-1,0)) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (m : ℕ) (p : Quotient), 0 < p.2.1 →
    eval (_root_.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSDensityGenericity.realCoordinates
      (_root_.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSDensityGenericity.fixedTensor
        (quotientObservation 3 m p)))
      _root_.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSDensityGenericity.recoveryPolynomial ≠ 0 →
    R.readout () m quotientCoordinates (quotientObservation 3 m p) = p
private def parameter : Quotient :=
  ((_root_.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSTwoSiteMinimality.witnessParameter 0).1,
    400, (17 : ℂ) / 5)
private theorem parameter_observation : quotientObservation 3 0 parameter = rawPrefix 3 0 (witness 0) := by
  let θ := _root_.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSTwoSiteMinimality.witnessParameter 0
  let η : Quotient := (parameter.1,1,parameter.2.2)
  have hs : _root_.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSTwoSiteMinimality.state 3 θ =
      (20 : ℂ) • _root_.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSTwoSiteMinimality.state 3 η := by
    have hr : _root_.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSTwoSiteMinimality.right θ =
        (20 : ℂ) • _root_.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSTwoSiteMinimality.right η := by
      ext i; fin_cases i <;> norm_num [θ,η,parameter,
        _root_.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSTwoSiteMinimality.right,
        _root_.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSTwoSiteMinimality.witnessParameter]
    funext w
    simp only [_root_.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSTwoSiteMinimality.state,
      state_formula, hr, mulVec_smul, dotProduct_smul, Pi.smul_apply,smul_eq_mul]
    rfl
  have hw := _root_.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSTwoSiteMinimality.witness_gauge 0
  change _root_.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSTwoSiteMinimality.state 3 θ = witness 0 at hw
  rw [← hw,hs]
  have hC : amplitudeColumns 3 0
      ((20 : ℂ) • _root_.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSTwoSiteMinimality.state 3 η) =
      (20 : ℂ) • amplitudeColumns 3 0
        (_root_.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSTwoSiteMinimality.state 3 η) := rfl
  rw [rawPrefix,hC,conjTranspose_smul,Matrix.smul_mul,Matrix.mul_smul,smul_smul]
  norm_num [quotientObservation,parameter,η]
  rfl
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hg := (quotient_locus_witness 0).2.2.1
  change eval (_root_.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSDensityGenericity.realCoordinates
    (_root_.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSDensityGenericity.fixedTensor
      (rawPrefix 3 0 (witness 0))))
    _root_.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSDensityGenericity.recoveryPolynomial ≠ 0 at hg
  rw [← parameter_observation] at hg
  have he := h 0 parameter (by norm_num [parameter]) hg
  have hh := congrArg (fun p : Quotient => p.2.1) he
  norm_num [rejected,realize,parameter] at hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨0, (fun _ _ => (0,0,0)), (fun _ _ => (0,1,0)), ?_⟩
  intro he
  have hh := congrArg (fun f : Observation → Quotient => (f 0).2.1) he
  exact zero_ne_one hh

def family : Registration arena (type_of% (@quotient_retraction)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨quotient_retraction,rejected,rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@quotient_retraction) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSQuotient.Retraction.unit
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSQuotient.Retraction.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ m family => family m) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSQuotient
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end Retraction

namespace Rational
abbrev signature : Signature where
  Params := ℕ
  State _ := ∀ m : ℕ, QuotientRealIndex → MvPolynomial (ObservationIndex ⊕ ObservationIndex) ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := QuotientRealIndex → MvPolynomial (ObservationIndex ⊕ ObservationIndex) ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ m family => family m)
  (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ _ => 0)
  (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (m : ℕ) (Q : Observation),
eval (_root_.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSDensityGenericity.realCoordinates
      (fun ij => Q ij.1 ij.2)) (quotientLocusPolynomial m) ≠ 0 →
   Fintype.card QuotientRealIndex = 13 ∧
    (∀ i : QuotientRealIndex,
      0 < eval (_root_.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSDensityGenericity.realCoordinates (fun ij => Q ij.1 ij.2))
        (R.readout () m quotientRealDenominator i) ∧
      eval (_root_.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSDensityGenericity.realCoordinates (fun ij => Q ij.1 ij.2))
        (quotientRealNumerator m i) /
      eval (_root_.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSDensityGenericity.realCoordinates (fun ij => Q ij.1 ij.2))
        (R.readout () m quotientRealDenominator i) =
      quotientRealCoordinates (quotientCoordinates m Q) i) ∧
    0 < positiveGramDenominator m Q ∧
    (∀ i j, boundaryGram m Q i j =
      PhasePolynomial.actual (positiveGramPolynomial m i j) (fun ij => Q ij.1 ij.2) /
        (positiveGramDenominator m Q : ℂ)) ∧
    (∀ (k a : ℕ) (u v : Word k) (imaginary : Bool) (p : Quotient),
      eval (quotientRealCoordinates p) (quotientObservationPolynomial k a u v imaginary) =
        if imaginary then (quotientObservation k a p u v).im
        else (quotientObservation k a p u v).re) ∧
    boundaryGram m Q 0 0 ≠ 0
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hp := ((h 0 (rawPrefix 3 0 (witness 0)) (quotient_locus_witness 0).2.1).2.1
    (.inl 0)).1
  norm_num [rejected,realize] at hp
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨0, (fun _ _ => 0), (fun _ _ => 1), ?_⟩
  intro he
  have hh := congrFun he (.inl 0)
  exact zero_ne_one hh

def family : Registration arena (type_of% (@rational_quotient_inverse)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨rational_quotient_inverse,rejected,rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@rational_quotient_inverse) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSQuotient.Rational.unit
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSQuotient.Rational.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ m family => family m) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSQuotient
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "arg", "fn", "arg", "body", "fn", "arg", "arg", "arg", "fn"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end Rational
#print axioms Retraction.registration
#print axioms Rational.registration
#print axioms Witness.registration
#print axioms Gram.registration
#print axioms Representative.registration
namespace Conjugate
abbrev signature : Signature where
  Params := Unit
  State _ := ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization signature := realize signature (fun _ _ x => x) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law A := ∀ (ι : Type*) (p : _root_.D5.S3.Quantum.Algebra.PhasePolynomial.Poly ι) (z : ι → ℂ),
    A.readout () () (_root_.D5.S3.Quantum.Algebra.PhasePolynomial.actual (polynomialConjugate p) z) =
      star (_root_.D5.S3.Quantum.Algebra.PhasePolynomial.actual p z)
private lemma rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h PUnit 1 (fun _ => 0)
  norm_num [rejected,realize,_root_.D5.S3.Quantum.Algebra.PhasePolynomial.actual] at hh
private lemma dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(),0,1,?_⟩
  norm_num [actual,realize]
def source_registration : Registration arena (type_of% @polynomialConjugate_eval) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@polynomialConjugate_eval,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected,fun j hj => (hj (Subsingleton.elim j i)).elim,rfl,rejected_law⟩
    · intro e; exact nomatch e
  dependence := dependence
def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@polynomialConjugate_eval) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSQuotient.polynomialConjugate_eval.__information_unit
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSQuotient.Conjugate.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }
end Conjugate
end Reg.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSQuotient
