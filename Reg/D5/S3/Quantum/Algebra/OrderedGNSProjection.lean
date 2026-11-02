import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Algebra.OrderedGNSProjection
import Reg.Support.DependentFamily

/-! # Faithful-state internal positivity: full dependent-family audit -/

open _root_.D5.S3.Quantum.Algebra.OrderedGNSProjection
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Quantum.Algebra.OrderedGNSProjection
noncomputable section
open Matrix
open scoped ComplexOrder MatrixOrder
universe u

structure TestParams where
  carrier : Type u
  finite : Fintype carrier
  decEq : DecidableEq carrier
  rho : Matrix carrier carrier ℂ
  y : Matrix carrier carrier ℂ

abbrev testSignature : Signature where
  Params := TestParams.{u}
  State p := Matrix p.carrier p.carrier ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def testActual : Realization testSignature.{u} :=
  realize testSignature (fun _ p q =>
    letI := p.finite
    letI := p.decEq
    (state p.rho (star q * p.y * q)).re) (fun e => nomatch e)

def testBad : Realization testSignature.{u} :=
  realize testSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev testArena : Arena where
  signature := testSignature.{u}
  Law obs :=
    ∀ {n : Type u} [fin : Fintype n] [dec : DecidableEq n]
      (rho : Matrix n n ℂ) (_hrho : rho.PosDef)
      (A : StarSubalgebra ℂ (Matrix n n ℂ))
      (y : Matrix n n ℂ) (_hy : y.IsHermitian) (_hyA : y ∈ A),
      (∀ q ∈ A, 0 ≤ obs.readout () ⟨n, fin, dec, rho, y⟩ q) → y.PosSemidef

private theorem test_bad_law : ¬ testArena.{u}.Law testBad := by
  intro h
  let n := ULift.{u} (Fin 1)
  have hy : (-1 : Matrix n n ℂ).IsHermitian := by simp
  have hn := @h n inferInstance inferInstance 1 Matrix.PosDef.one ⊤ (-1) hy (by trivial) (by
    intro q hq
    exact le_rfl)
  have hd := hn.diag_nonneg (i := ULift.up (0 : Fin 1))
  norm_num at hd

private theorem test_dependence : ObservationalDependence testSignature.{u} testActual := by
  intro i
  refine ⟨⟨ULift.{u} (Fin 1), inferInstance, inferInstance, 1, 1⟩, 0, 1, ?_⟩
  simp [testActual, realize, state, trace]

def positive_source_registration :
    Registration testArena (type_of% @positive_of_internal_compressions.{u}) where
  actual := testActual
  bridge := Iff.rfl
  variation := ⟨@positive_of_internal_compressions, testBad, test_bad_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨testBad, ?_, ?_, test_bad_law⟩
      · intro j hj
        exact (hj (Subsingleton.elim _ _)).elim
      · funext e
        exact nomatch e
    · intro e
      exact nomatch e
  dependence := test_dependence

structure ProjectionParams where
  carrier : Type u
  finite : Fintype carrier
  decEq : DecidableEq carrier
  rho : Matrix carrier carrier ℂ
  faithful : letI := finite; letI := decEq; rho.PosDef

abbrev projectionSignature : Signature where
  Params := ProjectionParams.{u}
  State p := letI := p.finite; letI := p.decEq; StarSubalgebra ℂ (Matrix p.carrier p.carrier ℂ)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := letI := p.finite; letI := p.decEq; Matrix p.carrier p.carrier ℂ →ₗ[ℂ] Matrix p.carrier p.carrier ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def projectionActual : Realization projectionSignature.{u} :=
  realize projectionSignature (fun _ p x =>
    letI := p.finite
    letI := p.decEq
    projection p.rho p.faithful x) (fun e => nomatch e)

def projectionBad : Realization projectionSignature.{u} :=
  realize projectionSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev projectionArena : Arena where
  signature := projectionSignature.{u}
  Law obs :=
    ∀ {n : Type u} [fin : Fintype n] [dec : DecidableEq n]
      (rho : Matrix n n ℂ) (hrho : rho.PosDef) (htrace : trace rho = 1)
      (A : StarSubalgebra ℂ (Matrix n n ℂ)),
      let E := obs.readout () ⟨n, fin, dec, rho, hrho⟩ A
      state rho 1 = 1 ∧
      (∀ x, E x ∈ A) ∧
      (∀ x a, a ∈ A → state rho (star a * E x) = state rho (star a * x)) ∧
      (∀ x y, y ∈ A →
        (∀ a ∈ A, state rho (star a * y) = state rho (star a * x)) → y = E x) ∧
      (RightComparison rho hrho A ↔ ∀ x, E (star x) = star (E x)) ∧
      (RightComparison rho hrho A ↔ Expectation rho A E)

private theorem projection_bad_law : ¬ projectionArena.{u}.Law projectionBad := by
  intro h
  let n := ULift.{u} (Fin 1)
  have ht : trace (1 : Matrix n n ℂ) = 1 := by simp [trace]
  have hl := (@h n inferInstance inferInstance 1 Matrix.PosDef.one ht ⊤).2.2.1 1 1 (by trivial)
  change state (1 : Matrix n n ℂ) (star (1 : Matrix n n ℂ) * (0 : Matrix n n ℂ)) =
    state (1 : Matrix n n ℂ) (star (1 : Matrix n n ℂ) * 1) at hl
  norm_num [state, trace, n] at hl

private theorem projection_dependence :
    ObservationalDependence projectionSignature.{u} projectionActual := by
  intro i
  let n := ULift.{u} (Fin 2)
  let rho : Matrix n n ℂ := (1 / 2 : ℝ) • 1
  have hrho : rho.PosDef := Matrix.PosDef.one.smul (by norm_num : (0 : ℝ) < 1 / 2)
  have ht : trace rho = 1 := by norm_num [rho, trace, n]
  let T := ordered_gns_characterization rho hrho ht
  have hu := (T ⊤).2.2.2.1
  refine ⟨⟨n, inferInstance, inferInstance, rho, hrho⟩, ⊤, ⊥, ?_⟩
  change projection rho hrho ⊤ ≠ projection rho hrho ⊥
  intro he
  let x : Matrix n n ℂ := Matrix.single (ULift.up 0) (ULift.up 1) 1
  have hx := (hu x x (by trivial) (fun _ _ => rfl)).symm
  have hxmem := (T ⊥).2.1 x
  rw [← he, hx] at hxmem
  rcases StarSubalgebra.mem_bot.mp hxmem with ⟨c, hc⟩
  have hij := congrArg (fun z : Matrix n n ℂ => z (ULift.up 0) (ULift.up 1)) hc
  have hne : (ULift.up (0 : Fin 2) : n) ≠ ULift.up 1 := by decide
  norm_num [x, Matrix.algebraMap_matrix_apply, Matrix.single, hne] at hij

def projection_source_registration :
    Registration projectionArena (type_of% @ordered_gns_characterization.{u}) where
  actual := projectionActual
  bridge := Iff.rfl
  variation := ⟨@ordered_gns_characterization, projectionBad, projection_bad_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨projectionBad, ?_, ?_, projection_bad_law⟩
      · intro j hj
        exact (hj (Subsingleton.elim _ _)).elim
      · funext e
        exact nomatch e
    · intro e
      exact nomatch e
  dependence := projection_dependence


def positivity_registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@positive_of_internal_compressions.{u}) (Realization testSignature.{u}) Unit Unit := {
  unitName := `D5.S3.Quantum.Algebra.OrderedGNSProjection.positive_of_internal_compressions.audit
  realizationName := `Reg.D5.S3.Quantum.Algebra.OrderedGNSProjection.positive_source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨testArena⟩
  objectArena := .source ⟨testArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source testArena ⟨positive_source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize testSignature (fun _ p q =>
      letI := p.finite
      letI := p.decEq
      (state p.rho (star q * p.y * q)).re) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Algebra.OrderedGNSProjection
    definition := none
    coordinates := #[0, 1, 2, 3, 6]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "domain", "body", "body", "arg"]
      stateBinder := 9
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

def projection_registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@ordered_gns_characterization.{u}) (Realization projectionSignature.{u}) Unit Unit := {
  unitName := `D5.S3.Quantum.Algebra.OrderedGNSProjection.ordered_gns_characterization.audit
  realizationName := `Reg.D5.S3.Quantum.Algebra.OrderedGNSProjection.projection_source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨projectionArena⟩
  objectArena := .source ⟨projectionArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source projectionArena ⟨projection_source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize projectionSignature (fun _ p A =>
      letI := p.finite
      letI := p.decEq
      projection p.rho p.faithful A) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Algebra.OrderedGNSProjection
    definition := none
    coordinates := #[0, 1, 2, 3, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg", "arg", "arg", "arg", "arg", "arg", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms positive_source_registration
#print axioms projection_source_registration
#print axioms positivity_registration
#print axioms projection_registration

end
end Reg.D5.S3.Quantum.Algebra.OrderedGNSProjection
