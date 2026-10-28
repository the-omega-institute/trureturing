import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Foundation.FiniteKrausChannel
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Quantum.Foundation.FiniteKrausChannel

open _root_.D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

abbrev signature.{u, v, k, s} : Signature where
  Params := Σ A : Type u, Type s
  State p := Matrix p.1 p.1 p.2
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Matrix p.1 p.1 p.2 → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual.{u, v, k, s} : Realization signature.{u, v, k, s} :=
  realize signature (fun _ _ X => Eq X) (fun e => nomatch e)

def rejected.{u, v, k, s} : Realization signature.{u, v, k, s} :=
  realize signature (fun _ _ _ _ => True) (fun e => nomatch e)

abbrev arena.{u, v, k, s} : Arena where
  signature := signature.{u, v, k, s}
  Law R := ∀ {A : Type u} {B : Type v} [Fintype A] [DecidableEq A] [Fintype B]
    {κ : Type k} [Fintype κ] {S : Type s} [CommSemiring S] [Star S]
    (M N : κ → Matrix B A S),
    R.readout () ⟨A, S⟩ (∑ i, (N i).conjTranspose * M i) 1 →
      (MatrixMap.of_kraus M N).IsTracePreserving

theorem rejected_law.{u, v, k, s} : ¬ arena.{u, v, k, s}.Law rejected := by
  intro h
  have hbad := @h (ULift.{u} Unit) (ULift.{v} Unit)
    inferInstance inferInstance inferInstance (ULift.{k} Unit) inferInstance
    (ULift.{s} ℂ) inferInstance inferInstance (fun _ => 0) (fun _ => 0) trivial
  have htrace := hbad (1 : Matrix (ULift.{u} Unit) (ULift.{u} Unit) (ULift.{s} ℂ))
  simpa [MatrixMap.of_kraus, Matrix.trace] using htrace

theorem dependence.{u, v, k, s} :
    ObservationalDependence signature.{u, v, k, s} actual := by
  intro i
  refine ⟨⟨ULift.{u} Unit, ULift.{s} ℂ⟩, 0, 1, ?_⟩
  intro h
  have he := congrFun h 0
  change ((0 : Matrix (ULift.{u} Unit) (ULift.{u} Unit) (ULift.{s} ℂ)) = 0) =
    (1 = 0) at he
  simpa using he

def source_registration.{u, v, k, s} :
    Registration arena.{u, v, k, s}
      (type_of% (@MatrixMap.IsTracePreserving.of_kraus_isTracePreserving.{u, v, k, s})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@MatrixMap.IsTracePreserving.of_kraus_isTracePreserving.{u, v, k, s},
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration.{u, v, k, s} :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@MatrixMap.IsTracePreserving.of_kraus_isTracePreserving.{u, v, k, s})
      (Realization signature.{u, v, k, s}) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Foundation.FiniteKrausChannel.unit
  realizationName := `Reg.D5.S3.Quantum.Foundation.FiniteKrausChannel.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ X => Eq X) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Foundation.FiniteKrausChannel
    definition := none
    coordinates := #[0, 7]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "domain", "fn"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.Foundation.FiniteKrausChannel
