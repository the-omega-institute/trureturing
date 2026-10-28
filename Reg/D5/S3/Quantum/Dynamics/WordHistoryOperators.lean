import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Quantum.Dynamics.WordHistoryOperators

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Dynamics.WordHistoryOperators
noncomputable section
universe u
namespace Reg.D5.S3.Quantum.Dynamics.WordHistoryOperators

abbrev signature : Signature where
  Params := Type u
  State A := WordHilbert A
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ A := WordHilbert A → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ _ => True) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {Alphabet : Type u} (g : Alphabet),
    ¬ ∃ A : WordHilbert Alphabet →L[ℂ] WordHilbert Alphabet,
      ∀ (f : WordHilbert Alphabet) (hf : FiniteSupport f),
        R.readout () Alphabet (A f) (number f hf)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  exact h (ULift.up ()) ⟨0, fun _ _ => trivial⟩

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  let f : WordHilbert (ULift.{u} Unit) := lp.single 2 [] 1
  refine ⟨ULift.{u} Unit, 0, f, ?_⟩
  intro h
  have he := congrFun h 0
  have hf : f = 0 := he.mp rfl
  have hz := congrArg (fun x : WordHilbert (ULift.{u} Unit) => x []) hf
  simp [f] at hz

def family : Registration arena.{u} (type_of% (@number_unbounded.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@number_unbounded, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@number_unbounded.{u})
    (type_of% (realize signature.{u} (fun _ _ x y => x = y) (fun e => nomatch e)))
    Unit Unit := {
  unitName := `D5.S3.Quantum.Dynamics.WordHistoryOperators.number_unbounded.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Dynamics.WordHistoryOperators.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Dynamics.WordHistoryOperators
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "arg", "arg", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms family
#print axioms registration
end Reg.D5.S3.Quantum.Dynamics.WordHistoryOperators
