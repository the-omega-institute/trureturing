import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.LocalTwoStepRecognizer
import Reg.Support.DependentFamily

/-! The actual decoder distinguishes a leaf and its legal two-step cherry. -/

namespace Reg.D5.S3.Arith.FibonacciAtomic.LocalTwoStepRecognizer

open _root_.D5.S3.Arith.FibonacciAtomic.LocalTwoStepRecognizer
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := Unit
  State _ := Shape
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Option Labelled
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x => decode x) (fun x => nomatch x)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => none) (fun x => nomatch x)

def arena : Arena where
  signature := signature
  Law F :=
    (∀ x u, F.readout () () x = some u ↔ Expanded u x) ∧
    (∀ x, Grammar x ↔ ∃! u, Expanded u x) ∧
    (∀ x y u, Unordered x y → decode x = some u →
      ∃ v, decode y = some v ∧ Unordered u v) ∧
    (∀ x y, Unordered x y → (decode x = none ↔ decode y = none)) ∧
    (∀ u v x y, Expanded u x → Expanded v y → (Unordered x y ↔ Unordered u v)) ∧
    (∀ u x, Expanded u x → unorderedImage (treeClass u) = treeClass x) ∧
    Function.Injective unorderedImage

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hc := (h.1 cherry alpha).mpr ⟨_, _, .alphaToBeta, .betaLeft, rfl⟩
  cases hc

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨(), tip, cherry, ?_⟩
  intro h
  cases h

def family : Registration arena (type_of% exact_local_two_step) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨exact_local_two_step, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j hj => (hj (@Subsingleton.elim Unit _ j i)).elim,
    rfl, rejected_law⟩, fun a => nomatch a⟩
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    exact_local_two_step (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.LocalTwoStepRecognizer.unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.LocalTwoStepRecognizer.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.LocalTwoStepRecognizer
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg", "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

end Reg.D5.S3.Arith.FibonacciAtomic.LocalTwoStepRecognizer
