import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.LocalWiring.UnaryMooreSharpness
import Reg.Support.DependentFamily

/-! Genuine emitted digit at the chosen cut from the selected real witness. -/

namespace Reg.D5.S3.Arith.FibonacciAtomic.LocalWiring.UnaryMooreSharpness

open _root_.D5.S3.Arith.FibonacciAtomic.LocalWiring.UnaryMooreSharpness
open _root_.D5.S3.Arith.FibonacciAtomic.LocalWiring.UnaryMooreSeparation (Machine)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := Σ _ : Nat, Nat
  State _ := Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p side => witnessOutput p.1 p.2 side) (fun a => nomatch a)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun a => nomatch a)

def arena : Arena where
  signature := signature
  Law F := ∀ (K : Nat) (_hK : 1 ≤ K),
    (∀ (v : Nat), v < 2*K-1 →
      (∀ side : Bool, F.readout () ⟨K, v⟩ side = side) ∧
      Fintype.card (Fin (K-1+1)) ≤ K ∧
      (∀ i < v, (witnesses (K-1) v).1.emit i = (witnesses (K-1) v).2.emit i) ∧
      (witnesses (K-1) v).1.emit v ≠ (witnesses (K-1) v).2.emit v) ∧
    (∀ v : Nat, UniformlySeparates K v ↔ 2*K-1 ≤ v)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have bad := ((h 2 (by decide)).1 1 (by decide)).1 true
  change false = true at bad
  cases bad

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨⟨2, 1⟩, false, true, ?_⟩
  change witnessOutput 2 1 false ≠ witnessOutput 2 1 true
  decide

def family : Registration arena (type_of% unary_moore_sharpness) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨unary_moore_sharpness, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j hj => (hj (@Subsingleton.elim Unit _ j i)).elim,
    rfl, rejected_law⟩, fun a => nomatch a⟩
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@unary_moore_sharpness) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.LocalWiring.UnaryMooreSharpness.unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.LocalWiring.UnaryMooreSharpness.family
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
    owner := `D5.S3.Arith.FibonacciAtomic.LocalWiring.UnaryMooreSharpness
    definition := none
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "body", "body", "fn", "arg", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit

end Reg.D5.S3.Arith.FibonacciAtomic.LocalWiring.UnaryMooreSharpness
