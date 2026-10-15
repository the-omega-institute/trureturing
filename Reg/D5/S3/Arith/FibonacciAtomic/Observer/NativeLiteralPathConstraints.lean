import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Arith.FibonacciAtomic.Observer.NativeLiteralPathConstraints

set_option autoImplicit false
set_option relaxedAutoImplicit false

open _root_.D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport (Source)
open _root_.D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition (Address Reply readout)
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeLiteralPathConstraints
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeLiteralPathConstraints

abbrev signature : Signature where
  Params := Σ _ : (Nat → Nat), Σ _ : (Nat → Source), Term
  State _ := Source
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Source
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p u => value u p.1 p.2.1 p.2.2) (fun i => nomatch i)

def bad : Realization signature :=
  realize signature (fun _ _ _ => .of false) (fun i => nomatch i)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (u : Source) (e : Nat → Nat) (x : Nat → Source)
    (p : Address) (y : Reply) (V : Term),
    (compile p y V).Holds u e x ↔ readout p (R.readout () ⟨e,x,V⟩ u) = y

private theorem bad_law : ¬ arena.Law bad := by
  intro h
  have no := (h (.of true) (fun _ => 0) (fun _ => .of true) [] .alpha
    (label true)).mp (by rfl)
  cases no

def proof : Registration arena (type_of% (@compile_exact)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@compile_exact, bad, bad_law⟩
  sensitivity := ⟨fun i => ⟨bad, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, bad_law⟩, fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨⟨(fun _ => 0),(fun _ => .of true),original 0⟩, .of true, .of false, ?_⟩
    intro h
    cases h

noncomputable def registration : LeanInformationAudit.Contract.Registration.{0,1,1,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeLiteralPathConstraints.compile_exact)
    (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeLiteralPathConstraints.compile_exact
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeLiteralPathConstraints.proof
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨proof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p u => value u p.1 p.2.1 p.2.2)
    (fun i => nomatch i))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeLiteralPathConstraints
    definition := none
    coordinates := #[1,2,5]
    readouts := #[{ path := #["body","body","body","body","body","body","arg","fn","arg","arg"], stateBinder := 0, functionOperand := false, stateOperand := some #["fn","fn","fn","arg"], booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeLiteralPathConstraints
