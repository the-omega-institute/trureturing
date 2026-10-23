import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Arith.FibonacciAtomic.Observer.NativePayloadHistoryInstallation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

open _root_.D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport (Source)
open _root_.D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition (Address readout acquisitionTrace)
open _root_.D5.S3.Arith.FibonacciAtomic.ActualLeafHistoryRigidity (subtree)
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativePrefixIdentityReflection (MixedExpr eval)
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativePayloadHistoryInstallation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativePayloadHistoryInstallation

abbrev signature : Signature where
  Params := Address
  State _ := Source
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Option Source
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p U => subtree p U) (fun e => nomatch e)

def bad : Realization signature :=
  realize signature (fun _ _ _ => none) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {ι : Type} (E : MixedExpr ι) (loc : ι → Address)
    (p : Address) (U : Source) (z : ι → Source),
    (∀ i ∈ names E, subtree (loc i) U = some (z i)) →
    (Holds U (compile loc p E) ↔ R.readout () p U = some (eval z E))

private theorem bad_law : ¬ arena.Law bad := by
  intro h
  have no := (h (ι := Empty) (.ground (.of true)) (fun i => nomatch i) []
    (.of true) (fun i => nomatch i) (by simp [names])).mp
    (by simp [Holds, compile, groundRecords, acquisitionTrace, Record.Holds, readout])
  cases no

def proof : Registration arena (type_of% (@payload_history_exact)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨payload_history_exact, bad, bad_law⟩
  sensitivity := ⟨fun i => ⟨bad, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, bad_law⟩, fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨[], .of true, .of false, ?_⟩
    intro h
    cases h

noncomputable def registration : LeanInformationAudit.Contract.Registration.{0,1,1,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativePayloadHistoryInstallation.payload_history_exact)
    (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativePayloadHistoryInstallation.payload_history_exact
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativePayloadHistoryInstallation.proof
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨proof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p U => subtree p U) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativePayloadHistoryInstallation
    definition := none
    coordinates := #[3]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","arg","fn","arg","fn"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms proof
end Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativePayloadHistoryInstallation
