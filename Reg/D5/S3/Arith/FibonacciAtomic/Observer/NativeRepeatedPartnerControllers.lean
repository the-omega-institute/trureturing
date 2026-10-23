import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Observer.NativeRepeatedPartnerControllers
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeRepeatedPartnerControllers
open _root_.D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport (substitution)
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.ActualCutPartitionRecovery
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeSixSourceCones
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeSixSourceMoore
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeRepeatedPartnerControllers
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
abbrev signature : Signature where
  Params := Unit
  State _ := Fin 5
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := LiteralRow
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization signature := realize signature (fun _ _ h => predecessor h) (fun e => nomatch e)
def bad : Realization signature := realize signature (fun _ _ _ => row) (fun e => nomatch e)
private def succeedsWith (R : Realization signature) {n : Nat} (T : Table n)
    (entry : Fin 5 → Fin n ⊕ Fin 5) (q : Nat) : Prop :=
  ∀ x : Fiber, ∃ (h : Fin 5) (tr : List (Fin n)),
    Run (installed T) (substitution x.val) (entry (acquiredLabel (profile x))) tr h ∧
    R.readout () () h = canonicalRow P x.val ∧ tr.length ≤ q
private def worstWith (R : Realization signature) {n : Nat} (T : Table n)
    (entry : Fin 5 → Fin n ⊕ Fin 5) (q : Nat) : Prop :=
  ∃ (x : Fiber) (h : Fin 5) (tr : List (Fin n)),
    Run (installed T) (substitution x.val) (entry (acquiredLabel (profile x))) tr h ∧
    R.readout () () h = canonicalRow P x.val ∧ tr.length = q
private def attainsWith (R : Realization signature) {n : Nat} (T : Table n)
    (entry : Fin 5 → Fin n ⊕ Fin 5) (r q : Nat) : Prop :=
  Exports entry r ∧ succeedsWith R T entry q ∧ worstWith R T entry q ∧ Reached T entry
abbrev arena : Arena where
  signature := signature
  Law R := attainsWith R ten (fun _ => .inl 0) 1 3 ∧
    attainsWith R nine (fun _ => .inl 0) 1 4 ∧
    attainsWith R eight entryEight 2 2 ∧ attainsWith R seven entrySeven 3 1 ∧
    attainsWith R six entrySix 4 1 ∧ attainsWith R five Sum.inr 5 0
private theorem badLaw : ¬ arena.Law bad := by
  intro law
  obtain ⟨h,tr,run,out,budget⟩ := law.1.2.1
    (_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeSixSourceCones.actual 2)
  change row = canonicalRow P (origin 2) at out
  rw [(six_source_realization.1 2).2.2] at out
  exact (by decide : row ≠ predecessor (label 2)) out
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(),0,1,?_⟩
  change predecessor 0 ≠ predecessor 1
  decide

def family : Registration arena (type_of% (@matching_controllers)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨matching_controllers,bad,badLaw⟩
  sensitivity := ⟨fun i => ⟨bad,fun j h => (h (Subsingleton.elim j i)).elim,rfl,badLaw⟩,
    fun e => nomatch e⟩
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@matching_controllers)
    (type_of% (realize signature actual.readout actual.anchor)) Type Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.NativeRepeatedPartnerControllers.matching_controllers.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeRepeatedPartnerControllers.family
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
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeRepeatedPartnerControllers
    definition := some { owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeRepeatedPartnerControllers, name := `D5.S3.Arith.FibonacciAtomic.Observer.NativeRepeatedPartnerControllers.Succeeds, path := #[] }
    coordinates := #[0,1,2,3]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","arg","fn","arg","fn","arg"],
      stateBinder := 0, functionOperand := false,
      stateOperand := some #["arg"], booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
#print axioms registration
end Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeRepeatedPartnerControllers
