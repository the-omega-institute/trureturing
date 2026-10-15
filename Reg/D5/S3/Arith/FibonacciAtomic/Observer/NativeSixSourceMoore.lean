import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Observer.NativeSixSourceMoore
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeSixSourceMoore
open _root_.D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport (substitution)
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.ActualCutPartitionRecovery
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeSixSourceCones
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeSixSourceMoore
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
universe u v
abbrev signature : Signature where
  Params := Unit
  State _ := Fiber
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := LiteralRow
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization signature :=
  realize signature (fun _ _ x => canonicalRow P x.val) (fun e => nomatch e)
def bad : Realization signature :=
  realize signature (fun _ _ _ => row) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {Q : Type u} {H : Type v} [Fintype Q] [Fintype H]
    (M : Controller Q H) (entry : Q ⊕ H),
    (∀ x : Fiber, ∃ h tr,
      Run M (substitution x.val) entry tr h ∧
      M.out h = R.readout () () x ∧ tr.length ≤ 3) →
    5 ≤ Fintype.card Q ∧ 5 ≤ Fintype.card H ∧ 10 ≤ Fintype.card (Q ⊕ H)
private theorem badLaw : ¬ arena.{u,v}.Law bad := by
  intro law
  let M : Controller (ULift.{u} (Fin 0)) (ULift.{v} (Fin 1)) :=
    { addr := fun s => Fin.elim0 s.down
      next := fun s => Fin.elim0 s.down
      out := fun _ => row }
  have h := law M (.inr ⟨0⟩) (fun x => ⟨⟨0⟩,[],Run.halt _,rfl,by decide⟩)
  simpa using h.1
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(),_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeSixSourceCones.actual 0,
    _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeSixSourceCones.actual 2,?_⟩
  change canonicalRow P (origin 0) ≠ canonicalRow P (origin 2)
  rw [(six_source_realization.1 0).2.2,(six_source_realization.1 2).2.2]
  decide

def family : Registration arena.{u,v} (type_of% (@three_call_state_obstruction.{u,v})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@three_call_state_obstruction.{u,v},bad,badLaw⟩
  sensitivity := ⟨fun i => ⟨bad,fun j h => (h (Subsingleton.elim j i)).elim,
    rfl,badLaw⟩,fun e => nomatch e⟩
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@three_call_state_obstruction.{u,v})
    (type_of% (realize signature actual.readout actual.anchor)) Type Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.NativeSixSourceMoore.three_call_state_obstruction.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeSixSourceMoore.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v}⟩
  objectArena := .source ⟨arena.{u,v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u,v} ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeSixSourceMoore
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","body","body","arg","body","body","body","arg","fn","arg","arg"],
      stateBinder := 0, functionOperand := false,
      stateOperand := some #["arg","arg"], booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
#print axioms registration
end Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeSixSourceMoore
