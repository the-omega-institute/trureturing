import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Observer.NativeRepeatedPartnerFrontier
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeRepeatedPartnerFrontier
open _root_.D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport (substitution)
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.ActualCutPartitionRecovery
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeSixSourceCones
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeSixSourceMoore
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeRepeatedPartnerFrontier
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
private def solvesWith (R : Realization signature) {Q : Type u} {H : Type v}
    [Fintype Q] [Fintype H] (M : Controller Q H) (entry : Fiber → Q ⊕ H) (r q : Nat) : Prop :=
  (∃ E : Finset (Q ⊕ H), E.card ≤ r ∧ ∀ x, entry x ∈ E) ∧
  ∀ x : Fiber, ∃ h tr, Run M (substitution x.val) (entry x) tr h ∧
    M.out h = R.readout () () x ∧ tr.length ≤ q
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(),_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeSixSourceCones.actual 0,
    _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeSixSourceCones.actual 2,?_⟩
  change canonicalRow P (origin 0) ≠ canonicalRow P (origin 2)
  rw [(six_source_realization.1 0).2.2,(six_source_realization.1 2).2.2]
  decide
namespace Lower
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {Q : Type u} {H : Type v} [Fintype Q] [Fintype H]
    (M : Controller Q H) (entry : Fiber → Q ⊕ H) (r q : Nat), solvesWith R M entry r q →
    5 ≤ r * 2^q ∧ 5 ≤ Fintype.card H ∧ max 5 (10-r) ≤ Fintype.card (Q ⊕ H)
private theorem badLaw : ¬ arena.{u,v}.Law bad := by
  intro law
  let M : Controller (ULift.{u} (Fin 0)) (ULift.{v} (Fin 1)) :=
    { addr := fun s => Fin.elim0 s.down
      next := fun s => Fin.elim0 s.down
      out := fun _ => row }
  let entry : Fiber → ULift.{u} (Fin 0) ⊕ ULift.{v} (Fin 1) := fun _ => .inr ⟨0⟩
  have success : solvesWith bad M entry 1 0 :=
    ⟨⟨{.inr ⟨0⟩},by simp,fun _ => Finset.mem_singleton_self _⟩,
      fun _ => ⟨⟨0⟩,[],Run.halt _,rfl,by decide⟩⟩
  have h := law M entry 1 0 success
  norm_num at h
def family : Registration arena.{u,v} (type_of% (@native_budget_lower.{u,v})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@native_budget_lower.{u,v},bad,badLaw⟩
  sensitivity := ⟨fun i => ⟨bad,fun j h => (h (Subsingleton.elim j i)).elim,
    rfl,badLaw⟩,fun e => nomatch e⟩
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@native_budget_lower.{u,v})
    (type_of% (realize signature actual.readout actual.anchor)) Type Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.NativeRepeatedPartnerFrontier.native_budget_lower.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeRepeatedPartnerFrontier.Lower.family
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
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeRepeatedPartnerFrontier
    definition := some { owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeRepeatedPartnerFrontier, name := `D5.S3.Arith.FibonacciAtomic.Observer.NativeRepeatedPartnerFrontier.Solves, path := #[] }
    coordinates := #[0,1,2,3,4,5,6,7]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","arg","body","body","body","arg","fn","arg","arg"],
      stateBinder := 0, functionOperand := false,
      stateOperand := some #["arg","arg"], booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
#print axioms registration
end Lower
namespace Exact
abbrev arena : Arena where
  signature := signature
  Law R := ∀ r q : Nat, 1 ≤ r →
    (∀ {Q : Type u} {H : Type v} [Fintype Q] [Fintype H]
      (M : Controller Q H) (entry : Fiber → Q ⊕ H), solvesWith R M entry r q →
      5 ≤ r * 2^q ∧ minimum r q ≤ Fintype.card (Q ⊕ H)) ∧
    (5 ≤ r * 2^q → ∃ (n : Nat) (M : Controller (Fin n) (Fin 5))
      (entry : Fiber → Fin n ⊕ Fin 5), solvesWith R M entry r q ∧ n+5 = minimum r q)
private theorem badLaw : ¬ arena.{u,v}.Law bad := by
  intro law
  let M : Controller (ULift.{u} (Fin 0)) (ULift.{v} (Fin 1)) :=
    { addr := fun s => Fin.elim0 s.down
      next := fun s => Fin.elim0 s.down
      out := fun _ => row }
  let entry : Fiber → ULift.{u} (Fin 0) ⊕ ULift.{v} (Fin 1) := fun _ => .inr ⟨0⟩
  have success : solvesWith bad M entry 1 0 :=
    ⟨⟨{.inr ⟨0⟩},by simp,fun _ => Finset.mem_singleton_self _⟩,
      fun _ => ⟨⟨0⟩,[],Run.halt _,rfl,by decide⟩⟩
  have h := (law 1 0 (by decide)).1 M entry success
  norm_num at h
def family : Registration arena.{u,v} (type_of% (@exact_frontier.{u,v})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exact_frontier.{u,v},bad,badLaw⟩
  sensitivity := ⟨fun i => ⟨bad,fun j h => (h (Subsingleton.elim j i)).elim,
    rfl,badLaw⟩,fun e => nomatch e⟩
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@exact_frontier.{u,v})
    (type_of% (realize signature actual.readout actual.anchor)) Type Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.NativeRepeatedPartnerFrontier.exact_frontier.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeRepeatedPartnerFrontier.Exact.family
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
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeRepeatedPartnerFrontier
    definition := some { owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeRepeatedPartnerFrontier, name := `D5.S3.Arith.FibonacciAtomic.Observer.NativeRepeatedPartnerFrontier.Solves, path := #[] }
    coordinates := #[0,1,2,3,4,5,6,7]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","arg","body","body","body","arg","fn","arg","arg"],
      stateBinder := 0, functionOperand := false,
      stateOperand := some #["arg","arg"], booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
#print axioms registration
end Exact
end Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeRepeatedPartnerFrontier
