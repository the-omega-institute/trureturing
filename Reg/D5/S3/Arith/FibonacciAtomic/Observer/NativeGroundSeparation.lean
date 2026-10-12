import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Observer.NativeHistoryCells
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport (Source)
open D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition (Address Reply)
open D5.S3.Arith.FibonacciAtomic.Observer.ActualCutPartitionRecovery
open D5.S3.Arith.FibonacciAtomic.Observer.ActualCutPartitionDecoder
open D5.S3.Arith.FibonacciAtomic.Observer.NativeDepthPatterns
open D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSeparation
open D5.S3.Arith.FibonacciAtomic.Observer.NativeSymbolicRecutting
open D5.S3.Arith.FibonacciAtomic.Observer.NativeCutFibers
open D5.S3.Arith.FibonacciAtomic.Observer.NativeHistoryCells
open D5.S3.Arith.FibonacciAtomic.ActualLeafHistoryRigidity (subtree)
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSeparation
abbrev signature : Signature where
  Params := Σ X : Type, Fintype X × List (Term X × Term X)
  State p := p.1 → Source
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Term p.1 → Source
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ _ v => evaluate v) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (X : Type) (inst : Fintype X) (pairs : List (Term X × Term X)),
    (∀ p ∈ pairs, p.1 ≠ p.2) ↔ ∃ v : X → Source,
      ∀ p ∈ pairs, R.readout () ⟨X,inst,pairs⟩ v p.1 ≠ R.readout () ⟨X,inst,pairs⟩ v p.2

theorem bridge : (type_of% (@simultaneous_ground_separation)) ↔ arena.Law actual := Iff.rfl
theorem actual_law : arena.Law actual := @simultaneous_ground_separation

def bad : Realization signature := realize signature (fun _ _ _ _ => .of true) (fun e => nomatch e)
private theorem bad_law : ¬ arena.Law bad := by
  intro h
  let a : Term Empty := .of (.inl true)
  let b : Term Empty := .of (.inl false)
  have distinct : ∀ p ∈ [(a,b)], p.1 ≠ p.2 := by
    intro p hp
    have ep : p = (a,b) := by simpa using hp
    subst p
    intro eq
    cases eq
  obtain ⟨v,hv⟩ := (h Empty inferInstance [(a,b)]).mp distinct
  exact hv (a,b) (by simp) rfl

def proof : Registration arena (type_of% (@simultaneous_ground_separation)) where
  actual := actual
  bridge := bridge
  variation := ⟨actual_law,bad,bad_law⟩
  sensitivity := ⟨fun i => ⟨bad,fun j h => (h (Subsingleton.elim j i)).elim,rfl,bad_law⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨⟨Unit,inferInstance,[]⟩,(fun _ => .of true),(fun _ => .of false),?_⟩
    intro eq
    have no := congrFun eq (.of (.inr ()))
    cases no

#print axioms proof
noncomputable def simultaneous_ground_separation_registration : LeanInformationAudit.Contract.Registration.{1,1,1,0,0,0,1,0,0,0,0,0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSeparation.simultaneous_ground_separation)
    (Realization signature) (Type → Type) Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSeparation.simultaneous_ground_separation
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSeparation.proof
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨proof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ v => evaluate v) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some (fun X : Type => X → Source)
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSeparation
    definition := none
    coordinates := #[0,1,2]
    readouts := #[{ path := #["body", "body", "body", "arg", "arg", "body", "body", "body", "arg", "fn", "arg", "fn"], stateBinder := 3, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms simultaneous_ground_separation_registration

end Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSeparation
