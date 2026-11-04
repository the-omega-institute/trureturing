import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeEffectiveAtomicGuard
import Reg.Support.DependentFamily

/-! Observe the computed finite syntax while retaining the complete original
source theorem and its unrestricted semantic telescope. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeEffectiveAtomicGuard
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeAffineImageSaturation
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGuardedFreeExtension
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGuardedImageSaturation
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeCompletionPrefixLifting
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.CompletionHomogeneousFixedPoints
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open PresburgerArithmetic LeanInformationAudit

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeEffectiveAtomicGuard

noncomputable section

abbrev signature : Signature where
  Params := Unit
  State _ := Formula
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Formula
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev actual : Realization signature := realize signature (fun _ _ f => f) (fun e => nomatch e)
abbrev rejected : Realization signature := realize signature (fun _ _ _ => constant false) (fun e => nomatch e)

def observed (R : Realization signature) (f : Formula) : Formula := R.readout () () f

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(),constant true,constant false,?_⟩
  intro eq
  cases eq

namespace Atomic

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n k m s : Nat} (I : Input n k m) (guarded : Guarded I.equations)
    (mode : Mode s m) (p : Fin n → Nat) (legal : Legal I p) (E : Expression k m) (j : Nat),
    (observed R (atomicGuard I mode E j)).holds (environment p) ↔
      evaluate (ranks I p) (canonical I.equations (ranks I p) guarded mode) E = atomic j

private theorem actual_law : arena.Law actual := by exact @atomic_guard_correct

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  let I : Input 0 0 0 := {
    equations := Fin.elim0
    filters := []
    indices := Fin.elim0
    guard := .qf .truth }
  let p : Fin 0 → Nat := Fin.elim0
  have guarded : Guarded I.equations := fun i => Fin.elim0 i
  have legal : Legal I p := ⟨rfl,fun i => Fin.elim0 i⟩
  let mode : Mode 0 0 := Fin.elim0
  have impossible := (law I guarded mode p legal (.ground (.of true)) 0).mpr rfl
  cases impossible

def evidence : Registration arena (type_of% (@atomic_guard_correct)) where
  actual := actual
  bridge := by rfl
  variation := ⟨actual_law,rejected,rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,fun j h => (h (Subsingleton.elim j i)).elim,rfl,rejected_law⟩,
    fun e => nomatch e⟩
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@atomic_guard_correct) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.NativeEffectiveAtomicGuard.atomic_guard_correct.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeEffectiveAtomicGuard.Atomic.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ f => f) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some Formula
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end Atomic

namespace Constant

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (b : Bool) (xs : List Int),
    (observed R (constant b)).holds xs ↔ b = true

private theorem actual_law : arena.Law actual := by exact constant_holds

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have impossible := (law true []).mpr rfl
  cases impossible

def evidence : Registration arena (type_of% (constant_holds)) where
  actual := actual
  bridge := by rfl
  variation := ⟨actual_law,rejected,rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,fun j h => (h (Subsingleton.elim j i)).elim,rfl,rejected_law⟩,
    fun e => nomatch e⟩
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (constant_holds) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.NativeEffectiveAtomicGuard.constant_holds.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeEffectiveAtomicGuard.Constant.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ f => f) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some Formula
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end Constant
end
end Reg.D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeEffectiveAtomicGuard
