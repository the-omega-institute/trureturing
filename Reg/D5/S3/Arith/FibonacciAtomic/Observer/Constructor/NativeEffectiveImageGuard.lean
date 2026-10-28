import Reg.D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeEffectiveAtomicGuard
import D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeEffectiveImageGuard

set_option autoImplicit false
set_option relaxedAutoImplicit false

open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeEffectiveImageGuard
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeEffectiveAtomicGuard
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeAffineImageSaturation
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGuardedFreeExtension
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGuardedImageSaturation
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeCompletionPrefixLifting
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open PresburgerArithmetic LeanInformationAudit

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeEffectiveImageGuard

noncomputable section

abbrev signature := NativeEffectiveAtomicGuard.signature
abbrev actual := NativeEffectiveAtomicGuard.actual
abbrev rejected := NativeEffectiveAtomicGuard.rejected
abbrev observed := NativeEffectiveAtomicGuard.observed

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(),constant true,constant false,?_⟩
  intro eq
  cases eq

namespace Normalized

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n k m : Nat} (I : Input n k m) (guarded : Guarded I.equations)
    (mode : Mode (threshold I.filters) m) (p : Fin n → Nat),
    (observed R (imageGuard I mode)).holds (environment p) ↔
      Legal I p ∧ Passes (ranks I p)
        (canonical I.equations (ranks I p) guarded mode) I.filters

private theorem actual_law : arena.Law actual := @effective_image_guard

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  let I : Input 0 0 0 := { equations := Fin.elim0, filters := [], indices := Fin.elim0,
    guard := .qf .truth }
  let p : Fin 0 → Nat := Fin.elim0
  have guarded : Guarded I.equations := fun i => Fin.elim0 i
  have legal : Legal I p := ⟨rfl,fun i => Fin.elim0 i⟩
  let mode : Mode (threshold I.filters) 0 := Fin.elim0
  have passes : Passes (ranks I p) (canonical I.equations (ranks I p) guarded mode) I.filters :=
    fun E t h => False.elim (List.not_mem_nil h)
  have impossible := (law I guarded mode p).mpr ⟨legal,passes⟩
  cases impossible

def evidence : Registration arena (type_of% (@effective_image_guard)) where
  actual := actual
  bridge := by rfl
  variation := ⟨actual_law,rejected,rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,fun j h => (h (Subsingleton.elim j i)).elim,rfl,rejected_law⟩,
    fun e => nomatch e⟩
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@effective_image_guard) (Realization signature) (Nat → Type) Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.NativeEffectiveImageGuard.effective_image_guard.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeEffectiveImageGuard.Normalized.evidence
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

end Normalized

namespace Original

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n k m : Nat} (I : Input n k m) (mode : EffectiveMode I) (p : Fin n → Nat),
    ((observed R (originalImageGuard I mode)).holds (environment p) ↔
      Legal I p ∧ SourcePasses I p (effectiveCanonical I mode p)) ∧
    ((observed R (originalImageGuard I mode)).holds (environment p) ↔
      Legal I p ∧ ∃ v, SourceSatisfies I p v ∧ EffectiveInMode I mode p v ∧ SourcePasses I p v)

private theorem actual_law : arena.Law actual := @original_effective_image_guard

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  let I : Input 0 0 0 := { equations := Fin.elim0, filters := [], indices := Fin.elim0,
    guard := .qf .truth }
  let p : Fin 0 → Nat := Fin.elim0
  have legal : Legal I p := ⟨rfl,fun i => Fin.elim0 i⟩
  let mode : EffectiveMode I := Fin.elim0
  have passes : SourcePasses I p (effectiveCanonical I mode p) :=
    fun E t h => False.elim (List.not_mem_nil h)
  have impossible := (law I mode p).1.mpr ⟨legal,passes⟩
  cases impossible

def evidence : Registration arena (type_of% (@original_effective_image_guard)) where
  actual := actual
  bridge := by rfl
  variation := ⟨actual_law,rejected,rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,fun j h => (h (Subsingleton.elim j i)).elim,rfl,rejected_law⟩,
    fun e => nomatch e⟩
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@original_effective_image_guard) (Realization signature) (Nat → Type) Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.NativeEffectiveImageGuard.original_effective_image_guard.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeEffectiveImageGuard.Original.evidence
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

end Original
end
end Reg.D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeEffectiveImageGuard
