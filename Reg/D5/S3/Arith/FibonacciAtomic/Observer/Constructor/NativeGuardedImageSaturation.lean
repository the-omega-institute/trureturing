import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeGuardedImageSaturation
import Reg.Support.DependentFamily

/-! Joint filter acceptance is observed on one whole completed assignment.
The law keeps canonical membership and the exact same-mode existential. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGuardedFreeExtension
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGuardedImageSaturation
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeImageSaturationInterface
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeCompletionPrefixLifting
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.CompletionHomogeneousFixedPoints
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeGuardedImageSaturation

noncomputable section

abbrev signature : Signature where
  Params := Σ k : Nat, Σ m : Nat, (Fin k → Nat) × List (Filter k m)
  State q := Fin q.2.1 → CompletionTree
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev actual : Realization signature := realize signature
  (fun _ q v => @decide (Passes q.2.2.1 v q.2.2.2) (Classical.propDecidable _))
  (fun e => nomatch e)

abbrev rejected : Realization signature := realize signature
  (fun _ _ v => @decide (∀ i, IsFinite (v i)) (Classical.propDecidable _))
  (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {k m : Nat} (S : System k m) (p : Fin k → Nat)
    (guarded : Guarded S) (filters : List (Filter k m)) (mode : Mode (threshold filters) m),
    Satisfies S p (canonical S p guarded mode) ∧
    InMode S (threshold filters) mode (canonical S p guarded mode) ∧
    ((∃ v, Satisfies S p v ∧ InMode S (threshold filters) mode v ∧
        R.readout () ⟨k, m, p, filters⟩ v = true) ↔
      R.readout () ⟨k, m, p, filters⟩ (canonical S p guarded mode) = true)

private theorem actual_law : arena.Law actual := by
  simpa only [arena, actual, realize, decide_eq_true_eq] using (@normalized_saturation)

private theorem rejected_law : ¬ arena.Law rejected := by
  classical
  intro law
  let S : System 0 1 := fun _ => none
  let p : Fin 0 → Nat := Fin.elim0
  have guarded : Guarded S := by intro i a j eq; cases eq
  let mode : Mode (threshold ([] : List (Filter 0 1))) 1 := fun _ => none
  let v : Fin 1 → CompletionTree := fun _ => atomic 2
  have sat : Satisfies S p v := by intro i E eq; cases eq
  have vm : InMode S (threshold []) mode v := by
    intro i hi j bound eq
    have rank := _root_.D5.S3.Arith.FibonacciAtomic.Observer.CompletionPositiveDriftRegion.atomic_injective eq
    change j ≤ 0 + 1 at bound
    omega
  have finite : ∀ i, IsFinite (v i) := by
    intro i
    exact _root_.D5.S3.Arith.FibonacciAtomic.Observer.CompletionPositiveDriftRegion.atomic_finite 2
  have accepted : rejected.readout () ⟨0, 1, p, []⟩ v = true := by
    exact @decide_eq_true (∀ i : Fin 1, IsFinite (v i)) (Classical.propDecidable _) finite
  have bad := ((law S p guarded [] mode).2.2).mp ⟨v, sat, vm, accepted⟩
  have cf := (Classical.choose_spec
    (guarded_extension S p guarded (canonicalFree mode)).exists).2 (0 : Fin 1) rfl
  change canonical S p guarded mode 0 = Omega at cf
  have allFinite : ∀ i, IsFinite (canonical S p guarded mode i) :=
    @of_decide_eq_true (∀ i : Fin 1, IsFinite (canonical S p guarded mode i))
      (Classical.propDecidable _) bad
  exact _root_.D5.S3.Arith.FibonacciAtomic.Observer.CompletionPositiveDriftRegion.omega_not_finite
    (cf ▸ allFinite 0)

private theorem readout_depends : ObservationalDependence signature actual := by
  intro role
  let p : Fin 0 → Nat := Fin.elim0
  let filters : List (Filter 0 1) := [(.var 0 0, 1)]
  let v : Fin 1 → CompletionTree := fun _ => leaf false
  let w : Fin 1 → CompletionTree := fun _ => leaf true
  have yes : Passes p v filters := by
    intro E t ht
    have eq : (E, t) = (.var 0 0, 1) := List.mem_singleton.mp ht
    cases eq
    exact ⟨leaf true, rho_alpha⟩
  have no : ¬ Passes p w filters := by
    intro passes
    have image := passes (.var 0 0) 1 (List.mem_singleton_self _)
    have h := (native_image_iff 1 (leaf true)).mp image
    rcases h with h | h | ⟨U, V, h, _⟩
    · have first : atomic 1 = leaf false := rho_alpha
      rw [first] at h
      have tag := congrArg (fun X => (PFunctor.M.dest X).1) h
      cases tag
    · have second : atomic 2 = node (leaf false) (leaf true) := by
        change rho (rho (leaf true)) = _
        rw [rho_alpha, rho_beta]
      rw [second] at h
      have tag := congrArg (fun X => (PFunctor.M.dest X).1) h
      cases tag
    · have tag := congrArg (fun X => (PFunctor.M.dest X).1) h
      cases tag
  refine ⟨⟨0, 1, p, filters⟩, v, w, ?_⟩
  simp only [actual, realize, yes, no, decide_true, decide_false]
  decide

def evidence : Registration arena (type_of% (@normalized_saturation)) where
  actual := actual
  bridge := by simp only [actual, realize, decide_eq_true_eq]
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := readout_depends

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@normalized_saturation) (Realization signature) (Nat → Type) Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.NativeGuardedImageSaturation.normalized_saturation.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeGuardedImageSaturation.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ q v => @decide (Passes q.2.2.1 v q.2.2.2) (Classical.propDecidable _))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some (fun m : Nat => Fin m → CompletionTree)
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeGuardedImageSaturation
    definition := none
    coordinates := #[0, 1, 3, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg", "arg",
        "fn", "arg", "arg", "body", "arg", "arg"]
      stateBinder := 7
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeGuardedImageSaturation

open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGuardedAtomicReplacement
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeImageSaturationInterface
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.CompletionPositiveDriftRegion (atomic_finite omega_not_finite)

open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGuardedImageSaturation
namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeGuardedImageSaturation.ExposedSuppliers
noncomputable section

abbrev completionSignature : Signature where
  Params := Unit
  State _ := CompletionTree
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := CompletionTree
  Anchor := Empty
  finiteAnchor := inferInstance
abbrev actual : Realization completionSignature :=
  realize completionSignature (fun _ _ X => X) (fun e => nomatch e)
abbrev rejected : Realization completionSignature :=
  realize completionSignature (fun _ _ _ => leaf true) (fun e => nomatch e)
def observed (R : Realization completionSignature) (X : CompletionTree) : CompletionTree :=
  R.readout () () X
private theorem dependence : ObservationalDependence completionSignature actual := by
  intro role
  refine ⟨(),leaf true,leaf false,?_⟩
  intro eq
  have tag := congrArg (fun X => (PFunctor.M.dest X).1) eq
  cases tag

private theorem alpha_not_image_one : ¬ NativeImage 1 (leaf true) := by
  rintro ⟨X,eq⟩
  obtain ⟨l,rank,_⟩ := atomic_predecessor 1 0 X eq
  omega

namespace Coinduction
abbrev arena : Arena where
  signature := completionSignature
  Law R := ∀ (k : Nat) (Q : CompletionTree → Prop),
    (∀ X, Q X → X = atomic k ∨ X = atomic (k+1) ∨
      ∃ U V, X = node U V ∧ Q U ∧ Q V) → ∀ X, Q X → NativeImage k (observed R X)
private theorem actual_law : arena.Law actual := @image_coinduction
private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  apply alpha_not_image_one
  exact law 1 (fun X => X = Omega) (by
    intro X eq
    subst X
    exact Or.inr (Or.inr ⟨Omega,Omega,omega_node,rfl,rfl⟩)) Omega rfl

def evidence : Registration arena (type_of% (@image_coinduction)) where
  actual := actual
  bridge := by rfl
  variation := ⟨actual_law,rejected,rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,fun j h => (h (Subsingleton.elim j i)).elim,rfl,rejected_law⟩,
    fun e => nomatch e⟩
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@image_coinduction) (Realization completionSignature) Type Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.NativeGuardedImageSaturation.image_coinduction.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeGuardedImageSaturation.ExposedSuppliers.Coinduction.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize completionSignature (fun _ _ x => x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some CompletionTree
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end Coinduction

namespace LargeShift
abbrev arena : Arena where
  signature := completionSignature
  Law R := ∀ (k a : Nat) (X : CompletionTree), k ≤ a →
    NativeImage k (observed R (rho^[a] X))
private theorem actual_law : arena.Law actual := @image_shift_large
private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  exact alpha_not_image_one (law 1 1 Omega le_rfl)

def evidence : Registration arena (type_of% (@image_shift_large)) where
  actual := actual
  bridge := by rfl
  variation := ⟨actual_law,rejected,rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,fun j h => (h (Subsingleton.elim j i)).elim,rfl,rejected_law⟩,
    fun e => nomatch e⟩
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@image_shift_large) (Realization completionSignature) Type Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.NativeGuardedImageSaturation.image_shift_large.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeGuardedImageSaturation.ExposedSuppliers.LargeShift.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize completionSignature (fun _ _ x => x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some CompletionTree
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end LargeShift

namespace CancelShift
abbrev arena : Arena where
  signature := completionSignature
  Law R := ∀ (k a : Nat) (X : CompletionTree), a ≤ k →
    (NativeImage k (rho^[a] X) ↔ NativeImage (k-a) (observed R X))
private theorem actual_law : arena.Law actual := @image_shift_cancel
private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  apply alpha_not_image_one
  apply (law 2 1 Omega (by omega)).mp
  refine ⟨Omega,?_⟩
  rw [iterate_omega,iterate_omega]

def evidence : Registration arena (type_of% (@image_shift_cancel)) where
  actual := actual
  bridge := by rfl
  variation := ⟨actual_law,rejected,rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,fun j h => (h (Subsingleton.elim j i)).elim,rfl,rejected_law⟩,
    fun e => nomatch e⟩
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@image_shift_cancel) (Realization completionSignature) Type Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.NativeGuardedImageSaturation.image_shift_cancel.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeGuardedImageSaturation.ExposedSuppliers.CancelShift.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize completionSignature (fun _ _ x => x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some CompletionTree
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end CancelShift

end
end Reg.D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeGuardedImageSaturation.ExposedSuppliers
