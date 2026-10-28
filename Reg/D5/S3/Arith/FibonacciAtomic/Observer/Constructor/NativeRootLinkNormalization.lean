import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeRootLinkNormalization
import Reg.Support.DependentFamily

/-! The observation evaluates an actual reconstruction expression on a whole
completed assignment. Its law is the original two-sided normalization theorem. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGuardedFreeExtension
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeRootLinkNormalization
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeCompletionPrefixLifting
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeRootLinkNormalization

noncomputable section

abbrev signature : Signature where
  Params := Σ k : Nat, Σ m : Nat, (Fin k → Nat) × Expression k m
  State q := Fin q.2.1 → CompletionTree
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := CompletionTree
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev actual : Realization signature := realize signature
  (fun _ q v => evaluate q.2.2.1 v q.2.2.2) (fun e => nomatch e)

abbrev rejected : Realization signature := realize signature
  (fun _ _ _ => leaf true) (fun e => nomatch e)

def maps (R : Realization signature) {k m : Nat} (p : Fin k → Nat)
    (P : Fin m → Expression k m) (v : Fin m → CompletionTree) : Fin m → CompletionTree :=
  fun i => R.readout () ⟨k, m, p, P i⟩ v

def correspondence (R : Realization signature) {k m : Nat}
    (S : System k m) (T : Presentation k m) : Prop :=
  ∀ p : Fin k → Nat,
    (∀ v, Satisfies S p v →
      Satisfies T.equations p (maps R p T.project v) ∧
      maps R p T.reconstruct (maps R p T.project v) = v) ∧
    (∀ w, Satisfies T.equations p w →
      Satisfies S p (maps R p T.reconstruct w) ∧
      maps R p T.project (maps R p T.reconstruct w) = w)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {k m : Nat} (S : System k m),
    ∃ T : Presentation k m, Guarded T.equations ∧ correspondence R S T

private theorem actual_law : arena.Law actual := by
  exact @root_link_normalization

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  let S : System 0 1 := fun _ => none
  obtain ⟨T, _, corr⟩ := law S
  let p : Fin 0 → Nat := Fin.elim0
  let v : Fin 1 → CompletionTree := fun _ => leaf false
  have sat : Satisfies S p v := by intro i E eq; cases eq
  have eq := congrFun ((corr p).1 v sat).2 (0 : Fin 1)
  have eq : leaf true = leaf false := eq
  have tags := congrArg (fun X => (PFunctor.M.dest X).1) eq
  cases tags

private theorem readout_depends : ObservationalDependence signature actual := by
  intro role
  let p : Fin 0 → Nat := Fin.elim0
  refine ⟨⟨0, 1, p, .var 0 0⟩, (fun _ => leaf true), (fun _ => leaf false), ?_⟩
  intro eq
  have tags := congrArg (fun X => (PFunctor.M.dest X).1) eq
  cases tags

def evidence : Registration arena (type_of% (@root_link_normalization)) where
  actual := actual
  bridge := by rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := readout_depends

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@root_link_normalization) (Realization signature) (Nat → Type) Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.NativeRootLinkNormalization.root_link_normalization.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeRootLinkNormalization.evidence
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
    (fun _ q v => evaluate q.2.2.1 v q.2.2.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some (fun m : Nat => Fin m → CompletionTree)
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

namespace Saturation

open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGuardedImageSaturation

abbrev signature : Signature where
  Params := Σ m : Nat, Fin m
  State q := Fin q.1 → CompletionTree
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := CompletionTree
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev actual : Realization signature := realize signature
  (fun _ q v => v q.2) (fun e => nomatch e)

abbrev rejected : Realization signature := realize signature
  (fun _ _ _ => leaf true) (fun e => nomatch e)

def observed (R : Realization signature) {m : Nat} (v : Fin m → CompletionTree) :
    Fin m → CompletionTree := fun i => R.readout () ⟨m, i⟩ v

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {k m : Nat} (S : System k m) (p : Fin k → Nat)
    (filters : List (Filter k m)) (mode : FreeMode S (threshold filters)),
    Satisfies S p (observed R (originalCanonical S p filters mode)) ∧
    OriginalInMode S p mode (observed R (originalCanonical S p filters mode)) ∧
    ((∃ v, Satisfies S p v ∧ OriginalInMode S p mode v ∧ Passes p v filters) ↔
      Passes p (observed R (originalCanonical S p filters mode)) filters)

private theorem actual_law : arena.Law actual := by
  exact @original_saturation

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  let S : System 0 1 := fun _ => some (.ground (.of false))
  let p : Fin 0 → Nat := Fin.elim0
  let mode : FreeMode S (threshold ([] : List (Filter 0 1))) := fun _ => none
  have sat := (law S p [] mode).1
  have eq : leaf true = leaf false := sat 0 (.ground (.of false)) rfl
  have tags := congrArg (fun X => (PFunctor.M.dest X).1) eq
  cases tags

private theorem readout_depends : ObservationalDependence signature actual := by
  intro role
  refine ⟨⟨1, 0⟩, (fun _ => leaf true), (fun _ => leaf false), ?_⟩
  intro eq
  have tags := congrArg (fun X => (PFunctor.M.dest X).1) eq
  cases tags

def evidence : Registration arena (type_of% (@original_saturation)) where
  actual := actual
  bridge := by rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := readout_depends

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@original_saturation) (Realization signature) (Nat → Type) Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.NativeRootLinkNormalization.original_saturation.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeRootLinkNormalization.Saturation.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ q v => v q.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some (fun m : Nat => Fin m → CompletionTree)
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end Saturation

end
end Reg.D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeRootLinkNormalization
