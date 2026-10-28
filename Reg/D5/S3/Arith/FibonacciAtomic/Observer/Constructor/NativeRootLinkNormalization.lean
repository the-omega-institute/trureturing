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

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeRootLinkNormalization.ExposedSuppliers
noncomputable section

private theorem different_leaves : leaf true ≠ leaf false := by
  intro eq
  have tags := congrArg (fun X => (PFunctor.M.dest X).1) eq
  cases tags

namespace Self

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {k m : Nat} (S : System k m) (i : Fin m) (a : Nat),
    S i = some (.var a i) → correspondence R S (selfStep S i a)
private theorem actual_law : arena.Law actual := @selfStep_correct
private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  let S : System 0 1 := fun _ => some (.var 0 0)
  let p : Fin 0 → Nat := Fin.elim0
  let v : Fin 1 → CompletionTree := fun _ => leaf false
  have sat : Satisfies S p v := by
    intro i E eq
    have e : E = .var 0 0 := Option.some.inj eq.symm
    subst E
    rfl
  have eq := congrFun (((law S 0 0 rfl) p).1 v sat).2 (0 : Fin 1)
  exact different_leaves eq

def evidence : Registration arena (type_of% (@selfStep_correct)) where
  actual := actual
  bridge := by rfl
  variation := ⟨actual_law,rejected,rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,fun j h => (h (Subsingleton.elim j i)).elim,rfl,rejected_law⟩,
    fun e => nomatch e⟩
  dependence := readout_depends

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@selfStep_correct) (Realization signature) (Nat → Type) Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.NativeRootLinkNormalization.selfStep_correct.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeRootLinkNormalization.ExposedSuppliers.Self.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some actual
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some (fun m : Nat => Fin m → CompletionTree)
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end Self

namespace Link

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {k m : Nat} (S : System k m) (i : Fin m) (a : Nat) (j : Fin m),
    j ≠ i → S i = some (.var a j) → correspondence R S (linkStep S i a j)
private theorem actual_law : arena.Law actual := @linkStep_correct
private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  let S : System 0 2 := fun i => if i = 0 then some (.var 0 1) else none
  let p : Fin 0 → Nat := Fin.elim0
  let v : Fin 2 → CompletionTree := fun _ => leaf false
  have sat : Satisfies S p v := by
    intro i E eq
    dsimp [S] at eq
    split_ifs at eq with h
    · have e : E = .var 0 1 := Option.some.inj eq.symm
      subst E
      rfl
  have eq := congrFun (((law S 0 0 1 (by decide) (by simp [S])) p).1 v sat).2 (0 : Fin 2)
  exact different_leaves eq

def evidence : Registration arena (type_of% (@linkStep_correct)) where
  actual := actual
  bridge := by rfl
  variation := ⟨actual_law,rejected,rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,fun j h => (h (Subsingleton.elim j i)).elim,rfl,rejected_law⟩,
    fun e => nomatch e⟩
  dependence := readout_depends

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@linkStep_correct) (Realization signature) (Nat → Type) Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.NativeRootLinkNormalization.linkStep_correct.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeRootLinkNormalization.ExposedSuppliers.Link.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some actual
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some (fun m : Nat => Fin m → CompletionTree)
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end Link

namespace Compose

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {k m : Nat} (S : System k m) (T U : Presentation k m),
    Correct S T → Correct T.equations U → correspondence R S (compose T U)
private theorem actual_law : arena.Law actual := @compose_correct
private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  let S : System 0 1 := fun _ => none
  let T : Presentation 0 1 := ⟨S,identity,identity⟩
  let p : Fin 0 → Nat := Fin.elim0
  let v : Fin 1 → CompletionTree := fun _ => leaf false
  have corr : Correct S T := by
    intro p
    constructor <;> intro v sat <;> exact ⟨sat,rfl⟩
  have sat : Satisfies S p v := by intro i E eq; cases eq
  have eq := congrFun (((law S T T corr corr) p).1 v sat).2 (0 : Fin 1)
  exact different_leaves eq

def evidence : Registration arena (type_of% (@compose_correct)) where
  actual := actual
  bridge := by rfl
  variation := ⟨actual_law,rejected,rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,fun j h => (h (Subsingleton.elim j i)).elim,rfl,rejected_law⟩,
    fun e => nomatch e⟩
  dependence := readout_depends

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@compose_correct) (Realization signature) (Nat → Type) Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.NativeRootLinkNormalization.compose_correct.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeRootLinkNormalization.ExposedSuppliers.Compose.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some actual
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some (fun m : Nat => Fin m → CompletionTree)
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end Compose

abbrev countSignature : Signature where
  Params := Unit
  State _ := Nat
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Nat
  Anchor := Empty
  finiteAnchor := inferInstance
abbrev countActual : Realization countSignature :=
  realize countSignature (fun _ _ x => x) (fun e => nomatch e)
abbrev countRejected : Realization countSignature :=
  realize countSignature (fun _ _ x => x+1) (fun e => nomatch e)
def countObserved (R : Realization countSignature) (x : Nat) := R.readout () () x
private theorem countDependence : ObservationalDependence countSignature countActual := by
  intro role
  refine ⟨(),0,1,?_⟩
  change (0 : Nat) ≠ 1
  omega

namespace SelfDecrease

abbrev arena : Arena where
  signature := countSignature
  Law R := ∀ {k m : Nat} (S : System k m) (i : Fin m) (a : Nat),
    S i = some (.var a i) →
      countObserved R (roots (selfStep S i a).equations).card < (roots S).card
private theorem actual_law : arena.Law countActual := @selfStep_decreases
private theorem rejected_law : ¬ arena.Law countRejected := by
  classical
  intro law
  let S : System 0 1 := fun _ => some (.var 0 0)
  have bad := law S 0 0 rfl
  have count : (roots S).card = 1 := by
    have eq : roots S = Finset.univ := by
      ext i
      simp only [mem_roots,Finset.mem_univ,iff_true]
      exact ⟨0,0,rfl⟩
    rw [eq]
    simp
  have smaller := selfStep_decreases S 0 0 rfl
  change (roots (selfStep S 0 0).equations).card + 1 < (roots S).card at bad
  omega

def evidence : Registration arena (type_of% (@selfStep_decreases)) where
  actual := countActual
  bridge := by rfl
  variation := ⟨actual_law,countRejected,rejected_law⟩
  sensitivity := ⟨fun i => ⟨countRejected,fun j h => (h (Subsingleton.elim j i)).elim,rfl,rejected_law⟩,
    fun e => nomatch e⟩
  dependence := countDependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@selfStep_decreases) (Realization countSignature) Type Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.NativeRootLinkNormalization.selfStep_decreases.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeRootLinkNormalization.ExposedSuppliers.SelfDecrease.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some countActual
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some Nat
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end SelfDecrease

namespace LinkDecrease

abbrev arena : Arena where
  signature := countSignature
  Law R := ∀ {k m : Nat} (S : System k m) (i : Fin m) (a : Nat) (j : Fin m),
    S i = some (.var a j) →
      countObserved R (roots (linkStep S i a j).equations).card < (roots S).card
private theorem actual_law : arena.Law countActual := @linkStep_decreases
private theorem rejected_law : ¬ arena.Law countRejected := by
  classical
  intro law
  let S : System 0 1 := fun _ => some (.var 0 0)
  have bad := law S 0 0 0 rfl
  have count : (roots S).card = 1 := by
    have eq : roots S = Finset.univ := by
      ext i
      simp only [mem_roots,Finset.mem_univ,iff_true]
      exact ⟨0,0,rfl⟩
    rw [eq]
    simp
  have smaller := linkStep_decreases S 0 0 0 rfl
  change (roots (linkStep S 0 0 0).equations).card + 1 < (roots S).card at bad
  omega

def evidence : Registration arena (type_of% (@linkStep_decreases)) where
  actual := countActual
  bridge := by rfl
  variation := ⟨actual_law,countRejected,rejected_law⟩
  sensitivity := ⟨fun i => ⟨countRejected,fun j h => (h (Subsingleton.elim j i)).elim,rfl,rejected_law⟩,
    fun e => nomatch e⟩
  dependence := countDependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@linkStep_decreases) (Realization countSignature) Type Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.NativeRootLinkNormalization.linkStep_decreases.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeRootLinkNormalization.ExposedSuppliers.LinkDecrease.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some countActual
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some Nat
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end LinkDecrease

abbrev setSignature : Signature where
  Params := Nat
  State m := Finset (Fin m)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ m := Finset (Fin m)
  Anchor := Empty
  finiteAnchor := inferInstance
abbrev setActual : Realization setSignature :=
  realize setSignature (fun _ _ x => x) (fun e => nomatch e)
abbrev setRejected : Realization setSignature :=
  realize setSignature (fun _ _ _ => ∅) (fun e => nomatch e)
def setObserved (R : Realization setSignature) {m : Nat} (x : Finset (Fin m)) :=
  R.readout () m x
private theorem setDependence : ObservationalDependence setSignature setActual := by
  intro role
  refine ⟨1,∅,{0},?_⟩
  change (∅ : Finset (Fin 1)) ≠ {0}
  simp

namespace Membership

abbrev arena : Arena where
  signature := setSignature
  Law R := ∀ {k m : Nat} (S : System k m) (i : Fin m),
    i ∈ setObserved R (roots S) ↔ ∃ a j, S i = some (.var a j)
private theorem actual_law : arena.Law setActual := @mem_roots
private theorem rejected_law : ¬ arena.Law setRejected := by
  intro law
  let S : System 0 1 := fun _ => some (.var 0 0)
  have bad := (law S 0).mpr ⟨0,0,rfl⟩
  change (0 : Fin 1) ∈ (∅ : Finset (Fin 1)) at bad
  simpa using bad

def evidence : Registration arena (type_of% (@mem_roots)) where
  actual := setActual
  bridge := by rfl
  variation := ⟨actual_law,setRejected,rejected_law⟩
  sensitivity := ⟨fun i => ⟨setRejected,fun j h => (h (Subsingleton.elim j i)).elim,rfl,rejected_law⟩,
    fun e => nomatch e⟩
  dependence := setDependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@mem_roots) (Realization setSignature) (Nat → Type) Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.NativeRootLinkNormalization.mem_roots.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeRootLinkNormalization.ExposedSuppliers.Membership.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some setActual
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some (fun m : Nat => Finset (Fin m))
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end Membership


namespace Filters
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeImageSaturationInterface
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGuardedImageSaturation
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGuardedAtomicReplacement
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {k m : Nat} (T : Presentation k m) (p : Fin k → Nat)
    (w : Fin m → CompletionTree) (filters : List (Filter k m)),
    Passes p w (transformedFilters T filters) ↔ Passes p (maps R p T.reconstruct w) filters
private theorem actual_law : arena.Law actual := @filters_correspond
private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  let T : Presentation 0 1 := ⟨(fun _ => none),identity,identity⟩
  let p : Fin 0 → Nat := Fin.elim0
  let w : Fin 1 → CompletionTree := fun _ => leaf false
  let filters : List (Filter 0 1) := [(.var 0 0,1)]
  have passes : Passes p w (transformedFilters T filters) := by
    intro E t ht
    have eq : (E,t) = (.var 0 0,1) := by
      simpa [transformedFilters,T,identity,substitute,shift,filters] using ht
    have a := congrArg Prod.fst eq
    have b := congrArg Prod.snd eq
    change E = .var 0 0 at a
    change t = 1 at b
    subst E t
    refine ⟨leaf true,?_⟩
    change _root_.D5.S3.Arith.FibonacciAtomic.Observer.CompletionHomogeneousFixedPoints.rho
      (leaf true) = leaf false
    exact _root_.D5.S3.Arith.FibonacciAtomic.Observer.CompletionHomogeneousFixedPoints.rho_alpha
  have bad := ((law T p w filters).mp passes) (.var 0 0) 1 (by simp [filters])
  change NativeImage 1 (leaf true) at bad
  obtain ⟨X,eq⟩ := bad
  obtain ⟨j,rank,_⟩ := atomic_predecessor 1 0 X eq
  omega
def evidence : Registration arena (type_of% (@filters_correspond)) where
  actual := actual
  bridge := by rfl
  variation := ⟨actual_law,rejected,rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,fun j h => (h (Subsingleton.elim j i)).elim,rfl,rejected_law⟩,
    fun e => nomatch e⟩
  dependence := readout_depends

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@filters_correspond) (Realization signature) (Nat → Type) Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.NativeRootLinkNormalization.filters_correspond.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeRootLinkNormalization.ExposedSuppliers.Filters.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some actual
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some (fun m : Nat => Fin m → CompletionTree)
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]


end Filters
end
end Reg.D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeRootLinkNormalization.ExposedSuppliers
