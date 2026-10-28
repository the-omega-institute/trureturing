import D5.S3.ObserverMemory.BinarySelectorRecutFibers
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

namespace Reg.D5.S3.ObserverMemory.BinarySelectorRecutFibers
open _root_.D5.S3.ObserverMemory.BinarySelectorRecutFibers
open _root_.D5.S3.ObserverMemory.StrictAnchoredBoundary
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
noncomputable section
open Classical

namespace RelationFamily
abbrev signature : Signature where
  Params := Unit
  State _ := Nat
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Set (List Bool)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ _ m => relation m) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => {[]}) (fun e => nomatch e)
def source (R : Realization signature) (m : Nat) : Set (List Bool) := R.readout () () m
def current (R : Realization signature) (m : Nat) (x : Word m) : Set (Set (List Bool) × List Bool) :=
  {z | z ∈ image (source R m) (2*m+1,1) ∧ {f | z.2 ++ f ∈ z.1} = {x.val}}
def fixed (R : Realization signature) (m : Nat) (x : Word m) (b : Bool) : Set (Set (List Bool) × List Bool) :=
  {z | z ∈ current R m x ∧ z.2 = [b]}

private theorem rejected_image (m k d : Nat) (hk : 0 < k) : image (source rejected m) (k,d) = ∅ := by
  ext z
  constructor
  · rintro ⟨s,rfl⟩
    rcases s.property.2 with ⟨f,hf⟩
    have he : (s.val.1 ++ s.val.2) ++ f = [] := hf
    have hl := congrArg List.length he
    have ht := congrArg Prod.fst s.property.1
    simp only [List.length_nil,List.length_append,publicType] at hl ht
    omega
  · simp

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(),1,2,?_⟩
  intro h
  change relation 1 = relation 2 at h
  let f := code (default : Point 1)
  have h1 : f ∈ relation 1 := ⟨default,rfl⟩
  have h2 : f ∈ relation 2 := h ▸ h1
  have hl1 := (selector_residual_classification 1).2.2.1 f h1
  have hl2 := (selector_residual_classification 2).2.2.1 f h2
  omega
end RelationFamily

namespace Classification
open RelationFamily
abbrev arena : Arena where
  signature := signature
  Law R := ∀ m : Nat,     (∀ w : List Bool, w ∈ source R m ↔ ∃ i j : Word m,
      w = (i.val ++ j.val) ++ false :: i.val ∨ w = (i.val ++ j.val) ++ true :: j.val) ∧
    (source R m).Nonempty ∧ (∀ f ∈ source R m, f.length = 3 * m + 1) ∧
    Nat.card (source R m) = 2 * (2 ^ m)^2 ∧
    (∀ u : List Bool, u.length = 2 * m →
      ((∃ f, u ++ f ∈ source R m) ↔ ∃ i j : Word m, u = i.val ++ j.val)) ∧
    (∀ u : List Bool, u.length = 2 * m + 1 →
      ((∃ f, u ++ f ∈ source R m) ↔ ∃ p : Point m, u = selectorPrefix p)) ∧
    (∀ i j : Word m, residual (source R m) (i.val ++ j.val) = predecessor i j ∧
      (∀ b : Bool, {f | [b] ++ f ∈ predecessor i j} = {(selected ((i,j),b)).val})) ∧
    Function.Injective (fun ij : Word m × Word m => predecessor ij.1 ij.2) ∧
    (∀ p : Point m, actual (source R m) (state p) ∧
      residual (source R m) (selectorPrefix p) = {(selected p).val} ∧
      boundary (source R m) (state p) = fine p) ∧
    residualSet (source R m) (2*m) = Set.range (fun ij : Word m × Word m => predecessor ij.1 ij.2) ∧
    Nat.card (residualSet (source R m) (2*m)) = (2^m)^2 ∧
    residualSet (source R m) (2*m+1) = Set.range (fun x : Word m => ({x.val} : Set (List Bool))) ∧
    image (source R m) (2 * m + 1, 0) = Set.range (fun x : Word m => ({x.val},([] : List Bool))) ∧
    image (source R m) (2 * m + 1, 1) = Set.range (@fine m)
theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hf := (h 1).2.2.1 ([] : List Bool) (by exact rfl)
  norm_num [rejected,realize] at hf
def sourceRegistration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨fun m => selector_residual_classification m,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e; exact nomatch e
  dependence := dependence
noncomputable def registration : LeanInformationAudit.Contract.Registration.{0,0,1,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.ObserverMemory.BinarySelectorRecutFibers.selector_residual_classification)
    (type_of% (realize signature (fun _ _ m => relation m) (fun e => nomatch e)))
    Unit Unit := {
  unitName := `Reg.D5.S3.ObserverMemory.BinarySelectorRecutFibers.selector_residual_classification.__information_unit,
  realizationName := `Reg.D5.S3.ObserverMemory.BinarySelectorRecutFibers.Classification.sourceRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨sourceRegistration⟩,
  correspondence := {stage := .evidence,objectStage := .evidence},
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ m => relation m) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.ObserverMemory.BinarySelectorRecutFibers, definition := none, coordinates := #[], readouts := #[{ path := #["body", "fn", "arg", "body", "fn", "arg", "fn", "arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }
#print axioms sourceRegistration
end Classification

namespace Widths
open RelationFamily
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (m : Nat) (hm : 1 ≤ m),     Nat.card (image (source R m) (2*m+1,0)) = 2^m ∧
    Nat.card (image (source R m) (2*m+1,1)) = 2*(2^m)^2 ∧
    (Nat.card (image (source R m) (2*m+1,1)) : ℚ) /
      Nat.card (image (source R m) (2*m+1,0)) = 2 * (2^m : Nat) ∧
    (∀ x : Word m, current R m x =
      Set.range (fun byPair : Bool × Word m => fine (rebuild x byPair.1 byPair.2)) ∧
      Nat.card (current R m x) = 2*2^m ∧
      (∀ b : Bool, fixed R m x b = Set.range (fun y : Word m => fine (rebuild x b y)) ∧
        Nat.card (fixed R m x b) = 2^m)) ∧
    (∀ s s', actual (source R m) s → actual (source R m) s' → publicType s = publicType s' →
      (legal (3*m+1) (source R m) s = legal (3*m+1) (source R m) s' ↔
        boundary (source R m) s = boundary (source R m) s')) ∧
    (∀ (X : Type) (a : List Bool × List Bool → X), Exact (3*m+1) (source R m) a →
      ∃! factor : Set.range (fun s : typedState (source R m) (2*m+1,1) => a s.val) →
        image (source R m) (2*m+1,1),
        (Set.rangeFactorization (fun s : typedState (source R m) (2*m+1,1) => boundary (source R m) s.val) =
          factor ∘ Set.rangeFactorization (fun s : typedState (source R m) (2*m+1,1) => a s.val)) ∧
        Function.Surjective factor ∧
        2*(2^m)^2 ≤ Nat.card (Set.range (fun s : typedState (source R m) (2*m+1,1) => a s.val))) ∧
    (∀ s a, actual (source R m) s →
      Option.map (fun r => (publicType r,boundary (source R m) r)) (step (3*m+1) (source R m) s a) =
        boundaryStep (3*m+1) (publicType s) (boundary (source R m) s) a) ∧
    (∀ (X : Type) (a : List Bool × List Bool → X), Exact (3*m+1) (source R m) a →
      2^m ≤ Nat.card (Set.range (fun s : typedState (source R m) (2*m+1,0) => a s.val)))
theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hf := (h 1 (by decide)).1
  rw [rejected_image 1 3 0 (by decide)] at hf
  norm_num at hf
def sourceRegistration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨fun m hm => selector_widths_and_fibers m hm,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e; exact nomatch e
  dependence := dependence
noncomputable def registration : LeanInformationAudit.Contract.Registration.{0,0,1,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.ObserverMemory.BinarySelectorRecutFibers.selector_widths_and_fibers)
    (type_of% (realize signature (fun _ _ m => relation m) (fun e => nomatch e)))
    Unit Unit := {
  unitName := `Reg.D5.S3.ObserverMemory.BinarySelectorRecutFibers.selector_widths_and_fibers.__information_unit,
  realizationName := `Reg.D5.S3.ObserverMemory.BinarySelectorRecutFibers.Widths.sourceRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨sourceRegistration⟩,
  correspondence := {stage := .evidence,objectStage := .evidence},
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ m => relation m) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.ObserverMemory.BinarySelectorRecutFibers, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "fn", "arg", "fn", "arg", "arg", "arg", "fn", "arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }
#print axioms sourceRegistration
end Widths

namespace Sharpness
open RelationFamily
abbrev arena : Arena where
  signature := signature
  Law R :=     (∀ m : Nat, Nat.card (image (source R m) (2*m+1,1)) =
      2 * Nat.card (image (source R m) (2*m+1,0)) ^ 2 ∧ (source R m).Finite) ∧
    (∀ m : Nat, ∀ x : Word m, Function.Injective (fun j : Word m => predecessor x j) ∧
      ∀ j : Word m, {f | [false] ++ f ∈ predecessor x j} = {x.val}) ∧
    (∀ K : Nat, ∃ m : Nat, 1 ≤ m ∧
      K * Nat.card (image (source R m) (2*m+1,0)) < Nat.card (image (source R m) (2*m+1,1)))
theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨m,hm,hlt⟩ := h.2.2 0
  rw [rejected_image m (2*m+1) 0 (by omega),rejected_image m (2*m+1) 1 (by omega)] at hlt
  simp at hlt
def sourceRegistration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨selector_full_branching_sharpness,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e; exact nomatch e
  dependence := dependence
noncomputable def registration : LeanInformationAudit.Contract.Registration.{0,0,1,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.ObserverMemory.BinarySelectorRecutFibers.selector_full_branching_sharpness)
    (type_of% (realize signature (fun _ _ m => relation m) (fun e => nomatch e)))
    Unit Unit := {
  unitName := `Reg.D5.S3.ObserverMemory.BinarySelectorRecutFibers.selector_full_branching_sharpness.__information_unit,
  realizationName := `Reg.D5.S3.ObserverMemory.BinarySelectorRecutFibers.Sharpness.sourceRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨sourceRegistration⟩,
  correspondence := {stage := .evidence,objectStage := .evidence},
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ m => relation m) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.ObserverMemory.BinarySelectorRecutFibers, definition := none, coordinates := #[], readouts := #[{ path := #["fn", "arg", "body", "fn", "arg", "fn", "arg", "arg", "arg", "fn", "arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }
#print axioms sourceRegistration
end Sharpness

namespace Supplements
abbrev signature : Signature where
  Params := Nat
  State m := Point m
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ m := Bool × Word m
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ _ p => label p) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => (false,default)) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ m : Nat,     (∀ (Z : Type) [Finite Z] (L : Point m → Z),
      (∃ R : Word m × Z → Point m, ∀ p, R (selected p,L p) = p) → 2*2^m ≤ Nat.card Z) ∧
    (∀ (Z : Type) [Finite Z] (L : Point m → Z),
      (∃ R : (Word m × Bool) × Z → Point m, ∀ p, R ((selected p,p.2),L p) = p) → 2^m ≤ Nat.card Z) ∧
    (∀ p : Point m, rebuild (selected p) (R.readout () m p).1 (R.readout () m p).2 = p ∧
      rebuild (selected p) p.2 (unused p) = p ∧
      binaryRecover (selected p) (binaryLabel p) = p ∧
      fine (rebuild (selected p) (R.readout () m p).1 (R.readout () m p).2) = boundary (relation m) (state p)) ∧
    (∀ i j : Word m, R.readout () m ((i,j),false) = (false,j) ∧ R.readout () m ((i,j),true) = (true,i)) ∧
    Nat.card (Bool × Word m) = 2*2^m ∧ Nat.card (Word m) = 2^m ∧
    (∀ ℓ : Nat,
      (∃ L : Point m → Word ℓ, Function.Injective (fun p => (selected p,L p))) ↔ m+1 ≤ ℓ) ∧
    (∀ ℓ : Nat,
      (∃ L : Point m → Word ℓ, Function.Injective (fun p => ((selected p,p.2),L p))) ↔ m ≤ ℓ) ∧
    Nat.clog 2 (2*2^m) = m+1 ∧ Nat.clog 2 (2^m) = m
theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hf := ((h 0).2.2.2.1 default default).2
  have hb := congrArg Prod.fst hf
  simp [rejected,realize] at hb
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1,((default,default),false),((default,default),true),?_⟩
  intro h
  have hb := congrArg Prod.fst h
  simp [actual,realize,label] at hb

def sourceRegistration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨selector_optimal_supplements,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e; exact nomatch e
  dependence := dependence
noncomputable def registration : LeanInformationAudit.Contract.Registration.{0,0,1,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.ObserverMemory.BinarySelectorRecutFibers.selector_optimal_supplements)
    (type_of% (realize signature (fun _ _ p => label p) (fun e => nomatch e)))
    Unit Unit := {
  unitName := `Reg.D5.S3.ObserverMemory.BinarySelectorRecutFibers.selector_optimal_supplements.__information_unit,
  realizationName := `Reg.D5.S3.ObserverMemory.BinarySelectorRecutFibers.Supplements.sourceRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨sourceRegistration⟩,
  correspondence := {stage := .evidence,objectStage := .evidence},
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ p => label p) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.ObserverMemory.BinarySelectorRecutFibers, definition := none, coordinates := #[0], readouts := #[{ path := #["body", "arg", "arg", "fn", "arg", "body", "fn", "arg", "fn", "arg", "fn", "arg", "arg"], stateBinder := 1, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }
#print axioms sourceRegistration
end Supplements

namespace Separators
abbrev signature : Signature where
  Params := Σ m : Nat, Point m
  State p := Point p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := List (Action Bool)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ p q => separator p.2 q) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => []) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ m : Nat,     (∀ p : Point m, ∀ b : Bool, ∀ x : Word m,
      experiment p b x ∈ legal (3*m+1) (relation m) (state p) ↔ x = selected (p.1,b)) ∧
    (∀ p q : Point m, fine p ≠ fine q →
      (R.readout () ⟨m,p⟩ q).length ≤ m+2 ∧
      R.readout () ⟨m,p⟩ q ∈ legal (3*m+1) (relation m) (state p) ∧
      R.readout () ⟨m,p⟩ q ∉ legal (3*m+1) (relation m) (state q)) ∧
    (∀ s t : typedState (relation m) (2*m+1,1), boundary (relation m) s.val ≠ boundary (relation m) t.val →
      ∃ w : List (Action Bool), w.length ≤ m+2 ∧
        w ∈ legal (3*m+1) (relation m) s.val ∧ w ∉ legal (3*m+1) (relation m) t.val)
private def p : Point 1 := ((default,default),false)
private def q : Point 1 := ((default,default),true)
theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hne : fine p ≠ fine q := by simp [fine,p,q]
  have hf := (h 1).2.1 p q hne
  have hn := hf.2.2
  simp [rejected,realize,legal,_root_.D5.S0.Automata.TypedPartialDFAOOverBase.runTransition] at hn
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨1,p⟩,p,q,?_⟩
  intro h
  have hl := congrArg List.length h
  simp [actual,realize,separator,p,q,experiment] at hl
def sourceRegistration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨selector_legal_separators,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e; exact nomatch e
  dependence := dependence
noncomputable def registration : LeanInformationAudit.Contract.Registration.{0,0,1,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.ObserverMemory.BinarySelectorRecutFibers.selector_legal_separators)
    (type_of% (realize signature (fun _ p q => separator p.2 q) (fun e => nomatch e)))
    Unit Unit := {
  unitName := `Reg.D5.S3.ObserverMemory.BinarySelectorRecutFibers.selector_legal_separators.__information_unit,
  realizationName := `Reg.D5.S3.ObserverMemory.BinarySelectorRecutFibers.Separators.sourceRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨sourceRegistration⟩,
  correspondence := {stage := .evidence,objectStage := .evidence},
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ p q => separator p.2 q) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.ObserverMemory.BinarySelectorRecutFibers, definition := none, coordinates := #[0, 1], readouts := #[{ path := #["body", "arg", "fn", "arg", "body", "body", "body", "fn", "arg", "fn", "arg", "arg"], stateBinder := 2, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }
#print axioms sourceRegistration
end Separators
namespace Refutation
open RelationFamily
abbrev arena : Arena where
  signature := signature
  Law R := ¬ ∀ m : Nat, 1 ≤ m →
    Nat.card (image (source R m) (2*m+1,1)) ≤ 2 * Nat.card (image (source R m) (2*m+1,0))
theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  apply h
  intro m hm
  rw [rejected_image m (2*m+1) 0 (by omega),rejected_image m (2*m+1) 1 (by omega)]
  simp
def sourceRegistration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e; exact nomatch e
  dependence := dependence
noncomputable def registration : LeanInformationAudit.Contract.Registration.{0,0,1,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.ObserverMemory.BinarySelectorRecutFibers.result)
    (type_of% (realize signature (fun _ _ m => relation m) (fun e => nomatch e)))
    Unit Unit := {
  unitName := `Reg.D5.S3.ObserverMemory.BinarySelectorRecutFibers.result.__information_unit,
  realizationName := `Reg.D5.S3.ObserverMemory.BinarySelectorRecutFibers.Refutation.sourceRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨sourceRegistration⟩,
  correspondence := {stage := .evidence,objectStage := .evidence},
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ m => relation m) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.ObserverMemory.BinarySelectorRecutFibers, definition := some { owner := `D5.S3.ObserverMemory.BinarySelectorRecutFibers, name := `D5.S3.ObserverMemory.BinarySelectorRecutFibers.AlphabetOnlyTwoBound, path := #["arg"] }, coordinates := #[], readouts := #[{ path := #["arg", "body", "body", "fn", "arg", "arg", "arg", "fn", "arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }
#print axioms sourceRegistration
end Refutation
end
end Reg.D5.S3.ObserverMemory.BinarySelectorRecutFibers
