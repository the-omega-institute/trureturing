import D5.S3.ConceptDynamics.Gluing.BoundaryObservationSplicing
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

/-! Source-bound audit of compatible dependent raw-record splicing. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.ConceptDynamics.Gluing.BoundaryObservationSplicing

open _root_.D5.S3.ConceptDynamics.Observation.HistoryPayloadFactorization
open _root_.D5.S3.ConceptDynamics.Gluing.RunningIntersectionRecords
open _root_.D5.S3.ConceptDynamics.Gluing.BoundaryObservationSplicing
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

universe i u v

/-- Equality of dependent assignments retains arbitrary carriers, fibers and scopes. -/
abbrev signature : Signature where
  Params := Σ Node : Type i, Σ Var : Type u, Σ Value : Var → Type v,
    Σ _S : Node → Set Var, Σ _A : Set Node, Set Node
  State p := Assignment p.2.2.1
    (componentScope p.2.2.2.1 (p.2.2.2.2.1 ∪ p.2.2.2.2.2))
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Assignment p.2.2.1
    (componentScope p.2.2.2.1 (p.2.2.2.2.1 ∪ p.2.2.2.2.2)) → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{i,u,v} :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected : Realization signature.{i,u,v} :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

/-- The source telescope is unchanged; only its conclusion's assignment equality varies. -/
def arena : Arena where
  signature := signature.{i,u,v}
  Law R := ∀ {Node : Type i} {Var : Type u}
    (Value : Var → Type v) (S : Node → Set Var)
    (Γ : (n : Node) → Set (Assignment Value (S n)))
    (A B : Set Node) (_hdisj : Disjoint A B)
    (a : rawJoin Value S Γ A) (b : rawJoin Value S Γ B)
    (_h : overlapBoundaryLeft Value S Γ A B a = overlapBoundaryRight Value S Γ A B b),
    ∃! j : rawJoin Value S Γ (A ∪ B),
      R.readout () ⟨Node, Var, Value, S, A, B⟩ j.val
        (spliceAssignment Value S Γ A B a b)

private theorem rejected_law : ¬ arena.{i,u,v}.Law rejected := by
  intro h
  let Value : PUnit.{u+1} → Type v := fun _ => PUnit.{v+1}
  let S : PUnit.{i+1} → Set PUnit.{u+1} := fun _ => Set.univ
  let Γ : (n : PUnit.{i+1}) → Set (Assignment Value (S n)) := fun _ => Set.univ
  let a : rawJoin Value S Γ ∅ := ⟨fun _ => PUnit.unit, by
    intro n hn
    exact hn.elim⟩
  have overlap : overlapBoundaryLeft Value S Γ ∅ ∅ a =
      overlapBoundaryRight Value S Γ ∅ ∅ a := by
    funext x
    rfl
  obtain ⟨j, hj, _⟩ := h Value S Γ ∅ ∅ (by simp) a a overlap
  exact hj

def evidence : Registration arena.{i,u,v}
    (type_of% (@compatible_splice_unique.{i,u,v})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@compatible_splice_unique.{i,u,v}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, ?_, rejected_law⟩
      · intro other h
        exact (h (by cases other; cases role; rfl)).elim
      · funext e
        exact nomatch e
    · intro e
      exact nomatch e
  dependence := by
    intro role
    let p : signature.{i,u,v}.Params :=
      ⟨PUnit.{i+1}, PUnit.{u+1}, (fun _ => ULift.{v} Bool),
        (fun _ => Set.univ), Set.univ, ∅⟩
    let x : signature.State p := fun _ => ⟨false⟩
    let y : signature.State p := fun _ => ⟨true⟩
    refine ⟨p, x, y, ?_⟩
    intro he
    have hyx : y = x := Eq.mp (congrFun he x) rfl
    have bad := congrArg (fun f => (f ⟨PUnit.unit,
      ⟨PUnit.unit, Or.inl (Set.mem_univ _), Set.mem_univ _⟩⟩).down) hyx
    exact Bool.noConfusion bad

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@compatible_splice_unique.{i,u,v}) (Realization signature.{i,u,v}) Unit Unit where
  unitName := `D5.S3.ConceptDynamics.Gluing.BoundaryObservationSplicing.compatible_splice_unique.__information_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Gluing.BoundaryObservationSplicing.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{i,u,v}⟩
  objectArena := .source ⟨arena.{i,u,v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{i,u,v} ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{i,u,v} (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Gluing.BoundaryObservationSplicing
    definition := none
    coordinates := #[0, 1, 2, 3, 5, 6]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "arg", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

namespace TwoContext
universe u_1 u_2 u_3

abbrev signature : Signature where
  Params := Type u_3
  State X := X
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ X := X → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u_3} :=
  realize signature (fun _ _ x y => x = y) (fun e => Empty.elim e)

def rejected : Realization signature.{u_3} :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

def arena : Arena where
  signature := signature.{u_3}
  Law R := ∀ {Node : Type i} {Var : Type u}
    (Value : Var → Type v) (S : Node → Set Var)
    (Γ : (n : Node) → Set (Assignment Value (S n)))
    {A B : Set Node} {QA : Type u_1} {QB : Type u_2} {Output : Type u_3}
    (_hdisj : Disjoint A B)
    (qA : rawJoin Value S Γ A → QA) (qB : rawJoin Value S Γ B → QB)
    (G : rawJoin Value S Γ Set.univ → Output)
    (_hA : BoundaryOutputRetention Value S Γ A qA G)
    (_hB : BoundaryOutputRetention Value S Γ B qB G)
    (w w' : rawJoin Value S Γ Set.univ)
    (_hqa : qA (restrictRecord Value S Γ A w) = qA (restrictRecord Value S Γ A w'))
    (_hqb : qB (restrictRecord Value S Γ B w) = qB (restrictRecord Value S Γ B w'))
    (_hout : restrictRecord Value S Γ (A ∪ B)ᶜ w =
      restrictRecord Value S Γ (A ∪ B)ᶜ w'),
      R.readout () Output (G w) (G w')

private theorem rejected_law : ¬ arena.{i,u,v,u_1,u_2,u_3}.Law rejected := by
  intro h
  let Value : PUnit.{u+1} → Type v := fun _ => PUnit.{v+1}
  let S : PUnit.{i+1} → Set PUnit.{u+1} := fun _ => Set.univ
  let Γ : (n : PUnit.{i+1}) → Set (Assignment Value (S n)) := fun _ => Set.univ
  let w : rawJoin Value S Γ Set.univ := ⟨fun _ => PUnit.unit, fun _ _ => Set.mem_univ _⟩
  let qA : rawJoin Value S Γ ∅ → PUnit.{u_1+1} := fun _ => PUnit.unit
  let qB : rawJoin Value S Γ ∅ → PUnit.{u_2+1} := fun _ => PUnit.unit
  let G : rawJoin Value S Γ Set.univ → ULift.{u_3} Bool := fun _ => ⟨false⟩
  have retentionA : BoundaryOutputRetention Value S Γ ∅ qA G := by
    intro a a' _
    constructor
    · funext x
      exact Subsingleton.elim _ _
    · intro r hr hr'
      rfl
  have retentionB : BoundaryOutputRetention Value S Γ ∅ qB G := by
    intro b b' _
    constructor
    · funext x
      exact Subsingleton.elim _ _
    · intro r hr hr'
      rfl
  exact h Value S Γ (by simp) qA qB G retentionA retentionB w w rfl rfl rfl

def evidence : Registration arena.{i,u,v,u_1,u_2,u_3}
    (type_of% (@two_context_output_eq.{i,u,v,u_1,u_2,u_3})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@two_context_output_eq.{i,u,v,u_1,u_2,u_3}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, ?_, rejected_law⟩
      · intro other h
        exact (h (by cases other; cases role; rfl)).elim
      · funext e
        exact nomatch e
    · intro e
      exact nomatch e
  dependence := by
    intro role
    refine ⟨ULift.{u_3} Bool, ⟨false⟩, ⟨true⟩, ?_⟩
    intro h
    have bad : (⟨true⟩ : ULift.{u_3} Bool) = ⟨false⟩ := Eq.mp (congrFun h ⟨false⟩) rfl
    exact Bool.noConfusion (congrArg ULift.down bad)

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@two_context_output_eq.{i,u,v,u_1,u_2,u_3}) (Realization signature.{u_3}) Unit Unit where
  unitName := `D5.S3.ConceptDynamics.Gluing.BoundaryObservationSplicing.two_context_output_eq.__information_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Gluing.BoundaryObservationSplicing.TwoContext.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{i,u,v,u_1,u_2,u_3}⟩
  objectArena := .source ⟨arena.{i,u,v,u_1,u_2,u_3}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{i,u,v,u_1,u_2,u_3} ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u_3} (fun _ _ x y => x = y) (fun e => Empty.elim e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Gluing.BoundaryObservationSplicing
    definition := none
    coordinates := #[9]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end TwoContext

end Reg.D5.S3.ConceptDynamics.Gluing.BoundaryObservationSplicing
