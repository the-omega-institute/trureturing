import D5.S3.Observer.Separation.CapacitySensitiveSupport
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

/-! Complete-family audit of the least sensitive support on a finite product. -/

set_option autoImplicit false

namespace Reg.D5.S3.Observer.Separation.CapacitySensitiveSupport

open _root_.D5.S3.Observer.Separation.CapacitySensitiveSupport
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

universe u v w

abbrev signature : Signature where
  Params := Σ U : Type u, Σ O : U → Type v, Σ Y : Type w, ((∀ i, O i) → Y)
  State p := ∀ i, p.2.1 i
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.2.2.1
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u,v,w} :=
  realize signature (fun _ p h => p.2.2.2 h) (fun e => nomatch e)

noncomputable def rejected : Realization signature.{u,v,w} :=
  realize signature (fun _ p h => p.2.2.2 (Classical.choice ⟨h⟩)) (fun e => nomatch e)

def arena : Arena where
  signature := signature.{u,v,w}
  Law R := ∀ {U : Type u} [Finite U] {O : U → Type v} {Y : Type w}
    (c : (∀ i, O i) → Y) (S : Set U),
    DependsOn (R.readout () ⟨U, O, Y, c⟩) S ↔ sensitive c ⊆ S

private theorem rejected_law : ¬ arena.{u,v,w}.Law rejected := by
  intro law
  let c : (PUnit.{u+1} → ULift.{v} Bool) → ULift.{w} Bool :=
    fun h => ⟨(h PUnit.unit).down⟩
  have constant : DependsOn
      (rejected.readout () ⟨PUnit.{u+1}, (fun _ => ULift.{v} Bool), ULift.{w} Bool, c⟩)
      ∅ := by
    intro h h' _
    rfl
  have no := (@law PUnit.{u+1} inferInstance (fun _ => ULift.{v} Bool)
    (ULift.{w} Bool) c ∅).mp constant
  apply no (show PUnit.unit ∈ sensitive c from ?_)
  refine ⟨(fun _ => ⟨false⟩), (fun _ => ⟨true⟩), ?_, ?_⟩
  · intro j hj
    exact (hj (Subsingleton.elim _ _)).elim
  · intro he
    exact Bool.noConfusion (congrArg ULift.down he)

def evidence : Registration arena.{u,v,w}
    (type_of% (@dependsOn_iff_sensitive_subset.{u,v,w})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@dependsOn_iff_sensitive_subset.{u,v,w}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other h
      exact (h (by cases other; cases role; rfl)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro role
    let p : signature.{u,v,w}.Params :=
      ⟨PUnit.{u+1}, (fun _ => ULift.{v} Bool), ULift.{w} Bool,
        fun h => ⟨(h PUnit.unit).down⟩⟩
    refine ⟨p, (fun _ => ⟨false⟩), (fun _ => ⟨true⟩), ?_⟩
    intro he
    exact Bool.noConfusion (congrArg ULift.down he)

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@dependsOn_iff_sensitive_subset.{u,v,w}) (Realization signature.{u,v,w}) Unit Unit where
  unitName := .str
    `D5.S3.Observer.Separation.CapacitySensitiveSupport.dependsOn_iff_sensitive_subset
    "__information_unit"
  realizationName := `Reg.D5.S3.Observer.Separation.CapacitySensitiveSupport.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v,w}⟩
  objectArena := .source ⟨arena.{u,v,w}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u,v,w} ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u,v,w} (fun _ p h => p.2.2.2 h) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.Separation.CapacitySensitiveSupport
    definition := none
    coordinates := #[0, 2, 3, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence

namespace Source

open _root_.D5.S3.Observer.Separation.FixedTreeCommonExtension

abbrev signature : Signature where
  Params := Σ I : Type, Σ V : Type, Σ O : Type, Σ X : I → Type,
    Σ _t : Tree I V, Σ D : Set (∀ i, X i), (D → O)
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def actual : Realization signature :=
  realize signature (fun _ p k =>
    minimumPeak p.2.2.2.2.1 p.2.2.2.2.2.1 p.2.2.2.2.2.2 ≤ k) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {I V O : Type} [Fintype I] {X : I → Type}
    [∀ i, Finite (X i)] [∀ i, Nonempty (X i)]
    (t : Tree I V) (_ht : Full t) (_hall : leaves t = Finset.univ)
    (D : Set (∀ i, X i)) (_hD : D.Nonempty) (f : D → O),
    (∀ (v : Nodes t) (S : Set ↥(Dᶜ)),
      DependsOn (sourceCost t D f v) S ↔ sensitive (sourceCost t D f v) ⊆ S) ∧
    (∀ k : ℕ, R.readout () ⟨I, V, O, X, t, D, f⟩ k ↔
      (sensitiveJoin (sourceCost t D f) k).Nonempty)

def emptyTree : Tree Empty Unit := .node () 0 Fin.elim0

def emptyDomain : Set (Empty → Unit) := Set.univ

def emptyTask : emptyDomain → Unit := fun _ => ()

private theorem empty_full : Full emptyTree := by
  constructor
  · intro j; exact Fin.elim0 j
  · intro j; exact Fin.elim0 j

private theorem empty_all : leaves emptyTree = Finset.univ := by
  classical
  ext i
  exact nomatch i

private theorem empty_nonempty : emptyDomain.Nonempty :=
  ⟨(fun i => nomatch i), Set.mem_univ _⟩

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have source := source_result emptyTree empty_full empty_all
    emptyDomain empty_nonempty emptyTask
  have join := (source.2 (minimumPeak emptyTree emptyDomain emptyTask)).mp le_rfl
  exact ((@law Empty Unit Unit inferInstance (fun _ => Unit)
    (fun _ => inferInstance) (fun _ => inferInstance)
    emptyTree empty_full empty_all emptyDomain empty_nonempty emptyTask).2
      (minimumPeak emptyTree emptyDomain emptyTask)).mpr join

private theorem empty_one : ProtocolBudget emptyTree emptyDomain emptyTask 1 := by
  classical
  let m : Implementation (V := Unit) (fun _ : Empty => Unit) := {
    Message := fun _ => Unit
    encode := fun _ _ _ => ()
    combine := fun _ _ _ _ => () }
  refine ⟨m, (fun _ => ()), (fun _ => rfl), ?_⟩
  intro v
  unfold reachable
  calc
    Nat.card (Set.range (fun x : emptyDomain => evaluate m v.val x.val)) ≤ Nat.card Unit :=
      Nat.card_le_card_of_injective
        (fun q : Set.range (fun x : emptyDomain => evaluate m v.val x.val) => (q.val : Unit))
        (fun _ _ he => Subtype.ext he)
    _ = 1 := by simp

private theorem empty_positive : 1 ≤ minimumPeak emptyTree emptyDomain emptyTask := by
  classical
  obtain ⟨m, read, correct, bound⟩ :=
    (show ProtocolBudget emptyTree emptyDomain emptyTask
      (minimumPeak emptyTree emptyDomain emptyTask) from Nat.sInf_mem (s := {k | ProtocolBudget emptyTree emptyDomain emptyTask k})
        ⟨1, empty_one⟩)
  let v : Nodes emptyTree := ⟨emptyTree, by simp [emptyTree, subtrees]⟩
  letI : Nonempty emptyDomain := ⟨⟨(fun i => nomatch i), Set.mem_univ _⟩⟩
  have one : reachable m emptyDomain emptyTree = 1 := by
    unfold reachable
    have same : (fun x : emptyDomain => evaluate m emptyTree x.val) =
        fun _ : emptyDomain => m.combine () 0 Fin.elim0 (fun j => Fin.elim0 j) := by
      funext x
      change m.combine () 0 Fin.elim0 _ = _
      congr 1
      funext j
      exact Fin.elim0 j
    rw [same, Set.range_const]
    simp
  simpa only [v, one] using bound v

noncomputable def evidence : Registration arena (type_of% @source_result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@source_result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other h
      exact (h (by cases other; cases role; rfl)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro role
    let p : signature.Params :=
      ⟨Empty, Unit, Unit, (fun _ => Unit), emptyTree, emptyDomain, emptyTask⟩
    refine ⟨p, (0 : ℕ), (1 : ℕ), ?_⟩
    have yes : actual.readout role p 1 := Nat.sInf_le empty_one
    have no : ¬ actual.readout role p 0 := by
      change ¬ minimumPeak emptyTree emptyDomain emptyTask ≤ 0
      have positive := empty_positive
      omega
    intro he
    exact no (Eq.mpr he yes)

noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@source_result) (Realization signature) Unit Unit where
  unitName := `D5.S3.Observer.Separation.CapacitySensitiveSupport.source_result.__information_unit
  realizationName := `Reg.D5.S3.Observer.Separation.CapacitySensitiveSupport.Source.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p k =>
    minimumPeak p.2.2.2.2.1 p.2.2.2.2.2.1 p.2.2.2.2.2.2 ≤ k) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.Separation.CapacitySensitiveSupport
    definition := none
    coordinates := #[0, 1, 2, 4, 7, 10, 12]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "arg", "body", "fn", "arg"]
      stateBinder := 13
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence

end Source

end Reg.D5.S3.Observer.Separation.CapacitySensitiveSupport
