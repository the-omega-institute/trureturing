import D5.S3.Observer.Separation.ExecutableCapacityJoin
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace Reg.D5.S3.Observer.Separation.ExecutableCapacityJoin

open _root_.D5.S3.Observer.Separation.FixedTreeCommonExtension
open _root_.D5.S3.Observer.Separation.CapacitySensitiveSupport
open _root_.D5.S3.Observer.Separation.ExecutableCapacityJoin
open _root_.D5.S3.ConceptDynamics.Observation.HistoryPayloadFactorization
open _root_.D5.S3.ConceptDynamics.Gluing.RunningIntersectionRecords
open _root_.D5.S3.ConceptDynamics.Gluing.FiniteRunningIntersection
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Source

abbrev signature : Signature where
  Params := Type
  State X := Option X
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ s => s.isSome) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ {I V O : Type} [Fintype I] [DecidableEq I] {X : I → Type}
  [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
  [Fintype O] [DecidableEq O] [∀ i, Nonempty (X i)]
  (t : Tree I V) (D : Set (∀ i, X i)) [DecidablePred (· ∈ D)]
  (hD : D.Nonempty) (f : D → O)
  [Fintype (Nodes t)] [DecidableEq (Nodes t)]
  (G : SimpleGraph (Nodes t)) [DecidableRel G.Adj] (ht : Full t) (hall : leaves t = Finset.univ)
    (hG : G.IsTree)
    (hRI : RunningIntersection G (fun v => sensitive (sourceCost t D f v)))
    (r : Nodes t) (nodes : List (Nodes t)) (hNodes : ∀ n, n ∈ nodes)
    (vars : List ↥(Dᶜ)) (hVars : ∀ x, x ∈ vars)
    (values : List O) (hValues : ∀ o, o ∈ values),
    costTable t D f = sourceCost t D f ∧
    (∀ k : ℕ,
      R.readout () (Assignment (fun _ => O) (componentScope
        (fun v => sensitive (costTable t D f v)) Set.univ))
        (sourceSolve t D hD f G hG hRI r nodes hNodes vars hVars values hValues k) =
        true ↔ minimumPeak t D f ≤ k) ∧
    (∀ k j, sourceSolve t D hD f G hG hRI r nodes hNodes vars hVars values hValues k =
      some j → j ∈ rawJoin (fun _ => O) (fun v => sensitive (costTable t D f v))
        (fun v => localFeasible (costTable t D f) k v) Set.univ) ∧
    (∀ (k : ℕ) (e : G.Dart),
      (∀ a, a ∈ messageTable G (fun v => sensitive (costTable t D f v))
        (localTable (costTable t D f) k) hG e ↔
          a ∈ D5.S3.ConceptDynamics.Gluing.RunningIntersectionMessages.separatorMessages
            G (fun _ => O) (fun v => sensitive (costTable t D f v))
            (fun v => localFeasible (costTable t D f) k v) hG e) ∧
      (messageTable G (fun v => sensitive (costTable t D f v))
        (localTable (costTable t D f) k) hG e).card ≤
          Fintype.card O ^ Fintype.card
            ↥(sensitive (costTable t D f e.snd) ∩ sensitive (costTable t D f e.fst)) ∧
      Fintype.card
        ↥(sensitive (costTable t D f e.snd) ∩ sensitive (costTable t D f e.fst)) ≤
          separatorWidth G (fun v => sensitive (costTable t D f v)))

private def tree : Tree Empty Unit := .node () 0 Fin.elim0
private abbrev N := Nodes tree
private def root : N := ⟨tree, by simp [tree, subtrees]⟩
private instance : Subsingleton N := ⟨fun a b => by
  apply Subtype.ext
  have ha : a.val = tree := by simpa [tree, subtrees] using a.property
  have hb : b.val = tree := by simpa [tree, subtrees] using b.property
  exact ha.trans hb.symm⟩
private instance : Nonempty N := ⟨root⟩
private instance : DecidableEq N := fun _ _ => isTrue (Subsingleton.elim _ _)
private instance : Fintype N := ⟨{root}, fun n => by simp [Subsingleton.elim n root]⟩
private def promise : Set (Empty → Unit) := Set.univ
private instance : DecidablePred (· ∈ promise) := fun _ => isTrue (Set.mem_univ _)
private def task (_ : promise) : Unit := ()
private theorem promise_nonempty : promise.Nonempty :=
  ⟨(fun i => nomatch i), Set.mem_univ _⟩
private def graph : SimpleGraph N := ⊥
private instance : DecidableRel graph.Adj := inferInstanceAs (DecidableRel (⊥ : SimpleGraph N).Adj)
private theorem graph_tree : graph.IsTree := SimpleGraph.IsTree.of_subsingleton
private theorem graph_ri : RunningIntersection graph
    (fun v => sensitive (sourceCost tree promise task v)) :=
  fun _ => SimpleGraph.Preconnected.of_subsingleton

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have full : Full tree := ⟨(fun j => Fin.elim0 j), (fun j => Fin.elim0 j)⟩
  have all : leaves tree = Finset.univ := by ext i; exact nomatch i
  have bad := ((law tree promise promise_nonempty task graph full all
    graph_tree graph_ri root [root] (by intro n; simp [Subsingleton.elim n root])
    [] (by intro x; exact x.property.elim (Set.mem_univ _))
    [()] (by intro x; cases x; simp)).2.1
      (minimumPeak tree promise task)).mpr le_rfl
  exact Bool.noConfusion bad

def evidence : Registration arena (type_of% @source_solver_spec) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@source_solver_spec, rejected, rejected_law⟩
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
    refine ⟨Unit, none, some (), ?_⟩
    change false ≠ true
    decide

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@source_solver_spec) (Realization signature) Unit Unit where
  unitName := `D5.S3.Observer.Separation.ExecutableCapacityJoin.source_solver_spec.__information_unit
  realizationName := `Reg.D5.S3.Observer.Separation.ExecutableCapacityJoin.Source.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence

end Source

namespace Boundary

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ k => EmptyCoordinates.answer k) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => true) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := R.readout () () 0 = false ∧ EmptyCoordinates.answer 1 = true ∧
    minimumPeak (.node () 0 Fin.elim0 : Tree Empty Unit)
      (Set.univ : Set (Empty → Unit)) (fun _ => ()) = 1

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  exact Bool.noConfusion law.1

def evidence : Registration arena (type_of% @_root_.D5.S3.Observer.Separation.ExecutableCapacityJoin.result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S3.Observer.Separation.ExecutableCapacityJoin.result, rejected, rejected_law⟩
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
    refine ⟨(), (0 : ℕ), (1 : ℕ), ?_⟩
    change EmptyCoordinates.answer 0 ≠ EmptyCoordinates.answer 1
    rw [_root_.D5.S3.Observer.Separation.ExecutableCapacityJoin.result.1,
      _root_.D5.S3.Observer.Separation.ExecutableCapacityJoin.result.2.1]
    decide

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Observer.Separation.ExecutableCapacityJoin.result)
    (Realization signature) Unit Unit where
  unitName := `D5.S3.Observer.Separation.ExecutableCapacityJoin.result.__information_unit
  realizationName := `Reg.D5.S3.Observer.Separation.ExecutableCapacityJoin.Boundary.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.Separation.ExecutableCapacityJoin
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence

end Boundary
end Reg.D5.S3.Observer.Separation.ExecutableCapacityJoin
