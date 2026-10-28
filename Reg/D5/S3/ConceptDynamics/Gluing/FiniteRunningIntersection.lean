import D5.S3.ConceptDynamics.Gluing.FiniteRunningIntersection
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration
import Mathlib.Combinatorics.SimpleGraph.Star

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.ConceptDynamics.Gluing.FiniteRunningIntersection

open _root_.D5.S3.ConceptDynamics.Observation.HistoryPayloadFactorization
open _root_.D5.S3.ConceptDynamics.Gluing.RunningIntersectionRecords
open _root_.D5.S3.ConceptDynamics.Gluing.RunningIntersectionMessages
open _root_.D5.S3.ConceptDynamics.Gluing.FiniteRunningIntersection
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Messages

abbrev signature : Signature where
  Params := Type
  State X := Finset X
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ X := X → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ s x => x ∈ s) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ {Node Var O : Type} [Fintype Node] [DecidableEq Node]
  [Fintype Var] [DecidableEq Var] [Fintype O] [DecidableEq O]
  (T : SimpleGraph Node) [DecidableRel T.Adj]
  (S : Node → Set Var) [∀ n, DecidablePred (· ∈ S n)]
  (rows : (n : Node) → Finset (Assignment (fun _ => O) (S n))) (hT : T.IsTree) (e : T.Dart),
    (∀ a, R.readout () (Assignment (fun _ => O) (S e.snd ∩ S e.fst))
      (messageTable T S rows hT e) a ↔
      a ∈ separatorMessages T (fun _ => O) S (fun n => ↑(rows n)) hT e) ∧
    (messageTable T S rows hT e).card ≤
      Fintype.card O ^ Fintype.card ↥(S e.snd ∩ S e.fst)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  let T := SimpleGraph.starGraph (0 : Fin 2)
  let S : Fin 2 → Set Unit := fun _ => ∅
  let rows : (n : Fin 2) → Finset (Assignment (fun _ => Unit) (S n)) :=
    fun _ => {fun _ => ()}
  let e : T.Dart := ⟨(1, 0), by decide⟩
  have semantic : (fun _ => ()) ∈ separatorMessages T (fun _ => Unit) S
      (fun n => ↑(rows n)) (SimpleGraph.isTree_starGraph _) e := by
    rw [separatorMessages.eq_def]
    refine ⟨(fun _ => ()), by simp [rows], rfl, ?_⟩
    intro w hw hwp
    fin_cases w <;> simp_all [T, e, SimpleGraph.starGraph_adj]

  exact ((law T S rows (SimpleGraph.isTree_starGraph _) e).1 _).mpr semantic

def evidence : Registration arena (type_of% @message_table_spec) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@message_table_spec, rejected, rejected_law⟩
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
    refine ⟨Unit, (∅ : Finset Unit), ({()} : Finset Unit), ?_⟩
    intro he
    have hmem := congrFun he ()
    change (() ∈ (∅ : Finset Unit)) = (() ∈ ({()} : Finset Unit)) at hmem
    have no : () ∈ (∅ : Finset Unit) := Eq.mpr hmem (by simp)
    exact Finset.notMem_empty () no

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@message_table_spec) (Realization signature) Unit Unit where
  unitName := `D5.S3.ConceptDynamics.Gluing.FiniteRunningIntersection.message_table_spec.__information_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Gluing.FiniteRunningIntersection.Messages.evidence
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

end Messages

namespace Decoder

abbrev signature : Signature where
  Params := Type
  State X := X
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ X := X → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ {Node Var O : Type} [Fintype Node] [DecidableEq Node]
  [Fintype Var] [DecidableEq Var] [Fintype O] [DecidableEq O]
  (T : SimpleGraph Node) [DecidableRel T.Adj]
  (S : Node → Set Var) [∀ n, DecidablePred (· ∈ S n)]
  (rows : (n : Node) → Finset (Assignment (fun _ => O) (S n))) (hT : T.IsTree) (hRI : RunningIntersection T S) (r : Node)
    (nodes : List Node) (hNodes : ∀ n, n ∈ nodes)
    (a : (n : Node) → Assignment (fun _ => O) (S n)) (ha : Valid T S rows a),
    ∀ n, R.readout () (Assignment (fun _ => O) (S n)) (restrictAssignment (fun _ => O) (E := componentScope S Set.univ)
      (fun _ hx => ⟨n, Set.mem_univ _, hx⟩) (decode S nodes hNodes a)) (a n)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  let T : SimpleGraph Unit := ⊥
  let S : Unit → Set Unit := fun _ => ∅
  let rows : (n : Unit) → Finset (Assignment (fun _ => Unit) (S n)) :=
    fun _ => {fun _ => ()}
  let a : (n : Unit) → Assignment (fun _ => Unit) (S n) := fun _ _ => ()
  have valid : Valid T S rows a := by
    constructor
    · intro n; simp [rows, a]
    · intro p q hpq; exact hpq.elim
  exact law T S rows SimpleGraph.IsTree.of_subsingleton
    (fun _ => SimpleGraph.Preconnected.of_subsingleton) () [()]
    (by intro n; cases n; simp) a valid ()

def evidence : Registration arena (type_of% @decode_spec) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@decode_spec, rejected, rejected_law⟩
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
    refine ⟨Bool, false, true, ?_⟩
    intro he
    have no : true = false := Eq.mp (congrFun he false) rfl
    cases no

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@decode_spec) (Realization signature) Unit Unit where
  unitName := `D5.S3.ConceptDynamics.Gluing.FiniteRunningIntersection.decode_spec.__information_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Gluing.FiniteRunningIntersection.Decoder.evidence
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

end Decoder

namespace Solver

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
  Law R := ∀ {Node Var O : Type} [Fintype Node] [DecidableEq Node]
  [Fintype Var] [DecidableEq Var] [Fintype O] [DecidableEq O]
  (T : SimpleGraph Node) [DecidableRel T.Adj]
  (S : Node → Set Var) [∀ n, DecidablePred (· ∈ S n)]
  (rows : (n : Node) → Finset (Assignment (fun _ => O) (S n))) (hT : T.IsTree) (hRI : RunningIntersection T S) (r : Node)
    (nodes : List Node) (hNodes : ∀ n, n ∈ nodes)
    (vars : List Var) (hVars : ∀ x, x ∈ vars)
    (values : List O) (hValues : ∀ o, o ∈ values) (base : O),
    (R.readout () (Assignment (fun _ => O) (componentScope S Set.univ))
      (solve T S rows hT hRI r nodes hNodes vars hVars values hValues base) = true ↔
      (rawJoin (fun _ => O) S (fun n => ↑(rows n)) Set.univ).Nonempty) ∧
    (∀ j, solve T S rows hT hRI r nodes hNodes vars hVars values hValues base = some j →
      j ∈ rawJoin (fun _ => O) S (fun n => ↑(rows n)) Set.univ) ∧
    (∀ e : T.Dart, (messageTable T S rows hT e).card ≤
      Fintype.card O ^ Fintype.card ↥(S e.snd ∩ S e.fst) ∧
      Fintype.card ↥(S e.snd ∩ S e.fst) ≤ separatorWidth T S)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  let T : SimpleGraph Unit := ⊥
  let S : Unit → Set Unit := fun _ => ∅
  let rows : (n : Unit) → Finset (Assignment (fun _ => Unit) (S n)) :=
    fun _ => {fun _ => ()}
  have join : (rawJoin (fun _ => Unit) S (fun n => ↑(rows n)) Set.univ).Nonempty := by
    refine ⟨fun _ => (), ?_⟩
    intro n hn
    simp [rows, restrictAssignment]
  have bad := (law T S rows SimpleGraph.IsTree.of_subsingleton
    (fun _ => SimpleGraph.Preconnected.of_subsingleton) () [()]
    (by intro n; cases n; simp) [()] (by intro x; cases x; simp)
    [()] (by intro x; cases x; simp) ()).1.mpr join
  exact Bool.noConfusion bad

def evidence : Registration arena (type_of% @solve_spec) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@solve_spec, rejected, rejected_law⟩
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
    (@solve_spec) (Realization signature) Unit Unit where
  unitName := `D5.S3.ConceptDynamics.Gluing.FiniteRunningIntersection.solve_spec.__information_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Gluing.FiniteRunningIntersection.Solver.evidence
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

end Solver

end Reg.D5.S3.ConceptDynamics.Gluing.FiniteRunningIntersection
