/- GID: D5/S3/ConceptDynamics/Gluing/FiniteRunningIntersection
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Gluing/FiniteRunningIntersection
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Data.Fintype.BigOperators]
   utility: kind=checker; basis=consumer=D5/S3/Observer/Separation/ExecutableCapacityJoin.source_solver_spec; instance=D5/S3/Observer/Separation/ExecutableCapacityJoin.result
   digest: Executable separator tables and finite certificate decoding refine running-intersection messages. -/

import D5.S3.ConceptDynamics.Gluing.RunningIntersectionMessages
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.List.Basic

/-! Finite table elimination on arbitrary running-intersection support trees. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Gluing.FiniteRunningIntersection

open D5.S3.ConceptDynamics.Observation.HistoryPayloadFactorization
open D5.S3.ConceptDynamics.Gluing.RunningIntersectionRecords
open D5.S3.ConceptDynamics.Gluing.RunningIntersectionMessages
open SimpleGraph

variable {Node Var O : Type} [Fintype Node] [DecidableEq Node]
  [Fintype Var] [DecidableEq Var] [Fintype O] [DecidableEq O]
  (T : SimpleGraph Node) [DecidableRel T.Adj]
  (S : Node → Set Var) [∀ n, DecidablePred (· ∈ S n)]
  (rows : (n : Node) → Finset (Assignment (fun _ => O) (S n)))

omit [Fintype Node] [DecidableEq Node] [DecidableRel T.Adj] in
private theorem child_component_lt [Finite Node] (hT : T.IsTree) (e : T.Dart)
    (w : Node) (hw : T.Adj w e.fst) (hwp : w ≠ e.snd) :
    (edgeLeft T ⟨(w, e.fst), hw⟩).ncard < (edgeLeft T e).ncard := by
  classical
  let c : T.Dart := ⟨(w, e.fst), hw⟩
  have hc := edge_cut_components T hT c
  have he := edge_cut_components T hT e
  have hwE : w ∈ edgeLeft T e := by
    have hedge : s(e.fst, w) ≠ e.edge := by
      intro h
      rcases Sym2.eq_iff.mp h with h | h
      · exact hwp h.2
      · exact e.fst_ne_snd h.1
    exact (show (T.deleteEdges {e.edge}).Adj e.fst w by
      simpa using And.intro hw.symm hedge).reachable
  have sub : edgeLeft T c ⊆ edgeLeft T e := by
    intro n hn
    obtain ⟨p⟩ := hn
    let q := p.map (Hom.ofLE (T.deleteEdges_le {c.edge}))
    have hv : e.fst ∉ p.support := by
      intro hv
      exact hc.2.1 (p.takeUntil e.fst hv).reachable
    have hedge : e.edge ∉ q.edges := by
      intro h
      have hs := q.fst_mem_support_of_mem_edges h
      apply hv
      simpa only [q, Walk.support_map, Hom.coe_ofLE, List.map_id_fun, id_eq] using hs
    exact hwE.trans (reachable_deleteEdges_iff_exists_walk.mpr ⟨q, hedge⟩)
  exact Set.ncard_lt_ncard ⟨sub, fun back => hc.2.1 (back he.1)⟩ (Set.toFinite _)

/-- Compute an inward table by testing every nonparent neighbor and projecting
the surviving input rows. Only finite equality, adjacency and membership are tested. -/
def messageTable [Finite Node] (hT : T.IsTree) (e : T.Dart) :
    Finset (Assignment (fun _ => O) (S e.snd ∩ S e.fst)) :=
  ((rows e.fst).filter (fun a => ∀ w : Node,
    (if hw : T.Adj w e.fst then if hwp : w ≠ e.snd then
      decide (restrictAssignment (fun _ => O) (D := S e.fst ∩ S w)
        Set.inter_subset_left a ∈ messageTable hT ⟨(w, e.fst), hw⟩)
      else true else true) = true)).image
    (restrictAssignment (fun _ => O) Set.inter_subset_right)
termination_by (edgeLeft T e).ncard
decreasing_by all_goals exact child_component_lt T hT e _ ‹T.Adj _ e.fst› ‹_ ≠ e.snd›

/-- Every computed message is exactly the semantic recursive message, and its
actual output fits the original separator assignment carrier. -/
theorem message_table_spec (hT : T.IsTree) (e : T.Dart) :
    (∀ a, a ∈ messageTable T S rows hT e ↔
      a ∈ separatorMessages T (fun _ => O) S (fun n => ↑(rows n)) hT e) ∧
    (messageTable T S rows hT e).card ≤
      Fintype.card O ^ Fintype.card ↥(S e.snd ∩ S e.fst) := by
  classical
  have exactness : ∀ (e : T.Dart) a, a ∈ messageTable T S rows hT e ↔
      a ∈ separatorMessages T (fun _ => O) S (fun n => ↑(rows n)) hT e := by
    intro e
    induction e using separatorMessages.induct T hT with
    | case1 e ih =>
      intro a
      rw [messageTable.eq_def, separatorMessages.eq_def]
      simp only [Finset.mem_image, Finset.mem_filter, Set.mem_setOf_eq, Finset.mem_coe]
      constructor
      · rintro ⟨b, ⟨hb, hc⟩, rfl⟩
        exact ⟨b, hb, rfl, fun w hw hwp => (ih w hw hwp _).mp (by simpa [hw, hwp] using hc w)⟩
      · rintro ⟨b, hb, rfl, hc⟩
        exact ⟨b, ⟨hb, fun w => by
          split_ifs with hw hwp
          · simpa using (ih w hw hwp _).mpr (hc w hw hwp)
          all_goals rfl⟩, rfl⟩
  refine ⟨exactness e, ?_⟩
  calc
    (messageTable T S rows hT e).card ≤
        Fintype.card (Assignment (fun _ => O) (S e.snd ∩ S e.fst)) :=
      Finset.card_le_univ _
    _ = Fintype.card O ^ Fintype.card ↥(S e.snd ∩ S e.fst) := Fintype.card_fun

/-- The root table retains exactly the local rows passing all inward tables. -/
def rootTable (hT : T.IsTree) (r : Node) :
    Finset (Assignment (fun _ => O) (S r)) :=
  (rows r).filter (fun a => ∀ w : Node, if hw : T.Adj w r then
    restrictAssignment (fun _ => O) (D := S r ∩ S w) Set.inter_subset_left a ∈
      messageTable T S rows hT ⟨(w, r), hw⟩ else True)

/-- A compressed certificate has one local row per node, agreeing on every
complete separator. No consistency of the unfiltered input relations is assumed. -/
def Valid (a : (n : Node) → Assignment (fun _ => O) (S n)) : Prop :=
  (∀ n, a n ∈ rows n) ∧ ∀ (p q : Node), T.Adj p q →
    restrictAssignment (fun _ => O) (D := S p ∩ S q) Set.inter_subset_left (a p) =
      restrictAssignment (fun _ => O) Set.inter_subset_right (a q)

private theorem certificate_extends (hT : T.IsTree)
    (hRI : RunningIntersection T S) (r : Node)
    (a : (n : Node) → Assignment (fun _ => O) (S n))
    (ha : Valid T S rows a) :
    ∃ j : Assignment (fun _ => O) (componentScope S Set.univ),
      ∀ n, restrictAssignment (fun _ => O)
        (E := componentScope S Set.univ) (fun _ hx => ⟨n, Set.mem_univ _, hx⟩) j = a n := by
  classical
  let singletons (n : Node) : Set (Assignment (fun _ => O) (S n)) := {a n}
  have hc : EdgeProjectionConsistency T (fun _ => O) S singletons := by
    intro p q hpq
    simp only [singletons, Set.image_singleton]
    exact congrArg (fun b => ({b} : Set (Assignment (fun _ => O) (S p ∩ S q))))
      (ha.2 p q hpq)
  obtain ⟨j, _⟩ := local_row_extends_raw_join T (fun _ => O) S singletons
    hT hRI (fun n => ⟨a n, rfl⟩) hc r (a r) rfl
  exact ⟨j.val, fun n => Set.mem_singleton_iff.mp (j.property n (Set.mem_univ _))⟩

private instance validDecidable : DecidablePred (Valid T S rows) := fun a =>
  inferInstanceAs (Decidable ((∀ n, a n ∈ rows n) ∧ ∀ (p q : Node), T.Adj p q →
    restrictAssignment (fun _ => O) (D := S p ∩ S q) Set.inter_subset_left (a p) =
      restrictAssignment (fun _ => O) Set.inter_subset_right (a q)))

/-- Root acceptance is precisely the existence of a finite separator certificate. -/
private theorem root_certificate_iff (hT : T.IsTree) (hRI : RunningIntersection T S)
    (r : Node) : (rootTable T S rows hT r).Nonempty ↔
      ∃ a, Valid T S rows a := by
  classical
  have root : (rootTable T S rows hT r).Nonempty ↔
      (rawJoin (fun _ => O) S (fun n => ↑(rows n)) Set.univ).Nonempty := by
    rw [raw_join_nonempty_iff_root T (fun _ => O) S (fun n => ↑(rows n)) hT hRI r]
    simp only [rootTable, Finset.Nonempty, Finset.mem_filter, Finset.mem_coe]
    constructor
    · rintro ⟨a, ha, hc⟩
      exact ⟨a, ha, fun w hw => ((message_table_spec T S rows hT ⟨(w, r), hw⟩).1 _).mp (by simpa [hw] using hc w)⟩
    · rintro ⟨a, ha, hc⟩
      exact ⟨a, ha, fun w => by
        split_ifs with hw
        · exact ((message_table_spec T S rows hT ⟨(w, r), hw⟩).1 _).mpr (hc w hw)
        ⟩
  rw [root]
  constructor
  · rintro ⟨j, hj⟩
    refine ⟨fun n => restrictAssignment (fun _ => O)
      (E := componentScope S Set.univ) (fun _ hx => ⟨n, Set.mem_univ _, hx⟩) j,
      (fun n => hj n (Set.mem_univ _)), ?_⟩
    intro p q _
    rfl
  · rintro ⟨a, ha⟩
    obtain ⟨j, hj⟩ := certificate_extends T S rows hT hRI r a ha
    refine ⟨j, ?_⟩
    intro n hn
    rw [hj n]
    exact ha.1 n

/-- Decode a row certificate by finding an occurrence of each requested variable.
The search uses the supplied finite node enumeration, not an existence oracle. -/
def decode (nodes : List Node) (hNodes : ∀ n, n ∈ nodes)
    (a : (n : Node) → Assignment (fun _ => O) (S n)) :
    Assignment (fun _ => O) (componentScope S Set.univ) := fun x =>
  let n := nodes.chooseX (fun n => x.val ∈ S n) (by
    obtain ⟨n, _, hn⟩ := x.property
    exact ⟨n, hNodes n, hn⟩)
  a n.val ⟨x.val, n.property.2⟩

/-- The finite occurrence decoder reconstructs every row of a valid certificate. -/
theorem decode_spec (hT : T.IsTree) (hRI : RunningIntersection T S) (r : Node)
    (nodes : List Node) (hNodes : ∀ n, n ∈ nodes)
    (a : (n : Node) → Assignment (fun _ => O) (S n)) (ha : Valid T S rows a) :
    ∀ n, restrictAssignment (fun _ => O) (E := componentScope S Set.univ)
      (fun _ hx => ⟨n, Set.mem_univ _, hx⟩) (decode S nodes hNodes a) = a n := by
  obtain ⟨j, hj⟩ := certificate_extends T S rows hT hRI r a ha
  have eq : decode S nodes hNodes a = j := by
    funext x
    let n := nodes.chooseX (fun n => x.val ∈ S n) (by
      obtain ⟨n, _, hn⟩ := x.property
      exact ⟨n, hNodes n, hn⟩)
    exact (congrFun (hj n.val) ⟨x.val, n.property.2⟩).symm
  intro n
  rw [eq]
  exact hj n

/-- Enumerate total functions by finite updates from explicit coordinate and
output lists. The base value is used only outside the listed coordinates. -/
private def functionEnumeration (values : List O) (base : O) : List Var → List (Var → O)
  | [] => [fun _ => base]
  | x :: xs => (functionEnumeration values base xs).flatMap
      (fun g => values.map (fun o => Function.update g x o))

private theorem enumeration_covers (values : List O) (base : O)
    (hValues : ∀ o, o ∈ values) (xs : List Var) (f : Var → O) :
    ∃ g ∈ functionEnumeration values base xs, ∀ x ∈ xs, g x = f x := by
  induction xs with
  | nil => exact ⟨(fun _ => base), by simp [functionEnumeration], by simp⟩
  | cons x xs ih =>
    obtain ⟨g, hg, he⟩ := ih
    refine ⟨Function.update g x (f x), ?_, ?_⟩
    · simp only [functionEnumeration, List.mem_flatMap, List.mem_map]
      exact ⟨g, hg, f x, hValues _, rfl⟩
    · intro y hy
      by_cases h : y = x
      · subst y; simp
      · rw [Function.update_of_ne h]
        exact he y ((List.mem_cons.mp hy).resolve_left h)

/-- Candidate certificates use explicit finite assignment enumeration. Validity
checks only input-row membership and equality on complete edge separators. -/
private def certificateCandidates (vars : List Var) (values : List O) (base : O) :
    List ((n : Node) → Assignment (fun _ => O) (S n)) :=
  (functionEnumeration values base vars).map (fun g n x => g x.val)

private theorem certificate_candidate_exists (hT : T.IsTree)
    (hRI : RunningIntersection T S) (r : Node)
    (vars : List Var) (hVars : ∀ x, x ∈ vars)
    (values : List O) (hValues : ∀ o, o ∈ values) (base : O)
    (hRoot : (rootTable T S rows hT r).Nonempty) :
    ∃ a, a ∈ certificateCandidates S vars values base ∧ Valid T S rows a := by
  classical
  obtain ⟨a, ha⟩ := (root_certificate_iff T S rows hT hRI r).mp hRoot
  obtain ⟨j, hj⟩ := certificate_extends T S rows hT hRI r a ha
  let f : Var → O := fun x => if hx : x ∈ componentScope S Set.univ then j ⟨x, hx⟩
    else base
  obtain ⟨g, hg, he⟩ := enumeration_covers values base hValues vars f
  have gf : g = f := funext (fun x => he x (hVars x))
  have ga : (fun n (x : S n) => g x.val) = a := by
    funext n x
    rw [gf]
    have hx : x.val ∈ componentScope S Set.univ := ⟨n, Set.mem_univ _, x.property⟩
    simpa [f, hx, restrictAssignment] using congrFun (hj n) x
  refine ⟨a, ?_, ha⟩
  rw [certificateCandidates, List.mem_map]
  exact ⟨g, hg, ga⟩

/-- Select a finite certificate and decode it exactly when the computed root
table accepts. All semantic existence proofs are erased from computation. -/
def solve (hT : T.IsTree) (hRI : RunningIntersection T S) (r : Node)
    (nodes : List Node) (hNodes : ∀ n, n ∈ nodes)
    (vars : List Var) (hVars : ∀ x, x ∈ vars)
    (values : List O) (hValues : ∀ o, o ∈ values) (base : O) :
    Option (Assignment (fun _ => O) (componentScope S Set.univ)) :=
  if h : (rootTable T S rows hT r).Nonempty then
    let a := (certificateCandidates S vars values base).chooseX (Valid T S rows)
      (certificate_candidate_exists T S rows hT hRI r vars hVars values hValues base h)
    some (decode S nodes hNodes a.val)
  else none

/-- Separator width counts illegal-cell assignments across an edge. A singleton
tree has width zero. It does not bound all tables or the witness search together. -/
def separatorWidth : ℕ :=
  Finset.univ.sup (fun e : T.Dart => Fintype.card ↥(S e.snd ∩ S e.fst))

/-- The executable solver decides the exact native join and returns a compatible
global assignment. Every actual message retains the original carrier bound. -/
theorem solve_spec (hT : T.IsTree) (hRI : RunningIntersection T S) (r : Node)
    (nodes : List Node) (hNodes : ∀ n, n ∈ nodes)
    (vars : List Var) (hVars : ∀ x, x ∈ vars)
    (values : List O) (hValues : ∀ o, o ∈ values) (base : O) :
    ((solve T S rows hT hRI r nodes hNodes vars hVars values hValues base).isSome = true ↔
      (rawJoin (fun _ => O) S (fun n => ↑(rows n)) Set.univ).Nonempty) ∧
    (∀ j, solve T S rows hT hRI r nodes hNodes vars hVars values hValues base = some j →
      j ∈ rawJoin (fun _ => O) S (fun n => ↑(rows n)) Set.univ) ∧
    (∀ e : T.Dart, (messageTable T S rows hT e).card ≤
      Fintype.card O ^ Fintype.card ↥(S e.snd ∩ S e.fst) ∧
      Fintype.card ↥(S e.snd ∩ S e.fst) ≤ separatorWidth T S) := by
  classical
  have join_cert : (rawJoin (fun _ => O) S (fun n => ↑(rows n)) Set.univ).Nonempty ↔
      ∃ a, Valid T S rows a := by
    constructor
    · rintro ⟨j, hj⟩
      exact ⟨fun n x => j ⟨x.val, ⟨n, Set.mem_univ _, x.property⟩⟩,
        (fun n => hj n (Set.mem_univ _)), (fun _ _ _ => rfl)⟩
    · rintro ⟨a, ha⟩
      obtain ⟨j, hj⟩ := certificate_extends T S rows hT hRI r a ha
      exact ⟨j, fun n _ => by rw [hj n]; exact ha.1 n⟩
  constructor
  · rw [join_cert, ← root_certificate_iff T S rows hT hRI r]
    unfold solve
    split_ifs <;> simp_all
  constructor
  · intro j hj
    unfold solve at hj
    split_ifs at hj with h
    · have eq := Option.some.inj hj
      rw [← eq]
      let a := (certificateCandidates S vars values base).chooseX (Valid T S rows)
        (certificate_candidate_exists T S rows hT hRI r vars hVars values hValues base h)
      intro n hn
      rw [decode_spec T S rows hT hRI r nodes hNodes a.val a.property.2 n]
      exact a.property.2.1 n
  · intro e
    exact ⟨(message_table_spec T S rows hT e).2,
      Finset.le_sup (f := fun e : T.Dart => Fintype.card ↥(S e.snd ∩ S e.fst))
        (Finset.mem_univ e)⟩

end D5.S3.ConceptDynamics.Gluing.FiniteRunningIntersection
