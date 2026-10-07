/- GID: D5/S3/ConceptDynamics/Gluing/RunningIntersectionMessages
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Gluing/RunningIntersectionMessages
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Acyclic]
   utility: none
   digest: Recursive tree messages characterize nonemptiness of the native raw join. -/

import D5.S3.ConceptDynamics.Gluing.RunningIntersectionRecords

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Gluing.RunningIntersectionMessages

open D5.S3.ConceptDynamics.Observation.HistoryPayloadFactorization
open D5.S3.ConceptDynamics.Gluing.RunningIntersectionRecords
open SimpleGraph

universe i u v
variable {Node : Type i} {Var : Type u}
variable (T : SimpleGraph Node) (Value : Var → Type v) (S : Node → Set Var)
variable (Γ : (n : Node) → Set (Assignment Value (S n)))

/-- An inward message is computed from the local row and all neighbors except
the parent. The separator carrier lists the parent first. Choosing a root
selects the darts directed toward it; no global-join projection defines a message. -/
noncomputable def separatorMessages [Finite Node] (hT : T.IsTree) (e : T.Dart) :
    Set (Assignment Value (S e.snd ∩ S e.fst)) :=
  {t | ∃ a ∈ Γ e.fst,
    restrictAssignment Value Set.inter_subset_right a = t ∧
    ∀ (w : Node) (hw : T.Adj w e.fst), w ≠ e.snd →
      restrictAssignment Value (D := S e.fst ∩ S w) Set.inter_subset_left a ∈
        separatorMessages hT ⟨(w, e.fst), hw⟩}
termination_by (edgeLeft T e).ncard
decreasing_by
  classical
  let c : T.Dart := ⟨(w, e.fst), hw⟩
  have hc := edge_cut_components T hT c
  have he := edge_cut_components T hT e
  have hwE : w ∈ edgeLeft T e := by
    have hedge : s(e.fst, w) ≠ e.edge := by
      intro h
      rcases Sym2.eq_iff.mp h with h | h
      · exact ‹w ≠ e.snd› h.2
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

/-- Root acceptance is equivalent to a nonempty raw global join. Relations,
scopes, separators and dependent value types need not be nonempty or finite. -/
theorem raw_join_nonempty_iff_root [Finite Node] (hT : T.IsTree)
    (hRI : RunningIntersection T S) (r : Node) :
    (rawJoin Value S Γ Set.univ).Nonempty ↔
      ∃ a ∈ Γ r, ∀ (w : Node) (hw : T.Adj w r),
        restrictAssignment Value (D := S r ∩ S w) Set.inter_subset_left a ∈
          separatorMessages T Value S Γ hT ⟨(w, r), hw⟩ := by
  classical
  constructor
  · rintro ⟨j, hj⟩
    have adequate (e : T.Dart) :
        restrictAssignment Value (D := S e.snd ∩ S e.fst)
          (E := componentScope S Set.univ)
          (fun _ hx => ⟨e.fst, Set.mem_univ _, hx.2⟩) j ∈
            separatorMessages T Value S Γ hT e := by
      induction e using separatorMessages.induct T hT with
      | case1 e ih =>
        rw [separatorMessages.eq_def]
        refine ⟨restrictAssignment Value (D := S e.fst)
          (E := componentScope S Set.univ)
          (fun _ hx => ⟨e.fst, Set.mem_univ _, hx⟩) j,
          hj e.fst (Set.mem_univ _), rfl, ?_⟩
        intro w hw hwp
        exact ih w hw hwp
    let a : Assignment Value (S r) :=
      restrictAssignment Value (E := componentScope S Set.univ)
        (fun _ hx => ⟨r, Set.mem_univ _, hx⟩) j
    exact ⟨a, hj r (Set.mem_univ _), fun w hw => adequate ⟨(w, r), hw⟩⟩
  · rintro ⟨a, ha, hroot⟩
    let Good (n : Node) := {b : Assignment Value (S n) //
      b ∈ Γ n ∧ ∀ (w : Node) (hw : T.Adj w n),
        restrictAssignment Value (D := S n ∩ S w) Set.inter_subset_left b ∈
          separatorMessages T Value S Γ hT ⟨(w, n), hw⟩}
    have next (p q : Node) (hpq : T.Adj p q) (b : Good p) :
        ∃ c : Good q,
          restrictAssignment Value (D := S p ∩ S q) Set.inter_subset_right c.val =
            restrictAssignment Value Set.inter_subset_left b.val := by
      have hb := b.property.2 q hpq.symm
      rw [separatorMessages.eq_def] at hb
      obtain ⟨c, hc, hcb, hchildren⟩ := hb
      have hcGood : ∀ (w : Node) (hw : T.Adj w q),
          restrictAssignment Value (D := S q ∩ S w) Set.inter_subset_left c ∈
            separatorMessages T Value S Γ hT ⟨(w, q), hw⟩ := by
        intro w hw
        by_cases hwp : w = p
        · subst w
          rw [separatorMessages.eq_def]
          refine ⟨b.val, b.property.1, ?_, ?_⟩
          · funext x
            exact (congrFun hcb ⟨x.val, x.property.2, x.property.1⟩).symm
          · intro z hz _
            exact b.property.2 z hz
        · exact hchildren w hw hwp
      exact ⟨⟨c, hc, hcGood⟩, hcb⟩
    let step (p q : Node) (hpq : T.Adj p q) (b : Good p) : Good q :=
      (next p q hpq b).choose
    have step_agrees (p q : Node) (hpq : T.Adj p q) (b : Good p) :
        restrictAssignment Value (D := S p ∩ S q) Set.inter_subset_right
          (step p q hpq b).val =
            restrictAssignment Value Set.inter_subset_left b.val :=
      (next p q hpq b).choose_spec
    let lift {p q : Node} (walk : T.Walk p q) : Good p → Good q :=
      walk.concatRec (motive := fun p q _ => Good p → Good q)
        (fun b => b) (fun _ hpq f b => step _ _ hpq (f b))
    have lift_concat {p q z : Node} (walk : T.Walk p q) (hqz : T.Adj q z)
        (b : Good p) :
        lift (walk.concat hqz) b = step q z hqz (lift walk b) := by
      simp only [lift, Walk.concatRec_concat]
    let initial : Good r := ⟨a, ha, hroot⟩
    let path (n : Node) : T.Path r n := (hT.connected r n).some.toPath
    let rows (n : Node) : Good n := lift (path n).val initial
    have agree (p q : Node) (hpq : T.Adj p q) :
        restrictAssignment Value (D := S p ∩ S q) Set.inter_subset_left (rows p).val =
          restrictAssignment Value Set.inter_subset_right (rows q).val := by
      by_cases hp : p ∈ (path q).val.support
      · have hpath := hT.isAcyclic.path_concat (path p).property
          (path q).property hpq hp
        have hrows : rows q = step p q hpq (rows p) := by
          change lift (path q).val initial = _
          rw [hpath, lift_concat]
        rw [hrows]
        exact (step_agrees p q hpq (rows p)).symm
      · have hq := hT.isAcyclic.mem_support_of_ne_mem_support_of_adj_of_isPath
          (path p).property (path q).property hpq hp
        have hpath := hT.isAcyclic.path_concat (path q).property
          (path p).property hpq.symm hq
        have hrows : rows p = step q p hpq.symm (rows q) := by
          change lift (path p).val initial = _
          rw [hpath, lift_concat]
        rw [hrows]
        funext x
        exact congrFun (step_agrees q p hpq.symm (rows q))
          ⟨x.val, x.property.2, x.property.1⟩
    let singletons (n : Node) : Set (Assignment Value (S n)) := {(rows n).val}
    have nonempty (n : Node) : (singletons n).Nonempty := ⟨(rows n).val, rfl⟩
    have consistent : EdgeProjectionConsistency T Value S singletons := by
      intro p q hpq
      simp only [singletons, Set.image_singleton]
      exact congrArg (fun b => ({b} : Set (Assignment Value (S p ∩ S q)))) (agree p q hpq)
    obtain ⟨j, _⟩ := local_row_extends_raw_join T Value S singletons hT hRI
      nonempty consistent r (rows r).val (Set.mem_singleton _)
    refine ⟨j.val, ?_⟩
    intro n hn
    have hj := j.property n hn
    have hrow : restrictAssignment Value (D := S n) (E := componentScope S Set.univ)
        (fun _ hx => ⟨n, hn, hx⟩) j.val = (rows n).val :=
      Set.mem_singleton_iff.mp hj
    rw [hrow]
    exact (rows n).property.1

end D5.S3.ConceptDynamics.Gluing.RunningIntersectionMessages
