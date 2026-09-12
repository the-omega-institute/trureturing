/- GID: D5/S3/ConceptDynamics/Gluing/RunningIntersectionRecords
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Gluing/RunningIntersectionRecords
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Acyclic, mathlib/module/Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph]
   utility: none
   digest: Running intersection identifies complete cut boundaries and extends every specified local row on a finite tree. -/

import D5.S3.ConceptDynamics.Observation.HistoryPayloadFactorization
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Gluing.RunningIntersectionRecords

open D5.S3.ConceptDynamics.Observation.HistoryPayloadFactorization
open SimpleGraph
universe i u v
variable {Node : Type i} {Var : Type u} (T : SimpleGraph Node)
variable (Value : Var → Type v) (S : Node → Set Var)

/-- Occurrences are preconnected; a variable that never occurs imposes no condition. -/
def RunningIntersection : Prop := ∀ x, (T.induce {n | x ∈ S n}).Preconnected

private theorem running_intersection_iff : RunningIntersection T S ↔
    ∀ x, (∃ n, x ∈ S n) → (T.induce {n | x ∈ S n}).Connected := by
  constructor
  · intro h x hx
    refine { preconnected := h x, nonempty := ?_ }
    obtain ⟨n, hn⟩ := hx
    exact ⟨⟨n, hn⟩⟩
  · intro h x a b
    exact (h x ⟨a.val, a.property⟩).preconnected a b

private theorem occurrence_path_support (hT : T.IsAcyclic)
    (hRI : RunningIntersection T S) {x : Var} {p q : Node}
    (hp : x ∈ S p) (hq : x ∈ S q) (w : T.Path p q) :
    ∀ n ∈ w.val.support, x ∈ S n := by
  classical
  obtain ⟨v⟩ := hRI x ⟨p, hp⟩ ⟨q, hq⟩
  let v' := v.toPath.map (Embedding.induce {n | x ∈ S n}).toHom Subtype.val_injective
  have hw : w = v' := (hT.subsingleton_path p q).elim _ _
  intro n hn
  rw [hw] at hn
  change n ∈ (v.toPath.val.map (Embedding.induce {n | x ∈ S n}).toHom).support at hn
  rw [Walk.support_map] at hn
  obtain ⟨z, _, rfl⟩ := List.mem_map.mp hn
  exact z.property

/-- The actual connected component after deleting the chosen edge. -/
def edgeLeft (e : T.Dart) : Set Node := {n | (T.deleteEdges {e.edge}).Reachable e.fst n}

private theorem cut_endpoints (hT : T.IsTree) (e : T.Dart) :
    e.fst ∈ edgeLeft T e ∧ e.snd ∉ edgeLeft T e := by
  refine ⟨Reachable.refl _, ?_⟩
  exact (isBridge_iff.mp ((isAcyclic_iff_forall_isBridge.mp hT.isAcyclic) e.edge_mem))

private theorem cut_crossing (e : T.Dart) {p q : Node}
    (hp : p ∈ edgeLeft T e) (hq : q ∉ edgeLeft T e) (hpq : T.Adj p q) :
    s(p, q) = e.edge := by
  by_contra h
  have hpqH : (T.deleteEdges {e.edge}).Adj p q := by simpa using And.intro hpq h
  exact hq (hp.trans hpqH.reachable)

/-- Deleting a tree edge leaves exactly the two endpoint components. -/
theorem edge_cut_components (hT : T.IsTree) (e : T.Dart) :
    e.fst ∈ edgeLeft T e ∧ e.snd ∉ edgeLeft T e ∧
    (edgeLeft T e)ᶜ = {n | (T.deleteEdges {e.edge}).Reachable e.snd n} ∧
    ∀ n, (T.deleteEdges {e.edge}).connectedComponentMk n =
        (T.deleteEdges {e.edge}).connectedComponentMk e.fst ∨
      (T.deleteEdges {e.edge}).connectedComponentMk n =
        (T.deleteEdges {e.edge}).connectedComponentMk e.snd := by
  have he := cut_endpoints T hT e
  have sides : ∀ {a b : Node}, T.Walk a b →
      ((T.deleteEdges {e.edge}).Reachable e.fst a ∨
        (T.deleteEdges {e.edge}).Reachable e.snd a) →
      ((T.deleteEdges {e.edge}).Reachable e.fst b ∨
        (T.deleteEdges {e.edge}).Reachable e.snd b) := by
    intro a b w
    induction w with
    | nil => exact id
    | @cons a b c hab w ih =>
      intro ha
      apply ih
      by_cases hab' : s(a, b) = e.edge
      · rcases Sym2.eq_iff.mp hab' with h | h
        · exact Or.inr (h.2 ▸ Reachable.refl _)
        · exact Or.inl (h.2 ▸ Reachable.refl _)
      · have habH : (T.deleteEdges {e.edge}).Adj a b := by simpa using And.intro hab hab'
        exact ha.imp (fun h => h.trans habH.reachable) (fun h => h.trans habH.reachable)
  have allSides (n : Node) := sides (hT.connected.preconnected e.fst n).some (Or.inl he.1)
  refine ⟨he.1, he.2, ?_, ?_⟩
  · ext n
    exact ⟨fun hn => (allSides n).resolve_left hn,
      fun hn hl => he.2 (hl.trans hn.symm)⟩
  · intro n
    exact (allSides n).imp (fun h => ConnectedComponent.eq.mpr h.symm)
      (fun h => ConnectedComponent.eq.mpr h.symm)

private theorem occurrence_crossing (hRI : RunningIntersection T S) (A : Set Node)
    {x : Var} (hx : x ∈ componentScope S A ∩ componentScope S Aᶜ) :
    ∃ p ∈ A, ∃ q ∉ A, T.Adj p q ∧ x ∈ S p ∩ S q := by
  obtain ⟨⟨p, hp, hxp⟩, ⟨q, hq, hxq⟩⟩ := hx
  obtain ⟨w⟩ := hRI x ⟨p, hxp⟩ ⟨q, hxq⟩
  obtain ⟨d, _, hdA, hdB⟩ := w.exists_boundary_dart
    (Subtype.val ⁻¹' A) hp hq
  exact ⟨d.fst.val, hdA, d.snd.val, hdB, d.adj, d.fst.property, d.snd.property⟩

/-- The full boundary is the union of complete crossing-edge separators, for any A. -/
theorem boundary_eq_union_separators (hRI : RunningIntersection T S) (A : Set Node) :
    componentScope S A ∩ componentScope S Aᶜ =
      ⋃ p ∈ A, ⋃ q ∉ A, ⋃ (_ : T.Adj p q), S p ∩ S q := by
  ext x
  simp only [Set.mem_iUnion]
  exact ⟨fun hx => by
      obtain ⟨p, hp, q, hq, ha, hs⟩ := occurrence_crossing T S hRI A hx
      exact ⟨p, hp, q, hq, ha, hs⟩,
    fun ⟨p, hp, q, hq, _, hx⟩ => ⟨⟨p, hp, hx.1⟩, ⟨q, hq, hx.2⟩⟩⟩

/-- Running intersection makes an actual cut's full overlap exactly its edge separator. -/
theorem cut_scope_eq_separator (hT : T.IsTree) (hRI : RunningIntersection T S)
    (e : T.Dart) :
    componentScope S (edgeLeft T e) ∩ componentScope S (edgeLeft T e)ᶜ =
      S e.fst ∩ S e.snd := by
  have he := edge_cut_components T hT e
  rw [boundary_eq_union_separators T S hRI]
  ext x
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨p, hp, q, hq, hpq, hx⟩
    rcases Sym2.eq_iff.mp (cut_crossing T e hp hq hpq) with h | h
    · simpa only [h.1, h.2] using hx
    · exact (he.2.1 (h.1 ▸ hp)).elim
  · intro hx
    exact ⟨e.fst, he.1, e.snd, he.2.1, e.adj, hx⟩

variable (Γ : (n : Node) → Set (Assignment Value (S n)))

/-- Equality of the complete projection images, not coordinatewise marginal checks. -/
def EdgeProjectionConsistency : Prop := ∀ p q, T.Adj p q →
  restrictAssignment Value (D := S p ∩ S q) Set.inter_subset_left '' Γ p =
    restrictAssignment Value (D := S p ∩ S q) Set.inter_subset_right '' Γ q

/-- The glue of two fixed complete cut records is unique; local relations may be empty. -/
theorem cut_records_glue_unique (hT : T.IsTree) (hRI : RunningIntersection T S)
    (e : T.Dart) (a : rawJoin Value S Γ (edgeLeft T e))
    (b : rawJoin Value S Γ (edgeLeft T e)ᶜ)
    (h : restrictAssignment Value (D := S e.fst ∩ S e.snd) (E := componentScope S (edgeLeft T e))
        (fun _ hx => ⟨e.fst, (cut_endpoints T hT e).1, hx.1⟩) a.val =
      restrictAssignment Value (D := S e.fst ∩ S e.snd) (E := componentScope S (edgeLeft T e)ᶜ)
        (fun _ hx => ⟨e.snd, (cut_endpoints T hT e).2, hx.2⟩) b.val) :
    ∃! j : rawJoin Value S Γ Set.univ,
      restrictRecord Value S Γ (edgeLeft T e) j = a ∧
      restrictRecord Value S Γ (edgeLeft T e)ᶜ j = b := by
  have hab : b ∈ compatibleCompletions Value S Γ (edgeLeft T e) a := by
    funext x
    have hx := (Set.ext_iff.mp (cut_scope_eq_separator T S hT hRI e) x.val).mp x.property
    exact (congrFun h ⟨x.val, hx⟩).symm
  obtain ⟨j, _, hja, hjb⟩ := compatible_union_restrictions Value S Γ _ a b hab
  refine ⟨j, ⟨hja, hjb⟩, ?_⟩
  intro k hk
  apply Subtype.ext
  funext x
  obtain ⟨n, _, hnx⟩ := x.property
  by_cases hn : n ∈ edgeLeft T e
  · exact congrFun (congrArg Subtype.val (hk.1.trans hja.symm)) ⟨x.val, n, hn, hnx⟩
  · exact congrFun (congrArg Subtype.val (hk.2.trans hjb.symm)) ⟨x.val, n, hn, hnx⟩

private theorem connected_region_in_cut {A : Set Node} (hA : (T.induce A).Connected)
    {p q : Node} (hp : p ∈ A) (hq : q ∉ A) (hpq : T.Adj p q) :
    A ⊆ edgeLeft T ⟨(p, q), hpq⟩ := by
  intro n hn
  obtain ⟨w⟩ := hA.preconnected ⟨p, hp⟩ ⟨n, hn⟩
  apply reachable_deleteEdges_iff_exists_walk.mpr
  refine ⟨w.map (Embedding.induce A).toHom, ?_⟩
  intro he
  have hqs := (w.map (Embedding.induce A).toHom).snd_mem_support_of_mem_edges he
  rw [Walk.support_map] at hqs
  obtain ⟨z, _, hz⟩ := List.mem_map.mp hqs
  change z.val = q at hz
  exact hq (hz ▸ z.property)

private theorem neighbor_overlap (hT : T.IsTree) (hRI : RunningIntersection T S)
    {A : Set Node} (hA : (T.induce A).Connected) {p q : Node}
    (hp : p ∈ A) (hq : q ∉ A) (hpq : T.Adj p q) :
    componentScope S A ∩ S q = S p ∩ S q := by
  have hsub := connected_region_in_cut T hA hp hq hpq
  have he := edge_cut_components T hT ⟨(p, q), hpq⟩
  have hc := cut_scope_eq_separator T S hT hRI ⟨(p, q), hpq⟩
  ext x
  constructor
  · rintro ⟨⟨n, hn, hx⟩, hxq⟩
    exact (Set.ext_iff.mp hc x).mp ⟨⟨n, hsub hn, hx⟩, ⟨q, he.2.1, hxq⟩⟩
  · intro hx
    exact ⟨⟨p, hp, hx.1⟩, hx.2⟩

/-- Add one outside neighbor while preserving every coordinate of the given partial record. -/
theorem extend_record_at_neighbor (hT : T.IsTree) (hRI : RunningIntersection T S)
    (hΓ : EdgeProjectionConsistency T Value S Γ) {A : Set Node}
    (hA : (T.induce A).Connected) {p q : Node} (hp : p ∈ A) (hq : q ∉ A)
    (hpq : T.Adj p q) (a : rawJoin Value S Γ A) :
    ∃ a' : rawJoin Value S Γ (A ∪ {q}),
      restrictAssignment Value (D := componentScope S A) (E := componentScope S (A ∪ {q}))
        (fun _ ⟨n, hn, hx⟩ => ⟨n, Or.inl hn, hx⟩) a'.val = a.val := by
  let ap : Assignment Value (S p) :=
    restrictAssignment Value (E := componentScope S A) (fun _ hx => ⟨p, hp, hx⟩) a.val
  have hap : ap ∈ Γ p := a.property p hp
  have him : restrictAssignment Value (D := S p ∩ S q) Set.inter_subset_left ap ∈
      restrictAssignment Value (D := S p ∩ S q) Set.inter_subset_right '' Γ q := by
    rw [← hΓ p q hpq]
    exact ⟨ap, hap, rfl⟩
  obtain ⟨b, hb, hba⟩ := him
  have overlap := neighbor_overlap T S hT hRI hA hp hq hpq
  let N := {n : Node // n ∈ A ∪ {q}}
  let S' : N → Set Var := fun n => S n.val
  let Γ' : (n : N) → Set (Assignment Value (S' n)) := fun n => Γ n.val
  let A' : Set N := Subtype.val ⁻¹' A
  have outside (n : N) : n ∈ A'ᶜ ↔ n.val = q := by
    constructor
    · intro hn
      exact (n.property.resolve_left hn)
    · intro hn
      change n.val ∉ A
      simpa only [hn] using hq
  have scopeA : componentScope S' A' = componentScope S A := by
    ext x
    exact ⟨fun ⟨n, hn, hx⟩ => ⟨n.val, hn, hx⟩,
      fun ⟨n, hn, hx⟩ => ⟨⟨n, Or.inl hn⟩, hn, hx⟩⟩
  have scopeB : componentScope S' A'ᶜ = S q := by
    ext x
    exact ⟨fun ⟨n, hn, hx⟩ => (outside n).mp hn ▸ hx,
      fun hx => ⟨⟨q, Or.inr rfl⟩, hq, hx⟩⟩
  have scopeU : componentScope S' Set.univ = componentScope S (A ∪ {q}) := by
    ext x
    exact ⟨fun ⟨n, _, hx⟩ => ⟨n.val, n.property, hx⟩,
      fun ⟨n, hn, hx⟩ => ⟨⟨n, hn⟩, Set.mem_univ _, hx⟩⟩
  let ar : rawJoin Value S' Γ' A' :=
    ⟨restrictAssignment Value scopeA.subset a.val, fun n hn => a.property n.val hn⟩
  let br : rawJoin Value S' Γ' A'ᶜ :=
    ⟨restrictAssignment Value scopeB.subset b, by
      intro n hn
      have hnq := (outside n).mp hn
      change restrictAssignment Value _ (restrictAssignment Value _ b) ∈ Γ n.val
      rcases n with ⟨n, hnN⟩
      change n = q at hnq
      subst n
      exact hb⟩
  have compatible : br ∈ compatibleCompletions Value S' Γ' A' ar := by
    funext x
    have hx : x.val ∈ componentScope S A ∩ S q :=
      ⟨scopeA ▸ x.property.1, scopeB ▸ x.property.2⟩
    have hxsep := overlap ▸ hx
    exact congrFun hba ⟨x.val, hxsep⟩
  obtain ⟨j, _, hjA, _⟩ := compatible_union_restrictions Value S' Γ' A' ar br compatible
  let a' : rawJoin Value S Γ (A ∪ {q}) :=
    ⟨restrictAssignment Value scopeU.symm.subset j.val,
      fun n hn => j.property ⟨n, hn⟩ (Set.mem_univ _)⟩
  refine ⟨a', ?_⟩
  funext x
  exact congrFun (congrArg Subtype.val hjA) ⟨x.val, scopeA.symm ▸ x.property⟩

private theorem finite_record_growth [Finite Node] (hT : T.IsTree)
    (hRI : RunningIntersection T S) (hΓ : EdgeProjectionConsistency T Value S Γ)
    (A : Set Node) (hA : (T.induce A).Connected) (a : rawJoin Value S Γ A) :
    ∃ j : rawJoin Value S Γ Set.univ,
      restrictRecord Value S Γ A j = a := by
  classical
  generalize hk : Aᶜ.ncard = k
  induction k using Nat.strong_induction_on generalizing A with
  | h k ih =>
    by_cases hAU : A = Set.univ
    · subst A
      exact ⟨a, rfl⟩
    · obtain ⟨q, hq⟩ := (Set.ne_univ_iff_exists_notMem A).mp hAU
      obtain ⟨p⟩ := hA.nonempty
      obtain ⟨w⟩ := hT.connected.preconnected p.val q
      obtain ⟨d, _, hdA, hdB⟩ := w.exists_boundary_dart A p.property hq
      have hnext : (T.induce (A ∪ {d.snd})).Connected :=
        connected_induce_union hA.preconnected Preconnected.of_subsingleton
          hdA (Set.mem_singleton _) d.adj
      obtain ⟨a', ha'⟩ := extend_record_at_neighbor T Value S Γ hT hRI hΓ
        hA hdA hdB d.adj a
      have hlt : (A ∪ {d.snd})ᶜ.ncard < k := by
        rw [← hk]
        apply Set.ncard_lt_ncard (ht := Set.toFinite _)
        exact ⟨fun n hn hnA => hn (Or.inl hnA),
          fun hback => hback hdB (Or.inr rfl)⟩
      obtain ⟨j, hj⟩ := ih _ hlt _ hnext a' rfl
      refine ⟨j, ?_⟩
      apply Subtype.ext
      funext x
      exact (congrFun (congrArg Subtype.val hj)
        ⟨x.val, by obtain ⟨n, hn, hx⟩ := x.property; exact ⟨n, Or.inl hn, hx⟩⟩).trans
          (congrFun ha' x)

/-- Every specified local row extends to the raw global join. This asserts existence only. -/
theorem local_row_extends_raw_join [Finite Node] (hT : T.IsTree)
    (hRI : RunningIntersection T S) (_hne : ∀ n, (Γ n).Nonempty)
    (hΓ : EdgeProjectionConsistency T Value S Γ)
    (r : Node) (a : Assignment Value (S r)) (ha : a ∈ Γ r) :
    ∃ j : rawJoin Value S Γ Set.univ,
      restrictAssignment Value (D := S r) (E := componentScope S Set.univ)
        (fun _ hx => ⟨r, Set.mem_univ _, hx⟩) j.val = a := by
  have scope : componentScope S {r} = S r := by
    ext x
    constructor
    · rintro ⟨n, hn, hx⟩
      exact Set.mem_singleton_iff.mp hn ▸ hx
    · intro hx
      exact ⟨r, rfl, hx⟩
  let ar : rawJoin Value S Γ {r} :=
    ⟨restrictAssignment Value scope.subset a, by
      intro n hn
      obtain rfl := Set.mem_singleton_iff.mp hn
      exact ha⟩
  let : Nonempty {n // n ∈ ({r} : Set Node)} := ⟨⟨r, Set.mem_singleton _⟩⟩
  have hconn : (T.induce {r}).Connected := ⟨Preconnected.of_subsingleton⟩
  obtain ⟨j, hj⟩ := finite_record_growth T Value S Γ hT hRI hΓ {r} hconn ar
  refine ⟨j, ?_⟩
  funext x
  exact congrFun (congrArg Subtype.val hj) ⟨x.val, scope.symm ▸ x.property⟩

end D5.S3.ConceptDynamics.Gluing.RunningIntersectionRecords
