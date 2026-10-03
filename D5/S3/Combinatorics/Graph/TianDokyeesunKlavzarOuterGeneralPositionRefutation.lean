/- GID: D5/S3/Combinatorics/Graph/TianDokyeesunKlavzarOuterGeneralPositionRefutation
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/TianDokyeesunKlavzarOuterGeneralPositionRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Metric]
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/Graph/TianDokyeesunKlavzarOuterGeneralPositionRefutation.claim; result=D5/S3/Combinatorics/Graph/TianDokyeesunKlavzarOuterGeneralPositionRefutation.result; claim=D5/S3/Combinatorics/Graph/TianDokyeesunKlavzarOuterGeneralPositionRefutation.claim
   digest: A 19-vertex graph refutes the outer general position vertex-removal bound. -/

/-
proof_shape: result: content
escape_witness: result (local walk construction and finite graph certificates)
admission_basis: open-problem-resolution (arXiv:2510.01294v2, Conjecture 3.4; issue #12543)
Direct frozen dependencies: none (pinned Mathlib only)
-/

import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 10000

namespace D5.S3.Combinatorics.Graph.TianDokyeesunKlavzarOuterGeneralPositionRefutation
open SimpleGraph

/-- Actual vertex deletion, retaining precisely the other vertices and induced edges. -/
def vertexDelete {V : Type} (Q : SimpleGraph V) (x : V) :
    SimpleGraph {v : V | v ≠ x} := Q.induce {v | v ≠ x}

/-- Deletion does not increase the number of connected components.
The empty graph has zero components, so the vertex of K1 is non-cut. -/
def NonCut {V : Type} (Q : SimpleGraph V) (x : V) : Prop :=
  Nat.card (vertexDelete Q x).ConnectedComponent ≤ Nat.card Q.ConnectedComponent

/-- Every shortest path with a selected first endpoint has no selected internal vertex.
Undirected reversal accounts for either endpoint being selected. -/
def OuterPosition {V : Type} (Q : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ u ∈ S, ∀ v, ∀ p : Q.Walk u v, p.IsPath → p.length = Q.dist u v →
    ∀ w ∈ S, w ≠ u → w ≠ v → w ∉ p.support

/-- Maximum cardinality among all outer general position sets, including the empty set. -/
noncomputable def outerNumber {V : Type} [Fintype V] [DecidableEq V]
    (Q : SimpleGraph V) : ℕ := by
  classical
  exact ((Finset.univ : Finset (Finset V)).filter (OuterPosition Q)).sup Finset.card

/-- The full finite simple connected graph claim of Conjecture 3.4. -/
noncomputable def claim : Prop := by
  classical
  exact ∀ (V : Type) [Fintype V] [DecidableEq V] (Q : SimpleGraph V),
    Q.Connected → ∀ x : V, NonCut Q x →
      outerNumber (vertexDelete Q x) ≤ outerNumber Q + Q.degree x

set_option maxHeartbeats 8000000 in
-- Finite distance and color-obstruction certificates are checked inside this proof.
/-- Conjecture 3.4 fails on a connected graph with a non-cut vertex of degree two. -/
theorem result : ¬ claim := by
  have certified_walk {V : Type} (Q : SimpleGraph V) (d : V → V → ℕ)
      (hz : ∀ u, d u u = 0)
      (hs : ∀ u v, u ≠ v → ∃ w, Q.Adj u w ∧ d w v + 1 = d u v)
      (u v : V) : ∃ p : Q.Walk u v, p.length = d u v := by
    have go : ∀ n, ∀ u v, d u v = n → ∃ p : Q.Walk u v, p.length = n := by
      intro n
      induction n using Nat.strong_induction_on with
      | h n ih =>
        intro u v huv
        by_cases he : u = v
        · subst v
          exact ⟨.nil, by simpa [hz] using huv⟩
        · obtain ⟨w, haw, hw⟩ := hs u v he
          have hlt : d w v < n := by omega
          obtain ⟨p, hp⟩ := ih (d w v) hlt w v rfl
          exact ⟨.cons haw p, by simp [hp]; omega⟩
    exact go (d u v) u v rfl

  have certified_distance {V : Type} (Q : SimpleGraph V) (d : V → V → ℕ)
      (hz : ∀ u, d u u = 0)
      (hs : ∀ u v, u ≠ v → ∃ w, Q.Adj u w ∧ d w v + 1 = d u v)
      (hl : ∀ u w v, Q.Adj u w → d u v ≤ d w v + 1)
      (u v : V) : Q.dist u v = d u v := by
    have lower : ∀ {a b}, (p : Q.Walk a b) → d a b ≤ p.length := by
      intro a b p
      induction p with
      | nil => simp [hz]
      | @cons a w b haw p ih =>
        simpa only [Walk.length_cons] using (hl a w b haw).trans (Nat.add_le_add_right ih 1)
    obtain ⟨p, hp⟩ := certified_walk Q d hz hs u v
    apply le_antisymm
    · simpa [hp] using Q.dist_le p
    · obtain ⟨q, hq⟩ := p.reachable.exists_walk_length_eq_dist
      simpa [hq] using lower q
  let graph (n : ℕ) (edges : List (ℕ × ℕ)) : SimpleGraph (Fin n) := {
    Adj u v := u ≠ v ∧ ((u.val,v.val) ∈ edges ∨ (v.val,u.val) ∈ edges)
    symm := ⟨by intro u v h; exact ⟨h.1.symm,h.2.elim Or.inr Or.inl⟩⟩
    loopless := ⟨by intro u h; exact h.1 rfl⟩
  }
  let (n : ℕ) (es : List (ℕ × ℕ)) : DecidableRel (graph n es).Adj :=
    fun u v => inferInstanceAs (Decidable (u ≠ v ∧ ((u.val,v.val) ∈ es ∨ (v.val,u.val) ∈ es)))

  let edgesH : List (ℕ × ℕ) := [
    (0, 8), (0, 17), (1, 8), (1, 17), (2, 8), (2, 17), (3, 8), (3, 17),
    (4, 12), (4, 13), (5, 12), (5, 13), (6, 12), (6, 13), (7, 12), (7, 13),
    (8, 9), (9, 10), (10, 11), (11, 12), (13, 14), (14, 15), (15, 16), (16, 17)]
  let edgesG : List (ℕ × ℕ) := edgesH ++ [(8,18),(13,18)]
  let H := graph 18 edgesH
  let G := graph 19 edgesG
  let matrixH : Array (Array ℕ) := #[#[0,2,2,2,6,6,6,6,1,2,3,4,5,5,4,3,2,1],
  #[2,0,2,2,6,6,6,6,1,2,3,4,5,5,4,3,2,1],
  #[2,2,0,2,6,6,6,6,1,2,3,4,5,5,4,3,2,1],
  #[2,2,2,0,6,6,6,6,1,2,3,4,5,5,4,3,2,1],
  #[6,6,6,6,0,2,2,2,5,4,3,2,1,1,2,3,4,5],
  #[6,6,6,6,2,0,2,2,5,4,3,2,1,1,2,3,4,5],
  #[6,6,6,6,2,2,0,2,5,4,3,2,1,1,2,3,4,5],
  #[6,6,6,6,2,2,2,0,5,4,3,2,1,1,2,3,4,5],
  #[1,1,1,1,5,5,5,5,0,1,2,3,4,6,5,4,3,2],
  #[2,2,2,2,4,4,4,4,1,0,1,2,3,5,6,5,4,3],
  #[3,3,3,3,3,3,3,3,2,1,0,1,2,4,5,6,5,4],
  #[4,4,4,4,2,2,2,2,3,2,1,0,1,3,4,5,6,5],
  #[5,5,5,5,1,1,1,1,4,3,2,1,0,2,3,4,5,6],
  #[5,5,5,5,1,1,1,1,6,5,4,3,2,0,1,2,3,4],
  #[4,4,4,4,2,2,2,2,5,6,5,4,3,1,0,1,2,3],
  #[3,3,3,3,3,3,3,3,4,5,6,5,4,2,1,0,1,2],
  #[2,2,2,2,4,4,4,4,3,4,5,6,5,3,2,1,0,1],
  #[1,1,1,1,5,5,5,5,2,3,4,5,6,4,3,2,1,0]]
  let matrixG : Array (Array ℕ) := #[#[0,2,2,2,4,4,4,4,1,2,3,4,5,3,4,3,2,1,2],
  #[2,0,2,2,4,4,4,4,1,2,3,4,5,3,4,3,2,1,2],
  #[2,2,0,2,4,4,4,4,1,2,3,4,5,3,4,3,2,1,2],
  #[2,2,2,0,4,4,4,4,1,2,3,4,5,3,4,3,2,1,2],
  #[4,4,4,4,0,2,2,2,3,4,3,2,1,1,2,3,4,5,2],
  #[4,4,4,4,2,0,2,2,3,4,3,2,1,1,2,3,4,5,2],
  #[4,4,4,4,2,2,0,2,3,4,3,2,1,1,2,3,4,5,2],
  #[4,4,4,4,2,2,2,0,3,4,3,2,1,1,2,3,4,5,2],
  #[1,1,1,1,3,3,3,3,0,1,2,3,4,2,3,4,3,2,1],
  #[2,2,2,2,4,4,4,4,1,0,1,2,3,3,4,5,4,3,2],
  #[3,3,3,3,3,3,3,3,2,1,0,1,2,4,5,6,5,4,3],
  #[4,4,4,4,2,2,2,2,3,2,1,0,1,3,4,5,6,5,4],
  #[5,5,5,5,1,1,1,1,4,3,2,1,0,2,3,4,5,6,3],
  #[3,3,3,3,1,1,1,1,2,3,4,3,2,0,1,2,3,4,1],
  #[4,4,4,4,2,2,2,2,3,4,5,4,3,1,0,1,2,3,2],
  #[3,3,3,3,3,3,3,3,4,5,6,5,4,2,1,0,1,2,3],
  #[2,2,2,2,4,4,4,4,3,4,5,6,5,3,2,1,0,1,4],
  #[1,1,1,1,5,5,5,5,2,3,4,5,6,4,3,2,1,0,3],
  #[2,2,2,2,2,2,2,2,1,2,3,4,3,1,2,3,4,3,0]]
  let dH (u v : Fin 18) := (matrixH[u.val]!).getD v.val 0
  let dG (u v : Fin 19) := (matrixG[u.val]!).getD v.val 0

  have certH : (∀ u, dH u u = 0) ∧
      (∀ u v, u ≠ v → ∃ w, H.Adj u w ∧ dH w v + 1 = dH u v) ∧
      (∀ u w v, H.Adj u w → dH u v ≤ dH w v + 1) := by decide

  have certG : (∀ u, dG u u = 0) ∧
      (∀ u v, u ≠ v → ∃ w, G.Adj u w ∧ dG w v + 1 = dG u v) ∧
      (∀ u w v, G.Adj u w → dG u v ≤ dG w v + 1) := by decide

  have distH (u v : Fin 18) : H.dist u v = dH u v :=
    certified_distance H dH certH.1 certH.2.1 certH.2.2 u v

  have distG (u v : Fin 19) : G.dist u v = dG u v :=
    certified_distance G dG certG.1 certG.2.1 certG.2.2 u v
  let metricOuter {V : Type} (Q : SimpleGraph V) (S : Finset V) : Prop :=
    ∀ u ∈ S, ∀ w ∈ S, u ≠ w → ∀ v, u ≠ v → w ≠ v →
      Q.dist u v ≠ Q.dist u w + Q.dist w v

  let selectedH : Finset (Fin 18) := {0,1,2,3,4,5,6,7}
  have selectedH_outer : metricOuter H selectedH := by
    simp only [metricOuter, distH]
    decide
  let color (u : Fin 19) : Fin 5 :=
    ⟨(#[0,1,2,3,0,1,2,3,0,4,0,0,1,0,4,1,1,0,2] : Array ℕ)[u.val]!, by
      fin_cases u <;> decide⟩

  have color_obstruction : ∀ u v : Fin 19, u ≠ v → color u = color v →
      ∃ w, u ≠ w ∧ v ≠ w ∧
        (dG u w = dG u v + dG v w ∨ dG v w = dG v u + dG u w) := by decide

  have outer_G_upper (S : Finset (Fin 19)) (hS : metricOuter G S) : S.card ≤ 5 := by
    have hi : (S : Set (Fin 19)).InjOn color := by
      intro u hu v hv he
      by_contra hne
      obtain ⟨w, huw, hvw, hbad⟩ := color_obstruction u v hne he
      rcases hbad with hbad | hbad
      · exact hS u hu v hv hne w huw hvw (by simpa only [distG] using hbad)
      · exact hS v hv u hu (Ne.symm hne) w hvw huw (by simpa only [distG] using hbad)
    have hc := Finset.card_le_card_of_injOn color
      (show Set.MapsTo color (S : Set (Fin 19)) (Finset.univ : Finset (Fin 5)) from by
        intro u hu; simp) hi
    simpa using hc
  have outer_bridge {V : Type} [DecidableEq V] (Q : SimpleGraph V) (hc : Q.Connected)
      (S : Finset V) :
      metricOuter Q S ↔ OuterPosition Q S := by
    constructor
    · intro ho u hu v p _ hp w hw hwu hwv hmem
      have hleft := Q.length_eq_dist_of_subwalk hp (p.isSubwalk_takeUntil hmem)
      have hright := Q.length_eq_dist_of_subwalk hp (p.isSubwalk_dropUntil hmem)
      have hsplit : p.length = (p.takeUntil w hmem).length + (p.dropUntil w hmem).length := by
        rw [← Walk.length_append, p.take_spec hmem]
      apply ho u hu w hw hwu.symm v
      · intro huv
        subst v
        have hzero := Q.dist_self (v := u)
        have hsum := hsplit
        rw [hp, hzero, hleft, hright] at hsum
        have hd := (hc u w).dist_eq_zero_iff
        exact hwu (hd.mp (by omega)).symm
      · exact hwv
      · rw [← hp, hsplit, hleft, hright]
    · intro hp u hu w hw huw v huv hwv he
      obtain ⟨p, hl⟩ := (hc u w).exists_walk_length_eq_dist
      obtain ⟨q, hr⟩ := (hc w v).exists_walk_length_eq_dist
      have hlen : (p.append q).length = Q.dist u v := by
        rw [Walk.length_append, hl, hr, ← he]
      have hm : w ∈ (p.append q).support := by
        exact (Walk.mem_support_append_iff p q).mpr (Or.inl p.end_mem_support)
      exact hp u hu v (p.append q) ((p.append q).isPath_of_length_eq_dist hlen)
        hlen w hw huw.symm hwv hm
  let embed (u : Fin 18) : Fin 19 := ⟨u.val, by omega⟩
  have induced_deletion : ∀ u v, H.Adj u v ↔ G.Adj (embed u) (embed v) := by decide

  have embed_covers_deletion (w : Fin 19) (hw : w ≠ 18) : ∃ u, embed u = w := by
    have hlt : w.val < 18 := by
      have hn : w.val ≠ 18 := by intro he; apply hw; exact Fin.ext he
      omega
    exact ⟨⟨w.val,hlt⟩, Fin.ext rfl⟩

  have H_connected : H.Connected := by
    apply SimpleGraph.Connected.mk
    intro u v
    obtain ⟨p,hp⟩ := certified_walk H dH certH.1 certH.2.1 u v
    exact p.reachable

  have G_connected : G.Connected := by
    apply SimpleGraph.Connected.mk
    intro u v
    obtain ⟨p,hp⟩ := certified_walk G dG certG.1 certG.2.1 u v
    exact p.reachable

  let deletionHom : H →g G.induce {v : Fin 19 | v ≠ 18} := {
    toFun u := ⟨embed u, by
      intro he
      have he' := congrArg Fin.val he
      have hu := u.isLt
      simp only [embed] at he'
      omega⟩
    map_rel' := by
      intro u v huv
      exact (induced_deletion u v).mp huv }
  have deletionHom_surjective : Function.Surjective deletionHom := by
    intro v
    obtain ⟨u,hu⟩ := embed_covers_deletion v.val v.property
    exact ⟨u, Subtype.ext hu⟩

  have actual_deletion_connected : (G.induce {v : Fin 19 | v ≠ 18}).Connected :=
    H_connected.map deletionHom deletionHom_surjective
  have neighbors_x : (G.neighborFinset (18 : Fin 19)).card = 2 := by decide
  classical
  have upper : outerNumber G ≤ 5 := by
    apply Finset.sup_le
    intro S hS
    exact outer_G_upper S ((outer_bridge G G_connected S).mpr (Finset.mem_filter.mp hS).2)
  have lower : 8 ≤ outerNumber (G.induce {v : Fin 19 | v ≠ 18}) := by
    let D := G.induce {v : Fin 19 | v ≠ 18}
    have hinj : Function.Injective deletionHom := by
      intro u v he
      apply Fin.ext
      exact congrArg (fun t => t.val.val) he
    let e : H ≃g D := {
      toEquiv := Equiv.ofBijective deletionHom ⟨hinj, deletionHom_surjective⟩
      map_rel_iff' := by intro u v; exact (induced_deletion u v).symm }
    have hd : ∀ u v, D.dist (e u) (e v) = H.dist u v := by
      intro u v
      apply le_antisymm
      · obtain ⟨p, hp⟩ := (H_connected u v).exists_walk_length_eq_dist
        have hle := D.dist_le (p.map e.toHom)
        change D.dist (e u) (e v) ≤ (p.map e.toHom).length at hle
        simpa only [Walk.length_map, hp] using hle
      · obtain ⟨p, hp⟩ := (actual_deletion_connected (e u) (e v)).exists_walk_length_eq_dist
        have hle := H.dist_le (p.map e.symm.toHom)
        change H.dist (e.symm (e u)) (e.symm (e v)) ≤ (p.map e.symm.toHom).length at hle
        simpa only [Walk.length_map, e.symm_apply_apply, hp] using hle
    let T := selectedH.map e.toEmbedding.toEmbedding
    have hout : metricOuter D T := by
      intro u hu w hw huw v huv hwv
      obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hu
      obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp hw
      obtain ⟨c, rfl⟩ := e.surjective v
      have hab : a ≠ b := by intro he; exact huw (congrArg e he)
      have hac : a ≠ c := by intro he; exact huv (congrArg e he)
      have hbc : b ≠ c := by intro he; exact hwv (congrArg e he)
      change D.dist (e a) (e c) ≠ D.dist (e a) (e b) + D.dist (e b) (e c)
      simpa only [hd] using selectedH_outer a ha b hb hab c hac hbc
    have hmem : T ∈ ((Finset.univ : Finset (Finset {v : Fin 19 | v ≠ 18})).filter
        (OuterPosition D)) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact (outer_bridge D actual_deletion_connected T).mp hout
    have hc : T.card = 8 := by
      rw [Finset.card_map]
      decide
    have hm := Finset.le_sup (f := Finset.card) hmem
    change T.card ≤ outerNumber D at hm
    rw [hc] at hm
    exact hm
  have noncut : NonCut G (18 : Fin 19) := by
    let : Subsingleton G.ConnectedComponent :=
      G_connected.preconnected.subsingleton_connectedComponent
    let : Subsingleton (G.induce {v : Fin 19 | v ≠ 18}).ConnectedComponent :=
      actual_deletion_connected.preconnected.subsingleton_connectedComponent
    let : Nonempty (G.induce {v : Fin 19 | v ≠ 18}).ConnectedComponent :=
      ⟨(G.induce {v : Fin 19 | v ≠ 18}).connectedComponentMk (deletionHom 0)⟩
    change Nat.card (G.induce {v : Fin 19 | v ≠ 18}).ConnectedComponent ≤
      Nat.card G.ConnectedComponent
    simp only [Nat.card_unique]
    exact le_rfl
  have degree_x : G.degree (18 : Fin 19) = 2 := by
    exact neighbors_x
  intro hc
  have bound := hc (Fin 19) G G_connected 18 noncut
  have degree_card : Nat.card (G.neighborSet (18 : Fin 19)) = 2 := by
    simpa only [← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] using degree_x
  have degree_normalize (ft : Fintype (G.neighborSet (18 : Fin 19))) :
      @SimpleGraph.degree _ G 18 ft = Nat.card (G.neighborSet (18 : Fin 19)) :=
    (@SimpleGraph.card_neighborSet_eq_degree _ G 18 ft).symm.trans
      (@Nat.card_eq_fintype_card _ ft).symm
  have bound' : outerNumber (G.induce {v : Fin 19 | v ≠ 18}) ≤ outerNumber G +
      Nat.card (G.neighborSet (18 : Fin 19)) :=
    bound.trans_eq (congrArg (fun t : ℕ => outerNumber G + t) (degree_normalize _))
  omega

#print axioms result

end D5.S3.Combinatorics.Graph.TianDokyeesunKlavzarOuterGeneralPositionRefutation
