/- GID: D5/S3/Combinatorics/Graph/Walks/HaggkvistPentagonHomomorphism
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Walks/HaggkvistPentagonHomomorphism
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Combinatorics/Graph/Walks/HaggkvistPentagonHomomorphism.surjective_of_not_two_color; premises=D5/S3/Combinatorics/Graph/Walks/HaggkvistPentagonHomomorphism.path_color_adj
   digest: Dense triangle-free graphs admit homomorphisms to the pentagon. -/

/-
admission_basis: escape-witness: HaggkvistDense.pentagon_hom
escape_witness: D5.S3.Combinatorics.Graph.Walks.HaggkvistPentagonHomomorphism.HaggkvistDense.pentagon_hom
Direct frozen dependencies:
  none
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/20094
HaggMaximal.exists_edge_of_dense: proof_shape: bind-only; escape_witness: none; consumers: HaggkvistDense.pentagon_hom; Direct frozen dependencies: none
HaggMaximal.common_neighbor_of_maximal: proof_shape: bind-only; escape_witness: none; consumers: HaggMaximal.common_neighbor_all; Direct frozen dependencies: none
HaggMaximal.common_neighbor_all: proof_shape: bind-only; escape_witness: none; consumers: HaggkvistDense.pentagon_hom; Direct frozen dependencies: none
HaggMaximal.maximal_completion: proof_shape: bind-only; escape_witness: none; consumers: HaggkvistDense.pentagon_hom; Direct frozen dependencies: none
HaggAttachment.edge_rotate: proof_shape: bind-only; escape_witness: none; consumers: HaggAttachment.twin_edge, HaggFullAttachment.attachment_with_neighbor; Direct frozen dependencies: none
HaggAttachment.edge_symm: proof_shape: bind-only; escape_witness: none; consumers: HaggAttachment.replace_pentagon, HaggAttachment.transfer_twin; Direct frozen dependencies: none
HaggAttachment.index_common: proof_shape: bind-only; escape_witness: none; consumers: HaggAttachment.transfer_twin, HaggFullAttachment.adjacency_of_twins; Direct frozen dependencies: none
HaggAttachment.twin_edge: proof_shape: content; escape_witness: HaggAttachment.twin_edge; consumers: HaggAttachment.transfer_twin; Direct frozen dependencies: none
HaggAttachment.base_twin: proof_shape: bind-only; escape_witness: none; consumers: HaggAttachment.old_base_twin, HaggFullAttachment.attachment_zero; Direct frozen dependencies: none
HaggAttachment.replace_pentagon: proof_shape: bind-only; escape_witness: none; consumers: HaggAttachment.transfer_twin, HaggFullAttachment.attachment_zero, HaggFullAttachment.every_vertex_twin; Direct frozen dependencies: none
HaggAttachment.old_base_twin: proof_shape: bind-only; escape_witness: none; consumers: HaggAttachment.transfer_twin; Direct frozen dependencies: none
HaggAttachment.transfer_twin: proof_shape: content; escape_witness: HaggAttachment.transfer_twin; consumers: HaggFullAttachment.attachment_zero, HaggFullAttachment.every_vertex_twin; Direct frozen dependencies: none
HaggFullAttachment.attachment_zero: proof_shape: content; escape_witness: HaggFullAttachment.attachment_zero; consumers: HaggFullAttachment.attachment_with_neighbor; Direct frozen dependencies: none
HaggFullAttachment.base_transition: proof_shape: bind-only; escape_witness: none; consumers: HaggFullAttachment.attachment_with_neighbor; Direct frozen dependencies: none
HaggFullAttachment.attachment_with_neighbor: proof_shape: content; escape_witness: HaggFullAttachment.attachment_with_neighbor; consumers: HaggFullAttachment.every_vertex_twin; Direct frozen dependencies: none
HaggFullAttachment.every_vertex_twin: proof_shape: content; escape_witness: HaggFullAttachment.every_vertex_twin; consumers: HaggFullAttachment.pentagon_partition; Direct frozen dependencies: none
HaggFullAttachment.adjacency_of_twins: proof_shape: bind-only; escape_witness: none; consumers: HaggFullAttachment.pentagon_partition; Direct frozen dependencies: none
HaggFullAttachment.pentagon_partition: proof_shape: content; escape_witness: HaggFullAttachment.pentagon_partition; consumers: HaggkvistDense.pentagon_hom; Direct frozen dependencies: none
HaggBipartiteAlternative.pentagon_of_missing_cross: proof_shape: content; escape_witness: HaggBipartiteAlternative.pentagon_of_missing_cross; consumers: HaggBipartiteAlternative.two_sides_of_no_pentagon; Direct frozen dependencies: none
HaggBipartiteAlternative.two_sides_of_no_pentagon: proof_shape: content; escape_witness: HaggBipartiteAlternative.two_sides_of_no_pentagon; consumers: HaggkvistDense.pentagon_hom; Direct frozen dependencies: none
HaggBipartiteAlternative.pentagon_map_of_two_sides: proof_shape: bind-only; escape_witness: none; consumers: HaggkvistDense.pentagon_hom; Direct frozen dependencies: none
PentagonImage.PathColor: proof_shape: bind-only; escape_witness: none; consumers: PentagonImage.path_color_adj, PentagonImage.two_color_of_missing; Direct frozen dependencies: none
PentagonImage.path_color_adj: proof_shape: bind-only; escape_witness: none; consumers: PentagonImage.two_color_of_missing; Direct frozen dependencies: none
PentagonImage.two_color_of_missing: proof_shape: bind-only; escape_witness: none; consumers: PentagonImage.surjective_of_not_two_color; Direct frozen dependencies: none
PentagonImage.surjective_of_not_two_color: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Combinatorics.Graph.ComponentPacking.AhanjidehEkimYildizZ.AEYLowerDense.no_small_dense, D5.S3.Combinatorics.Graph.ComponentPacking.AhanjidehEkimYildizZ.ExceptionalLower.no_order_59, D5.S3.Combinatorics.Graph.ComponentPacking.AhanjidehEkimYildizZ.ExceptionalLower.surjective; Direct frozen dependencies: none
HaggkvistDense.pentagon_hom: proof_shape: content; escape_witness: HaggkvistDense.pentagon_hom; consumers: D5.S3.Combinatorics.Graph.ComponentPacking.AhanjidehEkimYildizZ.AEYLowerDense.no_small_dense, D5.S3.Combinatorics.Graph.ComponentPacking.AhanjidehEkimYildizZ.ExceptionalLower.no_order_59; Direct frozen dependencies: none
-/

import D5.S3.Combinatorics.Graph.Walks.DenseTriangleFreeConfigurations
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.Hall.Basic
import Mathlib.Order.Max
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic

set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

namespace D5.S3.Combinatorics.Graph.Walks.HaggkvistPentagonHomomorphism
open D5.S3.Combinatorics.Graph.Walks.DenseTriangleFreeConfigurations
open HaggLocalConfigurations

namespace HaggMaximal
open Finset DenseDegreeCounting
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A strict positive degree threshold forces an edge. -/
private theorem exists_edge_of_dense (hd : 3 * Fintype.card V < 8 * G.minDegree) :
    ∃ a b, G.Adj a b := by
  all_goals
    classical
    by_contra hn
    push_neg at hn
    have he : G = ⊥ := by exact (SimpleGraph.eq_bot_iff_isIsolated G).mpr hn
    simp [he] at hd

/-- A maximal triangle-free graph has common neighbors for distinct missing pairs. -/
private theorem common_neighbor_of_maximal
    (hG : Maximal (fun H : SimpleGraph V => H.CliqueFree 3) G)
    (a b : V) (hne : a ≠ b) (hab : ¬ G.Adj a b) :
    ∃ r, G.Adj a r ∧ G.Adj b r := by
  all_goals
    obtain ⟨s, ha, hb, hca, hcb⟩ := SimpleGraph.exists_of_maximal_cliqueFree_not_adj
      (n := 2) hG hne hab
    have hs : s.card = 1 := by
      have hcard := hca.card_eq
      rw [Finset.card_insert_of_notMem ha] at hcard
      omega
    obtain ⟨r, hr⟩ := Finset.card_eq_one.mp hs
    subst s
    refine ⟨r, ?_, ?_⟩
    · have he := hca.isClique
      have he' : a ≠ r → G.Adj a r := by simpa only [Finset.coe_insert, Finset.coe_singleton, SimpleGraph.isClique_pair] using he
      exact he' (by simpa using ha)
    · have he := hcb.isClique
      have he' : b ≠ r → G.Adj b r := by simpa only [Finset.coe_insert, Finset.coe_singleton, SimpleGraph.isClique_pair] using he
      exact he' (by simpa using hb)

/-- Positive minimum degree includes identical pairs in the common-neighbor property. -/
private theorem common_neighbor_all
    (hG : Maximal (fun H : SimpleGraph V => H.CliqueFree 3) G)
    (hd : 0 < G.minDegree) :
    ∀ a b, ¬ G.Adj a b → ∃ r, G.Adj a r ∧ G.Adj b r := by
  all_goals
    intro a b hab
    by_cases he : a = b
    · subst b
      obtain ⟨r, har⟩ := (G.degree_pos_iff_exists_adj a).mp (hd.trans_le (G.minDegree_le_degree a))
      exact ⟨r, har, har⟩
    · exact common_neighbor_of_maximal G hG a b he hab

/-- Finite maximal completion preserves the strict density threshold. -/
private theorem maximal_completion (hG : G.CliqueFree 3)
    (hd : 3 * Fintype.card V < 8 * G.minDegree) :
    ∃ H : SimpleGraph V, G ≤ H ∧ H.CliqueFree 3 ∧
      (letI := fun a b => Classical.propDecidable (H.Adj a b); 3 * Fintype.card V < 8 * H.minDegree) ∧
      Maximal (fun K : SimpleGraph V => K.CliqueFree 3) H := by
  all_goals
    classical
    obtain ⟨H, hle, hm⟩ := @Finite.exists_le_maximal _ _ _ (fun H : SimpleGraph V => H.CliqueFree 3) G hG
    exact ⟨H, hle, hm.1, hd.trans_le (Nat.mul_le_mul_left 8 (SimpleGraph.minDegree_le_minDegree hle)), hm⟩

end HaggMaximal

namespace HaggAttachment
open HaggLocalConfigurations HaggFinitePatterns
variable {V : Type*} (G : SimpleGraph V)

/-- Rotation preserves the pentagon adjacency relation. -/
private theorem edge_rotate (i j k : Fin 5) : ((SimpleGraph.cycleGraph 5).comap (fun i : Fin 5 => 3 * i)).Adj (i + j) (i + k) ↔ ((SimpleGraph.cycleGraph 5).comap (fun i : Fin 5 => 3 * i)).Adj j k := by
  all_goals
    fin_cases i <;> fin_cases j <;> fin_cases k <;> decide

/-- The pentagon adjacency relation is symmetric. -/
private theorem edge_symm (i j : Fin 5) :
    ((SimpleGraph.cycleGraph 5).comap (fun i : Fin 5 => 3 * i)).Adj i j ↔
      ((SimpleGraph.cycleGraph 5).comap (fun i : Fin 5 => 3 * i)).Adj j i :=
  ((SimpleGraph.cycleGraph 5).comap (fun i : Fin 5 => 3 * i)).adj_comm i j

/-- Nonadjacent pentagon vertices have a common neighbor distinct from each endpoint. -/
private theorem index_common (i j : Fin 5) (h : ¬ ((SimpleGraph.cycleGraph 5).comap (fun i : Fin 5 => 3 * i)).Adj i j) :
    ∃ k, ((SimpleGraph.cycleGraph 5).comap (fun i : Fin 5 => 3 * i)).Adj i k ∧ ((SimpleGraph.cycleGraph 5).comap (fun i : Fin 5 => 3 * i)).Adj j k ∧ k ≠ i ∧ k ≠ j := by
  all_goals
    revert h
    fin_cases i <;> fin_cases j <;> decide

/-- The twin edge lemma transports to every pentagon edge. -/
private theorem twin_edge (hG : (∀ ⦃a b c : V⦄, G.Adj a b → G.Adj b c → ¬ G.Adj a c)) (hn : NoHex G)
    (hc : ∀ a b, ¬ G.Adj a b → ∃ r, G.Adj a r ∧ G.Adj b r)
    (hA : ¬ Nonempty (A3 →g G))
    (p : Fin 5 → V) (hp : Pentagon G p) (x y : V) (i j : Fin 5)
    (hx : Twin G p x i) (hy : Twin G p y j) (he : ((SimpleGraph.cycleGraph 5).comap (fun i : Fin 5 => 3 * i)).Adj i j) : G.Adj x y := by
  all_goals
    have hplus (i : Fin 5) (x y : V) (hx : Twin G p x i)
        (hy : Twin G p y (i + 2)) : G.Adj x y := by
      let q : Fin 5 → V := fun k => p (i + k)
      have hq : Pentagon G q := by
        intro a b hab
        exact hp _ _ ((edge_rotate i a b).mpr hab)
      have hx0 : Twin G q x 0 := by
        intro k
        simpa only [q, add_zero] using (hx (i + k)).trans (by simpa only [add_zero] using edge_rotate i 0 k)
      have hy2 : Twin G q y 2 := by
        intro k
        exact (hy (i + k)).trans (edge_rotate i 2 k)
      exact twin_edge_zero_two G hG hn hc hA q hq x y hx0 hy2
    rcases (pentagon_edge_iff _ _).mp he with rfl | rfl
    · exact hplus i x y hx hy
    · have hi : i + 3 + 2 = i := by exact add_eq_of_eq_add_neg rfl
      exact (hplus (i + 3) y x hy (by simpa only [hi] using hx)).symm

/-- Every base vertex is its own pentagon twin. -/
private theorem base_twin (hG : (∀ ⦃a b c : V⦄, G.Adj a b → G.Adj b c → ¬ G.Adj a c)) (p : Fin 5 → V) (hp : Pentagon G p) (i : Fin 5) :
    Twin G p (p i) i := by
  all_goals
    exact twin_of_two G hG p hp (p i) i (hp _ _ ((pentagon_edge_iff _ _).mpr (Or.inl rfl))) (hp _ _ ((pentagon_edge_iff _ _).mpr (Or.inr rfl)))

/-- Replacing a pentagon vertex by a twin preserves all pentagon edges. -/
private theorem replace_pentagon (p : Fin 5 → V) (hp : Pentagon G p) (i : Fin 5) (z : V)
    (hz : Twin G p z i) : Pentagon G (Function.update p i z) := by
  all_goals
    intro a b hab
    have habne : a ≠ b := by
      exact SimpleGraph.ne_of_adj _ hab
    by_cases ha : a = i
    · subst a
      have hb : b ≠ i := Ne.symm habne
      simpa [Function.update, hb] using (hz b).mpr hab
    · by_cases hb : b = i
      · subst b
        simpa [Function.update, ha] using ((hz a).mpr ((edge_symm a i).mp hab)).symm
      · simpa [Function.update, ha, hb] using hp a b hab

/-- The removed base vertex is a twin of its replacement in the replaced pentagon. -/
private theorem old_base_twin (hG : (∀ ⦃a b c : V⦄, G.Adj a b → G.Adj b c → ¬ G.Adj a c)) (p : Fin 5 → V) (hp : Pentagon G p)
    (i : Fin 5) (z : V) (hz : Twin G p z i) :
    Twin G (Function.update p i z) (p i) i := by
  all_goals
    have hself : ¬ G.Adj (p i) z := by
      have h1 := hp i (i + 2) ((pentagon_edge_iff _ _).mpr (Or.inl rfl))
      have h2 := (hz (i + 2)).mpr ((pentagon_edge_iff _ _).mpr (Or.inl rfl))
      exact hG h1 h2.symm
    intro k
    by_cases hk : k = i
    · subst k
      simp only [Function.update, if_pos rfl]
      have hi : ¬ ((SimpleGraph.cycleGraph 5).comap (fun i : Fin 5 => 3 * i)).Adj i i := by
        exact SimpleGraph.irrefl (SimpleGraph.comap (fun i : Fin 5 => 3 * i) (SimpleGraph.cycleGraph 5))
      exact iff_of_false hself hi
    · simpa [Function.update, hk] using base_twin G hG p hp i k

/-- Twin membership transfers back across replacement away from the replaced index. -/
private theorem transfer_twin (hG : (∀ ⦃a b c : V⦄, G.Adj a b → G.Adj b c → ¬ G.Adj a c)) (hn : NoHex G)
    (hc : ∀ a b, ¬ G.Adj a b → ∃ r, G.Adj a r ∧ G.Adj b r)
    (hA : ¬ Nonempty (A3 →g G))
    (p : Fin 5 → V) (hp : Pentagon G p) (i : Fin 5) (z x : V)
    (hz : Twin G p z i) (j : Fin 5) (hji : j ≠ i)
    (hx : Twin G (Function.update p i z) x j) : Twin G p x j := by
  all_goals
    intro k
    by_cases hk : k = i
    · subst k
      by_cases he : ((SimpleGraph.cycleGraph 5).comap (fun i : Fin 5 => 3 * i)).Adj j i
      · have hq := replace_pentagon G p hp i z hz
        have ho := old_base_twin G hG p hp i z hz
        exact iff_of_true (twin_edge G hG hn hc hA _ hq x (p i) j i hx ho he) he
      · obtain ⟨r, hir, hjr, hri, _⟩ := index_common i j ((edge_symm j i).not.mp he)
        have hxr : G.Adj x (p r) := by simpa [Function.update, hri] using (hx r).mpr hjr
        have hir' : G.Adj (p i) (p r) := hp i r hir
        exact iff_of_false (hG hxr hir'.symm) he
    · simpa [Function.update, hk] using hx k

end HaggAttachment

namespace HaggFullAttachment
open HaggAttachment HaggLocalConfigurations HaggFinitePatterns
variable {V : Type*} (G : SimpleGraph V)

/-- A pentagon neighbor and the preceding missing neighbor supply a twin. -/
private theorem attachment_zero (hG : (∀ ⦃a b c : V⦄, G.Adj a b → G.Adj b c → ¬ G.Adj a c)) (hn : NoHex G)
    (hc : ∀ a b, ¬ G.Adj a b → ∃ r, G.Adj a r ∧ G.Adj b r)
    (hA : ¬ Nonempty (A3 →g G))
    (p : Fin 5 → V) (hp : Pentagon G p) (x : V)
    (hx2 : G.Adj x (p 2)) (hx1 : ¬ G.Adj x (p 1)) : Twin G p x 0 := by
  all_goals
    obtain ⟨z, hxz, h1z⟩ := hc x (p 1) hx1
    have h02 := hp 0 2 (by decide)
    have h03 := hp 0 3 (by decide)
    have h13 := hp 1 3 (by decide)
    have h21 : ¬ G.Adj (p 2) (p 1) := by
      intro h
      have := (base_twin G hG p hp 2 1).mp h
      simp only [pentagon_edge_iff] at this
      norm_num at this
    have h := hn z x (p 2) (p 0) (p 3) (p 1)
      hxz.symm hx2 h02.symm h03 h13.symm h1z
    rcases h with hz0 | hx3 | h21'
    · have hz : Twin G p z 3 := twin_of_two G hG p hp z 3
        (by simpa using hz0) (by simpa using h1z.symm)
      have hq := replace_pentagon G p hp 3 z hz
      have hxq : Twin G (Function.update p 3 z) x 0 := twin_of_two G hG _ hq x 0
        (by simpa [Function.update] using hx2) (by simpa [Function.update] using hxz)
      exact transfer_twin G hG hn hc hA p hp 3 z x hz 0 (by decide) hxq
    · exact twin_of_two G hG p hp x 0 (by simpa using hx2) (by simpa using hx3)
    · exact False.elim (h21 h21')

/-- Any nonempty independent base-neighborhood has a cyclic transition. -/
private theorem base_transition (hG : (∀ ⦃a b c : V⦄, G.Adj a b → G.Adj b c → ¬ G.Adj a c)) (p : Fin 5 → V) (hp : Pentagon G p)
    (x : V) (hnb : ∃ j, G.Adj x (p j)) :
    ∃ i, G.Adj x (p (i + 2)) ∧ ¬ G.Adj x (p (i + 1)) := by
  all_goals
    classical
    by_contra hn
    push_neg at hn
    have h0 := hn 0; have h1 := hn 1; have h2 := hn 2
    have h3 := hn 3; have h4 := hn 4
    norm_num at h0 h1 h2 h3 h4
    obtain ⟨j, hj⟩ := hnb
    have h02 := hp 0 2 (by decide)
    have hn02 := hG (a := x) (b := p 0) (c := p 2)
    have hn20 := hG (a := x) (b := p 2) (c := p 0)
    fin_cases j <;> norm_num at hj
    all_goals tauto

/-- Every vertex with a base neighbor attaches as a pentagon twin. -/
private theorem attachment_with_neighbor (hG : (∀ ⦃a b c : V⦄, G.Adj a b → G.Adj b c → ¬ G.Adj a c)) (hn : NoHex G)
    (hc : ∀ a b, ¬ G.Adj a b → ∃ r, G.Adj a r ∧ G.Adj b r)
    (hA : ¬ Nonempty (A3 →g G))
    (p : Fin 5 → V) (hp : Pentagon G p) (x : V)
    (hnb : ∃ j, G.Adj x (p j)) : ∃ i, Twin G p x i := by
  all_goals
    obtain ⟨i, hi2, hi1⟩ := base_transition G hG p hp x hnb
    let q : Fin 5 → V := fun k => p (i + k)
    have hq : Pentagon G q := by
      intro a b hab
      exact hp _ _ ((edge_rotate i a b).mpr hab)
    have ht := attachment_zero G hG hn hc hA q hq x hi2 hi1
    refine ⟨i, ?_⟩
    intro k
    have hk : i + (k - i) = k := by exact add_sub_cancel i k
    have hh := ht (k - i)
    change G.Adj x (p (i + (k - i))) ↔ ((SimpleGraph.cycleGraph 5).comap (fun i : Fin 5 => 3 * i)).Adj 0 (k - i) at hh
    rw [hk] at hh
    exact hh.trans (by simpa only [add_zero, hk] using (edge_rotate i 0 (k - i)).symm)

/-- Every vertex attaches to a pentagon in a maximal graph with the two excluded obstructions. -/
private theorem every_vertex_twin (hG : (∀ ⦃a b c : V⦄, G.Adj a b → G.Adj b c → ¬ G.Adj a c)) (hn : NoHex G)
    (hc : ∀ a b, ¬ G.Adj a b → ∃ r, G.Adj a r ∧ G.Adj b r)
    (hA : ¬ Nonempty (A3 →g G))
    (p : Fin 5 → V) (hp : Pentagon G p) (x : V) : ∃ i, Twin G p x i := by
  all_goals
    classical
    by_cases hnb : ∃ j, G.Adj x (p j)
    · exact attachment_with_neighbor G hG hn hc hA p hp x hnb
    · have hx0 : ¬ G.Adj x (p 0) := fun h => hnb ⟨0, h⟩
      obtain ⟨z, hxz, h0z⟩ := hc x (p 0) hx0
      obtain ⟨i, hzi⟩ := attachment_with_neighbor G hG hn hc hA p hp z ⟨0, h0z.symm⟩
      have hq := replace_pentagon G p hp i z hzi
      obtain ⟨j, hxj⟩ := attachment_with_neighbor G hG hn hc hA _ hq x
        ⟨i, by simpa [Function.update] using hxz⟩
      have hji : j ≠ i := by
        intro hj
        subst j
        have hh := (hxj i).mp (by simpa [Function.update] using hxz)
        fin_cases i <;> simp only [pentagon_edge_iff] at hh
        all_goals norm_num at hh
      exact ⟨j, transfer_twin G hG hn hc hA p hp i z x hzi j hji hxj⟩

/-- Twin classes respect pentagon adjacency. -/
private theorem adjacency_of_twins (hG : (∀ ⦃a b c : V⦄, G.Adj a b → G.Adj b c → ¬ G.Adj a c)) (p : Fin 5 → V) (hp : Pentagon G p)
    (x y : V) (i j : Fin 5) (hx : Twin G p x i) (hy : Twin G p y j)
    (hxy : G.Adj x y) : ((SimpleGraph.cycleGraph 5).comap (fun i : Fin 5 => 3 * i)).Adj i j := by
  all_goals
    by_contra hij
    obtain ⟨k, hik, hjk, _, _⟩ := index_common i j hij
    exact hG ((hx k).mpr hik) ((hy k).mpr hjk).symm hxy

/-- Once a pentagon exists, every vertex maps to a pentagon class. -/
private theorem pentagon_partition (hG : (∀ ⦃a b c : V⦄, G.Adj a b → G.Adj b c → ¬ G.Adj a c)) (hn : NoHex G)
    (hc : ∀ a b, ¬ G.Adj a b → ∃ r, G.Adj a r ∧ G.Adj b r)
    (hA : ¬ Nonempty (A3 →g G))
    (p : Fin 5 → V) (hp : Pentagon G p) :
    ∃ f : V → Fin 5, ∀ ⦃x y⦄, G.Adj x y → ((SimpleGraph.cycleGraph 5).comap (fun i : Fin 5 => 3 * i)).Adj (f x) (f y) := by
  all_goals
    classical
    choose f hf using every_vertex_twin G hG hn hc hA p hp
    exact ⟨f, fun {_ _} h => adjacency_of_twins G hG p hp _ _ _ _ (hf _) (hf _) h⟩

end HaggFullAttachment

namespace HaggBipartiteAlternative
open HaggLocalConfigurations
variable {V : Type*} (G : SimpleGraph V)

/-- A missing edge between opposite edge-neighbor classes creates a pentagon. -/
private theorem pentagon_of_missing_cross
    (hc : ∀ a b, ¬ G.Adj a b → ∃ r, G.Adj a r ∧ G.Adj b r)
    (a b x y : V) (hab : G.Adj a b) (hbx : G.Adj b x) (hay : G.Adj a y)
    (hxy : ¬ G.Adj x y) : ∃ p : Fin 5 → V, Pentagon G p := by
  all_goals
    obtain ⟨r, hxr, hyr⟩ := hc x y hxy
    refine ⟨![a,r,b,y,x], ?_⟩
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp only [pentagon_edge_iff] at hij
    all_goals norm_num at hij
    all_goals norm_num
    all_goals first | assumption | exact hab.symm | exact hbx.symm | exact hay.symm |
      exact hxr.symm | exact hyr.symm

/-- With no pentagon, a maximal triangle-free graph with an edge has two independent sides. -/
private theorem two_sides_of_no_pentagon (hG : (∀ ⦃a b c : V⦄, G.Adj a b → G.Adj b c → ¬ G.Adj a c))
    (hc : ∀ a b, ¬ G.Adj a b → ∃ r, G.Adj a r ∧ G.Adj b r)
    (hn : ¬ ∃ p : Fin 5 → V, Pentagon G p)
    (a b : V) (hab : G.Adj a b) :
    ∃ f : V → Fin 2, ∀ ⦃x y⦄, G.Adj x y → f x ≠ f y := by
  all_goals
    classical
    have cross {x y : V} (hbx : G.Adj b x) (hay : G.Adj a y) : G.Adj x y := by
      by_contra hnxy
      exact hn (pentagon_of_missing_cross G hc a b x y hab hbx hay hnxy)
    have cover (x : V) : G.Adj a x ∨ G.Adj b x := by
      by_contra hx
      push_neg at hx
      obtain ⟨z, hxz, haz⟩ := hc x a (fun h => hx.1 h.symm)
      obtain ⟨r, hxr, hbr⟩ := hc x b (fun h => hx.2 h.symm)
      exact hG hxr (cross hbr haz) hxz
    let f : V → Fin 2 := fun x => if G.Adj a x then 0 else 1
    refine ⟨f, ?_⟩
    intro x y hxy hEq
    by_cases hx : G.Adj a x
    · have hy : G.Adj a y := by
        by_contra hy
        simp [f, hx, hy] at hEq
      exact hG hx hxy hy
    · have hbx := (cover x).resolve_left hx
      have hy : ¬ G.Adj a y := by
        intro hy
        simp [f, hx, hy] at hEq
      have hby := (cover y).resolve_left hy
      exact hG hbx hxy hby

/-- A bipartition also supplies a pentagon homomorphism. -/
private theorem pentagon_map_of_two_sides
    (f : V → Fin 2) (hf : ∀ ⦃x y⦄, G.Adj x y → f x ≠ f y) :
    ∃ g : V → Fin 5, ∀ ⦃x y⦄, G.Adj x y → ((SimpleGraph.cycleGraph 5).comap (fun i : Fin 5 => 3 * i)).Adj (g x) (g y) := by
  all_goals
    let g : V → Fin 5 := fun x => if f x = 0 then 0 else 2
    refine ⟨g, ?_⟩
    intro x y hxy
    have hne := hf hxy
    by_cases hx0 : f x = 0 <;> by_cases hy0 : f y = 0
    · exact False.elim (hne (hx0.trans hy0.symm))
    · simp only [g, if_pos hx0, if_neg hy0]
      decide
    · simp only [g, if_neg hx0, if_pos hy0]
      decide
    · have hx1 : f x = 1 := by exact Fin.eq_one_of_ne_zero (f x) hx0
      have hy1 : f y = 1 := by exact Fin.eq_one_of_ne_zero (f y) hy0
      exact False.elim (hne (hx1.trans hy1.symm))

end HaggBipartiteAlternative

namespace PentagonImage
open HaggLocalConfigurations
variable {V : Type*} (G : SimpleGraph V)



private def PathColor (missing k : Fin 5) : Fin 2 :=
  if k = missing + 1 ∨ k = missing + 2 then 0 else 1

/-- Removing one pentagon class leaves a path, which has the indicated two-coloring. -/
private theorem path_color_adj (missing i j : Fin 5) (hi : i ≠ missing) (hj : j ≠ missing)
    (hij : ((SimpleGraph.cycleGraph 5).comap (fun i : Fin 5 => 3 * i)).Adj i j) : PathColor missing i ≠ PathColor missing j := by
  revert hi hj hij
  fin_cases missing <;> fin_cases i <;> fin_cases j <;> decide

/-- A pentagon map that omits a class induces a bipartition. -/
private theorem two_color_of_missing (f : V → Fin 5)
    (hf : ∀ ⦃x y⦄, G.Adj x y → ((SimpleGraph.cycleGraph 5).comap (fun i : Fin 5 => 3 * i)).Adj (f x) (f y))
    (missing : Fin 5) (hm : ∀ x, f x ≠ missing) :
    ∃ g : V → Fin 2, ∀ ⦃x y⦄, G.Adj x y → g x ≠ g y := by
  exact ⟨fun x => PathColor missing (f x), fun {_ _} h => path_color_adj _ _ _ (hm _) (hm _) (hf h)⟩

/-- A nonbipartite graph's pentagon map uses every class. -/
theorem surjective_of_not_two_color (f : V → Fin 5)
    (hf : ∀ ⦃x y⦄, G.Adj x y → ((SimpleGraph.cycleGraph 5).comap (fun i : Fin 5 => 3 * i)).Adj (f x) (f y))
    (hn : ¬ ∃ g : V → Fin 2, ∀ ⦃x y⦄, G.Adj x y → g x ≠ g y) :
    Function.Surjective f := by
  classical
  intro i
  by_contra hi
  push_neg at hi
  exact hn (two_color_of_missing G f hf i hi)

end PentagonImage


namespace HaggkvistDense
open HaggLocalConfigurations
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Every finite triangle-free graph above the three-eighths threshold maps to a pentagon. -/
theorem pentagon_hom (hG : G.CliqueFree 3)
    (hd : 3 * Fintype.card V < 8 * G.minDegree) :
    ∃ f : V → Fin 5, ∀ ⦃x y⦄, G.Adj x y → ((SimpleGraph.cycleGraph 5).comap (fun i : Fin 5 => 3 * i)).Adj (f x) (f y) := by
  all_goals
    classical
    obtain ⟨H, hle, hH, hdH, hm⟩ := HaggMaximal.maximal_completion G hG hd
    have htri := HaggForbidden.triangle_free_of_clique_free H hH
    have hcom := HaggMaximal.common_neighbor_all H hm (by omega)
    have hhex := HaggHexagon.no_hexagon H htri (HaggForbidden.d2 H hdH)
      (HaggForbidden.d3 H hdH) hcom (HaggForbidden.no_myc H htri hdH)
    have hexists : ∃ f : V → Fin 5, ∀ ⦃x y⦄, H.Adj x y → ((SimpleGraph.cycleGraph 5).comap (fun i : Fin 5 => 3 * i)).Adj (f x) (f y) := by
      by_cases hp : ∃ p : Fin 5 → V, Pentagon H p
      · obtain ⟨p, hp⟩ := hp
        exact HaggFullAttachment.pentagon_partition H htri hhex hcom
          (HaggForbidden.no_a3 H htri hdH) p hp
      · obtain ⟨a, b, hab⟩ := HaggMaximal.exists_edge_of_dense H hdH
        obtain ⟨f, hf⟩ := HaggBipartiteAlternative.two_sides_of_no_pentagon H htri hcom hp a b hab
        exact HaggBipartiteAlternative.pentagon_map_of_two_sides H f hf
    obtain ⟨f, hf⟩ := hexists
    exact ⟨f, fun {_ _} h => hf (hle h)⟩


end HaggkvistDense

end D5.S3.Combinatorics.Graph.Walks.HaggkvistPentagonHomomorphism
