/- GID: D5/S3/Combinatorics/Graph/MutualVisibility/Andrasfai
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/MutualVisibility/Andrasfai
   mirror-E: none(waiver:no-computational-evidence)
   anchors: []
   utility: none
   digest: Original-host mutual visibility in the Andrasfai Cayley graphs is characterized by explicit cyclic obstructions. -/

import D5.S3.Combinatorics.Graph.MutualVisibility.Model
import Mathlib.Data.ZMod.Basic

/-! The parameter `m` denotes the original graph index minus one: the host has
`3*m+2` vertices and is exactly the original graph G_(m+1). There is no graph G_0.
The obstruction theorem concerns all labelled subsets and the existing
original-host shortest-walk predicate. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.MutualVisibility.Andrasfai

open SimpleGraph

abbrev Vertex (m : ℕ) := ZMod (3 * m + 2)

private instance modulus_neZero (m : ℕ) : NeZero (3 * m + 2) := ⟨by omega⟩

/-- The connection set is precisely the representatives congruent to one modulo three. -/
def host (m : ℕ) : SimpleGraph (Vertex m) where
  Adj u v := (v - u).val % 3 = 1
  symm := ⟨by
    intro u v h
    have hn : v - u ≠ 0 := by intro hz; simp [hz] at h
    have hb := ZMod.val_lt (v - u)
    have hp := (ZMod.val_pos).mpr hn
    rw [show u - v = -(v - u) by ring, ZMod.neg_val, ite_eq_right hn]
    omega⟩
  loopless := ⟨by intro u h; simpa using h⟩

/-- Every labelled feasible subset, including the empty set and singletons. -/
noncomputable def count (m : ℕ) : ℕ := Fintype.card (Configuration (host m))

private theorem visible_iff_common {V : Type*} [DecidableEq V]
    (G : SimpleGraph V)
    (hd : ∀ u v, u ≠ v → ¬ G.Adj u v → (G.commonNeighbors u v).Nonempty)
    (X : Finset V) :
    Visible G X ↔ ∀ u ∈ X, ∀ v ∈ X, u ≠ v → ¬ G.Adj u v →
      ∃ z, G.Adj u z ∧ G.Adj v z ∧ z ∉ X := by
  have hdist (u v : V) (huv : u ≠ v) (ha : ¬ G.Adj u v) : G.dist u v = 2 := by
    have he := (G.edist_eq_two_iff).mpr ⟨huv, ha, hd u v huv ha⟩
    simp [SimpleGraph.dist, he]
  constructor
  · intro h u hu v hv huv ha
    obtain ⟨p, hp, hs⟩ := h u hu v hv huv
    rw [hdist u v huv ha] at hp
    cases p with
    | nil => simp at hp
    | @cons u z v haz q =>
      have hq : q.length = 1 := by simpa using hp
      have hzv := q.adj_of_length_eq_one hq
      refine ⟨z, haz, hzv.symm, ?_⟩
      intro hz
      have he := hs z (by simp) hz
      rcases he with he | he
      · exact haz.ne he.symm
      · exact hzv.ne he
  · intro h u hu v hv huv
    by_cases ha : G.Adj u v
    · refine ⟨ha.toWalk, ?_, ?_⟩
      · simpa using (G.dist_eq_one_iff_adj.mpr ha).symm
      · intro z hz _
        simpa using hz
    · obtain ⟨z, huz, hvz, hz⟩ := h u hu v hv huv ha
      refine ⟨Walk.cons huz (Walk.cons hvz.symm Walk.nil), ?_, ?_⟩
      · simpa using (hdist u v huv ha).symm
      · intro t ht htx
        simp only [Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil, or_false] at ht
        rcases ht with rfl | rfl | rfl
        · exact Or.inl rfl
        · exact (hz htx).elim
        · exact Or.inr rfl

private theorem host_adj_cast (m j : ℕ) (hj : j ≤ m) (u : Vertex m) :
    (host m).Adj u (u + (1 + 3*j : ℕ)) := by
  change (u + (1 + 3*j : ℕ) - u).val % 3 = 1
  rw [add_sub_cancel_left, ZMod.val_natCast_of_lt (by omega)]
  omega

private theorem val_sub_borrow {m : ℕ} (a b : Vertex m) (h : a.val < b.val) :
    (a-b).val = 3*m+2+a.val-b.val := by
  have hn : b-a ≠ 0 := by
    intro he
    have := congrArg ZMod.val (sub_eq_zero.mp he)
    omega
  rw [show a-b = -(b-a) by ring, ZMod.neg_val, ite_eq_right hn,
    ZMod.val_sub (Nat.le_of_lt h)]
  have hb := ZMod.val_lt b
  omega

private theorem common_neighbors (m k : ℕ) (hk : 1 ≤ k) (hkm : k ≤ m)
    (u z : Vertex m) :
    ((host m).Adj u z ∧ (host m).Adj (u + (3*k-1 : ℕ)) z) ↔
      ∃ j < k, z = u + (1+3*j : ℕ) := by
  have hd : (3*k-1 : ℕ) < 3*m+2 := by omega
  have hdv : ((3*k-1 : ℕ) : Vertex m).val = 3*k-1 := ZMod.val_natCast_of_lt hd
  constructor
  · rintro ⟨huz, hvz⟩
    let a : Vertex m := z-u
    have hav : a.val < 3*m+2 := ZMod.val_lt a
    have har : a.val % 3 = 1 := huz
    let j := a.val / 3
    have haj : a.val = 1+3*j := by dsimp [j]; omega
    have hjm : j ≤ m := by omega
    have hjk : j < k := by
      by_contra h
      have hle : ((3*k-1 : ℕ) : Vertex m).val ≤ a.val := by rw [hdv]; omega
      change (z-(u+(3*k-1 : ℕ))).val % 3 = 1 at hvz
      rw [show z-(u+(3*k-1 : ℕ)) = a-(3*k-1 : ℕ) by dsimp [a]; ring,
        ZMod.val_sub hle, hdv] at hvz
      omega
    refine ⟨j, hjk, ?_⟩
    have hac : ((a.val : ℕ) : Vertex m) = a := ZMod.natCast_zmod_val a
    rw [haj] at hac
    dsimp [a] at hac
    rw [hac]
    ring
  · rintro ⟨j, hj, rfl⟩
    refine ⟨host_adj_cast m j (by omega) u, ?_⟩
    change ((u+(1+3*j : ℕ))-(u+(3*k-1 : ℕ))).val % 3 = 1
    rw [show (u+(1+3*j : ℕ))-(u+(3*k-1 : ℕ)) =
      (1+3*j : ℕ)-(3*k-1 : ℕ) by ring]
    have hjv : ((1+3*j : ℕ) : Vertex m).val = 1+3*j :=
      ZMod.val_natCast_of_lt (by omega)
    rw [val_sub_borrow _ _ (by rw [hjv, hdv]; omega), hjv, hdv]
    omega

private theorem nonedge_orientation (m : ℕ) (u v : Vertex m)
    (hne : u ≠ v) (ha : ¬ (host m).Adj u v) :
    (∃ k, 1 ≤ k ∧ k ≤ m ∧ v = u + (3*k-1 : ℕ)) ∨
    (∃ k, 1 ≤ k ∧ k ≤ m ∧ u = v + (3*k-1 : ℕ)) := by
  have hpos : 0 < (v-u).val := ZMod.val_pos.mpr (sub_ne_zero.mpr hne.symm)
  have hlt := ZMod.val_lt (v-u)
  change ¬ (v-u).val % 3 = 1 at ha
  by_cases hr : (v-u).val % 3 = 2
  · let k := ((v-u).val+1)/3
    have hk : 1 ≤ k ∧ k ≤ m ∧ (v-u).val = 3*k-1 := by dsimp [k]; omega
    refine Or.inl ⟨k, hk.1, hk.2.1, ?_⟩
    have hc := ZMod.natCast_zmod_val (v-u)
    rw [hk.2.2] at hc
    rw [hc]
    ring
  · have hn : v-u ≠ 0 := sub_ne_zero.mpr hne.symm
    have hv : (u-v).val = 3*m+2-(v-u).val := by
      rw [show u-v = -(v-u) by ring, ZMod.neg_val, ite_eq_right hn]
    let k := ((u-v).val+1)/3
    have hk : 1 ≤ k ∧ k ≤ m ∧ (u-v).val = 3*k-1 := by dsimp [k]; omega
    refine Or.inr ⟨k, hk.1, hk.2.1, ?_⟩
    have hc := ZMod.natCast_zmod_val (u-v)
    rw [hk.2.2] at hc
    rw [hc]
    ring

private theorem host_common_nonempty (m : ℕ) (u v : Vertex m)
    (hne : u ≠ v) (ha : ¬ (host m).Adj u v) :
    ((host m).commonNeighbors u v).Nonempty := by
  rcases nonedge_orientation m u v hne ha with ⟨k, hk, hkm, rfl⟩ | ⟨k, hk, hkm, he⟩
  · refine ⟨u+1, ?_⟩
    rw [SimpleGraph.mem_commonNeighbors]
    exact (common_neighbors m k hk hkm u (u+1)).mpr ⟨0, by omega, by simp⟩
  · refine ⟨v+1, ?_⟩
    rw [SimpleGraph.mem_commonNeighbors, he]
    exact ((common_neighbors m k hk hkm v (v+1)).mpr ⟨0, by omega, by simp⟩).symm

/-- A forbidden cyclic configuration consists of the nonedge endpoints and
all their common neighbors. The inequalities retain every boundary case. -/
def Obstruction (m : ℕ) (X : Finset (Vertex m)) : Prop :=
  ∃ u : Vertex m, ∃ k : ℕ, 1 ≤ k ∧ k ≤ m ∧ u ∈ X ∧
    u+(3*k-1 : ℕ) ∈ X ∧ ∀ j < k, u+(1+3*j : ℕ) ∈ X

/-- Exact obstruction characterization of the existing original-host predicate. -/
theorem visible_iff_no_obstruction (m : ℕ) (X : Finset (Vertex m)) :
    Visible (host m) X ↔ ¬ Obstruction m X := by
  rw [visible_iff_common (host m) (host_common_nonempty m) X]
  constructor
  · intro h ⟨u, k, hk, hkm, hu, hv, hall⟩
    have hd : ((3*k-1 : ℕ) : Vertex m).val = 3*k-1 :=
      ZMod.val_natCast_of_lt (by omega)
    have hne : u ≠ u+(3*k-1 : ℕ) := by
      intro he
      have hz : ((3*k-1 : ℕ) : Vertex m) = 0 := by
        have hh := congrArg (fun t : Vertex m => t-u) he
        simpa using hh.symm
      have := congrArg ZMod.val hz
      simp only [ZMod.val_zero] at this
      omega
    have ha : ¬ (host m).Adj u (u+(3*k-1 : ℕ)) := by
      change ¬ (u+(3*k-1 : ℕ)-u).val % 3 = 1
      rw [add_sub_cancel_left, hd]
      omega
    obtain ⟨z, huz, hvz, hz⟩ := h u hu _ hv hne ha
    obtain ⟨j, hj, rfl⟩ := (common_neighbors m k hk hkm u z).mp ⟨huz, hvz⟩
    exact hz (hall j hj)
  · intro h u hu v hv hne ha
    rcases nonedge_orientation m u v hne ha with ⟨k, hk, hkm, he⟩ | ⟨k, hk, hkm, he⟩
    · have hex : ∃ j < k, u+(1+3*j : ℕ) ∉ X := by
        by_contra hn
        push Not at hn
        exact h ⟨u, k, hk, hkm, hu, he ▸ hv, hn⟩
      obtain ⟨j, hj, hz⟩ := hex
      have hc := (common_neighbors m k hk hkm u (u+(1+3*j : ℕ))).mpr ⟨j, hj, rfl⟩
      exact ⟨_, hc.1, he ▸ hc.2, hz⟩
    · have hex : ∃ j < k, v+(1+3*j : ℕ) ∉ X := by
        by_contra hn
        push Not at hn
        exact h ⟨v, k, hk, hkm, hv, he ▸ hu, hn⟩
      obtain ⟨j, hj, hz⟩ := hex
      have hc := (common_neighbors m k hk hkm v (v+(1+3*j : ℕ))).mpr ⟨j, hj, rfl⟩
      exact ⟨_, he ▸ hc.2, hc.1, hz⟩

/-- The factor `11 (Σ Σ 1)^(k-1) 1`, read in the periodically extended
labelled word. Positions not mentioned in this predicate are unrestricted. -/
def ForbiddenFactor (m : ℕ) (X : Finset (Vertex m)) (u : Vertex m) (k : ℕ) : Prop :=
  1 ≤ k ∧ u ∈ X ∧ u+(3*k-1 : ℕ) ∈ X ∧ ∀ j < k, u+(1+3*j : ℕ) ∈ X

private theorem long_factor_obstruction (m : ℕ) (hm : 1 ≤ m)
    (X : Finset (Vertex m)) (u : Vertex m) (k : ℕ) (hkm : m < k)
    (h : ForbiddenFactor m X u k) : Obstruction m X := by
  have hlast : u + (1+3*m : ℕ) = u-1 := by
    have hz : ((3*m+2 : ℕ) : Vertex m) = 0 := by
      exact ZMod.natCast_self _
    push_cast at hz ⊢
    linear_combination hz
  have hfirst : u+1 ∈ X := by simpa using h.2.2.2 0 (by omega)
  have hprev : u-1 ∈ X := by
    rw [← hlast]
    exact h.2.2.2 m hkm
  refine ⟨u-1, 1, by omega, hm, hprev, ?_, ?_⟩
  · have he : u-1+(3*1-1 : ℕ) = u+1 := by norm_num; ring
    exact he.symm ▸ hfirst
  · intro j hj
    have hj0 : j = 0 := by omega
    subst j
    simpa using h.2.1

/-- For every original index at least two, the finite graph obstructions are
exactly the occurrences of the full unbounded regular family in its periodic word. -/
theorem visible_iff_periodic_avoidance (m : ℕ) (hm : 1 ≤ m)
    (X : Finset (Vertex m)) :
    Visible (host m) X ↔ ∀ u : Vertex m, ∀ k : ℕ, ¬ ForbiddenFactor m X u k := by
  rw [visible_iff_no_obstruction]
  constructor
  · intro h u k hf
    by_cases hkm : k ≤ m
    · exact h ⟨u, k, hf.1, hkm, hf.2⟩
    · exact h (long_factor_obstruction m hm X u k (by omega) hf)
  · intro h ⟨u, k, hk, hkm, hh⟩
    exact h u k ⟨hk, hh⟩

end D5.S3.Combinatorics.Graph.MutualVisibility.Andrasfai
