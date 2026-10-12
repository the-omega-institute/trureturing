/- GID: D5/S3/Combinatorics/PositionSets/VertexPositionRatioRefutation
   generality: I
   mirror-B: D5/B/S3/Combinatorics/PositionSets/VertexPositionRatioRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/PositionSets/VertexPositionRatioRefutation.claim; result=D5/S3/Combinatorics/PositionSets/VertexPositionRatioRefutation.result; claim=D5/S3/Combinatorics/PositionSets/VertexPositionRatioRefutation.claim
   digest: Connected graphs have unbounded upper to minimum vertex position ratio. -/

/-
proof_shape: result: content
escape_witness: none
admission_basis: open-problem-resolution (#15320; Refuted)
Direct frozen dependencies: none (pinned Mathlib only)
The public result is the designated refutation result (`basis=refutes`) and is exempt
from four-slot escape registration (CLAUDE.md §3.9).
Per-declaration proof shapes and live consumers (definitions have no proof shape):
potential_walk: content; consumers: potential_abs_dist; escape_witness: none.
potential_abs_dist: content; consumers: potential_dist; escape_witness: none.
potential_dist: content; consumers: root_dist, selected_distance_lower; escape_witness: none.
sphere_position: bind-only; consumers: x_lower; escape_witness: none.
card_le_posNum: bind-only; consumers: x_lower; escape_witness: none.
posNum_le: bind-only; consumers: hub_upper; escape_witness: none.
posNum_le_vp: bind-only; consumers: family_bounds; escape_witness: none.
vpMinus_le_posNum: bind-only; consumers: family_bounds; escape_witness: none.
level_node: bind-only;
  consumers: node_adj, potential_selected, selected_distance_upper, selected_injective; escape_witness: none.
node_zero: bind-only; consumers: node_adj, node_reconstruct; escape_witness: none.
ray_node: bind-only;
  consumers: node_adj, potential_selected, selected_distance_upper, selected_injective; escape_witness: none.
node_reconstruct: bind-only; consumers: same_ray_onGeodesic; escape_witness: none.
level_edge: bind-only; consumers: root_dist; escape_witness: none.
node_adj: bind-only; consumers: ray_walk, selected_distance_upper; escape_witness: none.
ray_walk: content;
  consumers: root_walk, same_ray_onGeodesic, selected_distance_upper; escape_witness: none.
root_walk: content;
  consumers: connected, root_dist, root_onGeodesic, same_ray_onGeodesic; escape_witness: none.
connected: content; consumers: result, root_dist, selected_distance_lower; escape_witness: none.
root_dist: content; consumers: root_onGeodesic, same_ray_onGeodesic; escape_witness: none.
same_ray_onGeodesic: content; consumers: hub_upper; escape_witness: none.
root_onGeodesic: content; consumers: hub_upper; escape_witness: none.
hub_upper: content; consumers: family_bounds; escape_witness: none.
rayPotential_zero: bind-only; consumers: potential_path; escape_witness: none.
rayPotential_step: bind-only; consumers: potential_path; escape_witness: none.
potential_path: bind-only; consumers: potential_edge; escape_witness: none.
potential_cross: bind-only; consumers: potential_edge; escape_witness: none.
potential_edge: bind-only; consumers: selected_distance_lower; escape_witness: none.
potential_x: bind-only; consumers: selected_distance_lower; escape_witness: none.
potential_selected: bind-only; consumers: selected_distance_lower; escape_witness: none.
selected_distance_lower: content; consumers: selected_distance; escape_witness: none.
selected_distance_upper: content; consumers: selected_distance; escape_witness: none.
selected_distance: content; consumers: x_lower; escape_witness: none.
selected_injective: bind-only; consumers: x_lower; escape_witness: none.
x_lower: content; consumers: family_bounds; escape_witness: none.
family_bounds: content; consumers: result; escape_witness: none.
ratio_growth: bind-only; consumers: result; escape_witness: none.
result: content; consumers: designated refutation; escape_witness: none.
-/

import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Algebra.Order.Archimedean.Real.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 10000

namespace D5.S3.Combinatorics.PositionSets.VertexPositionRatioRefutation
open SimpleGraph

def OnGeodesic {V : Type} (G : SimpleGraph V) (x y z : V) : Prop :=
  ∃ p : G.Walk x y, p.length = G.dist x y ∧ z ∈ p.support

def IsXPositionSet {V : Type} (G : SimpleGraph V) (x : V) (S : Finset V) : Prop :=
  ∀ y ∈ S, ∀ z ∈ S, z ≠ y → ¬ OnGeodesic G x y z

noncomputable def posNum {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (x : V) : ℕ := by
  classical
  exact ((Finset.univ : Finset (Finset V)).filter (IsXPositionSet G x)).sup Finset.card

noncomputable def vp {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : ℕ := Finset.univ.sup (posNum G)

noncomputable def vpMinus {V : Type} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) : ℕ :=
  Finset.univ.inf' Finset.univ_nonempty (posNum G)

def claim : Prop := ∃ C : ℝ, ∀ (V : Type) [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj],
    G.Connected → (vp G : ℝ) ≤ C * (vpMinus G : ℝ)


private lemma potential_walk {V : Type} (G : SimpleGraph V) (f : V → ℤ)
    (hf : ∀ u v, G.Adj u v → f u ≤ f v + 1)
    {u v : V} (p : G.Walk u v) : f u ≤ f v + (p.length : ℤ) := by
  induction p with
  | nil => simp
  | @cons u w v h p ih =>
    have := hf u w h
    simp only [Walk.length_cons, Nat.cast_add, Nat.cast_one]
    omega

private lemma potential_abs_dist {V : Type} (G : SimpleGraph V) (f : V → ℤ)
    (hf : ∀ u v, G.Adj u v → |f u - f v| ≤ 1)
    {u v : V} (hr : G.Reachable u v) : |f u - f v| ≤ (G.dist u v : ℤ) := by
  obtain ⟨p,hp⟩ := hr.exists_walk_length_eq_dist
  have hstep : ∀ a b, G.Adj a b → f a ≤ f b + 1 := by
    intro a b hab
    have := (abs_le.mp (hf a b hab)).2
    omega
  have h1 := potential_walk G f hstep p
  have h2 := potential_walk G f hstep p.reverse
  simp only [Walk.length_reverse, hp] at h1 h2
  exact abs_le.mpr ⟨by omega,by omega⟩

private lemma potential_dist {V : Type} (G : SimpleGraph V) (f : V → ℕ)
    (hf : ∀ u v, G.Adj u v → f u ≤ f v + 1)
    {u v : V} (hr : G.Reachable u v) : f u ≤ f v + G.dist u v := by
  have h := potential_abs_dist G (fun v => (f v : ℤ)) (by
    intro a b hab
    have h1 := hf a b hab
    have h2 := hf b a hab.symm
    exact abs_le.mpr ⟨by omega,by omega⟩) hr
  have := (abs_le.mp h).2
  omega

private lemma sphere_position {V : Type} [DecidableEq V] (G : SimpleGraph V) (x : V)
    (S : Finset V) (r : ℕ) (hs : ∀ v ∈ S, G.dist x v = r) :
    IsXPositionSet G x S := by
  intro y hy z hz hne ⟨p, hp, hm⟩
  have hl := G.length_eq_dist_of_subwalk hp (p.isSubwalk_takeUntil hm)
  have hr := G.length_eq_dist_of_subwalk hp (p.isSubwalk_dropUntil hm)
  have he : p.length = (p.takeUntil z hm).length + (p.dropUntil z hm).length := by
    rw [← Walk.length_append, p.take_spec hm]
  have hd : G.dist z y = 0 := by rw [hp, hl, hr, hs y hy, hs z hz] at he; omega
  exact hne ((p.dropUntil z hm).reachable.dist_eq_zero_iff.mp hd)

private lemma card_le_posNum {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (x : V) (S : Finset V) (hs : IsXPositionSet G x S) :
    S.card ≤ posNum G x := by
  classical
  exact Finset.le_sup (f := Finset.card) (by simp [hs])

private lemma posNum_le {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (x : V) (n : ℕ)
    (h : ∀ S, IsXPositionSet G x S → S.card ≤ n) : posNum G x ≤ n := by
  classical
  exact Finset.sup_le (fun S hS => h S (Finset.mem_filter.mp hS).2)

private lemma posNum_le_vp {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (x : V) : posNum G x ≤ vp G :=
  Finset.le_sup (Finset.mem_univ x)

private lemma vpMinus_le_posNum {V : Type} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) (x : V) : vpMinus G ≤ posNum G x :=
  Finset.inf'_le _ (Finset.mem_univ x)



private def rayLength (m : ℕ) : (Fin (m + 1) ⊕ Fin m) → ℕ
  | .inl _ => 4 * m
  | .inr j => 2 * m + 2 * (j.val + 1)


private def level {m : ℕ} : (Option (Σ r : (Fin (m + 1) ⊕ Fin m), Fin (rayLength m r))) → ℕ
  | none => 0
  | some ⟨_, k⟩ => k.val + 1

private def ray {m : ℕ} :
     (Option (Σ r : (Fin (m + 1) ⊕ Fin m), Fin (rayLength m r))) → (Fin (m + 1) ⊕ Fin m)
  | none => .inl 0
  | some ⟨r, _⟩ => r

private def node {m : ℕ}
    (r : (Fin (m + 1) ⊕ Fin m))
    (k : ℕ)
    (hk : k ≤ rayLength m r) : (Option (Σ r : (Fin (m + 1) ⊕ Fin m), Fin (rayLength m r))) :=
  if h : k = 0 then none else some ⟨r, ⟨k - 1, by omega⟩⟩

@[simp] private lemma level_node {m : ℕ}
    (r : (Fin (m + 1) ⊕ Fin m)) (k : ℕ) (hk : k ≤ rayLength m r) :
    level (node r k hk) = k := by
  unfold node
  split_ifs with h
  · simp [level, h]
  · simp only [level]; omega

@[simp] private lemma node_zero {m : ℕ} (r : (Fin (m + 1) ⊕ Fin m)) (h : 0 ≤ rayLength m r) :
    node r 0 h = none := by simp [node]

private lemma ray_node {m : ℕ}
    (r : (Fin (m + 1) ⊕ Fin m)) (k : ℕ) (hk : k ≤ rayLength m r) (h : k ≠ 0) :
    ray (node r k hk) = r := by simp [node, h, ray]

private lemma node_reconstruct {m : ℕ}
    (v : (Option (Σ r : (Fin (m + 1) ⊕ Fin m), Fin (rayLength m r)))) :
    ∃ h : level v ≤ rayLength m (ray v), node (ray v) (level v) h = v := by
  cases v with
  | none => exact ⟨by simp [level], by simp [level]⟩
  | some v =>
    rcases v with ⟨r,k⟩
    refine ⟨by exact k.isLt, ?_⟩
    simp [level, ray, node]

private def a {m : ℕ} (j : Fin m) := 2 * m + 2 * (j.val + 1)
private def b {m : ℕ} (j : Fin m) := 2 * m + j.val + 2

private def PathAdj {m : ℕ}
    (u v : (Option (Σ r : (Fin (m + 1) ⊕ Fin m), Fin (rayLength m r)))) : Prop :=
  (ray u = ray v ∨ u = none ∨ v = none) ∧
  (level u + 1 = level v ∨ level v + 1 = level u)

private def Cross {m : ℕ}
    (u v : (Option (Σ r : (Fin (m + 1) ⊕ Fin m), Fin (rayLength m r)))) : Prop :=
  (∃ j : Fin m, ray u = .inl 0 ∧ ray v = .inr j ∧ level u = b j ∧ level v = b j) ∨
  (∃ j : Fin m, ∃ i : Fin (m + 1), ray u = .inr j ∧ ray v = .inl i ∧
    i ≠ 0 ∧ level u = a j ∧ level v = a j)

private def graph (m : ℕ) : SimpleGraph ((Option (Σ r : (Fin (m + 1) ⊕ Fin m), Fin (rayLength m r)))) where
  Adj u v := PathAdj u v ∨ Cross u v ∨ Cross v u
  symm := ⟨by
    intro u v h
    rcases h with h | h | h
    · exact Or.inl ⟨h.1.elim (fun h => Or.inl h.symm)
        (fun h => Or.inr (h.elim Or.inr Or.inl)), h.2.symm⟩
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)⟩
  loopless := ⟨by
    intro u h
    rcases h with h | h | h
    · rcases h.2 with h | h <;> omega
    all_goals
      rcases h with ⟨j,h1,h2,_,_⟩ | ⟨j,i,h1,h2,_,_,_⟩
      · rw [h1] at h2; cases h2
      · rw [h1] at h2; cases h2⟩

private instance instGraphAdjDecidable (m : ℕ) : DecidableRel (graph m).Adj :=
  fun u v => by unfold graph PathAdj Cross; infer_instance

private lemma level_edge {m : ℕ}
    {u v : (Option (Σ r : (Fin (m + 1) ⊕ Fin m), Fin (rayLength m r)))} (h : (graph m).Adj u v) :
    level u ≤ level v + 1 := by
  rcases h with h | h | h
  · rcases h.2 with h | h <;> omega
  all_goals
    rcases h with ⟨j,_,_,h1,h2⟩ | ⟨j,i,_,_,_,h1,h2⟩ <;> omega

private lemma node_adj {m : ℕ} (r : (Fin (m + 1) ⊕ Fin m)) (k : ℕ) (hk : k + 1 ≤ rayLength m r) :
    (graph m).Adj (node r k (by omega)) (node r (k + 1) hk) := by
  apply Or.inl
  constructor
  · by_cases h : k = 0
    · exact Or.inr (Or.inl (by simp [h]))
    · exact Or.inl (by rw [ray_node _ _ _ h, ray_node _ _ _ (by omega)])
  · exact Or.inl (by simp)

private lemma ray_walk {m : ℕ} (r : (Fin (m + 1) ⊕ Fin m)) (s t : ℕ)
    (ht : t ≤ rayLength m r) (hst : s ≤ t) :
    ∃ p : (graph m).Walk (node r s (by omega)) (node r t ht), p.length = t - s := by
  obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le hst
  induction d with
  | zero => exact ⟨.nil, by simp⟩
  | succ d ih =>
    obtain ⟨p,hp⟩ := ih (by omega) (by omega)
    have he := node_adj r (s + d) (by omega)
    refine ⟨p.append he.toWalk, ?_⟩
    simp only [Walk.length_append, SimpleGraph.Adj.toWalk, Walk.length_cons, Walk.length_nil, hp]
    omega

private lemma root_walk {m : ℕ} (v : (Option (Σ r : (Fin (m + 1) ⊕ Fin m), Fin (rayLength m r)))) :
    ∃ p : (graph m).Walk none v, p.length = level v := by
  cases v with
  | none => exact ⟨.nil, rfl⟩
  | some v =>
    rcases v with ⟨r,k⟩
    have hk : k.val + 1 ≤ rayLength m r := k.isLt
    obtain ⟨p,hp⟩ := ray_walk r 0 (k.val + 1) hk (by omega)
    simpa [node, level] using (show ∃ p : (graph m).Walk
      (node r 0 (by omega)) (node r (k.val + 1) hk), p.length = k.val + 1 from
        ⟨p, by simpa using hp⟩)

private lemma connected (m : ℕ) : (graph m).Connected := by
  apply SimpleGraph.Connected.mk
  intro u v
  obtain ⟨p,_⟩ := root_walk u
  obtain ⟨q,_⟩ := root_walk v
  exact p.reachable.symm.trans q.reachable

private lemma root_dist {m : ℕ}
    (v :
     (Option (Σ r : (Fin (m + 1) ⊕ Fin m), Fin (rayLength m r)))) :
     (graph m).dist none v = level v := by
  obtain ⟨p,hp⟩ := root_walk v
  apply le_antisymm
  · simpa [hp] using (graph m).dist_le p
  · have h := potential_dist (graph m) level (fun _ _ h => level_edge h)
      ((connected m) v none)
    simpa [level, SimpleGraph.dist_comm] using h

private lemma same_ray_onGeodesic {m : ℕ}
    (u v : (Option (Σ r : (Fin (m + 1) ⊕ Fin m), Fin (rayLength m r))))
    (he : ray u = ray v) (hle : level u ≤ level v) : OnGeodesic (graph m) none v u := by
  obtain ⟨hu,heu⟩ := node_reconstruct u
  obtain ⟨hv,hev⟩ := node_reconstruct v
  obtain ⟨p,hp⟩ := root_walk u
  have hule : level u ≤ rayLength m (ray v) := by rw [← he]; exact hu
  have hnu : node (ray v) (level u) hule = u := by simpa only [← he] using heu
  have hex := ray_walk (ray v) (level u) (level v) hv hle
  rw [hnu,hev] at hex
  obtain ⟨q,hq⟩ := hex
  refine ⟨p.append q, ?_, ?_⟩
  · rw [Walk.length_append, hp, hq, root_dist]; omega
  · exact (Walk.mem_support_append_iff p q).mpr (Or.inl p.end_mem_support)

private lemma root_onGeodesic {m : ℕ}
    (v :
     (Option (Σ r : (Fin (m + 1) ⊕ Fin m), Fin (rayLength m r)))) : OnGeodesic (graph m) none v none :=
    by
  obtain ⟨p,hp⟩ := root_walk v
  exact ⟨p, hp.trans (root_dist v).symm, p.start_mem_support⟩

private lemma hub_upper {m : ℕ} : posNum (graph m) none ≤ 2 * m + 1 := by
  apply posNum_le
  intro S hs
  by_cases h0 : none ∈ S
  · have hsub : S ⊆ {none} := by
      intro v hv
      simp only [Finset.mem_singleton]
      by_contra he
      exact hs v hv none h0 (Ne.symm he) (root_onGeodesic v)
    have hcard := Finset.card_le_card hsub
    simp only [Finset.card_singleton] at hcard
    omega
  · have hi : Set.InjOn ray (S : Set ((Option (Σ r : (Fin (m + 1) ⊕ Fin m), Fin (rayLength m r))))) := by
      intro u hu v hv he
      by_contra hn
      rcases le_total (level u) (level v) with hle | hle
      · exact hs v hv u hu hn (same_ray_onGeodesic u v he hle)
      · exact hs u hu v hv (Ne.symm hn) (same_ray_onGeodesic v u he.symm hle)
    have hc := Finset.card_le_card_of_injOn ray
      (show Set.MapsTo ray (S : Set ((Option (Σ r : (Fin (m + 1) ⊕ Fin m), Fin (rayLength m r))))) (Finset.univ : Finset ((Fin (m + 1) ⊕ Fin m))) from
        fun _ _ => Finset.mem_univ _) hi
    simp only [Finset.card_univ, Fintype.card_sum, Fintype.card_fin] at hc
    omega

private def rayPotential (m : ℕ) (r : (Fin (m + 1) ⊕ Fin m)) (k : ℕ) : ℕ :=
  if k = 0 then 2 * m + 1 else
    match r with
    | .inl i => if i = 0 then min (2 * m + 1) (4 * m - k) else 2 * m + k % 2
    | .inr j => min (2 * m + 1) (max (4 * m + 1 - k) (k - (2 * j.val + 3)))

private def potential {m : ℕ}
    (v :
     (Option (Σ r : (Fin (m + 1) ⊕ Fin m), Fin (rayLength m r)))) :=
    rayPotential m (ray v) (level v)

private lemma rayPotential_zero (m : ℕ)
    (r : (Fin (m + 1) ⊕ Fin m)) : rayPotential m r 0 = 2 * m + 1 := by
  simp [rayPotential]

private lemma rayPotential_step (m : ℕ) (r : (Fin (m + 1) ⊕ Fin m)) (k l : ℕ)
    (he : k + 1 = l ∨ l + 1 = k) : rayPotential m r k ≤ rayPotential m r l + 1 := by
  cases r with
  | inl i =>
    by_cases hi : i = 0
    · simp only [rayPotential, hi, ↓reduceIte]
      split_ifs <;> omega
    · simp only [rayPotential, hi, ↓reduceIte]
      split_ifs <;> omega
  | inr j =>
    simp only [rayPotential]
    split_ifs <;> omega

private lemma potential_path {m : ℕ} (hm : 2 ≤ m)
    {u v : (Option (Σ r : (Fin (m + 1) ⊕ Fin m), Fin (rayLength m r)))} (h : PathAdj u v) :
    potential u ≤ potential v + 1 := by
  rcases h with ⟨he,hl⟩
  rcases he with he | rfl | rfl
  · change rayPotential m (ray u) (level u) ≤ rayPotential m (ray v) (level v) + 1
    rw [he]
    exact rayPotential_step m (ray v) (level u) (level v) hl
  · have hv : level v = 1 := by
      change 0 + 1 = level v ∨ level v + 1 = 0 at hl
      omega
    change rayPotential m (ray none) 0 ≤ rayPotential m (ray v) (level v) + 1
    rw [rayPotential_zero,hv]
    cases hr : ray v with
    | inl i => simp only [rayPotential]; split_ifs <;> omega
    | inr j => simp only [rayPotential]; split_ifs <;> omega
  · have hu : level u = 1 := by
      change level u + 1 = 0 ∨ 0 + 1 = level u at hl
      omega
    change rayPotential m (ray u) (level u) ≤ rayPotential m (ray none) 0 + 1
    rw [rayPotential_zero,hu]
    cases hr : ray u with
    | inl i => simp only [rayPotential]; split_ifs <;> omega
    | inr j => simp only [rayPotential]; split_ifs <;> omega

private lemma potential_cross {m : ℕ} (hm : 2 ≤ m)
    {u v : (Option (Σ r : (Fin (m + 1) ⊕ Fin m), Fin (rayLength m r)))} (h : Cross u v) :
    potential u ≤ potential v + 1 ∧ potential v ≤ potential u + 1 := by
  rcases h with ⟨j,hu,hv,hlu,hlv⟩ | ⟨j,i,hu,hv,hi,hlu,hlv⟩
  · simp only [potential,hu,hv,hlu,hlv,rayPotential,b]
    split_ifs <;> omega
  · have hmod : (2 * m + 2 * (j.val + 1)) % 2 = 0 := by omega
    simp only [potential,hu,hv,hlu,hlv,rayPotential,a,hi,hmod]
    split_ifs <;> omega

private lemma potential_edge {m : ℕ} (hm : 2 ≤ m)
    (u v : (Option (Σ r : (Fin (m + 1) ⊕ Fin m), Fin (rayLength m r))))
    (h : (graph m).Adj u v) : potential u ≤ potential v + 1 := by
  rcases h with h | h | h
  · exact potential_path hm h
  · exact (potential_cross hm h).1
  · exact (potential_cross hm h).2


private def x (m : ℕ) :
     (Option (Σ r : (Fin (m + 1) ⊕ Fin m), Fin (rayLength m r))) :=
    node (m := m) (.inl 0) (4 * m) (by simp [ rayLength])

private def selected {m : ℕ} (hm : 2 ≤ m) (ij : Fin m × Fin (m - 1)) :
     (Option (Σ r : (Fin (m + 1) ⊕ Fin m), Fin (rayLength m r))) :=
  node (((Sum.inl ij.1.succ) : Fin (m + 1) ⊕ Fin m)) (2 * m + 2 * (ij.2.val + 1) + 1) (by
    simp only [rayLength]; have := ij.2.isLt; omega)

private lemma potential_x {m : ℕ} (hm : 2 ≤ m) : potential (x m) = 0 := by
  have hn : 4 * m ≠ 0 := by omega
  simp [potential, x, rayLength, node, ray, level, rayPotential, hn]
  omega

private lemma potential_selected {m : ℕ} (hm : 2 ≤ m) (ij : Fin m × Fin (m - 1)) :
    potential (selected hm ij) = 2 * m + 1 := by
  have hn : 2 * m + 2 * (ij.2.val + 1) + 1 ≠ 0 := by omega
  have hi : (⟨ij.1.val + 1, by omega⟩ : Fin (m + 1)) ≠ 0 := by
    intro he; have := congrArg Fin.val he; simp only [Fin.val_zero] at this; omega
  have hmod : (2 * m + 2 * (ij.2.val + 1) + 1) % 2 = 1 := by omega
  simp [potential,selected,ray_node _ _ _ hn,rayPotential,hi,hmod]

private lemma selected_distance_lower {m : ℕ} (hm : 2 ≤ m) (ij : Fin m × Fin (m - 1)) :
    2 * m + 1 ≤ (graph m).dist (x m) (selected hm ij) := by
  have h := potential_dist (graph m) potential (potential_edge hm)
    ((connected m) (selected hm ij) (x m))
  simpa [potential_selected hm ij,potential_x hm,SimpleGraph.dist_comm] using h

private lemma selected_distance_upper {m : ℕ} (hm : 2 ≤ m) (ij : Fin m × Fin (m - 1)) :
    (graph m).dist (x m) (selected hm ij) ≤ 2 * m + 1 := by
  let j : Fin m := ⟨ij.2.val, by have := ij.2.isLt; omega⟩
  let i : Fin (m + 1) := ⟨ij.1.val + 1, by have := ij.1.isLt; omega⟩
  have hi : i ≠ 0 := by intro he; have := congrArg Fin.val he; simp [i] at this
  have ha : a j ≤ 4 * m := by dsimp [a,j]; have := ij.2.isLt; omega
  have hb : b j ≤ a j := by dsimp [a,b]; omega
  have hbN : b j ≤ 4 * m := hb.trans ha
  have hb0 : b j ≠ 0 := by dsimp [b]; omega
  have ha0 : a j ≠ 0 := by dsimp [a]; omega
  obtain ⟨p,hp⟩ := ray_walk (m := m) (.inl 0) (b j) (4 * m) (by simp [rayLength]) hbN
  obtain ⟨q,hq⟩ := ray_walk (.inr j) (b j) (a j) (by simp [rayLength,a]) hb
  have hHQ : (graph m).Adj (node (m := m) (.inl 0) (b j) (by simpa [rayLength] using hbN))
      (node (.inr j) (b j) (by simpa [rayLength,a] using hb)) := by
    apply Or.inr; apply Or.inl; apply Or.inl
    refine ⟨j, ?_, ?_, ?_, ?_⟩
    · exact ray_node _ _ _ hb0
    · exact ray_node _ _ _ hb0
    · exact level_node _ _ _
    · exact level_node _ _ _
  have hQP : (graph m).Adj (node (.inr j) (a j) (by simp [rayLength,a]))
      (node (.inl i) (a j) (by simpa [rayLength] using ha)) := by
    apply Or.inr; apply Or.inl; apply Or.inr
    refine ⟨j,i,?_,?_,hi,?_,?_⟩
    · exact ray_node _ _ _ ha0
    · exact ray_node _ _ _ ha0
    · exact level_node _ _ _
    · exact level_node _ _ _
  have hat : a j + 1 ≤ rayLength m (.inl i) := by
    simp only [rayLength]; dsimp [a,j]; have := ij.2.isLt; omega
  let w := p.reverse.append
    (hHQ.toWalk.append (q.append (hQP.toWalk.append (node_adj (.inl i) (a j) hat).toWalk)))
  have hw : w.length = 2 * m + 1 := by
    simp only [w, Walk.length_append, Walk.length_reverse, SimpleGraph.Adj.length_toWalk,hp,hq]
    dsimp [a,b]
    omega
  have hd := (graph m).dist_le w
  change (graph m).dist (x m) (selected hm ij) ≤ w.length at hd
  exact hw ▸ hd

private lemma selected_distance {m : ℕ} (hm : 2 ≤ m) (ij : Fin m × Fin (m - 1)) :
    (graph m).dist (x m) (selected hm ij) = 2 * m + 1 :=
  le_antisymm (selected_distance_upper hm ij) (selected_distance_lower hm ij)

private lemma selected_injective {m : ℕ} (hm : 2 ≤ m) : Function.Injective (selected hm) := by
  intro ij kl he
  have hlevel := congrArg level he
  simp only [selected,level_node] at hlevel
  have hn1 : 2 * m + 2 * (ij.2.val + 1) + 1 ≠ 0 := by omega
  have hn2 : 2 * m + 2 * (kl.2.val + 1) + 1 ≠ 0 := by omega
  have hray := congrArg ray he
  simp only [selected,ray_node _ _ _ hn1,ray_node _ _ _ hn2,
    Sum.inl.injEq] at hray
  have hval := congrArg Fin.val hray
  apply Prod.ext
  · apply Fin.ext; change ij.1.val + 1 = kl.1.val + 1 at hval; omega
  · apply Fin.ext; omega

private lemma x_lower {m : ℕ} (hm : 2 ≤ m) : m * (m - 1) ≤ posNum (graph m) (x m) := by
  classical
  let S := Finset.univ.image (selected hm)
  have hc : S.card = m * (m - 1) := by
    rw [Finset.card_image_of_injective _ (selected_injective hm)]
    simp
  have hs : IsXPositionSet (graph m) (x m) S := by
    apply sphere_position (graph m) (x m) S (2 * m + 1)
    intro v hv
    obtain ⟨ij,_,rfl⟩ := Finset.mem_image.mp hv
    exact selected_distance hm ij
  rw [← hc]
  exact card_le_posNum _ _ S hs

private lemma family_bounds {m : ℕ} (hm : 2 ≤ m) :
    m * (m - 1) ≤ vp (graph m) ∧ vpMinus (graph m) ≤ 2 * m + 1 := by
  exact ⟨(x_lower hm).trans (posNum_le_vp _ _),
    (vpMinus_le_posNum _ none).trans hub_upper⟩

private lemma ratio_growth (C : ℝ) : ∃ m : ℕ, 2 ≤ m ∧
    C * (2 * (m:ℝ) + 1) < ((m * (m - 1) : ℕ) : ℝ) := by
  let D := max C 0
  have hD : 0 ≤ D := le_max_right _ _
  have hCD : C ≤ D := le_max_left _ _
  obtain ⟨m,hm⟩ := exists_nat_gt (3 * D + 3)
  have hm2R : (2:ℝ) ≤ (m:ℝ) := by linarith
  have hm2 : 2 ≤ m := by exact_mod_cast hm2R
  have hmpos : (0:ℝ) < (m:ℝ) := by linarith
  have hmul := mul_pos hmpos (sub_pos.mpr hm)
  have hDmul := mul_nonneg hD (show 0 ≤ (m:ℝ) - 1 by linarith)
  have hcmp := mul_le_mul_of_nonneg_right hCD (show 0 ≤ 2 * (m:ℝ) + 1 by positivity)
  refine ⟨m,hm2,?_⟩
  rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one]
  nlinarith


theorem result : ¬ claim := by
  rintro ⟨C,hC⟩
  let D := max C 0
  obtain ⟨m,hm,hgrowth⟩ := ratio_growth D
  obtain ⟨hlo,hhi⟩ := family_bounds hm
  have hG :=
    hC ((Option (Σ r : (Fin (m + 1) ⊕ Fin m), Fin (rayLength m r)))) (graph m) (connected m)
  have hloR : ((m * (m - 1) : ℕ) : ℝ) ≤ (vp (graph m) : ℝ) := by
    exact_mod_cast hlo
  have hhiR : (vpMinus (graph m) : ℝ) ≤ 2 * (m:ℝ) + 1 := by
    exact_mod_cast hhi
  have hup : (vp (graph m) : ℝ) ≤ D * (vpMinus (graph m) : ℝ) :=
    hG.trans (mul_le_mul_of_nonneg_right (le_max_left C 0) (Nat.cast_nonneg _))
  have hup2 : (vp (graph m) : ℝ) ≤ D * (2 * (m:ℝ) + 1) :=
    hup.trans (mul_le_mul_of_nonneg_left hhiR (le_max_right C 0))
  exact (not_lt_of_ge (hloR.trans hup2)) hgrowth


end D5.S3.Combinatorics.PositionSets.VertexPositionRatioRefutation
