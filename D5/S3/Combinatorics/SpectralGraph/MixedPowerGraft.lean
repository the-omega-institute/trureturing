/- GID: D5/S3/Combinatorics/SpectralGraph/MixedPowerGraft
   generality: I
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/MixedPowerGraft
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Moving a pendant tip toward the longer arm decreases the mixed largest eigenvalue of the power. -/

import D5.S3.Combinatorics.Graph.ZeroForcing.GridPowerZeroForcingRefutation
import D5.S3.Combinatorics.Graph.PairedEdgeEnergy
import D5.S3.Combinatorics.Graph.GraphDistance
import D5.S3.Combinatorics.Graph.TreeGraft

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Matrix Finset SimpleGraph
open D5.S3.Combinatorics.Graph.ZeroForcing.GridPowerZeroForcingRefutation (graphPower)
open OmegaMath.RealRayleigh OmegaMath.MixedAdjacency OmegaMath.PairedEdgeEnergy OmegaMath.TreeGraft

noncomputable section

section Power

namespace D5.S3.Combinatorics.SpectralGraph.MixedPowerGraft

variable {V : Type*}

theorem graphPower_adj_dist_iff (G : SimpleGraph V) (hc : G.Connected) (k : ℕ) (i j : V) :
    (graphPower G k).Adj i j ↔ i ≠ j ∧ G.dist i j ≤ k := by
  change (i ≠ j ∧ G.edist i j ≤ (k : ℕ∞)) ↔ _
  rw [← (hc.preconnected i j).coe_dist_eq_edist]
  simp

private theorem le_graphPower (G : SimpleGraph V) {k : ℕ} (hk : 1 ≤ k) :
    G ≤ graphPower G k := by
  intro i j h
  refine ⟨h.ne, ?_⟩
  rw [G.edist_eq_one_iff_adj.mpr h]
  exact_mod_cast hk

theorem graphPower_connected (G : SimpleGraph V) (hc : G.Connected) {k : ℕ} (hk : 1 ≤ k) :
    (graphPower G k).Connected :=
  hc.mono (le_graphPower G hk)

end D5.S3.Combinatorics.SpectralGraph.MixedPowerGraft

end Power

open D5.S3.Combinatorics.SpectralGraph.MixedPowerGraft

section LeafAdjacency

namespace OmegaMath.TreeGraft

variable {V : Type*}

variable {T : SimpleGraph V} {z l : V}

private theorem power_leaf_adj [Fintype V] [DecidableEq V] (hT : T.Connected) (hz : ∀ v, T.Adj z v ↔ v = l)
    (l' : Surviving z) (hl : l'.val = l) {k : ℕ} (hk : 1 ≤ k) (v : Surviving z) :
    (graphPower T k).Adj z v.val ↔ (surviving T z).dist l' v ≤ k - 1 := by
  rw [graphPower_adj_dist_iff T hT, leaf_dist hT hz l' hl, and_iff_right v.property.symm]
  omega

end OmegaMath.TreeGraft

end LeafAdjacency

section PoweredGraft

namespace OmegaMath.TreeGraft.TerminalArms

variable {V : Type*} {T : SimpleGraph V} {z : V} {L : ℕ}
variable [Fintype V] [DecidableRel T.Adj] (A : TerminalArms T z L)

private abbrev PairIndex (L : ℕ) := Fin ((L + 1) / 2)

private theorem pair_left_lt (i : PairIndex L) : 2 * i.val < L := by
  have := i.isLt
  omega

private def leftIndex (i : PairIndex L) : Fin (L + 1) :=
  ⟨i.val, by have := pair_left_lt i; omega⟩

@[simp] private theorem rev_val (i : Fin (L + 1)) : i.rev.val = L - i.val := by
  simp [Fin.val_rev]

private def pairVertex (ib : PairIndex L × Bool) : V :=
  (A.q (if ib.2 then leftIndex ib.1 else (leftIndex ib.1).rev)).val

private theorem pairVertex_injective : Function.Injective A.pairVertex := by
  rintro ⟨i, b⟩ ⟨j, c⟩ h
  have he := congrArg Fin.val (A.q.injective (Subtype.ext h))
  have hi := pair_left_lt i
  have hj := pair_left_lt j
  cases b <;> cases c <;>
    simp only [Bool.false_eq_true, ite_false, ite_true,
      leftIndex, rev_val] at he
  · have hij : i = j := Fin.ext (by omega)
    simp [hij]
  · omega
  · omega
  · have hij : i = j := Fin.ext he
    simp [hij]

private abbrev Fixed := {v : V // v ∉ Set.range A.pairVertex}

/-- The moved tip, a possible midpoint, and all vertices outside the path are fixed. -/
private noncomputable def partition : Partition (PairIndex L) A.Fixed V := by
  classical
  exact (Equiv.sumCongr (Equiv.ofInjective A.pairVertex A.pairVertex_injective) (Equiv.refl _)).trans
    (Equiv.Set.sumCompl (Set.range A.pairVertex))

private def fixedTip : A.Fixed := ⟨z, by
  rintro ⟨⟨i, b⟩, he⟩
  exact (A.q _).property he⟩

@[simp] private theorem partition_right (i : PairIndex L) :
    right A.partition i = (A.q (leftIndex i).rev).val := rfl

private theorem fixed_of_external (w : Surviving z) (hw : w ∉ Set.range A.q) :
    w.val ∉ Set.range A.pairVertex := by
  rintro ⟨⟨i, b⟩, he⟩
  exact hw ⟨_, Subtype.ext he⟩

private theorem midpoint_of_fixed (w : A.Fixed) (j : Fin (L + 1)) (hw : (A.q j).val = w.val) :
    2 * j.val = L := by
  by_contra h
  have hj := j.isLt
  by_cases hj' : 2 * j.val < L
  · let i : PairIndex L := ⟨j.val, by omega⟩
    have he : leftIndex i = j := Fin.ext rfl
    exact w.property ⟨(i, true), by simpa [pairVertex, he] using hw⟩
  · let i : PairIndex L := ⟨L - j.val, by omega⟩
    have he : (leftIndex i).rev = j := Fin.ext (by simp [i, leftIndex]; omega)
    exact w.property ⟨(i, false), by simpa [pairVertex, he] using hw⟩

private theorem parallel_dist (hT : T.IsTree) (i j : Fin (L + 1)) :
    (surviving T z).dist (A.q i.rev) (A.q j.rev) = (surviving T z).dist (A.q i) (A.q j) := by
  have hi := i.isLt
  have hj := j.isLt
  simp only [A.path_dist hT, rev_val, max_def, min_def]
  split <;> split <;> omega

private theorem cross_dist (hT : T.IsTree) (i j : Fin (L + 1))
    (hi : 2 * i.val ≤ L) (hj : 2 * j.val ≤ L) :
    (surviving T z).dist (A.q i) (A.q j.rev) = L - i.val - j.val ∧
      (surviving T z).dist (A.q i.rev) (A.q j) = L - i.val - j.val := by
  have h₁ : i.val ≤ L - j.val := by omega
  have h₂ : j.val ≤ L - i.val := by omega
  constructor
  · rw [A.path_dist hT, rev_val, max_eq_right h₁, min_eq_left h₁]
    omega
  · rw [A.path_dist hT, rev_val, max_eq_left h₂, min_eq_right h₂]

private theorem parallel_le_cross (hT : T.IsTree) (i j : Fin (L + 1))
    (hi : 2 * i.val ≤ L) (hj : 2 * j.val ≤ L) :
    (surviving T z).dist (A.q i) (A.q j) ≤ (surviving T z).dist (A.q i) (A.q j.rev) := by
  rw [(A.cross_dist hT i j hi hj).1, A.path_dist hT]
  simp only [max_def, min_def]
  split <;> omega

/-- For every fixed survivor, the left side of each reflected pair is closer.
Taking the endpoint pair gives the nesting of the two attachment balls on fixed survivors. -/
private theorem fixed_dist_le (hT : T.IsTree) (w : A.Fixed) (hw : w.val ≠ z)
    (i : Fin (L + 1)) (hi : 2 * i.val ≤ L) :
    (surviving T z).dist ⟨w.val, hw⟩ (A.q i) ≤
      (surviving T z).dist ⟨w.val, hw⟩ (A.q i.rev) := by
  by_cases hq : (⟨w.val, hw⟩ : Surviving z) ∈ Set.range A.q
  · obtain ⟨j, hj⟩ := hq
    have he := A.midpoint_of_fixed w j (congrArg Subtype.val hj)
    rw [← hj]
    simp only [A.path_dist hT, rev_val, max_def, min_def]
    split <;> split <;> omega
  · have hs := A.shorter
    rw [A.external_dist hT hq i, A.external_dist hT hq i.rev]
    simp only [rev_val, max_def, min_def]
    split <;> split <;> omega

section Power


variable [DecidableEq V] {k : ℕ}

private theorem old_leaf_power_adj (hT : T.IsTree) (hk : 1 ≤ k) (w : Surviving z) :
    (graphPower T k).Adj z w.val ↔ (surviving T z).dist (A.q 0) w ≤ k - 1 :=
  power_leaf_adj hT.connected A.leaf (A.q 0) rfl hk w

private theorem new_leaf_power_adj (hT : T.IsTree) (hk : 1 ≤ k) (w : Surviving z) :
    (graphPower (graft T z (A.q (Fin.last L)).val) k).Adj z w.val ↔
      (surviving T z).dist (A.q (Fin.last L)) w ≤ k - 1 := by
  rw [power_leaf_adj (A.graft_tree hT).connected (graft_adj_leaf (A.q (Fin.last L)).property)
    (A.q (Fin.last L)) rfl hk w, surviving_graft]

omit [DecidableEq V] in
private theorem old_power_adj (A : TerminalArms T z L) (hT : T.IsTree) (u v : Surviving z) :
    (graphPower T k).Adj u.val v.val ↔ u ≠ v ∧ (surviving T z).dist u v ≤ k := by
  rw [graphPower_adj_dist_iff T hT.connected, ← surviving_dist hT.connected
    (leaf_subsingleton A.leaf) u v, ne_eq, Subtype.val_inj]

omit [DecidableEq V] in
private theorem new_power_adj (hT : T.IsTree) (u v : Surviving z) :
    (graphPower (graft T z (A.q (Fin.last L)).val) k).Adj u.val v.val ↔
      u ≠ v ∧ (surviving T z).dist u v ≤ k := by
  rw [graphPower_adj_dist_iff _ (A.graft_tree hT).connected,
    (graft_dist_surviving hT A.leaf (A.q (Fin.last L)) u v).1, ne_eq, Subtype.val_inj]

private theorem power_incidence (hT : T.IsTree) (hk : 1 ≤ k) :
    Incidence A.partition A.fixedTip (graphPower T k)
      (graphPower (graft T z (A.q (Fin.last L)).val) k) := by
  have hlo (i : PairIndex L) : 2 * (leftIndex i).val ≤ L := by
    exact (pair_left_lt i).le
  have hsep (i j : PairIndex L) : leftIndex i ≠ (leftIndex j).rev := by
    intro he
    have he' := congrArg Fin.val he
    have hi := pair_left_lt i
    have hj := pair_left_lt j
    simp only [leftIndex, rev_val] at he'
    omega
  constructor
  · intro u v hu hv
    exact (A.new_power_adj hT ⟨u, hu⟩ ⟨v, hv⟩).trans (A.old_power_adj hT ⟨u, hu⟩ ⟨v, hv⟩).symm
  · intro i j
    change (graphPower T k).Adj (A.q (leftIndex i)).val (A.q (leftIndex j)).val ↔
      (graphPower T k).Adj (A.q (leftIndex i).rev).val (A.q (leftIndex j).rev).val
    simp only [A.old_power_adj hT, A.parallel_dist hT,
      ne_eq, A.q.injective.eq_iff, Fin.rev_injective.eq_iff]
  · intro i j
    change (graphPower T k).Adj (A.q (leftIndex i)).val (A.q (leftIndex j).rev).val ↔
      (graphPower T k).Adj (A.q (leftIndex i).rev).val (A.q (leftIndex j)).val
    simp only [A.old_power_adj hT,
      (A.cross_dist hT _ _ (hlo i) (hlo j)).1, (A.cross_dist hT _ _ (hlo i) (hlo j)).2,
      A.q.injective.ne_iff]
    exact (and_iff_right (hsep i j)).trans (and_iff_right (hsep j i).symm).symm
  · intro i j hij
    change (graphPower T k).Adj (A.q (leftIndex i)).val (A.q (leftIndex j).rev).val →
      (graphPower T k).Adj (A.q (leftIndex i)).val (A.q (leftIndex j)).val
    simp only [A.old_power_adj hT]
    intro h
    refine ⟨fun he => hij (Fin.ext (congrArg (fun t : Fin (L + 1) => t.val) (A.q.injective he))), ?_⟩
    exact (A.parallel_le_cross hT _ _ (hlo i) (hlo j)).trans h.2
  · intro i w hw
    have hwz : w.val ≠ z := fun he => hw (Subtype.ext he)
    have hne (j : PairIndex L × Bool) : w.val ≠ A.pairVertex j :=
      fun he => w.property ⟨j, he.symm⟩
    change (graphPower T k).Adj w.val (A.q (leftIndex i).rev).val →
      (graphPower T k).Adj w.val (A.q (leftIndex i)).val
    rw [A.old_power_adj hT (⟨w.val, hwz⟩ : Surviving z),
      A.old_power_adj hT (⟨w.val, hwz⟩ : Surviving z)]
    intro h
    exact ⟨fun he => hne (i, true) (congrArg Subtype.val he),
      (A.fixed_dist_le hT w hwz _ (hlo i)).trans h.2⟩
  · intro i
    change (graphPower (graft T z (A.q (Fin.last L)).val) k).Adj z (A.q (leftIndex i)).val ↔
      (graphPower T k).Adj z (A.q (leftIndex i).rev).val
    rw [A.new_leaf_power_adj hT hk, A.old_leaf_power_adj hT hk, ← Fin.rev_zero,
      ← A.parallel_dist hT]
    simp
  · intro i
    change (graphPower (graft T z (A.q (Fin.last L)).val) k).Adj z (A.q (leftIndex i).rev).val ↔
      (graphPower T k).Adj z (A.q (leftIndex i)).val
    rw [A.new_leaf_power_adj hT hk, A.old_leaf_power_adj hT hk, ← Fin.rev_zero,
      A.parallel_dist hT]
  · intro i
    change (graphPower T k).Adj z (A.q (leftIndex i).rev).val →
      (graphPower T k).Adj z (A.q (leftIndex i)).val
    rw [A.old_leaf_power_adj hT hk, A.old_leaf_power_adj hT hk,
      A.path_dist hT, A.path_dist hT]
    have hi := pair_left_lt i
    simp only [Fin.val_zero, leftIndex, rev_val, max_def, min_def, Nat.zero_le, ite_true,
      Nat.sub_zero]
    omega
  · intro w
    change (graphPower (graft T z (A.q (Fin.last L)).val) k).Adj w.val z →
      (graphPower T k).Adj w.val z
    by_cases hw : w.val = z
    · simp [hw]
    · rw [adj_comm, adj_comm (u := w.val), A.new_leaf_power_adj hT hk ⟨w.val, hw⟩,
        A.old_leaf_power_adj hT hk ⟨w.val, hw⟩,
        SimpleGraph.dist_comm (u := A.q (Fin.last L)),
        SimpleGraph.dist_comm (u := A.q 0)]
      have hd := A.fixed_dist_le hT w hw 0 (by simp)
      rw [Fin.rev_zero] at hd
      exact fun h => hd.trans h

/-- Moving the shorter tip to the longer tip weakly decreases the mixed spectral value. -/
private theorem mixedTop_graft_le (hT : T.IsTree) (hk : 1 ≤ k) {α : ℝ} (hα : 0 ≤ α) (hα' : α ≤ 1) :
    mixedTop (graphPower (graft T z (A.q (Fin.last L)).val) k) α ≤
      mixedTop (graphPower T k) α := by
  classical
  let : Fintype A.Fixed := Fintype.ofFinite _
  exact mixedTop_le (A.power_incidence hT hk) hα hα'

end Power
end OmegaMath.TreeGraft.TerminalArms

end PoweredGraft

section LastGraft

namespace OmegaMath.TreeGraft.TerminalArms

variable {V : Type*} {T : SimpleGraph V} {z : V} {L : ℕ}
variable [Fintype V] [DecidableRel T.Adj] (A : TerminalArms T z L)

private def oldPath : pathGraph (L + 2) →g T where
  toFun := Fin.cons (α := fun _ => V) z (fun i => (A.q i).val)
  map_rel' := by
    intro x y h
    have hstep (x y : Fin (L + 2)) (hxy : x.val + 1 = y.val) :
        T.Adj (Fin.cons (α := fun _ => V) z (fun i => (A.q i).val) x)
          (Fin.cons (α := fun _ => V) z (fun i => (A.q i).val) y) := by
      cases y using Fin.cases with
      | zero => simp at hxy
      | succ j =>
        cases x using Fin.cases with
        | zero =>
          have hj : j = 0 := Fin.ext (by simp at hxy; omega)
          simpa [hj] using A.tip_adj
        | succ i =>
          simp only [Fin.cons_succ]
          apply A.step
          simp only [Fin.val_succ] at hxy
          omega
    exact (pathGraph_adj.mp h).elim (hstep x y) (fun h => (hstep y x h).symm)

private theorem oldPath_injective : Function.Injective A.oldPath := by
  intro x y h
  change Fin.cons (α := fun _ => V) z (fun i => (A.q i).val) x =
    Fin.cons (α := fun _ => V) z (fun i => (A.q i).val) y at h
  cases x using Fin.cases <;> cases y using Fin.cases
  · rfl
  · simp only [Fin.cons_zero, Fin.cons_succ] at h
    exact ((A.q _).property h.symm).elim
  · simp only [Fin.cons_zero, Fin.cons_succ] at h
    exact ((A.q _).property h).elim
  · simp only [Fin.cons_succ] at h
    exact congrArg Fin.succ (A.q.injective (Subtype.ext h))

/-- If the original tree is nonpath, some survivor is outside the two arms. -/
private theorem card_lt_of_nonpath (A : TerminalArms T z L) (hT : T.IsTree)
    (hNonpath : ¬ Nonempty (T ≃g pathGraph (Fintype.card V))) :
    L + 2 < Fintype.card V := by
  have hle : L + 2 ≤ Fintype.card V := by
    simpa using Fintype.card_le_of_injective A.oldPath A.oldPath_injective
  by_contra h
  have hc : L + 2 = Fintype.card V := by omega
  have hb : Function.Bijective A.oldPath :=
    (Fintype.bijective_iff_injective_and_card A.oldPath).mpr ⟨A.oldPath_injective, by simpa⟩
  let e : pathGraph (L + 2) ≃g T := {
    toEquiv := Equiv.ofBijective A.oldPath hb
    map_rel_iff' := by
      intro i j
      change T.Adj (A.oldPath i) (A.oldPath j) ↔ (pathGraph (L + 2)).Adj i j
      rw [← dist_eq_one_iff_adj, ← dist_eq_one_iff_adj,
        tree_dist_of_pathHom hT A.oldPath A.oldPath_injective,
        OmegaMath.Combinatorics.Graph.GraphDistance.pathGraph_dist, Nat.dist_eq_max_sub_min] }
  exact hNonpath ⟨hc ▸ e.symm⟩

private def reversePathIso (n : ℕ) : pathGraph n ≃g pathGraph n where
  toEquiv := Fin.revPerm
  map_rel_iff' := by
    intro i j
    change (pathGraph n).Adj i.rev j.rev ↔ (pathGraph n).Adj i j
    rw [pathGraph_adj, pathGraph_adj, Fin.val_rev, Fin.val_rev]
    have := i.isLt
    have := j.isLt
    omega

omit [Fintype V] in
private theorem pathIso_leaf_zero {H : SimpleGraph V} {r : V} {n : ℕ}
    (hz : ∀ v, H.Adj z v ↔ v = r)
    (e : H ≃g pathGraph n) : ∃ f : H ≃g pathGraph n, (f z).val = 0 := by
  let iz := e z
  have hEnd : iz.val = 0 ∨ iz.val + 1 = n := by
    by_contra! h
    let l : Fin n := ⟨iz.val - 1, by have := iz.isLt; omega⟩
    let r' : Fin n := ⟨iz.val + 1, by have := iz.isLt; omega⟩
    have hl : (pathGraph n).Adj iz l := pathGraph_adj.mpr (Or.inr (by dsimp [l]; omega))
    have hr : (pathGraph n).Adj iz r' := pathGraph_adj.mpr (Or.inl rfl)
    have hl' : H.Adj z (e.symm l) := by
      simpa [iz] using e.symm.toHom.map_rel hl
    have hr' : H.Adj z (e.symm r') := by
      simpa [iz] using e.symm.toHom.map_rel hr
    have he := congrArg Fin.val (e.symm.injective (((hz _).mp hl').trans ((hz _).mp hr').symm))
    dsimp [l, r'] at he
    omega
  rcases hEnd with h | h
  · exact ⟨e, h⟩
  · refine ⟨e.trans (reversePathIso n), ?_⟩
    change iz.rev.val = 0
    rw [Fin.val_rev]
    omega

omit [Fintype V] in
private theorem dist_eq_index_of_iso_zero [DecidableEq V] {H : SimpleGraph V} {n : ℕ}
    (e : H ≃g pathGraph n) (he : (e z).val = 0) (v : V) :
    H.dist z v = (e v).val := by
  have h := congrArg ENat.toNat (edist_iso e z v)
  change H.dist z v = (pathGraph n).dist (e z) (e v) at h
  rw [h, OmegaMath.Combinatorics.Graph.GraphDistance.pathGraph_dist, he, Nat.dist_eq_max_sub_min]
  simp

section Power

variable [DecidableEq V]

/-- On the last nonpath-to-path graft the short arm has length one.
The vertex at distance `max 1 (k - L)` on the other side of the root survives
and lies outside the reflected path. -/
private theorem last_graft_geometry (hT : T.IsTree)
    (hNonpath : ¬ Nonempty (T ≃g pathGraph (Fintype.card V)))
    (hPath : Nonempty (graft T z (A.q (Fin.last L)).val ≃g pathGraph (Fintype.card V)))
    {k : ℕ} (hn : k + 2 ≤ Fintype.card V) :
    A.root = 0 ∧ ∃ u : Surviving z, u ∉ Set.range A.q ∧
      (surviving T z).dist (A.q 0) u = max 1 (k - L) ∧
      (surviving T z).dist (A.q (Fin.last L)) u = L + max 1 (k - L) := by
  let H := graft T z (A.q (Fin.last L)).val
  have hH : H.IsTree := A.graft_tree hT
  have hz := graft_adj_leaf (T := T) (A.q (Fin.last L)).property
  obtain ⟨e, he⟩ := pathIso_leaf_zero hz hPath.some
  have hlarge := A.card_lt_of_nonpath hT hNonpath
  have hq (i : Fin (L + 1)) : (e (A.q i).val).val = 1 + (L - i.val) := by
    rw [← dist_eq_index_of_iso_zero e he, leaf_dist hH.connected hz
      (A.q (Fin.last L)) rfl, surviving_graft, A.path_dist hT, Fin.val_last]
    have hi : i.val ≤ L := Nat.le_of_lt_succ i.isLt
    rw [max_eq_left hi, min_eq_right hi]
  let d := max 1 (k - L)
  have hd : 1 ≤ d := le_max_left _ _
  have hbound : L + 1 + d < Fintype.card V := by
    dsimp [d]
    simp only [max_def]
    split <;> omega
  let j : Fin (Fintype.card V) := ⟨L + 1 + d, hbound⟩
  let v : V := e.symm j
  have hv : e v = j := e.apply_symm_apply j
  have hvz : v ≠ z := by
    intro h
    have hzj := congrArg Fin.val (hv.symm.trans (congrArg e h))
    rw [he] at hzj
    dsimp [j] at hzj
    omega
  let u : Surviving z := ⟨v, hvz⟩
  have hu : u ∉ Set.range A.q := by
    rintro ⟨i, hi⟩
    have hvi : e (A.q i).val = j := (congrArg (fun u : Surviving z => e u.val) hi).trans hv
    have := congrArg Fin.val hvi
    rw [hq] at this
    dsimp [j] at this
    omega
  have oldDist : (surviving T z).dist (A.q 0) u = d := by
    rw [← surviving_graft (T := T) (r := (A.q (Fin.last L)).val),
      surviving_dist hH.connected (leaf_subsingleton hz)]
    change (ENat.toNat (H.edist (A.q 0).val v)) = d
    rw [edist_iso e]
    change (pathGraph (Fintype.card V)).dist (e (A.q 0).val) (e v) = d
    rw [OmegaMath.Combinatorics.Graph.GraphDistance.pathGraph_dist, Nat.dist_eq_max_sub_min, hq, hv]
    simp only [Fin.val_zero, Nat.sub_zero]
    simp only [j, max_def, min_def]
    split <;> omega
  have newDist : (surviving T z).dist (A.q (Fin.last L)) u = L + d := by
    have h := dist_eq_index_of_iso_zero e he v
    rw [hv, leaf_dist hH.connected hz (A.q (Fin.last L)) rfl u, surviving_graft] at h
    change 1 + (surviving T z).dist (A.q (Fin.last L)) u = L + 1 + d at h
    omega
  have h₀ := A.external_dist hT hu 0
  have h₁ := A.external_dist hT hu (Fin.last L)
  rw [SimpleGraph.dist_comm (u := u), oldDist] at h₀
  rw [SimpleGraph.dist_comm (u := u), newDist, Fin.val_last] at h₁
  have hs : A.root.val ≤ L := Nat.le_of_lt_succ A.root.isLt
  rw [max_eq_right hs, min_eq_left hs] at h₁
  simp only [Fin.val_zero, max_eq_left (Nat.zero_le _), min_eq_right (Nat.zero_le _),
    Nat.sub_zero] at h₀
  refine ⟨Fin.ext ?_, u, hu, oldDist, newDist⟩
  change A.root.val = 0
  omega

/-- The fixed vertex on the far side of the root belongs only to the old leaf ball. -/
private theorem last_graft_witness (hT : T.IsTree)
    (hNonpath : ¬ Nonempty (T ≃g pathGraph (Fintype.card V)))
    (hPath : Nonempty (graft T z (A.q (Fin.last L)).val ≃g pathGraph (Fintype.card V)))
    {k : ℕ} (hk : 2 ≤ k) (hn : k + 2 ≤ Fintype.card V) :
    ∃ w : A.Fixed, (graphPower T k).Adj (fixed A.partition w) (fixed A.partition A.fixedTip) ∧
      ¬ (graphPower (graft T z (A.q (Fin.last L)).val) k).Adj
        (fixed A.partition w) (fixed A.partition A.fixedTip) := by
  obtain ⟨_, u, hu, oldDist, newDist⟩ := A.last_graft_geometry hT hNonpath hPath hn
  have hL : 1 ≤ L := by have := A.shorter; omega
  have hdk : max 1 (k - L) ≤ k - 1 := by
    apply max_le <;> omega
  have hdk' : k ≤ L + max 1 (k - L) := by
    have := le_max_right 1 (k - L)
    omega
  let w : A.Fixed := ⟨u.val, A.fixed_of_external u hu⟩
  refine ⟨w, ?_, ?_⟩
  · change (graphPower T k).Adj u.val z
    exact ((A.old_leaf_power_adj hT (by omega) u).mpr (oldDist.symm ▸ hdk)).symm
  · change ¬ (graphPower (graft T z (A.q (Fin.last L)).val) k).Adj u.val z
    intro h
    have hle := (A.new_leaf_power_adj hT (by omega) u).mp h.symm
    omega

/-- The last graft from a nonpath tree to a path strictly decreases the mixed
spectral radius when `k ≥ 2` and the path power is incomplete. -/
private theorem mixedTop_last_graft_lt (hT : T.IsTree)
    (hNonpath : ¬ Nonempty (T ≃g pathGraph (Fintype.card V)))
    (hPath : Nonempty (graft T z (A.q (Fin.last L)).val ≃g pathGraph (Fintype.card V)))
    {k : ℕ} (hk : 2 ≤ k) (hn : k + 2 ≤ Fintype.card V)
    {α : ℝ} (hα : 0 ≤ α) (hα' : α < 1) :
    mixedTop (graphPower (graft T z (A.q (Fin.last L)).val) k) α <
      mixedTop (graphPower T k) α := by
  classical
  let : Fintype A.Fixed := Fintype.ofFinite _
  obtain ⟨w, hw, hw'⟩ := A.last_graft_witness hT hNonpath hPath hk hn
  have hk' : 1 ≤ k := by omega
  exact mixedTop_lt (A.power_incidence hT hk')
    (graphPower_connected _ (A.graft_tree hT).connected hk') hα hα' w hw hw'

end Power
end OmegaMath.TreeGraft.TerminalArms

end LastGraft

section PendantArms

namespace OmegaMath.TreeGraft

variable {V : Type*} {T : SimpleGraph V} {v : V}

namespace PendantArm

variable [Fintype V] [DecidableRel T.Adj] {a b : ℕ}
variable (X : PendantArm T v a) (Y : PendantArm T v b)

theorem mixedTop_move_le [DecidableEq V] (hT : T.IsTree) (hb : 1 ≤ b) (hab : b ≤ a)
    (hfirst : X.first (hb.trans hab) ≠ Y.first hb) {k : ℕ} (hk : 1 ≤ k)
    {α : ℝ} (hα : 0 ≤ α) (hα' : α ≤ 1) :
    mixedTop (graphPower (X.move Y hb) k) α ≤ mixedTop (graphPower T k) α := by
  rw [X.move_eq_graft Y hT hb hab hfirst, ← X.terminalArms_right Y hT hb hab hfirst]
  exact (X.terminalArms Y hT hb hab hfirst).mixedTop_graft_le hT hk hα hα'

theorem mixedTop_last_move_lt [DecidableEq V] (hT : T.IsTree) (hb : 1 ≤ b) (hab : b ≤ a)
    (hfirst : X.first (hb.trans hab) ≠ Y.first hb)
    (hNonpath : ¬ Nonempty (T ≃g pathGraph (Fintype.card V)))
    (hPath : Nonempty (X.move Y hb ≃g pathGraph (Fintype.card V)))
    {k : ℕ} (hk : 2 ≤ k) (hn : k + 2 ≤ Fintype.card V) {α : ℝ}
    (hα : 0 ≤ α) (hα' : α < 1) :
    mixedTop (graphPower (X.move Y hb) k) α < mixedTop (graphPower T k) α := by
  rw [X.move_eq_graft Y hT hb hab hfirst, ← X.terminalArms_right Y hT hb hab hfirst] at hPath ⊢
  exact (X.terminalArms Y hT hb hab hfirst).mixedTop_last_graft_lt hT hNonpath hPath hk hn hα hα'

end PendantArm
end OmegaMath.TreeGraft

end PendantArms

section FirstPower

open scoped Classical

namespace D5.S3.Combinatorics.SpectralGraph.MixedPowerGraft

private theorem graphPower_one {V : Type*} (G : SimpleGraph V) : graphPower G 1 = G := by
  ext u v
  change (u ≠ v ∧ G.edist u v ≤ (1 : ℕ∞)) ↔ G.Adj u v
  rw [edist_le_one_iff_adj_or_eq]
  exact ⟨fun ⟨hne, h⟩ => h.resolve_right hne, fun h => ⟨h.ne, Or.inl h⟩⟩

end D5.S3.Combinatorics.SpectralGraph.MixedPowerGraft

open D5.S3.Combinatorics.SpectralGraph.MixedPowerGraft
namespace OmegaMath.TreeGraft

variable {V : Type*} [Fintype V] [DecidableEq V]

private noncomputable def neighbors (G : SimpleGraph V) (u : V) : Finset V :=
  G.neighborFinset u

omit [DecidableEq V] in
@[simp] private theorem mem_neighbors (G : SimpleGraph V) (u v : V) :
    v ∈ neighbors G u ↔ G.Adj u v :=
  G.mem_neighborFinset u v

private theorem mixed_row (G : SimpleGraph V) (α : ℝ) (x : V → ℝ) (u : V) :
    (mixedMatrix G α *ᵥ x) u =
      α * ((neighbors G u).card : ℝ) * x u + (1 - α) * ∑ v ∈ neighbors G u, x v := by
  simp only [mixedMatrix, Matrix.add_mulVec, Matrix.smul_mulVec, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, degMatrix_mulVec_apply, adjMatrix_mulVec_apply, mul_assoc, neighbors,
    SimpleGraph.degree]

namespace TerminalArms

variable {T : SimpleGraph V} {z : V} {L : ℕ}
  [DecidableRel T.Adj] (A : TerminalArms T z L)

/-- The final move to a path is strict for the first power. If the Rayleigh
values agree, the compressed vector and the input both satisfy the top
eigenvector equation. Three rows rule out the three orders of the attachment
coordinates. -/
theorem mixedTop_last_graft_one_lt (hT : T.IsTree)
    (hNonpath : ¬ Nonempty (T ≃g pathGraph (Fintype.card V)))
    (hPath : Nonempty (graft T z (A.q (Fin.last L)).val ≃g pathGraph (Fintype.card V)))
    {α : ℝ} (hα : 0 ≤ α) (hα' : α < 1) :
    mixedTop (graphPower (graft T z (A.q (Fin.last L)).val) 1) α <
      mixedTop (graphPower T 1) α := by
  let l := (A.q 0).val
  let r := (A.q (Fin.last L)).val
  let H := graft T z r
  have hL : 1 ≤ L := by have := A.shorter; omega
  have hlz : l ≠ z := (A.q 0).property
  have hrz : r ≠ z := (A.q (Fin.last L)).property
  have hlr : l ≠ r := by
    intro h
    have := congrArg Fin.val (A.q.injective (Subtype.ext h))
    simp at this
    omega
  let : Nonempty V := hT.connected.nonempty
  let : Fintype A.Fixed := Fintype.ofFinite _
  have hgeom := A.card_lt_of_nonpath hT hNonpath
  obtain ⟨hroot, w, hw, hwd, _⟩ :=
    A.last_graft_geometry hT hNonpath hPath (k := 1) (by omega)
  have hwl : T.Adj l w.val := by
    change (surviving T z).Adj (A.q 0) w
    apply dist_eq_one_iff_adj.mp
    simpa [Nat.sub_eq_zero_of_le hL] using hwd
  have hinc : Incidence A.partition A.fixedTip T H := by
    simpa only [graphPower_one] using A.power_incidence hT (k := 1) (by decide)
  obtain ⟨x, hunit, henergy, heig, hx⟩ :=
    mixed_positive_maximizer H (A.graft_tree hT).connected hα hα'
  let y := compress A.partition x
  have hyunit : UnitVector y := compress_unitVector A.partition hunit
  have hle : mixedTop H α ≤ energy (mixedMatrix T α) y :=
    henergy ▸ energy_le_compress hinc hα hα'.le (fun v => (hx v).le)
  rw [graphPower_one, graphPower_one]
  refine lt_of_le_of_ne (hle.trans (energy_le_top (mixedMatrix T α) hyunit)) ?_
  intro heq
  have hyenergy : energy (mixedMatrix T α) y = mixedTop T α :=
    le_antisymm (energy_le_top (mixedMatrix T α) hyunit) (heq ▸ hle)
  have hyeig := mulVec_eq_top_of_max (mixedMatrix T α) (mixedMatrix_hermitian T α) hyunit hyenergy
  change mixedMatrix T α *ᵥ y = mixedTop T α • y at hyeig
  rw [← heq] at hyeig
  have row (u : V) (hu : x u = y u) :
      (mixedMatrix H α *ᵥ x) u = (mixedMatrix T α *ᵥ y) u := by
    rw [heig, hyeig]
    change mixedTop H α * x u = mixedTop H α * y u
    rw [hu]
  have hpos : 0 < 1 - α := sub_pos.mpr hα'
  let i₀ : PairIndex L := ⟨0, by omega⟩
  have hlpair : left A.partition i₀ = l := rfl
  have hrpair : right A.partition i₀ = r := by
    rw [partition_right, show leftIndex i₀ = 0 from Fin.ext rfl, Fin.rev_zero]
  have hyl : y l = max (x l) (x r) := by
    simpa only [hlpair, hrpair] using compress_left A.partition x i₀
  have hyr : y r = min (x l) (x r) := by
    simpa only [hlpair, hrpair] using compress_right A.partition x i₀
  have hyz : y z = x z := compress_fixed A.partition x A.fixedTip
  have fixedCoord (u : Surviving z) (hu : u ∉ Set.range A.q) : y u.val = x u.val :=
    compress_fixed A.partition x ⟨u.val, A.fixed_of_external u hu⟩
  have hyw := fixedCoord w hw
  have hnew (v : V) : H.Adj z v ↔ v = r := graft_adj_leaf hrz v
  have hoff {u v : V} (hu : u ≠ z) (hv : v ≠ z) :
      H.Adj u v ↔ T.Adj u v := hinc.off_leaf hu hv
  have hleafT : neighbors T z = {l} := by
    ext v
    exact (mem_neighbors T z v).trans ((A.leaf v).trans Finset.mem_singleton.symm)
  have hleafH : neighbors H z = {r} := by
    ext v
    exact (mem_neighbors H z v).trans ((hnew v).trans Finset.mem_singleton.symm)
  have hlt₁ : ¬ x r < x l := by
    intro h
    have hzrow := row z hyz.symm
    rw [mixed_row, mixed_row, hleafT, hleafH, sum_singleton, sum_singleton, hyz,
      hyl, max_eq_left h.le] at hzrow
    simp only [card_singleton] at hzrow
    exact (mul_lt_mul_of_pos_left h hpos).ne (add_left_cancel hzrow)
  have hlt₂ : ¬ x l < x r := by
    intro h
    have hwz : w.val ≠ z := w.property
    have hnT : ¬ T.Adj w.val z := fun hz => hw ⟨0, Subtype.ext ((A.leaf _).mp hz.symm).symm⟩
    have hnH : ¬ H.Adj w.val z := fun hz => hw ⟨Fin.last L, Subtype.ext ((hnew _).mp hz.symm).symm⟩
    have hneighbors : neighbors H w.val = neighbors T w.val := by
      ext v
      simp only [mem_neighbors]
      by_cases hv : v = z
      · subst v
        simp [hnT, hnH]
      · exact hoff hwz hv
    have hlmem : l ∈ neighbors H w.val :=
      (mem_neighbors _ _ _).mpr ((hoff hwz hlz).mpr hwl.symm)
    have hsum : ∑ v ∈ neighbors H w.val, x v < ∑ v ∈ neighbors H w.val, y v := by
      refine Finset.sum_lt_sum (fun v hv => ?_) ⟨l, hlmem, ?_⟩
      · have hvadj : H.Adj w.val v := (mem_neighbors _ _ _).mp hv
        have hvz : v ≠ z := fun he => hnH (he ▸ hvadj)
        let u : Surviving z := ⟨v, hvz⟩
        by_cases hu : u ∈ Set.range A.q
        · obtain ⟨j, hj⟩ := hu
          have ht : (surviving T z).Adj (A.q j) w := by
            change T.Adj (A.q j).val w.val
            rw [hj]
            exact ((hoff hwz hvz).mp hvadj).symm
          have hindex := (A.external_adj hw ht).trans hroot
          subst j
          have hv' : l = v := congrArg Subtype.val hj
          rw [← hv', hyl]
          exact le_max_left _ _
        · exact (fixedCoord u hu).ge
      · rw [hyl, max_eq_right h.le]
        exact h
    have hwrow := row w.val hyw.symm
    rw [mixed_row, mixed_row, hyw, ← hneighbors] at hwrow
    exact (mul_lt_mul_of_pos_left hsum hpos).ne (add_left_cancel hwrow)
  have htie : x l = x r := le_antisymm (le_of_not_gt hlt₁) (le_of_not_gt hlt₂)
  have hyltie : y l = x l := hyl.trans (max_eq_left htie.ge)
  let j₁ : Fin (L + 1) := ⟨1, by omega⟩
  have hy₁ : x (A.q j₁).val ≤ y (A.q j₁).val := by
    rcases lt_trichotomy 2 L with h | h | h
    · let i₁ : PairIndex L := ⟨1, by omega⟩
      have hi : left A.partition i₁ = (A.q j₁).val := rfl
      rw [← hi]
      change x (left A.partition i₁) ≤ compress A.partition x (left A.partition i₁)
      rw [compress_left]
      exact le_max_left _ _
    · have hfix : (A.q j₁).val ∉ Set.range A.pairVertex := by
        rintro ⟨⟨i, b⟩, hi⟩
        have he := congrArg Fin.val (A.q.injective (Subtype.ext hi))
        have hb := i.isLt
        cases b <;> simp [j₁, leftIndex] at he <;> omega
      exact (compress_fixed A.partition x ⟨_, hfix⟩).ge
    · have he : j₁ = Fin.last L := Fin.ext (by change 1 = L; omega)
      rw [he]
      change x r ≤ y r
      rw [hyr, htie, min_self]
  have hlno : ¬ H.Adj l z := fun h => hlr ((hnew _).mp h.symm)
  have hneigh : neighbors T l = insert z (neighbors H l) := by
    ext v
    simp only [mem_neighbors, mem_insert]
    by_cases hv : v = z
    · subst v
      simp [A.tip_adj.symm, l]
    · simp [hv, hoff hlz hv]
  have hsum : ∑ v ∈ neighbors H l, x v ≤ ∑ v ∈ neighbors H l, y v := by
    apply Finset.sum_le_sum
    intro v hv
    have hHv : H.Adj l v := (mem_neighbors _ _ _).mp hv
    have hvz : v ≠ z := fun he => hlno (he ▸ hHv)
    let u : Surviving z := ⟨v, hvz⟩
    by_cases hu : u ∈ Set.range A.q
    · obtain ⟨j, hj⟩ := hu
      have hadj : (surviving T z).Adj (A.q 0) (A.q j) := by
        rw [hj]
        exact (hoff hlz hvz).mp hHv
      have hd := dist_eq_one_iff_adj.mpr hadj
      rw [A.path_dist hT] at hd
      have hj₁ : j = j₁ := Fin.ext (by simpa [j₁] using hd)
      subst j
      simpa only [hj] using hy₁
    · exact (fixedCoord u hu).ge
  have hzmem : z ∉ neighbors H l := fun hz => hlno ((mem_neighbors _ _ _).mp hz)
  have hlrow := row l hyltie.symm
  rw [mixed_row, mixed_row, hyltie, hneigh, sum_insert hzmem, hyz] at hlrow
  rw [card_insert_of_notMem hzmem, Nat.cast_add, Nat.cast_one] at hlrow
  have hdiag : 0 ≤ α * x l := mul_nonneg hα (hx l).le
  have hzterm : 0 < (1 - α) * x z := mul_pos hpos (hx z)
  have hsum' := mul_le_mul_of_nonneg_left hsum hpos.le
  linarith only [hlrow, hdiag, hzterm, hsum']

end TerminalArms

end OmegaMath.TreeGraft

end FirstPower
