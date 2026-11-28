/- GID: D5/S3/Combinatorics/Graph/Chordal/Staircase/BinaryStaircaseGraph
   generality: G
   mirror-B: none(waiver:covered-by-chordal-banach-exact-strata-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The binary staircase graph, its orientation, and the relation between its weighted lane circulations and the leaf coordinates in the filling theorem. -/

import OmegaBuild.Commands
import D5.S3.Combinatorics.Graph.Chordal.Staircase.BinaryStaircaseFilling
import Mathlib.Combinatorics.SimpleGraph.Clique

compile_only_with_mathlib

/-! Omega original.

The binary staircase graph, its orientation, and the relation between its
weighted lane circulations and the leaf coordinates in the filling theorem.
-/
namespace FiveLaneRouting.BinaryStaircase

open Finset SimpleGraph
open scoped BigOperators
noncomputable section

abbrev Vertex := Unit ⊕ ((Block × Label) ⊕ Leaf)

def startVertex : Vertex := Sum.inl ()
def blockVertex (b : Block) (i : Label) : Vertex := Sum.inr (Sum.inl (b, i))
def endVertex (t : Leaf) : Vertex := Sum.inr (Sum.inr t)

def rank : Vertex → ℕ
  | .inl _ => 0
  | .inr (.inl (b, i)) => 1 + 5 * b.val + i.val
  | .inr (.inr t) => 76 + t.val

def Forward : Vertex → Vertex → Prop
  | .inl _, .inr (.inl (b, _)) => b = 0
  | .inr (.inl (b, i)), .inr (.inl (c, j)) =>
    (b = c ∧ i < j) ∨ (0 < c.val ∧ b.val = (c.val - 1) / 2 ∧ j ≤ i)
  | .inr (.inl (b, _)), .inr (.inr t) => b = leaf t
  | _, _ => False

instance : DecidableRel Forward := fun u v => by
  rcases u with ⟨⟩ | ⟨b, i⟩ | t <;> rcases v with ⟨⟩ | ⟨c, j⟩ | t' <;>
    unfold Forward <;> infer_instance

theorem rank_injective : Function.Injective rank := by
  intro u v h
  rcases u with ⟨⟩ | ⟨b, i⟩ | t <;> rcases v with ⟨⟩ | ⟨c, j⟩ | t' <;>
    simp only [rank] at h
  all_goals try first | rfl | omega
  · have hb : b = c := Fin.ext (by omega)
    have hi : i = j := Fin.ext (by omega)
    simp [hb, hi]
  · have ht : t = t' := Fin.ext (by omega)
    simp [ht]

theorem forward_rank {u v : Vertex} (h : Forward u v) : rank u < rank v := by
  rcases u with ⟨⟩ | ⟨b, i⟩ | t <;> rcases v with ⟨⟩ | ⟨c, j⟩ | t' <;>
    simp only [rank, Forward] at h ⊢
  · omega
  · rcases h with ⟨rfl, h⟩ | ⟨hc, hp, hj⟩
    · exact Nat.add_lt_add_left h _
    · omega
  · omega

def graph : SimpleGraph Vertex where
  Adj u v := Forward u v ∨ Forward v u
  symm := ⟨fun _ _ h => Or.symm h⟩
  loopless := ⟨fun _ h => h.elim (fun h => (forward_rank h).false) (fun h => (forward_rank h).false)⟩

instance : DecidableRel graph.Adj := fun u v =>
  inferInstanceAs (Decidable (Forward u v ∨ Forward v u))

theorem forward_iff_adj_rank {u v : Vertex} : Forward u v ↔ graph.Adj u v ∧ rank u < rank v :=
  ⟨fun h => ⟨Or.inl h, forward_rank h⟩, fun ⟨h, hr⟩ =>
    h.resolve_right fun hr' => hr.not_gt (forward_rank hr')⟩

theorem forward_blocks {b c : Block} {i j : Label} :
    Forward (blockVertex b i) (blockVertex c j) ↔
      (b = c ∧ i < j) ∨ (∃ s : Slab, b = parent s ∧ c = child s ∧ j ≤ i) := by
  change ((b = c ∧ i < j) ∨ (0 < c.val ∧ b.val = (c.val - 1) / 2 ∧ j ≤ i)) ↔ _
  constructor
  · rintro (h | ⟨hc, hb, hj⟩)
    · exact Or.inl h
    · let s : Slab := ⟨c.val - 1, by omega⟩
      exact Or.inr ⟨s, Fin.ext hb, Fin.ext (by dsimp [child, s]; omega), hj⟩
  · rintro (h | ⟨s, rfl, rfl, hj⟩)
    · exact Or.inl h
    · exact Or.inr ⟨Nat.succ_pos _, by simp [parent, child], hj⟩

/-- These are the five types of ordered triangles. The labels before the
singleton in an old-pair triangle are at least the singleton label, and the
labels after it in a new-pair triangle are at most the singleton label. -/
inductive OrientedTriangle : Vertex → Vertex → Vertex → Prop where
  | internal (b : Block) (i j k : Label) (hij : i < j) (hjk : j < k) :
      OrientedTriangle (blockVertex b i) (blockVertex b j) (blockVertex b k)
  | old (s : Slab) (i j k : Label) (hij : i < j) (hki : k ≤ i) :
      OrientedTriangle (blockVertex (parent s) i) (blockVertex (parent s) j) (blockVertex (child s) k)
  | young (s : Slab) (i j k : Label) (hjk : j < k) (hki : k ≤ i) :
      OrientedTriangle (blockVertex (parent s) i) (blockVertex (child s) j) (blockVertex (child s) k)
  | start (i j : Label) (hij : i < j) :
      OrientedTriangle startVertex (blockVertex 0 i) (blockVertex 0 j)
  | finish (t : Leaf) (i j : Label) (hij : i < j) :
      OrientedTriangle (blockVertex (leaf t) i) (blockVertex (leaf t) j) (endVertex t)

private theorem parent_lt_child (s : Slab) : (parent s).val < (child s).val := by
  dsimp [parent, child]
  omega

private theorem child_injective : Function.Injective child := by
  intro s t h
  apply Fin.ext
  have e := congrArg Fin.val h
  dsimp [child] at e
  omega

private theorem within_of_same {b : Block} {i j : Label} :
    Forward (blockVertex b i) (blockVertex b j) ↔ i < j := by
  rw [forward_blocks]
  constructor
  · rintro (h | ⟨s, hp, hc, _⟩)
    · exact h.2
    · exact ((parent_lt_child s).ne (congrArg Fin.val (hp.symm.trans hc))).elim
  · exact fun h => Or.inl ⟨rfl, h⟩

theorem orientedTriangle_iff {u v w : Vertex} :
    OrientedTriangle u v w ↔ Forward u v ∧ Forward v w ∧ Forward u w := by
  constructor
  · intro ht
    cases ht with
    | internal b i j k hij hjk =>
      exact ⟨within_of_same.mpr hij, within_of_same.mpr hjk, within_of_same.mpr (hij.trans hjk)⟩
    | old s i j k hij hki =>
      exact ⟨within_of_same.mpr hij, forward_blocks.mpr (Or.inr ⟨s, rfl, rfl, hki.trans hij.le⟩),
        forward_blocks.mpr (Or.inr ⟨s, rfl, rfl, hki⟩)⟩
    | young s i j k hjk hki =>
      exact ⟨forward_blocks.mpr (Or.inr ⟨s, rfl, rfl, hjk.le.trans hki⟩), within_of_same.mpr hjk,
        forward_blocks.mpr (Or.inr ⟨s, rfl, rfl, hki⟩)⟩
    | start i j h =>
      exact ⟨rfl, within_of_same.mpr h, rfl⟩
    | finish t i j h =>
      exact ⟨within_of_same.mpr h, rfl, rfl⟩
  · intro ⟨huv, hvw, huw⟩
    rcases u with ⟨⟩ | ⟨a, i⟩ | t <;> rcases v with ⟨⟩ | ⟨b, j⟩ | t' <;>
      rcases w with ⟨⟩ | ⟨c, k⟩ | t'' <;> try contradiction
    · change b = 0 at huv
      change c = 0 at huw
      subst b
      subst c
      exact .start j k (within_of_same.mp hvw)
    · obtain h₁ | ⟨s, ha, hc, hki⟩ := forward_blocks.mp huw
      · obtain h₂ | ⟨s, hb, hs, hkj⟩ := forward_blocks.mp hvw
        · obtain ⟨rfl, hik⟩ := h₁
          obtain ⟨rfl, hjk⟩ := h₂
          exact .internal _ i j k (within_of_same.mp huv) hjk
        · have hbc : b.val < c.val := by simpa [hb, hs] using parent_lt_child s
          have hab := forward_rank huv
          have ha := h₁.1
          simp only [rank] at hab
          subst a
          omega
      · obtain h₂ | ⟨t, hb, ht, hkj⟩ := forward_blocks.mp hvw
        · obtain ⟨hb, hjk⟩ := h₂
          subst b
          subst c
          subst a
          exact .young s i j k hjk hki
        · have he : s = t := child_injective (hc.symm.trans ht)
          subst t
          subst a
          subst b
          subst c
          exact .old s i j k (within_of_same.mp huv) hki
    · change a = leaf t'' at huw
      change b = leaf t'' at hvw
      subst a
      subst b
      exact .finish t'' i j (within_of_same.mp huv)

def older (v : Vertex) : Finset Vertex := univ.filter (fun u => Forward u v)

private theorem olderCard (v : Vertex) (h : 6 ≤ rank v) : (older v).card = 5 := by
  revert v
  decide

def IsCliqueIn (s : Finset Vertex) : Prop :=
  ∀ u ∈ s, ∀ v ∈ s, u ≠ v → graph.Adj u v

instance (s : Finset Vertex) : Decidable (IsCliqueIn s) :=
  inferInstanceAs (Decidable (∀ u ∈ s, ∀ v ∈ s, u ≠ v → graph.Adj u v))

private theorem adj_block_same (b : Block) {i j : Label} (h : i ≠ j) :
    graph.Adj (blockVertex b i) (blockVertex b j) := by
  rcases lt_or_gt_of_ne h with h | h
  · exact Or.inl (within_of_same.mpr h)
  · exact Or.inr (within_of_same.mpr h)

private theorem zero_not_child (s : Slab) : (0 : Block) ≠ child s := by
  intro e
  have h := congrArg Fin.val e
  change 0 = s.val + 1 at h
  omega

private theorem olderClique (v : Vertex) : IsCliqueIn (older v) := by
  intro a ha b hb hne
  have fa : Forward a v := (mem_filter.mp ha).2
  have fb : Forward b v := (mem_filter.mp hb).2
  rcases v with ⟨⟩ | ⟨c, k⟩ | t
  · rcases a with ⟨⟩ | ⟨i, j⟩ | q <;> exact False.elim fa
  · rcases a with ⟨⟩ | ⟨a, i⟩ | r <;> rcases b with ⟨⟩ | ⟨b, j⟩ | s <;>
      try first | exact False.elim (hne rfl) | exact False.elim fa | exact False.elim fb
    · change c = 0 at fa
      subst c
      rcases forward_blocks.mp fb with ⟨h, _⟩ | ⟨s, _, hs, _⟩
      · subst b
        exact Or.inl rfl
      · exact (zero_not_child s hs).elim
    · change c = 0 at fb
      subst c
      rcases forward_blocks.mp fa with ⟨h, _⟩ | ⟨s, _, hs, _⟩
      · subst a
        exact Or.inr rfl
      · exact (zero_not_child s hs).elim
    · rcases forward_blocks.mp fa with ⟨ha, hi⟩ | ⟨s, ha, hsc, hi⟩ <;>
        rcases forward_blocks.mp fb with ⟨hb, hj⟩ | ⟨t, hb, htc, hj⟩
      · subst a
        subst b
        exact adj_block_same c (fun h => hne (congrArg (blockVertex c) h))
      · subst a
        exact Or.inr (forward_blocks.mpr (Or.inr ⟨t, hb, htc, hi.le.trans hj⟩))
      · subst b
        exact Or.inl (forward_blocks.mpr (Or.inr ⟨s, ha, hsc, hj.le.trans hi⟩))
      · have hst := child_injective (hsc.symm.trans htc)
        subst t
        subst a
        subst b
        exact adj_block_same (parent s) (fun h => hne (congrArg (blockVertex (parent s)) h))
  · rcases a with ⟨⟩ | ⟨a, i⟩ | r <;> rcases b with ⟨⟩ | ⟨b, j⟩ | s <;>
      try first | exact False.elim fa | exact False.elim fb
    change a = leaf t at fa
    change b = leaf t at fb
    subst a
    subst b
    exact adj_block_same (leaf t) (fun h => hne (congrArg (blockVertex (leaf t)) h))

theorem initial_clique : IsCliqueIn (univ.filter (fun v : Vertex => rank v < 6)) := by decide

/-- The insertion order starts with K6, and each subsequent vertex has exactly
five older neighbors forming a clique. -/
theorem is_five_tree : (univ.filter (fun v : Vertex => rank v < 6)).card = 6 ∧
    IsCliqueIn (univ.filter (fun v : Vertex => rank v < 6)) ∧
    ∀ v, 6 ≤ rank v → (older v).card = 5 ∧ IsCliqueIn (older v) :=
  ⟨by decide, initial_clique, fun v h => ⟨olderCard v h, olderClique v⟩⟩


def divergence (q : Current) : Imbalance := fun i => ∑ j, q i j

def internalBoundary (p : Fill) (b : Block) : Current :=
  fun i j => (∑ k, p.2 b k i j) +
      (∑ a ∈ univ.filter (fun a => entering b a), projectSide (p.1 a) i j) -
      ∑ a ∈ univ.filter (fun a => leaving b a), projectSide (p.1 a) i j

private theorem internalBoundary_skew {p : Fill} (hp : ValidFill p) (b : Block) :
    SkewCurrent (internalBoundary p b) := by
  intro i j
  have hi (k : Label) : p.2 b k j i = -p.2 b k i j := (hp.2 b k j i).2
  have hs (a : Site) : projectSide (p.1 a) j i = -projectSide (p.1 a) i j :=
    projectSide_skew (validSide_skew (hp.1 a)) i j
  simp only [internalBoundary, hi, hs, sum_neg_distrib]
  ring

private theorem crossBoundary_zero {p : Fill} (hp : ValidFill p) (s : Slab) {i j : Label}
    (h : i < j) : crossBoundary (p.1 (oldSite s)) (p.1 (newSite s)) i j = 0 := by
  have ho : OldTriangles (p.1 (oldSite s)) := hp.1 (oldSite s)
  have hn : NewTriangles (p.1 (newSite s)) := hp.1 (newSite s)
  simp [crossBoundary, fun k => ho.2 j i k ((min_le_left i k).trans_lt h),
    fun k => hn.2 i j k (h.trans_le (le_max_left j k))]

/-- Convert the oriented cap, slab and internal-edge values to values on the
graph's forward edges. Each edge has exactly one such coordinate. -/
def edgeCoordinates (start : Imbalance) (finish : Leaf → Imbalance)
    (cross : Slab → Current) (internal : Block → Current) : Vertex → Vertex → ℝ
  | .inl _, .inr (.inl (b, i)) => if b = 0 then start i else 0
  | .inr (.inl (b, i)), .inr (.inr t) => if b = leaf t then finish t i else 0
  | .inr (.inl (b, i)), .inr (.inl (c, j)) =>
      if b = c then internal b i j
      else ∑ s : Slab, if parent s = b ∧ child s = c then cross s i j else 0
  | _, _ => 0

/-- Triangle-to-edge boundary in the orientation determined by the insertion
order, before division by the weight scaling factor. -/
def edgeBoundary (p : Fill) : Vertex → Vertex → ℝ :=
  edgeCoordinates (divergence (projectSide (p.1 startSite)))
    (fun t => divergence (projectSide (p.1 (endSite t))))
    (fun s => crossBoundary (p.1 (oldSite s)) (p.1 (newSite s)))
    (internalBoundary p)

def laneFlow (z : MultiDemand) : Vertex → Vertex → ℝ :=
  edgeCoordinates (demands z startSite) (fun t => demands z (endSite t))
    (fun s => diagonal (demands z (oldSite s))) 0

private theorem edgeCoordinates_cross (start : Imbalance) (finish : Leaf → Imbalance)
    (cross : Slab → Current) (internal : Block → Current) (s : Slab) (i j : Label) :
    edgeCoordinates start finish cross internal (blockVertex (parent s) i)
      (blockVertex (child s) j) = cross s i j := by
  have hne : parent s ≠ child s := fun h => (parent_lt_child s).ne (congrArg Fin.val h)
  have he (t : Slab) : parent t = parent s ∧ child t = child s ↔ t = s :=
    ⟨fun h => child_injective h.2, fun h => by simp [h]⟩
  simp [edgeCoordinates, blockVertex, hne, he]

/-- The coordinate equations are precisely the equality of the oriented
triangle boundary and the required lane circulation on every edge. -/
theorem fills_iff_edgeBoundary {p : Fill} {z : MultiDemand} (hp : ValidFill p) :
    Fills p z ↔ ∀ u v, Forward u v → edgeBoundary p u v = laneFlow z u v := by
  constructor
  · intro h u v huv
    rcases u with ⟨⟩ | ⟨a, i⟩ | t <;> rcases v with ⟨⟩ | ⟨b, j⟩ | t' <;> try contradiction
    · change b = 0 at huv
      subst b
      simpa [edgeBoundary, laneFlow, edgeCoordinates, divergence] using h.start j
    · rcases forward_blocks.mp huv with ⟨hab, _⟩ | ⟨s, rfl, rfl, _⟩
      · subst b
        have h₀ := sub_eq_zero.mpr (h.internal a i j)
        simpa [edgeBoundary, laneFlow, edgeCoordinates, internalBoundary] using h₀
      · change edgeBoundary p (blockVertex (parent s) i) (blockVertex (child s) j) =
          laneFlow z (blockVertex (parent s) i) (blockVertex (child s) j)
        rw [edgeBoundary, laneFlow, edgeCoordinates_cross, edgeCoordinates_cross, h.slab s]
    · change a = leaf t' at huv
      subst a
      simpa [edgeBoundary, laneFlow, edgeCoordinates, divergence] using h.finish t' i
  · intro h
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i
      simpa [edgeBoundary, laneFlow, edgeCoordinates, divergence, startVertex, blockVertex] using
        h startVertex (blockVertex 0 i) rfl
    · intro t i
      simpa [edgeBoundary, laneFlow, edgeCoordinates, divergence, blockVertex, endVertex] using
        h (blockVertex (leaf t) i) (endVertex t) rfl
    · intro s
      funext i j
      by_cases hij : j ≤ i
      · have he := h (blockVertex (parent s) i) (blockVertex (child s) j)
          (forward_blocks.mpr (Or.inr ⟨s, rfl, rfl, hij⟩))
        rwa [edgeBoundary, laneFlow, edgeCoordinates_cross, edgeCoordinates_cross] at he
      · have hl : i < j := lt_of_not_ge hij
        simp [crossBoundary_zero hp s hl, diagonal, hl.ne]
    · intro b i j
      apply sub_eq_zero.mp
      change internalBoundary p b i j = 0
      have hsk := internalBoundary_skew hp b
      have he {i j : Label} (hij : i < j) : internalBoundary p b i j = 0 := by
        simpa [edgeBoundary, laneFlow, edgeCoordinates, blockVertex] using
          h (blockVertex b i) (blockVertex b j) (within_of_same.mpr hij)
      rcases lt_trichotomy i j with hij | rfl | hij
      · exact he hij
      · linarith [hsk i i]
      · rw [hsk j i, he hij, neg_zero]


/-- Every positive-weight edge belongs to one lane. The old and new sites of a
slab encode the same edge flows. The balance equations use units of 1/200. -/
structure LaneConserving (f : Site → Imbalance) : Prop where
  sameSlab : ∀ s, f (oldSite s) = f (newSite s)
  terminal : ∀ t, ∑ i, f (endSite t) i = 0
  balance : ∀ b, (∑ a ∈ univ.filter (fun a => entering b a), f a) =
    ∑ a ∈ univ.filter (fun a => leaving b a), f a

def LaneBounded (f : Site → Imbalance) : Prop :=
  ∀ a i, |f a i| ≤ (multiplicity a : ℝ)

private theorem demands_end (z : MultiDemand) (t : Leaf) : demands z (endSite t) = (z t).val := by
  simp [demands, aggregate, endSite, below, sum_filter, sum_ite_eq]

private theorem demands_conserve (z : MultiDemand) : LaneConserving (demands z) := by
  refine ⟨fun _ => rfl, fun t => by rw [demands_end]; exact demand_sum (z t), fun b => ?_⟩
  funext i
  let q (t : Leaf) : Current := fun i _ => (z t).val i
  have h := congrFun (congrFun (aggregate_balance b q) i) (0 : Label)
  simpa [demands, aggregate, q, sum_apply] using h

private def incomingSite (b : Block) : Site :=
  if h : b.val = 0 then startSite else newSite ⟨b.val - 1, by omega⟩

private theorem incoming_start : incomingSite (0 : Block) = startSite := by decide

private theorem incoming_child (s : Slab) : incomingSite (child s) = newSite s := by
  revert s
  decide

private theorem entering_filter (b : Block) :
    univ.filter (fun a => entering b a) = {incomingSite b} := by
  revert b
  decide

private theorem leaving_cases (b : Block) (a : Site) (h : leaving b a = true) :
    (∃ t, a = endSite t) ∨ ∃ s, a = oldSite s ∧ b.val < (child s).val := by
  rcases a with u | t | s | s
  · exact False.elim (by contradiction)
  · exact Or.inl ⟨t,rfl⟩
  · change decide (parent s = b) = true at h
    rw [← of_decide_eq_true h]
    exact Or.inr ⟨s, rfl, parent_lt_child s⟩
  · exact False.elim (by contradiction)

private theorem demand_unique (f g : Site → Imbalance) (hf : LaneConserving f)
    (hg : LaneConserving g) (h : ∀ t, f (endSite t) = g (endSite t)) : f = g := by
  have hin (n : ℕ) (b : Block) (hb : 15 - b.val = n) :
      f (incomingSite b) = g (incomingSite b) := by
    induction n using Nat.strong_induction_on generalizing b with
    | h n ih =>
      have hf' := hf.balance b
      have hg' := hg.balance b
      rw [entering_filter, sum_singleton] at hf' hg'
      rw [hf', hg']
      apply sum_congr rfl
      intro a ha
      rcases leaving_cases b a (mem_filter.mp ha).2 with ⟨t,rfl⟩ | ⟨s,rfl,hbs⟩
      · exact h t
      · rw [hf.sameSlab, hg.sameSlab, ← incoming_child]
        exact ih _ (by have := (child s).isLt; omega) (child s) rfl
  funext a
  rcases a with u | t | s | s
  · cases u
    change f startSite = g startSite
    simpa only [incoming_start] using hin _ 0 rfl
  · exact h t
  · change f (oldSite s) = g (oldSite s)
    rw [hf.sameSlab, hg.sameSlab, ← incoming_child]
    exact hin _ (child s) rfl
  · change f (newSite s) = g (newSite s)
    simpa only [incoming_child] using hin _ (child s) rfl

private theorem multiplicity_end (t : Leaf) : multiplicity (endSite t) = 1 := by
  have he : univ.filter (fun t' => below (endSite t) t') = {t} := by
    ext t'
    simp [endSite, below, eq_comm]
  simp [multiplicity, aggregate, he]

private theorem demands_bounded {z : MultiDemand} (hz : admissible z) :
    LaneBounded (demands z) := by
  intro a i
  simp only [demands, aggregate, sum_apply]
  refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum fun t _ => hz t i).trans_eq ?_)
  simp [multiplicity, aggregate, sum_const, nsmul_eq_mul]

/-- A bounded lane circulation is determined by its eight balanced terminal
demands. Conversely all eight balanced terminal demands are independent. -/
theorem lane_coordinates (f : Site → Imbalance) :
    LaneConserving f ∧ LaneBounded f ↔ ∃ z, admissible z ∧ demands z = f := by
  constructor
  · rintro ⟨hf, hb⟩
    let z (t : Leaf) : Demand := ⟨f (endSite t), LinearMap.mem_ker.mpr (by
      rw [total_apply, hf.terminal t])⟩
    refine ⟨z, fun t i => ?_, ?_⟩
    · simpa [z, multiplicity_end] using hb (endSite t) i
    · apply demand_unique _ f (demands_conserve z) hf
      intro t
      exact demands_end z t
  · rintro ⟨z, hz, rfl⟩
    exact ⟨demands_conserve z, demands_bounded hz⟩


/-- A common triangle envelope tested on the forward edges of the graph.
The eight terminal demands parametrize all allowed lane circulations. -/
def GraphEnvelope (c : Fill) : Prop :=
  ∀ z, admissible z → ∃ p, ValidFill p ∧ covers c p ∧
    ∀ u v, Forward u v → edgeBoundary p u v = laneFlow z u v

def GraphLinearEnvelope (c : Fill) : Prop :=
  ∃ L : MultiDemand →ₗ[ℝ] Fill, ∀ z, admissible z → ValidFill (L z) ∧ covers c (L z) ∧
    ∀ u v, Forward u v → edgeBoundary (L z) u v = laneFlow z u v

theorem graphEnvelope_iff (c : Fill) : GraphEnvelope c ↔ Unrestricted c := by
  constructor
  · intro h z hz
    obtain ⟨p, hv, hc, hp⟩ := h z hz
    exact ⟨p, hv, (fills_iff_edgeBoundary hv).mpr hp, hc⟩
  · intro h z hz
    obtain ⟨p, hv, hp, hc⟩ := h z hz
    exact ⟨p, hv, hc, (fills_iff_edgeBoundary hv).mp hp⟩

theorem graphLinearEnvelope_iff (c : Fill) : GraphLinearEnvelope c ↔ Linear c := by
  constructor
  · rintro ⟨L, hL⟩
    refine ⟨L, fun z hz => ?_⟩
    obtain ⟨hv, hc, hp⟩ := hL z hz
    exact ⟨hv, (fills_iff_edgeBoundary hv).mpr hp, hc⟩
  · rintro ⟨L, hL⟩
    refine ⟨L, fun z hz => ?_⟩
    obtain ⟨hv, hp, hc⟩ := hL z hz
    exact ⟨hv, hc, (fills_iff_edgeBoundary hv).mp hp⟩

end
end FiveLaneRouting.BinaryStaircase
