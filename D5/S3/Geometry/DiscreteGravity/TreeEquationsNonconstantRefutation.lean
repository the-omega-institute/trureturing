/- GID: D5/S3/Geometry/DiscreteGravity/TreeEquationsNonconstantRefutation
   generality: I
   mirror-B: D5/B/S3/Geometry/DiscreteGravity/TreeEquationsNonconstantRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Geometry/DiscreteGravity/TreeEquationsNonconstantRefutation.claim; result=D5/S3/Geometry/DiscreteGravity/TreeEquationsNonconstantRefutation.result; claim=D5/S3/Geometry/DiscreteGravity/TreeEquationsNonconstantRefutation.claim
   digest: A positive nonconstant solution on a cubic tree refutes the tEoM conjecture. -/

import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring.RingNF

/-! The tree equations of motion of Huang, Stoica, Xia and Zhong, arXiv:2006.06716v1,
admit a positive nonconstant setting on a bi-infinite spine with binary branches. -/

set_option autoImplicit false
set_option linter.style.longLine false

noncomputable section

open scoped BigOperators

namespace D5.S3.Geometry.DiscreteGravity.TreeEquationsNonconstantRefutation

/-- The source's sum of reciprocal incident edge lengths. -/
def cVal {v : Type} (g : SimpleGraph v) [g.LocallyFinite]
    (ell : v → v → ℝ) (i : v) : ℝ :=
  ∑ j ∈ g.neighborFinset i, 1 / ell i j

/-- The source's sum of reciprocal squared incident edge lengths. -/
def dVal {v : Type} (g : SimpleGraph v) [g.LocallyFinite]
    (ell : v → v → ℝ) (i : v) : ℝ :=
  ∑ j ∈ g.neighborFinset i, 1 / ell i j ^ 2

/-- The ratio occurring in the tree equation of motion. -/
def ratio {v : Type} (g : SimpleGraph v) [g.LocallyFinite]
    (ell : v → v → ℝ) (i : v) : ℝ := cVal g ell i / dVal g ell i

/-- The tree equation of motion on the edge `ij`. -/
def tEoM {v : Type} (g : SimpleGraph v) [g.LocallyFinite]
    (ell : v → v → ℝ) (i j : v) : ℝ :=
  (1 / ell i j) * (ratio g ell i ^ 2 + ratio g ell j ^ 2) -
    ratio g ell i - ratio g ell j

/-- The positive-length nonconstant-solution conjecture on every realization of T₂. -/
def claim : Prop :=
  ∀ (v : Type) (g : SimpleGraph v) [g.LocallyFinite] [DecidableRel g.Adj],
    g.IsTree → (∀ i, g.degree i = 3) → ∀ ell : v → v → ℝ,
    (∀ i j, g.Adj i j → ell i j = ell j i) →
    (∀ i j, g.Adj i j → 0 < ell i j) →
    (∀ i j, g.Adj i j → tEoM g ell i j = 0) →
    ∃ c, ∀ i j, g.Adj i j → ell i j = c

private def parent : Sum ℤ (ℤ × List Bool) → Sum ℤ (ℤ × List Bool) :=
  Sum.elim (fun n => Sum.inl (n - 1))
    (fun p => p.2.casesOn (Sum.inl p.1) (fun _ w => Sum.inr (p.1, w)))

private def rank : Sum ℤ (ℤ × List Bool) → ℤ :=
  Sum.elim id (fun p => p.1 + 1 + p.2.length)

private lemma parent_rank (i : Sum ℤ (ℤ × List Bool)) :
    rank (parent i) = rank i - 1 := by
  rcases i with n | ⟨n, w⟩
  · rfl
  · cases w <;> simp [parent.eq_1, rank.eq_1]
    omega

private def graph : SimpleGraph (Sum ℤ (ℤ × List Bool)) :=
  SimpleGraph.fromRel (fun i j => parent i = j)

private lemma graph_adj (i j : Sum ℤ (ℤ × List Bool)) :
    graph.Adj i j ↔ parent i = j ∨ parent j = i := by
  rw [graph.eq_1, SimpleGraph.fromRel_adj]
  constructor
  · exact And.right
  · intro h
    refine ⟨?_, h⟩
    intro he
    subst j
    have hr := parent_rank i
    rcases h with h | h <;> rw [h] at hr <;> omega

private def neighbors (i : Sum ℤ (ℤ × List Bool)) : Finset (Sum ℤ (ℤ × List Bool)) :=
  Sum.elim (fun n => {Sum.inl (n - 1), Sum.inl (n + 1), Sum.inr (n, [])})
    (fun p => {parent (Sum.inr p), Sum.inr (p.1, false :: p.2),
      Sum.inr (p.1, true :: p.2)}) i

private lemma mem_neighbors (i j : Sum ℤ (ℤ × List Bool)) :
    j ∈ neighbors i ↔ graph.Adj i j := by
  rcases i with n | ⟨n, w⟩ <;> rcases j with m | ⟨m, z⟩
  · simp [neighbors.eq_1, graph_adj, parent.eq_1]
    omega
  · cases z <;> simp [neighbors.eq_1, graph_adj, parent.eq_1, eq_comm]
  · cases w <;> simp [neighbors.eq_1, graph_adj, parent.eq_1, eq_comm]
  · cases w <;> cases z <;> simp [neighbors.eq_1, graph_adj, parent.eq_1]
    all_goals aesop

private instance graph_finite : graph.LocallyFinite :=
  fun i => Fintype.ofFinset (neighbors i) (mem_neighbors i)

private lemma neighbor_eq (i : Sum ℤ (ℤ × List Bool)) :
    graph.neighborFinset i = neighbors i := by
  exact Set.toFinset_ofFinset (neighbors i) (mem_neighbors i)

private lemma parent_child_ne (n : ℤ) (w : List Bool) (b : Bool) :
    parent (Sum.inr (n, w)) ≠ Sum.inr (n, b :: w) := by
  intro h
  have hr := parent_rank (Sum.inr (n, w))
  rw [h] at hr
  simp [rank.eq_1] at hr
  omega

private lemma graph_degree (i : Sum ℤ (ℤ × List Bool)) : graph.degree i = 3 := by
  rw [← graph.card_neighborFinset_eq_degree, neighbor_eq]
  rcases i with n | ⟨n, w⟩
  · simp [neighbors.eq_1, show n - 1 ≠ n + 1 by omega]
  · simp [neighbors.eq_1, parent_child_ne]

private lemma graph_connected : graph.Connected := by
  have hs : ∀ n : ℤ, graph.Reachable (Sum.inl n) (Sum.inl 0) := by
    intro n
    induction n using Int.induction_on with
    | zero => exact .rfl
    | succ n ih =>
      exact (show graph.Adj (Sum.inl ((n : ℤ) + 1)) (Sum.inl n) from
        (graph_adj _ _).mpr (Or.inl (by simp [parent.eq_1]))).reachable.trans ih
    | pred n ih =>
      exact (show graph.Adj (Sum.inl (-(n : ℤ) - 1)) (Sum.inl (-n)) from
        (graph_adj _ _).mpr (Or.inr rfl)).reachable.trans ih
  have hb : ∀ (n : ℤ) (w : List Bool),
      graph.Reachable (Sum.inr (n, w)) (Sum.inl n) := by
    intro n w
    induction w with
    | nil => exact (show graph.Adj (Sum.inr (n, [])) (Sum.inl n) from (graph_adj _ _).mpr (Or.inl rfl)).reachable
    | cons b w ih =>
      exact (show graph.Adj (Sum.inr (n, b :: w)) (Sum.inr (n, w)) from
        (graph_adj _ _).mpr (Or.inl rfl)).reachable.trans ih
  apply (graph.connected_iff_exists_forall_reachable).mpr
  refine ⟨Sum.inl 0, ?_⟩
  rintro (n | ⟨n, w⟩)
  · exact (hs n).symm
  · exact ((hb n w).trans (hs n)).symm

private lemma graph_acyclic : graph.IsAcyclic := by
  have down : ∀ x y, graph.Adj x y → rank y ≤ rank x → y = parent x := by
    intro x y h hle
    rcases (graph_adj x y).mp h with h | h
    · exact h.symm
    · have hr := parent_rank y
      rw [h] at hr
      omega
  intro v c hc
  classical
  obtain ⟨x, hx, hm⟩ := Finset.exists_max_image c.support.toFinset rank
    ⟨v, by simp⟩
  have hx : x ∈ c.support := List.mem_toFinset.mp hx
  let p := c.rotate x hx
  have hp : p.IsCycle := hc.rotate hx
  have hmax : ∀ y ∈ p.support, rank y ≤ rank x := by
    intro y hy
    exact hm y (List.mem_toFinset.mpr ((c.mem_support_rotate_iff x hx).mp hy))
  apply hp.snd_ne_penultimate
  exact (down x p.snd (p.adj_snd hp.not_nil)
    (hmax _ (p.getVert_mem_support 1))).trans
    (down x p.penultimate (p.adj_penultimate hp.not_nil).symm
      (hmax _ (p.getVert_mem_support (p.length - 1)))).symm

private lemma graph_tree : graph.IsTree := ⟨graph_connected, graph_acyclic⟩

private def lengths : Sum ℤ (ℤ × List Bool) → Sum ℤ (ℤ × List Bool) → ℝ :=
  Sum.elim
    (fun n => Sum.elim (fun m => (5 / 3 : ℝ) * ((2 : ℝ) ^ (min n m)))
      (fun p => ((2 : ℝ) ^ p.1)))
    (fun p => Sum.elim (fun _ => ((2 : ℝ) ^ p.1)) (fun q => ((2 : ℝ) ^ (min p.1 q.1))))

private lemma lengths_symmetric (i j : Sum ℤ (ℤ × List Bool)) :
    graph.Adj i j → lengths i j = lengths j i := by
  intro _
  rcases i with n | ⟨n, w⟩ <;> rcases j with m | ⟨m, z⟩ <;>
    simp [lengths.eq_1, min_comm]

private lemma lengths_positive (i j : Sum ℤ (ℤ × List Bool)) :
    graph.Adj i j → 0 < lengths i j := by
  intro _
  rcases i with n | ⟨n, w⟩ <;> rcases j with m | ⟨m, z⟩ <;>
    simp only [lengths.eq_1, Sum.elim_inl, Sum.elim_inr]
  · exact mul_pos (by norm_num) (zpow_pos (by norm_num) _)
  all_goals exact zpow_pos (by norm_num) _

private lemma ratio_spine (n : ℤ) : ratio graph lengths (Sum.inl n) = ((2 : ℝ) ^ n) := by
  have hn := zpow_ne_zero n (by norm_num : (2 : ℝ) ≠ 0)
  change (∑ j ∈ graph.neighborFinset (Sum.inl n), 1 / lengths (Sum.inl n) j) /
    (∑ j ∈ graph.neighborFinset (Sum.inl n), 1 / lengths (Sum.inl n) j ^ 2) = ((2 : ℝ) ^ n)
  simp [neighbor_eq, neighbors.eq_1, lengths.eq_1,
    show n - 1 ≠ n + 1 by omega, zpow_sub_one₀ (by norm_num : (2 : ℝ) ≠ 0)]
  field_simp
  ring

private lemma ratio_branch (n : ℤ) (w : List Bool) :
    ratio graph lengths (Sum.inr (n, w)) = ((2 : ℝ) ^ n) := by
  have hn := zpow_ne_zero n (by norm_num : (2 : ℝ) ≠ 0)
  have hp : lengths (Sum.inr (n, w)) (parent (Sum.inr (n, w))) = ((2 : ℝ) ^ n) := by
    cases w <;> simp [lengths.eq_1, parent.eq_1]
  change (∑ j ∈ graph.neighborFinset (Sum.inr (n, w)), 1 / lengths (Sum.inr (n, w)) j) /
    (∑ j ∈ graph.neighborFinset (Sum.inr (n, w)),
      1 / lengths (Sum.inr (n, w)) j ^ 2) = ((2 : ℝ) ^ n)
  simp [neighbor_eq, neighbors.eq_1, parent_child_ne, hp]
  simp [lengths.eq_1]
  field_simp

private lemma residuals (i j : Sum ℤ (ℤ × List Bool)) :
    graph.Adj i j → tEoM graph lengths i j = 0 := by
  have hp : ∀ x, tEoM graph lengths x (parent x) = 0 := by
    intro x
    change (1 / lengths x (parent x)) *
      (ratio graph lengths x ^ 2 + ratio graph lengths (parent x) ^ 2) -
      ratio graph lengths x - ratio graph lengths (parent x) = 0
    rcases x with n | ⟨n, w⟩
    · have hn := zpow_ne_zero n (by norm_num : (2 : ℝ) ≠ 0)
      simp only [parent.eq_1, Sum.elim_inl, ratio_spine]
      simp [lengths.eq_1, zpow_sub_one₀ (by norm_num : (2 : ℝ) ≠ 0)]
      field_simp
      ring
    · have hn := zpow_ne_zero n (by norm_num : (2 : ℝ) ≠ 0)
      cases w <;> simp only [parent.eq_1, Sum.elim_inr, ratio_spine, ratio_branch]
      all_goals simp [lengths.eq_1]
      all_goals field_simp; ring
  intro h
  rcases (graph_adj i j).mp h with h | h
  · rw [← h]
    exact hp i
  · have he : graph.Adj i j := (graph_adj i j).mpr (Or.inr h)
    have hs := lengths_symmetric i j he
    have hz := hp j
    rw [h] at hz
    change (1 / lengths j i) * (ratio graph lengths j ^ 2 + ratio graph lengths i ^ 2) -
      ratio graph lengths j - ratio graph lengths i = 0 at hz
    change (1 / lengths i j) * (ratio graph lengths i ^ 2 + ratio graph lengths j ^ 2) -
      ratio graph lengths i - ratio graph lengths j = 0
    rw [hs]
    nlinarith

private lemma nonconstant :
    ¬ ∃ c, ∀ i j, graph.Adj i j → lengths i j = c := by
  rintro ⟨c, h⟩
  have hb := h (Sum.inl 0) (Sum.inr (0, [])) ((graph_adj _ _).mpr (Or.inr rfl))
  have hs := h (Sum.inl 0) (Sum.inl 1) ((graph_adj _ _).mpr (Or.inr (by norm_num [parent.eq_1])))
  norm_num [lengths.eq_1] at hb hs
  linarith

/-- The preregistered cubic tree carries a positive nonconstant tEoM solution. -/
theorem result : ¬ claim := by
  classical
  intro h
  exact nonconstant (h _ graph graph_tree graph_degree lengths
    lengths_symmetric lengths_positive residuals)

end D5.S3.Geometry.DiscreteGravity.TreeEquationsNonconstantRefutation
