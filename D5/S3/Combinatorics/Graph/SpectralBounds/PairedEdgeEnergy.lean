/- GID: D5/S3/Combinatorics/Graph/SpectralBounds/PairedEdgeEnergy
   generality: G
   mirror-B: none(waiver:covered-by-mixed-power-graft-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Reflected-pair compression for mixed edge energy. -/

import OmegaBuild.Commands
import D5.S3.Combinatorics.Graph.SpectralBounds.MixedAdjacency

/-! Omega original. Reflected-pair compression for mixed edge energy. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Matrix Finset SimpleGraph
open OmegaMath.RealRayleigh OmegaMath.MixedAdjacency
open scoped Classical

noncomputable section

namespace OmegaMath.PairedEdgeEnergy

/-- The mixed quadratic-form contribution of one undirected edge. -/
private def edgeEnergy (α a b : ℝ) : ℝ :=
  α * (a ^ 2 + b ^ 2) + 2 * (1 - α) * a * b

private theorem edgeEnergy_comm (α a b : ℝ) : edgeEnergy α a b = edgeEnergy α b a := by
  unfold edgeEnergy
  ring

private theorem edgeEnergy_nonneg {α a b : ℝ}
    (hα : 0 ≤ α) (hα' : α ≤ 1) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ edgeEnergy α a b := by
  have : 0 ≤ 1 - α := sub_nonneg.mpr hα'
  unfold edgeEnergy
  positivity

private theorem edgeEnergy_pos {α a b : ℝ}
    (hα : 0 ≤ α) (hα' : α < 1) (ha : 0 < a) (hb : 0 < b) :
    0 < edgeEnergy α a b := by
  have : 0 < 1 - α := sub_pos.mpr hα'
  unfold edgeEnergy
  positivity

private theorem edgeEnergy_le_right {α t a b : ℝ}
    (hα : 0 ≤ α) (hα' : α ≤ 1) (ht : 0 ≤ t) (ha : 0 ≤ a) (hab : a ≤ b) :
    edgeEnergy α t a ≤ edgeEnergy α t b := by
  have hdiff : 0 ≤ b - a := sub_nonneg.mpr hab
  have hsum : 0 ≤ b + a := add_nonneg (ha.trans hab) ha
  have hcoeff : 0 ≤ 1 - α := sub_nonneg.mpr hα'
  have h : 0 ≤ (b - a) * (α * (b + a) + 2 * (1 - α) * t) := by positivity
  apply sub_nonneg.mp
  convert h using 1
  unfold edgeEnergy
  ring

variable {V P W : Type*}

/-- The ordered adjacency sum counts every undirected edge twice. -/
private theorem two_energy_mixedMatrix [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (α : ℝ) (x : V → ℝ) :
    2 * energy (mixedMatrix G α) x =
      ∑ u, ∑ v, if G.Adj u v then edgeEnergy α (x u) (x v) else 0 := by
  have hs : (∑ u, ∑ v, if G.Adj u v then α * (x v)^2 else 0) =
      (∑ u, ∑ v, if G.Adj u v then α * (x u)^2 else 0) := by
    rw [Finset.sum_comm]
    exact sum_congr rfl fun u _ => sum_congr rfl fun v _ =>
      if_congr (G.adj_comm v u) rfl rfl
  have hd : α * (x ⬝ᵥ (G.degMatrix ℝ *ᵥ x)) =
      ∑ u, ∑ v, if G.Adj u v then α * (x u)^2 else 0 := by
    rw [G.dotProduct_mulVec_degMatrix, Finset.mul_sum]
    apply sum_congr rfl
    intro u _
    have he : α * ((G.degree u : ℝ) * x u * x u) = (G.degree u : ℝ) * (α * (x u)^2) := by
      ring
    rw [he, G.degree_eq_sum_if_adj, Finset.sum_mul]
    exact sum_congr rfl fun v _ => by by_cases h : G.Adj u v <;> simp [h]
  have ha : (1 - α) * (x ⬝ᵥ (G.adjMatrix ℝ *ᵥ x)) =
      ∑ u, ∑ v, if G.Adj u v then (1 - α) * (x u * x v) else 0 := by
    rw [G.dotProduct_mulVec_adjMatrix]
    simp_rw [Finset.mul_sum, mul_ite, mul_zero]
  rw [energy, mixedMatrix, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec,
    dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul, hd, ha]
  have hsplit : (∑ u, ∑ v, if G.Adj u v then edgeEnergy α (x u) (x v) else 0) =
      (∑ u, ∑ v, if G.Adj u v then α * (x u)^2 else 0) +
      (∑ u, ∑ v, if G.Adj u v then α * (x v)^2 else 0) +
      2 * (∑ u, ∑ v, if G.Adj u v then (1 - α) * (x u * x v) else 0) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine sum_congr rfl fun u _ => sum_congr rfl fun v _ => ?_
    by_cases h : G.Adj u v
    · simp only [h, ite_true, edgeEnergy]
      ring
    · simp [h]
  rw [hsplit, hs]
  ring

/-- A vertex partition labels each reflected pair by one index and its two members by Bool.
The fixed part includes the moved leaf. -/
abbrev Partition (P W V : Type*) := ((P × Bool) ⊕ W) ≃ V

abbrev left (e : Partition P W V) (i : P) : V := e (.inl (i, true))
abbrev right (e : Partition P W V) (i : P) : V := e (.inl (i, false))
abbrev fixed (e : Partition P W V) (w : W) : V := e (.inr w)

/-- Sort each reflected pair so its larger coordinate is on the left. -/
def compress (e : Partition P W V) (x : V → ℝ) (v : V) : ℝ :=
  match e.symm v with
  | .inl (i, true) => max (x (left e i)) (x (right e i))
  | .inl (i, false) => min (x (left e i)) (x (right e i))
  | .inr _ => x v

@[simp] theorem compress_left (e : Partition P W V) (x : V → ℝ) (i : P) :
    compress e x (left e i) = max (x (left e i)) (x (right e i)) := by
  simp [compress]

@[simp] theorem compress_right (e : Partition P W V) (x : V → ℝ) (i : P) :
    compress e x (right e i) = min (x (left e i)) (x (right e i)) := by
  simp [compress]

@[simp] theorem compress_fixed (e : Partition P W V) (x : V → ℝ) (w : W) :
    compress e x (fixed e w) = x (fixed e w) := by
  simp [compress]

private theorem apply_max_add_apply_min (f : ℝ → ℝ) (a b : ℝ) :
    f (max a b) + f (min a b) = f a + f b := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, min_eq_left h, add_comm]
  · rw [max_eq_left h, min_eq_right h]

private theorem sum_partition [Fintype P] [Fintype W] [Fintype V]
    (e : Partition P W V) (f : V → ℝ) :
    ∑ v, f v = (∑ i, (f (left e i) + f (right e i))) + ∑ w, f (fixed e w) := by
  rw [← e.sum_comp f, Fintype.sum_sum_type, Fintype.sum_prod_type]
  simp only [Fintype.sum_bool]

/-- Sorting preserves the squared Euclidean norm for arbitrary real input. -/
private theorem compress_sum_sq [Fintype P] [Fintype W] [Fintype V]
    (e : Partition P W V) (x : V → ℝ) :
    ∑ v, (compress e x v)^2 = ∑ v, (x v)^2 := by
  rw [sum_partition e (fun v => (compress e x v)^2), sum_partition e (fun v => (x v)^2)]
  simp only [compress_left, compress_right, compress_fixed]
  exact congrArg (fun t => t + ∑ w, (x (fixed e w))^2)
    (sum_congr rfl fun i _ => apply_max_add_apply_min (fun t => t^2) _ _)

theorem compress_unitVector [Fintype P] [Fintype W] [Fintype V]
    (e : Partition P W V) {x : V → ℝ} (hx : UnitVector x) :
    UnitVector (compress e x) := by
  unfold UnitVector at *
  rwa [compress_sum_sq e x]

/-- Structural adjacency conditions for sorting a vector from the post-transfer graph H
toward the pre-transfer graph G. The fixed index z labels the moved leaf. -/
structure Incidence (e : Partition P W V) (z : W) (G H : SimpleGraph V) : Prop where
  /-- Both graphs restrict to the same graph on the complement of the moved leaf. -/
  off_leaf : ∀ ⦃u v⦄, u ≠ fixed e z → v ≠ fixed e z → (H.Adj u v ↔ G.Adj u v)
  parallel : ∀ i j, G.Adj (left e i) (left e j) ↔ G.Adj (right e i) (right e j)
  cross : ∀ i j, G.Adj (left e i) (right e j) ↔ G.Adj (right e i) (left e j)
  cross_to_parallel : ∀ ⦃i j⦄, i ≠ j → G.Adj (left e i) (right e j) →
    G.Adj (left e i) (left e j)
  fixed_nested : ∀ i w, w ≠ z → G.Adj (fixed e w) (right e i) → G.Adj (fixed e w) (left e i)
  leaf_left : ∀ i, H.Adj (fixed e z) (left e i) ↔ G.Adj (fixed e z) (right e i)
  leaf_right : ∀ i, H.Adj (fixed e z) (right e i) ↔ G.Adj (fixed e z) (left e i)
  leaf_nested : ∀ i, G.Adj (fixed e z) (right e i) → G.Adj (fixed e z) (left e i)
  leaf_fixed : ∀ w, H.Adj (fixed e w) (fixed e z) → G.Adj (fixed e w) (fixed e z)

private theorem pair_ne_fixed (e : Partition P W V) (i : P) (b : Bool) (w : W) :
    e (.inl (i, b)) ≠ fixed e w := by
  intro h
  cases e.injective h

private theorem fixed_ne_fixed (e : Partition P W V) {w z : W} (h : w ≠ z) :
    fixed e w ≠ fixed e z := fun he => h (Sum.inr.inj (e.injective he))

/-- If the only edges between two pairs are parallel, sorting weakly increases
their total edge energy. The square terms cancel from the difference. -/
private theorem parallel_le {α : ℝ} (hα : α ≤ 1) (a b c d : ℝ) :
    edgeEnergy α a c + edgeEnergy α b d ≤
      edgeEnergy α (max a b) (max c d) + edgeEnergy α (min a b) (min c d) := by
  have hgain (a b c d : ℝ) (hab : b ≤ a) (hcd : c ≤ d) :
      edgeEnergy α a c + edgeEnergy α b d ≤ edgeEnergy α a d + edgeEnergy α b c := by
    have h : 0 ≤ 2 * (1 - α) * (a - b) * (d - c) := by
      have := sub_nonneg.mpr hα
      have := sub_nonneg.mpr hab
      have := sub_nonneg.mpr hcd
      positivity
    apply sub_nonneg.mp
    convert h using 1
    unfold edgeEnergy
    ring
  rcases le_total a b with hab | hab <;> rcases le_total c d with hcd | hcd
  · rw [max_eq_right hab, min_eq_left hab, max_eq_right hcd, min_eq_left hcd, add_comm]
  · rw [max_eq_right hab, min_eq_left hab, max_eq_left hcd, min_eq_right hcd]
    simpa only [add_comm] using hgain b a d c hab hcd
  · simpa only [max_eq_left hab, min_eq_right hab, max_eq_right hcd, min_eq_left hcd]
      using hgain a b c d hab hcd
  · rw [max_eq_left hab, min_eq_right hab, max_eq_left hcd, min_eq_right hcd]

private def twoPairEnergy (p c : Prop) (α a b u v : ℝ) : ℝ :=
  (if p then edgeEnergy α a u + edgeEnergy α b v else 0) +
    (if c then edgeEnergy α a v + edgeEnergy α b u else 0)

private theorem twoPairEnergy_le {p c : Prop} {α : ℝ} (h : c → p) (hα : α ≤ 1)
    (a b u v : ℝ) :
    twoPairEnergy p c α a b u v ≤
      twoPairEnergy p c α (max a b) (min a b) (max u v) (min u v) := by
  by_cases hc : c
  · have hp := h hc
    simp only [twoPairEnergy, hc, hp, ite_true]
    have regroup (a b u v : ℝ) :
        edgeEnergy α a u + edgeEnergy α b v + (edgeEnergy α a v + edgeEnergy α b u) =
          (edgeEnergy α a u + edgeEnergy α a v) + (edgeEnergy α b u + edgeEnergy α b v) := by
      ac_rfl
    rw [regroup a b u v, regroup (max a b) (min a b) (max u v) (min u v),
      apply_max_add_apply_min (edgeEnergy α (max a b)) u v,
      apply_max_add_apply_min (edgeEnergy α (min a b)) u v,
      apply_max_add_apply_min (fun t => edgeEnergy α t u + edgeEnergy α t v) a b]
  · by_cases hp : p
    · simpa only [twoPairEnergy, hp, hc, ite_true, ite_false, add_zero] using
        parallel_le hα a b u v
    · simp [twoPairEnergy, hp, hc]

private def onePairEnergy (p q : Prop) (α t a b : ℝ) : ℝ :=
  (if p then edgeEnergy α t a else 0) + (if q then edgeEnergy α t b else 0)

private theorem onePairEnergy_le {p q : Prop} {α t a b : ℝ}
    (h : q → p) (hα : 0 ≤ α) (hα' : α ≤ 1) (ht : 0 ≤ t) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    onePairEnergy p q α t a b ≤ onePairEnergy p q α t (max a b) (min a b) ∧
    onePairEnergy q p α t a b ≤ onePairEnergy p q α t (max a b) (min a b) := by
  by_cases hq : q
  · simp only [onePairEnergy, h hq, hq, ite_true, apply_max_add_apply_min, le_refl, and_self]
  · by_cases hp : p
    · simp only [onePairEnergy, hp, hq, ite_true, ite_false, add_zero, zero_add]
      exact ⟨edgeEnergy_le_right hα hα' ht ha (le_max_left _ _),
        edgeEnergy_le_right hα hα' ht hb (le_max_right _ _)⟩
    · simp [onePairEnergy, hp, hq]

private def edgeAt (G : SimpleGraph V) (α : ℝ) (x : V → ℝ) (u v : V) : ℝ :=
  if G.Adj u v then edgeEnergy α (x u) (x v) else 0

private theorem edgeAt_comm (G : SimpleGraph V) (α : ℝ) (x : V → ℝ) (u v : V) :
    edgeAt G α x u v = edgeAt G α x v u :=
  if_congr (G.adj_comm u v) (edgeEnergy_comm α (x u) (x v)) rfl

private def pairPairEnergy (e : Partition P W V) (G : SimpleGraph V) (α : ℝ)
    (x : V → ℝ) (i j : P) : ℝ :=
  (edgeAt G α x (left e i) (left e j) + edgeAt G α x (left e i) (right e j)) +
    (edgeAt G α x (right e i) (left e j) + edgeAt G α x (right e i) (right e j))

private def pairFixedEnergy (e : Partition P W V) (G : SimpleGraph V) (α : ℝ)
    (x : V → ℝ) (i : P) (w : W) : ℝ :=
  edgeAt G α x (fixed e w) (left e i) + edgeAt G α x (fixed e w) (right e i)

private theorem pairPairEnergy_eq (e : Partition P W V) (G : SimpleGraph V) (α : ℝ)
    (x : V → ℝ) (i j : P) {p c : Prop}
    (hll : G.Adj (left e i) (left e j) ↔ p)
    (hrr : G.Adj (right e i) (right e j) ↔ p)
    (hlr : G.Adj (left e i) (right e j) ↔ c)
    (hrl : G.Adj (right e i) (left e j) ↔ c) :
    pairPairEnergy e G α x i j =
      twoPairEnergy p c α (x (left e i)) (x (right e i)) (x (left e j)) (x (right e j)) := by
  by_cases hp : p <;> by_cases hc : c
  all_goals simp [pairPairEnergy, edgeAt, twoPairEnergy, hll, hrr, hlr, hrl, hp, hc]
  ac_rfl

private theorem pairPairEnergy_le {e : Partition P W V} {z : W} {G H : SimpleGraph V}
    (h : Incidence e z G H) {α : ℝ} (hα : α ≤ 1) (x : V → ℝ) (i j : P) :
    pairPairEnergy e H α x i j ≤ pairPairEnergy e G α (compress e x) i j := by
  have common (b c : Bool) :
      H.Adj (e (.inl (i, b))) (e (.inl (j, c))) ↔
        G.Adj (e (.inl (i, b))) (e (.inl (j, c))) :=
    h.off_leaf (pair_ne_fixed e i b z) (pair_ne_fixed e j c z)
  rw [pairPairEnergy_eq e H α x i j (common true true)
      ((common false false).trans (h.parallel i j).symm) (common true false)
      ((common false true).trans (h.cross i j).symm),
    pairPairEnergy_eq e G α (compress e x) i j Iff.rfl (h.parallel i j).symm
      Iff.rfl (h.cross i j).symm]
  simp only [compress_left, compress_right]
  by_cases hij : i = j
  · subst j
    have sorted (a b : ℝ) : edgeEnergy α (max a b) (min a b) = edgeEnergy α a b := by
      rcases le_total a b with hab | hab
      · rw [max_eq_right hab, min_eq_left hab, edgeEnergy_comm]
      · rw [max_eq_left hab, min_eq_right hab]
    simp only [twoPairEnergy, SimpleGraph.irrefl, ite_false, zero_add]
    split
    · rw [edgeEnergy_comm α (x (right e i)) (x (left e i)),
        edgeEnergy_comm α (min (x (left e i)) (x (right e i)))
          (max (x (left e i)) (x (right e i))), sorted]
    · exact le_rfl
  · exact twoPairEnergy_le (h.cross_to_parallel hij) hα _ _ _ _

private theorem pairFixedEnergy_eq (e : Partition P W V) (G : SimpleGraph V) (α : ℝ)
    (x : V → ℝ) (i : P) (w : W) {p q : Prop}
    (hl : G.Adj (fixed e w) (left e i) ↔ p) (hr : G.Adj (fixed e w) (right e i) ↔ q) :
    pairFixedEnergy e G α x i w =
      onePairEnergy p q α (x (fixed e w)) (x (left e i)) (x (right e i)) := by
  simp only [pairFixedEnergy, edgeAt, onePairEnergy, hl, hr]

private theorem pairFixedEnergy_le {e : Partition P W V} {z : W} {G H : SimpleGraph V}
    (h : Incidence e z G H) {α : ℝ} (hα : 0 ≤ α) (hα' : α ≤ 1)
    {x : V → ℝ} (hx : ∀ v, 0 ≤ x v) (i : P) (w : W) :
    pairFixedEnergy e H α x i w ≤ pairFixedEnergy e G α (compress e x) i w := by
  rw [pairFixedEnergy_eq e G α (compress e x) i w Iff.rfl Iff.rfl]
  simp only [compress_fixed, compress_left, compress_right]
  by_cases hw : w = z
  · subst w
    rw [pairFixedEnergy_eq e H α x i z (h.leaf_left i) (h.leaf_right i)]
    exact (onePairEnergy_le (h.leaf_nested i) hα hα' (hx _) (hx _) (hx _)).2
  · rw [pairFixedEnergy_eq e H α x i w
      (h.off_leaf (fixed_ne_fixed e hw) (pair_ne_fixed e i true z))
      (h.off_leaf (fixed_ne_fixed e hw) (pair_ne_fixed e i false z))]
    exact (onePairEnergy_le (h.fixed_nested i w hw) hα hα' (hx _) (hx _) (hx _)).1

private theorem fixedFixed_adj {e : Partition P W V} {z : W} {G H : SimpleGraph V}
    (h : Incidence e z G H) (w v : W) :
    H.Adj (fixed e w) (fixed e v) → G.Adj (fixed e w) (fixed e v) := by
  intro ha
  by_cases hw : w = z
  · subst w
    exact (h.leaf_fixed v ha.symm).symm
  by_cases hv : v = z
  · subst v
    exact h.leaf_fixed w ha
  exact (h.off_leaf (fixed_ne_fixed e hw) (fixed_ne_fixed e hv)).mp ha

private theorem fixedFixedEnergy_le {e : Partition P W V} {z : W} {G H : SimpleGraph V}
    (h : Incidence e z G H) {α : ℝ} (hα : 0 ≤ α) (hα' : α ≤ 1)
    {x : V → ℝ} (hx : ∀ v, 0 ≤ x v) (w v : W) :
    edgeAt H α x (fixed e w) (fixed e v) ≤
      edgeAt G α (compress e x) (fixed e w) (fixed e v) := by
  simp only [edgeAt, compress_fixed]
  by_cases ha : H.Adj (fixed e w) (fixed e v)
  · simp [ha, fixedFixed_adj h w v ha]
  · by_cases hg : G.Adj (fixed e w) (fixed e v)
    · simpa only [ha, hg, ite_true, ite_false] using edgeEnergy_nonneg hα hα' (hx _) (hx _)
    · simp [ha, hg]

section Finite

variable [Fintype P] [Fintype W] [Fintype V] [DecidableEq V]

/-- Group the ordered edge sum by the pair and fixed parts of the partition. -/
private theorem energy_blocks (e : Partition P W V) (G : SimpleGraph V) (α : ℝ)
    (x : V → ℝ) :
    2 * energy (mixedMatrix G α) x =
      (∑ i, ∑ j, pairPairEnergy e G α x i j) +
        2 * (∑ i, ∑ w, pairFixedEnergy e G α x i w) +
        (∑ w, ∑ v, edgeAt G α x (fixed e w) (fixed e v)) := by
  rw [two_energy_mixedMatrix]
  change (∑ u, ∑ v, edgeAt G α x u v) = _
  rw [sum_partition e (fun u => ∑ v, edgeAt G α x u v)]
  simp_rw [sum_partition e (edgeAt G α x _)]
  have swap (i : P) (b : Bool) (w : W) :
      edgeAt G α x (e (.inl (i, b))) (fixed e w) =
        edgeAt G α x (fixed e w) (e (.inl (i, b))) :=
    edgeAt_comm G α x _ _
  simp only [pairPairEnergy, pairFixedEnergy, swap, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun w i => edgeAt G α x (fixed e w) (left e i)),
    Finset.sum_comm (f := fun w i => edgeAt G α x (fixed e w) (right e i))]
  ring

variable {e : Partition P W V} {z : W} {G H : SimpleGraph V} {α : ℝ} {x : V → ℝ}

private theorem compare_energy (h : Incidence e z G H) (hα : 0 ≤ α) (hα' : α ≤ 1)
    (hx : ∀ v, 0 ≤ x v) :
    energy (mixedMatrix H α) x ≤ energy (mixedMatrix G α) (compress e x) ∧
      ∀ w, α < 1 → 0 < x (fixed e z) → 0 < x (fixed e w) →
        G.Adj (fixed e w) (fixed e z) → ¬ H.Adj (fixed e w) (fixed e z) →
        energy (mixedMatrix H α) x < energy (mixedMatrix G α) (compress e x) := by
  have hp := Finset.sum_le_sum (s := univ) fun i _ =>
    Finset.sum_le_sum (s := univ) fun j _ => pairPairEnergy_le h hα' x i j
  have hm := Finset.sum_le_sum (s := univ) fun i _ =>
    Finset.sum_le_sum (s := univ) fun w _ => pairFixedEnergy_le h hα hα' hx i w
  have hf (w v : W) := fixedFixedEnergy_le h hα hα' hx w v
  have hle := add_le_add hp (mul_le_mul_of_nonneg_left hm (by norm_num : (0 : ℝ) ≤ 2))
  constructor
  · have htotal := add_le_add hle (Finset.sum_le_sum (s := univ) fun w _ =>
      Finset.sum_le_sum (s := univ) fun v _ => hf w v)
    rw [← energy_blocks e H α x, ← energy_blocks e G α (compress e x)] at htotal
    linarith
  · intro w hαlt hzp hwp hG hH
    have hedge : edgeAt H α x (fixed e w) (fixed e z) <
        edgeAt G α (compress e x) (fixed e w) (fixed e z) := by
      simpa only [edgeAt, compress_fixed, hH, hG, ite_true, ite_false] using
        edgeEnergy_pos hα hαlt hwp hzp
    have hfStrict := Finset.sum_lt_sum (s := univ) (fun w _ => Finset.sum_le_sum (s := univ) fun v _ => hf w v)
      ⟨w, mem_univ w, Finset.sum_lt_sum (s := univ) (fun v _ => hf w v) ⟨z, mem_univ z, hedge⟩⟩
    have htotal := add_lt_add_of_le_of_lt hle hfStrict
    rw [← energy_blocks e H α x, ← energy_blocks e G α (compress e x)] at htotal
    linarith

/-- For 0 ≤ α ≤ 1, sorting a nonnegative vector toward the nested incidences
weakly increases its mixed graph energy across the transfer. -/
theorem energy_le_compress (h : Incidence e z G H) (hα : 0 ≤ α) (hα' : α ≤ 1)
    (hx : ∀ v, 0 ≤ x v) :
    energy (mixedMatrix H α) x ≤ energy (mixedMatrix G α) (compress e x) :=
  (compare_energy h hα hα' hx).1

/-- An extra edge from the moved leaf to a fixed vertex gives strict gain when
both endpoint coordinates are positive and α < 1. -/
private theorem energy_lt_compress (h : Incidence e z G H) (hα : 0 ≤ α) (hα' : α < 1)
    (hx : ∀ v, 0 ≤ x v) (w : W) (hz : 0 < x (fixed e z)) (hw : 0 < x (fixed e w))
    (hG : G.Adj (fixed e w) (fixed e z)) (hH : ¬ H.Adj (fixed e w) (fixed e z)) :
    energy (mixedMatrix H α) x < energy (mixedMatrix G α) (compress e x) :=
  (compare_energy h hα hα'.le hx).2 w hα' hz hw hG hH

/-- The largest mixed eigenvalue after the transfer is at most its value before it. -/
theorem mixedTop_le (h : Incidence e z G H) (hα : 0 ≤ α) (hα' : α ≤ 1) :
    mixedTop H α ≤ mixedTop G α := by
  let : Nonempty V := ⟨fixed e z⟩
  obtain ⟨x, hunit, henergy, _, hx⟩ := mixed_nonnegative_maximizer H hα hα'
  rw [← henergy]
  exact (energy_le_compress h hα hα' hx).trans
    (energy_le_top (mixedMatrix G α) (compress_unitVector e hunit))

/-- For connected post-transfer H, an unmatched fixed neighbor of the moved leaf
in G forces strict inequality of the largest mixed eigenvalues. -/
theorem mixedTop_lt (h : Incidence e z G H) (hc : H.Connected) (hα : 0 ≤ α) (hα' : α < 1)
    (w : W) (hG : G.Adj (fixed e w) (fixed e z)) (hH : ¬ H.Adj (fixed e w) (fixed e z)) :
    mixedTop H α < mixedTop G α := by
  let : Nonempty V := hc.nonempty
  obtain ⟨x, hunit, henergy, _, hx⟩ := mixed_positive_maximizer H hc hα hα'
  rw [← henergy]
  exact (energy_lt_compress h hα hα' (fun v => (hx v).le) w (hx _) (hx _) hG hH).trans_le
    (energy_le_top (mixedMatrix G α) (compress_unitVector e hunit))

end Finite

end OmegaMath.PairedEdgeEnergy
