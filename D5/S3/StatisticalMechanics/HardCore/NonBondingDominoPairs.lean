/- GID: D5/S3/StatisticalMechanics/HardCore/NonBondingDominoPairs
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/HardCore/NonBondingDominoPairs
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Proves Conjecture 1 of R. J. Mathar (arXiv:2404.18806, 2024): the sets of two non-bonding dominoes on an r x c board (hard dimers with nearest-neighbour exclusion) number 2c^2r^2 - 2(cr^2 + c^2r) + (r^2 + c^2)/2 - 22cr + (59/2)(c + r) - 30 for r, c >= 3. -/

/-
proof_shape: result: content
escape_witness: form (2): the conclusion `result` itself, produced on its live path by the
  anchor bijection of the dominoes (horizontal and vertical), the classification of the bonded
  anchor offsets (11 for H-H and V-V, 12 for H-V and V-H), the product formula for anchor pairs
  with a given offset, and the two-to-one map from ordered to unordered pairs
admission_basis: open-problem-resolution (issue #11068)
Direct frozen dependencies: none (pinned Mathlib only)
-/

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Int.Interval
import Mathlib.Data.Nat.Dist
import Mathlib.Data.Set.Card
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.StatisticalMechanics.HardCore.NonBondingDominoPairs

open Finset

/-!
R. J. Mathar, "Bivariate Generating Functions Enumerating Non-Bonding Dominoes on Rectangular
Boards" (arXiv:2404.18806, 2024): two dominoes are non-bonding when no square of one is at L1
distance less than 2 from a square of the other, i.e. they share at most a corner point. These are
hard dimers with nearest-neighbour exclusion on the square lattice. `D(r, c, 2)` counts the
placements of two such dominoes on an `r × c` board; Conjecture 1 of the paper gives it as a
biquadratic polynomial for `r, c ≥ 3`.
-/

/-- A domino on the `r × c` board: two squares of the board at L1 distance 1. -/
def IsDomino (r c : ℕ) (s : Finset (ℕ × ℕ)) : Prop :=
  ∃ p q : ℕ × ℕ, s = {p, q} ∧ p.1 < r ∧ p.2 < c ∧ q.1 < r ∧ q.2 < c ∧
    Nat.dist p.1 q.1 + Nat.dist p.2 q.2 = 1

/-- Two dominoes are non-bonding: all their squares are at L1 distance at least 2. -/
def NonBonding (s t : Finset (ℕ × ℕ)) : Prop :=
  ∀ p ∈ s, ∀ q ∈ t, 2 ≤ Nat.dist p.1 q.1 + Nat.dist p.2 q.2

/-- `D(r, c, 2)`: the sets of two dominoes on the `r × c` board that are non-bonding. -/
noncomputable def D2 (r c : ℕ) : ℕ :=
  {P : Finset (Finset (ℕ × ℕ)) | P.card = 2 ∧ (∀ s ∈ P, IsDomino r c s) ∧
    ∀ s ∈ P, ∀ t ∈ P, s ≠ t → NonBonding s t}.ncard

/-- Mathar's Conjecture 1 (arXiv:2404.18806, 2024). -/
def claim : Prop :=
  ∀ r c : ℕ, 3 ≤ r → 3 ≤ c →
    (D2 r c : ℚ) = 2 * c ^ 2 * r ^ 2 - 2 * (c * r ^ 2 + c ^ 2 * r) + 1 / 2 * (r ^ 2 + c ^ 2) -
      22 * c * r + 59 / 2 * (c + r) - 30

/-- The horizontal domino anchored at `a`. -/
private def hc (a : ℕ × ℕ) : Finset (ℕ × ℕ) := {a, (a.1, a.2 + 1)}
/-- The vertical domino anchored at `a`. -/
private def vc (a : ℕ × ℕ) : Finset (ℕ × ℕ) := {a, (a.1 + 1, a.2)}
/-- Pairs `(x, y)` in `[0, m) × [0, m')` with `y - x = d`. -/
private def g (m m' : ℕ) (d : ℤ) : ℕ :=
  ((range m ×ˢ range m').filter (fun p => (p.2 : ℤ) - p.1 = d)).card
/-- Anchor offsets of a horizontal domino bonding with a horizontal one (and the equal one). -/
private def offHH : Finset (ℤ × ℤ) :=
  {(-1, -1), (-1, 0), (-1, 1), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -1), (1, 0), (1, 1)}
/-- The anchor offsets of a vertical domino that bond with a horizontal one. -/
private def offHV : Finset (ℤ × ℤ) :=
  {(-2, 0), (-2, 1), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (0, -1), (0, 0), (0, 1), (0, 2),
    (1, 0), (1, 1)}
/-- The anchor offsets of a horizontal domino that bond with a vertical one. -/
private def offVH : Finset (ℤ × ℤ) :=
  {(-1, -1), (-1, 0), (0, -2), (0, -1), (0, 0), (0, 1), (1, -2), (1, -1), (1, 0), (1, 1),
    (2, -1), (2, 0)}
/-- Anchor offsets of a vertical domino bonding with a vertical one (and the equal one). -/
private def offVV : Finset (ℤ × ℤ) :=
  {(-2, 0), (-1, -1), (-1, 0), (-1, 1), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, 0)}

set_option maxHeartbeats 1000000 in
-- the four bond characterizations and the 32 overlap evaluations are local steps of one proof
theorem result : claim := by
  classical
  -- one-dimensional overlap counts
  have gform : ∀ (m m' : ℕ) (d : ℤ),
      (g m m' d : ℤ) = ((min (m : ℤ) (m' - d) - max 0 (-d)).toNat : ℤ) := by
    intro m m' d
    unfold g
    have h1 : ((range m ×ˢ range m').filter (fun p => (p.2 : ℤ) - p.1 = d)).card =
        ((range m).filter (fun x : ℕ => 0 ≤ (x : ℤ) + d ∧ (x : ℤ) + d < m')).card := by
      refine Finset.card_nbij' (fun p => p.1) (fun x : ℕ => (x, ((x : ℤ) + d).toNat)) ?_ ?_ ?_ ?_
      · intro p hp
        simp only [coe_filter, mem_product, mem_range, Set.mem_ofPred_eq] at hp ⊢
        omega
      · intro x hx
        simp only [coe_filter, mem_product, mem_range, Set.mem_ofPred_eq] at hx ⊢
        omega
      · intro p hp
        simp only [coe_filter, mem_product, mem_range, Set.mem_ofPred_eq] at hp
        refine Prod.ext rfl ?_
        simp only
        omega
      · intro x _
        rfl
    have h2 : ((range m).filter (fun x : ℕ => 0 ≤ (x : ℤ) + d ∧ (x : ℤ) + d < m')).map
        (Nat.castEmbedding : ℕ ↪ ℤ) = Finset.Ico (max 0 (-d)) (min (m : ℤ) (m' - d)) := by
      ext z
      simp only [mem_map, mem_filter, mem_range, Nat.castEmbedding_apply, mem_Ico]
      constructor
      · rintro ⟨x, ⟨hx, h⟩, rfl⟩
        omega
      · intro h
        exact ⟨z.toNat, ⟨by omega, by omega⟩, by omega⟩
    rw [h1, ← Finset.card_map (Nat.castEmbedding : ℕ ↪ ℤ), h2, Int.card_Ico]
  have e : ∀ (m m' : ℕ) (d v : ℤ), min (m : ℤ) (m' - d) - max 0 (-d) = v → 0 ≤ v →
      (g m m' d : ℤ) = v := by
    intro m m' d v h hv
    rw [gform, h, Int.toNat_of_nonneg hv]
  -- ordered anchor pairs with a prescribed offset
  have count : ∀ (Off : Finset (ℤ × ℤ)) (m1 n1 m2 n2 : ℕ),
      (((range m1 ×ˢ range n1) ×ˢ (range m2 ×ˢ range n2)).filter
        (fun p => ((p.2.1 : ℤ) - p.1.1, (p.2.2 : ℤ) - p.1.2) ∈ Off)).card =
        ∑ o ∈ Off, g m1 m2 o.1 * g n1 n2 o.2 := by
    intro Off m1 n1 m2 n2
    refine (Finset.card_eq_sum_card_fiberwise
      (f := fun p : (ℕ × ℕ) × (ℕ × ℕ) => ((p.2.1 : ℤ) - p.1.1, (p.2.2 : ℤ) - p.1.2))
      (t := Off) (fun p hp => (mem_filter.mp hp).2)).trans ?_
    refine Finset.sum_congr rfl (fun o ho => ?_)
    unfold g
    rw [← Finset.card_product]
    refine Finset.card_nbij' (fun p => ((p.1.1, p.2.1), (p.1.2, p.2.2)))
      (fun q => ((q.1.1, q.2.1), (q.1.2, q.2.2))) ?_ ?_ ?_ ?_
    · intro p hp
      simp only [Finset.mem_coe, mem_filter, mem_product, mem_range, Prod.ext_iff] at hp ⊢
      omega
    · intro q hq
      simp only [Finset.mem_coe, mem_filter, mem_product, mem_range, Prod.ext_iff] at hq ⊢
      refine ⟨⟨⟨⟨hq.1.1.1, hq.2.1.1⟩, ⟨hq.1.1.2, hq.2.1.2⟩⟩, ?_⟩, hq.1.2, hq.2.2⟩
      rw [show ((q.1.2 : ℤ) - q.1.1, (q.2.2 : ℤ) - q.2.1) = o from Prod.ext hq.1.2 hq.2.2]
      exact ho
    · intro p _; rfl
    · intro q _; rfl
  -- a type pair: non-bonding anchor pairs are all pairs minus the bonded offsets
  have typeSum : ∀ (x y : ℕ × ℕ → Finset (ℕ × ℕ)) (Off : Finset (ℤ × ℤ)) (m1 n1 m2 n2 : ℕ),
      (∀ a b, NonBonding (x a) (y b) ↔ ((b.1 : ℤ) - a.1, (b.2 : ℤ) - a.2) ∉ Off) →
      (∑ a ∈ range m1 ×ˢ range n1, ∑ b ∈ range m2 ×ˢ range n2,
          (if NonBonding (x a) (y b) then 1 else 0 : ℤ)) =
        (m1 : ℤ) * n1 * (m2 * n2) - ∑ o ∈ Off, (g m1 m2 o.1 : ℤ) * g n1 n2 o.2 := by
    intro x y Off m1 n1 m2 n2 hxy
    have hite : ∀ a b, (if NonBonding (x a) (y b) then 1 else 0 : ℤ) =
        1 - if ((b.1 : ℤ) - a.1, (b.2 : ℤ) - a.2) ∈ Off then 1 else 0 := by
      intro a b
      by_cases h : ((b.1 : ℤ) - a.1, (b.2 : ℤ) - a.2) ∈ Off
      · rw [if_pos h, if_neg (fun hn => (hxy a b).mp hn h)]; norm_num
      · rw [if_neg h, if_pos ((hxy a b).mpr h)]; norm_num
    simp only [hite, sum_sub_distrib, sum_const, card_product, card_range, nsmul_eq_mul,
      mul_one]
    have hc := count Off m1 n1 m2 n2
    rw [card_filter, sum_product] at hc
    have hc' := congrArg (fun k : ℕ => (k : ℤ)) hc
    simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, Nat.cast_mul] at hc'
    rw [hc']
    push_cast
    ring
  have bHH : ∀ a b : ℕ × ℕ,
      NonBonding (hc a) (hc b) ↔ ((b.1 : ℤ) - a.1, (b.2 : ℤ) - a.2) ∉ offHH := by
    rintro ⟨i, j⟩ ⟨i', j'⟩
    simp only [NonBonding, hc, mem_insert, mem_singleton, forall_eq_or_imp, forall_eq,
      Nat.dist]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩ hmem
      simp only [offHH, mem_insert, mem_singleton, Prod.mk.injEq] at hmem
      rcases hmem with ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ |
        ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ <;> omega
    · intro h
      simp only [offHH, mem_insert, mem_singleton, Prod.mk.injEq, not_or, not_and] at h
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> omega
  have bHV : ∀ a b : ℕ × ℕ,
      NonBonding (hc a) (vc b) ↔ ((b.1 : ℤ) - a.1, (b.2 : ℤ) - a.2) ∉ offHV := by
    rintro ⟨i, j⟩ ⟨i', j'⟩
    simp only [NonBonding, hc, vc, mem_insert, mem_singleton, forall_eq_or_imp, forall_eq,
      Nat.dist]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩ hmem
      simp only [offHV, mem_insert, mem_singleton, Prod.mk.injEq] at hmem
      rcases hmem with ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ |
        ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ <;> omega
    · intro h
      simp only [offHV, mem_insert, mem_singleton, Prod.mk.injEq, not_or, not_and] at h
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> omega
  have bVH : ∀ a b : ℕ × ℕ,
      NonBonding (vc a) (hc b) ↔ ((b.1 : ℤ) - a.1, (b.2 : ℤ) - a.2) ∉ offVH := by
    rintro ⟨i, j⟩ ⟨i', j'⟩
    simp only [NonBonding, hc, vc, mem_insert, mem_singleton, forall_eq_or_imp, forall_eq,
      Nat.dist]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩ hmem
      simp only [offVH, mem_insert, mem_singleton, Prod.mk.injEq] at hmem
      rcases hmem with ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ |
        ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ <;> omega
    · intro h
      simp only [offVH, mem_insert, mem_singleton, Prod.mk.injEq, not_or, not_and] at h
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> omega
  have bVV : ∀ a b : ℕ × ℕ,
      NonBonding (vc a) (vc b) ↔ ((b.1 : ℤ) - a.1, (b.2 : ℤ) - a.2) ∉ offVV := by
    rintro ⟨i, j⟩ ⟨i', j'⟩
    simp only [NonBonding, vc, mem_insert, mem_singleton, forall_eq_or_imp, forall_eq,
      Nat.dist]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩ hmem
      simp only [offVV, mem_insert, mem_singleton, Prod.mk.injEq] at hmem
      rcases hmem with ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ |
        ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ <;> omega
    · intro h
      simp only [offVV, mem_insert, mem_singleton, Prod.mk.injEq, not_or, not_and] at h
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> omega
  -- ordered pairs of distinct dominoes are twice the unordered ones
  have pairs : ∀ D : Finset (Finset (ℕ × ℕ)), (∀ s ∈ D, s.Nonempty) →
      ((D ×ˢ D).filter (fun p => NonBonding p.1 p.2)).card =
        2 * {P : Finset (Finset (ℕ × ℕ)) | P.card = 2 ∧ (∀ s ∈ P, s ∈ D) ∧
          ∀ s ∈ P, ∀ t ∈ P, s ≠ t → NonBonding s t}.ncard := by
    intro D hne
    have hsymm : ∀ s t, NonBonding s t → NonBonding t s := by
      intro s t h q hq p hp
      rw [Nat.dist_comm q.1, Nat.dist_comm q.2]
      exact h p hp q hq
    have hirr : ∀ s ∈ D, ¬ NonBonding s s := by
      intro s hs h
      obtain ⟨p, hp⟩ := hne s hs
      have := h p hp p hp
      simp [Nat.dist_self] at this
    set O := (D ×ˢ D).filter (fun p => NonBonding p.1 p.2) with hO
    let f : Finset (ℕ × ℕ) × Finset (ℕ × ℕ) → Finset (Finset (ℕ × ℕ)) := fun p => {p.1, p.2}
    have hset : {P : Finset (Finset (ℕ × ℕ)) | P.card = 2 ∧ (∀ s ∈ P, s ∈ D) ∧
        ∀ s ∈ P, ∀ t ∈ P, s ≠ t → NonBonding s t} = ↑(O.image f) := by
      ext P
      simp only [Set.mem_ofPred_eq, coe_image, Set.mem_image, mem_coe, hO, mem_filter,
        mem_product, f]
      constructor
      · rintro ⟨h2, hD, hR⟩
        obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp h2
        exact ⟨(x, y), ⟨⟨hD x (by simp), hD y (by simp)⟩, hR x (by simp) y (by simp) hxy⟩, rfl⟩
      · rintro ⟨⟨x, y⟩, ⟨⟨hx, hy⟩, hxy⟩, rfl⟩
        have hne' : x ≠ y := fun h => hirr x hx (h ▸ hxy)
        refine ⟨Finset.card_pair hne', ?_, ?_⟩
        · intro s hs
          simp only [mem_insert, mem_singleton] at hs
          rcases hs with rfl | rfl
          · exact hx
          · exact hy
        · intro s hs t ht hst
          simp only [mem_insert, mem_singleton] at hs ht
          rcases hs with rfl | rfl <;> rcases ht with rfl | rfl
          · exact absurd rfl hst
          · exact hxy
          · exact hsymm _ _ hxy
          · exact absurd rfl hst
    rw [hset, Set.ncard_coe_finset, Finset.card_eq_sum_card_image f O,
      Finset.sum_const_nat (m := 2)]
    · ring
    intro P hP
    obtain ⟨⟨x, y⟩, hp, rfl⟩ := mem_image.mp hP
    simp only [hO, mem_filter, mem_product] at hp
    have hne' : x ≠ y := fun h => hirr x hp.1.1 (h ▸ hp.2)
    have hfib : O.filter (fun q => f q = f (x, y)) = {(x, y), (y, x)} := by
      ext ⟨a, b⟩
      simp only [hO, mem_filter, mem_product, mem_insert, mem_singleton, Prod.mk.injEq, f]
      constructor
      · rintro ⟨⟨⟨ha, hb⟩, hab⟩, h⟩
        have hane : a ≠ b := fun h' => hirr a ha (h' ▸ hab)
        have ha' : a ∈ ({x, y} : Finset (Finset (ℕ × ℕ))) := h ▸ (by simp)
        have hb' : b ∈ ({x, y} : Finset (Finset (ℕ × ℕ))) := h ▸ (by simp)
        simp only [mem_insert, mem_singleton] at ha' hb'
        rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl
        · exact absurd rfl hane
        · exact Or.inl ⟨rfl, rfl⟩
        · exact Or.inr ⟨rfl, rfl⟩
        · exact absurd rfl hane
      · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
        · exact ⟨⟨⟨hp.1.1, hp.1.2⟩, hp.2⟩, rfl⟩
        · exact ⟨⟨⟨hp.1.2, hp.1.1⟩, hsymm _ _ hp.2⟩, Finset.pair_comm _ _⟩
    rw [hfib, Finset.card_pair (by simp [hne'])]
  intro r c hr hc3
  obtain ⟨R, rfl⟩ : ∃ R, r = R + 3 := ⟨r - 3, by omega⟩
  obtain ⟨C, rfl⟩ : ∃ C, c = C + 3 := ⟨c - 3, by omega⟩
  -- dominoes are the horizontal and the vertical ones, given by their anchors
  have memDom : ∀ s, IsDomino (R + 3) (C + 3) s ↔
      s ∈ (range (R + 3) ×ˢ range (C + 2)).image hc ∪
        (range (R + 2) ×ˢ range (C + 3)).image vc := by
    intro s
    constructor
    · rintro ⟨⟨p1, p2⟩, ⟨q1, q2⟩, rfl, hp1, hp2, hq1, hq2, hd⟩
      simp only [Nat.dist] at hd hp1 hp2 hq1 hq2
      simp only [mem_union, mem_image, mem_product, mem_range, hc, vc]
      rcases (by omega : (p1 = q1 ∧ q2 = p2 + 1) ∨ (p1 = q1 ∧ p2 = q2 + 1) ∨
          (p2 = q2 ∧ q1 = p1 + 1) ∨ (p2 = q2 ∧ p1 = q1 + 1)) with h | h | h | h
      · exact Or.inl ⟨(p1, p2), ⟨by omega, by omega⟩, by rw [h.1, h.2]⟩
      · exact Or.inl ⟨(q1, q2), ⟨by omega, by omega⟩, by rw [h.1, h.2, Finset.pair_comm]⟩
      · exact Or.inr ⟨(p1, p2), ⟨by omega, by omega⟩, by rw [h.1, h.2]⟩
      · exact Or.inr ⟨(q1, q2), ⟨by omega, by omega⟩, by rw [h.1, h.2, Finset.pair_comm]⟩
    · simp only [mem_union, mem_image, mem_product, mem_range, hc, vc]
      rintro (⟨⟨i, j⟩, ⟨hi, hj⟩, rfl⟩ | ⟨⟨i, j⟩, ⟨hi, hj⟩, rfl⟩)
      · exact ⟨(i, j), (i, j + 1), rfl, by simp only; omega, by simp only; omega,
          by simp only; omega, by simp only; omega, by simp [Nat.dist]⟩
      · exact ⟨(i, j), (i + 1, j), rfl, by simp only; omega, by simp only; omega,
          by simp only; omega, by simp only; omega, by simp [Nat.dist]⟩
  have injH : ∀ a b : ℕ × ℕ, hc a = hc b → a = b := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ h
    have h1 : (i, j) ∈ hc (i', j') := h ▸ (show (i, j) ∈ hc (i, j) by simp [hc])
    have h2 : (i', j') ∈ hc (i, j) := h ▸ (show (i', j') ∈ hc (i', j') by simp [hc])
    simp only [hc, mem_insert, mem_singleton, Prod.mk.injEq] at h1 h2
    ext <;> simp only <;> omega
  have injV : ∀ a b : ℕ × ℕ, vc a = vc b → a = b := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ h
    have h1 : (i, j) ∈ vc (i', j') := h ▸ (show (i, j) ∈ vc (i, j) by simp [vc])
    have h2 : (i', j') ∈ vc (i, j) := h ▸ (show (i', j') ∈ vc (i', j') by simp [vc])
    simp only [vc, mem_insert, mem_singleton, Prod.mk.injEq] at h1 h2
    ext <;> simp only <;> omega
  have disj : Disjoint ((range (R + 3) ×ˢ range (C + 2)).image hc)
      ((range (R + 2) ×ˢ range (C + 3)).image vc) := by
    rw [Finset.disjoint_left]
    rintro s hs1 hs2
    obtain ⟨⟨i, j⟩, -, rfl⟩ := mem_image.mp hs1
    obtain ⟨⟨i', j'⟩, -, hb⟩ := mem_image.mp hs2
    have h1 : (i, j) ∈ vc (i', j') := hb ▸ (show (i, j) ∈ hc (i, j) by simp [hc])
    have h2 : (i, j + 1) ∈ vc (i', j') := hb ▸ (show (i, j + 1) ∈ hc (i, j) by simp [hc])
    simp only [vc, mem_insert, mem_singleton, Prod.mk.injEq] at h1 h2
    omega
  have hne : ∀ s ∈ (range (R + 3) ×ˢ range (C + 2)).image hc ∪
      (range (R + 2) ×ˢ range (C + 3)).image vc, s.Nonempty := by
    intro s hs
    simp only [mem_union, mem_image] at hs
    rcases hs with ⟨a, -, rfl⟩ | ⟨a, -, rfl⟩
    · exact ⟨a, by simp [hc]⟩
    · exact ⟨a, by simp [vc]⟩
  -- D(r, c, 2) through ordered pairs of anchors
  have hD2 : (2 * D2 (R + 3) (C + 3) : ℤ) =
      (∑ a ∈ range (R + 3) ×ˢ range (C + 2), ∑ b ∈ range (R + 3) ×ˢ range (C + 2),
          (if NonBonding (hc a) (hc b) then 1 else 0 : ℤ)) +
        (∑ a ∈ range (R + 3) ×ˢ range (C + 2), ∑ b ∈ range (R + 2) ×ˢ range (C + 3),
          (if NonBonding (hc a) (vc b) then 1 else 0 : ℤ)) +
        (∑ a ∈ range (R + 2) ×ˢ range (C + 3), ∑ b ∈ range (R + 3) ×ˢ range (C + 2),
          (if NonBonding (vc a) (hc b) then 1 else 0 : ℤ)) +
        (∑ a ∈ range (R + 2) ×ˢ range (C + 3), ∑ b ∈ range (R + 2) ×ˢ range (C + 3),
          (if NonBonding (vc a) (vc b) then 1 else 0 : ℤ)) := by
    have h := pairs _ hne
    have hset : {P : Finset (Finset (ℕ × ℕ)) | P.card = 2 ∧ (∀ s ∈ P, s ∈
        (range (R + 3) ×ˢ range (C + 2)).image hc ∪ (range (R + 2) ×ˢ range (C + 3)).image vc) ∧
        ∀ s ∈ P, ∀ t ∈ P, s ≠ t → NonBonding s t} =
        {P : Finset (Finset (ℕ × ℕ)) | P.card = 2 ∧ (∀ s ∈ P, IsDomino (R + 3) (C + 3) s) ∧
        ∀ s ∈ P, ∀ t ∈ P, s ≠ t → NonBonding s t} := by
      ext P
      simp only [Set.mem_ofPred_eq, memDom]
    rw [hset] at h
    have h' : 2 * D2 (R + 3) (C + 3) = _ := h.symm
    rw [show (2 * D2 (R + 3) (C + 3) : ℤ) = ((2 * D2 (R + 3) (C + 3) : ℕ) : ℤ) by push_cast; ring,
      h', card_filter, sum_product]
    push_cast
    rw [sum_union disj, sum_image (fun a _ b _ hab => injH a b hab),
      sum_image (fun a _ b _ hab => injV a b hab)]
    simp only [sum_union disj, sum_image (fun a _ b _ hab => injH a b hab),
      sum_image (fun a _ b _ hab => injV a b hab), sum_add_distrib]
    ring
  rw [typeSum hc hc offHH (R + 3) (C + 2) (R + 3) (C + 2) bHH,
    typeSum hc vc offHV (R + 3) (C + 2) (R + 2) (C + 3) bHV,
    typeSum vc hc offVH (R + 2) (C + 3) (R + 3) (C + 2) bVH,
    typeSum vc vc offVV (R + 2) (C + 3) (R + 2) (C + 3) bVV] at hD2
  simp only [offHH, offHV, offVH, offVV] at hD2
  simp (disch := decide) only [sum_insert, sum_singleton] at hD2
  rw [e (C + 2) (C + 2) (-2) (C + 0) (by push_cast; omega) (by omega),
    e (C + 2) (C + 2) (-1) (C + 1) (by push_cast; omega) (by omega),
    e (C + 2) (C + 2) 0 (C + 2) (by push_cast; omega) (by omega),
    e (C + 2) (C + 2) 1 (C + 1) (by push_cast; omega) (by omega),
    e (C + 2) (C + 2) 2 (C + 0) (by push_cast; omega) (by omega),
    e (C + 2) (C + 3) (-1) (C + 1) (by push_cast; omega) (by omega),
    e (C + 2) (C + 3) 0 (C + 2) (by push_cast; omega) (by omega),
    e (C + 2) (C + 3) 1 (C + 2) (by push_cast; omega) (by omega),
    e (C + 2) (C + 3) 2 (C + 1) (by push_cast; omega) (by omega),
    e (C + 3) (C + 2) (-2) (C + 1) (by push_cast; omega) (by omega),
    e (C + 3) (C + 2) (-1) (C + 2) (by push_cast; omega) (by omega),
    e (C + 3) (C + 2) 0 (C + 2) (by push_cast; omega) (by omega),
    e (C + 3) (C + 2) 1 (C + 1) (by push_cast; omega) (by omega),
    e (C + 3) (C + 3) (-1) (C + 2) (by push_cast; omega) (by omega),
    e (C + 3) (C + 3) 0 (C + 3) (by push_cast; omega) (by omega),
    e (C + 3) (C + 3) 1 (C + 2) (by push_cast; omega) (by omega),
    e (R + 2) (R + 2) (-2) (R + 0) (by push_cast; omega) (by omega),
    e (R + 2) (R + 2) (-1) (R + 1) (by push_cast; omega) (by omega),
    e (R + 2) (R + 2) 0 (R + 2) (by push_cast; omega) (by omega),
    e (R + 2) (R + 2) 1 (R + 1) (by push_cast; omega) (by omega),
    e (R + 2) (R + 2) 2 (R + 0) (by push_cast; omega) (by omega),
    e (R + 2) (R + 3) (-1) (R + 1) (by push_cast; omega) (by omega),
    e (R + 2) (R + 3) 0 (R + 2) (by push_cast; omega) (by omega),
    e (R + 2) (R + 3) 1 (R + 2) (by push_cast; omega) (by omega),
    e (R + 2) (R + 3) 2 (R + 1) (by push_cast; omega) (by omega),
    e (R + 3) (R + 2) (-2) (R + 1) (by push_cast; omega) (by omega),
    e (R + 3) (R + 2) (-1) (R + 2) (by push_cast; omega) (by omega),
    e (R + 3) (R + 2) 0 (R + 2) (by push_cast; omega) (by omega),
    e (R + 3) (R + 2) 1 (R + 1) (by push_cast; omega) (by omega),
    e (R + 3) (R + 3) (-1) (R + 2) (by push_cast; omega) (by omega),
    e (R + 3) (R + 3) 0 (R + 3) (by push_cast; omega) (by omega),
    e (R + 3) (R + 3) 1 (R + 2) (by push_cast; omega) (by omega)] at hD2
  have hq := congrArg (fun z : ℤ => (z : ℚ)) hD2
  push_cast at hq ⊢
  linear_combination hq / 2


end D5.S3.StatisticalMechanics.HardCore.NonBondingDominoPairs
