/- GID: D5/S3/Combinatorics/MatchingEnumeration/BlumTriangleRectangles
   generality: G
   mirror-B: D5/B/S3/Combinatorics/MatchingEnumeration/BlumTriangleRectangles
   mirror-E: none(waiver:rectangle-edge-count-construction)
   anchors: [mathlib/module/Mathlib.Order.Interval.Finset.Nat]
   utility: none
   digest: Counting oriented grid edges evaluates the rectangle Gram matrix. -/

import Mathlib.Order.Interval.Finset.Nat
import D5.S3.Combinatorics.MatchingEnumeration.BlumTriangleReduced

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.MatchingEnumeration.BlumTriangleRectangles

open BlumTriangleDefs BlumTriangleReduced Finset Matrix

set_option maxHeartbeats 800000 in
-- The finite edge bijection and four boundary counts share this elaboration budget.
open Classical in
/-- Rectangle intersections count all horizontal and vertical boundary contributions to
    the restricted adjacency form. -/
theorem rectangle_gram {K : Type*} [Field K] [CharP K 2] (k : ℕ) :
    let E := {u : Vertex (4 * k) // u.1.1.val % 2 = 0}
    let B : Matrix E E K := fun u v => if reducedAdj k u.1 v.1 then 1 else 0
    let W : Fin (2 * k) → E → K := fun j u =>
      if u.1.1.1.val / 2 ≤ j.val ∧ j.val ≤ u.1.1.2.val / 2 ∧
        u.1.1.2.val / 2 ≤
          (if j.val % 2 = 0 then 2 * k - 1 else 4 * k - 1 - j.val)
      then 1 else 0
    ∀ i j, dotProduct (W i) (B.mulVec (W j)) =
      if i = j then 0 else if min i.val j.val % 2 = 0 then 1 else 0 := by
  classical
  dsimp only
  let E := {u : Vertex (4 * k) // u.1.1.val % 2 = 0}
  let R : ℕ → ℕ := fun j => if j % 2 = 0 then 2 * k - 1 else 4 * k - 1 - j
  let T : Fin (2 * k) → E → Prop := fun j u =>
    u.1.1.1.val / 2 ≤ j.val ∧ j.val ≤ u.1.1.2.val / 2 ∧
      u.1.1.2.val / 2 ≤ R j.val
  let ar : E → ℕ := fun u => u.1.1.1.val / 2
  let bc : E → ℕ := fun u => u.1.1.2.val / 2
  have coordinates (u : E) :
      2 * ar u = u.1.1.1.val ∧ 2 * bc u = u.1.1.2.val := by
    have hu := u.1.2
    have hp := u.2
    dsimp [ar, bc]
    omega
  have ext (u v : E) (hr : ar u = ar v) (hc : bc u = bc v) : u = v := by
    have hu := coordinates u
    have hv := coordinates v
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext <;> apply Fin.ext <;> omega
  have rbound (j : Fin (2 * k)) : j.val ≤ R j.val ∧ R j.val + j.val < 4 * k := by
    have hj := j.isLt
    dsimp [R]
    split_ifs <;> omega
  let mk : ∀ a b, a < 2 * k → a ≤ b → a + b < 4 * k → E :=
    fun a b ha hab hs => ⟨⟨(⟨2 * a, by omega⟩, ⟨2 * b, by omega⟩), by
      change 2 * a ≤ 2 * b ∧ 2 * b + 2 * a ≤ 2 * (4 * k - 1) ∧
        (2 * a) % 2 = (2 * b) % 2
      omega⟩, by simp⟩
  let forward : Fin (2 * k) → Fin (2 * k) → ℕ → ℕ → Finset (E × E) :=
    fun i j dr dc => univ.filter fun p =>
      T i p.1 ∧ T j p.2 ∧ ar p.2 = ar p.1 + dr ∧ bc p.2 = bc p.1 + dc
  have edge_count (i j : Fin (2 * k)) (dr dc nr lo hi : ℕ)
      (hrect : ∀ a b : ℕ,
        (a ≤ i.val ∧ i.val ≤ b ∧ b ≤ R i.val ∧
          a + dr ≤ j.val ∧ j.val ≤ b + dc ∧ b + dc ≤ R j.val) ↔
        a < nr ∧ lo ≤ b ∧ b < hi) :
      (forward i j dr dc).card = nr * (hi - lo) := by
    let Q := (range nr) ×ˢ (Ico lo hi)
    have valid (a b : ℕ) (hq : a < nr ∧ lo ≤ b ∧ b < hi) :
        a < 2 * k ∧ a ≤ b ∧ a + b < 4 * k ∧
          a + dr < 2 * k ∧ a + dr ≤ b + dc ∧ a + dr + (b + dc) < 4 * k := by
      have hr := (hrect a b).mpr hq
      have hri := rbound i
      have hrj := rbound j
      have hilt := i.isLt
      have hjlt := j.isLt
      omega
    let f : ∀ p ∈ Q, E × E := fun p hp =>
      let hq : p.1 < nr ∧ lo ≤ p.2 ∧ p.2 < hi := by
        simpa only [Q, mem_product, mem_range, mem_Ico, and_assoc] using hp
      let h := valid p.1 p.2 hq
      (mk p.1 p.2 h.1 h.2.1 h.2.2.1,
        mk (p.1 + dr) (p.2 + dc) h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2)
    have hf (p) (hp : p ∈ Q) : f p hp ∈ forward i j dr dc := by
      have hq : p.1 < nr ∧ lo ≤ p.2 ∧ p.2 < hi := by
        simpa only [Q, mem_product, mem_range, mem_Ico, and_assoc] using hp
      have h := (hrect p.1 p.2).mpr hq
      simpa [f, forward, T, ar, bc, mk, and_assoc] using h
    have hinj (p) (hp : p ∈ Q) (q) (hq : q ∈ Q) (he : f p hp = f q hq) : p = q := by
      have he1 := congrArg (fun s : E × E => ar s.1) he
      have he2 := congrArg (fun s : E × E => bc s.1) he
      dsimp [f, mk, ar, bc] at he1 he2
      exact Prod.ext (by omega) (by omega)
    have hsur (p) (hp : p ∈ forward i j dr dc) : ∃ q hq, f q hq = p := by
      have h : T i p.1 ∧ T j p.2 ∧ ar p.2 = ar p.1 + dr ∧
          bc p.2 = bc p.1 + dc := (mem_filter.mp hp).2
      have hb : ar p.1 < nr ∧ lo ≤ bc p.1 ∧ bc p.1 < hi := by
        apply (hrect (ar p.1) (bc p.1)).mp
        dsimp [T, ar, bc] at h ⊢
        omega
      have hq : (ar p.1, bc p.1) ∈ Q := by
        simpa only [Q, mem_product, mem_range, mem_Ico, and_assoc] using hb
      refine ⟨(ar p.1, bc p.1), hq, ?_⟩
      apply Prod.ext
      · apply ext <;> simp [f, mk, ar, bc]
      · apply ext
        · simpa [f, mk, ar, bc] using h.2.2.1.symm
        · simpa [f, mk, ar, bc] using h.2.2.2.symm
    have hc := card_bij f hf hinj hsur
    simpa [Q, card_product] using hc.symm
  let N : Fin (2 * k) → Fin (2 * k) → ℕ → ℕ → K :=
    fun i j dr dc => ((forward i j dr dc).card : K)
  have sum_forward (i j : Fin (2 * k)) (dr dc : ℕ) :
      (∑ u : E, ∑ v : E, if T i u ∧ T j v ∧
        ar v = ar u + dr ∧ bc v = bc u + dc then (1 : K) else 0) = N i j dr dc := by
    rw [← Fintype.sum_prod_type']
    exact natCast_card_filter _ univ |>.symm
  have classify (u v : E) : reducedAdj k u.1 v.1 ↔
      (ar v = ar u ∧ bc v = bc u + 1) ∨
      (ar u = ar v ∧ bc u = bc v + 1) ∨
      (ar v = ar u + 1 ∧ bc v = bc u) ∨
      (ar u = ar v + 1 ∧ bc u = bc v) := by
    have hu := coordinates u
    have hv := coordinates v
    have hpu := u.2
    have hpv := v.2
    have hrow := u.1.1.1.isLt
    have hxu : u.1.1.2.val ≠ 4 * k - 1 := by omega
    have hxv : v.1.1.2.val ≠ 4 * k - 1 := by omega
    simp only [reducedAdj, hxu, hxv, and_false, false_and, not_false_eq_true, and_true,
      Adj, Step, hpu, hpv, true_and]
    constructor
    · rintro ((h | h | h) | (h | h | h))
      · omega
      · exact Or.inl ⟨by omega, by omega⟩
      · exact Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))
      · omega
      · exact Or.inr (Or.inl ⟨by omega, by omega⟩)
      · exact Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩))
    · rintro (h | h | h | h)
      · left; right; left; constructor <;> omega
      · right; right; left; constructor <;> omega
      · left; right; right; constructor <;> omega
      · right; right; right; constructor <;> omega
  have pairing (i j : Fin (2 * k)) :
      dotProduct (fun u : E => if T i u then (1 : K) else 0)
        (Matrix.mulVec (fun u v : E => if reducedAdj k u.1 v.1 then (1 : K) else 0)
          (fun u => if T j u then 1 else 0)) =
      N i j 0 1 + N j i 0 1 + N i j 1 0 + N j i 1 0 := by
    change (∑ u : E, (if T i u then (1 : K) else 0) *
      ∑ v : E, (if reducedAdj k u.1 v.1 then (1 : K) else 0) *
        (if T j v then 1 else 0)) = _
    simp_rw [mul_sum]
    have individual (u v : E) :
        (if T i u then (1 : K) else 0) *
            ((if reducedAdj k u.1 v.1 then (1 : K) else 0) *
              (if T j v then 1 else 0)) =
        (if T i u ∧ T j v ∧ ar v = ar u + 0 ∧ bc v = bc u + 1 then 1 else 0) +
        (if T j v ∧ T i u ∧ ar u = ar v + 0 ∧ bc u = bc v + 1 then 1 else 0) +
        (if T i u ∧ T j v ∧ ar v = ar u + 1 ∧ bc v = bc u + 0 then 1 else 0) +
        (if T j v ∧ T i u ∧ ar u = ar v + 1 ∧ bc u = bc v + 0 then 1 else 0) := by
      rw [classify]
      by_cases hi : T i u <;> by_cases hj : T j v
      · by_cases h1 : ar v = ar u ∧ bc v = bc u + 1
        · simp [hi, hj, h1]
          omega
        · by_cases h2 : ar u = ar v ∧ bc u = bc v + 1
          · simp [hi, hj, h2]
            omega
          · by_cases h3 : ar v = ar u + 1 ∧ bc v = bc u
            · simp [hi, hj, h3]
              omega
            · simp [hi, hj, h1, h2, h3]
      · simp [hi, hj]
      · simp [hi, hj]
      · simp [hi, hj]
    simp_rw [individual, sum_add_distrib]
    rw [sum_forward, sum_forward]
    rw [sum_comm (f := fun u v : E =>
      if T j v ∧ T i u ∧ ar u = ar v + 0 ∧ bc u = bc v + 1 then (1 : K) else 0)]
    rw [sum_comm (f := fun u v : E =>
      if T j v ∧ T i u ∧ ar u = ar v + 1 ∧ bc u = bc v + 0 then (1 : K) else 0)]
    rw [sum_forward, sum_forward]
  have increasing (i j : Fin (2 * k)) (hij : i.val < j.val) :
      N i j 0 1 + N j i 0 1 + N i j 1 0 + N j i 1 0 =
        if i.val % 2 = 0 then 1 else 0 := by
    have hi := i.isLt
    have hj := j.isLt
    have hRi := rbound i
    have hRj := rbound j
    have cross : j.val ≤ R i.val := by
      dsimp [R]
      split_ifs <;> omega
    have c1 := edge_count i j 0 1 (i.val + 1) (j.val - 1)
      (min (R i.val + 1) (R j.val)) (by
        intro a b
        rw [lt_min_iff]
        omega)
    have c2 := edge_count j i 0 1 (i.val + 1) j.val
      (min (R j.val + 1) (R i.val)) (by
        intro a b
        rw [lt_min_iff]
        omega)
    have c3 := edge_count i j 1 0 (i.val + 1) j.val
      (min (R i.val) (R j.val) + 1) (by
        intro a b
        have hm : b < min (R i.val) (R j.val) + 1 ↔
            b ≤ R i.val ∧ b ≤ R j.val := by omega
        rw [hm]
        omega)
    have c4 := edge_count j i 1 0 i.val j.val
      (min (R i.val) (R j.val) + 1) (by
        intro a b
        have hm : b < min (R i.val) (R j.val) + 1 ↔
            b ≤ R i.val ∧ b ≤ R j.val := by omega
        rw [hm]
        omega)
    dsimp only [N]
    rw [c1, c2, c3, c4]
    simp only [Nat.cast_mul]
    let x := min (R i.val + 1) (R j.val) - (j.val - 1)
    let y := min (R j.val + 1) (R i.val) - j.val
    let z := min (R i.val) (R j.val) + 1 - j.val
    change ((i.val + 1 : ℕ) : K) * (x : K) +
      ((i.val + 1 : ℕ) : K) * (y : K) +
      ((i.val + 1 : ℕ) : K) * (z : K) + (i.val : K) * (z : K) = _
    by_cases hpi : i.val % 2 = 0 <;> by_cases hpj : j.val % 2 = 0
    · have hx : x % 2 = 0 := by
        dsimp [x, R]
        rw [if_pos hpi, if_pos hpj]
        omega
      have hy : y % 2 = 1 := by
        dsimp [y, R]
        rw [if_pos hpi, if_pos hpj]
        omega
      have hz : z % 2 = 0 := by
        dsimp [z, R]
        rw [if_pos hpi, if_pos hpj]
        omega
      rw [CharTwo.natCast_eq_mod (i.val + 1), CharTwo.natCast_eq_mod i.val,
        CharTwo.natCast_eq_mod x, CharTwo.natCast_eq_mod y,
        CharTwo.natCast_eq_mod z]
      simp only [hx, hy, hz, hpi,
        show (i.val + 1) % 2 = 1 by omega]
      simp
    · have hx : x % 2 = 0 := by
        dsimp [x, R]
        rw [if_pos hpi, if_neg hpj]
        omega
      have hy : y % 2 = 0 := by
        dsimp [y, R]
        rw [if_pos hpi, if_neg hpj]
        omega
      have hz : z % 2 = 1 := by
        dsimp [z, R]
        rw [if_pos hpi, if_neg hpj]
        omega
      rw [CharTwo.natCast_eq_mod (i.val + 1), CharTwo.natCast_eq_mod i.val,
        CharTwo.natCast_eq_mod x, CharTwo.natCast_eq_mod y,
        CharTwo.natCast_eq_mod z]
      simp only [hx, hy, hz, hpi,
        show (i.val + 1) % 2 = 1 by omega]
      simp
    · have hx : x % 2 = 0 := by
        dsimp [x, R]
        rw [if_neg hpi, if_pos hpj]
        omega
      have hy : y % 2 = 0 := by
        dsimp [y, R]
        rw [if_neg hpi, if_pos hpj]
        omega
      have hz : z % 2 = 0 := by
        dsimp [z, R]
        rw [if_neg hpi, if_pos hpj]
        omega
      rw [CharTwo.natCast_eq_mod (i.val + 1), CharTwo.natCast_eq_mod i.val,
        CharTwo.natCast_eq_mod x, CharTwo.natCast_eq_mod y,
        CharTwo.natCast_eq_mod z]
      simp only [hx, hy, hz,
        show i.val % 2 = 1 by omega, show (i.val + 1) % 2 = 0 by omega]
      simp
    · have hx : x % 2 = 0 := by
        dsimp [x, R]
        rw [if_neg hpi, if_neg hpj]
        omega
      have hy : y % 2 = 0 := by
        dsimp [y, R]
        rw [if_neg hpi, if_neg hpj]
        omega
      have hz : z % 2 = 0 := by
        dsimp [z, R]
        rw [if_neg hpi, if_neg hpj]
        omega
      rw [CharTwo.natCast_eq_mod (i.val + 1), CharTwo.natCast_eq_mod i.val,
        CharTwo.natCast_eq_mod x, CharTwo.natCast_eq_mod y,
        CharTwo.natCast_eq_mod z]
      simp only [hx, hy, hz,
        show i.val % 2 = 1 by omega, show (i.val + 1) % 2 = 0 by omega]
      simp
  intro i j
  change dotProduct (fun u => if T i u then (1 : K) else 0)
    (Matrix.mulVec (fun u v : E => if reducedAdj k u.1 v.1 then (1 : K) else 0)
      (fun u => if T j u then 1 else 0)) = _
  rw [pairing]
  by_cases heq : i = j
  · subst j
    rw [if_pos rfl]
    rw [CharTwo.add_self_eq_zero, zero_add, CharTwo.add_self_eq_zero]
  · rw [if_neg heq]
    by_cases hij : i.val < j.val
    · rw [increasing i j hij, min_eq_left (by omega)]
    · have hji : j.val < i.val := by
        have hne : i.val ≠ j.val := fun h => heq (Fin.ext h)
        omega
      rw [min_eq_right (by omega)]
      convert increasing j i hji using 1
      ring

end D5.S3.Combinatorics.MatchingEnumeration.BlumTriangleRectangles
