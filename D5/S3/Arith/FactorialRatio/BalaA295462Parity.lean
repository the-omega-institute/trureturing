/- GID: D5/S3/Arith/FactorialRatio/BalaA295462Parity
   generality: I
   mirror-B: D5/B/S3/Arith/FactorialRatio/BalaA295462Parity
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Bala's binary-spacing parity characterization for A295462. -/

/-
admission_basis: open-problem-resolution (#22428; Proved)
escape_witness: first_bad_pair and bad_defect_witness (the lowest short gap forces a positive valuation summand).
The rational quotient and all-pairs binary spacing retain the source expressions.
Binary support uses Nat.bitIndices and List.toFinset directly.
Direct frozen dependency declarations:
  D5/S3/Arith/FactorialRatio/OeisA347854BalaHalfIndexIntegral.mul_div_reduce
  D5/S3/Arith/FactorialRatio/OeisA347854BalaHalfIndexIntegral.grid_floor
  D5/S3/Arith/FactorialRatio/OeisA347854BalaHalfIndexIntegral.factorial_prod_dvd_of_floor
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/22536
Declarations:
  a: proof_shape: bind-only; escape_witness: none;
    consumers: claim, result, quotient_natural.
    Direct frozen dependencies: none.
  spacedBits: proof_shape: bind-only; escape_witness: none;
    consumers: tail_bound, bad_defect_witness, claim, sparse_defect_zero, result, sparse_mod, first_bad_pair.
    Direct frozen dependencies: none.
  claim: proof_shape: bind-only; escape_witness: none;
    consumers: result.
    Direct frozen dependencies: none.
  defect: proof_shape: bind-only; escape_witness: none;
    consumers: defect_mod, bad_defect_witness, quotient_valuation, sparse_defect_zero, bad_interval, denominator_dvd, result, defect_bounds.
    Direct frozen dependencies: none.
  defect_mod: proof_shape: bind-only; escape_witness: none;
    consumers: bad_defect_witness, sparse_defect_zero, defect_bounds.
    Direct frozen dependencies: mul_div_reduce.
  defect_bounds: proof_shape: bind-only; escape_witness: none;
    consumers: denominator_dvd, result.
    Direct frozen dependencies: grid_floor, mul_div_reduce.
  denominator_dvd: proof_shape: bind-only; escape_witness: none;
    consumers: quotient_natural.
    Direct frozen dependencies: factorial_prod_dvd_of_floor, grid_floor, mul_div_reduce.
  mem_bits: proof_shape: bind-only; escape_witness: none;
    consumers: sparse_defect_zero, sparse_mod, prefix_split, first_bad_pair.
    Direct frozen dependencies: none.
  sum_bits: proof_shape: bind-only; escape_witness: none;
    consumers: tail_bound, sparse_defect_zero, prefix_split, first_bad_pair.
    Direct frozen dependencies: none.
  mem_bits_mod: proof_shape: bind-only; escape_witness: none;
    consumers: tail_bound, sparse_defect_zero, sparse_mod, prefix_split, first_bad_pair.
    Direct frozen dependencies: none.
  sparse_sum_bound: proof_shape: content; escape_witness: sparse_sum_bound (finite separated-support geometric estimate);
    consumers: tail_bound.
    Direct frozen dependencies: none.
  sparse_mod: proof_shape: bind-only; escape_witness: none;
    consumers: sparse_defect_zero.
    Direct frozen dependencies: none.
  tail_bound: proof_shape: content; escape_witness: sparse_sum_bound;
    consumers: sparse_defect_zero, first_bad_pair.
    Direct frozen dependencies: none.
  prefix_split: proof_shape: bind-only; escape_witness: none;
    consumers: sparse_defect_zero, first_bad_pair.
    Direct frozen dependencies: none.
  sparse_defect_zero: proof_shape: content; escape_witness: sparse_sum_bound;
    consumers: result.
    Direct frozen dependencies: mul_div_reduce.
  bad_interval: proof_shape: bind-only; escape_witness: none;
    consumers: bad_defect_witness.
    Direct frozen dependencies: none.
  first_bad_pair: proof_shape: content; escape_witness: first_bad_pair (least short occupied pair and strict lower-tail bound);
    consumers: bad_defect_witness.
    Direct frozen dependencies: none.
  bad_defect_witness: proof_shape: content; escape_witness: first_bad_pair;
    consumers: result.
    Direct frozen dependencies: mul_div_reduce.
  quotient_natural: proof_shape: bind-only; escape_witness: none;
    consumers: result.
    Direct frozen dependencies: factorial_prod_dvd_of_floor, grid_floor, mul_div_reduce.
  quotient_valuation: proof_shape: bind-only; escape_witness: none;
    consumers: result.
    Direct frozen dependencies: none.
  odd_iff_valuation_zero: proof_shape: bind-only; escape_witness: none;
    consumers: result.
    Direct frozen dependencies: none.
  result: proof_shape: content; escape_witness: first_bad_pair and bad_defect_witness;
    consumers: none (settling result).
    Direct frozen dependencies: mul_div_reduce, grid_floor, factorial_prod_dvd_of_floor.
-/

import D5.S3.Arith.FactorialRatio.OeisA347854BalaHalfIndexIntegral
import Mathlib.Combinatorics.Colex

/-! Exact rational factorial quotients and four-separated binary support. -/

namespace D5.S3.Arith.FactorialRatio.BalaA295462Parity

/-- The factorial quotient in OEIS A295462, interpreted by exact rational division. -/
def a (n : ℕ) : ℚ :=
  ((Nat.factorial (15 * n) : ℚ) * (Nat.factorial (2 * n) : ℚ)) /
    ((Nat.factorial (10 * n) : ℚ) * (Nat.factorial (6 * n) : ℚ) *
      (Nat.factorial n : ℚ))

/-- At least three zero bits lie between any two occupied binary positions. -/
def spacedBits (n : ℕ) : Prop :=
  ∀ (i : ℕ) (j : ℕ), i < j →
    n.testBit i = true → n.testBit j = true → i + 4 ≤ j

/-- Bala's parity conjecture, with integrality made explicit. -/
def claim : Prop :=
  ∀ (n : ℕ), ∃ (m : ℕ), a n = (m : ℚ) ∧ (Odd m ↔ spacedBits n)

open scoped BigOperators
open D5.S3.Arith.FactorialRatio.OeisA347854BalaHalfIndexIntegral

private def defect (n q : ℕ) : ℤ :=
  ((15 * n / q : ℕ) : ℤ) + ((2 * n / q : ℕ) : ℤ) -
    ((10 * n / q : ℕ) : ℤ) - ((6 * n / q : ℕ) : ℤ) - ((n / q : ℕ) : ℤ)

set_option maxHeartbeats 800000 in
-- The floor and support estimates use repeated arithmetic elimination.
private theorem defect_mod (n q : ℕ) (hq : 0 < q) : defect n q = defect (n % q) q := by
  unfold defect
  have h1 := mul_div_reduce 1 n q hq
  simp only [one_mul] at h1
  rw [mul_div_reduce 15 n q hq, mul_div_reduce 2 n q hq,
    mul_div_reduce 10 n q hq, mul_div_reduce 6 n q hq, h1]
  simp only [Nat.cast_add, Nat.cast_mul]
  have hz : n % q / q = 0 := Nat.div_eq_of_lt (Nat.mod_lt n hq)
  rw [hz]
  ring

set_option maxHeartbeats 800000 in
-- The floor and support estimates use repeated arithmetic elimination.
private theorem defect_bounds (n q : ℕ) (hq : 0 < q) : 0 ≤ defect n q ∧ defect n q ≤ 1 := by
  rw [defect_mod n q hq]
  let r := n % q
  have hr : r < q := Nat.mod_lt n hq
  have hb : 30 * r / q < 30 := (Nat.div_lt_iff_lt_mul hq).mpr (by omega)
  have g15 := grid_floor 30 15 2 r q hq (by decide) (by decide)
  have g2 := grid_floor 30 2 15 r q hq (by decide) (by decide)
  have g10 := grid_floor 30 10 3 r q hq (by decide) (by decide)
  have g6 := grid_floor 30 6 5 r q hq (by decide) (by decide)
  change 0 ≤ defect r q ∧ defect r q ≤ 1
  unfold defect
  rw [g15, g2, g10, g6, Nat.div_eq_of_lt hr]
  generalize 30 * r / q = j at *
  omega

set_option maxHeartbeats 800000 in
-- The floor and support estimates use repeated arithmetic elimination.
private theorem denominator_dvd (n : ℕ) :
    (10 * n).factorial * (6 * n).factorial * n.factorial ∣
      (15 * n).factorial * (2 * n).factorial := by
  have h := factorial_prod_dvd_of_floor [15 * n, 2 * n] [10 * n, 6 * n, n] (by
    intro q hq
    have hb := (defect_bounds n q hq).1
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    unfold defect at hb
    omega)
  simpa [mul_assoc] using h



set_option maxHeartbeats 800000 in
-- The floor and support estimates use repeated arithmetic elimination.
private theorem mem_bits (n i : ℕ) : i ∈ n.bitIndices.toFinset ↔ n.testBit i = true := by
  simp [Nat.mem_bitIndices]

set_option maxHeartbeats 800000 in
-- The floor and support estimates use repeated arithmetic elimination.
private theorem sum_bits (n : ℕ) : ∑ i ∈ n.bitIndices.toFinset, 2^i = n := by
  exact Finset.sum_toFinset_bitIndices_two_pow n

set_option maxHeartbeats 800000 in
-- The floor and support estimates use repeated arithmetic elimination.
private theorem mem_bits_mod (n k i : ℕ) :
    i ∈ (n % 2^k).bitIndices.toFinset ↔ i < k ∧ n.testBit i = true := by
  simp [Nat.mem_bitIndices, Nat.testBit_mod_two_pow]

set_option maxHeartbeats 800000 in
-- The floor and support estimates use repeated arithmetic elimination.
private theorem sparse_sum_bound (s : Finset ℕ)
    (hs : ∀ i ∈ s, ∀ j ∈ s, i < j → i + 4 ≤ j)
    (e : ℕ) (he : ∀ i ∈ s, i + 4 ≤ e) : 15 * (∑ i ∈ s, 2^i) < 2^e := by
  induction s using Finset.induction_on_max generalizing e with
  | empty => simp
  | insert a s hmax ih =>
    have ha : a ∉ s := by intro ha; have := hmax a ha; omega
    have hsub : ∀ i ∈ s, ∀ j ∈ s, i < j → i + 4 ≤ j := by
      intro i hi j hj hij
      exact hs i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij
    have htail : ∀ i ∈ s, i + 4 ≤ a := by
      intro i hi
      exact hs i (Finset.mem_insert_of_mem hi) a (Finset.mem_insert_self _ _) (hmax i hi)
    have hb := ih hsub a htail
    have hae := he a (Finset.mem_insert_self _ _)
    have hp : 16 * 2^a ≤ 2^e := by
      calc
        _ = 2^(a + 4) := by rw [pow_add]; norm_num; ring
        _ ≤ _ := Nat.pow_le_pow_right (by omega) hae
    rw [Finset.sum_insert ha]
    omega

set_option maxHeartbeats 800000 in
-- The floor and support estimates use repeated arithmetic elimination.
private theorem sparse_mod (n k : ℕ) (h : spacedBits n) : spacedBits (n % 2^k) := by
  intro i j hij hi hj
  have hi' := (mem_bits_mod n k i).mp ((mem_bits _ _).mpr hi)
  have hj' := (mem_bits_mod n k j).mp ((mem_bits _ _).mpr hj)
  exact h i j hij hi'.2 hj'.2

set_option maxHeartbeats 800000 in
-- The floor and support estimates use repeated arithmetic elimination.
private theorem tail_bound (n e : ℕ) (h : spacedBits n) (he : n.testBit e = true) :
    15 * (n % 2^e) < 2^e := by
  rw [← sum_bits (n % 2^e)]
  apply sparse_sum_bound
  · intro i hi j hj hij
    have hi' := (mem_bits_mod n e i).mp hi
    have hj' := (mem_bits_mod n e j).mp hj
    exact h i j hij hi'.2 hj'.2
  · intro i hi
    have hi' := (mem_bits_mod n e i).mp hi
    exact h i e hi'.1 hi'.2 he

set_option maxHeartbeats 800000 in
-- The floor and support estimates use repeated arithmetic elimination.
private theorem prefix_split (n t : ℕ) (ht : n.testBit t = true)
    (hmax : ∀ i, n.testBit i = true → i ≤ t) : n = 2^t + n % 2^t := by
  have hs : n.bitIndices.toFinset = insert t ((n % 2^t).bitIndices.toFinset) := by
    ext i
    rw [mem_bits n i, Finset.mem_insert, mem_bits_mod]
    constructor
    · intro hi
      rcases lt_or_eq_of_le (hmax i hi) with h | h
      · exact Or.inr ⟨h, hi⟩
      · exact Or.inl h
    · rintro (rfl | ⟨_, hi⟩)
      · exact ht
      · exact hi
  have ht' : t ∉ (n % 2^t).bitIndices.toFinset := by simp
  have h := sum_bits n
  rw [hs, Finset.sum_insert ht', sum_bits] at h
  exact h.symm

set_option maxHeartbeats 800000 in
-- The floor and support estimates use repeated arithmetic elimination.
private theorem sparse_defect_zero (n : ℕ) (hn : spacedBits n) (k : ℕ) : defect n (2^k) = 0 := by
  rw [defect_mod n (2^k) (by positivity)]
  let m := n % 2^k
  by_cases hm : m = 0
  · simp [m] at hm
    simp [hm, defect]
  have hne : (m.bitIndices.toFinset).Nonempty := by
    by_contra h
    have hz : m.bitIndices.toFinset = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    have := sum_bits m
    simp [hz] at this
    omega
  let t := (m.bitIndices.toFinset).max' hne
  have htm : m.testBit t = true := (mem_bits m t).mp (Finset.max'_mem _ hne)
  have hmax : ∀ i, m.testBit i = true → i ≤ t := by
    intro i hi
    exact Finset.le_max' _ i ((mem_bits m i).mpr hi)
  have hsplit := prefix_split m t htm hmax
  have ht : t < k := ((mem_bits_mod n k t).mp ((mem_bits m t).mpr htm)).1
  have htail := tail_bound m t (sparse_mod n k hn) htm
  have hp : 0 < 2^t := by positivity
  have hq : 2^k = 2^t * 2^(k-t) := by rw [← pow_add, Nat.add_sub_of_le (by omega : t ≤ k)]
  change defect m (2^k) = 0
  rw [hsplit]
  unfold defect
  rcases (by omega : k = t + 1 ∨ k = t + 2 ∨ k = t + 3 ∨ t + 4 ≤ k) with h | h | h | h
  · rw [h, pow_add]
    norm_num only [Nat.reducePow]
    have h15 : 15 * (2^t + m % 2^t) / (2^t * 2) = 7 := Nat.div_eq_of_lt_le (by omega) (by omega)
    have h2 : 2 * (2^t + m % 2^t) / (2^t * 2) = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
    have h10 : 10 * (2^t + m % 2^t) / (2^t * 2) = 5 := Nat.div_eq_of_lt_le (by omega) (by omega)
    have h6 : 6 * (2^t + m % 2^t) / (2^t * 2) = 3 := Nat.div_eq_of_lt_le (by omega) (by omega)
    have h1 : (2^t + m % 2^t) / (2^t * 2) = 0 := Nat.div_eq_of_lt (by omega)
    rw [h15, h2, h10, h6, h1]
    norm_num
  · rw [h, pow_add]
    norm_num only [Nat.reducePow]
    have h15 : 15 * (2^t + m % 2^t) / (2^t * 4) = 3 := Nat.div_eq_of_lt_le (by omega) (by omega)
    have h2 : 2 * (2^t + m % 2^t) / (2^t * 4) = 0 := Nat.div_eq_of_lt (by omega)
    have h10 : 10 * (2^t + m % 2^t) / (2^t * 4) = 2 := Nat.div_eq_of_lt_le (by omega) (by omega)
    have h6 : 6 * (2^t + m % 2^t) / (2^t * 4) = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
    have h1 : (2^t + m % 2^t) / (2^t * 4) = 0 := Nat.div_eq_of_lt (by omega)
    rw [h15, h2, h10, h6, h1]
    norm_num
  · rw [h, pow_add]
    norm_num only [Nat.reducePow]
    have h15 : 15 * (2^t + m % 2^t) / (2^t * 8) = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
    have h2 : 2 * (2^t + m % 2^t) / (2^t * 8) = 0 := Nat.div_eq_of_lt (by omega)
    have h10 : 10 * (2^t + m % 2^t) / (2^t * 8) = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
    have h6 : 6 * (2^t + m % 2^t) / (2^t * 8) = 0 := Nat.div_eq_of_lt (by omega)
    have h1 : (2^t + m % 2^t) / (2^t * 8) = 0 := Nat.div_eq_of_lt (by omega)
    rw [h15, h2, h10, h6, h1]
    norm_num
  · have hpow : 16 * 2^t ≤ 2^k := by
      calc
        _ = 2^(t + 4) := by rw [pow_add]; norm_num; ring
        _ ≤ _ := Nat.pow_le_pow_right (by omega) h
    have h15 : 15 * (2^t + m % 2^t) / (2^k) = 0 := Nat.div_eq_of_lt (by omega)
    have h2 : 2 * (2^t + m % 2^t) / (2^k) = 0 := Nat.div_eq_of_lt (by omega)
    have h10 : 10 * (2^t + m % 2^t) / (2^k) = 0 := Nat.div_eq_of_lt (by omega)
    have h6 : 6 * (2^t + m % 2^t) / (2^k) = 0 := Nat.div_eq_of_lt (by omega)
    have h1 : (2^t + m % 2^t) / (2^k) = 0 := Nat.div_eq_of_lt (by omega)
    rw [h15, h2, h10, h6, h1]
    norm_num


set_option maxHeartbeats 800000 in
-- The floor and support estimates use repeated arithmetic elimination.
private theorem bad_interval (p R d : ℕ) (hp : 0 < p) (hR : 15 * R < p)
    (hd : d = 1 ∨ d = 2 ∨ d = 3) :
    defect ((2^d + 1) * p + R) (2^(d + 1) * p) = 1 := by
  rcases hd with rfl | rfl | rfl
  · norm_num only [pow_succ, pow_zero, mul_one, one_mul, Nat.reduceAdd, Nat.reduceMul]
    unfold defect
    have h15 : 15 * (3 * p + R) / (4 * p) = 11 := Nat.div_eq_of_lt_le (by omega) (by omega)
    have h2 : 2 * (3 * p + R) / (4 * p) = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
    have h10 : 10 * (3 * p + R) / (4 * p) = 7 := Nat.div_eq_of_lt_le (by omega) (by omega)
    have h6 : 6 * (3 * p + R) / (4 * p) = 4 := Nat.div_eq_of_lt_le (by omega) (by omega)
    have h1 : (3 * p + R) / (4 * p) = 0 := Nat.div_eq_of_lt (by omega)
    rw [h15, h2, h10, h6, h1]
    norm_num
  · norm_num only [pow_succ, pow_zero, mul_one, one_mul, Nat.reduceAdd, Nat.reduceMul]
    unfold defect
    have h15 : 15 * (5 * p + R) / (8 * p) = 9 := Nat.div_eq_of_lt_le (by omega) (by omega)
    have h2 : 2 * (5 * p + R) / (8 * p) = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
    have h10 : 10 * (5 * p + R) / (8 * p) = 6 := Nat.div_eq_of_lt_le (by omega) (by omega)
    have h6 : 6 * (5 * p + R) / (8 * p) = 3 := Nat.div_eq_of_lt_le (by omega) (by omega)
    have h1 : (5 * p + R) / (8 * p) = 0 := Nat.div_eq_of_lt (by omega)
    rw [h15, h2, h10, h6, h1]
    norm_num
  · norm_num only [pow_succ, pow_zero, mul_one, one_mul, Nat.reduceAdd, Nat.reduceMul]
    unfold defect
    have h15 : 15 * (9 * p + R) / (16 * p) = 8 := Nat.div_eq_of_lt_le (by omega) (by omega)
    have h2 : 2 * (9 * p + R) / (16 * p) = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
    have h10 : 10 * (9 * p + R) / (16 * p) = 5 := Nat.div_eq_of_lt_le (by omega) (by omega)
    have h6 : 6 * (9 * p + R) / (16 * p) = 3 := Nat.div_eq_of_lt_le (by omega) (by omega)
    have h1 : (9 * p + R) / (16 * p) = 0 := Nat.div_eq_of_lt (by omega)
    rw [h15, h2, h10, h6, h1]
    norm_num

set_option maxHeartbeats 800000 in
-- The floor and support estimates use repeated arithmetic elimination.
private theorem first_bad_pair (n : ℕ) (hn : ¬spacedBits n) :
    ∃ e t R : ℕ, e < t ∧ t < e + 4 ∧ n.testBit t = true ∧
      n % 2^(t + 1) = 2^t + 2^e + R ∧ 15 * R < 2^e := by
  classical
  have hex : ∃ t : ℕ, ∃ e : ℕ,
      e < t ∧ n.testBit e = true ∧ n.testBit t = true ∧ t < e + 4 := by
    unfold spacedBits at hn
    push Not at hn
    obtain ⟨e,t,het,he,ht,hgap⟩ := hn
    exact ⟨t,e,het,he,ht,by omega⟩
  let t := Nat.find hex
  obtain ⟨e,het,he,ht,hgap⟩ := Nat.find_spec hex
  have hgood (i j : ℕ) (hij : i < j) (hjt : j < t)
      (hi : n.testBit i = true) (hj : n.testBit j = true) : i + 4 ≤ j := by
    by_contra h
    have hbad : ∃ e, e < j ∧ n.testBit e = true ∧ n.testBit j = true ∧ j < e + 4 :=
      ⟨i,hij,hi,hj,by omega⟩
    have hmin := Nat.find_min' hex hbad
    change t ≤ j at hmin
    omega
  let m := n % 2^t
  have hsp : spacedBits m := by
    intro i j hij hi hj
    have hi' := (mem_bits_mod n t i).mp ((mem_bits m i).mpr hi)
    have hj' := (mem_bits_mod n t j).mp ((mem_bits m j).mpr hj)
    exact hgood i j hij hj'.1 hi'.2 hj'.2
  have hem : m.testBit e = true :=
    (mem_bits m e).mp ((mem_bits_mod n t e).mpr ⟨het,he⟩)
  have hmmax : ∀ i, m.testBit i = true → i ≤ e := by
    intro i hi
    have hi' := (mem_bits_mod n t i).mp ((mem_bits m i).mpr hi)
    by_contra hie
    have hge := hgood e i (by omega) hi'.1 he hi'.2
    omega
  have hm := prefix_split m e hem hmmax
  have htail := tail_bound m e hsp hem
  have htop : (n % 2^(t + 1)).bitIndices.toFinset = insert t (m.bitIndices.toFinset) := by
    ext i
    rw [mem_bits_mod, Finset.mem_insert]
    constructor
    · rintro ⟨hit,hi⟩
      by_cases hie : i = t
      · exact Or.inl hie
      · exact Or.inr ((mem_bits_mod n t i).mpr ⟨by omega,hi⟩)
    · rintro (rfl | hi)
      · exact ⟨by omega,ht⟩
      · have hi' := (mem_bits_mod n t i).mp hi
        exact ⟨by omega,hi'.2⟩
  have htm : t ∉ m.bitIndices.toFinset := by simp [m]
  have hsum := sum_bits (n % 2^(t + 1))
  rw [htop, Finset.sum_insert htm, sum_bits] at hsum
  refine ⟨e,t,m % 2^e,het,hgap,ht,?_,htail⟩
  omega

set_option maxHeartbeats 800000 in
-- The floor and support estimates use repeated arithmetic elimination.
private theorem bad_defect_witness (n : ℕ) (hn : ¬spacedBits n) :
    ∃ k : ℕ, 1 ≤ k ∧ k < 15 * n + 2 ∧ defect n (2^k) = 1 := by
  obtain ⟨e,t,R,het,hgap,ht,hsplit,hR⟩ := first_bad_pair n hn
  have hp : 0 < 2^e := by positivity
  have htn : t < n := lt_of_lt_of_le (Nat.lt_two_pow_self (n := t)) (Nat.ge_two_pow_of_testBit ht)
  refine ⟨t + 1,by omega,by omega,?_⟩
  rw [defect_mod n (2^(t + 1)) (by positivity), hsplit]
  have heq : t = e + (t-e) := by omega
  rw [heq, pow_add, show e + (t-e) + 1 = e + ((t-e) + 1) by omega, pow_add]
  have hd : t-e = 1 ∨ t-e = 2 ∨ t-e = 3 := by omega
  convert bad_interval (2^e) R (t-e) hp hR hd using 1; congr 1 <;> ring


set_option maxHeartbeats 800000 in
-- The floor and support estimates use repeated arithmetic elimination.
private theorem quotient_natural (n : ℕ) : ∃ m : ℕ,
    a n = (m : ℚ) ∧ m ≠ 0 ∧
    (15 * n).factorial * (2 * n).factorial =
      ((10 * n).factorial * (6 * n).factorial * n.factorial) * m := by
  obtain ⟨m,hm⟩ := denominator_dvd n
  refine ⟨m,?_,?_,hm⟩
  · unfold a
    have hcast : ((15 * n).factorial : ℚ) * ((2 * n).factorial : ℚ) =
        (((10 * n).factorial : ℚ) * ((6 * n).factorial : ℚ) * (n.factorial : ℚ)) * (m : ℚ) := by
      exact_mod_cast hm
    rw [hcast]
    have hD : (((10 * n).factorial : ℚ) * ((6 * n).factorial : ℚ) * (n.factorial : ℚ)) ≠ 0 := by positivity
    exact mul_div_cancel_left₀ (m : ℚ) hD
  · intro hz
    rw [hz, mul_zero] at hm
    exact (by positivity : (15 * n).factorial * (2 * n).factorial ≠ 0) hm

set_option maxHeartbeats 800000 in
-- The floor and support estimates use repeated arithmetic elimination.
private theorem quotient_valuation (n m : ℕ) (hm : m ≠ 0)
    (heq : (15 * n).factorial * (2 * n).factorial =
      ((10 * n).factorial * (6 * n).factorial * n.factorial) * m) :
    (padicValNat 2 m : ℤ) = ∑ k ∈ Finset.Ico 1 (15 * n + 2), defect n (2^k) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hv := congrArg (padicValNat 2) heq
  rw [padicValNat.mul (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _),
    padicValNat.mul (by positivity) hm,
    padicValNat.mul (by positivity) (Nat.factorial_ne_zero _),
    padicValNat.mul (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _)] at hv
  have vf (u : ℕ) (hu : u ≤ 15 * n) :
      padicValNat 2 u.factorial = ∑ k ∈ Finset.Ico 1 (15 * n + 2), u / 2^k := by
    exact padicValNat_factorial (lt_of_le_of_lt (Nat.log_le_self 2 u) (by omega))
  have hsum : (∑ k ∈ Finset.Ico 1 (15 * n + 2), defect n (2^k)) =
      (padicValNat 2 (15 * n).factorial : ℤ) + (padicValNat 2 (2 * n).factorial : ℤ) -
      (padicValNat 2 (10 * n).factorial : ℤ) - (padicValNat 2 (6 * n).factorial : ℤ) -
      (padicValNat 2 n.factorial : ℤ) := by
    rw [vf (15 * n) (by omega), vf (2 * n) (by omega), vf (10 * n) (by omega),
      vf (6 * n) (by omega), vf n (by omega)]
    simp [defect, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [hsum]
  omega

set_option maxHeartbeats 800000 in
-- The floor and support estimates use repeated arithmetic elimination.
private theorem odd_iff_valuation_zero (m : ℕ) (hm : m ≠ 0) : Odd m ↔ padicValNat 2 m = 0 := by
  rw [padicValNat.eq_zero_iff]
  simp only [OfNat.ofNat_ne_one, hm, false_or]
  exact Nat.odd_iff.trans Nat.two_dvd_ne_zero.symm

theorem result : D5.S3.Arith.FactorialRatio.BalaA295462Parity.claim := by
  intro n
  obtain ⟨m,ha,hm,heq⟩ := quotient_natural n
  refine ⟨m,ha,?_⟩
  have hv := quotient_valuation n m hm heq
  rw [odd_iff_valuation_zero m hm]
  constructor
  · intro hzero
    by_contra hn
    obtain ⟨k,hk,hkn,hw⟩ := bad_defect_witness n hn
    have hmem : k ∈ Finset.Ico 1 (15 * n + 2) := Finset.mem_Ico.mpr ⟨hk,hkn⟩
    have hle : defect n (2^k) ≤ ∑ j ∈ Finset.Ico 1 (15 * n + 2), defect n (2^j) :=
      Finset.single_le_sum (fun j _ => (defect_bounds n (2^j) (by positivity)).1) hmem
    rw [hw, ← hv, hzero] at hle
    norm_num at hle
  · intro hn
    have hz : (∑ k ∈ Finset.Ico 1 (15 * n + 2), defect n (2^k)) = 0 := by
      apply Finset.sum_eq_zero
      intro k _
      exact sparse_defect_zero n hn k
    rw [hz] at hv
    exact_mod_cast hv

end D5.S3.Arith.FactorialRatio.BalaA295462Parity
