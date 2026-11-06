/- GID: D5/S3/Combinatorics/Circle/MersenneExceptional19Nonboolean
   generality: G
   mirror-B: none(waiver:source-preparation-only)
   mirror-E: none(waiver:source-preparation-only)
   anchors: [D5/S3/Combinatorics/Circle/SourceWidth]
   utility: none
   digest: An infinite exceptional-19 family of physical zero pairs with negative intersection. -/
module
public import D5.S3.Combinatorics.Circle.SourceWidth
public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Algebra.BigOperators.Fin

/-!
Source-only candidate, UNCOMPILED. This file makes no kernel, registration,
independent-review, novelty, or official-delivery claim.

Ordinary-proof input: exceptional-19-infinite-nonboolean-ordinary-proof-20261106.txt,
SHA256 c532a26ee09774c073794158788d4ed0299c07b42b9b3f054b3964c3f2d7420f.
The supplied oracle reasoning and finite controls are not Lean evidence.
The only public theorem below quantifies over every natural r, including zero.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section

namespace D5.S3.Combinatorics.Circle.MersenneExceptional19Nonboolean

open scoped BigOperators
open SourceWidth

private def base (r : ℕ) : ℕ := 2 ^ (18 * r + 12)

private theorem base_step (r : ℕ) : base (r + 1) = 262144 * base r := by
  unfold base
  have he : 18 * (r + 1) + 12 = (18 * r + 12) + 18 := by omega
  rw [he, pow_add]
  norm_num <;> ring

private theorem base_lower (r : ℕ) : 4096 ≤ base r := by
  have h := Nat.pow_le_pow_right (by decide : 0 < 2)
    (show 12 ≤ 18 * r + 12 by omega)
  norm_num at h
  exact h

-- These are the literal low/high blocks of u-1, a-1, h, b.
private def um : ℕ → ℕ
  | 0 => 2586
  | r + 1 => 262144 * um r + 248346

private def am : ℕ → ℕ
  | 0 => 1077
  | r + 1 => 262144 * am r + 234549

private def hiQ : ℕ → ℕ
  | 0 => 215
  | r + 1 => 262144 * hiQ r + 151767

private def hiTwoQ : ℕ → ℕ
  | 0 => 431
  | r + 1 => 262144 * hiTwoQ r + 41391

private def xm : ℕ → ℕ
  | 0 => 16
  | r + 1 => 262144 * xm r + 229392

private def yy : ℕ → ℕ
  | 0 => 135
  | r + 1 => 262144 * yy r + 135

private theorem block_equations (r : ℕ) :
    19 * (um r + 1) = 12 * base r + 1 ∧
    19 * (am r + 1) = 5 * base r + 2 ∧
    19 * hiQ r + 11 = base r ∧
    19 * hiTwoQ r + 3 = 2 * base r := by
  induction r with
  | zero => norm_num [um, am, hiQ, hiTwoQ, base]
  | succ r ih =>
    rcases ih with ⟨hu, ha, hh, hb⟩
    simp only [um, am, hiQ, hiTwoQ, base_step]
    constructor
    · nlinarith
    constructor
    · nlinarith
    constructor <;> nlinarith

private theorem terminal_bits (r : ℕ) : um r % 4 = 2 ∧ am r % 4 = 1 := by
  cases r with
  | zero => norm_num [um, am]
  | succ r => norm_num [um, am, Nat.add_mod, Nat.mul_mod]

private theorem add_one_carry (x y : ℕ) (hx : x % 4 = 2) (hy : y % 4 = 1) :
    (x + 1) &&& (y + 1) = (x &&& y) + 2 := by
  have hx0 : x = Nat.bit false (Nat.bit true (x / 4)) := by
    simp only [Nat.bit_val]
    norm_num
    omega
  have hy0 : y = Nat.bit true (Nat.bit false (y / 4)) := by
    simp only [Nat.bit_val]
    norm_num
    omega
  have hx1 : x + 1 = Nat.bit true (Nat.bit true (x / 4)) := by
    simp only [Nat.bit_val]
    norm_num
    omega
  have hy1 : y + 1 = Nat.bit false (Nat.bit true (y / 4)) := by
    simp only [Nat.bit_val]
    norm_num
    omega
  conv_lhs => rw [hx1, hy1]
  conv_rhs => rw [hx0, hy0]
  simp only [Nat.land_bit]
  norm_num [Nat.bit_val] <;> ring

private theorem land_low_block (x y : ℕ) :
    (262144 * x + 248346) &&& (262144 * y + 234549) =
      262144 * (x &&& y) + 229392 := by
  have hx : 262144 * x + 248346 = Nat.bit false (Nat.bit true (Nat.bit false (Nat.bit true (Nat.bit true (Nat.bit false (Nat.bit false (Nat.bit false (Nat.bit false (Nat.bit true (Nat.bit false (Nat.bit true (Nat.bit false (Nat.bit false (Nat.bit true (Nat.bit true (Nat.bit true (Nat.bit true (x)))))))))))))))))) := by
    norm_num [Nat.bit_val] <;> ring
  have hy : 262144 * y + 234549 = Nat.bit true (Nat.bit false (Nat.bit true (Nat.bit false (Nat.bit true (Nat.bit true (Nat.bit false (Nat.bit false (Nat.bit false (Nat.bit false (Nat.bit true (Nat.bit false (Nat.bit true (Nat.bit false (Nat.bit false (Nat.bit true (Nat.bit true (Nat.bit true (y)))))))))))))))))) := by
    norm_num [Nat.bit_val] <;> ring
  rw [hx, hy]
  simp only [Nat.land_bit]
  norm_num [Nat.bit_val] <;> ring

private theorem land_high_block (x y : ℕ) :
    (262144 * x + 151767) &&& (262144 * y + 41391) =
      262144 * (x &&& y) + 135 := by
  have hx : 262144 * x + 151767 = Nat.bit true (Nat.bit true (Nat.bit true (Nat.bit false (Nat.bit true (Nat.bit false (Nat.bit true (Nat.bit true (Nat.bit false (Nat.bit false (Nat.bit false (Nat.bit false (Nat.bit true (Nat.bit false (Nat.bit true (Nat.bit false (Nat.bit false (Nat.bit true (x)))))))))))))))))) := by
    norm_num [Nat.bit_val] <;> ring
  have hy : 262144 * y + 41391 = Nat.bit true (Nat.bit true (Nat.bit true (Nat.bit true (Nat.bit false (Nat.bit true (Nat.bit false (Nat.bit true (Nat.bit true (Nat.bit false (Nat.bit false (Nat.bit false (Nat.bit false (Nat.bit true (Nat.bit false (Nat.bit true (Nat.bit false (Nat.bit false (y)))))))))))))))))) := by
    norm_num [Nat.bit_val] <;> ring
  rw [hx, hy]
  simp only [Nat.land_bit]
  norm_num [Nat.bit_val] <;> ring


private theorem block_intersections (r : ℕ) :
    (um r &&& am r) = xm r ∧ (hiQ r &&& hiTwoQ r) = yy r := by
  induction r with
  | zero => constructor <;> decide
  | succ r ih =>
    constructor
    · simp only [um, am, xm, land_low_block, ih.1]
    · simp only [hiQ, hiTwoQ, yy, land_high_block, ih.2]

private theorem intersection_equations (r : ℕ) :
    9709 * ((um r + 1) &&& (am r + 1)) = 40 * base r + 10922 ∧
    9709 * (hiQ r &&& hiTwoQ r) + 5 = 320 * base r := by
  have hb := block_intersections r
  have ht := terminal_bits r
  rw [add_one_carry _ _ ht.1 ht.2, hb.1, hb.2]
  clear hb ht
  suffices 9709 * (xm r + 2) = 40 * base r + 10922 ∧
      9709 * yy r + 5 = 320 * base r by exact this
  induction r with
  | zero => norm_num [xm, yy, base]
  | succ r ih =>
    simp only [xm, yy, base_step]
    constructor <;> nlinarith [ih.1, ih.2]

private theorem land_blocks (d L A U V : ℕ) (hL : L < 2 ^ d) (hA : A < 2 ^ d) :
    ((L + 2 ^ d * U) &&& (A + 2 ^ d * V)) =
      (L &&& A) + 2 ^ d * (U &&& V) := by
  have hX : (L &&& A) < 2 ^ d := Nat.and_lt_two_pow L hA
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_land]
  rw [Nat.add_comm L, Nat.add_comm A, Nat.add_comm (L &&& A)]
  rw [Nat.testBit_two_pow_mul_add U hL,
    Nat.testBit_two_pow_mul_add V hA,
    Nat.testBit_two_pow_mul_add (U &&& V) hX]
  by_cases hi : i < d <;> simp [hi, Nat.testBit_land]

private theorem binary_value (k n : ℕ) (hn : n < 2 ^ k) :
    (∑ i ∈ Finset.range k, if n.testBit i = true then (2 : ℤ) ^ i else 0) = (n : ℤ) := by
  induction k generalizing n with
  | zero =>
    have : n = 0 := by simpa using hn
    simp [this]
  | succ k ih =>
    have hd : n / 2 < 2 ^ k := by
      rw [pow_succ] at hn
      omega
    rw [Finset.sum_range_succ']
    have hs :
        (∑ i ∈ Finset.range k,
          if n.testBit (i + 1) = true then (2 : ℤ) ^ (i + 1) else 0) =
          2 * ∑ i ∈ Finset.range k,
            if (n / 2).testBit i = true then (2 : ℤ) ^ i else 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [Nat.testBit_add_one, pow_succ]
      split_ifs <;> ring
    rw [hs, ih (n / 2) hd]
    have he := Nat.mod_add_div n 2
    by_cases hb : n % 2 = 1
    · simp only [Nat.testBit_zero, hb, decide_true, if_true, pow_zero]
      omega
    · have hz : n % 2 = 0 := by omega
      simp only [Nat.testBit_zero, hz, Nat.zero_ne_one, decide_false,
        Bool.false_eq_true, if_false]
      omega

private def weight (d t i : ℕ) : ℤ :=
  centered (modulus (3 * d)) ((2 : ℤ) ^ i * (t : ℤ))

private def selectedSum (d t M : ℕ) : ℤ :=
  ∑ i ∈ (Finset.univ.filter (fun i : Fin (3 * d) => M.testBit i.val = true)),
    actualSource (3 * d) t i

private theorem selectedSum_range (d t M : ℕ) :
    selectedSum d t M =
      ∑ i ∈ Finset.range (3 * d), if M.testBit i = true then weight d t i else 0 := by
  classical
  unfold selectedSum
  rw [Finset.sum_filter]
  simpa only [actualSource, weight] using
    (Fin.sum_univ_eq_sum_range
      (fun i => if M.testBit i = true then weight d t i else 0) (3 * d))

private theorem centered_of_representative {N x v : ℤ}
    (hN : 0 < N) (ho : N % 2 = 1)
    (hv : -N < 2 * v ∧ 2 * v < N)
    (q : ℤ) (hq : x = v + q * N) : centered N x = v := by
  apply centered_unique hN ho (centered_bounds hN ho x)
  · have he := Int.emod_add_mul_ediv N 2
    omega
  · rw [centered_mod, hq, Int.add_mul_emod_self_right]

private theorem source_parameters (d : ℕ) (hd : 12 ≤ d) :
    let B : ℕ := 2 ^ d
    let g : ℤ := (B : ℤ) - 1
    let H : ℤ := (B : ℤ) ^ 2 + B + 1
    4096 ≤ B ∧
    0 < g ∧ 0 < H ∧
    modulus (3 * d) = g * H ∧
    0 < modulus (3 * d) ∧ modulus (3 * d) % 2 = 1 ∧
    (((B - 1) * (2 * B - 3) : ℕ) : ℤ) = g * (2 * B - 3) := by
  dsimp
  have hBn : 4096 ≤ (2 : ℕ) ^ d := by
    have h := Nat.pow_le_pow_right (by decide : 0 < 2) hd
    norm_num at h
    exact h
  have hB : (4096 : ℤ) ≤ ((2 : ℕ) ^ d : ℤ) := by exact_mod_cast hBn
  have hcast : (((2 : ℕ) ^ d : ℕ) : ℤ) = (2 : ℤ) ^ d := by norm_cast
  have hN : modulus (3 * d) =
      (((2 : ℕ) ^ d : ℤ) - 1) *
        (((2 : ℕ) ^ d : ℤ) ^ 2 + ((2 : ℕ) ^ d : ℤ) + 1) := by
    dsimp [modulus]
    have he : 3 * d = d * 3 := by omega
    rw [he, pow_mul]
    ring
  have hpos : 0 < modulus (3 * d) := by
    rw [hN]
    exact mul_pos (by omega) (by positivity)
  have hodd : modulus (3 * d) % 2 = 1 := by
    have he : 3 * d = (3 * d - 1) + 1 := by omega
    rw [modulus, he, pow_succ]
    omega
  refine ⟨hBn, by omega, by positivity, hN, hpos, hodd, ?_⟩
  norm_num [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ (2 : ℕ) ^ d),
    Nat.cast_sub (by omega : 3 ≤ 2 * (2 : ℕ) ^ d)]

private theorem scale_bounds {g H v : ℤ} (hg : 0 < g)
    (hv : -H < 2 * v ∧ 2 * v < H) :
    -(g * H) < 2 * (g * v) ∧ 2 * (g * v) < g * H := by
  constructor
  · calc
      -(g * H) = g * (-H) := by ring
      _ < g * (2 * v) := mul_lt_mul_of_pos_left hv.1 hg
      _ = 2 * (g * v) := by ring
  · calc
      2 * (g * v) = g * (2 * v) := by ring
      _ < g * H := mul_lt_mul_of_pos_left hv.2 hg

private theorem weight_low (d B i : ℕ) (hd : 12 ≤ d)
    (hB : B = 2 ^ d) (hi : i < d) :
    weight d ((B - 1) * (2 * B - 3)) i =
      ((B : ℤ) - 1) * ((2 * (B : ℤ) - 3) * (2 : ℤ) ^ i -
        if i = d - 1 then (B : ℤ) ^ 2 + B + 1 else 0) := by
  have hp := source_parameters d hd
  dsimp only at hp
  rw [← hB] at hp
  rcases hp with ⟨hBn, hg, hH, hN, hpos, hodd, ht⟩
  have hBi : (4096 : ℤ) ≤ (B : ℤ) := by exact_mod_cast hBn
  have hpowB : (2 : ℤ) ^ d = (B : ℤ) := by exact_mod_cast hB.symm
  let g : ℤ := (B : ℤ) - 1
  let H : ℤ := (B : ℤ) ^ 2 + B + 1
  let m : ℤ := 2 * B - 3
  change modulus (3 * d) = g * H at hN
  change 0 < g at hg
  change 0 < H at hH
  change (((B - 1) * (2 * B - 3) : ℕ) : ℤ) = g * m at ht
  unfold weight
  rw [ht]
  change centered (modulus (3 * d)) ((2 : ℤ) ^ i * (g * m)) =
    g * (m * (2 : ℤ) ^ i - if i = d - 1 then H else 0)
  by_cases hiTop : i = d - 1
  · rw [if_pos hiTop]
    have hz : 2 * (2 : ℤ) ^ i = (B : ℤ) := by
      calc
        2 * (2 : ℤ) ^ i = (2 : ℤ) ^ (i + 1) := by rw [pow_succ']
        _ = (2 : ℤ) ^ d := by congr 1; omega
        _ = (B : ℤ) := hpowB
    have hz' := congrArg (fun z : ℤ => m * z) hz
    have hquad := mul_nonneg (show (0 : ℤ) ≤ B by omega)
      (show (0 : ℤ) ≤ (B : ℤ) - 5 by omega)
    have hv : -H < 2 * (m * (2 : ℤ) ^ i - H) ∧
        2 * (m * (2 : ℤ) ^ i - H) < H := by
      dsimp [m, H] at *
      constructor <;> nlinarith [hquad]
    apply centered_of_representative hpos hodd
      (by rw [hN]; exact scale_bounds hg hv) 1
    rw [hN]
    ring
  · rw [if_neg hiTop, sub_zero]
    have hz : 4 * (2 : ℤ) ^ i ≤ (B : ℤ) := by
      have he : i + 2 ≤ d := by omega
      have hh := Nat.pow_le_pow_right (by decide : 0 < 2) he
      have hh' : (2 : ℤ) ^ (i + 2) ≤ (B : ℤ) := by
        rw [hB]
        exact_mod_cast hh
      norm_num [pow_add] at hh'
      nlinarith
    have hzpos : 0 < (2 : ℤ) ^ i := by positivity
    have hm : 0 < m := by dsimp [m]; omega
    have hmul := mul_nonneg (le_of_lt hm)
      (show 0 ≤ (B : ℤ) - 4 * (2 : ℤ) ^ i by omega)
    have hv : -H < 2 * (m * (2 : ℤ) ^ i) ∧
        2 * (m * (2 : ℤ) ^ i) < H := by
      dsimp [m, H] at *
      constructor <;> nlinarith [mul_pos hm hzpos]
    apply centered_of_representative hpos hodd
      (by rw [hN]; exact scale_bounds hg hv) 0
    ring

private theorem weight_high (d B j : ℕ) (hd : 12 ≤ d)
    (hB : B = 2 ^ d) (hj : j < d - 3) :
    weight d ((B - 1) * (2 * B - 3)) (d + j) =
      -(((B : ℤ) - 1) * (5 * (B : ℤ) + 2)) * (2 : ℤ) ^ j := by
  have hp := source_parameters d hd
  dsimp only at hp
  rw [← hB] at hp
  rcases hp with ⟨hBn, hg, hH, hN, hpos, hodd, ht⟩
  have hBi : (4096 : ℤ) ≤ (B : ℤ) := by exact_mod_cast hBn
  have hpowB : (2 : ℤ) ^ d = (B : ℤ) := by exact_mod_cast hB.symm
  let g : ℤ := (B : ℤ) - 1
  let H : ℤ := (B : ℤ) ^ 2 + B + 1
  let c : ℤ := 5 * B + 2
  let m : ℤ := 2 * B - 3
  change modulus (3 * d) = g * H at hN
  change 0 < g at hg
  change 0 < H at hH
  change (((B - 1) * (2 * B - 3) : ℕ) : ℤ) = g * m at ht
  have hz : 16 * (2 : ℤ) ^ j ≤ (B : ℤ) := by
    have hh := Nat.pow_le_pow_right (by decide : 0 < 2)
      (show j + 4 ≤ d by omega)
    have hh' : (2 : ℤ) ^ (j + 4) ≤ (B : ℤ) := by
      rw [hB]
      exact_mod_cast hh
    norm_num [pow_add] at hh'
    nlinarith
  have hzpos : 0 < (2 : ℤ) ^ j := by positivity
  have hc : 0 < c := by dsimp [c]; omega
  have hmul := mul_nonneg (le_of_lt hc)
    (show 0 ≤ (B : ℤ) - 16 * (2 : ℤ) ^ j by omega)
  have hv : -H < 2 * (-c * (2 : ℤ) ^ j) ∧
      2 * (-c * (2 : ℤ) ^ j) < H := by
    dsimp [c, H] at *
    constructor <;> nlinarith [mul_pos hc hzpos]
  unfold weight
  rw [ht, pow_add, hpowB]
  change centered (modulus (3 * d))
    ((B : ℤ) * (2 : ℤ) ^ j * (g * m)) = -(g * c) * (2 : ℤ) ^ j
  have he : -(g * c) * (2 : ℤ) ^ j = g * (-c * (2 : ℤ) ^ j) := by ring
  rw [he]
  apply centered_of_representative hpos hodd
    (by rw [hN]; exact scale_bounds hg hv) (2 * (2 : ℤ) ^ j)
  rw [hN]
  dsimp [g, H, c, m]
  ring

private theorem bounded_mask_sum (d B L U : ℕ) (hd : 12 ≤ d)
    (hB : B = 2 ^ d) (hL : L < B) (hU : U < 2 ^ (d - 3)) :
    selectedSum d ((B - 1) * (2 * B - 3)) (L + B * U) =
      ((B : ℤ) - 1) *
        ((2 * (B : ℤ) - 3) * (L : ℤ) -
          ((B : ℤ) ^ 2 + B + 1) *
            (if L.testBit (d - 1) = true then (1 : ℤ) else 0) -
          (5 * (B : ℤ) + 2) * (U : ℤ)) := by
  classical
  let t : ℕ := (B - 1) * (2 * B - 3)
  let g : ℤ := (B : ℤ) - 1
  let m : ℤ := 2 * B - 3
  let H : ℤ := (B : ℤ) ^ 2 + B + 1
  let c : ℤ := 5 * B + 2
  let e : ℤ := if L.testBit (d - 1) = true then 1 else 0
  have hL' : L < 2 ^ d := by simpa only [hB] using hL
  have hmask : L + B * U = 2 ^ d * U + L := by rw [hB]; omega
  have hbitLow (i : ℕ) (hi : i < d) :
      (L + B * U).testBit i = L.testBit i := by
    rw [hmask, Nat.testBit_two_pow_mul_add U hL']
    simp only [if_pos hi]
  have hbitHigh (j : ℕ) :
      (L + B * U).testBit (d + j) = U.testBit j := by
    rw [hmask, Nat.testBit_two_pow_mul_add U hL']
    simp [show ¬d + j < d by omega]
  have hlo :
      (∑ i ∈ Finset.range d,
        if (L + B * U).testBit i = true then weight d t i else 0) =
        g * (m * (L : ℤ) - H * e) := by
    calc
      _ = ∑ i ∈ Finset.range d,
          (g * m * (if L.testBit i = true then (2 : ℤ) ^ i else 0) -
            if i = d - 1 then g * H * e else 0) := by
        apply Finset.sum_congr rfl
        intro i hi
        have hir : i < d := Finset.mem_range.mp hi
        rw [hbitLow i hir]
        have hw := weight_low d B i hd hB hir
        change weight d t i = g * (m * (2 : ℤ) ^ i -
          if i = d - 1 then H else 0) at hw
        rw [hw]
        by_cases hit : i = d - 1
        · subst i
          by_cases hb : L.testBit (d - 1) = true <;>
            simp [hb, e] <;> ring
        · by_cases hb : L.testBit i = true <;>
            simp [hit, hb] <;> ring
      _ = g * m *
          (∑ i ∈ Finset.range d, if L.testBit i = true then (2 : ℤ) ^ i else 0) -
          ∑ i ∈ Finset.range d, if i = d - 1 then g * H * e else 0 := by
        rw [Finset.sum_sub_distrib, Finset.mul_sum]
      _ = g * (m * (L : ℤ) - H * e) := by
        rw [binary_value d L hL']
        simp only [Finset.sum_ite_eq', Finset.mem_range,
          show d - 1 < d by omega, if_true]
        ring
  have hU' : U < 2 ^ (2 * d) :=
    lt_of_lt_of_le hU (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega))
  have hhi :
      (∑ j ∈ Finset.range (2 * d),
        if (L + B * U).testBit (d + j) = true then weight d t (d + j) else 0) =
        -(g * c) * (U : ℤ) := by
    calc
      _ = ∑ j ∈ Finset.range (2 * d),
          -(g * c) * (if U.testBit j = true then (2 : ℤ) ^ j else 0) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [hbitHigh]
        by_cases hb : U.testBit j = true
        · have hj : j < d - 3 := by
            by_contra hn
            have hlt : U < 2 ^ j := lt_of_lt_of_le hU
              (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega))
            have hf := Nat.testBit_lt_two_pow hlt
            rw [hb] at hf
            contradiction
          rw [if_pos hb, if_pos hb]
          exact weight_high d B j hd hB hj
        · simp only [if_neg hb, mul_zero]
      _ = -(g * c) *
          (∑ j ∈ Finset.range (2 * d), if U.testBit j = true then (2 : ℤ) ^ j else 0) :=
        (Finset.mul_sum ..).symm
      _ = -(g * c) * (U : ℤ) := by rw [binary_value (2 * d) U hU']
  change selectedSum d t (L + B * U) =
    g * (m * (L : ℤ) - H * e - c * (U : ℤ))
  rw [selectedSum_range,
    show 3 * d = d + 2 * d by omega, Finset.sum_range_add, hlo, hhi]
  ring

set_option maxHeartbeats 1000000 in
/-- For every r, the two literal masks on the original physical labels have
integer sum zero, while their physical intersection has the exact negative sum. -/
theorem exceptional19_zero_pair_intersection (r : ℕ) :
    let d : ℕ := 18 * r + 12
    let B : ℕ := 2 ^ d
    let g : ℕ := B - 1
    let t : ℕ := g * (2 * B - 3)
    let Q : ℕ := (B ^ 2 + B + 1) / 19
    let A : Finset (Fin (3 * d)) :=
      Finset.univ.filter (fun i => Nat.testBit Q i.val = true)
    let C : Finset (Fin (3 * d)) :=
      Finset.univ.filter (fun i => Nat.testBit (2 * Q) i.val = true)
    (∑ i ∈ A, SourceWidth.actualSource (3 * d) t i) = (0 : ℤ) ∧
    (∑ i ∈ C, SourceWidth.actualSource (3 * d) t i) = (0 : ℤ) ∧
    (511 : ℤ) * (∑ i ∈ A ∩ C, SourceWidth.actualSource (3 * d) t i) =
      -((B : ℤ) - 1) * (80 * (B : ℤ) ^ 2 - 1111 * (B : ℤ) + 1724) ∧
    (∑ i ∈ A ∩ C, SourceWidth.actualSource (3 * d) t i) < (0 : ℤ) := by
  classical
  let d : ℕ := 18 * r + 12
  let B : ℕ := 2 ^ d
  let t : ℕ := (B - 1) * (2 * B - 3)
  let Q : ℕ := (B ^ 2 + B + 1) / 19
  let A : Finset (Fin (3 * d)) :=
    Finset.univ.filter (fun i => Nat.testBit Q i.val = true)
  let C : Finset (Fin (3 * d)) :=
    Finset.univ.filter (fun i => Nat.testBit (2 * Q) i.val = true)
  change (∑ i ∈ A, actualSource (3 * d) t i) = (0 : ℤ) ∧
    (∑ i ∈ C, actualSource (3 * d) t i) = (0 : ℤ) ∧
    (511 : ℤ) * (∑ i ∈ A ∩ C, actualSource (3 * d) t i) =
      -((B : ℤ) - 1) * (80 * (B : ℤ) ^ 2 - 1111 * (B : ℤ) + 1724) ∧
    (∑ i ∈ A ∩ C, actualSource (3 * d) t i) < (0 : ℤ)
  have hd : 12 ≤ d := by dsimp [d]; omega
  have hB : B = 2 ^ d := rfl
  have hbase : base r = B := rfl
  have hBn : 4096 ≤ B := by simpa only [hbase] using base_lower r
  have hBi : (4096 : ℤ) ≤ (B : ℤ) := by exact_mod_cast hBn
  let u : ℕ := um r + 1
  let a : ℕ := am r + 1
  let h : ℕ := hiQ r
  let b : ℕ := hiTwoQ r
  let X : ℕ := u &&& a
  let Y : ℕ := h &&& b
  have hblocks := block_equations r
  rw [hbase] at hblocks
  change 19 * u = 12 * B + 1 ∧ 19 * a = 5 * B + 2 ∧
    19 * h + 11 = B ∧ 19 * b + 3 = 2 * B at hblocks
  rcases hblocks with ⟨hu, ha, hh, hb⟩
  have hQeq : 19 * (u + B * h) = B ^ 2 + B + 1 := by
    have hhB := congrArg (fun z : ℕ => B * z) hh
    nlinarith only [hu, hhB]
  have hQ : Q = u + B * h := by dsimp [Q]; omega
  have hTwoQeq : 19 * (a + B * b) = 2 * (B ^ 2 + B + 1) := by
    have hbB := congrArg (fun z : ℕ => B * z) hb
    nlinarith only [ha, hbB]
  have hTwoQ : 2 * Q = a + B * b := by
    rw [hQ]
    nlinarith only [hQeq, hTwoQeq]
  have huLt : u < B := by omega
  have haLt : a < B := by omega
  have hhalf : B = 2 * 2 ^ (d - 1) := by
    calc
      B = 2 ^ d := hB
      _ = 2 ^ ((d - 1) + 1) := by congr 1
      _ = 2 * 2 ^ (d - 1) := by rw [pow_succ]; ring
  have hsmall : B = 8 * 2 ^ (d - 3) := by
    calc
      B = 2 ^ d := hB
      _ = 2 ^ ((d - 3) + 3) := by congr 1
      _ = 8 * 2 ^ (d - 3) := by rw [pow_add]; norm_num <;> ring
  have lower_half : ∀ (B u p : ℕ), B = 2 * p → 19 * u = 12 * B + 1 → p ≤ u := by
    intro B u p hB hu
    omega
  have upper_half : ∀ (B a p : ℕ), B = 2 * p → 19 * a = 5 * B + 2 → a < p := by
    intro B a p hB ha
    omega
  have upper_small : ∀ (B h q : ℕ), B = 8 * q → 19 * h + 11 = B → h < q := by
    intro B h q hB hh
    omega
  have upper_small_two : ∀ (B b q : ℕ), B = 8 * q → 19 * b + 3 = 2 * B → b < q := by
    intro B b q hB hb
    omega
  have huHalf : 2 ^ (d - 1) ≤ u := lower_half B u (2 ^ (d - 1)) hhalf hu
  have haHalf : a < 2 ^ (d - 1) := upper_half B a (2 ^ (d - 1)) hhalf ha
  have hhLt : h < 2 ^ (d - 3) := upper_small B h (2 ^ (d - 3)) hsmall hh
  have hbLt : b < 2 ^ (d - 3) := upper_small_two B b (2 ^ (d - 3)) hsmall hb
  have htopU : u.testBit (d - 1) = true := by
    apply Nat.testBit_of_two_pow_le_and_two_pow_add_one_gt huHalf
    rw [show d - 1 + 1 = d by omega]
    simpa only [← hB] using huLt
  have htopA : a.testBit (d - 1) = false := Nat.testBit_lt_two_pow haHalf
  have hXLt : X < B := by
    rw [hB]
    exact Nat.and_lt_two_pow u (by simpa only [← hB] using haLt)
  have hYLt : Y < 2 ^ (d - 3) := Nat.and_lt_two_pow h hbLt
  have htopX : X.testBit (d - 1) = false :=
    Nat.testBit_lt_two_pow (Nat.and_lt_two_pow u haHalf)
  have hmask : (Q &&& (2 * Q)) = X + B * Y := by
    calc
      (Q &&& (2 * Q)) = (u + B * h) &&& (a + B * b) :=
        congrArg₂ (fun x y : ℕ => x &&& y) hQ hTwoQ
      _ = X + B * Y := by
        simpa only [← hB] using
          land_blocks d u a h b (by simpa only [← hB] using huLt)
            (by simpa only [← hB] using haLt)
  have hphysical : A ∩ C =
      Finset.univ.filter (fun i : Fin (3 * d) =>
        Nat.testBit (Q &&& (2 * Q)) i.val = true) := by
    ext i
    simp [A, C, Nat.testBit_land]
  have huZ : 19 * (u : ℤ) = 12 * (B : ℤ) + 1 := by exact_mod_cast hu
  have haZ : 19 * (a : ℤ) = 5 * (B : ℤ) + 2 := by exact_mod_cast ha
  have hhZ : 19 * (h : ℤ) + 11 = (B : ℤ) := by exact_mod_cast hh
  have hbZ : 19 * (b : ℤ) + 3 = 2 * (B : ℤ) := by exact_mod_cast hb
  let gZ : ℤ := (B : ℤ) - 1
  let m : ℤ := 2 * (B : ℤ) - 3
  let H : ℤ := (B : ℤ) ^ 2 + B + 1
  let c : ℤ := 5 * (B : ℤ) + 2
  have huCancel : m * (u : ℤ) - H - c * (h : ℤ) = 0 := by
    have he1 := congrArg (fun z : ℤ => m * z) huZ
    have he2 := congrArg (fun z : ℤ => c * z) hhZ
    dsimp [m, H, c] at *
    nlinarith only [he1, he2]
  have haCancel : m * (a : ℤ) - c * (b : ℤ) = 0 := by
    have he1 := congrArg (fun z : ℤ => m * z) haZ
    have he2 := congrArg (fun z : ℤ => c * z) hbZ
    dsimp [m, c] at *
    nlinarith only [he1, he2]
  have hSA : selectedSum d t Q = 0 := by
    rw [hQ]
    rw [bounded_mask_sum d B u h hd hB huLt hhLt, htopU]
    change gZ * (m * (u : ℤ) - H * 1 - c * (h : ℤ)) = 0
    simpa only [mul_one, huCancel, mul_zero]
  have hSC : selectedSum d t (2 * Q) = 0 := by
    rw [hTwoQ]
    rw [bounded_mask_sum d B a b hd hB haLt hbLt, htopA]
    change gZ * (m * (a : ℤ) - H * 0 - c * (b : ℤ)) = 0
    simpa only [mul_zero, sub_zero, haCancel]
  have hSI : selectedSum d t (Q &&& (2 * Q)) =
      gZ * (m * (X : ℤ) - c * (Y : ℤ)) := by
    rw [hmask, bounded_mask_sum d B X Y hd hB hXLt hYLt, htopX]
    simp only [Bool.false_eq_true, if_false, mul_zero, sub_zero]
    dsimp [gZ, m, c]
  have hxy := intersection_equations r
  rw [hbase] at hxy
  change 9709 * X = 40 * B + 10922 ∧ 9709 * Y + 5 = 320 * B at hxy
  have hxZ : 9709 * (X : ℤ) = 40 * (B : ℤ) + 10922 := by exact_mod_cast hxy.1
  have hyZ : 9709 * (Y : ℤ) + 5 = 320 * (B : ℤ) := by exact_mod_cast hxy.2
  have hinner : 511 * (m * (X : ℤ) - c * (Y : ℤ)) =
      -(80 * (B : ℤ) ^ 2 - 1111 * (B : ℤ) + 1724) := by
    have he1 := congrArg (fun z : ℤ => m * z) hxZ
    have he2 := congrArg (fun z : ℤ => c * z) hyZ
    dsimp [m, c] at *
    nlinarith only [he1, he2]
  have hformula : 511 * selectedSum d t (Q &&& (2 * Q)) =
      -((B : ℤ) - 1) * (80 * (B : ℤ) ^ 2 - 1111 * (B : ℤ) + 1724) := by
    rw [hSI]
    calc
      511 * (gZ * (m * (X : ℤ) - c * (Y : ℤ))) =
          gZ * (511 * (m * (X : ℤ) - c * (Y : ℤ))) := by ring
      _ = gZ * (-(80 * (B : ℤ) ^ 2 - 1111 * (B : ℤ) + 1724)) := by rw [hinner]
      _ = _ := by dsimp [gZ]; ring
  have hpoly : 0 < 80 * (B : ℤ) ^ 2 - 1111 * (B : ℤ) + 1724 := by
    have hBpos : (0 : ℤ) < (B : ℤ) :=
      lt_of_lt_of_le (by norm_num) hBi
    have hB1111 : (1111 : ℤ) < (B : ℤ) :=
      lt_of_lt_of_le (by norm_num) hBi
    have hp := mul_pos hBpos (sub_pos.mpr hB1111)
    nlinarith [sq_nonneg (B : ℤ)]
  have hnegative : selectedSum d t (Q &&& (2 * Q)) < 0 := by
    have hBpos : (0 : ℤ) < (B : ℤ) :=
      lt_of_lt_of_le (by norm_num) hBi
    have hp := mul_pos (sub_pos.mpr (show (1 : ℤ) < (B : ℤ) by
      exact lt_of_lt_of_le (by norm_num) hBi)) hpoly
    nlinarith [hformula]
  refine ⟨hSA, hSC, ?_, ?_⟩
  · rw [hphysical]
    exact hformula
  · rw [hphysical]
    exact hnegative

end D5.S3.Combinatorics.Circle.MersenneExceptional19Nonboolean


