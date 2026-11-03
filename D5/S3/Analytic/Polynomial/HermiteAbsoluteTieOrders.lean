/- GID: D5/S3/Analytic/Polynomial/HermiteAbsoluteTieOrders
   generality: G
   mirror-B: D5/B/S3/Analytic/Polynomial/HermiteAbsoluteTieOrders
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Exact exhaustive orders with two maximal absolute Hermite coefficients. -/

import D5.S3.Analytic.Polynomial.HermiteAbsoluteMode

/-! Two absolute maxima in the original physicists Hermite coefficient row. -/

namespace D5.S3.Analytic.Polynomial.HermiteAbsoluteTieOrders

open HermiteSignedMode HermiteAbsoluteMode

/-- Absolute maximality over every exponent from zero through the order. -/
def IsAbsMax (k j : ℕ) : Prop :=
  j ≤ k ∧ ∀ i, i ≤ k →
    |(physicistsHermite k).coeff i| ≤ |(physicistsHermite k).coeff j|

/-- Exactly two distinct maximizing exponents in the complete coefficient row. -/
def HasExactlyTwo (k : ℕ) : Prop :=
  ∃ u v : ℕ, u < v ∧ ∀ j : ℕ, IsAbsMax k j ↔ j = u ∨ j = v

/-- The source formula, with a positive one-based natural index and integer arithmetic. -/
def a (n : ℕ) : ℤ :=
  2 * (n : ℤ) * ((n : ℤ) + 2) + ((n : ℤ) + 1) * (-1 : ℤ) ^ (n + 1)

/-- Positive, strictly increasing, and exhaustive one-based enumeration. -/
def claim : Prop :=
  (∀ n : ℕ, 1 ≤ n → 0 < a n) ∧
  (∀ n m : ℕ, 1 ≤ n → n < m → a n < a m) ∧
  ∀ k : ℕ, HasExactlyTwo k ↔ ∃! n : ℕ, 1 ≤ n ∧ (k : ℤ) = a n

private theorem max_iff_weight (k j : ℕ) :
    IsAbsMax k j ↔ ∃ r : ℕ, 2 * r ≤ k ∧ j = k - 2 * r ∧
      weight k r = weight k (mode k) := by
  have hm := (mode_rises k).1
  have hp := weight_pos k (mode k) hm
  constructor
  · intro h
    have htop := h.2 (k - 2 * mode k) (Nat.sub_le _ _)
    rw [polynomial_coeff k _ (Nat.sub_le _ _), polynomial_coeff k j h.1] at htop
    change weight k (mode k) ≤ |signedCoeff k j| at htop
    rcases coefficient_cases k j with hz | ⟨r, hr, hj, hw⟩
    · rw [hz] at htop
      linarith
    · exact ⟨r, hr, hj, le_antisymm (weight_le_mode k r hr) (hw ▸ htop)⟩
  · rintro ⟨r, hr, rfl, he⟩
    refine ⟨Nat.sub_le _ _, ?_⟩
    intro i hi
    rw [polynomial_coeff k i hi, polynomial_coeff k _ (Nat.sub_le _ _)]
    change |signedCoeff k i| ≤ weight k r
    rw [he]
    rcases coefficient_cases k i with hz | ⟨s, hs, hj, hw⟩
    · rw [hz]; exact hp.le
    · rw [hw]; exact weight_le_mode k s hs

private theorem strict_before (k r : ℕ) (hr : r + 1 < mode k) :
    weight k r < weight k (r + 1) := by
  have hm := mode_rises k
  have hmd := hm.1
  have hmc := hm.2
  have hdom : 2 * (r + 1) ≤ k := by omega
  have hcomp := second_mono (show k - 2 * mode k ≤ k - 2 * (r + 1) by omega)
  have ht : 4 * (r + 1) < second (k - 2 * (r + 1)) := by omega
  have htq : (4 * (r + 1) : ℚ) < second (k - 2 * (r + 1)) := by exact_mod_cast ht
  have hw := weight_pos k r (by omega)
  have he := adjacent k r hdom
  have hd : (0 : ℚ) < 4 * (r + 1) := by positivity
  nlinarith

private theorem equal_mode_indices (k r : ℕ) (hr : 2 * r ≤ k)
    (he : weight k r = weight k (mode k)) :
    r = mode k ∨ r + 1 = mode k := by
  have hle : r ≤ mode k := by
    by_contra h
    have := weight_lt_mode k r hr (by omega)
    linarith
  by_cases h : r + 1 < mode k
  · have hs := strict_before k r h
    have ht := weight_le_mode k (r + 1) (by have := (mode_rises k).1; omega)
    linarith
  · omega

private theorem adjacent_equal (k r : ℕ) (hr : 2 * (r + 1) ≤ k) :
    weight k r = weight k (r + 1) ↔
      second (k - 2 * (r + 1)) = 4 * (r + 1) := by
  have he := adjacent k r hr
  have hp := weight_pos k r (by omega)
  have hd : (0 : ℚ) < 4 * (r + 1) := by positivity
  constructor
  · intro hh
    rw [← hh] at he
    have : (second (k - 2 * (r + 1)) : ℚ) = 4 * (r + 1) := by nlinarith
    exact_mod_cast this
  · intro hh
    have : (second (k - 2 * (r + 1)) : ℚ) = 4 * (r + 1) := by exact_mod_cast hh
    rw [this] at he
    nlinarith

private theorem tie_is_mode (k r : ℕ) (hk : 2 * r ≤ k)
    (he : second (k - 2 * r) = 4 * r) : r = mode k := by
  have hle : r ≤ mode k := le_mode ⟨hk, he.ge⟩
  have hm := mode_rises k
  have hmd := hm.1
  have hmc := hm.2
  have hc := second_mono (show k - 2 * mode k ≤ k - 2 * r by omega)
  omega

private theorem tie_characterization (k : ℕ) :
    HasExactlyTwo k ↔ ∃ r : ℕ, 1 ≤ r ∧ 2 * r ≤ k ∧
      second (k - 2 * r) = 4 * r := by
  constructor
  · rintro ⟨u, v, huv, h⟩
    obtain ⟨r, hr, hu, her⟩ := (max_iff_weight k u).mp ((h u).mpr (Or.inl rfl))
    obtain ⟨s, hs, hv, hes⟩ := (max_iff_weight k v).mp ((h v).mpr (Or.inr rfl))
    have hri := equal_mode_indices k r hr her
    have hsi := equal_mode_indices k s hs hes
    have hsr : s < r := by omega
    have hrr : r = mode k := by omega
    have hss : s + 1 = r := by omega
    refine ⟨r, by omega, hr, ?_⟩
    have heq : weight k s = weight k (s + 1) := by rw [hss, hrr]; exact hes
    have ht := (adjacent_equal k s (by omega)).mp heq
    simpa only [hss] using ht
  · rintro ⟨r, hr, hk, he⟩
    have hm := tie_is_mode k r hk he
    have heq : weight k (r - 1) = weight k r := by
      have hh : r - 1 + 1 = r := by omega
      simpa only [hh] using (adjacent_equal k (r - 1) (by omega)).mpr (by simpa only [hh] using he)
    refine ⟨k - 2 * r, k - 2 * (r - 1), by omega, ?_⟩
    intro j
    rw [max_iff_weight]
    constructor
    · rintro ⟨s, hs, hj, hes⟩
      have hi := equal_mode_indices k s hs hes
      rcases hi with hi | hi
      · left; omega
      · right; omega
    · rintro (rfl | rfl)
      · exact ⟨r, hk, rfl, by rw [← hm]⟩
      · exact ⟨r - 1, by omega, rfl, by rw [← hm]; exact heq⟩

private theorem a_odd (t : ℕ) :
    a (2 * t + 1) = 8 * (t : ℤ) ^ 2 + 18 * (t : ℤ) + 8 := by
  unfold a
  rw [show 2 * t + 1 + 1 = 2 * (t + 1) by omega, pow_mul]
  norm_num
  ring

private theorem a_even (t : ℕ) :
    a (2 * t + 2) = 8 * (t : ℤ) ^ 2 + 22 * (t : ℤ) + 13 := by
  unfold a
  rw [show 2 * t + 2 + 1 = 2 * (t + 1) + 1 by omega, pow_add, pow_mul]
  norm_num
  ring

private theorem a_strictMono : StrictMono a := by
  apply strictMono_nat_of_lt_succ
  intro n
  have hpow : (-1 : ℤ) ^ (n + 1 + 1) = -((-1 : ℤ) ^ (n + 1)) := by
    rw [pow_succ]; ring
  unfold a
  rw [hpow]
  push_cast
  rcases neg_one_pow_eq_or ℤ (n + 1) with h | h <;> rw [h] <;> nlinarith

private theorem a_positive (n : ℕ) (hn : 1 ≤ n) : 0 < a n := by
  have hone : a 1 = 8 := by norm_num [a]
  have hh := a_strictMono.monotone hn
  rw [hone] at hh
  omega

private theorem tie_orders (k : ℕ) :
    (∃ r : ℕ, 1 ≤ r ∧ 2 * r ≤ k ∧ second (k - 2 * r) = 4 * r) ↔
      ∃ n : ℕ, 1 ≤ n ∧ (k : ℤ) = a n := by
  constructor
  · rintro ⟨r, hr, hk, he⟩
    let j := k - 2 * r
    have hjk : k = j + 2 * r := by dsimp [j]; omega
    have he' : (j + 1) * (j + 2) = 4 * r := he
    have hmod := congrArg (fun x : ℕ => x % 4) he'
    have hrem : j % 4 = 0 ∨ j % 4 = 1 ∨ j % 4 = 2 ∨ j % 4 = 3 := by omega
    have hrem' : j % 4 = 2 ∨ j % 4 = 3 := by
      rcases hrem with h | h | h | h
      · norm_num [Nat.add_mod, Nat.mul_mod, h] at hmod
      · norm_num [Nat.add_mod, Nat.mul_mod, h] at hmod
      · exact Or.inl h
      · exact Or.inr h
    let t := j / 4
    rcases hrem' with h | h
    · have hj : j = 4 * t + 2 := by dsimp [t]; omega
      rw [hj] at hjk he'
      have hv : k = 8 * t ^ 2 + 18 * t + 8 := by nlinarith [he']
      refine ⟨2 * t + 1, by omega, ?_⟩
      rw [a_odd, hv]
      push_cast
      ring
    · have hj : j = 4 * t + 3 := by dsimp [t]; omega
      rw [hj] at hjk he'
      have hv : k = 8 * t ^ 2 + 22 * t + 13 := by nlinarith [he']
      refine ⟨2 * t + 2, by omega, ?_⟩
      rw [a_even, hv]
      push_cast
      ring
  · rintro ⟨n, hn, he⟩
    let t := (n - 1) / 2
    have hsplit : n = 2 * t + 1 ∨ n = 2 * t + 2 := by dsimp [t]; omega
    rcases hsplit with h | h
    · rw [h, a_odd] at he
      have hv : k = 8 * t ^ 2 + 18 * t + 8 := by exact_mod_cast he
      refine ⟨(4 * t + 3) * (t + 1), by nlinarith, ?_, ?_⟩
      · nlinarith [hv]
      · have hsum : k = 2 * ((4 * t + 3) * (t + 1)) + (4 * t + 2) := by nlinarith [hv]
        have hj : k - 2 * ((4 * t + 3) * (t + 1)) = 4 * t + 2 := by omega
        rw [hj]
        unfold second
        ring
    · rw [h, a_even] at he
      have hv : k = 8 * t ^ 2 + 22 * t + 13 := by exact_mod_cast he
      refine ⟨(4 * t + 5) * (t + 1), by nlinarith, ?_, ?_⟩
      · nlinarith [hv]
      · have hsum : k = 2 * ((4 * t + 5) * (t + 1)) + (4 * t + 3) := by nlinarith [hv]
        have hj : k - 2 * ((4 * t + 5) * (t + 1)) = 4 * t + 3 := by omega
        rw [hj]
        unfold second
        ring

/-- The complete original A381737 assertion, including exhaustion and unique indexing. -/
theorem result : claim := by
  refine ⟨a_positive, fun n m _ h => a_strictMono h, ?_⟩
  intro k
  rw [tie_characterization, tie_orders]
  constructor
  · rintro ⟨n, hn, he⟩
    refine ⟨n, ⟨hn, he⟩, ?_⟩
    rintro m ⟨hm, hem⟩
    exact a_strictMono.injective (hem.symm.trans he)
  · rintro ⟨n, hn, _⟩
    exact ⟨n, hn⟩

end D5.S3.Analytic.Polynomial.HermiteAbsoluteTieOrders
