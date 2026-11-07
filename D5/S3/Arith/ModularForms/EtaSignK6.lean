/- GID: D5/S3/Arith/ModularForms/EtaSignK6
   generality: G
   mirror-B: D5/B/S3/Arith/ModularForms/EtaSignK6
   mirror-E: none(waiver:full-normalized-eta-k6-sign)
   anchors: [mathlib/module/Mathlib.Combinatorics.Enumerative.Pentagonal.PowerSeries]
   utility: none
   digest: The complete all-index period-nine signs of the actual normalized Euler quotient E^9/E3^6. -/

import D5.S3.Arith.ModularForms.CubicThetaIdentities
import D5.S3.Combinatorics.PowerSeries.Trisection

/-! Two exact trisections and positive ordinary partition convolution give the full normalized k6 coefficient sign pattern. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Arith.ModularForms.EtaSignK6

open CubicThetaLattice CubicThetaIdentities
open D5.S3.Combinatorics.Partitions.OrdinaryEulerProduct
open D5.S3.Combinatorics.PowerSeries.Trisection

/-- Normalized Euler coefficients; residue labels have no fractional eta shift. -/
noncomputable def F6 : PowerSeries ℚ := E ^ 9 * PowerSeries.invOfUnit (expand3 E) 1 ^ 6
noncomputable def C6 (n : ℕ) : ℚ := PowerSeries.coeff n F6
noncomputable def G6 : PowerSeries ℚ := B ^ 2 * expand3 P

/-- The actual reciprocal appearing in F6 is a unit inverse of E(X^3). -/
theorem expanded_inverse : expand3 E * expand3 P = 1 := by
  rw [← map_mul, euler_mul_inverse, map_one]

/-- Expanding the actual Euler reciprocal gives exactly the denominator used in the source. -/
theorem F6_eq_expanded_inverse : F6 = E ^ 9 * expand3 P ^ 6 := by
  have hc : PowerSeries.constantCoeff (expand3 E) = 1 := by
    simpa only [expand3, PowerSeries.constantCoeff_expand] using
      CubicThetaCoreProduct.euler_constant_one
  have hi : expand3 P = PowerSeries.invOfUnit (expand3 E) 1 := by
    have hu := PowerSeries.mul_invOfUnit (expand3 E) 1 hc
    calc
      expand3 P = expand3 P * (expand3 E * PowerSeries.invOfUnit (expand3 E) 1) := by
        rw [hu, mul_one]
      _ = (expand3 E * expand3 P) * PowerSeries.invOfUnit (expand3 E) 1 := by ring
      _ = _ := by rw [expanded_inverse, one_mul]
  rw [F6, ← hi]

/-- The zero progression reduces to the squared cubic quotient divided by E(X^3). -/
theorem zero_component : B ^ 3 * P ^ 3 = G6 := by
  dsimp only [B, G6]
  calc
    _ = E ^ 6 * expand3 P ^ 3 * (E * P) ^ 3 := by ring
    _ = _ := by rw [euler_mul_inverse, one_pow, mul_one]; ring

/-- The first exact trisection preserves the essential constants -9 and 27. -/
theorem first_dissection :
    F6 = expand3 G6 +
      PowerSeries.X * expand3 (PowerSeries.C (-9) * (normTheta ^ 2 * coreTheta * P ^ 3)) +
      PowerSeries.X ^ 2 * expand3 (PowerSeries.C 27 * (normTheta * coreTheta ^ 2 * P ^ 3)) := by
  have hc : normTheta ^ 3 - 27 * PowerSeries.X * coreTheta ^ 3 = B ^ 3 := by
    rw [cubic_identity]
    ring
  have hF : F6 = B ^ 3 * expand3 (P ^ 3) := by
    simp only [F6_eq_expanded_inverse, B, map_pow]
    ring
  rw [hF, ← zero_component]
  rw [show expand3 (B ^ 3 * P ^ 3) =
      expand3 ((normTheta ^ 3 - 27 * PowerSeries.X * coreTheta ^ 3) * P ^ 3) by rw [hc]]
  rw [B_dissection]
  simp only [map_mul, map_pow, map_sub, map_neg, map_ofNat, PowerSeries.map_C,
    expand3, PowerSeries.expand_C, PowerSeries.expand_X]
  ring

/-- A second trisection determines all three progressions inside the zero component. -/
theorem second_dissection :
    G6 = expand3 (normTheta ^ 2 * P) +
      PowerSeries.X * expand3 (PowerSeries.C (-6) * (normTheta * coreTheta * P)) +
      PowerSeries.X ^ 2 * expand3 (PowerSeries.C 9 * (coreTheta ^ 2 * P)) := by
  rw [G6, B_dissection]
  simp only [map_mul, map_pow, map_neg, map_ofNat, expand3, PowerSeries.expand_C]
  ring

/-- Five coefficient formulas cover all natural indices, including degree zero. -/
theorem five_coefficient_formulas (m : ℕ) :
    C6 (3 * m + 1) = -9 * PowerSeries.coeff m (normTheta ^ 2 * coreTheta * P ^ 3) ∧
    C6 (3 * m + 2) = 27 * PowerSeries.coeff m (normTheta * coreTheta ^ 2 * P ^ 3) ∧
    C6 (9 * m) = PowerSeries.coeff m (normTheta ^ 2 * P) ∧
    C6 (9 * m + 3) = -6 * PowerSeries.coeff m (normTheta * coreTheta * P) ∧
    C6 (9 * m + 6) = 9 * PowerSeries.coeff m (coreTheta ^ 2 * P) := by
  have h1 := coeff_three_components _ _ _ _ first_dissection m
  have h2 := coeff_three_components _ _ _ _ second_dissection m
  have hz (n : ℕ) := (coeff_three_components _ _ _ _ first_dissection n).1
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa only [C6, PowerSeries.coeff_C_mul] using h1.2.1
  · simpa only [C6, PowerSeries.coeff_C_mul] using h1.2.2
  · change PowerSeries.coeff (9 * m) F6 = _
    rw [show 9 * m = 3 * (3 * m) by omega, hz, h2.1]
  · change PowerSeries.coeff (9 * m + 3) F6 = _
    rw [show 9 * m + 3 = 3 * (3 * m + 1) by omega, hz]
    simpa only [PowerSeries.coeff_C_mul] using h2.2.1
  · change PowerSeries.coeff (9 * m + 6) F6 = _
    rw [show 9 * m + 6 = 3 * (3 * m + 2) by omega, hz]
    simpa only [PowerSeries.coeff_C_mul] using h2.2.2

/-- Nonnegative normalized theta powers convolved with actual partitions are strictly positive. -/
theorem positive_convolution (a b s m : ℕ) (hs : 1 ≤ s) :
    0 < PowerSeries.coeff m (normTheta ^ a * coreTheta ^ b * P ^ s) := by
  have hn := theta_nonnegative_and_normalized
  have hH : ∀ n, 0 ≤ PowerSeries.coeff n (normTheta ^ a * coreTheta ^ b) :=
    coeff_mul_nonnegative (coeff_pow_nonnegative hn.1 a) (coeff_pow_nonnegative hn.2.1 b)
  have hP : ∀ n, 0 ≤ PowerSeries.coeff n (P ^ s) :=
    fun n => le_trans (by norm_num) (coeff_euler_inverse_pow_ge_one s n hs)
  have hzero : PowerSeries.constantCoeff (normTheta ^ a * coreTheta ^ b) = 1 := by
    rw [map_mul, map_pow, map_pow, hn.2.2.1, hn.2.2.2, one_pow, one_pow, mul_one]
  exact lt_of_lt_of_le (lt_of_lt_of_le (by norm_num) (coeff_euler_inverse_pow_ge_one s m hs))
    (coeff_mul_ge_right hH hP hzero m)

/-- Strict signs on the five progressions, with no finite-range or eventual restriction. -/
theorem progression_signs (m : ℕ) :
    C6 (3 * m + 1) < 0 ∧ 0 < C6 (3 * m + 2) ∧ 0 < C6 (9 * m) ∧
      C6 (9 * m + 3) < 0 ∧ 0 < C6 (9 * m + 6) := by
  rcases five_coefficient_formulas m with ⟨h1, h2, h0, h3, h6⟩
  rw [h1, h2, h0, h3, h6]
  have p1 := positive_convolution 2 1 3 m (by decide)
  have p2 := positive_convolution 1 2 3 m (by decide)
  have p0 := positive_convolution 2 0 1 m (by decide)
  have p3 := positive_convolution 1 1 1 m (by decide)
  have p6 := positive_convolution 0 2 1 m (by decide)
  simp only [pow_zero, pow_one, one_mul, mul_one] at p1 p2 p0 p3 p6
  exact ⟨by nlinarith, by nlinarith, p0, by nlinarith, by nlinarith⟩

/-- BHHK arXiv:2409.07164v1 Appendix A Table 1, complete entry 1^9 3^(-6). -/
theorem all_index_signs (n : ℕ) :
    (0 < C6 n ↔ n % 9 = 0 ∨ n % 9 = 2 ∨ n % 9 = 5 ∨ n % 9 = 6 ∨ n % 9 = 8) ∧
    (C6 n < 0 ↔ n % 9 = 1 ∨ n % 9 = 3 ∨ n % 9 = 4 ∨ n % 9 = 7) ∧
    C6 n ≠ 0 := by
  have h3 := progression_signs (n / 3)
  have h9 := progression_signs (n / 9)
  have hmod : n % 9 < 9 := Nat.mod_lt n (by decide)
  have hn3 : n = 3 * (n / 3) + n % 3 := by omega
  have hn9 : n = 9 * (n / 9) + n % 9 := by omega
  have hcases : n % 9 = 0 ∨ n % 9 = 1 ∨ n % 9 = 2 ∨ n % 9 = 3 ∨
      n % 9 = 4 ∨ n % 9 = 5 ∨ n % 9 = 6 ∨ n % 9 = 7 ∨ n % 9 = 8 := by omega
  rcases hcases with h | h | h | h | h | h | h | h | h
  all_goals have hres : n % 3 = (n % 9) % 3 := by omega
  all_goals simp only [h] at hres
  all_goals norm_num at hres
  all_goals simp only [hres] at hn3
  all_goals simp only [h] at hn9
  all_goals norm_num at hn3 hn9
  all_goals first
    | have hp : 0 < C6 n := by simpa only [← hn9] using h9.2.2.1
      constructor
      · simp [h, hp]
      constructor
      · simp [h, not_lt_of_ge (le_of_lt hp)]
      · exact ne_of_gt hp
    | have hp : C6 n < 0 := by simpa only [← hn3] using h3.1
      constructor
      · simp [h, not_lt_of_ge (le_of_lt hp)]
      constructor
      · simp [h, hp]
      · exact ne_of_lt hp
    | have hp : 0 < C6 n := by simpa only [← hn3] using h3.2.1
      constructor
      · simp [h, hp]
      constructor
      · simp [h, not_lt_of_ge (le_of_lt hp)]
      · exact ne_of_gt hp
    | have hp : C6 n < 0 := by simpa only [← hn9] using h9.2.2.2.1
      constructor
      · simp [h, not_lt_of_ge (le_of_lt hp)]
      constructor
      · simp [h, hp]
      · exact ne_of_lt hp
    | have hp : 0 < C6 n := by simpa only [← hn9] using h9.2.2.2.2
      constructor
      · simp [h, hp]
      constructor
      · simp [h, not_lt_of_ge (le_of_lt hp)]
      · exact ne_of_gt hp

end D5.S3.Arith.ModularForms.EtaSignK6
