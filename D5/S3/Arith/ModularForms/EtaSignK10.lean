/- GID: D5/S3/Arith/ModularForms/EtaSignK10
   generality: G
   mirror-B: D5/B/S3/Arith/ModularForms/EtaSignK10
   mirror-E: none(waiver:full-normalized-eta-k10-sign)
   anchors: [mathlib/module/Mathlib.Combinatorics.Enumerative.Pentagonal.PowerSeries]
   utility: none
   digest: All-index period-nine signs of the actual Euler quotient E^9/E3^10. -/

import D5.S3.Arith.ModularForms.EulerNineSquareDissection

/-! BHHK arXiv:2409.07164v1 Appendix A Table 1, entry 1^9 3^(-10).
The zero cubic progression is smoothed by actual ordinary partitions;
in particular the auxiliary degree-five hole does not survive. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Arith.ModularForms.EtaSignK10

open CubicThetaIdentities CubicThetaLattice EulerNineDissection EulerNineSquareDissection
open D5.S3.Combinatorics.Partitions.OrdinaryEulerProduct
open D5.S3.Combinatorics.Partitions.RestrictedEulerCancellation
open D5.S3.Combinatorics.Partitions.EulerNineComparison
open D5.S3.Combinatorics.PowerSeries.Trisection

noncomputable def F10 : PowerSeries ℚ := E ^ 9 * PowerSeries.invOfUnit (expand3 E) 1 ^ 10
noncomputable def C10 (n : ℕ) : ℚ := PowerSeries.coeff n F10
noncomputable def G10 : PowerSeries ℚ := E ^ 2 * expand3 P ^ 3

theorem F10_eq_expanded_inverse : F10 = E ^ 9 * expand3 P ^ 10 := by
  have hc : PowerSeries.constantCoeff (expand3 E) = 1 := by
    simpa only [expand3, PowerSeries.constantCoeff_expand] using
      CubicThetaCoreProduct.euler_constant_one
  have hi : expand3 P = PowerSeries.invOfUnit (expand3 E) 1 := by
    have hu := PowerSeries.mul_invOfUnit (expand3 E) 1 hc
    calc
      expand3 P = expand3 P * (expand3 E * PowerSeries.invOfUnit (expand3 E) 1) := by
        rw [hu, mul_one]
      _ = (expand3 E * expand3 P) * PowerSeries.invOfUnit (expand3 E) 1 := by ring
      _ = _ := by rw [EtaSignK6.expanded_inverse, one_mul]
  rw [F10, ← hi]

theorem zero_component : B ^ 3 * P ^ 7 = G10 := by
  dsimp only [B, G10]
  calc
    _ = E ^ 2 * expand3 P ^ 3 * (E * P) ^ 7 := by ring
    _ = _ := by rw [euler_mul_inverse, one_pow, mul_one]

/-- The exact cubic lift retains -9, 27, and the original coefficient scale. -/
theorem first_dissection :
    F10 = expand3 G10 +
      PowerSeries.X * expand3 (PowerSeries.C (-9) * (normTheta ^ 2 * coreTheta * P ^ 7)) +
      PowerSeries.X ^ 2 * expand3 (PowerSeries.C 27 * (normTheta * coreTheta ^ 2 * P ^ 7)) := by
  have hc : normTheta ^ 3 - 27 * PowerSeries.X * coreTheta ^ 3 = B ^ 3 := by
    rw [cubic_identity]
    ring
  have hF : F10 = B ^ 3 * expand3 (P ^ 7) := by
    simp only [F10_eq_expanded_inverse, B, map_pow]
    ring
  rw [hF, ← zero_component]
  rw [show expand3 (B ^ 3 * P ^ 7) =
      expand3 ((normTheta ^ 3 - 27 * PowerSeries.X * coreTheta ^ 3) * P ^ 7) by rw [hc]]
  rw [B_dissection]
  simp only [map_mul, map_pow, map_sub, map_neg, map_ofNat,
    expand3, PowerSeries.expand_C, PowerSeries.expand_X]
  ring

/-- All three squared sections are smoothed by the ordinary partition series. -/
theorem second_dissection :
    G10 = expand3 (U * P) +
      PowerSeries.X * expand3 (PowerSeries.C (-1) * (V * P)) +
      PowerSeries.X ^ 2 * expand3 (PowerSeries.C (-1) * (W * P)) := by
  have hg : G10 = R ^ 2 * expand3 P := by simp only [G10, R]; ring
  rw [hg, R_square_dissection]
  simp only [map_mul, expand3, PowerSeries.expand_C, map_neg, map_one]
  ring

private theorem partition_smoothing (H : PowerSeries ℚ)
    (hH : ∀ n, 0 ≤ PowerSeries.coeff n H) (h0 : 1 ≤ PowerSeries.constantCoeff H)
    (n : ℕ) : 1 ≤ PowerSeries.coeff n (H * P) := by
  have hP : ∀ m, 0 ≤ PowerSeries.coeff m P := by
    intro m
    have hp := coeff_euler_inverse_pow_ge_one 1 m (by omega)
    simp only [pow_one] at hp
    linarith
  have hp : 1 ≤ PowerSeries.coeff n P := by
    simpa only [pow_one] using coeff_euler_inverse_pow_ge_one 1 n (by omega)
  have ht : PowerSeries.coeff 0 H * PowerSeries.coeff n P ≤
      PowerSeries.coeff n (H * P) := by
    rw [PowerSeries.coeff_mul]
    exact Finset.single_le_sum (fun p _ => mul_nonneg (hH p.1) (hP p.2))
      (show (0, n) ∈ Finset.HasAntidiagonal.antidiagonal n by simp)
  have hm := mul_le_mul_of_nonneg_right h0 (hP n)
  simp only [one_mul, ← PowerSeries.coeff_zero_eq_constantCoeff_apply] at hm
  exact hp.trans (hm.trans ht)

/-- Strict positivity holds in every degree, including the former W degree-one hole. -/
theorem smoothed_positive (n : ℕ) :
    0 < PowerSeries.coeff n (U * P) ∧ 0 < PowerSeries.coeff n (V * P) ∧
      0 < PowerSeries.coeff n (W * P) := by
  have hu : 1 ≤ PowerSeries.constantCoeff U := by
    simpa only [PowerSeries.coeff_zero_eq_constantCoeff_apply] using coeff_U_ge_one 0
  have hv : 1 ≤ PowerSeries.constantCoeff V := by
    simpa only [PowerSeries.coeff_zero_eq_constantCoeff_apply] using coeff_V_ge_one 0
  have hw : 1 ≤ PowerSeries.constantCoeff W := by rw [W_initial.1]
  have pu := partition_smoothing U (fun m => (by norm_num : (0 : ℚ) ≤ 1).trans
    (coeff_U_ge_one m)) hu n
  have pv := partition_smoothing V (fun m => (by norm_num : (0 : ℚ) ≤ 1).trans
    (coeff_V_ge_one m)) hv n
  have pw := partition_smoothing W coeff_W_nonnegative hw n
  exact ⟨by linarith, by linarith, by linarith⟩

theorem five_coefficient_formulas (m : ℕ) :
    C10 (3 * m + 1) = -9 * PowerSeries.coeff m (normTheta ^ 2 * coreTheta * P ^ 7) ∧
    C10 (3 * m + 2) = 27 * PowerSeries.coeff m (normTheta * coreTheta ^ 2 * P ^ 7) ∧
    C10 (9 * m) = PowerSeries.coeff m (U * P) ∧
    C10 (9 * m + 3) = -PowerSeries.coeff m (V * P) ∧
    C10 (9 * m + 6) = -PowerSeries.coeff m (W * P) := by
  have h1 := coeff_three_components _ _ _ _ first_dissection m
  have h2 := coeff_three_components _ _ _ _ second_dissection m
  have hz (n : ℕ) := (coeff_three_components _ _ _ _ first_dissection n).1
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa only [C10, PowerSeries.coeff_C_mul] using h1.2.1
  · simpa only [C10, PowerSeries.coeff_C_mul] using h1.2.2
  · change PowerSeries.coeff (9 * m) F10 = _
    rw [show 9 * m = 3 * (3 * m) by omega, hz, h2.1]
  · change PowerSeries.coeff (9 * m + 3) F10 = _
    rw [show 9 * m + 3 = 3 * (3 * m + 1) by omega, hz]
    simpa only [PowerSeries.coeff_C_mul, neg_one_mul] using h2.2.1
  · change PowerSeries.coeff (9 * m + 6) F10 = _
    rw [show 9 * m + 6 = 3 * (3 * m + 2) by omega, hz]
    simpa only [PowerSeries.coeff_C_mul, neg_one_mul] using h2.2.2

theorem progression_signs (m : ℕ) :
    C10 (3 * m + 1) < 0 ∧ 0 < C10 (3 * m + 2) ∧ 0 < C10 (9 * m) ∧
      C10 (9 * m + 3) < 0 ∧ C10 (9 * m + 6) < 0 := by
  rcases five_coefficient_formulas m with ⟨h1, h2, h0, h3, h6⟩
  rw [h1, h2, h0, h3, h6]
  have p1 := EtaSignK6.positive_convolution 2 1 7 m (by decide)
  have p2 := EtaSignK6.positive_convolution 1 2 7 m (by decide)
  have ps := smoothed_positive m
  simp only [pow_one] at p1 p2
  exact ⟨by nlinarith, by nlinarith, ps.1, by linarith [ps.2.1], by linarith [ps.2.2]⟩

theorem C10_zero : C10 0 = 1 := by
  have he : PowerSeries.constantCoeff E = 1 := CubicThetaCoreProduct.euler_constant_one
  have hp : PowerSeries.constantCoeff P = 1 := by
    have h := congrArg PowerSeries.constantCoeff euler_mul_inverse
    simpa only [map_mul, he, one_mul, map_one] using h
  simp only [C10, F10_eq_expanded_inverse, PowerSeries.coeff_zero_eq_constantCoeff_apply,
    map_mul, map_pow, expand3, PowerSeries.constantCoeff_expand, he, hp, one_pow, one_mul]

/-- The full unchanged BHHK k10 table entry at every unshifted natural index. -/
theorem all_index_signs (n : ℕ) :
    (0 < C10 n ↔ n % 9 = 0 ∨ n % 9 = 2 ∨ n % 9 = 5 ∨ n % 9 = 8) ∧
    (C10 n < 0 ↔ n % 9 = 1 ∨ n % 9 = 3 ∨ n % 9 = 4 ∨ n % 9 = 6 ∨ n % 9 = 7) ∧
    C10 n ≠ 0 := by
  by_cases hn : n = 0
  · subst n
    rw [C10_zero]
    norm_num
  · have h3 := progression_signs (n / 3)
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
      | have hp : 0 < C10 n := by simpa only [← hn9] using h9.2.2.1
        constructor
        · simp [h, hp]
        constructor
        · simp [h, not_lt_of_ge (le_of_lt hp)]
        · exact ne_of_gt hp
      | have hp : C10 n < 0 := by simpa only [← hn3] using h3.1
        constructor
        · simp [h, not_lt_of_ge (le_of_lt hp)]
        constructor
        · simp [h, hp]
        · exact ne_of_lt hp
      | have hp : 0 < C10 n := by simpa only [← hn3] using h3.2.1
        constructor
        · simp [h, hp]
        constructor
        · simp [h, not_lt_of_ge (le_of_lt hp)]
        · exact ne_of_gt hp
      | have hp : C10 n < 0 := by simpa only [← hn9] using h9.2.2.2.1
        constructor
        · simp [h, not_lt_of_ge (le_of_lt hp)]
        constructor
        · simp [h, hp]
        · exact ne_of_lt hp
      | have hp : C10 n < 0 := by simpa only [← hn9] using h9.2.2.2.2
        constructor
        · simp [h, not_lt_of_ge (le_of_lt hp)]
        constructor
        · simp [h, hp]
        · exact ne_of_lt hp

end D5.S3.Arith.ModularForms.EtaSignK10
