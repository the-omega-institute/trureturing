/- GID: D5/S3/Arith/Erdos699DefectiveAdjacentCores
   generality: G
   mirror-B: D5/B/S3/Arith/Erdos699DefectiveAdjacentCores
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: A defective adjacent-core modulus forces three nontrivial gcds. -/

/- erdos699_defective_adjacent_gcds
   proof_shape: content
   escape_witness: The defective modulus, mod-8 parity, and mod-19
     nonsquare obstructions jointly rule out each unit gcd.
   admission_basis: escape-witness
   Direct frozen dependencies: none.
-/

import Mathlib.Tactic
import Mathlib.Data.Int.ModEq

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.Erdos699DefectiveAdjacentCores

private lemma square_bound_contradiction
    (b x : ℤ) (hB : 5 ≤ b) (hxlo : -(6 * b + 1) < x)
    (hxhi : x < 0) (hsq : x ^ 2 = 1 + 8 * b * (6 * b + 1)) : False := by
  have hdiff : 0 < x + (6 * b + 1) := by omega
  have hprod : 0 < ((6 * b + 1) - x) * (x + (6 * b + 1)) :=
    mul_pos (by omega) hdiff
  nlinarith only [hprod, hsq, hB]

private lemma positive_residue_cases
    (m z : ℤ) (hmlo : 0 < m) (hmhi : m < 18)
    (hmres : m + 6 = 8 * z) : m = 2 ∨ m = 10 := by
  omega

set_option maxHeartbeats 1000000 in
-- The three modular branches require repeated nonlinear normalization.
/-- The defective adjacent modulus `6b+1` and the cubic allocation force a
nontrivial common factor at each of three consecutive integers. -/
theorem erdos699_defective_adjacent_gcds
    (b s : ℤ) (hB : 5 ≤ b) (hodd : Odd b)
    (hB8 : b ≡ 5 [ZMOD 8]) (hB19 : b ≡ 8 [ZMOD 19])
    (hs : 1 ≤ s) (hsB : s ≤ 3 * b - 3)
    (hquad : 6 * b + 1 ∣ 4 * s ^ 2 - 1)
    (hcubic : b ∣ (s - 1) * s * (s + 1)) :
    1 < Int.gcd b (s - 1) ∧
    1 < Int.gcd b s ∧
    1 < Int.gcd b (s + 1) := by
  have hB8mod := hB8
  have hB19mod := hB19
  rw [Int.modEq_iff_dvd] at hB8mod hB19mod
  obtain ⟨r8, hr8⟩ := hB8mod
  obtain ⟨r19, hr19⟩ := hB19mod
  have hb8 : b = 8 * (-r8) + 5 := by omega
  have hb19 : b = 19 * (-r19) + 8 := by omega
  obtain ⟨t, ht⟩ := hodd
  obtain ⟨A, hA⟩ := hquad
  have hB0 : 0 ≤ b := by omega
  have hCpos : 0 < 6 * b + 1 := by omega
  have hs0 : 0 < s := by omega
  have hAspos : 0 < 4 * s ^ 2 - 1 := by
    nlinarith [sq_nonneg (s - 1)]
  have hApos : 0 < A := by
    by_contra h
    have hle : A ≤ 0 := by omega
    have hmulg := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hCpos) hle
    omega
  have hAlt : A < 6 * b := by
    by_contra h
    have hge : 6 * b ≤ A := by omega
    have hmulg := mul_le_mul_of_nonneg_left hge (le_of_lt hCpos)
    nlinarith [sq_nonneg (3 * b - s)]
  have hAmod : 4 ∣ A - 1 := by
    have hC : 6 * b + 1 = -48 * r8 + 31 := by omega
    rw [hC] at hA
    refine ⟨-12 * r8 * A + 8 * A - s ^ 2, ?_⟩
    nlinarith [hA]
  obtain ⟨k, hk⟩ := hAmod
  have hAeq : A = 4 * k + 1 := by omega
  have hk0 : 0 ≤ k := by omega

  have odd_square_mod_eight : ∀ x : ℤ, Odd x → x ^ 2 ≡ 1 [ZMOD 8] := by
    intro x hx
    obtain ⟨q, hq⟩ := hx
    obtain ⟨v, hv⟩ := Int.even_mul_succ_self q
    apply (Int.modEq_iff_dvd).2
    refine ⟨-v, ?_⟩
    rw [hq] at *
    nlinarith [hv]
  have no_square_five_mod_eight : ∀ x : ℤ, x ^ 2 ≡ 5 [ZMOD 8] → False := by
    intro x hx
    have hxn : 0 ≤ x % 8 := Int.emod_nonneg _ (by norm_num)
    have hxl : x % 8 < 8 := by
      simpa using (Int.emod_lt x (by norm_num : (8 : ℤ) ≠ 0))
    have hxr : x ≡ x % 8 [ZMOD 8] := by
      apply (Int.modEq_iff_dvd).2
      refine ⟨-(x / 8), ?_⟩
      have hxrep := Int.emod_add_mul_ediv x 8
      nlinarith [hxrep]
    have hmod : (x % 8) ^ 2 ≡ 5 [ZMOD 8] := (hxr.symm.pow 2).trans hx
    have heq : ((x % 8) ^ 2) % 8 = 5 % 8 := hmod
    interval_cases hv : x % 8 <;> norm_num at heq
  have no_square_two_mod_nineteen : ∀ x : ℤ, x ^ 2 ≡ 2 [ZMOD 19] → False := by
    intro x hx
    have hxn : 0 ≤ x % 19 := Int.emod_nonneg _ (by norm_num)
    have hxl : x % 19 < 19 := by
      simpa using (Int.emod_lt x (by norm_num : (19 : ℤ) ≠ 0))
    have hxr : x ≡ x % 19 [ZMOD 19] := by
      apply (Int.modEq_iff_dvd).2
      refine ⟨-(x / 19), ?_⟩
      have hxrep := Int.emod_add_mul_ediv x 19
      nlinarith [hxrep]
    have hmod : (x % 19) ^ 2 ≡ 2 [ZMOD 19] := (hxr.symm.pow 2).trans hx
    have heq : ((x % 19) ^ 2) % 19 = 2 % 19 := hmod
    interval_cases hv : x % 19 <;> norm_num at heq
  have no_square_three_mod_nineteen : ∀ x : ℤ, x ^ 2 ≡ 3 [ZMOD 19] → False := by
    intro x hx
    have hxn : 0 ≤ x % 19 := Int.emod_nonneg _ (by norm_num)
    have hxl : x % 19 < 19 := by
      simpa using (Int.emod_lt x (by norm_num : (19 : ℤ) ≠ 0))
    have hxr : x ≡ x % 19 [ZMOD 19] := by
      apply (Int.modEq_iff_dvd).2
      refine ⟨-(x / 19), ?_⟩
      have hxrep := Int.emod_add_mul_ediv x 19
      nlinarith [hxrep]
    have hmod : (x % 19) ^ 2 ≡ 3 [ZMOD 19] := (hxr.symm.pow 2).trans hx
    have heq : ((x % 19) ^ 2) % 19 = 3 % 19 := hmod
    interval_cases hv : x % 19 <;> norm_num at heq

  have hBs : Int.gcd b s ≠ 1 := by
    intro hg
    have hprod : b ∣ ((s - 1) * (s + 1)) * s := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hcubic
    have hd : b ∣ (s - 1) * (s + 1) :=
      Int.dvd_of_dvd_mul_left_of_gcd_one hprod hg
    have hd' : b ∣ s ^ 2 - 1 := by
      convert hd using 1
      ring
    obtain ⟨q, hq⟩ := hd'
    let v : ℤ := 4 * q - 6 * A
    have hv : A - 3 = b * v := by
      nlinarith [hA, hq]
    have hv0 : 0 ≤ v := by
      by_contra h
      have hvle : v ≤ -1 := by omega
      nlinarith [hv, hApos, hB]
    have hv5 : v ≤ 5 := by
      by_contra h
      have hvge : 6 ≤ v := by omega
      nlinarith [hv, hAlt, hB]
    have hv2 : v = 2 := by
      interval_cases v <;> omega
    have hA2 : A = 2 * b + 3 := by nlinarith [hv, hv2]
    have hsq : s ^ 2 = 3 * b ^ 2 + 5 * b + 1 := by
      nlinarith [hA, hA2]
    have hb2 : b ^ 2 ≡ 5 ^ 2 [ZMOD 8] := hB8.pow 2
    have hpoly : 3 * b ^ 2 + 5 * b + 1 ≡ 3 * 5 ^ 2 + 5 * 5 + 1 [ZMOD 8] := by
      apply Int.ModEq.add
      · apply Int.ModEq.add
        · exact hb2.mul_left 3
        · exact hB8.mul_left 5
      · exact Int.ModEq.refl 1
    have hnum : (3 * 5 ^ 2 + 5 * 5 + 1 : ℤ) ≡ 5 [ZMOD 8] := by
      norm_num [Int.ModEq]
    apply no_square_five_mod_eight s
    rw [hsq]
    exact hpoly.trans hnum

  have hBsp : Int.gcd b (s + 1) ≠ 1 := by
    intro hg
    have hprod : b ∣ ((s - 1) * s) * (s + 1) := by
      simpa [mul_assoc] using hcubic
    have hd : b ∣ (s - 1) * s :=
      Int.dvd_of_dvd_mul_left_of_gcd_one hprod hg
    obtain ⟨q, hq⟩ := hd
    have hdiv : b ∣ A - 4 * s + 1 := by
      refine ⟨4 * q - 6 * A, ?_⟩
      nlinarith [hA, hq]
    obtain ⟨m, hm⟩ := hdiv
    have hmlo : -12 < m := by
      nlinarith only [hm, hApos, hsB, hB]
    have hmhi : m < 6 := by
      nlinarith only [hm, hAlt, hs, hB]
    have hxodd : Odd (2 * s - (6 * b + 1)) := by
      have hCodd : Odd (6 * b + 1) := by
        refine ⟨6 * t + 3, ?_⟩
        omega
      exact Even.sub_odd ⟨s, by ring⟩ hCodd
    let x : ℤ := 2 * s - (6 * b + 1)
    have hsq : x ^ 2 = 1 + (m + 6) * b * (6 * b + 1) := by
      dsimp [x]
      linear_combination hA + (6 * b + 1) * hm
    have hC8 : 6 * b + 1 ≡ 31 [ZMOD 8] := by
      have hh := (hB8.mul_left 6).add (Int.ModEq.refl (1 : ℤ))
      exact hh
    have hbc8 : b * (6 * b + 1) ≡ 3 [ZMOD 8] := by
      have hh := Int.ModEq.mul hB8 hC8
      have hn : (5 : ℤ) * 31 ≡ 3 [ZMOD 8] := by norm_num [Int.ModEq]
      exact hh.trans hn
    have hx8 : x ^ 2 ≡ 1 [ZMOD 8] := odd_square_mod_eight x hxodd
    have heq : x ^ 2 ≡ 1 + (m + 6) * 3 [ZMOD 8] := by
      rw [hsq]
      simpa [mul_assoc] using
        (Int.ModEq.add (Int.ModEq.refl (1 : ℤ)) (hbc8.mul_left (m + 6)))
    have hzero : 0 ≡ (m + 6) * 3 [ZMOD 8] := by
      simpa using heq.sub hx8
    have hd8 : (8 : ℤ) ∣ 3 * (m + 6) := by
      have hd' : (8 : ℤ) ∣ (m + 6) * 3 :=
        (Int.modEq_zero_iff_dvd).mp hzero.symm
      obtain ⟨w, hw⟩ := hd'
      refine ⟨w, ?_⟩
      convert hw using 1
      ring
    have hc3 : IsCoprime (8 : ℤ) 3 := by norm_num
    have hd8' : (8 : ℤ) ∣ m + 6 := hc3.dvd_of_dvd_mul_left hd8
    obtain ⟨z, hz⟩ := hd8'
    have hmres : m + 6 = 8 * z := by omega
    have hm_cases : m = -6 ∨ m = 2 := by
      omega
    rcases hm_cases with rfl | rfl
    · nlinarith [hsq]
    · have hxlo : -(6 * b + 1) < x := by
        dsimp [x]
        omega
      have hxhi : x < 0 := by
        dsimp [x]
        nlinarith [hB]
      exact square_bound_contradiction b x hB hxlo hxhi hsq

  have hBsm : Int.gcd b (s - 1) ≠ 1 := by
    intro hg
    have hprod : b ∣ (s - 1) * (s * (s + 1)) := by
      simpa [mul_assoc] using hcubic
    have hd : b ∣ s * (s + 1) :=
      Int.dvd_of_dvd_mul_right_of_gcd_one hprod hg
    obtain ⟨q, hq⟩ := hd
    have hdiv : b ∣ A + 4 * s + 1 := by
      refine ⟨4 * q - 6 * A, ?_⟩
      linear_combination -hA + 4 * hq
    obtain ⟨m, hm⟩ := hdiv
    have hmlo : 0 < m := by
      by_contra h
      have hmle : m ≤ 0 := by omega
      have hbm : b * m ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hB0 hmle
      nlinarith only [hm, hApos, hs, hbm]
    have hmhi : m < 18 := by
      nlinarith only [hm, hAlt, hsB, hB]
    have hxodd : Odd (2 * s + (6 * b + 1)) := by
      have hCodd : Odd (6 * b + 1) := by
        refine ⟨6 * t + 3, ?_⟩
        omega
      obtain ⟨q, hq⟩ := hCodd
      refine ⟨s + q, ?_⟩
      nlinarith only [hq]
    let x : ℤ := 2 * s + (6 * b + 1)
    have hsq : x ^ 2 = 1 + (m + 6) * b * (6 * b + 1) := by
      dsimp [x]
      linear_combination hA + (6 * b + 1) * hm
    have hC8 : 6 * b + 1 ≡ 31 [ZMOD 8] := by
      have hh := (hB8.mul_left 6).add (Int.ModEq.refl (1 : ℤ))
      exact hh
    have hbc8 : b * (6 * b + 1) ≡ 3 [ZMOD 8] := by
      have hh := Int.ModEq.mul hB8 hC8
      have hn : (5 : ℤ) * 31 ≡ 3 [ZMOD 8] := by norm_num [Int.ModEq]
      exact hh.trans hn
    have hx8 : x ^ 2 ≡ 1 [ZMOD 8] := odd_square_mod_eight x hxodd
    have heq : x ^ 2 ≡ 1 + (m + 6) * 3 [ZMOD 8] := by
      rw [hsq]
      simpa [mul_assoc] using
        (Int.ModEq.add (Int.ModEq.refl (1 : ℤ)) (hbc8.mul_left (m + 6)))
    have hzero : 0 ≡ (m + 6) * 3 [ZMOD 8] := by
      have hsum : 1 + (m + 6) * 3 ≡ 1 [ZMOD 8] := heq.symm.trans hx8
      have hz := Int.ModEq.sub_right 1 hsum
      have hz' : (m + 6) * 3 ≡ 0 [ZMOD 8] := by
        simpa only [add_sub_cancel_left, sub_self] using hz
      exact hz'.symm
    have hd8 : (8 : ℤ) ∣ 3 * (m + 6) := by
      have hd' : (8 : ℤ) ∣ (m + 6) * 3 :=
        (Int.modEq_zero_iff_dvd).mp hzero.symm
      obtain ⟨w, hw⟩ := hd'
      refine ⟨w, ?_⟩
      nlinarith only [hw]
    have hc3 : IsCoprime (8 : ℤ) 3 := by norm_num
    have hd8' : (8 : ℤ) ∣ m + 6 := hc3.dvd_of_dvd_mul_left hd8
    obtain ⟨z, hz⟩ := hd8'
    have hmres : m + 6 = 8 * z := by omega
    have hm_cases : m = 2 ∨ m = 10 :=
      positive_residue_cases m z hmlo hmhi hmres
    rcases hm_cases with rfl | rfl
    · have h19 : b * (6 * b + 1) ≡ 12 [ZMOD 19] := by
        have hC19 : 6 * b + 1 ≡ 49 [ZMOD 19] := by
          have hh := (hB19.mul_left 6).add (Int.ModEq.refl (1 : ℤ))
          exact hh
        have hh := Int.ModEq.mul hB19 hC19
        have hn : (8 : ℤ) * 49 ≡ 12 [ZMOD 19] := by norm_num [Int.ModEq]
        exact hh.trans hn
      have hx19 : x ^ 2 ≡ 2 [ZMOD 19] := by
        rw [hsq]
        have hh := h19.mul_left 8
        have hone : (1 : ℤ) ≡ 1 [ZMOD 19] := Int.ModEq.refl 1
        have hsum := hone.add hh
        have hn : (1 : ℤ) + 8 * 12 ≡ 2 [ZMOD 19] := by norm_num [Int.ModEq]
        simpa [mul_assoc] using hsum.trans hn
      exact no_square_two_mod_nineteen x hx19
    · have h19 : b * (6 * b + 1) ≡ 12 [ZMOD 19] := by
        have hC19 : 6 * b + 1 ≡ 49 [ZMOD 19] := by
          have hh := (hB19.mul_left 6).add (Int.ModEq.refl (1 : ℤ))
          exact hh
        have hh := Int.ModEq.mul hB19 hC19
        have hn : (8 : ℤ) * 49 ≡ 12 [ZMOD 19] := by norm_num [Int.ModEq]
        exact hh.trans hn
      have hx19 : x ^ 2 ≡ 3 [ZMOD 19] := by
        rw [hsq]
        have hh := h19.mul_left 16
        have hone : (1 : ℤ) ≡ 1 [ZMOD 19] := Int.ModEq.refl 1
        have hsum := hone.add hh
        have hn : (1 : ℤ) + 16 * 12 ≡ 3 [ZMOD 19] := by norm_num [Int.ModEq]
        simpa [mul_assoc] using hsum.trans hn
      exact no_square_three_mod_nineteen x hx19

  have hposm : 0 < Int.gcd b (s - 1) :=
    Int.gcd_pos_of_ne_zero_left (s - 1) (by omega)
  have hpos0 : 0 < Int.gcd b s :=
    Int.gcd_pos_of_ne_zero_left s (by omega)
  have hposp : 0 < Int.gcd b (s + 1) :=
    Int.gcd_pos_of_ne_zero_left (s + 1) (by omega)
  constructor
  · omega
  constructor <;> omega

#print axioms erdos699_defective_adjacent_gcds

end D5.S3.Arith.Erdos699DefectiveAdjacentCores
