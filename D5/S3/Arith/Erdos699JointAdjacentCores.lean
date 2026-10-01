/- GID: D5/S3/Arith/Erdos699JointAdjacentCores
   generality: G
   mirror-B: D5/B/S3/Arith/Erdos699JointAdjacentCores
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Adjacent quadratic and cubic divisibilities force three nontrivial gcds. -/

/- erdos699_joint_adjacent_gcds
   proof_shape: content
   escape_witness: The two moduli and quotient range jointly rule out each
     unit gcd through three distinct parity contradictions.
   admission_basis: escape-witness
   Direct frozen dependencies: none.
-/

import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.Erdos699JointAdjacentCores

/-- The adjacent quadratic and cubic congruences force a nontrivial common
factor at each of three consecutive integers. -/
theorem erdos699_joint_adjacent_gcds
    (B s : ℤ) (hB : 5 ≤ B) (hodd : Odd B)
    (hs : 1 ≤ s) (hsB : s ≤ B - 1)
    (hquad : 2 * B + 1 ∣ 4 * s ^ 2 - 1)
    (hcubic : B ∣ (s - 1) * s * (s + 1)) :
    1 < Int.gcd B (s - 1) ∧
    1 < Int.gcd B s ∧
    1 < Int.gcd B (s + 1) := by
  obtain ⟨m, hm⟩ := hodd
  have hodd' : Odd B := ⟨m, hm⟩
  obtain ⟨A, hA⟩ := hquad
  have hB0 : 0 ≤ B := by omega
  have hCpos : 0 < 2 * B + 1 := by omega
  have hs0 : 0 < s := by omega
  have hAspos : 0 < 4 * s ^ 2 - 1 := by nlinarith [sq_nonneg (s - 1)]
  have hApos : 0 < A := by
    by_contra h
    have : A ≤ 0 := by omega
    have := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hCpos) this
    omega
  have hAlt : A < 2 * B := by
    by_contra h
    have hge : 2 * B ≤ A := by omega
    have hmulg := mul_le_mul_of_nonneg_left hge (le_of_lt hCpos)
    nlinarith [sq_nonneg (B - s)]
  have hAmod : 4 ∣ A - 1 := by
    refine ⟨m * A + A - s ^ 2, ?_⟩
    rw [hm] at hA
    nlinarith [hA]
  obtain ⟨k, hk⟩ := hAmod
  have hAeq : A = 4 * k + 1 := by omega
  have hk0 : 0 ≤ k := by omega
  have hkm : k ≤ m := by omega
  have hBs : Int.gcd B s ≠ 1 := by
    intro hg
    have hprod : B ∣ ((s - 1) * (s + 1)) * s := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hcubic
    have hd : B ∣ (s - 1) * (s + 1) :=
      Int.dvd_of_dvd_mul_left_of_gcd_one hprod hg
    have hd' : B ∣ s ^ 2 - 1 := by
      convert hd using 1; ring
    obtain ⟨q, hq⟩ := hd'
    have hAm : A - 3 = B * (4 * q - 2 * A) := by
      nlinarith [hA, hq]
    have hq0 : 0 ≤ 4 * q - 2 * A := by
      by_contra h
      have hle : 4 * q - 2 * A ≤ -1 := by omega
      have hm' := mul_le_mul_of_nonneg_left hle hB0
      omega
    have hq1 : 4 * q - 2 * A ≤ 1 := by
      by_contra h
      have hge : 2 ≤ 4 * q - 2 * A := by omega
      have hm' := mul_le_mul_of_nonneg_left hge hB0
      omega
    interval_cases hqval : (4 * q - 2 * A) <;> omega
  have hBsm : Int.gcd B (s - 1) ≠ 1 := by
    intro hg
    have hprod : B ∣ (s - 1) * (s * (s + 1)) := by
      simpa [mul_assoc] using hcubic
    have hd : B ∣ s * (s + 1) :=
      Int.dvd_of_dvd_mul_right_of_gcd_one hprod hg
    obtain ⟨q, hq⟩ := hd
    have hdiv : B ∣ A + 4 * s + 1 := by
      refine ⟨4 * q - 2 * A, ?_⟩
      nlinarith [hA, hq]
    have hdiv2 : B ∣ 2 * (2 * (k + s) + 1) := by
      convert hdiv using 1; omega
    have hzdiv : B ∣ 2 * (k + s) + 1 := by
      have hc : IsCoprime B (2 : ℤ) := Int.isCoprime_two_right.mpr hodd'
      have h' : B ∣ (2 * (k + s) + 1) * 2 := by
        simpa [mul_comm] using hdiv2
      exact hc.dvd_of_dvd_mul_right h'
    obtain ⟨r, hr⟩ := hzdiv
    have hzlo : 3 ≤ 2 * (k + s) + 1 := by omega
    have hzhi : 2 * (k + s) + 1 ≤ 3 * B - 2 := by omega
    have hrlo : 1 ≤ r := by
      by_contra h
      have hle : r ≤ 0 := by omega
      have hm' := mul_nonpos_of_nonneg_of_nonpos hB0 hle
      omega
    have hrhi : r ≤ 2 := by
      by_contra h
      have hge : 3 ≤ r := by omega
      have hm' := mul_le_mul_of_nonneg_left hge hB0
      omega
    have hr1 : r = 1 := by
      interval_cases r <;> omega
    have hks : k + s = m := by rw [hr1, hm] at hr; omega
    have hcore : B ^ 2 = s * (2 * B + s + 1) := by
      rw [hm] at hA
      nlinarith [hA]
    obtain ⟨v, hv⟩ := Int.even_mul_succ_self s
    have hcoreEven : B ^ 2 = 2 * (B * s + v) := by nlinarith [hcore, hv]
    have hBsOdd : B ^ 2 = 2 * (2 * m ^ 2 + 2 * m) + 1 := by
      rw [hm]
      ring
    omega
  have hBsp : Int.gcd B (s + 1) ≠ 1 := by
    intro hg
    have hprod : B ∣ ((s - 1) * s) * (s + 1) := by
      simpa [mul_assoc] using hcubic
    have hd : B ∣ (s - 1) * s :=
      Int.dvd_of_dvd_mul_left_of_gcd_one hprod hg
    obtain ⟨q, hq⟩ := hd
    have hdiv : B ∣ A - 4 * s + 1 := by
      refine ⟨4 * q - 2 * A, ?_⟩
      nlinarith [hA, hq]
    have hdiv2 : B ∣ 2 * (2 * (s - k) - 1) := by
      have hneg : B ∣ -(A - 4 * s + 1) := dvd_neg.mpr hdiv
      convert hneg using 1; omega
    have hwdiv : B ∣ 2 * (s - k) - 1 := by
      have hc : IsCoprime B (2 : ℤ) := Int.isCoprime_two_right.mpr hodd'
      have h' : B ∣ (2 * (s - k) - 1) * 2 := by
        simpa [mul_comm] using hdiv2
      exact hc.dvd_of_dvd_mul_right h'
    obtain ⟨r, hr⟩ := hwdiv
    have hwlo : 2 - B ≤ 2 * (s - k) - 1 := by omega
    have hwhi : 2 * (s - k) - 1 ≤ 2 * B - 3 := by omega
    have hrlo : 0 ≤ r := by
      by_contra h
      have hle : r ≤ -1 := by omega
      have hm' := mul_le_mul_of_nonneg_left hle hB0
      omega
    have hrhi : r ≤ 1 := by
      by_contra h
      have hge : 2 ≤ r := by omega
      have hm' := mul_le_mul_of_nonneg_left hge hB0
      omega
    have hr1 : r = 1 := by
      interval_cases r <;> omega
    have hsk : s - k = m + 1 := by rw [hr1, hm] at hr; omega
    have hsq : (2 * s - (2 * B + 1)) ^ 2 = 1 := by
      nlinarith [hA]
    nlinarith [sq_nonneg (2 * s - (2 * B + 1) + 1)]
  have hposm : 0 < Int.gcd B (s - 1) :=
    Int.gcd_pos_of_ne_zero_left (s - 1) (by omega)
  have hpos0 : 0 < Int.gcd B s :=
    Int.gcd_pos_of_ne_zero_left s (by omega)
  have hposp : 0 < Int.gcd B (s + 1) :=
    Int.gcd_pos_of_ne_zero_left (s + 1) (by omega)
  constructor
  · omega
  constructor <;> omega

#print axioms erdos699_joint_adjacent_gcds

end D5.S3.Arith.Erdos699JointAdjacentCores
