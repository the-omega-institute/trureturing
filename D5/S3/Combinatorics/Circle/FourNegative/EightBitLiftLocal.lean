/- GID: D5/S3/Combinatorics/Circle/FourNegative/EightBitLiftLocal
   generality: I
   mirror-B: none(waiver:consumed-by-eight-bit-physical-lift)
   mirror-E: none(waiver:dependent-physical-source-audit)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Literal physical eight-bit insertion and its charge-prefix proof. -/
import D5.S3.Combinatorics.Circle.FourNegative.EightBitLiftArithmetic

/-! # Shared physical orientation from the charge corridor -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.FourNegative.EightBitPhysicalLift

open SourceWidth PeriodicShorteningArithmetic

def corridorLower (C : ℤ) (b : Bool) : ℤ := if b then 0 else (C + 1) / 2

def corridorUpper (H C : ℤ) (b : Bool) : ℤ :=
  if b then H - (85 - C) / 2 else H

theorem corridor_iff (H C x : ℤ) (b : Bool) (hC : 0 ≤ C ∧ C ≤ 85) :
    (0 ≤ x ∧ x ≤ H ∧
      0 ≤ 2 * x - C + 85 * (if b then 1 else 0) ∧
      2 * x - C + 85 * (if b then 1 else 0) ≤ 2 * H + 1) ↔
      (corridorLower C b ≤ x ∧ x ≤ corridorUpper H C b) := by
  cases b <;> simp only [corridorLower, corridorUpper, Bool.false_eq_true,
    Bool.true_eq, if_false, if_true] <;> omega

theorem negative_pair_corridor (H C c x a p : ℤ) (b : Bool)
    (hC : 0 ≤ C) (hc : 0 ≤ c) (hCc : C + c ≤ 85)
    (hx : corridorLower C b ≤ x ∧ x ≤ corridorUpper H C b)
    (hz : corridorLower (C + c) b ≤ x + a + p ∧
      x + a + p ≤ corridorUpper H (C + c) b)
    (ha : a ≤ 0) (hp : 0 ≤ p) (hroom : p - a ≤ H - 85) :
    if x + p ≤ corridorUpper H C b then
      corridorLower C b ≤ x + p ∧ x + p ≤ corridorUpper H C b
    else
      corridorLower (C + c) b ≤ x + a ∧
        x + a ≤ corridorUpper H (C + c) b := by
  cases b <;> simp only [corridorLower, corridorUpper, Bool.false_eq_true,
    Bool.true_eq, if_false, if_true] at * <;> split_ifs <;> omega

/-- The quotient parity of the native charge makes each paired mapped row
positive, or leaves at least 171 units beyond the negative pair's span. -/
theorem low_row_parity (k : ℕ) (hk : 9 ≤ k) (i : Fin k) (hi : i.val < 8) :
    let a := 256 * actualSource k 85 i - 255 * charge k 85 i
    let p := 85 * (2 : ℤ) ^ i.val
    (0 ≤ a ∧ 0 ≤ 2 * a - charge k 85 i) ∨
      (a ≤ 0 ∧ p - a ≤ targetH k - 171) := by
  let P : ℤ := 2 ^ i.val
  let s : ℤ := 2 ^ (k - 1 - i.val)
  let z : ℤ := 85 / s
  let r : ℤ := 85 % s
  let c : ℤ := charge k 85 i
  have hP : 1 ≤ P := one_le_pow₀ (by norm_num)
  have hs : 2 ≤ s := by
    have he : 1 ≤ k - 1 - i.val := by omega
    simpa [s] using (pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) he)
  have hseven : (128 : ℤ) ≤ 2 ^ (k - 1) := by
    have h := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2)
      (show 7 ≤ k - 1 by omega)
    norm_num at h
    exact h
  have hPs : P * s = (2 : ℤ) ^ (k - 1) := by
    dsimp [P, s]
    rw [← pow_add]
    congr 1
    omega
  have hpow : (2 : ℤ) ^ k = 2 * P * s := by
    rw [mul_assoc, hPs, ← pow_succ']
    congr 1
    omega
  have hsEven : s % 2 = 0 := by
    have he : k - 1 - i.val = (k - 2 - i.val) + 1 := by omega
    simp [s, he, pow_succ, Int.mul_emod]
  have hr : 1 ≤ r ∧ r < s := by
    have hr0 := Int.emod_nonneg (85 : ℤ) (by omega : s ≠ 0)
    have hrlt := Int.emod_lt_of_pos (85 : ℤ) (by omega : 0 < s)
    have hdecomp := Int.emod_add_mul_ediv (85 : ℤ) s
    have hodd : r % 2 = 1 := by
      dsimp [r]
      rw [Int.emod_emod_of_dvd _ (show (2 : ℤ) ∣ s from Int.dvd_of_emod_eq_zero hsEven)]
      norm_num
    dsimp [r] at *
    omega
  have hz : 0 ≤ z := Int.ediv_nonneg (by norm_num) (by omega)
  have hdecomp : 85 = s * z + r := by
    have h := Int.emod_add_mul_ediv (85 : ℤ) s
    dsimp [z, r]
    omega
  have hc : c = z / 2 + z % 2 := rfl
  have hc0 : 0 ≤ c := by
    have h := Int.emod_nonneg z (by norm_num : (2 : ℤ) ≠ 0)
    have h' := Int.ediv_nonneg hz (by norm_num : (0 : ℤ) ≤ 2)
    omega
  have hzP : z < P := by
    have hsmall : (85 : ℤ) < P * s := by rw [hPs]; omega
    nlinarith
  have hhalf : targetH k = 256 * P * s - 1 := by
    have hm : modulus k = 2 * P * s - 1 := by rw [modulus, hpow]
    have hh : modulus k / 2 = P * s - 1 := by
      rw [hm, show 2 * P * s - 1 = 2 * (P * s) - 1 by ring]
      omega
    rw [targetH, hh]
    ring
  have hw : 85 ≤ 2 ^ (k - 1) - 1 := by
    have hp := Nat.pow_le_pow_right (by decide : 0 < 2) (show 7 ≤ k - 1 by omega)
    norm_num at hp
    omega
  have hf := (digit_data k 85 (by omega) hw i).2.1
  change actualSource k 85 i = P * 85 - (2 ^ k - 1) * c at hf
  have hpar := Int.emod_nonneg z (by norm_num : (2 : ℤ) ≠ 0)
  have hpar' := Int.emod_lt_of_pos z (by norm_num : (0 : ℤ) < 2)
  have hzc := Int.emod_add_mul_ediv z 2
  change (0 ≤ 256 * actualSource k 85 i - 255 * c ∧
      0 ≤ 2 * (256 * actualSource k 85 i - 255 * c) - c) ∨
    (256 * actualSource k 85 i - 255 * c ≤ 0 ∧
      85 * P - (256 * actualSource k 85 i - 255 * c) ≤ targetH k - 171)
  rcases (show z % 2 = 0 ∨ z % 2 = 1 by omega) with he | ho
  · have heq : z = 2 * c := by omega
    have hscaled := congrArg (fun t : ℤ => t * P) hdecomp
    rw [heq] at hscaled
    have ha : 256 * actualSource k 85 i - 255 * c = 256 * r * P + c := by
      rw [hf, hpow]
      nlinarith [hscaled]
    left
    rw [ha]
    constructor <;> nlinarith [mul_pos (by omega : 0 < r) (by omega : 0 < P)]
  · have heq : z = 2 * c - 1 := by omega
    have hscaled := congrArg (fun t : ℤ => t * P) hdecomp
    rw [heq] at hscaled
    have hc1 : 1 ≤ c := by omega
    have hcP : c ≤ P := by omega
    have ha : 256 * actualSource k 85 i - 255 * c =
        -256 * P * s + 256 * r * P + c := by
      rw [hf, hpow]
      nlinarith [hscaled]
    right
    rw [ha, hhalf]
    constructor
    · have hm := mul_le_mul_of_nonneg_left (show r ≤ s - 1 by omega)
        (show 0 ≤ P by omega)
      nlinarith
    · nlinarith [mul_le_mul_of_nonneg_left hr.1 (show 0 ≤ P by omega)]

end D5.S3.Combinatorics.Circle.FourNegative.EightBitPhysicalLift
