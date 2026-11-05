/- GID: D5/S3/Combinatorics/Circle/TwoNegativeNondecreasingJointLift/Endpoint
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/TwoNegativeNondecreasingJointLift/Endpoint
   mirror-E: none(waiver:no-escape-mirror-specified)
   anchors: [mathlib/module/Mathlib.Data.Int.ModEq, mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Unconditional complementary two-negative physical joint insertion. -/
import D5.S3.Combinatorics.Circle.TwoNegativeNondecreasingJointLift.Core

/-! Explicit bounded masks and the physical exception complete the complementary range. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.TwoNegativeNondecreasingJointLift
open SourceWidth PeriodicShortening RunFirstEarTransport
open private realize from D5.S3.Combinatorics.Circle.TwoNegativeNondecreasingJointLift.Core

/-- One physical permutation and one literal ear cut throughout the complementary range. -/
theorem actualSource_two_negative_nondec_joint_lift (a b : ℕ) (ha : 2 ≤ a)
    (hab : a ≤ b) :
    ∃ sigma : List (Fin (a + b)), ∃ j : ℕ, j ≤ a + b ∧
      OriginalOrder (a + b) (2 ^ a + 1) sigma ∧
      OriginalOrder (a + b + 1) (2 * (2 ^ a + 1))
        (earWord (a + b) sigma j) := by
  classical
  let q : ℤ := 2 ^ a
  let r : ℤ := 2 ^ b
  let Q : ℤ := 2 ^ (a - 1)
  let R : ℤ := 2 ^ (b - 1)
  let C : ℤ := q * R - 1
  have hb : 2 ≤ b := by omega
  have hq : q = 2 * Q := by
    dsimp [q, Q]
    calc
      (2 : ℤ) ^ a = 2 ^ ((a - 1) + 1) :=
        congrArg (fun n : ℕ => (2 : ℤ) ^ n) (by omega)
      _ = 2 * 2 ^ (a - 1) := by rw [pow_succ]; ring
  have hr : r = 2 * R := by
    dsimp [r, R]
    calc
      (2 : ℤ) ^ b = 2 ^ ((b - 1) + 1) :=
        congrArg (fun n : ℕ => (2 : ℤ) ^ n) (by omega)
      _ = 2 * 2 ^ (b - 1) := by rw [pow_succ]; ring
  have hq4 : 4 ≤ q := by
    have h := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) ha
    norm_num at h
    exact h
  have hr4 : 4 ≤ r := by
    have h := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) hb
    norm_num at h
    exact h
  have hQ2 : 2 ≤ Q := by omega
  have hR2 : 2 ≤ R := by omega
  have assemble (u v : ℕ) (hu : u < 2 ^ (b - 1)) (hv : v < 2 ^ (a - 1))
      (hs : let h : ℤ := C - ((q + 1) * u + (r + 1) * v)
        0 ≤ h ∧ h ≤ R ∧ q ≤ 2 * h + v ∧ 2 * h + v ≤ q + r) :
      ∃ sigma : List (Fin (a + b)), ∃ j : ℕ, j ≤ a + b ∧
        OriginalOrder (a + b) (2 ^ a + 1) sigma ∧
        OriginalOrder (a + b + 1) (2 * (2 ^ a + 1))
          (earWord (a + b) sigma j) := by
    exact realize a b u v ha hb hu hv hs
  by_cases hEq : a = b
  · let u : ℕ := 2 ^ (a - 1) - 1
    have hu : u < 2 ^ (b - 1) := by
      rw [← hEq]
      dsimp [u]
      have hp : 0 < (2 : ℕ) ^ (a - 1) := by positivity
      omega
    have hum : (u : ℤ) = Q - 1 := by
      have hp : 1 ≤ 2 ^ (a - 1) := Nat.one_le_two_pow
      simp [u, Q, Nat.cast_sub hp]
    have hRQ : R = Q := by simp only [R, Q, hEq]
    have hheight : C - ((q + 1) * (u : ℤ) + (r + 1) * (0 : ℕ)) = Q := by
      rw [hum]
      dsimp [C]
      rw [hRQ, hq]
      ring
    apply assemble u 0 hu (by positivity)
    dsimp only
    rw [hheight]
    omega
  · by_cases hGap : a + 2 ≤ b
    · let u : ℕ := ((C - Q) / (q + 1)).toNat
      have hD : 0 ≤ C - Q := by dsimp [C]; nlinarith
      have huCast : (u : ℤ) = (C - Q) / (q + 1) := by
        exact Int.toNat_of_nonneg (Int.ediv_nonneg hD (by omega))
      have hfloor : (q + 1) * (u : ℤ) ≤ C - Q ∧
          C - Q < (q + 1) * ((u : ℤ) + 1) := by
        have hh := Int.emod_add_mul_ediv (C - Q) (q + 1)
        have hlo := Int.emod_nonneg (C - Q) (show q + 1 ≠ 0 by omega)
        have hhi := Int.emod_lt_of_pos (C - Q) (show 0 < q + 1 by omega)
        rw [← huCast] at hh
        constructor <;> nlinarith
      have hR2q : 2 * q ≤ R := by
        have hh := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2)
          (show a + 1 ≤ b - 1 by omega)
        simpa [q, R, pow_succ, mul_comm] using hh
      have huR : (u : ℤ) < R := by
        have hh : C - Q < (q + 1) * R := by dsimp [C]; nlinarith
        exact (Int.mul_lt_mul_left (show 0 < q + 1 by omega)).mp
          (lt_of_le_of_lt hfloor.1 hh)
      have hu : u < 2 ^ (b - 1) := by
        dsimp [R] at huR
        exact_mod_cast huR
      have hlow : Q ≤ C - (q + 1) * (u : ℤ) := by omega
      have hhigh : C - (q + 1) * (u : ℤ) ≤ Q + q := by nlinarith [hfloor.2]
      apply assemble u 0 hu (by positivity)
      dsimp only
      norm_num only [Nat.cast_zero, mul_zero, add_zero]
      omega
    · have hAdj : b = a + 1 := by omega
      by_cases ha2 : a = 2
      · subst a
        subst b
        let sigma : List (Fin 5) := [0, 1, 4, 3, 2]
        have hp : sigma.Perm (List.finRange 5) := by decide
        have ho : OriginalOrder 5 5 sigma := by
          refine ⟨hp, ?_, ?_⟩
          · norm_num [sigma, actualSource, centered, modulus]
          · intro n
            by_cases hn : n ≤ 5
            · interval_cases n <;> norm_num [sigma, actualSource, centered, modulus]
            · rw [List.take_of_length_le (show sigma.length ≤ n by simp [sigma]; omega)]
              norm_num [sigma, actualSource, centered, modulus]
        refine ⟨sigma, 4, by norm_num, ho, ?_⟩
        refine ⟨by decide, ?_, ?_⟩
        · norm_num [sigma, earWord, actualSource, centered, modulus]
        · intro n
          by_cases hn : n ≤ 6
          · interval_cases n <;> norm_num [sigma, earWord, actualSource, centered, modulus]
          · rw [List.take_of_length_le (show (earWord 5 sigma 4).length ≤ n by
              norm_num [sigma, earWord]; omega)]
            norm_num [sigma, earWord, actualSource, centered, modulus]
      · let v : ℕ := 2 ^ (a - 1) - 1
        have hqr : r = 2 * q := by
          dsimp [q, r]; rw [hAdj, pow_succ]; ring
        have hRq : R = q := by
          dsimp [R, q]; rw [hAdj, Nat.add_sub_cancel]
        have hv : v < 2 ^ (a - 1) := by
          dsimp [v]
          have : 0 < (2 : ℕ) ^ (a - 1) := by positivity
          omega
        have hu : 1 < 2 ^ (b - 1) := by
          have hh : (1 : ℤ) < 2 ^ (b - 1) := by change 1 < R; omega
          exact_mod_cast hh
        have hvm : (v : ℤ) = Q - 1 := by
          have hp : 1 ≤ 2 ^ (a - 1) := Nat.one_le_two_pow
          simp [v, Q, Nat.cast_sub hp]
        have hheight : C - ((q + 1) * (1 : ℕ) + (r + 1) * (v : ℤ)) = Q - 1 := by
          dsimp [C]
          rw [hRq, hqr, hvm, hq]
          ring
        have hQ4 : 4 ≤ Q := by
          have hh := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2)
            (show 2 ≤ a - 1 by omega)
          norm_num at hh
          exact hh
        apply assemble 1 v hu hv
        dsimp only
        rw [hheight, hvm]
        omega

#print axioms actualSource_two_negative_nondec_joint_lift

end D5.S3.Combinatorics.Circle.TwoNegativeNondecreasingJointLift
