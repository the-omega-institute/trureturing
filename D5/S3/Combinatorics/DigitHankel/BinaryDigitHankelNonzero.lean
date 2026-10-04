/- GID: D5/S3/Combinatorics/DigitHankel/BinaryDigitHankelNonzero
   generality: G
   mirror-B: D5/B/S3/Combinatorics/DigitHankel/BinaryDigitHankelNonzero
   mirror-E: none(waiver:binary-hankel-family-inductions)
   anchors: [mathlib/module/Mathlib.Tactic]
   utility: none
   digest: Simultaneous induction evaluates centers and the adjacent endpoint determinants. -/

import D5.S3.Combinatorics.DigitHankel.BinaryDigitHankelRecurrence
import D5.S3.Combinatorics.DigitHankel.BinaryDigitHankelStructure
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace D5.S3.Combinatorics.DigitHankel.BinaryDigitHankel

open BinaryDigitHankelDefs BinaryDigitHankelRecurrence
open scoped Matrix

/-- Both endpoint families have explicit powers of two and zero auxiliary determinants. -/
theorem endpoint_evaluations (k : ℕ) (hk : 2 ≤ k) :
    hankel (threshold k - 1) (-2) =
      -(2 : ℤ) ^ ((k + 1) * threshold k - (3 * k) / 2 - 4) ∧
    hankel (threshold k + 1) (-2) =
      (2 : ℤ) ^ ((k + 1) * threshold k + k / 2 + 2 - k % 2) ∧
    endpoint (threshold k - 1) (-2) = 0 ∧ endpoint (threshold k + 1) (-2) = 0 := by
  classical
  have index (k : ℕ) (hk : 3 ≤ k) :
    2 ^ k < threshold k - 1 ∧ threshold k + 1 ≤ 3 * 2 ^ (k - 1) ∧
    2 ^ (k + 1) - (threshold k - 1) + 1 = threshold (k - 1) + 1 ∧
    2 ^ (k + 1) - (threshold k + 1) + 1 = threshold (k - 1) - 1 ∧
    (k + 1) * threshold k - (3 * k) / 2 - 4 =
      (k + 2) * (2 * (threshold k - 1) - 2 ^ (k + 1) - 1) +
        (k * threshold (k - 1) + (k - 1) / 2 + 2 - (k - 1) % 2) ∧
    (k + 1) * threshold k + k / 2 + 2 - k % 2 =
      (k + 2) * (2 * (threshold k + 1) - 2 ^ (k + 1) - 1) +
        (k * threshold (k - 1) - (3 * (k - 1)) / 2 - 4) := by
    have residue (j : ℕ) : 3 * threshold j + j % 2 = 2 ^ (j + 2) + 2 := by
      have rem (l : ℕ) : 2 ^ (l + 2) % 3 = 1 + l % 2 := by
        induction l with
        | zero => decide
        | succ l ih =>
          rw [show l + 1 + 2 = l + 2 + 1 by omega, pow_succ, Nat.mul_mod, ih]
          have := Nat.mod_lt l (by decide : 0 < 2)
          rcases (by omega : l % 2 = 0 ∨ l % 2 = 1) with he | he
          · have hs : (l + 1) % 2 = 1 := by omega
            rw [he, hs]
          · have hs : (l + 1) % 2 = 0 := by omega
            rw [he, hs]
      have hm : (2 ^ (j + 2) + 2) % 3 = j % 2 := by
        rw [Nat.add_mod, rem]
        have := Nat.mod_lt j (by decide : 0 < 2)
        omega
      unfold threshold
      have := Nat.mod_add_div (2 ^ (j + 2) + 2) 3
      omega
    have hcur := residue k
    have hprev := residue (k - 1)
    have hpower : 2 ^ (k + 2) = 4 * 2 ^ k := by rw [pow_add]; ring
    have hpower' : 2 ^ (k - 1 + 2) = 2 * 2 ^ k := by
      rw [show k - 1 + 2 = k + 1 by omega, pow_succ]; ring
    have hpower'' : 2 ^ k = 2 * 2 ^ (k - 1) := by
      calc
        2 ^ k = 2 ^ (k - 1 + 1) := by congr 1; omega
        _ = 2 * 2 ^ (k - 1) := by rw [pow_succ]; ring
    have hpow : 4 ≤ 2 ^ (k - 1) := by
      exact Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega : 2 ≤ k - 1)
    have hp := Nat.mod_lt k (by decide : 0 < 2)
    have hpp := Nat.mod_lt (k - 1) (by decide : 0 < 2)
    rw [hpower] at hcur
    rw [hpower'] at hprev
    have hc : threshold k = 2 * threshold (k - 1) - k % 2 := by omega
    have hsum : threshold k + threshold (k - 1) = 2 ^ (k + 1) + 1 := by
      rw [pow_succ]; omega
    have hlo : 2 ^ k < threshold k - 1 := by omega
    have hhi : threshold k + 1 ≤ 3 * 2 ^ (k - 1) := by
      by_cases he : k = 3
      · subst k; decide
      · have hl : 8 ≤ 2 ^ (k - 1) :=
          Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega : 3 ≤ k - 1)
        omega
    refine ⟨hlo, hhi, by omega, by omega, ?_, ?_⟩
    · let A := 2 * (threshold k - 1) - 2 ^ (k + 1) - 1
      let N := threshold k
      let M := threshold (k - 1)
      have hM : 6 ≤ M := by
        have hpowM : 8 ≤ 2 ^ k :=
          Nat.pow_le_pow_right (by decide : 1 ≤ 2) hk
        dsimp [M]; omega
      have he1 : A + M + 2 = N := by dsimp [A, M, N]; omega
      have he2 : N + k % 2 = 2 * M := by dsimp [M, N]; omega
      have hf1 : (3 * k) / 2 + (k - 1) / 2 + 1 = 2 * k := by omega
      have hf2 : k % 2 + (k - 1) % 2 = 1 := by omega
      have hb1 : (3 * k) / 2 + 4 ≤ (k + 1) * N := by
        have : (k + 1) * 6 ≤ (k + 1) * N :=
          Nat.mul_le_mul_left (k + 1) (by omega : 6 ≤ N)
        omega
      have hb2 : (k - 1) % 2 ≤ k * M + (k - 1) / 2 + 2 := by omega
      have hl := Nat.sub_add_cancel hb1
      have hr := Nat.sub_add_cancel hb2
      change (k + 1) * N - (3 * k) / 2 - 4 =
        (k + 2) * A + (k * M + (k - 1) / 2 + 2 - (k - 1) % 2)
      rw [Nat.sub_sub]
      nlinarith only [he1, he2, hf1, hf2, hl, hr]
    · let A := 2 * (threshold k + 1) - 2 ^ (k + 1) - 1
      let N := threshold k
      let M := threshold (k - 1)
      have hM : 6 ≤ M := by
        have hpowM : 8 ≤ 2 ^ k :=
          Nat.pow_le_pow_right (by decide : 1 ≤ 2) hk
        dsimp [M]; omega
      have he1 : A + M = N + 2 := by dsimp [A, M, N]; omega
      have he2 : N + k % 2 = 2 * M := by dsimp [M, N]; omega
      have hf1 : k / 2 + (3 * (k - 1)) / 2 = 2 * k - 2 := by omega
      have hb1 : k % 2 ≤ (k + 1) * N + k / 2 + 2 := by omega
      have hb2 : (3 * (k - 1)) / 2 + 4 ≤ k * M := by
        have : k * 6 ≤ k * M := Nat.mul_le_mul_left k hM
        omega
      have hl := Nat.sub_add_cancel hb1
      have hr := Nat.sub_add_cancel hb2
      change (k + 1) * N + k / 2 + 2 - k % 2 =
        (k + 2) * A + (k * M - (3 * (k - 1)) / 2 - 4)
      rw [Nat.sub_sub]
      have hf2 : k / 2 + (3 * (k - 1)) / 2 + 2 = 2 * k := by omega
      nlinarith only [he1, he2, hf2, hl, hr]
  induction k using Nat.strong_induction_on with
  | h k ih =>
    by_cases hbase : k = 2
    · subst k
      change hankel 5 (-2) = -(2 : ℤ) ^ 11 ∧ hankel 7 (-2) = (2 : ℤ) ^ 21 ∧
        endpoint 5 (-2) = 0 ∧ endpoint 7 (-2) = 0
      have base (n : ℕ) (hn : n = 5 ∨ n = 7) :
          hankel n (-2) = if n = 5 then -(2 : ℤ) ^ 11 else (2 : ℤ) ^ 21 := by
        rcases hn with rfl | rfl
        · let A : Matrix (Fin 5) (Fin 5) ℤ :=
            Matrix.of fun i j => digitSum (i + j) (-2)
          let M : Matrix (Fin 5) (Fin 5) ℤ :=
            !![1, 0, 0, 0, 0;
             0, 1, 0, 0, 0;
             2, 5, 1, 0, 0;
             3, 3, 1, 1, 0;
             -2, 1, 2, -2, 1]
          let U : Matrix (Fin 5) (Fin 5) ℤ :=
            !![1, -2, -1, 4, 5;
             0, 1, -2, -1, 4;
             0, 0, -8, 8, 32;
             0, 0, 0, 16, 32;
             0, 0, 0, 0, -16]
          have hmul : M * A.submatrix (Equiv.swap 0 1) id = U := by decide
          have hMl : M.IsLowerTriangular := by decide
          have hUu : U.IsUpperTriangular := by decide
          have hM : M.det = 1 := by
            rw [Matrix.det_of_isLowerTriangular M hMl]
            decide
          have hU : U.det = 2048 := by
            rw [Matrix.det_of_isUpperTriangular hUu]
            decide
          have h := congrArg Matrix.det hmul
          rw [Matrix.det_mul, hM, Matrix.det_permute, hU] at h
          have hsign : (Equiv.Perm.sign (Equiv.swap (0 : Fin 5) 1) : ℤ) = -1 := by
            simp
          rw [hsign] at h
          change A.det = _
          norm_num at h ⊢
          omega
        · let A : Matrix (Fin 7) (Fin 7) ℤ :=
            Matrix.of fun i j => digitSum (i + j) (-2)
          let M : Matrix (Fin 7) (Fin 7) ℤ :=
            !![1, 0, 0, 0, 0, 0, 0;
             0, 1, 0, 0, 0, 0, 0;
             2, 5, 1, 0, 0, 0, 0;
             3, 3, 1, 1, 0, 0, 0;
             -2, 1, 2, -2, 1, 0, 0;
             -2, 6, 5, -3, 1, 1, 0;
             2, 3, 7, 0, -1, 2, 3]
          let U : Matrix (Fin 7) (Fin 7) ℤ :=
            !![1, -2, -1, 4, 5, 2, 3;
             0, 1, -2, -1, 4, 5, 2;
             0, 0, -8, 8, 32, 32, 8;
             0, 0, 0, 16, 32, 16, 0;
             0, 0, 0, 0, -16, 16, -16;
             0, 0, 0, 0, 0, 48, -32;
             0, 0, 0, 0, 0, 0, -64]
          have hmul : M * A.submatrix (Equiv.swap 0 1) id = U := by decide
          have hMl : M.IsLowerTriangular := by decide
          have hUu : U.IsUpperTriangular := by decide
          have hM : M.det = 3 := by
            rw [Matrix.det_of_isLowerTriangular M hMl]
            decide
          have hU : U.det = -6291456 := by
            rw [Matrix.det_of_isUpperTriangular hUu]
            decide
          have h := congrArg Matrix.det hmul
          rw [Matrix.det_mul, hM, Matrix.det_permute, hU] at h
          have hsign : (Equiv.Perm.sign (Equiv.swap (0 : Fin 7) 1) : ℤ) = -1 := by
            simp
          rw [hsign] at h
          change A.det = _
          norm_num at h ⊢
          omega
      have aux (n : ℕ) (hn : n = 5 ∨ n = 7) : endpoint n (-2) = 0 := by
        rcases hn with rfl | rfl
        · let v : Fin 5 → ℤ := ![-1, 0, -1, 0, 2]
          have hz : (Matrix.of fun i j : Fin 5 => if j.val + 1 < 5 then
              digitSum (i.val + j.val + 1) (-2) - digitSum (i.val + j.val) (-2)
                else 1) *ᵥ v = 0 := by decide
          by_contra h
          have hzero := Matrix.eq_zero_of_mulVec_eq_zero h hz
          have := congrFun hzero 0
          norm_num [v] at this
        · let v : Fin 7 → ℤ := ![1, 1, 0, 0, 1, 1, 4]
          have hz : (Matrix.of fun i j : Fin 7 => if j.val + 1 < 7 then
              digitSum (i.val + j.val + 1) (-2) - digitSum (i.val + j.val) (-2)
                else 1) *ᵥ v = 0 := by decide
          by_contra h
          have hzero := Matrix.eq_zero_of_mulVec_eq_zero h hz
          have := congrFun hzero 0
          norm_num [v] at this
      refine ⟨?_, ?_, aux 5 (Or.inl rfl), aux 7 (Or.inr rfl)⟩
      · simpa using base 5 (Or.inl rfl)
      · simpa using base 7 (Or.inr rfl)
    have hk3 : 3 ≤ k := by omega
    obtain ⟨hlo, hhi, hreflectL, hreflectR, hlambda, hrho⟩ := index k hk3
    obtain ⟨hHL, hHR, hEL, hER⟩ := ih (k - 1) (by omega) (by omega)
    have hpow : 8 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hk3
    have hleft := reflection k (threshold k - 1) (-2) (by omega) (by omega) hlo
      (by omega)
    have hright := reflection k (threshold k + 1) (-2) (by omega) (by omega)
      (by omega) hhi
    dsimp only at hleft hright
    rw [hreflectL, hHR, hER] at hleft
    rw [hreflectR, hHL, hEL] at hright
    have hpar : threshold k % 2 = k % 2 := by
      have residue (j : ℕ) : 3 * threshold j + j % 2 = 2 ^ (j + 2) + 2 := by
        have rem (l : ℕ) : 2 ^ (l + 2) % 3 = 1 + l % 2 := by
          induction l with
          | zero => decide
          | succ l ih =>
            rw [show l + 1 + 2 = l + 2 + 1 by omega, pow_succ, Nat.mul_mod, ih]
            have := Nat.mod_lt l (by decide : 0 < 2)
            rcases (by omega : l % 2 = 0 ∨ l % 2 = 1) with he | he
            · have hs : (l + 1) % 2 = 1 := by omega
              rw [he, hs]
            · have hs : (l + 1) % 2 = 0 := by omega
              rw [he, hs]
        have hm : (2 ^ (j + 2) + 2) % 3 = j % 2 := by
          rw [Nat.add_mod, rem]
          have := Nat.mod_lt j (by decide : 0 < 2)
          omega
        unfold threshold
        have := Nat.mod_add_div (2 ^ (j + 2) + 2) 3
        omega
      have h := residue k
      rw [pow_add] at h
      norm_num at h
      omega
    have factor (n : ℕ) (hn : n % 2 = (k + 1) % 2)
        (hb : 2 ^ k < n) :
        (-1 : ℤ) ^ n * ((-2 : ℤ) ^ (k + 1) - 2 * (-2) ^ k) ^
          (2 * n - 2 ^ (k + 1) - 1) =
        (2 : ℤ) ^ ((k + 2) * (2 * n - 2 ^ (k + 1) - 1)) := by
      let a := 2 * n - 2 ^ (k + 1) - 1
      have ha : a % 2 = 1 := by dsimp [a]; rw [pow_succ]; omega
      have hu : (-2 : ℤ) ^ (k + 1) - 2 * (-2) ^ k =
          (-1 : ℤ) ^ (k + 1) * (2 : ℤ) ^ (k + 2) := by
        rw [show (-2 : ℤ) = (-1) * 2 by norm_num, mul_pow, mul_pow]
        rw [pow_succ, pow_succ, show k + 2 = k + 1 + 1 by omega,
          pow_succ, pow_succ]
        ring
      have hp : (n + (k + 1) * a) % 2 = 0 := by
        rw [Nat.add_mod, Nat.mul_mod, ha, hn]
        have := Nat.mod_lt (k + 1) (by decide : 0 < 2)
        omega
      change (-1 : ℤ) ^ n * ((-2 : ℤ) ^ (k + 1) - 2 * (-2) ^ k) ^ a = _
      rw [hu, mul_pow, ← pow_mul, ← mul_assoc, ← pow_mul, ← pow_add,
        neg_one_pow_eq_pow_mod_two, hp, pow_zero, one_mul]
    have hfL := factor (threshold k - 1) (by omega) hlo
    have hfR := factor (threshold k + 1) (by omega) (by omega)
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hleft.1]
      simp only [mul_zero, add_zero]
      rw [pow_succ, mul_neg_one]
      simp only [neg_mul]
      rw [hfL, ← pow_add, show k - 1 + 1 = k by omega, ← hlambda]
    · rw [hright.1]
      simp only [mul_zero, add_zero]
      rw [pow_succ, mul_neg_one]
      simp only [neg_mul, mul_neg, neg_neg]
      rw [hfR, ← pow_add, show k - 1 + 1 = k by omega, ← hrho]
    · simpa using hleft.2
    · simpa using hright.2

/-- A simultaneous reflection induction evaluates the centers and their auxiliary determinants. -/
theorem center_evaluations (k : ℕ) :
    endpoint (threshold k) (-2) =
      (-1 : ℤ) ^ k * (2 : ℤ) ^ ((k + 1) * threshold k - (k + 1) / 2) ∧
    12 * hankel (threshold k) (-2) =
      -((2 : ℤ) ^ (k + 1) + (-1 : ℤ) ^ k) * endpoint (threshold k) (-2) := by
  classical
  have residue (j : ℕ) : 3 * threshold j + j % 2 = 2 ^ (j + 2) + 2 := by
    have rem (l : ℕ) : 2 ^ (l + 2) % 3 = 1 + l % 2 := by
      induction l with
      | zero => decide
      | succ l ih =>
        rw [show l + 1 + 2 = l + 2 + 1 by omega, pow_succ, Nat.mul_mod, ih]
        have := Nat.mod_lt l (by decide : 0 < 2)
        rcases (by omega : l % 2 = 0 ∨ l % 2 = 1) with he | he
        · have hs : (l + 1) % 2 = 1 := by omega
          rw [he, hs]
        · have hs : (l + 1) % 2 = 0 := by omega
          rw [he, hs]
    have hm : (2 ^ (j + 2) + 2) % 3 = j % 2 := by
      rw [Nat.add_mod, rem]
      have := Nat.mod_lt j (by decide : 0 < 2)
      omega
    unfold threshold
    have := Nat.mod_add_div (2 ^ (j + 2) + 2) 3
    omega
  induction k using Nat.strong_induction_on with
  | h k ih =>
    by_cases hzero : k = 0
    · subst k
      decide
    by_cases hone : k = 1
    · subst k
      decide
    have hk : 2 ≤ k := by omega
    have hcur := residue k
    have hprev := residue (k - 1)
    have hp := Nat.mod_lt k (by decide : 0 < 2)
    have hpp := Nat.mod_lt (k - 1) (by decide : 0 < 2)
    have hpow : 4 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hk
    have hpow' : 2 ≤ 2 ^ (k - 1) :=
      Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega : 1 ≤ k - 1)
    have hpcur : 2 ^ (k + 2) = 4 * 2 ^ k := by rw [pow_add]; ring
    have hpprev : 2 ^ (k - 1 + 2) = 2 * 2 ^ k := by
      rw [show k - 1 + 2 = k + 1 by omega, pow_succ]; ring
    have hpstep : 2 ^ k = 2 * 2 ^ (k - 1) := by
      calc
        2 ^ k = 2 ^ (k - 1 + 1) := by congr 1; omega
        _ = 2 * 2 ^ (k - 1) := by rw [pow_succ]; ring
    rw [hpcur] at hcur
    rw [hpprev] at hprev
    have hlo : 2 ^ k < threshold k := by omega
    have hhi : threshold k ≤ 3 * 2 ^ (k - 1) := by omega
    have hsum : threshold k + threshold (k - 1) = 2 ^ (k + 1) + 1 := by
      rw [pow_succ]; omega
    have hreflect : 2 ^ (k + 1) - threshold k + 1 = threshold (k - 1) := by omega
    have htwice : threshold k + k % 2 = 2 * threshold (k - 1) := by omega
    have hpar : threshold k % 2 = k % 2 := by omega
    let a := 2 * threshold k - 2 ^ (k + 1) - 1
    let b := (k + 2) * a
    let u : ℤ := (-2) ^ (k + 1) - 2 * (-2) ^ k
    let P : ℤ := 2 ^ b
    let C : ℤ := ((-2 : ℤ) ^ k) ^ 2 * u ^ (a - 1)
    have ha : a + threshold (k - 1) = threshold k := by dsimp [a]; omega
    have hapos : 1 ≤ a := by dsimp [a]; rw [pow_succ]; omega
    have haodd : a % 2 = 1 := by dsimp [a]; rw [pow_succ]; omega
    have hu : u = (-1 : ℤ) ^ (k + 1) * (2 : ℤ) ^ (k + 2) := by
      dsimp [u]
      rw [show (-2 : ℤ) = (-1) * 2 by norm_num, mul_pow, mul_pow]
      rw [pow_succ, pow_succ, show k + 2 = k + 1 + 1 by omega, pow_succ, pow_succ]
      ring
    have hcoefE : (-1 : ℤ) ^ threshold k * u ^ a = -P := by
      have hm : (threshold k + (k + 1) * a) % 2 = 1 := by
        rw [Nat.add_mod, Nat.mul_mod, haodd, hpar]
        omega
      dsimp only [P, b]
      rw [hu, mul_pow, ← pow_mul, ← mul_assoc, ← pow_mul, ← pow_add,
        neg_one_pow_eq_pow_mod_two, hm]
      simp
    have hcoefH : (-1 : ℤ) ^ (threshold k + 1) * u ^ a = P := by
      rw [pow_succ, mul_neg_one, neg_mul, hcoefE, neg_neg]
    have hC : 4 * C = P * (2 : ℤ) ^ k := by
      have hameven : (a - 1) % 2 = 0 := by omega
      have hs : (-1 : ℤ) ^ ((k + 1) * (a - 1)) = 1 := by
        rw [neg_one_pow_eq_pow_mod_two, Nat.mul_mod, hameven]
        simp
      have he : 2 + k * 2 + (k + 2) * (a - 1) = b + k := by
        dsimp [b]
        have h := Nat.sub_add_cancel hapos
        nlinarith only [h]
      have heven : (-1 : ℤ) ^ (k * 2) = 1 := by
        rw [neg_one_pow_eq_pow_mod_two, Nat.mul_mod]
        simp
      have htwopow : ((-2 : ℤ) ^ k) ^ 2 = (2 : ℤ) ^ (k * 2) := by
        rw [← pow_mul, neg_pow, heven, one_mul]
      dsimp only [C, P]
      rw [htwopow, hu, mul_pow, ← pow_mul (-1 : ℤ) (k + 1) (a - 1), hs,
        one_mul, ← pow_mul (2 : ℤ) (k + 2) (a - 1),
        show (4 : ℤ) = 2 ^ 2 by norm_num, ← mul_assoc,
        ← pow_add, ← pow_add, he, pow_add]
    have hB : (k + 1) * threshold k - (k + 1) / 2 =
        b + (k * threshold (k - 1) - k / 2) := by
      have hM : 3 ≤ threshold (k - 1) := by omega
      have hN : 3 ≤ threshold k := by omega
      have hf : (k + 1) / 2 = k / 2 + k % 2 := by omega
      have hbcur : (k + 1) / 2 ≤ (k + 1) * threshold k := by
        have : (k + 1) * 3 ≤ (k + 1) * threshold k :=
          Nat.mul_le_mul_left (k + 1) hN
        omega
      have hbprev : k / 2 ≤ k * threshold (k - 1) := by
        have : k * 3 ≤ k * threshold (k - 1) := Nat.mul_le_mul_left k hM
        omega
      have hc := Nat.sub_add_cancel hbcur
      have hm := Nat.sub_add_cancel hbprev
      dsimp [b]
      nlinarith only [ha, htwice, hf, hc, hm]
    obtain ⟨hEprev, hHprev⟩ := ih (k - 1) (by omega)
    rw [show k - 1 + 1 = k by omega] at hEprev hHprev
    have hsgn : (-1 : ℤ) ^ k = -(-1 : ℤ) ^ (k - 1) := by
      calc
        (-1 : ℤ) ^ k = (-1) ^ (k - 1 + 1) := by congr 1; omega
        _ = -(-1) ^ (k - 1) := by rw [pow_succ]; ring
    have hrec := reflection k (threshold k) (-2) (by omega) (by omega) hlo hhi
    dsimp only at hrec
    rw [hreflect] at hrec
    change (hankel (threshold k) (-2) =
      ((-1 : ℤ) ^ (threshold k + 1) * u ^ a) * hankel (threshold (k - 1)) (-2) +
        C * endpoint (threshold (k - 1)) (-2)) ∧
      (endpoint (threshold k) (-2) =
        ((-1 : ℤ) ^ threshold k * u ^ a) * endpoint (threshold (k - 1)) (-2)) at hrec
    rw [hcoefH, hcoefE] at hrec
    refine ⟨?_, ?_⟩
    · calc
        endpoint (threshold k) (-2) =
            -P * ((-1 : ℤ) ^ (k - 1) * (2 : ℤ) ^
              (k * threshold (k - 1) - k / 2)) := by rw [hrec.2, hEprev]
        _ = (-1 : ℤ) ^ k * (2 : ℤ) ^
              (b + (k * threshold (k - 1) - k / 2)) := by
            rw [hsgn, pow_add]
            dsimp [P]
            ring
        _ = (-1 : ℤ) ^ k * (2 : ℤ) ^
              ((k + 1) * threshold k - (k + 1) / 2) := by rw [hB]
    · calc
        12 * hankel (threshold k) (-2) =
            P * (12 * hankel (threshold (k - 1)) (-2)) +
              (4 * C) * (3 * endpoint (threshold (k - 1)) (-2)) := by
            rw [hrec.1]
            ring
        _ = -((2 : ℤ) ^ (k + 1) + (-1 : ℤ) ^ k) * endpoint (threshold k) (-2) := by
            rw [hHprev, hC, hrec.2, hsgn, pow_succ]
            ring

end D5.S3.Combinatorics.DigitHankel.BinaryDigitHankel
