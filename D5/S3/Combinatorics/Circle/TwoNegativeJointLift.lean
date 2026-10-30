/- GID: D5/S3/Combinatorics/Circle/TwoNegativeJointLift
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/TwoNegativeJointLift
   mirror-E: none(waiver:no-escape-mirror-specified)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Native common-cut two-negative lift for the asymmetric dyadic source.
-/

import D5.S3.Combinatorics.Circle.RunFirstEarTransport
import D5.S3.Combinatorics.Circle.DyadicPrefix

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.TwoNegativeJointLift
open SourceWidth PeriodicShortening PeriodicShorteningArithmetic
open RunFirstEarTransport
open scoped BigOperators

private theorem nonneg_strip {α : Type*} (f : α → ℤ) (B : ℤ) (l : List α)
    (hpos : ∀ x ∈ l, 0 ≤ f x) (hsum : (l.map f).sum ≤ B) :
    InStrip f B 0 l := by
  induction l with
  | nil => simp [InStrip]
  | cons x xs ih =>
    have hx := hpos x (by simp)
    have hrest : ∀ y ∈ xs, 0 ≤ f y := fun y hy => hpos y (by simp [hy])
    have htail : 0 ≤ (xs.map f).sum := List.sum_nonneg (by
      intro y hy
      obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hy
      exact hrest z hz)
    have hsum' : (xs.map f).sum ≤ B - f x := by
      simp only [List.map_cons, List.sum_cons] at hsum
      omega
    refine ⟨by omega, by omega, ?_⟩
    exact ih hrest (by omega)

private theorem nonneg_list_sum {α : Type*} {f : α → ℤ} {l : List α}
    (h : ∀ x ∈ l, 0 ≤ f x) : 0 ≤ (l.map f).sum := by
  exact List.sum_nonneg (by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    exact h y hy)

theorem actualSource_two_negative_joint_lift (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hba : b < a) :
    ∃ sigma : List (Fin (a + b)), ∃ j : ℕ, j ≤ a + b ∧
      OriginalOrder (a + b) (2 ^ a + 1) sigma ∧
      OriginalOrder (a + b + 1) (2 * (2 ^ a + 1))
        (earWord (a + b) sigma j) := by
  classical
  let k := a + b
  let q := 2 ^ a
  let r := 2 ^ b
  let v := q + 1
  let A := 2 * r + 1
  let N : ℤ := modulus k
  let C : ℤ := N / 2
  let alpha : Fin k := ⟨b - 1, by dsimp [k]; omega⟩
  let beta : Fin k := ⟨k - 1, by dsimp [k]; omega⟩
  let fresh : Fin (k + 1) := Fin.last k
  let U : List (Fin k) := (List.finRange (b - 1)).map (fun i =>
    ⟨i.val, by dsimp [k]; omega⟩)
  let V : List (Fin k) := (List.finRange (a - 1)).map (fun i =>
    ⟨b + i.val, by dsimp [k]; omega⟩)
  let positives := U ++ V
  have hab : 1 ≤ a - b := by omega
  have hqpow : (q : ℤ) = (2 : ℤ) ^ a := by rfl
  have hrpow : (r : ℤ) = (2 : ℤ) ^ b := by rfl
  have hqr : (q : ℤ) * r = (2 : ℤ) ^ k := by
    dsimp [q, r, k]
    rw [← pow_add]
  have hq2r : 2 * (r : ℤ) ≤ q := by
    have hp : (2 : ℕ) ^ (b + 1) ≤ 2 ^ a := by
      exact Nat.pow_le_pow_right (by omega) (by omega)
    exact_mod_cast (show 2 * r ≤ q by simpa [r, Nat.pow_succ] using hp)
  have hr4 : (4 : ℤ) ≤ r := by
    have := Nat.one_le_two_pow (n := b - 2)
    dsimp [r]
    rw [show b = (b - 2) + 2 by omega, pow_add]
    norm_num at *
    nlinarith
  have hN : N = (q : ℤ) * r - 1 := by
    dsimp [N, modulus]
    rw [← hqr]
    norm_num
  have hNpos : 0 < N := by
    rw [hN]
    nlinarith [show (2 : ℤ) ≤ q by exact_mod_cast (show 2 ≤ q by dsimp [q]; omega)]
  have hNodd : N % 2 = 1 := by rw [hN]; omega
  have hC : 2 * C = N - 1 := by dsimp [C]; omega
  have hM : modulus (k + 1) = 2 * N + 1 := by
    dsimp [N, modulus]
    rw [show k + 1 = (a + b) + 1 by rfl, pow_succ, hqr]
    ring
  have hMhalf : modulus (k + 1) / 2 = N := by rw [hM]; omega
  have hMpos : 0 < modulus (k + 1) := by rw [hM]; omega
  have hModd : modulus (k + 1) % 2 = 1 := by rw [hM]; omega
  have old_centered (i : Fin k) (x : ℤ)
      (hx : -C ≤ x ∧ x ≤ C)
      (hmod : x % N = ((2 : ℤ) ^ i.val * (v : ℕ)) % N) :
      actualSource k v i = x := by
    unfold actualSource
    apply centered_unique hNpos hNodd (centered_bounds hNpos hNodd _) hx
    simpa [N] using hmod
  have new_centered (i : Fin (k + 1)) (x : ℤ)
      (hx : -N ≤ x ∧ x ≤ N)
      (hmod : x % modulus (k + 1) =
        ((2 : ℤ) ^ i.val * (2 * (v : ℕ))) % modulus (k + 1)) :
      actualSource (k + 1) (2 * v) i = x := by
    unfold actualSource
    apply centered_unique hMpos hModd (centered_bounds hMpos hModd _) hx
    simpa using hmod
  have hUval (i : Fin (b - 1)) :
      actualSource k v ⟨i.val, by dsimp [k]; omega⟩ =
        (q + 1 : ℤ) * 2 ^ i.val := by
    have hi : i.val ≤ b - 2 := by omega
    have hpowi : (2 : ℤ) ^ i.val ≤ (2 : ℤ) ^ (b - 2) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have hhalf : (q + 1 : ℤ) * 2 ^ i.val ≤ C := by
      rw [hC, hN, ← hqr]
      nlinarith [hpowi, hq2r, hr4]
    apply old_centered _ _ ⟨by positivity, hhalf⟩
    rw [Int.emod_eq_of_lt (by positivity)]
    · congr 1
      norm_num [v]
    · rw [← hqr]
      nlinarith [hpowi, hq2r]
  have hVval (i : Fin (a - 1)) :
      actualSource k v ⟨b + i.val, by dsimp [k]; omega⟩ =
        (r + 1 : ℤ) * 2 ^ i.val := by
    have hi : i.val ≤ a - 2 := by omega
    have hpowi : (2 : ℤ) ^ i.val ≤ (2 : ℤ) ^ (a - 2) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have hhalf : (r + 1 : ℤ) * 2 ^ i.val ≤ C := by
      rw [hC, hN]
      nlinarith [hpowi, hq2r, hr4]
    apply old_centered _ _ ⟨by positivity, hhalf⟩
    rw [Int.emod_eq_of_lt (by positivity)]
    · rw [show (2 : ℤ) ^ (b + i.val) * (v : ℕ) =
          ((q : ℤ) * r - 1) * 2 ^ i.val + (r + 1) * 2 ^ i.val by
          rw [← hqr]; simp only [Nat.cast_add, Nat.cast_one, Nat.cast_pow]; ring]
      rw [Int.add_emod_self_left]
    · rw [← hqr]
      nlinarith [hpowi, hq2r]
  have hAlphaval : actualSource k v alpha = -C + r / 2 := by
    apply old_centered alpha _
      (by rw [hC]; constructor <;> nlinarith [hr4])
    rw [show (2 : ℤ) ^ (b - 1) * (v : ℕ) =
      N + (r - N + 1) / 2 by rw [hN, ← hqr]; simp only [Nat.cast_add, Nat.cast_one,
      Nat.cast_pow]; ring]
    rw [Int.add_emod_self_left]
    have hr2 : (r : ℤ) % 2 = 0 := by dsimp [r]; omega
    rw [show (-C + r / 2) = (r - N + 1) / 2 by rw [hC]; ring]
    omega
  have hBetaval : actualSource k v beta = -C + q / 2 := by
    apply old_centered beta _
      (by rw [hC]; constructor <;> nlinarith [hq2r, hr4])
    have hq2 : (q : ℤ) % 2 = 0 := by dsimp [q]; omega
    rw [show (2 : ℤ) ^ (k - 1) * (v : ℕ) =
      (q + 2) / 2 * N + (-C + q / 2) by
      rw [hN, hC, ← hqr]; simp only [Nat.cast_add, Nat.cast_one, Nat.cast_pow]; ring]
    rw [Int.add_mul_emod_self_left]
  have hUnew (i : Fin (b - 1)) :
      actualSource (k + 1) (2 * v) (⟨i.val, by dsimp [k]; omega⟩ : Fin (k + 1)) =
        2 * ((q + 1 : ℤ) * 2 ^ i.val) := by
    apply new_centered _ _
      (by rw [hMhalf]; constructor <;> nlinarith [hUval i])
    rw [show (2 : ℤ) ^ i.val * (2 * (v : ℕ)) =
      2 * ((q + 1 : ℤ) * 2 ^ i.val) by norm_num [v]; ring]
  have hVnew (i : Fin (a - 1)) :
      actualSource (k + 1) (2 * v) (⟨b + i.val, by dsimp [k]; omega⟩ : Fin (k + 1)) =
        A * 2 ^ i.val := by
    apply new_centered _ _
      (by rw [hMhalf]; constructor <;> nlinarith [hq2r, hr4, hpowi])
    rw [show (2 : ℤ) ^ (b + i.val) * (2 * (v : ℕ)) =
      A * 2 ^ i.val + modulus (k + 1) * 2 ^ i.val by
      rw [hM, ← hqr]; simp only [Nat.cast_add, Nat.cast_one, Nat.cast_pow]; ring]
    rw [Int.add_mul_emod_self_right]
  have hAlphanew : actualSource (k + 1) (2 * v)
      (⟨b - 1, by dsimp [k]; omega⟩ : Fin (k + 1)) = -N + r := by
    apply new_centered _ _ ⟨by rw [hN]; nlinarith [hq2r], by rw [hN]; nlinarith [hq2r, hr4]⟩
    rw [show (2 : ℤ) ^ (b - 1) * (2 * (v : ℕ)) =
      (-N + r) + modulus (k + 1) by rw [hM, ← hqr]; simp only [Nat.cast_add,
      Nat.cast_one, Nat.cast_pow]; ring]
    rw [Int.add_emod_self_right]
  have hBetanew : actualSource (k + 1) (2 * v)
      (⟨k - 1, by dsimp [k]; omega⟩ : Fin (k + 1)) = -N + q / 2 := by
    apply new_centered _ _ ⟨by rw [hN]; nlinarith [hq2r], by rw [hN]; nlinarith [hq2r]⟩
    rw [show (2 : ℤ) ^ (k - 1) * (2 * (v : ℕ)) =
      (q / 2 + 1) * modulus (k + 1) + (-N + q / 2) by
      rw [hM, hN, ← hqr]; simp only [Nat.cast_add, Nat.cast_one, Nat.cast_pow]; ring]
    rw [Int.add_mul_emod_self_left]
  have hFresh : actualSource (k + 1) (2 * v) fresh = v := by
    apply new_centered _ _ ⟨by positivity, by rw [hN]; nlinarith [hq2r]⟩
    rw [show (2 : ℤ) ^ k * (2 * (v : ℕ)) =
      (v : ℤ) + modulus (k + 1) * (v : ℕ) by rw [hM, ← hqr]; simp only [Nat.cast_add,
      Nat.cast_one, Nat.cast_pow]; ring]
    rw [Int.add_mul_emod_self_right]
  sorry

end D5.S3.Combinatorics.Circle.TwoNegativeJointLift
