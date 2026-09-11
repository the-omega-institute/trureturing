/- GID: D5/S1/Recurrence/Residue/ExponentialSquareWeightTernarySupport
   generality: I
   mirror-B: D5/B/S1/Recurrence/Residue/ExponentialSquareWeightTernarySupport
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Ternary decimation classifies both remaining A397242 coefficient residues. -/

import D5.S1.Recurrence.Residue.ExponentialSquareWeightCatalanParity

open PowerSeries Finset
open scoped Classical
open D5.S1.Recurrence.Residue.ExponentialSquareWeightCatalanParity
namespace D5.S1.Recurrence.Residue.ExponentialSquareWeightTernarySupport

private theorem d_zero : d 0 = 0 := by rw [d]; norm_num
private theorem d_one : d 1 = 1 := by rw [d]; norm_num
private theorem d_two : d 2 = 1 := by rw [d_recurrence 2 (by omega)]; simp [d_one]

private theorem reduced_recurrence (n : ℕ) (hn : 2 ≤ n) :
    (d n : ZMod 3) = (n - 1 : ℕ) * (d (n - 1) : ZMod 3) +
      ∑ j ∈ range n, ((j : ZMod 3) ^ 2 - 1) * (n - j : ℕ) *
        (d j : ZMod 3) * (d (n - j) : ZMod 3) := by
  have hs : (∑ j ∈ range n,
      ((j : ℤ) ^ 2 - 1) * (n - j : ℕ) * d j * d (n - j)) =
      ∑ j ∈ Ico 2 n, ((j : ℤ) ^ 2 - 1) * (n - j : ℕ) * d j * d (n - j) := by
    rw [← sum_range_add_sum_Ico _ hn]
    simp [sum_range_succ, d_zero]
  have he := congrArg (Int.castRingHom (ZMod 3)) (d_recurrence n hn)
  rw [← hs] at he
  simpa using he

private theorem ternary (x : ZMod 3) : x = 0 ∨ x = 1 ∨ x = 2 := by
  have hv : x.val = 0 ∨ x.val = 1 ∨ x.val = 2 := by have := ZMod.val_lt x; omega
  rcases hv with hv | hv | hv <;> have he := ZMod.natCast_zmod_val x
  · left; simpa only [hv, Nat.cast_zero] using he.symm
  · right; left; simpa only [hv, Nat.cast_one] using he.symm
  · right; right; simpa only [hv, Nat.cast_ofNat] using he.symm

private theorem triple (m : ℕ) (hm : 1 ≤ m) :
    (d (3 * m) : ZMod 3) = -(d (3 * m - 1) : ZMod 3) := by
  rw [reduced_recurrence (3 * m) (by omega)]
  have hp : ((3 * m - 1 : ℕ) : ZMod 3) = -1 := by
    rw [Nat.cast_sub (by omega)]
    simp [show (3 : ZMod 3) = 0 from rfl]
  rw [hp, neg_one_mul]
  have hs : (∑ j ∈ range (3 * m), ((j : ZMod 3) ^ 2 - 1) *
      (3 * m - j : ℕ) * (d j : ZMod 3) * (d (3 * m - j) : ZMod 3)) = 0 := by
    apply sum_eq_zero
    intro j hj
    rw [Nat.cast_sub (by have := mem_range.mp hj; omega)]
    simp only [Nat.cast_mul, Nat.cast_ofNat, show (3 : ZMod 3) = 0 from rfl, zero_mul, zero_sub]
    rcases ternary (j : ZMod 3) with h | h | h <;>
      simp [h, show (2 : ZMod 3) ^ 2 - 1 = 0 from rfl]
  rw [hs, add_zero]

private theorem sum_triples {R : Type*} [AddCommMonoid R] (f : ℕ → R) (m : ℕ) :
    ∑ j ∈ range (3 * m), f j =
      ∑ r ∈ range m, (f (3 * r) + f (3 * r + 1) + f (3 * r + 2)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 3 * (m + 1) = (3 * m + 2) + 1 by omega,
      sum_range_succ, sum_range_succ, sum_range_succ, ih, sum_range_succ]
    abel

private theorem section_recurrence (m r : ℕ) (hr : r = 1 ∨ r = 2)
    (hn : 2 ≤ 3 * m + r) :
    (d (3 * m + r) : ZMod 3) =
      (r - 1 : ℕ) * (d (3 * m + r - 1) : ZMod 3) +
      (r : ZMod 3) * ∑ j ∈ range m,
        (d (3 * j + 2) : ZMod 3) * (d (3 * (m - 1 - j) + r) : ZMod 3) := by
  rw [reduced_recurrence _ hn]
  have hr1 : 1 ≤ r := by omega
  have hr2 : r ≤ 2 := by omega
  have hp : ((3 * m + r - 1 : ℕ) : ZMod 3) = (r - 1 : ℕ) := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub hr1]
    simp [show (3 : ZMod 3) = 0 from rfl]
  rw [hp]
  congr 1
  let f : ℕ → ZMod 3 := fun j => ((j : ZMod 3) ^ 2 - 1) *
    (3 * m + r - j : ℕ) * (d j : ZMod 3) * (d (3 * m + r - j) : ZMod 3)
  change ∑ j ∈ range (3 * m + r), f j = _
  have h1 (j : ℕ) : f (3 * j + 1) = 0 := by
    simp [f, show (3 : ZMod 3) = 0 from rfl]
  have h2 (j : ℕ) : f (3 * j + 2) = 0 := by
    simp [f, show (3 : ZMod 3) = 0 from rfl, show (2 : ZMod 3) ^ 2 - 1 = 0 from rfl]
  have hext : (∑ j ∈ range (3 * m + r), f j) =
      ∑ j ∈ range (3 * (m + 1)), f j := by
    rcases hr with rfl | rfl
    · conv_rhs => rw [show 3 * (m + 1) = (3 * m + 1 + 1) + 1 by omega,
        sum_range_succ, sum_range_succ, h1, h2, add_zero, add_zero]
    · conv_rhs => rw [show 3 * (m + 1) = (3 * m + 2) + 1 by omega,
        sum_range_succ, h2, add_zero]
  rw [hext, sum_triples, sum_range_succ']
  have hstart : f 0 + f 1 + f 2 = 0 := by
    rw [show 1 = 3 * 0 + 1 from rfl, h1, show 2 = 3 * 0 + 2 from rfl, h2]
    simp [f, d_zero]
  rw [hstart, add_zero, mul_sum]
  apply sum_congr rfl
  intro j hj
  have hjm := mem_range.mp hj
  rw [h1, h2, add_zero, add_zero]
  dsimp [f]
  rw [Nat.cast_sub (by omega)]
  simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat,
    show (3 : ZMod 3) = 0 from rfl, zero_mul, zero_add, zero_pow (by decide : 2 ≠ 0),
    zero_sub, sub_zero]
  rw [triple (j + 1) (by omega),
    show 3 * (j + 1) - 1 = 3 * j + 2 by omega,
    show 3 * m + r - 3 * (j + 1) = 3 * (m - 1 - j) + r by omega]
  ring

private noncomputable def U : PowerSeries (ZMod 3) := mk fun m => (d (3 * m + 1) : ZMod 3)
private noncomputable def V : PowerSeries (ZMod 3) := mk fun m => (d (3 * m + 2) : ZMod 3)

private theorem U_equation : U = 1 + X * (V * U) := by
  ext n
  cases n with
  | zero => simp [U, d_one]
  | succ n =>
    rw [map_add, coeff_one, if_neg (by omega), zero_add, coeff_succ_X_mul,
      coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => coeff i V * coeff j U) n]
    simp only [U, V, coeff_mk]
    rw [section_recurrence (n + 1) 1 (Or.inl rfl) (by omega)]
    simp

private theorem V_equation : V = U - X * V ^ 2 := by
  ext n
  cases n with
  | zero => simp [U, V, d_one, d_two]
  | succ n =>
    rw [map_sub, coeff_succ_X_mul, pow_two, coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => coeff i V * coeff j V) n]
    simp only [U, V, coeff_mk]
    rw [section_recurrence (n + 1) 2 (Or.inr rfl) (by omega)]
    simp only [Nat.add_sub_cancel, Nat.reduceSub, Nat.cast_one, one_mul,
      Nat.cast_ofNat]
    rw [show 3 * (n + 1) + 2 - 1 = 3 * (n + 1) + 1 by omega]
    have h2 : (2 : ZMod 3) = -1 := rfl
    rw [h2, neg_one_mul, sub_eq_add_neg]

private theorem V_cubic : V = 1 + X ^ 2 * V ^ 3 := by
  linear_combination U_equation + (1 - X * V) * V_equation

private theorem U_cubic : U = 1 - X + X ^ 2 * U ^ 3 - X * V := by
  have h3 : (3 : PowerSeries (ZMod 3)) = 0 := by
    rw [← map_ofNat C 3, show (3 : ZMod 3) = 0 from rfl, map_zero]
  have hcube : U ^ 3 = V ^ 3 + X ^ 3 * V ^ 6 := by
    have he : U = V + X * V ^ 2 := by linear_combination -V_equation
    rw [he]
    linear_combination (V * (X * V ^ 2) * (V + X * V ^ 2)) * h3
  rw [hcube]
  linear_combination (1 + X * (V - 1 + X ^ 2 * V ^ 3)) * V_cubic - V_equation + X * V * h3


private theorem cube_subst (f : PowerSeries (ZMod 3)) : f ^ 3 = f.subst (X ^ 3) := by
  have h := MvPowerSeries.map_frobenius_expand (σ := Unit) (R := ZMod 3)
    3 (by decide) (f := f)
  rw [ZMod.frobenius_zmod, MvPowerSeries.map_id] at h
  exact h.symm.trans (PowerSeries.expand_apply 3 (by decide) f)

private theorem cube_coeff (f : PowerSeries (ZMod 3)) (n : ℕ) :
    coeff n (f ^ 3) = if 3 ∣ n then coeff (n / 3) f else 0 := by
  rw [cube_subst, coeff_subst_X_pow (by decide : 3 ≠ 0)]
  rfl

private theorem cube_coeff_mul (f : PowerSeries (ZMod 3)) (n : ℕ) :
    coeff (3 * n) (f ^ 3) = coeff n f := by simp [cube_coeff]

private theorem cube_coeff_one (f : PowerSeries (ZMod 3)) (n : ℕ) :
    coeff (3 * n + 1) (f ^ 3) = 0 := by
  simp [cube_coeff, show ¬ 3 ∣ 3 * n + 1 by omega]

private theorem cube_coeff_two (f : PowerSeries (ZMod 3)) (n : ℕ) :
    coeff (3 * n + 2) (f ^ 3) = 0 := by
  simp [cube_coeff, show ¬ 3 ∣ 3 * n + 2 by omega]

private noncomputable def B : PowerSeries (ZMod 3) := mk fun n => (a n : ZMod 3)
private noncomputable def T : PowerSeries (ZMod 3) := X * V
private noncomputable def F : PowerSeries (ZMod 3) := X * U

private theorem B_sections : B = 1 + X * U ^ 3 - X ^ 2 * V ^ 3 := by
  ext n
  cases n with
  | zero => simp [B, a]
  | succ n =>
    rw [map_sub, map_add, coeff_one, if_neg (by omega), zero_add, coeff_succ_X_mul]
    rw [show X ^ 2 * V ^ 3 = X * (X * V ^ 3) by ring, coeff_succ_X_mul]
    simp only [B, coeff_mk, a_eq (n + 1) (by omega), Int.cast_mul, Int.cast_natCast]
    rcases show n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 by omega with h | h | h
    · obtain ⟨m, hm⟩ : ∃ m, n = 3 * m := ⟨n / 3, by omega⟩
      subst n
      rw [cube_coeff_mul]
      have hz : coeff (3 * m) (X * V ^ 3) = 0 := by
        cases m with
        | zero => simp
        | succ m =>
          rw [show 3 * (m + 1) = (3 * m + 2) + 1 by omega, coeff_succ_X_mul,
            cube_coeff_two]
      simp [hz, U, show (3 : ZMod 3) = 0 from rfl]
    · obtain ⟨m, hm⟩ : ∃ m, n = 3 * m + 1 := ⟨n / 3, by omega⟩
      subst n
      rw [cube_coeff_one, coeff_succ_X_mul, cube_coeff_mul]
      simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one,
        show (3 : ZMod 3) = 0 from rfl, zero_mul, zero_add, V, coeff_mk, zero_sub]
      change (1 + 1 : ZMod 3) * (d (3 * m + 2) : ZMod 3) = -(d (3 * m + 2) : ZMod 3)
      rw [show (1 + 1 : ZMod 3) = -1 from rfl, neg_one_mul]
    · obtain ⟨m, hm⟩ : ∃ m, n = 3 * m + 2 := ⟨n / 3, by omega⟩
      subst n
      rw [cube_coeff_two, show 3 * m + 2 = (3 * m + 1) + 1 by omega,
        coeff_succ_X_mul, cube_coeff_one]
      rw [show 3 * m + 1 + 1 + 1 = 3 * (m + 1) by omega]
      simp [show (3 : ZMod 3) = 0 from rfl]

private theorem F_bridge : F = X + X ^ 2 * B := by
  have h3 : (3 : PowerSeries (ZMod 3)) = 0 := by
    rw [← map_ofNat C 3, show (3 : ZMod 3) = 0 from rfl, map_zero]
  dsimp [F]
  linear_combination X * U_cubic - X ^ 2 * V_cubic - X ^ 2 * B_sections - X ^ 2 * h3

private theorem T_equation : T = X + T ^ 3 := by
  dsimp [T]
  linear_combination X * V_cubic

private theorem F_equation : F = T + T ^ 2 := by
  dsimp [F, T]
  linear_combination -X * V_equation

private theorem F_cubic : F = X + X ^ 2 + F ^ 3 - X * T ^ 3 := by
  have h3 : (3 : PowerSeries (ZMod 3)) = 0 := by
    rw [← map_ofNat C 3, show (3 : ZMod 3) = 0 from rfl, map_zero]
  have hc : F ^ 3 = T ^ 3 + T ^ 6 := by
    rw [F_equation, cube_subst, subst_add (.of_constantCoeff_zero
        (show constantCoeff ((X : PowerSeries (ZMod 3)) ^ 3) = 0 by simp)),
      ← cube_subst, subst_pow (.of_constantCoeff_zero
        (show constantCoeff ((X : PowerSeries (ZMod 3)) ^ 3) = 0 by simp)), ← cube_subst]
    ring
  rw [hc, F_equation]
  linear_combination (1 + T + X + T ^ 3) * T_equation + X * T ^ 3 * h3

private def P (n : ℕ) : Prop := ∃ k : ℕ, n = 3 ^ k
private def Q (n : ℕ) : Prop := ∃ k : ℕ, n = 2 * 3 ^ k
private def S (n : ℕ) : Prop := ∃ i j : ℕ, i < j ∧ n = 3 ^ i + 3 ^ j

private theorem P_zero : ¬ P 0 := by
  rintro ⟨k, hk⟩
  have : 0 < 3 ^ k := pow_pos (by omega) _
  omega

private theorem Q_zero : ¬ Q 0 := by
  rintro ⟨k, hk⟩
  have : 0 < 3 ^ k := pow_pos (by omega) _
  omega

private theorem S_zero : ¬ S 0 := by
  rintro ⟨i, j, hij, hn⟩
  have hi : 0 < (3 : ℕ) ^ i := pow_pos (by omega) _
  have hj : 0 < (3 : ℕ) ^ j := pow_pos (by omega) _
  omega

private theorem P_three (m : ℕ) : P (3 * m) ↔ P m := by
  constructor
  · rintro ⟨k, hk⟩
    cases k with
    | zero => simp only [pow_zero] at hk; omega
    | succ k => exact ⟨k, by rw [pow_succ] at hk; omega⟩
  · rintro ⟨k, hk⟩
    exact ⟨k + 1, by rw [pow_succ]; omega⟩

private theorem Q_three (m : ℕ) : Q (3 * m) ↔ Q m := by
  constructor
  · rintro ⟨k, hk⟩
    cases k with
    | zero => simp only [pow_zero, mul_one] at hk; omega
    | succ k => exact ⟨k, by rw [pow_succ] at hk; omega⟩
  · rintro ⟨k, hk⟩
    exact ⟨k + 1, by rw [pow_succ]; omega⟩

private theorem P_three_one (m : ℕ) : P (3 * m + 1) ↔ m = 0 := by
  constructor
  · rintro ⟨k, hk⟩
    cases k with
    | zero => simp only [pow_zero] at hk; omega
    | succ k => rw [pow_succ] at hk; omega
  · rintro rfl; exact ⟨0, rfl⟩

private theorem P_three_two (m : ℕ) : ¬ P (3 * m + 2) := by
  rintro ⟨k, hk⟩
  cases k with
  | zero => simp only [pow_zero] at hk; omega
  | succ k => rw [pow_succ] at hk; omega

private theorem Q_three_one (m : ℕ) : ¬ Q (3 * m + 1) := by
  rintro ⟨k, hk⟩
  cases k with
  | zero => simp only [pow_zero, mul_one] at hk; omega
  | succ k => rw [pow_succ] at hk; omega

private theorem Q_three_two (m : ℕ) : Q (3 * m + 2) ↔ m = 0 := by
  constructor
  · rintro ⟨k, hk⟩
    cases k with
    | zero => simp only [pow_zero, mul_one] at hk; omega
    | succ k => rw [pow_succ] at hk; omega
  · rintro rfl; exact ⟨0, rfl⟩

private theorem S_three (m : ℕ) : S (3 * m) ↔ S m := by
  constructor
  · rintro ⟨i, j, hij, hn⟩
    cases j with
    | zero => omega
    | succ j =>
      cases i with
      | zero => rw [pow_zero, pow_succ] at hn; omega
      | succ i =>
        refine ⟨i, j, by omega, ?_⟩
        rw [pow_succ, pow_succ] at hn
        omega
  · rintro ⟨i, j, hij, hn⟩
    refine ⟨i + 1, j + 1, by omega, ?_⟩
    rw [pow_succ, pow_succ, hn]
    omega

private theorem S_three_one (m : ℕ) : S (3 * m + 1) ↔ P m := by
  constructor
  · rintro ⟨i, j, hij, hn⟩
    cases j with
    | zero => omega
    | succ j =>
      cases i with
      | zero => exact ⟨j, by rw [pow_zero, pow_succ] at hn; omega⟩
      | succ i => rw [pow_succ, pow_succ] at hn; omega
  · rintro ⟨k, hk⟩
    exact ⟨0, k + 1, by omega, by rw [pow_zero, pow_succ, hk]; omega⟩

private theorem S_three_two (m : ℕ) : ¬ S (3 * m + 2) := by
  rintro ⟨i, j, hij, hn⟩
  cases j with
  | zero => omega
  | succ j =>
    cases i with
    | zero => rw [pow_zero, pow_succ] at hn; omega
    | succ i => rw [pow_succ, pow_succ] at hn; omega

private theorem T_coeff (n : ℕ) : coeff n T = if P n then 1 else 0 := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn0 : n = 0
    · subst n; simp [T, P_zero]
    have he := congrArg (coeff n) T_equation
    rw [map_add, coeff_X, cube_coeff] at he
    rcases show n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 by omega with h | h | h
    · have hn : n = 3 * (n / 3) := by omega
      have hd : 3 ∣ n := by omega
      rw [if_neg (by omega : n ≠ 1), if_pos hd, zero_add, ih (n / 3) (by omega)] at he
      rw [he, hn, P_three]
      simp
    · have hn : n = 3 * (n / 3) + 1 := by omega
      rw [if_neg (by omega : ¬ 3 ∣ n), add_zero] at he
      rw [he, hn, P_three_one]
      simp only [show (3 * (n / 3) + 1 = 1) ↔ n / 3 = 0 by omega]
      split_ifs <;> rfl
    · have hn : n = 3 * (n / 3) + 2 := by omega
      rw [if_neg (by omega : n ≠ 1), if_neg (by omega : ¬ 3 ∣ n), zero_add] at he
      rw [he, hn, if_neg (P_three_two _)]

private theorem F_three (m : ℕ) : coeff (3 * m) F = coeff m F := by
  cases m with
  | zero => rfl
  | succ m =>
    have he := congrArg (coeff (3 * (m + 1))) F_cubic
    rw [map_sub, map_add, map_add, coeff_X, if_neg (by omega), coeff_X_pow,
      if_neg (by omega), zero_add, zero_add, cube_coeff_mul,
      show 3 * (m + 1) = (3 * m + 2) + 1 by omega, coeff_succ_X_mul,
      cube_coeff_two, sub_zero] at he
    exact he

private theorem F_three_one (m : ℕ) :
    coeff (3 * m + 1) F = (if m = 0 then 1 else 0) - coeff m T := by
  have he := congrArg (coeff (3 * m + 1)) F_cubic
  rw [map_sub, map_add, map_add, coeff_X, coeff_X_pow, if_neg (show 3 * m + 1 ≠ 2 by omega),
    add_zero, cube_coeff_one, add_zero, coeff_succ_X_mul, cube_coeff_mul] at he
  simpa only [show (3 * m + 1 = 1) ↔ m = 0 by omega] using he

private theorem F_three_two (m : ℕ) :
    coeff (3 * m + 2) F = if m = 0 then 1 else 0 := by
  have he := congrArg (coeff (3 * m + 2)) F_cubic
  rw [map_sub, map_add, map_add, coeff_X, if_neg (by omega), zero_add, coeff_X_pow,
    cube_coeff_two, add_zero, show 3 * m + 2 = (3 * m + 1) + 1 by omega,
    coeff_succ_X_mul, cube_coeff_one, sub_zero] at he
  simpa only [show (3 * m + 1 + 1 = 2) ↔ m = 0 by omega] using he

private theorem F_support (n : ℕ) :
    coeff n F = if P n ∨ Q n then 1 else if S n then 2 else 0 := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn0 : n = 0
    · subst n; simp [F, P_zero, Q_zero, S_zero]
    rcases show n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 by omega with h | h | h
    · have hn : n = 3 * (n / 3) := by omega
      rw [hn, F_three, ih (n / 3) (by omega), P_three, Q_three, S_three]
    · have hn : n = 3 * (n / 3) + 1 := by omega
      rw [hn, F_three_one, T_coeff]
      simp only [P_three_one, Q_three_one, or_false, S_three_one]
      by_cases hm : n / 3 = 0
      · simp [hm, P_zero]
      · simp only [hm, if_false, zero_sub]
        split_ifs <;> rfl
    · have hn : n = 3 * (n / 3) + 2 := by omega
      rw [hn, F_three_two]
      simp only [P_three_two, Q_three_two, false_or, if_neg (S_three_two _)]


private theorem supports_disjoint (n : ℕ) : S n → ¬ (P n ∨ Q n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn0 : n = 0
    · subst n; exact fun h => (S_zero h).elim
    rcases show n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 by omega with h | h | h
    · have hn : n = 3 * (n / 3) := by omega
      intro hs hp
      rw [hn, S_three] at hs
      rw [hn, P_three, Q_three] at hp
      exact ih (n / 3) (by omega) hs hp
    · have hn : n = 3 * (n / 3) + 1 := by omega
      rw [hn]
      simp only [S_three_one, P_three_one, Q_three_one, or_false]
      intro hp hz
      rw [hz] at hp
      exact P_zero hp
    · have hn : n = 3 * (n / 3) + 2 := by omega
      rw [hn]
      exact fun hs => (S_three_two _ hs).elim

private theorem a_support (n : ℕ) :
    (a n : ZMod 3) = if P (n + 2) ∨ Q (n + 2) then 1 else if S (n + 2) then 2 else 0 := by
  have hb := congrArg (coeff (n + 2)) F_bridge
  rw [map_add, coeff_X, if_neg (by omega), zero_add, coeff_X_pow_mul, B, coeff_mk] at hb
  rw [← hb]
  exact F_support (n + 2)

/-- The complete ternary support of the frozen coefficients of OEIS A397242. -/
theorem ternary_support_classification (n : ℕ) :
    a n % 3 =
      if (∃ k : ℕ, n + 2 = 3 ^ k) ∨ (∃ k : ℕ, n + 2 = 2 * 3 ^ k) then 1
      else if (∃ i j : ℕ, i < j ∧ n + 2 = 3 ^ i + 3 ^ j) then 2 else 0 := by
  have he := a_support n
  change a n % 3 = if P (n + 2) ∨ Q (n + 2) then 1 else if S (n + 2) then 2 else 0
  split_ifs at he ⊢ with h h'
  · exact (ZMod.intCast_eq_intCast_iff' (a n) 1 3).mp he
  · exact (ZMod.intCast_eq_intCast_iff' (a n) 2 3).mp he
  · exact (ZMod.intCast_eq_intCast_iff' (a n) 0 3).mp he

/-- Hanna's residue-one conjecture in OEIS A397242. -/
theorem hanna_conjecture_one (n : ℕ) (_hn : 0 < n) :
    a n % 3 = 1 ↔
      (∃ k : ℕ, n + 2 = 3 ^ k) ∨ (∃ k : ℕ, n + 2 = 2 * 3 ^ k) := by
  rw [ternary_support_classification]
  split_ifs <;> simp_all

/-- Hanna's residue-two conjecture in OEIS A397242. -/
theorem hanna_conjecture_two (n : ℕ) (_hn : 0 < n) :
    a n % 3 = 2 ↔ ∃ i j : ℕ, i < j ∧ n + 2 = 3 ^ i + 3 ^ j := by
  have hd := supports_disjoint (n + 2)
  rw [ternary_support_classification]
  change (if P (n + 2) ∨ Q (n + 2) then (1 : ℤ) else if S (n + 2) then 2 else 0) = 2 ↔ S (n + 2)
  split_ifs <;> simp_all

#print axioms ternary_support_classification
#print axioms hanna_conjecture_one
#print axioms hanna_conjecture_two

end D5.S1.Recurrence.Residue.ExponentialSquareWeightTernarySupport
