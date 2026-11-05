/- GID: D5/S3/ArithSums/OudraA248186CubicFloor
   generality: I
   mirror-B: D5/B/S3/ArithSums/OudraA248186CubicFloor
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Oudra's cubic floor formula for the least reciprocal-product threshold index. -/

/-
result:
  proof_shape: bind-only
  escape_witness: none
  admission_basis: open-problem-resolution (#24012; Proved)
  Direct frozen dependencies: none (only pinned Mathlib).

All auxiliary theorems are private, bind-only and used by the consumers below.
residual_formula -> admissible_iff (finite telescoping and field normalization).
r_pos -> r_sq_over, q_overshoot, candidate_data (Real.rpow_pos_of_pos).
r_sq_over -> q_overshoot (field normalization).
q_shift -> q_overshoot (field normalization).
q_overshoot -> candidate_data (power identities and field normalization).
q_strictMono -> candidate_data, candidate_isleast, formula_of_source (ordered-ring normalization).
q_cast_int -> candidate_data (cast normalization).
admissible_iff -> candidate_isleast, formula_of_source (telescoping and normalization).
candidate_data -> candidate_isleast, formula_of_source (floor bounds and integer-gap normalization).
candidate_isleast -> exists_source (least-element construction from those bounds).
exists_source -> result (choice).
formula_of_source -> result (minimality and floor translation).
Each auxiliary theorem has escape_witness none and Direct frozen dependencies none.
The source expressions for residual, r, IsSourceSequence and claim are unchanged.
Cube-root normalization uses Real.rpow_mul_natCast directly inside its consumers.
The argument is symbolic for unbounded indices, not finite enumeration or a checker.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/24748.
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.ArithSums.OudraA248186CubicFloor

noncomputable def residual (k : ℕ) : ℝ :=
  1 / 18 - ∑ h ∈ Finset.Icc 1 k,
    1 / ((h : ℝ) * ((h : ℝ) + 1) * ((h : ℝ) + 2) * ((h : ℝ) + 3))
private theorem residual_formula (k : ℕ) :
    residual k = 1 / (3 * ((k:ℝ)+1) * ((k:ℝ)+2) * ((k:ℝ)+3)) := by
  unfold residual
  let f : ℕ → ℝ := fun h => -(1 / (3 * (h:ℝ) * ((h:ℝ)+1) * ((h:ℝ)+2)))
  have heq : ∀ h ∈ Finset.Icc 1 k,
      1 / ((h : ℝ) * ((h : ℝ) + 1) * ((h : ℝ) + 2) * ((h : ℝ) + 3)) = f (h+1) - f h := by
    intro h hh
    have hh0 : (0:ℝ) < h := by exact_mod_cast (Finset.mem_Icc.mp hh).1
    dsimp [f]
    push_cast
    field_simp
    ring
  rw [Finset.sum_congr rfl heq]
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_sub f (by omega : 1 ≤ k+1)]
  dsimp [f]
  push_cast
  norm_num [add_assoc]

noncomputable def r : ℝ := (3 : ℝ) ^ (-(1 : ℝ) / 3)
private theorem r_pos : 0 < r := by
  dsimp [r]
  positivity
private theorem r_sq_over (n : ℕ) (hn : (0:ℝ) < n) : r ^ 2 / (n:ℝ) = 1 / (3 * (r * n)) := by
  have hr : r ≠ 0 := ne_of_gt r_pos
  have hn0 : (n:ℝ) ≠ 0 := ne_of_gt hn
  field_simp
  ring_nf
  dsimp [r]
  rw [← Real.rpow_mul_natCast (by norm_num : (0:ℝ) ≤ 3)]
  norm_num [Real.rpow_neg_one]

private def q (x : ℝ) : ℝ := 3 * (x ^ 3 - x)
private theorem q_shift (x : ℝ) (hx : x ≠ 0) :
    q (x + 1 / (3*x)) = 3*x^3 + 1/(9*x^3) := by
  dsimp [q]
  field_simp
  ring

private theorem q_overshoot (n : ℕ) (hn : 2 < n) :
    q (r * (n:ℝ) + r^2 / (n:ℝ)) = (n:ℝ)^3 + 1 / (3 * (n:ℝ)^3) := by
  have hn0 : (0:ℝ) < (n:ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hr : 0 < r := r_pos
  have hx : 0 < r * (n:ℝ) := mul_pos hr hn0
  have hs : r^2 / (n:ℝ) = 1 / (3 * (r * (n:ℝ))) := r_sq_over n hn0
  rw [hs, q_shift _ (ne_of_gt hx)]
  have hxn : (r * (n:ℝ))^3 = (n:ℝ)^3 / 3 := by
    rw [mul_pow]
    dsimp [r]
    rw [← Real.rpow_mul_natCast (by norm_num : (0:ℝ) ≤ 3)]
    norm_num [Real.rpow_neg_one]
    ring
  have hxn0 : (r * (n:ℝ))^3 ≠ 0 := ne_of_gt (pow_pos hx 3)
  rw [hxn]
  field_simp [ne_of_gt hn0]
  ring
private theorem q_strictMono {y z : ℝ} (hz : 1 ≤ z) (hzy : z < y) : q z < q y := by
  have hy : 0 < y := lt_of_lt_of_le (lt_of_lt_of_le ?_ hz) ?_
  · have hfac : q y - q z = 3 * (y-z) * (y^2 + y*z + z^2 - 1) := by
      dsimp [q]
      ring
    have hpos : 0 < y^2 + y*z + z^2 - 1 := by
      have hy0 : 0 < y := lt_of_lt_of_le (by linarith : 0 < z) hzy.le
      have hz0 : 0 < z := lt_of_lt_of_le (by norm_num) hz
      have hm : 0 < y*z := mul_pos hy0 hz0
      nlinarith [sq_nonneg y, sq_nonneg z]
    have hd : 0 < q y - q z := by rw [hfac]; positivity
    linarith
  · linarith
  · linarith

private theorem q_cast_int (z : ℤ) :
    (((3 : ℤ) * (z^3 - z) : ℤ) : ℝ) = q (z : ℝ) := by
  dsimp [q]
  norm_num


private theorem admissible_iff (n k : ℕ) (hn : 0 < n) :
    residual k < 1 / (n:ℝ)^3 ↔ (n:ℝ)^3 < q ((k:ℝ)+2) := by
  rw [residual_formula]
  have hn3 : 0 < (n:ℝ)^3 := by positivity
  have hp : 0 < 3 * ((k:ℝ)+1) * ((k:ℝ)+2) * ((k:ℝ)+3) := by positivity
  rw [div_lt_div_iff₀ hp hn3]
  norm_num
  dsimp [q]
  ring_nf

private theorem candidate_data (n : ℕ) (hn : 2 < n) :
    ∃ m : ℤ, (m : ℝ) = ⌊r * (n:ℝ) + r^2/(n:ℝ)⌋ ∧
      (2:ℤ) ≤ m ∧
      q ((m:ℝ)) ≤ (n:ℝ)^3 ∧
      (n:ℝ)^3 < q ((m:ℝ)+1) := by
  let b : ℝ := r * (n:ℝ) + r^2/(n:ℝ)
  let m : ℤ := ⌊b⌋
  have hn0 : (0:ℝ) < (n:ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hr : 0 < r := r_pos
  have hx : 0 < r * (n:ℝ) := mul_pos hr hn0
  have hxn : (r * (n:ℝ))^3 = (n:ℝ)^3 / 3 := by
    rw [mul_pow]
    dsimp [r]
    rw [← Real.rpow_mul_natCast (by norm_num : (0:ℝ) ≤ 3)]
    norm_num [Real.rpow_neg_one]
    ring
  have hnreal : (3:ℝ) ≤ (n:ℝ) := by exact_mod_cast (show 3 ≤ n by omega)
  have hn3 : (3:ℝ)^3 ≤ (n:ℝ)^3 := pow_le_pow_left₀ (by norm_num) hnreal 3
  have hxcube : (2:ℝ)^3 < (r * (n:ℝ))^3 := by
    nlinarith [hxn, hn3]
  have hx2 : (2:ℝ) < r * (n:ℝ) := lt_of_pow_lt_pow_left₀ 3 hx.le hxcube
  have hb2 : (2:ℝ) < b := by
    dsimp [b]
    have hs : 0 < r^2/(n:ℝ) := div_pos (sq_pos_of_pos hr) hn0
    linarith
  have hq := q_overshoot n hn
  have hqlo : (n:ℝ)^3 < q b := by
    rw [hq]
    have : 0 < (3:ℝ) * (n:ℝ)^3 := by positivity
    nlinarith [one_div_pos.mpr this]
  have hqhi : q b < (n:ℝ)^3 + 1 := by
    rw [hq]
    have hden : (1:ℝ) < 3 * (n:ℝ)^3 := by nlinarith [hn3]
    have : 1 / (3 * (n:ℝ)^3) < (1:ℝ) := (div_lt_iff₀ (by positivity)).2 (by simpa using hden)
    linarith
  have hm2 : (2:ℤ) ≤ m := by
    dsimp [m]
    apply (Int.le_floor).2
    exact_mod_cast hb2.le
  have hmb : (m:ℝ) ≤ b := by dsimp [m]; exact Int.floor_le b
  have hqmb : q (m:ℝ) ≤ q b := by
    rcases eq_or_lt_of_le hmb with heq | hlt
    · simp [heq]
    · have hm1 : (1:ℤ) ≤ m := Int.le_of_lt hm2
      exact (q_strictMono (by exact_mod_cast hm1) hlt).le
  have hqmi : q (m:ℝ) < (n:ℝ)^3 + 1 := lt_of_le_of_lt hqmb hqhi
  have hcast : (((3:ℤ) * (m^3 - m) : ℤ) : ℝ) = q (m:ℝ) := q_cast_int m
  have hqmi' : (((3:ℤ) * (m^3 - m) : ℤ) : ℝ) < ((n:ℤ)^3 : ℝ) + 1 := by
    rw [hcast]
    norm_num
    exact hqmi
  have hqmi'' : (3:ℤ) * (m^3 - m) < (n:ℤ)^3 + 1 := by exact_mod_cast hqmi'
  have hqmle : (3:ℤ) * (m^3 - m) ≤ (n:ℤ)^3 := Int.le_of_lt_add_one hqmi''
  have hqmle' : q (m:ℝ) ≤ (n:ℝ)^3 := by
    rw [← hcast]
    exact_mod_cast hqmle
  have hbm1 : b < (m:ℝ) + 1 := by dsimp [m]; exact Int.lt_floor_add_one b
  have hqmp : (n:ℝ)^3 < q ((m:ℝ)+1) := by
    have hbm1' : b < (m:ℝ)+1 := hbm1
    have hqinc : q b < q ((m:ℝ)+1) := q_strictMono (by linarith [hb2]) hbm1'
    exact lt_trans hqlo hqinc
  exact ⟨m, rfl, hm2, hqmle', hqmp⟩
private theorem candidate_isleast (n : ℕ) (hn : 0 < n) :
    ∃ k : ℕ, IsLeast {k : ℕ | 1 ≤ k ∧ residual k < 1 / (n:ℝ)^3} k := by
  by_cases hn2 : 2 < n
  · obtain ⟨m, hmfloor, hm2, hqm, hqmp⟩ := candidate_data n hn2
    let k : ℕ := Int.toNat (m - 1)
    have hm1nonneg : 0 ≤ m - 1 := by omega
    have hkcast : (k : ℤ) = m - 1 := by
      dsimp [k]
      rw [Int.toNat_of_nonneg hm1nonneg]
    have hk2cast : ((k + 2 : ℕ) : ℤ) = m + 1 := by omega
    have hk1 : 1 ≤ k := by
      have : (1:ℤ) ≤ (k:ℤ) := by rw [hkcast]; omega
      exact_mod_cast this
    have hkadm : residual k < 1 / (n:ℝ)^3 := by
      rw [admissible_iff n k hn]
      have hqmp' : (n:ℝ)^3 < q (((k:ℝ)+2)) := by
        have hcast : ((k:ℝ)+2) = (m:ℝ)+1 := by
          exact_mod_cast hk2cast
        rw [hcast]
        exact hqmp
      exact hqmp'
    refine ⟨k, ⟨⟨hk1, hkadm⟩, ?_⟩⟩
    intro j hj
    by_contra hnot
    have hjk : j < k := Nat.lt_of_not_ge hnot
    have hj2le : j + 2 ≤ k + 1 := Nat.le_add_of_sub_le hjk
    have hj2m : ((j + 2 : ℕ) : ℤ) ≤ m := by
      have hj2le' : ((j + 2 : ℕ) : ℤ) ≤ ((k + 1 : ℕ) : ℤ) := by exact_mod_cast hj2le
      omega
    have hqjle : q (((j:ℝ)+2)) ≤ q (m:ℝ) := by
      have hcast : ((j:ℝ)+2) ≤ (m:ℝ) := by exact_mod_cast hj2m
      rcases eq_or_lt_of_le hcast with heq | hlt
      · simp [heq]
      · exact (q_strictMono (by exact_mod_cast (show (1:ℤ) ≤ (j+2:ℕ) by omega)) hlt).le
    have hjadm : (n:ℝ)^3 < q (((j:ℝ)+2)) := (admissible_iff n j hn).1 hj.2
    nlinarith [hqm, hqjle, hjadm]
  · have hn_cases : n = 1 ∨ n = 2 := by omega
    rcases hn_cases with rfl | rfl
    · refine ⟨1, ?_, ?_⟩
      · constructor
        · norm_num
        · rw [admissible_iff _ _ (by norm_num)]
          norm_num [q]
      · intro j hj
        have hj1 := hj.1
        omega
    · refine ⟨1, ?_, ?_⟩
      · constructor
        · norm_num
        · rw [admissible_iff _ _ (by norm_num)]
          norm_num [q]
      · intro j hj
        have hj1 := hj.1
        omega
def IsSourceSequence (A : ℕ → ℕ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → IsLeast {k : ℕ | 1 ≤ k ∧ residual k < 1 / (n : ℝ) ^ 3} (A n)
def claim : Prop :=
  (∃ A : ℕ → ℕ, IsSourceSequence A) ∧
    ∀ A : ℕ → ℕ, IsSourceSequence A → ∀ n : ℕ, 2 < n →
      (A n : ℤ) = ⌊r * (n : ℝ) + r ^ 2 / (n : ℝ) - 1⌋

private theorem exists_source : ∃ A : ℕ → ℕ, IsSourceSequence A := by
  classical
  let A : ℕ → ℕ := fun n => if hn : 1 ≤ n then Classical.choose (candidate_isleast n (lt_of_lt_of_le (by omega) hn)) else 0
  refine ⟨A, ?_⟩
  intro n hn
  dsimp [A]
  split <;> rename_i h
  · exact Classical.choose_spec (candidate_isleast n (lt_of_lt_of_le (by omega) h))
  · omega

private theorem formula_of_source (A : ℕ → ℕ) (hA : IsSourceSequence A)
    (n : ℕ) (hn : 2 < n) :
    (A n : ℤ) = ⌊r * (n : ℝ) + r ^ 2 / (n : ℝ) - 1⌋ := by
  obtain ⟨m, hmfloor, hm2, hqm, hqmp⟩ := candidate_data n hn
  let k : ℕ := Int.toNat (m - 1)
  have hA' := hA n (by omega)
  have hm1nonneg : 0 ≤ m - 1 := by omega
  have hkcast : (k : ℤ) = m - 1 := by
    dsimp [k]
    rw [Int.toNat_of_nonneg hm1nonneg]
  have hk2cast : ((k + 2 : ℕ) : ℤ) = m + 1 := by omega
  have hk1 : 1 ≤ k := by
    have : (1:ℤ) ≤ (k:ℤ) := by rw [hkcast]; omega
    exact_mod_cast this
  have hkadm : residual k < 1 / (n:ℝ)^3 := by
    rw [admissible_iff n k (by omega)]
    have hcast : ((k:ℝ)+2) = (m:ℝ)+1 := by exact_mod_cast hk2cast
    rw [hcast]
    exact hqmp
  have hle : A n ≤ k := hA'.2 ⟨hk1, hkadm⟩
  have hge : k ≤ A n := by
    by_contra hnot
    have hjk : A n < k := Nat.lt_of_not_ge hnot
    have hj2m : ((A n + 2 : ℕ) : ℤ) ≤ m := by
      have hj2le' : ((A n + 2 : ℕ) : ℤ) ≤ ((k + 1 : ℕ) : ℤ) := Int.ofNat_le.mpr (Nat.le_add_of_sub_le hjk)
      omega
    have hqjle : q (((A n:ℝ)+2)) ≤ q (m:ℝ) := by
      have hcast : ((A n:ℝ)+2) ≤ (m:ℝ) := by exact_mod_cast hj2m
      rcases eq_or_lt_of_le hcast with heq | hlt
      · simp [heq]
      · have hj1 : (1:ℤ) ≤ (A n + 2 : ℕ) := (Int.zero_eq_toNat_sub_iff 1 (↑(A n + 2))).mp rfl
        exact (q_strictMono (by exact_mod_cast hj1) hlt).le
    have hjadm : (n:ℝ)^3 < q (((A n:ℝ)+2)) :=
      (admissible_iff n (A n) (by omega)).1 hA'.1.2
    nlinarith [hqm, hqjle, hjadm]
  have hEq : A n = k := Nat.le_antisymm hle hge
  have hmfloor' : m = ⌊r * (n:ℝ) + r^2/(n:ℝ)⌋ := by exact_mod_cast hmfloor
  calc
    (A n : ℤ) = (k : ℤ) := by rw [hEq]
    _ = m - 1 := hkcast
    _ = ⌊r * (n:ℝ) + r^2/(n:ℝ)⌋ - 1 := by rw [hmfloor']
    _ = ⌊r * (n:ℝ) + r^2/(n:ℝ) - 1⌋ := by
      symm
      simpa using (Int.floor_sub_intCast (r * (n:ℝ) + r^2/(n:ℝ)) (1:ℤ))
theorem result : claim := by
  constructor
  · exact exists_source
  · intro A hA n hn
    exact formula_of_source A hA n hn
end D5.S3.ArithSums.OudraA248186CubicFloor
