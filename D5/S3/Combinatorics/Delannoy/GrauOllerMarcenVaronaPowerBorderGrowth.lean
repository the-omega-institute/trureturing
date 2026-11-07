/- GID: D5/S3/Combinatorics/Delannoy/GrauOllerMarcenVaronaPowerBorderGrowth
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Delannoy/GrauOllerMarcenVaronaPowerBorderGrowth
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Power-border Delannoy diagonal ratios approach exp(1) times the half-shift. -/

/-
admission_basis: open-problem-resolution (#19939; Proved)
escape_witness: none (admission is the external named problem settlement)
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/22168
Direct frozen dependencies: D5/S3/Combinatorics/Matroids/SpeyerUniformNormality.qAB,
through the factorial-border kernel; qAB declaration statement_id: sha256:29896652822aaa7119e8470a97a0a75560731fffc4cbfc489026fab990c39f29.
The recurrence and additive-limit statements use the conventions of #19938 and #19939.
The unit-border array is qAB evaluated at one.
All declarations have utility none: unbounded identities, estimates and limits.
D5.S3.Combinatorics.Delannoy.GrauOllerMarcenVaronaPowerBorderGrowth.result: proof_shape: content; escape_witness: none; Direct frozen dependencies: qAB.
-/

import D5.S3.Combinatorics.Delannoy.GrauOllerMarcenVaronaFactorialBorderGrowth

namespace D5.S3.Combinatorics.Delannoy.GrauOllerMarcenVaronaPowerBorderGrowth
open D5.S3.Combinatorics.Delannoy.GrauOllerMarcenVaronaFactorialBorderGrowth
open Finset Filter Topology
open scoped BigOperators

/-- The power-border conjecture: `f_{n+1,n+1}/f_{n,n} − e · (n + 1/2) → 0` for `b(n) = n^n` (OEIS A346385). -/
def claimPower : Prop :=
  Tendsto (fun n : ℕ => (f (fun k => k ^ k) (n + 1) (n + 1) : ℝ) / f (fun k => k ^ k) n n -
      Real.exp 1 * ((n : ℝ) + 1 / 2))
    atTop (𝓝 0)


private noncomputable def R (A : ℕ → ℝ) (n k : ℕ) : ℝ :=
  ∏ j ∈ range k, A (n-j)

@[simp] private theorem R_zero (A : ℕ → ℝ) (n : ℕ) : R A n 0 = 1 := by
  simp only [R, prod_range_zero]

private theorem R_succ (A : ℕ → ℝ) (n k : ℕ) :
    R A n (k+1) = R A n k * A (n-k) := by
  exact prod_range_succ (fun j => A (n-j)) k

private noncomputable def J (ρ c : ℝ) : ℕ → ℝ
  | 0 => 0
  | k+1 => J ρ c k * ρ + ρ^k * c

private theorem R_bounds (A : ℕ → ℝ) (hA : ∀ n, 0 ≤ A n ∧ A n ≤ 1) (n k : ℕ) :
    0 ≤ R A n k ∧ R A n k ≤ 1 := by
  unfold R
  exact ⟨prod_nonneg (fun j _ => (hA (n-j)).1),
    prod_le_one₀ (fun j _ => (hA (n-j)).1) (fun j _ => (hA (n-j)).2)⟩

private theorem shifted_scaled_limit (A : ℕ → ℝ) (ρ c : ℝ) (k : ℕ)
    (h : Tendsto (fun n : ℕ => (n:ℝ) * (A n - ρ)) atTop (𝓝 c)) :
    Tendsto (fun n : ℕ => (n:ℝ) * (A (n-k) - ρ)) atTop (𝓝 c) := by
  have ht : Tendsto (fun n : ℕ => (n:ℝ) / (n-k:ℕ)) atTop (𝓝 (1:ℝ)) := by
    apply (tendsto_natCast_div_add_atTop (-(k:ℝ))).congr'
    filter_upwards [eventually_ge_atTop k] with n hn
    rw [Nat.cast_sub hn]
    simp only [sub_eq_add_neg]
  have hu := ht.mul (h.comp (tendsto_sub_atTop_nat k))
  simp only [one_mul] at hu
  apply hu.congr'
  filter_upwards [eventually_ge_atTop (k+1)] with n hn
  have hz : ((n-k:ℕ):ℝ) ≠ 0 := by exact_mod_cast (show n-k ≠ 0 by omega)
  dsimp
  field_simp

private theorem R_scaled_limit (A : ℕ → ℝ) (ρ c : ℝ)
    (h : Tendsto (fun n : ℕ => (n:ℝ) * (A n - ρ)) atTop (𝓝 c)) (k : ℕ) :
    Tendsto (fun n : ℕ => (n:ℝ) * (R A n k - ρ^k)) atTop (𝓝 (J ρ c k)) := by
  have h0 := tendsto_of_scaled A ρ c h
  induction k
  case zero => simpa only [R_zero, J, pow_zero, sub_self, mul_zero] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℝ)) atTop (𝓝 0))
  case succ k ih =>
    have ht := (ih.mul (h0.comp (tendsto_sub_atTop_nat k))).add
      ((shifted_scaled_limit A ρ c k h).const_mul (ρ^k))
    change Tendsto _ _ (𝓝 (J ρ c k * ρ + ρ^k * c))
    convert ht using 1
    ext n
    simp only [R_succ, pow_succ, Function.comp_apply]
    ring

private theorem shifted_scaled_bound (A : ℕ → ℝ) (ρ C : ℝ)
    (hA : ∀ n, 0 ≤ A n ∧ A n ≤ 1) (hρ : 0 ≤ ρ ∧ ρ ≤ 1) (hC : 0 ≤ C)
    (h : ∀ n : ℕ, |(n:ℝ) * (A n - ρ)| ≤ C) (n k : ℕ) : |(n:ℝ) * (A (n-k) - ρ)| ≤ C + k := by
  have hd : |A (n-k) - ρ| ≤ 1 := abs_le.mpr ⟨by linarith [(hA (n-k)).1], by linarith [(hA (n-k)).2]⟩
  by_cases hkn : k ≤ n
  · calc
      _ = |((n-k:ℕ):ℝ) * (A (n-k) - ρ) + (k:ℝ) * (A (n-k) - ρ)| := by
        rw [Nat.cast_sub hkn]; congr 1; ring
      _ ≤ |((n-k:ℕ):ℝ) * (A (n-k) - ρ)| + |(k:ℝ) * (A (n-k) - ρ)| := abs_add_le _ _
      _ ≤ C + k := add_le_add (h (n-k)) (by
        rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg k)]
        exact mul_le_of_le_one_right (Nat.cast_nonneg k) hd)
  · rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg n)]
    have hnk : (n:ℝ) ≤ k := by exact_mod_cast (Nat.le_of_lt (Nat.lt_of_not_ge hkn))
    nlinarith

private theorem R_scaled_bound (A : ℕ → ℝ) (ρ C : ℝ)
    (hA : ∀ n, 0 ≤ A n ∧ A n ≤ 1) (hρ : 0 ≤ ρ ∧ ρ ≤ 1) (hC : 0 ≤ C)
    (h : ∀ n : ℕ, |(n:ℝ) * (A n - ρ)| ≤ C) (n k : ℕ) : |(n:ℝ) * (R A n k - ρ^k)| ≤ (k:ℝ) * (C+k) := by
  induction k
  case zero => simp [R]
  case succ k ih =>
    have hpow : 0 ≤ ρ^k ∧ ρ^k ≤ 1 := ⟨pow_nonneg hρ.1 _, pow_le_one₀ hρ.1 hρ.2⟩
    calc
      _ = |((n:ℝ) * (R A n k - ρ^k)) * A (n-k) +
          ρ^k * ((n:ℝ) * (A (n-k) - ρ))| := by simp only [R_succ, pow_succ]; congr 1; ring
      _ ≤ |(n:ℝ) * (R A n k - ρ^k)| * |A (n-k)| + |ρ^k| * |(n:ℝ) * (A (n-k) - ρ)| := by
        simpa only [abs_mul] using (abs_add_le
          (((n:ℝ) * (R A n k - ρ^k)) * A (n-k)) (ρ^k * ((n:ℝ) * (A (n-k) - ρ))))
      _ ≤ (k:ℝ) * (C+k) + (C+k) := by
        rw [abs_of_nonneg (hA _).1, abs_of_nonneg hpow.1]
        exact add_le_add ((mul_le_of_le_one_right (abs_nonneg _) (hA _).2).trans ih)
          ((mul_le_mul_of_nonneg_left (shifted_scaled_bound A ρ C hA hρ hC h n k) hpow.1).trans
            (mul_le_of_le_one_left (by positivity) hpow.2))
      _ ≤ ((k+1:ℕ):ℝ) * (C+(k+1:ℕ)) := by push_cast; nlinarith


private noncomputable def U (A : ℕ → ℝ) (n k : ℕ) : ℝ := Q n k * R A n k
private noncomputable def V (A : ℕ → ℝ) (n k : ℕ) : ℝ := P n k * R A n (k+1)
private noncomputable def Z (ρ : ℝ) (k : ℕ) : ℝ := W k * ρ^k
private noncomputable def E (ρ c : ℝ) (k : ℕ) : ℝ := G k * ρ^k + W k * J ρ c k
private noncomputable def B (C : ℝ) (k : ℕ) : ℝ := ((k:ℝ) + k*(C+k)) * M k

private theorem summable_B (C : ℝ) (hC : 0 ≤ C) : Summable (B C) := by
  apply Summable.of_nonneg_of_le (fun k => by unfold B M; positivity) _
    ((Real.summable_pow_div_factorial 24).mul_left (C+2))
  intro k
  have hk : (k:ℝ) ≤ (2:ℝ)^k := by exact_mod_cast (Nat.lt_two_pow_self (n := k)).le
  have hsq : (k:ℝ)^2 ≤ (4:ℝ)^k := by
    calc
      _ ≤ ((2:ℝ)^k)^2 := pow_le_pow_left₀ (by positivity) hk _
      _ = (4:ℝ)^k := by rw [← pow_mul, Nat.mul_comm, pow_mul]; norm_num
  have h24 : (2:ℝ)^k ≤ (4:ℝ)^k := pow_le_pow_left₀ (by norm_num) (by norm_num) _
  unfold B M
  simp only [← mul_div_assoc]
  apply div_le_div_of_nonneg_right _ (by positivity)
  calc
    ((k:ℝ) + k*(C+k)) * 6^k ≤ ((C+2)*4^k) * 6^k := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      have hm := mul_le_mul_of_nonneg_left (hk.trans h24) (show 0 ≤ C+1 by linarith)
      nlinarith
    _ = (C+2) * 24^k := by rw [mul_assoc, ← mul_pow]; norm_num

private theorem summable_Z (ρ : ℝ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1) : Summable (Z ρ) := by
  apply Summable.of_nonneg_of_le (fun k => mul_nonneg (by unfold W; positivity) (pow_nonneg hρ.1 _)) _ summable_M
  intro k
  exact (mul_le_of_le_one_right (by unfold W; positivity) (pow_le_one₀ hρ.1 hρ.2)).trans (W_le_M k)

private theorem U_summable (A : ℕ → ℝ) (n : ℕ) : Summable (U A n) := by
  apply summable_of_ne_finset_zero (s := range (n+1))
  intro k hk
  have hn : n < k := by simp only [mem_range, not_lt] at hk; omega
  simp [U, Q_of_gt n k hn]

private theorem U_scaled_limit (A : ℕ → ℝ) (ρ c : ℝ)
    (h : Tendsto (fun n : ℕ => (n:ℝ) * (A n - ρ)) atTop (𝓝 c)) (k : ℕ) :
    Tendsto (fun n : ℕ => (n:ℝ) * (U A n k - Z ρ k)) atTop (𝓝 (E ρ c k)) := by
  have hr := R_scaled_limit A ρ c h k
  have h0 := tendsto_of_scaled (fun n => R A n k) _ _ hr
  have ht := ((Q_scaled_limit k).mul h0).add (hr.const_mul (W k))
  change Tendsto _ _ (𝓝 (G k * ρ^k + W k * J ρ c k))
  convert ht using 1
  ext n
  unfold U Z
  ring

private theorem U_scaled_bound (A : ℕ → ℝ) (ρ C : ℝ)
    (hA : ∀ n, 0 ≤ A n ∧ A n ≤ 1) (hρ : 0 ≤ ρ ∧ ρ ≤ 1) (hC : 0 ≤ C)
    (h : ∀ n : ℕ, |(n:ℝ) * (A n - ρ)| ≤ C) (n k : ℕ) : |(n:ℝ) * (U A n k - Z ρ k)| ≤ B C k := by
  have hr := R_bounds A hA n k
  have hw : 0 ≤ W k := by unfold W; positivity
  calc
    _ = |((n:ℝ)*(Q n k-W k))*R A n k + W k*((n:ℝ)*(R A n k-ρ^k))| := by
      unfold U Z; congr 1; ring
    _ ≤ |(n:ℝ)*(Q n k-W k)| * R A n k + W k * |(n:ℝ)*(R A n k-ρ^k)| := by
      simpa only [abs_mul, abs_of_nonneg hr.1, abs_of_nonneg hw] using
        abs_add_le (((n:ℝ)*(Q n k-W k))*R A n k) (W k*((n:ℝ)*(R A n k-ρ^k)))
    _ ≤ (k:ℝ)*M k + W k*((k:ℝ)*(C+k)) :=
      add_le_add ((mul_le_of_le_one_right (abs_nonneg _) hr.2).trans (Q_scaled_bound n k))
        (mul_le_mul_of_nonneg_left (R_scaled_bound A ρ C hA hρ hC h n k) hw)
    _ ≤ B C k := by
      have hm := mul_le_mul_of_nonneg_right (W_le_M k) (show 0 ≤ (k:ℝ)*(C+k) by positivity)
      unfold B
      nlinarith

private theorem U_tsum_limit (A : ℕ → ℝ) (ρ c C : ℝ)
    (hA : ∀ n, 0 ≤ A n ∧ A n ≤ 1) (hρ : 0 ≤ ρ ∧ ρ ≤ 1) (hC : 0 ≤ C)
    (hbound : ∀ n : ℕ, |(n:ℝ) * (A n - ρ)| ≤ C)
    (h : Tendsto (fun n : ℕ => (n:ℝ) * (A n - ρ)) atTop (𝓝 c)) :
    Tendsto (fun n : ℕ => (n:ℝ) * ((∑' k, U A n k) - ∑' k, Z ρ k)) atTop
      (𝓝 (∑' k, E ρ c k)) := by
  have ht := tendsto_tsum_of_dominated_convergence (summable_B C hC) (U_scaled_limit A ρ c h)
    (Eventually.of_forall (fun n k => by simpa only [Real.norm_eq_abs] using U_scaled_bound A ρ C hA hρ hC hbound n k))
  convert ht using 1
  ext n
  rw [tsum_mul_left, (U_summable A n).tsum_sub (summable_Z ρ hρ)]

private theorem V_tsum_limit (A : ℕ → ℝ) (ρ c : ℝ)
    (hA : ∀ n, 0 ≤ A n ∧ A n ≤ 1)
    (h : Tendsto (fun n : ℕ => (n:ℝ) * (A n - ρ)) atTop (𝓝 c)) :
    Tendsto (fun n : ℕ => (n:ℝ) * ∑' k, V A n k) atTop
      (𝓝 (∑' k, W k * ρ^(k+1))) := by
  have hp (k : ℕ) : Tendsto (fun n : ℕ => (n:ℝ) * V A n k) atTop (𝓝 (W k * ρ^(k+1))) := by
    have hr := tendsto_of_scaled (fun n => R A n (k+1)) _ _ (R_scaled_limit A ρ c h (k+1))
    convert (P_scaled_limit k).mul hr using 1
    ext n; unfold V; ring
  have hb (n k : ℕ) : ‖(n:ℝ) * V A n k‖ ≤ ((k:ℝ)+1)*M k := by
    rw [Real.norm_eq_abs, V, ← mul_assoc, abs_mul, abs_of_nonneg (R_bounds A hA n (k+1)).1]
    exact (mul_le_of_le_one_right (abs_nonneg _) (R_bounds A hA n (k+1)).2).trans (P_scaled_bound n k)
  have ht := tendsto_tsum_of_dominated_convergence summable_succ_M hp (Eventually.of_forall hb)
  simpa only [tsum_mul_left] using ht

private theorem diagonal_U_limit (A : ℕ → ℝ) (hA : ∀ n, 0 ≤ A n ∧ A n ≤ 1) :
    Tendsto (fun n : ℕ => (n:ℝ) * U A n n) atTop (𝓝 (0:ℝ)) := by
  apply squeeze_zero (fun n => mul_nonneg (by positivity) (mul_nonneg (Q_nonneg n n) (R_bounds A hA n n).1))
    (fun n => show (n:ℝ)*U A n n ≤ (n:ℝ)*Q n n from
      mul_le_mul_of_nonneg_left (mul_le_of_le_one_right (Q_nonneg n n) (R_bounds A hA n n).2) (by positivity))
    diagonal_Q_scaled_limit


private noncomputable def A (b : ℕ → ℕ) (n : ℕ) : ℝ := (n:ℝ) * b (n-1) / b n

private theorem R_border (b : ℕ → ℕ) (hb : ∀ n, b n ≠ 0) (n k : ℕ) (hkn : k ≤ n) :
    R (A b) n k = (b (n-k):ℝ) * n.factorial / ((n-k).factorial * (b n:ℝ)) := by
  have hbR (j : ℕ) : (b j:ℝ) ≠ 0 := by exact_mod_cast hb j
  have hf (j : ℕ) : (j.factorial:ℝ) ≠ 0 := by positivity
  induction k
  case zero => simp only [R_zero, Nat.sub_zero]; field_simp [hf, hbR] <;> ring
  case succ k ih =>
    have hkn' : k ≤ n := by exact Nat.le_of_succ_le hkn
    have hnk : n-k ≠ 0 := by exact Nat.sub_ne_zero_iff_lt.mpr hkn
    have he : ((n-k:ℕ):ℝ) * ((n-k-1).factorial:ℝ) = ((n-k).factorial:ℝ) := by
      exact_mod_cast Nat.mul_factorial_pred hnk
    rw [R_succ, ih hkn']
    unfold A
    rw [show n-(k+1) = n-k-1 by omega]
    rw [← he]
    field_simp [hbR, hf] <;> ring

private theorem U_border (b : ℕ → ℕ) (hb : ∀ n, b n ≠ 0) (n k : ℕ) (hkn : k ≤ n) :
    U (A b) n k = (b (n-k):ℝ) * (fun m n => (f (fun _ => 1) m n : ℝ)) k n / b n := by
  unfold U
  rw [Q_factorial n k hkn, R_border b hb n k hkn]
  have hf (j : ℕ) : (j.factorial:ℝ) ≠ 0 := by positivity
  have hbR : (b n:ℝ) ≠ 0 := by exact Nat.cast_ne_zero.mpr (hb n)
  field_simp [hf, hbR]

private theorem delta_border_term (b : ℕ → ℕ) (hb : ∀ n, b n ≠ 0) (n k : ℕ) (hkn : k ≤ n) :
    delta b (n-k) * (fun m n => (f (fun _ => 1) m n : ℝ)) k n / b n = U (A b) n k - V (A b) n k := by
  have hbR (j : ℕ) : (b j:ℝ) ≠ 0 := by exact_mod_cast hb j
  have hf (j : ℕ) : (j.factorial:ℝ) ≠ 0 := by positivity
  rw [U_border b hb n k hkn]
  by_cases hk : k = n
  · subst k
    simp [V, P, delta]
  · have hkn' : k < n := by exact Nat.lt_of_le_of_ne hkn hk
    have hnk : ((n-k:ℕ):ℝ) ≠ 0 := by exact_mod_cast (show n-k ≠ 0 by omega)
    have hd : delta b (n-k) = (b (n-k):ℝ) - b (n-k-1) := by
      cases he : n-k
      case zero => omega
      case succ j => simp [delta, he]
    have he : ((n-k:ℕ):ℝ) * ((n-k-1).factorial:ℝ) = ((n-k).factorial:ℝ) := by
      exact_mod_cast Nat.mul_factorial_pred (show n-k ≠ 0 by omega)
    rw [hd, V, P, if_pos hkn', Q_factorial n k hkn, R_border b hb n (k+1) (by omega)]
    rw [show n-(k+1) = n-k-1 by omega]
    rw [← he]
    field_simp [hbR, hf, hnk] <;> ring

private theorem U_tsum (A : ℕ → ℝ) (n : ℕ) : ∑' k, U A n k = ∑ k ∈ range (n+1), U A n k := by
  apply tsum_eq_sum
  intro k hk
  have hn : n < k := by simp only [mem_range, not_lt] at hk; omega
  simp [U, Q_of_gt n k hn]

private theorem V_tsum (A : ℕ → ℝ) (n : ℕ) : ∑' k, V A n k = ∑ k ∈ range (n+1), V A n k := by
  apply tsum_eq_sum
  intro k hk
  have hn : ¬ k < n := by simp only [mem_range, not_lt] at hk; omega
  simp [V, P, hn]

private theorem normalized_border (b : ℕ → ℕ) (hb : ∀ n, b n ≠ 0) (n : ℕ) :
    (f b n n:ℝ) / b n = 2 * ∑' k, U (A b) n k - 2 * ∑' k, V (A b) n k - U (A b) n n := by
  have hc : conv (delta b) n n / b n = (∑' k, U (A b) n k) - ∑' k, V (A b) n k := by
    unfold conv
    have href := sum_range_reflect (fun j => delta b j * (fun m n => (f (fun _ => 1) m n : ℝ)) (n-j) n) (n+1)
    simp only [Nat.add_sub_cancel] at href
    rw [← href, sum_div, U_tsum, V_tsum, ← sum_sub_distrib]
    apply sum_congr rfl
    intro k hk
    have hkn : k ≤ n := Nat.le_of_lt_succ (mem_range.mp hk)
    rw [Nat.sub_sub_self hkn]
    exact delta_border_term b hb n k hkn
  have hd : (b 0:ℝ) * (fun m n => (f (fun _ => 1) m n : ℝ)) n n / b n = U (A b) n n := by
    rw [U_border b hb n n le_rfl, Nat.sub_self]
  rw [diagonal_convolution, sub_div, mul_div_assoc, hc, hd]
  ring

private theorem border_first_order (b : ℕ → ℕ) (hb : ∀ n, b n ≠ 0) (ρ c : ℝ)
    (hA : ∀ n, 0 ≤ A b n ∧ A b n ≤ 1) (hρ : 0 ≤ ρ ∧ ρ ≤ 1)
    (h : Tendsto (fun n : ℕ => (n:ℝ) * (A b n - ρ)) atTop (𝓝 c)) :
    Tendsto (fun n : ℕ => (n:ℝ) * ((f b n n:ℝ) / b n - 2 * ∑' k, Z ρ k)) atTop
      (𝓝 (2 * (∑' k, E ρ c k) - 2 * ∑' k, W k * ρ^(k+1))) := by
  obtain ⟨C, hC, hbound⟩ := (Metric.isBounded_range_of_tendsto _ h).exists_pos_norm_le
  have hbnd (n : ℕ) : |(n:ℝ) * (A b n-ρ)| ≤ C := by
    simpa only [Real.norm_eq_abs] using hbound _ (Set.mem_range_self n)
  have ht := (((U_tsum_limit (A b) ρ c C hA hρ hC.le hbnd h).const_mul 2).sub
    ((V_tsum_limit (A b) ρ c hA h).const_mul 2)).sub (diagonal_U_limit (A b) hA)
  simp only [sub_zero] at ht
  convert ht using 1
  ext n
  rw [normalized_border b hb n]
  ring


private def powBorder (n : ℕ) : ℕ := n^n
private noncomputable def L (n : ℕ) : ℝ := ((n:ℝ)-1) * Real.log (1-1/(n:ℝ))

private theorem powBorder_ne (n : ℕ) : powBorder n ≠ 0 := by
  cases n
  case zero => simp [powBorder]
  case succ n => exact pow_ne_zero _ (Nat.succ_ne_zero n)

private theorem A_power_eq (n : ℕ) (hn : 1 ≤ n) :
    A powBorder n = (((n-1:ℕ):ℝ) / n)^(n-1) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show n ≠ 0 by omega)
  have hm : ((m+1:ℕ):ℝ) ≠ 0 := by positivity
  simp only [A, powBorder, Nat.succ_sub_one, Nat.cast_pow, Nat.cast_succ]
  rw [div_pow, pow_succ]
  field_simp

private theorem A_power_bounds (n : ℕ) : 0 ≤ A powBorder n ∧ A powBorder n ≤ 1 := by
  by_cases hn : 1 ≤ n
  · rw [A_power_eq n hn]
    have hnR : (0:ℝ) < n := by exact Nat.cast_pos'.mpr hn
    have hratio : (0:ℝ) ≤ ((n-1:ℕ):ℝ) / n ∧ ((n-1:ℕ):ℝ) / n ≤ 1 :=
      ⟨div_nonneg (Nat.cast_nonneg _) hnR.le,
        (div_le_one hnR).2 (by exact_mod_cast Nat.sub_le n 1)⟩
    exact ⟨pow_nonneg hratio.1 _, pow_le_one₀ hratio.1 hratio.2⟩
  · have hn0 : n = 0 := by exact Nat.eq_zero_of_not_pos hn
    subst n
    simp [A]

private theorem A_power_exp (n : ℕ) (hn : 2 ≤ n) : A powBorder n = Real.exp (L n) := by
  rw [A_power_eq n (by omega)]
  have hnR : (n:ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hp : (0:ℝ) < 1-1/(n:ℝ) := by
    have hh : (1:ℝ) < n := by exact Nat.one_lt_cast.mpr hn
    exact sub_pos.mpr ((div_lt_one (by linarith)).2 hh)
  have hcast : ((n-1:ℕ):ℝ) = (n:ℝ)-1 := by rw [Nat.cast_sub (by omega), Nat.cast_one]
  have he : (((n-1:ℕ):ℝ) / n) = 1-1/(n:ℝ) := by rw [hcast]; field_simp
  rw [he, L, ← hcast, ← Real.log_pow, Real.exp_log (pow_pos hp _)]

private theorem L_error (n : ℕ) (hn : 2 ≤ n) : |(n:ℝ) * (L n + 1) - (1/2 + 1/(2*(n:ℝ)))| ≤ 1/(n:ℝ) := by
  have hnR : (1:ℝ) < n := by exact Nat.one_lt_cast.mpr hn
  have hn0 : (n:ℝ) ≠ 0 := by positivity
  have hh : |1/(n:ℝ)| < 1 := by rw [abs_of_pos (by positivity)]; exact (div_lt_one (by positivity)).2 hnR
  have ht : |1/(n:ℝ) + (1/(n:ℝ))^2/2 + Real.log (1-1/(n:ℝ))| ≤
      (1/(n:ℝ))^3/(1-1/(n:ℝ)) := by
    convert Real.abs_log_sub_add_sum_range_le hh 2 using 1 <;> norm_num [sum_range_succ]
  have hc : 0 ≤ (n:ℝ)*((n:ℝ)-1) := by positivity
  have he : (n:ℝ) * (L n + 1) - (1/2 + 1/(2*(n:ℝ))) =
      ((n:ℝ)*((n:ℝ)-1)) * (1/(n:ℝ) + (1/(n:ℝ))^2/2 + Real.log (1-1/(n:ℝ))) := by
    unfold L
    field_simp
    <;> ring
  rw [he, abs_mul, abs_of_nonneg hc]
  have hmul := mul_le_mul_of_nonneg_left ht hc
  have hden : 1-1/(n:ℝ) ≠ 0 := by
    have : 1/(n:ℝ) < 1 := (div_lt_one (by positivity)).2 hnR
    linarith
  have hz : ((n:ℝ)*((n:ℝ)-1)) * ((1/(n:ℝ))^(2+1)/(1-1/(n:ℝ))) = 1/(n:ℝ) := by
    field_simp [hn0, hden] <;> ring_nf <;> simp [← mul_pow, hn0]
  simpa only [hz] using hmul

private theorem L_scaled_limit :
    Tendsto (fun n : ℕ => (n:ℝ) * (L n + 1)) atTop (𝓝 (1/2:ℝ)) := by
  have he : Tendsto (fun n : ℕ => (n:ℝ) * (L n + 1) - (1/2 + 1/(2*(n:ℝ)))) atTop (𝓝 (0:ℝ)) := by
    apply squeeze_zero_norm' (eventually_atTop.mpr ⟨2, fun n hn => by simpa only [Real.norm_eq_abs] using L_error n hn⟩)
      (by simpa using (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)))
  have hi : Tendsto (fun n : ℕ => (1/2:ℝ) + 1/(2*(n:ℝ))) atTop (𝓝 (1/2:ℝ)) := by
    convert (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).div_const 2 |>.const_add (1/2:ℝ) using 1 <;> try norm_num <;> (ext n; ring)
  convert he.add hi using 1 <;> try norm_num <;> (ext n; ring)

private theorem exp_scaled_limit (u : ℕ → ℝ) (a c : ℝ)
    (h : Tendsto (fun n : ℕ => (n:ℝ) * (u n - a)) atTop (𝓝 c)) :
    Tendsto (fun n : ℕ => (n:ℝ) * (Real.exp (u n) - Real.exp a)) atTop (𝓝 (c * Real.exp a)) := by
  classical
  let q := Function.update (fun x : ℝ => (Real.exp x-Real.exp a)/(x-a)) a (Real.exp a)
  have hq : ContinuousAt q a := (Real.hasDerivAt_exp a).continuousAt_div
  have ht := h.mul (hq.tendsto.comp (tendsto_of_scaled u a c h))
  have hqa : q a = Real.exp a := by exact Function.update_self a (Real.exp a) fun x => (Real.exp x - Real.exp a) / (x - a)
  rw [hqa] at ht
  convert ht using 1
  ext n
  change (n:ℝ) * (Real.exp (u n) - Real.exp a) = (n:ℝ) * (u n-a) * q (u n)
  by_cases hn : u n = a
  · simp [hn]
  · dsimp [q]
    rw [Function.update_of_ne hn]
    field_simp

private theorem A_power_scaled_limit :
    Tendsto (fun n : ℕ => (n:ℝ) * (A powBorder n - Real.exp (-1))) atTop
      (𝓝 (Real.exp (-1)/2)) := by
  have hl : Tendsto (fun n : ℕ => (n:ℝ) * (L n - (-1))) atTop (𝓝 (1/2:ℝ)) := by
    simpa only [sub_neg_eq_add] using L_scaled_limit
  have ht := exp_scaled_limit L (-1) (1/2) hl
  rw [one_div_mul_eq_div] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 2] with n hn
  rw [A_power_exp n hn]


private theorem reciprocal_border (n : ℕ) :
    (powBorder (n+1):ℝ) / powBorder n / ((n:ℝ)+1) = (A powBorder (n+1))⁻¹ := by
  have hbR (j : ℕ) : (powBorder j:ℝ) ≠ 0 := by exact_mod_cast powBorder_ne j
  have hn : (n:ℝ)+1 ≠ 0 := by exact Nat.cast_add_one_ne_zero n
  unfold A
  simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
  field_simp [hbR, hn]

private theorem border_power_limit :
    Tendsto (fun n : ℕ => (powBorder (n+1):ℝ) / powBorder n - Real.exp 1*((n:ℝ)+1/2))
      atTop (𝓝 (0:ℝ)) := by
  let ρ := Real.exp (-1)
  have hρ : ρ ≠ 0 := Real.exp_ne_zero _
  have hr : ρ⁻¹ = Real.exp 1 := by dsimp [ρ]; rw [← Real.exp_neg]; norm_num
  have h0 := tendsto_of_scaled (A powBorder) ρ (ρ/2) A_power_scaled_limit
  have hs := h0.comp (tendsto_add_atTop_nat 1)
  have hc := A_power_scaled_limit.comp (tendsto_add_atTop_nat 1)
  have ht := ((hc.div (hs.mul_const ρ) (mul_ne_zero hρ hρ)).neg).add_const (1/(2*ρ))
  have hz : -(ρ/2/(ρ*ρ)) + 1/(2*ρ) = 0 := by field_simp <;> ring
  rw [hz] at ht
  apply ht.congr'
  filter_upwards [hs.eventually (eventually_ne_nhds hρ)] with n hn
  simp only [Pi.div_apply, Function.comp_apply, Nat.cast_add, Nat.cast_one]
  change A powBorder (n+1) ≠ 0 at hn
  rw [show (powBorder (n+1):ℝ) / powBorder n = ((n:ℝ)+1) * (A powBorder (n+1))⁻¹ from by
    have he := reciprocal_border n
    have hp : (n:ℝ)+1 ≠ 0 := by exact Nat.cast_add_one_ne_zero n
    simpa only [mul_comm] using (div_eq_iff hp).mp he]
  rw [← hr]
  change -(((n:ℝ)+1)*(A powBorder (n+1)-ρ)/(A powBorder (n+1)*ρ)) + 1/(2*ρ) =
    ((n:ℝ)+1)*(A powBorder (n+1))⁻¹ - ρ⁻¹*((n:ℝ)+1/2)
  field_simp [hn, hρ] <;> ring

theorem result : claimPower := by
  let ρ := Real.exp (-1)
  have hρ : 0 ≤ ρ ∧ ρ ≤ 1 := ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr (by norm_num)⟩
  have hf := border_first_order powBorder powBorder_ne ρ (ρ/2) A_power_bounds hρ A_power_scaled_limit
  have hc : 0 < 2 * ∑' k, Z ρ k := by
    have hz : 0 < ∑' k, Z ρ k := by
      apply (summable_Z ρ hρ).tsum_pos (fun k => by unfold Z W; positivity) 0
      norm_num [Z, W]
    linarith
  have h0 := tendsto_of_scaled _ _ _ hf
  have ha (n : ℕ) : (f powBorder n n:ℝ) = (powBorder n:ℝ) * ((f powBorder n n:ℝ) / powBorder n) := by
    have hbR : (powBorder n:ℝ) ≠ 0 := by exact_mod_cast powBorder_ne n
    field_simp
  have hA0 := tendsto_of_scaled (A powBorder) ρ (ρ/2) A_power_scaled_limit
  have hB : Tendsto (fun n : ℕ => (powBorder (n+1):ℝ) / powBorder n / ((n:ℝ)+1)) atTop (𝓝 (ρ⁻¹)) := by
    simpa only [reciprocal_border, Function.comp_apply] using (hA0.comp (tendsto_add_atTop_nat 1)).inv₀ (Real.exp_ne_zero _)
  have ht := ratio_transfer (fun n => (f powBorder n n:ℝ)) (fun n => (powBorder n:ℝ)) _
    _ _ _ (fun n => by exact_mod_cast powBorder_ne n) ha hc.ne' h0 hf hB
  have hu := ht.add border_power_limit
  simp only [add_zero] at hu
  change Tendsto (fun n : ℕ => (f powBorder (n+1) (n+1):ℝ) / f powBorder n n -
    Real.exp 1*((n:ℝ)+1/2)) atTop (𝓝 0)
  apply hu.congr'
  exact Eventually.of_forall (fun n => by dsimp; ring)

end D5.S3.Combinatorics.Delannoy.GrauOllerMarcenVaronaPowerBorderGrowth
