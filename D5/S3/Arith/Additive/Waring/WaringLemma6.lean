/- GID: D5/S3/Arith/Additive/Waring/WaringLemma6
   generality: G
   mirror-B: D5/B/S3/Arith/Additive/Waring/WaringLemma6
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Third-party formalization of the qualitative Hilbert–Waring theorem. -/

/- Source: https://github.com/yunyougu50-create/waring-lean4/blob/cd0735c253f3b640262fcc74a61306cb41e23765/WaringLemma6.lean#L1-L348
   Modified for this repository. Local imports use their D5 module paths.
   Selected declaration closure and supporting source.
   Full Apache-2.0 license: D5/S3/Arith/Additive/Waring/WaringDensity.lean. -/

import D5.S3.Arith.Additive.Waring.WaringCount

open Finset

namespace Waring

/-! ## Lemma 6（平方版）的零件：望远镜不等式 -/

/-- 单项望远镜：`1/b² ≤ 1/(b−1) − 1/b`（`b ≥ 2`）。 -/
theorem one_div_sq_le (b : ℕ) (hb : 2 ≤ b) :
    (1 : ℚ) / (b : ℚ) ^ 2 ≤ 1 / ((b : ℚ) - 1) - 1 / (b : ℚ) := by
  have hb1 : (2 : ℚ) ≤ (b : ℚ) := by exact_mod_cast hb
  have hb0 : (0 : ℚ) < (b : ℚ) := by linarith
  have hb0' : (0 : ℚ) < (b : ℚ) - 1 := by linarith
  have h : (1 : ℚ) / ((b : ℚ) - 1) - 1 / (b : ℚ) = 1 / (((b : ℚ) - 1) * (b : ℚ)) := by
    field_simp
    ring
  rw [h]
  apply one_div_le_one_div_of_le (by positivity)
  nlinarith

/-- `Σ_{b=a+1}^{x} 1/b² ≤ 1/a − 1/x`（`a ≥ 1`，`x ≥ a+1`）。 -/
theorem sum_inv_sq_Icc_aux (a x : ℕ) (ha : 1 ≤ a) (hax : a + 1 ≤ x) :
    (∑ b ∈ Finset.Icc (a + 1) x, (1 : ℚ) / (b : ℚ) ^ 2) ≤ 1 / (a : ℚ) - 1 / (x : ℚ) := by
  induction x, hax using Nat.le_induction with
  | base =>
    rw [Finset.Icc_self, Finset.sum_singleton]
    have h := one_div_sq_le (a + 1) (by omega)
    push_cast at h ⊢
    simp only [add_sub_cancel_right] at h
    linarith
  | succ x hx ih =>
    rw [Finset.sum_Icc_succ_top (by omega : a + 1 ≤ x + 1)]
    have hstep := one_div_sq_le (x + 1) (by omega)
    push_cast at hstep
    simp only [add_sub_cancel_right] at hstep
    push_cast at ih ⊢
    linarith

/-- `Σ_{b=a+1}^{x} 1/b² ≤ 1/a`。 -/
theorem sum_inv_sq_Icc_succ_le {a x : ℕ} (ha : 1 ≤ a) (hax : a + 1 ≤ x) :
    (∑ b ∈ Finset.Icc (a + 1) x, (1 : ℚ) / (b : ℚ) ^ 2) ≤ 1 / (a : ℚ) := by
  have h := sum_inv_sq_Icc_aux a x ha hax
  have hx : (0 : ℚ) < (x : ℚ) := by
    have : 0 < x := by omega
    exact_mod_cast this
  have : (0 : ℚ) ≤ 1 / (x : ℚ) := by positivity
  linarith

/-- 把 `{a ∈ [1,x] : b < a}` 认成 `[b+1, x]`。 -/
theorem filter_Icc_lt {b x : ℕ} (hb : 1 ≤ b) :
    (Finset.Icc 1 x).filter (fun a => b < a) = Finset.Icc (b + 1) x := by
  ext a
  rw [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Icc]
  omega

/-- `1/(ab) · 1/lcm(a,b) = gcd(a,b)/(ab)²`。 -/
theorem inv_mul_inv_lcm_eq {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    (1 : ℚ) / ((a : ℚ) * (b : ℚ)) * (1 / (Nat.lcm a b : ℚ))
      = (Nat.gcd a b : ℚ) / ((a : ℚ) * (b : ℚ)) ^ 2 := by
  have hgl : (Nat.gcd a b : ℚ) * (Nat.lcm a b : ℚ) = (a : ℚ) * (b : ℚ) := by
    exact_mod_cast Nat.gcd_mul_lcm a b
  have h1 : (0 : ℚ) < (a : ℚ) := by exact_mod_cast ha
  have h2 : (0 : ℚ) < (b : ℚ) := by exact_mod_cast hb
  have hl : (0 : ℚ) < (Nat.lcm a b : ℚ) := by exact_mod_cast Nat.lcm_pos ha hb
  rw [div_mul_div_comm, div_eq_div_iff (by positivity) (by positivity)]
  rw [one_mul, ← hgl]
  ring

/-! ## `σ₋₁(n)²` 在 `Icc 1 x` 上的双重和形式 -/

/-- `σ₋₁(n)²` 写成 `Icc 1 x` 上的双重 filter 求和（`n ≤ x`，`n ≠ 0`）。 -/
theorem sigmaMinusOne_sq_eq_sum_Icc {n : ℕ} (hn : n ≠ 0) {x : ℕ} (hnx : n ≤ x) :
    sigmaMinusOne n ^ 2
      = ∑ a ∈ Finset.Icc 1 x, ∑ b ∈ Finset.Icc 1 x,
          (if a ∣ n ∧ b ∣ n then (1 : ℚ) / ((a : ℚ) * (b : ℚ)) else 0) := by
  classical
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  have hndiv : n.divisors = (Finset.Icc 1 x).filter (fun a => a ∣ n) := by
    ext a
    rw [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨hdvd, -⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hdvd hnpos,
        le_trans (Nat.le_of_dvd hnpos hdvd) hnx⟩, hdvd⟩
    · rintro ⟨-, hdvd⟩
      exact ⟨hdvd, hn⟩
  have hinner : ∀ a : ℕ, (∑ b ∈ n.divisors, (1 : ℚ) / ((a : ℚ) * (b : ℚ)))
      = ∑ b ∈ Finset.Icc 1 x, (if b ∣ n then (1 : ℚ) / ((a : ℚ) * (b : ℚ)) else 0) := by
    intro a
    rw [hndiv, Finset.sum_filter]
  rw [sigmaMinusOne_sq_eq n, Finset.sum_congr rfl (fun a _ => hinner a)]
  rw [hndiv, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  by_cases ha : a ∣ n
  · simp only [ha, if_true]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    by_cases hb : b ∣ n <;> simp [hb]
  · rw [if_neg ha]
    rw [Finset.sum_eq_zero]
    intro b _
    rw [if_neg (fun h => ha h.1)]

/-- **交换求和**：`Σ_{n≤x} σ₋₁(n)² = Σ_{a,b≤x} (1/ab)·#{n≤x : a∣n ∧ b∣n}`。 -/
theorem sum_sigmaMinusOne_sq_eq (x : ℕ) :
    (∑ n ∈ Finset.Icc 1 x, sigmaMinusOne n ^ 2)
      = ∑ a ∈ Finset.Icc 1 x, ∑ b ∈ Finset.Icc 1 x,
          (1 : ℚ) / ((a : ℚ) * (b : ℚ))
            * (((Finset.Icc 1 x).filter (fun n => a ∣ n ∧ b ∣ n)).card : ℚ) := by
  classical
  have h1 : ∀ n ∈ Finset.Icc 1 x, sigmaMinusOne n ^ 2
      = ∑ a ∈ Finset.Icc 1 x, ∑ b ∈ Finset.Icc 1 x,
          (if a ∣ n ∧ b ∣ n then (1 : ℚ) / ((a : ℚ) * (b : ℚ)) else 0) := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    exact sigmaMinusOne_sq_eq_sum_Icc (by omega) hn.2
  rw [Finset.sum_congr rfl h1]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_comm)]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
  rw [← Finset.sum_filter]
  rw [Finset.sum_const, nsmul_eq_mul]
  ring

/-! ## 核：`Σ_{a,b≤x} gcd(a,b)/(ab)² ≤ 6` -/

/-- `gcd(a,b)/(ab)² ≤ 1/(ab·max(a,b))`。 -/
theorem gcd_div_sq_le {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    (Nat.gcd a b : ℚ) / ((a : ℚ) * (b : ℚ)) ^ 2
      ≤ 1 / ((a : ℚ) * (b : ℚ) * max (a : ℚ) (b : ℚ)) := by
  have h1 : (0 : ℚ) < (a : ℚ) := by exact_mod_cast ha
  have h2 : (0 : ℚ) < (b : ℚ) := by exact_mod_cast hb
  have hmax : (0 : ℚ) < max (a : ℚ) (b : ℚ) := lt_max_of_lt_left h1
  have hgl : (Nat.gcd a b : ℚ) * (Nat.lcm a b : ℚ) = (a : ℚ) * (b : ℚ) := by
    exact_mod_cast Nat.gcd_mul_lcm a b
  have hmaxle : max (a : ℚ) (b : ℚ) ≤ (Nat.lcm a b : ℚ) := by
    have h := max_le_lcm ha hb
    exact_mod_cast h
  have hkey : (Nat.gcd a b : ℚ) * max (a : ℚ) (b : ℚ) ≤ (a : ℚ) * (b : ℚ) := by
    calc (Nat.gcd a b : ℚ) * max (a : ℚ) (b : ℚ)
        ≤ (Nat.gcd a b : ℚ) * (Nat.lcm a b : ℚ) :=
          mul_le_mul_of_nonneg_left hmaxle (by positivity)
      _ = (a : ℚ) * (b : ℚ) := hgl
  have hden2 : (0 : ℚ) < ((a : ℚ) * (b : ℚ)) ^ 2 := by positivity
  have hden3 : (0 : ℚ) < (a : ℚ) * (b : ℚ) * max (a : ℚ) (b : ℚ) := by positivity
  have key : 1 / ((a : ℚ) * (b : ℚ) * max (a : ℚ) (b : ℚ))
        - (Nat.gcd a b : ℚ) / ((a : ℚ) * (b : ℚ)) ^ 2
      = ((a : ℚ) * (b : ℚ) - (Nat.gcd a b : ℚ) * max (a : ℚ) (b : ℚ))
        / (((a : ℚ) * (b : ℚ)) ^ 2 * max (a : ℚ) (b : ℚ)) := by
    field_simp
  rw [← sub_nonneg, key]
  apply div_nonneg _ (by positivity)
  linarith

/-- 把 `1/(ab·max)` 拆成「b<a」「a<b」「a=b」三段。 -/
theorem inv_mul_max_split {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    1 / ((a : ℚ) * (b : ℚ) * max (a : ℚ) (b : ℚ))
      = (if b < a then 1 / ((a : ℚ) ^ 2 * (b : ℚ)) else 0)
        + (if a < b then 1 / ((a : ℚ) * (b : ℚ) ^ 2) else 0)
        + (if a = b then 1 / ((a : ℚ) ^ 3) else 0) := by
  rcases lt_trichotomy b a with h | h | h
  · have hba : (b : ℚ) ≤ (a : ℚ) := by exact_mod_cast le_of_lt h
    rw [if_pos h, if_neg (by omega), if_neg (by omega), max_eq_left hba]
    ring
  · subst h
    rw [if_neg (by omega), if_neg (by omega), if_pos rfl, max_self]
    ring
  · have hab : (a : ℚ) ≤ (b : ℚ) := by exact_mod_cast le_of_lt h
    rw [if_neg (by omega), if_pos h, if_neg (by omega), max_eq_right hab]
    ring

/-- **Lemma 6 的核**：`Σ_{a,b≤x} gcd(a,b)/(ab)² ≤ 6`。 -/
theorem sum_gcd_div_sq_le (x : ℕ) :
    (∑ a ∈ Finset.Icc 1 x, ∑ b ∈ Finset.Icc 1 x,
        (Nat.gcd a b : ℚ) / ((a : ℚ) * (b : ℚ)) ^ 2) ≤ 6 := by
  classical
  set S := Finset.Icc 1 x with hS
  have hpos : ∀ a ∈ S, (0 : ℚ) < (a : ℚ) := by
    intro a ha
    have h1 : 0 < a := (Finset.mem_Icc.mp ha).1
    exact_mod_cast h1
  -- 第一段：`b < a`
  have hA : (∑ a ∈ S, ∑ b ∈ S, (if b < a then (1 : ℚ) / ((a : ℚ) ^ 2 * (b : ℚ)) else 0))
      ≤ 2 := by
    rw [Finset.sum_comm]
    have hrow : ∀ b ∈ S, (∑ a ∈ S, (if b < a then (1 : ℚ) / ((a : ℚ) ^ 2 * (b : ℚ)) else 0))
        ≤ (1 / (b : ℚ)) * (1 / (b : ℚ)) := by
      intro b hb
      have hb1 : 1 ≤ b := (Finset.mem_Icc.mp hb).1
      have hbpos : (0 : ℚ) < (b : ℚ) := hpos b hb
      have he : (∑ a ∈ S, (if b < a then (1 : ℚ) / ((a : ℚ) ^ 2 * (b : ℚ)) else 0))
          = (1 / (b : ℚ)) * (∑ a ∈ S, (if b < a then (1 : ℚ) / ((a : ℚ) ^ 2) else 0)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun a _ => ?_)
        by_cases h : b < a
        · rw [if_pos h, if_pos h, div_mul_div_comm, one_mul, mul_comm]
        · rw [if_neg h, if_neg h, mul_zero]
      have hle : (∑ a ∈ S, (if b < a then (1 : ℚ) / ((a : ℚ) ^ 2) else 0)) ≤ 1 / (b : ℚ) := by
        rw [← Finset.sum_filter]
        rcases Nat.lt_or_ge b x with hbx | hxb
        · have hset : S.filter (fun a => b < a) = Finset.Icc (b + 1) x := by
            rw [hS]
            exact filter_Icc_lt hb1
          rw [hset]
          exact sum_inv_sq_Icc_succ_le hb1 hbx
        · have hempty : S.filter (fun a => b < a) = ∅ := by
            rw [Finset.filter_eq_empty_iff]
            intro a ha
            rw [hS, Finset.mem_Icc] at ha
            omega
          rw [hempty, Finset.sum_empty]
          positivity
      rw [he]
      exact mul_le_mul_of_nonneg_left hle (by positivity)
    refine le_trans (Finset.sum_le_sum hrow) ?_
    calc (∑ b ∈ S, (1 / (b : ℚ)) * (1 / (b : ℚ)))
        = ∑ b ∈ S, (1 : ℚ) / (b : ℚ) ^ 2 := by
          refine Finset.sum_congr rfl (fun b _ => ?_)
          rw [div_mul_div_comm, one_mul, ← sq]
      _ ≤ 2 := by
          rw [hS]
          exact sum_inv_sq_le_two x
  -- 第二段：`a < b`
  have hC : (∑ a ∈ S, ∑ b ∈ S, (if a < b then (1 : ℚ) / ((a : ℚ) * (b : ℚ) ^ 2) else 0))
      ≤ 2 := by
    have hrow : ∀ a ∈ S, (∑ b ∈ S, (if a < b then (1 : ℚ) / ((a : ℚ) * (b : ℚ) ^ 2) else 0))
        ≤ (1 / (a : ℚ)) * (1 / (a : ℚ)) := by
      intro a ha
      have ha1 : 1 ≤ a := (Finset.mem_Icc.mp ha).1
      have hapos : (0 : ℚ) < (a : ℚ) := hpos a ha
      have he : (∑ b ∈ S, (if a < b then (1 : ℚ) / ((a : ℚ) * (b : ℚ) ^ 2) else 0))
          = (1 / (a : ℚ)) * (∑ b ∈ S, (if a < b then (1 : ℚ) / ((b : ℚ) ^ 2) else 0)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun b _ => ?_)
        by_cases h : a < b
        · rw [if_pos h, if_pos h, div_mul_div_comm, one_mul, mul_comm]
        · rw [if_neg h, if_neg h, mul_zero]
      have hle : (∑ b ∈ S, (if a < b then (1 : ℚ) / ((b : ℚ) ^ 2) else 0)) ≤ 1 / (a : ℚ) := by
        rw [← Finset.sum_filter]
        rcases Nat.lt_or_ge a x with hax | hxa
        · have hset : S.filter (fun b => a < b) = Finset.Icc (a + 1) x := by
            rw [hS]
            exact filter_Icc_lt ha1
          rw [hset]
          exact sum_inv_sq_Icc_succ_le ha1 hax
        · have hempty : S.filter (fun b => a < b) = ∅ := by
            rw [Finset.filter_eq_empty_iff]
            intro b hb
            rw [hS, Finset.mem_Icc] at hb
            omega
          rw [hempty, Finset.sum_empty]
          positivity
      rw [he]
      exact mul_le_mul_of_nonneg_left hle (by positivity)
    refine le_trans (Finset.sum_le_sum hrow) ?_
    calc (∑ a ∈ S, (1 / (a : ℚ)) * (1 / (a : ℚ)))
        = ∑ a ∈ S, (1 : ℚ) / (a : ℚ) ^ 2 := by
          refine Finset.sum_congr rfl (fun a _ => ?_)
          rw [div_mul_div_comm, one_mul, ← sq]
      _ ≤ 2 := by
          rw [hS]
          exact sum_inv_sq_le_two x
  -- 第三段：`a = b`
  have hB : (∑ a ∈ S, ∑ b ∈ S, (if a = b then (1 : ℚ) / ((a : ℚ) ^ 3) else 0)) ≤ 2 := by
    have he : ∀ a ∈ S, (∑ b ∈ S, (if a = b then (1 : ℚ) / ((a : ℚ) ^ 3) else 0))
        = (1 : ℚ) / ((a : ℚ) ^ 3) := by
      intro a ha
      rw [Finset.sum_ite_eq]
      rw [if_pos ha]
    rw [Finset.sum_congr rfl he]
    calc (∑ a ∈ S, (1 : ℚ) / ((a : ℚ) ^ 3))
        ≤ ∑ a ∈ S, (1 : ℚ) / ((a : ℚ) ^ 2) := by
          refine Finset.sum_le_sum (fun a ha => ?_)
          have ha1 : 1 ≤ a := (Finset.mem_Icc.mp ha).1
          have hapos : (0 : ℚ) < (a : ℚ) := hpos a ha
          apply one_div_le_one_div_of_le (by positivity)
          have h1 : (1 : ℚ) ≤ (a : ℚ) := by exact_mod_cast ha1
          nlinarith
      _ ≤ 2 := by
          rw [hS]
          exact sum_inv_sq_le_two x
  -- 汇总
  have hstep : (∑ a ∈ S, ∑ b ∈ S, 1 / ((a : ℚ) * (b : ℚ) * max (a : ℚ) (b : ℚ)))
      = ((∑ a ∈ S, ∑ b ∈ S, (if b < a then (1 : ℚ) / ((a : ℚ) ^ 2 * (b : ℚ)) else 0))
          + (∑ a ∈ S, ∑ b ∈ S, (if a < b then (1 : ℚ) / ((a : ℚ) * (b : ℚ) ^ 2) else 0)))
          + (∑ a ∈ S, ∑ b ∈ S, (if a = b then (1 : ℚ) / ((a : ℚ) ^ 3) else 0)) := by
    have hpt : ∀ a ∈ S, ∀ b ∈ S,
        1 / ((a : ℚ) * (b : ℚ) * max (a : ℚ) (b : ℚ))
          = (if b < a then 1 / ((a : ℚ) ^ 2 * (b : ℚ)) else 0)
            + (if a < b then 1 / ((a : ℚ) * (b : ℚ) ^ 2) else 0)
            + (if a = b then 1 / ((a : ℚ) ^ 3) else 0) := by
      intro a ha b hb
      have ha0 : 0 < a := (Finset.mem_Icc.mp ha).1
      have hb0 : 0 < b := (Finset.mem_Icc.mp hb).1
      exact inv_mul_max_split ha0 hb0
    rw [Finset.sum_congr rfl (fun a ha => Finset.sum_congr rfl (fun b hb => hpt a ha b hb))]
    simp only [Finset.sum_add_distrib]
  calc (∑ a ∈ S, ∑ b ∈ S, (Nat.gcd a b : ℚ) / ((a : ℚ) * (b : ℚ)) ^ 2)
      ≤ ∑ a ∈ S, ∑ b ∈ S, 1 / ((a : ℚ) * (b : ℚ) * max (a : ℚ) (b : ℚ)) := by
        refine Finset.sum_le_sum (fun a ha => Finset.sum_le_sum (fun b hb => ?_))
        have ha0 : 0 < a := (Finset.mem_Icc.mp ha).1
        have hb0 : 0 < b := (Finset.mem_Icc.mp hb).1
        exact gcd_div_sq_le ha0 hb0
    _ = _ := hstep
    _ ≤ (2 + 2) + 2 := by linarith [hA, hC, hB]
    _ = 6 := by norm_num

/-- **Lemma 6（平方版）**：`Σ_{n≤x} σ₋₁(n)² ≤ 6x`。 -/
theorem sum_sigmaMinusOne_sq_le (x : ℕ) :
    (∑ n ∈ Finset.Icc 1 x, sigmaMinusOne n ^ 2) ≤ 6 * (x : ℚ) := by
  classical
  rw [sum_sigmaMinusOne_sq_eq]
  have hterm : ∀ a ∈ Finset.Icc 1 x, ∀ b ∈ Finset.Icc 1 x,
      (1 : ℚ) / ((a : ℚ) * (b : ℚ))
          * (((Finset.Icc 1 x).filter (fun n => a ∣ n ∧ b ∣ n)).card : ℚ)
        ≤ (x : ℚ) * ((Nat.gcd a b : ℚ) / ((a : ℚ) * (b : ℚ)) ^ 2) := by
    intro a ha b hb
    have ha0 : 0 < a := (Finset.mem_Icc.mp ha).1
    have hb0 : 0 < b := (Finset.mem_Icc.mp hb).1
    rw [card_multiples_two x a b ha0 hb0]
    have h1 : (0 : ℚ) < (a : ℚ) := by exact_mod_cast ha0
    have h2 : (0 : ℚ) < (b : ℚ) := by exact_mod_cast hb0
    have hl : (0 : ℚ) < (Nat.lcm a b : ℚ) := by exact_mod_cast Nat.lcm_pos ha0 hb0
    calc (1 : ℚ) / ((a : ℚ) * (b : ℚ)) * ((x / Nat.lcm a b : ℕ) : ℚ)
        ≤ (1 : ℚ) / ((a : ℚ) * (b : ℚ)) * ((x : ℚ) / (Nat.lcm a b : ℚ)) := by
          have hx : (((x / Nat.lcm a b : ℕ)) : ℚ) ≤ (x : ℚ) / (Nat.lcm a b : ℚ) :=
            Nat.cast_div_le
          exact mul_le_mul_of_nonneg_left hx (by positivity)
      _ = (1 : ℚ) / ((a : ℚ) * (b : ℚ)) * (1 / (Nat.lcm a b : ℚ)) * (x : ℚ) := by ring
      _ = ((Nat.gcd a b : ℚ) / ((a : ℚ) * (b : ℚ)) ^ 2) * (x : ℚ) := by
          rw [inv_mul_inv_lcm_eq ha0 hb0]
      _ = (x : ℚ) * ((Nat.gcd a b : ℚ) / ((a : ℚ) * (b : ℚ)) ^ 2) := by ring
  calc (∑ a ∈ Finset.Icc 1 x, ∑ b ∈ Finset.Icc 1 x,
          (1 : ℚ) / ((a : ℚ) * (b : ℚ))
            * (((Finset.Icc 1 x).filter (fun n => a ∣ n ∧ b ∣ n)).card : ℚ))
      ≤ ∑ a ∈ Finset.Icc 1 x, ∑ b ∈ Finset.Icc 1 x,
          (x : ℚ) * ((Nat.gcd a b : ℚ) / ((a : ℚ) * (b : ℚ)) ^ 2) :=
        Finset.sum_le_sum (fun a ha => Finset.sum_le_sum (fun b hb => hterm a ha b hb))
    _ = (x : ℚ) * ∑ a ∈ Finset.Icc 1 x, ∑ b ∈ Finset.Icc 1 x,
          (Nat.gcd a b : ℚ) / ((a : ℚ) * (b : ℚ)) ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun a _ => ?_)
        rw [Finset.mul_sum]
    _ ≤ (x : ℚ) * 6 :=
        mul_le_mul_of_nonneg_left (sum_gcd_div_sq_le x) (by positivity)
    _ = 6 * (x : ℚ) := by ring

end Waring
