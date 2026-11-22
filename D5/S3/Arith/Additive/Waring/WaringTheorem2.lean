/- GID: D5/S3/Arith/Additive/Waring/WaringTheorem2
   generality: G
   mirror-B: D5/B/S3/Arith/Additive/Waring/WaringTheorem2
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Third-party formalization of the qualitative Hilbert–Waring theorem. -/

/- Source: https://github.com/yunyougu50-create/waring-lean4/blob/cd0735c253f3b640262fcc74a61306cb41e23765/WaringTheorem2.lean#L1-L489
   Modified for this repository. Local imports use their D5 module paths.
   Selected declaration closure and supporting source.
   Full Apache-2.0 license: D5/S3/Arith/Additive/Waring/WaringDensity.lean. -/

/-
Copyright (c) 2026 The Waring formalization authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Waring formalization authors
-/
import D5.S3.Arith.Additive.Waring.WaringIndStep2
import D5.S3.Arith.Additive.Waring.WaringLinnik

/-!
# Jameson Theorem 2：密度桥（Linnik 证明的最后一块）

设 `s = 8^{k-1}`、`r_s^{(k,M)}(n) = #{(n₁,…,n_s) : 0 ≤ nᵢ ≤ M, Σ nᵢ^k = n}`。
Jameson Theorem 2 断言

```text
#{n ≤ N : n 是至多 s 个 k 次幂之和} ≫ N.
```

本文件把它形式化，路线是标准的圆法三步：

1. **积分表示**（`rCount_eq_integral`）：
   `r(n) = ∫₀¹ S(α)^s e(-nα) dα`，`S(α) = Σ_{m≤M} e(α m^k)`；
2. **绝对值 + Theorem 1**（`rCount_le_integral`、`rCount_le_poly`）：
   `r(n) ≤ ∫₀¹ ‖S‖^{s} dα ≤ C·M^{s−k}`；
3. **计数**（`sum_rCount_ge`）：若 `s·M^k ≤ N`，则 `(M+1)^s ≤ Σ_{n≤N} r(n) + 1`。

由此 `densityCount ≥ (M+1)^s / (2 C M^{s−k}) ≫ N`，密度 `≫ 1`。

最后 `positiveDensity` 与 `waringTheorem_of_positive_density` 给出**完整的 Waring 定理**。
-/

open Finset intervalIntegral

namespace Waring

/-! ## 1. 表示数与指数和 -/

/-- `[0,M]` 中 `s` 个 `k` 次幂之和等于 `n` 的表示数。 -/
noncomputable def rCount (k s M n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin s → Fin (M + 1))).filter
    (fun f => ∑ i, (f i).val ^ k = n)).card

/-- 圆法中的指数和 `S(α) = Σ_{m ≤ M} e(α m^k)`。 -/
noncomputable def powSum (k M : ℕ) (α : ℝ) : ℂ :=
  ∑ m : Fin (M + 1), e (((m : ℕ) : ℝ) ^ k * α)

/-! ## 2. `S(α)^s` 的单层展开 -/

/-- `(S(α))^s` 展开成 `Fin s → Fin (M+1)` 上的单层和（`Fintype.sum_pow`）。 -/
theorem powSum_pow (k s M : ℕ) (α : ℝ) :
    powSum k M α ^ s
      = ∑ p : Fin s → Fin (M + 1), e (((∑ i, (p i).val ^ k : ℕ) : ℝ) * α) := by
  unfold powSum
  rw [Fintype.sum_pow]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [← e_sum_mul (Fin s) (fun i => ((p i).val : ℝ) ^ k) α]
  congr 1
  push_cast
  ring

/-! ## 3. 积分表示（正交性） -/

/-- **正交性积分表示**：`r(n) = ∫₀¹ S(α)^s e(-nα) dα`。 -/
theorem rCount_eq_integral (k s M n : ℕ) :
    (rCount k s M n : ℂ)
      = ∫ α in (0 : ℝ)..1, powSum k M α ^ s * e (-((n : ℝ) * α)) := by
  classical
  have hpt : ∀ α : ℝ, powSum k M α ^ s * e (-((n : ℝ) * α))
      = ∑ p : Fin s → Fin (M + 1),
          e ((((∑ i, ((p i).val : ℤ) ^ k) - (n : ℤ) : ℤ) : ℝ) * α) := by
    intro α
    rw [powSum_pow, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [← e_add]
    congr 1
    push_cast
    ring
  simp only [hpt]
  have hstep : ∀ p : Fin s → Fin (M + 1),
      (∫ α in (0 : ℝ)..1, e ((((∑ i, ((p i).val : ℤ) ^ k) - (n : ℤ) : ℤ) : ℝ) * α))
        = if (∑ i, (p i).val ^ k) = n then (1 : ℂ) else 0 := by
    intro p
    rw [integral_e_mul_int]
    have hcast : ((∑ i, (p i).val ^ k : ℕ) : ℤ) = ∑ i, ((p i).val : ℤ) ^ k := by
      push_cast
      ring
    by_cases h : (∑ i, (p i).val ^ k) = n
    · have hm0 : (∑ i, ((p i).val : ℤ) ^ k) - (n : ℤ) = 0 := by
        rw [← hcast, h]
        simp
      simp [h, hm0]
    · have hm0 : (∑ i, ((p i).val : ℤ) ^ k) - (n : ℤ) ≠ 0 := by
        rw [← hcast]
        intro hz
        apply h
        have h2 : ((∑ i, (p i).val ^ k : ℕ) : ℤ) = (n : ℤ) := by linarith
        exact_mod_cast h2
      simp [h, hm0]
  rw [intervalIntegral.integral_finsetSum]
  · rw [Finset.sum_congr rfl (fun p _ => hstep p)]
    rw [Finset.sum_boole, rCount]
  · intro p _
    exact Continuous.intervalIntegrable (continuous_e_comp _) 0 1

/-- **绝对值不等式**：`r(n) ≤ ∫₀¹ ‖S(α)‖^s dα`。 -/
theorem rCount_le_integral (k s M n : ℕ) :
    (rCount k s M n : ℝ) ≤ ∫ α in (0 : ℝ)..1, ‖powSum k M α‖ ^ s := by
  have hC := rCount_eq_integral k s M n
  have h1 : (rCount k s M n : ℝ)
      = ‖∫ α in (0 : ℝ)..1, powSum k M α ^ s * e (-((n : ℝ) * α))‖ := by
    rw [← hC]
    simp
  rw [h1]
  refine le_trans (intervalIntegral.norm_integral_le_integral_norm (show (0 : ℝ) ≤ 1 by norm_num)) ?_
  refine le_of_eq ?_
  apply intervalIntegral.integral_congr
  intro α _
  show ‖powSum k M α ^ s * e (-((n : ℝ) * α))‖ = ‖powSum k M α‖ ^ s
  rw [norm_mul, norm_pow, norm_e, mul_one]

/-! ## 4. 接到 Jameson Theorem 1 -/

/-- 系数向量：单项式 `n ↦ n^k`。 -/
def aPow (k : ℕ) : ℕ → ℤ := fun j => if j = k then (1 : ℤ) else 0

/-- `polyEval (aPow k) k n = n^k`。 -/
theorem polyEval_aPow (k : ℕ) (n : ℤ) : polyEval (aPow k) k n = n ^ k := by
  unfold polyEval aPow
  refine (Finset.sum_eq_single k ?_ ?_).trans ?_
  · intro j _ hj
    simp [hj]
  · intro hk
    exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self k)) hk
  · simp

/-- `expSum` 与 `powSum` 是同一个和。 -/
theorem expSum_aPow_eq_powSum (k M : ℕ) (α : ℝ) :
    expSum (fun n => polyEval (aPow k) k n) M α = powSum k M α := by
  unfold expSum powSum
  rw [Fin.sum_univ_eq_sum_range (f := fun m : ℕ => e (((m : ℝ) ^ k) * α)) (n := M + 1)]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  have hb : (fun n => polyEval (aPow k) k n) ((m : ℕ) : ℤ) = polyEval (aPow k) k ((m : ℕ) : ℤ) :=
    rfl
  rw [hb, polyEval_aPow]
  congr 1
  push_cast
  ring

/-- **表示数的上界**（`k ≥ 2`，`s = 8^{k−1}`）：`r(n) ≤ C·M^{s−k}`。 -/
theorem rCount_le_poly {k : ℕ} (hk : 2 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M n : ℕ), 1 ≤ M →
      (rCount k (8 ^ (k - 1)) M n : ℝ) ≤ C * (M : ℝ) ^ (8 ^ (k - 1) - k) := by
  classical
  obtain ⟨R, hRpos, hRb⟩ := meanValueBound_all k hk
  refine ⟨R 1, hRpos 1, ?_⟩
  intro M n hM
  have hcoeff : ∀ j, j ≤ k → |aPow k j| ≤ ((1 : ℕ) : ℤ) * (M : ℤ) ^ (k - j) := by
    intro j hj
    by_cases hjk : j = k
    · rw [hjk]
      simp [aPow]
    · have hz : aPow k j = 0 := by simp [aPow, hjk]
      rw [hz, abs_zero]
      positivity
  have had : aPow k k ≠ 0 := by simp [aPow]
  have hInt := hRb 1 M hM (aPow k) had hcoeff
  calc (rCount k (8 ^ (k - 1)) M n : ℝ)
      ≤ ∫ α in (0 : ℝ)..1, ‖powSum k M α‖ ^ (8 ^ (k - 1)) :=
        rCount_le_integral k (8 ^ (k - 1)) M n
    _ = ∫ α in (0 : ℝ)..1,
          ‖expSum (fun n => polyEval (aPow k) k n) M α‖ ^ (8 ^ (k - 1)) := by
        apply intervalIntegral.integral_congr
        intro α _
        show ‖powSum k M α‖ ^ (8 ^ (k - 1))
            = ‖expSum (fun n => polyEval (aPow k) k n) M α‖ ^ (8 ^ (k - 1))
        rw [expSum_aPow_eq_powSum]
    _ ≤ R 1 * (M : ℝ) ^ (8 ^ (k - 1) - k) := hInt

/-! ## 5. 计数的下界 -/

/-- `r(0) ≤ 1`：只有全零向量贡献。 -/
theorem rCount_zero_le_one (k s M : ℕ) (hk : 1 ≤ k) : rCount k s M 0 ≤ 1 := by
  classical
  have hsub : (Finset.univ : Finset (Fin s → Fin (M + 1))).filter
      (fun f => ∑ i, (f i).val ^ k = 0) ⊆ {(fun _ => (0 : Fin (M + 1)))} := by
    intro f hf
    rw [Finset.mem_filter] at hf
    obtain ⟨_, hf0⟩ := hf
    rw [Finset.mem_singleton]
    funext i
    have hterm : (f i).val ^ k = 0 := by
      have hle : (f i).val ^ k ≤ ∑ j : Fin s, (f j).val ^ k :=
        Finset.single_le_sum (f := fun j => (f j).val ^ k) (fun j _ => Nat.zero_le _)
          (Finset.mem_univ i)
      omega
    have hval : (f i).val = 0 := by
      have hk0 : k ≠ 0 := by omega
      exact (pow_eq_zero_iff hk0).mp hterm
    exact Fin.ext (by simpa using hval)
  have hc := Finset.card_le_card hsub
  rwa [Finset.card_singleton] at hc

/-- **计数下界**：若 `s·M^k ≤ N`，则 `(M+1)^s ≤ Σ_{1≤n≤N} r(n) + 1`。 -/
theorem sum_rCount_ge (k s M N : ℕ) (hk : 1 ≤ k) (hNM : s * M ^ k ≤ N) :
    (M + 1) ^ s ≤ (∑ n ∈ Finset.Icc 1 N, rCount k s M n) + 1 := by
  classical
  set U : Finset (Fin s → Fin (M + 1)) := Finset.univ with hU
  have hmaps : ∀ f : Fin s → Fin (M + 1), f ∈ U →
      (∑ i, (f i).val ^ k) ∈ Finset.range (N + 1) := by
    intro f _
    rw [Finset.mem_range]
    have h1 : ∀ i : Fin s, (f i).val ≤ M := fun i => by
      have := (f i).isLt
      omega
    have h3 : (∑ i : Fin s, (f i).val ^ k) ≤ ∑ _i : Fin s, M ^ k :=
      Finset.sum_le_sum (fun i _ => pow_le_pow_left₀ (Nat.zero_le _) (h1 i) k)
    have h4 : (∑ _i : Fin s, M ^ k) = s * M ^ k := by
      simp [Finset.sum_const, Finset.card_univ]
    omega
  have htotal : (∑ n ∈ Finset.range (N + 1), rCount k s M n) = (M + 1) ^ s := by
    have hfib := Finset.sum_fiberwise_of_maps_to (s := U) (t := Finset.range (N + 1))
      (g := fun f : Fin s → Fin (M + 1) => ∑ i, (f i).val ^ k)
      (f := fun _ => (1 : ℕ)) hmaps
    have hterm : ∀ n ∈ Finset.range (N + 1),
        rCount k s M n = (∑ x ∈ U with (∑ i, (x i).val ^ k) = n, (1 : ℕ)) := by
      intro n _
      have h1 : rCount k s M n
          = ((Finset.univ : Finset (Fin s → Fin (M + 1))).filter
              (fun f => ∑ i, (f i).val ^ k = n)).card := rfl
      have h2 : (∑ x ∈ U with (∑ i, (x i).val ^ k) = n, (1 : ℕ))
          = (U.filter (fun x => (∑ i, (x i).val ^ k) = n)).card :=
        (Finset.card_eq_sum_ones _).symm
      rw [h1, h2, hU]
    rw [Finset.sum_congr rfl hterm, hfib]
    rw [hU, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    simp
  have hmem0 : (0 : ℕ) ∈ Finset.range (N + 1) := Finset.mem_range.mpr (Nat.succ_pos N)
  have herase : (Finset.range (N + 1)).erase 0 = Finset.Icc 1 N := by
    ext j
    simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_Icc]
    omega
  have hsplit : (∑ n ∈ Finset.range (N + 1), rCount k s M n)
      = rCount k s M 0 + ∑ n ∈ Finset.Icc 1 N, rCount k s M n := by
    rw [← Finset.sum_erase_add (s := Finset.range (N + 1))
      (f := fun n => rCount k s M n) hmem0, herase, add_comm]
  have hz1 : rCount k s M 0 ≤ 1 := rCount_zero_le_one k s M hk
  omega

/-! ## 6. 密度桥（`k ≥ 2`） -/

/-- **Jameson Theorem 2（`k ≥ 2`）**：至多 `s = 8^{k−1}` 个 `k` 次幂之和的集合有正密度。 -/
theorem positiveDensity_k {k : ℕ} (hk : 2 ≤ k) :
    ∃ s : ℕ, ∃ δ : ℚ, 0 < δ ∧
      HasDensity {n : ℕ | ∃ t ≤ s, IsSumOfKthPowers k n t} δ := by
  classical
  obtain ⟨C, hCpos, hC⟩ := rCount_le_poly hk
  have hk1 : 1 ≤ k := by omega
  set s : ℕ := 8 ^ (k - 1) with hs
  have hs1 : 1 ≤ s := by rw [hs]; exact Nat.one_le_pow _ _ (by norm_num)
  have hks : k ≤ s := by
    rw [hs]
    have h1 : k < 2 ^ k := Nat.lt_two_pow_self
    have h2 : 2 ^ k ≤ 8 ^ (k - 1) := by
      rw [show (8 : ℕ) = 2 ^ 3 by norm_num, ← pow_mul]
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    exact le_trans (le_of_lt h1) h2
  set K : ℕ := Nat.ceil C + 1 with hK
  have hK1 : 1 ≤ K := by rw [hK]; omega
  have hKC : C ≤ (K : ℝ) := by
    have h1 : C ≤ ((Nat.ceil C : ℕ) : ℝ) := Nat.le_ceil C
    have h2 : ((Nat.ceil C : ℕ) : ℝ) ≤ (Nat.ceil C + 1 : ℕ) := by
      push_cast
      linarith
    rw [hK]
    linarith
  set A : Set ℕ := {n : ℕ | ∃ t ≤ s, IsSumOfKthPowers k n t} with hA
  have hC' : ∀ (M n : ℕ), 1 ≤ M → (rCount k s M n : ℝ) ≤ C * (M : ℝ) ^ (s - k) := by
    intro M n hM
    rw [hs]
    exact hC M n hM
  have hDpos : 0 < 2 * (s * K) := by
    have h2 : 0 < s * K := Nat.mul_pos (by omega) hK1
    omega
  refine ⟨s, 1 / ((2 * (s * K) : ℕ) : ℚ), ?_, ?_⟩
  · have hq : (0 : ℚ) < ((2 * (s * K) : ℕ) : ℚ) := by exact_mod_cast hDpos
    exact div_pos one_pos hq
  · intro N hN
    by_cases hNs : N ≤ s
    · -- 小 `N`：`[1,N] ⊆ A`，故 `densityCount = N`
      have hsub : ∀ m ∈ Finset.Icc 1 N, m ∈ A := by
        intro m hm
        rw [Finset.mem_Icc] at hm
        obtain ⟨hm1, hmN⟩ := hm
        rw [hA]
        exact ⟨m, le_trans hmN hNs, fun _ => 1, by simp⟩
      have hdc : densityCount A N = N := by
        unfold densityCount
        rw [Finset.filter_congr_decidable]
        have h2 : ((Finset.Icc 1 N).filter (fun m => m ∈ A)).card = (Finset.Icc 1 N).card := by
          congr 1
          exact Finset.filter_true_of_mem hsub
        have h3 : (Finset.Icc 1 N).card = N := by simp
        rw [h2, h3]
      rw [hdc]
      have hdle : (1 / ((2 * (s * K) : ℕ) : ℚ)) ≤ 1 := by
        rw [div_le_one (by exact_mod_cast hDpos)]
        have h2 : (1 : ℕ) ≤ 2 * (s * K) := by omega
        exact_mod_cast h2
      calc (1 / ((2 * (s * K) : ℕ) : ℚ)) * (N : ℚ) ≤ 1 * (N : ℚ) :=
            mul_le_mul_of_nonneg_right hdle (Nat.cast_nonneg N)
        _ = (N : ℚ) := by ring
    · -- 大 `N`：取最大的 `M` 使 `s·M^k ≤ N`
      simp only [not_le] at hNs
      set M : ℕ := Nat.findGreatest (fun m => s * m ^ k ≤ N) N with hMdef
      have hMs : s * M ^ k ≤ N := by
        have hp0 : s * 0 ^ k ≤ N := by
          rw [Nat.zero_pow (by omega : 0 < k), mul_zero]
          exact Nat.zero_le N
        have hspec := Nat.findGreatest_spec (P := fun m => s * m ^ k ≤ N) (m := 0) (n := N)
          (Nat.zero_le N) hp0
        simpa [hMdef] using hspec
      have hM1 : 1 ≤ M := by
        by_contra hcon
        have hlt : M < 1 := by omega
        have hnp := Nat.findGreatest_is_greatest (P := fun m => s * m ^ k ≤ N) (n := N)
          (k := 1) (hMdef ▸ hlt) (by omega : 1 ≤ N)
        exact hnp (by simpa using le_of_lt hNs)
      have hMltN : M < N := by
        rcases Nat.lt_or_ge M N with h | h
        · exact h
        · exfalso
          have hMle : M ≤ N := Nat.findGreatest_le N
          have hMeq : M = N := by omega
          rw [hMeq] at hMs
          have hN2 : 2 ≤ N := by omega
          have h1 : N < N ^ 2 := by
            have h2 : (1 : ℕ) < N := by omega
            calc N = N * 1 := (Nat.mul_one N).symm
              _ < N * N := Nat.mul_lt_mul_of_pos_left h2 (by omega : 0 < N)
              _ = N ^ 2 := by ring
          have h2 : N ^ 2 ≤ N ^ k := pow_le_pow_right₀ (by omega : 1 ≤ N) hk
          have h3 : N ^ k ≤ s * N ^ k := by
            calc N ^ k = 1 * N ^ k := (one_mul _).symm
              _ ≤ s * N ^ k := Nat.mul_le_mul_right _ hs1
          omega
      have hMup : N < s * (M + 1) ^ k := by
        have hnp := Nat.findGreatest_is_greatest (P := fun m => s * m ^ k ≤ N) (n := N)
          (k := M + 1) (by omega) (by omega : M + 1 ≤ N)
        omega
      -- (i) 下界
      have hlow : ((M : ℝ) + 1) ^ s
          ≤ (∑ n ∈ Finset.Icc 1 N, (rCount k s M n : ℝ)) + 1 := by
        have h := sum_rCount_ge k s M N hk1 hMs
        exact_mod_cast h
      -- (ii) 上界
      have hup : (∑ n ∈ Finset.Icc 1 N, (rCount k s M n : ℝ))
          ≤ ((densityCount A N : ℕ) : ℝ) * (C * (M : ℝ) ^ (s - k)) := by
        have hterm : ∀ n ∈ Finset.Icc 1 N, (rCount k s M n : ℝ)
            ≤ if n ∈ A then C * (M : ℝ) ^ (s - k) else 0 := by
          intro n _
          by_cases hAn : n ∈ A
          · simp only [hAn, ite_true]
            exact hC' M n hM1
          · simp only [hAn, ite_false]
            have hz : rCount k s M n = 0 := by
              rw [rCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
              intro f _ hf
              refine hAn ?_
              rw [hA]
              exact ⟨s, le_rfl, fun i => (f i).val, hf.symm⟩
            rw [hz]
            simp
        refine le_trans (Finset.sum_le_sum hterm) (le_of_eq ?_)
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
        rw [show densityCount A N = ((Finset.Icc 1 N).filter (fun n => n ∈ A)).card from by
          unfold densityCount
          rw [Finset.filter_congr_decidable]]
      have hmain : ((M : ℝ) + 1) ^ s
          ≤ ((densityCount A N : ℕ) : ℝ) * (C * (M : ℝ) ^ (s - k)) + 1 := by
        linarith
      -- (iii) `(M+1)^s ≥ 4`
      have h4 : (4 : ℝ) ≤ ((M : ℝ) + 1) ^ s := by
        have hMp : (2 : ℝ) ≤ (M : ℝ) + 1 := by
          have h1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM1
          linarith
        have hs2 : 2 ≤ s := by omega
        calc (4 : ℝ) = 2 ^ 2 := by norm_num
          _ ≤ ((M : ℝ) + 1) ^ 2 := pow_le_pow_left₀ (by norm_num) hMp 2
          _ ≤ ((M : ℝ) + 1) ^ s := pow_le_pow_right₀ (by linarith) hs2
      have hDC0 : (0 : ℝ) ≤ ((densityCount A N : ℕ) : ℝ) := by positivity
      have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
      have hFpos : (0 : ℝ) < (M : ℝ) ^ (s - k) := pow_pos hMpos _
      -- (iv) `(M+1)^k ≤ 2·DC·C`
      have hkey : ((M : ℝ) + 1) ^ k ≤ 2 * (((densityCount A N : ℕ) : ℝ) * C) := by
        have hfac : ((M : ℝ) + 1) ^ s = ((M : ℝ) + 1) ^ k * ((M : ℝ) + 1) ^ (s - k) := by
          rw [← pow_add, Nat.add_sub_of_le hks]
        have hle1 : (M : ℝ) ^ (s - k) ≤ ((M : ℝ) + 1) ^ (s - k) :=
          pow_le_pow_left₀ (le_of_lt hMpos) (by linarith) _
        have hstep : ((M : ℝ) + 1) ^ k * (M : ℝ) ^ (s - k) ≤ ((M : ℝ) + 1) ^ s := by
          rw [hfac]
          exact mul_le_mul_of_nonneg_left hle1 (by positivity)
        have h2F : ((densityCount A N : ℕ) : ℝ) * (C * (M : ℝ) ^ (s - k)) + 1
            ≤ 2 * (((densityCount A N : ℕ) : ℝ) * (C * (M : ℝ) ^ (s - k))) := by
          linarith
        have h3 : ((M : ℝ) + 1) ^ k * (M : ℝ) ^ (s - k)
            ≤ 2 * (((densityCount A N : ℕ) : ℝ) * (C * (M : ℝ) ^ (s - k))) :=
          le_trans hstep (le_trans hmain h2F)
        refine le_of_mul_le_mul_right ?_ hFpos
        calc ((M : ℝ) + 1) ^ k * (M : ℝ) ^ (s - k)
            ≤ 2 * (((densityCount A N : ℕ) : ℝ) * (C * (M : ℝ) ^ (s - k))) := h3
          _ = (2 * (((densityCount A N : ℕ) : ℝ) * C)) * (M : ℝ) ^ (s - k) := by ring
      -- (v) `N ≤ 2·s·K·DC`
      have hNle : (N : ℝ) ≤ 2 * (s : ℝ) * (K : ℝ) * ((densityCount A N : ℕ) : ℝ) := by
        have h1 : (N : ℝ) < (s : ℝ) * ((M : ℝ) + 1) ^ k := by
          have h2 : ((s * (M + 1) ^ k : ℕ) : ℝ) = (s : ℝ) * ((M : ℝ) + 1) ^ k := by
            push_cast
            ring
          rw [← h2]
          exact_mod_cast hMup
        have h2 : (s : ℝ) * ((M : ℝ) + 1) ^ k
            ≤ (s : ℝ) * (2 * (((densityCount A N : ℕ) : ℝ) * C)) :=
          mul_le_mul_of_nonneg_left hkey (by positivity)
        have h3 : (s : ℝ) * (2 * (((densityCount A N : ℕ) : ℝ) * C))
            ≤ 2 * (s : ℝ) * (K : ℝ) * ((densityCount A N : ℕ) : ℝ) := by
          have hs0 : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs1
          nlinarith [hKC, hDC0, hs0]
        linarith
      -- (vi) 转成 `ℚ`
      have hq : (N : ℚ) ≤ ((2 * (s * K) * densityCount A N : ℕ) : ℚ) := by
        have hR : (N : ℝ) ≤ ((2 * (s * K) * densityCount A N : ℕ) : ℝ) := by
          have hcast2 : ((2 * (s * K) * densityCount A N : ℕ) : ℝ)
              = 2 * (s : ℝ) * (K : ℝ) * ((densityCount A N : ℕ) : ℝ) := by
            push_cast
            ring
          linarith
        exact_mod_cast hR
      have hd : (0 : ℚ) < ((2 * (s * K) : ℕ) : ℚ) := by exact_mod_cast hDpos
      rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hd]
      calc (N : ℚ) ≤ ((2 * (s * K) * densityCount A N : ℕ) : ℚ) := hq
        _ = (densityCount A N : ℚ) * ((2 * (s * K) : ℕ) : ℚ) := by push_cast; ring

/-! ## 7. `k = 1` 的基例 -/

/-- **`k = 1`**：每个自然数都是 `1 = 1^1` 个一次幂之和，密度为 `1`。 -/
theorem positiveDensity_one :
    ∃ s : ℕ, ∃ δ : ℚ, 0 < δ ∧
      HasDensity {n : ℕ | ∃ t ≤ s, IsSumOfKthPowers 1 n t} δ := by
  classical
  set A : Set ℕ := {n : ℕ | ∃ t ≤ 1, IsSumOfKthPowers 1 n t} with hA
  refine ⟨1, 1 / 2, by norm_num, ?_⟩
  intro N hN
  have hsub : ∀ m ∈ Finset.Icc 1 N, m ∈ A := by
    intro m _
    rw [hA]
    exact ⟨1, le_rfl, fun _ => m, by simp⟩
  have hdc : densityCount A N = N := by
    unfold densityCount
    rw [Finset.filter_congr_decidable]
    have h2 : ((Finset.Icc 1 N).filter (fun m => m ∈ A)).card = (Finset.Icc 1 N).card := by
      congr 1
      exact Finset.filter_true_of_mem hsub
    have h3 : (Finset.Icc 1 N).card = N := by simp
    rw [h2, h3]
  rw [hdc]
  have h0 : (0 : ℚ) ≤ (N : ℚ) := Nat.cast_nonneg N
  nlinarith

/-! ## 8. 组装：Jameson Theorem 2 与完整的 Waring 定理 -/

/-- **Jameson Theorem 2（密度桥）**。 -/
theorem positiveDensity (k : ℕ) (hk : 0 < k) :
    ∃ s : ℕ, ∃ δ : ℚ, 0 < δ ∧
      HasDensity {n : ℕ | ∃ t ≤ s, IsSumOfKthPowers k n t} δ := by
  rcases Nat.eq_or_lt_of_le (show 1 ≤ k by omega) with h | h
  · rw [← h]
    exact positiveDensity_one
  · exact positiveDensity_k h

/-- **Waring 定理**（Hilbert 1909；此处走 Linnik 的密度路线）。 -/
theorem waringTheorem : WaringTheorem :=
  waringTheorem_of_positive_density positiveDensity

end Waring

/-! ## 交付检查 -/
