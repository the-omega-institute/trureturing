/- GID: D5/S3/Arith/Additive/Waring/WaringLemma8Form
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Third-party formalization of the qualitative Hilbert–Waring theorem. -/

/- Source: https://github.com/yunyougu50-create/waring-lean4/blob/cd0735c253f3b640262fcc74a61306cb41e23765/WaringLemma8Form.lean#L1-L327
   Modified for this repository. Local imports use their D5 module paths.
   Full Apache-2.0 license: D5/S3/Arith/Additive/Waring/WaringStatement.lean. -/

/-
Copyright (c) 2026 The Waring formalization authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Waring formalization authors
-/
import D5.S3.Arith.Additive.Waring.WaringQuadratic

/-!
# Jameson Lemma 8（`k = 2`）：常数精细形式

`WaringQuadratic.sum_qQ_sq_le` 给出的界是

```text
Σ_{|n| ≤ K} qQ(n)² ≤ 10⁶ · (2|a| + |b| + 1) · N⁶,
```

其中 `K = qK a b N = 4N²|a| + 2N|b|`。当 `|b| ~ N` 时因子 `(2|a| + |b| + 1)`
本身就是 `N` 的量级，界退化为 `N⁷`，无法用于 Weyl 归纳（那里需要
`|a| ≤ c₂`、`|b| ≤ c₁N` 时界是 `C(c₁,c₂)·N⁶`，而 `C` 与 `N` 无关）。

本文件重新走一遍常数账，把界**只写成 `K` 的函数**：

```text
Σ_{|n| ≤ K} qQ(n)² ≤ 10000 · K · N⁴.
```

常数账（`A = 4N(N+1) ≤ 8N²`、`B = 16N²`、`K = qK a b N ≥ 4N²`）：

```text
(2K+1)·A²          ≤ 3K · 64N⁴      = 192  · K·N⁴
2AB·(4K)           ≤ 8·(128N⁴)·K    = 1024 · K·N⁴
B²·(12K)           ≤ 256N⁴·12K      = 3072 · K·N⁴
qQ(0)²             ≤ 1089N⁶ ≤ 273·K·N⁴
----------------------------------------------
总计                                 ≤ 4561 · K·N⁴ ≤ 10000 · K·N⁴.
```

代入 `K ≤ (4c₂ + 2c₁)·N²`（由 `|a| ≤ c₂`、`|b| ≤ c₁N`）即得

```text
qEqCount a b N ≤ C(c₁,c₂)·N⁶.
```
-/

open Finset intervalIntegral

set_option maxHeartbeats 2000000

namespace Waring

/-! ## 第一部分：`qK` 的下界与上界 -/

/-- **`qK` 的下界**：`a ≠ 0` 时 `4N² ≤ qK a b N`。 -/
theorem qK_ge (a b : ℤ) (ha : a ≠ 0) (N : ℕ) : 4 * (N : ℤ) ^ 2 ≤ qK a b N := by
  have ha1 : (1 : ℤ) ≤ (a.natAbs : ℤ) := by
    have h : 1 ≤ a.natAbs := Nat.succ_le_of_lt (Int.natAbs_pos.mpr ha)
    exact_mod_cast h
  have h1 : 4 * (N : ℤ) ^ 2 * 1 ≤ 4 * (N : ℤ) ^ 2 * (a.natAbs : ℤ) :=
    mul_le_mul_of_nonneg_left ha1 (by positivity)
  have h2 : (0 : ℤ) ≤ 2 * (N : ℤ) * (b.natAbs : ℤ) := by positivity
  unfold qK
  linarith

/-- **`qK` 的上界**：`|a| ≤ c₂`、`|b| ≤ c₁N` 时 `qK ≤ (4c₂ + 2c₁)·N²`。 -/
theorem qK_le_form (a b : ℤ) (c₁ c₂ : ℕ) (N : ℕ)
    (ha2 : a.natAbs ≤ c₂) (hb1 : b.natAbs ≤ c₁ * N) :
    qK a b N ≤ (4 * (c₂ : ℤ) + 2 * (c₁ : ℤ)) * (N : ℤ) ^ 2 := by
  have h1 : |a| ≤ (c₂ : ℤ) := by
    rw [Int.abs_eq_natAbs]
    exact_mod_cast ha2
  have h2 : |b| ≤ (c₁ : ℤ) * (N : ℤ) := by
    have h : (b.natAbs : ℤ) ≤ ((c₁ * N : ℕ) : ℤ) := by exact_mod_cast hb1
    push_cast at h
    exact h
  have h3 : 4 * (N : ℤ) ^ 2 * |a| ≤ 4 * (N : ℤ) ^ 2 * (c₂ : ℤ) :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  have h4 : 2 * (N : ℤ) * |b| ≤ 2 * (N : ℤ) * ((c₁ : ℤ) * (N : ℤ)) :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  have h6 : (4 * (c₂ : ℤ) + 2 * (c₁ : ℤ)) * (N : ℤ) ^ 2
      = 4 * (c₂ : ℤ) * (N : ℤ) ^ 2 + 2 * (c₁ : ℤ) * (N : ℤ) ^ 2 := by ring
  rw [h6]
  unfold qK
  rw [show (a.natAbs : ℤ) = |a| from (Int.abs_eq_natAbs a).symm,
    show (b.natAbs : ℤ) = |b| from (Int.abs_eq_natAbs b).symm]
  linarith

/-! ## 第二部分：`Σ qQ² ≤ C·K·N⁴`（只依赖 `K` 本身） -/

/-- **常数精细的 `Σ qQ²` 界**：`Σ_{|n| ≤ K} qQ(n)² ≤ 10000 · K · N⁴`，
其中 `K = qK a b N`。 -/
theorem sum_qQ_sq_le_K (a b : ℤ) (ha : a ≠ 0) (N : ℕ) (hN : 1 ≤ N) :
    ((∑ n ∈ Finset.Icc (-(qK a b N)) (qK a b N), qQ a b N (2 * N) n ^ 2 : ℕ) : ℚ)
      ≤ 10000 * (qK a b N : ℚ) * (N : ℚ) ^ 4 := by
  classical
  have hNq : (1 : ℚ) ≤ (N : ℚ) := by exact_mod_cast hN
  set A : ℚ := 4 * (N : ℚ) * ((N : ℚ) + 1) with hA
  set B : ℚ := 16 * (N : ℚ) ^ 2 with hB
  set Kz : ℤ := qK a b N with hKz
  have hKz0 : 0 ≤ Kz := by rw [hKz]; exact qK_nonneg a b N
  have hKzq : (0 : ℚ) ≤ (Kz : ℚ) := by exact_mod_cast hKz0
  have hKz_ge : 4 * (N : ℚ) ^ 2 ≤ (Kz : ℚ) := by
    have h := qK_ge a b ha N
    rw [hKz]
    have h' : ((4 * (N : ℤ) ^ 2 : ℤ) : ℚ) ≤ ((qK a b N : ℤ) : ℚ) := by exact_mod_cast h
    push_cast at h'
    exact h'
  have hAnn : (0 : ℚ) ≤ A := by rw [hA]; positivity
  have hBnn : (0 : ℚ) ≤ B := by rw [hB]; positivity
  -- 1) cast 与分拆
  have hcast : ((∑ n ∈ Finset.Icc (-Kz) Kz, qQ a b N (2 * N) n ^ 2 : ℕ) : ℚ)
      = ∑ n ∈ Finset.Icc (-Kz) Kz, (qQ a b N (2 * N) n : ℚ) ^ 2 := by
    push_cast
    ring
  have h0mem : (0 : ℤ) ∈ Finset.Icc (-Kz) Kz := by
    rw [Finset.mem_Icc]
    constructor <;> omega
  have hsplit : (∑ n ∈ Finset.Icc (-Kz) Kz, (qQ a b N (2 * N) n : ℚ) ^ 2)
      = (qQ a b N (2 * N) 0 : ℚ) ^ 2
        + ∑ n ∈ (Finset.Icc (-Kz) Kz).erase 0, (qQ a b N (2 * N) n : ℚ) ^ 2 := by
    rw [add_comm]
    exact (Finset.sum_erase_add _ _ h0mem).symm
  -- 2) n = 0 项
  have hQ0 : (qQ a b N (2 * N) 0 : ℚ) ^ 2 ≤ 1089 * (N : ℚ) ^ 6 := by
    have h1 : qQ a b N (2 * N) 0 ≤ (2 * N + 1) ^ 2 + 4 * N * (N + 1) * (2 * N + 1) :=
      qQ_zero_le a b ha N (2 * N)
    have h2 : (2 * N + 1) ^ 2 + 4 * N * (N + 1) * (2 * N + 1) ≤ 33 * N ^ 3 := by
      have h3 : (2 * (N : ℚ) + 1) ^ 2 + 4 * (N : ℚ) * ((N : ℚ) + 1) * (2 * (N : ℚ) + 1)
          ≤ 33 * (N : ℚ) ^ 3 := by
        nlinarith [hNq]
      exact_mod_cast h3
    have h4 : (qQ a b N (2 * N) 0 : ℚ) ≤ 33 * (N : ℚ) ^ 3 := by
      have h5 : qQ a b N (2 * N) 0 ≤ 33 * N ^ 3 := le_trans h1 h2
      exact_mod_cast h5
    calc (qQ a b N (2 * N) 0 : ℚ) ^ 2 ≤ (33 * (N : ℚ) ^ 3) ^ 2 :=
          pow_le_pow_left₀ (by positivity) h4 2
      _ = 1089 * (N : ℚ) ^ 6 := by ring
  -- 3) 其余项 ≤ Σ (A + Bσ)²
  have hrest : (∑ n ∈ (Finset.Icc (-Kz) Kz).erase 0, (qQ a b N (2 * N) n : ℚ) ^ 2)
      ≤ ∑ n ∈ Finset.Icc (-Kz) Kz, (A + B * sigmaMinusOne n.natAbs) ^ 2 := by
    have h1 : (∑ n ∈ (Finset.Icc (-Kz) Kz).erase 0, (qQ a b N (2 * N) n : ℚ) ^ 2)
        ≤ ∑ n ∈ (Finset.Icc (-Kz) Kz).erase 0, (A + B * sigmaMinusOne n.natAbs) ^ 2 := by
      refine Finset.sum_le_sum (fun n hn => ?_)
      rw [Finset.mem_erase] at hn
      obtain ⟨hn0, -⟩ := hn
      have hq := qQ_le_sigma a b ha N (2 * N) hn0
      have hAs : 4 * (N : ℚ) * ((N : ℚ) + 1) = A := by rw [hA]
      have hBs : 8 * (N : ℚ) * ((2 * N : ℕ) : ℚ) = B := by
        rw [hB]
        push_cast
        ring
      rw [hAs, hBs] at hq
      exact pow_le_pow_left₀ (by positivity) hq 2
    have h2 : (∑ n ∈ (Finset.Icc (-Kz) Kz).erase 0, (A + B * sigmaMinusOne n.natAbs) ^ 2)
        ≤ ∑ n ∈ Finset.Icc (-Kz) Kz, (A + B * sigmaMinusOne n.natAbs) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.erase_subset (0 : ℤ) (Finset.Icc (-Kz) Kz)) (fun n _ _ => by positivity)
    linarith [h1, h2]
  -- 4) 展开 Σ (A + Bσ)²
  have hexp : (∑ n ∈ Finset.Icc (-Kz) Kz, (A + B * sigmaMinusOne n.natAbs) ^ 2)
      = ((2 * Kz + 1 : ℤ) : ℚ) * A ^ 2
        + 2 * A * B * (∑ n ∈ Finset.Icc (-Kz) Kz, sigmaMinusOne n.natAbs)
        + B ^ 2 * (∑ n ∈ Finset.Icc (-Kz) Kz, sigmaMinusOne n.natAbs ^ 2) := by
    have hpt : ∀ n : ℤ, (A + B * sigmaMinusOne n.natAbs) ^ 2
        = A ^ 2 + 2 * A * B * sigmaMinusOne n.natAbs
          + B ^ 2 * sigmaMinusOne n.natAbs ^ 2 := fun n => by ring
    rw [Finset.sum_congr rfl (fun n _ => hpt n)]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    have hcK : ((Finset.Icc (-Kz) Kz).card : ℚ) = ((2 * Kz + 1 : ℤ) : ℚ) := by
      rw [Int.card_Icc]
      have h1 : Kz + 1 - (-Kz) = 2 * Kz + 1 := by ring
      rw [h1]
      have h2 : ((2 * Kz + 1).toNat : ℤ) = 2 * Kz + 1 := Int.toNat_of_nonneg (by omega)
      exact_mod_cast h2
    have e1 : (∑ n ∈ Finset.Icc (-Kz) Kz, A ^ 2) = ((2 * Kz + 1 : ℤ) : ℚ) * A ^ 2 := by
      rw [Finset.sum_const, nsmul_eq_mul, hcK]
    have e2 : (∑ n ∈ Finset.Icc (-Kz) Kz, 2 * A * B * sigmaMinusOne n.natAbs)
        = 2 * A * B * ∑ n ∈ Finset.Icc (-Kz) Kz, sigmaMinusOne n.natAbs := by
      rw [Finset.mul_sum]
    have e3 : (∑ n ∈ Finset.Icc (-Kz) Kz, B ^ 2 * sigmaMinusOne n.natAbs ^ 2)
        = B ^ 2 * ∑ n ∈ Finset.Icc (-Kz) Kz, sigmaMinusOne n.natAbs ^ 2 := by
      rw [Finset.mul_sum]
    rw [e1, e2, e3]
  -- 5) 常数放缩（只用 Kz 本身，不引入 `2|a|+|b|+1`）
  have hK1 : ((2 * Kz + 1 : ℤ) : ℚ) ≤ 3 * (Kz : ℚ) := by
    have h1 : ((2 * Kz + 1 : ℤ) : ℚ) = 2 * (Kz : ℚ) + 1 := by push_cast; ring
    rw [h1]
    have hN2 : (1 : ℚ) ≤ (N : ℚ) ^ 2 := by nlinarith [hNq]
    have hKg : (1 : ℚ) ≤ (Kz : ℚ) := by nlinarith [hKz_ge, hN2]
    linarith
  have hA_ub : A ≤ 8 * (N : ℚ) ^ 2 := by
    rw [hA]
    nlinarith [hNq]
  have hA2 : A ^ 2 ≤ 64 * (N : ℚ) ^ 4 := by
    calc A ^ 2 ≤ (8 * (N : ℚ) ^ 2) ^ 2 := pow_le_pow_left₀ hAnn hA_ub 2
      _ = 64 * (N : ℚ) ^ 4 := by ring
  have hAB : A * B ≤ 128 * (N : ℚ) ^ 4 := by
    rw [hB]
    have h2 : A ≤ 8 * (N : ℚ) ^ 2 := hA_ub
    nlinarith [hAnn, hNq]
  have hB2 : B ^ 2 = 256 * (N : ℚ) ^ 4 := by
    rw [hB]
    ring
  -- 6) 主放缩：`(2K+1)A² + 8ABK + 12B²K ≤ 4288·K·N⁴ ≤ 5000·K·N⁴`
  have hmain : (∑ n ∈ Finset.Icc (-Kz) Kz, (A + B * sigmaMinusOne n.natAbs) ^ 2)
      ≤ 5000 * (Kz : ℚ) * (N : ℚ) ^ 4 := by
    rw [hexp]
    have hs1 := sum_sigmaMinusOne_Icc Kz hKz0
    have hs2 := sum_sigmaMinusOne_sq_Icc Kz hKz0
    have e1 : 2 * A * B * (∑ n ∈ Finset.Icc (-Kz) Kz, sigmaMinusOne n.natAbs)
        ≤ 2 * A * B * (4 * (Kz : ℚ)) := by
      apply mul_le_mul_of_nonneg_left hs1
      positivity
    have e2 : B ^ 2 * (∑ n ∈ Finset.Icc (-Kz) Kz, sigmaMinusOne n.natAbs ^ 2)
        ≤ B ^ 2 * (12 * (Kz : ℚ)) := by
      apply mul_le_mul_of_nonneg_left hs2
      positivity
    have hkey : ((2 * Kz + 1 : ℤ) : ℚ) * A ^ 2 + 2 * A * B * (4 * (Kz : ℚ))
        + B ^ 2 * (12 * (Kz : ℚ)) ≤ 5000 * (Kz : ℚ) * (N : ℚ) ^ 4 := by
      have h1 : ((2 * Kz + 1 : ℤ) : ℚ) * A ^ 2 ≤ (3 * (Kz : ℚ)) * (64 * (N : ℚ) ^ 4) :=
        mul_le_mul hK1 hA2 (by positivity) (by positivity)
      have h2 : 2 * A * B * (4 * (Kz : ℚ)) ≤ 8 * (128 * (N : ℚ) ^ 4) * (Kz : ℚ) := by
        have hAB' : 2 * A * B * 4 ≤ 8 * (128 * (N : ℚ) ^ 4) := by nlinarith [hAB]
        have h := mul_le_mul hAB' (le_refl (Kz : ℚ)) (by positivity) (by positivity)
        nlinarith [h]
      have h3 : B ^ 2 * (12 * (Kz : ℚ)) ≤ (256 * (N : ℚ) ^ 4) * (12 * (Kz : ℚ)) := by
        rw [hB2]
      nlinarith [h1, h2, h3, hKzq, hNq]
    linarith [e1, e2, hkey]
  -- 7) 汇总：`qQ(0)² + Σ_{n≠0} qQ(n)² ≤ (273 + 5000)·K·N⁴ ≤ 10000·K·N⁴`
  rw [hcast, hsplit]
  have hQ0' : (qQ a b N (2 * N) 0 : ℚ) ^ 2 ≤ 273 * (Kz : ℚ) * (N : ℚ) ^ 4 := by
    have hmul : 273 * (4 * (N : ℚ) ^ 2) * (N : ℚ) ^ 4 ≤ 273 * (Kz : ℚ) * (N : ℚ) ^ 4 := by
      have h := mul_le_mul_of_nonneg_right hKz_ge
        (show (0 : ℚ) ≤ 273 * (N : ℚ) ^ 4 by positivity)
      nlinarith [h]
    have hN6 : (0 : ℚ) ≤ (N : ℚ) ^ 6 := by positivity
    nlinarith [hQ0, hmul, hN6]
  nlinarith [hQ0', hrest, hmain, hKzq]

/-- **`qEqCount` 的 `K·N⁴` 形式界**（`ℚ` 版本）。 -/
theorem qEqCount_le_K_rat (a b : ℤ) (ha : a ≠ 0) (N : ℕ) (hN : 1 ≤ N) :
    (qEqCount a b N : ℚ) ≤ 10000 * (qK a b N : ℚ) * (N : ℚ) ^ 4 := by
  have h1 : qEqCount a b N ≤ ∑ n ∈ Finset.Icc (-(qK a b N)) (qK a b N),
      qQ a b N (2 * N) n ^ 2 :=
    le_trans (qEqCount_le_qHMCount a b N) (qHMCount_le_sum_sq a b N)
  have h2 := sum_qQ_sq_le_K a b ha N hN
  have h3 : (qEqCount a b N : ℚ)
      ≤ ((∑ n ∈ Finset.Icc (-(qK a b N)) (qK a b N), qQ a b N (2 * N) n ^ 2 : ℕ) : ℚ) := by
    exact_mod_cast h1
  linarith

/-! ## 第三部分：主定理 -/

/-- **Theorem 1（`k = 2`，常数精细形式）**：若 `|a| ≤ c₂`、`|b| ≤ c₁N`，则

```text
qEqCount a b N ≤ 100000 · (2c₂ + c₁ + 1)⁴ · N⁶,
```

常数只依赖 `c₁, c₂`，与 `N` 无关。 -/
theorem qEqCount_le_form (a b : ℤ) (ha : a ≠ 0) (c₁ c₂ : ℕ) (N : ℕ) (hN : 1 ≤ N)
    (ha2 : a.natAbs ≤ c₂) (hb1 : b.natAbs ≤ c₁ * N) :
    qEqCount a b N ≤ 100000 * (2 * c₂ + c₁ + 1) ^ 4 * N ^ 6 := by
  have hKub : (qK a b N : ℚ) ≤ (4 * (c₂ : ℚ) + 2 * (c₁ : ℚ)) * (N : ℚ) ^ 2 := by
    have h := qK_le_form a b c₁ c₂ N ha2 hb1
    have h' : ((qK a b N : ℤ) : ℚ)
        ≤ (((4 * (c₂ : ℤ) + 2 * (c₁ : ℤ)) * (N : ℤ) ^ 2 : ℤ) : ℚ) := by exact_mod_cast h
    push_cast at h'
    exact h'
  have hbase := qEqCount_le_K_rat a b ha N hN
  have h1 : (qEqCount a b N : ℚ)
      ≤ 10000 * ((4 * (c₂ : ℚ) + 2 * (c₁ : ℚ)) * (N : ℚ) ^ 2) * (N : ℚ) ^ 4 := by
    have h := mul_le_mul_of_nonneg_right hKub
      (show (0 : ℚ) ≤ 10000 * (N : ℚ) ^ 4 by positivity)
    have h' : (qK a b N : ℚ) * (10000 * (N : ℚ) ^ 4)
        ≤ ((4 * (c₂ : ℚ) + 2 * (c₁ : ℚ)) * (N : ℚ) ^ 2) * (10000 * (N : ℚ) ^ 4) := h
    nlinarith [hbase, h']
  have h2 : 10000 * ((4 * (c₂ : ℚ) + 2 * (c₁ : ℚ)) * (N : ℚ) ^ 2) * (N : ℚ) ^ 4
      ≤ 100000 * (2 * (c₂ : ℚ) + (c₁ : ℚ) + 1) ^ 4 * (N : ℚ) ^ 6 := by
    have hx1 : (1 : ℚ) ≤ 2 * (c₂ : ℚ) + (c₁ : ℚ) + 1 := by
      have h2 : (0 : ℚ) ≤ (c₂ : ℚ) := Nat.cast_nonneg c₂
      have h3 : (0 : ℚ) ≤ (c₁ : ℚ) := Nat.cast_nonneg c₁
      linarith
    have hxle : 2 * (c₂ : ℚ) + (c₁ : ℚ) ≤ 2 * (c₂ : ℚ) + (c₁ : ℚ) + 1 := by linarith
    have hx4 : (2 * (c₂ : ℚ) + (c₁ : ℚ) + 1)
        ≤ (2 * (c₂ : ℚ) + (c₁ : ℚ) + 1) ^ 4 := by
      have h := pow_le_pow_right₀ hx1 (by norm_num : (1 : ℕ) ≤ 4)
      simpa using h
    have hN6 : (0 : ℚ) ≤ (N : ℚ) ^ 6 := by positivity
    have ha0 : (0 : ℚ) ≤ 2 * (c₂ : ℚ) + (c₁ : ℚ) := by positivity
    have hkey : 20000 * (2 * (c₂ : ℚ) + (c₁ : ℚ)) * (N : ℚ) ^ 6
        ≤ 100000 * (2 * (c₂ : ℚ) + (c₁ : ℚ) + 1) ^ 4 * (N : ℚ) ^ 6 := by
      have hcoef : 20000 * (2 * (c₂ : ℚ) + (c₁ : ℚ))
          ≤ 100000 * (2 * (c₂ : ℚ) + (c₁ : ℚ) + 1) ^ 4 := by
        nlinarith [hx1, hxle, hx4, ha0]
      exact mul_le_mul_of_nonneg_right hcoef hN6
    have heq : 10000 * ((4 * (c₂ : ℚ) + 2 * (c₁ : ℚ)) * (N : ℚ) ^ 2) * (N : ℚ) ^ 4
        = 20000 * (2 * (c₂ : ℚ) + (c₁ : ℚ)) * (N : ℚ) ^ 6 := by ring
    rw [heq]
    exact hkey
  have htarget : (qEqCount a b N : ℚ)
      ≤ ((100000 * (2 * c₂ + c₁ + 1) ^ 4 * N ^ 6 : ℕ) : ℚ) := by
    have hcast : ((100000 * (2 * c₂ + c₁ + 1) ^ 4 * N ^ 6 : ℕ) : ℚ)
        = 100000 * (2 * (c₂ : ℚ) + (c₁ : ℚ) + 1) ^ 4 * (N : ℚ) ^ 6 := by
      push_cast
      ring
    rw [hcast]
    linarith [h1, h2]
  exact_mod_cast htarget

/-- **Theorem 1（`k = 2`，常数精细形式）的积分版本**：

```text
∫₀¹ |∑_{n≤N} e(α(a n² + b n))|⁸ dα ≤ 100000 · (2c₂ + c₁ + 1)⁴ · N⁶.
``` -/
theorem integral_normSq_pow_four_le_form (a b : ℤ) (ha : a ≠ 0) (c₁ c₂ : ℕ) (N : ℕ)
    (hN : 1 ≤ N) (ha2 : a.natAbs ≤ c₂) (hb1 : b.natAbs ≤ c₁ * N) :
    (∫ α in (0 : ℝ)..1, (Complex.normSq (qSum a b N α)) ^ 4)
      ≤ 100000 * ((2 * c₂ + c₁ + 1 : ℕ) : ℝ) ^ 4 * (N : ℝ) ^ 6 := by
  rw [integral_normSq_pow_four_q]
  have h := qEqCount_le_form a b ha c₁ c₂ N hN ha2 hb1
  have h' : (qEqCount a b N : ℝ)
      ≤ ((100000 * (2 * c₂ + c₁ + 1) ^ 4 * N ^ 6 : ℕ) : ℝ) := by exact_mod_cast h
  push_cast at h' ⊢
  exact h'

end Waring
