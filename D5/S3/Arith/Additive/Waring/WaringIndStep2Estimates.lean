/- GID: D5/S3/Arith/Additive/Waring/WaringIndStep2Estimates
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Third-party formalization of the qualitative Hilbert–Waring theorem. -/

/- Source: https://github.com/yunyougu50-create/waring-lean4/blob/cd0735c253f3b640262fcc74a61306cb41e23765/WaringIndStep2.lean#L1-L493
   Modified for this repository. Local imports use their D5 module paths.
   This file contains one segment of a split upstream module.
   Full Apache-2.0 license: D5/S3/Arith/Additive/Waring/WaringStatement.lean. -/

/-
Copyright (c) 2026 The Waring formalization authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Waring formalization authors
-/
import D5.S3.Arith.Additive.Waring.WaringIndStep
import D5.S3.Arith.Additive.Waring.WaringLemma7
import D5.S3.Arith.Additive.Waring.WaringHolder
import D5.S3.Arith.Additive.Waring.WaringQuadSum
import D5.S3.Arith.Additive.Waring.WaringCoeffBound
import D5.S3.Arith.Additive.Waring.WaringQuadratic
import D5.S3.Arith.Additive.Waring.WaringLemma8Form

/-!
# 加强版归纳步 `MeanValueBoundS (d−1) → MeanValueBoundS d`

Jameson Theorem 1 的归纳步，加强版：求和长度 `M ≤ N`，系数尺度 `N`。

## 状态：**全部完成** ✅

本文件自包含给出完整的归纳：

* `meanValueBoundS_two : MeanValueBoundS 2`（基例，第 1 节末）；
* `meanValueBoundS_succ : 3 ≤ d → MeanValueBoundS (d−1) → MeanValueBoundS d`（归纳步）。

由此对一切 `d ≥ 2` 有 `MeanValueBoundS d`（外部用 `Nat.le_induction` 组装）。
**零 `sorry`/`admit`/`axiom`，编译 exit 0。**

> 文件末尾（第 13 节）保留了两段**注释掉的早期尝试**（旧 `count_le`、旧
> `meanValueBoundS_succ` 的算术），仅作参考，不参与编译。

## 记号

`m := 8^{d−2}`（`d ≥ 3` 时 `m ≥ 8`），于是 `8^{d−1} = 8m`，且 `m = 2s`，
`s = 4·8^{d−3}`（供 `integral_sum_pow_four` 使用）。

## 分块（全部已证明）

1. `pointwise_bound`（第 1–4 步）：`‖S‖^{8m} ≤ 2^{4(m−1)}·8·((M+1)^{4m} + (2M)^{4(m−1)}·B^4)`，
   其中 `B = Σ_{h≠0}‖b_h‖^m`（`SigTerm`）；辅助：`pow_four_bound`、`pointwise_alg`；
2. `integral_bound`（第 5 步）：逐项积分
   `∫‖S‖^{8m} ≤ 2^{4(m−1)}·8·((M+1)^{4m} + (2M)^{4(m−1)}·∫B^4)`；
3. `four_sum_eq`（第 6 步）：`∫ (Σ_h‖b_h‖^m)^4` 的四重和展开（`integral_sum_pow_four`，
   取 `s = 4·8^{d−3}`，`2s = m`，见 `two_mul_s`/`one_le_s`）；
4. `integral_norm_T_pow_le_R`（第 7 步）：由 `MVSBound (d−1) R₀` 得
   `∫‖b_h‖^{8^{d−2}} ≤ max(R₀(C),1)·N^{8^{d−2}−(d−1)}`（`C = coeffConst c d`）；
5. `BCount_le_Rtot`（第 6 步前半 + 第 7 步）：每个 `BCount` 同界；
6. `four_sum_le_count`（第 8 步）：
   `∫(Σ‖b_h‖^m)^4 ≤ Rtot^4 · #{(h₁..h₄, Q₁..Q₄) : Qᵢ ∈ QSet hᵢ, Q₁+…+Q₄ = 0}`；
7. 第 9 步的**准备**：
   * `QSet_exists`：`Q ∈ QSet` 可写成两个 `Qsum` 之差；
   * `QSet_dvd`：`f = polyEval a d` 时 `h ∣ Q`；
   * `polyEval_diffCoeff_abs_le`：`|φ(n)| ≤ (d+1)·coeffConst·N^{d−1}`（`|n|,|h| ≤ N`）；
   * `QSet_div_abs_le`：`Q ∈ QSet`、`h ≠ 0` ⟹ `|Q/h| ≤ 2s(d+1)·coeffConst·N^{d−1} =: Kf c d N`；
   * `sum_piFinset_fin4`：`Fintype.piFinset` 在 `Fin 4` 上展开成 4 层求和
     （把 8 层求和折叠成 `Fin 4 → ℤ` 上的求和所需的桥）；
8. **第 9 步 (9a) 已完成**：`sum_QBox_le_MBox`：
   `∑_{Q ∈ QSet⁴} [Q₁+…+Q₄ = 0] ≤ ∑_{m ∈ ([−Kf,Kf])⁴} [h₁m₁+…+h₄m₄ = 0]`
   （映射 `Q ↦ fun i => Q i / hh i`，单射性来自 `QSet_dvd`，像落在 `Kf` 盒来自
   `QSet_div_abs_le`）；
9. **第 9 步 (9b) 已完成**：`card_sym_shrink`：
   `#{h ∈ hBox7 M, m ∈ ([−K,K])⁴, Σ hᵢmᵢ = 0} ≤ 16·hmCount7 M K`。
   映射 `sgnMap : (h, m) ↦ ((sgn(mᵢ)·hᵢ, |mᵢ|), sgn(mᵢ))` —— **符号翻转作用在 `hᵢ` 上**，
   故 `Σᵢ (sgn(mᵢ)hᵢ)·|mᵢ| = Σᵢ hᵢ(sgn(mᵢ)|mᵢ|) = Σᵢ hᵢmᵢ`，方程保持不变；
   像落在 `hmCount7 的盒子 × SymBox`（`SymBox = {±1}⁴`，`card = 16`）；
10. **基例（自包含）**：`meanValueBoundS_two : MeanValueBoundS 2`，
    连同 `polyEval_two_eq`、`expSum_polyEval_two`、`qEqCount_le_MN`
    （从 `WaringInduction` 逐字搬入；因 `import WaringQuadratic` 无命名冲突）；
11. **第 9 步 (9c) 已完成**：`count_le`：
    `∑_{h₁..h₄} ∑_{Q₁∈QSet hᵢ} [Q₁+…+Q₄ = 0] ≤ 16·5250·(M·Kf)³`。
    证明链：`sum_four_Q_le_MBox`（4 层 `Q ↦ Q/h` 逐层放大到 `Kf` 盒子，
    用 `Finset.sum_image` + `QSet_dvd` + `QSet_div_abs_le`，**不展开 `QSet`**）
    → `sum_piFinset_fin4`（`hBox7 M` 与 `KB` 的 4 层折叠）
    → `card_filter`（`∑ if … then 1 else 0 = card`，先 `ℕ` 后 `exact_mod_cast`）
    → `card_sym_shrink`（9b）→ `hmCount7_le'`（Lemma 7，需 `M ≤ Kf`，由 `le_Kf`）。
    辅助：`sum_piFinset_fin4_dep`、`one_le_c`、`coeffConst_pos`、`le_Kf`、`QSf`。

## 第 10 步（常数账 + 组装，已完成）

`Rd d R₀ c = 2^{4(m−1)}·8·(2^{4m} + 2^{4(m−1)}·Rmax⁴·16·5250·Ck³)`，其中
`Rmax = max(R₀(C),1)`、`Ck = 2s(d+1)·coeffConst`，于是
`∫ ≤ 2^{4(m−1)}·8·((M+1)^{4m} + (2M)^{4(m−1)}·Rmax⁴·N^{4(m−(d−1))}·16·5250·Ck³·N^{3d})`
= `Rd·N^{8m−d}`。指数核对：`4(m−1) + 4(m−(d−1)) + 3d = 8m − d` ✓
（`3d = 3 + 3(d−1)`：`M ≤ N` 贡献 `3`，`Kf = Ck·N^{d−1}` 贡献 `3(d−1)`）。
关键辅助：`hKf`（`Kf = Ck·N^{d−1}`）、`hmge : d−1 ≤ m`（`Nat.lt_two_pow_self`
+ `8 = 2^3`）、`hexp1`、`hNfin`、`hP1`、`hP2`、`hP2` 的 `mul_le_mul` 需先给
`intervalIntegral.integral_nonneg`。

## 环境说明

`WaringIndStep`（依赖 `WaringBPow`/`WaringQuadSum`）与 `WaringInduction`（依赖
`WaringQuadratic`）因 `e_sum` 命名冲突不能同时 import，故本文件**逐字重述**
`MeanValueBoundS` 的定义（与 `WaringInduction.MeanValueBoundS` 完全相同）。
注意：`WaringQuadratic`/`WaringLemma8Form` **可以**与本文件的 `WaringIndStep` 链
一起 import（`WaringBPow` 的 `e_sum` 已改名 `e_sum_finset`），基例因此可以自包含。
-/

open Finset intervalIntegral

namespace Waring

/-! ## 0. 命题陈述（与 `WaringInduction.MeanValueBoundS` 逐字相同） -/

/-- **加强版归纳命题**（`M ≤ N`）：求和长度 `M` 可以小于系数尺度的 `N`，
但界仍然用 `N`。 -/
def MeanValueBoundS (d : ℕ) : Prop :=
  ∃ R : ℕ → ℝ, (∀ c, 0 < R c) ∧
    ∀ (c N M : ℕ), 1 ≤ N → 1 ≤ M → M ≤ N → ∀ (a : ℕ → ℤ), a d ≠ 0 →
      (∀ j, j ≤ d → |a j| ≤ (c : ℤ) * (N : ℤ) ^ (d - j)) →
      (∫ α in (0 : ℝ)..1,
          ‖expSum (fun n => polyEval a d n) M α‖ ^ (8 ^ (d - 1)))
        ≤ R c * (N : ℝ) ^ (8 ^ (d - 1) - d)

/-! 由 `MeanValueBoundS d` 取 `M = N` 得原版（与 `WaringInduction` 的同名引理一致）。 -/

/-- `MeanValueBoundS d` 的显式应用形式（解包 `∃ R`）。 -/
theorem MeanValueBoundS.apply {d : ℕ} (h : MeanValueBoundS d) (c N M : ℕ)
    (hN : 1 ≤ N) (hM1 : 1 ≤ M) (hMN : M ≤ N) (a : ℕ → ℤ) (had : a d ≠ 0)
    (ha : ∀ j, j ≤ d → |a j| ≤ (c : ℤ) * (N : ℤ) ^ (d - j)) :
    ∃ R : ℝ, 0 < R ∧
      (∫ α in (0 : ℝ)..1,
          ‖expSum (fun n => polyEval a d n) M α‖ ^ (8 ^ (d - 1)))
        ≤ R * (N : ℝ) ^ (8 ^ (d - 1) - d) := by
  obtain ⟨R, hR, hbound⟩ := h
  exact ⟨R c, hR c, hbound c N M hN hM1 hMN a had ha⟩

/-! ## 1. 第 1–4 步：点态界 -/

/-- `B = Σ_{h≠0, |h|≤M} ‖b_h‖^m`，其中 `m = 8^{d−2}`。 -/
noncomputable def SigTerm (a : ℕ → ℤ) (d M : ℕ) (α : ℝ) : ℝ :=
  ∑ h ∈ (Finset.Icc (-(M : ℤ)) (M : ℤ)).erase 0,
    ‖T (fun n => polyEval a d n) M α h‖ ^ (8 ^ (d - 2))

/-- `(A+B)^4 ≤ 8(A^4 + B^4)`（`A, B ≥ 0`）。 -/
theorem pow_four_bound (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    (A + B) ^ 4 ≤ 8 * (A ^ 4 + B ^ 4) := by
  have h := add_pow_le_two_pow A B hA hB 4 (by norm_num)
  norm_num at h
  linarith

/-- 纯代数整理（第 2–4 步）：
`(2^{m−1}·((M+1)^m + (2M)^{m−1}·T))^4 ≤ 2^{4(m−1)}·8·((M+1)^{4m} + (2M)^{4(m−1)}·T^4)`。 -/
theorem pointwise_alg (M m : ℕ) (Tv : ℝ) (hTv : 0 ≤ Tv) :
    (2 ^ (m - 1) * ((M + 1 : ℝ) ^ m + (2 * (M : ℝ)) ^ (m - 1) * Tv)) ^ 4
      ≤ 2 ^ (4 * (m - 1)) * 8 * ((M + 1 : ℝ) ^ (4 * m)
          + (2 * (M : ℝ)) ^ (4 * (m - 1)) * Tv ^ 4) := by
  have h1 : (2 ^ (m - 1) * ((M + 1 : ℝ) ^ m + (2 * (M : ℝ)) ^ (m - 1) * Tv)) ^ 4
      = 2 ^ (4 * (m - 1))
        * (((M + 1 : ℝ) ^ m + (2 * (M : ℝ)) ^ (m - 1) * Tv) ^ 4) := by
    rw [mul_pow, ← pow_mul, Nat.mul_comm (m - 1) 4]
  rw [h1]
  have hA0 : (0 : ℝ) ≤ (M + 1 : ℝ) ^ m := by positivity
  have hB0 : (0 : ℝ) ≤ (2 * (M : ℝ)) ^ (m - 1) * Tv := by positivity
  have h2 := pow_four_bound _ _ hA0 hB0
  have h3 : (((M + 1 : ℝ) ^ m + (2 * (M : ℝ)) ^ (m - 1) * Tv) ^ 4)
      ≤ 8 * ((M + 1 : ℝ) ^ (4 * m)
          + (2 * (M : ℝ)) ^ (4 * (m - 1)) * Tv ^ 4) := by
    refine le_trans h2 (le_of_eq ?_)
    congr 2
    · rw [← pow_mul, Nat.mul_comm m 4]
    · rw [mul_pow, ← pow_mul, Nat.mul_comm (m - 1) 4]
  calc 2 ^ (4 * (m - 1))
        * (((M + 1 : ℝ) ^ m + (2 * (M : ℝ)) ^ (m - 1) * Tv) ^ 4)
      ≤ 2 ^ (4 * (m - 1)) * (8 * ((M + 1 : ℝ) ^ (4 * m)
          + (2 * (M : ℝ)) ^ (4 * (m - 1)) * Tv ^ 4)) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = 2 ^ (4 * (m - 1)) * 8 * ((M + 1 : ℝ) ^ (4 * m)
          + (2 * (M : ℝ)) ^ (4 * (m - 1)) * Tv ^ 4) := by ring

/-- **第 1–4 步（点态）**：`‖S‖^{8^{d−1}} ≤ 2^{4(m−1)}·8·((M+1)^{4m} + (2M)^{4(m−1)}·B^4)`。 -/
theorem pointwise_bound {d : ℕ} (hd : 3 ≤ d) (a : ℕ → ℤ) {M : ℕ} (hM1 : 1 ≤ M) (α : ℝ) :
    ‖expSum (fun n => polyEval a d n) M α‖ ^ (8 ^ (d - 1))
      ≤ 2 ^ (4 * (8 ^ (d - 2) - 1)) * 8 *
          ((M + 1 : ℝ) ^ (4 * 8 ^ (d - 2))
            + (2 * (M : ℝ)) ^ (4 * (8 ^ (d - 2) - 1)) * (SigTerm a d M α) ^ 4) := by
  have hm1 : 1 ≤ 8 ^ (d - 2) := by
    have h : (0 : ℕ) < 8 ^ (d - 2) := pow_pos (by norm_num) _
    omega
  have hpt := normSq_pow_le (fun n => polyEval a d n) M α (8 ^ (d - 2)) hm1 hM1
  have hTv : 0 ≤ SigTerm a d M α := by
    apply Finset.sum_nonneg
    intro h _
    positivity
  have hpow : 8 ^ (d - 1) = (2 * 8 ^ (d - 2)) * 4 := by
    have h1 : d - 1 = (d - 2) + 1 := by omega
    rw [h1, pow_succ]
    ring
  rw [hpow, pow_mul]
  exact le_trans (pow_le_pow_left₀ (by positivity) hpt 4)
    (pointwise_alg M (8 ^ (d - 2)) (SigTerm a d M α) hTv)

/-! ## 2. 第 5 步：积分 -/

/-- **第 5 步（积分）**：
`∫‖S‖^{8m} ≤ 2^{4(m−1)}·8·((M+1)^{4m} + (2M)^{4(m−1)}·∫B^4)`。 -/
theorem integral_bound {d : ℕ} (hd : 3 ≤ d) (a : ℕ → ℤ) {M : ℕ} (hM1 : 1 ≤ M) :
    (∫ α in (0 : ℝ)..1, ‖expSum (fun n => polyEval a d n) M α‖ ^ (8 ^ (d - 1)))
      ≤ 2 ^ (4 * (8 ^ (d - 2) - 1)) * 8 *
          ((M + 1 : ℝ) ^ (4 * 8 ^ (d - 2))
            + (2 * (M : ℝ)) ^ (4 * (8 ^ (d - 2) - 1))
              * ∫ α in (0 : ℝ)..1, (SigTerm a d M α) ^ 4) := by
  set g : ℝ → ℝ := fun α => 2 ^ (4 * (8 ^ (d - 2) - 1)) * 8 *
      ((M + 1 : ℝ) ^ (4 * 8 ^ (d - 2))
        + (2 * (M : ℝ)) ^ (4 * (8 ^ (d - 2) - 1)) * (SigTerm a d M α) ^ 4) with hg
  have hcont1 : Continuous fun α : ℝ =>
      ‖expSum (fun n => polyEval a d n) M α‖ ^ (8 ^ (d - 1)) := by
    unfold expSum e
    fun_prop
  have hcont2 : Continuous fun α : ℝ => (SigTerm a d M α) ^ 4 := by
    unfold SigTerm T e
    fun_prop
  have hcontg : Continuous g := by
    rw [hg]
    simp only [mul_assoc]
    unfold SigTerm T e
    fun_prop
  have hmono : (∫ α in (0 : ℝ)..1, ‖expSum (fun n => polyEval a d n) M α‖ ^ (8 ^ (d - 1)))
      ≤ ∫ α in (0 : ℝ)..1, g α := by
    refine intervalIntegral.integral_mono_on (by norm_num)
      (hcont1.intervalIntegrable 0 1) (hcontg.intervalIntegrable 0 1) ?_
    intro α _
    rw [hg]
    exact pointwise_bound hd a hM1 α
  have hsplit : (∫ x in (0 : ℝ)..1, ((M + 1 : ℝ) ^ (4 * 8 ^ (d - 2))
        + (2 * (M : ℝ)) ^ (4 * (8 ^ (d - 2) - 1)) * SigTerm a d M x ^ 4))
      = (M + 1 : ℝ) ^ (4 * 8 ^ (d - 2))
        + (2 * (M : ℝ)) ^ (4 * (8 ^ (d - 2) - 1))
          * (∫ x in (0 : ℝ)..1, SigTerm a d M x ^ 4) := by
    have step1 : (∫ x in (0 : ℝ)..1, ((M + 1 : ℝ) ^ (4 * 8 ^ (d - 2))
          + (2 * (M : ℝ)) ^ (4 * (8 ^ (d - 2) - 1)) * SigTerm a d M x ^ 4))
        = (∫ x in (0 : ℝ)..1, ((M + 1 : ℝ) ^ (4 * 8 ^ (d - 2))))
          + (∫ x in (0 : ℝ)..1, ((2 * (M : ℝ)) ^ (4 * (8 ^ (d - 2) - 1))
              * SigTerm a d M x ^ 4)) :=
      intervalIntegral.integral_add intervalIntegrable_const
        ((continuous_const.mul hcont2).intervalIntegrable 0 1)
    rw [step1, intervalIntegral.integral_const, intervalIntegral.integral_const_mul]
    ring
  have hgi : (∫ α in (0 : ℝ)..1, g α)
      = 2 ^ (4 * (8 ^ (d - 2) - 1)) * 8 *
          ((M + 1 : ℝ) ^ (4 * 8 ^ (d - 2))
            + (2 * (M : ℝ)) ^ (4 * (8 ^ (d - 2) - 1))
              * ∫ α in (0 : ℝ)..1, (SigTerm a d M α) ^ 4) := by
    rw [hg]
    simp only [mul_assoc]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hsplit]
  exact le_trans hmono (le_of_eq hgi)

/-! ## 3. 第 6 步：四重和与正交性 -/

/-- 展开 `∫ (Σ_h ‖b_h‖^m)^4`（`m = 8^{d−2} = 2s`，`s = 4·8^{d−3}`）。 -/
theorem four_sum_eq {d : ℕ} (hd : 3 ≤ d) (a : ℕ → ℤ) (M : ℕ) :
    (∫ α in (0 : ℝ)..1, (SigTerm a d M α) ^ 4)
      = ∑ h1 ∈ (Finset.Icc (-(M : ℤ)) (M : ℤ)).erase 0,
        ∑ h2 ∈ (Finset.Icc (-(M : ℤ)) (M : ℤ)).erase 0,
        ∑ h3 ∈ (Finset.Icc (-(M : ℤ)) (M : ℤ)).erase 0,
        ∑ h4 ∈ (Finset.Icc (-(M : ℤ)) (M : ℤ)).erase 0,
        ∑ Q1 ∈ QSet (fun n => polyEval a d n) M h1 (4 * 8 ^ (d - 3)),
        ∑ Q2 ∈ QSet (fun n => polyEval a d n) M h2 (4 * 8 ^ (d - 3)),
        ∑ Q3 ∈ QSet (fun n => polyEval a d n) M h3 (4 * 8 ^ (d - 3)),
        ∑ Q4 ∈ QSet (fun n => polyEval a d n) M h4 (4 * 8 ^ (d - 3)),
          (if Q1 + Q2 + Q3 + Q4 = 0 then
            (BCount (fun n => polyEval a d n) M h1 (4 * 8 ^ (d - 3)) Q1
              * BCount (fun n => polyEval a d n) M h2 (4 * 8 ^ (d - 3)) Q2
              * BCount (fun n => polyEval a d n) M h3 (4 * 8 ^ (d - 3)) Q3
              * BCount (fun n => polyEval a d n) M h4 (4 * 8 ^ (d - 3)) Q4 : ℝ)
          else 0) := by
  have hs1 : 1 ≤ 4 * 8 ^ (d - 3) := by
    have h : 0 < 4 * 8 ^ (d - 3) := by positivity
    omega
  have h2s : 2 * (4 * 8 ^ (d - 3)) = 8 ^ (d - 2) := by
    have h1 : d - 2 = (d - 3) + 1 := by omega
    rw [h1, pow_succ]
    ring
  have h := integral_sum_pow_four (fun n => polyEval a d n) M (4 * 8 ^ (d - 3)) hs1
  rw [h2s] at h
  exact h

/-! ## 4. 第 7 步：每个 `∫₀¹‖b_h‖^{8^{d−2}}` 的上界（用 `P(d−1)`）

`P(d−1)` 的解包形式：常数族 `R` 与界。 -/

/-- `P(k)` 的显式形式（`R` 固定）。 -/
def MVSBound (k : ℕ) (R : ℕ → ℝ) : Prop :=
  ∀ (c N M : ℕ), 1 ≤ N → 1 ≤ M → M ≤ N → ∀ (a : ℕ → ℤ), a k ≠ 0 →
    (∀ j, j ≤ k → |a j| ≤ (c : ℤ) * (N : ℤ) ^ (k - j)) →
    (∫ α in (0 : ℝ)..1, ‖expSum (fun n => polyEval a k n) M α‖ ^ (8 ^ (k - 1)))
      ≤ R c * (N : ℝ) ^ (8 ^ (k - 1) - k)

set_option maxHeartbeats 4000000 in
/-- **第 7 步**：`P(d−1) ⇒ ∫₀¹‖b_h‖^{8^{d−2}} ≤ max(R(C),1)·N^{8^{d−2}−(d−1)}`。 -/
theorem integral_norm_T_pow_le_R {d : ℕ} (hd : 3 ≤ d) {R₀ : ℕ → ℝ}
    (hMV : MVSBound (d - 1) R₀) :
    ∀ (c N M : ℕ), 1 ≤ N → 1 ≤ M → M ≤ N → ∀ (a : ℕ → ℤ), a d ≠ 0 →
    (∀ j, j ≤ d → |a j| ≤ (c : ℤ) * (N : ℤ) ^ (d - j)) →
    ∀ h ∈ (Finset.Icc (-(M : ℤ)) (M : ℤ)).erase 0,
      (∫ α in (0 : ℝ)..1, ‖T (fun n => polyEval a d n) M α h‖ ^ (8 ^ (d - 2)))
        ≤ max (R₀ (coeffConst c d)) 1 * (N : ℝ) ^ (8 ^ (d - 2) - (d - 1)) := by
  intro c N M hN hM1 hMN a had ha
  have hd1 : 1 ≤ d := by omega
  have hexp : (d - 1) - 1 = d - 2 := by omega
  intro h hS
  rw [Finset.mem_erase, Finset.mem_Icc] at hS
  obtain ⟨hne, hle1, hle2⟩ := hS
  have main : ∀ (g : ℤ), 0 < g → g.toNat ≤ M →
      (∫ α in (0 : ℝ)..1, ‖T (fun n => polyEval a d n) M α g‖ ^ (8 ^ (d - 2)))
        ≤ max (R₀ (coeffConst c d)) 1 * (N : ℝ) ^ (8 ^ (d - 2) - (d - 1)) := by
    intro g hg hgM
    rw [integral_norm_T_pow_eq (a := a) (d := d) (N := M) (h := g) hg hgM (8 ^ (d - 2))]
    -- 次数从 `d` 降到 `d−1`
    have hstep : (∫ β in (0 : ℝ)..1,
        ‖expSum (fun n => polyEval (diffCoeff a d g) d n) (M - g.toNat) β‖ ^ (8 ^ (d - 2)))
        = ∫ β in (0 : ℝ)..1,
          ‖expSum (fun n => polyEval (diffCoeff a d g) (d - 1) n) (M - g.toNat) β‖ ^
            (8 ^ (d - 2)) := by
      apply intervalIntegral.integral_congr
      intro β _
      have hfun : (fun n => polyEval (diffCoeff a d g) d n)
          = (fun n => polyEval (diffCoeff a d g) (d - 1) n) := by
        funext n
        exact polyEval_eq_of_last_zero (diffCoeff a d g) hd1 (diffCoeff_eq_zero_of_le le_rfl) n
      rw [hfun]
    rw [hstep]
    rcases Nat.eq_zero_or_pos (M - g.toNat) with h0 | h1pos
    · -- 长度为零：指数和只有一项
      rw [h0]
      have hpt : ∀ β : ℝ,
          ‖expSum (fun n => polyEval (diffCoeff a d g) (d - 1) n) 0 β‖ ^ (8 ^ (d - 2)) ≤ 1 := by
        intro β
        have hnorm : ‖expSum (fun n => polyEval (diffCoeff a d g) (d - 1) n) 0 β‖ = 1 := by
          unfold expSum
          rw [Finset.range_one, Finset.sum_singleton, norm_e]
        rw [hnorm, one_pow]
      have hcont : Continuous fun β : ℝ =>
          ‖expSum (fun n => polyEval (diffCoeff a d g) (d - 1) n) 0 β‖ ^ (8 ^ (d - 2)) := by
        unfold expSum e
        fun_prop
      have hbound : (∫ β in (0 : ℝ)..1,
          ‖expSum (fun n => polyEval (diffCoeff a d g) (d - 1) n) 0 β‖ ^ (8 ^ (d - 2))) ≤ 1 := by
        calc (∫ β in (0 : ℝ)..1,
              ‖expSum (fun n => polyEval (diffCoeff a d g) (d - 1) n) 0 β‖ ^ (8 ^ (d - 2)))
            ≤ ∫ β in (0 : ℝ)..1, (1 : ℝ) :=
              intervalIntegral.integral_mono_on (by norm_num) (hcont.intervalIntegrable 0 1)
                intervalIntegrable_const (fun x _ => hpt x)
          _ = 1 := by simp
      refine le_trans hbound ?_
      have h1 : (1 : ℝ) ≤ max (R₀ (coeffConst c d)) 1 := le_max_right _ _
      have h2 : (1 : ℝ) ≤ (N : ℝ) ^ (8 ^ (d - 2) - (d - 1)) := one_le_pow₀ (by exact_mod_cast hN)
      calc (1 : ℝ) = 1 * 1 := by ring
        _ ≤ max (R₀ (coeffConst c d)) 1 * (N : ℝ) ^ (8 ^ (d - 2) - (d - 1)) :=
            mul_le_mul h1 h2 (by norm_num) (by linarith)
    · -- 一般情形：用 `P(d−1)`
      have htoNatZ : ((g.toNat : ℕ) : ℤ) = g := Int.toNat_of_nonneg (le_of_lt hg)
      have habs : |g| ≤ (N : ℤ) := by
        have h2 : ((g.toNat : ℕ) : ℤ) ≤ (N : ℤ) := by
          have h3 : g.toNat ≤ N := le_trans hgM hMN
          exact_mod_cast h3
        rw [htoNatZ] at h2
        rw [abs_of_pos hg]
        exact h2
      have hcoeff : ∀ j, j ≤ d - 1 →
          |diffCoeff a d g j| ≤ (coeffConst c d : ℤ) * (N : ℤ) ^ ((d - 1) - j) := by
        intro j hj
        exact diffCoeff_bound' (a := a) (d := d) (h := g) (c := c) (N := N) ha habs j (by omega)
      have hblast : diffCoeff a d g (d - 1) ≠ 0 := by
        rw [diffCoeff_last hd1 g]
        exact mul_ne_zero had (by exact_mod_cast (show d ≠ 0 by omega))
      have hres := hMV (coeffConst c d) N (M - g.toNat) hN h1pos (by omega)
        (diffCoeff a d g) hblast hcoeff
      rw [hexp] at hres
      refine le_trans hres ?_
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · -- `h < 0`：换成 `−h > 0`
    have htoNat : (-h).toNat ≤ M := by
      have h1 : (((-h).toNat : ℕ) : ℤ) = -h := Int.toNat_of_nonneg (by omega)
      have h2 : (((-h).toNat : ℕ) : ℤ) ≤ (M : ℤ) := by rw [h1]; linarith
      exact_mod_cast h2
    have heq : (∫ α in (0 : ℝ)..1, ‖T (fun n => polyEval a d n) M α h‖ ^ (8 ^ (d - 2)))
        = ∫ α in (0 : ℝ)..1, ‖T (fun n => polyEval a d n) M α (-h)‖ ^ (8 ^ (d - 2)) := by
      apply intervalIntegral.integral_congr
      intro α _
      have hh := norm_T_neg (f := fun n => polyEval a d n) (N := M) (h := -h) (by omega) htoNat α
      show ‖T (fun n => polyEval a d n) M α h‖ ^ (8 ^ (d - 2))
        = ‖T (fun n => polyEval a d n) M α (-h)‖ ^ (8 ^ (d - 2))
      rw [show ‖T (fun n => polyEval a d n) M α h‖ = ‖T (fun n => polyEval a d n) M α (-h)‖ by
        simpa using hh]
    rw [heq]
    exact main (-h) (by omega) htoNat
  · -- `h > 0`
    have htoNatM : h.toNat ≤ M := by
      have h1 : ((h.toNat : ℕ) : ℤ) = h := Int.toNat_of_nonneg (by omega)
      have h2 : ((h.toNat : ℕ) : ℤ) ≤ (M : ℤ) := by rw [h1]; exact hle2
      exact_mod_cast h2
    exact main h hpos htoNatM

/-! ## 5. 第 8 步：四重和逐项放大到 `Rtot^4` 乘计数 -/

/-- `2·(4·8^{d−3}) = 8^{d−2}`（`d ≥ 3`）。 -/
theorem two_mul_s {d : ℕ} (hd : 3 ≤ d) : 2 * (4 * 8 ^ (d - 3)) = 8 ^ (d - 2) := by
  have h1 : d - 2 = (d - 3) + 1 := by omega
  rw [h1, pow_succ]
  ring

/-- `1 ≤ 4·8^{d−3}`。 -/
theorem one_le_s (d : ℕ) : 1 ≤ 4 * 8 ^ (d - 3) := by
  have h : 0 < 4 * 8 ^ (d - 3) := by positivity
  omega

/-- **每个 `BCount` 的上界**（第 6 步前半 + 第 7 步）。 -/
theorem BCount_le_Rtot {d : ℕ} (hd : 3 ≤ d) {R₀ : ℕ → ℝ}
    (hMV : MVSBound (d - 1) R₀) :
    ∀ (c N M : ℕ), 1 ≤ N → 1 ≤ M → M ≤ N → ∀ (a : ℕ → ℤ), a d ≠ 0 →
    (∀ j, j ≤ d → |a j| ≤ (c : ℤ) * (N : ℤ) ^ (d - j)) →
    ∀ (h : ℤ), h ∈ (Finset.Icc (-(M : ℤ)) (M : ℤ)).erase 0 → ∀ Q : ℤ,
      (BCount (fun n => polyEval a d n) M h (4 * 8 ^ (d - 3)) Q : ℝ)
        ≤ max (R₀ (coeffConst c d)) 1 * (N : ℝ) ^ (8 ^ (d - 2) - (d - 1)) := by
  intro c N M hN hM1 hMN a had ha h hS Q
  have h1 := BCount_le_integral (fun n => polyEval a d n) M h (4 * 8 ^ (d - 3))
    (one_le_s d) Q
  rw [two_mul_s hd] at h1
  exact le_trans h1 (integral_norm_T_pow_le_R hd hMV c N M hN hM1 hMN a had ha h hS)

/-- **第 8 步**：四重和被 `Rtot^4` 乘「满足 `Q₁+…+Q₄ = 0` 的项数」控制。 -/
theorem four_sum_le_count {d : ℕ} (hd : 3 ≤ d) {R₀ : ℕ → ℝ}
    (hMV : MVSBound (d - 1) R₀) :
    ∀ (c N M : ℕ), 1 ≤ N → 1 ≤ M → M ≤ N → ∀ (a : ℕ → ℤ), a d ≠ 0 →
    (∀ j, j ≤ d → |a j| ≤ (c : ℤ) * (N : ℤ) ^ (d - j)) →
    (∫ α in (0 : ℝ)..1, (SigTerm a d M α) ^ 4)
      ≤ (max (R₀ (coeffConst c d)) 1 * (N : ℝ) ^ (8 ^ (d - 2) - (d - 1))) ^ 4
        * (∑ h1 ∈ (Finset.Icc (-(M : ℤ)) (M : ℤ)).erase 0,
          ∑ h2 ∈ (Finset.Icc (-(M : ℤ)) (M : ℤ)).erase 0,
          ∑ h3 ∈ (Finset.Icc (-(M : ℤ)) (M : ℤ)).erase 0,
          ∑ h4 ∈ (Finset.Icc (-(M : ℤ)) (M : ℤ)).erase 0,
          ∑ Q1 ∈ QSet (fun n => polyEval a d n) M h1 (4 * 8 ^ (d - 3)),
          ∑ Q2 ∈ QSet (fun n => polyEval a d n) M h2 (4 * 8 ^ (d - 3)),
          ∑ Q3 ∈ QSet (fun n => polyEval a d n) M h3 (4 * 8 ^ (d - 3)),
          ∑ Q4 ∈ QSet (fun n => polyEval a d n) M h4 (4 * 8 ^ (d - 3)),
            (if Q1 + Q2 + Q3 + Q4 = 0 then (1 : ℝ) else 0)) := by
  intro c N M hN hM1 hMN a had ha
  rw [four_sum_eq hd a M]
  set Rt : ℝ := max (R₀ (coeffConst c d)) 1 * (N : ℝ) ^ (8 ^ (d - 2) - (d - 1)) with hRt
  have hRtpos : 0 < Rt := by
    rw [hRt]
    have h1 : (0 : ℝ) < max (R₀ (coeffConst c d)) 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
    have h3 : (0 : ℝ) < (N : ℝ) ^ (8 ^ (d - 2) - (d - 1)) := by
      have : (0:ℝ) < N := by exact_mod_cast hN
      positivity
    exact mul_pos h1 h3
  have hRt0 : 0 ≤ Rt := le_of_lt hRtpos
  simp only [Finset.mul_sum]
  refine Finset.sum_le_sum (fun h1 h1S => Finset.sum_le_sum (fun h2 h2S =>
    Finset.sum_le_sum (fun h3 h3S => Finset.sum_le_sum (fun h4 h4S =>
    Finset.sum_le_sum (fun Q1 Q1S => Finset.sum_le_sum (fun Q2 Q2S =>
    Finset.sum_le_sum (fun Q3 Q3S => Finset.sum_le_sum (fun Q4 Q4S => ?_))))))))
  have hB1 : (BCount (fun n => polyEval a d n) M h1 (4 * 8 ^ (d - 3)) Q1 : ℝ) ≤ Rt := by
    rw [hRt]; exact BCount_le_Rtot hd hMV c N M hN hM1 hMN a had ha h1 h1S Q1
  have hB2 : (BCount (fun n => polyEval a d n) M h2 (4 * 8 ^ (d - 3)) Q2 : ℝ) ≤ Rt := by
    rw [hRt]; exact BCount_le_Rtot hd hMV c N M hN hM1 hMN a had ha h2 h2S Q2
  have hB3 : (BCount (fun n => polyEval a d n) M h3 (4 * 8 ^ (d - 3)) Q3 : ℝ) ≤ Rt := by
    rw [hRt]; exact BCount_le_Rtot hd hMV c N M hN hM1 hMN a had ha h3 h3S Q3
  have hB4 : (BCount (fun n => polyEval a d n) M h4 (4 * 8 ^ (d - 3)) Q4 : ℝ) ≤ Rt := by
    rw [hRt]; exact BCount_le_Rtot hd hMV c N M hN hM1 hMN a had ha h4 h4S Q4
  have hC1 : (0 : ℝ) ≤ (BCount (fun n => polyEval a d n) M h1 (4 * 8 ^ (d - 3)) Q1 : ℝ) := by
    positivity
  have hC2 : (0 : ℝ) ≤ (BCount (fun n => polyEval a d n) M h2 (4 * 8 ^ (d - 3)) Q2 : ℝ) := by
    positivity
  have hC3 : (0 : ℝ) ≤ (BCount (fun n => polyEval a d n) M h3 (4 * 8 ^ (d - 3)) Q3 : ℝ) := by
    positivity
  have hC4 : (0 : ℝ) ≤ (BCount (fun n => polyEval a d n) M h4 (4 * 8 ^ (d - 3)) Q4 : ℝ) := by
    positivity
  have hP : (BCount (fun n => polyEval a d n) M h1 (4 * 8 ^ (d - 3)) Q1 : ℝ)
      * (BCount (fun n => polyEval a d n) M h2 (4 * 8 ^ (d - 3)) Q2 : ℝ)
      * (BCount (fun n => polyEval a d n) M h3 (4 * 8 ^ (d - 3)) Q3 : ℝ)
      * (BCount (fun n => polyEval a d n) M h4 (4 * 8 ^ (d - 3)) Q4 : ℝ) ≤ Rt ^ 4 := by
    have h12 : (BCount (fun n => polyEval a d n) M h1 (4 * 8 ^ (d - 3)) Q1 : ℝ)
        * (BCount (fun n => polyEval a d n) M h2 (4 * 8 ^ (d - 3)) Q2 : ℝ) ≤ Rt * Rt :=
      mul_le_mul hB1 hB2 hC2 hRt0
    have h123 : (BCount (fun n => polyEval a d n) M h1 (4 * 8 ^ (d - 3)) Q1 : ℝ)
        * (BCount (fun n => polyEval a d n) M h2 (4 * 8 ^ (d - 3)) Q2 : ℝ)
        * (BCount (fun n => polyEval a d n) M h3 (4 * 8 ^ (d - 3)) Q3 : ℝ) ≤ Rt * Rt * Rt :=
      mul_le_mul h12 hB3 hC3 (by positivity)
    have h1234 := mul_le_mul h123 hB4 hC4 (by positivity)
    calc (BCount (fun n => polyEval a d n) M h1 (4 * 8 ^ (d - 3)) Q1 : ℝ)
          * (BCount (fun n => polyEval a d n) M h2 (4 * 8 ^ (d - 3)) Q2 : ℝ)
          * (BCount (fun n => polyEval a d n) M h3 (4 * 8 ^ (d - 3)) Q3 : ℝ)
          * (BCount (fun n => polyEval a d n) M h4 (4 * 8 ^ (d - 3)) Q4 : ℝ)
        ≤ Rt * Rt * Rt * Rt := h1234
      _ = Rt ^ 4 := by ring
  by_cases hc : Q1 + Q2 + Q3 + Q4 = 0
  · rw [if_pos hc, if_pos hc, mul_one]
    exact hP
  · rw [if_neg hc, if_neg hc, mul_zero]


end Waring
