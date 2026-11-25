/- GID: D5/S3/Arith/Additive/Waring/WaringIndStep
   generality: G
   mirror-B: D5/B/S3/Arith/Additive/Waring/WaringIndStep
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Third-party formalization of the qualitative Hilbert–Waring theorem. -/

/- Source: https://github.com/yunyougu50-create/waring-lean4/blob/cd0735c253f3b640262fcc74a61306cb41e23765/WaringIndStep.lean#L1-L585
   Modified for this repository. Local imports use their D5 module paths.
   Selected declaration closure and supporting source.
   Full Apache-2.0 license: D5/S3/Arith/Additive/Waring/WaringDensity.lean. -/

/-
Copyright (c) 2026 The Waring formalization authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Waring formalization authors
-/
import D5.S3.Arith.Additive.Waring.WaringWeylInq
import D5.S3.Arith.Additive.Waring.WaringLemma7
import D5.S3.Arith.Additive.Waring.WaringHolder
import D5.S3.Arith.Additive.Waring.WaringCoeffBound
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

open Finset intervalIntegral

namespace Waring

/- Adapted from https://github.com/yunyougu50-create/waring-lean4/blob/cd0735c253f3b640262fcc74a61306cb41e23765/WaringBPow.lean#L1-L184 -/

/-!
# `|b_h|^{2s}` 的按频率展开（一般 `s`）

对任意自然数 `s`，差分和的偶次幂具有如下相位展开：

```text
|b_h|^{2s} = Σ_Q BCount(f,N,h,s,Q) · e(Q·α),
```

其中 `BCount` 是 `s` 元组的解数
`#{(u,v) : (Fin s → TS)²  |  Σ_i q(u i) − Σ_i q(v i) = Q}`，`q n = f(n+h) − f(n)`。

证明分三步：

* `T_pow_expand`：`b^s = Σ_{u : Fin s → TS} e(α · Qsum u)`（`Finset.sum_pow'` + 乘性 `e_sum_finset`）；
* `conjT_pow_expand`：`(conj b)^s = Σ_v e(−α · Qsum v)`；
* `sum_diff_fiber_pi`：把 `(Fin s → ℕ)` 上的双和按 `Qsum u − Qsum v` 的值分组
  （`Finset.sum_product` + `Finset.sum_fiberwise_of_maps_to'`）。

最后 `↑(normSq b) = conj b · b`，配合 `mul_pow` 组装。
-/

/-- `q n = f(n+h) − f(n)`（`b_h` 的相位差分）。 -/
noncomputable def dshift (f : ℤ → ℤ) (h : ℤ) (n : ℕ) : ℤ := f ((n : ℤ) + h) - f (n : ℤ)

/-- `Qsum u = Σ_{i : Fin s} q(u i)`，即 `s` 元组的相位和。 -/
noncomputable def Qsum (f : ℤ → ℤ) (h : ℤ) {s : ℕ} (u : Fin s → ℕ) : ℤ :=
  ∑ i : Fin s, dshift f h (u i)

/-- 指标集 `TS^{×s} = (Fin s → TS N h)`。 -/
noncomputable def PIdx (N : ℕ) (h : ℤ) (s : ℕ) : Finset (Fin s → ℕ) :=
  Fintype.piFinset (fun _ => TS N h)

/-- **频率 `Q` 的计数**：`(u,v) : (Fin s → TS)²` 中使 `Qsum u − Qsum v = Q` 的对数。 -/
noncomputable def BCount (f : ℤ → ℤ) (N : ℕ) (h : ℤ) (s : ℕ) (Q : ℤ) : ℕ :=
  ((PIdx N h s).product (PIdx N h s)).filter
    (fun p : (Fin s → ℕ) × (Fin s → ℕ) => Qsum f h p.1 - Qsum f h p.2 = Q) |>.card

/-- 所有可能出现的频率集合（`image Qsum` 的两两差）。 -/
noncomputable def QSet (f : ℤ → ℤ) (N : ℕ) (h : ℤ) (s : ℕ) : Finset ℤ :=
  ((PIdx N h s).image (Qsum f h)).biUnion
    (fun a => ((PIdx N h s).image (Qsum f h)).image (fun b => b - a))

/-- **加法特征是可乘的**（`Finset` 版）：`e (Σ x_i) = Π e (x_i)`。

（与 `WaringQuadratic.e_sum` 的 `Fintype` 版分离命名。） -/
theorem e_sum_finset {ι : Type*} (s : Finset ι) (x : ι → ℝ) :
    e (∑ i ∈ s, x i) = ∏ i ∈ s, e (x i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [e_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, e_add, ih]

/-- `b_h` 写成 `TS` 上的和。 -/
theorem T_eq_TS (f : ℤ → ℤ) (N : ℕ) (h : ℤ) (α : ℝ) :
    T f N α h = ∑ n ∈ TS N h, e ((dshift f h n : ℝ) * α) := by
  rw [T, TS]
  rfl

/-- **`b_h^s` 的单层展开**：`b^s = Σ_{u : Fin s → TS} e(α · Qsum u)`。 -/
theorem T_pow_expand (f : ℤ → ℤ) (N : ℕ) (h : ℤ) (α : ℝ) (s : ℕ) :
    (T f N α h) ^ s = ∑ u ∈ PIdx N h s, e ((Qsum f h u : ℝ) * α) := by
  rw [T_eq_TS, PIdx, Finset.sum_pow']
  refine Finset.sum_congr rfl (fun u _ => ?_)
  rw [← e_sum_finset]
  congr 1
  have hQ : ((Qsum f h u : ℤ) : ℝ) = ∑ i : Fin s, ((dshift f h (u i) : ℤ) : ℝ) := by
    rw [Qsum]
    push_cast
    rfl
  rw [hQ, Finset.sum_mul]

/-- **`(conj b_h)^s` 的单层展开**：`(conj b)^s = Σ_{v : Fin s → TS} e(−α · Qsum v)`。 -/
theorem conjT_pow_expand (f : ℤ → ℤ) (N : ℕ) (h : ℤ) (α : ℝ) (s : ℕ) :
    ((starRingEnd ℂ) (T f N α h)) ^ s
      = ∑ v ∈ PIdx N h s, e (-((Qsum f h v : ℝ) * α)) := by
  have hconj : (starRingEnd ℂ) (T f N α h)
      = ∑ n ∈ TS N h, e (-((dshift f h n : ℝ) * α)) := by
    rw [T_eq_TS, map_sum]
    exact Finset.sum_congr rfl (fun n _ => by rw [← e_neg])
  rw [hconj, PIdx, Finset.sum_pow']
  refine Finset.sum_congr rfl (fun v _ => ?_)
  rw [← e_sum_finset]
  congr 1
  have hQ : ((Qsum f h v : ℤ) : ℝ) = ∑ i : Fin s, ((dshift f h (v i) : ℤ) : ℝ) := by
    rw [Qsum]
    push_cast
    rfl
  rw [hQ, Finset.sum_mul, ← Finset.sum_neg_distrib]

/-- **按 ℤ 值函数的值差分组（`Fin s → ℕ` 版本）**：
`Σ_{u,v} F (q u − q v) = Σ_Q (#{q u − q v = Q}) • F Q`。 -/
theorem sum_diff_fiber_pi {M : Type*} [AddCommMonoid M] {ι : Type*} [Fintype ι]
    [DecidableEq ι] (s : Finset ℕ) (q : (ι → ℕ) → ℤ) (F : ℤ → M) :
    (∑ u ∈ Fintype.piFinset (fun _ : ι => s),
        ∑ v ∈ Fintype.piFinset (fun _ : ι => s), F (q u - q v))
      = ∑ Q ∈ ((Fintype.piFinset (fun _ : ι => s)).image q).biUnion
            (fun a => ((Fintype.piFinset (fun _ : ι => s)).image q).image
              (fun b => b - a)),
          (((Fintype.piFinset (fun _ : ι => s)).product
            (Fintype.piFinset (fun _ : ι => s))).filter
            (fun p : (ι → ℕ) × (ι → ℕ) => q p.1 - q p.2 = Q)).card • F Q := by
  classical
  rw [show (∑ u ∈ Fintype.piFinset (fun _ : ι => s),
        ∑ v ∈ Fintype.piFinset (fun _ : ι => s), F (q u - q v))
      = ∑ p ∈ (Fintype.piFinset (fun _ : ι => s)).product
            (Fintype.piFinset (fun _ : ι => s)), F (q p.1 - q p.2) from
    (Finset.sum_product (Fintype.piFinset (fun _ : ι => s))
      (Fintype.piFinset (fun _ : ι => s))
      (fun p : (ι → ℕ) × (ι → ℕ) => F (q p.1 - q p.2))).symm]
  have hmaps : ∀ p ∈ (Fintype.piFinset (fun _ : ι => s)).product
      (Fintype.piFinset (fun _ : ι => s)),
      q p.1 - q p.2 ∈ ((Fintype.piFinset (fun _ : ι => s)).image q).biUnion
        (fun a => ((Fintype.piFinset (fun _ : ι => s)).image q).image (fun b => b - a)) := by
    intro p hp
    obtain ⟨u, v⟩ := p
    obtain ⟨hu, hv⟩ := Finset.mem_product.mp hp
    refine Finset.mem_biUnion.mpr ⟨q v, Finset.mem_image_of_mem q hv, ?_⟩
    exact Finset.mem_image_of_mem (fun b => b - q v) (Finset.mem_image_of_mem q hu)
  rw [← Finset.sum_fiberwise_of_maps_to' hmaps F]
  exact Finset.sum_congr rfl (fun Q _ => Finset.sum_const _)

/-- **`|b_h|^{2s}` 的按频率展开**（一般 `s`）：
`|b_h|^{2s} = Σ_Q BCount(Q) · e(Q·α)`。 -/
theorem normSq_pow_T_fiber (f : ℤ → ℤ) (N : ℕ) (h : ℤ) (α : ℝ) (s : ℕ) :
    ((Complex.normSq (T f N α h) : ℝ) : ℂ) ^ s
      = ∑ Q ∈ QSet f N h s, (BCount f N h s Q : ℂ) * e ((Q : ℝ) * α) := by
  -- 1) `↑(normSq b) = conj b · b`
  have hbase : ((Complex.normSq (T f N α h) : ℝ) : ℂ)
      = (starRingEnd ℂ) (T f N α h) * T f N α h := Complex.normSq_eq_conj_mul_self
  -- 2) 两边各自做 `s` 次幂的单层展开
  rw [hbase, mul_pow, conjT_pow_expand, T_pow_expand, Finset.sum_mul_sum]
  -- 3) 每项合并成 `e(α(Qsum u − Qsum v))`
  have hterm : ∀ v u : Fin s → ℕ,
      e (-((Qsum f h v : ℝ) * α)) * e ((Qsum f h u : ℝ) * α)
        = e (((Qsum f h u - Qsum f h v : ℤ) : ℝ) * α) := by
    intro v u
    rw [← e_add]
    congr 1
    push_cast
    ring
  rw [Finset.sum_congr rfl (fun v _ => Finset.sum_congr rfl (fun u _ => hterm v u))]
  -- 4) 交换求和顺序并按差分组
  rw [Finset.sum_comm]
  simp only [PIdx, QSet, BCount]
  rw [sum_diff_fiber_pi (TS N h) (Qsum f h) (fun Q : ℤ => e ((Q : ℝ) * α))]
  -- 5) `ℕ`-倍转成复数乘法
  refine Finset.sum_congr rfl (fun Q _ => ?_)
  rw [nsmul_eq_mul]

/- Adapted from https://github.com/yunyougu50-create/waring-lean4/blob/cd0735c253f3b640262fcc74a61306cb41e23765/WaringQuadSum.lean#L1-L239 -/

/-- **桥接**：多项式情形 `dshift` 分解出显式 `h` 因子（`diffH_polyEval`）。 -/
theorem dshift_polyEval (a : ℕ → ℤ) (d : ℕ) (h : ℤ) (n : ℕ) :
    dshift (polyEval a d) h n = h * polyEval (diffCoeff a d h) d (n : ℤ) := by
  have hh := congrFun (diffH_polyEval a d h) (n : ℤ)
  unfold diffH at hh
  simpa [dshift] using hh

/-- `α ↦ e(c·α)` 连续。 -/
theorem continuous_e_mul (c : ℝ) : Continuous fun α : ℝ => e (c * α) := by
  unfold e
  fun_prop

/-- 有限和与区间积分交换（连续版本）。 -/
theorem integral_finsetSum_cont {ι : Type*} [DecidableEq ι] (s : Finset ι) (g : ι → ℝ → ℂ)
    (h : ∀ i ∈ s, Continuous (g i)) :
    (∫ α in (0:ℝ)..1, ∑ i ∈ s, g i α) = ∑ i ∈ s, ∫ α in (0:ℝ)..1, g i α := by
  rw [intervalIntegral.integral_finsetSum]
  intro i hi
  exact (h i hi).intervalIntegrable 0 1

/-- **归纳命题 `P(d)`**（Jameson Theorem 1 的精确形式）。 -/
def MeanValueBound (d : ℕ) : Prop :=
  ∃ R : ℕ → ℝ, (∀ c, 0 < R c) ∧
    ∀ (c : ℕ) (N : ℕ), 1 ≤ N → ∀ (a : ℕ → ℤ), a d ≠ 0 →
      (∀ j, j ≤ d → |a j| ≤ (c : ℤ) * (N : ℤ) ^ (d - j)) →
      (∫ α in (0 : ℝ)..1,
          ‖expSum (fun n => polyEval a d n) N α‖ ^ (8 ^ (d - 1)))
        ≤ R c * (N : ℝ) ^ (8 ^ (d - 1) - d)

/-- `h ≥ 0` 时 `TS N h = {0, …, N−h}`。 -/
theorem TS_eq_range {N : ℕ} {h : ℤ} (hh : 0 ≤ h) (hN : h.toNat ≤ N) :
    TS N h = Finset.range (N + 1 - h.toNat) := by
  ext n
  rw [TS, Finset.mem_filter, Finset.mem_range, Finset.mem_Icc, Finset.mem_range]
  have hcast : ((h.toNat : ℕ) : ℤ) = h := Int.toNat_of_nonneg hh
  constructor
  · rintro ⟨hn, h1, h2⟩
    have h3 : (n : ℤ) + h ≤ (N : ℤ) := by linarith
    have h4 : ((n + h.toNat : ℕ) : ℤ) ≤ (N : ℤ) := by
      push_cast [hcast]
      exact h3
    have h5 : n + h.toNat ≤ N := by exact_mod_cast h4
    omega
  · intro hn
    have h4 : n + h.toNat ≤ N := by omega
    have h4' : ((n : ℤ)) + h ≤ (N : ℤ) := by
      have : ((n + h.toNat : ℕ) : ℤ) ≤ (N : ℤ) := by exact_mod_cast h4
      push_cast [hcast] at this
      exact this
    refine ⟨by omega, by linarith, by linarith⟩

/-- 多项式情形 `T` 的相位分解：`T (polyEval a d) N α h = Σ_{n∈TS} e(αh·φ(n))`。 -/
theorem T_polyEval_eq (a : ℕ → ℤ) (d : ℕ) (N : ℕ) (h : ℤ) (α : ℝ) :
    T (polyEval a d) N α h
      = ∑ n ∈ TS N h,
          e ((α * (h : ℝ)) * ((polyEval (diffCoeff a d h) d (n : ℤ) : ℤ) : ℝ)) := by
  rw [T_eq_TS]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [dshift_polyEval]
  congr 1
  push_cast
  ring

/-- `h ≥ 0` 时 `TS N (−h) = {h, …, N}`。 -/
theorem TS_neg_eq_Icc {N : ℕ} {h : ℤ} (hh : 0 ≤ h) :
    TS N (-h) = Finset.Icc h.toNat N := by
  ext n
  simp only [TS, Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
  have hcast : ((h.toNat : ℕ) : ℤ) = h := Int.toNat_of_nonneg hh
  constructor
  · rintro ⟨hn, h1, h2⟩
    refine ⟨?_, by omega⟩
    have h3 : (h : ℤ) ≤ (n : ℤ) := by linarith
    have h4 : ((h.toNat : ℕ) : ℤ) ≤ (n : ℤ) := by rw [hcast]; exact h3
    exact_mod_cast h4
  · rintro ⟨h1, h2⟩
    have h1' : ((h.toNat : ℕ) : ℤ) ≤ (n : ℤ) := by exact_mod_cast h1
    rw [hcast] at h1'
    refine ⟨by omega, by linarith, by linarith⟩

/-- `b_{−h}` 是 `b_h` 的共轭（`h ≥ 0`）。 -/
theorem T_neg {f : ℤ → ℤ} {N : ℕ} {h : ℤ} (hh : 0 ≤ h) (hN : h.toNat ≤ N) (α : ℝ) :
    T f N α (-h) = (starRingEnd ℂ) (T f N α h) := by
  have hconj : (starRingEnd ℂ) (T f N α h)
      = ∑ n ∈ TS N h, e (-((dshift f h n : ℝ) * α)) := by
    rw [T_eq_TS, map_sum]
    exact Finset.sum_congr rfl (fun n _ => by rw [← e_neg])
  rw [hconj, T_eq_TS, TS_neg_eq_Icc hh, TS_eq_range hh hN]
  rw [← Finset.Ico_succ_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  simp only [dshift, Nat.cast_add, Int.toNat_of_nonneg hh]
  rw [show h + (n : ℤ) + -h = n by omega, add_comm h (n : ℤ)]
  congr 1
  push_cast
  ring

/-- `‖b_{−h}‖ = ‖b_h‖`（`h ≥ 0`）。 -/
theorem norm_T_neg {f : ℤ → ℤ} {N : ℕ} {h : ℤ} (hh : 0 ≤ h) (hN : h.toNat ≤ N) (α : ℝ) :
    ‖T f N α (-h)‖ = ‖T f N α h‖ := by
  rw [T_neg hh hN]
  simp

set_option maxHeartbeats 1000000 in
/-- **变量替换**（`h > 0`）：`b_h` 的 `m` 阶矩等于差分多项式 `φ` 的指数和的 `m` 阶矩，
其中 `φ = polyEval (diffCoeff a d h) d`（次数降一），求和长度从 `N+1` 变为 `N−h+1`。 -/
theorem integral_norm_T_pow_eq {a : ℕ → ℤ} {d : ℕ} {N : ℕ} {h : ℤ}
    (hh : 0 < h) (hN : h.toNat ≤ N) (m : ℕ) :
    (∫ α in (0 : ℝ)..1, ‖T (polyEval a d) N α h‖ ^ m)
      = ∫ β in (0 : ℝ)..1,
          ‖expSum (fun n => polyEval (diffCoeff a d h) d n) (N - h.toNat) β‖ ^ m := by
  have hh0 : 0 ≤ h := le_of_lt hh
  have hhR : (h : ℝ) ≠ 0 := by
    have hpos : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hh
    exact ne_of_gt hpos
  set K : ℕ := N - h.toNat with hK
  have hrank : N + 1 - h.toNat = K + 1 := by rw [hK]; omega
  have hTS : TS N h = Finset.range (K + 1) := by rw [TS_eq_range hh0 hN, hrank]
  set φ : ℕ → ℝ := fun n => ((polyEval (diffCoeff a d h) d (n : ℤ) : ℤ) : ℝ) with hφ
  set G : ℝ → ℝ := fun β => ‖∑ n ∈ Finset.range (K + 1), e (β * φ n)‖ ^ m with hG
  -- (1) 被积函数 = `G (h·α)`
  have hstep1 : (∫ α in (0 : ℝ)..1, ‖T (polyEval a d) N α h‖ ^ m)
      = ∫ α in (0 : ℝ)..1, G ((h : ℝ) * α) := by
    apply intervalIntegral.integral_congr
    intro α _
    show ‖T (polyEval a d) N α h‖ ^ m = G ((h : ℝ) * α)
    have hTeq : T (polyEval a d) N α h
        = ∑ n ∈ Finset.range (K + 1), e ((α * (h : ℝ)) * φ n) := by
      rw [T_polyEval_eq, hTS]
    rw [hTeq, hG]
    apply congrArg (fun x : ℂ => ‖x‖ ^ m)
    refine Finset.sum_congr rfl (fun n _ => ?_)
    apply congrArg e
    ring
  -- (2) `G` 周期 1
  have hper : Function.Periodic G 1 := by
    intro β
    have hsum : (∑ n ∈ Finset.range (K + 1), e ((β + 1) * φ n))
        = ∑ n ∈ Finset.range (K + 1), e (β * φ n) := by
      refine Finset.sum_congr rfl (fun n _ => ?_)
      have hsp : (β + 1) * φ n = β * φ n + φ n := by ring
      rw [hsp, e_add]
      have hφn : φ n = ((polyEval (diffCoeff a d h) d (n : ℤ) : ℤ) : ℝ) := by rw [hφ]
      rw [hφn, e_int, mul_one]
    show ‖∑ n ∈ Finset.range (K + 1), e ((β + 1) * φ n)‖ ^ m
      = ‖∑ n ∈ Finset.range (K + 1), e (β * φ n)‖ ^ m
    rw [hsum]
  -- (3) 连续性 / 可积性
  have hcont : Continuous G := by
    rw [hG]
    apply Continuous.pow
    apply Continuous.norm
    apply continuous_finsetSum
    intro n _
    simpa only [mul_comm] using continuous_e_mul (φ n)
  have hint : ∀ t₁ t₂ : ℝ, IntervalIntegrable G MeasureTheory.volume t₁ t₂ :=
    fun t₁ t₂ => hcont.intervalIntegrable t₁ t₂
  -- (4) 缩放
  have hcomp : (∫ α in (0 : ℝ)..1, G ((h : ℝ) * α))
      = (h : ℝ)⁻¹ * ∫ β in (0 : ℝ)..(h : ℝ), G β := by
    have h := intervalIntegral.integral_comp_mul_left (f := G) (a := (0 : ℝ)) (b := 1)
      (c := (h : ℝ)) hhR
    simpa using h
  -- (5) 周期性 ⇒ 一个整周期
  have hzs : (∫ β in (0 : ℝ)..(h : ℝ), G β) = (h : ℝ) * ∫ β in (0 : ℝ)..1, G β := by
    have h := Function.Periodic.intervalIntegral_add_zsmul_eq hper h (0 : ℝ) hint
    simpa using h
  -- (6) `G` 就是 `‖expSum φ K‖^m`
  have hfinal : (∫ β in (0 : ℝ)..1, G β)
      = ∫ β in (0 : ℝ)..1,
          ‖expSum (fun n => polyEval (diffCoeff a d h) d n) K β‖ ^ m := by
    apply intervalIntegral.integral_congr
    intro β _
    show G β = ‖expSum (fun n => polyEval (diffCoeff a d h) d n) K β‖ ^ m
    rw [hG]
    unfold expSum
    apply congrArg (fun x : ℂ => ‖x‖ ^ m)
    refine Finset.sum_congr rfl (fun n _ => ?_)
    apply congrArg e
    rw [hφ]
    exact mul_comm β _
  calc (∫ α in (0 : ℝ)..1, ‖T (polyEval a d) N α h‖ ^ m)
      = ∫ α in (0 : ℝ)..1, G ((h : ℝ) * α) := hstep1
    _ = (h : ℝ)⁻¹ * ∫ β in (0 : ℝ)..(h : ℝ), G β := hcomp
    _ = (h : ℝ)⁻¹ * ((h : ℝ) * ∫ β in (0 : ℝ)..1, G β) := by rw [hzs]
    _ = ∫ β in (0 : ℝ)..1, G β := inv_mul_cancel_left₀ hhR _
    _ = ∫ β in (0 : ℝ)..1,
          ‖expSum (fun n => polyEval (diffCoeff a d h) d n) K β‖ ^ m := hfinal
    _ = ∫ β in (0 : ℝ)..1,
          ‖expSum (fun n => polyEval (diffCoeff a d h) d n) (N - h.toNat) β‖ ^ m := by
        rw [hK]

/-- 末项系数为零时，`d` 次与 `d−1` 次多项式求值相同。 -/
theorem polyEval_eq_of_last_zero (b : ℕ → ℤ) {d : ℕ} (hd : 1 ≤ d) (hb : b d = 0) (n : ℤ) :
    polyEval b d n = polyEval b (d - 1) n := by
  unfold polyEval
  rw [show d + 1 = (d - 1) + 1 + 1 by omega, Finset.sum_range_succ]
  have hlast : b ((d - 1) + 1) * n ^ ((d - 1) + 1) = 0 := by
    rw [show (d - 1) + 1 = d by omega, hb]
    ring
  rw [hlast, add_zero]

/-- **差分多项式最高次系数**：`diffCoeff a d h (d−1) = a_d · d`（`d ≥ 1`）。 -/
theorem diffCoeff_last {a : ℕ → ℤ} {d : ℕ} (hd : 1 ≤ d) (h : ℤ) :
    diffCoeff a d h (d - 1) = a d * (d : ℤ) := by
  unfold diffCoeff
  have hset : Finset.Ico (d - 1 + 1) (d + 1) = {d} := by
    ext j
    simp only [Finset.mem_Ico, Finset.mem_singleton]
    omega
  rw [hset, Finset.sum_singleton]
  have hzero : d - 1 - (d - 1) = 0 := by omega
  rw [hzero, pow_zero, mul_one]
  have hch : d.choose (d - 1) = d := by
    obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
    simpa using Nat.choose_succ_self_right e
  rw [hch]

/-- 差分多项式系数的统一常数。 -/
def coeffConst (c d : ℕ) : ℕ :=
  c * ∑ r ∈ Finset.range d, ∑ j ∈ Finset.range (d + 1), Nat.choose j r

/-- **统一次数界的系数界**：`|diffCoeff a d h r| ≤ (coeffConst c d)·N^{d−1−r}`。 -/
theorem diffCoeff_bound' {a : ℕ → ℤ} {d : ℕ} {h : ℤ} {c N : ℕ}
    (ha : ∀ j, j ≤ d → |a j| ≤ (c : ℤ) * (N : ℤ) ^ (d - j))
    (hh : |h| ≤ (N : ℤ)) (r : ℕ) (hr : r < d) :
    |diffCoeff a d h r| ≤ (coeffConst c d : ℤ) * (N : ℤ) ^ (d - 1 - r) := by
  have hbase := diffCoeff_bound (a := a) (d := d) (h := h) (C := c) (N := N) ha hh r hr
  have hsub : Finset.Ico (r + 1) (d + 1) ⊆ Finset.range (d + 1) := by
    intro j hj
    rw [Finset.mem_Ico] at hj
    rw [Finset.mem_range]
    omega
  have hSle : (∑ j ∈ Finset.Ico (r + 1) (d + 1), ((j.choose r : ℕ) : ℤ))
      ≤ (∑ r' ∈ Finset.range d, ∑ j ∈ Finset.range (d + 1), ((Nat.choose j r' : ℕ) : ℤ)) := by
    have h1 : (∑ j ∈ Finset.Ico (r + 1) (d + 1), ((j.choose r : ℕ) : ℤ))
        ≤ ∑ j ∈ Finset.range (d + 1), ((j.choose r : ℕ) : ℤ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => by positivity)
    have h2 : (∑ j ∈ Finset.range (d + 1), ((j.choose r : ℕ) : ℤ))
        ≤ (∑ r' ∈ Finset.range d, ∑ j ∈ Finset.range (d + 1), ((Nat.choose j r' : ℕ) : ℤ)) := by
      refine Finset.single_le_sum (f := fun r' => ∑ j ∈ Finset.range (d + 1),
        ((Nat.choose j r' : ℕ) : ℤ)) (fun i _ => by positivity) ?_
      rw [Finset.mem_range]
      exact hr
    exact le_trans h1 h2
  have hN0 : (0 : ℤ) ≤ (N : ℤ) ^ (d - 1 - r) := by positivity
  have hkey : (c : ℤ) * (∑ j ∈ Finset.Ico (r + 1) (d + 1), ((j.choose r : ℕ) : ℤ))
      ≤ (coeffConst c d : ℤ) := by
    have hc0 : (0 : ℤ) ≤ (c : ℤ) := by positivity
    calc (c : ℤ) * (∑ j ∈ Finset.Ico (r + 1) (d + 1), ((j.choose r : ℕ) : ℤ))
        ≤ (c : ℤ) * (∑ r' ∈ Finset.range d,
            ∑ j ∈ Finset.range (d + 1), ((Nat.choose j r' : ℕ) : ℤ)) :=
          mul_le_mul_of_nonneg_left hSle hc0
      _ = (coeffConst c d : ℤ) := by
          rw [coeffConst]
          push_cast
          ring
  calc |diffCoeff a d h r|
      ≤ (c : ℤ) * (∑ j ∈ Finset.Ico (r + 1) (d + 1), (j.choose r : ℤ))
        * (N : ℤ) ^ (d - 1 - r) := hbase
    _ ≤ (coeffConst c d : ℤ) * (N : ℤ) ^ (d - 1 - r) :=
        mul_le_mul_of_nonneg_right hkey hN0

/-

set_option maxHeartbeats 4000000 in
/-- **单个 `b_h` 的矩界**：`P(d−1) ⇒ ∫‖b_h‖^{8^{d−2}} ≤ R·N^{8^{d−2}−(d−1)}`，
对一切 `h ≠ 0`、`|h| ≤ N`。 -/
theorem integral_norm_T_pow_le {d : ℕ} (hd : 3 ≤ d) (hMV : MeanValueBound (d - 1)) :
    ∃ R : ℕ → ℝ, (∀ c, 0 < R c) ∧
      ∀ (c : ℕ) (N : ℕ), 1 ≤ N → ∀ (a : ℕ → ℤ), a d ≠ 0 →
      (∀ j, j ≤ d → |a j| ≤ (c : ℤ) * (N : ℤ) ^ (d - j)) →
      ∀ h ∈ (Finset.Icc (-(N : ℤ)) (N : ℤ)).erase 0,
        (∫ α in (0 : ℝ)..1, ‖T (polyEval a d) N α h‖ ^ (8 ^ (d - 2)))
          ≤ R c * (N : ℝ) ^ (8 ^ (d - 2) - (d - 1)) := by
  obtain ⟨R₀, hR₀pos, hR₀b⟩ := hMV
  have hd1 : 1 ≤ d := by omega
  have hexp : (d - 1) - 1 = d - 2 := by omega
  refine ⟨fun c => max (R₀ (coeffConst c d)) 1, ?_, ?_⟩
  · intro c
    exact lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  intro c N hN a had ha h hS
  rw [Finset.mem_erase, Finset.mem_Icc] at hS
  obtain ⟨hne, hle1, hle2⟩ := hS
  -- 正步长 `g` 的情形
  have main : ∀ (g : ℤ), 0 < g → g.toNat ≤ N →
      (∫ α in (0 : ℝ)..1, ‖T (polyEval a d) N α g‖ ^ (8 ^ (d - 2)))
        ≤ max (R₀ (coeffConst c d)) 1 * (N : ℝ) ^ (8 ^ (d - 2) - (d - 1)) := by
    intro g hg hgN
    rw [integral_norm_T_pow_eq hg hgN (8 ^ (d - 2))]
    -- 次数从 `d` 降到 `d−1`
    have hstep : (∫ β in (0 : ℝ)..1,
        ‖expSum (fun n => polyEval (diffCoeff a d g) d n) (N - g.toNat) β‖ ^ (8 ^ (d - 2)))
        = ∫ β in (0 : ℝ)..1,
          ‖expSum (fun n => polyEval (diffCoeff a d g) (d - 1) n) (N - g.toNat) β‖ ^
            (8 ^ (d - 2)) := by
      apply intervalIntegral.integral_congr
      intro β _
      congr 2
      unfold expSum
      refine Finset.sum_congr rfl (fun n _ => ?_)
      congr 1
      rw [polyEval_eq_of_last_zero (diffCoeff a d g) hd1 (diffCoeff_eq_zero_of_le le_rfl)]
    rw [hstep]
    rcases Nat.eq_zero_or_pos (N - g.toNat) with h0 | h1pos
    · -- `N = g`：指数和只有一项
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
              intervalIntegral.integral_mono_on (by norm_num) (hcont.intervalIntegrable _ _)
                intervalIntegrable_const hpt
          _ = 1 := by simp
      refine le_trans hbound ?_
      have h1 : (1 : ℝ) ≤ max (R₀ (coeffConst c d)) 1 := le_max_right _ _
      have h2 : (1 : ℝ) ≤ (N : ℝ) ^ (8 ^ (d - 2) - (d - 1)) :=
        one_le_pow₀ (by exact_mod_cast hN)
      calc (1 : ℝ) = 1 * 1 := by ring
        _ ≤ max (R₀ (coeffConst c d)) 1 * (N : ℝ) ^ (8 ^ (d - 2) - (d - 1)) :=
            mul_le_mul h1 h2 (by norm_num) (by linarith)
    · -- 一般情形：用 `P(d−1)`
      have htoNatZ : ((g.toNat : ℕ) : ℤ) = g := Int.toNat_of_nonneg (le_of_lt hg)
      have habs : |g| ≤ (N : ℤ) := by
        have h2 : ((g.toNat : ℕ) : ℤ) ≤ (N : ℤ) := by exact_mod_cast hgN
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
      have hres := hR₀b (coeffConst c d) (N - g.toNat) h1pos (diffCoeff a d g) hblast hcoeff
      rw [hexp] at hres
      refine le_trans hres ?_
      apply mul_le_mul_of_nonneg_right (le_max_left _ _)
      positivity
  -- 分 `h` 的符号
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · -- `h < 0`：换成 `−h > 0`
    have htoNat : (-h).toNat ≤ N := by
      have h1 : (((-h).toNat : ℕ) : ℤ) = -h := Int.toNat_of_nonneg (by omega)
      have h2 : (((-h).toNat : ℕ) : ℤ) ≤ (N : ℤ) := by rw [h1]; linarith
      exact_mod_cast h2
    have heq : (∫ α in (0 : ℝ)..1, ‖T (polyEval a d) N α h‖ ^ (8 ^ (d - 2)))
        = ∫ α in (0 : ℝ)..1, ‖T (polyEval a d) N α (-h)‖ ^ (8 ^ (d - 2)) := by
      apply intervalIntegral.integral_congr
      intro α _
      have hh := norm_T_neg (f := polyEval a d) (N := N) (h := -h) (by omega) htoNat α
      rw [show ‖T (polyEval a d) N α h‖ = ‖T (polyEval a d) N α (-h)‖ by
        simpa using hh]
    rw [heq]
    exact main (-h) (by omega) htoNat
  · -- `h > 0`
    have htoNatN : h.toNat ≤ N := by
      have h1 : ((h.toNat : ℕ) : ℤ) = h := Int.toNat_of_nonneg (by omega)
      have h2 : ((h.toNat : ℕ) : ℤ) ≤ (N : ℤ) := by rw [h1]; exact hle2
      exact_mod_cast h2
    exact main h hpos htoNatN
-/

/-- 不出现在 `QSet` 中的频率对应的计数为 `0`。 -/
theorem BCount_eq_zero_of_not_mem {f : ℤ → ℤ} {N : ℕ} {h : ℤ} {s : ℕ} {Q : ℤ}
    (hQ : Q ∉ QSet f N h s) : BCount f N h s Q = 0 := by
  rw [BCount]
  by_contra hne
  obtain ⟨p, hp⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hne)
  rw [Finset.mem_filter] at hp
  obtain ⟨hpS, hpq⟩ := hp
  obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hpS
  apply hQ
  rw [QSet]
  refine Finset.mem_biUnion.mpr ⟨Qsum f h p.2, Finset.mem_image_of_mem _ hp2, ?_⟩
  refine Finset.mem_image.mpr ⟨Qsum f h p.1, Finset.mem_image_of_mem _ hp1, ?_⟩
  rw [← hpq]

set_option maxHeartbeats 2000000 in
/-- **`BCount` 被 `L¹` 范数控制**：`BCount f N h s Q ≤ ∫₀¹‖b_h‖^{2s} dα`。 -/
theorem BCount_le_integral (f : ℤ → ℤ) (N : ℕ) (h : ℤ) (s : ℕ) (Q : ℤ) :
    (BCount f N h s Q : ℝ) ≤ ∫ α in (0 : ℝ)..1, ‖T f N α h‖ ^ (2 * s) := by
  classical
  rcases Classical.em (Q ∈ QSet f N h s) with hQmem | hQnot
  · -- (a) `BCount Q` 是 Fourier 系数
    have hmain : (∫ α in (0 : ℝ)..1,
        ((Complex.normSq (T f N α h) : ℝ) : ℂ) ^ s * e (-((Q : ℝ) * α)))
        = (BCount f N h s Q : ℂ) := by
      have hpt : ∀ α : ℝ, ((Complex.normSq (T f N α h) : ℝ) : ℂ) ^ s * e (-((Q : ℝ) * α))
          = ∑ Q' ∈ QSet f N h s,
              (BCount f N h s Q' : ℂ) * e (((Q' - Q : ℤ) : ℝ) * α) := by
        intro α
        rw [normSq_pow_T_fiber f N h α s, Finset.sum_mul]
        refine Finset.sum_congr rfl (fun Q' _ => ?_)
        rw [mul_assoc, ← e_add]
        congr 1
        push_cast
        ring
      have hcont : ∀ Q' ∈ QSet f N h s, Continuous fun α : ℝ =>
          (BCount f N h s Q' : ℂ) * e (((Q' - Q : ℤ) : ℝ) * α) := by
        intro Q' _
        exact continuous_const.mul (continuous_e_mul _)
      simp_rw [hpt]
      rw [integral_finsetSum_cont _ _ hcont]
      have hterm : ∀ Q' ∈ QSet f N h s,
          (∫ α in (0 : ℝ)..1, (BCount f N h s Q' : ℂ) * e (((Q' - Q : ℤ) : ℝ) * α))
            = (BCount f N h s Q' : ℂ) * (if Q' = Q then 1 else 0) := by
        intro Q' _
        rw [intervalIntegral.integral_const_mul, integral_e_mul_int]
        by_cases hq : Q' - Q = 0
        · have hq' : Q' = Q := by omega
          rw [if_pos hq, if_pos hq', mul_one]
        · have hq' : Q' ≠ Q := by omega
          rw [if_neg hq, if_neg hq', mul_zero]
      rw [Finset.sum_congr rfl hterm]
      rw [show (∑ Q' ∈ QSet f N h s, (BCount f N h s Q' : ℂ) * (if Q' = Q then 1 else 0))
          = ∑ Q' ∈ QSet f N h s, (if Q' = Q then (BCount f N h s Q' : ℂ) else 0) from by
        refine Finset.sum_congr rfl (fun Q' _ => ?_)
        by_cases hq : Q' = Q <;> simp [hq]]
      rw [Finset.sum_ite_eq']
      simp [hQmem]
    -- (b) 取模
    have hnorm : ‖(BCount f N h s Q : ℂ)‖ ≤ ∫ α in (0 : ℝ)..1,
        ‖((Complex.normSq (T f N α h) : ℝ) : ℂ) ^ s * e (-((Q : ℝ) * α))‖ := by
      rw [← hmain]
      exact intervalIntegral.norm_integral_le_integral_norm (μ := MeasureTheory.volume) (by norm_num)
    rw [Complex.norm_natCast] at hnorm
    refine le_trans hnorm ?_
    apply le_of_eq
    apply intervalIntegral.integral_congr
    intro α _
    show ‖((Complex.normSq (T f N α h) : ℝ) : ℂ) ^ s * e (-((Q : ℝ) * α))‖
      = ‖T f N α h‖ ^ (2 * s)
    rw [norm_mul, norm_pow, norm_e, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Complex.normSq_nonneg _), Complex.normSq_eq_norm_sq, ← pow_mul]
  · -- 不在 `QSet` 中：计数为零
    rw [BCount_eq_zero_of_not_mem hQnot]
    simp only [Nat.cast_zero]
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro α _
    positivity

end Waring
