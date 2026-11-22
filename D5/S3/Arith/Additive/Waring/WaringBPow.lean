/- GID: D5/S3/Arith/Additive/Waring/WaringBPow
   generality: G
   mirror-B: D5/B/S3/Arith/Additive/Waring/WaringBPow
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Third-party formalization of the qualitative Hilbert–Waring theorem. -/

/- Source: https://github.com/yunyougu50-create/waring-lean4/blob/cd0735c253f3b640262fcc74a61306cb41e23765/WaringBPow.lean#L1-L184
   Modified for this repository. Local imports use their D5 module paths.
   Selected declaration closure and supporting source.
   Full Apache-2.0 license: D5/S3/Arith/Additive/Waring/WaringDensity.lean. -/

/-
Copyright (c) 2026 The Waring formalization authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Waring formalization authors
-/
import D5.S3.Arith.Additive.Waring.WaringWeylInq

/-!
# `|b_h|^{2s}` 的按频率展开（一般 `s`）

`WaringWeylInq.normSq_T_fiber` 给出了 `s = 1` 的情形：

```text
|b_h|² = Σ_Q A(Q,h) · e(Q·α),   A(Q,h) = #{(n,m) ∈ TS²  |  q m − q n = Q}
```

本文件把它推广到任意 `s ≥ 1`（`s = 0` 时结论也成立，`1 ≤ s` 只是与 Weyl
归纳的用法对齐）：

```text
|b_h|^{2s} = Σ_Q BCount(f,N,h,s,Q) · e(Q·α),
```

其中 `BCount` 是 `s` 元组的解数
`#{(u,v) : (Fin s → TS)²  |  Σ_i q(u i) − Σ_i q(v i) = Q}`，`q n = f(n+h) − f(n)`。

证明分三步：

* `T_pow_expand`：`b^s = Σ_{u : Fin s → TS} e(α · Qsum u)`（`Finset.sum_pow'` + 乘性 `e_sum_finset`）；
* `conjT_pow_expand`：`(conj b)^s = Σ_v e(−α · Qsum v)`；
* `sum_diff_fiber_pi`：把 `(Fin s → ℕ)` 上的双和按 `Qsum u − Qsum v` 的值分组
  （`Finset.sum_product` + `Finset.sum_fiberwise_of_maps_to`，与 `sum_diff_fiber` 同构）。

最后 `↑(normSq b) = conj b · b`，配合 `mul_pow` 组装。

**命名注意**：本文件的 `e_sum_finset` 是 `Finset` 版本；`WaringQuadratic.e_sum` 是
`Fintype` 版本，两者曾同名冲突，故此处改名为 `e_sum_finset`。
-/

open Finset

namespace Waring

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
  rw [← Finset.sum_fiberwise_of_maps_to
    (t := ((Fintype.piFinset (fun _ : ι => s)).image q).biUnion
      (fun a => ((Fintype.piFinset (fun _ : ι => s)).image q).image (fun b => b - a)))
    (g := fun p : (ι → ℕ) × (ι → ℕ) => q p.1 - q p.2)
    hmaps (f := fun p => F (q p.1 - q p.2))]
  refine Finset.sum_congr rfl (fun Q _ => ?_)
  have hstep : ∀ p ∈ ((Fintype.piFinset (fun _ : ι => s)).product
      (Fintype.piFinset (fun _ : ι => s))).filter
      (fun p : (ι → ℕ) × (ι → ℕ) => q p.1 - q p.2 = Q),
      F (q p.1 - q p.2) = F Q := by
    intro p hp
    rw [Finset.mem_filter] at hp
    rw [hp.2]
  rw [Finset.sum_congr rfl hstep, Finset.sum_const]

/-- **`|b_h|^{2s}` 的按频率展开**（一般 `s`）：
`|b_h|^{2s} = Σ_Q BCount(Q) · e(Q·α)`。 -/
theorem normSq_pow_T_fiber (f : ℤ → ℤ) (N : ℕ) (h : ℤ) (α : ℝ) (s : ℕ) (_hs : 1 ≤ s) :
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

end Waring
