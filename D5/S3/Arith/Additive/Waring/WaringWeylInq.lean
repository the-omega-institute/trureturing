/- GID: D5/S3/Arith/Additive/Waring/WaringWeylInq
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Third-party formalization of the qualitative Hilbert–Waring theorem. -/

/- Source: https://github.com/yunyougu50-create/waring-lean4/blob/cd0735c253f3b640262fcc74a61306cb41e23765/WaringWeylInq.lean#L1-L363
   Modified for this repository. Local imports use their D5 module paths.
   Full Apache-2.0 license: D5/S3/Arith/Additive/Waring/WaringStatement.lean. -/

/-
Copyright (c) 2026 The Waring formalization authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Waring formalization authors
-/
import D5.S3.Arith.Additive.Waring.WaringExpSum

/-!
# Weyl 差分不等式（分组部分）

Weyl 归纳的核心不等式是

```text
|Σ_{n≤N} e(α f(n))|² ≤ (N+1) + 2 Σ_{1≤h≤N} |Σ_{n≤N-h} e(α (f(n+h) − f(n)))|.
```

来源：`‖S‖² = Σ_{n,m} e(α(f(m)−f(n)))`，按差 `h = m−n` 分组。

本文件给出这一步的**有限和重排**（纯组合）：

* `sum_range_shift`: `Σ_{m=0}^{N} F(m−n) = Σ_{h=−n}^{N−n} F h`（区间平移）；
* `sum_diff_group`: 双和按差分组。
-/

open Finset

namespace Waring

variable {M : Type*} [AddCommMonoid M]

/-- **区间平移**：`Σ_{m=0}^{N} F (m − n) = Σ_{h=−n}^{N−n} F h`。 -/
theorem sum_range_shift (F : ℤ → M) (n N : ℕ) :
    (∑ m ∈ Finset.range (N + 1), F ((m : ℤ) - (n : ℤ)))
      = ∑ h ∈ Finset.Icc (-(n : ℤ)) ((N : ℤ) - (n : ℤ)), F h := by
  refine Finset.sum_bij (fun m _ => (m : ℤ) - (n : ℤ)) ?_ ?_ ?_ ?_
  · -- 像落在 `Icc (−n) (N−n)` 中
    intro m hm
    rw [Finset.mem_range] at hm
    rw [Finset.mem_Icc]
    have hm' : (m : ℤ) ≤ (N : ℤ) := by exact_mod_cast Nat.lt_succ_iff.mp hm
    constructor <;> omega
  · -- 单射
    intro m _ m' _ heq
    have : (m : ℤ) = (m' : ℤ) := by linarith
    exact_mod_cast this
  · -- 满射
    intro h hh
    rw [Finset.mem_Icc] at hh
    refine ⟨((h + (n : ℤ)).toNat), ?_, ?_⟩
    · rw [Finset.mem_range]
      have h0 : (0 : ℤ) ≤ h + (n : ℤ) := by linarith [hh.1]
      have h1 : h + (n : ℤ) ≤ (N : ℤ) := by linarith [hh.2]
      have h2 : ((h + (n : ℤ)).toNat : ℤ) ≤ (N : ℤ) := by rwa [Int.toNat_of_nonneg h0]
      exact Nat.lt_succ_iff.mpr (by exact_mod_cast h2)
    · have h0 : (0 : ℤ) ≤ h + (n : ℤ) := by linarith [hh.1]
      have : ((h + (n : ℤ)).toNat : ℤ) = h + (n : ℤ) := Int.toNat_of_nonneg h0
      show ((h + (n : ℤ)).toNat : ℤ) - (n : ℤ) = h
      rw [this]
      ring
  · -- 求和项一致
    intro m _
    rfl

/-- **双和按差分组**：把 `Σ_{n,m} F (m−n) n` 重排成按 `h = m−n` 分组。 -/
theorem sum_diff_group (F : ℤ → ℕ → M) (N : ℕ) :
    (∑ n ∈ Finset.range (N + 1), ∑ m ∈ Finset.range (N + 1), F ((m : ℤ) - (n : ℤ)) n)
      = ∑ h ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
          ∑ n ∈ (Finset.range (N + 1)).filter
            (fun (n : ℕ) => h ∈ Finset.Icc (-(n : ℤ)) ((N : ℤ) - (n : ℤ))), F h n := by
  -- 第一步：对每个 n 做区间平移
  have hstep1 : (∑ n ∈ Finset.range (N + 1), ∑ m ∈ Finset.range (N + 1), F ((m : ℤ) - (n : ℤ)) n)
      = ∑ n ∈ Finset.range (N + 1),
          ∑ h ∈ Finset.Icc (-(n : ℤ)) ((N : ℤ) - (n : ℤ)), F h n := by
    refine Finset.sum_congr rfl (fun n _ => ?_)
    exact sum_range_shift (fun h => F h n) n N
  rw [hstep1]
  -- 第二步：`(n,h)` 与 `(h,n)` 的双射
  rw [Finset.sum_sigma' (s := Finset.range (N + 1))
    (t := fun (n : ℕ) => Finset.Icc (-(n : ℤ)) ((N : ℤ) - (n : ℤ)))
    (f := fun (n : ℕ) (h : ℤ) => F h n)]
  rw [Finset.sum_sigma' (s := Finset.Icc (-(N : ℤ)) (N : ℤ))
    (t := fun (h : ℤ) => (Finset.range (N + 1)).filter
      (fun (n : ℕ) => h ∈ Finset.Icc (-(n : ℤ)) ((N : ℤ) - (n : ℤ))))
    (f := fun (h : ℤ) (n : ℕ) => F h n)]
  refine Finset.sum_bij (fun p _ => ⟨p.2, p.1⟩) ?_ ?_ ?_ ?_
  · -- 像在右侧 sigma 中
    intro p hp
    obtain ⟨n, h⟩ := p
    rw [Finset.mem_sigma] at hp
    obtain ⟨hn, hh⟩ := hp
    simp only [Sigma.fst, Sigma.snd] at hn hh
    rw [Finset.mem_range] at hn
    rw [Finset.mem_Icc] at hh
    refine Finset.mem_sigma.mpr ⟨?_, ?_⟩
    · show h ∈ Finset.Icc (-(N : ℤ)) (N : ℤ)
      rw [Finset.mem_Icc]
      omega
    · show n ∈ (Finset.range (N + 1)).filter
          (fun (n : ℕ) => h ∈ Finset.Icc (-(n : ℤ)) ((N : ℤ) - (n : ℤ)))
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_range.mpr (by omega), Finset.mem_Icc.mpr ⟨hh.1, hh.2⟩⟩
  · -- 单射
    intro p _ q _ heq
    have hp : (⟨p.2, p.1⟩ : Sigma fun h : ℤ => ℕ) = ⟨q.2, q.1⟩ := heq
    have h1 : p.2 = q.2 := by
      simpa only [Sigma.fst] using congrArg Sigma.fst hp
    have h2 : p.1 = q.1 := by
      simpa only [Sigma.snd] using congrArg Sigma.snd hp
    obtain ⟨n1, x1⟩ := p
    obtain ⟨n2, x2⟩ := q
    simp only at h1 h2
    rw [h2, h1]
  · -- 满射
    intro q hq
    obtain ⟨h, n⟩ := q
    rw [Finset.mem_sigma] at hq
    obtain ⟨hh, hn⟩ := hq
    rw [Finset.mem_filter] at hn
    exact ⟨⟨n, h⟩, Finset.mem_sigma.mpr ⟨hn.1, hn.2⟩, rfl⟩
  · -- 求和项一致
    intro p _
    obtain ⟨n, h⟩ := p
    rfl

/-- `e(0) = 1`。 -/
theorem e_zero : e 0 = 1 := by
  unfold e
  simp

/-- **差分和** `b_h = Σ_{n : 0≤n+h≤N} e(α(f(n+h) − f(n)))`（Jameson 的 `b_h`）。 -/
noncomputable def T (f : ℤ → ℤ) (N : ℕ) (α : ℝ) (h : ℤ) : ℂ :=
  ∑ n ∈ (Finset.range (N + 1)).filter
      (fun (n : ℕ) => h ∈ Finset.Icc (-(n : ℤ)) ((N : ℤ) - (n : ℤ))),
    e (((f ((n : ℤ) + h) - f (n : ℤ) : ℤ) : ℝ) * α)

/-- `h = 0` 时差分和就是 `N + 1`（每项 `e(0) = 1`）。 -/
theorem T_zero (f : ℤ → ℤ) (N : ℕ) (α : ℝ) : T f N α 0 = ((N + 1 : ℕ) : ℂ) := by
  have hfilter : (Finset.range (N + 1)).filter
      (fun (n : ℕ) => (0 : ℤ) ∈ Finset.Icc (-(n : ℤ)) ((N : ℤ) - (n : ℤ)))
      = Finset.range (N + 1) := by
    apply Finset.filter_true_of_mem
    intro n hn
    rw [Finset.mem_range] at hn
    rw [Finset.mem_Icc]
    constructor <;> push_cast <;> omega
  have hone : ∀ n ∈ Finset.range (N + 1),
      e (((f ((n : ℤ) + 0) - f (n : ℤ) : ℤ) : ℝ) * α) = 1 := by
    intro n _
    have hz : ((f ((n : ℤ) + 0) - f (n : ℤ) : ℤ) : ℝ) = 0 := by
      simp
    rw [hz, zero_mul, e_zero]
  show (∑ n ∈ (Finset.range (N + 1)).filter
      (fun (n : ℕ) => (0 : ℤ) ∈ Finset.Icc (-(n : ℤ)) ((N : ℤ) - (n : ℤ))),
        e (((f ((n : ℤ) + 0) - f (n : ℤ) : ℤ) : ℝ) * α)) = ((N + 1 : ℕ) : ℂ)
  rw [hfilter, Finset.sum_congr rfl hone, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, mul_one]

/-- `‖b_0‖ = N + 1`。 -/
theorem norm_T_zero (f : ℤ → ℤ) (N : ℕ) (α : ℝ) : ‖T f N α 0‖ = (N + 1 : ℝ) := by
  rw [T_zero, Complex.norm_natCast]
  push_cast
  ring

/-- **Weyl 差分不等式**（分组形式）：
`‖Σ_n e(α f(n))‖² ≤ Σ_{|h|≤N} ‖Σ_{n: 0≤n+h≤N} e(α(f(n+h) − f(n)))‖`。 -/
theorem normSq_expSum_le (f : ℤ → ℤ) (N : ℕ) (α : ℝ) :
    ‖expSum f N α‖ ^ 2
      ≤ ∑ h ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
          ‖∑ n ∈ (Finset.range (N + 1)).filter
              (fun (n : ℕ) => h ∈ Finset.Icc (-(n : ℤ)) ((N : ℤ) - (n : ℤ))),
              e (((f ((n : ℤ) + h) - f (n : ℤ) : ℤ) : ℝ) * α)‖ := by
  -- 记号：差分项
  set G : ℤ → ℕ → ℂ := fun h n => e (((f ((n : ℤ) + h) - f (n : ℤ) : ℤ) : ℝ) * α) with hG
  -- 1) `‖S‖²` 展开成双和
  have hsq : ((‖expSum f N α‖ ^ 2 : ℝ) : ℂ)
      = ∑ n ∈ Finset.range (N + 1), ∑ m ∈ Finset.range (N + 1),
          e (((f (m : ℤ) - f (n : ℤ) : ℤ) : ℝ) * α) := by
    rw [← Complex.normSq_eq_norm_sq]
    exact normSq_expSum f N α
  -- 2) 每个求和项写成 `G (m−n) n`
  have hF : ∀ n m : ℕ, e (((f (m : ℤ) - f (n : ℤ) : ℤ) : ℝ) * α) = G ((m : ℤ) - (n : ℤ)) n := by
    intro n m
    rw [hG]
    congr 1
    push_cast
    ring
  -- 3) 双和按差分组
  have hgroup : (∑ n ∈ Finset.range (N + 1), ∑ m ∈ Finset.range (N + 1),
        G ((m : ℤ) - (n : ℤ)) n)
      = ∑ h ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
          ∑ n ∈ (Finset.range (N + 1)).filter
            (fun (n : ℕ) => h ∈ Finset.Icc (-(n : ℤ)) ((N : ℤ) - (n : ℤ))), G h n :=
    sum_diff_group G N
  -- 4) 合并成复数等式
  have hEq : ((‖expSum f N α‖ ^ 2 : ℝ) : ℂ)
      = ∑ h ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
          ∑ n ∈ (Finset.range (N + 1)).filter
            (fun (n : ℕ) => h ∈ Finset.Icc (-(n : ℤ)) ((N : ℤ) - (n : ℤ))), G h n := by
    rw [hsq]
    rw [Finset.sum_congr rfl (fun n _ => Finset.sum_congr rfl (fun m _ => hF n m))]
    exact hgroup
  -- 5) 取模并用三角不等式
  calc ‖expSum f N α‖ ^ 2
      = ‖((‖expSum f N α‖ ^ 2 : ℝ) : ℂ)‖ := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    _ = ‖∑ h ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
          ∑ n ∈ (Finset.range (N + 1)).filter
            (fun (n : ℕ) => h ∈ Finset.Icc (-(n : ℤ)) ((N : ℤ) - (n : ℤ))), G h n‖ := by
          rw [hEq]
    _ ≤ ∑ h ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
          ‖∑ n ∈ (Finset.range (N + 1)).filter
            (fun (n : ℕ) => h ∈ Finset.Icc (-(n : ℤ)) ((N : ℤ) - (n : ℤ))), G h n‖ :=
          norm_sum_le _ _

/-- `e(k) = 1` 对整数 `k`。 -/
theorem e_int (k : ℤ) : e ((k : ℝ)) = 1 := by
  unfold e
  have h : 2 * (Real.pi : ℂ) * Complex.I * ((k : ℝ) : ℂ)
      = (k : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast
    ring
  rw [h, Complex.exp_int_mul_two_pi_mul_I]

/-- **`b_h` 的周期性**：若 `h ∣ f(n+h) − f(n)` 对每个 `n` 成立（整系数多项式
总是如此），则 `b_h(α + 1/h) = b_h(α)`。 -/
theorem T_period (f : ℤ → ℤ) (N : ℕ) (h : ℤ) (hh : h ≠ 0)
    (hdiv : ∀ n : ℤ, h ∣ f (n + h) - f n) (α : ℝ) :
    T f N (α + 1 / (h : ℝ)) h = T f N α h := by
  have hterm : ∀ n : ℕ,
      e (((f ((n : ℤ) + h) - f (n : ℤ) : ℤ) : ℝ) * (α + 1 / (h : ℝ)))
        = e (((f ((n : ℤ) + h) - f (n : ℤ) : ℤ) : ℝ) * α) := by
    intro n
    obtain ⟨k, hk⟩ := hdiv (n : ℤ)
    have hrw : ((f ((n : ℤ) + h) - f (n : ℤ) : ℤ) : ℝ) * (α + 1 / (h : ℝ))
        = ((f ((n : ℤ) + h) - f (n : ℤ) : ℤ) : ℝ) * α + (k : ℝ) := by
      rw [hk]
      push_cast
      have hh' : (h : ℝ) ≠ 0 := by exact_mod_cast hh
      field_simp
    rw [hrw, e_add, e_int, mul_one]
  unfold T
  exact Finset.sum_congr rfl (fun n _ => hterm n)

/-- 多项式的差分被步长整除：`h ∣ f(n+h) − f(n)`。 -/
theorem polyEval_dvd (a : ℕ → ℤ) (d : ℕ) (h : ℤ) (n : ℤ) :
    h ∣ polyEval a d (n + h) - polyEval a d n := by
  have hd := congrFun (diffH_polyEval a d h) n
  unfold diffH at hd
  exact ⟨polyEval (diffCoeff a d h) d n, hd⟩

/-- **多项式情形的周期性**：`b_h(α + 1/h) = b_h(α)`。 -/
theorem T_period_polyEval (a : ℕ → ℤ) (d : ℕ) (N : ℕ) (h : ℤ) (hh : h ≠ 0) (α : ℝ) :
    T (polyEval a d) N (α + 1 / (h : ℝ)) h = T (polyEval a d) N α h :=
  T_period _ _ h hh (fun n => polyEval_dvd a d h n) α

/-- **`‖b_h‖²` 的双和展开**：
`↑(normSq (b_h)) = Σ_{n,m ∈ S_h} e(α((f(m+h)−f(m)) − (f(n+h)−f(n))))`。 -/
theorem normSq_T (f : ℤ → ℤ) (N : ℕ) (h : ℤ) (α : ℝ) :
    ((Complex.normSq (T f N α h) : ℝ) : ℂ)
      = ∑ n ∈ (Finset.range (N + 1)).filter
            (fun (n : ℕ) => h ∈ Finset.Icc (-(n : ℤ)) ((N : ℤ) - (n : ℤ))),
          ∑ m ∈ (Finset.range (N + 1)).filter
            (fun (n : ℕ) => h ∈ Finset.Icc (-(n : ℤ)) ((N : ℤ) - (n : ℤ))),
            e ((((f ((m : ℤ) + h) - f (m : ℤ))
                  - (f ((n : ℤ) + h) - f (n : ℤ)) : ℤ) : ℝ) * α) := by
  have hconj : (starRingEnd ℂ) (T f N α h)
      = ∑ n ∈ (Finset.range (N + 1)).filter
            (fun (n : ℕ) => h ∈ Finset.Icc (-(n : ℤ)) ((N : ℤ) - (n : ℤ))),
          e (-(((f ((n : ℤ) + h) - f (n : ℤ) : ℤ) : ℝ) * α)) := by
    unfold T
    rw [map_sum]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [← e_neg]
  rw [Complex.normSq_eq_conj_mul_self, hconj]
  unfold T
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl (fun n _ => Finset.sum_congr rfl (fun m _ => ?_))
  rw [← e_add]
  congr 1
  push_cast
  ring
/-- **按 ℤ 值函数的值差分组**（一般形式）：
`Σ_{n,m∈s} F (q m − q n) = Σ_Q (#{(n,m) : q m − q n = Q}) • F Q`。 -/
theorem sum_diff_fiber {M : Type*} [AddCommMonoid M] (s : Finset ℕ) (q : ℕ → ℤ) (F : ℤ → M) :
    (∑ n ∈ s, ∑ m ∈ s, F (q m - q n))
      = ∑ Q ∈ (s.image q).biUnion (fun a => (s.image q).image (fun b => b - a)),
          ((s.product s).filter (fun p : ℕ × ℕ => q p.2 - q p.1 = Q)).card • F Q := by
  rw [show (∑ n ∈ s, ∑ m ∈ s, F (q m - q n))
      = ∑ p ∈ s.product s, F (q p.2 - q p.1) from
    (Finset.sum_product s s (fun p : ℕ × ℕ => F (q p.2 - q p.1))).symm]
  have hmaps : ∀ p ∈ s.product s,
      q p.2 - q p.1 ∈ (s.image q).biUnion (fun a => (s.image q).image (fun b => b - a)) := by
    intro p hp
    obtain ⟨n, m⟩ := p
    obtain ⟨hn, hm⟩ := Finset.mem_product.mp hp
    refine Finset.mem_biUnion.mpr ⟨q n, Finset.mem_image_of_mem q hn, ?_⟩
    exact Finset.mem_image_of_mem _ (Finset.mem_image_of_mem q hm)
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun p : ℕ × ℕ => q p.2 - q p.1) hmaps
    (f := fun p => F (q p.2 - q p.1))]
  refine Finset.sum_congr rfl (fun Q _ => ?_)
  have hstep : ∀ p ∈ (s.product s).filter (fun p : ℕ × ℕ => q p.2 - q p.1 = Q),
      F (q p.2 - q p.1) = F Q := by
    intro p hp
    rw [Finset.mem_filter] at hp
    rw [hp.2]
  rw [Finset.sum_congr rfl hstep, Finset.sum_const]

/-- 差分和的指标集 `{n : 0 ≤ n ≤ N, 0 ≤ n+h ≤ N}`。 -/
noncomputable def TS (N : ℕ) (h : ℤ) : Finset ℕ :=
  (Finset.range (N + 1)).filter (fun n => h ∈ Finset.Icc (-(n : ℤ)) ((N : ℤ) - (n : ℤ)))

/-- **`‖b_h‖²` 按频率分组**：`‖b_h‖² = Σ_Q A(Q,h) e(αQ)`，`A(Q,h)` 是解数，
其中 `q n = f(n+h) − f(n)`（`= h·φ(n,h)`）。 -/
theorem normSq_T_fiber (f : ℤ → ℤ) (N : ℕ) (h : ℤ) (α : ℝ) :
    ((Complex.normSq (T f N α h) : ℝ) : ℂ)
      = ∑ Q ∈ ((TS N h).image (fun n : ℕ => f ((n : ℤ) + h) - f (n : ℤ))).biUnion
          (fun a => ((TS N h).image (fun n : ℕ => f ((n : ℤ) + h) - f (n : ℤ))).image
            (fun b => b - a)),
          (((TS N h).product (TS N h)).filter
            (fun p : ℕ × ℕ => (f ((p.2 : ℤ) + h) - f (p.2 : ℤ))
              - (f ((p.1 : ℤ) + h) - f (p.1 : ℤ)) = Q)).card
          • e ((Q : ℝ) * α) := by
  have h1 : ((Complex.normSq (T f N α h) : ℝ) : ℂ)
      = ∑ n ∈ TS N h, ∑ m ∈ TS N h,
          e ((((f ((m : ℤ) + h) - f (m : ℤ))
              - (f ((n : ℤ) + h) - f (n : ℤ)) : ℤ) : ℝ) * α) := by
    rw [normSq_T]
    rfl
  rw [h1]
  exact sum_diff_fiber (TS N h) (fun n => f ((n : ℤ) + h) - f (n : ℤ))
    (fun Q : ℤ => e ((Q : ℝ) * α))

/-- **`α = 0` 时 `b_h` 的值**：`b_h(0) = #TS`（每项 `e(0) = 1`）。 -/
theorem T_alpha_zero (f : ℤ → ℤ) (N : ℕ) (h : ℤ) :
    T f N 0 h = ((TS N h).card : ℂ) := by
  unfold T
  change (∑ n ∈ TS N h, e (((f ((n : ℤ) + h) - f (n : ℤ) : ℤ) : ℝ) * 0)) = ((TS N h).card : ℂ)
  have hone : ∀ n ∈ TS N h,
      e (((f ((n : ℤ) + h) - f (n : ℤ) : ℤ) : ℝ) * 0) = 1 := by
    intro n _
    rw [mul_zero, e_zero]
  rw [Finset.sum_congr rfl hone, Finset.sum_const, nsmul_eq_mul, mul_one]

/-- **Weyl 差分不等式**（把 `h = 0` 项分离出来，Jameson 的 (1) 的绝对值版本）：
`‖Σ_n e(α f(n))‖² ≤ (N+1) + Σ_{h≠0} ‖b_h‖`。 -/
theorem normSq_expSum_le_zero (f : ℤ → ℤ) (N : ℕ) (α : ℝ) :
    ‖expSum f N α‖ ^ 2
      ≤ (N + 1 : ℝ)
        + ∑ h ∈ (Finset.Icc (-(N : ℤ)) (N : ℤ)).erase 0, ‖T f N α h‖ := by
  have h := normSq_expSum_le f N α
  have h0mem : (0 : ℤ) ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) := by
    rw [Finset.mem_Icc]
    constructor <;> simp
  have hsplit : (∑ h ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), ‖T f N α h‖)
      = ‖T f N α 0‖ + ∑ h ∈ (Finset.Icc (-(N : ℤ)) (N : ℤ)).erase 0, ‖T f N α h‖ := by
    conv_lhs => rw [← Finset.insert_erase h0mem]
    rw [Finset.sum_insert (by simp)]
  have h' : ‖expSum f N α‖ ^ 2
      ≤ ∑ h ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), ‖T f N α h‖ := h
  rw [hsplit, norm_T_zero] at h'
  exact h'

end Waring
