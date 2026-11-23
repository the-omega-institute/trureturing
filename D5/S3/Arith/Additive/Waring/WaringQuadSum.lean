/- GID: D5/S3/Arith/Additive/Waring/WaringQuadSum
   generality: G
   mirror-B: D5/B/S3/Arith/Additive/Waring/WaringQuadSum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Third-party formalization of the qualitative Hilbert–Waring theorem. -/

/- Source: https://github.com/yunyougu50-create/waring-lean4/blob/cd0735c253f3b640262fcc74a61306cb41e23765/WaringQuadSum.lean#L1-L239
   Modified for this repository. Local imports use their D5 module paths.
   Selected declaration closure and supporting source.
   Full Apache-2.0 license: D5/S3/Arith/Additive/Waring/WaringDensity.lean. -/

/-
Copyright (c) 2026 The Waring formalization authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Waring formalization authors
-/
import D5.S3.Arith.Additive.Waring.WaringBPow

/-!
# 归纳步第 8 步：四重和 + 正交性

本文件把 `‖b_h‖^{2s}` 的按频率展开（`WaringBPow.normSq_pow_T_fiber`）提升到**四重和**：

```text
∫₀¹ (Σ_h ‖b_h‖^{2s})⁴ dα
  = Σ_{h₁..h₄ ∈ S} Σ_{Q₁ ∈ QSet h₁} ⋯ Σ_{Q₄ ∈ QSet h₄}
      [Q₁+Q₂+Q₃+Q₄ = 0] · BCount h₁ Q₁ ⋯ BCount h₄ Q₄
```

**相位约定**：`T f N α h = Σ_n e(α·(f(n+h) − f(n)))`，频率 `Q` 直接就是
`Σ_i (f(nᵢ+h) − f(nᵢ)) − Σ_i (f(mᵢ+h) − f(mᵢ))`，**不含 `h` 因子**。
因此正交性条件是 `Q₁+Q₂+Q₃+Q₄ = 0`（而不是 Jameson 的 `Σ hᵢ mᵢ = 0`）。

要把 Lemma 7（`hmCount7_le'`，条件 `Σ hᵢmᵢ = 0`）接上，需要把 `f` 特化为
多项式 `polyEval a d`，此时 `diffH_polyEval` 给出 `f(n+h) − f(n) = h · φ(n)`，
从而 `Q = h·M`、条件变成 `h₁M₁ + h₂M₂ + h₃M₃ + h₄M₄ = 0`。
桥接引理见 `dshift_polyEval` / `Qsum_polyEval`。
-/

open Finset

namespace Waring

/-- **桥接**：多项式情形 `dshift` 分解出显式 `h` 因子（`WaringWeylDiff.diffH_polyEval`）。 -/
theorem dshift_polyEval (a : ℕ → ℤ) (d : ℕ) (h : ℤ) (n : ℕ) :
    dshift (polyEval a d) h n = h * polyEval (diffCoeff a d h) d (n : ℤ) := by
  have hh := congrFun (diffH_polyEval a d h) (n : ℤ)
  unfold diffH at hh
  simpa [dshift] using hh

/-- **桥接**：多项式情形 `Qsum` 整体提出 `h` 因子。 -/
theorem Qsum_polyEval (a : ℕ → ℤ) (d : ℕ) (h : ℤ) {s : ℕ} (u : Fin s → ℕ) :
    Qsum (polyEval a d) h u = h * ∑ i : Fin s, polyEval (diffCoeff a d h) d (u i : ℤ) := by
  unfold Qsum
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => dshift_polyEval a d h (u i))

/-- `α ↦ e(c·α)` 连续。 -/
theorem continuous_e_mul (c : ℝ) : Continuous fun α : ℝ => e (c * α) := by
  unfold e
  fun_prop

/-- **四重展开**：四个和之积展开成四层嵌套和（右结合形状）。 -/
theorem mul_four_finset (s1 s2 s3 s4 : Finset ℤ) (f1 f2 f3 f4 : ℤ → ℂ) :
    (∑ x ∈ s1, f1 x) * ((∑ x ∈ s2, f2 x) * ((∑ x ∈ s3, f3 x) * (∑ x ∈ s4, f4 x)))
      = ∑ x1 ∈ s1, ∑ x2 ∈ s2, ∑ x3 ∈ s3, ∑ x4 ∈ s4,
          f1 x1 * (f2 x2 * (f3 x3 * f4 x4)) := by
  have h34 : (∑ x ∈ s3, f3 x) * (∑ x ∈ s4, f4 x)
      = ∑ x3 ∈ s3, ∑ x4 ∈ s4, f3 x3 * f4 x4 := Finset.sum_mul_sum s3 s4 f3 f4
  rw [h34]
  have h234 : (∑ x ∈ s2, f2 x) * (∑ x3 ∈ s3, ∑ x4 ∈ s4, f3 x3 * f4 x4)
      = ∑ x2 ∈ s2, ∑ x3 ∈ s3, ∑ x4 ∈ s4, f2 x2 * (f3 x3 * f4 x4) := by
    rw [Finset.sum_mul_sum s2 s3 f2 (fun x3 => ∑ x4 ∈ s4, f3 x3 * f4 x4)]
    refine Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => ?_))
    rw [Finset.mul_sum]
  rw [h234]
  have h1234 : (∑ x ∈ s1, f1 x) *
      (∑ x2 ∈ s2, ∑ x3 ∈ s3, ∑ x4 ∈ s4, f2 x2 * (f3 x3 * f4 x4))
      = ∑ x1 ∈ s1, ∑ x2 ∈ s2, ∑ x3 ∈ s3, ∑ x4 ∈ s4,
          f1 x1 * (f2 x2 * (f3 x3 * f4 x4)) := by
    rw [Finset.sum_mul_sum s1 s2 f1
      (fun x2 => ∑ x3 ∈ s3, ∑ x4 ∈ s4, f2 x2 * (f3 x3 * f4 x4))]
    refine Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => ?_))
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun x3 _ => ?_)
    rw [Finset.mul_sum]
  rw [h1234]

/-- 四重展开后的一项（`BCount` 系数乘指数特征）。 -/
noncomputable def TN (f : ℤ → ℤ) (N s : ℕ) (h1 h2 h3 h4 Q1 Q2 Q3 Q4 : ℤ) (α : ℝ) : ℂ :=
  ((BCount f N h1 s Q1 : ℂ) * e ((Q1 : ℝ) * α)) *
    (((BCount f N h2 s Q2 : ℂ) * e ((Q2 : ℝ) * α)) *
     (((BCount f N h3 s Q3 : ℂ) * e ((Q3 : ℝ) * α)) *
      ((BCount f N h4 s Q4 : ℂ) * e ((Q4 : ℝ) * α))))

/-- **单项打包**：`Π BCount · e(α·(Q₁+Q₂+Q₃+Q₄))`。 -/
theorem TN_pack (f : ℤ → ℤ) (N s : ℕ) (h1 h2 h3 h4 Q1 Q2 Q3 Q4 : ℤ) (α : ℝ) :
    TN f N s h1 h2 h3 h4 Q1 Q2 Q3 Q4 α
      = ((BCount f N h1 s Q1 * BCount f N h2 s Q2 * BCount f N h3 s Q3
            * BCount f N h4 s Q4 : ℕ) : ℂ)
        * e (((Q1 + Q2 + Q3 + Q4 : ℤ) : ℝ) * α) := by
  unfold TN
  have hPQ : ((BCount f N h1 s Q1 : ℂ) * e ((Q1 : ℝ) * α)) *
      (((BCount f N h2 s Q2 : ℂ) * e ((Q2 : ℝ) * α)) *
       (((BCount f N h3 s Q3 : ℂ) * e ((Q3 : ℝ) * α)) *
        ((BCount f N h4 s Q4 : ℂ) * e ((Q4 : ℝ) * α))))
      = ((BCount f N h1 s Q1 : ℂ) *
          ((BCount f N h2 s Q2 : ℂ) *
           ((BCount f N h3 s Q3 : ℂ) * (BCount f N h4 s Q4 : ℂ)))) *
        (e ((Q1 : ℝ) * α) *
          (e ((Q2 : ℝ) * α) * (e ((Q3 : ℝ) * α) * e ((Q4 : ℝ) * α)))) := by
    ring
  have hB : (BCount f N h1 s Q1 : ℂ) *
      ((BCount f N h2 s Q2 : ℂ) *
       ((BCount f N h3 s Q3 : ℂ) * (BCount f N h4 s Q4 : ℂ)))
      = ((BCount f N h1 s Q1 * BCount f N h2 s Q2 * BCount f N h3 s Q3
            * BCount f N h4 s Q4 : ℕ) : ℂ) := by
    push_cast
    ring
  have hE : e ((Q1 : ℝ) * α) *
      (e ((Q2 : ℝ) * α) * (e ((Q3 : ℝ) * α) * e ((Q4 : ℝ) * α)))
      = e (((Q1 + Q2 + Q3 + Q4 : ℤ) : ℝ) * α) := by
    rw [← e_add ((Q3 : ℝ) * α) ((Q4 : ℝ) * α),
      ← e_add ((Q2 : ℝ) * α) (((Q3 : ℝ) * α) + ((Q4 : ℝ) * α)),
      ← e_add ((Q1 : ℝ) * α)
        (((Q2 : ℝ) * α) + (((Q3 : ℝ) * α) + ((Q4 : ℝ) * α)))]
    congr 1
    push_cast
    ring
  rw [hPQ, hB, hE]

/-- 单项连续。 -/
theorem continuous_TN (f : ℤ → ℤ) (N s : ℕ) (h1 h2 h3 h4 Q1 Q2 Q3 Q4 : ℤ) :
    Continuous fun α : ℝ => TN f N s h1 h2 h3 h4 Q1 Q2 Q3 Q4 α := by
  unfold TN
  exact (continuous_const.mul (continuous_e_mul _)).mul
    ((continuous_const.mul (continuous_e_mul _)).mul
     ((continuous_const.mul (continuous_e_mul _)).mul
      (continuous_const.mul (continuous_e_mul _))))

attribute [fun_prop] continuous_TN

/-- **点态四重展开**：`↑((Σ_h ‖b_h‖^{2s})^4)` 展开成八重嵌套和。 -/
theorem pointwise_expand (f : ℤ → ℤ) (N s : ℕ) (hs : 1 ≤ s) (S : Finset ℤ) (α : ℝ) :
    (((∑ h ∈ S, ‖T f N α h‖ ^ (2*s)) ^ 4 : ℝ) : ℂ)
      = ∑ h1 ∈ S, ∑ h2 ∈ S, ∑ h3 ∈ S, ∑ h4 ∈ S,
          ∑ Q1 ∈ QSet f N h1 s, ∑ Q2 ∈ QSet f N h2 s,
          ∑ Q3 ∈ QSet f N h3 s, ∑ Q4 ∈ QSet f N h4 s,
            TN f N s h1 h2 h3 h4 Q1 Q2 Q3 Q4 α := by
  rw [Complex.ofReal_pow, Complex.ofReal_sum]
  have hterm : ∀ h : ℤ, ((‖T f N α h‖ ^ (2*s) : ℝ) : ℂ)
      = ∑ Q ∈ QSet f N h s, (BCount f N h s Q : ℂ) * e ((Q : ℝ) * α) := by
    intro h
    have hp : ‖T f N α h‖ ^ (2*s) = (Complex.normSq (T f N α h)) ^ s := by
      rw [pow_mul, ← Complex.normSq_eq_norm_sq]
    rw [hp, Complex.ofReal_pow]
    exact normSq_pow_T_fiber f N h α s
  simp only [hterm]
  have hpow4 : ∀ x : ℂ, x ^ 4 = x * (x * (x * x)) := fun x => by ring
  rw [hpow4]
  rw [mul_four_finset S S S S
    (fun h => ∑ Q ∈ QSet f N h s, (BCount f N h s Q : ℂ) * e ((Q : ℝ) * α))
    (fun h => ∑ Q ∈ QSet f N h s, (BCount f N h s Q : ℂ) * e ((Q : ℝ) * α))
    (fun h => ∑ Q ∈ QSet f N h s, (BCount f N h s Q : ℂ) * e ((Q : ℝ) * α))
    (fun h => ∑ Q ∈ QSet f N h s, (BCount f N h s Q : ℂ) * e ((Q : ℝ) * α))]
  refine Finset.sum_congr rfl (fun h1 _ => Finset.sum_congr rfl (fun h2 _ =>
    Finset.sum_congr rfl (fun h3 _ => Finset.sum_congr rfl (fun h4 _ => ?_))))
  exact mul_four_finset (QSet f N h1 s) (QSet f N h2 s) (QSet f N h3 s) (QSet f N h4 s)
    (fun Q => (BCount f N h1 s Q : ℂ) * e ((Q : ℝ) * α))
    (fun Q => (BCount f N h2 s Q : ℂ) * e ((Q : ℝ) * α))
    (fun Q => (BCount f N h3 s Q : ℂ) * e ((Q : ℝ) * α))
    (fun Q => (BCount f N h4 s Q : ℂ) * e ((Q : ℝ) * α))

/-- 有限和与区间积分交换（连续版本）。 -/
theorem integral_finsetSum_cont {ι : Type*} [DecidableEq ι] (s : Finset ι) (g : ι → ℝ → ℂ)
    (h : ∀ i ∈ s, Continuous (g i)) :
    (∫ α in (0:ℝ)..1, ∑ i ∈ s, g i α) = ∑ i ∈ s, ∫ α in (0:ℝ)..1, g i α := by
  rw [intervalIntegral.integral_finsetSum]
  intro i hi
  exact (h i hi).intervalIntegrable 0 1

/-- **八重求和逐项积分**（正交性 `∫₀¹ e(mα) = [m=0]`）。 -/
theorem integral_compute (f : ℤ → ℤ) (N s : ℕ) (S : Finset ℤ) :
    (∫ α in (0:ℝ)..1, ∑ h1 ∈ S, ∑ h2 ∈ S, ∑ h3 ∈ S, ∑ h4 ∈ S,
        ∑ Q1 ∈ QSet f N h1 s, ∑ Q2 ∈ QSet f N h2 s,
        ∑ Q3 ∈ QSet f N h3 s, ∑ Q4 ∈ QSet f N h4 s,
          TN f N s h1 h2 h3 h4 Q1 Q2 Q3 Q4 α)
      = ∑ h1 ∈ S, ∑ h2 ∈ S, ∑ h3 ∈ S, ∑ h4 ∈ S,
          ∑ Q1 ∈ QSet f N h1 s, ∑ Q2 ∈ QSet f N h2 s,
          ∑ Q3 ∈ QSet f N h3 s, ∑ Q4 ∈ QSet f N h4 s,
            ((BCount f N h1 s Q1 * BCount f N h2 s Q2 * BCount f N h3 s Q3
              * BCount f N h4 s Q4 : ℕ) : ℂ)
              * (if Q1 + Q2 + Q3 + Q4 = 0 then 1 else 0) := by
  rw [integral_finsetSum_cont]
  refine Finset.sum_congr rfl (fun h1 _ => ?_)
  rw [integral_finsetSum_cont]
  refine Finset.sum_congr rfl (fun h2 _ => ?_)
  rw [integral_finsetSum_cont]
  refine Finset.sum_congr rfl (fun h3 _ => ?_)
  rw [integral_finsetSum_cont]
  refine Finset.sum_congr rfl (fun h4 _ => ?_)
  rw [integral_finsetSum_cont]
  refine Finset.sum_congr rfl (fun Q1 _ => ?_)
  rw [integral_finsetSum_cont]
  refine Finset.sum_congr rfl (fun Q2 _ => ?_)
  rw [integral_finsetSum_cont]
  refine Finset.sum_congr rfl (fun Q3 _ => ?_)
  rw [integral_finsetSum_cont]
  refine Finset.sum_congr rfl (fun Q4 _ => ?_)
  rw [intervalIntegral.integral_congr
    (fun α _ => TN_pack f N s h1 h2 h3 h4 Q1 Q2 Q3 Q4 α)]
  rw [intervalIntegral.integral_const_mul]
  rw [integral_e_mul_int]
  all_goals fun_prop

/-- **四重和**：`∫₀¹ (Σ_{h} ‖b_h‖^{2s})^4 dα` 展开成正交性计数。

相位约定：`T f N α h = Σ_n e(α(f(n+h)−f(n)))`，频率 `Q` 不含 `h` 因子，
故正交性条件是 `Q₁+Q₂+Q₃+Q₄ = 0`。 -/
theorem integral_sum_pow_four (f : ℤ → ℤ) (N : ℕ) (s : ℕ) (hs : 1 ≤ s) :
    (∫ α in (0:ℝ)..1,
      (∑ h ∈ (Finset.Icc (-(N:ℤ)) (N:ℤ)).erase 0, ‖T f N α h‖ ^ (2*s)) ^ 4)
      = ∑ h1 ∈ (Finset.Icc (-(N:ℤ)) (N:ℤ)).erase 0,
        ∑ h2 ∈ (Finset.Icc (-(N:ℤ)) (N:ℤ)).erase 0,
        ∑ h3 ∈ (Finset.Icc (-(N:ℤ)) (N:ℤ)).erase 0,
        ∑ h4 ∈ (Finset.Icc (-(N:ℤ)) (N:ℤ)).erase 0,
        ∑ Q1 ∈ QSet f N h1 s, ∑ Q2 ∈ QSet f N h2 s,
        ∑ Q3 ∈ QSet f N h3 s, ∑ Q4 ∈ QSet f N h4 s,
          (if Q1 + Q2 + Q3 + Q4 = 0 then
            (BCount f N h1 s Q1 * BCount f N h2 s Q2 * BCount f N h3 s Q3
              * BCount f N h4 s Q4 : ℝ)
          else 0) := by
  classical
  set S : Finset ℤ := (Finset.Icc (-(N:ℤ)) (N:ℤ)).erase 0 with hS
  apply Complex.ofReal_inj.mp
  rw [← intervalIntegral.integral_ofReal]
  simp_rw [pointwise_expand f N s hs S]
  rw [integral_compute f N s S]
  have hconv : ∀ (c : ℕ) (m : ℤ), ((c : ℂ) * (if m = 0 then 1 else 0))
      = (((if m = 0 then (c : ℝ) else 0) : ℝ) : ℂ) := by
    intro c m
    by_cases h : m = 0
    · simp [h]
    · simp [h]
  simp only [hconv]
  simp only [Complex.ofReal_sum]
  push_cast
  rfl

end Waring
