/- GID: D5/S3/Arith/Additive/Waring/WaringCoeffBound
   generality: G
   mirror-B: D5/B/S3/Arith/Additive/Waring/WaringCoeffBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Third-party formalization of the qualitative Hilbert–Waring theorem. -/

/- Source: https://github.com/yunyougu50-create/waring-lean4/blob/cd0735c253f3b640262fcc74a61306cb41e23765/WaringCoeffBound.lean#L1-L87
   Modified for this repository. Local imports use their D5 module paths.
   Selected declaration closure and supporting source.
   Full Apache-2.0 license: D5/S3/Arith/Additive/Waring/WaringDensity.lean. -/

import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Algebra.Polynomial.Basic

/-!
# 差分多项式的系数界（Jameson Theorem 1 归纳步）

Jameson 的原话：

> `φ(n,h) = (1/h)(f(n+h) − f(n)) = Σ_{r=0}^{k−1} b_r n^r`，
> `b_r = Σ_{j=r+1}^{k} C(j,r) a_j h^{j−r−1}`，
> 由 `|a_j| ≤ c_j N^{k−j}` 得 `|b_r| ≪ N^{k−r−1}`。

本文件给出：

* `abs_diffCoeff_le`：`|b_r| ≤ Σ_{j>r} |a_j| C(j,r) |h|^{j−1−r}`（三角不等式）；
* `diffCoeff_bound`：在 `|a_j| ≤ C N^{k−j}`、`|h| ≤ N` 下，
  `|b_r| ≤ C · (Σ_{j>r} C(j,r)) · N^{k−1−r}`。
-/

open Finset

namespace Waring

/- Adapted from https://github.com/yunyougu50-create/waring-lean4/blob/cd0735c253f3b640262fcc74a61306cb41e23765/WaringWeylDiff.lean#L1-L164 -/

/-!
# Weyl 差分：步长 `h` 的差分把次数降一

Weyl 归纳（Jameson Theorem 1 的一般 `k`）的第一步是把指数和
`∑_{n≤N} e(α f(n))` 的矩估计归约到差分多项式
`φ(n,h) = (f(n+h) − f(n))/h`，其次数比 `f` 低一。本文件给出这个
**纯代数**零件：

* `polyEval a d`: 整系数多项式 `∑_{j≤d} a_j n^j` 的求值；
* `diffH h f = f(n+h) − f(n)`；
* `pow_diff`: 单项式的差分公式
  `(n+h)^j − n^j = h · ∑_{i<j} C(j,i) n^i h^{j−1−i}`；
* `diffCoeff a d h i = ∑_{i<j≤d} a_j C(j,i) h^{j−1−i}`：差分多项式的系数；
* `diffH_polyEval`: `diffH h (polyEval a d) = h · polyEval (diffCoeff a d h) d`；
* `diffCoeff_eq_zero_of_le`: `i ≥ d` 时 `diffCoeff a d h i = 0`，即次数真的降一。

这一步不需要任何分析；Jameson 讲义里 `φ(n,h)` 的定义与"次数降一"正是
Theorem 1 归纳步的代数前提。
-/

/-- 整系数多项式 `∑_{j=0}^{d} a_j n^j` 的求值。 -/
def polyEval (a : ℕ → ℤ) (d : ℕ) (n : ℤ) : ℤ :=
  ∑ j ∈ Finset.range (d + 1), a j * n ^ j

/-- 步长 `h` 的差分：`n ↦ f (n + h) − f n`。 -/
def diffH (h : ℤ) (f : ℤ → ℤ) : ℤ → ℤ := fun n => f (n + h) - f n

/-- **单项式差分公式**：`(n+h)^j − n^j = h · ∑_{i<j} C(j,i) n^i h^{j−1−i}`。 -/
theorem pow_diff (j : ℕ) (n h : ℤ) :
    (n + h) ^ j - n ^ j
      = h * ∑ i ∈ Finset.range j, (j.choose i : ℤ) * n ^ i * h ^ (j - 1 - i) := by
  cases j with
  | zero => simp
  | succ k =>
    rw [add_pow]
    rw [Finset.sum_range_succ]
    have hlast : n ^ (k + 1) * h ^ (k + 1 - (k + 1)) * (((k + 1).choose (k + 1) : ℕ) : ℤ)
        = n ^ (k + 1) := by
      simp
    rw [hlast]
    rw [add_sub_cancel_right]
    rw [show (k + 1) - 1 = k by omega]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [Finset.mem_range] at hi
    have h1 : k + 1 - i = (k - i) + 1 := by omega
    rw [h1, pow_succ]
    ring

/-- 差分多项式的系数：`b_i = ∑_{i<j≤d} a_j C(j,i) h^{j−1−i}`。 -/
def diffCoeff (a : ℕ → ℤ) (d : ℕ) (h : ℤ) (i : ℕ) : ℤ :=
  ∑ j ∈ Finset.Ico (i + 1) (d + 1), a j * (j.choose i : ℤ) * h ^ (j - 1 - i)

/-- **差分把次数降一**（带显式系数）：`diffH h (polyEval a d) = h · polyEval b d`，
其中 `b = diffCoeff a d h`。 -/
theorem diffH_polyEval (a : ℕ → ℤ) (d : ℕ) (h : ℤ) :
    diffH h (polyEval a d) = fun n => h * polyEval (diffCoeff a d h) d n := by
  funext n
  -- 逐项用单项式公式
  have hpt : ∀ j ∈ Finset.range (d + 1),
      a j * (n + h) ^ j - a j * n ^ j
        = h * ∑ i ∈ Finset.range j, a j * (j.choose i : ℤ) * n ^ i * h ^ (j - 1 - i) := by
    intro j _
    have hpd := pow_diff j n h
    calc a j * (n + h) ^ j - a j * n ^ j
        = a j * ((n + h) ^ j - n ^ j) := by ring
      _ = a j * (h * ∑ i ∈ Finset.range j, (j.choose i : ℤ) * n ^ i * h ^ (j - 1 - i)) := by
            rw [hpd]
      _ = ∑ i ∈ Finset.range j,
            a j * (h * ((j.choose i : ℤ) * n ^ i * h ^ (j - 1 - i))) := by
            rw [Finset.mul_sum, Finset.mul_sum]
      _ = ∑ i ∈ Finset.range j,
            h * (a j * (j.choose i : ℤ) * n ^ i * h ^ (j - 1 - i)) := by
            refine Finset.sum_congr rfl (fun i _ => by ring)
      _ = h * ∑ i ∈ Finset.range j, a j * (j.choose i : ℤ) * n ^ i * h ^ (j - 1 - i) := by
            rw [Finset.mul_sum]
  -- 三角形重排：把内层 `range j` 扩到 `range (d+1)`
  have hexp : ∀ j ∈ Finset.range (d + 1),
      (∑ i ∈ Finset.range j, a j * (j.choose i : ℤ) * n ^ i * h ^ (j - 1 - i))
        = ∑ i ∈ Finset.range (d + 1),
            (if i < j then a j * (j.choose i : ℤ) * n ^ i * h ^ (j - 1 - i) else 0) := by
    intro j hj
    rw [Finset.mem_range] at hj
    rw [← Finset.sum_filter]
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  unfold diffH polyEval diffCoeff
  rw [show (∑ j ∈ Finset.range (d + 1), a j * (n + h) ^ j)
        - (∑ j ∈ Finset.range (d + 1), a j * n ^ j)
      = ∑ j ∈ Finset.range (d + 1), (a j * (n + h) ^ j - a j * n ^ j) from
    (Finset.sum_sub_distrib (s := Finset.range (d + 1))
      (f := fun j => a j * (n + h) ^ j) (g := fun j => a j * n ^ j)).symm]
  rw [Finset.sum_congr rfl hpt]
  rw [← Finset.mul_sum]
  congr 1
  rw [Finset.sum_congr rfl hexp]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [Finset.mem_range] at hi
  rw [← Finset.sum_filter]
  have hset : (Finset.range (d + 1)).filter (fun j => i < j) = Finset.Ico (i + 1) (d + 1) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [show (∑ j ∈ (Finset.range (d + 1)).filter (fun j => i < j),
        a j * (j.choose i : ℤ) * n ^ i * h ^ (j - 1 - i))
      = (∑ j ∈ (Finset.range (d + 1)).filter (fun j => i < j),
        a j * (j.choose i : ℤ) * h ^ (j - 1 - i)) * n ^ i from by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl (fun j _ => by ring)]
  rw [hset]

/-- `i ≥ d` 时差分系数的次数确实降为 0。 -/
theorem diffCoeff_eq_zero_of_le {a : ℕ → ℤ} {d : ℕ} {h : ℤ} {i : ℕ} (hi : d ≤ i) :
    diffCoeff a d h i = 0 := by
  unfold diffCoeff
  apply Finset.sum_eq_zero
  intro j hj
  rw [Finset.mem_Ico] at hj
  omega

/-! ## 线性性与迭代接口 -/

/-- 差分系数的绝对值界（三角不等式）。 -/
theorem abs_diffCoeff_le (a : ℕ → ℤ) (d : ℕ) (h : ℤ) (r : ℕ) :
    |diffCoeff a d h r|
      ≤ ∑ j ∈ Finset.Ico (r + 1) (d + 1), |a j| * (j.choose r : ℤ) * |h| ^ (j - 1 - r) := by
  unfold diffCoeff
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine Finset.sum_le_sum (fun j _ => ?_)
  rw [abs_mul, abs_mul, abs_pow, abs_of_nonneg (by positivity : (0 : ℤ) ≤ (j.choose r : ℤ))]

/-- **系数界**：`|a_j| ≤ C·N^{d−j}` 且 `|h| ≤ N` ⟹
`|b_r| ≤ C·(Σ_{j>r} C(j,r))·N^{d−1−r}`。 -/
theorem diffCoeff_bound {a : ℕ → ℤ} {d : ℕ} {h : ℤ} {C N : ℕ}
    (ha : ∀ j, j ≤ d → |a j| ≤ (C : ℤ) * (N : ℤ) ^ (d - j))
    (hh : |h| ≤ (N : ℤ)) (r : ℕ) (hr : r < d) :
    |diffCoeff a d h r|
      ≤ (C : ℤ) * (∑ j ∈ Finset.Ico (r + 1) (d + 1), (j.choose r : ℤ))
        * (N : ℤ) ^ (d - 1 - r) := by
  refine le_trans (abs_diffCoeff_le a d h r) ?_
  -- 逐项：`|a_j| * C(j,r) * |h|^(j−1−r) ≤ C * C(j,r) * N^(d−1−r)`
  have hterm : ∀ j ∈ Finset.Ico (r + 1) (d + 1),
      |a j| * (j.choose r : ℤ) * |h| ^ (j - 1 - r)
        ≤ (C : ℤ) * (j.choose r : ℤ) * (N : ℤ) ^ (d - 1 - r) := by
    intro j hj
    rw [Finset.mem_Ico] at hj
    obtain ⟨hj1, hj2⟩ := hj
    have hjd : j ≤ d := by omega
    have hjr : r < j := by omega
    have hNj : 0 ≤ (N : ℤ) := by positivity
    -- 三个因子分别控制
    have h1 : |a j| ≤ (C : ℤ) * (N : ℤ) ^ (d - j) := ha j hjd
    have h2 : (0 : ℤ) ≤ (j.choose r : ℤ) := by positivity
    have h3 : |h| ^ (j - 1 - r) ≤ (N : ℤ) ^ (j - 1 - r) :=
      pow_le_pow_left₀ (abs_nonneg h) hh _
    -- 合并
    have hstep : |a j| * (j.choose r : ℤ) * |h| ^ (j - 1 - r)
        ≤ ((C : ℤ) * (N : ℤ) ^ (d - j)) * (j.choose r : ℤ) * (N : ℤ) ^ (j - 1 - r) := by
      have h12 : |a j| * (j.choose r : ℤ)
          ≤ ((C : ℤ) * (N : ℤ) ^ (d - j)) * (j.choose r : ℤ) :=
        mul_le_mul_of_nonneg_right h1 h2
      calc |a j| * (j.choose r : ℤ) * |h| ^ (j - 1 - r)
          = (|a j| * (j.choose r : ℤ)) * |h| ^ (j - 1 - r) := by ring
        _ ≤ (((C : ℤ) * (N : ℤ) ^ (d - j)) * (j.choose r : ℤ)) * |h| ^ (j - 1 - r) :=
              mul_le_mul_of_nonneg_right h12 (by positivity)
        _ ≤ (((C : ℤ) * (N : ℤ) ^ (d - j)) * (j.choose r : ℤ)) * (N : ℤ) ^ (j - 1 - r) :=
              mul_le_mul_of_nonneg_left h3 (by positivity)
        _ = ((C : ℤ) * (N : ℤ) ^ (d - j)) * (j.choose r : ℤ) * (N : ℤ) ^ (j - 1 - r) := by ring
    refine le_trans hstep ?_
    -- `N^(d−j) * N^(j−1−r) = N^(d−1−r)`
    have hexp : (d - j) + (j - 1 - r) = d - 1 - r := by omega
    have heq2 : ((C : ℤ) * (N : ℤ) ^ (d - j)) * (j.choose r : ℤ) * (N : ℤ) ^ (j - 1 - r)
        = (C : ℤ) * (j.choose r : ℤ) * (N : ℤ) ^ (d - 1 - r) := by
      calc ((C : ℤ) * (N : ℤ) ^ (d - j)) * (j.choose r : ℤ) * (N : ℤ) ^ (j - 1 - r)
          = (C : ℤ) * (j.choose r : ℤ) * ((N : ℤ) ^ (d - j) * (N : ℤ) ^ (j - 1 - r)) := by ring
        _ = (C : ℤ) * (j.choose r : ℤ) * (N : ℤ) ^ ((d - j) + (j - 1 - r)) := by
              rw [pow_add]
        _ = (C : ℤ) * (j.choose r : ℤ) * (N : ℤ) ^ (d - 1 - r) := by rw [hexp]
    exact le_of_eq heq2
  have heq : (∑ j ∈ Finset.Ico (r + 1) (d + 1),
        (C : ℤ) * (j.choose r : ℤ) * (N : ℤ) ^ (d - 1 - r))
      = (C : ℤ) * (∑ j ∈ Finset.Ico (r + 1) (d + 1), (j.choose r : ℤ))
        * (N : ℤ) ^ (d - 1 - r) := by
    rw [Finset.mul_sum, Finset.sum_mul]
  exact le_trans (Finset.sum_le_sum hterm) (le_of_eq heq)

end Waring
