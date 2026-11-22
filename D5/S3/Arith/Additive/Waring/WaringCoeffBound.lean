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

import D5.S3.Arith.Additive.Waring.WaringWeylDiff

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
    (hh : |h| ≤ (N : ℤ)) (hC : 0 ≤ (C : ℤ)) (r : ℕ) (hr : r < d) :
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
