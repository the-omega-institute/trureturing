/- GID: D5/S3/Arith/Additive/Waring/WaringExpSum
   generality: G
   mirror-B: D5/B/S3/Arith/Additive/Waring/WaringExpSum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Third-party formalization of the qualitative Hilbert–Waring theorem. -/

/- Source: https://github.com/yunyougu50-create/waring-lean4/blob/cd0735c253f3b640262fcc74a61306cb41e23765/WaringExpSum.lean#L1-L123
   Modified for this repository. Local imports use their D5 module paths.
   Selected declaration closure and supporting source.
   Full Apache-2.0 license: D5/S3/Arith/Additive/Waring/WaringDensity.lean. -/

/-
Copyright (c) 2026 The Waring formalization authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Waring formalization authors
-/
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import D5.S3.Arith.Additive.Waring.WaringWeylDiff

/-!
# 指数和 `e(x)` 与一般指数和 `Σ_{n≤N} e(α f(n))`

Weyl 归纳（Jameson Theorem 1 的一般 `k`）需要一般整系数多项式的指数和，
而不是 `theta` 的 `f(n) = n²` 特例。本文件建立：

* `e x = exp(2πi x)`，及其**乘性** `e_add`、**共轭** `e_neg`、**模 1** `norm_e`；
* `expSum f N α = Σ_{n=0}^{N} e(α f(n))`；
* `expSum_conj`：`conj (expSum f) = expSum (-f)`；
* `normSq_expSum`：`‖expSum f‖²` 展开成双和
  `Σ_{n,m} e(α (f(m) − f(n)))`（Weyl 差分不等式的起点）；
-/

open Finset intervalIntegral

namespace Waring

/- Integral orthogonality from WaringCircle.lean at the same upstream revision.
   Copyright (c) 2026 The Waring formalization authors. All rights reserved.
   Released under Apache 2.0 license as described in WaringDensity.lean.
   Authors: The Waring formalization authors -/

/-- **正交性**：`∫₀¹ exp(2πi m α) dα = 1`（`m = 0`）或 `0`（`m ≠ 0`）。 -/
theorem integral_exp_mul_int (m : ℤ) :
    (∫ x in (0 : ℝ)..1, Complex.exp ((m : ℂ) * (2 * Real.pi * Complex.I) * (x : ℂ)))
      = if m = 0 then 1 else 0 := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  · have hc : ((m : ℂ) * (2 * Real.pi * Complex.I)) ≠ 0 := by
      simp [hm, Real.pi_ne_zero]
    rw [integral_exp_mul_complex (a := (0 : ℝ)) (b := 1) hc]
    have hexp : Complex.exp ((m : ℂ) * (2 * Real.pi * Complex.I)) = 1 :=
      Complex.exp_int_mul_two_pi_mul_I m
    simp [hexp, hm]

/-- `e(x) = exp(2πi x)`。 -/
noncomputable def e (x : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * (x : ℂ))

/-- **正交性**：`∫₀¹ e(m·α) dα = 1`（`m = 0`）或 `0`（`m ≠ 0`）。 -/
theorem integral_e_mul_int (m : ℤ) :
    (∫ α in (0 : ℝ)..1, e ((m : ℝ) * α)) = if m = 0 then (1 : ℂ) else 0 := by
  have hv : ∀ α : ℝ,
      e ((m : ℝ) * α) = Complex.exp ((m : ℂ) * (2 * Real.pi * Complex.I) * (α : ℂ)) := by
    intro α
    unfold e
    congr 1
    push_cast
    ring
  simp_rw [hv]
  exact integral_exp_mul_int m

/-- 乘性：`e(x+y) = e(x)·e(y)`。 -/
theorem e_add (x y : ℝ) : e (x + y) = e x * e y := by
  unfold e
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- 共轭：`e(−x) = conj (e x)`。 -/
theorem e_neg (x : ℝ) : e (-x) = (starRingEnd ℂ) (e x) := by
  unfold e
  rw [← Complex.exp_conj]
  congr 1
  push_cast
  simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
  ring

/-- `|e(x)| = 1`。 -/
theorem norm_e (x : ℝ) : ‖e x‖ = 1 := by
  unfold e
  have h : 2 * (Real.pi : ℂ) * Complex.I * (x : ℂ)
      = (((2 * Real.pi * x : ℝ)) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [h, Complex.norm_exp_ofReal_mul_I]

/-- 一般指数和 `expSum f N α = Σ_{n=0}^{N} e(α f(n))`。 -/
noncomputable def expSum (f : ℤ → ℤ) (N : ℕ) (α : ℝ) : ℂ :=
  ∑ n ∈ Finset.range (N + 1), e (((f (n : ℤ) : ℤ) : ℝ) * α)

/-- 共轭把 `f` 变成 `−f`。 -/
theorem expSum_conj (f : ℤ → ℤ) (N : ℕ) (α : ℝ) :
    (starRingEnd ℂ) (expSum f N α) = expSum (fun n => -f n) N α := by
  unfold expSum
  rw [map_sum]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [← e_neg]
  congr 1
  push_cast
  ring

/-- **`‖S‖²` 的双和展开**：`‖Σ_n e(α f(n))‖² = Σ_{n,m} e(α (f(m) − f(n)))`。
这是 Weyl 差分不等式的起点（下一步按差 `m − n` 分组）。 -/
theorem normSq_expSum (f : ℤ → ℤ) (N : ℕ) (α : ℝ) :
    ((Complex.normSq (expSum f N α) : ℝ) : ℂ)
      = ∑ n ∈ Finset.range (N + 1), ∑ m ∈ Finset.range (N + 1),
          e (((f (m : ℤ) - f (n : ℤ) : ℤ) : ℝ) * α) := by
  rw [Complex.normSq_eq_conj_mul_self, expSum_conj]
  unfold expSum
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl (fun n _ => Finset.sum_congr rfl (fun m _ => ?_))
  rw [← e_add]
  congr 1
  push_cast
  ring

end Waring
