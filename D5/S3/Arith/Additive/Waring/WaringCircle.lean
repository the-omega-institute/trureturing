/- GID: D5/S3/Arith/Additive/Waring/WaringCircle
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Third-party formalization of the qualitative Hilbert–Waring theorem. -/

/- Source: https://github.com/yunyougu50-create/waring-lean4/blob/cd0735c253f3b640262fcc74a61306cb41e23765/WaringCircle.lean#L1-L194
   Modified for this repository. Local imports use their D5 module paths.
   Full Apache-2.0 license: D5/S3/Arith/Additive/Waring/WaringStatement.lean. -/

/-
Copyright (c) 2026 The Waring formalization authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Waring formalization authors
-/
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# 圆法的原子：`θ` 函数、正交性、共轭

Linnik 证明的分析半边（`WARING-M3-PLAN.md` Theorem 1）从指数和出发：

```text
θ_N(α) = ∑_{n ≤ N} e(α n²),        e(x) = exp(2πi x).
```

本文件建立三块最基础的东西：

* `theta`：`θ` 的定义；
* `integral_exp_mul_int`：**正交性** `∫₀¹ e(mα) dα = δ_{m0}`；
* `conj_theta`：`conj θ_N(α) = ∑ e(-α n²)`，从而
  `|θ|² = θ · conj θ` 是实数，且 `|θ|^{2k}` 可以展开成 `2k` 重和。

有了这些，"矩 = 计数"（`∫₀¹ |θ|^{2k} dα` 等于相应方程的解数）就只剩
展开有限和、交换积分与求和、逐项用正交性。

**注意**：本文件只做这些原子。Theorem 1 的估计（`≪ N^{8^{k-1}-k}`）仍未做，
见 `WARING-M3-PLAN.md`。
-/

open intervalIntegral

namespace Waring

/-- 圆法中的指数和 `θ_N(α) = ∑_{n ≤ N} e(α n²)`。 -/
noncomputable def theta (N : ℕ) (α : ℝ) : ℂ :=
  ∑ n : Fin (N + 1), Complex.exp (2 * Real.pi * Complex.I * ((n : ℂ) ^ 2 * (α : ℂ)))

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

/-- `θ` 的共轭：`conj θ_N(α) = ∑_{n ≤ N} e(-α n²)`。 -/
theorem conj_theta (N : ℕ) (α : ℝ) :
    (starRingEnd ℂ) (theta N α)
      = ∑ n : Fin (N + 1),
          Complex.exp (-(2 * Real.pi * Complex.I * ((n : ℂ) ^ 2 * (α : ℂ)))) := by
  unfold theta
  rw [map_sum]
  refine Finset.sum_congr rfl ?_
  intro n _
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, map_pow, map_ofNat, map_natCast, Complex.conj_I, Complex.conj_ofReal]
  ring

/-- `|θ|² = conj θ · θ`（作为复数）。 -/
theorem ofReal_normSq_theta (N : ℕ) (α : ℝ) :
    ((Complex.normSq (theta N α) : ℝ) : ℂ) = (starRingEnd ℂ) (theta N α) * theta N α :=
  Complex.normSq_eq_conj_mul_self

/-- `θ²` 展开成二重和。 -/
theorem theta_sq (N : ℕ) (α : ℝ) :
    theta N α ^ 2 = ∑ a : Fin (N + 1), ∑ b : Fin (N + 1),
      Complex.exp (2 * Real.pi * Complex.I * (((a : ℂ) ^ 2 + (b : ℂ) ^ 2) * (α : ℂ))) := by
  unfold theta
  rw [sq, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [← Complex.exp_add]
  congr 1
  ring

/-- `(conj θ)²` 展开成二重和。 -/
theorem conj_theta_sq (N : ℕ) (α : ℝ) :
    (starRingEnd ℂ) (theta N α) ^ 2 = ∑ a : Fin (N + 1), ∑ b : Fin (N + 1),
      Complex.exp (-(2 * Real.pi * Complex.I * (((a : ℂ) ^ 2 + (b : ℂ) ^ 2) * (α : ℂ)))) := by
  rw [conj_theta, sq, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [← Complex.exp_add]
  congr 1
  ring

/-- `θ⁴` 展开成单层四重和。 -/
theorem theta_pow_four (N : ℕ) (α : ℝ) :
    theta N α ^ 4 = ∑ p : Fin 4 → Fin (N + 1),
      Complex.exp (2 * Real.pi * Complex.I * ((∑ i : Fin 4, ((p i : ℕ) : ℂ) ^ 2) * (α : ℂ))) := by
  unfold theta
  rw [Finset.sum_pow']
  rw [Fintype.piFinset_univ]
  refine Finset.sum_congr rfl ?_
  intro p _
  rw [← Complex.exp_sum]
  congr 1
  rw [Finset.sum_mul, Finset.mul_sum]

/-- `(conj θ)⁴` 展开成单层四重和。 -/
theorem conj_theta_pow_four (N : ℕ) (α : ℝ) :
    (starRingEnd ℂ) (theta N α) ^ 4 = ∑ p : Fin 4 → Fin (N + 1),
      Complex.exp (-(2 * Real.pi * Complex.I * ((∑ i : Fin 4, ((p i : ℕ) : ℂ) ^ 2) * (α : ℂ)))) := by
  rw [conj_theta]
  rw [Finset.sum_pow']
  rw [Fintype.piFinset_univ]
  refine Finset.sum_congr rfl ?_
  intro p _
  rw [← Complex.exp_sum]
  congr 1
  rw [Finset.sum_neg_distrib]
  congr 1
  rw [Finset.sum_mul, Finset.mul_sum]

/-- **矩 = 计数**（`k = 2` 的八次矩）：

```text
∫₀¹ |θ_N(α)|⁸ dα = #{(p, q) : (Fin 4 → Fin (N+1))² | Σ pᵢ² = Σ qᵢ²}.
```
-/
theorem integral_normSq_pow_four (N : ℕ) :
    (∫ α in (0 : ℝ)..1, (Complex.normSq (theta N α)) ^ 4)
      = (((Finset.univ : Finset ((Fin 4 → Fin (N + 1)) × (Fin 4 → Fin (N + 1)))).filter
          (fun pq => (∑ i : Fin 4, ((pq.1 i : ℕ)) ^ 2) = (∑ i : Fin 4, ((pq.2 i : ℕ)) ^ 2))).card : ℝ) := by
  have hfun : ∀ α : ℝ, (((Complex.normSq (theta N α)) ^ 4 : ℝ) : ℂ)
      = ((starRingEnd ℂ) (theta N α)) ^ 4 * (theta N α) ^ 4 := by
    intro α
    rw [Complex.ofReal_pow, Complex.normSq_eq_conj_mul_self]
    ring
  have hcomb : ∀ (p q : Fin 4 → Fin (N + 1)) (α : ℝ),
      Complex.exp (-(2 * Real.pi * Complex.I * ((∑ i : Fin 4, ((p i : ℕ) : ℂ) ^ 2) * (α : ℂ))))
        * Complex.exp (2 * Real.pi * Complex.I * ((∑ i : Fin 4, ((q i : ℕ) : ℂ) ^ 2) * (α : ℂ)))
      = Complex.exp (((∑ i : Fin 4, ((q i : ℕ) : ℂ) ^ 2) - (∑ i : Fin 4, ((p i : ℕ) : ℂ) ^ 2))
          * (2 * Real.pi * Complex.I) * (α : ℂ)) := by
    intro p q α
    rw [← Complex.exp_add]
    congr 1
    ring
  have hstep : ∀ pq : (Fin 4 → Fin (N + 1)) × (Fin 4 → Fin (N + 1)),
      (∫ α in (0 : ℝ)..1, Complex.exp (((∑ i : Fin 4, ((pq.2 i : ℕ) : ℂ) ^ 2)
            - (∑ i : Fin 4, ((pq.1 i : ℕ) : ℂ) ^ 2)) * (2 * Real.pi * Complex.I) * (α : ℂ)))
        = (if (∑ i : Fin 4, ((pq.1 i : ℕ)) ^ 2) = (∑ i : Fin 4, ((pq.2 i : ℕ)) ^ 2) then 1 else 0) := by
    intro pq
    set m : ℤ := ((∑ i : Fin 4, ((pq.2 i : ℕ)) ^ 2 : ℕ) : ℤ)
      - ((∑ i : Fin 4, ((pq.1 i : ℕ)) ^ 2 : ℕ) : ℤ) with hm
    have hexp : ((∑ i : Fin 4, ((pq.2 i : ℕ) : ℂ) ^ 2) - (∑ i : Fin 4, ((pq.1 i : ℕ) : ℂ) ^ 2))
        = (m : ℂ) := by
      rw [hm]
      push_cast
      ring
    rw [hexp, integral_exp_mul_int]
    by_cases h : (∑ i : Fin 4, ((pq.1 i : ℕ)) ^ 2) = (∑ i : Fin 4, ((pq.2 i : ℕ)) ^ 2)
    · have hz : m = 0 := by
        rw [hm, h]; simp
      simp [h, hz]
    · have hz : m ≠ 0 := by
        intro hz
        rw [hm] at hz
        have hcast2 : ((∑ i : Fin 4, ((pq.2 i : ℕ)) ^ 2 : ℕ) : ℤ)
            = ((∑ i : Fin 4, ((pq.1 i : ℕ)) ^ 2 : ℕ) : ℤ) := by linarith
        exact h (by exact_mod_cast hcast2.symm)
      simp [h, hz]
  have hswap : (∫ α in (0 : ℝ)..1, ∑ p : (Fin 4 → Fin (N + 1)), ∑ q : (Fin 4 → Fin (N + 1)),
      Complex.exp ((((∑ i : Fin 4, ((q i : ℕ) : ℂ) ^ 2) - (∑ i : Fin 4, ((p i : ℕ) : ℂ) ^ 2))
        * (2 * Real.pi * Complex.I) * (α : ℂ))))
      = ∑ p : (Fin 4 → Fin (N + 1)), ∑ q : (Fin 4 → Fin (N + 1)),
          ∫ α in (0 : ℝ)..1, Complex.exp ((((∑ i : Fin 4, ((q i : ℕ) : ℂ) ^ 2)
            - (∑ i : Fin 4, ((p i : ℕ) : ℂ) ^ 2)) * (2 * Real.pi * Complex.I) * (α : ℂ))) := by
    rw [intervalIntegral.integral_finsetSum]
    · refine Finset.sum_congr rfl ?_
      intro p _
      rw [intervalIntegral.integral_finsetSum]
      intro q _
      exact Continuous.intervalIntegrable (by fun_prop) 0 1
    · intro p _
      exact Continuous.intervalIntegrable (by fun_prop) 0 1
  apply Complex.ofReal_inj.mp
  rw [← intervalIntegral.integral_ofReal]
  simp_rw [hfun, conj_theta_pow_four, theta_pow_four]
  simp only [Finset.sum_mul_sum]
  simp_rw [hcomb]
  rw [hswap]
  rw [Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => hstep (p, q)))]
  rw [← Fintype.sum_prod_type (f := fun pq : (Fin 4 → Fin (N + 1)) × (Fin 4 → Fin (N + 1)) =>
    if (∑ i : Fin 4, ((pq.1 i : ℕ)) ^ 2) = (∑ i : Fin 4, ((pq.2 i : ℕ)) ^ 2) then (1 : ℂ) else 0)]
  rw [Finset.sum_boole]
  norm_cast

end Waring
