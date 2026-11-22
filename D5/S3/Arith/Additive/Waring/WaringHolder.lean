/- GID: D5/S3/Arith/Additive/Waring/WaringHolder
   generality: G
   mirror-B: D5/B/S3/Arith/Additive/Waring/WaringHolder
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Third-party formalization of the qualitative Hilbert–Waring theorem. -/

/- Source: https://github.com/yunyougu50-create/waring-lean4/blob/cd0735c253f3b640262fcc74a61306cb41e23765/WaringHolder.lean#L1-L203
   Modified for this repository. Local imports use their D5 module paths.
   Selected declaration closure and supporting source.
   Full Apache-2.0 license: D5/S3/Arith/Additive/Waring/WaringDensity.lean. -/

import D5.S3.Arith.Additive.Waring.WaringWeylInq

/-!
# Hölder 步骤（Weyl 归纳）

Jameson Theorem 1 归纳步：由 `|S|² ≤ N+1 + Σ_{h≠0} b_h`（`WaringWeylInq`），
对 `|Σ_{h≠0} b_h|` 用 Hölder：

```text
|Σ_{h≠0} b_h|^m ≤ (Σ_{h≠0} |b_h|)^m ≤ (2N)^{m−1} Σ_{h≠0} |b_h|^m .
```

本文件给出：

* `sum_pow_le_card_pow_mul_sum_pow`：幂平均不等式
  `(Σ_{i∈s} x_i)^m ≤ #s^{m−1} · Σ x_i^m`（`x_i ≥ 0`）；
* `holder_step`：`‖Σ_{h≠0} b_h‖^m ≤ (2N)^{m−1} Σ_{h≠0} ‖b_h‖^m`。
-/

open Finset

namespace Waring

/-- **幂平均不等式**：`(Σ x_i)^m ≤ #s^{m−1} · Σ x_i^m`（`x_i ≥ 0`，`m ≥ 1`）。 -/
theorem sum_pow_le_card_pow_mul_sum_pow {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (hx : ∀ i ∈ s, 0 ≤ x i) (m : ℕ) (hm : 1 ≤ m) :
    (∑ i ∈ s, x i) ^ m ≤ (s.card : ℝ) ^ (m - 1) * ∑ i ∈ s, x i ^ m := by
  have h := Real.rpow_sum_le_const_mul_sum_rpow s x (p := (m : ℝ)) (by exact_mod_cast hm)
  have h1 : (∑ i ∈ s, |x i|) = ∑ i ∈ s, x i :=
    Finset.sum_congr rfl (fun i hi => abs_of_nonneg (hx i hi))
  rw [h1] at h
  have h3 : (∑ i ∈ s, |x i| ^ (m : ℝ)) = ∑ i ∈ s, x i ^ m := by
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [abs_of_nonneg (hx i hi), Real.rpow_natCast]
  rw [h3] at h
  rw [Real.rpow_natCast] at h
  have hcast : ((m : ℝ) - 1) = ((m - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hm]
    norm_num
  rw [hcast, Real.rpow_natCast] at h
  exact h

/-- **二元幂平均**：`(a+b)^m ≤ 2^{m−1}(a^m + b^m)`（`a, b ≥ 0`，`m ≥ 1`）。 -/
theorem add_pow_le_two_pow (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (m : ℕ) (hm : 1 ≤ m) :
    (a + b) ^ m ≤ 2 ^ (m - 1) * (a ^ m + b ^ m) := by
  have hx : ∀ i ∈ (Finset.univ : Finset (Fin 2)),
      0 ≤ (fun i : Fin 2 => if i = 0 then a else b) i := by
    intro i _
    fin_cases i <;> simp [ha, hb]
  have h := sum_pow_le_card_pow_mul_sum_pow (Finset.univ : Finset (Fin 2))
    (fun i : Fin 2 => if i = 0 then a else b) hx m hm
  simpa [Fin.sum_univ_two] using h

/-- **Jameson (2) 的点态形式**（积分之前）：
`‖S‖^{2m} ≤ 2^{m−1}·((N+1)^m + (2N)^{m−1}·Σ_{h≠0}‖b_h‖^m)`。 -/
theorem normSq_pow_le (f : ℤ → ℤ) (N : ℕ) (α : ℝ) (m : ℕ) (hm : 1 ≤ m) (hN : 1 ≤ N) :
    ‖expSum f N α‖ ^ (2 * m)
      ≤ 2 ^ (m - 1) * ((N + 1 : ℝ) ^ m
          + (2 * (N : ℝ)) ^ (m - 1)
            * ∑ h ∈ (Finset.Icc (-(N : ℤ)) (N : ℤ)).erase 0, ‖T f N α h‖ ^ m) := by
  set S : Finset ℤ := (Finset.Icc (-(N : ℤ)) (N : ℤ)).erase 0 with hS
  set B : ℝ := ∑ h ∈ S, ‖T f N α h‖ with hB
  -- 集合大小
  have h0mem : (0 : ℤ) ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) := by
    rw [Finset.mem_Icc]
    constructor <;> simp
  have hcard : (S.card : ℝ) = 2 * (N : ℝ) := by
    rw [hS, Finset.card_erase_of_mem h0mem, Int.card_Icc]
    have hc : (N : ℤ) + 1 - (-(N : ℤ)) = 2 * (N : ℤ) + 1 := by ring
    rw [hc]
    have htoNat : (2 * (N : ℤ) + 1).toNat = 2 * N + 1 := by
      have h := Int.toNat_of_nonneg (show (0 : ℤ) ≤ 2 * (N : ℤ) + 1 by positivity)
      have h2 : ((2 * (N : ℤ) + 1).toNat : ℤ) = ((2 * N + 1 : ℕ) : ℤ) := by
        rw [h]
        push_cast
        ring
      exact_mod_cast h2
    rw [htoNat]
    have hsub : 2 * N + 1 - 1 = 2 * N := by omega
    rw [hsub]
    push_cast
    ring
  -- 1) `‖S‖² ≤ N+1 + B`
  have h1 : ‖expSum f N α‖ ^ 2 ≤ (N + 1 : ℝ) + B := by
    rw [hB, hS]
    exact normSq_expSum_le_zero f N α
  have h2 : ‖expSum f N α‖ ^ (2 * m) ≤ ((N + 1 : ℝ) + B) ^ m := by
    rw [pow_mul]
    exact pow_le_pow_left₀ (by positivity) h1 m
  -- 2) 二元幂平均
  have h3 : ((N + 1 : ℝ) + B) ^ m
      ≤ 2 ^ (m - 1) * ((N + 1 : ℝ) ^ m + B ^ m) :=
    add_pow_le_two_pow _ _ (by positivity) (by positivity) m hm
  -- 3) `B^m ≤ (2N)^{m−1} Σ ‖b_h‖^m`
  have h4 : B ^ m ≤ (2 * (N : ℝ)) ^ (m - 1) * ∑ h ∈ S, ‖T f N α h‖ ^ m := by
    have hb := sum_pow_le_card_pow_mul_sum_pow S (fun h => ‖T f N α h‖)
      (fun h _ => norm_nonneg _) m hm
    rw [hB]
    refine le_trans hb ?_
    rw [hcard]
  calc ‖expSum f N α‖ ^ (2 * m)
      ≤ ((N + 1 : ℝ) + B) ^ m := h2
    _ ≤ 2 ^ (m - 1) * ((N + 1 : ℝ) ^ m + B ^ m) := h3
    _ ≤ 2 ^ (m - 1)
          * ((N + 1 : ℝ) ^ m + (2 * (N : ℝ)) ^ (m - 1) * ∑ h ∈ S, ‖T f N α h‖ ^ m) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          linarith [h4]
    _ = 2 ^ (m - 1) * ((N + 1 : ℝ) ^ m
          + (2 * (N : ℝ)) ^ (m - 1)
            * ∑ h ∈ (Finset.Icc (-(N : ℤ)) (N : ℤ)).erase 0, ‖T f N α h‖ ^ m) := by
          rw [hS]

end Waring
