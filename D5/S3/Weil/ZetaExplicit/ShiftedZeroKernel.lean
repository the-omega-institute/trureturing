/- GID: D5/S3/Weil/ZetaExplicit/ShiftedZeroKernel
   generality: G
   mirror-B: D5/B/S3/Weil/ZetaExplicit/ShiftedZeroKernel
   mirror-E: none(waiver:analytic-local-count-kernel)
   anchors: []
   utility: none
   digest: Bound the actual shifted multiplicity kernel by a logarithmic weight. -/

/-
The finite-window grouping is adapted from ZeroSummability, whose original source is
anthropics/zeta-23-lean, commit 3635e74826a4c1fcece7d1cd2b6fa75e43a00510.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import D5.S3.Weil.ZetaExplicit.ZeroSummability

/-! The shifted multiplicity kernel is controlled by the two-sided local count. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace Zeta23.WeilEF

private theorem log_abs_add_three_ge_one (x : ℝ) :
    1 ≤ Real.log (|x| + 3) := by
  rw [Real.le_log_iff_exp_le (by positivity)]
  have h := Real.exp_one_lt_d9
  linarith [abs_nonneg x]

/-- A displacement of at most one costs a factor of three. -/
private theorem shifted_denominator_three (u d : ℝ) (hd0 : 0 ≤ d) (hd1 : d ≤ 1) :
    1 + (u + d) ^ 2 ≤ 3 * (1 + u ^ 2) := by
  have hd2 : d ^ 2 ≤ 1 := by nlinarith
  nlinarith [sq_nonneg (u - d), sq_nonneg u]

private theorem shifted_log_numerator (s : ℝ) (j : ℤ) :
    Real.log (|((key s + j : ℤ) : ℝ)| + 3) ≤
      2 * Real.log (|s| + 3) + Real.log (|(j : ℝ)| + 3) := by
  have hn : |(key s : ℝ)| ≤ |s| + 1 := by
    rw [abs_le]
    have hlt := key_lt s
    have hle := le_key_add_one s
    constructor <;> linarith [le_abs_self s, neg_abs_le s]
  have hprod : |((key s + j : ℤ) : ℝ)| + 3 ≤
      (|(key s : ℝ)| + 3) * (|(j : ℝ)| + 3) := by
    push_cast
    have h := abs_add_le (key s : ℝ) (j : ℝ)
    nlinarith [abs_nonneg (key s : ℝ), abs_nonneg (j : ℝ),
      mul_nonneg (abs_nonneg (key s : ℝ)) (abs_nonneg (j : ℝ))]
  have hnlog : Real.log (|(key s : ℝ)| + 3) ≤
      Real.log 2 + Real.log (|s| + 3) := by
    rw [← Real.log_mul (by norm_num) (by positivity)]
    exact Real.log_le_log (by positivity) (by linarith [abs_nonneg s])
  have hlog2 : Real.log 2 ≤ Real.log (|s| + 3) :=
    Real.log_le_log (by norm_num) (by linarith [abs_nonneg s])
  calc
    Real.log (|((key s + j : ℤ) : ℝ)| + 3) ≤
        Real.log ((|(key s : ℝ)| + 3) * (|(j : ℝ)| + 3)) :=
      Real.log_le_log (by positivity) hprod
    _ = Real.log (|(key s : ℝ)| + 3) + Real.log (|(j : ℝ)| + 3) :=
      Real.log_mul (by positivity) (by positivity)
    _ ≤ _ := by linarith

/-- Translation is performed on finite integer sets before any shifted infinite sum. -/
private theorem shifted_integer_weight_finite_le (s : ℝ) (B : Finset ℤ) :
    ∑ k ∈ B, Real.log (|(k : ℝ)| + 3) / (1 + (s - (k : ℝ)) ^ 2) ≤
      9 * totalWeight * Real.log (|s| + 3) := by
  classical
  let J := B.image (fun k => k - key s)
  have htranslate :
      (∑ k ∈ B, Real.log (|(k : ℝ)| + 3) / (1 + (s - (k : ℝ)) ^ 2)) =
        ∑ j ∈ J, Real.log (|((key s + j : ℤ) : ℝ)| + 3) /
          (1 + (s - ((key s + j : ℤ) : ℝ)) ^ 2) := by
    change _ = ∑ j ∈ B.image (fun k => k - key s), _
    rw [Finset.sum_image (fun a ha b hb hab => (sub_left_inj).mp hab)]
    apply Finset.sum_congr rfl
    intro k hk
    rw [show key s + (k - key s) = k by omega]
  have hpoint (j : ℤ) :
      Real.log (|((key s + j : ℤ) : ℝ)| + 3) /
          (1 + (s - ((key s + j : ℤ) : ℝ)) ^ 2) ≤
        3 * ((2 * Real.log (|s| + 3)) / (1 + (j : ℝ) ^ 2) +
          Real.log (|(j : ℝ)| + 3) / (1 + (j : ℝ) ^ 2)) := by
    have hden : 1 + (j : ℝ) ^ 2 ≤
        3 * (1 + (s - ((key s + j : ℤ) : ℝ)) ^ 2) := by
      have h := shifted_denominator_three
        (-(s - ((key s + j : ℤ) : ℝ))) (s - (key s : ℝ))
        (by linarith [key_lt s]) (by linarith [le_key_add_one s])
      push_cast at h ⊢
      nlinarith [h]
    have hinv : 1 / (1 + (s - ((key s + j : ℤ) : ℝ)) ^ 2) ≤
        3 / (1 + (j : ℝ) ^ 2) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      linarith
    calc
      _ = Real.log (|((key s + j : ℤ) : ℝ)| + 3) *
          (1 / (1 + (s - ((key s + j : ℤ) : ℝ)) ^ 2)) := by ring
      _ ≤ (2 * Real.log (|s| + 3) + Real.log (|(j : ℝ)| + 3)) *
          (3 / (1 + (j : ℝ) ^ 2)) :=
        mul_le_mul (shifted_log_numerator s j) hinv (by positivity)
          (by linarith [log_abs_add_three_ge_one s, log_abs_add_three_ge_one (j : ℝ)])
      _ = _ := by ring
  have hweight : (∑ j ∈ J, Real.log (|(j : ℝ)| + 3) / (1 + (j : ℝ) ^ 2)) ≤
      totalWeight :=
    summable_weight.sum_le_tsum _ (fun j _ => div_nonneg
      (Real.log_nonneg (by linarith [abs_nonneg (j : ℝ)])) (by positivity))
  have hunweighted : (∑ j ∈ J, 1 / (1 + (j : ℝ) ^ 2)) ≤ totalWeight := by
    refine le_trans (Finset.sum_le_sum (fun j hj => ?_)) hweight
    exact div_le_div_of_nonneg_right (log_abs_add_three_ge_one (j : ℝ)) (by positivity)
  have hW0 : 0 ≤ totalWeight :=
    tsum_nonneg (fun j => div_nonneg
      (Real.log_nonneg (by linarith [abs_nonneg (j : ℝ)])) (by positivity))
  rw [htranslate]
  calc
    _ ≤ ∑ j ∈ J, 3 * ((2 * Real.log (|s| + 3)) / (1 + (j : ℝ) ^ 2) +
        Real.log (|(j : ℝ)| + 3) / (1 + (j : ℝ) ^ 2)) :=
      Finset.sum_le_sum (fun j hj => hpoint j)
    _ = 3 * (2 * Real.log (|s| + 3) * (∑ j ∈ J, 1 / (1 + (j : ℝ) ^ 2)) +
        ∑ j ∈ J, Real.log (|(j : ℝ)| + 3) / (1 + (j : ℝ) ^ 2)) := by
      simp_rw [div_eq_mul_inv, one_mul]
      rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum]
    _ ≤ 3 * (2 * Real.log (|s| + 3) * totalWeight + totalWeight) := by
      gcongr
      linarith [log_abs_add_three_ge_one s]
    _ ≤ 9 * totalWeight * Real.log (|s| + 3) := by
      nlinarith [mul_nonneg hW0 (sub_nonneg.mpr (log_abs_add_three_ge_one s))]

/-- Every finite subset is bounded before summability is invoked. -/
private theorem shifted_zero_kernel_finite_le (Z : ZeroConfig) {A : ℝ} (hA : 1 ≤ A)
    (hlocal : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A * Real.log (|t| + 3))
    (s : ℝ) (E : Finset Z.carrier) :
    ∑ ρ ∈ E, (Z.mult ρ : ℝ) / (1 + (s - (gammaOf ρ).re) ^ 2) ≤
      27 * A * totalWeight * Real.log (|s| + 3) := by
  classical
  have hLC := Tail.LocalCount.ofWindowCount Z hA hlocal
  have hA0 : 0 ≤ A := zero_le_one.trans hA
  let κ : Z.carrier → ℤ := fun ρ => key (ρ : ℂ).im
  simp_rw [gammaOf_re]
  rw [← Finset.sum_fiberwise_of_maps_to (g := κ) (t := E.image κ)
    (fun ρ hρ => Finset.mem_image_of_mem κ hρ)]
  have hfiber (k : ℤ) :
      ∑ ρ ∈ E with κ ρ = k, (Z.mult ρ : ℝ) / (1 + (s - (ρ : ℂ).im) ^ 2) ≤
        3 * A * (Real.log (|(k : ℝ)| + 3) / (1 + (s - (k : ℝ)) ^ 2)) := by
    have hwin := hLC.window (k : ℝ) (E.filter fun ρ => κ ρ = k) (by
      intro ρ hρ
      have hk := (Finset.mem_filter.mp hρ).2
      change key (ρ : ℂ).im = k at hk
      rw [← hk]
      exact ⟨key_lt _, le_key_add_one _⟩)
    have hpoint : ∀ ρ ∈ E.filter (fun ρ => κ ρ = k),
        (Z.mult ρ : ℝ) / (1 + (s - (ρ : ℂ).im) ^ 2) ≤
          (3 / (1 + (s - (k : ℝ)) ^ 2)) * (Z.mult ρ : ℝ) := by
      intro ρ hρ
      have hk := (Finset.mem_filter.mp hρ).2
      change key (ρ : ℂ).im = k at hk
      have hlt := key_lt (ρ : ℂ).im
      have hle := le_key_add_one (ρ : ℂ).im
      rw [hk] at hlt hle
      have hden : 1 + (s - (k : ℝ)) ^ 2 ≤
          3 * (1 + (s - (ρ : ℂ).im) ^ 2) := by
        have h := shifted_denominator_three (s - (ρ : ℂ).im)
          ((ρ : ℂ).im - (k : ℝ)) (by linarith) (by linarith)
        convert h using 1; ring
      have hinv : 1 / (1 + (s - (ρ : ℂ).im) ^ 2) ≤
          3 / (1 + (s - (k : ℝ)) ^ 2) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        linarith
      calc
        _ = (Z.mult ρ : ℝ) * (1 / (1 + (s - (ρ : ℂ).im) ^ 2)) := by ring
        _ ≤ (Z.mult ρ : ℝ) * (3 / (1 + (s - (k : ℝ)) ^ 2)) :=
          mul_le_mul_of_nonneg_left hinv (Nat.cast_nonneg _)
        _ = _ := by ring
    calc
      _ ≤ ∑ ρ ∈ E with κ ρ = k,
          (3 / (1 + (s - (k : ℝ)) ^ 2)) * (Z.mult ρ : ℝ) :=
        Finset.sum_le_sum hpoint
      _ = (3 / (1 + (s - (k : ℝ)) ^ 2)) *
          ∑ ρ ∈ E with κ ρ = k, (Z.mult ρ : ℝ) := by rw [Finset.mul_sum]
      _ ≤ (3 / (1 + (s - (k : ℝ)) ^ 2)) * (A * Real.log (|(k : ℝ)| + 3)) :=
        mul_le_mul_of_nonneg_left hwin (by positivity)
      _ = _ := by ring
  calc
    _ ≤ ∑ k ∈ E.image κ,
        3 * A * (Real.log (|(k : ℝ)| + 3) / (1 + (s - (k : ℝ)) ^ 2)) :=
      Finset.sum_le_sum (fun k hk => hfiber k)
    _ = 3 * A * ∑ k ∈ E.image κ,
        Real.log (|(k : ℝ)| + 3) / (1 + (s - (k : ℝ)) ^ 2) := by
      rw [Finset.mul_sum]
    _ ≤ 3 * A * (9 * totalWeight * Real.log (|s| + 3)) :=
      mul_le_mul_of_nonneg_left (shifted_integer_weight_finite_le s (E.image κ))
        (by positivity)
    _ = _ := by ring

/-- The actual shifted multiplicity kernel is summable and has a logarithmic bound. -/
theorem shifted_zero_kernel_summable_tsum_le (Z : ZeroConfig) {A : ℝ} (hA : 1 ≤ A)
    (hlocal : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A * Real.log (|t| + 3)) (s : ℝ) :
    Summable (fun ρ : Z.carrier =>
      (Z.mult ρ : ℝ) / (1 + (s - (gammaOf ρ).re) ^ 2)) ∧
    (∑' ρ : Z.carrier, (Z.mult ρ : ℝ) / (1 + (s - (gammaOf ρ).re) ^ 2)) ≤
      27 * A * totalWeight * Real.log (|s| + 3) := by
  have hnonneg (ρ : Z.carrier) :
      0 ≤ (Z.mult ρ : ℝ) / (1 + (s - (gammaOf ρ).re) ^ 2) := by positivity
  have hfinite := shifted_zero_kernel_finite_le Z hA hlocal s
  have hsummable := summable_of_sum_le hnonneg hfinite
  exact ⟨hsummable, hsummable.tsum_le_of_sum_le hfinite⟩

#print axioms shifted_zero_kernel_summable_tsum_le

end Zeta23.WeilEF
