/- GID: D5/S3/Arith/Robin/ActualContinuousFactorialCompensation/SharpTail
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/ActualContinuousFactorialCompensation/SharpTail
   mirror-E: none(waiver:analytic-inequality)
   anchors: []
   utility: none
   digest: The literal factorial compensation has a real-uniform sharp tail and its exact limit. -/

import D5.S3.Arith.Robin.ActualContinuousFactorialCompensation.SharpTail.Cancellation
import D5.S3.Arith.Robin.ActualContinuousFactorialCompensation.SharpTail.Factorial

/-! The harmonic, factorial and signed-tail estimates cancel the entire floor
phase and identify the exact limit of the existing arithmetic G. -/

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set MeasureTheory Filter
open scoped BigOperators Topology

namespace D5.S3.Arith.Robin.ActualContinuousFactorialCompensation

private lemma gamma_nonneg : 0 ≤ gamma := by
  have := Real.one_half_lt_eulerMascheroniConstant
  dsimp [gamma]
  linarith

lemma G_centered_decomposition {x : ℝ} (hx : 1 ≤ x) :
    G x - ell = (1 + gamma + Real.log x) * harmonicPrimitive x -
      (eta x - ((1 / 2 - Int.fract x) * Real.log x + L / 2)) +
      2 * x * T_epsilon x := by
  rw [G_tail_decomposition hx]
  dsimp [ell, harmonicPrimitive, h1]
  ring

/-- The sharp remainder holds for every real x at least one, with literal floor phase. -/
theorem G_sharp_tail_bound {x : ℝ} (hx : 1 ≤ x) :
    |G x - ell| ≤ (4 * gamma + 24) * (1 + Real.log x) / x := by
  have hx0 : 0 < x := by linarith
  have hl : 0 ≤ Real.log x := Real.log_nonneg hx
  have hc : 0 ≤ 1 + gamma + Real.log x := by linarith [gamma_nonneg]
  have hF := harmonicPrimitive_bound hx
  have he := eta_phase_bound hx
  have hT := T_epsilon_quadratic_bound hx
  rw [G_centered_decomposition hx]
  calc
    _ ≤ |(1 + gamma + Real.log x) * harmonicPrimitive x -
        (eta x - ((1 / 2 - Int.fract x) * Real.log x + L / 2))| +
        |2 * x * T_epsilon x| := abs_add_le _ _
    _ ≤ (|(1 + gamma + Real.log x) * harmonicPrimitive x| +
        |eta x - ((1 / 2 - Int.fract x) * Real.log x + L / 2)|) +
        |2 * x * T_epsilon x| := add_le_add (abs_sub _ _) (le_refl _)
    _ ≤ ((1 + gamma + Real.log x) * (4 / x) + 4 / x) +
        (2 * x) * (8 / x ^ 2) := by
      rw [abs_mul, abs_of_nonneg hc, abs_mul, abs_of_pos (by positivity : 0 < 2 * x)]
      gcongr
    _ = (4 * gamma + 24 + 4 * Real.log x) / x := by field_simp; ring
    _ ≤ (4 * gamma + 24) * (1 + Real.log x) / x := by
      apply (div_le_div_iff_of_pos_right hx0).mpr
      nlinarith [mul_nonneg gamma_nonneg hl]

theorem exists_G_sharp_tail_constant :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 1 ≤ x → |G x - (alpha + h1 / 2)| ≤
      C * (1 + Real.log x) / x := by
  refine ⟨4 * gamma + 24, by linarith [gamma_nonneg], ?_⟩
  intro x hx
  exact G_sharp_tail_bound hx

/-- The limit is exact and is taken over the full real half-line. -/
theorem tendsto_G_ell : Tendsto G atTop (𝓝 (alpha + h1 / 2)) := by
  obtain ⟨C, _, hC⟩ := exists_G_sharp_tail_constant
  have hz : Tendsto (fun x : ℝ => (1 + Real.log x) / x) atTop (𝓝 0) := by
    have hlog : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
      simpa only [id_eq] using Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
    have hi : Tendsto (fun x : ℝ => 1 / x) atTop (𝓝 0) := by
      simpa only [one_div] using (tendsto_inv_atTop_zero : Tendsto
        (fun x : ℝ => x⁻¹) atTop (𝓝 0))
    convert hi.add hlog using 1
    · ext x; ring
    · norm_num
  have hbound := hz.const_mul C
  have hc : Tendsto (fun x : ℝ => G x - ell) atTop (𝓝 0) := by
    apply squeeze_zero_norm' (a := fun x : ℝ => C * ((1 + Real.log x) / x))
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
      simpa only [Real.norm_eq_abs, mul_div_assoc, ell] using hC x hx
    · simpa only [mul_zero] using hbound
  simpa only [sub_add_cancel, zero_add, ell] using hc.add_const ell

end D5.S3.Arith.Robin.ActualContinuousFactorialCompensation
