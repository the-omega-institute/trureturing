/- GID: D5/S3/Arith/ModularForms/RademacherLimitAnalysis
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Holomorphy and cusp decay for the normalized rectangular Rademacher limit. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.Arith.ModularForms.RademacherRectangularConvergence
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.NumberTheory.ModularForms.QExpansion

/-!
# Holomorphy and the principal part of the rectangular limit

The finite vacuum cutoffs are holomorphic. Their locally uniform limit has the
same principal part at infinity as the polar seed. The cusp estimate uses the
quadratic remainder and the positive-power linear series separately.
-/

open Filter UpperHalfPlane
open scoped BigOperators Manifold Topology UpperHalfPlane

namespace D5.S3.Arith.ModularForms.RademacherLimitAnalysis

open RademacherVacuum hiding PrimitiveRow remainderLimit
open RademacherRectangularConvergence RademacherLinearTailConvergence

open private im_mul_le_norm_denominator norm_vacuumArgument_le
  strip_denominator_sq_bound summable_remainderWeight
  from D5.S3.Arith.ModularForms.RademacherVacuum
open private modulusMajorant summable_modulusMajorant norm_linearQTailCoefficient_le
  qRadius geometricMass hasSum_qRadius_pow_succ
  from D5.S3.Arith.ModularForms.RademacherLinearTailConvergence

set_option autoImplicit false

noncomputable section

local notation "𝕢" => Function.Periodic.qParam 1

/-- Each literal finite rectangular cutoff is holomorphic on the upper half-plane. -/
theorem mdifferentiable_rademacherCutoff (N : ℕ) : MDiff (rademacherCutoff N) := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  let U : Set ℂ := {z | 0 < z.im}
  let polar (z : ℂ) := Complex.exp (-((2 * Real.pi : ℝ) : ℂ) * Complex.I * z)
  let denom (p : ℤ × ℤ) (z : ℂ) := (p.1 : ℂ) * z + (p.2 : ℂ)
  let arg (p : ℤ × ℤ) (z : ℂ) :=
    ((2 * Real.pi : ℝ) : ℂ) * Complex.I / ((p.1 : ℂ) * denom p z)
  let term (p : ℤ × ℤ) (z : ℂ) :=
    vacuumPhase p.1 p.2 * (Complex.exp (arg p z) - 1)
  have hpolar : DifferentiableOn ℂ polar U := by
    dsimp only [polar]
    exact ((differentiableOn_const (-((2 * Real.pi : ℝ) : ℂ) * Complex.I)).mul
      differentiableOn_id).cexp
  have hterm (p : ℤ × ℤ) (hp : p ∈ cutoffPairs N) : DifferentiableOn ℂ (term p) U := by
    have hc : 0 < p.1 := ((mem_cutoffPairs (c := p.1) (d := p.2)).mp hp).1
    have hcR : (0 : ℝ) < (p.1 : ℝ) := by exact_mod_cast hc
    have hcC : (p.1 : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
    have hden (z : ℂ) (hz : z ∈ U) : denom p z ≠ 0 := by
      have hz' : 0 < z.im := hz
      have hnorm : (p.1 : ℝ) * z.im ≤ ‖denom p z‖ :=
        im_mul_le_norm_denominator p.1 p.2 ⟨z, hz'⟩
      exact norm_pos_iff.mp ((mul_pos hcR hz').trans_le hnorm)
    have hd : DifferentiableOn ℂ (denom p) U :=
      ((differentiableOn_const (p.1 : ℂ)).mul differentiableOn_id).add
        (differentiableOn_const (p.2 : ℂ))
    have ha : DifferentiableOn ℂ (arg p) U :=
      (differentiableOn_const (((2 * Real.pi : ℝ) : ℂ) * Complex.I)).div
        ((differentiableOn_const (p.1 : ℂ)).mul hd)
        (fun z hz => mul_ne_zero hcC (hden z hz))
    exact (differentiableOn_const (vacuumPhase p.1 p.2)).mul
      (ha.cexp.sub (differentiableOn_const (1 : ℂ)))
  have hsum : DifferentiableOn ℂ (fun z => ∑ p ∈ cutoffPairs N, term p z) U :=
    DifferentiableOn.fun_sum hterm
  refine (hpolar.add hsum).congr ?_
  intro z hz
  simp only [Function.comp_apply, ofComplex_apply_of_im_pos hz]
  rfl

/-- The limit defined by the two convergent Rademacher series is holomorphic. -/
theorem mdifferentiable_rademacherLimit : MDiff rademacherLimit := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  have hcont : ContinuousOn ofComplex {z : ℂ | 0 < z.im} := by
    intro z hz
    have hz' : 0 < z.im := hz
    exact (mdifferentiableAt_ofComplex hz').continuousAt.continuousWithinAt
  have hlocal :=
    tendstoLocallyUniformly_rademacherCutoff_sub_twelve.tendstoLocallyUniformlyOn.comp
      ofComplex (Set.mapsTo_univ _ _) hcont
  refine hlocal.differentiableOn (Eventually.of_forall fun N => ?_) isOpen_upperHalfPlaneSet
  have hN := UpperHalfPlane.mdifferentiable_iff.mp (mdifferentiable_rademacherCutoff N)
  exact hN.sub (differentiableOn_const (12 : ℂ))

/-- The quadratic majorant is summable on the whole strip, with the same
constant at every height at least one. -/
theorem quadraticRemainder_strip_majorant :
    ∃ C : ℝ, 0 < C ∧ Summable (fun p : ℤ × ℤ => C * remainderWeight p) ∧
      ∀ τ ∈ verticalStrip 1 1, ∀ c d : ℤ, 0 < c →
        ‖quadraticRemainder c d τ‖ ≤ C * remainderWeight (c, d) := by
  let r := EisensteinSeries.r ⟨⟨1, 1⟩, (zero_lt_one : (0 : ℝ) < 1)⟩
  have hr : 0 < r := EisensteinSeries.r_pos _
  let B := (2 * Real.pi) ^ 2 * Real.exp (2 * Real.pi / 1)
  have hB : 0 < B := by
    dsimp only [B]
    positivity
  refine ⟨B / r ^ 2, div_pos hB (pow_pos hr _), summable_remainderWeight.mul_left _, ?_⟩
  intro τ hτ c d hc
  have hcR : 0 < (c : ℝ) := by exact_mod_cast hc
  have him := ((mem_verticalStrip_iff 1 1 τ).mp hτ).2
  have hden : r ^ 2 * max 1 ((d : ℝ) ^ 2) ≤ ‖denominator c d τ‖ ^ 2 :=
    strip_denominator_sq_bound zero_lt_one hτ hc d
  have hd : (0 : ℝ) < max 1 ((d : ℝ) ^ 2) := zero_lt_one.trans_le (le_max_left _ _)
  have hpositive : 0 < (c : ℝ) ^ 2 * (r ^ 2 * max 1 ((d : ℝ) ^ 2)) :=
    mul_pos (pow_pos hcR _) (mul_pos (pow_pos hr _) hd)
  calc
    ‖quadraticRemainder c d τ‖ ≤ B / ((c : ℝ) ^ 2 * ‖denominator c d τ‖ ^ 2) :=
      norm_quadraticRemainder_le hc d τ zero_lt_one him
    _ ≤ B / ((c : ℝ) ^ 2 * (r ^ 2 * max 1 ((d : ℝ) ^ 2))) :=
      div_le_div_of_nonneg_left hB.le hpositive
        (mul_le_mul_of_nonneg_left hden (sq_nonneg _))
    _ = B / r ^ 2 * remainderWeight (c, d) := by
      simp only [remainderWeight, div_eq_mul_inv, mul_inv_rev, one_mul]
      ring

private theorem tendsto_quadraticRemainder {c : ℤ} (hc : 0 < c) (d : ℤ) :
    Tendsto (quadraticRemainder c d) atImInfty (𝓝 0) := by
  have him : Tendsto im atImInfty atTop := tendsto_comap
  have hinv : Tendsto (fun τ : ℍ => τ.im⁻¹) atImInfty (𝓝 0) :=
    tendsto_inv_atTop_zero.comp him
  have hbound : Tendsto (fun τ : ℍ => (2 * Real.pi) / τ.im) atImInfty (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using hinv.const_mul (2 * Real.pi)
  -- The denominator has imaginary part c * τ.im, which bounds its norm from below.
  have harg : Tendsto (vacuumArgument c d) atImInfty (𝓝 0) :=
    squeeze_zero_norm (fun τ => norm_vacuumArgument_le hc d τ τ.im_pos le_rfl) hbound
  have hexp := Complex.continuous_exp.continuousAt.tendsto.comp harg
  change Tendsto (fun τ => quadraticRemainder c d τ) atImInfty (𝓝 0)
  simpa only [quadraticRemainder, Complex.exp_zero, sub_self, sub_zero, mul_zero,
    Function.comp_apply] using
    ((hexp.sub (tendsto_const_nhds (x := (1 : ℂ)))).sub harg).const_mul (vacuumPhase c d)

private theorem remainderLimit_T_zpow (n : ℤ) (τ : ℍ) :
    remainderLimit (ModularGroup.T ^ n • τ) = remainderLimit τ := by
  have hT (z : ℍ) : remainderLimit (ModularGroup.T • z) = remainderLimit z := by
    rw [modular_T_smul]
    exact remainderLimit_one_vadd z
  refine zpow_induction_left
    (g := ModularGroup.T) (P := fun g => remainderLimit (g • τ) = remainderLimit τ)
    (by simp) ?_ ?_ n
  · intro g hg
    rw [mul_smul, hT, hg]
  · intro g hg
    rw [mul_smul, ← hT (ModularGroup.T⁻¹ • (g • τ)), smul_inv_smul, hg]

/-- The absolutely convergent quadratic remainder vanishes at infinity.
Integer translation puts every real part in the same strip. Tannery's theorem
then bounds the complement of a finite set of rows by the summable norm tail. -/
theorem tendsto_remainderLimit_atImInfty : Tendsto remainderLimit atImInfty (𝓝 0) := by
  let reduce (τ : ℍ) := ModularGroup.T ^ (-⌊τ.re⌋) • τ
  have him (τ : ℍ) : (reduce τ).im = τ.im := by
    simp only [reduce, modular_T_zpow_smul, vadd_im]
  have hreduce : Tendsto reduce atImInfty atImInfty := by
    rw [atImInfty, tendsto_comap_iff]
    change Tendsto (fun τ => (reduce τ).im) (comap im atTop) atTop
    simpa only [him] using (tendsto_comap : Tendsto im (comap im atTop) atTop)
  obtain ⟨C, _, hsum, hbound⟩ := quadraticRemainder_strip_majorant
  have hdom : ∀ᶠ τ in atImInfty, ∀ p : PrimitiveRow,
      ‖quadraticRemainder p.val.1 p.val.2 (reduce τ)‖ ≤ C * remainderWeight p.val := by
    have hheight : ∀ᶠ τ : ℍ in atImInfty, 1 ≤ τ.im :=
      (atImInfty_mem _).mpr ⟨1, fun _ h => h⟩
    filter_upwards [hheight] with τ hτ p
    have hre : (reduce τ).re = τ.re - (⌊τ.re⌋ : ℝ) := by
      simp only [reduce, modular_T_zpow_smul, vadd_re, Int.cast_neg]
      ring
    have hstrip : reduce τ ∈ verticalStrip 1 1 := by
      refine (mem_verticalStrip_iff 1 1 _).mpr ⟨?_, (him τ).symm ▸ hτ⟩
      rw [hre, abs_of_nonneg (sub_nonneg.mpr (Int.floor_le τ.re))]
      exact (sub_lt_iff_lt_add.mpr (by
        simpa only [add_comm] using Int.lt_floor_add_one τ.re)).le
    exact hbound (reduce τ) hstrip p.val.1 p.val.2 p.property.1
  have h : Tendsto (fun τ => remainderLimit (reduce τ)) atImInfty (𝓝 0) := by
    unfold remainderLimit
    simpa only [tsum_zero] using
      tendsto_tsum_of_dominated_convergence
        (f := fun τ (p : PrimitiveRow) => quadraticRemainder p.val.1 p.val.2 (reduce τ))
        (g := fun _ : PrimitiveRow => (0 : ℂ))
        (hsum.subtype (fun p : ℤ × ℤ => 0 < p.1 ∧ Int.gcd p.1 p.2 = 1))
        (fun p => (tendsto_quadraticRemainder p.property.1 p.val.2).comp hreduce) hdom
  exact h.congr (fun τ => remainderLimit_T_zpow (-⌊τ.re⌋) τ)

private theorem norm_qParam_eq_qRadius (τ : ℍ) : ‖𝕢 (τ : ℂ)‖ = qRadius τ.im := by
  rw [Function.Periodic.norm_qParam, div_one, coe_im, qRadius]

/-- The absolute geometric majorant of the positive-power linear series
vanishes as the q-radius goes to zero. -/
theorem tendsto_linearPrincipalValueQTailLimit_atImInfty :
    Tendsto linearPrincipalValueQTailLimit atImInfty (𝓝 0) := by
  let M : ℝ := ∑' c : ℕ, modulusMajorant c
  have hcoeff (n : ℕ) : ‖∑' c : ℕ, linearQTailCoefficient c (n + 1)‖ ≤ M :=
    tsum_of_norm_bounded summable_modulusMajorant.hasSum
      (fun c => norm_linearQTailCoefficient_le c (n + 1))
  have hrho : Tendsto (fun τ : ℍ => qRadius τ.im) atImInfty (𝓝 0) := by
    simpa only [norm_qParam_eq_qRadius, norm_zero] using
      (qParam_tendsto_atImInfty (h := 1) zero_lt_one).norm
  have hden : Tendsto (fun τ : ℍ => 1 - qRadius τ.im) atImInfty (𝓝 1) := by
    simpa only [sub_zero] using (tendsto_const_nhds (x := (1 : ℝ))).sub hrho
  have hmass : Tendsto (fun τ : ℍ => geometricMass τ.im) atImInfty (𝓝 0) := by
    have h : Tendsto (fun τ : ℍ => qRadius τ.im / (1 - qRadius τ.im))
        atImInfty (𝓝 ((0 : ℝ) / 1)) := hrho.div hden one_ne_zero
    simpa only [geometricMass, div_eq_mul_inv, zero_mul] using h
  refine squeeze_zero_norm (a := fun τ => M * geometricMass τ.im) (fun τ => ?_) ?_
  · unfold linearPrincipalValueQTailLimit
    refine tsum_of_norm_bounded ((hasSum_qRadius_pow_succ τ.im_pos).mul_left M) (fun n => ?_)
    rw [norm_mul, norm_pow, norm_qParam_eq_qRadius]
    exact mul_le_mul_of_nonneg_right (hcoeff n) (pow_nonneg (Real.exp_pos _).le _)
  · simpa only [mul_zero] using hmass.const_mul M

/-- After removing the polar seed, the independently defined rectangular limit
has zero limit at the cusp. -/
theorem tendsto_rademacherLimit_sub_pole_atImInfty :
    Tendsto (fun τ : ℍ => rademacherLimit τ - (𝕢 (τ : ℂ))⁻¹) atImInfty (𝓝 0) := by
  have h := tendsto_linearPrincipalValueQTailLimit_atImInfty.add tendsto_remainderLimit_atImInfty
  have heq (τ : ℍ) : linearPrincipalValueQTailLimit τ + remainderLimit τ =
      rademacherLimit τ - (𝕢 (τ : ℂ))⁻¹ := by
    unfold rademacherLimit
    abel
  simpa only [zero_add] using h.congr heq

end

end D5.S3.Arith.ModularForms.RademacherLimitAnalysis
