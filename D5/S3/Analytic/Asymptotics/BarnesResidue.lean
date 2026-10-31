/- GID: D5/S3/Analytic/Asymptotics/BarnesResidue
   generality: G
   mirror-B: D5/B/S3/Analytic/Asymptotics/BarnesResidue
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A contour shift across one pole preserves the dy residue normalization. -/

/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the repository root LICENSE.
Authors: Bastiaan J Braams
SPDX-License-Identifier: Apache-2.0

Adapted source port, 2026-10-31, from bjbraams/lean-DLMF revision
560b9475f35bbc6e4f5296631298859825091f7f. Imports, namespace and visibility
are adapted for this repository. The reciprocal primitive retains its TauCeti
Perron.Basic provenance; the immutable source chain and complete-license and
NOTICE assessment are in Library/Asymptotics/braams2026barnesmittagport.md.
Retire each port when this repository's pinned Mathlib supplies an equivalent
declaration and replace its actual consumers with direct Mathlib calls.
-/

import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

noncomputable section
open Complex MeasureTheory Set Filter Real intervalIntegral
open scoped Topology Interval
namespace D5.S3.Analytic.Asymptotics.BarnesResidue

/-- A primitive of `t ↦ (c + it)⁻¹` on `ℝ` for `c ≠ 0`. -/
private theorem barnesRes_hasDerivAt_primitive {c : ℝ} (hc : c ≠ 0) (t : ℝ) :
    HasDerivAt
      (fun u : ℝ => (Real.arctan (u / c) : ℂ) - I / 2 * (Real.log (c ^ 2 + u ^ 2) : ℂ))
      (((c : ℂ) + t * I)⁻¹) t := by
  have hpos : (0 : ℝ) < c ^ 2 + t ^ 2 := by positivity
  have harctan : HasDerivAt (fun u : ℝ => Real.arctan (u / c)) (c / (c ^ 2 + t ^ 2)) t := by
    have h := ((hasDerivAt_id t).div_const c).arctan
    simp only [id_eq] at h
    convert h using 1
    field_simp
  have hlog : HasDerivAt (fun u : ℝ => Real.log (c ^ 2 + u ^ 2)) (2 * t / (c ^ 2 + t ^ 2)) t := by
    have hsq : HasDerivAt (fun u : ℝ => c ^ 2 + u ^ 2) (2 * t) t :=
      ((hasDerivAt_pow 2 t).const_add (c ^ 2)).congr_deriv (by norm_num)
    exact hsq.log hpos.ne'
  have h := harctan.ofReal_comp.sub (hlog.ofReal_comp.const_mul (I / 2))
  refine h.congr_deriv ?_
  have hposC : ((c : ℂ) ^ 2 + (t : ℂ) ^ 2) ≠ 0 := by
    exact_mod_cast (by exact_mod_cast hpos.ne' : ((c ^ 2 + t ^ 2 : ℝ) : ℂ) ≠ 0)
  refine eq_inv_of_mul_eq_one_left ?_
  push_cast
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring

/-- `t ↦ (c + it)⁻¹` is continuous for `c ≠ 0`. -/
private theorem barnesRes_continuous_recip {c : ℝ} (hc : c ≠ 0) :
    Continuous fun t : ℝ => ((c : ℂ) + t * I)⁻¹ :=
  Continuous.inv₀ (by fun_prop) fun t h => hc (by simpa using congrArg re h)

/-- `∫_{-T}^{T} (c + it)⁻¹ dt = 2 arctan (T / c)` for `c ≠ 0`. -/
private theorem barnesRes_integral_recip {c : ℝ} (hc : c ≠ 0) (T : ℝ) :
    ∫ t in -T..T, ((c : ℂ) + t * I)⁻¹ = 2 * (Real.arctan (T / c) : ℂ) := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u _ => barnesRes_hasDerivAt_primitive hc u)
    ((barnesRes_continuous_recip hc).intervalIntegrable _ _), neg_div, Real.arctan_neg, neg_sq]
  push_cast; ring

/-- `∫_{-T}^{T} (c + it)⁻¹ dt → π sign c` as `T → ∞`. -/
private theorem barnesRes_tendsto_integral_recip {c : ℝ} (hc : c ≠ 0) :
    Tendsto (fun T : ℝ => ∫ t in -T..T, ((c : ℂ) + t * I)⁻¹) atTop
      (𝓝 (if 0 < c then (π : ℂ) else -π)) := by
  simp_rw [barnesRes_integral_recip hc]
  have key : Tendsto (fun T : ℝ => Real.arctan (T / c)) atTop
      (𝓝 (if 0 < c then π / 2 else -(π / 2))) := by
    split_ifs with h
    · exact (tendsto_nhds_of_tendsto_nhdsWithin Real.tendsto_arctan_atTop).comp
        (tendsto_id.atTop_div_const h)
    · have hneg : c < 0 := lt_of_le_of_ne (not_lt.mp h) hc
      exact (tendsto_nhds_of_tendsto_nhdsWithin Real.tendsto_arctan_atBot).comp
        (tendsto_id.atTop_div_const_of_neg hneg)
  have := ((continuous_ofReal.tendsto _).comp key).const_mul (2 : ℂ)
  have hv : (if 0 < c then (π : ℂ) else -π) =
      2 * ((if 0 < c then π / 2 else -(π / 2) : ℝ) : ℂ) := by
    split_ifs <;> push_cast <;> ring
  rw [hv]
  exact this

/-- The bound `‖∫_{c₁}^{c₂} (x + iy - p)⁻¹ dx‖ ≤ (c₂ - c₁) / |y - Im p|`. -/
private theorem barnesRes_norm_horizontal_recip_le {c₁ c₂ : ℝ} (h : c₁ ≤ c₂) (p : ℂ) {y : ℝ}
    (hy : y ≠ p.im) :
    ‖∫ x in c₁..c₂, ((x : ℂ) + y * I - p)⁻¹‖ ≤ (c₂ - c₁) * |y - p.im|⁻¹ := by
  have hb : ∀ x : ℝ, ‖((x : ℂ) + y * I - p)⁻¹‖ ≤ |y - p.im|⁻¹ := by
    intro x
    rw [norm_inv]
    have hpos : 0 < |y - p.im| := abs_pos.mpr (sub_ne_zero.mpr hy)
    refine inv_anti₀ hpos ?_
    have := abs_im_le_norm ((x : ℂ) + y * I - p)
    simpa using this
  calc ‖∫ x in c₁..c₂, ((x : ℂ) + y * I - p)⁻¹‖ ≤ |y - p.im|⁻¹ * |c₂ - c₁| :=
        intervalIntegral.norm_integral_le_of_norm_le_const (fun x _ => hb x)
    _ = (c₂ - c₁) * |y - p.im|⁻¹ := by
        rw [abs_of_nonneg (sub_nonneg.mpr h : (0:ℝ) ≤ c₂ - c₁)]; ring

/-- **Shifting a vertical line of integration past a simple pole.** Let `φ` be holomorphic on the
closed strip `c₁ ≤ Re s ≤ c₂`, `c₁ < Re p < c₂`, and `f s = φ s / (s - p)`. If `f` is integrable
on both boundary lines and its integrals over horizontal cross-sections tend to `0` at `±i∞`, then
`∫ f(c₂+iy) dy - ∫ f(c₁+iy) dy = 2π φ(p)`. -/
theorem barnesRes_vertical_shift {φ : ℂ → ℂ} {c₁ c₂ : ℝ} {p : ℂ} (h₁ : c₁ < p.re)
    (h₂ : p.re < c₂) (hφ : DifferentiableOn ℂ φ (re ⁻¹' Icc c₁ c₂))
    (hi₁ : Integrable fun y : ℝ => φ (c₁ + y * I) / (c₁ + y * I - p))
    (hi₂ : Integrable fun y : ℝ => φ (c₂ + y * I) / (c₂ + y * I - p))
    (htop : Tendsto (fun T : ℝ => ∫ x in c₁..c₂, φ (x + T * I) / (x + T * I - p)) atTop (𝓝 0))
    (hbot : Tendsto (fun T : ℝ => ∫ x in c₁..c₂, φ (x + T * I) / (x + T * I - p)) atBot (𝓝 0)) :
    (∫ y : ℝ, φ (c₂ + y * I) / (c₂ + y * I - p)) - ∫ y : ℝ, φ (c₁ + y * I) / (c₁ + y * I - p) =
      2 * π * φ p := by
  set S : Set ℂ := re ⁻¹' Icc c₁ c₂ with hS
  set f : ℂ → ℂ := fun s => φ s / (s - p) with hf
  set g : ℂ → ℂ := dslope φ p with hg
  set β : ℝ := p.im with hβ
  have hc : c₁ ≤ c₂ := by linarith
  have hSp : S ∈ 𝓝 p := by
    have : re ⁻¹' Ioo c₁ c₂ ⊆ S := preimage_mono Ioo_subset_Icc_self
    exact Filter.mem_of_superset ((isOpen_Ioo.preimage continuous_re).mem_nhds ⟨h₁, h₂⟩) this
  have hgd : DifferentiableOn ℂ g S := (differentiableOn_dslope hSp).mpr hφ
  have hgc : ContinuousOn g S := hgd.continuousOn
  -- decomposition off the pole
  have hdec : ∀ s : ℂ, s ≠ p → f s = φ p * (s - p)⁻¹ + g s := by
    intro s hs
    have h := sub_smul_dslope φ p s
    rw [smul_eq_mul] at h
    have hs' : s - p ≠ 0 := sub_ne_zero.mpr hs
    have h2 : φ s = φ p + (s - p) * g s := by rw [hg]; linear_combination -h
    simp only [hf]
    rw [h2]
    field_simp
  -- continuity of `g` along the four sides
  have hgh' : ∀ y : ℝ, IntervalIntegrable (fun x : ℝ => g (x + y * I)) volume c₁ c₂ := by
    intro y
    refine ContinuousOn.intervalIntegrable (hgc.comp
      (by fun_prop : Continuous fun x : ℝ => (x : ℂ) + y * I).continuousOn fun x hx => ?_)
    rw [uIcc_of_le hc] at hx
    simpa [hS] using hx
  have hgv : ∀ c : ℝ, c ∈ Icc c₁ c₂ → Continuous fun y : ℝ => g (c + y * I) := by
    intro c hcI
    exact hgc.comp_continuous (by fun_prop) fun y => by simpa [hS] using hcI
  -- the identity at height `T`
  have hTid : ∀ T : ℝ, 0 < T →
      I * ((∫ y in β - T..β + T, f (c₂ + y * I)) - ∫ y in β - T..β + T, f (c₁ + y * I)) =
        φ p * ((∫ x in c₁..c₂, ((x : ℂ) + (β - T : ℝ) * I - p)⁻¹) -
            (∫ x in c₁..c₂, ((x : ℂ) + (β + T : ℝ) * I - p)⁻¹) +
            I * ((∫ y in β - T..β + T, ((c₂ : ℂ) + y * I - p)⁻¹) -
              ∫ y in β - T..β + T, ((c₁ : ℂ) + y * I - p)⁻¹)) -
          ((∫ x in c₁..c₂, f (x + (β - T : ℝ) * I)) - ∫ x in c₁..c₂, f (x + (β + T : ℝ) * I)) := by
    intro T hT0
    have hrect := integral_boundary_rect_eq_zero_of_differentiableOn g
      ((c₁ : ℂ) + (β - T : ℝ) * I) ((c₂ : ℂ) + (β + T : ℝ) * I) (by
        refine hgd.mono fun s hs => ?_
        simp only [mem_reProdIm, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im,
          mul_one, sub_self, add_zero] at hs
        simpa [hS, uIcc_of_le hc] using hs.1)
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      add_zero, add_im, mul_im, zero_add, smul_eq_mul] at hrect
    -- pointwise decompositions on the four sides
    have hne_h : ∀ (x : ℝ) (y : ℝ), y ≠ β → (x : ℂ) + y * I ≠ p := by
      intro x y hy h; apply hy; have := congrArg im h; simpa [hβ] using this
    have hne_v : ∀ (c : ℝ) (y : ℝ), c ≠ p.re → (c : ℂ) + y * I ≠ p := by
      intro c y hc' h; apply hc'; have := congrArg re h; simpa using this
    have hinvh : ∀ y : ℝ, y ≠ β → Continuous fun x : ℝ => ((x : ℂ) + y * I - p)⁻¹ :=
      fun y hy => Continuous.inv₀ (by fun_prop) fun x => sub_ne_zero.mpr (hne_h x y hy)
    have hinvv : ∀ c : ℝ, c ≠ p.re → Continuous fun y : ℝ => ((c : ℂ) + y * I - p)⁻¹ :=
      fun c hc' => Continuous.inv₀ (by fun_prop) fun y => sub_ne_zero.mpr (hne_v c y hc')
    have hyb1 : β - T ≠ β := by linarith
    have hyb2 : β + T ≠ β := by linarith
    have hH : ∀ y : ℝ, y ≠ β → ∫ x in c₁..c₂, f (x + y * I) =
        φ p * (∫ x in c₁..c₂, ((x : ℂ) + y * I - p)⁻¹) + ∫ x in c₁..c₂, g (x + y * I) := by
      intro y hy
      rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add
        (((hinvh y hy).intervalIntegrable _ _).const_mul _) (hgh' y)]
      exact intervalIntegral.integral_congr fun x _ => hdec _ (hne_h x y hy)
    have hV : ∀ c : ℝ, c ∈ Icc c₁ c₂ → c ≠ p.re → ∫ y in β - T..β + T, f (c + y * I) =
        φ p * (∫ y in β - T..β + T, ((c : ℂ) + y * I - p)⁻¹) +
          ∫ y in β - T..β + T, g (c + y * I) := by
      intro c hcI hc'
      rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add
        (((hinvv c hc').intervalIntegrable _ _).const_mul _)
        ((hgv c hcI).intervalIntegrable _ _)]
      exact intervalIntegral.integral_congr fun y _ => hdec _ (hne_v c y hc')
    rw [hH _ hyb1, hH _ hyb2, hV c₂ ⟨hc, le_rfl⟩ h₂.ne', hV c₁ ⟨le_rfl, hc⟩ h₁.ne]
    linear_combination hrect
  -- limits
  have hTt : Tendsto (fun T : ℝ => β - T) atTop atBot := tendsto_atBot_add_const_left _ _
    (tendsto_neg_atTop_atBot)
  have hTt' : Tendsto (fun T : ℝ => β + T) atTop atTop := tendsto_atTop_add_const_left _ _
    tendsto_id
  have hvert : ∀ c : ℝ, Integrable (fun y : ℝ => f (c + y * I)) →
      Tendsto (fun T : ℝ => ∫ y in β - T..β + T, f (c + y * I)) atTop
        (𝓝 (∫ y : ℝ, f (c + y * I))) :=
    fun c hi => intervalIntegral_tendsto_integral hi hTt hTt'
  have hLHS := ((hvert c₂ hi₂).sub (hvert c₁ hi₁)).const_mul I
  -- the reciprocal-kernel rectangle integral
  have hshift : ∀ (c : ℝ) (T : ℝ), ∫ y in β - T..β + T, ((c : ℂ) + y * I - p)⁻¹ =
      ∫ t in -T..T, (((c - p.re : ℝ) : ℂ) + t * I)⁻¹ := by
    intro c T
    have := intervalIntegral.integral_comp_add_right
      (fun y : ℝ => ((c : ℂ) + y * I - p)⁻¹) β (a := -T) (b := T)
    rw [show -T + β = β - T by ring, show T + β = β + T by ring] at this
    rw [← this]
    refine intervalIntegral.integral_congr fun t _ => ?_
    congr 1
    apply Complex.ext <;> simp [hβ]
  have hinv2 := barnesRes_tendsto_integral_recip (c := c₂ - p.re) (by linarith)
  have hinv1 := barnesRes_tendsto_integral_recip (c := c₁ - p.re) (by linarith)
  simp only [show (0:ℝ) < c₂ - p.re by linarith, ↓reduceIte] at hinv2
  simp only [show ¬ (0:ℝ) < c₁ - p.re by linarith, ↓reduceIte] at hinv1
  have hhinv : ∀ (s : ℝ → ℝ), Tendsto s atTop (atBot ⊔ atTop) → (∀ᶠ T in atTop, s T ≠ β) →
      Tendsto (fun T : ℝ => |s T - β|⁻¹) atTop (𝓝 0) → Tendsto (fun T : ℝ =>
        ∫ x in c₁..c₂, ((x : ℂ) + (s T : ℝ) * I - p)⁻¹) atTop (𝓝 0) := by
    intro s _ hs hlim
    refine squeeze_zero_norm' ?_ (by simpa using hlim.const_mul (c₂ - c₁))
    filter_upwards [hs] with T hT
    exact barnesRes_norm_horizontal_recip_le hc p hT
  have hb1 : Tendsto (fun T : ℝ => ∫ x in c₁..c₂, ((x : ℂ) + (β - T : ℝ) * I - p)⁻¹) atTop
      (𝓝 0) := by
    refine hhinv (fun T => β - T) (hTt.mono_right le_sup_left) ?_ ?_
    · filter_upwards [eventually_gt_atTop 0] with T hT; linarith
    · have : (fun T : ℝ => |β - T - β|⁻¹) =ᶠ[atTop] fun T => T⁻¹ := by
        filter_upwards [eventually_gt_atTop 0] with T hT
        rw [show β - T - β = -T by ring, abs_neg, abs_of_pos hT]
      exact (tendsto_inv_atTop_zero).congr' this.symm
  have hb2 : Tendsto (fun T : ℝ => ∫ x in c₁..c₂, ((x : ℂ) + (β + T : ℝ) * I - p)⁻¹) atTop
      (𝓝 0) := by
    refine hhinv (fun T => β + T) (hTt'.mono_right le_sup_right) ?_ ?_
    · filter_upwards [eventually_gt_atTop 0] with T hT; linarith
    · have : (fun T : ℝ => |β + T - β|⁻¹) =ᶠ[atTop] fun T => T⁻¹ := by
        filter_upwards [eventually_gt_atTop 0] with T hT
        rw [show β + T - β = T by ring, abs_of_pos hT]
      exact (tendsto_inv_atTop_zero).congr' this.symm
  have hRHS := ((((hb1.sub hb2).add (((hinv2.congr fun T => (hshift c₂ T).symm).sub
      (hinv1.congr fun T => (hshift c₁ T).symm)).const_mul I)).const_mul (φ p)).sub
      ((hbot.comp hTt).sub (htop.comp hTt')))
  have hRHS' := hRHS.congr' (by
    filter_upwards [eventually_gt_atTop 0] with T hT
    exact (hTid T hT).symm)
  have huniq := tendsto_nhds_unique hLHS hRHS'
  have hI : (I : ℂ) ≠ 0 := I_ne_zero
  have : I * ((∫ y : ℝ, f (c₂ + y * I)) - ∫ y : ℝ, f (c₁ + y * I)) = I * (2 * π * φ p) := by
    rw [huniq]; ring
  exact mul_left_cancel₀ hI this


end D5.S3.Analytic.Asymptotics.BarnesResidue
