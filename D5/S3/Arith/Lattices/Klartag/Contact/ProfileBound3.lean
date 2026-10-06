/- GID: D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound3
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/Klartag/Contact/ProfileBound3
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Contact profile counts and accumulated projection dimension. -/

/- Copyright 2026 Lean FRO, LLC. Licensed under Apache-2.0.
   Source: mlgraham/lean-eval-klartag-submission, commit
   270b3358a135f64a6688636660c07772e8db0173.
   Attribution and full license: Library/QuadraticForms/klartag2025packing.md. -/

import D5.S3.Arith.Lattices.Klartag.Contact.ProfileBound2

open D5.S3.Arith.Lattices.Klartag.Construction
open D5.S3.Arith.Lattices.Klartag.Walk

namespace D5.S3.Arith.Lattices.Klartag

open MeasureTheory
open Set
open Real
open scoped ENNReal NNReal

/-- `yOf a₀ t (subst a₀ √t y) = y`: the substitution is a right inverse of the paper's `y(r)`. -/
theorem yOf_subst {a₀ t y : ℝ} (ht : 0 < t) (hu : 0 < a₀ - Real.sqrt t * y) :
    yOf a₀ t (subst a₀ (Real.sqrt t) y) = y := by
  have hs : (0 : ℝ) < Real.sqrt t := Real.sqrt_pos.2 ht
  rw [yOf, subst_sq hu, inv_inv]
  field_simp
  ring

/-- The radius at which the profile takes the value `Φ(y)`: the paper's substitution, un-scaled by
`α` and shifted out by the cube radius `δ`. -/
noncomputable def radiusOf (a₀ α δ t y : ℝ) : ℝ := subst a₀ (Real.sqrt t) y / α + δ

theorem hasDerivAt_radiusOf {a₀ α δ t y : ℝ} (hu : 0 < a₀ - Real.sqrt t * y) :
    HasDerivAt (radiusOf a₀ α δ t) (substDeriv a₀ (Real.sqrt t) y / α) y := by
  exact ((hasDerivAt_subst hu).div_const α).add_const δ

theorem strictMonoOn_radiusOf {a₀ α δ t : ℝ} (hα : 0 < α) (ht : 0 < t) {S : Set ℝ}
    (hS : ∀ y ∈ S, 0 < a₀ - Real.sqrt t * y) : StrictMonoOn (radiusOf a₀ α δ t) S := by
  intro y hy z hz hyz
  have hs : (0 : ℝ) < Real.sqrt t := Real.sqrt_pos.2 ht
  have hsub := strictMonoOn_subst hs hS hy hz hyz
  unfold radiusOf
  have hdiv : subst a₀ (Real.sqrt t) y / α < subst a₀ (Real.sqrt t) z / α := by
    have := mul_lt_mul_of_pos_right hsub (inv_pos.2 hα)
    simpa [div_eq_mul_inv] using this
  linarith

theorem injOn_radiusOf {a₀ α δ t : ℝ} (hα : 0 < α) (ht : 0 < t) {S : Set ℝ}
    (hS : ∀ y ∈ S, 0 < a₀ - Real.sqrt t * y) : Set.InjOn (radiusOf a₀ α δ t) S :=
  (strictMonoOn_radiusOf hα ht hS).injOn

/-- **The profile at the substituted radius is `Φ`.**  Both `if`-branches take their
non-degenerate values — the radius is inside the window, and the shifted, scaled radius is
positive — and `yOf_subst` collapses the rest. -/
theorem profile_radiusOf {a₀ α W t y : ℝ} {n : ℕ} (hα : 0 < α) (ht : 0 < t)
    (hu : 0 < a₀ - Real.sqrt t * y)
    (hW : radiusOf a₀ α (Real.sqrt n / 2) t y ≤ W) :
    profile a₀ α W n t (radiusOf a₀ α (Real.sqrt n / 2) t y) = PhiC y := by
  have hshift : α * (radiusOf a₀ α (Real.sqrt n / 2) t y - Real.sqrt n / 2)
      = subst a₀ (Real.sqrt t) y := by
    rw [radiusOf]
    field_simp
    ring
  have hpos : 0 < subst a₀ (Real.sqrt t) y := subst_pos hu
  rw [profile, if_neg (not_lt.2 hW), hshift, if_neg (not_le.2 hpos), yOf_subst ht hu]

theorem integral_shell_eq {a₀ α t : ℝ} {n : ℕ} (hα : 0 < α) (ht : 0 < t) {S : Set ℝ}
    (hSm : MeasurableSet S) (hS : ∀ y ∈ S, 0 < a₀ - Real.sqrt t * y) (G : ℝ → ℝ) :
    ∫ r in radiusOf a₀ α (Real.sqrt n / 2) t '' S, G r
      = ∫ y in S, |substDeriv a₀ (Real.sqrt t) y / α| * G (radiusOf a₀ α (Real.sqrt n / 2) t y) := by
  have hderiv : ∀ y ∈ S, HasDerivWithinAt (radiusOf a₀ α (Real.sqrt n / 2) t)
      (substDeriv a₀ (Real.sqrt t) y / α) S y :=
    fun y hy => (hasDerivAt_radiusOf (hS y hy)).hasDerivWithinAt
  simpa [smul_eq_mul] using
    MeasureTheory.integral_image_eq_integral_abs_deriv_smul hSm hderiv (injOn_radiusOf hα ht hS) G

/-- **The substituted integrand, with the shift priced.**  Combining `subst_integrand` (the
Jacobian and the `r^{n−1}` factor) with `shift_constant` (the cube shift, bounded by `e^{1/2}` under
`tiling_defect`) and `rpow_neg_le_of_one_le` (normalising `a₀` away).

The right-hand side is exactly the integrand of `I₁`, `I₂` and `I₃`, times `e^{1/2}·√t/(2·αⁿ)`. -/
theorem substituted_integrand_le {a₀ α t y : ℝ} {n : ℕ} (hα : 0 < α) (ht : 0 < t) (hn : 0 < n)
    (ha₀ : 1 ≤ a₀) (hu : 0 < a₀ - Real.sqrt t * y)
    (hdef : (n : ℝ) * (α * Real.sqrt n / 2) ≤ 1 / 4)
    (hlow : (1 : ℝ) / (2 * α) ≤ subst a₀ (Real.sqrt t) y / α)
    (hpos : 0 < 1 - Real.sqrt t * y) :
    |substDeriv a₀ (Real.sqrt t) y / α| * (radiusOf a₀ α (Real.sqrt n / 2) t y) ^ (n - 1)
      ≤ Real.exp (1 / 2) / α ^ n
        * (Real.sqrt t / 2 * (1 - Real.sqrt t * y) ^ (-(((n : ℝ) + 2) / 2))) := by
  have hs0 : (0 : ℝ) ≤ Real.sqrt t := Real.sqrt_nonneg t
  have hjac : (0 : ℝ) ≤ substDeriv a₀ (Real.sqrt t) y := by
    rw [substDeriv]; positivity
  have habs : |substDeriv a₀ (Real.sqrt t) y / α| = substDeriv a₀ (Real.sqrt t) y / α := by
    rw [abs_of_nonneg (by positivity)]

  have hshift : (radiusOf a₀ α (Real.sqrt n / 2) t y) ^ (n - 1)
      ≤ Real.exp (1 / 2) * (subst a₀ (Real.sqrt t) y / α) ^ (n - 1) := by
    rw [radiusOf]
    refine le_trans (pow_add_le_exp_mul (by positivity)
      (div_pos one_pos (by linarith)) hlow (n - 1)) ?_
    refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_)
      (pow_nonneg (le_of_lt (div_pos (subst_pos hu) hα)) _)
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hcast : ((n - 1 : ℕ) : ℝ) ≤ (n : ℝ) := by
      have h1 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by push_cast [Nat.cast_sub hn]; ring
      rw [h1]; linarith
    have hsn : (0 : ℝ) ≤ Real.sqrt n := Real.sqrt_nonneg _
    have hid : ((n - 1 : ℕ) : ℝ) * (Real.sqrt n / 2) / (1 / (2 * α))
        = ((n - 1 : ℕ) : ℝ) * Real.sqrt n * α := by
      field_simp
    rw [hid]
    nlinarith [hdef, hcast, hsn, hα]

  have hsi : substDeriv a₀ (Real.sqrt t) y * (subst a₀ (Real.sqrt t) y) ^ (n - 1)
      = Real.sqrt t / 2 * (a₀ - Real.sqrt t * y) ^ (-(((n : ℝ) + 2) / 2)) := by
    have h := subst_integrand (a₀ := a₀) (s := Real.sqrt t) (y := y) hu hs0 hn
    rwa [abs_of_nonneg hjac] at h

  have hnorm : (a₀ - Real.sqrt t * y) ^ (-(((n : ℝ) + 2) / 2))
      ≤ (1 - Real.sqrt t * y) ^ (-(((n : ℝ) + 2) / 2)) :=
    rpow_neg_le_of_one_le ha₀ hpos (by positivity)
  have hαn : (0 : ℝ) < α ^ n := by positivity
  have hαn1 : (0 : ℝ) < α ^ (n - 1) := by positivity
  calc |substDeriv a₀ (Real.sqrt t) y / α| * (radiusOf a₀ α (Real.sqrt n / 2) t y) ^ (n - 1)
      = substDeriv a₀ (Real.sqrt t) y / α * (radiusOf a₀ α (Real.sqrt n / 2) t y) ^ (n - 1) := by
        rw [habs]
    _ ≤ substDeriv a₀ (Real.sqrt t) y / α
          * (Real.exp (1 / 2) * (subst a₀ (Real.sqrt t) y / α) ^ (n - 1)) := by
        exact mul_le_mul_of_nonneg_left hshift (by positivity)
    _ = Real.exp (1 / 2) / (α * α ^ (n - 1))
          * (substDeriv a₀ (Real.sqrt t) y * (subst a₀ (Real.sqrt t) y) ^ (n - 1)) := by
        rw [div_pow]
        field_simp
    _ = Real.exp (1 / 2) / (α * α ^ (n - 1))
          * (Real.sqrt t / 2 * (a₀ - Real.sqrt t * y) ^ (-(((n : ℝ) + 2) / 2))) := by rw [hsi]
    _ ≤ Real.exp (1 / 2) / (α * α ^ (n - 1))
          * (Real.sqrt t / 2 * (1 - Real.sqrt t * y) ^ (-(((n : ℝ) + 2) / 2))) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hnorm (by positivity))
          (by positivity)
    _ = Real.exp (1 / 2) / α ^ n
          * (Real.sqrt t / 2 * (1 - Real.sqrt t * y) ^ (-(((n : ℝ) + 2) / 2))) := by
        congr 2
        rw [← pow_succ']
        congr 1
        omega

theorem integral_shell_le {a₀ α W t : ℝ} {n : ℕ} (hα : 0 < α) (ht : 0 < t) (hn : 0 < n)
    (ha₀ : 1 ≤ a₀) (hdef : (n : ℝ) * (α * Real.sqrt n / 2) ≤ 1 / 4)
    {S : Set ℝ} (hSm : MeasurableSet S)
    (hS : ∀ y ∈ S, 0 < a₀ - Real.sqrt t * y)
    (hlow : ∀ y ∈ S, (1 : ℝ) / (2 * α) ≤ subst a₀ (Real.sqrt t) y / α)
    (hpos : ∀ y ∈ S, 0 < 1 - Real.sqrt t * y)
    (hW : ∀ y ∈ S, radiusOf a₀ α (Real.sqrt n / 2) t y ≤ W)
    (hint1 : IntegrableOn (fun y : ℝ => |substDeriv a₀ (Real.sqrt t) y / α|
      * ((radiusOf a₀ α (Real.sqrt n / 2) t y) ^ (n - 1)
        * profile a₀ α W n t (radiusOf a₀ α (Real.sqrt n / 2) t y))) S)
    (hint2 : IntegrableOn (fun y : ℝ => Real.exp (1 / 2) / α ^ n
      * (Real.sqrt t / 2 * (1 - Real.sqrt t * y) ^ (-(((n : ℝ) + 2) / 2))) * PhiC y) S) :
    ∫ r in radiusOf a₀ α (Real.sqrt n / 2) t '' S, r ^ (n - 1) * profile a₀ α W n t r
      ≤ ∫ y in S, Real.exp (1 / 2) / α ^ n
          * (Real.sqrt t / 2 * (1 - Real.sqrt t * y) ^ (-(((n : ℝ) + 2) / 2))) * PhiC y := by
  rw [integral_shell_eq hα ht hSm hS (fun r : ℝ => r ^ (n - 1) * profile a₀ α W n t r)]
  refine setIntegral_mono_on hint1 hint2 hSm (fun y hy => ?_)
  rw [profile_radiusOf hα ht (hS y hy) (hW y hy)]
  have h := substituted_integrand_le hα ht hn ha₀ (hS y hy) hdef (hlow y hy) (hpos y hy)
  calc |substDeriv a₀ (Real.sqrt t) y / α|
        * ((radiusOf a₀ α (Real.sqrt n / 2) t y) ^ (n - 1) * PhiC y)
      = (|substDeriv a₀ (Real.sqrt t) y / α|
          * (radiusOf a₀ α (Real.sqrt n / 2) t y) ^ (n - 1)) * PhiC y := by ring
    _ ≤ (Real.exp (1 / 2) / α ^ n
          * (Real.sqrt t / 2 * (1 - Real.sqrt t * y) ^ (-(((n : ℝ) + 2) / 2)))) * PhiC y :=
        mul_le_mul_of_nonneg_right h (PhiC_nonneg y)

/-- `PhiC = Φ` on the positive reals, so the bound of `integral_shell_le` is the `I₁`/`I₂`/`I₃`
integrand with the constant `e^{1/2}·√t/(2αⁿ)` in front. -/
theorem integrand_eq_pieces {t y : ℝ} {n : ℕ} (hy : 0 < y) {c : ℝ} :
    c * (Real.sqrt t / 2 * (1 - Real.sqrt t * y) ^ (-(((n : ℝ) + 2) / 2))) * PhiC y
      = c * (Real.sqrt t / 2) * (Phi y * (1 - y * Real.sqrt t) ^ (-(((n : ℝ) + 2) / 2))) := by
  rw [PhiC_of_pos hy, mul_comm (Real.sqrt t) y]
  ring

end D5.S3.Arith.Lattices.Klartag
