/- GID: D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound4
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/Klartag/Contact/ProfileBound4
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Contact profile counts and accumulated projection dimension. -/

/- Copyright 2026 Lean FRO, LLC. Licensed under Apache-2.0.
   Source: mlgraham/lean-eval-klartag-submission, commit
   270b3358a135f64a6688636660c07772e8db0173.
   Attribution and full license: Library/QuadraticForms/klartag2025packing.md. -/

import D5.S3.Arith.Lattices.Klartag.Contact.ProfileBound3

open D5.S3.Arith.Lattices.Klartag.Construction
open D5.S3.Arith.Lattices.Klartag.Walk

namespace D5.S3.Arith.Lattices.Klartag

open MeasureTheory
open Set
open Real
open scoped ENNReal NNReal

variable {a₀ α W : ℝ} {n : ℕ}

/-- `∫₀^ρ r^{n−1} dr = ρⁿ/n`. -/
theorem integral_pow_Ioc {ρ : ℝ} (hρ : 0 ≤ ρ) (hn : 0 < n) :
    ∫ r in Ioc (0 : ℝ) ρ, r ^ (n - 1) = ρ ^ n / n := by
  have hsucc : n - 1 + 1 = n := by omega
  have hcast : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by
    have h1 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by push_cast [Nat.cast_sub hn]; ring
    rw [h1]; ring
  rw [← intervalIntegral.integral_of_le hρ, integral_pow, hsucc,
    zero_pow (by omega : n ≠ 0), sub_zero, hcast]

/-- **The inner-ball piece.**  On `(0, ρ]` the profile is at most `1/2` (it is exactly `1/2` below
the shell), so the piece contributes `ρⁿ/(2n)`. -/
theorem inner_ball_le {ρ t : ℝ} (hn : 0 < n) (hρ : 0 ≤ ρ)
    (hint : IntegrableOn (fun r : ℝ => r ^ (n - 1) * profile a₀ α W n t r) (Ioc (0 : ℝ) ρ)) :
    ∫ r in Ioc (0 : ℝ) ρ, r ^ (n - 1) * profile a₀ α W n t r ≤ ρ ^ n / (2 * n) := by
  have hmono : ∫ r in Ioc (0 : ℝ) ρ, r ^ (n - 1) * profile a₀ α W n t r
      ≤ ∫ r in Ioc (0 : ℝ) ρ, 1 / 2 * r ^ (n - 1) := by
    refine setIntegral_mono_on hint ?_ measurableSet_Ioc (fun r hr => ?_)
    · exact (Continuous.integrableOn_Ioc (by fun_prop))
    · have hr0 : (0 : ℝ) ≤ r := hr.1.le
      calc r ^ (n - 1) * profile a₀ α W n t r
          ≤ r ^ (n - 1) * (1 / 2) :=
            mul_le_mul_of_nonneg_left (profile_le_half t r) (pow_nonneg hr0 _)
        _ = 1 / 2 * r ^ (n - 1) := by ring
  refine le_trans hmono ?_
  rw [MeasureTheory.integral_const_mul, integral_pow_Ioc hρ hn]
  have hn0 : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.2 hn
  field_simp
  exact le_refl _

theorem continuousOn_radiusOf {a₀ α δ t : ℝ} (hα : 0 < α) {Y : ℝ}
    (hS : ∀ y ∈ Icc (0 : ℝ) Y, 0 < a₀ - Real.sqrt t * y) :
    ContinuousOn (radiusOf a₀ α δ t) (Icc (0 : ℝ) Y) := by
  unfold radiusOf subst
  refine ContinuousOn.add (ContinuousOn.div ?_ continuousOn_const (fun _ _ => ne_of_gt hα))
    continuousOn_const
  refine ContinuousOn.inv₀ ?_ (fun y hy => ?_)
  · exact (Real.continuous_sqrt.comp_continuousOn (by fun_prop))
  · exact ne_of_gt (Real.sqrt_pos.2 (hS y hy))

/-- **The shell is covered by the window's image.**  `intermediate_value_Ioc`, with `radiusOf`
continuous on `[0, Y]`. -/
theorem shell_subset_image {a₀ α δ t Y : ℝ} (hα : 0 < α) (hY : 0 ≤ Y)
    (hS : ∀ y ∈ Icc (0 : ℝ) Y, 0 < a₀ - Real.sqrt t * y) :
    Ioc (radiusOf a₀ α δ t 0) (radiusOf a₀ α δ t Y)
      ⊆ radiusOf a₀ α δ t '' Ioc (0 : ℝ) Y :=
  intermediate_value_Ioc hY (continuousOn_radiusOf hα hS)

/-- `∫₀^W = ∫₀^ρ + ∫_ρ^W`, the inner ball plus the shell. -/
theorem window_split {ρ t : ℝ} (hρ : 0 ≤ ρ) (hρW : ρ ≤ W)
    (h1 : IntegrableOn (fun r : ℝ => r ^ (n - 1) * profile a₀ α W n t r) (Ioc (0 : ℝ) ρ))
    (h2 : IntegrableOn (fun r : ℝ => r ^ (n - 1) * profile a₀ α W n t r) (Ioc ρ W)) :
    ∫ r in Ioc (0 : ℝ) W, r ^ (n - 1) * profile a₀ α W n t r
      = (∫ r in Ioc (0 : ℝ) ρ, r ^ (n - 1) * profile a₀ α W n t r)
        + ∫ r in Ioc ρ W, r ^ (n - 1) * profile a₀ α W n t r :=
  setIntegral_Ioc_split hρ hρW h1 h2

/-- **The window integral, bounded by the inner ball plus the shell.**  The shape the final
assembly consumes: the fourth piece explicit, the shell handed to `integral_shell_le`. -/
theorem window_le {ρ t Cshell : ℝ} (hn : 0 < n) (hρ : 0 ≤ ρ) (hρW : ρ ≤ W)
    (h1 : IntegrableOn (fun r : ℝ => r ^ (n - 1) * profile a₀ α W n t r) (Ioc (0 : ℝ) ρ))
    (h2 : IntegrableOn (fun r : ℝ => r ^ (n - 1) * profile a₀ α W n t r) (Ioc ρ W))
    (hshell : ∫ r in Ioc ρ W, r ^ (n - 1) * profile a₀ α W n t r ≤ Cshell) :
    ∫ r in Ioc (0 : ℝ) W, r ^ (n - 1) * profile a₀ α W n t r ≤ ρ ^ n / (2 * n) + Cshell := by
  rw [window_split hρ hρW h1 h2]
  exact add_le_add (inner_ball_le hn hρ h1) hshell

end D5.S3.Arith.Lattices.Klartag
