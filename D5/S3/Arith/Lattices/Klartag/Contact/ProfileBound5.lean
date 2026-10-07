/- GID: D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound5
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/Klartag/Contact/ProfileBound5
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Contact profile counts and accumulated projection dimension. -/

/- Copyright 2026 Lean FRO, LLC. Licensed under Apache-2.0.
   Source: mlgraham/lean-eval-klartag-submission, commit
   270b3358a135f64a6688636660c07772e8db0173.
   Attribution and full license: Library/QuadraticForms/klartag2025packing.md. -/

import D5.S3.Arith.Lattices.Klartag.Contact.ProfileBound4

open D5.S3.Arith.Lattices.Klartag.Construction
open D5.S3.Arith.Lattices.Klartag.Walk

namespace D5.S3.Arith.Lattices.Klartag

open MeasureTheory
open Set
open Real
open scoped ENNReal NNReal

/-- **`radiusOf '' (0, Y] = (radiusOf 0, radiusOf Y]`.**  `⊇` is the intermediate value theorem
(`shell_subset_image`); `⊆` is strict monotonicity.  Getting the *equality* rather than a
containment is what keeps the assembly short: no measurability of an abstract image is needed. -/
theorem image_radiusOf_Ioc {a₀ α δ t Y : ℝ} (hα : 0 < α) (ht : 0 < t) (hY : 0 ≤ Y)
    (hS : ∀ y ∈ Icc (0 : ℝ) Y, 0 < a₀ - Real.sqrt t * y) :
    radiusOf a₀ α δ t '' Ioc (0 : ℝ) Y
      = Ioc (radiusOf a₀ α δ t 0) (radiusOf a₀ α δ t Y) := by
  have hmono : StrictMonoOn (radiusOf a₀ α δ t) (Icc (0 : ℝ) Y) :=
    strictMonoOn_radiusOf hα ht hS
  refine Set.Subset.antisymm ?_ (shell_subset_image hα hY hS)
  rintro r ⟨y, hy, rfl⟩
  have hy0 : (0 : ℝ) < y := hy.1
  have hyY : y ≤ Y := hy.2
  have hmem0 : (0 : ℝ) ∈ Icc (0 : ℝ) Y := ⟨le_rfl, hY⟩
  have hmemy : y ∈ Icc (0 : ℝ) Y := ⟨hy0.le, hyY⟩
  have hmemY : Y ∈ Icc (0 : ℝ) Y := ⟨hY, le_rfl⟩
  exact ⟨hmono hmem0 hmemy hy0, (hmono.monotoneOn) hmemy hmemY hyY⟩

/-- **The shell integral becomes the `I₁`/`I₂`/`I₃` integral.**  `integral_shell_eq` through the
image identity, then `integral_shell_le`, then `integrand_eq_pieces` pulls the constant out. -/
theorem shell_integral_le {a₀ α W t Y : ℝ} {n : ℕ} (hα : 0 < α) (ht : 0 < t) (hn : 0 < n)
    (ha₀ : 1 ≤ a₀) (hY : 0 ≤ Y) (hdef : (n : ℝ) * (α * Real.sqrt n / 2) ≤ 1 / 4)
    (hWdef : W = radiusOf a₀ α (Real.sqrt n / 2) t Y)
    (hSc : ∀ y ∈ Icc (0 : ℝ) Y, 0 < a₀ - Real.sqrt t * y)
    (hlow : ∀ y ∈ Ioc (0 : ℝ) Y, (1 : ℝ) / (2 * α) ≤ subst a₀ (Real.sqrt t) y / α)
    (hpos : ∀ y ∈ Ioc (0 : ℝ) Y, 0 < 1 - Real.sqrt t * y)
    (hW : ∀ y ∈ Ioc (0 : ℝ) Y, radiusOf a₀ α (Real.sqrt n / 2) t y ≤ W)
    (hint1 : IntegrableOn (fun y : ℝ => |substDeriv a₀ (Real.sqrt t) y / α|
      * ((radiusOf a₀ α (Real.sqrt n / 2) t y) ^ (n - 1)
        * profile a₀ α W n t (radiusOf a₀ α (Real.sqrt n / 2) t y))) (Ioc (0 : ℝ) Y))
    (hint2 : IntegrableOn (fun y : ℝ => Real.exp (1 / 2) / α ^ n
      * (Real.sqrt t / 2 * (1 - Real.sqrt t * y) ^ (-(((n : ℝ) + 2) / 2))) * PhiC y)
      (Ioc (0 : ℝ) Y))
    :
    ∫ r in Ioc (radiusOf a₀ α (Real.sqrt n / 2) t 0) W,
        r ^ (n - 1) * profile a₀ α W n t r
      ≤ Real.exp (1 / 2) / α ^ n * (Real.sqrt t / 2)
        * ∫ y in Ioc (0 : ℝ) Y, Phi y * (1 - y * Real.sqrt t) ^ (-(((n : ℝ) + 2) / 2)) := by
  have hSm : MeasurableSet (Ioc (0 : ℝ) Y) := measurableSet_Ioc
  have hS : ∀ y ∈ Ioc (0 : ℝ) Y, 0 < a₀ - Real.sqrt t * y :=
    fun y hy => hSc y ⟨hy.1.le, hy.2⟩
  have himg : Ioc (radiusOf a₀ α (Real.sqrt n / 2) t 0) W
      = radiusOf a₀ α (Real.sqrt n / 2) t '' Ioc (0 : ℝ) Y := by
    rw [image_radiusOf_Ioc hα ht hY hSc, hWdef]
  rw [himg]
  refine le_trans (integral_shell_le hα ht hn ha₀ hdef hSm hS hlow hpos hW hint1 hint2) ?_
  have hcongr : ∫ y in Ioc (0 : ℝ) Y, Real.exp (1 / 2) / α ^ n
        * (Real.sqrt t / 2 * (1 - Real.sqrt t * y) ^ (-(((n : ℝ) + 2) / 2))) * PhiC y
      = ∫ y in Ioc (0 : ℝ) Y, Real.exp (1 / 2) / α ^ n * (Real.sqrt t / 2)
        * (Phi y * (1 - y * Real.sqrt t) ^ (-(((n : ℝ) + 2) / 2))) := by
    refine setIntegral_congr_fun hSm (fun y hy => ?_)
    exact integrand_eq_pieces (n := n) hy.1
  rw [hcongr, MeasureTheory.integral_const_mul]

/-- **`hgbound` for the concrete profile**, with the constant written out: the inner ball, the
shift-and-Jacobian factor, and the three pieces. -/
theorem hgbound_final {a₀ α W t Cshell : ℝ} {n : ℕ} (hn : 0 < n)
    (hρ : 0 ≤ radiusOf a₀ α (Real.sqrt n / 2) t 0)
    (hρW : radiusOf a₀ α (Real.sqrt n / 2) t 0 ≤ W) (hW0 : 0 ≤ W)
    (h1 : IntegrableOn (fun r : ℝ => r ^ (n - 1) * profile a₀ α W n t r)
      (Ioc (0 : ℝ) (radiusOf a₀ α (Real.sqrt n / 2) t 0)))
    (h2 : IntegrableOn (fun r : ℝ => r ^ (n - 1) * profile a₀ α W n t r)
      (Ioc (radiusOf a₀ α (Real.sqrt n / 2) t 0) W))
    (hshell : ∫ r in Ioc (radiusOf a₀ α (Real.sqrt n / 2) t 0) W,
      r ^ (n - 1) * profile a₀ α W n t r ≤ Cshell) :
    ∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal (y ^ (n - 1) * profile a₀ α W n t y)
      ≤ ENNReal.ofReal ((radiusOf a₀ α (Real.sqrt n / 2) t 0) ^ n / (2 * n) + Cshell) :=
  hgbound_of_window hW0 (window_le hn hρ hρW h1 h2 hshell)

/-- The three pieces summed, with the prefactor. -/
theorem pieces_sum_le {t K₁ K₂ K₃ A Y : ℝ} {n : ℕ}
    (hA1 : (1 : ℝ) ≤ A) (hAY : A ≤ Y) (h0 : (0 : ℝ) ≤ 1)
    (i1 : IntegrableOn
      (fun y : ℝ => Phi y * (1 - y * Real.sqrt t) ^ (-(((n : ℝ) + 2) / 2))) (Ioc 0 1))
    (i2 : IntegrableOn
      (fun y : ℝ => Phi y * (1 - y * Real.sqrt t) ^ (-(((n : ℝ) + 2) / 2))) (Ioc 1 A))
    (i3 : IntegrableOn
      (fun y : ℝ => Phi y * (1 - y * Real.sqrt t) ^ (-(((n : ℝ) + 2) / 2))) (Ioc A Y))
    (b1 : ((n : ℝ) * Real.sqrt t / 2) *
      ∫ y in Ioc (0 : ℝ) 1, Phi y * (1 - y * Real.sqrt t) ^ (-(((n : ℝ) + 2) / 2))
        ≤ K₁ * Real.exp ((n : ℝ) ^ 2 * t / 8))
    (b2 : ((n : ℝ) * Real.sqrt t / 2) *
      ∫ y in Ioc (1 : ℝ) A, Phi y * (1 - y * Real.sqrt t) ^ (-(((n : ℝ) + 2) / 2))
        ≤ K₂ * Real.exp ((n : ℝ) ^ 2 * t / 8))
    (b3 : ((n : ℝ) * Real.sqrt t / 2) *
      ∫ y in Ioc A Y, Phi y * (1 - y * Real.sqrt t) ^ (-(((n : ℝ) + 2) / 2))
        ≤ K₃ * Real.exp ((n : ℝ) ^ 2 * t / 8)) :
    ((n : ℝ) * Real.sqrt t / 2) *
        ∫ y in Ioc (0 : ℝ) Y, Phi y * (1 - y * Real.sqrt t) ^ (-(((n : ℝ) + 2) / 2))
      ≤ (K₁ + K₂ + K₃) * Real.exp ((n : ℝ) ^ 2 * t / 8) := by
  rw [setIntegral_Ioc_split₃ h0 hA1 hAY i1 i2 i3, mul_add, mul_add]
  have hring : (K₁ + K₂ + K₃) * Real.exp ((n : ℝ) ^ 2 * t / 8)
      = K₁ * Real.exp ((n : ℝ) ^ 2 * t / 8) + K₂ * Real.exp ((n : ℝ) ^ 2 * t / 8)
        + K₃ * Real.exp ((n : ℝ) ^ 2 * t / 8) := by ring
  rw [hring]
  exact add_le_add (add_le_add b1 b2) b3

/-- **The shell integral, bounded by the three pieces' constant.**  Composing
`shell_integral_le` with `pieces_sum_le`: the `√t/2` of the former is `1/n` times the `n√t/2` the
pieces carry, which is where the `1/n` in `C₁` comes from. -/
theorem shell_le_pieces {a₀ α W t Y K : ℝ} {n : ℕ} (hn : 0 < n) (hα : 0 < α)
    (hshell : ∫ r in Ioc (radiusOf a₀ α (Real.sqrt n / 2) t 0) W,
        r ^ (n - 1) * profile a₀ α W n t r
      ≤ Real.exp (1 / 2) / α ^ n * (Real.sqrt t / 2)
        * ∫ y in Ioc (0 : ℝ) Y, Phi y * (1 - y * Real.sqrt t) ^ (-(((n : ℝ) + 2) / 2)))
    (hpieces : ((n : ℝ) * Real.sqrt t / 2) *
             ∫ y in Ioc (0 : ℝ) Y, Phi y * (1 - y * Real.sqrt t) ^ (-(((n : ℝ) + 2) / 2))
      ≤ K * Real.exp ((n : ℝ) ^ 2 * t / 8)) :
    ∫ r in Ioc (radiusOf a₀ α (Real.sqrt n / 2) t 0) W,
        r ^ (n - 1) * profile a₀ α W n t r
      ≤ Real.exp (1 / 2) / ((n : ℝ) * α ^ n) * K * Real.exp ((n : ℝ) ^ 2 * t / 8) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.2 hn
  have hαn : (0 : ℝ) < α ^ n := by positivity
  refine le_trans hshell ?_
  have hrw : Real.exp (1 / 2) / α ^ n * (Real.sqrt t / 2)
        * ∫ y in Ioc (0 : ℝ) Y, Phi y * (1 - y * Real.sqrt t) ^ (-(((n : ℝ) + 2) / 2))
      = Real.exp (1 / 2) / ((n : ℝ) * α ^ n)
        * (((n : ℝ) * Real.sqrt t / 2)
          * ∫ y in Ioc (0 : ℝ) Y, Phi y * (1 - y * Real.sqrt t) ^ (-(((n : ℝ) + 2) / 2))) := by
    field_simp
  rw [hrw, mul_assoc]
  exact mul_le_mul_of_nonneg_left hpieces (by positivity)

end D5.S3.Arith.Lattices.Klartag
