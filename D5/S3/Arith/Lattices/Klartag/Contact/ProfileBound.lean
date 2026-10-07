/- GID: D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/Klartag/Contact/ProfileBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Contact profile counts and accumulated projection dimension. -/

/- Copyright 2026 Lean FRO, LLC. Licensed under Apache-2.0.
   Source: mlgraham/lean-eval-klartag-submission, commit
   270b3358a135f64a6688636660c07772e8db0173.
   Attribution and full license: Library/QuadraticForms/klartag2025packing.md. -/

import D5.S3.Arith.Lattices.Klartag.Contact.Profile

open D5.S3.Arith.Lattices.Klartag.Construction
open D5.S3.Arith.Lattices.Klartag.Walk

namespace D5.S3.Arith.Lattices.Klartag

open MeasureTheory
open Set
open Real
open scoped ENNReal NNReal

variable {a₀ α W : ℝ} {n : ℕ}

/-- The `ℝ≥0∞` integral of the profile is the `ofReal` of its Bochner integral. -/
theorem lintegral_profile_eq_ofReal (hW : 0 ≤ W) (t : ℝ) :
    ∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal (y ^ (n - 1) * profile a₀ α W n t y)
      = ENNReal.ofReal (∫ y in Ioi (0 : ℝ), y ^ (n - 1) * profile a₀ α W n t y) :=
  (MeasureTheory.ofReal_integral_eq_lintegral_ofReal (integrableOn_profile_radial hW t)
    (by
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with y hy
      exact mul_nonneg (pow_nonneg (le_of_lt hy) _) (profile_nonneg t y))).symm

/-- **`hgbound` from a real bound.**  Everything `ℝ≥0∞` is discharged here, so the three-piece
split may be carried out entirely over `ℝ`. -/
theorem hgbound_of_bochner (hW : 0 ≤ W) {t C : ℝ}
    (h : ∫ y in Ioi (0 : ℝ), y ^ (n - 1) * profile a₀ α W n t y ≤ C) :
    ∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal (y ^ (n - 1) * profile a₀ α W n t y)
      ≤ ENNReal.ofReal C := by
  rw [lintegral_profile_eq_ofReal hW t]
  exact ENNReal.ofReal_le_ofReal h

/-- The same, restricted to the window — the form the split consumes. -/
theorem hgbound_of_window (hW : 0 ≤ W) {t C : ℝ}
    (h : ∫ y in Ioc (0 : ℝ) W, y ^ (n - 1) * profile a₀ α W n t y ≤ C) :
    ∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal (y ^ (n - 1) * profile a₀ α W n t y)
      ≤ ENNReal.ofReal C := by
  refine hgbound_of_bochner hW ?_
  have hzero : ∀ y : ℝ, W < y → y ^ (n - 1) * profile a₀ α W n t y = 0 := by
    intro y hy
    rw [profile_zero_of_gt hy, mul_zero]
  have hsplit : Ioi (0 : ℝ) = Ioc (0 : ℝ) W ∪ Ioi W := (Ioc_union_Ioi_eq_Ioi hW).symm
  have hdisj : Disjoint (Ioc (0 : ℝ) W) (Ioi W) :=
    Set.disjoint_left.2 (fun y hy1 hy2 => absurd hy2 (not_lt.2 hy1.2))
  have htail : IntegrableOn (fun y : ℝ => y ^ (n - 1) * profile a₀ α W n t y) (Ioi W) := by
    have h0 : IntegrableOn (fun _ : ℝ => (0 : ℝ)) (Ioi W) volume := integrableOn_zero
    exact h0.congr_fun (fun y hy => (hzero y hy).symm) measurableSet_Ioi
  have hwin : IntegrableOn (fun y : ℝ => y ^ (n - 1) * profile a₀ α W n t y)
      (Ioc (0 : ℝ) W) := (integrableOn_profile_radial hW t).mono_set (fun y hy => hy.1)
  have hzero' : ∫ y in Ioi W, y ^ (n - 1) * profile a₀ α W n t y = 0 := by
    rw [setIntegral_congr_fun measurableSet_Ioi (fun y hy => hzero y hy)]
    simp
  rw [hsplit, setIntegral_union hdisj measurableSet_Ioi hwin htail, hzero', add_zero]
  exact h

/-- `(u + c)^m ≤ e^{m·c/u₀}·u^m` for `u ≥ u₀ > 0` and `c ≥ 0`. -/
theorem pow_add_le_exp_mul {c u₀ u : ℝ} (hc : 0 ≤ c) (hu₀ : 0 < u₀) (hu : u₀ ≤ u) (m : ℕ) :
    (u + c) ^ m ≤ Real.exp (m * c / u₀) * u ^ m := by
  have hu0 : (0 : ℝ) < u := lt_of_lt_of_le hu₀ hu
  have hfac : u + c = u * (1 + c / u) := by field_simp
  have hexp : (1 : ℝ) + c / u ≤ Real.exp (c / u) := by
    have := Real.add_one_le_exp (c / u)
    linarith
  have hmono : c / u ≤ c / u₀ := by
    apply div_le_div_of_nonneg_left hc hu₀ hu
  calc (u + c) ^ m = u ^ m * (1 + c / u) ^ m := by rw [hfac, mul_pow]
    _ ≤ u ^ m * (Real.exp (c / u)) ^ m := by gcongr
    _ = u ^ m * Real.exp (m * (c / u)) := by rw [← Real.exp_nat_mul]
    _ ≤ u ^ m * Real.exp (m * (c / u₀)) := by gcongr
    _ = Real.exp (m * c / u₀) * u ^ m := by
        rw [mul_comm]
        congr 2
        ring

/-- Two-piece additivity on `Ioc`. -/
theorem setIntegral_Ioc_split {f : ℝ → ℝ} {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    (h1 : IntegrableOn f (Ioc a b)) (h2 : IntegrableOn f (Ioc b c)) :
    ∫ y in Ioc a c, f y = (∫ y in Ioc a b, f y) + ∫ y in Ioc b c, f y := by
  have hdisj : Disjoint (Ioc a b) (Ioc b c) :=
    Set.disjoint_left.2 (fun y hy1 hy2 => absurd hy2.1 (not_lt.2 hy1.2))
  rw [← Ioc_union_Ioc_eq_Ioc hab hbc, setIntegral_union hdisj measurableSet_Ioc h1 h2]

theorem setIntegral_Ioc_split₃ {f : ℝ → ℝ} {a b c d : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d)
    (h1 : IntegrableOn f (Ioc a b)) (h2 : IntegrableOn f (Ioc b c))
    (h3 : IntegrableOn f (Ioc c d)) :
    ∫ y in Ioc a d, f y
      = (∫ y in Ioc a b, f y) + (∫ y in Ioc b c, f y) + ∫ y in Ioc c d, f y := by
  have h23 : IntegrableOn f (Ioc b d) := by
    rw [← Ioc_union_Ioc_eq_Ioc hbc hcd]
    exact h2.union h3
  rw [setIntegral_Ioc_split hab (le_trans hbc hcd) h1 h23,
    setIntegral_Ioc_split hbc hcd h2 h3, add_assoc]

section I2

/-- **`I₂` with its prefactor, bounded by an absolute constant times `e^{n²t/8}`.**

This is Klartag's eq. (59) together with eq. (56)'s prefactor, complete.  The constant is
`e^J·(2/√(2π) + 2)`, where `J` bounds the junk term of `Lemma43.integrand_le` on `(1, L]`. -/
theorem I2_le {t J L : ℝ} (ht : 0 ≤ t) (hLs : L * Real.sqrt t ≤ 1 / 2)
    (hb : 2 ≤ (n : ℝ) * Real.sqrt t / 2)
    (hLb : (n : ℝ) * Real.sqrt t / 2 / 2 ≤ L)
    (hJ : ∀ y ∈ Ioc (1 : ℝ) L,
      y * Real.sqrt t + ((n : ℝ) + 2) / 2 * (y * Real.sqrt t) ^ 2 ≤ J)
    (hint1 : IntegrableOn
      (fun y : ℝ => Phi y * (1 - y * Real.sqrt t) ^ (-(((n : ℝ) + 2) / 2))) (Ioc 1 L))
    (hint2 : IntegrableOn (fun y : ℝ =>
      Real.exp J / Real.sqrt (2 * π) * Real.exp ((n : ℝ) ^ 2 * t / 8)
        * (Real.exp (-(y - (n : ℝ) * Real.sqrt t / 2) ^ 2 / 2) / y)) (Ioc 1 L)) :
    ((n : ℝ) * Real.sqrt t / 2) *
        ∫ y in Ioc (1 : ℝ) L, Phi y * (1 - y * Real.sqrt t) ^ (-(((n : ℝ) + 2) / 2))
      ≤ Real.exp J * (2 / Real.sqrt (2 * π) + 2) * Real.exp ((n : ℝ) ^ 2 * t / 8) := by
  set b : ℝ := (n : ℝ) * Real.sqrt t / 2 with hbdef
  have hb0 : (0 : ℝ) < b := by linarith

  have hK : ∫ y in Ioc (1 : ℝ) L, Real.exp (-(y - b) ^ 2 / 2) / y
      ≤ (2 + 2 * Real.sqrt (2 * π)) / b := gaussian_over_y_le hb hLb

  have hone := oneDim_le (n := n) ht hLs hJ hint1 hint2 hK

  calc b * ∫ y in Ioc (1 : ℝ) L, Phi y * (1 - y * Real.sqrt t) ^ (-(((n : ℝ) + 2) / 2))
      ≤ b * (Real.exp J * ((2 + 2 * Real.sqrt (2 * π)) / b) / Real.sqrt (2 * π)
          * Real.exp ((n : ℝ) ^ 2 * t / 8)) := by
        exact mul_le_mul_of_nonneg_left hone hb0.le
    _ = (b * (Real.exp J * ((2 + 2 * Real.sqrt (2 * π)) / b) / Real.sqrt (2 * π)))
          * Real.exp ((n : ℝ) ^ 2 * t / 8) := by ring
    _ ≤ (Real.exp J * (2 / Real.sqrt (2 * π) + 2)) * Real.exp ((n : ℝ) ^ 2 * t / 8) := by
        refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
        exact prefactor_cancel hb0 le_rfl
    _ = Real.exp J * (2 / Real.sqrt (2 * π) + 2) * Real.exp ((n : ℝ) ^ 2 * t / 8) := by ring

end I2

end D5.S3.Arith.Lattices.Klartag
