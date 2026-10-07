/- GID: D5/S3/Arith/Lattices/Klartag/Contact/Lemma43C
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/Klartag/Contact/Lemma43C
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Contact profile counts and accumulated projection dimension. -/

/- Copyright 2026 Lean FRO, LLC. Licensed under Apache-2.0.
   Source: mlgraham/lean-eval-klartag-submission, commit
   270b3358a135f64a6688636660c07772e8db0173.
   Attribution and full license: Library/QuadraticForms/klartag2025packing.md. -/

import D5.S3.Arith.Lattices.Klartag.Contact.Lemma43B

open D5.S3.Arith.Lattices.Klartag.Construction

namespace D5.S3.Arith.Lattices.Klartag

open MeasureTheory
open Set
open Real
open scoped ENNReal NNReal

/-- `∫₀^T e^{c·t} dt = (e^{c·T} − 1)/c`. -/
theorem integral_exp_mul_Ioc {c T : ℝ} (hc : c ≠ 0) (hT : 0 ≤ T) :
    ∫ t in Ioc (0 : ℝ) T, Real.exp (c * t) = (Real.exp (c * T) - 1) / c := by
  have hderiv : ∀ x ∈ uIcc (0 : ℝ) T, HasDerivAt (fun t : ℝ => Real.exp (c * t) / c)
      (Real.exp (c * x)) x := by
    intro x _
    have h1 : HasDerivAt (fun t : ℝ => c * t) c x := by
      simpa using (hasDerivAt_id x).const_mul c
    have h2 : HasDerivAt (fun t : ℝ => Real.exp (c * t)) (Real.exp (c * x) * c) x := h1.exp
    have h3 := h2.div_const c
    have heq : Real.exp (c * x) * c / c = Real.exp (c * x) := by field_simp
    rwa [heq] at h3
  have hint : IntervalIntegrable (fun t : ℝ => Real.exp (c * t)) volume 0 T :=
    (Continuous.intervalIntegrable (by fun_prop) _ _)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [← intervalIntegral.integral_of_le hT, hFTC]
  simp
  field_simp

/-- With `T = 16·log n/n²`, the exponent is exactly `2·log n`, so `e^{n²T/8} = n²`. -/
theorem exp_n2T_eq {n : ℕ} (hn : 0 < n) {T : ℝ} (hT : T = 16 * Real.log n / (n : ℝ) ^ 2) :
    Real.exp ((n : ℝ) ^ 2 / 8 * T) = (n : ℝ) ^ 2 := by
  have hn0 : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.2 hn
  have hexp : (n : ℝ) ^ 2 / 8 * T = 2 * Real.log n := by
    rw [hT]; field_simp; ring
  rw [hexp, two_mul, Real.exp_add, Real.exp_log hn0]
  ring

/-- **The `t`-integral of Lemma 4.3's bound, exactly.**  `∫₀ᵀ e^{n²t/8} dt = 8 − 8/n²`.

No asymptotics: this is an identity at `T = 16·log n/n²`.  Verified numerically against quadrature
to ten digits (`/private/tmp/claude-501/b-l10-2/t_integral.py`). -/
theorem integral_exp_n2_eq {n : ℕ} (hn : 0 < n) {T : ℝ}
    (hT : T = 16 * Real.log n / (n : ℝ) ^ 2) (hT0 : 0 ≤ T) :
    ∫ t in Ioc (0 : ℝ) T, Real.exp ((n : ℝ) ^ 2 / 8 * t) = 8 - 8 / (n : ℝ) ^ 2 := by
  have hn0 : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.2 hn
  have hc : (n : ℝ) ^ 2 / 8 ≠ 0 := by positivity
  rw [integral_exp_mul_Ioc hc hT0, exp_n2T_eq hn hT]
  field_simp

/-- `T = 16·log n/n²` is non-negative for `n ≥ 1`. -/
theorem T_nonneg {n : ℕ} (hn : 1 ≤ n) : (0 : ℝ) ≤ 16 * Real.log n / (n : ℝ) ^ 2 := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hlog : (0 : ℝ) ≤ Real.log n := Real.log_nonneg hn1
  positivity

section Antitone

/-- An integral of antitone functions is antitone. -/
theorem antitone_integral {T : ℝ} {g : ℝ → ℝ → ℝ}
    (hanti : ∀ t ∈ Ioc (0 : ℝ) T, Antitone (g t))
    (hint : ∀ r : ℝ, IntegrableOn (fun t : ℝ => g t r) (Ioc (0 : ℝ) T)) :
    Antitone (fun r : ℝ => ∫ t in Ioc (0 : ℝ) T, g t r) := by
  intro r₁ r₂ h
  exact setIntegral_mono_on (hint r₂) (hint r₁) measurableSet_Ioc (fun t ht => hanti t ht h)

/-- The `t`-integrated profile is non-negative. -/
theorem integral_nonneg_of_nonneg {T : ℝ} {g : ℝ → ℝ → ℝ} (hg0 : ∀ t r, 0 ≤ g t r) (r : ℝ) :
    0 ≤ ∫ t in Ioc (0 : ℝ) T, g t r :=
  setIntegral_nonneg measurableSet_Ioc (fun t _ => hg0 t r)

end Antitone

section Tonelli

/-- **Tonelli for the radial/`t` pair.**  The `ℝ≥0∞` swap; only measurability is needed. -/
theorem lintegral_radial_t_swap {T : ℝ} (G : ℝ → ℝ → ℝ≥0∞)
    (hG : AEMeasurable (Function.uncurry G)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioc (0 : ℝ) T)))) :
    ∫⁻ y in Ioi (0 : ℝ), ∫⁻ t in Ioc (0 : ℝ) T, G y t
      = ∫⁻ t in Ioc (0 : ℝ) T, ∫⁻ y in Ioi (0 : ℝ), G y t :=
  lintegral_lintegral_swap hG

/-- **The `t`-integrated radial bound in `ℝ≥0∞`.**  Feed the fixed-`t` Lemma 4.3 bound
`∫ y ≤ C₁·e^{n²t/8}` and get `∫ y ∫ t ≤ C₁·(8 − 8/n²)` — the exact constant of §1. -/
theorem lintegral_radial_t_le {n : ℕ} (hn : 0 < n) {T C₁ : ℝ}
    (hT : T = 16 * Real.log n / (n : ℝ) ^ 2) (hT0 : 0 ≤ T) (hC₁ : 0 ≤ C₁)
    (G : ℝ → ℝ → ℝ≥0∞)
    (hG : AEMeasurable (Function.uncurry G)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioc (0 : ℝ) T))))
    (hbound : ∀ t ∈ Ioc (0 : ℝ) T, ∫⁻ y in Ioi (0 : ℝ), G y t
      ≤ ENNReal.ofReal (C₁ * Real.exp ((n : ℝ) ^ 2 / 8 * t))) :
    ∫⁻ y in Ioi (0 : ℝ), ∫⁻ t in Ioc (0 : ℝ) T, G y t
      ≤ ENNReal.ofReal (C₁ * (8 - 8 / (n : ℝ) ^ 2)) := by
  have hcont : Continuous (fun t : ℝ => C₁ * Real.exp ((n : ℝ) ^ 2 / 8 * t)) := by fun_prop
  have hintOn : IntegrableOn (fun t : ℝ => C₁ * Real.exp ((n : ℝ) ^ 2 / 8 * t))
      (Ioc (0 : ℝ) T) := hcont.integrableOn_Ioc
  have hnn : ∀ t : ℝ, 0 ≤ C₁ * Real.exp ((n : ℝ) ^ 2 / 8 * t) := by
    intro t; positivity
  have hval : ∫ t in Ioc (0 : ℝ) T, C₁ * Real.exp ((n : ℝ) ^ 2 / 8 * t)
      = C₁ * (8 - 8 / (n : ℝ) ^ 2) := by
    rw [MeasureTheory.integral_const_mul, integral_exp_n2_eq hn hT hT0]
  calc ∫⁻ y in Ioi (0 : ℝ), ∫⁻ t in Ioc (0 : ℝ) T, G y t
      = ∫⁻ t in Ioc (0 : ℝ) T, ∫⁻ y in Ioi (0 : ℝ), G y t := lintegral_radial_t_swap G hG
    _ ≤ ∫⁻ t in Ioc (0 : ℝ) T,
          ENNReal.ofReal (C₁ * Real.exp ((n : ℝ) ^ 2 / 8 * t)) := by
        refine setLIntegral_mono (hcont.measurable.ennreal_ofReal) (fun t ht => hbound t ht)
    _ = ENNReal.ofReal (∫ t in Ioc (0 : ℝ) T, C₁ * Real.exp ((n : ℝ) ^ 2 / 8 * t)) :=
        (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hintOn
          (Filter.Eventually.of_forall (fun t => hnn t))).symm
    _ = ENNReal.ofReal (C₁ * (8 - 8 / (n : ℝ) ^ 2)) := by rw [hval]

/-- **From an `ℝ≥0∞` bound to `RadialWeightData.radial_bound`.**  The Bochner statement the
structure wants, recovered from the `ℝ≥0∞` one under integrability. -/
theorem radial_bound_of_lintegral {n : ℕ} {f : ℝ → ℝ} {C : ℝ}
    (hf0 : ∀ r : ℝ, 0 ≤ f r) (hC0 : 0 ≤ C)
    (hint : IntegrableOn (fun y : ℝ => y ^ (n - 1) * f y) (Ioi (0 : ℝ)))
    (hlint : ∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal (y ^ (n - 1) * f y) ≤ ENNReal.ofReal C) :
    ∫ y in Ioi (0 : ℝ), y ^ (n - 1) * f y ≤ C := by
  have hbridge := MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint
    (by filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with y hy
        exact mul_nonneg (pow_nonneg (le_of_lt hy) _) (hf0 y))
  rw [← hbridge] at hlint
  exact (ENNReal.ofReal_le_ofReal_iff hC0).1 hlint

end Tonelli

section Assembly

open D5.S3.Arith.Lattices.Klartag.Construction.Section5
open D5.S3.Arith.Lattices.Klartag.Construction.Tiling

/-- Pulling `y^{n−1}` and the `t`-integral through `ENNReal.ofReal`. -/
theorem lintegral_t_ofReal {n : ℕ} {T y : ℝ} (hy : 0 ≤ y) {g : ℝ → ℝ → ℝ}
    (hg0 : ∀ t r : ℝ, 0 ≤ g t r)
    (hint : IntegrableOn (fun t : ℝ => g t y) (Ioc (0 : ℝ) T)) :
    ∫⁻ t in Ioc (0 : ℝ) T, ENNReal.ofReal (y ^ (n - 1) * g t y)
      = ENNReal.ofReal (y ^ (n - 1) * ∫ t in Ioc (0 : ℝ) T, g t y) := by
  have hc : (0 : ℝ) ≤ y ^ (n - 1) := pow_nonneg hy _
  have hfun : (fun t : ℝ => ENNReal.ofReal (y ^ (n - 1) * g t y))
      = fun t : ℝ => ENNReal.ofReal (y ^ (n - 1)) * ENNReal.ofReal (g t y) := by
    funext t
    rw [ENNReal.ofReal_mul hc]
  rw [hfun, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall (fun t => hg0 t y)),
    ← ENNReal.ofReal_mul hc]

/-- `8 − 8/n² ≥ 0` for `n ≥ 1`. -/
theorem eight_sub_nonneg {n : ℕ} (hn : 0 < n) : (0 : ℝ) ≤ 8 - 8 / (n : ℝ) ^ 2 := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hsq : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  have : 8 / (n : ℝ) ^ 2 ≤ 8 := by
    rw [div_le_iff₀ (by nlinarith)]
    nlinarith
  linarith

end Assembly

section Successor

open D5.S3.Arith.Lattices.Klartag.Construction.Section5
open D5.S3.Arith.Lattices.Klartag.Construction.Tiling
open D5.S3.Arith.Lattices.Klartag.Construction.ConstructionA

end Successor

section Excursion

end Excursion

end D5.S3.Arith.Lattices.Klartag
