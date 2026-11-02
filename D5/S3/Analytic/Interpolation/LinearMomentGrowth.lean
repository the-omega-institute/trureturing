/- GID: D5/S3/Analytic/Interpolation/LinearMomentGrowth
   generality: I
   mirror-B: D5/B/S3/Analytic/Interpolation/LinearMomentGrowth
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Algebra.Group.ForwardDiff, mathlib/module/Mathlib.Topology.Order.Compact]
   utility: none
   digest: Quantitative exponential growth from a linear upper rate for finite atomic moment positivity. -/

import D5.S3.Analytic.Interpolation.SublinearMomentGrowth

/-! Dilation, finite Newton envelopes and quantitative all-real growth. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Finset Filter Function Real
open scoped BigOperators ComplexConjugate Topology fwdDiff

namespace D5.S3.Analytic.Interpolation.LinearMomentGrowth

open D5.S3.Analytic.Fourier.PositiveDefiniteImaginaryAxis
open D5.S3.Analytic.Interpolation.SublinearMomentGrowth

/-- Pull the full finite-family positivity telescope through a positive dilation. -/
private lemma scaled_momentPositive (F : ℝ → ℝ) (m : ℝ → ℕ) (h : ℝ)
    (hh : 0 < h) (hpos : momentPositive F m) :
    momentPositive (fun s : ℝ => F (h * s)) (fun D : ℝ => m (h * D)) := by
  unfold momentPositive at hpos ⊢
  obtain ⟨D₀, hD₀⟩ := eventually_atTop.mp hpos
  filter_upwards [eventually_ge_atTop (D₀ / h)] with D hD
  have hDscaled : D₀ ≤ h * D := by
    simpa only [mul_comm] using (div_le_iff₀ hh).mp hD
  intro n x a hx ha
  let y : Fin n → ℝ := fun i => h * x i
  have hy : ∀ i, 0 ≤ y i ∧ y i ≤ h * D := by
    intro i
    constructor
    · dsimp [y]
      exact mul_nonneg hh.le (hx i).1
    · dsimp [y]
      exact mul_le_mul_of_nonneg_left (hx i).2 (le_of_lt hh)
  have hya : ∀ r : ℕ, r < m (h * D) →
      ∑ i, a i * ((y i : ℂ) ^ r) = 0 := by
    intro r hr
    calc
      ∑ i, a i * ((y i : ℂ) ^ r) =
          (h : ℂ) ^ r * ∑ i, a i * ((x i : ℂ) ^ r) := by
        simp only [y, Complex.ofReal_mul, mul_pow]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = 0 := by rw [ha r hr, mul_zero]
  simpa only [y, ← mul_sub] using hD₀ (h * D) hDscaled n y a hy hya

/-- The eventual lower-order premise is preserved by the same positive dilation. -/
private lemma scaled_eventually_one (m : ℝ → ℕ) (h : ℝ) (hh : 0 < h)
    (hm : ∀ᶠ D : ℝ in atTop, 1 ≤ m D) :
    ∀ᶠ D : ℝ in atTop, 1 ≤ m (h * D) := by
  obtain ⟨D₀, hD₀⟩ := eventually_atTop.mp hm
  filter_upwards [eventually_ge_atTop (D₀ / h)] with D hD
  apply hD₀ (h * D)
  simpa only [mul_comm] using (div_le_iff₀ hh).mp hD

/-- A strict fixed-window slope follows from the supplied eventual rate bound. -/
private lemma scaled_rate_lt (m : ℝ → ℕ) (c h : ℝ) (hh : 0 < h)
    (hc : 0 ≤ c) (hgap : h * c < (1 / 16 : ℝ))
    (hrate : ∀ η : ℝ, 0 < η →
      ∀ᶠ D : ℝ in atTop, (m D : ℝ) / D ≤ c + η) :
    ∀ᶠ D : ℝ in atTop, (m (h * D) : ℝ) / D < (1 / 16 : ℝ) := by
  have hmargin : 0 < 1 / (16 * h) - c := by
    have hid : h * (1 / (16 * h)) = (1 / 16 : ℝ) := by
      field_simp [ne_of_gt hh]
    nlinarith
  let η : ℝ := (1 / (16 * h) - c) / 2
  have hη : 0 < η := by
    dsimp [η]
    positivity
  obtain ⟨S₀, hS₀⟩ := eventually_atTop.mp (hrate η hη)
  filter_upwards [eventually_ge_atTop (max (S₀ / h) 1)] with D hD
  have hDpos : 0 < D := by
    have : (1 : ℝ) ≤ D := le_trans (le_max_right _ _) hD
    linarith
  have hscaled : S₀ ≤ h * D := by
    have hDh : S₀ / h ≤ D := le_trans (le_max_left _ _) hD
    simpa only [mul_comm] using (div_le_iff₀ hh).mp hDh
  have hbound := hS₀ (h * D) hscaled
  have hrewrite : (m (h * D) : ℝ) / D =
      h * ((m (h * D) : ℝ) / (h * D)) := by
    field_simp [ne_of_gt hh, ne_of_gt hDpos]
  rw [hrewrite]
  have hnonneg : 0 ≤ h := le_of_lt hh
  have hupper : h * ((m (h * D) : ℝ) / (h * D)) ≤ h * (c + η) :=
    mul_le_mul_of_nonneg_left hbound hnonneg
  have hid : h * (1 / (16 * h)) = (1 / 16 : ℝ) := by
    field_simp [ne_of_gt hh]
  have hstrict : h * (c + η) < (1 / 16 : ℝ) := by
    dsimp [η]
    nlinarith
  exact hupper.trans_lt hstrict

/-- Newton's finite estimate with the fixed ratio needed for the universal slope. -/
private lemma eventual_newton_envelope_fixed {G : ℝ → ℝ} {k : ℝ → ℕ}
    (hG : Continuous G) (heven : ∀ t : ℝ, G (-t) = G t)
    (hk : ∀ᶠ t : ℝ in atTop, 1 ≤ k t)
    (hsmall : ∀ᶠ t : ℝ in atTop, (k t : ℝ) / t < (1 / 16 : ℝ))
    (hpos : momentPositive G k) :
    ∀ᶠ t : ℝ in atTop,
      ((2 * k t + 1 : ℕ) : ℝ) ≤ t / 2 ∧
      |G t| ≤ envelope G (2 * k t + 1 : ℕ) *
        ∑ q ∈ range (2 * k t + 1),
          (2 : ℝ) ^ q * ((Nat.floor t).choose q : ℝ) := by
  filter_upwards [hpos, hk, hsmall, eventually_ge_atTop (4 : ℝ)] with t hD hk' hs ht
  have ht0 : 0 < t := by linarith
  have hkt : (k t : ℝ) < t / 16 := by
    have h := (div_lt_iff₀ ht0).mp hs
    linarith
  have horder : ((2 * k t + 1 : ℕ) : ℝ) ≤ t / 2 := by
    push_cast
    linarith
  have hkn : 2 * k t ≤ Nat.floor t := by
    apply Nat.le_floor
    push_cast
    linarith
  have hfloor := Nat.floor_le ht0.le
  have hr0 : 0 ≤ t - (Nat.floor t : ℝ) := sub_nonneg.mpr hfloor
  have hr1 : t - (Nat.floor t : ℝ) ≤ 1 := by
    linarith [Nat.lt_floor_add_one t]
  have heq : (Nat.floor t : ℝ) + (t - (Nat.floor t : ℝ)) = t := by ring
  refine ⟨horder, ?_⟩
  have h := finite_newton_envelope hG heven (k t) (Nat.floor t)
    (t - (Nat.floor t : ℝ)) hk' hkn hr0 hr1 (by simpa only [heq] using hD)
  simpa only [heq] using h

/-- The quarter-parameter binomial estimate gives the fixed exponent `t`. -/
private lemma eventual_binomial_exp_fixed {k : ℝ → ℕ}
    (hsmall : ∀ᶠ t : ℝ in atTop, (k t : ℝ) / t < (1 / 16 : ℝ)) :
    ∀ᶠ t : ℝ in atTop, 2 * k t ≤ Nat.floor t →
      (∑ q ∈ range (2 * k t + 1),
        (2 : ℝ) ^ q * ((Nat.floor t).choose q : ℝ)) ≤ exp t := by
  filter_upwards [hsmall, eventually_ge_atTop (4 : ℝ)] with t ht ht4
  have ht0 : 0 < t := by linarith
  have hkt : (k t : ℝ) < t / 16 := by
    have h := (div_lt_iff₀ ht0).mp ht
    linarith
  intro hpn
  have hfloor : (Nat.floor t : ℝ) ≤ t := Nat.floor_le ht0.le
  have hexp : ((2 * k t : ℕ) : ℝ) / (1 / 4 : ℝ) +
      2 * (Nat.floor t : ℝ) * (1 / 4 : ℝ) ≤ t := by
    push_cast
    norm_num
    nlinarith
  exact (binomial_sum_exp (Nat.floor t) (2 * k t) (1 / 4 : ℝ)
    hpn (by norm_num) (by norm_num)).trans (exp_le_exp.mpr hexp)

/-- The pointwise fixed-slope estimate closes at half the radius. -/
private lemma eventual_half_envelope_fixed {G : ℝ → ℝ} {k : ℝ → ℕ}
    (hG : Continuous G) (heven : ∀ t : ℝ, G (-t) = G t)
    (hk : ∀ᶠ t : ℝ in atTop, 1 ≤ k t)
    (hsmall : ∀ᶠ t : ℝ in atTop, (k t : ℝ) / t < (1 / 16 : ℝ))
    (hpos : momentPositive G k) :
    ∀ᶠ t : ℝ in atTop, |G t| ≤ envelope G (t / 2) * exp t := by
  filter_upwards [eventual_newton_envelope_fixed hG heven hk hsmall hpos,
    eventual_binomial_exp_fixed hsmall, eventually_ge_atTop (0 : ℝ)] with t hn hb ht
  have hpn : 2 * k t ≤ Nat.floor t := by
    apply Nat.le_floor
    have hr := hn.1
    push_cast at hr ⊢
    linarith
  have hrad : envelope G (2 * k t + 1 : ℕ) ≤ envelope G (t / 2) :=
    envelope_mono hG (by positivity) hn.1
  exact hn.2.trans (mul_le_mul hrad (hb hpn)
    (sum_nonneg (fun q hq => by positivity)) (envelope_pos G (t / 2)).le)

/-- Universal quantitative theorem: the factor `32` is obtained by dilation. -/
theorem linear_moment_growth (F : ℝ → ℝ) (m : ℝ → ℕ) (c : ℝ)
    (hF : Continuous F) (heven : ∀ t : ℝ, F (-t) = F t)
    (hm : ∀ᶠ D : ℝ in atTop, 1 ≤ m D) (hc : 0 ≤ c)
    (hrate : ∀ η : ℝ, 0 < η →
      ∀ᶠ D : ℝ in atTop, (m D : ℝ) / D ≤ c + η)
    (hpos : momentPositive F m) :
    ∀ β : ℝ, 32 * c < β → ∃ C : ℝ, 0 < C ∧
      ∀ t : ℝ, |F t| ≤ C * exp (β * |t|) := by
  intro β hβ
  have hβ0 : 0 < β := by nlinarith
  let h : ℝ := 2 / β
  have hh : 0 < h := by
    dsimp [h]
    positivity
  have hgap : h * c < (1 / 16 : ℝ) := by
    dsimp [h]
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ hβ0).2
    nlinarith
  let G : ℝ → ℝ := fun s => F (h * s)
  let k : ℝ → ℕ := fun D => m (h * D)
  have hG : Continuous G := by
    exact hF.comp (continuous_const.mul continuous_id)
  have hGeven : ∀ s : ℝ, G (-s) = G s := by
    intro s
    dsimp [G]
    rw [show h * -s = -(h * s) by ring, heven]
  have hk : ∀ᶠ D : ℝ in atTop, 1 ≤ k D := by
    dsimp [k]
    exact scaled_eventually_one m h hh hm
  have hsmall : ∀ᶠ D : ℝ in atTop, (k D : ℝ) / D < (1 / 16 : ℝ) := by
    dsimp [k]
    exact scaled_rate_lt m c h hh hc hgap hrate
  have hGpos : momentPositive G k := by
    dsimp [G, k]
    exact scaled_momentPositive F m h hh hpos
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp
    (eventual_half_envelope_fixed hG hGeven hk hsmall hGpos)
  let T : ℝ := max 4 T₀
  have hT : 0 < T := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have htail (t : ℝ) (ht : T ≤ t) :
      |G t| ≤ envelope G (t / 2) * exp t :=
    hT₀ t ((le_max_right _ _).trans ht)
  have hstep := envelope_half_step hG (η := 1) (by norm_num) hT
    (by simpa only [one_mul] using htail)
  refine ⟨envelope G (2 * T), envelope_pos G (2 * T), ?_⟩
  intro t
  have hbound := envelope_dyadic hG (η := 1) (by norm_num) hT hstep |(t / h)| (abs_nonneg (t / h))
  have hscaled : |G (t / h)| ≤ envelope G (2 * T) * exp (2 * |t / h|) := by
    exact (abs_le_envelope_of_even hG hGeven (R := |t / h|) le_rfl).trans
      (by simpa only [mul_one] using hbound)
  have hth : h * (t / h) = t := by
    field_simp [ne_of_gt hh]
  have hexp : 2 * |t / h| = β * |t| := by
    rw [abs_div, abs_of_pos hh]
    dsimp [h]
    field_simp [ne_of_gt hβ0]
  dsimp [G] at hscaled
  rw [hth, hexp] at hscaled
  exact hscaled

end D5.S3.Analytic.Interpolation.LinearMomentGrowth
