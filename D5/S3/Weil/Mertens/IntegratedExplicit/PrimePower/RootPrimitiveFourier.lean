/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/RootPrimitiveFourier
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/PrimePower/RootPrimitiveFourier
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Normalized root primitives and separation of actual zero modes from a fixed frequency. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.RootSpectrum
import D5.S3.Weil.Mertens.IntegratedExplicit.RHPrimeWindowMean

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower

open D5.S3.Weil.Mertens.IntegratedExplicit (actualCoeff)
open D5.S3.Weil.Mertens.IntegratedExplicit.RHPrimeWindowMean (frequency)
open Set D5.S3.Weil.ZeroSum
open D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds

/-- The integrated mode gains at most one factor of the root degree from its primitive. -/
theorem root_primitive_coefficient_norm_le {r : ℝ} (hr : 1 < r) (k : ℕ) :
    ‖rootCoeff r k / rootExponent r k‖ ≤ (r * ‖actualCoeff k‖) * r := by
  have hr0 : 0 < r := zero_lt_one.trans hr
  rw [norm_div]
  calc
    _ ≤ ‖rootCoeff r k‖ / r⁻¹ :=
      div_le_div_of_nonneg_left (norm_nonneg _) (inv_pos.mpr hr0) (rootExponent_norm hr k)
    _ ≤ _ := by rw [div_inv_eq_mul]; gcongr; exact rootCoeff_bound hr k

/-- Removing the common real decay rate expresses the primitive as a centered zero series. -/
theorem normalized_root_primitive_series {r : ℝ} (hr : 1 < r) (u : ℝ) :
    let s : ℝ := 1/2-(2*r)⁻¹
    Real.exp (s*u)*rootPrimitive r (Real.exp u) =
      (∑' k, (rootCoeff r k / rootExponent r k) *
        Complex.exp ((frequency k/(r : ℂ))*(u : ℂ))).re := by
  let s : ℝ := 1/2-(2*r)⁻¹
  have hrC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
  have hshift (k : ℕ) : rootExponent r k + (s : ℂ) = frequency k/(r : ℂ) := by
    simp only [rootExponent, frequency, s]
    push_cast
    field_simp
    ring
  change Real.exp (s*u)*rootPrimitive r (Real.exp u) = _
  unfold rootPrimitive
  rw [← Complex.re_ofReal_mul, ← tsum_mul_left]
  congr 1
  apply tsum_congr
  intro k
  rw [← rootPrimitiveMode_eq hr]
  change (Real.exp (s*u) : ℂ) *
    (rootCoeff r k * Complex.exp (rootExponent r k * (u : ℂ))/rootExponent r k) = _
  rw [Complex.ofReal_exp]
  push_cast
  rw [show Complex.exp ((s : ℂ)*(u : ℂ)) *
      (rootCoeff r k * Complex.exp (rootExponent r k * (u : ℂ))/rootExponent r k) =
      (rootCoeff r k / rootExponent r k) * (Complex.exp (rootExponent r k * (u : ℂ)) *
        Complex.exp ((s : ℂ)*(u : ℂ))) by ring,
    ← Complex.exp_add, ← add_mul, hshift]

/-- Each tested frequency is separated from the remaining distinct modes of the actual zeros. -/
theorem actual_frequency_gap {r : ℝ} (hr : 0 < r) (w : ℂ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ k : ℕ, frequency k / (r : ℂ) ≠ w →
      δ ≤ ‖frequency k / (r : ℂ)-w‖ := by
  let mode (k : ℕ) := frequency k / (r : ℂ)
  let modes (n : ℕ) := (actualData.zero n - 1/2)/(r : ℂ)
  let near := {n : ℕ | spectralRadius (actualData.zero n) ≤ (1+‖w‖)*r}
  have hnear : near.Finite := actualData.locallyFinite _
  let others := modes '' near \ {w}
  have hothers : others.Finite := (hnear.image modes).sdiff
  have hopen : IsOpen othersᶜ := hothers.isClosed.isOpen_compl
  have hw : w ∈ othersᶜ := by simp [others]
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hopen w hw
  refine ⟨min δ 1, lt_min hδ zero_lt_one, fun k hk => ?_⟩
  change mode k ≠ w at hk
  by_contra! hdist
  have hsmall : ‖mode k-w‖ < δ := hdist.trans_le (min_le_left _ _)
  have hone : ‖mode k-w‖ < 1 := hdist.trans_le (min_le_right _ _)
  have hmode : ‖mode k‖ ≤ 1+‖w‖ := calc
    ‖mode k‖ = ‖(mode k-w)+w‖ := by rw [sub_add_cancel]
    _ ≤ ‖mode k-w‖+‖w‖ := norm_add_le _ _
    _ ≤ 1+‖w‖ := by linarith
  let n := (actualOccurrenceEquiv k).1
  have hn : n ∈ near := by
    simp only [near, Set.mem_ofPred_eq, D5.S3.Weil.ZeroSum.spectralRadius, spectralParameter]
    have h : ‖frequency k‖ / r ≤ 1+‖w‖ := by
      simpa only [mode, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr] using hmode
    have hh := (div_le_iff₀ hr).mp h
    rw [norm_mul, norm_neg, Complex.norm_I, one_mul]
    rw [show (↑D5.S3.Weil.Convention.criticalAbscissa : ℂ) = 1/2 by norm_num [D5.S3.Weil.Convention.criticalAbscissa]]
    change ‖actualZero k - 1/2‖ ≤ _
    exact hh
  have hmk : mode k ∈ others := ⟨⟨n, hn, rfl⟩, by simpa only [Set.mem_singleton_iff] using hk⟩
  have hdist' : mode k ∈ Metric.ball w δ := by
    simpa only [Metric.mem_ball, dist_eq_norm] using hsmall
  exact (hball hdist') hmk

end D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower
