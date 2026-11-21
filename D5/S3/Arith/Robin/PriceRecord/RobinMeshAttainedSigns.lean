/- GID: D5/S3/Arith/Robin/PriceRecord/RobinMeshAttainedSigns
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/PriceRecord/RobinMeshAttainedSigns
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: An attained off-line zeta abscissa forces both signs on every ratio-one canonical Robin mesh. -/

import D5.S3.Arith.Robin.PriceRecord.RobinMeshFourierRecovery
import D5.S3.Weil.ZetaBridge.AlternatingZetaContinuation

/-!
# Two-sided excursions on a prescribed mesh in the attained case

Gap-weighted Fourier recovery gives a zero mean at the real abscissa and a
nonzero coefficient at the attaining zero. This forces excursions of both
signs at the critical exponent on the given mesh.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter
open scoped Topology

namespace D5.S3.Arith.Robin.PriceRecord.RobinMeshAttainedSigns

open GapWeightedFourier (average phase frequently_two_signs_of_zero_mean)
open D5.S3.Arith.Robin.ActualTwoPriceDefect (strictInteger)
open D5.S3.Arith.Robin.ForwardKernel.KappaGap (zeroAbscissa zero_re_le_abscissa)
open D5.S3.Arith.Robin.PriceRecord.ActualBalancedCutoff (firstLayerPrice)
open D5.S3.Arith.Robin.PriceRecord.RobinMeshFourierRecovery
  (actual_canonical_samples_fourier_recovery)
open D5.S3.Weil.GronwallLowerEnvelope (robinLogMargin)
open D5.S3.Weil.ZeroSum (IsNontrivialZero)
open D5.S3.Weil.ZetaBridge.AlternatingZetaContinuation (riemannZeta_ne_zero_of_real_mem_Ioo)
open D5.S3.Weil.ZetaBridge.ZeroDataNonemptyIffInfinite
  (exists_multiplicity hasZetaZeroMultiplicity_iff_analyticOrderAt_eq)

/-- If a zero attains the off-line abscissa, every positive increasing ratio-one
mesh admits increasing index subsequences with fixed opposite signed excursions
at the exponent `1 - zeroAbscissa`. -/
theorem actual_attained_canonical_critical_subsequences {ρ : ℂ}
    (hρ : IsNontrivialZero ρ) (hhalf : 1 / 2 < ρ.re) (hρΘ : ρ.re = zeroAbscissa)
    {N : ℕ → ℕ} (hN : StrictMono N) (hpos : 0 < N 0)
    (hratio : Tendsto (fun k => (N (k + 1) : ℝ) / (N k : ℝ)) atTop (𝓝 1)) :
    ∃ c : ℝ, 0 < c ∧ ∃ ip im : ℕ → ℕ, StrictMono ip ∧ StrictMono im ∧
      (∀ j, c < Real.rpow (N (ip j) : ℝ) (1 - zeroAbscissa) * Real.log (N (ip j) : ℝ) *
        robinLogMargin (strictInteger (firstLayerPrice ((N (ip j) : ℝ) + 1)))) ∧
      (∀ j, Real.rpow (N (im j) : ℝ) (1 - zeroAbscissa) * Real.log (N (im j) : ℝ) *
        robinLogMargin (strictInteger (firstLayerPrice ((N (im j) : ℝ) + 1))) < -c) := by
  let y : ℕ → ℝ := fun k => Real.log (N k : ℝ)
  let a : ℕ → ℝ := fun k =>
    Real.rpow (N k : ℝ) (1 - ρ.re) * Real.log (N k : ℝ) *
      robinLogMargin (strictInteger (firstLayerPrice ((N k : ℝ) + 1)))
  let L : ℂ := -(analyticOrderNatAt riemannZeta ρ : ℂ) / (ρ * (1 - ρ))
  have hstrip (z : ℂ) (hz : IsNontrivialZero z) : z.re ≤ ρ.re :=
    (zero_re_le_abscissa hz).trans_eq hρΘ.symm
  have hx : Tendsto (fun k => (N k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hN.tendsto_atTop
  have hy : Tendsto y atTop atTop := Real.tendsto_log_atTop.comp hx
  have hm : StrictMono y := by
    intro i j hij
    exact Real.log_lt_log (Nat.cast_pos.mpr (hpos.trans_le (hN.monotone (Nat.zero_le i))))
      (Nat.cast_lt.mpr (hN hij))
  have hreal_ne := riemannZeta_ne_zero_of_real_mem_Ioo ρ.re hρ.2.1 hρ.2.2
  have horder_zero : analyticOrderNatAt riemannZeta (ρ.re : ℂ) = 0 := by
    have han := Zeta23.WeilEF.analyticAt_riemannZeta (Complex.ofReal_ne_one.mpr hρ.2.2.ne)
    have horder := han.analyticOrderAt_eq_zero.mpr hreal_ne
    simp [analyticOrderNatAt, horder]
  have hzero : Tendsto (average y (fun k => (a k : ℂ))) atTop (𝓝 0) := by
    have h := actual_canonical_samples_fourier_recovery (ρ.re : ℂ)
      (by simpa only [Complex.ofReal_re] using hhalf.le)
      (by simpa only [Complex.ofReal_re] using hρ.2.2)
      (fun z hz => by simpa only [Complex.ofReal_re] using hstrip z hz) hN hpos hratio
    simpa only [Complex.ofReal_re, Complex.ofReal_im, if_neg hhalf.ne', Complex.ofReal_zero,
      sub_zero, neg_zero, phase, mul_zero, zero_mul, Complex.exp_zero, mul_one, horder_zero,
      Nat.cast_zero, zero_div, a, y] using h
  have htwist : Tendsto (average y (fun k => (a k : ℂ) * phase (-ρ.im) (y k))) atTop
      (𝓝 L) := by
    simpa only [if_neg hhalf.ne', Complex.ofReal_zero, sub_zero, a, y, L] using
      actual_canonical_samples_fourier_recovery ρ hhalf.le hρ.2.2 hstrip hN hpos hratio
  have hL : L ≠ 0 := by
    obtain ⟨m, hmultiplicity⟩ := exists_multiplicity hρ
    have horder : analyticOrderNatAt riemannZeta ρ = m := by
      have h := (hasZetaZeroMultiplicity_iff_analyticOrderAt_eq hρ).mp hmultiplicity
      simp [analyticOrderNatAt, h]
    have hmcast : (m : ℂ) ≠ 0 := by exact_mod_cast hmultiplicity.1.ne'
    have hρ0 : ρ ≠ 0 := by
      intro he
      exact hρ.2.1.ne' (by simpa only [Complex.zero_re] using congrArg Complex.re he)
    have hρ1 : ρ ≠ 1 := by
      intro he
      exact hρ.2.2.ne (by simpa only [Complex.one_re] using congrArg Complex.re he)
    dsimp only [L]
    rw [horder]
    exact div_ne_zero (neg_ne_zero.mpr hmcast) (mul_ne_zero hρ0 (sub_ne_zero.mpr hρ1.symm))
  have hphase (k : ℕ) : ‖phase (-ρ.im) (y k)‖ = 1 := by
    rw [phase, mul_assoc, ← Complex.ofReal_mul, Complex.norm_exp_I_mul_ofReal]
  let c : ℝ := ‖L‖ / 4
  have hnorm : 0 < ‖L‖ := norm_pos_iff.mpr hL
  have hc : 0 < c := by dsimp only [c]; linarith only [hnorm]
  have hcL : 2 * c < ‖L‖ := by dsimp only [c]; linarith only [hnorm]
  obtain ⟨hp, hn⟩ := frequently_two_signs_of_zero_mean hm hy hphase hzero htwist hc.le hcL
  obtain ⟨ip, hip, hp⟩ := extraction_of_frequently_atTop hp
  obtain ⟨im, him, hn⟩ := extraction_of_frequently_atTop hn
  exact ⟨c, hc, ip, im, hip, him, by simpa only [a, hρΘ] using hp,
    by simpa only [a, hρΘ] using hn⟩

/-- The same type of index subsequences give divergence to opposite infinities
at every exponent strictly larger than `1 - zeroAbscissa`. -/
theorem actual_attained_canonical_divergent_subsequences {ρ : ℂ}
    (hρ : IsNontrivialZero ρ) (hhalf : 1 / 2 < ρ.re) (hρΘ : ρ.re = zeroAbscissa)
    {N : ℕ → ℕ} (hN : StrictMono N) (hpos : 0 < N 0)
    (hratio : Tendsto (fun k => (N (k + 1) : ℝ) / (N k : ℝ)) atTop (𝓝 1))
    {α : ℝ} (hα : 1 - zeroAbscissa < α) :
    ∃ ip im : ℕ → ℕ, StrictMono ip ∧ StrictMono im ∧
      Tendsto (fun j => Real.rpow (N (ip j) : ℝ) α * Real.log (N (ip j) : ℝ) *
        robinLogMargin (strictInteger (firstLayerPrice ((N (ip j) : ℝ) + 1)))) atTop atTop ∧
      Tendsto (fun j => Real.rpow (N (im j) : ℝ) α * Real.log (N (im j) : ℝ) *
        robinLogMargin (strictInteger (firstLayerPrice ((N (im j) : ℝ) + 1)))) atTop atBot := by
  obtain ⟨c, hc, ip, im, hip, him, hp, hn⟩ :=
    actual_attained_canonical_critical_subsequences hρ hhalf hρΘ hN hpos hratio
  let q : ℝ := α - (1 - zeroAbscissa)
  have hq : 0 < q := sub_pos.mpr hα
  have hx : Tendsto (fun k => (N k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hN.tendsto_atTop
  have hxpos (k : ℕ) : 0 < (N k : ℝ) :=
    Nat.cast_pos.mpr (hpos.trans_le (hN.monotone (Nat.zero_le k)))
  have hscale (k : ℕ) :
      Real.rpow (N k : ℝ) α * Real.log (N k : ℝ) *
        robinLogMargin (strictInteger (firstLayerPrice ((N k : ℝ) + 1))) =
      Real.rpow (N k : ℝ) q *
        (Real.rpow (N k : ℝ) (1 - zeroAbscissa) * Real.log (N k : ℝ) *
          robinLogMargin (strictInteger (firstLayerPrice ((N k : ℝ) + 1)))) := by
    have he : α = q + (1 - zeroAbscissa) := by
      dsimp only [q]
      ring
    have hpow := (congrArg (Real.rpow (N k : ℝ)) he).trans
      (Real.rpow_add (hxpos k) q (1 - zeroAbscissa))
    simp only [hpow, mul_assoc]
  have hfactor (i : ℕ → ℕ) (hi : StrictMono i) :
      Tendsto (fun j => Real.rpow (N (i j) : ℝ) q) atTop atTop :=
    ((tendsto_rpow_atTop hq).comp hx).comp hi.tendsto_atTop
  refine ⟨ip, im, hip, him, ?_, ?_⟩
  · refine tendsto_atTop_mono (fun j => ?_) ((hfactor ip hip).atTop_mul_const hc)
    rw [hscale]
    exact mul_le_mul_of_nonneg_left (hp j).le (Real.rpow_pos_of_pos (hxpos (ip j)) q).le
  · refine tendsto_atBot_mono (fun j => ?_)
      ((hfactor im him).atTop_mul_const_of_neg (neg_neg_of_pos hc))
    rw [hscale]
    exact mul_le_mul_of_nonneg_left (hn j).le (Real.rpow_pos_of_pos (hxpos (im j)) q).le

end D5.S3.Arith.Robin.PriceRecord.RobinMeshAttainedSigns
