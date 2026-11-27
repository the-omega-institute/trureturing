/- GID: D5/S3/Weil/ZetaPntBounds/MobiusDyadicBoundaryWindows
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaPntBounds/MobiusDyadicBoundaryWindows
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Critical signed dyadic Möbius energy bounds the sum of contributions from disjoint zero windows. -/

import D5.S3.Arith.Robin.ForwardKernel.KappaGap
import D5.S3.Weil.ZetaPntBounds.MobiusDyadicBoundary
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
Each zero gives a lower bound on the weighted reciprocal mass on its ordinate window.
For disjoint windows these bounds sum to at most the total reciprocal mass.
The boundary Möbius energy estimate supplies a bound on that mass for `riemannZeta`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Filter MeasureTheory Set
open scoped BigOperators Function

namespace D5.S3.Weil.ZetaPntBounds.MobiusDyadicBoundaryWindows

open D5.S3.Arith.Robin.ForwardKernel.KappaGap (zeroAbscissa zero_re_le_abscissa)
open D5.S3.Weil.Mertens.MobiusDyadicEnergy (mobiusDyadicDifference)
open D5.S3.Weil.ZeroSum (IsNontrivialZero)
open D5.S3.Weil.ZetaPntBounds.MobiusDyadicBoundary
  (weighted_reciprocal_zeta_sq_bound_of_mobiusDyadicEnergy)
open D5.S3.Weil.ZetaPntBounds.MobiusPartialSumL2Divergence (exists_nontrivial_zero_re_ge_half)

/-- The open interval of ordinates centered at the zero with radius $\theta - \Re\rho$. -/
def window (θ : ℝ) (ρ : ℂ) : Set ℝ :=
  Ioo (ρ.im - (θ - ρ.re)) (ρ.im + (θ - ρ.re))

/-- The closed rectangle between the zero and the line of real part `θ`, with imaginary part
in the closed interval with the same endpoints as the ordinate window. -/
def rectangle (θ : ℝ) (ρ : ℂ) : Set ℂ :=
  ({z : ℂ | ρ.re ≤ z.re} ∩ {z : ℂ | z.re ≤ θ}) ∩
    ({z : ℂ | ρ.im - (θ - ρ.re) ≤ z.im} ∩ {z : ℂ | z.im ≤ ρ.im + (θ - ρ.re)})

/-- The weighted reciprocal square of `f` on the vertical line of real part `θ`. -/
def reciprocalDensity (f : ℂ → ℂ) (θ y : ℝ) : ℝ :=
  1 / ((1 + |y|) ^ 2 * ‖f ((θ : ℂ) + (y : ℂ) * I)‖ ^ 2)

private theorem norm_le_of_zero_window {f : ℂ → ℂ} {θ M y : ℝ} {ρ : ℂ}
    (hρ : f ρ = 0) (hgap : ρ.re < θ) (hM : 0 ≤ M)
    (hdiff : ∀ z ∈ rectangle θ ρ, DifferentiableAt ℂ f z)
    (hderiv : ∀ z ∈ rectangle θ ρ, ‖deriv f z‖ ≤ M)
    (hy : y ∈ window θ ρ) :
    ‖f ((θ : ℂ) + (y : ℂ) * I)‖ ≤ 2 * (θ - ρ.re) * M := by
  let z : ℂ := (θ : ℂ) + (y : ℂ) * I
  let δ : ℝ := θ - ρ.re
  have hd : 0 < δ := sub_pos.mpr hgap
  have hzr : z.re = θ := by simp [z, Complex.mul_re]
  have hzi : z.im = y := by simp [z, Complex.mul_im]
  have hconv : Convex ℝ (rectangle θ ρ) :=
    ((convex_halfSpace_re_ge ρ.re).inter (convex_halfSpace_re_le θ)).inter
      ((convex_halfSpace_im_ge _).inter (convex_halfSpace_im_le _))
  have hyLeft : ρ.im - δ < y := hy.1
  have hyRight : y < ρ.im + δ := hy.2
  have hmemρ : ρ ∈ rectangle θ ρ := by
    change (ρ.re ≤ ρ.re ∧ ρ.re ≤ θ) ∧ (ρ.im - δ ≤ ρ.im ∧ ρ.im ≤ ρ.im + δ)
    exact ⟨⟨le_rfl, hgap.le⟩, by linarith only [hd], by linarith only [hd]⟩
  have hmemz : z ∈ rectangle θ ρ := by
    change (ρ.re ≤ z.re ∧ z.re ≤ θ) ∧ (ρ.im - δ ≤ z.im ∧ z.im ≤ ρ.im + δ)
    rw [hzr, hzi]
    exact ⟨⟨hgap.le, le_rfl⟩, hyLeft.le, hyRight.le⟩
  have hdist : ‖z - ρ‖ ≤ 2 * δ := by
    refine (Complex.norm_le_abs_re_add_abs_im (z - ρ)).trans ?_
    rw [Complex.sub_re, Complex.sub_im, hzr, hzi]
    change |δ| + |y - ρ.im| ≤ 2 * δ
    rw [abs_of_pos hd]
    have ha : |y - ρ.im| ≤ δ := abs_le.mpr
      ⟨by linarith only [hyLeft], by linarith only [hyRight]⟩
    linarith only [ha]
  calc
    ‖f ((θ : ℂ) + (y : ℂ) * I)‖ = ‖f z - f ρ‖ := by
      rw [hρ, sub_zero]
    _ ≤ M * ‖z - ρ‖ := hconv.norm_image_sub_le_of_norm_deriv_le hdiff hderiv hmemρ hmemz
    _ ≤ M * (2 * δ) := mul_le_mul_of_nonneg_left hdist hM
    _ = 2 * (θ - ρ.re) * M := mul_comm M (2 * δ)

private theorem window_mass_lower {f : ℂ → ℂ} {θ M : ℝ} {ρ : ℂ}
    (hρ : f ρ = 0) (hgap : ρ.re < θ) (hgap_le : θ - ρ.re ≤ 1) (hM : 0 < M)
    (hzero : ∀ y ∈ window θ ρ, f ((θ : ℂ) + (y : ℂ) * I) ≠ 0)
    (hdiff : ∀ z ∈ rectangle θ ρ, DifferentiableAt ℂ f z)
    (hderiv : ∀ z ∈ rectangle θ ρ, ‖deriv f z‖ ≤ M)
    (hInt : IntegrableOn (reciprocalDensity f θ) (window θ ρ)) :
    1 / (8 * (θ - ρ.re) * M ^ 2 * (1 + |ρ.im|) ^ 2) ≤
      ∫ y in window θ ρ, reciprocalDensity f θ y := by
  let δ := θ - ρ.re
  let B := (16 : ℝ) * δ ^ 2 * M ^ 2 * (1 + |ρ.im|) ^ 2
  have hd : 0 < δ := sub_pos.mpr hgap
  have hd₁ : δ ≤ 1 := hgap_le
  have hpoint (y : ℝ) (hy : y ∈ window θ ρ) :
      1 / B ≤ reciprocalDensity f θ y := by
    have hbound : ‖f ((θ : ℂ) + (y : ℂ) * I)‖ ≤ 2 * δ * M :=
      norm_le_of_zero_window hρ hgap hM.le hdiff hderiv hy
    have hy₀ : |y - ρ.im| ≤ δ := by
      have hleft : ρ.im - δ < y := hy.1
      have hright : y < ρ.im + δ := hy.2
      exact abs_le.mpr ⟨by linarith only [hleft], by linarith only [hright]⟩
    have hyabs : |y| ≤ |ρ.im| + δ := by
      calc
        |y| = |ρ.im + (y - ρ.im)| := by rw [show ρ.im + (y - ρ.im) = y by ring]
        _ ≤ |ρ.im| + |y - ρ.im| := abs_add_le _ _
        _ ≤ _ := add_le_add le_rfl hy₀
    have hyd : 1 + |y| ≤ 2 * (1 + |ρ.im|) := by
      linarith only [hyabs, hd₁, abs_nonneg ρ.im]
    have hden : (1 + |y|) ^ 2 * ‖f ((θ : ℂ) + (y : ℂ) * I)‖ ^ 2 ≤ B := by
      calc
        _ ≤ (2 * (1 + |ρ.im|)) ^ 2 * (2 * δ * M) ^ 2 := by
          exact mul_le_mul
            (pow_le_pow_left₀ (by positivity) hyd 2)
            (pow_le_pow_left₀ (norm_nonneg _) hbound 2) (by positivity) (by positivity)
        _ = B := by
          dsimp only [B]
          ring
    have hpos : 0 < (1 + |y|) ^ 2 * ‖f ((θ : ℂ) + (y : ℂ) * I)‖ ^ 2 :=
      mul_pos (by positivity) (pow_pos (norm_pos_iff.mpr (hzero y hy)) _)
    exact one_div_le_one_div_of_le hpos hden
  have hfinite : volume (window θ ρ) ≠ ⊤ :=
    (measure_Ioo_lt_top (μ := (volume : Measure ℝ)) (a := ρ.im - δ) (b := ρ.im + δ)).ne
  have hconst : IntegrableOn (fun _ : ℝ => 1 / B) (window θ ρ) :=
    integrableOn_const hfinite
  have hm : MeasurableSet (window θ ρ) := measurableSet_Ioo
  calc
    _ = ∫ _ in window θ ρ, 1 / B := by
      rw [setIntegral_const, smul_eq_mul]
      change 1 / (8 * δ * M ^ 2 * (1 + |ρ.im|) ^ 2) =
        volume.real (Ioo (ρ.im - δ) (ρ.im + δ)) * (1 / B)
      have hendpoints : ρ.im - δ ≤ ρ.im + δ := by linarith only [hd]
      rw [Real.volume_real_Ioo_of_le hendpoints]
      dsimp only [B]
      have hweight : 0 < 1 + |ρ.im| := by positivity
      field_simp [hd.ne', hM.ne', hweight.ne'] <;> ring
    _ ≤ _ := setIntegral_mono_on hconst hInt hm hpoint

/-- The sum of the local lower bounds for a finite family of zeros with disjoint ordinate
windows is bounded by the total weighted reciprocal mass on the zero-free line.
The derivative bounds and differentiability are required on the corresponding closed
rectangles. -/
theorem finite_gap_mass_le_integral_reciprocalDensity {ι : Type*} (t : Finset ι)
    (f : ℂ → ℂ) (θ : ℝ) (ρ : ι → ℂ) (M : ι → ℝ)
    (hρ : ∀ i ∈ t, f (ρ i) = 0)
    (hgap : ∀ i ∈ t, (ρ i).re < θ) (hgap_le : ∀ i ∈ t, θ - (ρ i).re ≤ 1)
    (hM : ∀ i ∈ t, 0 < M i)
    (hzero : ∀ y : ℝ, f ((θ : ℂ) + (y : ℂ) * I) ≠ 0)
    (hdiff : ∀ i ∈ t, ∀ z ∈ rectangle θ (ρ i), DifferentiableAt ℂ f z)
    (hderiv : ∀ i ∈ t, ∀ z ∈ rectangle θ (ρ i), ‖deriv f z‖ ≤ M i)
    (hdisjoint : Set.Pairwise (↑t) (Disjoint on fun i => window θ (ρ i)))
    (hInt : Integrable (reciprocalDensity f θ)) :
    (∑ i ∈ t, 1 / (8 * (θ - (ρ i).re) * (M i) ^ 2 * (1 + |(ρ i).im|) ^ 2)) ≤
      ∫ y, reciprocalDensity f θ y := by
  let windows : ι → Set ℝ := fun i => window θ (ρ i)
  have hmeas (i : ι) : MeasurableSet (windows i) := measurableSet_Ioo
  calc
    _ ≤ ∑ i ∈ t, ∫ y in windows i, reciprocalDensity f θ y :=
      Finset.sum_le_sum fun i hi => window_mass_lower (hρ i hi) (hgap i hi)
        (hgap_le i hi) (hM i hi) (fun y _ => hzero y) (hdiff i hi) (hderiv i hi)
        hInt.integrableOn
    _ = ∫ y in ⋃ i ∈ t, windows i, reciprocalDensity f θ y :=
      (integral_biUnion_finset (s := windows) (f := reciprocalDensity f θ)
        t (fun i _ => hmeas i) hdisjoint (fun _ _ => hInt.integrableOn)).symm
    _ ≤ ∫ y, reciprocalDensity f θ y :=
      setIntegral_le_integral hInt (ae_of_all _ fun _ => by
        unfold reciprocalDensity
        positivity)

/-- Critical energy bounds the sum of the reciprocal spikes from a finite family of
zeros with disjoint ordinate windows. Each derivative bound holds on the corresponding
closed rectangle. -/
theorem finite_gap_mass_le_of_critical_energy {ι : Type} (t : Finset ι)
    (ρ : ι → ℂ) (M : ι → ℝ) (hΘ : zeroAbscissa < 1)
    (hunattained : ∀ z : ℂ, IsNontrivialZero z → z.re ≠ zeroAbscissa)
    (hρ : ∀ i ∈ t, IsNontrivialZero (ρ i)) (hM : ∀ i ∈ t, 0 < M i)
    (hderiv : ∀ i ∈ t, ∀ z ∈ rectangle zeroAbscissa (ρ i), ‖deriv riemannZeta z‖ ≤ M i)
    (hdisjoint : Set.Pairwise (↑t) (Disjoint on fun i => window zeroAbscissa (ρ i)))
    (hE : IntegrableOn
      (fun x : ℝ => mobiusDyadicDifference x ^ 2 * x ^ (-(2 * zeroAbscissa - 1))) (Ioi 1)) :
    (∑ i ∈ t, 1 / (8 * (zeroAbscissa - (ρ i).re) * (M i) ^ 2 * (1 + |(ρ i).im|) ^ 2)) ≤
      4 + 4 * Real.pi *
        (∫ x in Ioi (1 : ℝ), mobiusDyadicDifference x ^ 2 * x ^ (-(2 * zeroAbscissa - 1))) /
        (1 - (2 : ℝ) ^ (zeroAbscissa - 1)) ^ 2 := by
  obtain ⟨r, hr, hh⟩ := exists_nontrivial_zero_re_ge_half
  have hΘhalf : (1 / 2 : ℝ) ≤ zeroAbscissa := hh.trans (zero_re_le_abscissa hr)
  have hzero (y : ℝ) : riemannZeta ((zeroAbscissa : ℂ) + (y : ℂ) * I) ≠ 0 := by
    let z : ℂ := (zeroAbscissa : ℂ) + (y : ℂ) * I
    have hre : z.re = zeroAbscissa := by simp [z, Complex.mul_re]
    change riemannZeta z ≠ 0
    intro hz
    have hzr₀ : 0 < z.re := by
      rw [hre]
      linarith only [hΘhalf]
    have hzr₁ : z.re < 1 := by simpa only [hre] using hΘ
    exact hunattained z ⟨hz, hzr₀, hzr₁⟩ hre
  obtain ⟨hInt, hbound⟩ :=
    weighted_reciprocal_zeta_sq_bound_of_mobiusDyadicEnergy (θ := zeroAbscissa)
      (by linarith only [hΘhalf]) (by linarith only [hΘ])
      hΘ.ne hzero hE
  change Integrable (reciprocalDensity riemannZeta zeroAbscissa) at hInt
  change (∫ y, reciprocalDensity riemannZeta zeroAbscissa y) ≤ _ at hbound
  have hgap (i : ι) (hi : i ∈ t) : (ρ i).re < zeroAbscissa :=
    lt_of_le_of_ne (zero_re_le_abscissa (hρ i hi)) (hunattained _ (hρ i hi))
  have hgap_le (i : ι) (hi : i ∈ t) : zeroAbscissa - (ρ i).re ≤ 1 := by
    linarith only [hΘ, (hρ i hi).2.1]
  have hdiff (i : ι) (_hi : i ∈ t) (z : ℂ) (hz : z ∈ rectangle zeroAbscissa (ρ i)) :
      DifferentiableAt ℂ riemannZeta z := by
    apply differentiableAt_riemannZeta
    intro he
    have hre : z.re ≤ zeroAbscissa := hz.1.2
    rw [he, Complex.one_re] at hre
    linarith only [hre, hΘ]
  exact (finite_gap_mass_le_integral_reciprocalDensity t riemannZeta zeroAbscissa ρ M
    (fun i hi => (hρ i hi).1) hgap hgap_le hM hzero hdiff hderiv hdisjoint hInt).trans hbound

/-- The critical Möbius energy bounds the full series of gap contributions from
a family of zeros whose ordinate windows are pairwise disjoint. -/
theorem gap_mass_summable_of_critical_energy {ι : Type}
    (ρ : ι → ℂ) (M : ι → ℝ) (hΘ : zeroAbscissa < 1)
    (hunattained : ∀ z : ℂ, IsNontrivialZero z → z.re ≠ zeroAbscissa)
    (hρ : ∀ i, IsNontrivialZero (ρ i)) (hM : ∀ i, 0 < M i)
    (hderiv : ∀ i, ∀ z ∈ rectangle zeroAbscissa (ρ i), ‖deriv riemannZeta z‖ ≤ M i)
    (hdisjoint : Pairwise (Disjoint on fun i => window zeroAbscissa (ρ i)))
    (hE : IntegrableOn
      (fun x : ℝ => mobiusDyadicDifference x ^ 2 * x ^ (-(2 * zeroAbscissa - 1))) (Ioi 1)) :
    Summable (fun i => 1 / (8 * (zeroAbscissa - (ρ i).re) * (M i) ^ 2 * (1 + |(ρ i).im|) ^ 2)) ∧
    (∑' i, 1 / (8 * (zeroAbscissa - (ρ i).re) * (M i) ^ 2 * (1 + |(ρ i).im|) ^ 2)) ≤
      4 + 4 * Real.pi *
        (∫ x in Ioi (1 : ℝ), mobiusDyadicDifference x ^ 2 * x ^ (-(2 * zeroAbscissa - 1))) /
        (1 - (2 : ℝ) ^ (zeroAbscissa - 1)) ^ 2 := by
  have hnonneg (i : ι) :
      0 ≤ 1 / (8 * (zeroAbscissa - (ρ i).re) * (M i) ^ 2 * (1 + |(ρ i).im|) ^ 2) := by
    have hgap := sub_nonneg.mpr (zero_re_le_abscissa (hρ i))
    positivity
  have hfinite (t : Finset ι) :=
    finite_gap_mass_le_of_critical_energy t ρ M hΘ hunattained
      (fun i _ => hρ i) (fun i _ => hM i) (fun i _ => hderiv i)
      (hdisjoint.set_pairwise (↑t : Set ι)) hE
  have hs := summable_of_sum_le hnonneg hfinite
  exact ⟨hs, hs.tsum_le_of_sum_le hfinite⟩


end D5.S3.Weil.ZetaPntBounds.MobiusDyadicBoundaryWindows
