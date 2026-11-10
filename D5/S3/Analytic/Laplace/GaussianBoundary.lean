/- GID: D5/S3/Analytic/Laplace/GaussianBoundary
   generality: G
   mirror-B: D5/B/S3/Analytic/Laplace/GaussianBoundary
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Gaussian inversion separates paired spectral poles from an exponentially small holomorphic remainder. -/

import D5.S3.Analytic.Fourier.GaussianKernel
import D5.S3.Analytic.Oscillation.GaussianSpectrum
import D5.S3.Analytic.Laplace.GaussianStripControl
import D5.S3.Analytic.Laplace.GaussianBoundaryPoles
import D5.S3.Analytic.Laplace.GaussianBoundaryCorrections
import D5.S3.Analytic.Laplace.GaussianBoundaryContour
import D5.S3.Analytic.Laplace.QuantitativeFejerBoundary.DampedIdentity

/-! Gaussian boundary inversion for paired Laplace transforms. -/

namespace D5.S3.Analytic.Laplace.GaussianBoundary

open D5.S3.Analytic.Fourier.GaussianKernel
open D5.S3.Analytic.Oscillation.OrdinateCounting
open D5.S3.Analytic.Oscillation.GaussianSpectrum
open D5.S3.Analytic.Laplace.PairedPoleRegularity
open D5.S3.Analytic.Laplace.QuantitativeFejerBoundary
open MeasureTheory Set Filter
open scoped Topology BigOperators

noncomputable section

set_option backward.isDefEq.respectTransparency false

private lemma gaussian_fubini {f : ℝ → ℝ} {M : ℝ} (hM : 0 < M) (c y : ℝ)
    (hi : IntegrableOn (fun u => f u * Real.exp (-c * u)) (Ici 0)) :
    IntegrableOn (fun u => f u * q M (y - u)) (Ici 0) ∧
    (gaussianAverage f M y : ℂ) = (1 / (2 * Real.pi) : ℂ) *
      ∫ t : ℝ, laplace f ((c : ℂ) + t * Complex.I) * Complex.exp
        (((c : ℂ) + t * Complex.I) * y +
          ((c : ℂ) + t * Complex.I) ^ 2 / (2 * M ^ 2)) := by
  let E : ℝ → ℂ := fun t => Complex.exp
    (((c : ℂ) + t * Complex.I) * y +
      ((c : ℂ) + t * Complex.I) ^ 2 / (2 * M ^ 2))
  let F : ℝ → ℝ → ℂ := fun u t =>
    ((f u * Real.exp (-c * u) : ℝ) : ℂ) * E t *
      Complex.exp (-Complex.I * (t : ℂ) * u)
  have hFi : Integrable (Function.uncurry F) ((volume.restrict (Ici 0)).prod volume) := by
    apply (hi.ofReal.mul_prod (q_bromwich_integrable hM c y)).mul_bdd (c := 1)
    · exact (show Continuous (fun p : ℝ × ℝ =>
          Complex.exp (-Complex.I * (p.2 : ℂ) * p.1)) by fun_prop).aestronglyMeasurable
    · filter_upwards with p
      simp [Complex.norm_exp, Complex.mul_re, Complex.mul_im]
  have he (u t : ℝ) : F u t = (f u : ℂ) * Complex.exp
      (((c : ℂ) + t * Complex.I) * (y - u) +
        ((c : ℂ) + t * Complex.I) ^ 2 / (2 * M ^ 2)) := by
    dsimp [F, E]
    rw [Complex.ofReal_mul, Complex.ofReal_exp, mul_assoc, ← Complex.exp_add,
      mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  have he1 (u : ℝ) : (1 / (2 * Real.pi) : ℂ) * (∫ t, F u t) =
      (f u * q M (y - u) : ℝ) := by
    simp_rw [he]
    rw [integral_const_mul, ← mul_assoc, mul_comm _ (f u : ℂ), mul_assoc,
      show (y : ℂ) - u = ((y - u : ℝ) : ℂ) by push_cast; rfl,
      ← q_bromwich hM c (y - u), Complex.ofReal_mul]
  have he2 (t : ℝ) : (∫ u in Ici 0, F u t) =
      laplace f ((c : ℂ) + t * Complex.I) * E t := by
    unfold laplace
    rw [← integral_mul_const]
    apply integral_congr_ae
    filter_upwards with u
    dsimp [F]
    rw [Complex.ofReal_mul, Complex.ofReal_exp]
    have hex : Complex.exp ((-c * u : ℝ) : ℂ) *
        Complex.exp (-Complex.I * (t : ℂ) * u) =
        Complex.exp (-((c : ℂ) + t * Complex.I) * u) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    calc
      _ = (f u : ℂ) * (Complex.exp ((-c * u : ℝ) : ℂ) *
          Complex.exp (-Complex.I * (t : ℂ) * u)) * E t := by ring
      _ = _ := by rw [hex]
  have hreal : IntegrableOn (fun u => f u * q M (y - u)) (Ici 0) := by
    have hh := (hFi.integral_prod_left.const_mul (1 / (2 * Real.pi) : ℂ)).re
    exact hh.congr (ae_of_all _ (fun u => by
      change ((1 / (2 * Real.pi) : ℂ) * (∫ t, F u t)).re = _
      rw [he1]; simp))
  refine ⟨hreal, ?_⟩
  change Complex.ofRealCLM (∫ u in Ici 0, f u * q M (y - u)) = _
  rw [← Complex.ofRealCLM.integral_comp_comm hreal]
  calc
    _ = ∫ u in Ici 0, (1 / (2 * Real.pi) : ℂ) * ∫ t, F u t := by
      apply integral_congr_ae
      exact ae_of_all _ (fun u => (he1 u).symm)
    _ = _ := by
      rw [integral_const_mul, integral_integral_swap hFi]
      simp_rw [he2]
      rfl


private lemma finite_pole_inversion (S : Spectrum) {M : ℝ} (hM : 0 < M)
    (T y : ℝ) :
    (1 / (2 * Real.pi) : ℂ) *
      ∫ t : ℝ, (-(1 / 2 : ℂ) * ∑ j ∈ S.cut T,
        poleTerm S j ((3 / 4 : ℂ) + t * Complex.I)) * Complex.exp
          (((3 / 4 : ℂ) + t * Complex.I) * y +
            ((3 / 4 : ℂ) + t * Complex.I) ^ 2 / (2 * M ^ 2)) =
      -(↑(∑ j ∈ S.cut T, (S.mult j : ℝ) *
        ∫ u in Ici 0, Real.cos (S.gamma j * u) * q M (y - u)) : ℂ) := by
  classical
  have hi (j : S.index) : IntegrableOn
      (fun u => Real.cos (S.gamma j * u) * q M (y - u)) (Ici 0) := by
    exact ((q_laws hM).1.comp_sub_left y).integrableOn.bdd_mul (by fun_prop)
      (ae_of_all _ (fun u => Real.abs_cos_le_one _))
  have havg : gaussianAverage (polePolynomial S (T / 2)) M y =
      -∑ j ∈ S.cut T, (S.mult j : ℝ) *
        ∫ u in Ici 0, Real.cos (S.gamma j * u) * q M (y - u) := by
    unfold gaussianAverage polePolynomial
    simp only [show 2 * (T / 2) = T by ring, neg_mul, Finset.sum_mul]
    simp_rw [mul_assoc]
    rw [integral_neg, integral_finsetSum _ (fun j _ => (hi j).const_mul _)]
    simp_rw [integral_const_mul]
  have h := (gaussian_fubini hM (3 / 4) y
    (polePolynomial_convergence S (T / 2) (by norm_num : (0 : ℝ) < 3 / 4))).2
  rw [havg] at h
  have hLap (t : ℝ) := polePolynomial_laplace S (T / 2)
    (s := (((3 / 4 : ℝ) : ℂ)) + t * Complex.I) (by norm_num)
  simp only [show 2 * (T / 2) = T by ring] at hLap
  simp_rw [hLap] at h
  norm_num only [Complex.ofReal_div, Complex.ofReal_ofNat] at h
  simpa only [Complex.ofReal_neg] using h.symm


private lemma infinite_pole_inversion (S : Spectrum) (hN : CountAsymptotic S)
    {M y : ℝ} (hM : 1 ≤ M) (hy : 1 ≤ y) :
    (1 / (2 * Real.pi) : ℂ) * (-(1 / 2 : ℂ) *
      ∫ t : ℝ, (∑' j : S.index, poleTerm S j ((3 / 4 : ℂ) + t * Complex.I)) *
        Complex.exp (((3 / 4 : ℂ) + t * Complex.I) * y +
          ((3 / 4 : ℂ) + t * Complex.I) ^ 2 / (2 * M ^ 2))) =
      -(↑(∑' j : S.index, (S.mult j : ℝ) *
        ∫ u in Ici 0, Real.cos (S.gamma j * u) * q M (y - u)) : ℂ) := by
  have hM0 : 0 < M := by linarith
  have hleft := ((pole_gaussian_cutoff_tendsto S hN hM0 y).const_mul
    (-(1 / 2 : ℂ))).const_mul (1 / (2 * Real.pi) : ℂ)
  have hright := (Complex.continuous_ofReal.tendsto _).comp
    (((gaussian_halfline_summable S hN hM hy).hasSum.comp
      (spectrum_cut_tendsto S)).neg)
  simp only [Complex.ofReal_neg] at hright
  apply tendsto_nhds_unique hleft
  apply hright.congr'
  exact Eventually.of_forall (fun T => by
    simpa only [Function.comp_apply, mul_assoc, integral_const_mul, Complex.ofReal_neg] using
      (finite_pole_inversion S hM0 T y).symm)

/-- A Gaussian average of paired Laplace data cancels the Gaussian cosine spectrum,
leaving a uniform exponentially decaying remainder. -/
theorem gaussian_boundary
    (S : Spectrum) (hN : CountAsymptotic S)
    {f : ℝ → ℝ} (D : PairedLaplaceData S f 2)
    (hstrip : GaussianStripControl D.J) :
    ∃ C : ℝ, 0 < C ∧ ∀ M y : ℝ, 1 ≤ M → 1 ≤ y →
      IntegrableOn (fun u => f u * q M (y - u)) (Set.Ici 0) ∧
      |gaussianAverage f M y + gaussianCos S M y| ≤
        C * M ^ 3 * Real.exp (-y / 6) := by
  obtain ⟨A, hA, hreg⟩ := gaussian_regular_bound hstrip
  obtain ⟨B, hB, hcorr⟩ := gaussian_corrections_bound S hN
  refine ⟨A + B, by positivity, fun M y hM hy => ?_⟩
  have hM0 : 0 < M := by linarith
  have hfub := gaussian_fubini hM0 (3 / 4) y
    (D.initial_convergence (3 / 4) (by norm_num))
  refine ⟨hfub.1, ?_⟩
  let E : ℝ → ℂ := fun t => Complex.exp
    (((3 / 4 : ℂ) + t * Complex.I) * y +
      ((3 / 4 : ℂ) + t * Complex.I) ^ 2 / (2 * M ^ 2))
  let P : ℝ → ℂ := fun t => ∑' j : S.index,
    poleTerm S j ((3 / 4 : ℂ) + t * Complex.I)
  let R : ℂ := (1 / (2 * Real.pi) : ℂ) *
    ∫ t : ℝ, D.J ((3 / 4 : ℂ) + t * Complex.I) * E t
  let Bsum : ℝ := ∑' j : S.index,
    (S.mult j : ℝ) * gaussianCorrection M y (S.gamma j)
  have hiP : Integrable (fun t => P t * E t) :=
    pole_gaussian_tsum_integrable S hN hM0 y
  have hiJ : Integrable (fun t : ℝ => D.J ((3 / 4 : ℂ) + t * Complex.I) * E t) := by
    simpa only [Complex.ofReal_div, Complex.ofReal_ofNat] using
      regular_vertical_integrable hstrip hM0 y
        (c := 3 / 4) (by norm_num) le_rfl
  have hinv : (gaussianAverage f M y : ℂ) =
      (1 / (2 * Real.pi) : ℂ) * (-(1 / 2 : ℂ) * ∫ t, P t * E t) + R := by
    rw [hfub.2]
    norm_num only [Complex.ofReal_div, Complex.ofReal_ofNat]
    have heq (t : ℝ) :
        laplace f ((3 / 4 : ℂ) + t * Complex.I) * E t =
          -(1 / 2 : ℂ) * (P t * E t) +
            D.J ((3 / 4 : ℂ) + t * Complex.I) * E t := by
      rw [D.identity _ (by norm_num) (by norm_num)]
      dsimp [P]
      ring
    change (1 / (2 * Real.pi) : ℂ) *
      (∫ t : ℝ, laplace f ((3 / 4 : ℂ) + t * Complex.I) * E t) = _
    simp_rw [heq]
    rw [integral_add (hiP.const_mul _) hiJ, integral_const_mul]
    dsimp [R]
    ring
  have hsum : (∑' j : S.index, (S.mult j : ℝ) *
      ∫ u in Ici 0, Real.cos (S.gamma j * u) * q M (y - u)) =
        gaussianCos S M y - Bsum := by
    simp_rw [gaussian_cos_halfline hM0, mul_sub, ← mul_assoc]
    exact (gaussianCos_summable S hN hM0 y).tsum_sub
      (gaussian_corrections_summable S hN hM hy)
  have hidentity : ((gaussianAverage f M y + gaussianCos S M y : ℝ) : ℂ) =
      (Bsum : ℂ) + R := by
    rw [Complex.ofReal_add, hinv]
    change (1 / (2 * Real.pi) : ℂ) * (-(1 / 2 : ℂ) *
      (∫ t : ℝ, (∑' j : S.index, poleTerm S j ((3 / 4 : ℂ) + t * Complex.I)) * E t)) +
        R + (gaussianCos S M y : ℂ) = _
    rw [infinite_pole_inversion S hN hM hy, hsum]
    push_cast
    ring
  have hR : ‖R‖ ≤ A * M ^ 3 * Real.exp (-y / 6) := by
    simpa only [R, E, Complex.ofReal_div, Complex.ofReal_ofNat] using hreg M y hM
  have hBsum : |Bsum| ≤ B * M ^ 3 * Real.exp (-y / 6) := hcorr M y hM hy
  calc
    _ = ‖((gaussianAverage f M y + gaussianCos S M y : ℝ) : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs]
    _ = ‖(Bsum : ℂ) + R‖ := congrArg norm hidentity
    _ ≤ |Bsum| + ‖R‖ := by simpa using norm_add_le (Bsum : ℂ) R
    _ ≤ B * M ^ 3 * Real.exp (-y / 6) + A * M ^ 3 * Real.exp (-y / 6) :=
      add_le_add hBsum hR
    _ = (A + B) * M ^ 3 * Real.exp (-y / 6) := by ring

end
end D5.S3.Analytic.Laplace.GaussianBoundary
