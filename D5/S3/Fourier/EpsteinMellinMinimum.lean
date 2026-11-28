/- GID: D5/S3/Fourier/EpsteinMellinMinimum
   generality: G
   mirror-B: D5/B/S3/Fourier/EpsteinMellinMinimum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Convergence and the real Mellin representation of planar Epstein zeta series. -/

import D5.S3.Fourier.ThetaLatticeMinimum
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Summable
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.NumberTheory.LSeries.MellinEqDirichlet
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Planar Epstein zeta and its Mellin integral -/

set_option autoImplicit false

open scoped BigOperators ENNReal
open MeasureTheory Set

namespace D5.S3.Fourier.PlanarTheta
noncomputable section

/-- Continuity in positive temperature. -/
theorem continuousOn_temperature (x : ℝ) {y : ℝ} (hy : 0 < y) :
    ContinuousOn (fun t => F t x y) (Set.Ioi 0) := by
  intro t ht
  have ht0 : 0 < t := ht
  have ht2 : 0 < t / 2 := by positivity
  have hc : ContinuousOn (fun s => F s x y) (Set.Ioi (t / 2)) := by
    apply continuousOn_tsum
    · intro v
      exact (by fun_prop : Continuous (fun s => Real.exp (-Real.pi * s * Q x y v))).continuousOn
    · exact summable (t / 2) x ht2 hy
    · intro v s hs
      change |Real.exp (-Real.pi * s * Q x y v)| ≤ _
      rw [abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_exp.mpr
      have hq : 0 ≤ Q x y v := by unfold Q; positivity
      have h := mul_le_mul_of_nonneg_left hs.le (mul_nonneg Real.pi_pos.le hq)
      nlinarith only [h]
  have hm : t ∈ Set.Ioi (t / 2) := by change t / 2 < t; linarith
  exact (hc.continuousAt (isOpen_Ioi.mem_nhds hm)).continuousWithinAt

/-- The zero vector contributes zero when the real exponent s is positive. -/
def epstein (s x y : ℝ) : ℝ := ∑' v : ℤ × ℤ, (Q x y v) ^ (-s)

private lemma q_nonneg (x : ℝ) {y : ℝ} (hy : 0 < y) (v : ℤ × ℤ) : 0 ≤ Q x y v := by
  unfold Q
  positivity

private lemma q_pos {x y : ℝ} (hy : 0 < y) {v : ℤ × ℤ} (hv : v ≠ (0, 0)) :
    0 < Q x y v := by
  apply lt_of_le_of_ne (q_nonneg x hy v)
  intro h
  have hz : latticePoint x y v = 0 :=
    Complex.normSq_eq_zero.mp (((lattice_geometry x hy).2 v).trans h.symm)
  have hzero : latticePoint x y (0, 0) = 0 := by
    apply Complex.ext <;> simp [latticePoint]
  exact hv ((lattice_geometry x hy).1 (hz.trans hzero.symm))

private lemma norm_square_le (v : Fin 2 → ℤ) :
    ‖v‖ ^ 2 ≤ (v 0 : ℝ) ^ 2 + (v 1 : ℝ) ^ 2 := by
  rw [EisensteinSeries.norm_eq_max_natAbs]
  simp only [Nat.cast_max, Nat.cast_natAbs, Int.cast_abs]
  rcases le_total |(v 0 : ℝ)| |(v 1 : ℝ)| with h | h
  · rw [max_eq_right h, sq_abs]
    nlinarith [sq_nonneg (v 0 : ℝ)]
  · rw [max_eq_left h, sq_abs]
    nlinarith [sq_nonneg (v 1 : ℝ)]

/-- The Epstein series converges throughout its natural real half-plane. -/
theorem epstein_summable {s x y : ℝ} (hs : 1 < s) (hy : 0 < y) :
    Summable (fun v : ℤ × ℤ => (Q x y v) ^ (-s)) := by
  let C := max (2 * y) ((2 * |x| ^ 2 + 1) / y)
  have hC : 0 < C := (by positivity : 0 < 2 * y).trans_le (le_max_left _ _)
  have hmajor := (EisensteinSeries.summable_one_div_norm_rpow
    (k := 2 * s) (by linarith)).mul_left (C ^ s)
  have hvec : Summable (fun v : Fin 2 → ℤ => (Q x y (v 0, v 1)) ^ (-s)) := by
    apply hmajor.of_nonneg_of_le (fun v => Real.rpow_nonneg (q_nonneg x hy _) _) ?_
    intro v
    by_cases hv : v = 0
    · subst v
      change (Q x y (0, 0)) ^ (-s) ≤ C ^ s * ‖(0 : Fin 2 → ℤ)‖ ^ (-(2 * s))
      rw [show Q x y (0, 0) = 0 by simp [Q],
        Real.zero_rpow (by linarith : (-s : ℝ) ≠ 0)]
      exact mul_nonneg (Real.rpow_nonneg hC.le s) (Real.rpow_nonneg (norm_nonneg _) _)
    · have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
      have hcontrol : ‖v‖ ^ 2 ≤ C * Q x y (v 0, v 1) :=
        (norm_square_le v).trans (quadratic_control hy le_rfl le_rfl le_rfl (v 0, v 1))
      have hq : ‖v‖ ^ 2 / C ≤ Q x y (v 0, v 1) :=
        (div_le_iff₀ hC).mpr (by simpa only [mul_comm] using hcontrol)
      calc
        _ ≤ (‖v‖ ^ 2 / C) ^ (-s) := Real.rpow_le_rpow_of_nonpos
          (div_pos (sq_pos_of_pos hn) hC) hq (by linarith)
        _ = C ^ s * ‖v‖ ^ (-(2 * s)) := by
          rw [Real.div_rpow (sq_nonneg _) hC.le,
            ← Real.rpow_natCast_mul hn.le 2 (-s), Real.rpow_neg hC.le s,
            div_inv_eq_mul]
          norm_num only [Nat.cast_ofNat]
          rw [show (2 : ℝ) * (-s) = -(2 * s) by ring]
          ring
  exact (finTwoArrowEquiv ℤ).summable_iff.mp (by simpa [Function.comp_def] using hvec)

private lemma gamma_term_integrable {s r : ℝ} (hs : 0 < s) (hr : 0 < r) :
    IntegrableOn (fun t : ℝ => t ^ (s - 1) * Real.exp (-(r * t))) (Ioi 0) := by
  have h := Real.GammaIntegral_convergent hs
  rw [← mul_zero r, ← integrableOn_Ioi_comp_mul_left_iff _ _ hr] at h
  have hscaled := h.const_mul ((r ^ (s - 1))⁻¹)
  refine IntegrableOn.congr_fun hscaled ?_ measurableSet_Ioi
  intro t ht
  dsimp only
  rw [Real.mul_rpow hr.le ht.le]
  field_simp [(Real.rpow_pos_of_pos hr (s - 1)).ne']
  <;> ring

private def mellinTerm (s x y : ℝ) (v : ℤ × ℤ) (t : ℝ) : ℝ :=
  if v = (0, 0) then 0 else Real.exp (-Real.pi * t * Q x y v) * t ^ (s - 1)

private lemma mellin_term_integrable {s x y : ℝ} (hs : 0 < s) (hy : 0 < y)
    (v : ℤ × ℤ) : IntegrableOn (mellinTerm s x y v) (Ioi 0) := by
  by_cases hv : v = (0, 0)
  · have he : mellinTerm s x y v = (fun _ : ℝ => 0) := by
      funext t
      rw [mellinTerm, if_pos hv]
    rw [he]
    exact integrableOn_zero
  · have hq := q_pos (x := x) hy hv
    have h := gamma_term_integrable hs (mul_pos Real.pi_pos hq)
    refine IntegrableOn.congr_fun h ?_ measurableSet_Ioi
    intro t ht
    have he : Real.exp (-((Real.pi * Q x y v) * t)) =
        Real.exp (-Real.pi * t * Q x y v) := by congr 1; ring
    dsimp only
    rw [mellinTerm, if_neg hv, he]
    ring

private lemma mellin_term_integral {s x y : ℝ} (hs : 0 < s) (hy : 0 < y)
    (v : ℤ × ℤ) :
    (∫ t : ℝ in Ioi 0, mellinTerm s x y v t) =
      (Real.pi ^ (-s) * Real.Gamma s) * (Q x y v) ^ (-s) := by
  by_cases hv : v = (0, 0)
  · subst v
    simp [mellinTerm, Q, Real.zero_rpow (by linarith : (-s : ℝ) ≠ 0)]
  · have hq := q_pos (x := x) hy hv
    have he : (∫ t : ℝ in Ioi 0, mellinTerm s x y v t) =
        ∫ t : ℝ in Ioi 0, t ^ (s - 1) * Real.exp (-((Real.pi * Q x y v) * t)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      have he : Real.exp (-((Real.pi * Q x y v) * t)) =
          Real.exp (-Real.pi * t * Q x y v) := by congr 1; ring
      dsimp only
      rw [mellinTerm, if_neg hv, he]
      ring
    rw [he, Real.integral_rpow_mul_exp_neg_mul_Ioi hs (mul_pos Real.pi_pos hq)]
    rw [one_div, Real.inv_rpow (mul_pos Real.pi_pos hq).le,
      ← Real.rpow_neg (mul_pos Real.pi_pos hq).le s,
      Real.mul_rpow Real.pi_pos.le hq.le]
    ring

private lemma mellin_term_nonneg {s x y t : ℝ} (ht : 0 < t) (v : ℤ × ℤ) :
    0 ≤ mellinTerm s x y v t := by
  unfold mellinTerm
  split_ifs <;> positivity

private lemma mellin_terms_sum {s x y t : ℝ} (ht : 0 < t) (hy : 0 < y) :
    (∑' v : ℤ × ℤ, mellinTerm s x y v t) = (F t x y - 1) * t ^ (s - 1) := by
  have h := (summable t x ht hy).tsum_eq_add_tsum_ite (0, 0)
  have hz : Real.exp (-Real.pi * t * Q x y (0, 0)) = 1 := by simp [Q]
  rw [hz] at h
  have he : (∑' v : ℤ × ℤ, if v = (0, 0) then 0 else Real.exp (-Real.pi * t * Q x y v)) =
      F t x y - 1 := by
    dsimp [F]
    linarith only [h]
  calc
    _ = ∑' v : ℤ × ℤ, (if v = (0, 0) then 0 else
        Real.exp (-Real.pi * t * Q x y v)) * t ^ (s - 1) := by
      apply tsum_congr
      intro v
      simp only [mellinTerm]
      split_ifs <;> simp
    _ = _ := by rw [tsum_mul_right, he]

private lemma mellin_integral_norm_summable {s x y : ℝ} (hs : 1 < s) (hy : 0 < y) :
    Summable (fun v : ℤ × ℤ => ∫ t : ℝ in Ioi 0, ‖mellinTerm s x y v t‖) := by
  have hs0 : 0 < s := by linarith
  have h := (epstein_summable (x := x) hs hy).mul_left (Real.pi ^ (-s) * Real.Gamma s)
  convert h using 1
  ext v
  rw [← mellin_term_integral hs0 hy v]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  exact Real.norm_of_nonneg (mellin_term_nonneg ht v)

private lemma mellin_weight_continuous {s x y : ℝ} (hy : 0 < y) :
    ContinuousOn (fun t : ℝ => (F t x y - 1) * t ^ (s - 1)) (Ioi 0) := by
  apply ((continuousOn_temperature x hy).sub continuousOn_const).mul
  intro t ht
  exact (Real.continuousAt_rpow_const t (s - 1) (Or.inl ht.ne')).continuousWithinAt

/-- The positive-temperature Mellin weight is integrable for every real s greater than one. -/
theorem epstein_mellin_integrable {s x y : ℝ} (hs : 1 < s) (hy : 0 < y) :
    IntegrableOn (fun t : ℝ => (F t x y - 1) * t ^ (s - 1)) (Ioi 0) := by
  have hs0 : 0 < s := by linarith
  let μ := volume.restrict (Ioi (0 : ℝ))
  let f := fun (v : ℤ × ℤ) (t : ℝ) => mellinTerm s x y v t
  have hf (v : ℤ × ℤ) : Integrable (f v) μ := mellin_term_integrable hs0 hy v
  have hnorm : Summable (fun v : ℤ × ℤ => ∫ t, ‖f v t‖ ∂μ) :=
    mellin_integral_norm_summable hs hy
  have hfinite : (∑' v : ℤ × ℤ, ∫⁻ t, ‖f v t‖ₑ ∂μ) < ∞ := by
    simp_rw [← ofReal_integral_norm_eq_lintegral_enorm (hf _)]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun v => integral_nonneg (fun t => norm_nonneg _))
      hnorm]
    exact ENNReal.ofReal_lt_top
  refine ⟨(mellin_weight_continuous hy).aestronglyMeasurable measurableSet_Ioi, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  have he : (fun t : ℝ => ‖(F t x y - 1) * t ^ (s - 1)‖ₑ) =ᵐ[μ]
      (fun t => ‖∑' v : ℤ × ℤ, f v t‖ₑ) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    change ‖(F t x y - 1) * t ^ (s - 1)‖ₑ =
      ‖∑' v : ℤ × ℤ, mellinTerm s x y v t‖ₑ
    rw [mellin_terms_sum ht hy]
  rw [lintegral_congr_ae he]
  apply lt_of_le_of_lt (lintegral_mono (fun t => enorm_tsum_le_tsum_enorm))
  rw [lintegral_tsum (fun v => (hf v).aestronglyMeasurable.enorm)]
  exact hfinite

/-- Mellin representation with the zero vector removed and the Gamma normalization explicit. -/
theorem epstein_mellin {s x y : ℝ} (hs : 1 < s) (hy : 0 < y) :
    epstein s x y = (Real.pi ^ s / Real.Gamma s) *
      ∫ t : ℝ in Ioi 0, (F t x y - 1) * t ^ (s - 1) := by
  have hs0 : 0 < s := by linarith
  have hqzero (v : ℤ × ℤ) : Q x y v = 0 ↔ v = (0, 0) := by
    constructor
    · intro h
      by_contra hv
      exact (q_pos hy hv).ne' h
    · rintro rfl
      simp [Q]
  have hF (t : ℝ) (ht : t ∈ Ioi 0) : HasSum (fun v : ℤ × ℤ =>
      if Q x y v = 0 then 0 else (1 : ℂ) * Real.exp (-Real.pi * Q x y v * t))
      ((F t x y - 1 : ℝ) : ℂ) := by
    have hn := summable t x ht hy
    have hsum : Summable (fun v : ℤ × ℤ =>
        if v = (0, 0) then (0 : ℝ) else Real.exp (-Real.pi * t * Q x y v)) := by
      apply hn.of_nonneg_of_le (fun v => by split_ifs <;> positivity)
      intro v
      split_ifs
      · exact (Real.exp_pos _).le
      · exact le_rfl
    have he : (∑' v : ℤ × ℤ, if v = (0, 0) then (0 : ℝ) else
        Real.exp (-Real.pi * t * Q x y v)) = F t x y - 1 := by
      have h := mellin_terms_sum (s := 1) (x := x) ht hy
      simpa only [mellinTerm, sub_self, Real.rpow_zero, mul_one] using h
    have hc := Complex.hasSum_ofReal.mpr (he ▸ hsum.hasSum)
    convert hc using 1
    ext v
    simp only [hqzero v]
    split_ifs <;> simp only [Complex.ofReal_zero, one_mul, Complex.ofReal_one]
    congr 2
    ring
  have hsum : Summable (fun v : ℤ × ℤ => ‖(1 : ℂ)‖ / Q x y v ^ (s : ℂ).re) := by
    convert epstein_summable hs hy using 1
    ext v
    rw [norm_one, Complex.ofReal_re, one_div, Real.rpow_neg (q_nonneg x hy v)]
  have hm := hasSum_mellin_pi_mul₀ (a := fun _ : ℤ × ℤ => (1 : ℂ))
    (p := Q x y) (s := (s : ℂ)) (fun v => q_nonneg x hy v)
    (by simpa using hs0) hF hsum
  have hterm (v : ℤ × ℤ) :
      (Real.pi : ℂ) ^ (-(s : ℂ)) * Complex.Gamma (s : ℂ) * 1 /
        (Q x y v : ℂ) ^ (s : ℂ) =
      (((Real.pi ^ (-s) * Real.Gamma s) * (Q x y v) ^ (-s) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_neg, ← Complex.ofReal_cpow Real.pi_pos.le,
      Complex.Gamma_ofReal, ← Complex.ofReal_cpow (q_nonneg x hy v),
      ← Complex.ofReal_mul, mul_one, ← Complex.ofReal_div,
      Real.rpow_neg (q_nonneg x hy v), div_eq_mul_inv]
  have hi : mellin (fun t => ((F t x y - 1 : ℝ) : ℂ)) (s : ℂ) =
      ((∫ t : ℝ in Ioi 0, (F t x y - 1) * t ^ (s - 1) : ℝ) : ℂ) := by
    rw [mellin, ← integral_complex_ofReal]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    dsimp only
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_cpow ht.le]
    simp only [smul_eq_mul, ← Complex.ofReal_mul]
    congr 1
    ring
  have he : (Real.pi ^ (-s) * Real.Gamma s) * epstein s x y =
      ∫ t : ℝ in Ioi 0, (F t x y - 1) * t ^ (s - 1) := by
    apply Complex.ofReal_injective
    have hh := hm.tsum_eq
    simp_rw [hterm] at hh
    rw [← Complex.ofReal_tsum, hi] at hh
    simpa only [epstein, tsum_mul_left] using hh
  rw [← he, Real.rpow_neg Real.pi_pos.le s]
  field_simp [(Real.Gamma_pos_of_pos hs0).ne', (Real.rpow_pos_of_pos Real.pi_pos s).ne']
  <;> ring

/-- The Epstein zeta function has the same unique minimizer on the reduced half-strip. -/
theorem reduced_epstein_minimum {s x y : ℝ} (hs : 1 < s)
    (hx : 0 ≤ x) (hx' : x ≤ 1 / 2) (hy : Real.sqrt 3 / 2 ≤ y) :
    epstein s (1 / 2) (Real.sqrt 3 / 2) ≤ epstein s x y ∧
      (epstein s x y = epstein s (1 / 2) (Real.sqrt 3 / 2) ↔
        x = 1 / 2 ∧ y = Real.sqrt 3 / 2) := by
  have hc : 0 < Real.sqrt 3 / 2 := by positivity
  have hy0 : 0 < y := hc.trans_le hy
  have hs0 : 0 < s := by linarith
  let h := fun t : ℝ => ((F t x y - 1) * t ^ (s - 1)) -
    ((F t (1 / 2) (Real.sqrt 3 / 2) - 1) * t ^ (s - 1))
  have hint : IntegrableOn h (Ioi 0) :=
    (epstein_mellin_integrable hs hy0).sub (epstein_mellin_integrable hs hc)
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] h := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    have hm := (reduced_theta_minimum ht hx hx' hy).1
    have hp : 0 < t ^ (s - 1) := Real.rpow_pos_of_pos ht _
    dsimp [h]
    nlinarith [mul_nonneg (sub_nonneg.mpr hm) hp.le]
  have he : epstein s x y - epstein s (1 / 2) (Real.sqrt 3 / 2) =
      (Real.pi ^ s / Real.Gamma s) * ∫ t : ℝ in Ioi 0, h t := by
    rw [epstein_mellin hs hy0, epstein_mellin hs hc,
      integral_sub (epstein_mellin_integrable hs hy0) (epstein_mellin_integrable hs hc)]
    ring
  have hcoeff : 0 < Real.pi ^ s / Real.Gamma s :=
    div_pos (Real.rpow_pos_of_pos Real.pi_pos s) (Real.Gamma_pos_of_pos hs0)
  constructor
  · have hi : 0 ≤ ∫ t : ℝ in Ioi 0, h t := integral_nonneg_of_ae hnonneg
    have hm := mul_nonneg hcoeff.le hi
    linarith only [he, hm]
  · constructor
    · intro heq
      by_contra hxy
      have hpos (t : ℝ) (ht : 0 < t) : 0 < h t := by
        have hm := reduced_theta_minimum ht hx hx' hy
        have hstrict : F t (1 / 2) (Real.sqrt 3 / 2) < F t x y := by
          apply lt_of_le_of_ne hm.1
          intro htheta
          exact hxy (hm.2.mp htheta.symm)
        have hp := Real.rpow_pos_of_pos ht (s - 1)
        dsimp [h]
        nlinarith [mul_pos (sub_pos.mpr hstrict) hp]
      have hsupport : Function.support h ∩ Ioi 0 = Ioi 0 := by
        apply inter_eq_right.mpr
        intro t ht
        exact (hpos t ht).ne'
      have hi : 0 < ∫ t : ℝ in Ioi 0, h t := by
        apply (setIntegral_pos_iff_support_of_nonneg_ae hnonneg hint).mpr
        rw [hsupport, Real.volume_Ioi]
        exact ENNReal.zero_lt_top
      have hm := mul_pos hcoeff hi
      rw [heq, sub_self] at he
      linarith only [he, hm]
    · rintro ⟨rfl, rfl⟩
      rfl

/-- Epstein zeta written in the actual coordinates of a complex lattice basis. -/
def basisEpstein (s : ℝ) (a b : ℂ) : ℝ :=
  ∑' v : ℤ × ℤ, Complex.normSq ((v.1 : ℂ) * a + (v.2 : ℂ) * b) ^ (-s)

private lemma basis_form_transport (a b : ℂ) (hab : |a.re * b.im - a.im * b.re| = 1) :
    ∃ x y : ℝ, 0 ≤ x ∧ x ≤ 1 / 2 ∧ 0 < y ∧ Real.sqrt 3 / 2 ≤ y ∧
      (∀ s : ℝ, basisEpstein s a b = epstein s x y) ∧
      ∀ t : ℝ, basisTheta t a b = F t x y := by
  obtain ⟨x, y, hx, hx', hy0, _, hy, e, he⟩ := basis_reduction_geometry a b hab
  refine ⟨x, y, hx, hx', hy0, hy, ?_, ?_⟩
  · intro s
    unfold basisEpstein epstein
    simp_rw [he]
    exact e.toEquiv.tsum_eq (fun v : ℤ × ℤ => (Q x y v) ^ (-s))
  · intro t
    unfold basisTheta F
    simp_rw [he]
    exact e.toEquiv.tsum_eq (fun v : ℤ × ℤ => Real.exp (-Real.pi * t * Q x y v))


/-- Mellin's integral represents the basis zeta with the same area-one normalization. -/
private theorem basis_epstein_mellin_unit (a b : ℂ) (hab : |a.re * b.im - a.im * b.re| = 1)
    {s : ℝ} (hs : 1 < s) :
    basisEpstein s a b = (Real.pi ^ s / Real.Gamma s) *
      ∫ t : ℝ in Ioi 0, (basisTheta t a b - 1) * t ^ (s - 1) := by
  obtain ⟨x, y, _, _, hy0, _, hz, htheta⟩ := basis_form_transport a b hab
  simp_rw [htheta]
  rw [hz s]
  exact epstein_mellin hs hy0

/-- Area-one Epstein zeta is minimized precisely by orthogonal images of the hexagonal lattice. -/
private theorem basis_epstein_minimum_unit (a b : ℂ)
    (hab : |a.re * b.im - a.im * b.re| = 1) {s : ℝ} (hs : 1 < s) :
    epstein s (1 / 2) (Real.sqrt 3 / 2) ≤ basisEpstein s a b ∧
      (basisEpstein s a b = epstein s (1 / 2) (Real.sqrt 3 / 2) ↔ IsHexagonalBasis a b) := by
  obtain ⟨x, y, hx, hx', hy0, hy, hz, htheta⟩ := basis_form_transport a b hab
  have hm := reduced_epstein_minimum hs hx hx' hy
  have hthetaOne : F 1 (1 / 2) (Real.sqrt 3 / 2) ≤ basisTheta 1 a b ∧
      (basisTheta 1 a b = F 1 (1 / 2) (Real.sqrt 3 / 2) ↔ IsHexagonalBasis a b) := by
    simpa using basis_theta_minimum_isometry a b (A := 1) (by norm_num) hab
      (t := 1) (by norm_num)
  constructor
  · rw [hz s]
    exact hm.1
  · constructor
    · intro h
      have hxy := hm.2.mp ((hz s).symm.trans h)
      apply hthetaOne.2.mp
      rw [htheta 1, hxy.1, hxy.2]
    · intro hiso
      have ht : ∀ t : ℝ, 0 < t → basisTheta t a b =
          F t (1 / 2) (Real.sqrt 3 / 2) := by
        intro t ht
        have h := (basis_theta_minimum_isometry a b (A := 1) (by norm_num) hab ht).2
        simpa using h.mpr (by simpa using hiso)
      rw [basis_epstein_mellin_unit a b hab hs,
        epstein_mellin hs (by positivity : 0 < Real.sqrt 3 / 2)]
      congr 1
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht0
      dsimp only
      rw [ht t ht0]

private lemma epstein_scale (r : ℝ) (s : ℝ) (a b : ℂ) :
    basisEpstein s (r • a) (r • b) = (r ^ 2) ^ (-s) * basisEpstein s a b := by
  unfold basisEpstein
  simp_rw [basis_normSq_scale, Real.mul_rpow (sq_nonneg r) (Complex.normSq_nonneg _)]
  rw [tsum_mul_left]

/-- Epstein minimum and actual isometry classification at arbitrary positive covolume. -/
theorem basis_epstein_minimum_isometry (a b : ℂ) {A s : ℝ} (hA : 0 < A)
    (hab : |a.re * b.im - a.im * b.re| = A) (hs : 1 < s) :
    A ^ (-s) * epstein s (1 / 2) (Real.sqrt 3 / 2) ≤ basisEpstein s a b ∧
      (basisEpstein s a b = A ^ (-s) * epstein s (1 / 2) (Real.sqrt 3 / 2) ↔
        IsHexagonalBasis (((Real.sqrt A)⁻¹ : ℝ) • a) (((Real.sqrt A)⁻¹ : ℝ) • b)) := by
  have hsqrt : 0 < Real.sqrt A := Real.sqrt_pos.mpr hA
  have hm := basis_epstein_minimum_unit (((Real.sqrt A)⁻¹ : ℝ) • a)
    (((Real.sqrt A)⁻¹ : ℝ) • b) (basis_normalized_area a b hA hab) hs
  have he := epstein_scale (Real.sqrt A) s (((Real.sqrt A)⁻¹ : ℝ) • a)
    (((Real.sqrt A)⁻¹ : ℝ) • b)
  simp only [smul_smul, mul_inv_cancel₀ hsqrt.ne', one_smul, Real.sq_sqrt hA.le] at he
  rw [he]
  have hp : 0 < A ^ (-s) := Real.rpow_pos_of_pos hA _
  exact ⟨mul_le_mul_of_nonneg_left hm.1 hp.le, by
    rw [mul_left_cancel_iff_of_pos hp]
    exact hm.2⟩

end
end D5.S3.Fourier.PlanarTheta
