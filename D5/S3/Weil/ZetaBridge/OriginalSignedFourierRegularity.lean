/- GID: D5/S3/Weil/ZetaBridge/OriginalSignedFourierRegularity
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaBridge/OriginalSignedFourierRegularity
   mirror-E: none(waiver:literal-line-L2-translation)
   anchors: []
   utility: none
   digest: Two-boundary translation regularity of literal Ioc signed Fourier heads. -/

import D5.S3.Weil.ZetaBridge.OriginalSignedPrimeFourier
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace OriginalSignedFourierRegularity

open MeasureTheory Set Filter
open scoped BigOperators ComplexConjugate
open PhysicalCompressedCosineMatrix
open OriginalSignedCompressedFourier OriginalSignedPrimeFourier

/-- Literal line representative, retaining both jumps of the Ioc interval. -/
def lineMode (L : ℝ) (n : ℤ) : ℝ → ℂ := zeroExtension (L / 2) (mode L n)

private lemma mode_norm_sq (L : ℝ) (hL : 0 < L) (n : ℤ) (x : ℝ) :
    ‖mode L n x‖ ^ 2 = L⁻¹ := by
  have hn : ‖OriginalEvenCosineComplete.character (L / 2) n x‖ = 1 :=
    Circle.norm_coe _
  rw [normalization_dictionary L hL]
  simp only [norm_div, norm_mul, norm_zpow, norm_neg, norm_one, one_zpow,
    one_mul, hn,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg L), div_pow,
    one_pow, Real.sq_sqrt hL.le, one_div]
  rw [← inv_pow, Real.sq_sqrt hL.le]

private lemma mode_memLp (L : ℝ) (hL : 0 < L) (n : ℤ) :
    MemLp (mode L n) 2 (volume.restrict (window (L / 2))) := by
  change MemLp (mode L n) 2 (volume.restrict (Ioc (-(L / 2)) (L / 2)))
  apply MemLp.of_bound (mode_continuous L n).aestronglyMeasurable (Real.sqrt (L⁻¹))
  exact Eventually.of_forall fun x => by
    have hx := mode_norm_sq L hL n x
    have hr := Real.sq_sqrt (inv_nonneg.mpr hL.le)
    apply (sq_le_sq₀ (norm_nonneg (mode L n x)) (Real.sqrt_nonneg (L⁻¹))).mp
    rw [hx, hr]

private lemma line_memLp (L : ℝ) (hL : 0 < L) (n : ℤ) :
    MemLp (lineMode L n) 2 (volume : Measure ℝ) := by
  exact (memLp_indicator_iff_restrict measurableSet_Ioc.nullMeasurableSet).mpr
    (mode_memLp L hL n)

/-- The exact dx mass, before any Fourier completeness theorem. -/
private lemma line_energy (L : ℝ) (hL : 0 < L) (n : ℤ) :
    (∫ x : ℝ, ‖lineMode L n x‖ ^ 2) = 1 := by
  have he : (fun x => ‖lineMode L n x‖ ^ 2) =
      (window (L / 2)).indicator (fun _ : ℝ => L⁻¹) := by
    funext x
    by_cases hx : x ∈ window (L / 2)
    · simp [lineMode, zeroExtension, hx, mode_norm_sq L hL]
    · simp [lineMode, zeroExtension, hx]
  rw [he]
  change (∫ x : ℝ, (window (L / 2)).indicator (fun _ : ℝ => L⁻¹) x) = 1
  rw [integral_indicator (show MeasurableSet (window (L / 2)) from measurableSet_Ioc),
    setIntegral_const]
  simp only [window, Real.volume_real_Ioc, sub_neg_eq_add, smul_eq_mul,
    show L / 2 + L / 2 = L by ring, max_eq_left hL.le]
  exact mul_inv_cancel₀ hL.ne'

private lemma shift_memLp (L : ℝ) (hL : 0 < L) (n : ℤ) (h : ℝ) :
    MemLp (fun x => lineMode L n (x - h)) 2 (volume : Measure ℝ) := by
  exact (line_memLp L hL n).comp_measurePreserving
    (measurePreserving_sub_right volume h)

/-- The line L2 gap; this is not an H1 assertion about the zero extension. -/
def translationSquaredNorm (L : ℝ) (n : ℤ) (h : ℝ) : ℝ :=
  ∫ x : ℝ, ‖lineMode L n x - lineMode L n (x - h)‖ ^ 2

/-- Each of the two disjoint endpoint strips contributes exactly h/L.
The statements keep the literal Ioc representatives at both ends. -/
theorem boundary_strip_energies (L : ℝ) (hL : 0 < L) (n : ℤ) (h : ℝ)
    (hh : 0 ≤ h) (hcap : h ≤ L) :
    (∫ x in Ioc (-(L / 2)) (-(L / 2) + h),
      ‖lineMode L n x - lineMode L n (x - h)‖ ^ 2) = h / L ∧
    (∫ x in Ioc (L / 2) (L / 2 + h),
      ‖lineMode L n x - lineMode L n (x - h)‖ ^ 2) = h / L := by
  constructor
  · calc
      _ = ∫ _x in Ioc (-(L / 2)) (-(L / 2) + h), L⁻¹ := by
        apply setIntegral_congr_fun measurableSet_Ioc
        intro x hx
        have hin : x ∈ window (L / 2) := ⟨hx.1, by linarith [hx.2]⟩
        have hout : x - h ∉ window (L / 2) := by
          intro hz
          have hz' := hz.1
          linarith [hx.2]
        simp [lineMode, zeroExtension, hin, hout, mode_norm_sq L hL]
      _ = h / L := by
        rw [setIntegral_const]
        simp [Real.volume_Ioc, ENNReal.toReal_ofReal hh, smul_eq_mul, div_eq_mul_inv, hh]
  · calc
      _ = ∫ _x in Ioc (L / 2) (L / 2 + h), L⁻¹ := by
        apply setIntegral_congr_fun measurableSet_Ioc
        intro x hx
        have hout : x ∉ window (L / 2) := by
          intro hz
          have hz' := hz.2
          linarith [hx.1]
        have hin : x - h ∈ window (L / 2) := ⟨by linarith [hx.1], by linarith [hx.2]⟩
        simp [lineMode, zeroExtension, hin, hout, mode_norm_sq L hL]
      _ = h / L := by
        rw [setIntegral_const]
        simp [Real.volume_Ioc, ENNReal.toReal_ofReal hh, smul_eq_mul, div_eq_mul_inv, hh]

/-- Both separate boundary strips are retained: their contribution is `2h/L`.
The remaining term is the exact overlap energy, including n=0, h=0 and h=L. -/
theorem translation_squared_norm (L : ℝ) (hL : 0 < L) (n : ℤ) (h : ℝ)
    (hh : 0 ≤ h) (hcap : h ≤ L) :
    translationSquaredNorm L n h =
      2 * h / L + 2 * (1 - h / L) * (1 - Real.cos (frequency L n * h)) := by
  let F := lineMode L n
  let G := fun x => lineMode L n (x - h)
  have hF : MemLp F 2 (volume : Measure ℝ) := line_memLp L hL n
  have hG : MemLp G 2 (volume : Measure ℝ) := shift_memLp L hL n h
  have hiF : Integrable (fun x => ‖F x‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm hF.aestronglyMeasurable).mp hF
  have hiG : Integrable (fun x => ‖G x‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm hG.aestronglyMeasurable).mp hG
  have hip : Integrable (fun x => conj (F x) * G x) := by
    have H := L2.integrable_inner (𝕜 := ℂ) (hF.toLp F) (hG.toLp G)
    apply H.congr
    filter_upwards [hF.coeFn_toLp, hG.coeFn_toLp] with x hx hy
    simp [hx, hy, RCLike.inner_apply', mul_comm]
  have hcorr : ∫ x, conj (F x) * G x = entry L n n h := by
    rw [entry, pairing_line]
    rfl
  have hE : ∫ x, ‖G x‖ ^ 2 = 1 := by
    calc
      _ = ∫ x : ℝ, ‖lineMode L n x‖ ^ 2 :=
        integral_sub_right_eq_self (fun x : ℝ => ‖lineMode L n x‖ ^ 2) h
      _ = 1 := line_energy L hL n
  have hEF : ∫ x, ‖F x‖ ^ 2 = 1 := line_energy L hL n
  have hr : Integrable (fun x => 2 * (conj (F x) * G x).re) := hip.re.const_mul 2
  have hsub : Integrable (fun x => ‖F x‖ ^ 2 - 2 * (conj (F x) * G x).re) :=
    hiF.sub hr
  have hre : (∫ x, (conj (F x) * G x).re) = (∫ x, conj (F x) * G x).re :=
    integral_re hip
  have he (x : ℝ) : ‖F x - G x‖ ^ 2 =
      ‖F x‖ ^ 2 - 2 * (conj (F x) * G x).re + ‖G x‖ ^ 2 := by
    simpa [RCLike.inner_apply', mul_comm] using norm_sub_sq (𝕜 := ℂ) (F x) (G x)
  unfold translationSquaredNorm
  change (∫ x, ‖F x - G x‖ ^ 2) = _
  simp_rw [he]
  rw [integral_add hsub hiG, integral_sub hiF hr, integral_const_mul,
    hre, hcorr, hE, hEF]
  have hp := entry_paired L hL n n h hh hcap
  rw [entry_adjoint] at hp
  have hr : (entry L n n h).re + (entry L n n h).re =
      2 * (1 - h / L) * Real.cos (frequency L n * h) := by
    simpa using congrArg Complex.re hp
  nlinarith [hr]

/-- The endpoint-jump term is linear in h, even for the zero mode. -/
theorem translation_squared_norm_le (L : ℝ) (hL : 0 < L) (n : ℤ) (h : ℝ)
    (hh : 0 ≤ h) (hcap : h ≤ L) :
    translationSquaredNorm L n h ≤ 2 * h / L + (frequency L n) ^ 2 * h ^ 2 := by
  rw [translation_squared_norm L hL n h hh hcap]
  have hc : 0 ≤ 1 - h / L := by
    have := (div_le_one hL).mpr hcap
    linarith
  have hc1 : 1 - h / L ≤ 1 := sub_le_self 1 (div_nonneg hh hL.le)
  have ht := Real.one_sub_sq_div_two_le_cos (x := frequency L n * h)
  have hn : 0 ≤ 1 - Real.cos (frequency L n * h) := by
    linarith [Real.cos_le_one (frequency L n * h)]
  nlinarith [mul_le_mul_of_nonneg_right hc1 hn]

private lemma l2_energy (u : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖u‖ ^ 2 = ∫ x, ‖u x‖ ^ 2 := by
  rw [@norm_sq_eq_re_inner ℂ, L2.inner_def, ← integral_re (L2.integrable_inner u u)]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by simp only [← norm_sq_eq_re_inner]

/-- A subject-local line L2 representative of the actual displaced mode.
It is a consumer of the literal integral estimate, not a replacement domain. -/
def displacedMode (L : ℝ) (hL : 0 < L) (n : ℤ) (h : ℝ) :
    Lp ℂ 2 (volume : Measure ℝ) :=
  ((line_memLp L hL n).sub (shift_memLp L hL n h)).toLp
    (fun x => lineMode L n x - lineMode L n (x - h))

private lemma displacedMode_energy (L : ℝ) (hL : 0 < L) (n : ℤ) (h : ℝ) :
    ‖displacedMode L hL n h‖ ^ 2 = translationSquaredNorm L n h := by
  rw [l2_energy]
  apply integral_congr_ae
  filter_upwards [((line_memLp L hL n).sub (shift_memLp L hL n h)).coeFn_toLp]
    with x hx
  exact congrArg (fun z : ℂ => ‖z‖ ^ 2) hx

private lemma displacedMode_bound (L : ℝ) (hL : 0 < L) (n : ℤ) (h : ℝ)
    (hh : 0 ≤ h) (hcap : h ≤ L) :
    ‖displacedMode L hL n h‖ ≤ Real.sqrt (2 / L) * Real.sqrt h + |frequency L n| * h := by
  have hb := translation_squared_norm_le L hL n h hh hcap
  rw [← displacedMode_energy L hL] at hb
  have hs := Real.sq_sqrt (show 0 ≤ 2 / L by positivity)
  have ht := Real.sq_sqrt hh
  have hf : 0 ≤ Real.sqrt (2 / L) * Real.sqrt h := by positivity
  have hw : 0 ≤ |frequency L n| * h := mul_nonneg (abs_nonneg _) hh
  have hid : (Real.sqrt (2 / L) * Real.sqrt h) ^ 2 = 2 * h / L := by
    rw [mul_pow, hs, ht]
    ring
  apply (sq_le_sq₀ (norm_nonneg (displacedMode L hL n h)) (add_nonneg hf hw)).mp
  have hw2 : (|frequency L n| * h) ^ 2 = frequency L n ^ 2 * h ^ 2 := by
    rw [mul_pow, sq_abs]
  nlinarith [mul_nonneg hf hw]

/-- Literal finite complex head displacement on the line L2 carrier. -/
def displacedHead (L : ℝ) (hL : 0 < L) (S : Finset ℤ) (v : ℤ → ℂ) (h : ℝ) :
    Lp ℂ 2 (volume : Measure ℝ) := ∑ n ∈ S, v n • displacedMode L hL n h

/-- The finite head majorant retains both the sqrt(h) boundary contribution
and the h interior contribution, for every signed finite mode set. -/
theorem finite_head_translation_bound (L : ℝ) (hL : 0 < L) (S : Finset ℤ)
    (v : ℤ → ℂ) (h : ℝ) (hh : 0 ≤ h) (hcap : h ≤ L) :
    ‖displacedHead L hL S v h‖ ≤
      (Real.sqrt (2 / L) * ∑ n ∈ S, ‖v n‖) * Real.sqrt h +
        (∑ n ∈ S, ‖v n‖ * |frequency L n|) * h := by
  unfold displacedHead
  calc
    _ ≤ ∑ n ∈ S, ‖v n • displacedMode L hL n h‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ S, ‖v n‖ *
        (Real.sqrt (2 / L) * Real.sqrt h + |frequency L n| * h) := by
      apply Finset.sum_le_sum
      intro n _
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left (displacedMode_bound L hL n h hh hcap) (norm_nonneg _)
    _ = _ := by
      simp only [mul_add, ← mul_assoc, Finset.sum_add_distrib, ← Finset.sum_mul]
      ring

/-- Cauchy--Schwarz gives the coefficient-l2 version used by the original
finite-head strong-action estimate. Empty heads and zero modes are included. -/
theorem finite_head_translation_bound_l2 (L : ℝ) (hL : 0 < L) (S : Finset ℤ)
    (v : ℤ → ℂ) (h : ℝ) (hh : 0 ≤ h) (hcap : h ≤ L) :
    ‖displacedHead L hL S v h‖ ≤
      (Real.sqrt (2 * (S.card : ℝ) / L) * Real.sqrt h +
        Real.sqrt (∑ n ∈ S, frequency L n ^ 2) * h) *
          Real.sqrt (∑ n ∈ S, ‖v n‖ ^ 2) := by
  have hmass : 0 ≤ ∑ n ∈ S, ‖v n‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hfreq : 0 ≤ ∑ n ∈ S, frequency L n ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hsum : 0 ≤ ∑ n ∈ S, ‖v n‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hwsum : 0 ≤ ∑ n ∈ S, ‖v n‖ * |frequency L n| :=
    Finset.sum_nonneg fun _ _ => mul_nonneg (norm_nonneg _) (abs_nonneg _)
  have hc := Finset.sum_mul_sq_le_sq_mul_sq S (fun n => ‖v n‖) (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hc
  have hw := Finset.sum_mul_sq_le_sq_mul_sq S (fun n => ‖v n‖) (fun n => |frequency L n|)
  simp only [sq_abs] at hw
  have hrm := Real.sq_sqrt hmass
  have hrf := Real.sq_sqrt hfreq
  have hrc := Real.sq_sqrt (show 0 ≤ (S.card : ℝ) by positivity)
  have hc' : (∑ n ∈ S, ‖v n‖) ≤
      Real.sqrt (S.card : ℝ) * Real.sqrt (∑ n ∈ S, ‖v n‖ ^ 2) := by
    have he : (Real.sqrt (S.card : ℝ) * Real.sqrt (∑ n ∈ S, ‖v n‖ ^ 2)) ^ 2 =
        (S.card : ℝ) * (∑ n ∈ S, ‖v n‖ ^ 2) := by rw [mul_pow, hrc, hrm]
    apply (sq_le_sq₀ hsum (mul_nonneg (Real.sqrt_nonneg (S.card : ℝ))
      (Real.sqrt_nonneg (∑ n ∈ S, ‖v n‖ ^ 2)))).mp
    rw [he]
    simpa only [mul_comm] using hc
  have hw' : (∑ n ∈ S, ‖v n‖ * |frequency L n|) ≤
      Real.sqrt (∑ n ∈ S, ‖v n‖ ^ 2) * Real.sqrt (∑ n ∈ S, frequency L n ^ 2) := by
    have he : (Real.sqrt (∑ n ∈ S, ‖v n‖ ^ 2) *
        Real.sqrt (∑ n ∈ S, frequency L n ^ 2)) ^ 2 =
        (∑ n ∈ S, ‖v n‖ ^ 2) * (∑ n ∈ S, frequency L n ^ 2) := by
      rw [mul_pow, hrm, hrf]
    apply (sq_le_sq₀ hwsum (mul_nonneg (Real.sqrt_nonneg (∑ n ∈ S, ‖v n‖ ^ 2))
      (Real.sqrt_nonneg (∑ n ∈ S, frequency L n ^ 2)))).mp
    rw [he]
    exact hw
  have hs : Real.sqrt (2 / L) * Real.sqrt (S.card : ℝ) =
      Real.sqrt (2 * (S.card : ℝ) / L) := by
    rw [← Real.sqrt_mul (by positivity : 0 ≤ 2 / L)]
    congr 1
    ring
  calc
    _ ≤ (Real.sqrt (2 / L) * ∑ n ∈ S, ‖v n‖) * Real.sqrt h +
        (∑ n ∈ S, ‖v n‖ * |frequency L n|) * h :=
      finite_head_translation_bound L hL S v h hh hcap
    _ ≤ (Real.sqrt (2 / L) *
        (Real.sqrt (S.card : ℝ) * Real.sqrt (∑ n ∈ S, ‖v n‖ ^ 2))) * Real.sqrt h +
        (Real.sqrt (∑ n ∈ S, ‖v n‖ ^ 2) *
          Real.sqrt (∑ n ∈ S, frequency L n ^ 2)) * h := by
      gcongr
    _ = _ := by rw [← mul_assoc, hs]; ring

/-- The finite L2 sum is the displacement of the literal zero extension
of the original finite complex profile, not a periodic extension. -/
theorem displacedHead_ae (L : ℝ) (hL : 0 < L) (S : Finset ℤ)
    (v : ℤ → ℂ) (h : ℝ) :
    (displacedHead L hL S v h : ℝ → ℂ) =ᵐ[volume]
      (fun x => zeroExtension (L / 2) (head L S v) x -
        zeroExtension (L / 2) (head L S v) (x - h)) := by
  classical
  have hm (n : ℤ) : (v n • displacedMode L hL n h : Lp ℂ 2 (volume : Measure ℝ)) =ᵐ[volume]
      (fun x => v n * (lineMode L n x - lineMode L n (x - h))) := by
    filter_upwards [Lp.coeFn_smul (v n) (displacedMode L hL n h),
      ((line_memLp L hL n).sub (shift_memLp L hL n h)).coeFn_toLp] with x hx hy
    calc
      _ = v n * (displacedMode L hL n h : ℝ → ℂ) x := hx
      _ = _ := congrArg (fun z : ℂ => v n * z) hy
  have hall : ∀ᵐ x ∂volume, ∀ n ∈ S,
      (v n • displacedMode L hL n h : Lp ℂ 2 (volume : Measure ℝ)) x =
        v n * (lineMode L n x - lineMode L n (x - h)) :=
    S.eventually_all.mpr (fun n _ => hm n)
  have hs : (displacedHead L hL S v h : ℝ → ℂ) =ᵐ[volume]
      fun x => ∑ n ∈ S, v n * (lineMode L n x - lineMode L n (x - h)) := by
    filter_upwards [Lp.coeFn_fun_finsetSum S (fun n => v n • displacedMode L hL n h),
      hall] with x hx hy
    exact hx.trans (Finset.sum_congr rfl (fun n hn => hy n hn))
  apply hs.trans
  exact Eventually.of_forall fun x => by
    have he (y : ℝ) : zeroExtension (L / 2) (head L S v) y =
        ∑ n ∈ S, v n * lineMode L n y := by
      by_cases hy : y ∈ window (L / 2) <;> simp [zeroExtension, head, lineMode, hy]
    dsimp only
    rw [he x, he (x - h)]
    simp only [mul_sub, Finset.sum_sub_distrib]

end OriginalSignedFourierRegularity
