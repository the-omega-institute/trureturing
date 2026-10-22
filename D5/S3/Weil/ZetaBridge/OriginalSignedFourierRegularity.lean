/- GID: D5/S3/Weil/ZetaBridge/OriginalSignedFourierRegularity
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaBridge/OriginalSignedFourierRegularity
   mirror-E: none(waiver:literal-line-L2-translation)
   anchors: []
   utility: none
   digest: Two-boundary translation regularity of literal Ioc signed Fourier heads. -/

import D5.S3.Weil.ZetaBridge.OriginalSignedPrimeFourier
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
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
  rw [inv_pow, Real.sq_sqrt hL.le]

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
  have hip : Integrable (fun x => conj (F x) * G x) := by
    have H := L2.integrable_inner (𝕜 := ℂ) (hF.toLp F) (hG.toLp G)
    apply H.congr
    filter_upwards [hF.coeFn_toLp, hG.coeFn_toLp] with x hx hy
    simp [hx, hy, RCLike.inner_apply', mul_comm]
  have hcorr : ∫ x, conj (F x) * G x = entry L n n h := by
    rw [entry, pairing_line]
    rfl
  let E := fun x => ‖F x - G x‖ ^ 2
  let A := Ioc (-(L / 2)) (-(L / 2) + h)
  let B := Ioc (-(L / 2) + h) (L / 2)
  let C := Ioc (L / 2) (L / 2 + h)
  have hiE : Integrable E :=
    (memLp_two_iff_integrable_sq_norm (hF.sub hG).aestronglyMeasurable).mp (hF.sub hG)
  have hAB : Disjoint A B := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact (not_lt_of_ge hx.2) hy.1
  have hABC : Disjoint (A ∪ B) C := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    rcases hx with hx | hx
    · have := hx.2
      have := hy.1
      dsimp [A, C] at *
      linarith
    · exact (not_lt_of_ge hx.2) hy.1
  have hsupport : ∀ x, x ∉ (A ∪ B) ∪ C → E x = 0 := by
    intro x hx
    have hout : x ≤ -(L / 2) ∨ L / 2 + h < x := by
      dsimp [A, B, C] at hx
      simp only [mem_union, mem_Ioc, not_or, not_and, not_le] at hx
      by_cases ha : x ≤ -(L / 2)
      · exact Or.inl ha
      · right
        have hxa : -(L / 2) < x := lt_of_not_ge ha
        have hxb := hx.1.1 hxa
        have hxc := hx.1.2 hxb
        exact hx.2 hxc
    have hxF : x ∉ window (L / 2) := by
      rcases hout with hx | hx <;> simp only [window, mem_Ioc] <;> intro hz <;> linarith [hz.1, hz.2]
    have hxG : x - h ∉ window (L / 2) := by
      rcases hout with hx | hx <;> simp only [window, mem_Ioc] <;> intro hz <;> linarith [hz.1, hz.2]
    simp [E, F, G, lineMode, zeroExtension, hxF, hxG]
  have hpartition : translationSquaredNorm L n h =
      (∫ x in A, E x) + (∫ x in B, E x) + ∫ x in C, E x := by
    change (∫ x, E x) = _
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hsupport,
      setIntegral_union hABC measurableSet_Ioc (hiE.integrableOn) (hiE.integrableOn),
      setIntegral_union hAB measurableSet_Ioc (hiE.integrableOn) (hiE.integrableOn)]
  have hcross : (∫ x in B, conj (F x) * G x) = entry L n n h := by
    rw [← hcorr]
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    by_cases hxF : x ∈ window (L / 2)
    · have hxG : x - h ∉ window (L / 2) := by
        intro hz
        apply hx
        exact ⟨by linarith [hz.1], hxF.2⟩
      simp [G, lineMode, zeroExtension, hxG]
    · simp [F, lineMode, zeroExtension, hxF]
  have hoverlap : (∫ x in B, E x) =
      2 * ((L - h) / L) - 2 * (entry L n n h).re := by
    have he : (∫ x in B, E x) =
        ∫ x in B, (2 * L⁻¹ - 2 * (conj (F x) * G x).re) := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro x hx
      have hxF : x ∈ window (L / 2) := ⟨by linarith [hx.1], hx.2⟩
      have hxG : x - h ∈ window (L / 2) := ⟨by linarith [hx.1], by linarith [hx.2]⟩
      have hf : ‖F x‖ ^ 2 = L⁻¹ := by simp [F, lineMode, zeroExtension, hxF, mode_norm_sq L hL]
      have hg : ‖G x‖ ^ 2 = L⁻¹ := by simp [G, lineMode, zeroExtension, hxG, mode_norm_sq L hL]
      dsimp [E]
      rw [show ‖F x - G x‖ ^ 2 = ‖F x‖ ^ 2 - 2 * (conj (F x) * G x).re + ‖G x‖ ^ 2 by
        simpa [RCLike.inner_apply', mul_comm] using norm_sub_sq (𝕜 := ℂ) (F x) (G x), hf, hg]
      ring
    have hic : IntegrableOn (fun _ : ℝ => 2 * L⁻¹) B volume :=
      integrableOn_const (show volume B ≠ ⊤ from measure_Ioc_lt_top.ne)
    have hir : IntegrableOn (fun x => 2 * (conj (F x) * G x).re) B volume :=
      (hip.re.const_mul 2).integrableOn
    have hre : (∫ x in B, (conj (F x) * G x).re) =
        (∫ x in B, conj (F x) * G x).re := integral_re hip.integrableOn
    rw [he, integral_sub hic hir]
    simp_rw [integral_const_mul]
    rw [hre, hcross, setIntegral_const]
    dsimp [B]
    rw [Real.volume_real_Ioc, max_eq_left (by linarith : 0 ≤ L / 2 - (-(L / 2) + h))]
    ring
  obtain ⟨hleft, hright⟩ := boundary_strip_energies L hL n h hh hcap
  change (∫ x in A, E x) = h / L at hleft
  change (∫ x in C, E x) = h / L at hright
  rw [hpartition, hleft, hright, hoverlap]
  have hp := entry_paired L hL n n h hh hcap
  rw [entry_adjoint] at hp
  rw [ite_eq_left (show n = n from rfl)] at hp
  have hr := congrArg Complex.re hp
  simp only [Complex.add_re, Complex.conj_re, Complex.ofReal_re] at hr
  field_simp [hL.ne'] at hr ⊢
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

/-- A subject-local line L2 representative of the actual displaced mode.
It is a consumer of the literal integral estimate, not a replacement domain. -/
def displacedMode (L : ℝ) (hL : 0 < L) (n : ℤ) (h : ℝ) :
    Lp ℂ 2 (volume : Measure ℝ) :=
  ((line_memLp L hL n).sub (shift_memLp L hL n h)).toLp
    (fun x => lineMode L n x - lineMode L n (x - h))

private lemma displacedMode_energy (L : ℝ) (hL : 0 < L) (n : ℤ) (h : ℝ) :
    ‖displacedMode L hL n h‖ ^ 2 = translationSquaredNorm L n h := by
  rw [OriginalEvenCosineComplete.l2_energy volume]
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


/-- The finite head majorant retains both the sqrt(h) boundary contribution
and the h interior contribution, for every signed finite mode set. -/
theorem finite_head_translation_bound (L : ℝ) (hL : 0 < L) (S : Finset ℤ)
    (v : ℤ → ℂ) (h : ℝ) (hh : 0 ≤ h) (hcap : h ≤ L) :
    ‖displacedHead L hL S v h‖ ≤
      (Real.sqrt (2 / L) * ∑ n ∈ S, ‖v n‖) * Real.sqrt h +
        (∑ n ∈ S, ‖v n‖ * |frequency L n|) * h := by
  classical
  let d := fun n x => lineMode L n x - lineMode L n (x - h)
  have hm (n : ℤ) : MemLp (d n) 2 (volume : Measure ℝ) :=
    (line_memLp L hL n).sub (shift_memLp L hL n h)
  have hphysical : lpNorm (fun x => zeroExtension (L / 2) (head L S v) x -
      zeroExtension (L / 2) (head L S v) (x - h)) 2 volume ≤
      (Real.sqrt (2 / L) * ∑ n ∈ S, ‖v n‖) * Real.sqrt h +
        (∑ n ∈ S, ‖v n‖ * |frequency L n|) * h := by
    have he : (fun x => zeroExtension (L / 2) (head L S v) x -
        zeroExtension (L / 2) (head L S v) (x - h)) = ∑ n ∈ S, v n • d n := by
      funext x
      have hext (y : ℝ) : zeroExtension (L / 2) (head L S v) y =
          ∑ n ∈ S, v n * lineMode L n y := by
        by_cases hy : y ∈ window (L / 2) <;> simp [zeroExtension, head, lineMode, hy]
      simp only [hext x, hext (x - h), Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
        d, mul_sub, Finset.sum_sub_distrib]
    rw [he]
    calc
      _ ≤ ∑ n ∈ S, lpNorm (v n • d n) 2 volume :=
        lpNorm_sum_le (fun n _ => (hm n).const_smul (v n)) (by norm_num)
      _ ≤ ∑ n ∈ S, ‖v n‖ *
          (Real.sqrt (2 / L) * Real.sqrt h + |frequency L n| * h) := by
        apply Finset.sum_le_sum
        intro n _
        rw [lpNorm_const_smul]
        have hb := displacedMode_bound L hL n h hh hcap
        rw [displacedMode, Lp.norm_toLp] at hb
        exact mul_le_mul_of_nonneg_left hb (norm_nonneg (v n))
      _ = _ := by
        simp only [mul_add, ← mul_assoc, Finset.sum_add_distrib, ← Finset.sum_mul]
        ring
  rw [Lp.norm_def, eLpNorm_congr_ae (displacedHead_ae L hL S v h)]
  exact hphysical

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


end OriginalSignedFourierRegularity
