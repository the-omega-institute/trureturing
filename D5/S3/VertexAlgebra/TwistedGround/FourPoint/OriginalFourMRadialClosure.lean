/- GID: D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMRadialClosure
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMRadialClosure
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Transfer of the common physical coefficient comparisons to the original channels. -/

import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMDLipRadialChannel
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMRadialChannels
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMWordMarks

/-! The normalized A and B readouts and the actual D boundary share a
single marked coefficient of the physical product. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalFourMDLipMean

open Complex LatticeGeneratingFieldLocality
open LatticeHalfFockChargedCoefficients (omega)
open OriginalFourMActualChart (Chart Puncture parameter)
open OriginalFourMPhysicalProduct (physicalProduct)
open OriginalFourMSpatialWick (spatialCoefficient)
open OriginalFourMWordMarks (WordMark wordMarkList wordMarkMode wordMarkList_maps
  wordMarkList_puncture wordMarkList_nodup wordMarkMode_finite_box)
open OriginalFourMChargeCoset (quadraticSign fourierSign oscillatorLower slitChannelA slitChannelB
  dLipChannel identityK identityK_of_real_interval_crossing)
open OriginalFourPointChartGluing (rA rB)
open LatticeTwistedGroundRealization.SignQuotient (ModTwoCharge)
open D5.S3.Analytic.OriginalHalfBinomialDiskCorrection (disk)
open private creationWord punctureWords from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMSewnProjection
open private slitLaurent from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMSlitChartGerms
open private Word MarkedCoefficient from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMRadialChannels

private def wordChartJet (D : LatticeData) (hu : IsUnit D.G.det)
    (words : Puncture → List (Index D)) (x : ℝ) (c : Chart) (a : ModTwoCharge D) : ℂ := by
  classical
  let l := (punctureWords (wordMarkList words)).flatMap Prod.snd
  exact spatialCoefficient (Sum.elim (fun i => (wordMarkMode words i).2) (fun _ => 1))
    (l.map Sum.inr ++ l.map Sum.inl) (fun z : (WordMark words ⊕ WordMark words) → ℂ =>
      physicalProduct D hu Sigma.fst (fun i => (wordMarkMode words i).1) true x c a
        (z ∘ Sum.inl) (z ∘ Sum.inr)) 0

/-- The original real chart equations follow once the A and B radial
projectors are evaluated. The D readout and the phase cancellation use
the same finite labels for all real points of the overlap. -/
private theorem crossing_of_radial_word_readouts (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (h24 : D.rank = 24)
    (words : Puncture → List (Index D)) (H K L : ℕ) (m n r : ℤ)
    (hP : (creationWord D (words .P)).IsWeightedHomogeneous
      (fun i => (omega D i : ℤ)) (2 * (H : ℤ) - 3))
    (hQ : (creationWord D (words .Q)).IsWeightedHomogeneous
      (fun i => (omega D i : ℤ)) (2 * (K : ℤ) - 3))
    (hR : (creationWord D (words .R)).IsWeightedHomogeneous
      (fun i => (omega D i : ℤ)) (2 * (L : ℤ) - 3))
    (hS : (creationWord D (words .S)).IsWeightedHomogeneous
      (fun i => (omega D i : ℤ)) (2 * ((H : ℤ) + K + L - (m+n+r) - 2) - 3)) :
    let P := creationWord D (words .P)
    let Q := creationWord D (words .Q)
    let R := creationWord D (words .R)
    let S := creationWord D (words .S)
    let s := m+n+r
    let common := fun x : ℝ => -I * ((x : ℂ) ^ (-s-5) * (1 - (x : ℂ)) ^ (3 : ℕ))
    (∀ a x, 1/2 < x → x < 1 →
      wordChartJet D hu words x .A a =
        common x * slitLaurent D H K s P Q R S a (rA (x : ℂ))) →
    (∀ a x, 1/2 < x → x < 1 →
      wordChartJet D hu words x .B a =
        common x * (x : ℂ) ^ (6 : ℕ) * (x : ℂ) ^ (s+2) *
          slitChannelB D H K L m n r P Q R S a (rB (x : ℂ))) →
    ∀ (a : ModTwoCharge D) (x : ℝ), 1/2 < x → x < 1 →
      slitChannelA D H K s P Q R S a (rA (x : ℂ)) =
        (2 : ℂ) ^ 12 * (x : ℂ) ^ (s+2) * slitChannelB D H K L m n r P Q R S a (rB (x : ℂ)) ∧
      slitChannelA D H K s P Q R S a (rA (x : ℂ)) =
        dLipChannel D true H K L m n r P Q R S a (x : ℂ)⁻¹ := by
  classical
  dsimp only
  intro hA hB
  let P := creationWord D (words .P)
  let Q := creationWord D (words .Q)
  let R := creationWord D (words .R)
  let S := creationWord D (words .S)
  let s := m+n+r
  let l := (punctureWords (wordMarkList words)).flatMap Prod.snd
  let common := fun x : ℝ => -I * ((x : ℂ) ^ (-s-5) * (1 - (x : ℂ)) ^ (3 : ℕ))
  obtain ⟨N, hb, hs, hi⟩ := wordMarkMode_finite_box D hu words
  have hcross (a : ModTwoCharge D) (x : ℝ) (hx : 1/2 < x) (hx₁ : x < 1) :
      slitChannelA D H K s P Q R S a (rA (x : ℂ)) =
        (2 : ℂ) ^ 12 * (x : ℂ) ^ (s+2) * slitChannelB D H K L m n r P Q R S a (rB (x : ℂ)) ∧
      slitChannelA D H K s P Q R S a (rA (x : ℂ)) =
        dLipChannel D true H K L m n r P Q R S a (x : ℂ)⁻¹ := by
    have hx₀ : 0 < x := by linarith
    have hxn : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx₀.ne'
    have hxc : 1 - (x : ℂ) ≠ 0 := by
      rw [← ofReal_one, ← ofReal_sub]
      exact ofReal_ne_zero.mpr (sub_ne_zero.mpr hx₁.ne')
    have hcommon : common x ≠ 0 :=
      mul_ne_zero (neg_ne_zero.mpr I_ne_zero) (mul_ne_zero (zpow_ne_zero _ hxn) (pow_ne_zero _ hxc))
    let w := (parameter .A (x : ℂ)) ^ (1/2 : ℂ)
    have hwA : w ^ (2 : ℕ) = parameter .A (x : ℂ) := by
      unfold w
      rw [← Complex.cpow_mul_nat]
      norm_num
    have hw : ‖w‖ < 1 := by
      have hi₀ : 1 < x⁻¹ := (one_lt_inv₀ hx₀).2 hx₁
      have hi₂ : x⁻¹ < 2 := by
        rw [← one_div, div_lt_iff₀ hx₀]
        linarith
      have ha : ‖parameter .A (x : ℂ)‖ < 1 := by
        rw [parameter, ← ofReal_inv, ← ofReal_one, ← ofReal_sub, Complex.norm_real,
          Real.norm_of_nonpos (sub_nonpos.mpr hi₀.le)]
        linarith
      rw [← hwA, norm_pow] at ha
      nlinarith [norm_nonneg w]
    have h := physical_weighted_crossing D hu hD h24
      (Sigma.fst : WordMark words → Puncture) (fun i => (wordMarkMode words i).1)
      hx₀ hx₁ hwA hw (Sum.elim (fun i => (wordMarkMode words i).2) (fun _ => 1))
      (l.map Sum.inr ++ l.map Sum.inl) a
    change
      (∑ b, quadraticSign D b * fourierSign D b a * wordChartJet D hu words x .A b) =
        (2 : ℂ) ^ (12 : ℕ) * ((x : ℂ) ^ (6 : ℕ))⁻¹ * wordChartJet D hu words x .B a ∧
      (∑ b, quadraticSign D (b+a) * wordChartJet D hu words x .D b) =
        (2 : ℂ) ^ (12 : ℕ) * ((x : ℂ) ^ (6 : ℕ))⁻¹ * wordChartJet D hu words x .B a at h
    have ha : (∑ b, quadraticSign D b * fourierSign D b a * wordChartJet D hu words x .A b) =
        common x * slitChannelA D H K s P Q R S a (rA (x : ℂ)) := by
      unfold slitChannelA
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      rw [hA b x hx hx₁]
      ring
    have hd : (∑ b, quadraticSign D (b+a) * wordChartJet D hu words x .D b) =
        common x * dLipChannel D true H K L m n r P Q R S a (x : ℂ)⁻¹ := by
      unfold dLipChannel
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      have hv := dLip_radial_channel D hu hD b N H K L m n r hx₀ hx₁
        (Sigma.fst : WordMark words → Puncture) (wordMarkMode words) hb
        (wordMarkList words) (wordMarkList_puncture words) (wordMarkList_nodup words)
        (by simpa only [wordMarkList_maps] using hi .D x)
        (by simpa only [wordMarkList_maps] using hs)
        (by simpa only [wordMarkList_maps] using hP) (by simpa only [wordMarkList_maps] using hQ)
        (by simpa only [wordMarkList_maps] using hR) (by simpa only [wordMarkList_maps] using hS)
      change wordChartJet D hu words x .D b = _ at hv
      rw [hv]
      simp only [wordMarkList_maps, parameter]
      ring
    have hab := h.1
    rw [ha, hB a x hx hx₁] at hab
    have htarget : common x * slitChannelA D H K s P Q R S a (rA (x : ℂ)) =
        common x * ((2 : ℂ) ^ 12 * (x : ℂ) ^ (s+2) *
          slitChannelB D H K L m n r P Q R S a (rB (x : ℂ))) := by
      rw [hab]
      field_simp [hxn]
      ring
    refine ⟨mul_left_cancel₀ hcommon htarget, ?_⟩
    have hAD := h.1.trans h.2.symm
    rw [ha, hd] at hAD
    exact mul_left_cancel₀ hcommon hAD
  exact hcross

set_option maxHeartbeats 4000000 in
/-- The three actual radial chart readouts cross on the real overlap for four
creation words of the required weights. -/
theorem radial_word_crossings (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (h24 : D.rank = 24)
    (words : Puncture → List (Index D)) (H K L : ℕ) (m n r : ℤ)
    (hP : (creationWord D (words .P)).IsWeightedHomogeneous
      (fun i => (omega D i : ℤ)) (2 * (H : ℤ) - 3))
    (hQ : (creationWord D (words .Q)).IsWeightedHomogeneous
      (fun i => (omega D i : ℤ)) (2 * (K : ℤ) - 3))
    (hR : (creationWord D (words .R)).IsWeightedHomogeneous
      (fun i => (omega D i : ℤ)) (2 * (L : ℤ) - 3))
    (hS : (creationWord D (words .S)).IsWeightedHomogeneous
      (fun i => (omega D i : ℤ)) (2 * ((H : ℤ) + K + L - (m+n+r) - 2) - 3)) :
    let P := creationWord D (words .P)
    let Q := creationWord D (words .Q)
    let R := creationWord D (words .R)
    let S := creationWord D (words .S)
    let s := m+n+r
    ∀ (a : ModTwoCharge D) (x : ℝ), 1/2 < x → x < 1 →
      slitChannelA D H K s P Q R S a (rA (x : ℂ)) =
        (2 : ℂ) ^ 12 * (x : ℂ) ^ (s+2) * slitChannelB D H K L m n r P Q R S a (rB (x : ℂ)) ∧
      slitChannelA D H K s P Q R S a (rA (x : ℂ)) =
        dLipChannel D true H K L m n r P Q R S a (x : ℂ)⁻¹ := by
  classical
  let P := creationWord D (words .P)
  let Q := creationWord D (words .Q)
  let R := creationWord D (words .R)
  let S := creationWord D (words .S)
  let s := m+n+r
  let common := fun x : ℝ => -I * ((x : ℂ) ^ (-s-5) * (1 - (x : ℂ)) ^ (3 : ℕ))
  obtain ⟨N, hb, hs, hi⟩ := wordMarkMode_finite_box D hu words
  have readouts (a : ModTwoCharge D) (x : ℝ) (hx : 1/2 < x) (hx₁ : x < 1) :
      wordChartJet D hu words x .A a =
        common x * slitLaurent D H K s P Q R S a (rA (x : ℂ)) ∧
      wordChartJet D hu words x .B a =
        common x * (x : ℂ) ^ (6 : ℕ) * (x : ℂ) ^ (s+2) *
          slitChannelB D H K L m n r P Q R S a (rB (x : ℂ)) := by
    have hx₀ : 0 < x := by linarith
    have hA : ‖parameter .A (x : ℂ)‖ < 1 := by
      have h₁ : 1 < x⁻¹ := (one_lt_inv₀ hx₀).2 hx₁
      have h₂ : x⁻¹ < 2 := by
        rw [← one_div, div_lt_iff₀ hx₀]
        linarith
      rw [parameter, ← ofReal_inv, ← ofReal_one, ← ofReal_sub, Complex.norm_real,
        Real.norm_of_nonpos (sub_nonpos.mpr h₁.le)]
      linarith
    have hB : ‖parameter .B (x : ℂ)‖ < 1 := by
      simpa only [parameter, Complex.norm_real, Real.norm_of_nonneg hx₀.le] using hx₁
    have root (z : ℂ) (hz : ‖z‖ < 1) :
        ∃ w : ℂ, w ^ 2 = z ∧ ‖w‖ < 1 := by
      refine ⟨z ^ (1/2 : ℂ), ?_, ?_⟩
      · rw [← Complex.cpow_mul_nat]
        norm_num
      · have sq : (z ^ (1/2 : ℂ)) ^ (2 : ℕ) = z := by
          rw [← Complex.cpow_mul_nat]
          norm_num
        rw [← sq, norm_pow] at hz
        nlinarith [norm_nonneg (z ^ (1/2 : ℂ))]
    obtain ⟨wA, hwA, hwa⟩ := root _ hA
    obtain ⟨wB, hwB, hwb⟩ := root _ hB
    have hNomeA := radial_nome_eq_chart hx₀ hx₁ true .A (Or.inl rfl)
      (by simpa [disk, Metric.mem_ball, dist_zero_right] using hA)
    have hNomeB := radial_nome_eq_chart hx₀ hx₁ true .B (Or.inr rfl)
      (by simpa [disk, Metric.mem_ball, dist_zero_right] using hB)
    have h := OriginalFourMRadialChannels.radial_AB_laurent_readouts D hu hD h24 a
      N H K L m n r hx hx₁ true hwa hwb hwA hwB
      (by rwa [hwA]) (by rwa [hwB])
      (Sigma.fst : WordMark words → Puncture) (wordMarkMode words) hb
      (wordMarkList words) (wordMarkList_puncture words) (wordMarkList_nodup words)
      (by simpa only [wordMarkList_maps] using fun c => hi c x)
      (by simpa only [Word, wordMarkList_maps] using hs)
      (by simpa only [Word, wordMarkList_maps] using hP)
      (by simpa only [Word, wordMarkList_maps] using hQ)
      (by simpa only [Word, wordMarkList_maps] using hR)
      (by simpa only [Word, wordMarkList_maps] using hS)
    dsimp only at h
    refine ⟨?_, ?_⟩
    · simpa only [Word, wordMarkList_maps, MarkedCoefficient, wordChartJet, P, Q, R, S,
        s, common, parameter, rA] using h.1
    · simpa only [Word, wordMarkList_maps, MarkedCoefficient, wordChartJet, P, Q, R, S,
        s, common, parameter, rB, mul_comm ((x : ℂ) ^ (6 : ℕ))
          (-I * ((x : ℂ) ^ (-(m+n+r)-5) * (1 - (x : ℂ)) ^ (3 : ℕ)))] using h.2
  exact crossing_of_radial_word_readouts D hu hD h24 words H K L m n r hP hQ hR hS
    (fun a x hx hx₁ => (readouts a x hx hx₁).1)
    (fun a x hx hx₁ => (readouts a x hx hx₁).2)

end D5.S3.VertexAlgebra.TwistedGround.OriginalFourMDLipMean
