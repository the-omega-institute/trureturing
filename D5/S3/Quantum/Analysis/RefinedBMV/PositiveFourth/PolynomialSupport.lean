/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveFourth/PolynomialSupport
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Polynomial signs transfer to the four-copy Gram kernel. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveFourth.CommonGapClearing
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveFourth.FiniteGapPolynomial
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveFourth.PositiveGramQuartic

/-! The common factor for the twelve entries is positive in the ordered region. -/

namespace RefinedBMV.ThreeBlockGram.PositiveSpectrum

open Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

open private spectralEntryDefects
  from D5.S3.Quantum.Analysis.RefinedBMV.PositiveFourth.CommonGapClearing

theorem sixSigns_of_clearedSpectralEntries (p : ℕ) {r t s : ℝ}
    (hr : 0 ≤ r) (hrt : r < t) (hts : t < s)
    (hsigns : (QuarticData.ofGapEntries
      (clearedSpectralEntries (p : ℝ) (r^4) (t^4) (s^4) (r^p) (t^p) (s^p))).SixSigns) :
    (kernelQuarticData (fun i j k l ↦ 2 * spectralDefect p ![r^4,t^4,s^4] i j k l)).SixSigns := by
  have ht := hr.trans hrt.le
  have hs := ht.trans hts.le
  have hrt₄ : r^4 < t^4 := pow_lt_pow_left₀ hrt hr (by decide)
  have hts₄ : t^4 < s^4 := pow_lt_pow_left₀ hts ht (by decide)
  have hvas : spectralVandermonde (r^4) (t^4) (s^4) < 0 := by
    unfold spectralVandermonde
    exact mul_neg_of_pos_of_neg
      (mul_pos_of_neg_of_neg (sub_neg.mpr hrt₄) (sub_neg.mpr (hrt₄.trans hts₄)))
      (sub_neg.mpr hts₄)
  let c := 6 * (-spectralVandermonde (r^4) (t^4) (s^4))^3
  have hc : 0 < c := mul_pos (by norm_num) (pow_pos (neg_pos.mpr hvas) _)
  let D := spectralDefect p ![r^4,t^4,s^4]
  have hentries : clearedSpectralEntries (p : ℝ) (r^4) (t^4) (s^4) (r^p) (t^p) (s^p) =
      fun i ↦ c * ![f D 0 1, f D 0 2, f D 1 0, f D 1 2, f D 2 0, f D 2 1,
        h D 0 1 2, h D 1 0 2, h D 2 0 1, g D 0 1, g D 0 2, g D 1 2] i := by
    funext i
    rw [clearedSpectralEntries_eq p hr ht hs i]
    fin_cases i <;> rfl
  rw [hentries] at hsigns
  rw [← quarticData_of_gapEntries D]
  exact QuarticData.sixSigns_of_posScale _ hc hsigns

private theorem sixSigns_of_finiteSpectralEntries (p : ℕ) {r t s : ℝ}
    (hr : 0 ≤ r) (ht : 0 ≤ t) (hs : 0 ≤ s)
    (hsigns : (QuarticData.ofGapEntries (finiteSpectralEntries p r t s)).SixSigns) :
    (kernelQuarticData (fun i j k l ↦ 2 * spectralDefect p ![r^4,t^4,s^4] i j k l)).SixSigns := by
  let D := spectralDefect p ![r^4,t^4,s^4]
  have hentries : finiteSpectralEntries p r t s =
      ![f D 0 1, f D 0 2, f D 1 0, f D 1 2, f D 2 0, f D 2 1,
        h D 0 1 2, h D 1 0 2, h D 2 0 1, g D 0 1, g D 0 2, g D 1 2] := by
    funext i
    rw [finiteSpectralEntries_eq p hr ht hs i]
    fin_cases i <;> rfl
  rw [hentries, quarticData_of_gapEntries] at hsigns
  exact hsigns

/-- The direct composition certificates and the affine certificates apply
to complementary ranges of the first degree. -/
theorem product_bound_of_polynomial_signs
    {n : Type*} [Fintype n] [DecidableEq n] (p : ℕ) (hp : 0 < p)
    (A B : Matrix n n ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (s : Fin 3 → ℝ) (hs : ∀ i, 0 < s i) (horder : StrictMono s)
    (hspectrum : ∀ a, ∃ i, hA.isHermitian.eigenvalues a = s i)
    (small : p < 33 → ∀ r t : ℝ, 0 < r → r < 1 → 0 < t → t < 1 →
      (QuarticData.ofGapEntries (finiteSpectralEntries p (r*t) t 1)).SixSigns)
    (large : 33 ≤ p → ∀ r t : ℝ, 0 < r → r < 1 → 0 < t → t < 1 →
      (QuarticData.ofGapEntries
        (clearedSpectralEntries (p : ℝ) ((r*t)^4) (t^4) 1 ((r*t)^p) (t^p) 1)).SixSigns) :
    trace (((A ^ ((p : ℝ) / 4)) * B) ^ 4) ≤ FourCopyGap.wordMean p A B := by
  apply product_bound_of_spectrum_subset_of_sharpSupport p A B hA hB s
    (fun i => (hs i).le) hspectrum
  · intro i j hij
    exact spectralDefect_binary_conditioning p hp s i j (hs i) (hs j) (horder hij).ne
  · apply sharpSupport_of_normalized_positive_spectrum p s hs horder
    intro r t hr hr₁ ht ht₁
    have hrt : r * t < t := by simpa using mul_lt_mul_of_pos_right hr₁ ht
    have hrt₀ : 0 < r * t := mul_pos hr ht
    let values : Fin 3 → ℝ := ![(r*t)^4, t^4, (1:ℝ)^4]
    have hpos (i : Fin 3) : 0 < values i := by
      fin_cases i <;> simp [values, pow_pos, hr, ht]
    have hmono : StrictMono values := by
      apply Fin.strictMono_iff_lt_succ.mpr
      intro i
      fin_cases i
      · exact pow_lt_pow_left₀ hrt hrt₀.le (by decide)
      · exact pow_lt_pow_left₀ ht₁ ht.le (by decide)
    have hsigns :
        (kernelQuarticData (fun i j k l ↦ 2 * spectralDefect p values i j k l)).SixSigns := by
      by_cases h : p < 33
      · exact sixSigns_of_finiteSpectralEntries p hrt₀.le ht.le zero_le_one
          (small h r t hr hr₁ ht ht₁)
      · exact sixSigns_of_clearedSpectralEntries p hrt₀.le hrt ht₁
          (by simpa only [one_pow] using large (by omega) r t hr hr₁ ht ht₁)
    simpa only [values, mul_pow, one_pow] using
      sharpSupport_of_positive_spectrum_signs p hp values hpos hmono hsigns

#print axioms product_bound_of_polynomial_signs

end RefinedBMV.ThreeBlockGram.PositiveSpectrum
