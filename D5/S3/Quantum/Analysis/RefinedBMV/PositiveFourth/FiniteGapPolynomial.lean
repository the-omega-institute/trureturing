/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveFourth/FiniteGapPolynomial
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A direct polynomial representation of the finite-degree four-copy gaps. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveFourth.CommonGapClearing
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveFourth.PositiveGramQuartic

/-! The finite-degree calculation uses the composition sum and needs no
Vandermonde denominator. -/

open scoped BigOperators

namespace RefinedBMV.ThreeBlockGram.PositiveSpectrum

def finiteGapPolynomial {R : Type*} [CommRing R] (p : ℕ) (a b c d : R) : R :=
  (∑ g ∈ FourCopyGap.gaps p, (a^4)^g.1 * (b^4)^g.2.1 * (c^4)^g.2.2.1 * (d^4)^g.2.2.2) -
    ((FourCopyGap.gaps p).card : R) * (a*b*c*d)^p

open private monomial balanced from D5.S3.Quantum.Analysis.RefinedBMV.SingularFourth.FourCopyGap
open private fourth_rpow from D5.S3.Quantum.Analysis.RefinedBMV.PositiveFourth.FourthGapPolynomial

theorem finiteGapPolynomial_eq (p : ℕ) {a b c d : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    finiteGapPolynomial p a b c d = FourCopyGap.gapDefect p (a^4) (b^4) (c^4) (d^4) := by
  rw [finiteGapPolynomial, FourCopyGap.gapDefect]
  have h (g : FourCopyGap.Gap) :
      (a^4)^g.1 * (b^4)^g.2.1 * (c^4)^g.2.2.1 * (d^4)^g.2.2.2 =
        monomial (a^4) (b^4) (c^4) (d^4) g := rfl
  simp only [h, balanced, fourth_rpow p ha, fourth_rpow p hb,
    fourth_rpow p hc, fourth_rpow p hd, mul_pow]

def finiteSpectralEntries {R : Type*} [CommRing R] (p : ℕ) (a b c : R) : Fin 12 → R :=
  let D := finiteGapPolynomial p
  ![D a a a b, D a a a c, D b b b a, D b b b c, D c c c a, D c c c b,
    D a a b c, D b b a c, D c c a b, D a a b b, D a a c c, D b b c c]

open private spectralEntryDefects
  from D5.S3.Quantum.Analysis.RefinedBMV.PositiveFourth.CommonGapClearing

theorem finiteSpectralEntries_eq (p : ℕ) {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (i : Fin 12) :
    finiteSpectralEntries p a b c i = spectralEntryDefects p (a^4) (b^4) (c^4) i := by
  fin_cases i <;>
    simp [finiteSpectralEntries, spectralEntryDefects, finiteGapPolynomial_eq, ha, hb, hc]

open private gapDefect_scale
  from D5.S3.Quantum.Analysis.RefinedBMV.SingularFourth.ZeroSpectrumAllocation

/-- Reciprocal gap variables turn the finite-degree check into ordinary
polynomial positivity on the nonnegative quadrant. -/
theorem sixSigns_of_reciprocalEntries (p : ℕ) {r t : ℝ}
    (hr : 0 < r) (ht : 0 < t)
    (hsigns : (QuarticData.ofGapEntries
      (finiteSpectralEntries p 1 r⁻¹ (r⁻¹ * t⁻¹))).SixSigns) :
    (kernelQuarticData (fun i j k l ↦
      2 * spectralDefect p ![r^4*t^4, t^4, 1] i j k l)).SixSigns := by
  let c := r^4 * t^4
  let s : Fin 3 → ℝ := ![r^4*t^4, t^4, 1]
  let u : Fin 3 → ℝ := ![1, (r⁻¹)^4, (r⁻¹*t⁻¹)^4]
  have hu (i : Fin 3) : 0 ≤ u i := by fin_cases i <;> simp [u] <;> positivity
  have hc : 0 < c := mul_pos (pow_pos hr _) (pow_pos ht _)
  have hs (i : Fin 3) : s i = c * u i := by
    fin_cases i <;> simp [s, c, u, mul_pow] <;> field_simp [hr.ne', ht.ne'] <;> ring
  let D := spectralDefect p s
  let E := spectralDefect p u
  have hscale (i j k l : Fin 3) : D i j k l = c^p * E i j k l := by
    change FourCopyGap.gapDefect p (s i) (s j) (s k) (s l) =
      c^p * FourCopyGap.gapDefect p (u i) (u j) (u k) (u l)
    rw [hs i, hs j, hs k, hs l, gapDefect_scale p hc.le (hu i) (hu j) (hu k) (hu l)]
  have he : finiteSpectralEntries p (1 : ℝ) r⁻¹ (r⁻¹*t⁻¹) =
      ![f E 0 1, f E 0 2, f E 1 0, f E 1 2, f E 2 0, f E 2 1,
        h E 0 1 2, h E 1 0 2, h E 2 0 1, g E 0 1, g E 0 2, g E 1 2] := by
    funext j
    rw [finiteSpectralEntries_eq p zero_le_one (inv_nonneg.mpr hr.le)
      (mul_nonneg (inv_nonneg.mpr hr.le) (inv_nonneg.mpr ht.le))]
    fin_cases j <;> simp [spectralEntryDefects, E, spectralDefect, f, g, h, u]
  change (kernelQuarticData (fun i j k l ↦ 2 * D i j k l)).SixSigns
  rw [← quarticData_of_gapEntries D]
  have hcp := pow_pos hc p
  apply QuarticData.sixSigns_of_posScale _ (inv_pos.mpr hcp)
  have hentries : (fun j : Fin 12 ↦ (c^p)⁻¹ *
      (![f D 0 1, f D 0 2, f D 1 0, f D 1 2, f D 2 0, f D 2 1,
        h D 0 1 2, h D 1 0 2, h D 2 0 1, g D 0 1, g D 0 2, g D 1 2] : Fin 12 → ℝ) j) =
      finiteSpectralEntries p 1 r⁻¹ (r⁻¹*t⁻¹) := by
    rw [he]
    funext j
    fin_cases j <;> simp [f, g, h, hscale, ← mul_assoc, hcp.ne']
  rw [hentries]
  exact hsigns

end RefinedBMV.ThreeBlockGram.PositiveSpectrum
