/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveFourth/CommonGapClearing
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A common Vandermonde factor clears three-value four-copy gap denominators. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveFourth.FourthGapPolynomial

/-! The signed common denominator for the three multiplicity patterns. -/

namespace RefinedBMV.ThreeBlockGram.PositiveSpectrum

section Polynomial

variable {R : Type*} [Add R] [Sub R] [Mul R] [Pow R ℕ]
  [OfNat R 1] [OfNat R 2] [OfNat R 3] [OfNat R 6] [OfNat R 12]

def spectralVandermonde (a b c : R) : R := (a - b) * (a - c) * (b - c)

def commonThreeOne (p a b c u v : R) : R :=
  (a - c)^3 * (b - c)^3 * threeOnePolynomial p a b u v

def commonTwoTwo (p a b c u v : R) : R :=
  (a - c)^3 * (b - c)^3 * twoTwoPolynomial p a b u v

def commonTwoOneOne (p a b c u v w : R) : R :=
  (a - b) * (a - c) * (b - c)^2 * twoOneOnePolynomial p a b c u v w

end Polynomial

theorem commonThreeOne_eq (p : ℕ) {r t : ℝ} (s : ℝ) (hr : 0 ≤ r) (ht : 0 ≤ t) :
    commonThreeOne (p : ℝ) (r^4) (t^4) (s^4) (r^p) (t^p) =
      6 * spectralVandermonde (r^4) (t^4) (s^4)^3 *
        FourCopyGap.gapDefect p (r^4) (r^4) (r^4) (t^4) := by
  unfold commonThreeOne spectralVandermonde
  rw [threeOnePolynomial_eq p hr ht]
  ring

theorem commonTwoTwo_eq (p : ℕ) {r t : ℝ} (s : ℝ) (hr : 0 ≤ r) (ht : 0 ≤ t) :
    commonTwoTwo (p : ℝ) (r^4) (t^4) (s^4) (r^p) (t^p) =
      6 * spectralVandermonde (r^4) (t^4) (s^4)^3 *
        FourCopyGap.gapDefect p (r^4) (r^4) (t^4) (t^4) := by
  unfold commonTwoTwo spectralVandermonde
  rw [twoTwoPolynomial_eq p hr ht]
  ring

theorem commonTwoOneOne_eq (p : ℕ) {r t s : ℝ} (hr : 0 ≤ r) (ht : 0 ≤ t)
    (hs : 0 ≤ s) :
    commonTwoOneOne (p : ℝ) (r^4) (t^4) (s^4) (r^p) (t^p) (s^p) =
      6 * spectralVandermonde (r^4) (t^4) (s^4)^3 *
        FourCopyGap.gapDefect p (r^4) (r^4) (t^4) (s^4) := by
  unfold commonTwoOneOne spectralVandermonde
  rw [twoOneOnePolynomial_eq p hr ht hs]
  ring

/-- The twelve inputs of the six Gram signs, in order of the six triple-single
entries, the three double-single-single entries and the three double-double entries. -/
def clearedSpectralEntries {R : Type*} [Add R] [Sub R] [Mul R] [Neg R] [Pow R ℕ]
    [OfNat R 1] [OfNat R 2] [OfNat R 3] [OfNat R 6] [OfNat R 12]
    (p a b c u v w : R) : Fin 12 → R :=
  ![-commonThreeOne p a b c u v, commonThreeOne p a c b u w,
    commonThreeOne p b a c v u, -commonThreeOne p b c a v w,
    -commonThreeOne p c a b w u, commonThreeOne p c b a w v,
    -commonTwoOneOne p a b c u v w, commonTwoOneOne p b a c v u w,
    -commonTwoOneOne p c a b w u v,
    -commonTwoTwo p a b c u v, commonTwoTwo p a c b u w, -commonTwoTwo p b c a v w]

private noncomputable def spectralEntryDefects (p : ℕ) (a b c : ℝ) : Fin 12 → ℝ :=
  let D := FourCopyGap.gapDefect p
  ![D a a a b, D a a a c, D b b b a, D b b b c, D c c c a, D c c c b,
    D a a b c, D b b a c, D c c a b, D a a b b, D a a c c, D b b c c]

/-- A single common factor relates all twelve polynomial values to the
spectral defects. The factor is positive on a strictly increasing spectrum. -/
theorem clearedSpectralEntries_eq (p : ℕ) {r t s : ℝ}
    (hr : 0 ≤ r) (ht : 0 ≤ t) (hs : 0 ≤ s) (i : Fin 12) :
    clearedSpectralEntries (p : ℝ) (r^4) (t^4) (s^4) (r^p) (t^p) (s^p) i =
      6 * (-spectralVandermonde (r^4) (t^4) (s^4))^3 *
        spectralEntryDefects p (r^4) (t^4) (s^4) i := by
  fin_cases i <;>
    simp [clearedSpectralEntries, spectralEntryDefects, commonThreeOne_eq, commonTwoTwo_eq,
      commonTwoOneOne_eq, hr, ht, hs, spectralVandermonde] <;> ring_nf <;> simp

end RefinedBMV.ThreeBlockGram.PositiveSpectrum
