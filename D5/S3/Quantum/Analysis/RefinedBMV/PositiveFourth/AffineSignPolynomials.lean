/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveFourth/AffineSignPolynomials
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The six affine four-copy sign expressions and their positive factors. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveFourth.PolynomialSupport

/-! The affine certificates express each sign as a quotient polynomial
times an explicit product of nonnegative factors. -/

namespace RefinedBMV.ThreeBlockGram.PositiveSpectrum

inductive GramSign
  | axisFirst | axisMiddle | axisLast | mixedFirst | mixedMiddle | mixedLast
  deriving DecidableEq

section Polynomial

variable {R : Type*} [Add R] [Sub R] [Mul R] [Neg R] [Pow R ℕ]
  [OfNat R 1] [OfNat R 2] [OfNat R 3] [OfNat R 4] [OfNat R 6] [OfNat R 12]
  [OfNat R 11] [OfNat R 14] [OfNat R 16]

def GramSign.value (sign : GramSign) (q : Fin 12 → R) : R :=
  let s := QuarticData.ofGapEntries q
  match sign with
  | .axisFirst => s.axis1
  | .axisMiddle => s.axis2
  | .axisLast => s.axis3
  | .mixedFirst => s.mixed1
  | .mixedMiddle => s.mixed2
  | .mixedLast => s.mixed3

/-- The first two gap variables are the fourth powers of the spectral ratios. -/
def affineEntries (x r t u v : R) : Fin 12 → R :=
  clearedSpectralEntries (x + 11) (r*t) t 1 (u*v) v 1

def GramSign.removedFactor (sign : GramSign) (x r t u v : R) : R :=
  let q := affineEntries x r t u v
  let A := 1 - r
  let B := 1 - t
  let C := 1 - r*t
  match sign with
  | .axisFirst => 16 * t^12 * v^4 * A^6 * B^8 * C^6
  | .axisMiddle => 16 * t^12 * v^4 * A^6 * B^6 * C^8
  | .axisLast => 16 * t^12 * A^8 * B^6 * C^6
  | .mixedFirst => q 6 * q 7 * t^18 * v^4 * A^12 * B^11 * C^10 * (x+12) * (x+14)
  | .mixedMiddle => (q 6)^2 * (q 7)^2 * t^24 * v^4 * A^18 * B^14 * C^14 * (x+12)^2 * (x+14)^2
  | .mixedLast => q 6 * q 7 * t^18 * v^4 * A^12 * B^10 * C^11 * (x+12) * (x+14)

end Polynomial

theorem GramSign.removedFactor_nonneg (sign : GramSign) {x r t u v : ℝ}
    (hx : 0 ≤ x) (_hr : 0 ≤ r) (hr₁ : r ≤ 1)
    (ht : 0 ≤ t) (ht₁ : t ≤ 1) (_hv : 0 ≤ v)
    (hq₆ : 0 ≤ affineEntries x r t u v 6) (hq₇ : 0 ≤ affineEntries x r t u v 7) :
    0 ≤ sign.removedFactor x r t u v := by
  have hA : 0 ≤ 1 - r := sub_nonneg.mpr hr₁
  have hB : 0 ≤ 1 - t := sub_nonneg.mpr ht₁
  have hC : 0 ≤ 1 - r*t := sub_nonneg.mpr
    ((mul_le_mul_of_nonneg_right hr₁ ht).trans (by simpa using ht₁))
  cases sign <;> simp only [removedFactor] <;> positivity

theorem sixSigns_of_gramSigns (q : Fin 12 → ℝ)
    (h : ∀ sign : GramSign, 0 ≤ sign.value q) : (QuarticData.ofGapEntries q).SixSigns :=
  ⟨h .axisFirst, h .axisMiddle, h .axisLast, h .mixedFirst, h .mixedMiddle, h .mixedLast⟩

private theorem affineEntries_at_degree (p : ℕ) (hp : 11 ≤ p) (r t : ℝ) :
    affineEntries ((p-11 : ℕ) : ℝ) (r^4) (t^4) (r^p) (t^p) =
      clearedSpectralEntries (p : ℝ) ((r*t)^4) (t^4) 1 ((r*t)^p) (t^p) 1 := by
  have h : ((p-11 : ℕ) : ℝ) + 11 = (p : ℝ) := by
    rw [Nat.cast_sub hp]
    norm_num
  simp only [affineEntries, h, mul_pow]

open private spectralEntryDefects
  from D5.S3.Quantum.Analysis.RefinedBMV.PositiveFourth.CommonGapClearing

/-- The signed differences used as removed factors are nonnegative for the
ordered spectrum. This follows from the cyclic arithmetic-geometric mean bound. -/
theorem affineEntries_nonneg_at_degree (p : ℕ) (hp : 11 ≤ p) {r t : ℝ}
    (hr : 0 < r) (hr₁ : r < 1) (ht : 0 < t) (ht₁ : t < 1) (i : Fin 12) :
    0 ≤ affineEntries ((p-11 : ℕ) : ℝ) (r^4) (t^4) (r^p) (t^p) i := by
  have hrt : r*t < t := by simpa using mul_lt_mul_of_pos_right hr₁ ht
  have hrt₀ : 0 ≤ r*t := mul_nonneg hr.le ht.le
  have h01 : (r*t)^4 < t^4 := pow_lt_pow_left₀ hrt hrt₀ (by decide)
  have h12 : t^4 < (1:ℝ)^4 := pow_lt_pow_left₀ ht₁ ht.le (by decide)
  have hV : spectralVandermonde ((r*t)^4) (t^4) ((1:ℝ)^4) < 0 := by
    unfold spectralVandermonde
    exact mul_neg_of_pos_of_neg
      (mul_pos_of_neg_of_neg (sub_neg.mpr h01) (sub_neg.mpr (h01.trans h12)))
      (sub_neg.mpr h12)
  have hentry : 0 ≤ spectralEntryDefects p ((r*t)^4) (t^4) ((1:ℝ)^4) i := by
    fin_cases i <;>
      simp only [spectralEntryDefects] <;>
      apply FourCopyGap.gapDefect_nonneg <;> positivity
  have h := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 6)
    (pow_nonneg (neg_nonneg.mpr hV.le) 3)) hentry
  have he := clearedSpectralEntries_eq p hrt₀ ht.le zero_le_one i
  simp only [one_pow] at he h
  rw [affineEntries_at_degree p hp, he]
  exact h

theorem sixSigns_of_affineQuotients (p : ℕ) (hp : 11 ≤ p) {r t : ℝ}
    (hr : 0 < r) (hr₁ : r < 1) (ht : 0 < t) (ht₁ : t < 1)
    (quotient : GramSign → ℝ) (hquotient : ∀ sign, 0 ≤ quotient sign)
    (hid : ∀ sign,
      sign.removedFactor ((p-11 : ℕ) : ℝ) (r^4) (t^4) (r^p) (t^p) * quotient sign =
        sign.value (affineEntries ((p-11 : ℕ) : ℝ) (r^4) (t^4) (r^p) (t^p))) :
    (QuarticData.ofGapEntries
      (clearedSpectralEntries (p : ℝ) ((r*t)^4) (t^4) 1 ((r*t)^p) (t^p) 1)).SixSigns := by
  rw [← affineEntries_at_degree p hp]
  apply sixSigns_of_gramSigns
  intro sign
  rw [← hid sign]
  refine mul_nonneg (sign.removedFactor_nonneg (by positivity) (by positivity) ?_
    (by positivity) ?_ (by positivity)
    (affineEntries_nonneg_at_degree p hp hr hr₁ ht ht₁ 6)
    (affineEntries_nonneg_at_degree p hp hr hr₁ ht ht₁ 7)) (hquotient sign)
  · exact pow_le_one₀ hr.le hr₁.le
  · exact pow_le_one₀ ht.le ht₁.le

end RefinedBMV.ThreeBlockGram.PositiveSpectrum
