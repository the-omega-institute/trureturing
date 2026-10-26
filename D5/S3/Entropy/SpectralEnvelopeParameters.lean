/- GID: D5/S3/Entropy/SpectralEnvelopeParameters
   generality: I
   mirror-B: D5/B/S3/Entropy/SpectralEnvelopeParameters
   mirror-E: none(waiver:exact-real-algebra)
   anchors: []
   utility: none
   digest: Exact parameterization and constants of the three-point spectral envelope. -/

import D5.S3.Entropy.CountableSpectralMoments
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section
open scoped BigOperators

namespace D5.S3.Entropy.SpectralEnvelopeParameters
open CountableSpectralMoments

def envelope (q : ℝ) : ℝ := (10 - 18 * q - (6 * q - 2) * Real.sqrt (6 * q - 2)) / 108
def upperCoordinate (q : ℝ) : ℝ := (2 + Real.sqrt (6 * q - 2)) / 6
def threshold : ℝ := (17 - 5 * Real.sqrt 5) / 16

def threeSpectrum (x : ℝ) : ℕ → ℝ :=
  fun n => if n = 0 then x else if n = 1 then x else if n = 2 then 1 - 2 * x else 0

private theorem three_summable (x : ℝ) : Summable (threeSpectrum x) := by
  apply summable_of_ne_finset_zero (s := Finset.range 3)
  intro n hn
  have h : 3 ≤ n := by simpa using hn
  simp [threeSpectrum, show n ≠ 0 by omega, show n ≠ 1 by omega, show n ≠ 2 by omega]

private theorem three_mass (x : ℝ) : mass (threeSpectrum x) = 1 := by
  unfold mass
  rw [tsum_eq_sum (s := Finset.range 3) (fun n hn => by
    have h : 3 ≤ n := by simpa using hn
    simp [threeSpectrum, show n ≠ 0 by omega, show n ≠ 1 by omega, show n ≠ 2 by omega])]
  norm_num [Finset.sum_range_succ, threeSpectrum]
  ring

private theorem three_purity (x : ℝ) : purity (threeSpectrum x) = 6 * x ^ 2 - 4 * x + 1 := by
  unfold purity
  rw [tsum_eq_sum (s := Finset.range 3) (fun n hn => by
    have h : 3 ≤ n := by simpa using hn
    simp [threeSpectrum, show n ≠ 0 by omega, show n ≠ 1 by omega, show n ≠ 2 by omega])]
  norm_num [Finset.sum_range_succ, threeSpectrum]
  ring

private theorem three_third (x : ℝ) : third (threeSpectrum x) = x ^ 2 * (1 - 2 * x) := by
  unfold third
  rw [tsum_eq_sum (s := Finset.range 3) (fun n hn => by
    have h : 3 ≤ n := by simpa using hn
    simp [tripleLayer, threeSpectrum, show n ≠ 0 by omega,
      show n ≠ 1 by omega, show n ≠ 2 by omega])]
  norm_num [Finset.sum_range_succ, tripleLayer, threeSpectrum]
  ring

private theorem coordinate_bounds {q : ℝ} (hq0 : 1 / 3 ≤ q) (hq1 : q ≤ 3 / 8) :
    1 / 3 ≤ upperCoordinate q ∧ upperCoordinate q ≤ 5 / 12 := by
  have hs0 := Real.sqrt_nonneg (6 * q - 2)
  have hs2 := Real.sq_sqrt (show 0 ≤ 6 * q - 2 by linarith)
  unfold upperCoordinate
  constructor <;> nlinarith

private theorem coordinate_purity {q : ℝ} (hq : 1 / 3 ≤ q) :
    6 * upperCoordinate q ^ 2 - 4 * upperCoordinate q + 1 = q := by
  have hs := Real.sq_sqrt (show 0 ≤ 6 * q - 2 by linarith)
  unfold upperCoordinate
  nlinarith

private theorem coordinate_value {q : ℝ} (hq : 1 / 3 ≤ q) :
    upperCoordinate q ^ 2 * (1 - 2 * upperCoordinate q) = envelope q := by
  have hs := Real.sq_sqrt (show 0 ≤ 6 * q - 2 by linarith)
  unfold upperCoordinate envelope
  nlinarith [congrArg (fun z : ℝ => Real.sqrt (6 * q - 2) * z) hs]

private theorem envelope_antitone {a b : ℝ} (ha : 1 / 3 ≤ a) (hab : a ≤ b) :
    envelope b ≤ envelope a := by
  have har : 0 ≤ 6 * a - 2 := by linarith
  have hbr : 0 ≤ 6 * b - 2 := by linarith
  have hmul : (6 * a - 2) * Real.sqrt (6 * a - 2) ≤
      (6 * b - 2) * Real.sqrt (6 * b - 2) :=
    mul_le_mul (by linarith) (Real.sqrt_le_sqrt (by linarith))
      (Real.sqrt_nonneg _) hbr
  unfold envelope
  linarith

private theorem endpoint_constants : envelope (3 / 8) = 25 / 864 ∧
    (1 : ℝ) / 32 - 25 / 864 = 1 / 432 := by
  have hs : Real.sqrt (1 / 4 : ℝ) = 1 / 2 := by
    apply (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).mpr
    norm_num
  constructor
  · norm_num [envelope, hs]
  · norm_num

private theorem threshold_bounds : 1 / 3 ≤ threshold ∧ threshold ≤ 3 / 8 := by
  have hs0 := Real.sqrt_nonneg (5 : ℝ)
  have hs2 := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  unfold threshold
  constructor <;> nlinarith

private theorem threshold_value : envelope threshold = 1 / 32 := by
  have hs0 := Real.sqrt_nonneg (5 : ℝ)
  have hs2 := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  have harg : 6 * threshold - 2 = ((3 * Real.sqrt 5 - 5) / 4) ^ 2 := by
    unfold threshold
    nlinarith
  have hd : 0 ≤ (3 * Real.sqrt 5 - 5) / 4 := by nlinarith
  have hs : Real.sqrt (6 * threshold - 2) = (3 * Real.sqrt 5 - 5) / 4 := by
    rw [harg, Real.sqrt_sq hd]
  unfold envelope
  rw [hs]
  unfold threshold
  nlinarith [congrArg (fun z : ℝ => Real.sqrt (5 : ℝ) * z) hs2]

end D5.S3.Entropy.SpectralEnvelopeParameters
