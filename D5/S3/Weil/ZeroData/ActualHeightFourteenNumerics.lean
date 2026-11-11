/- GID: D5/S3/Weil/ZeroData/ActualHeightFourteenNumerics
   generality: I
   mirror-B: none(waiver:evidence-not-specified-by-formal-manifest)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Weil/ZeroData/ActualHeightFourteen.actual_height_gt_fourteen; premises=D5/S3/Weil/ZeroData/ActualHeightFourteenNumerics.h14Gamma,D5/S3/Weil/ZeroData/ActualHeightFourteenNumerics.h14LogPi,D5/S3/Weil/ZeroData/ActualHeightFourteenNumerics.h14Q6_bound,D5/S3/Weil/ZeroData/ActualHeightFourteenNumerics.h14Q8_bound,D5/S3/Weil/ZeroData/ActualHeightFourteenNumerics.h14Q10_bound,D5/S3/Weil/ZeroData/ActualHeightFourteenNumerics.h14Q12_bound,D5/S3/Weil/ZeroData/ActualHeightFourteenNumerics.h14Q14_bound,D5/S3/Weil/ZeroData/ActualHeightFourteenNumerics.h14_kernel_bounds
   digest: Bound the signed five-point von Mangoldt contribution with its complete tail. -/

import D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds
import D5.S3.Weil.ZeroData.ActualHeightFourteenSector
import D5.S3.Arith.GoldenResource.HarmonicGammaTail
import D5.S3.Arith.GoldenResource.RobinRationalBasis

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds

open D5.S3.Weil.ZeroSum
open D5.S3.Weil.ZeroData.UnconditionalCanonicalZeroData
open D5.S3.Zeros.CompletedZeta
open D5.S3.Zeros.Endpoints.FirstLiCoefficientNormalization
open D5.S3.Zeros.Endpoints.FirstLiCoefficientPositivity
open D5.S3.Zeros.Endpoints.XiEndpointValues
open D5.S3.Zeros.Resolvent.XiNormalizedResolvent
open D5.S3.Zeros.Resolvent.XiSquareExteriorRemainder
open D5.S3.Weil.Convention
open scoped BigOperators ComplexConjugate
open scoped BigOperators ComplexConjugate Topology

private def h14QTerm (s n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ s

private def h14Q (s : ℕ) : ℝ :=
  (-deriv riemannZeta (s : ℂ) / riemannZeta s).re

private theorem h14Q_hasSum (s : ℕ) (hs : 2 ≤ s) :
    HasSum (h14QTerm s) (h14Q s) := by
  have hre : 1 < (s : ℂ).re := by
    simp only [Complex.natCast_re]
    exact_mod_cast (show 1 < s by omega)
  have hsum := ArithmeticFunction.LSeriesSummable_vonMangoldt (s := (s : ℂ)) hre
  have he := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div
    (s := (s : ℂ)) hre
  have ht (n : ℕ) : LSeries.term
      (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) (s : ℂ) n =
        ((h14QTerm s n : ℝ) : ℂ) := by
    rw [LSeries.term_of_ne_zero' (by exact_mod_cast (show s ≠ 0 by omega))]
    simp only [Complex.cpow_natCast, h14QTerm, Complex.ofReal_div,
      Complex.ofReal_pow, Complex.ofReal_natCast]
  have hc : HasSum (fun n : ℕ => ((h14QTerm s n : ℝ) : ℂ))
      (-deriv riemannZeta (s : ℂ) / riemannZeta s) := by
    rw [← he]
    exact hsum.hasSum.congr_fun (fun n => (ht n).symm)
  simpa only [h14Q, Complex.ofReal_re] using Complex.hasSum_re hc

private theorem h14Log2 :
    (138629436111989 / 200000000000000 : ℝ) ≤ Real.log 2 ∧
      Real.log 2 ≤ (346573590279973 / 500000000000000 : ℝ) := by
  have hl := Real.sum_range_le_log_div
    (by norm_num : (0 : ℝ) ≤ 1 / 3) (by norm_num : (1 / 3 : ℝ) < 1) 24
  have hu := Real.log_div_le_sum_range_add
    (by norm_num : (0 : ℝ) ≤ 1 / 3) (by norm_num : (1 / 3 : ℝ) < 1) 24
  norm_num [Finset.sum_range_succ] at hl hu
  constructor <;> linarith only [hl, hu]

private theorem h14Log3 :
    (1098612288668109 / 1000000000000000 : ℝ) ≤ Real.log 3 ∧ Real.log 3 ≤ (1098612288668111 / 1000000000000000 : ℝ) := by
  have h := D5.S3.Arith.GoldenResource.RobinRationalBasis.log_expansion_remainder_bound
    (y := (3 / 2 : ℝ)) (by norm_num) (by norm_num) 20
  have he : Real.log (3 / 2 : ℝ) = Real.log 3 - 1 * Real.log 2 := by
    rw [show (3 / 2 : ℝ) = 3 / (2 : ℝ) ^ (1 : ℕ) by norm_num,
      Real.log_div (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  dsimp [D5.S3.Arith.GoldenResource.RobinRationalBasis.logRemainder] at h
  rw [he] at h
  norm_num [D5.S3.Arith.GoldenResource.RobinRationalBasis.atanhPartial,
    D5.S3.Arith.GoldenResource.RobinRationalBasis.atanhParameter,
    Finset.sum_range_succ] at h
  constructor <;> linarith only [h.1, h.2, h14Log2.1, h14Log2.2]

private theorem h14Log5 :
    (1609437912434099 / 1000000000000000 : ℝ) ≤ Real.log 5 ∧ Real.log 5 ≤ (804718956217051 / 500000000000000 : ℝ) := by
  have h := D5.S3.Arith.GoldenResource.RobinRationalBasis.log_expansion_remainder_bound
    (y := (5 / 4 : ℝ)) (by norm_num) (by norm_num) 20
  have he : Real.log (5 / 4 : ℝ) = Real.log 5 - 2 * Real.log 2 := by
    rw [show (5 / 4 : ℝ) = 5 / (2 : ℝ) ^ (2 : ℕ) by norm_num,
      Real.log_div (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  dsimp [D5.S3.Arith.GoldenResource.RobinRationalBasis.logRemainder] at h
  rw [he] at h
  norm_num [D5.S3.Arith.GoldenResource.RobinRationalBasis.atanhPartial,
    D5.S3.Arith.GoldenResource.RobinRationalBasis.atanhParameter,
    Finset.sum_range_succ] at h
  constructor <;> linarith only [h.1, h.2, h14Log2.1, h14Log2.2]

private theorem h14Log7 :
    (121619384315957 / 62500000000000 : ℝ) ≤ Real.log 7 ∧ Real.log 7 ≤ (389182029811063 / 200000000000000 : ℝ) := by
  have h := D5.S3.Arith.GoldenResource.RobinRationalBasis.log_expansion_remainder_bound
    (y := (7 / 4 : ℝ)) (by norm_num) (by norm_num) 20
  have he : Real.log (7 / 4 : ℝ) = Real.log 7 - 2 * Real.log 2 := by
    rw [show (7 / 4 : ℝ) = 7 / (2 : ℝ) ^ (2 : ℕ) by norm_num,
      Real.log_div (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  dsimp [D5.S3.Arith.GoldenResource.RobinRationalBasis.logRemainder] at h
  rw [he] at h
  norm_num [D5.S3.Arith.GoldenResource.RobinRationalBasis.atanhPartial,
    D5.S3.Arith.GoldenResource.RobinRationalBasis.atanhParameter,
    Finset.sum_range_succ] at h
  constructor <;> linarith only [h.1, h.2, h14Log2.1, h14Log2.2]

private theorem h14Log11 :
    (2397895272798369 / 1000000000000000 : ℝ) ≤ Real.log 11 ∧ Real.log 11 ≤ (2397895272798373 / 1000000000000000 : ℝ) := by
  have h := D5.S3.Arith.GoldenResource.RobinRationalBasis.log_expansion_remainder_bound
    (y := (11 / 8 : ℝ)) (by norm_num) (by norm_num) 20
  have he : Real.log (11 / 8 : ℝ) = Real.log 11 - 3 * Real.log 2 := by
    rw [show (11 / 8 : ℝ) = 11 / (2 : ℝ) ^ (3 : ℕ) by norm_num,
      Real.log_div (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  dsimp [D5.S3.Arith.GoldenResource.RobinRationalBasis.logRemainder] at h
  rw [he] at h
  norm_num [D5.S3.Arith.GoldenResource.RobinRationalBasis.atanhPartial,
    D5.S3.Arith.GoldenResource.RobinRationalBasis.atanhParameter,
    Finset.sum_range_succ] at h
  constructor <;> linarith only [h.1, h.2, h14Log2.1, h14Log2.2]

private theorem h14Log13 :
    (512989871492307 / 200000000000000 : ℝ) ≤ Real.log 13 ∧ Real.log 13 ≤ (2564949357461539 / 1000000000000000 : ℝ) := by
  have h := D5.S3.Arith.GoldenResource.RobinRationalBasis.log_expansion_remainder_bound
    (y := (13 / 8 : ℝ)) (by norm_num) (by norm_num) 20
  have he : Real.log (13 / 8 : ℝ) = Real.log 13 - 3 * Real.log 2 := by
    rw [show (13 / 8 : ℝ) = 13 / (2 : ℝ) ^ (3 : ℕ) by norm_num,
      Real.log_div (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  dsimp [D5.S3.Arith.GoldenResource.RobinRationalBasis.logRemainder] at h
  rw [he] at h
  norm_num [D5.S3.Arith.GoldenResource.RobinRationalBasis.atanhPartial,
    D5.S3.Arith.GoldenResource.RobinRationalBasis.atanhParameter,
    Finset.sum_range_succ] at h
  constructor <;> linarith only [h.1, h.2, h14Log2.1, h14Log2.2]

private theorem h14Log17 :
    (1416606672028107 / 500000000000000 : ℝ) ≤ Real.log 17 ∧ Real.log 17 ≤ (2833213344056219 / 1000000000000000 : ℝ) := by
  have h := D5.S3.Arith.GoldenResource.RobinRationalBasis.log_expansion_remainder_bound
    (y := (17 / 16 : ℝ)) (by norm_num) (by norm_num) 20
  have he : Real.log (17 / 16 : ℝ) = Real.log 17 - 4 * Real.log 2 := by
    rw [show (17 / 16 : ℝ) = 17 / (2 : ℝ) ^ (4 : ℕ) by norm_num,
      Real.log_div (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  dsimp [D5.S3.Arith.GoldenResource.RobinRationalBasis.logRemainder] at h
  rw [he] at h
  norm_num [D5.S3.Arith.GoldenResource.RobinRationalBasis.atanhPartial,
    D5.S3.Arith.GoldenResource.RobinRationalBasis.atanhParameter,
    Finset.sum_range_succ] at h
  constructor <;> linarith only [h.1, h.2, h14Log2.1, h14Log2.2]

private theorem h14Log19 :
    (2944438979166439 / 1000000000000000 : ℝ) ≤ Real.log 19 ∧ Real.log 19 ≤ (736109744791611 / 250000000000000 : ℝ) := by
  have h := D5.S3.Arith.GoldenResource.RobinRationalBasis.log_expansion_remainder_bound
    (y := (19 / 16 : ℝ)) (by norm_num) (by norm_num) 20
  have he : Real.log (19 / 16 : ℝ) = Real.log 19 - 4 * Real.log 2 := by
    rw [show (19 / 16 : ℝ) = 19 / (2 : ℝ) ^ (4 : ℕ) by norm_num,
      Real.log_div (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  dsimp [D5.S3.Arith.GoldenResource.RobinRationalBasis.logRemainder] at h
  rw [he] at h
  norm_num [D5.S3.Arith.GoldenResource.RobinRationalBasis.atanhPartial,
    D5.S3.Arith.GoldenResource.RobinRationalBasis.atanhParameter,
    Finset.sum_range_succ] at h
  constructor <;> linarith only [h.1, h.2, h14Log2.1, h14Log2.2]

private theorem h14Log23 :
    (783873553982287 / 250000000000000 : ℝ) ≤ Real.log 23 ∧ Real.log 23 ≤ (3135494215929153 / 1000000000000000 : ℝ) := by
  have h := D5.S3.Arith.GoldenResource.RobinRationalBasis.log_expansion_remainder_bound
    (y := (23 / 16 : ℝ)) (by norm_num) (by norm_num) 20
  have he : Real.log (23 / 16 : ℝ) = Real.log 23 - 4 * Real.log 2 := by
    rw [show (23 / 16 : ℝ) = 23 / (2 : ℝ) ^ (4 : ℕ) by norm_num,
      Real.log_div (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  dsimp [D5.S3.Arith.GoldenResource.RobinRationalBasis.logRemainder] at h
  rw [he] at h
  norm_num [D5.S3.Arith.GoldenResource.RobinRationalBasis.atanhPartial,
    D5.S3.Arith.GoldenResource.RobinRationalBasis.atanhParameter,
    Finset.sum_range_succ] at h
  constructor <;> linarith only [h.1, h.2, h14Log2.1, h14Log2.2]

private theorem h14Log29 :
    (420911978748309 / 125000000000000 : ℝ) ≤ Real.log 29 ∧ Real.log 29 ≤ (3367295829986477 / 1000000000000000 : ℝ) := by
  have h := D5.S3.Arith.GoldenResource.RobinRationalBasis.log_expansion_remainder_bound
    (y := (29 / 16 : ℝ)) (by norm_num) (by norm_num) 20
  have he : Real.log (29 / 16 : ℝ) = Real.log 29 - 4 * Real.log 2 := by
    rw [show (29 / 16 : ℝ) = 29 / (2 : ℝ) ^ (4 : ℕ) by norm_num,
      Real.log_div (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  dsimp [D5.S3.Arith.GoldenResource.RobinRationalBasis.logRemainder] at h
  rw [he] at h
  norm_num [D5.S3.Arith.GoldenResource.RobinRationalBasis.atanhPartial,
    D5.S3.Arith.GoldenResource.RobinRationalBasis.atanhParameter,
    Finset.sum_range_succ] at h
  constructor <;> linarith only [h.1, h.2, h14Log2.1, h14Log2.2]

private theorem h14Log31 :
    (686797440897029 / 200000000000000 : ℝ) ≤ Real.log 31 ∧ Real.log 31 ≤ (68679744089703 / 20000000000000 : ℝ) := by
  have h := D5.S3.Arith.GoldenResource.RobinRationalBasis.log_expansion_remainder_bound
    (y := (31 / 16 : ℝ)) (by norm_num) (by norm_num) 20
  have he : Real.log (31 / 16 : ℝ) = Real.log 31 - 4 * Real.log 2 := by
    rw [show (31 / 16 : ℝ) = 31 / (2 : ℝ) ^ (4 : ℕ) by norm_num,
      Real.log_div (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  dsimp [D5.S3.Arith.GoldenResource.RobinRationalBasis.logRemainder] at h
  rw [he] at h
  norm_num [D5.S3.Arith.GoldenResource.RobinRationalBasis.atanhPartial,
    D5.S3.Arith.GoldenResource.RobinRationalBasis.atanhParameter,
    Finset.sum_range_succ] at h
  constructor <;> linarith only [h.1, h.2, h14Log2.1, h14Log2.2]

private theorem h14Log37 :
    (1805458956322111 / 500000000000000 : ℝ) ≤ Real.log 37 ∧ Real.log 37 ≤ (902729478161057 / 250000000000000 : ℝ) := by
  have h := D5.S3.Arith.GoldenResource.RobinRationalBasis.log_expansion_remainder_bound
    (y := (37 / 32 : ℝ)) (by norm_num) (by norm_num) 20
  have he : Real.log (37 / 32 : ℝ) = Real.log 37 - 5 * Real.log 2 := by
    rw [show (37 / 32 : ℝ) = 37 / (2 : ℝ) ^ (5 : ℕ) by norm_num,
      Real.log_div (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  dsimp [D5.S3.Arith.GoldenResource.RobinRationalBasis.logRemainder] at h
  rw [he] at h
  norm_num [D5.S3.Arith.GoldenResource.RobinRationalBasis.atanhPartial,
    D5.S3.Arith.GoldenResource.RobinRationalBasis.atanhParameter,
    Finset.sum_range_succ] at h
  constructor <;> linarith only [h.1, h.2, h14Log2.1, h14Log2.2]

private theorem h14Log41 :
    (1856786033352153 / 500000000000000 : ℝ) ≤ Real.log 41 ∧ Real.log 41 ≤ (464196508338039 / 125000000000000 : ℝ) := by
  have h := D5.S3.Arith.GoldenResource.RobinRationalBasis.log_expansion_remainder_bound
    (y := (41 / 32 : ℝ)) (by norm_num) (by norm_num) 20
  have he : Real.log (41 / 32 : ℝ) = Real.log 41 - 5 * Real.log 2 := by
    rw [show (41 / 32 : ℝ) = 41 / (2 : ℝ) ^ (5 : ℕ) by norm_num,
      Real.log_div (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  dsimp [D5.S3.Arith.GoldenResource.RobinRationalBasis.logRemainder] at h
  rw [he] at h
  norm_num [D5.S3.Arith.GoldenResource.RobinRationalBasis.atanhPartial,
    D5.S3.Arith.GoldenResource.RobinRationalBasis.atanhParameter,
    Finset.sum_range_succ] at h
  constructor <;> linarith only [h.1, h.2, h14Log2.1, h14Log2.2]

private theorem h14Log43 :
    (94030002892339 / 25000000000000 : ℝ) ≤ Real.log 43 ∧ Real.log 43 ≤ (1880600057846783 / 500000000000000 : ℝ) := by
  have h := D5.S3.Arith.GoldenResource.RobinRationalBasis.log_expansion_remainder_bound
    (y := (43 / 32 : ℝ)) (by norm_num) (by norm_num) 20
  have he : Real.log (43 / 32 : ℝ) = Real.log 43 - 5 * Real.log 2 := by
    rw [show (43 / 32 : ℝ) = 43 / (2 : ℝ) ^ (5 : ℕ) by norm_num,
      Real.log_div (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  dsimp [D5.S3.Arith.GoldenResource.RobinRationalBasis.logRemainder] at h
  rw [he] at h
  norm_num [D5.S3.Arith.GoldenResource.RobinRationalBasis.atanhPartial,
    D5.S3.Arith.GoldenResource.RobinRationalBasis.atanhParameter,
    Finset.sum_range_succ] at h
  constructor <;> linarith only [h.1, h.2, h14Log2.1, h14Log2.2]

private theorem h14Log47 :
    (3850147601710057 / 1000000000000000 : ℝ) ≤ Real.log 47 ∧ Real.log 47 ≤ (3850147601710063 / 1000000000000000 : ℝ) := by
  have h := D5.S3.Arith.GoldenResource.RobinRationalBasis.log_expansion_remainder_bound
    (y := (47 / 32 : ℝ)) (by norm_num) (by norm_num) 20
  have he : Real.log (47 / 32 : ℝ) = Real.log 47 - 5 * Real.log 2 := by
    rw [show (47 / 32 : ℝ) = 47 / (2 : ℝ) ^ (5 : ℕ) by norm_num,
      Real.log_div (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  dsimp [D5.S3.Arith.GoldenResource.RobinRationalBasis.logRemainder] at h
  rw [he] at h
  norm_num [D5.S3.Arith.GoldenResource.RobinRationalBasis.atanhPartial,
    D5.S3.Arith.GoldenResource.RobinRationalBasis.atanhParameter,
    Finset.sum_range_succ] at h
  constructor <;> linarith only [h.1, h.2, h14Log2.1, h14Log2.2]

private theorem h14Log53 :
    (99257297838803 / 25000000000000 : ℝ) ≤ Real.log 53 ∧ Real.log 53 ≤ (1985145956776063 / 500000000000000 : ℝ) := by
  have h := D5.S3.Arith.GoldenResource.RobinRationalBasis.log_expansion_remainder_bound
    (y := (53 / 32 : ℝ)) (by norm_num) (by norm_num) 20
  have he : Real.log (53 / 32 : ℝ) = Real.log 53 - 5 * Real.log 2 := by
    rw [show (53 / 32 : ℝ) = 53 / (2 : ℝ) ^ (5 : ℕ) by norm_num,
      Real.log_div (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  dsimp [D5.S3.Arith.GoldenResource.RobinRationalBasis.logRemainder] at h
  rw [he] at h
  norm_num [D5.S3.Arith.GoldenResource.RobinRationalBasis.atanhPartial,
    D5.S3.Arith.GoldenResource.RobinRationalBasis.atanhParameter,
    Finset.sum_range_succ] at h
  constructor <;> linarith only [h.1, h.2, h14Log2.1, h14Log2.2]

private theorem h14Log59 :
    (4077537443905717 / 1000000000000000 : ℝ) ≤ Real.log 59 ∧ Real.log 59 ≤ (4077537443905723 / 1000000000000000 : ℝ) := by
  have h := D5.S3.Arith.GoldenResource.RobinRationalBasis.log_expansion_remainder_bound
    (y := (59 / 32 : ℝ)) (by norm_num) (by norm_num) 20
  have he : Real.log (59 / 32 : ℝ) = Real.log 59 - 5 * Real.log 2 := by
    rw [show (59 / 32 : ℝ) = 59 / (2 : ℝ) ^ (5 : ℕ) by norm_num,
      Real.log_div (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  dsimp [D5.S3.Arith.GoldenResource.RobinRationalBasis.logRemainder] at h
  rw [he] at h
  norm_num [D5.S3.Arith.GoldenResource.RobinRationalBasis.atanhPartial,
    D5.S3.Arith.GoldenResource.RobinRationalBasis.atanhParameter,
    Finset.sum_range_succ] at h
  constructor <;> linarith only [h.1, h.2, h14Log2.1, h14Log2.2]

private theorem h14Log61 :
    (4110873864173309 / 1000000000000000 : ℝ) ≤ Real.log 61 ∧ Real.log 61 ≤ (822174772834663 / 200000000000000 : ℝ) := by
  have h := D5.S3.Arith.GoldenResource.RobinRationalBasis.log_expansion_remainder_bound
    (y := (61 / 32 : ℝ)) (by norm_num) (by norm_num) 20
  have he : Real.log (61 / 32 : ℝ) = Real.log 61 - 5 * Real.log 2 := by
    rw [show (61 / 32 : ℝ) = 61 / (2 : ℝ) ^ (5 : ℕ) by norm_num,
      Real.log_div (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  dsimp [D5.S3.Arith.GoldenResource.RobinRationalBasis.logRemainder] at h
  rw [he] at h
  norm_num [D5.S3.Arith.GoldenResource.RobinRationalBasis.atanhPartial,
    D5.S3.Arith.GoldenResource.RobinRationalBasis.atanhParameter,
    Finset.sum_range_succ] at h
  constructor <;> linarith only [h.1, h.2, h14Log2.1, h14Log2.2]

private theorem h14Gamma : Real.eulerMascheroniConstant < 5772157 / 10000000 := by
  exact lt_trans
    D5.S3.Arith.GoldenResource.HarmonicGammaTail.eulerMascheroni_upper_128
    (by norm_num)

private theorem h14LogPi : 2289459771 / 2000000000 < Real.log Real.pi := by
  let p : ℝ := 314159265358979323846 / 100000000000000000000
  have h := D5.S3.Arith.GoldenResource.RobinRationalBasis.log_expansion_remainder_bound
    (y := p / 2) (by norm_num [p]) (by norm_num [p]) 12
  have he : Real.log (p / 2) = Real.log p - Real.log 2 :=
    Real.log_div (by norm_num [p]) (by norm_num)
  dsimp [D5.S3.Arith.GoldenResource.RobinRationalBasis.logRemainder] at h
  rw [he] at h
  have hr : (2289459771 / 2000000000 : ℝ) <
      6931471803 / 10000000000 +
        D5.S3.Arith.GoldenResource.RobinRationalBasis.atanhPartial
          (D5.S3.Arith.GoldenResource.RobinRationalBasis.atanhParameter (p / 2)) 12 := by
    norm_num [p, D5.S3.Arith.GoldenResource.RobinRationalBasis.atanhPartial,
      D5.S3.Arith.GoldenResource.RobinRationalBasis.atanhParameter, Finset.sum_range_succ]
  have hp : p < Real.pi := by
    dsimp [p]
    convert Real.pi_gt_d20 using 1 <;> norm_num
  have hm := Real.log_lt_log (by norm_num [p] : 0 < p) hp
  have hlogp : 6931471803 / 10000000000 +
      D5.S3.Arith.GoldenResource.RobinRationalBasis.atanhPartial
        (D5.S3.Arith.GoldenResource.RobinRationalBasis.atanhParameter (p / 2)) 12 <
      Real.log p := by
    linarith only [h.1, Real.log_two_gt_d9]
  exact lt_trans hr (lt_trans hlogp hm)

private def h14Finite (s : ℕ) : ℝ :=
  Real.log 2 / (2 : ℝ) ^ s +
    Real.log 3 / (3 : ℝ) ^ s +
    Real.log 2 / (4 : ℝ) ^ s +
    Real.log 5 / (5 : ℝ) ^ s +
    Real.log 7 / (7 : ℝ) ^ s +
    Real.log 2 / (8 : ℝ) ^ s +
    Real.log 3 / (9 : ℝ) ^ s +
    Real.log 11 / (11 : ℝ) ^ s +
    Real.log 13 / (13 : ℝ) ^ s +
    Real.log 2 / (16 : ℝ) ^ s +
    Real.log 17 / (17 : ℝ) ^ s +
    Real.log 19 / (19 : ℝ) ^ s +
    Real.log 23 / (23 : ℝ) ^ s +
    Real.log 5 / (25 : ℝ) ^ s +
    Real.log 3 / (27 : ℝ) ^ s +
    Real.log 29 / (29 : ℝ) ^ s +
    Real.log 31 / (31 : ℝ) ^ s +
    Real.log 2 / (32 : ℝ) ^ s +
    Real.log 37 / (37 : ℝ) ^ s +
    Real.log 41 / (41 : ℝ) ^ s +
    Real.log 43 / (43 : ℝ) ^ s +
    Real.log 47 / (47 : ℝ) ^ s +
    Real.log 7 / (49 : ℝ) ^ s +
    Real.log 53 / (53 : ℝ) ^ s +
    Real.log 59 / (59 : ℝ) ^ s +
    Real.log 61 / (61 : ℝ) ^ s +
    Real.log 2 / (64 : ℝ) ^ s

private theorem h14Finite_eq (s : ℕ) :
    (∑ n ∈ Finset.range 65, h14QTerm s n) = h14Finite s := by
  have h0 : ArithmeticFunction.vonMangoldt 0 = 0 := by simp
  have h1 : ArithmeticFunction.vonMangoldt 1 = 0 := by simp
  have h2 : ArithmeticFunction.vonMangoldt 2 = Real.log 2 := by
    exact ArithmeticFunction.vonMangoldt_apply_prime (by norm_num : Nat.Prime 2)
  have h3 : ArithmeticFunction.vonMangoldt 3 = Real.log 3 := by
    exact ArithmeticFunction.vonMangoldt_apply_prime (by norm_num : Nat.Prime 3)
  have h4 : ArithmeticFunction.vonMangoldt 4 = Real.log 2 := by
    rw [show (4 : ℕ) = 2 ^ (2 : ℕ) by norm_num,
      ArithmeticFunction.vonMangoldt_apply_pow (by norm_num : (2 : ℕ) ≠ 0)]
    exact ArithmeticFunction.vonMangoldt_apply_prime (by norm_num : Nat.Prime 2)
  have h5 : ArithmeticFunction.vonMangoldt 5 = Real.log 5 := by
    exact ArithmeticFunction.vonMangoldt_apply_prime (by norm_num : Nat.Prime 5)
  have h6 : ArithmeticFunction.vonMangoldt 6 = 0 := by
    apply ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr
    intro hpow
    obtain ⟨p, hp, huniq⟩ := isPrimePow_iff_unique_prime_dvd.mp hpow
    have ha : 2 = p := huniq 2 ⟨by norm_num, by norm_num⟩
    have hb : 3 = p := huniq 3 ⟨by norm_num, by norm_num⟩
    omega
  have h7 : ArithmeticFunction.vonMangoldt 7 = Real.log 7 := by
    exact ArithmeticFunction.vonMangoldt_apply_prime (by norm_num : Nat.Prime 7)
  have h8 : ArithmeticFunction.vonMangoldt 8 = Real.log 2 := by
    rw [show (8 : ℕ) = 2 ^ (3 : ℕ) by norm_num,
      ArithmeticFunction.vonMangoldt_apply_pow (by norm_num : (3 : ℕ) ≠ 0)]
    exact ArithmeticFunction.vonMangoldt_apply_prime (by norm_num : Nat.Prime 2)
  have h9 : ArithmeticFunction.vonMangoldt 9 = Real.log 3 := by
    rw [show (9 : ℕ) = 3 ^ (2 : ℕ) by norm_num,
      ArithmeticFunction.vonMangoldt_apply_pow (by norm_num : (2 : ℕ) ≠ 0)]
    exact ArithmeticFunction.vonMangoldt_apply_prime (by norm_num : Nat.Prime 3)
  have h10 : ArithmeticFunction.vonMangoldt 10 = 0 := by
    apply ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr
    intro hpow
    obtain ⟨p, hp, huniq⟩ := isPrimePow_iff_unique_prime_dvd.mp hpow
    have ha : 2 = p := huniq 2 ⟨by norm_num, by norm_num⟩
    have hb : 5 = p := huniq 5 ⟨by norm_num, by norm_num⟩
    omega
  have h11 : ArithmeticFunction.vonMangoldt 11 = Real.log 11 := by
    exact ArithmeticFunction.vonMangoldt_apply_prime (by norm_num : Nat.Prime 11)
  have h12 : ArithmeticFunction.vonMangoldt 12 = 0 := by
    apply ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr
    intro hpow
    obtain ⟨p, hp, huniq⟩ := isPrimePow_iff_unique_prime_dvd.mp hpow
    have ha : 2 = p := huniq 2 ⟨by norm_num, by norm_num⟩
    have hb : 3 = p := huniq 3 ⟨by norm_num, by norm_num⟩
    omega
  have h13 : ArithmeticFunction.vonMangoldt 13 = Real.log 13 := by
    exact ArithmeticFunction.vonMangoldt_apply_prime (by norm_num : Nat.Prime 13)
  have h14 : ArithmeticFunction.vonMangoldt 14 = 0 := by
    apply ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr
    intro hpow
    obtain ⟨p, hp, huniq⟩ := isPrimePow_iff_unique_prime_dvd.mp hpow
    have ha : 2 = p := huniq 2 ⟨by norm_num, by norm_num⟩
    have hb : 7 = p := huniq 7 ⟨by norm_num, by norm_num⟩
    omega
  have h15 : ArithmeticFunction.vonMangoldt 15 = 0 := by
    apply ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr
    intro hpow
    obtain ⟨p, hp, huniq⟩ := isPrimePow_iff_unique_prime_dvd.mp hpow
    have ha : 3 = p := huniq 3 ⟨by norm_num, by norm_num⟩
    have hb : 5 = p := huniq 5 ⟨by norm_num, by norm_num⟩
    omega
  have h16 : ArithmeticFunction.vonMangoldt 16 = Real.log 2 := by
    rw [show (16 : ℕ) = 2 ^ (4 : ℕ) by norm_num,
      ArithmeticFunction.vonMangoldt_apply_pow (by norm_num : (4 : ℕ) ≠ 0)]
    exact ArithmeticFunction.vonMangoldt_apply_prime (by norm_num : Nat.Prime 2)
  have h17 : ArithmeticFunction.vonMangoldt 17 = Real.log 17 := by
    exact ArithmeticFunction.vonMangoldt_apply_prime (by norm_num : Nat.Prime 17)
  have h18 : ArithmeticFunction.vonMangoldt 18 = 0 := by
    apply ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr
    intro hpow
    obtain ⟨p, hp, huniq⟩ := isPrimePow_iff_unique_prime_dvd.mp hpow
    have ha : 2 = p := huniq 2 ⟨by norm_num, by norm_num⟩
    have hb : 3 = p := huniq 3 ⟨by norm_num, by norm_num⟩
    omega
  have h19 : ArithmeticFunction.vonMangoldt 19 = Real.log 19 := by
    exact ArithmeticFunction.vonMangoldt_apply_prime (by norm_num : Nat.Prime 19)
  have h20 : ArithmeticFunction.vonMangoldt 20 = 0 := by
    apply ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr
    intro hpow
    obtain ⟨p, hp, huniq⟩ := isPrimePow_iff_unique_prime_dvd.mp hpow
    have ha : 2 = p := huniq 2 ⟨by norm_num, by norm_num⟩
    have hb : 5 = p := huniq 5 ⟨by norm_num, by norm_num⟩
    omega
  have h21 : ArithmeticFunction.vonMangoldt 21 = 0 := by
    apply ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr
    intro hpow
    obtain ⟨p, hp, huniq⟩ := isPrimePow_iff_unique_prime_dvd.mp hpow
    have ha : 3 = p := huniq 3 ⟨by norm_num, by norm_num⟩
    have hb : 7 = p := huniq 7 ⟨by norm_num, by norm_num⟩
    omega
  have h22 : ArithmeticFunction.vonMangoldt 22 = 0 := by
    apply ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr
    intro hpow
    obtain ⟨p, hp, huniq⟩ := isPrimePow_iff_unique_prime_dvd.mp hpow
    have ha : 2 = p := huniq 2 ⟨by norm_num, by norm_num⟩
    have hb : 11 = p := huniq 11 ⟨by norm_num, by norm_num⟩
    omega
  have h23 : ArithmeticFunction.vonMangoldt 23 = Real.log 23 := by
    exact ArithmeticFunction.vonMangoldt_apply_prime (by norm_num : Nat.Prime 23)
  have h24 : ArithmeticFunction.vonMangoldt 24 = 0 := by
    apply ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr
    intro hpow
    obtain ⟨p, hp, huniq⟩ := isPrimePow_iff_unique_prime_dvd.mp hpow
    have ha : 2 = p := huniq 2 ⟨by norm_num, by norm_num⟩
    have hb : 3 = p := huniq 3 ⟨by norm_num, by norm_num⟩
    omega
  have h25 : ArithmeticFunction.vonMangoldt 25 = Real.log 5 := by
    rw [show (25 : ℕ) = 5 ^ (2 : ℕ) by norm_num,
      ArithmeticFunction.vonMangoldt_apply_pow (by norm_num : (2 : ℕ) ≠ 0)]
    exact ArithmeticFunction.vonMangoldt_apply_prime (by norm_num : Nat.Prime 5)
  have h26 : ArithmeticFunction.vonMangoldt 26 = 0 := by
    apply ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr
    intro hpow
    obtain ⟨p, hp, huniq⟩ := isPrimePow_iff_unique_prime_dvd.mp hpow
    have ha : 2 = p := huniq 2 ⟨by norm_num, by norm_num⟩
    have hb : 13 = p := huniq 13 ⟨by norm_num, by norm_num⟩
    omega
  have h27 : ArithmeticFunction.vonMangoldt 27 = Real.log 3 := by
    rw [show (27 : ℕ) = 3 ^ (3 : ℕ) by norm_num,
      ArithmeticFunction.vonMangoldt_apply_pow (by norm_num : (3 : ℕ) ≠ 0)]
    exact ArithmeticFunction.vonMangoldt_apply_prime (by norm_num : Nat.Prime 3)
  have h28 : ArithmeticFunction.vonMangoldt 28 = 0 := by
    apply ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr
    intro hpow
    obtain ⟨p, hp, huniq⟩ := isPrimePow_iff_unique_prime_dvd.mp hpow
    have ha : 2 = p := huniq 2 ⟨by norm_num, by norm_num⟩
    have hb : 7 = p := huniq 7 ⟨by norm_num, by norm_num⟩
    omega
  have h29 : ArithmeticFunction.vonMangoldt 29 = Real.log 29 := by
    exact ArithmeticFunction.vonMangoldt_apply_prime (by norm_num : Nat.Prime 29)
  have h30 : ArithmeticFunction.vonMangoldt 30 = 0 := by
    apply ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr
    intro hpow
    obtain ⟨p, hp, huniq⟩ := isPrimePow_iff_unique_prime_dvd.mp hpow
    have ha : 2 = p := huniq 2 ⟨by norm_num, by norm_num⟩
    have hb : 3 = p := huniq 3 ⟨by norm_num, by norm_num⟩
    omega
  have h31 : ArithmeticFunction.vonMangoldt 31 = Real.log 31 := by
    exact ArithmeticFunction.vonMangoldt_apply_prime (by norm_num : Nat.Prime 31)
  have h32 : ArithmeticFunction.vonMangoldt 32 = Real.log 2 := by
    rw [show (32 : ℕ) = 2 ^ (5 : ℕ) by norm_num,
      ArithmeticFunction.vonMangoldt_apply_pow (by norm_num : (5 : ℕ) ≠ 0)]
    exact ArithmeticFunction.vonMangoldt_apply_prime (by norm_num : Nat.Prime 2)
  have h33 : ArithmeticFunction.vonMangoldt 33 = 0 := by
    apply ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr
    intro hpow
    obtain ⟨p, hp, huniq⟩ := isPrimePow_iff_unique_prime_dvd.mp hpow
    have ha : 3 = p := huniq 3 ⟨by norm_num, by norm_num⟩
    have hb : 11 = p := huniq 11 ⟨by norm_num, by norm_num⟩
    omega
  have h34 : ArithmeticFunction.vonMangoldt 34 = 0 := by
    apply ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr
    intro hpow
    obtain ⟨p, hp, huniq⟩ := isPrimePow_iff_unique_prime_dvd.mp hpow
    have ha : 2 = p := huniq 2 ⟨by norm_num, by norm_num⟩
    have hb : 17 = p := huniq 17 ⟨by norm_num, by norm_num⟩
    omega
  have h35 : ArithmeticFunction.vonMangoldt 35 = 0 := by
    apply ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr
    intro hpow
    obtain ⟨p, hp, huniq⟩ := isPrimePow_iff_unique_prime_dvd.mp hpow
    have ha : 5 = p := huniq 5 ⟨by norm_num, by norm_num⟩
    have hb : 7 = p := huniq 7 ⟨by norm_num, by norm_num⟩
    omega
  have h36 : ArithmeticFunction.vonMangoldt 36 = 0 := by
    apply ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr
    intro hpow
    obtain ⟨p, hp, huniq⟩ := isPrimePow_iff_unique_prime_dvd.mp hpow
    have ha : 2 = p := huniq 2 ⟨by norm_num, by norm_num⟩
    have hb : 3 = p := huniq 3 ⟨by norm_num, by norm_num⟩
    omega
  have h37 : ArithmeticFunction.vonMangoldt 37 = Real.log 37 := by
    exact ArithmeticFunction.vonMangoldt_apply_prime (by norm_num : Nat.Prime 37)
  have h38 : ArithmeticFunction.vonMangoldt 38 = 0 := by
    apply ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr
    intro hpow
    obtain ⟨p, hp, huniq⟩ := isPrimePow_iff_unique_prime_dvd.mp hpow
    have ha : 2 = p := huniq 2 ⟨by norm_num, by norm_num⟩
    have hb : 19 = p := huniq 19 ⟨by norm_num, by norm_num⟩
    omega
  have h39 : ArithmeticFunction.vonMangoldt 39 = 0 := by
    apply ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr
    intro hpow
    obtain ⟨p, hp, huniq⟩ := isPrimePow_iff_unique_prime_dvd.mp hpow
    have ha : 3 = p := huniq 3 ⟨by norm_num, by norm_num⟩
    have hb : 13 = p := huniq 13 ⟨by norm_num, by norm_num⟩
    omega
  have h40 : ArithmeticFunction.vonMangoldt 40 = 0 := by
    apply ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr
    intro hpow
    obtain ⟨p, hp, huniq⟩ := isPrimePow_iff_unique_prime_dvd.mp hpow
    have ha : 2 = p := huniq 2 ⟨by norm_num, by norm_num⟩
    have hb : 5 = p := huniq 5 ⟨by norm_num, by norm_num⟩
    omega
  have h41 : ArithmeticFunction.vonMangoldt 41 = Real.log 41 := by
    exact ArithmeticFunction.vonMangoldt_apply_prime (by norm_num : Nat.Prime 41)
  have h42 : ArithmeticFunction.vonMangoldt 42 = 0 := by
    apply ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr
    intro hpow
    obtain ⟨p, hp, huniq⟩ := isPrimePow_iff_unique_prime_dvd.mp hpow
    have ha : 2 = p := huniq 2 ⟨by norm_num, by norm_num⟩
    have hb : 3 = p := huniq 3 ⟨by norm_num, by norm_num⟩
    omega
  have h43 : ArithmeticFunction.vonMangoldt 43 = Real.log 43 := by
    exact ArithmeticFunction.vonMangoldt_apply_prime (by norm_num : Nat.Prime 43)
  have h44 : ArithmeticFunction.vonMangoldt 44 = 0 := by
    apply ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr
    intro hpow
    obtain ⟨p, hp, huniq⟩ := isPrimePow_iff_unique_prime_dvd.mp hpow
    have ha : 2 = p := huniq 2 ⟨by norm_num, by norm_num⟩
    have hb : 11 = p := huniq 11 ⟨by norm_num, by norm_num⟩
    omega
  have h45 : ArithmeticFunction.vonMangoldt 45 = 0 := by
    apply ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr
    intro hpow
    obtain ⟨p, hp, huniq⟩ := isPrimePow_iff_unique_prime_dvd.mp hpow
    have ha : 3 = p := huniq 3 ⟨by norm_num, by norm_num⟩
    have hb : 5 = p := huniq 5 ⟨by norm_num, by norm_num⟩
    omega
  have h46 : ArithmeticFunction.vonMangoldt 46 = 0 := by
    apply ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr
    intro hpow
    obtain ⟨p, hp, huniq⟩ := isPrimePow_iff_unique_prime_dvd.mp hpow
    have ha : 2 = p := huniq 2 ⟨by norm_num, by norm_num⟩
    have hb : 23 = p := huniq 23 ⟨by norm_num, by norm_num⟩
    omega
  have h47 : ArithmeticFunction.vonMangoldt 47 = Real.log 47 := by
    exact ArithmeticFunction.vonMangoldt_apply_prime (by norm_num : Nat.Prime 47)
  have h48 : ArithmeticFunction.vonMangoldt 48 = 0 := by
    apply ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr
    intro hpow
    obtain ⟨p, hp, huniq⟩ := isPrimePow_iff_unique_prime_dvd.mp hpow
    have ha : 2 = p := huniq 2 ⟨by norm_num, by norm_num⟩
    have hb : 3 = p := huniq 3 ⟨by norm_num, by norm_num⟩
    omega
  have h49 : ArithmeticFunction.vonMangoldt 49 = Real.log 7 := by
    rw [show (49 : ℕ) = 7 ^ (2 : ℕ) by norm_num,
      ArithmeticFunction.vonMangoldt_apply_pow (by norm_num : (2 : ℕ) ≠ 0)]
    exact ArithmeticFunction.vonMangoldt_apply_prime (by norm_num : Nat.Prime 7)
  have h50 : ArithmeticFunction.vonMangoldt 50 = 0 := by
    apply ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr
    intro hpow
    obtain ⟨p, hp, huniq⟩ := isPrimePow_iff_unique_prime_dvd.mp hpow
    have ha : 2 = p := huniq 2 ⟨by norm_num, by norm_num⟩
    have hb : 5 = p := huniq 5 ⟨by norm_num, by norm_num⟩
    omega
  have h51 : ArithmeticFunction.vonMangoldt 51 = 0 := by
    apply ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr
    intro hpow
    obtain ⟨p, hp, huniq⟩ := isPrimePow_iff_unique_prime_dvd.mp hpow
    have ha : 3 = p := huniq 3 ⟨by norm_num, by norm_num⟩
    have hb : 17 = p := huniq 17 ⟨by norm_num, by norm_num⟩
    omega
  have h52 : ArithmeticFunction.vonMangoldt 52 = 0 := by
    apply ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr
    intro hpow
    obtain ⟨p, hp, huniq⟩ := isPrimePow_iff_unique_prime_dvd.mp hpow
    have ha : 2 = p := huniq 2 ⟨by norm_num, by norm_num⟩
    have hb : 13 = p := huniq 13 ⟨by norm_num, by norm_num⟩
    omega
  have h53 : ArithmeticFunction.vonMangoldt 53 = Real.log 53 := by
    exact ArithmeticFunction.vonMangoldt_apply_prime (by norm_num : Nat.Prime 53)
  have h54 : ArithmeticFunction.vonMangoldt 54 = 0 := by
    apply ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr
    intro hpow
    obtain ⟨p, hp, huniq⟩ := isPrimePow_iff_unique_prime_dvd.mp hpow
    have ha : 2 = p := huniq 2 ⟨by norm_num, by norm_num⟩
    have hb : 3 = p := huniq 3 ⟨by norm_num, by norm_num⟩
    omega
  have h55 : ArithmeticFunction.vonMangoldt 55 = 0 := by
    apply ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr
    intro hpow
    obtain ⟨p, hp, huniq⟩ := isPrimePow_iff_unique_prime_dvd.mp hpow
    have ha : 5 = p := huniq 5 ⟨by norm_num, by norm_num⟩
    have hb : 11 = p := huniq 11 ⟨by norm_num, by norm_num⟩
    omega
  have h56 : ArithmeticFunction.vonMangoldt 56 = 0 := by
    apply ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr
    intro hpow
    obtain ⟨p, hp, huniq⟩ := isPrimePow_iff_unique_prime_dvd.mp hpow
    have ha : 2 = p := huniq 2 ⟨by norm_num, by norm_num⟩
    have hb : 7 = p := huniq 7 ⟨by norm_num, by norm_num⟩
    omega
  have h57 : ArithmeticFunction.vonMangoldt 57 = 0 := by
    apply ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr
    intro hpow
    obtain ⟨p, hp, huniq⟩ := isPrimePow_iff_unique_prime_dvd.mp hpow
    have ha : 3 = p := huniq 3 ⟨by norm_num, by norm_num⟩
    have hb : 19 = p := huniq 19 ⟨by norm_num, by norm_num⟩
    omega
  have h58 : ArithmeticFunction.vonMangoldt 58 = 0 := by
    apply ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr
    intro hpow
    obtain ⟨p, hp, huniq⟩ := isPrimePow_iff_unique_prime_dvd.mp hpow
    have ha : 2 = p := huniq 2 ⟨by norm_num, by norm_num⟩
    have hb : 29 = p := huniq 29 ⟨by norm_num, by norm_num⟩
    omega
  have h59 : ArithmeticFunction.vonMangoldt 59 = Real.log 59 := by
    exact ArithmeticFunction.vonMangoldt_apply_prime (by norm_num : Nat.Prime 59)
  have h60 : ArithmeticFunction.vonMangoldt 60 = 0 := by
    apply ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr
    intro hpow
    obtain ⟨p, hp, huniq⟩ := isPrimePow_iff_unique_prime_dvd.mp hpow
    have ha : 2 = p := huniq 2 ⟨by norm_num, by norm_num⟩
    have hb : 3 = p := huniq 3 ⟨by norm_num, by norm_num⟩
    omega
  have h61 : ArithmeticFunction.vonMangoldt 61 = Real.log 61 := by
    exact ArithmeticFunction.vonMangoldt_apply_prime (by norm_num : Nat.Prime 61)
  have h62 : ArithmeticFunction.vonMangoldt 62 = 0 := by
    apply ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr
    intro hpow
    obtain ⟨p, hp, huniq⟩ := isPrimePow_iff_unique_prime_dvd.mp hpow
    have ha : 2 = p := huniq 2 ⟨by norm_num, by norm_num⟩
    have hb : 31 = p := huniq 31 ⟨by norm_num, by norm_num⟩
    omega
  have h63 : ArithmeticFunction.vonMangoldt 63 = 0 := by
    apply ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr
    intro hpow
    obtain ⟨p, hp, huniq⟩ := isPrimePow_iff_unique_prime_dvd.mp hpow
    have ha : 3 = p := huniq 3 ⟨by norm_num, by norm_num⟩
    have hb : 7 = p := huniq 7 ⟨by norm_num, by norm_num⟩
    omega
  have h64 : ArithmeticFunction.vonMangoldt 64 = Real.log 2 := by
    rw [show (64 : ℕ) = 2 ^ (6 : ℕ) by norm_num,
      ArithmeticFunction.vonMangoldt_apply_pow (by norm_num : (6 : ℕ) ≠ 0)]
    exact ArithmeticFunction.vonMangoldt_apply_prime (by norm_num : Nat.Prime 2)
  simp only [h14QTerm, h14Finite, Finset.sum_range_succ, Finset.sum_range_zero,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38, h39, h40, h41, h42, h43, h44, h45, h46, h47, h48, h49, h50, h51, h52, h53, h54, h55, h56, h57, h58, h59, h60, h61, h62, h63, h64,
    Nat.cast_ofNat, zero_div, zero_add, add_zero]

private def h14Tail (s : ℕ) (x : ℝ) : ℝ := x ^ (1 - (s : ℝ)) / 2

private theorem h14Tail_antitone (s : ℕ) (hs : 3 ≤ s) :
    AntitoneOn (h14Tail s) (Set.Ici (64 : ℝ)) := by
  intro a ha b hb hab
  exact div_le_div_of_nonneg_right
    (Real.rpow_le_rpow_of_nonpos (by linarith [Set.mem_Ici.mp ha]) hab
      (by
        have hs' : (3 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
        linarith)) (by norm_num)

private theorem h14Tail_integrable (s : ℕ) (hs : 3 ≤ s) :
    MeasureTheory.IntegrableOn (h14Tail s) (Set.Ioi (64 : ℝ)) := by
  exact (integrableOn_Ioi_rpow_of_lt
    (by
      have hs' : (3 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
      linarith)
    (by norm_num : (0 : ℝ) < 64)).div_const 2

private theorem h14Tail_nonneg (s : ℕ) (x : ℝ) (hx : x ∈ Set.Ioi (64 : ℝ)) :
    0 ≤ h14Tail s x := by
  exact div_nonneg (Real.rpow_nonneg (by linarith [Set.mem_Ioi.mp hx]) _) (by norm_num)

private theorem h14Term_le_tail (s n : ℕ) (hn : 65 ≤ n) :
    h14QTerm s n ≤ h14Tail s n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hl : ArithmeticFunction.vonMangoldt n ≤ (n : ℝ) / 2 :=
    ArithmeticFunction.vonMangoldt_le_log.trans (heightRefinement_log_le_half n hn0)
  calc
    h14QTerm s n ≤ ((n : ℝ) / 2) / (n : ℝ) ^ s :=
      div_le_div_of_nonneg_right hl (by positivity)
    _ = h14Tail s n := by
      rw [h14Tail, Real.rpow_sub hn0, Real.rpow_one, Real.rpow_natCast]
      ring

private theorem h14Q_finite_lower (s : ℕ) (hs : 3 ≤ s) :
    h14Finite s ≤ h14Q s := by
  rw [← h14Finite_eq]
  apply sum_le_hasSum (Finset.range 65)
    (fun n _ => div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity))
    (h14Q_hasSum s (by omega))

private theorem h14Q_finite_upper (s : ℕ) (hs : 3 ≤ s) :
    h14Q s ≤ h14Finite s + (∫ x in Set.Ioi (64 : ℝ), h14Tail s x) := by
  have hseries := (h14Q_hasSum s (by omega)).summable
  have htail := (summable_nat_add_iff 65).mpr hseries
  have hgfull : Summable (fun n : ℕ => h14Tail s n) :=
    (h14Tail_antitone s hs).summable_of_integrableOn_Ioi
      (h14Tail_integrable s hs) (h14Tail_nonneg s)
  have hgtail := (summable_nat_add_iff 65).mpr hgfull
  have htail_le := htail.tsum_le_tsum
    (fun n => h14Term_le_tail s (n + 65) (by omega)) hgtail
  have htint := (h14Tail_antitone s hs).tsum_comp_add_le_integral 64
    (h14Tail_integrable s hs) (h14Tail_nonneg s)
  norm_num only [Nat.cast_ofNat] at htint
  have htint' : (∑' n : ℕ, h14Tail s (n + 65 : ℕ)) ≤
      ∫ x in Set.Ioi (64 : ℝ), h14Tail s x := by
    simpa only [← Nat.add_assoc, show (64 + 1 : ℕ) = 65 by norm_num] using htint
  have hsplit := hseries.sum_add_tsum_nat_add 65
  rw [(h14Q_hasSum s (by omega)).tsum_eq, h14Finite_eq] at hsplit
  linarith only [hsplit, htail_le, htint']

private theorem h14Q6_bound : h14Q 6 ≤ (12633076304737 / 1000000000000000 : ℝ) := by
  have h := h14Q_finite_upper 6 (by norm_num)
  have ht : (∫ x in Set.Ioi (64 : ℝ), h14Tail 6 x) = (1 / 134217728 : ℝ) := by
    change (∫ x in Set.Ioi (64 : ℝ), x ^ (1 - (6 : ℝ)) / 2) = _
    rw [MeasureTheory.integral_div, integral_Ioi_rpow_of_lt
      (by norm_num : (1 - (6 : ℝ)) < -1) (by norm_num : (0 : ℝ) < 64)]
    norm_num [Real.rpow_neg_natCast]
  have hf : h14Finite 6 ≤ (17249321509217161498400458902529221275645632912349903331633559641695482165021093576227780971581265613435917700914900024065485577135422988848470963330504156371061324564891212261 / 1365410235157891238947835315549977423165935059055842834311559910610947327036629826991657180903272858646616152840361446862489314125590244186695462289408000000000000000000000000000 : ℝ) := by
    dsimp [h14Finite]
    linarith only [h14Log2.2, h14Log3.2, h14Log5.2, h14Log7.2, h14Log11.2, h14Log13.2, h14Log17.2, h14Log19.2, h14Log23.2, h14Log29.2, h14Log31.2, h14Log37.2, h14Log41.2, h14Log43.2, h14Log47.2, h14Log53.2, h14Log59.2, h14Log61.2]
  have hr : (17249321509217161498400458902529221275645632912349903331633559641695482165021093576227780971581265613435917700914900024065485577135422988848470963330504156371061324564891212261 / 1365410235157891238947835315549977423165935059055842834311559910610947327036629826991657180903272858646616152840361446862489314125590244186695462289408000000000000000000000000000 : ℝ) + (1 / 134217728) ≤ (12633076304737 / 1000000000000000) := by norm_num
  rw [ht] at h
  linarith only [h, hf, hr]

private theorem h14Q8_bound : (1445084153477 / 500000000000000 : ℝ) ≤ h14Q 8 := by
  have h := h14Q_finite_lower 8 (by norm_num)
  have hf : (3677274747139739474093032805621964745927047700647429769155714443776690319280276256892856506192440708792693455740908631592280350760978836944345287483860587678359512993791910832703034924532994089196263330580424016220485903653737923 / 1272339308732082349912793946777540127293305849622521581431386473593914333794257667919294400239490867213709238425438793277955737370276553670500109253431211341813784240832954932029606242586777308438200320000000000000000000000000000000 : ℝ) ≤ h14Finite 8 := by
    dsimp [h14Finite]
    linarith only [h14Log2.1, h14Log3.1, h14Log5.1, h14Log7.1, h14Log11.1, h14Log13.1, h14Log17.1, h14Log19.1, h14Log23.1, h14Log29.1, h14Log31.1, h14Log37.1, h14Log41.1, h14Log43.1, h14Log47.1, h14Log53.1, h14Log59.1, h14Log61.1]
  have hr : (1445084153477 / 500000000000000 : ℝ) ≤ (3677274747139739474093032805621964745927047700647429769155714443776690319280276256892856506192440708792693455740908631592280350760978836944345287483860587678359512993791910832703034924532994089196263330580424016220485903653737923 / 1272339308732082349912793946777540127293305849622521581431386473593914333794257667919294400239490867213709238425438793277955737370276553670500109253431211341813784240832954932029606242586777308438200320000000000000000000000000000000) := by norm_num
  linarith only [h, hf, hr]

private theorem h14Q10_bound : h14Q 10 ≤ (174085111381 / 250000000000000 : ℝ) := by
  have h := h14Q_finite_upper 10 (by norm_num)
  have ht : (∫ x in Set.Ioi (64 : ℝ), h14Tail 10 x) = (1 / 4503599627370496 : ℝ) := by
    change (∫ x in Set.Ioi (64 : ℝ), x ^ (1 - (10 : ℝ)) / 2) = _
    rw [MeasureTheory.integral_div, integral_Ioi_rpow_of_lt
      (by norm_num : (1 - (10 : ℝ)) < -1) (by norm_num : (0 : ℝ) < 64)]
    norm_num [Real.rpow_neg_natCast]
  have hf : h14Finite 10 ≤ (1857577211964025815411150338103476064653274472898733597229358463009816620319307509011926686536563726599393389128504318823821108457828409626456008602869442476331313283636830763529280841835350382127391520125002119150132535455405518355859430147700254784863165031816566162003200345236901 / 2667627917557450816561849618012376138330598469099411734267724087723496016100571871889637252651104842866736498652142736309663457134840979906909332338838037316722266173420920907059876823936150802692008425638944208469371356106518994769688343197493546188800000000000000000000000000000000000 : ℝ) := by
    dsimp [h14Finite]
    linarith only [h14Log2.2, h14Log3.2, h14Log5.2, h14Log7.2, h14Log11.2, h14Log13.2, h14Log17.2, h14Log19.2, h14Log23.2, h14Log29.2, h14Log31.2, h14Log37.2, h14Log41.2, h14Log43.2, h14Log47.2, h14Log53.2, h14Log59.2, h14Log61.2]
  have hr : (1857577211964025815411150338103476064653274472898733597229358463009816620319307509011926686536563726599393389128504318823821108457828409626456008602869442476331313283636830763529280841835350382127391520125002119150132535455405518355859430147700254784863165031816566162003200345236901 / 2667627917557450816561849618012376138330598469099411734267724087723496016100571871889637252651104842866736498652142736309663457134840979906909332338838037316722266173420920907059876823936150802692008425638944208469371356106518994769688343197493546188800000000000000000000000000000000000 : ℝ) + (1 / 4503599627370496) ≤ (174085111381 / 250000000000000) := by norm_num
  rw [ht] at h
  linarith only [h, hf, hr]

private theorem h14Q12_bound : (2677198143 / 15625000000000 : ℝ) ≤ h14Q 12 := by
  have h := h14Q_finite_lower 12 (by norm_num)
  have hf : (425917548289740772598845621061159896700160705476288498215162310804980542657065936860942525756878337501403239071034147897496295863932293405091665514279344388433217865455336405389037832977176268191280091941767428195198735982693834242021839142362348086033793294802476190812469036665299614727174370378220819757601678790974930532113143765443 / 2485793480365237136503119446972360110536523498394024653874541743926968137354882849424565745530347249324850334855712980017406796948387639322546653446721294268632682601477170772602132945312171463061837353326059512871906330445486044185629125438209088379054748648771408824725509757725747413019488998653952000000000000000000000000000000000000000 : ℝ) ≤ h14Finite 12 := by
    dsimp [h14Finite]
    linarith only [h14Log2.1, h14Log3.1, h14Log5.1, h14Log7.1, h14Log11.1, h14Log13.1, h14Log17.1, h14Log19.1, h14Log23.1, h14Log29.1, h14Log31.1, h14Log37.1, h14Log41.1, h14Log43.1, h14Log47.1, h14Log53.1, h14Log59.1, h14Log61.1]
  have hr : (2677198143 / 15625000000000 : ℝ) ≤ (425917548289740772598845621061159896700160705476288498215162310804980542657065936860942525756878337501403239071034147897496295863932293405091665514279344388433217865455336405389037832977176268191280091941767428195198735982693834242021839142362348086033793294802476190812469036665299614727174370378220819757601678790974930532113143765443 / 2485793480365237136503119446972360110536523498394024653874541743926968137354882849424565745530347249324850334855712980017406796948387639322546653446721294268632682601477170772602132945312171463061837353326059512871906330445486044185629125438209088379054748648771408824725509757725747413019488998653952000000000000000000000000000000000000000) := by norm_num
  linarith only [h, hf, hr]

private theorem h14Q14_bound : h14Q 14 ≤ (42538887969 / 1000000000000000 : ℝ) := by
  have h := h14Q_finite_upper 14 (by norm_num)
  have ht : (∫ x in Set.Ioi (64 : ℝ), h14Tail 14 x) = (1 / 113336795588871485128704 : ℝ) := by
    change (∫ x in Set.Ioi (64 : ℝ), x ^ (1 - (14 : ℝ)) / 2) = _
    rw [MeasureTheory.integral_div, integral_Ioi_rpow_of_lt
      (by norm_num : (1 - (14 : ℝ)) < -1) (by norm_num : (0 : ℝ) < 64)]
    norm_num [Real.rpow_neg_natCast]
  have hf : h14Finite 14 ≤ (221703978187685851911099559204634454887584281497709992886425975529391773382425321273661557671319187584317198060011632827481718349905383345521139417137901278314551660639576458698243205572166250535908491039797432148348615509775333685305286570702206306578384097064819183375263536112151192169600450070319375093428144775402207233877570835342430815235169863297130329976022485667589578514257855141 / 5211795344209504029754563105301476616109476784967940523077477746495069349658767178514705802768329381958887254794348584104337731880320527057831810163023431573521473290329067148337234578401209466566945624662227907460925816785471912758087460930616071722590068600245043508128183385732491533763292906820223875028782320956504515332195762655303414291554631680000000000000000000000000000000000000000000 : ℝ) := by
    dsimp [h14Finite]
    linarith only [h14Log2.2, h14Log3.2, h14Log5.2, h14Log7.2, h14Log11.2, h14Log13.2, h14Log17.2, h14Log19.2, h14Log23.2, h14Log29.2, h14Log31.2, h14Log37.2, h14Log41.2, h14Log43.2, h14Log47.2, h14Log53.2, h14Log59.2, h14Log61.2]
  have hr : (221703978187685851911099559204634454887584281497709992886425975529391773382425321273661557671319187584317198060011632827481718349905383345521139417137901278314551660639576458698243205572166250535908491039797432148348615509775333685305286570702206306578384097064819183375263536112151192169600450070319375093428144775402207233877570835342430815235169863297130329976022485667589578514257855141 / 5211795344209504029754563105301476616109476784967940523077477746495069349658767178514705802768329381958887254794348584104337731880320527057831810163023431573521473290329067148337234578401209466566945624662227907460925816785471912758087460930616071722590068600245043508128183385732491533763292906820223875028782320956504515332195762655303414291554631680000000000000000000000000000000000000000000 : ℝ) + (1 / 113336795588871485128704) ≤ (42538887969 / 1000000000000000) := by norm_num
  rw [ht] at h
  linarith only [h, hf, hr]

/-- The signed complete zeta logarithmic-derivative combination used by the six-pole kernel.
The logarithm of two uses the pinned Mathlib lower bound `Real.log_two_gt_d9`;
the remaining scalar bounds are supplied by the local gamma, logarithm of pi,
and complete von Mangoldt estimates. -/
theorem h14_evaluatedMass_upper :
    66493177 / 143006288128704000 +
      (4 / 12649365729) * Real.eulerMascheroniConstant -
      Real.log 2 / 1816214400 - (9487 / 40477970332800) * Real.log Real.pi +
      (-deriv riemannZeta (6 : ℂ) / riemannZeta 6).re / 3990729600 -
      (-deriv riemannZeta (8 : ℂ) / riemannZeta 8).re / 3555377280 +
      (-deriv riemannZeta (10 : ℂ) / riemannZeta 10).re / 6739588800 -
      (-deriv riemannZeta (12 : ℂ) / riemannZeta 12).re / 24711825600 +
      (-deriv riemannZeta (14 : ℂ) / riemannZeta 14).re / 216459734400 ≤
      72126772613108177 / 15194418113674800000000000000000 := by
  change 66493177 / 143006288128704000 +
      (4 / 12649365729) * Real.eulerMascheroniConstant -
      Real.log 2 / 1816214400 - (9487 / 40477970332800) * Real.log Real.pi +
      h14Q 6 / 3990729600 - h14Q 8 / 3555377280 +
      h14Q 10 / 6739588800 - h14Q 12 / 24711825600 +
      h14Q 14 / 216459734400 ≤ 72126772613108177 / 15194418113674800000000000000000

  have hr : (66493177 / 143006288128704000 : ℝ) +
      (4 / 12649365729) * (5772157 / 10000000) -
      (6931471803 / 10000000000) / 1816214400 -
      (9487 / 40477970332800) * (2289459771 / 2000000000) +
      (12633076304737 / 1000000000000000) / 3990729600 -
      (1445084153477 / 500000000000000) / 3555377280 +
      (174085111381 / 250000000000000) / 6739588800 -
      (2677198143 / 15625000000000) / 24711825600 +
      (42538887969 / 1000000000000000) / 216459734400 =
        72126772613108177 / 15194418113674800000000000000000 := by norm_num
  linarith only [hr, h14Gamma.le, Real.log_two_gt_d9.le, h14LogPi.le,
    h14Q6_bound, h14Q8_bound, h14Q10_bound, h14Q12_bound, h14Q14_bound]



namespace H14Sector
private def shifts : Fin 6 → ℝ := ![0, 30, 56, 90, 132, 182]

private lemma shifts_nonneg : ∀ j, 0 ≤ shifts j := by
  intro j
  fin_cases j <;> norm_num [shifts]

private lemma shifts_zero : ∃ j, shifts j = 0 := ⟨0, by norm_num [shifts]⟩

private lemma six_phase {u : ℝ} (hu : 100 < u) :
    ((6 : ℝ) + 1) / Real.sqrt u < Real.pi / 2 := by
  have hs : 10 < Real.sqrt u := by
    apply (Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 10)).2
    norm_num
    exact hu
  have hrat : (7 : ℝ) / Real.sqrt u < 7 / 10 :=
    div_lt_div_of_pos_left (by norm_num) (by norm_num) hs
  norm_num only at *
  linarith [Real.pi_gt_three]

private lemma six_threshold : threshold 6 < 100 := by
  have hpi2 : 0 < Real.pi ^ 2 := by positivity
  change 4 * ((6 : ℝ) + 1) ^ 2 / Real.pi ^ 2 < 100
  apply (div_lt_iff₀ hpi2).2
  nlinarith [Real.pi_gt_three, sq_nonneg (Real.pi - 3)]

private theorem six_positive {u p : ℝ} (hu : 100 < u) (hp : p ∈ Set.Icc 0 (1 / 4)) :
    0 < weight shifts u p := by
  exact weight_pos shifts_nonneg (by linarith) hp (six_phase hu)

private theorem six_lower {u p : ℝ} (hu : 100 < u) (hupper : u ≤ 196)
    (hp : p ∈ Set.Icc 0 (1 / 4)) :
    weight shifts 196 0 ≤ weight shifts u p := by
  have ha := strictAntiOn_weight_u (by decide : 0 < 6) shifts_nonneg hp
  have hleft : u ∈ Set.Ioi (threshold 6) := lt_trans six_threshold hu
  have hright : (196 : ℝ) ∈ Set.Ioi (threshold 6) := by
    exact lt_trans six_threshold (by norm_num)
  have hucomp : weight shifts 196 p ≤ weight shifts u p :=
    ha.antitoneOn hleft hright hupper
  have hm := strictMonoOn_weight_p shifts_nonneg shifts_zero
    (by norm_num : (0 : ℝ) < 196) (six_phase (by norm_num : (100 : ℝ) < 196))
  have hpcomp : weight shifts 196 0 ≤ weight shifts 196 p :=
    hm.monotoneOn (by norm_num : (0 : ℝ) ∈ Set.Icc 0 (1 / 4)) hp hp.1
  exact hpcomp.trans hucomp

private theorem six_pair_value : 2 * weight shifts 196 0 =
    (345650537 : ℝ) / 72636763553532703907200 := by
  norm_num [weight, reciprocalProduct, factor, stripImaginary, shifts,
    Fin.prod_univ_succ, Complex.inv_re, Complex.inv_im, Complex.normSq,
    Complex.mul_re, Complex.mul_im]
end H14Sector

def h14Kernel (rho : ℂ) : ℂ :=
  1 / ((rho * (1 - rho)) * (rho * (1 - rho) + 30) *
    (rho * (1 - rho) + 56) * (rho * (1 - rho) + 90) *
    (rho * (1 - rho) + 132) * (rho * (1 - rho) + 182))

def h14Weight (rho : ℂ) : ℝ := (h14Kernel rho).re


private theorem h14Weight_sector (rho : ℂ) :
    h14Weight rho = H14Sector.weight H14Sector.shifts (rho.im ^ 2)
      (rho.re * (1 - rho.re)) := by
  have hb : (rho.im * (1 - 2 * rho.re)) ^ 2 =
      rho.im ^ 2 * (1 - 4 * (rho.re * (1 - rho.re))) := by ring
  have he : rho * (1 - rho) =
      ((rho.im ^ 2 + rho.re * (1 - rho.re) : ℝ) : ℂ) +
        ((rho.im * (1 - 2 * rho.re) : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;>
      simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
        Complex.I_re, Complex.I_im, Complex.sub_re, Complex.sub_im,
        ← Complex.ofReal_pow, Complex.ofReal_re, Complex.ofReal_im,
        Complex.one_re, Complex.one_im] <;> ring
  rw [← H14Sector.real_product_signed_reduction H14Sector.shifts
    (rho.im ^ 2) (rho.re * (1 - rho.re)) (rho.im * (1 - 2 * rho.re)) hb]
  have hprod : (∏ j : Fin 6,
      (((rho.im ^ 2 + rho.re * (1 - rho.re) + H14Sector.shifts j : ℝ) : ℂ) +
        ((rho.im * (1 - 2 * rho.re) : ℝ) : ℂ) * Complex.I)) =
      (rho * (1 - rho)) * (rho * (1 - rho) + 30) *
        (rho * (1 - rho) + 56) * (rho * (1 - rho) + 90) *
        (rho * (1 - rho) + 132) * (rho * (1 - rho) + 182) := by
    simp [H14Sector.shifts, Fin.prod_univ_succ, he]
    <;> push_cast <;> ring
  rw [Finset.prod_inv_distrib, hprod]
  simp only [h14Weight, h14Kernel, one_div]


/-- The full strip kernel is positive above height ten; below height fourteen
its doubled weight dominates the exact conjugate-pair lower bound. -/
theorem h14_kernel_bounds (rho : ℂ) (h0 : 0 < rho.re) (h1 : rho.re < 1)
    (hu : 100 < rho.im ^ 2) :
    0 < h14Weight rho ∧
      (rho.im ^ 2 ≤ 196 →
        345650537 / 72636763553532703907200 ≤ 2 * h14Weight rho) := by
  obtain ⟨hp, hp4⟩ := heightRefinement_strip_product_bounds h0 h1
  constructor
  · rw [h14Weight_sector]
    exact H14Sector.six_positive hu ⟨hp.le, hp4⟩
  · intro hupper
    have hl := H14Sector.six_lower hu hupper ⟨hp.le, hp4⟩
    rw [← h14Weight_sector] at hl
    linarith only [hl, H14Sector.six_pair_value]


end D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds
