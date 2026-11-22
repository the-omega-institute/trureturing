/- GID: D5/S3/Quantum/Semigroups/WuEndpointQuarticPrefix
   generality: I
   mirror-B: D5/B/S3/Quantum/Semigroups/WuEndpointQuarticPrefix
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A quartic variance bound for the four prefix averages at the Wu endpoint. -/

module

public import D5.S3.Quantum.Semigroups.WuEndpointPrefixMajorization
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Quartic positivity for prefixes of the Wu endpoint spectrum

The convolution in `A1_spectral_majorization` bounds the ordered spectrum of
the signed two-mode channel. This module proves the quartic lower bound on
each spectrum obtained by averaging a tail of that convolution.
-/

noncomputable section

open scoped BigOperators

namespace WuRankOneEndpointFloor

/-- The normalized power sum of a four-point spectrum. -/
@[expose] public def spectralMoment (k : ℕ) (x : Fin 4 → ℝ) : ℝ :=
  (∑ i : Fin 4, x i ^ k) / 4

/-- Keep the first `k` entries and replace the others by their mean. -/
@[expose] public def endpointPrefixAverage (k : Fin 4) (y : Fin 4 → ℝ) : Fin 4 → ℝ :=
  let all := spectralMoment 1 y
  let lastThree := (y 1 + y 2 + y 3) / 3
  let lastTwo := (y 2 + y 3) / 2
  ![![all, all, all, all], ![y 0, lastThree, lastThree, lastThree],
    ![y 0, y 1, lastTwo, lastTwo], y] k

private def quarticGap (x y : Fin 4 → ℝ) : ℝ :=
  spectralMoment 3 x * spectralMoment 3 y - spectralMoment 2 x * spectralMoment 4 y -
    (spectralMoment 1 x) ^ 2 * (spectralMoment 2 x - (spectralMoment 1 x) ^ 2) ^ 2 / 5

-- The bottom entry is z, and p, q, t are the adjacent gaps in order.
private def gapVector (z p q t : ℝ) : Fin 4 → ℝ :=
  ![z + t + q + p, z + t + q, z + t, z]

private def classicalInGaps (r z p q t : ℝ) : Fin 4 → ℝ :=
  ![z + (5 / 12 + r / 2) * p + (1 / 2 + r / 2) * q + (7 / 12 + r / 2) * t,
    z + p / 12 + (1 / 2 + r / 2) * q + 11 * t / 12,
    z + p / 12 + (1 / 2 - r / 2) * q + 11 * t / 12,
    z + (5 / 12 - r / 2) * p + (1 / 2 - r / 2) * q + (7 / 12 - r / 2) * t]

private theorem damping_sq : lambda ^ 2 = (2 / 3 : ℝ) :=
  Real.sq_sqrt (by norm_num)

private theorem endpointClassical_gapVector (z p q t : ℝ) :
    endpointClassical (gapVector z p q t) = classicalInGaps lambda z p q t := by
  have hAlpha : endpointAlpha ^ 2 = 5 / 12 + lambda / 2 := by
    unfold endpointAlpha
    linear_combination (1 / 4 : ℝ) * damping_sq
  have hBeta : endpointBeta ^ 2 = 5 / 12 - lambda / 2 := by
    unfold endpointBeta
    linear_combination (1 / 4 : ℝ) * damping_sq
  have hCross : endpointAlpha * endpointBeta = (1 / 12 : ℝ) := by
    unfold endpointAlpha endpointBeta
    linear_combination -(1 / 4 : ℝ) * damping_sq
  funext i
  fin_cases i <;>
    simp [endpointClassical, classicalInGaps, gapVector, hAlpha, hBeta, hCross,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] <;> ring

private theorem zeroPrefix_eq_mean (r z p q t : ℝ) :
    endpointPrefixAverage 0 (classicalInGaps r z p q t) =
      fun _ => spectralMoment 1 (gapVector z p q t) := by
  funext i
  fin_cases i <;>
    simp [endpointPrefixAverage, classicalInGaps, gapVector, spectralMoment, Fin.sum_univ_four,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] <;> ring

private theorem uniform_gap (x : Fin 4 → ℝ) (hNonneg : ∀ i, 0 ≤ x i) :
    0 ≤ quarticGap x (fun _ => spectralMoment 1 x) := by
  let m := spectralMoment 1 x
  have hVariance : 0 ≤ spectralMoment 2 x - m ^ 2 := by
    have h := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
      (r := x) (f := fun _ => (1 : ℝ)) (g := fun i => x i ^ 2)
      (fun _ _ => zero_le_one) (fun _ _ => sq_nonneg _) (fun _ _ => by simp)
    simp at h
    simp only [m, spectralMoment, pow_one]
    nlinarith only [h]
  have hCauchy : 0 ≤ m * spectralMoment 3 x - (spectralMoment 2 x) ^ 2 := by
    have h := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
      (r := fun i => x i ^ 2) (f := x) (g := fun i => x i ^ 3)
      (fun i _ => hNonneg i) (fun i _ => pow_nonneg (hNonneg i) _)
      (fun i _ => le_of_eq (by ring))
    simp only [m, spectralMoment, pow_one]
    nlinarith only [h]
  have hConst (j : ℕ) : spectralMoment j (fun _ => m) = m ^ j := by
    simp only [spectralMoment, Fin.sum_univ_four]
    ring
  calc
    0 ≤ m ^ 2 * (m * spectralMoment 3 x - (spectralMoment 2 x) ^ 2) +
      (4 / 5) * m ^ 2 * (spectralMoment 2 x - m ^ 2) ^ 2 +
      m ^ 4 * (spectralMoment 2 x - m ^ 2) := by positivity
    _ = quarticGap x (fun _ => spectralMoment 1 x) := by
      change _ = spectralMoment 3 x * spectralMoment 3 (fun _ => m) -
        spectralMoment 2 x * spectralMoment 4 (fun _ => m) -
        m ^ 2 * (spectralMoment 2 x - m ^ 2) ^ 2 / 5
      rw [hConst, hConst]
      ring

private theorem damping_powers {r : ℝ} (hSq : r ^ 2 = (2 / 3 : ℝ)) :
    r ^ 3 = (2 / 3) * r ∧ r ^ 4 = (4 / 9 : ℝ) := by
  constructor
  · linear_combination r * hSq
  · linear_combination (r ^ 2 + (2 / 3 : ℝ)) * hSq

/-!
Set v to the smaller outer gap and d to the difference. The certificates
group the residual monomials by the power of z. For coefficients decreasing
in r, s = 41/50 - r gives a nonnegative constant and a nonnegative multiple
of s. The two-entry prefix uses weighted squares to absorb mixed terms. In the
unaveraged case with p ≥ t, a square in centered coordinates absorbs the
terms of highest degree in the bottom eigenvalue.
-/

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 4096 in
-- Normalize both degree-six polynomials, then reduce powers of the damping.
private theorem one_prefix_p_le_t {r z v q d : ℝ}
    (hr : 0 ≤ r) (hSq : r ^ 2 = (2 / 3 : ℝ)) (hUpper : 0 ≤ 41 / 50 - r)
    (hz : 0 ≤ z) (hv : 0 ≤ v) (hq : 0 ≤ q) (hd : 0 ≤ d) :
    0 ≤ quarticGap (gapVector z v q (v + d))
      (endpointPrefixAverage 1 (classicalInGaps r z v q (v + d))) := by
  let s : ℝ := 41 / 50 - r
  have hs : 0 ≤ s := hUpper
  obtain ⟨hCube, hFourth⟩ := damping_powers hSq
  calc
    0 ≤
      z ^ 4 * (
        24 * v ^ 2 + 24 * v * q + (24 + 24 * r) * v * d + 24 * q ^ 2 + (12 + 12 * r) * q * d +
        (13 + 12 * r) * d ^ 2) / 72 +
      z ^ 3 * (
        (62784 + 28800 * s) * v ^ 3 + (94176 + 43200 * s) * v ^ 2 * q +
        (141300 + 43200 * r) * v ^ 2 * d + (111888 + 21600 * s) * v * q ^ 2 +
        (141300 + 43200 * r) * v * q * d + (101700 + 82800 * r) * v * d ^ 2 +
        (40248 + 3600 * s) * q ^ 3 + (90000 + 10800 * r) * q ^ 2 * d + (50850 +
        41400 * r) * q * d ^ 2 +
        (32825 + 27000 * r) * d ^ 3) / 64800 +
      z ^ 2 * (
        (15043392 + 18662400 * s) * v ^ 4 + (30086784 + 37324800 * s) * v ^ 3 * q +
        (56206944 + 14716800 * s) * v ^ 3 * d + (44376768 + 27993600 * s) * v ^ 2 * q ^ 2 +
        (84310416 + 22075200 * s) * v ^ 2 * q * d + (65402280 + 17582400 * r) * v ^ 2 * d ^ 2 +
        (29333376 + 9331200 * s) * v * q ^ 3 + (77922864 + 11620800 * s) * v * q ^ 2 * d +
        (65402280 + 17582400 * r) * v * q * d ^ 2 + (33581520 + 20230800 * r) * v * d ^ 3 +
        (6349392 + 1166400 * s) * q ^ 4 + (24909696 + 2131200 * s) * q ^ 3 * d +
        (31321800 + 4104000 * r) * q ^ 2 * d ^ 2 + (16790760 + 10115400 * r) * q * d ^ 3 +
        (7631135 + 5046600 * r) * d ^ 4) / 13996800 +
      z * (
        (3607488 + 9849600 * s) * v ^ 5 + (9018720 + 24624000 * s) * v ^ 4 * q +
        (15142752 + 20678400 * s) * v ^ 4 * d + (16727328 + 24753600 * s) * v ^ 3 * q ^ 2 +
        (30285504 + 41356800 * s) * v ^ 3 * q * d + (29101104 + 10918800 * s) * v ^ 3 * d ^ 2 +
        (16072272 + 12506400 * s) * v ^ 2 * q ^ 3 + (41722236 + 31795200 * s) * v ^ 2 * q ^ 2 * d +
        (43651656 + 16378200 * s) * v ^ 2 * q * d ^ 2 + (25602705 + 3269400 * r) * v ^ 2 * d ^ 3 +
        (6865056 + 3175200 * s) * v * q ^ 4 + (26579484 + 11116800 * s) * v * q ^ 3 * d +
        (37041516 + 9250200 * s) * v * q ^ 2 * d ^ 2 + (25602705 + 3269400 * r) * v * q * d ^ 3 +
        (10013300 + 4206000 * r) * v * d ^ 4 + (1054440 + 324000 * s) * q ^ 5 +
        (5665644 + 1486800 * s) * q ^ 4 * d + (11245482 + 1895400 * s) * q ^ 3 * d ^ 2 +
        (10761705 + 465000 * r) * q ^ 2 * d ^ 3 + (5006650 + 2103000 * r) * q * d ^ 4 +
        (1771395 + 905400 * r) * d ^ 5) / 6998400 +
      (
        (4174848 + 116121600 * s) * v ^ 6 + (12524544 + 348364800 * s) * v ^ 5 * q +
        (11621376 + 363571200 * s) * v ^ 5 * d + (78080256 + 439603200 * s) * v ^ 4 * q ^ 2 +
        (29053440 + 908928000 * s) * v ^ 4 * q * d + (83044800 + 411840000 * s) * v ^ 4 * d ^ 2 +
        (135286272 + 298598400 * s) * v ^ 3 * q ^ 3 + (250180992 +
        921254400 * s) * v ^ 3 * q ^ 2 * d +
        (166089600 + 823680000 * s) * v ^ 3 * q * d ^ 2 + (184472352 +
        185702400 * s) * v ^ 3 * d ^ 3 +
        (96850944 + 115084800 * s) * v ^ 2 * q ^ 4 + (346218048 +
        472953600 * s) * v ^ 2 * q ^ 3 * d +
        (391923936 + 642211200 * s) * v ^ 2 * q ^ 2 * d ^ 2 +
        (276708528 + 278553600 * s) * v ^ 2 * q * d ^ 3 + (171156696 +
        6115200 * s) * v ^ 2 * d ^ 4 +
        (31295232 + 23846400 * s) * v * q ^ 5 + (168427584 + 122860800 * s) * v * q ^ 4 * d +
        (308879136 + 230371200 * s) * v * q ^ 3 * d ^ 2 +
        (277574160 + 158496000 * s) * v * q ^ 2 * d ^ 3 + (171156696 +
        6115200 * s) * v * q * d ^ 4 +
        (57415720 + 18960000 * r) * v * d ^ 5 + (3791808 + 2073600 * s) * q ^ 6 +
        (27479232 + 12902400 * s) * q ^ 5 * d + (71635824 + 31852800 * s) * q ^ 4 * d ^ 2 +
        (92668992 + 32822400 * s) * q ^ 3 * d ^ 3 + (69976756 + 6307200 * s) * q ^ 2 * d ^ 4 +
        (28707860 + 9480000 * r) * q * d ^ 5 + (8695365 + 3988800 * r) * d ^ 6) / 223948800 := by
      positivity
    _ = _ := by
      simp only [quarticGap, spectralMoment, gapVector, endpointPrefixAverage,
        classicalInGaps, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
        s]
      ring_nf
      simp only [hSq, hCube, hFourth]
      ring

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 4096 in
-- Normalize both degree-six polynomials, then reduce powers of the damping.
private theorem one_prefix_t_le_p {r z v q d : ℝ}
    (hr : 0 ≤ r) (hSq : r ^ 2 = (2 / 3 : ℝ)) (hUpper : 0 ≤ 41 / 50 - r)
    (hz : 0 ≤ z) (hv : 0 ≤ v) (hq : 0 ≤ q) (hd : 0 ≤ d) :
    0 ≤ quarticGap (gapVector z (v + d) q v)
      (endpointPrefixAverage 1 (classicalInGaps r z (v + d) q v)) := by
  let s : ℝ := 41 / 50 - r
  have hs : 0 ≤ s := hUpper
  obtain ⟨hCube, hFourth⟩ := damping_powers hSq
  calc
    0 ≤
      z ^ 4 * (
        600 * v ^ 2 + 600 * v * q + (108 + 600 * s) * v * d + 600 * q ^ 2 + (54 + 300 * s) * q * d +
        (79 + 300 * s) * d ^ 2) / 1800 +
      z ^ 3 * (
        (62784 + 28800 * s) * v ^ 3 + (94176 + 43200 * s) * v ^ 2 * q +
        (11628 + 129600 * s) * v ^ 2 * d + (111888 + 21600 * s) * v * q ^ 2 +
        (11628 + 129600 * s) * v * q * d + (4500 + 90000 * s) * v * d ^ 2 + (40248 +
        3600 * s) * q ^ 3 +
        (13032 + 32400 * s) * q ^ 2 * d + (2250 + 45000 * s) * q * d ^ 2 + (691 +
        16200 * s) * d ^ 3) / 64800 +
      z ^ 2 * (
        (15043392 + 18662400 * s) * v ^ 4 + (30086784 + 37324800 * s) * v ^ 3 * q +
        (3966624 + 59932800 * s) * v ^ 3 * d + (44376768 + 27993600 * s) * v ^ 2 * q ^ 2 +
        (5949936 + 89899200 * s) * v ^ 2 * q * d + (1459368 + 50241600 * s) * v ^ 2 * d ^ 2 +
        (29333376 + 9331200 * s) * v * q ^ 3 + (10830672 + 44366400 * s) * v * q ^ 2 * d +
        (1459368 + 50241600 * s) * v * q * d ^ 2 + (1021656 + 15565200 * s) * v * d ^ 3 +
        (6349392 + 1166400 * s) * q ^ 4 + (4423680 + 7200000 * s) * q ^ 3 * d +
        (1140984 + 12268800 * s) * q ^ 2 * d ^ 2 + (510828 + 7782600 * s) * q * d ^ 3 +
        (254867 + 1547400 * s) * d ^ 4) / 13996800 +
      z * (
        (3607488 + 9849600 * s) * v ^ 5 + (9018720 + 24624000 * s) * v ^ 4 * q +
        (2894688 + 28569600 * s) * v ^ 4 * d + (16727328 + 24753600 * s) * v ^ 3 * q ^ 2 +
        (5789376 + 57139200 * s) * v ^ 3 * q * d + (4604976 + 26701200 * s) * v ^ 3 * d ^ 2 +
        (16072272 + 12506400 * s) * v ^ 2 * q ^ 3 + (8459748 + 42465600 * s) * v ^ 2 * q ^ 2 * d +
        (6907464 + 40051800 * s) * v ^ 2 * q * d ^ 2 + (4238067 + 10451400 * s) * v ^ 2 * d ^ 3 +
        (6865056 + 3175200 * s) * v * q ^ 4 + (5565060 + 13896000 * s) * v * q ^ 3 * d +
        (3779028 + 19920600 * s) * v * q ^ 2 * d ^ 2 + (4238067 + 10451400 * s) * v * q * d ^ 3 +
        (1664738 + 1623600 * s) * v * d ^ 4 + (1054440 + 324000 * s) * q ^ 5 +
        (1199412 + 1688400 * s) * q ^ 4 * d + (738270 + 3285000 * s) * q ^ 3 * d ^ 2 +
        (903603 + 2673600 * s) * q ^ 2 * d ^ 3 + (832369 + 811800 * s) * q * d ^ 4 +
        (230624 + 58800 * s) * d ^ 5) / 6998400 +
      (
        (4174848 + 116121600 * s) * v ^ 6 + (12524544 + 348364800 * s) * v ^ 5 * q +
        (13427712 + 333158400 * s) * v ^ 5 * d + (78080256 + 439603200 * s) * v ^ 4 * q ^ 2 +
        (33569280 + 832896000 * s) * v ^ 4 * q * d + (87560640 + 335808000 * s) * v ^ 4 * d ^ 2 +
        (135286272 + 298598400 * s) * v ^ 3 * q ^ 3 + (62140032 +
        837158400 * s) * v ^ 3 * q ^ 2 * d +
        (175121280 + 671616000 * s) * v ^ 3 * q * d ^ 2 + (114990048 +
        148377600 * s) * v ^ 3 * d ^ 3 +
        (96850944 + 115084800 * s) * v ^ 2 * q ^ 4 + (59640768 +
        422841600 * s) * v ^ 2 * q ^ 3 * d +
        (109862496 + 516067200 * s) * v ^ 2 * q ^ 2 * d ^ 2 +
        (172485072 + 222566400 * s) * v ^ 2 * q * d ^ 3 + (62417400 +
        26160000 * s) * v ^ 2 * d ^ 4 +
        (31295232 + 23846400 * s) * v * q ^ 5 + (25274304 + 107308800 * s) * v * q ^ 4 * d +
        (22301856 + 180259200 * s) * v * q ^ 3 * d ^ 2 + (68051760 +
        120576000 * s) * v * q ^ 2 * d ^ 3 +
        (62417400 + 26160000 * s) * v * q * d ^ 4 + (15054824 + 316800 * s) * v * d ^ 5 +
        (3791808 + 2073600 * s) * q ^ 6 + (3816000 + 10944000 * s) * q ^ 5 * d +
        (59184 + 24076800 * s) * q ^ 4 * d ^ 2 + (5278368 + 23193600 * s) * q ^ 3 * d ^ 3 +
        (12225796 + 8371200 * s) * q ^ 2 * d ^ 4 + (7527412 + 158400 * s) * q * d ^ 5 +
        (1100885 + 225600 * r) * d ^ 6) / 223948800 := by
      positivity
    _ = _ := by
      simp only [quarticGap, spectralMoment, gapVector, endpointPrefixAverage,
        classicalInGaps, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
        s]
      ring_nf
      simp only [hSq, hCube, hFourth]
      ring

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 4096 in
-- Normalize both degree-six polynomials, then reduce powers of the damping.
private theorem two_prefix_p_le_t {r z v q d : ℝ}
    (hr : 0 ≤ r) (hSq : r ^ 2 = (2 / 3 : ℝ)) (hLower : 0 ≤ r - 4 / 5) (hUpper : 0 ≤ 41 / 50 - r)
    (hz : 0 ≤ z) (hv : 0 ≤ v) (hq : 0 ≤ q) (hd : 0 ≤ d) :
    0 ≤ quarticGap (gapVector z v q (v + d))
      (endpointPrefixAverage 2 (classicalInGaps r z v q (v + d))) := by
  let s : ℝ := 41 / 50 - r
  have hs : 0 ≤ s := hUpper
  let weight1 : ℝ := (2929 * r - 2160) / 2304
  have hWeight1 : 0 ≤ weight1 := by
    dsimp [weight1]
    linarith only [hLower]
  let weight2 : ℝ := (1587 * r - 1243) / 2304
  have hWeight2 : 0 ≤ weight2 := by
    dsimp [weight2]
    linarith only [hLower]
  obtain ⟨hCube, hFourth⟩ := damping_powers hSq
  calc
    0 ≤
      weight1 * v ^ 2 * d ^ 2 * (v - q) ^ 2 +
      weight2 * v ^ 3 * d * (2 * q - v) ^ 2 +
      z ^ 4 * (
        12 * v ^ 2 + (12 + 12 * r) * v * d + (7 + 6 * r) * d ^ 2) / 48 +
      z ^ 3 * (
        (3324 + 1800 * s) * v ^ 3 + (924 + 1800 * s) * v ^ 2 * q + (7800 + 2100 * r) * v ^ 2 * d +
        (1800 + 600 * r) * v * q * d + (5800 + 4350 * r) * v * d ^ 2 + (1100 +
        450 * r) * q * d ^ 2 +
        (1950 + 1425 * r) * d ^ 3) / 4800 +
      z ^ 2 * (
        (403056 + 583200 * s) * v ^ 4 + (318024 + 874800 * s) * v ^ 3 * q +
        (1512684 + 541800 * s) * v ^ 3 * d + (259848 + 291600 * s) * v ^ 2 * q ^ 2 +
        (915624 + 658800 * s) * v ^ 2 * q * d + (1886940 + 353700 * r) * v ^ 2 * d ^ 2 +
        175680 * v * q ^ 3 + (330912 + 86400 * s) * v * q ^ 2 * d +
        (912240 + 45900 * r) * v * q * d ^ 2 + (989460 + 487050 * r) * v * d ^ 3 + 43920 * q ^ 4 +
        87840 * q ^ 3 * d + (136602 + 18900 * s) * q ^ 2 * d ^ 2 + (286380 +
        54000 * r) * q * d ^ 3 +
        (229480 + 123825 * r) * d ^ 4) / 518400 +
      z * (
        (220968 + 615600 * s) * v ^ 5 + (387216 + 1231200 * s) * v ^ 4 * q +
        (848628 + 1326600 * s) * v ^ 4 * d + (618048 + 777600 * s) * v ^ 3 * q ^ 2 +
        (914796 + 2086200 * s) * v ^ 3 * q * d + (1584450 + 823500 * s) * v ^ 3 * d ^ 2 +
        (587880 + 162000 * s) * v ^ 2 * q ^ 3 + (909036 + 880200 * s) * v ^ 2 * q ^ 2 * d +
        (1178280 + 1080000 * s) * v ^ 2 * q * d ^ 2 + (1519380 + 22350 * r) * v ^ 2 * d ^ 3 +
        263520 * v * q ^ 4 + (602712 + 86400 * s) * v * q ^ 3 * d +
        (549000 + 324000 * s) * v * q ^ 2 * d ^ 2 + (784401 + 160950 * s) * v * q * d ^ 3 +
        (599900 + 167550 * r) * v * d ^ 4 + 43920 * q ^ 5 + 153720 * q ^ 4 * d +
        (165006 + 29700 * s) * q ^ 3 * d ^ 2 + (142551 + 63450 * s) * q ^ 2 * d ^ 3 +
        (199189 + 1050 * s) * q * d ^ 4 + (107295 + 38925 * r) * d ^ 5) / 518400 +
      (
        (238464 + 3628800 * s) * v ^ 6 + (820800 + 9072000 * s) * v ^ 5 * q +
        (30168 + 17031600 * s) * v ^ 5 * d + (3272832 + 8294400 * s) * v ^ 4 * q ^ 2 +
        (704088 + 23691600 * s) * v ^ 4 * d ^ 2 + (4915008 + 3369600 * s) * v ^ 3 * q ^ 3 +
        (2994048 + 38073600 * s) * v ^ 3 * q ^ 2 * d + (4134960 + 6660000 * s) * v ^ 3 * d ^ 3 +
        (3341952 + 518400 * s) * v ^ 2 * q ^ 4 + (6990336 + 3715200 * s) * v ^ 2 * q ^ 3 * d +
        (326808 + 20523600 * s) * v ^ 2 * q ^ 2 * d ^ 2 + (584856 +
        8701200 * s) * v ^ 2 * q * d ^ 3 +
        (4137336 + 1039200 * s) * v ^ 2 * d ^ 4 + 1059840 * v * q ^ 5 +
        (3858624 + 172800 * s) * v * q ^ 4 * d + (3167856 + 1447200 * s) * v * q ^ 3 * d ^ 2 +
        (229224 + 3058800 * s) * v * q ^ 2 * d ^ 3 + (1355160 + 1596000 * s) * v * q * d ^ 4 +
        (1646360 + 232800 * r) * v * d ^ 5 + 118080 * q ^ 6 + 705600 * q ^ 5 * d +
        (1111536 + 43200 * s) * q ^ 4 * d ^ 2 + (493200 + 324000 * s) * q ^ 3 * d ^ 3 +
        (116684 + 472800 * s) * q ^ 2 * d ^ 4 + (407644 + 124800 * s) * q * d ^ 5 +
        (253695 + 68400 * r) * d ^ 6) / 8294400 := by
      positivity
    _ = _ := by
      simp only [quarticGap, spectralMoment, gapVector, endpointPrefixAverage,
        classicalInGaps, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
        s, weight1, weight2]
      ring_nf
      simp only [hSq, hCube, hFourth]
      ring

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 4096 in
-- Normalize both degree-six polynomials, then reduce powers of the damping.
private theorem two_prefix_t_le_p {r z v q d : ℝ}
    (hSq : r ^ 2 = (2 / 3 : ℝ)) (hLower : 0 ≤ r - 4 / 5) (hUpper : 0 ≤ 41 / 50 - r)
    (hz : 0 ≤ z) (hv : 0 ≤ v) (hq : 0 ≤ q) (hd : 0 ≤ d) :
    0 ≤ quarticGap (gapVector z (v + d) q v)
      (endpointPrefixAverage 2 (classicalInGaps r z (v + d) q v)) := by
  let s : ℝ := 41 / 50 - r
  have hs : 0 ≤ s := hUpper
  let weight1 : ℝ := (7 * r - 5) / 32
  have hWeight1 : 0 ≤ weight1 := by
    dsimp [weight1]
    linarith only [hLower]
  obtain ⟨hCube, hFourth⟩ := damping_powers hSq
  calc
    0 ≤
      weight1 * z ^ 2 * v * d * (z - 2 * q) ^ 2 +
      z ^ 4 * (
        1200 * v ^ 2 + (105 + 2250 * s) * v * d + (208 + 600 * s) * d ^ 2) / 4800 +
      z ^ 3 * (
        (6648 + 3600 * s) * v ^ 3 + (1848 + 3600 * s) * v ^ 2 * q + (900 + 15000 * s) * v ^ 2 * d +
        (590 + 10500 * s) * v * d ^ 2 + (202 + 3900 * s) * q * d ^ 2 + (101 +
        1950 * s) * d ^ 3) / 9600 +
      z ^ 2 * (
        (806112 + 1166400 * s) * v ^ 4 + (636048 + 1749600 * s) * v ^ 3 * q +
        (199080 + 3582000 * s) * v ^ 3 * d + (519696 + 583200 * s) * v ^ 2 * q ^ 2 +
        (76896 + 3931200 * s) * v ^ 2 * q * d + (114516 + 3040200 * s) * v ^ 2 * d ^ 2 +
        351360 * v * q ^ 3 + (281664 + 1900800 * s) * v * q ^ 2 * d +
        (145404 + 2521800 * s) * v * q * d ^ 2 + (78558 + 974100 * s) * v * d ^ 3 + 87840 * q ^ 4 +
        175680 * q ^ 3 * d + (131076 + 448200 * s) * q ^ 2 * d ^ 2 + (43236 +
        448200 * s) * q * d ^ 3 +
        (19043 + 101850 * s) * d ^ 4) / 1036800 +
      z * (
        (441936 + 1231200 * s) * v ^ 5 + (774432 + 2462400 * s) * v ^ 4 * q +
        (512424 + 3502800 * s) * v ^ 4 * d + (1236096 + 1555200 * s) * v ^ 3 * q ^ 2 +
        (1268136 + 5677200 * s) * v ^ 3 * q * d + (799236 + 3346200 * s) * v ^ 3 * d ^ 2 +
        (1175760 + 324000 * s) * v ^ 2 * q ^ 3 + (1890216 + 2905200 * s) * v ^ 2 * q ^ 2 * d +
        (1514376 + 4417200 * s) * v ^ 2 * q * d ^ 2 + (667110 + 1378500 * s) * v ^ 2 * d ^ 3 +
        527040 * v * q ^ 4 + (1146096 + 475200 * s) * v * q ^ 3 * d +
        (1170144 + 1792800 * s) * v * q ^ 2 * d ^ 2 + (753270 + 1330500 * s) * v * q * d ^ 3 +
        (251110 + 238500 * s) * v * d ^ 4 + 87840 * q ^ 5 + 219600 * q ^ 4 * d +
        (300348 + 210600 * s) * q ^ 3 * d ^ 2 + (230922 + 315900 * s) * q ^ 2 * d ^ 3 +
        (130976 + 130200 * s) * q * d ^ 4 + (34321 + 12450 * s) * d ^ 5) / 1036800 +
      (
        (238464 + 3628800 * s) * v ^ 6 + (820800 + 9072000 * s) * v ^ 5 * q +
        (1190592 + 10454400 * s) * v ^ 5 * d + (3272832 + 8294400 * s) * v ^ 4 * q ^ 2 +
        (4944096 + 22507200 * s) * v ^ 4 * q * d + (3950496 + 10987200 * s) * v ^ 4 * d ^ 2 +
        (4915008 + 3369600 * s) * v ^ 3 * q ^ 3 + (9257184 + 17956800 * s) * v ^ 3 * q ^ 2 * d +
        (9827568 + 20397600 * s) * v ^ 3 * q * d ^ 2 + (4530384 + 5320800 * s) * v ^ 3 * d ^ 3 +
        (3341952 + 518400 * s) * v ^ 2 * q ^ 4 + (7754688 + 6393600 * s) * v ^ 2 * q ^ 3 * d +
        (9331776 + 14083200 * s) * v ^ 2 * q ^ 2 * d ^ 2 + (7441272 +
        8168400 * s) * v ^ 2 * q * d ^ 3 +
        (2354472 + 1190400 * s) * v ^ 2 * d ^ 4 + 1059840 * v * q ^ 5 +
        (2825280 + 864000 * s) * v * q ^ 4 * d + (3932208 + 4125600 * s) * v * q ^ 3 * d ^ 2 +
        (3754104 + 4414800 * s) * v * q ^ 2 * d ^ 3 + (2427384 + 1408800 * s) * v * q * d ^ 4 +
        (560344 + 100800 * s) * v * d ^ 5 + 118080 * q ^ 6 + 354240 * q ^ 5 * d +
        (594864 + 388800 * s) * q ^ 4 * d ^ 2 + (599328 + 777600 * s) * q ^ 3 * d ^ 3 +
        (523364 + 466800 * s) * q ^ 2 * d ^ 4 + (282740 + 78000 * s) * q * d ^ 5 +
        (47671 + 1200 * s) * d ^ 6) / 8294400 := by
      positivity
    _ = _ := by
      simp only [quarticGap, spectralMoment, gapVector, endpointPrefixAverage,
        classicalInGaps, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
        s, weight1]
      ring_nf
      simp only [hSq, hCube, hFourth]
      ring

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 4096 in
-- Normalize both degree-six polynomials, then reduce powers of the damping.
private theorem three_prefix_p_le_t {r z v q d : ℝ}
    (hSq : r ^ 2 = (2 / 3 : ℝ))
    (hz : 0 ≤ z) (hv : 0 ≤ v) (hq : 0 ≤ q) (hd : 0 ≤ d) :
    0 ≤ quarticGap (gapVector z v q (v + d))
      (endpointPrefixAverage 3 (classicalInGaps r z v q (v + d))) := by
  obtain ⟨_, hFourth⟩ := damping_powers hSq
  calc
    0 ≤
      z ^ 4 * (
        d ^ 2) / 24 +
      z ^ 3 * (
        12 * v ^ 2 * d + 12 * v * q * d + 28 * v * d ^ 2 + 14 * q * d ^ 2 + 15 * d ^ 3) / 96 +
      z ^ 2 * (
        23616 * v ^ 4 + 47232 * v ^ 3 * q + 86112 * v ^ 3 * d + 58752 * v ^ 2 * q ^ 2 +
        129168 * v ^ 2 * q * d + 133128 * v ^ 2 * d ^ 2 + 35136 * v * q ^ 3 +
        78192 * v * q ^ 2 * d +
        133128 * v * q * d ^ 2 + 93312 * v * d ^ 3 + 8784 * q ^ 4 + 17568 * q ^ 3 * d +
        32760 * q ^ 2 * d ^ 2 + 46656 * q * d ^ 3 + 24661 * d ^ 4) / 103680 +
      z * (
        23616 * v ^ 5 + 59040 * v ^ 4 * q + 69264 * v ^ 4 * d + 82368 * v ^ 3 * q ^ 2 +
        138528 * v ^ 3 * q * d + 101592 * v ^ 3 * d ^ 2 + 64512 * v ^ 2 * q ^ 3 +
        139860 * v ^ 2 * q ^ 2 * d + 152388 * v ^ 2 * q * d ^ 2 + 85563 * v ^ 2 * d ^ 3 +
        26352 * v * q ^ 4 + 70596 * v * q ^ 3 * d + 93168 * v * q ^ 2 * d ^ 2 +
        85563 * v * q * d ^ 3 +
        38620 * v * d ^ 4 + 4392 * q ^ 5 + 15372 * q ^ 4 * d + 21186 * q ^ 3 * d ^ 2 +
        24003 * q ^ 2 * d ^ 3 + 19310 * q * d ^ 4 + 7257 * d ^ 5) / 51840 +
      (
        193536 * v ^ 6 + 580608 * v ^ 5 * q + 493056 * v ^ 5 * d + 1052928 * v ^ 4 * q ^ 2 +
        1232640 * v ^ 4 * q * d + 728640 * v ^ 4 * d ^ 2 + 1138176 * v ^ 3 * q ^ 3 +
        2021760 * v ^ 3 * q ^ 2 * d + 1457280 * v ^ 3 * q * d ^ 2 + 811872 * v ^ 3 * d ^ 3 +
        684288 * v ^ 2 * q ^ 4 + 1800000 * v ^ 2 * q ^ 3 * d + 1710432 * v ^ 2 * q ^ 2 * d ^ 2 +
        1217808 * v ^ 2 * q * d ^ 3 + 583656 * v ^ 2 * d ^ 4 + 211968 * v * q ^ 5 +
        800064 * v * q ^ 4 * d + 981792 * v * q ^ 3 * d ^ 2 + 804528 * v * q ^ 2 * d ^ 3 +
        583656 * v * q * d ^ 4 + 228632 * v * d ^ 5 + 23616 * q ^ 6 + 141120 * q ^ 5 * d +
        235152 * q ^ 4 * d ^ 2 + 199296 * q ^ 3 * d ^ 3 + 168236 * q ^ 2 * d ^ 4 +
        114316 * q * d ^ 5 +
        37299 * d ^ 6) / 1658880 := by
      positivity
    _ = _ := by
      simp only [quarticGap, spectralMoment, gapVector, endpointPrefixAverage,
        classicalInGaps, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
      ring_nf
      simp only [hSq, hFourth]
      ring

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 4096 in
-- Normalize both degree-six polynomials, then reduce powers of the damping.
private theorem three_prefix_t_le_p {r z v q d : ℝ}
    (hSq : r ^ 2 = (2 / 3 : ℝ))
    (hz : 0 ≤ z) (hv : 0 ≤ v) (hq : 0 ≤ q) (hd : 0 ≤ d) :
    0 ≤ quarticGap (gapVector z (v + d) q v)
      (endpointPrefixAverage 3 (classicalInGaps r z (v + d) q v)) := by
  let m : ℝ := z + ((v + d) + 2 * q + 3 * v) / 4
  let a : ℝ := ((v + d) + 2 * q + v) / 4
  let b : ℝ := ((v + d) + v) / 4
  let c : ℝ := ((v + d) - v) / 4
  obtain ⟨_, hFourth⟩ := damping_powers hSq
  calc
    0 ≤
      (2 / 3) * m ^ 2 * (m * c - (3 / 2) * a * b) ^ 2 +
      z ^ 2 * (
        27792 * v ^ 4 + 55584 * v ^ 3 * q + 55584 * v ^ 3 * d + 98064 * v ^ 2 * q ^ 2 +
        83376 * v ^ 2 * q * d + 49176 * v ^ 2 * d ^ 2 + 70272 * v * q ^ 3 + 98064 * v * q ^ 2 * d +
        49176 * v * q * d ^ 2 + 21384 * v * d ^ 3 + 17568 * q ^ 4 + 35136 * q ^ 3 * d +
        28260 * q ^ 2 * d ^ 2 + 10692 * q * d ^ 3 + 4367 * d ^ 4) / 207360 +
      z * (
        111168 * v ^ 5 + 277920 * v ^ 4 * q + 371088 * v ^ 4 * d + 503424 * v ^ 3 * q ^ 2 +
        742176 * v ^ 3 * q * d + 494208 * v ^ 3 * d ^ 2 + 477216 * v ^ 2 * q ^ 3 +
        838512 * v ^ 2 * q ^ 2 * d + 741312 * v ^ 2 * q * d ^ 2 + 324792 * v ^ 2 * d ^ 3 +
        210816 * v * q ^ 4 + 467424 * v * q ^ 3 * d + 490896 * v * q ^ 2 * d ^ 2 +
        324792 * v * q * d ^ 3 + 107972 * v * d ^ 4 + 35136 * q ^ 5 + 87840 * q ^ 4 * d +
        121896 * q ^ 3 * d ^ 2 + 95004 * q ^ 2 * d ^ 3 + 53986 * q * d ^ 4 +
        14087 * d ^ 5) / 414720 +
      (
        76032 * v ^ 6 + 228096 * v ^ 5 * q + 973440 * v ^ 5 * d + 1094976 * v ^ 4 * q ^ 2 +
        2433600 * v ^ 4 * q * d + 2123280 * v ^ 4 * d ^ 2 + 1809792 * v ^ 3 * q ^ 3 +
        3602304 * v ^ 3 * q ^ 2 * d + 4246560 * v ^ 3 * q * d ^ 2 + 2012256 * v ^ 3 * d ^ 3 +
        1290816 * v ^ 2 * q ^ 4 + 2969856 * v ^ 2 * q ^ 3 * d + 3659760 * v ^ 2 * q ^ 2 * d ^ 2 +
        3018384 * v ^ 2 * q * d ^ 3 + 968520 * v ^ 2 * d ^ 4 + 423936 * v * q ^ 5 +
        1111104 * v * q ^ 4 * d + 1536480 * v * q ^ 3 * d ^ 2 + 1480176 * v * q ^ 2 * d ^ 3 +
        968520 * v * q * d ^ 4 + 224960 * v * d ^ 5 + 47232 * q ^ 6 + 141696 * q ^ 5 * d +
        236592 * q ^ 4 * d ^ 2 + 237024 * q ^ 3 * d ^ 3 + 207376 * q ^ 2 * d ^ 4 +
        112480 * q * d ^ 5 +
        19007 * d ^ 6) / 3317760 := by
      positivity
    _ = _ := by
      simp only [quarticGap, spectralMoment, gapVector, endpointPrefixAverage,
        classicalInGaps, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
        m, a, b, c]
      ring_nf
      simp only [hSq, hFourth]
      ring

/-- The `1/5` endpoint bound for every prefix average of the classical endpoint image. -/
public theorem endpoint_quartic_prefix (x : Fin 4 → ℝ) (hSorted : Antitone x)
    (hNonneg : ∀ i, 0 ≤ x i) (k : Fin 4) :
    (spectralMoment 1 x) ^ 2 * (spectralMoment 2 x - (spectralMoment 1 x) ^ 2) ^ 2 / 5 ≤
      spectralMoment 3 x * spectralMoment 3 (endpointPrefixAverage k (endpointClassical x)) -
        spectralMoment 2 x * spectralMoment 4 (endpointPrefixAverage k (endpointClassical x)) := by
  let z := x 3
  let p := x 0 - x 1
  let q := x 1 - x 2
  let t := x 2 - x 3
  have hz : 0 ≤ z := hNonneg 3
  have hp : 0 ≤ p := sub_nonneg.mpr (hSorted (by decide : (0 : Fin 4) ≤ 1))
  have hq : 0 ≤ q := sub_nonneg.mpr (hSorted (by decide : (1 : Fin 4) ≤ 2))
  have ht : 0 ≤ t := sub_nonneg.mpr (hSorted (by decide : (2 : Fin 4) ≤ 3))
  have hVector : x = gapVector z p q t := by
    funext i
    fin_cases i <;>
      simp [gapVector, z, p, q, t, Matrix.cons_val_two, Matrix.cons_val_three,
        Matrix.head_cons, Matrix.tail_cons] <;> ring
  have hDamping : 0 ≤ lambda := Real.sqrt_nonneg _
  have hLower : 0 ≤ lambda - 4 / 5 := by
    apply sub_nonneg.mpr
    apply (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 4 / 5) hDamping).mp
    rw [damping_sq]
    norm_num
  have hUpper : 0 ≤ 41 / 50 - lambda := by
    apply sub_nonneg.mpr
    apply (sq_le_sq₀ hDamping (by norm_num : (0 : ℝ) ≤ 41 / 50)).mp
    rw [damping_sq]
    norm_num
  apply sub_nonneg.mp
  change 0 ≤ quarticGap x (endpointPrefixAverage k (endpointClassical x))
  rw [hVector, endpointClassical_gapVector]
  fin_cases k <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
  · rw [zeroPrefix_eq_mean, ← hVector]
    exact uniform_gap x hNonneg
  · rcases le_total p t with hpt | htp
    · simpa only [show p + (t - p) = t by ring] using
        one_prefix_p_le_t hDamping damping_sq hUpper hz hp hq (sub_nonneg.mpr hpt)
    · simpa only [show t + (p - t) = p by ring] using
        one_prefix_t_le_p hDamping damping_sq hUpper hz ht hq (sub_nonneg.mpr htp)
  · rcases le_total p t with hpt | htp
    · simpa only [show p + (t - p) = t by ring] using
        two_prefix_p_le_t hDamping damping_sq hLower hUpper hz hp hq (sub_nonneg.mpr hpt)
    · simpa only [show t + (p - t) = p by ring] using
        two_prefix_t_le_p damping_sq hLower hUpper hz ht hq (sub_nonneg.mpr htp)
  · rcases le_total p t with hpt | htp
    · simpa only [show p + (t - p) = t by ring] using
        three_prefix_p_le_t damping_sq hz hp hq (sub_nonneg.mpr hpt)
    · simpa only [show t + (p - t) = p by ring] using
        three_prefix_t_le_p damping_sq hz ht hq (sub_nonneg.mpr htp)

#print axioms endpoint_quartic_prefix

end WuRankOneEndpointFloor
