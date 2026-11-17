/- GID: D5/S3/Arith/Robin/PriceRecord/ActualInventoryTailBounds
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/PriceRecord/ActualInventoryTailBounds
   mirror-E: none(waiver:uniform-real-clock-estimates)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Arith/Robin/PriceRecord/ActualInventoryCollectiveSeparation.actual_witness; premises=D5/S3/Arith/Robin/PriceRecord/ActualInventoryTailBounds.w_N_bounds_raw,D5/S3/Arith/Robin/PriceRecord/ActualInventoryTailBounds.w_M_bounds_raw
   digest: Uniform rational logarithmic estimates supply the actual inventory separation. -/

import D5.S3.Arith.Robin.PriceRecord.ActualInventorySmallPrimeBounds

set_option autoImplicit false
set_option maxRecDepth 100000
noncomputable section
namespace D5.S3.Arith.Robin.PriceRecord.ActualInventoryBounds

open D5.S3.Arith.GoldenResourceOptimalInteger
open D5.S3.Arith.GoldenResource.GoldenResourceThresholdCriterion
open D5.S3.Arith.GoldenResourceObjectiveFactorization
open D5.S3.Arith.GoldenResource5040PriceInterval
open D5.S3.Arith.GoldenResource.GoldenSmallestMissingPrime
open D5.S3.Arith.GoldenResource.FirstLayerMarginalAntitone
open D5.S3.Arith.GoldenResource.GoldenResource5040EndpointComparison
open D5.S3.Arith.GoldenResource.RobinRationalBasis
open D5.S3.Arith.Robin.ActualTwoPriceDefect
open D5.S3.Arith.Robin.ActualGlobalBracketing
open D5.S3.Arith.Robin.ActualRobinInterval
open D5.S3.Arith.Robin.PriceRecord.ActualBalancedCutoff
open D5.S3.Arith.Robin.PriceRecord.NonlinearPrimeExclusion
open D5.S3.Weil.GronwallLowerEnvelope
open scoped BigOperators


variable {L : ℝ} (hclock : ((352426901 / 10000000) : ℝ) < L ∧ L < (44053363 / 1250000))

theorem log_prime_17 :
    ((7083033 / 2500000) : ℝ) < Real.log 17 ∧ Real.log 17 < (5666427 / 2000000) := by
  refine rational_log_bounds 17 (17 / 16) _ _ 4 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

theorem gain_17_1_bounds :
    ((571583 / 10000000) : ℝ) < Real.log (18 / 17) ∧ Real.log (18 / 17) < (285793 / 5000000) := by
  have hs := log_expansion_remainder_bound (y := ((18 / 17) : ℝ)) (by norm_num) (by norm_num) 8
  norm_num [logRemainder, atanhParameter, atanhPartial, Finset.sum_range_succ] at hs
  constructor <;> linarith only [hs.1, hs.2]

theorem gain_17_1_identity :
    goldenLayerMarginal 17 1 * Real.log 17 = Real.log ((18 / 17) : ℝ) := by
  norm_num [goldenLayerMarginal]

theorem gain_17_2_bounds :
    ((261 / 80000) : ℝ) < Real.log (307 / 306) ∧ Real.log (307 / 306) < (8157 / 2500000) := by
  have hs := log_expansion_remainder_bound (y := ((307 / 306) : ℝ)) (by norm_num) (by norm_num) 8
  norm_num [logRemainder, atanhParameter, atanhPartial, Finset.sum_range_succ] at hs
  constructor <;> linarith only [hs.1, hs.2]

theorem gain_17_2_identity :
    goldenLayerMarginal 17 2 * Real.log 17 = Real.log ((307 / 306) : ℝ) := by
  norm_num [goldenLayerMarginal]

include hclock in
private theorem delete_17_clock :
    ((162047383 / 5000000) : ℝ) < L - Real.log 17 ∧ L - Real.log 17 < (81023693 / 2500000) := by
  have hn := hclock
  have hp := log_prime_17
  constructor <;> linarith only [hn.1, hn.2, hp.1, hp.2]

private theorem log_literal_52 :
    ((34784507 / 10000000) : ℝ) < Real.log (162047383 / 5000000) ∧ Real.log (162047383 /
        5000000) < (3478451 / 1000000) := by
  refine rational_log_bounds (162047383 / 5000000) (162047383 / 160000000) _ _ 5 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

private theorem log_literal_53 :
    ((34784507 / 10000000) : ℝ) < Real.log (81023693 / 2500000) ∧ Real.log (81023693 / 2500000)
        < (3478451 / 1000000) := by
  refine rational_log_bounds (81023693 / 2500000) (81023693 / 80000000) _ _ 5 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

include hclock in
private theorem delete_17_log :
    ((34784507 / 10000000) : ℝ) < Real.log (L - Real.log 17) ∧ Real.log (L - Real.log 17) <
        (3478451 / 1000000) := by
  exact log_interval_bounds (by norm_num) ((delete_17_clock hclock)).1 ((delete_17_clock hclock)).2
      log_literal_52.1 log_literal_53.2

private theorem log_literal_54 :
    ((3116467 / 2500000) : ℝ) < Real.log (34784507 / 10000000) ∧ Real.log (34784507 / 10000000)
        < (12465871 / 10000000) := by
  refine rational_log_bounds (34784507 / 10000000) (34784507 / 20000000) _ _ 1 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

private theorem log_literal_55 :
    ((12465869 / 10000000) : ℝ) < Real.log (3478451 / 1000000) ∧ Real.log (3478451 / 1000000) <
        (779117 / 625000) := by
  refine rational_log_bounds (3478451 / 1000000) (3478451 / 2000000) _ _ 1 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

include hclock in
theorem delete_17_f :
    ((3116467 / 2500000) : ℝ) < Real.log (Real.log (L - Real.log 17)) ∧ Real.log (Real.log (L -
        Real.log 17)) < (779117 / 625000) := by
  exact log_interval_bounds (by norm_num) ((delete_17_log hclock)).1 ((delete_17_log hclock)).2 log_literal_54.1
      log_literal_55.2

include hclock in
private theorem insert_17_clock :
    ((380759033 / 10000000) : ℝ) < L + Real.log 17 ∧ L + Real.log 17 < (380759039 / 10000000) := by
  have hn := hclock
  have hp := log_prime_17
  constructor <;> linarith only [hn.1, hn.2, hp.1, hp.2]

private theorem log_literal_56 :
    ((7279163 / 2000000) : ℝ) < Real.log (380759033 / 10000000) ∧ Real.log (380759033 /
        10000000) < (18197909 / 5000000) := by
  refine rational_log_bounds (380759033 / 10000000) (380759033 / 320000000) _ _ 5 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

private theorem log_literal_57 :
    ((7279163 / 2000000) : ℝ) < Real.log (380759039 / 10000000) ∧ Real.log (380759039 /
        10000000) < (18197909 / 5000000) := by
  refine rational_log_bounds (380759039 / 10000000) (380759039 / 320000000) _ _ 5 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

include hclock in
private theorem insert_17_log :
    ((7279163 / 2000000) : ℝ) < Real.log (L + Real.log 17) ∧ Real.log (L + Real.log 17) <
        (18197909 / 5000000) := by
  exact log_interval_bounds (by norm_num) ((insert_17_clock hclock)).1 ((insert_17_clock hclock)).2
      log_literal_56.1 log_literal_57.2

private theorem log_literal_58 :
    ((6459343 / 5000000) : ℝ) < Real.log (7279163 / 2000000) ∧ Real.log (7279163 / 2000000) <
        (12918689 / 10000000) := by
  refine rational_log_bounds (7279163 / 2000000) (7279163 / 4000000) _ _ 1 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

private theorem log_literal_59 :
    ((6459343 / 5000000) : ℝ) < Real.log (18197909 / 5000000) ∧ Real.log (18197909 / 5000000) <
        (12918689 / 10000000) := by
  refine rational_log_bounds (18197909 / 5000000) (18197909 / 10000000) _ _ 1 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

include hclock in
theorem insert_17_f :
    ((6459343 / 5000000) : ℝ) < Real.log (Real.log (L + Real.log 17)) ∧ Real.log (Real.log (L +
        Real.log 17)) < (12918689 / 10000000) := by
  exact log_interval_bounds (by norm_num) ((insert_17_log hclock)).1 ((insert_17_log hclock)).2 log_literal_58.1
      log_literal_59.2

theorem log_prime_19 :
    ((7361097 / 2500000) : ℝ) < Real.log 19 ∧ Real.log 19 < (29444391 / 10000000) := by
  refine rational_log_bounds 19 (19 / 16) _ _ 4 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

theorem gain_19_1_bounds :
    ((512931 / 10000000) : ℝ) < Real.log (20 / 19) ∧ Real.log (20 / 19) < (256467 / 5000000) := by
  have hs := log_expansion_remainder_bound (y := ((20 / 19) : ℝ)) (by norm_num) (by norm_num) 8
  norm_num [logRemainder, atanhParameter, atanhPartial, Finset.sum_range_succ] at hs
  constructor <;> linarith only [hs.1, hs.2]

theorem gain_19_1_identity :
    goldenLayerMarginal 19 1 * Real.log 19 = Real.log ((20 / 19) : ℝ) := by
  norm_num [goldenLayerMarginal]

theorem gain_19_2_bounds :
    ((657 / 250000) : ℝ) < Real.log (381 / 380) ∧ Real.log (381 / 380) < (26283 / 10000000) := by
  have hs := log_expansion_remainder_bound (y := ((381 / 380) : ℝ)) (by norm_num) (by norm_num) 8
  norm_num [logRemainder, atanhParameter, atanhPartial, Finset.sum_range_succ] at hs
  constructor <;> linarith only [hs.1, hs.2]

theorem gain_19_2_identity :
    goldenLayerMarginal 19 2 * Real.log 19 = Real.log ((381 / 380) : ℝ) := by
  norm_num [goldenLayerMarginal]

include hclock in
private theorem delete_19_clock :
    ((32298251 / 1000000) : ℝ) < L - Real.log 19 ∧ L - Real.log 19 < (80745629 / 2500000) := by
  have hn := hclock
  have hp := log_prime_19
  constructor <;> linarith only [hn.1, hn.2, hp.1, hp.2]

private theorem log_literal_60 :
    ((34750129 / 10000000) : ℝ) < Real.log (32298251 / 1000000) ∧ Real.log (32298251 / 1000000)
        < (8687533 / 2500000) := by
  refine rational_log_bounds (32298251 / 1000000) (32298251 / 32000000) _ _ 5 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

private theorem log_literal_61 :
    ((34750129 / 10000000) : ℝ) < Real.log (80745629 / 2500000) ∧ Real.log (80745629 / 2500000)
        < (8687533 / 2500000) := by
  refine rational_log_bounds (80745629 / 2500000) (80745629 / 80000000) _ _ 5 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

include hclock in
private theorem delete_19_log :
    ((34750129 / 10000000) : ℝ) < Real.log (L - Real.log 19) ∧ Real.log (L - Real.log 19) <
        (8687533 / 2500000) := by
  exact log_interval_bounds (by norm_num) ((delete_19_clock hclock)).1 ((delete_19_clock hclock)).2
      log_literal_60.1 log_literal_61.2

private theorem log_literal_62 :
    ((622799 / 500000) : ℝ) < Real.log (34750129 / 10000000) ∧ Real.log (34750129 / 10000000) <
        (12455983 / 10000000) := by
  refine rational_log_bounds (34750129 / 10000000) (34750129 / 20000000) _ _ 1 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

private theorem log_literal_63 :
    ((12455981 / 10000000) : ℝ) < Real.log (8687533 / 2500000) ∧ Real.log (8687533 / 2500000) <
        (778499 / 625000) := by
  refine rational_log_bounds (8687533 / 2500000) (8687533 / 5000000) _ _ 1 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

include hclock in
theorem delete_19_f :
    ((622799 / 500000) : ℝ) < Real.log (Real.log (L - Real.log 19)) ∧ Real.log (Real.log (L -
        Real.log 19)) < (778499 / 625000) := by
  exact log_interval_bounds (by norm_num) ((delete_19_log hclock)).1 ((delete_19_log hclock)).2 log_literal_62.1
      log_literal_63.2

include hclock in
private theorem insert_19_clock :
    ((381871289 / 10000000) : ℝ) < L + Real.log 19 ∧ L + Real.log 19 < (76374259 / 2000000) := by
  have hn := hclock
  have hp := log_prime_19
  constructor <;> linarith only [hn.1, hn.2, hp.1, hp.2]

private theorem log_literal_64 :
    ((4553123 / 1250000) : ℝ) < Real.log (381871289 / 10000000) ∧ Real.log (381871289 /
        10000000) < (36424987 / 10000000) := by
  refine rational_log_bounds (381871289 / 10000000) (381871289 / 320000000) _ _ 5 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

private theorem log_literal_65 :
    ((4553123 / 1250000) : ℝ) < Real.log (76374259 / 2000000) ∧ Real.log (76374259 / 2000000) <
        (36424987 / 10000000) := by
  refine rational_log_bounds (76374259 / 2000000) (76374259 / 64000000) _ _ 5 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

include hclock in
private theorem insert_19_log :
    ((4553123 / 1250000) : ℝ) < Real.log (L + Real.log 19) ∧ Real.log (L + Real.log 19) <
        (36424987 / 10000000) := by
  exact log_interval_bounds (by norm_num) ((insert_19_clock hclock)).1 ((insert_19_clock hclock)).2
      log_literal_64.1 log_literal_65.2

private theorem log_literal_66 :
    ((12926697 / 10000000) : ℝ) < Real.log (4553123 / 1250000) ∧ Real.log (4553123 / 1250000) <
        (129267 / 100000) := by
  refine rational_log_bounds (4553123 / 1250000) (4553123 / 2500000) _ _ 1 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

private theorem log_literal_67 :
    ((6463349 / 5000000) : ℝ) < Real.log (36424987 / 10000000) ∧ Real.log (36424987 / 10000000)
        < (12926701 / 10000000) := by
  refine rational_log_bounds (36424987 / 10000000) (36424987 / 20000000) _ _ 1 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

include hclock in
theorem insert_19_f :
    ((12926697 / 10000000) : ℝ) < Real.log (Real.log (L + Real.log 19)) ∧ Real.log (Real.log (L
        + Real.log 19)) < (12926701 / 10000000) := by
  exact log_interval_bounds (by norm_num) ((insert_19_log hclock)).1 ((insert_19_log hclock)).2 log_literal_66.1
      log_literal_67.2

theorem log_prime_23 :
    ((31354941 / 10000000) : ℝ) < Real.log 23 ∧ Real.log 23 < (489921 / 156250) := by
  refine rational_log_bounds 23 (23 / 16) _ _ 4 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

theorem gain_23_1_bounds :
    ((85119 / 2000000) : ℝ) < Real.log (24 / 23) ∧ Real.log (24 / 23) < (212799 / 5000000) := by
  have hs := log_expansion_remainder_bound (y := ((24 / 23) : ℝ)) (by norm_num) (by norm_num) 8
  norm_num [logRemainder, atanhParameter, atanhPartial, Finset.sum_range_succ] at hs
  constructor <;> linarith only [hs.1, hs.2]

theorem gain_23_1_identity :
    goldenLayerMarginal 23 1 * Real.log 23 = Real.log ((24 / 23) : ℝ) := by
  norm_num [goldenLayerMarginal]

theorem gain_23_2_bounds :
    ((9049 / 5000000) : ℝ) < Real.log (553 / 552) ∧ Real.log (553 / 552) < (18101 / 10000000) := by
  have hs := log_expansion_remainder_bound (y := ((553 / 552) : ℝ)) (by norm_num) (by norm_num) 8
  norm_num [logRemainder, atanhParameter, atanhPartial, Finset.sum_range_succ] at hs
  constructor <;> linarith only [hs.1, hs.2]

theorem gain_23_2_identity :
    goldenLayerMarginal 23 2 * Real.log 23 = Real.log ((553 / 552) : ℝ) := by
  norm_num [goldenLayerMarginal]

include hclock in
private theorem delete_23_clock :
    ((321071957 / 10000000) : ℝ) < L - Real.log 23 ∧ L - Real.log 23 < (321071963 / 10000000) := by
  have hn := hclock
  have hp := log_prime_23
  constructor <;> linarith only [hn.1, hn.2, hp.1, hp.2]

private theorem log_literal_68 :
    ((86727 / 25000) : ℝ) < Real.log (321071957 / 10000000) ∧ Real.log (321071957 / 10000000) <
        (34690803 / 10000000) := by
  refine rational_log_bounds (321071957 / 10000000) (321071957 / 320000000) _ _ 5 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

private theorem log_literal_69 :
    ((86727 / 25000) : ℝ) < Real.log (321071963 / 10000000) ∧ Real.log (321071963 / 10000000) <
        (34690803 / 10000000) := by
  refine rational_log_bounds (321071963 / 10000000) (321071963 / 320000000) _ _ 5 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

include hclock in
private theorem delete_23_log :
    ((86727 / 25000) : ℝ) < Real.log (L - Real.log 23) ∧ Real.log (L - Real.log 23) < (34690803
        / 10000000) := by
  exact log_interval_bounds (by norm_num) ((delete_23_clock hclock)).1 ((delete_23_clock hclock)).2
      log_literal_68.1 log_literal_69.2

private theorem log_literal_70 :
    ((12438893 / 10000000) : ℝ) < Real.log (86727 / 25000) ∧ Real.log (86727 / 25000) < (777431
        / 625000) := by
  refine rational_log_bounds (86727 / 25000) (86727 / 50000) _ _ 1 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

private theorem log_literal_71 :
    ((6219447 / 5000000) : ℝ) < Real.log (34690803 / 10000000) ∧ Real.log (34690803 / 10000000)
        < (12438897 / 10000000) := by
  refine rational_log_bounds (34690803 / 10000000) (34690803 / 20000000) _ _ 1 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

include hclock in
theorem delete_23_f :
    ((12438893 / 10000000) : ℝ) < Real.log (Real.log (L - Real.log 23)) ∧ Real.log (Real.log (L
        - Real.log 23)) < (12438897 / 10000000) := by
  exact log_interval_bounds (by norm_num) ((delete_23_log hclock)).1 ((delete_23_log hclock)).2 log_literal_70.1
      log_literal_71.2

include hclock in
private theorem insert_23_clock :
    ((191890921 / 5000000) : ℝ) < L + Real.log 23 ∧ L + Real.log 23 < (47972731 / 1250000) := by
  have hn := hclock
  have hp := log_prime_23
  constructor <;> linarith only [hn.1, hn.2, hp.1, hp.2]

private theorem log_literal_72 :
    ((3647489 / 1000000) : ℝ) < Real.log (191890921 / 5000000) ∧ Real.log (191890921 / 5000000)
        < (36474893 / 10000000) := by
  refine rational_log_bounds (191890921 / 5000000) (191890921 / 160000000) _ _ 5 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

private theorem log_literal_73 :
    ((3647489 / 1000000) : ℝ) < Real.log (47972731 / 1250000) ∧ Real.log (47972731 / 1250000) <
        (36474893 / 10000000) := by
  refine rational_log_bounds (47972731 / 1250000) (47972731 / 40000000) _ _ 5 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

include hclock in
private theorem insert_23_log :
    ((3647489 / 1000000) : ℝ) < Real.log (L + Real.log 23) ∧ Real.log (L + Real.log 23) <
        (36474893 / 10000000) := by
  exact log_interval_bounds (by norm_num) ((insert_23_clock hclock)).1 ((insert_23_clock hclock)).2
      log_literal_72.1 log_literal_73.2

private theorem log_literal_74 :
    ((3235097 / 2500000) : ℝ) < Real.log (3647489 / 1000000) ∧ Real.log (3647489 / 1000000) <
        (12940391 / 10000000) := by
  refine rational_log_bounds (3647489 / 1000000) (3647489 / 2000000) _ _ 1 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

private theorem log_literal_75 :
    ((12940389 / 10000000) : ℝ) < Real.log (36474893 / 10000000) ∧ Real.log (36474893 /
        10000000) < (1617549 / 1250000) := by
  refine rational_log_bounds (36474893 / 10000000) (36474893 / 20000000) _ _ 1 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

include hclock in
theorem insert_23_f :
    ((3235097 / 2500000) : ℝ) < Real.log (Real.log (L + Real.log 23)) ∧ Real.log (Real.log (L +
        Real.log 23)) < (1617549 / 1250000) := by
  exact log_interval_bounds (by norm_num) ((insert_23_log hclock)).1 ((insert_23_log hclock)).2 log_literal_74.1
      log_literal_75.2

theorem log_prime_29 :
    ((33672957 / 10000000) : ℝ) < Real.log 29 ∧ Real.log 29 < (52614 / 15625) := by
  refine rational_log_bounds 29 (29 / 16) _ _ 4 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

theorem gain_29_1_bounds :
    ((169507 / 5000000) : ℝ) < Real.log (30 / 29) ∧ Real.log (30 / 29) < (339017 / 10000000) := by
  have hs := log_expansion_remainder_bound (y := ((30 / 29) : ℝ)) (by norm_num) (by norm_num) 8
  norm_num [logRemainder, atanhParameter, atanhPartial, Finset.sum_range_succ] at hs
  constructor <;> linarith only [hs.1, hs.2]

theorem gain_29_1_identity :
    goldenLayerMarginal 29 1 * Real.log 29 = Real.log ((30 / 29) : ℝ) := by
  norm_num [goldenLayerMarginal]

theorem gain_29_2_bounds :
    ((5743 / 5000000) : ℝ) < Real.log (871 / 870) ∧ Real.log (871 / 870) < (11489 / 10000000) := by
  have hs := log_expansion_remainder_bound (y := ((871 / 870) : ℝ)) (by norm_num) (by norm_num) 8
  norm_num [logRemainder, atanhParameter, atanhPartial, Finset.sum_range_succ] at hs
  constructor <;> linarith only [hs.1, hs.2]

theorem gain_29_2_identity :
    goldenLayerMarginal 29 2 * Real.log 29 = Real.log ((871 / 870) : ℝ) := by
  norm_num [goldenLayerMarginal]

include hclock in
private theorem delete_29_clock :
    ((318753941 / 10000000) : ℝ) < L - Real.log 29 ∧ L - Real.log 29 < (318753947 / 10000000) := by
  have hn := hclock
  have hp := log_prime_29
  constructor <;> linarith only [hn.1, hn.2, hp.1, hp.2]

private theorem log_literal_76 :
    ((17309171 / 5000000) : ℝ) < Real.log (318753941 / 10000000) ∧ Real.log (318753941 /
        10000000) < (6923669 / 2000000) := by
  refine rational_log_bounds (318753941 / 10000000) (318753941 / 160000000) _ _ 4 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

private theorem log_literal_77 :
    ((17309171 / 5000000) : ℝ) < Real.log (318753947 / 10000000) ∧ Real.log (318753947 /
        10000000) < (6923669 / 2000000) := by
  refine rational_log_bounds (318753947 / 10000000) (318753947 / 160000000) _ _ 4 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

include hclock in
private theorem delete_29_log :
    ((17309171 / 5000000) : ℝ) < Real.log (L - Real.log 29) ∧ Real.log (L - Real.log 29) <
        (6923669 / 2000000) := by
  exact log_interval_bounds (by norm_num) ((delete_29_clock hclock)).1 ((delete_29_clock hclock)).2
      log_literal_76.1 log_literal_77.2

private theorem log_literal_78 :
    ((194031 / 156250) : ℝ) < Real.log (17309171 / 5000000) ∧ Real.log (17309171 / 5000000) <
        (12417987 / 10000000) := by
  refine rational_log_bounds (17309171 / 5000000) (17309171 / 10000000) _ _ 1 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

private theorem log_literal_79 :
    ((2483597 / 2000000) : ℝ) < Real.log (6923669 / 2000000) ∧ Real.log (6923669 / 2000000) <
        (3104497 / 2500000) := by
  refine rational_log_bounds (6923669 / 2000000) (6923669 / 4000000) _ _ 1 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

include hclock in
theorem delete_29_f :
    ((194031 / 156250) : ℝ) < Real.log (Real.log (L - Real.log 29)) ∧ Real.log (Real.log (L -
        Real.log 29)) < (3104497 / 2500000) := by
  exact log_interval_bounds (by norm_num) ((delete_29_log hclock)).1 ((delete_29_log hclock)).2 log_literal_78.1
      log_literal_79.2

include hclock in
private theorem insert_29_clock :
    ((193049929 / 5000000) : ℝ) < L + Real.log 29 ∧ L + Real.log 29 < (48262483 / 1250000) := by
  have hn := hclock
  have hp := log_prime_29
  constructor <;> linarith only [hn.1, hn.2, hp.1, hp.2]

private theorem log_literal_80 :
    ((9133777 / 2500000) : ℝ) < Real.log (193049929 / 5000000) ∧ Real.log (193049929 / 5000000)
        < (36535111 / 10000000) := by
  refine rational_log_bounds (193049929 / 5000000) (193049929 / 160000000) _ _ 5 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

private theorem log_literal_81 :
    ((9133777 / 2500000) : ℝ) < Real.log (48262483 / 1250000) ∧ Real.log (48262483 / 1250000) <
        (36535111 / 10000000) := by
  refine rational_log_bounds (48262483 / 1250000) (48262483 / 40000000) _ _ 5 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

include hclock in
private theorem insert_29_log :
    ((9133777 / 2500000) : ℝ) < Real.log (L + Real.log 29) ∧ Real.log (L + Real.log 29) <
        (36535111 / 10000000) := by
  exact log_interval_bounds (by norm_num) ((insert_29_clock hclock)).1 ((insert_29_clock hclock)).2
      log_literal_80.1 log_literal_81.2

private theorem log_literal_82 :
    ((3239221 / 2500000) : ℝ) < Real.log (9133777 / 2500000) ∧ Real.log (9133777 / 2500000) <
        (12956887 / 10000000) := by
  refine rational_log_bounds (9133777 / 2500000) (9133777 / 5000000) _ _ 1 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

private theorem log_literal_83 :
    ((2591377 / 2000000) : ℝ) < Real.log (36535111 / 10000000) ∧ Real.log (36535111 / 10000000)
        < (1619611 / 1250000) := by
  refine rational_log_bounds (36535111 / 10000000) (36535111 / 20000000) _ _ 1 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

include hclock in
theorem insert_29_f :
    ((3239221 / 2500000) : ℝ) < Real.log (Real.log (L + Real.log 29)) ∧ Real.log (Real.log (L +
        Real.log 29)) < (1619611 / 1250000) := by
  exact log_interval_bounds (by norm_num) ((insert_29_log hclock)).1 ((insert_29_log hclock)).2 log_literal_82.1
      log_literal_83.2

theorem log_prime_31 :
    ((34339871 / 10000000) : ℝ) < Real.log 31 ∧ Real.log 31 < (17169937 / 5000000) := by
  refine rational_log_bounds 31 (31 / 16) _ _ 4 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

theorem gain_31_1_bounds :
    ((63497 / 2000000) : ℝ) < Real.log (32 / 31) ∧ Real.log (32 / 31) < (19843 / 625000) := by
  have hs := log_expansion_remainder_bound (y := ((32 / 31) : ℝ)) (by norm_num) (by norm_num) 8
  norm_num [logRemainder, atanhParameter, atanhPartial, Finset.sum_range_succ] at hs
  constructor <;> linarith only [hs.1, hs.2]

theorem gain_31_1_identity :
    goldenLayerMarginal 31 1 * Real.log 31 = Real.log ((32 / 31) : ℝ) := by
  norm_num [goldenLayerMarginal]

theorem gain_31_2_bounds :
    ((5037 / 5000000) : ℝ) < Real.log (993 / 992) ∧ Real.log (993 / 992) < (10077 / 10000000) := by
  have hs := log_expansion_remainder_bound (y := ((993 / 992) : ℝ)) (by norm_num) (by norm_num) 8
  norm_num [logRemainder, atanhParameter, atanhPartial, Finset.sum_range_succ] at hs
  constructor <;> linarith only [hs.1, hs.2]

theorem gain_31_2_identity :
    goldenLayerMarginal 31 2 * Real.log 31 = Real.log ((993 / 992) : ℝ) := by
  norm_num [goldenLayerMarginal]

include hclock in
private theorem delete_31_clock :
    ((318087027 / 10000000) : ℝ) < L - Real.log 31 ∧ L - Real.log 31 < (318087033 / 10000000) := by
  have hn := hclock
  have hp := log_prime_31
  constructor <;> linarith only [hn.1, hn.2, hp.1, hp.2]

private theorem log_literal_84 :
    ((17298699 / 5000000) : ℝ) < Real.log (318087027 / 10000000) ∧ Real.log (318087027 /
        10000000) < (34597401 / 10000000) := by
  refine rational_log_bounds (318087027 / 10000000) (318087027 / 160000000) _ _ 4 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

private theorem log_literal_85 :
    ((17298699 / 5000000) : ℝ) < Real.log (318087033 / 10000000) ∧ Real.log (318087033 /
        10000000) < (34597401 / 10000000) := by
  refine rational_log_bounds (318087033 / 10000000) (318087033 / 160000000) _ _ 4 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

include hclock in
private theorem delete_31_log :
    ((17298699 / 5000000) : ℝ) < Real.log (L - Real.log 31) ∧ Real.log (L - Real.log 31) <
        (34597401 / 10000000) := by
  exact log_interval_bounds (by norm_num) ((delete_31_clock hclock)).1 ((delete_31_clock hclock)).2
      log_literal_84.1 log_literal_85.2

private theorem log_literal_86 :
    ((3102983 / 2500000) : ℝ) < Real.log (17298699 / 5000000) ∧ Real.log (17298699 / 5000000) <
        (2482387 / 2000000) := by
  refine rational_log_bounds (17298699 / 5000000) (17298699 / 10000000) _ _ 1 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

private theorem log_literal_87 :
    ((12411933 / 10000000) : ℝ) < Real.log (34597401 / 10000000) ∧ Real.log (34597401 /
        10000000) < (387873 / 312500) := by
  refine rational_log_bounds (34597401 / 10000000) (34597401 / 20000000) _ _ 1 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

include hclock in
theorem delete_31_f :
    ((3102983 / 2500000) : ℝ) < Real.log (Real.log (L - Real.log 31)) ∧ Real.log (Real.log (L -
        Real.log 31)) < (387873 / 312500) := by
  exact log_interval_bounds (by norm_num) ((delete_31_log hclock)).1 ((delete_31_log hclock)).2 log_literal_86.1
      log_literal_87.2

include hclock in
private theorem insert_31_clock :
    ((96691693 / 2500000) : ℝ) < L + Real.log 31 ∧ L + Real.log 31 < (193383389 / 5000000) := by
  have hn := hclock
  have hp := log_prime_31
  constructor <;> linarith only [hn.1, hn.2, hp.1, hp.2]

private theorem log_literal_88 :
    ((18276183 / 5000000) : ℝ) < Real.log (96691693 / 2500000) ∧ Real.log (96691693 / 2500000) <
        (36552369 / 10000000) := by
  refine rational_log_bounds (96691693 / 2500000) (96691693 / 80000000) _ _ 5 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

private theorem log_literal_89 :
    ((18276183 / 5000000) : ℝ) < Real.log (193383389 / 5000000) ∧ Real.log (193383389 / 5000000)
        < (36552369 / 10000000) := by
  refine rational_log_bounds (193383389 / 5000000) (193383389 / 160000000) _ _ 5 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

include hclock in
private theorem insert_31_log :
    ((18276183 / 5000000) : ℝ) < Real.log (L + Real.log 31) ∧ Real.log (L + Real.log 31) <
        (36552369 / 10000000) := by
  exact log_interval_bounds (by norm_num) ((insert_31_clock hclock)).1 ((insert_31_clock hclock)).2
      log_literal_88.1 log_literal_89.2

private theorem log_literal_90 :
    ((12961607 / 10000000) : ℝ) < Real.log (18276183 / 5000000) ∧ Real.log (18276183 / 5000000)
        < (1296161 / 1000000) := by
  refine rational_log_bounds (18276183 / 5000000) (18276183 / 10000000) _ _ 1 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

private theorem log_literal_91 :
    ((1620201 / 1250000) : ℝ) < Real.log (36552369 / 10000000) ∧ Real.log (36552369 / 10000000)
        < (12961611 / 10000000) := by
  refine rational_log_bounds (36552369 / 10000000) (36552369 / 20000000) _ _ 1 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

include hclock in
theorem insert_31_f :
    ((12961607 / 10000000) : ℝ) < Real.log (Real.log (L + Real.log 31)) ∧ Real.log (Real.log (L
        + Real.log 31)) < (12961611 / 10000000) := by
  exact log_interval_bounds (by norm_num) ((insert_31_log hclock)).1 ((insert_31_log hclock)).2 log_literal_90.1
      log_literal_91.2

theorem log_prime_37 :
    ((18054589 / 5000000) : ℝ) < Real.log 37 ∧ Real.log 37 < (36109181 / 10000000) := by
  refine rational_log_bounds 37 (37 / 32) _ _ 5 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

theorem gain_37_1_bounds :
    ((266681 / 10000000) : ℝ) < Real.log (38 / 37) ∧ Real.log (38 / 37) < (66671 / 2500000) := by
  have hs := log_expansion_remainder_bound (y := ((38 / 37) : ℝ)) (by norm_num) (by norm_num) 8
  norm_num [logRemainder, atanhParameter, atanhPartial, Finset.sum_range_succ] at hs
  constructor <;> linarith only [hs.1, hs.2]

theorem gain_37_1_identity :
    goldenLayerMarginal 37 1 * Real.log 37 = Real.log ((38 / 37) : ℝ) := by
  norm_num [goldenLayerMarginal]

theorem log_prime_34 :
    ((8815901 / 2500000) : ℝ) < Real.log 34 ∧ Real.log 34 < (35263607 / 10000000) := by
  refine rational_log_bounds 34 (17 / 16) _ _ 5 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

theorem gain_34_1_bounds :
    ((144937 / 5000000) : ℝ) < Real.log (35 / 34) ∧ Real.log (35 / 34) < (289877 / 10000000) := by
  have hs := log_expansion_remainder_bound (y := ((35 / 34) : ℝ)) (by norm_num) (by norm_num) 8
  norm_num [logRemainder, atanhParameter, atanhPartial, Finset.sum_range_succ] at hs
  constructor <;> linarith only [hs.1, hs.2]

theorem log_prime_35 :
    ((35553479 / 10000000) : ℝ) < Real.log 35 ∧ Real.log 35 < (17776741 / 5000000) := by
  refine rational_log_bounds 35 (35 / 32) _ _ 5 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

theorem gain_35_1_bounds :
    ((281707 / 10000000) : ℝ) < Real.log (36 / 35) ∧ Real.log (36 / 35) < (28171 / 1000000) := by
  have hs := log_expansion_remainder_bound (y := ((36 / 35) : ℝ)) (by norm_num) (by norm_num) 8
  norm_num [logRemainder, atanhParameter, atanhPartial, Finset.sum_range_succ] at hs
  constructor <;> linarith only [hs.1, hs.2]

theorem w_N_bounds_raw :
    ((18224697 / 10000000) : ℝ) < Real.log (70225920 / 11350339) ∧ Real.log (70225920 /
        11350339) < (182247 / 100000) := by
  refine rational_log_bounds (70225920 / 11350339) (17556480 / 11350339) _ _ 2 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

theorem w_M_bounds_raw :
    ((1198299 / 625000) : ℝ) < Real.log (3074209873920 / 451928782799) ∧ Real.log (3074209873920
        / 451928782799) < (19172787 / 10000000) := by
  refine rational_log_bounds (3074209873920 / 451928782799) (768552468480 / 451928782799) _ _ 2 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]


private theorem gap32_x :
    ((17328679 / 5000000) : ℝ) < Real.log 32 ∧ Real.log 32 < (34657361 / 10000000) := by
  refine rational_log_bounds 32 1 _ _ 5 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

theorem gap32_gain :
    ((61543 / 2000000) : ℝ) < Real.log (33 / 32) ∧ Real.log (33 / 32) < (153859 / 5000000) := by
  have hs := log_expansion_remainder_bound (y := ((33 / 32) : ℝ)) (by norm_num) (by norm_num) 8
  norm_num [logRemainder, atanhParameter, atanhPartial, Finset.sum_range_succ] at hs
  constructor <;> linarith only [hs.1, hs.2]

include hclock in
theorem gap32_clock :
    ((15888477 / 500000) : ℝ) < L - Real.log (32 : ℝ) ∧ L - Real.log (32 : ℝ) < (158884773 /
        5000000) := by
  have hn := hclock
  have hp := gap32_x
  constructor <;> linarith only [hn.1, hn.2, hp.1, hp.2]

private theorem extra_log_literal_0 :
    ((8646853 / 2500000) : ℝ) < Real.log (15888477 / 500000) ∧ Real.log (15888477 / 500000) <
        (6917483 / 2000000) := by
  refine rational_log_bounds (15888477 / 500000) (15888477 / 8000000) _ _ 4 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

private theorem extra_log_literal_1 :
    ((8646853 / 2500000) : ℝ) < Real.log (158884773 / 5000000) ∧ Real.log (158884773 / 5000000)
        < (6917483 / 2000000) := by
  refine rational_log_bounds (158884773 / 5000000) (158884773 / 80000000) _ _ 4 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

include hclock in
private theorem gap32_log :
    ((8646853 / 2500000) : ℝ) < Real.log (L - Real.log (32 : ℝ)) ∧ Real.log (L - Real.log (32 :
        ℝ)) < (6917483 / 2000000) := by
  exact log_interval_bounds (by norm_num) ((gap32_clock hclock)).1 ((gap32_clock hclock)).2 extra_log_literal_0.1
      extra_log_literal_1.2

private theorem extra_log_literal_2 :
    ((6204523 / 5000000) : ℝ) < Real.log (8646853 / 2500000) ∧ Real.log (8646853 / 2500000) <
        (12409049 / 10000000) := by
  refine rational_log_bounds (8646853 / 2500000) (8646853 / 5000000) _ _ 1 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

private theorem extra_log_literal_3 :
    ((6204523 / 5000000) : ℝ) < Real.log (6917483 / 2000000) ∧ Real.log (6917483 / 2000000) <
        (12409049 / 10000000) := by
  refine rational_log_bounds (6917483 / 2000000) (6917483 / 4000000) _ _ 1 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

include hclock in
theorem gap32_f :
    ((6204523 / 5000000) : ℝ) < Real.log (Real.log (L - Real.log (32 : ℝ))) ∧ Real.log (Real.log
        (L - Real.log (32 : ℝ))) < (12409049 / 10000000) := by
  exact log_interval_bounds (by norm_num) ((gap32_log hclock)).1 ((gap32_log hclock)).2 extra_log_literal_2.1
      extra_log_literal_3.2

private theorem gap369_x :
    ((18041057 / 5000000) : ℝ) < Real.log (369 / 10) ∧ Real.log (369 / 10) < (36082117 /
        10000000) := by
  refine rational_log_bounds (369 / 10) (369 / 320) _ _ 5 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

theorem gap369_gain :
    ((133697 / 5000000) : ℝ) < Real.log (379 / 369) ∧ Real.log (379 / 369) < (267397 / 10000000)
        := by
  have hs := log_expansion_remainder_bound (y := ((379 / 369) : ℝ)) (by norm_num) (by norm_num) 8
  norm_num [logRemainder, atanhParameter, atanhPartial, Finset.sum_range_succ] at hs
  constructor <;> linarith only [hs.1, hs.2]

include hclock in
private theorem gap369_clock :
    ((77701803 / 2000000) : ℝ) < L + Real.log ((369 / 10) : ℝ) ∧ L + Real.log ((369 / 10) : ℝ) <
        (388509021 / 10000000) := by
  have hn := hclock
  have hp := gap369_x
  constructor <;> linarith only [hn.1, hn.2, hp.1, hp.2]

private theorem extra_log_literal_4 :
    ((36597311 / 10000000) : ℝ) < Real.log (77701803 / 2000000) ∧ Real.log (77701803 / 2000000)
        < (18298657 / 5000000) := by
  refine rational_log_bounds (77701803 / 2000000) (77701803 / 64000000) _ _ 5 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

private theorem extra_log_literal_5 :
    ((36597311 / 10000000) : ℝ) < Real.log (388509021 / 10000000) ∧ Real.log (388509021 /
        10000000) < (18298657 / 5000000) := by
  refine rational_log_bounds (388509021 / 10000000) (388509021 / 320000000) _ _ 5 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

include hclock in
private theorem gap369_log :
    ((36597311 / 10000000) : ℝ) < Real.log (L + Real.log ((369 / 10) : ℝ)) ∧ Real.log (L +
        Real.log ((369 / 10) : ℝ)) < (18298657 / 5000000) := by
  exact log_interval_bounds (by norm_num) ((gap369_clock hclock)).1 ((gap369_clock hclock)).2
      extra_log_literal_4.1 extra_log_literal_5.2

private theorem extra_log_literal_6 :
    ((2594779 / 2000000) : ℝ) < Real.log (36597311 / 10000000) ∧ Real.log (36597311 / 10000000)
        < (6486949 / 5000000) := by
  refine rational_log_bounds (36597311 / 10000000) (36597311 / 20000000) _ _ 1 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

private theorem extra_log_literal_7 :
    ((1621737 / 1250000) : ℝ) < Real.log (18298657 / 5000000) ∧ Real.log (18298657 / 5000000) <
        (12973899 / 10000000) := by
  refine rational_log_bounds (18298657 / 5000000) (18298657 / 10000000) _ _ 1 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

include hclock in
theorem gap369_f :
    ((2594779 / 2000000) : ℝ) < Real.log (Real.log (L + Real.log ((369 / 10) : ℝ))) ∧ Real.log
        (Real.log (L + Real.log ((369 / 10) : ℝ))) < (12973899 / 10000000) := by
  exact log_interval_bounds (by norm_num) ((gap369_log hclock)).1 ((gap369_log hclock)).2 extra_log_literal_6.1
      extra_log_literal_7.2


/-- A uniform adjacent-layer reduction, independent of any chosen integer. -/
theorem layer_pair_of_clock_product {L : ℝ} (ht : (125 : ℝ) < L * Real.log L ∧
    L * Real.log L < 126) {p k : ℕ} {u v : ℝ}
    (hp : 0 < Real.log p)
    (hu : goldenLayerMarginal p k * Real.log p = u)
    (hv : goldenLayerMarginal p (k + 1) * Real.log p = v)
    (hi : Real.log p < 125 * u) (ho : 126 * v < Real.log p) (hv0 : 0 ≤ v) :
    price L < goldenLayerMarginal p k ∧ goldenLayerMarginal p (k + 1) < price L := by
  have hpos : 0 < L * Real.log L := by linarith only [ht.1]
  have hu0 : 0 < u := by linarith only [hi, hp]
  constructor
  · apply (mul_lt_mul_iff_left₀ hp).mp
    rw [hu]
    change 1 / (L * Real.log L) * Real.log p < _
    rw [one_div_mul_eq_div, div_lt_iff₀ hpos]
    nlinarith only [ht.1, hi, hu0]
  · apply (mul_lt_mul_iff_left₀ hp).mp
    rw [hv]
    change _ < 1 / (L * Real.log L) * Real.log p
    rw [one_div_mul_eq_div, lt_div_iff₀ hpos]
    nlinarith only [ht.2, ho, hv0]


end D5.S3.Arith.Robin.PriceRecord.ActualInventoryBounds
