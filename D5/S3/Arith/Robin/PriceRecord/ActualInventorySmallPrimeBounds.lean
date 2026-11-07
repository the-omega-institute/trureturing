/- GID: D5/S3/Arith/Robin/PriceRecord/ActualInventorySmallPrimeBounds
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/PriceRecord/ActualInventorySmallPrimeBounds
   mirror-E: none(waiver:uniform-real-clock-estimates)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Arith/Robin/PriceRecord/ActualInventoryCollectiveSeparation.actual_witness; premises=D5/S3/Arith/Robin/PriceRecord/ActualInventorySmallPrimeBounds.log_literal_0,D5/S3/Arith/Robin/PriceRecord/ActualInventorySmallPrimeBounds.log_literal_1
   digest: Uniform rational logarithmic estimates supply the actual inventory separation. -/

import D5.S3.Arith.Robin.PriceRecord.NonlinearPrimeExclusion
import D5.S3.Arith.GoldenResource.RobinRationalBasis
import D5.S3.Arith.GoldenResource5040PriceInterval


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

private theorem log_literal_0 :
    ((1781129 / 500000) : ℝ) < Real.log (352426901 / 10000000) ∧ Real.log (352426901 / 10000000)
        < (35622583 / 10000000) := by
  refine rational_log_bounds (352426901 / 10000000) (352426901 / 320000000) _ _ 5 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

private theorem log_literal_1 :
    ((1781129 / 500000) : ℝ) < Real.log (44053363 / 1250000) ∧ Real.log (44053363 / 1250000) <
        (35622583 / 10000000) := by
  refine rational_log_bounds (44053363 / 1250000) (44053363 / 40000000) _ _ 5 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

include hclock in
theorem log_clock_bounds :
    ((1781129 / 500000) : ℝ) < Real.log (L) ∧ Real.log (L) < (35622583 / 10000000) := by
  exact log_interval_bounds (by norm_num) (hclock).1 (hclock).2 log_literal_0.1
      log_literal_1.2

private theorem log_literal_2 :
    ((2540789 / 2000000) : ℝ) < Real.log (1781129 / 500000) ∧ Real.log (1781129 / 500000) <
        (3175987 / 2500000) := by
  refine rational_log_bounds (1781129 / 500000) (1781129 / 1000000) _ _ 1 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

private theorem log_literal_3 :
    ((2540789 / 2000000) : ℝ) < Real.log (35622583 / 10000000) ∧ Real.log (35622583 / 10000000)
        < (3175987 / 2500000) := by
  refine rational_log_bounds (35622583 / 10000000) (35622583 / 20000000) _ _ 1 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

include hclock in
theorem f_clock_bounds :
    ((2540789 / 2000000) : ℝ) < Real.log (Real.log L) ∧ Real.log (Real.log L) < (3175987 /
        2500000) := by
  exact log_interval_bounds (by norm_num) ((log_clock_bounds hclock)).1 ((log_clock_bounds hclock)).2
      log_literal_2.1 log_literal_3.2

theorem log_prime_2 :
    ((693147 / 1000000) : ℝ) < Real.log 2 ∧ Real.log 2 < (6931473 / 10000000) := by
  refine rational_log_bounds 2 1 _ _ 1 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

theorem gain_2_6_bounds :
    ((1581 / 200000) : ℝ) < Real.log (127 / 126) ∧ Real.log (127 / 126) < (79053 / 10000000) := by
  have hs := log_expansion_remainder_bound (y := ((127 / 126) : ℝ)) (by norm_num) (by norm_num) 8
  norm_num [logRemainder, atanhParameter, atanhPartial, Finset.sum_range_succ] at hs
  constructor <;> linarith only [hs.1, hs.2]

theorem gain_2_6_identity :
    goldenLayerMarginal 2 6 * Real.log 2 = Real.log ((127 / 126) : ℝ) := by
  norm_num [goldenLayerMarginal]

theorem gain_2_7_bounds :
    ((39291 / 10000000) : ℝ) < Real.log (255 / 254) ∧ Real.log (255 / 254) < (19647 / 5000000) := by
  have hs := log_expansion_remainder_bound (y := ((255 / 254) : ℝ)) (by norm_num) (by norm_num) 8
  norm_num [logRemainder, atanhParameter, atanhPartial, Finset.sum_range_succ] at hs
  constructor <;> linarith only [hs.1, hs.2]

theorem gain_2_7_identity :
    goldenLayerMarginal 2 7 * Real.log 2 = Real.log ((255 / 254) : ℝ) := by
  norm_num [goldenLayerMarginal]

include hclock in
private theorem delete_2_clock :
    ((86373857 / 2500000) : ℝ) < L - Real.log 2 ∧ L - Real.log 2 < (172747717 / 5000000) := by
  have hn := hclock
  have hp := log_prime_2
  constructor <;> linarith only [hn.1, hn.2, hp.1, hp.2]

private theorem log_literal_4 :
    ((17711971 / 5000000) : ℝ) < Real.log (86373857 / 2500000) ∧ Real.log (86373857 / 2500000) <
        (7084789 / 2000000) := by
  refine rational_log_bounds (86373857 / 2500000) (86373857 / 80000000) _ _ 5 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

private theorem log_literal_5 :
    ((17711971 / 5000000) : ℝ) < Real.log (172747717 / 5000000) ∧ Real.log (172747717 / 5000000)
        < (7084789 / 2000000) := by
  refine rational_log_bounds (172747717 / 5000000) (172747717 / 160000000) _ _ 5 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

include hclock in
private theorem delete_2_log :
    ((17711971 / 5000000) : ℝ) < Real.log (L - Real.log 2) ∧ Real.log (L - Real.log 2) <
        (7084789 / 2000000) := by
  exact log_interval_bounds (by norm_num) ((delete_2_clock hclock)).1 ((delete_2_clock hclock)).2 log_literal_4.1
      log_literal_5.2

private theorem log_literal_6 :
    ((12648027 / 10000000) : ℝ) < Real.log (17711971 / 5000000) ∧ Real.log (17711971 / 5000000)
        < (1264803 / 1000000) := by
  refine rational_log_bounds (17711971 / 5000000) (17711971 / 10000000) _ _ 1 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

private theorem log_literal_7 :
    ((3162007 / 2500000) : ℝ) < Real.log (7084789 / 2000000) ∧ Real.log (7084789 / 2000000) <
        (12648031 / 10000000) := by
  refine rational_log_bounds (7084789 / 2000000) (7084789 / 4000000) _ _ 1 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

include hclock in
theorem delete_2_f :
    ((12648027 / 10000000) : ℝ) < Real.log (Real.log (L - Real.log 2)) ∧ Real.log (Real.log (L -
        Real.log 2)) < (12648031 / 10000000) := by
  exact log_interval_bounds (by norm_num) ((delete_2_log hclock)).1 ((delete_2_log hclock)).2 log_literal_6.1
      log_literal_7.2

include hclock in
private theorem insert_2_clock :
    ((359358371 / 10000000) : ℝ) < L + Real.log 2 ∧ L + Real.log 2 < (359358377 / 10000000) := by
  have hn := hclock
  have hp := log_prime_2
  constructor <;> linarith only [hn.1, hn.2, hp.1, hp.2]

private theorem log_literal_8 :
    ((35817349 / 10000000) : ℝ) < Real.log (359358371 / 10000000) ∧ Real.log (359358371 /
        10000000) < (4477169 / 1250000) := by
  refine rational_log_bounds (359358371 / 10000000) (359358371 / 320000000) _ _ 5 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

private theorem log_literal_9 :
    ((35817349 / 10000000) : ℝ) < Real.log (359358377 / 10000000) ∧ Real.log (359358377 /
        10000000) < (4477169 / 1250000) := by
  refine rational_log_bounds (359358377 / 10000000) (359358377 / 320000000) _ _ 5 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

include hclock in
private theorem insert_2_log :
    ((35817349 / 10000000) : ℝ) < Real.log (L + Real.log 2) ∧ Real.log (L + Real.log 2) <
        (4477169 / 1250000) := by
  exact log_interval_bounds (by norm_num) ((insert_2_clock hclock)).1 ((insert_2_clock hclock)).2 log_literal_8.1
      log_literal_9.2

private theorem log_literal_10 :
    ((12758471 / 10000000) : ℝ) < Real.log (35817349 / 10000000) ∧ Real.log (35817349 /
        10000000) < (6379237 / 5000000) := by
  refine rational_log_bounds (35817349 / 10000000) (35817349 / 20000000) _ _ 1 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

private theorem log_literal_11 :
    ((1594809 / 1250000) : ℝ) < Real.log (4477169 / 1250000) ∧ Real.log (4477169 / 1250000) <
        (510339 / 400000) := by
  refine rational_log_bounds (4477169 / 1250000) (4477169 / 2500000) _ _ 1 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

include hclock in
theorem insert_2_f :
    ((12758471 / 10000000) : ℝ) < Real.log (Real.log (L + Real.log 2)) ∧ Real.log (Real.log (L +
        Real.log 2)) < (510339 / 400000) := by
  exact log_interval_bounds (by norm_num) ((insert_2_log hclock)).1 ((insert_2_log hclock)).2 log_literal_10.1
      log_literal_11.2

theorem log_prime_3 :
    ((10986121 / 10000000) : ℝ) < Real.log 3 ∧ Real.log 3 < (2746531 / 2500000) := by
  refine rational_log_bounds 3 (3 / 2) _ _ 1 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

theorem gain_3_3_bounds :
    ((253177 / 10000000) : ℝ) < Real.log (40 / 39) ∧ Real.log (40 / 39) < (12659 / 500000) := by
  have hs := log_expansion_remainder_bound (y := ((40 / 39) : ℝ)) (by norm_num) (by norm_num) 8
  norm_num [logRemainder, atanhParameter, atanhPartial, Finset.sum_range_succ] at hs
  constructor <;> linarith only [hs.1, hs.2]

theorem gain_3_3_identity :
    goldenLayerMarginal 3 3 * Real.log 3 = Real.log ((40 / 39) : ℝ) := by
  norm_num [goldenLayerMarginal]

theorem gain_3_4_bounds :
    ((82987 / 10000000) : ℝ) < Real.log (121 / 120) ∧ Real.log (121 / 120) < (8299 / 1000000) := by
  have hs := log_expansion_remainder_bound (y := ((121 / 120) : ℝ)) (by norm_num) (by norm_num) 8
  norm_num [logRemainder, atanhParameter, atanhPartial, Finset.sum_range_succ] at hs
  constructor <;> linarith only [hs.1, hs.2]

theorem gain_3_4_identity :
    goldenLayerMarginal 3 4 * Real.log 3 = Real.log ((121 / 120) : ℝ) := by
  norm_num [goldenLayerMarginal]

include hclock in
private theorem delete_3_clock :
    ((341440777 / 10000000) : ℝ) < L - Real.log 3 ∧ L - Real.log 3 < (341440783 / 10000000) := by
  have hn := hclock
  have hp := log_prime_3
  constructor <;> linarith only [hn.1, hn.2, hp.1, hp.2]

private theorem log_literal_12 :
    ((3530589 / 1000000) : ℝ) < Real.log (341440777 / 10000000) ∧ Real.log (341440777 /
        10000000) < (35305893 / 10000000) := by
  refine rational_log_bounds (341440777 / 10000000) (341440777 / 320000000) _ _ 5 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

private theorem log_literal_13 :
    ((3530589 / 1000000) : ℝ) < Real.log (341440783 / 10000000) ∧ Real.log (341440783 /
        10000000) < (35305893 / 10000000) := by
  refine rational_log_bounds (341440783 / 10000000) (341440783 / 320000000) _ _ 5 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

include hclock in
private theorem delete_3_log :
    ((3530589 / 1000000) : ℝ) < Real.log (L - Real.log 3) ∧ Real.log (L - Real.log 3) <
        (35305893 / 10000000) := by
  exact log_interval_bounds (by norm_num) ((delete_3_clock hclock)).1 ((delete_3_clock hclock)).2 log_literal_12.1
      log_literal_13.2

private theorem log_literal_14 :
    ((6307323 / 5000000) : ℝ) < Real.log (3530589 / 1000000) ∧ Real.log (3530589 / 1000000) <
        (12614649 / 10000000) := by
  refine rational_log_bounds (3530589 / 1000000) (3530589 / 2000000) _ _ 1 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

private theorem log_literal_15 :
    ((6307323 / 5000000) : ℝ) < Real.log (35305893 / 10000000) ∧ Real.log (35305893 / 10000000)
        < (12614649 / 10000000) := by
  refine rational_log_bounds (35305893 / 10000000) (35305893 / 20000000) _ _ 1 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

include hclock in
theorem delete_3_f :
    ((6307323 / 5000000) : ℝ) < Real.log (Real.log (L - Real.log 3)) ∧ Real.log (Real.log (L -
        Real.log 3)) < (12614649 / 10000000) := by
  exact log_interval_bounds (by norm_num) ((delete_3_log hclock)).1 ((delete_3_log hclock)).2 log_literal_14.1
      log_literal_15.2

include hclock in
private theorem insert_3_clock :
    ((181706511 / 5000000) : ℝ) < L + Real.log 3 ∧ L + Real.log 3 < (90853257 / 2500000) := by
  have hn := hclock
  have hp := log_prime_3
  constructor <;> linarith only [hn.1, hn.2, hp.1, hp.2]

private theorem log_literal_16 :
    ((35929547 / 10000000) : ℝ) < Real.log (181706511 / 5000000) ∧ Real.log (181706511 /
        5000000) < (718591 / 200000) := by
  refine rational_log_bounds (181706511 / 5000000) (181706511 / 160000000) _ _ 5 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

private theorem log_literal_17 :
    ((8982387 / 2500000) : ℝ) < Real.log (90853257 / 2500000) ∧ Real.log (90853257 / 2500000) <
        (35929551 / 10000000) := by
  refine rational_log_bounds (90853257 / 2500000) (90853257 / 80000000) _ _ 5 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

include hclock in
private theorem insert_3_log :
    ((35929547 / 10000000) : ℝ) < Real.log (L + Real.log 3) ∧ Real.log (L + Real.log 3) <
        (35929551 / 10000000) := by
  exact log_interval_bounds (by norm_num) ((insert_3_clock hclock)).1 ((insert_3_clock hclock)).2 log_literal_16.1
      log_literal_17.2

private theorem log_literal_18 :
    ((3197437 / 2500000) : ℝ) < Real.log (35929547 / 10000000) ∧ Real.log (35929547 / 10000000)
        < (12789751 / 10000000) := by
  refine rational_log_bounds (35929547 / 10000000) (35929547 / 20000000) _ _ 1 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

private theorem log_literal_19 :
    ((12789749 / 10000000) : ℝ) < Real.log (35929551 / 10000000) ∧ Real.log (35929551 /
        10000000) < (1598719 / 1250000) := by
  refine rational_log_bounds (35929551 / 10000000) (35929551 / 20000000) _ _ 1 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

include hclock in
theorem insert_3_f :
    ((3197437 / 2500000) : ℝ) < Real.log (Real.log (L + Real.log 3)) ∧ Real.log (Real.log (L +
        Real.log 3)) < (1598719 / 1250000) := by
  exact log_interval_bounds (by norm_num) ((insert_3_log hclock)).1 ((insert_3_log hclock)).2 log_literal_18.1
      log_literal_19.2

theorem log_prime_5 :
    ((8047189 / 5000000) : ℝ) < Real.log 5 ∧ Real.log 5 < (16094381 / 10000000) := by
  refine rational_log_bounds 5 (5 / 4) _ _ 2 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

theorem gain_5_2_bounds :
    ((327897 / 10000000) : ℝ) < Real.log (31 / 30) ∧ Real.log (31 / 30) < (3279 / 100000) := by
  have hs := log_expansion_remainder_bound (y := ((31 / 30) : ℝ)) (by norm_num) (by norm_num) 8
  norm_num [logRemainder, atanhParameter, atanhPartial, Finset.sum_range_succ] at hs
  constructor <;> linarith only [hs.1, hs.2]

theorem gain_5_2_identity :
    goldenLayerMarginal 5 2 * Real.log 5 = Real.log ((31 / 30) : ℝ) := by
  norm_num [goldenLayerMarginal]

theorem gain_5_3_bounds :
    ((64307 / 10000000) : ℝ) < Real.log (156 / 155) ∧ Real.log (156 / 155) < (6431 / 1000000) := by
  have hs := log_expansion_remainder_bound (y := ((156 / 155) : ℝ)) (by norm_num) (by norm_num) 8
  norm_num [logRemainder, atanhParameter, atanhPartial, Finset.sum_range_succ] at hs
  constructor <;> linarith only [hs.1, hs.2]

theorem gain_5_3_identity :
    goldenLayerMarginal 5 3 * Real.log 5 = Real.log ((156 / 155) : ℝ) := by
  norm_num [goldenLayerMarginal]

include hclock in
private theorem delete_5_clock :
    ((8408313 / 250000) : ℝ) < L - Real.log 5 ∧ L - Real.log 5 < (168166263 / 5000000) := by
  have hn := hclock
  have hp := log_prime_5
  constructor <;> linarith only [hn.1, hn.2, hp.1, hp.2]

private theorem log_literal_20 :
    ((35155151 / 10000000) : ℝ) < Real.log (8408313 / 250000) ∧ Real.log (8408313 / 250000) <
        (17577577 / 5000000) := by
  refine rational_log_bounds (8408313 / 250000) (8408313 / 8000000) _ _ 5 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

private theorem log_literal_21 :
    ((35155151 / 10000000) : ℝ) < Real.log (168166263 / 5000000) ∧ Real.log (168166263 /
        5000000) < (17577577 / 5000000) := by
  refine rational_log_bounds (168166263 / 5000000) (168166263 / 160000000) _ _ 5 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

include hclock in
private theorem delete_5_log :
    ((35155151 / 10000000) : ℝ) < Real.log (L - Real.log 5) ∧ Real.log (L - Real.log 5) <
        (17577577 / 5000000) := by
  exact log_interval_bounds (by norm_num) ((delete_5_clock hclock)).1 ((delete_5_clock hclock)).2 log_literal_20.1
      log_literal_21.2

private theorem log_literal_22 :
    ((12571859 / 10000000) : ℝ) < Real.log (35155151 / 10000000) ∧ Real.log (35155151 /
        10000000) < (6285931 / 5000000) := by
  refine rational_log_bounds (35155151 / 10000000) (35155151 / 20000000) _ _ 1 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

private theorem log_literal_23 :
    ((628593 / 500000) : ℝ) < Real.log (17577577 / 5000000) ∧ Real.log (17577577 / 5000000) <
        (12571863 / 10000000) := by
  refine rational_log_bounds (17577577 / 5000000) (17577577 / 10000000) _ _ 1 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

include hclock in
theorem delete_5_f :
    ((12571859 / 10000000) : ℝ) < Real.log (Real.log (L - Real.log 5)) ∧ Real.log (Real.log (L -
        Real.log 5)) < (12571863 / 10000000) := by
  exact log_interval_bounds (by norm_num) ((delete_5_log hclock)).1 ((delete_5_log hclock)).2 log_literal_22.1
      log_literal_23.2

include hclock in
private theorem insert_5_clock :
    ((368521279 / 10000000) : ℝ) < L + Real.log 5 ∧ L + Real.log 5 < (73704257 / 2000000) := by
  have hn := hclock
  have hp := log_prime_5
  constructor <;> linarith only [hn.1, hn.2, hp.1, hp.2]

private theorem log_literal_24 :
    ((9017283 / 2500000) : ℝ) < Real.log (368521279 / 10000000) ∧ Real.log (368521279 /
        10000000) < (7213827 / 2000000) := by
  refine rational_log_bounds (368521279 / 10000000) (368521279 / 320000000) _ _ 5 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

private theorem log_literal_25 :
    ((9017283 / 2500000) : ℝ) < Real.log (73704257 / 2000000) ∧ Real.log (73704257 / 2000000) <
        (7213827 / 2000000) := by
  refine rational_log_bounds (73704257 / 2000000) (73704257 / 64000000) _ _ 5 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

include hclock in
private theorem insert_5_log :
    ((9017283 / 2500000) : ℝ) < Real.log (L + Real.log 5) ∧ Real.log (L + Real.log 5) < (7213827
        / 2000000) := by
  exact log_interval_bounds (by norm_num) ((insert_5_clock hclock)).1 ((insert_5_clock hclock)).2 log_literal_24.1
      log_literal_25.2

private theorem log_literal_26 :
    ((6414261 / 5000000) : ℝ) < Real.log (9017283 / 2500000) ∧ Real.log (9017283 / 2500000) <
        (513141 / 400000) := by
  refine rational_log_bounds (9017283 / 2500000) (9017283 / 5000000) _ _ 1 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

private theorem log_literal_27 :
    ((12828523 / 10000000) : ℝ) < Real.log (7213827 / 2000000) ∧ Real.log (7213827 / 2000000) <
        (6414263 / 5000000) := by
  refine rational_log_bounds (7213827 / 2000000) (7213827 / 4000000) _ _ 1 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

include hclock in
theorem insert_5_f :
    ((6414261 / 5000000) : ℝ) < Real.log (Real.log (L + Real.log 5)) ∧ Real.log (Real.log (L +
        Real.log 5)) < (6414263 / 5000000) := by
  exact log_interval_bounds (by norm_num) ((insert_5_log hclock)).1 ((insert_5_log hclock)).2 log_literal_26.1
      log_literal_27.2

theorem log_prime_7 :
    ((194591 / 100000) : ℝ) < Real.log 7 ∧ Real.log 7 < (19459103 / 10000000) := by
  refine rational_log_bounds 7 (7 / 4) _ _ 2 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

theorem gain_7_2_bounds :
    ((88497 / 5000000) : ℝ) < Real.log (57 / 56) ∧ Real.log (57 / 56) < (176997 / 10000000) := by
  have hs := log_expansion_remainder_bound (y := ((57 / 56) : ℝ)) (by norm_num) (by norm_num) 8
  norm_num [logRemainder, atanhParameter, atanhPartial, Finset.sum_range_succ] at hs
  constructor <;> linarith only [hs.1, hs.2]

theorem gain_7_2_identity :
    goldenLayerMarginal 7 2 * Real.log 7 = Real.log ((57 / 56) : ℝ) := by
  norm_num [goldenLayerMarginal]

theorem gain_7_3_bounds :
    ((2503 / 1000000) : ℝ) < Real.log (400 / 399) ∧ Real.log (400 / 399) < (25033 / 10000000) := by
  have hs := log_expansion_remainder_bound (y := ((400 / 399) : ℝ)) (by norm_num) (by norm_num) 8
  norm_num [logRemainder, atanhParameter, atanhPartial, Finset.sum_range_succ] at hs
  constructor <;> linarith only [hs.1, hs.2]

theorem gain_7_3_identity :
    goldenLayerMarginal 7 3 * Real.log 7 = Real.log ((400 / 399) : ℝ) := by
  norm_num [goldenLayerMarginal]

include hclock in
private theorem delete_7_clock :
    ((166483899 / 5000000) : ℝ) < L - Real.log 7 ∧ L - Real.log 7 < (83241951 / 2500000) := by
  have hn := hclock
  have hp := log_prime_7
  constructor <;> linarith only [hn.1, hn.2, hp.1, hp.2]

private theorem log_literal_28 :
    ((7010921 / 2000000) : ℝ) < Real.log (166483899 / 5000000) ∧ Real.log (166483899 / 5000000)
        < (2190913 / 625000) := by
  refine rational_log_bounds (166483899 / 5000000) (166483899 / 160000000) _ _ 5 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

private theorem log_literal_29 :
    ((17527303 / 5000000) : ℝ) < Real.log (83241951 / 2500000) ∧ Real.log (83241951 / 2500000) <
        (35054609 / 10000000) := by
  refine rational_log_bounds (83241951 / 2500000) (83241951 / 80000000) _ _ 5 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

include hclock in
private theorem delete_7_log :
    ((7010921 / 2000000) : ℝ) < Real.log (L - Real.log 7) ∧ Real.log (L - Real.log 7) <
        (35054609 / 10000000) := by
  exact log_interval_bounds (by norm_num) ((delete_7_clock hclock)).1 ((delete_7_clock hclock)).2 log_literal_28.1
      log_literal_29.2

private theorem log_literal_30 :
    ((12543217 / 10000000) : ℝ) < Real.log (7010921 / 2000000) ∧ Real.log (7010921 / 2000000) <
        (627161 / 500000) := by
  refine rational_log_bounds (7010921 / 2000000) (7010921 / 4000000) _ _ 1 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

private theorem log_literal_31 :
    ((12543219 / 10000000) : ℝ) < Real.log (35054609 / 10000000) ∧ Real.log (35054609 /
        10000000) < (6271611 / 5000000) := by
  refine rational_log_bounds (35054609 / 10000000) (35054609 / 20000000) _ _ 1 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

include hclock in
theorem delete_7_f :
    ((12543217 / 10000000) : ℝ) < Real.log (Real.log (L - Real.log 7)) ∧ Real.log (Real.log (L -
        Real.log 7)) < (6271611 / 5000000) := by
  exact log_interval_bounds (by norm_num) ((delete_7_log hclock)).1 ((delete_7_log hclock)).2 log_literal_30.1
      log_literal_31.2

include hclock in
private theorem insert_7_clock :
    ((371886001 / 10000000) : ℝ) < L + Real.log 7 ∧ L + Real.log 7 < (371886007 / 10000000) := by
  have hn := hclock
  have hp := log_prime_7
  constructor <;> linarith only [hn.1, hn.2, hp.1, hp.2]

private theorem log_literal_32 :
    ((36160021 / 10000000) : ℝ) < Real.log (371886001 / 10000000) ∧ Real.log (371886001 /
        10000000) < (4520003 / 1250000) := by
  refine rational_log_bounds (371886001 / 10000000) (371886001 / 320000000) _ _ 5 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

private theorem log_literal_33 :
    ((36160021 / 10000000) : ℝ) < Real.log (371886007 / 10000000) ∧ Real.log (371886007 /
        10000000) < (4520003 / 1250000) := by
  refine rational_log_bounds (371886007 / 10000000) (371886007 / 320000000) _ _ 5 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

include hclock in
private theorem insert_7_log :
    ((36160021 / 10000000) : ℝ) < Real.log (L + Real.log 7) ∧ Real.log (L + Real.log 7) <
        (4520003 / 1250000) := by
  exact log_interval_bounds (by norm_num) ((insert_7_clock hclock)).1 ((insert_7_clock hclock)).2 log_literal_32.1
      log_literal_33.2

private theorem log_literal_34 :
    ((12853689 / 10000000) : ℝ) < Real.log (36160021 / 10000000) ∧ Real.log (36160021 /
        10000000) < (3213423 / 2500000) := by
  refine rational_log_bounds (36160021 / 10000000) (36160021 / 20000000) _ _ 1 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

private theorem log_literal_35 :
    ((1285369 / 1000000) : ℝ) < Real.log (4520003 / 1250000) ∧ Real.log (4520003 / 1250000) <
        (12853693 / 10000000) := by
  refine rational_log_bounds (4520003 / 1250000) (4520003 / 2500000) _ _ 1 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

include hclock in
theorem insert_7_f :
    ((12853689 / 10000000) : ℝ) < Real.log (Real.log (L + Real.log 7)) ∧ Real.log (Real.log (L +
        Real.log 7)) < (12853693 / 10000000) := by
  exact log_interval_bounds (by norm_num) ((insert_7_log hclock)).1 ((insert_7_log hclock)).2 log_literal_34.1
      log_literal_35.2

theorem log_prime_11 :
    ((23978951 / 10000000) : ℝ) < Real.log 11 ∧ Real.log 11 < (11989477 / 5000000) := by
  refine rational_log_bounds 11 (11 / 8) _ _ 3 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

theorem gain_11_1_bounds :
    ((27191 / 312500) : ℝ) < Real.log (12 / 11) ∧ Real.log (12 / 11) < (174023 / 2000000) := by
  have hs := log_expansion_remainder_bound (y := ((12 / 11) : ℝ)) (by norm_num) (by norm_num) 8
  norm_num [logRemainder, atanhParameter, atanhPartial, Finset.sum_range_succ] at hs
  constructor <;> linarith only [hs.1, hs.2]

theorem gain_11_1_identity :
    goldenLayerMarginal 11 1 * Real.log 11 = Real.log ((12 / 11) : ℝ) := by
  norm_num [goldenLayerMarginal]

theorem gain_11_2_bounds :
    ((75471 / 10000000) : ℝ) < Real.log (133 / 132) ∧ Real.log (133 / 132) < (37737 / 5000000) := by
  have hs := log_expansion_remainder_bound (y := ((133 / 132) : ℝ)) (by norm_num) (by norm_num) 8
  norm_num [logRemainder, atanhParameter, atanhPartial, Finset.sum_range_succ] at hs
  constructor <;> linarith only [hs.1, hs.2]

theorem gain_11_2_identity :
    goldenLayerMarginal 11 2 * Real.log 11 = Real.log ((133 / 132) : ℝ) := by
  norm_num [goldenLayerMarginal]

include hclock in
private theorem delete_11_clock :
    ((328447947 / 10000000) : ℝ) < L - Real.log 11 ∧ L - Real.log 11 < (328447953 / 10000000) := by
  have hn := hclock
  have hp := log_prime_11
  constructor <;> linarith only [hn.1, hn.2, hp.1, hp.2]

private theorem log_literal_36 :
    ((34917931 / 10000000) : ℝ) < Real.log (328447947 / 10000000) ∧ Real.log (328447947 /
        10000000) < (17458967 / 5000000) := by
  refine rational_log_bounds (328447947 / 10000000) (328447947 / 320000000) _ _ 5 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

private theorem log_literal_37 :
    ((34917931 / 10000000) : ℝ) < Real.log (328447953 / 10000000) ∧ Real.log (328447953 /
        10000000) < (17458967 / 5000000) := by
  refine rational_log_bounds (328447953 / 10000000) (328447953 / 320000000) _ _ 5 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

include hclock in
private theorem delete_11_log :
    ((34917931 / 10000000) : ℝ) < Real.log (L - Real.log 11) ∧ Real.log (L - Real.log 11) <
        (17458967 / 5000000) := by
  exact log_interval_bounds (by norm_num) ((delete_11_clock hclock)).1 ((delete_11_clock hclock)).2
      log_literal_36.1 log_literal_37.2

private theorem log_literal_38 :
    ((1563019 / 1250000) : ℝ) < Real.log (34917931 / 10000000) ∧ Real.log (34917931 / 10000000)
        < (2500831 / 2000000) := by
  refine rational_log_bounds (34917931 / 10000000) (34917931 / 20000000) _ _ 1 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

private theorem log_literal_39 :
    ((12504153 / 10000000) : ℝ) < Real.log (17458967 / 5000000) ∧ Real.log (17458967 / 5000000)
        < (3126039 / 2500000) := by
  refine rational_log_bounds (17458967 / 5000000) (17458967 / 10000000) _ _ 1 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

include hclock in
theorem delete_11_f :
    ((1563019 / 1250000) : ℝ) < Real.log (Real.log (L - Real.log 11)) ∧ Real.log (Real.log (L -
        Real.log 11)) < (3126039 / 2500000) := by
  exact log_interval_bounds (by norm_num) ((delete_11_log hclock)).1 ((delete_11_log hclock)).2 log_literal_38.1
      log_literal_39.2

include hclock in
private theorem insert_11_clock :
    ((94101463 / 2500000) : ℝ) < L + Real.log 11 ∧ L + Real.log 11 < (188202929 / 5000000) := by
  have hn := hclock
  have hp := log_prime_11
  constructor <;> linarith only [hn.1, hn.2, hp.1, hp.2]

private theorem log_literal_40 :
    ((36280827 / 10000000) : ℝ) < Real.log (94101463 / 2500000) ∧ Real.log (94101463 / 2500000)
        < (3628083 / 1000000) := by
  refine rational_log_bounds (94101463 / 2500000) (94101463 / 80000000) _ _ 5 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

private theorem log_literal_41 :
    ((36280827 / 10000000) : ℝ) < Real.log (188202929 / 5000000) ∧ Real.log (188202929 /
        5000000) < (3628083 / 1000000) := by
  refine rational_log_bounds (188202929 / 5000000) (188202929 / 160000000) _ _ 5 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

include hclock in
private theorem insert_11_log :
    ((36280827 / 10000000) : ℝ) < Real.log (L + Real.log 11) ∧ Real.log (L + Real.log 11) <
        (3628083 / 1000000) := by
  exact log_interval_bounds (by norm_num) ((insert_11_clock hclock)).1 ((insert_11_clock hclock)).2
      log_literal_40.1 log_literal_41.2

private theorem log_literal_42 :
    ((6443521 / 5000000) : ℝ) < Real.log (36280827 / 10000000) ∧ Real.log (36280827 / 10000000)
        < (2577409 / 2000000) := by
  refine rational_log_bounds (36280827 / 10000000) (36280827 / 20000000) _ _ 1 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

private theorem log_literal_43 :
    ((12887043 / 10000000) : ℝ) < Real.log (3628083 / 1000000) ∧ Real.log (3628083 / 1000000) <
        (6443523 / 5000000) := by
  refine rational_log_bounds (3628083 / 1000000) (3628083 / 2000000) _ _ 1 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

include hclock in
theorem insert_11_f :
    ((6443521 / 5000000) : ℝ) < Real.log (Real.log (L + Real.log 11)) ∧ Real.log (Real.log (L +
        Real.log 11)) < (6443523 / 5000000) := by
  exact log_interval_bounds (by norm_num) ((insert_11_log hclock)).1 ((insert_11_log hclock)).2 log_literal_42.1
      log_literal_43.2

theorem log_prime_13 :
    ((6412373 / 2500000) : ℝ) < Real.log 13 ∧ Real.log 13 < (5129899 / 2000000) := by
  refine rational_log_bounds 13 (13 / 8) _ _ 3 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

theorem gain_13_1_bounds :
    ((370539 / 5000000) : ℝ) < Real.log (14 / 13) ∧ Real.log (14 / 13) < (741081 / 10000000) := by
  have hs := log_expansion_remainder_bound (y := ((14 / 13) : ℝ)) (by norm_num) (by norm_num) 8
  norm_num [logRemainder, atanhParameter, atanhPartial, Finset.sum_range_succ] at hs
  constructor <;> linarith only [hs.1, hs.2]

theorem gain_13_1_identity :
    goldenLayerMarginal 13 1 * Real.log 13 = Real.log ((14 / 13) : ℝ) := by
  norm_num [goldenLayerMarginal]

theorem gain_13_2_bounds :
    ((54793 / 10000000) : ℝ) < Real.log (183 / 182) ∧ Real.log (183 / 182) < (13699 / 2500000) := by
  have hs := log_expansion_remainder_bound (y := ((183 / 182) : ℝ)) (by norm_num) (by norm_num) 8
  norm_num [logRemainder, atanhParameter, atanhPartial, Finset.sum_range_succ] at hs
  constructor <;> linarith only [hs.1, hs.2]

theorem gain_13_2_identity :
    goldenLayerMarginal 13 2 * Real.log 13 = Real.log ((183 / 182) : ℝ) := by
  norm_num [goldenLayerMarginal]

include hclock in
private theorem delete_13_clock :
    ((163388703 / 5000000) : ℝ) < L - Real.log 13 ∧ L - Real.log 13 < (81694353 / 2500000) := by
  have hn := hclock
  have hp := log_prime_13
  constructor <;> linarith only [hn.1, hn.2, hp.1, hp.2]

private theorem log_literal_44 :
    ((1743347 / 500000) : ℝ) < Real.log (163388703 / 5000000) ∧ Real.log (163388703 / 5000000) <
        (34866943 / 10000000) := by
  refine rational_log_bounds (163388703 / 5000000) (163388703 / 160000000) _ _ 5 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

private theorem log_literal_45 :
    ((1743347 / 500000) : ℝ) < Real.log (81694353 / 2500000) ∧ Real.log (81694353 / 2500000) <
        (34866943 / 10000000) := by
  refine rational_log_bounds (81694353 / 2500000) (81694353 / 80000000) _ _ 5 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

include hclock in
private theorem delete_13_log :
    ((1743347 / 500000) : ℝ) < Real.log (L - Real.log 13) ∧ Real.log (L - Real.log 13) <
        (34866943 / 10000000) := by
  exact log_interval_bounds (by norm_num) ((delete_13_clock hclock)).1 ((delete_13_clock hclock)).2
      log_literal_44.1 log_literal_45.2

private theorem log_literal_46 :
    ((12489539 / 10000000) : ℝ) < Real.log (1743347 / 500000) ∧ Real.log (1743347 / 500000) <
        (6244771 / 5000000) := by
  refine rational_log_bounds (1743347 / 500000) (1743347 / 1000000) _ _ 1 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

private theorem log_literal_47 :
    ((12489539 / 10000000) : ℝ) < Real.log (34866943 / 10000000) ∧ Real.log (34866943 /
        10000000) < (6244771 / 5000000) := by
  refine rational_log_bounds (34866943 / 10000000) (34866943 / 20000000) _ _ 1 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

include hclock in
theorem delete_13_f :
    ((12489539 / 10000000) : ℝ) < Real.log (Real.log (L - Real.log 13)) ∧ Real.log (Real.log (L
        - Real.log 13)) < (6244771 / 5000000) := by
  exact log_interval_bounds (by norm_num) ((delete_13_log hclock)).1 ((delete_13_log hclock)).2 log_literal_46.1
      log_literal_47.2

include hclock in
private theorem insert_13_clock :
    ((378076393 / 10000000) : ℝ) < L + Real.log 13 ∧ L + Real.log 13 < (378076399 / 10000000) := by
  have hn := hclock
  have hp := log_prime_13
  constructor <;> linarith only [hn.1, hn.2, hp.1, hp.2]

private theorem log_literal_48 :
    ((3632511 / 1000000) : ℝ) < Real.log (378076393 / 10000000) ∧ Real.log (378076393 /
        10000000) < (36325113 / 10000000) := by
  refine rational_log_bounds (378076393 / 10000000) (378076393 / 320000000) _ _ 5 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

private theorem log_literal_49 :
    ((3632511 / 1000000) : ℝ) < Real.log (378076399 / 10000000) ∧ Real.log (378076399 /
        10000000) < (36325113 / 10000000) := by
  refine rational_log_bounds (378076399 / 10000000) (378076399 / 320000000) _ _ 5 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

include hclock in
private theorem insert_13_log :
    ((3632511 / 1000000) : ℝ) < Real.log (L + Real.log 13) ∧ Real.log (L + Real.log 13) <
        (36325113 / 10000000) := by
  exact log_interval_bounds (by norm_num) ((insert_13_clock hclock)).1 ((insert_13_clock hclock)).2
      log_literal_48.1 log_literal_49.2

private theorem log_literal_50 :
    ((322481 / 250000) : ℝ) < Real.log (3632511 / 1000000) ∧ Real.log (3632511 / 1000000) <
        (12899243 / 10000000) := by
  refine rational_log_bounds (3632511 / 1000000) (3632511 / 2000000) _ _ 1 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

private theorem log_literal_51 :
    ((12899241 / 10000000) : ℝ) < Real.log (36325113 / 10000000) ∧ Real.log (36325113 /
        10000000) < (3224811 / 2500000) := by
  refine rational_log_bounds (36325113 / 10000000) (36325113 / 20000000) _ _ 1 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

include hclock in
theorem insert_13_f :
    ((322481 / 250000) : ℝ) < Real.log (Real.log (L + Real.log 13)) ∧ Real.log (Real.log (L +
        Real.log 13)) < (3224811 / 2500000) := by
  exact log_interval_bounds (by norm_num) ((insert_13_log hclock)).1 ((insert_13_log hclock)).2 log_literal_50.1
      log_literal_51.2


end D5.S3.Arith.Robin.PriceRecord.ActualInventoryBounds
