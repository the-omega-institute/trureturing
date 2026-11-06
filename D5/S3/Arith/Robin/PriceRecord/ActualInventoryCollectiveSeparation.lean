/- GID: D5/S3/Arith/Robin/PriceRecord/ActualInventoryCollectiveSeparation
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/PriceRecord/ActualInventoryCollectiveSeparation
   mirror-E: none(waiver:exact-original-margin-separation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Arith/Robin/PriceRecord/ActualInventoryCollectiveSeparation.inventory_singletons_imply_collective; result=D5/S3/Arith/Robin/PriceRecord/ActualInventoryCollectiveSeparation.result; claim=D5/S3/Arith/Robin/PriceRecord/ActualInventoryCollectiveSeparation.inventory_singletons_imply_collective
   digest: An actual own-clock strict inventory defeats the collective Robin implication. -/

import D5.S3.Arith.Robin.PriceRecord.NonlinearPrimeExclusion
import D5.S3.Arith.GoldenResource.RobinRationalBasis
import D5.S3.Arith.GoldenResource5040PriceInterval

/-! Exact rational estimates use the existing native atanh and gamma suppliers.
No external numerical certificate is a premise. The new finite separation uses
actual valuation layers, a positive original margin, and the same integer clock.
The universal implication, not RH, is the statement refuted below. -/

set_option autoImplicit false
set_option maxRecDepth 100000
noncomputable section
namespace D5.S3.Arith.Robin.PriceRecord.ActualInventoryCollectiveSeparation

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

def witnessN : ℕ := 2021649740510400
def witnessM : ℕ := 6198089008491993412800
private abbrev L : ℝ := Real.log (witnessN : ℝ)
private abbrev f (x : ℝ) : ℝ := Real.log (Real.log x)

private theorem clock_bounds_raw :
    ((352426901 / 10000000) : ℝ) < Real.log 2021649740510400 ∧ Real.log 2021649740510400 <
        (44053363 / 1250000) := by
  refine rational_log_bounds 2021649740510400 (31588277195475 / 17592186044416) _ _ 50 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

private theorem clock_bounds : ((352426901 / 10000000) : ℝ) < L ∧ L < (44053363 / 1250000) :=
    clock_bounds_raw

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

private theorem log_clock_bounds :
    ((1781129 / 500000) : ℝ) < Real.log (L) ∧ Real.log (L) < (35622583 / 10000000) := by
  exact log_interval_bounds (by norm_num) (clock_bounds).1 (clock_bounds).2 log_literal_0.1
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

private theorem f_clock_bounds :
    ((2540789 / 2000000) : ℝ) < Real.log (Real.log L) ∧ Real.log (Real.log L) < (3175987 /
        2500000) := by
  exact log_interval_bounds (by norm_num) (log_clock_bounds).1 (log_clock_bounds).2
      log_literal_2.1 log_literal_3.2

private theorem log_prime_2 :
    ((693147 / 1000000) : ℝ) < Real.log 2 ∧ Real.log 2 < (6931473 / 10000000) := by
  refine rational_log_bounds 2 1 _ _ 1 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

private theorem gain_2_6_bounds :
    ((1581 / 200000) : ℝ) < Real.log (127 / 126) ∧ Real.log (127 / 126) < (79053 / 10000000) := by
  have hs := log_expansion_remainder_bound (y := ((127 / 126) : ℝ)) (by norm_num) (by norm_num) 8
  norm_num [logRemainder, atanhParameter, atanhPartial, Finset.sum_range_succ] at hs
  constructor <;> linarith only [hs.1, hs.2]

private theorem gain_2_6_identity :
    goldenLayerMarginal 2 6 * Real.log 2 = Real.log ((127 / 126) : ℝ) := by
  norm_num [goldenLayerMarginal]

private theorem gain_2_7_bounds :
    ((39291 / 10000000) : ℝ) < Real.log (255 / 254) ∧ Real.log (255 / 254) < (19647 / 5000000) := by
  have hs := log_expansion_remainder_bound (y := ((255 / 254) : ℝ)) (by norm_num) (by norm_num) 8
  norm_num [logRemainder, atanhParameter, atanhPartial, Finset.sum_range_succ] at hs
  constructor <;> linarith only [hs.1, hs.2]

private theorem gain_2_7_identity :
    goldenLayerMarginal 2 7 * Real.log 2 = Real.log ((255 / 254) : ℝ) := by
  norm_num [goldenLayerMarginal]

private theorem delete_2_clock :
    ((86373857 / 2500000) : ℝ) < L - Real.log 2 ∧ L - Real.log 2 < (172747717 / 5000000) := by
  have hn := clock_bounds
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

private theorem delete_2_log :
    ((17711971 / 5000000) : ℝ) < Real.log (L - Real.log 2) ∧ Real.log (L - Real.log 2) <
        (7084789 / 2000000) := by
  exact log_interval_bounds (by norm_num) (delete_2_clock).1 (delete_2_clock).2 log_literal_4.1
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

private theorem delete_2_f :
    ((12648027 / 10000000) : ℝ) < Real.log (Real.log (L - Real.log 2)) ∧ Real.log (Real.log (L -
        Real.log 2)) < (12648031 / 10000000) := by
  exact log_interval_bounds (by norm_num) (delete_2_log).1 (delete_2_log).2 log_literal_6.1
      log_literal_7.2

private theorem insert_2_clock :
    ((359358371 / 10000000) : ℝ) < L + Real.log 2 ∧ L + Real.log 2 < (359358377 / 10000000) := by
  have hn := clock_bounds
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

private theorem insert_2_log :
    ((35817349 / 10000000) : ℝ) < Real.log (L + Real.log 2) ∧ Real.log (L + Real.log 2) <
        (4477169 / 1250000) := by
  exact log_interval_bounds (by norm_num) (insert_2_clock).1 (insert_2_clock).2 log_literal_8.1
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

private theorem insert_2_f :
    ((12758471 / 10000000) : ℝ) < Real.log (Real.log (L + Real.log 2)) ∧ Real.log (Real.log (L +
        Real.log 2)) < (510339 / 400000) := by
  exact log_interval_bounds (by norm_num) (insert_2_log).1 (insert_2_log).2 log_literal_10.1
      log_literal_11.2

private theorem log_prime_3 :
    ((10986121 / 10000000) : ℝ) < Real.log 3 ∧ Real.log 3 < (2746531 / 2500000) := by
  refine rational_log_bounds 3 (3 / 2) _ _ 1 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

private theorem gain_3_3_bounds :
    ((253177 / 10000000) : ℝ) < Real.log (40 / 39) ∧ Real.log (40 / 39) < (12659 / 500000) := by
  have hs := log_expansion_remainder_bound (y := ((40 / 39) : ℝ)) (by norm_num) (by norm_num) 8
  norm_num [logRemainder, atanhParameter, atanhPartial, Finset.sum_range_succ] at hs
  constructor <;> linarith only [hs.1, hs.2]

private theorem gain_3_3_identity :
    goldenLayerMarginal 3 3 * Real.log 3 = Real.log ((40 / 39) : ℝ) := by
  norm_num [goldenLayerMarginal]

private theorem gain_3_4_bounds :
    ((82987 / 10000000) : ℝ) < Real.log (121 / 120) ∧ Real.log (121 / 120) < (8299 / 1000000) := by
  have hs := log_expansion_remainder_bound (y := ((121 / 120) : ℝ)) (by norm_num) (by norm_num) 8
  norm_num [logRemainder, atanhParameter, atanhPartial, Finset.sum_range_succ] at hs
  constructor <;> linarith only [hs.1, hs.2]

private theorem gain_3_4_identity :
    goldenLayerMarginal 3 4 * Real.log 3 = Real.log ((121 / 120) : ℝ) := by
  norm_num [goldenLayerMarginal]

private theorem delete_3_clock :
    ((341440777 / 10000000) : ℝ) < L - Real.log 3 ∧ L - Real.log 3 < (341440783 / 10000000) := by
  have hn := clock_bounds
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

private theorem delete_3_log :
    ((3530589 / 1000000) : ℝ) < Real.log (L - Real.log 3) ∧ Real.log (L - Real.log 3) <
        (35305893 / 10000000) := by
  exact log_interval_bounds (by norm_num) (delete_3_clock).1 (delete_3_clock).2 log_literal_12.1
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

private theorem delete_3_f :
    ((6307323 / 5000000) : ℝ) < Real.log (Real.log (L - Real.log 3)) ∧ Real.log (Real.log (L -
        Real.log 3)) < (12614649 / 10000000) := by
  exact log_interval_bounds (by norm_num) (delete_3_log).1 (delete_3_log).2 log_literal_14.1
      log_literal_15.2

private theorem insert_3_clock :
    ((181706511 / 5000000) : ℝ) < L + Real.log 3 ∧ L + Real.log 3 < (90853257 / 2500000) := by
  have hn := clock_bounds
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

private theorem insert_3_log :
    ((35929547 / 10000000) : ℝ) < Real.log (L + Real.log 3) ∧ Real.log (L + Real.log 3) <
        (35929551 / 10000000) := by
  exact log_interval_bounds (by norm_num) (insert_3_clock).1 (insert_3_clock).2 log_literal_16.1
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

private theorem insert_3_f :
    ((3197437 / 2500000) : ℝ) < Real.log (Real.log (L + Real.log 3)) ∧ Real.log (Real.log (L +
        Real.log 3)) < (1598719 / 1250000) := by
  exact log_interval_bounds (by norm_num) (insert_3_log).1 (insert_3_log).2 log_literal_18.1
      log_literal_19.2

private theorem log_prime_5 :
    ((8047189 / 5000000) : ℝ) < Real.log 5 ∧ Real.log 5 < (16094381 / 10000000) := by
  refine rational_log_bounds 5 (5 / 4) _ _ 2 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

private theorem gain_5_2_bounds :
    ((327897 / 10000000) : ℝ) < Real.log (31 / 30) ∧ Real.log (31 / 30) < (3279 / 100000) := by
  have hs := log_expansion_remainder_bound (y := ((31 / 30) : ℝ)) (by norm_num) (by norm_num) 8
  norm_num [logRemainder, atanhParameter, atanhPartial, Finset.sum_range_succ] at hs
  constructor <;> linarith only [hs.1, hs.2]

private theorem gain_5_2_identity :
    goldenLayerMarginal 5 2 * Real.log 5 = Real.log ((31 / 30) : ℝ) := by
  norm_num [goldenLayerMarginal]

private theorem gain_5_3_bounds :
    ((64307 / 10000000) : ℝ) < Real.log (156 / 155) ∧ Real.log (156 / 155) < (6431 / 1000000) := by
  have hs := log_expansion_remainder_bound (y := ((156 / 155) : ℝ)) (by norm_num) (by norm_num) 8
  norm_num [logRemainder, atanhParameter, atanhPartial, Finset.sum_range_succ] at hs
  constructor <;> linarith only [hs.1, hs.2]

private theorem gain_5_3_identity :
    goldenLayerMarginal 5 3 * Real.log 5 = Real.log ((156 / 155) : ℝ) := by
  norm_num [goldenLayerMarginal]

private theorem delete_5_clock :
    ((8408313 / 250000) : ℝ) < L - Real.log 5 ∧ L - Real.log 5 < (168166263 / 5000000) := by
  have hn := clock_bounds
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

private theorem delete_5_log :
    ((35155151 / 10000000) : ℝ) < Real.log (L - Real.log 5) ∧ Real.log (L - Real.log 5) <
        (17577577 / 5000000) := by
  exact log_interval_bounds (by norm_num) (delete_5_clock).1 (delete_5_clock).2 log_literal_20.1
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

private theorem delete_5_f :
    ((12571859 / 10000000) : ℝ) < Real.log (Real.log (L - Real.log 5)) ∧ Real.log (Real.log (L -
        Real.log 5)) < (12571863 / 10000000) := by
  exact log_interval_bounds (by norm_num) (delete_5_log).1 (delete_5_log).2 log_literal_22.1
      log_literal_23.2

private theorem insert_5_clock :
    ((368521279 / 10000000) : ℝ) < L + Real.log 5 ∧ L + Real.log 5 < (73704257 / 2000000) := by
  have hn := clock_bounds
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

private theorem insert_5_log :
    ((9017283 / 2500000) : ℝ) < Real.log (L + Real.log 5) ∧ Real.log (L + Real.log 5) < (7213827
        / 2000000) := by
  exact log_interval_bounds (by norm_num) (insert_5_clock).1 (insert_5_clock).2 log_literal_24.1
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

private theorem insert_5_f :
    ((6414261 / 5000000) : ℝ) < Real.log (Real.log (L + Real.log 5)) ∧ Real.log (Real.log (L +
        Real.log 5)) < (6414263 / 5000000) := by
  exact log_interval_bounds (by norm_num) (insert_5_log).1 (insert_5_log).2 log_literal_26.1
      log_literal_27.2

private theorem log_prime_7 :
    ((194591 / 100000) : ℝ) < Real.log 7 ∧ Real.log 7 < (19459103 / 10000000) := by
  refine rational_log_bounds 7 (7 / 4) _ _ 2 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

private theorem gain_7_2_bounds :
    ((88497 / 5000000) : ℝ) < Real.log (57 / 56) ∧ Real.log (57 / 56) < (176997 / 10000000) := by
  have hs := log_expansion_remainder_bound (y := ((57 / 56) : ℝ)) (by norm_num) (by norm_num) 8
  norm_num [logRemainder, atanhParameter, atanhPartial, Finset.sum_range_succ] at hs
  constructor <;> linarith only [hs.1, hs.2]

private theorem gain_7_2_identity :
    goldenLayerMarginal 7 2 * Real.log 7 = Real.log ((57 / 56) : ℝ) := by
  norm_num [goldenLayerMarginal]

private theorem gain_7_3_bounds :
    ((2503 / 1000000) : ℝ) < Real.log (400 / 399) ∧ Real.log (400 / 399) < (25033 / 10000000) := by
  have hs := log_expansion_remainder_bound (y := ((400 / 399) : ℝ)) (by norm_num) (by norm_num) 8
  norm_num [logRemainder, atanhParameter, atanhPartial, Finset.sum_range_succ] at hs
  constructor <;> linarith only [hs.1, hs.2]

private theorem gain_7_3_identity :
    goldenLayerMarginal 7 3 * Real.log 7 = Real.log ((400 / 399) : ℝ) := by
  norm_num [goldenLayerMarginal]

private theorem delete_7_clock :
    ((166483899 / 5000000) : ℝ) < L - Real.log 7 ∧ L - Real.log 7 < (83241951 / 2500000) := by
  have hn := clock_bounds
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

private theorem delete_7_log :
    ((7010921 / 2000000) : ℝ) < Real.log (L - Real.log 7) ∧ Real.log (L - Real.log 7) <
        (35054609 / 10000000) := by
  exact log_interval_bounds (by norm_num) (delete_7_clock).1 (delete_7_clock).2 log_literal_28.1
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

private theorem delete_7_f :
    ((12543217 / 10000000) : ℝ) < Real.log (Real.log (L - Real.log 7)) ∧ Real.log (Real.log (L -
        Real.log 7)) < (6271611 / 5000000) := by
  exact log_interval_bounds (by norm_num) (delete_7_log).1 (delete_7_log).2 log_literal_30.1
      log_literal_31.2

private theorem insert_7_clock :
    ((371886001 / 10000000) : ℝ) < L + Real.log 7 ∧ L + Real.log 7 < (371886007 / 10000000) := by
  have hn := clock_bounds
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

private theorem insert_7_log :
    ((36160021 / 10000000) : ℝ) < Real.log (L + Real.log 7) ∧ Real.log (L + Real.log 7) <
        (4520003 / 1250000) := by
  exact log_interval_bounds (by norm_num) (insert_7_clock).1 (insert_7_clock).2 log_literal_32.1
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

private theorem insert_7_f :
    ((12853689 / 10000000) : ℝ) < Real.log (Real.log (L + Real.log 7)) ∧ Real.log (Real.log (L +
        Real.log 7)) < (12853693 / 10000000) := by
  exact log_interval_bounds (by norm_num) (insert_7_log).1 (insert_7_log).2 log_literal_34.1
      log_literal_35.2

private theorem log_prime_11 :
    ((23978951 / 10000000) : ℝ) < Real.log 11 ∧ Real.log 11 < (11989477 / 5000000) := by
  refine rational_log_bounds 11 (11 / 8) _ _ 3 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

private theorem gain_11_1_bounds :
    ((27191 / 312500) : ℝ) < Real.log (12 / 11) ∧ Real.log (12 / 11) < (174023 / 2000000) := by
  have hs := log_expansion_remainder_bound (y := ((12 / 11) : ℝ)) (by norm_num) (by norm_num) 8
  norm_num [logRemainder, atanhParameter, atanhPartial, Finset.sum_range_succ] at hs
  constructor <;> linarith only [hs.1, hs.2]

private theorem gain_11_1_identity :
    goldenLayerMarginal 11 1 * Real.log 11 = Real.log ((12 / 11) : ℝ) := by
  norm_num [goldenLayerMarginal]

private theorem gain_11_2_bounds :
    ((75471 / 10000000) : ℝ) < Real.log (133 / 132) ∧ Real.log (133 / 132) < (37737 / 5000000) := by
  have hs := log_expansion_remainder_bound (y := ((133 / 132) : ℝ)) (by norm_num) (by norm_num) 8
  norm_num [logRemainder, atanhParameter, atanhPartial, Finset.sum_range_succ] at hs
  constructor <;> linarith only [hs.1, hs.2]

private theorem gain_11_2_identity :
    goldenLayerMarginal 11 2 * Real.log 11 = Real.log ((133 / 132) : ℝ) := by
  norm_num [goldenLayerMarginal]

private theorem delete_11_clock :
    ((328447947 / 10000000) : ℝ) < L - Real.log 11 ∧ L - Real.log 11 < (328447953 / 10000000) := by
  have hn := clock_bounds
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

private theorem delete_11_log :
    ((34917931 / 10000000) : ℝ) < Real.log (L - Real.log 11) ∧ Real.log (L - Real.log 11) <
        (17458967 / 5000000) := by
  exact log_interval_bounds (by norm_num) (delete_11_clock).1 (delete_11_clock).2
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

private theorem delete_11_f :
    ((1563019 / 1250000) : ℝ) < Real.log (Real.log (L - Real.log 11)) ∧ Real.log (Real.log (L -
        Real.log 11)) < (3126039 / 2500000) := by
  exact log_interval_bounds (by norm_num) (delete_11_log).1 (delete_11_log).2 log_literal_38.1
      log_literal_39.2

private theorem insert_11_clock :
    ((94101463 / 2500000) : ℝ) < L + Real.log 11 ∧ L + Real.log 11 < (188202929 / 5000000) := by
  have hn := clock_bounds
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

private theorem insert_11_log :
    ((36280827 / 10000000) : ℝ) < Real.log (L + Real.log 11) ∧ Real.log (L + Real.log 11) <
        (3628083 / 1000000) := by
  exact log_interval_bounds (by norm_num) (insert_11_clock).1 (insert_11_clock).2
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

private theorem insert_11_f :
    ((6443521 / 5000000) : ℝ) < Real.log (Real.log (L + Real.log 11)) ∧ Real.log (Real.log (L +
        Real.log 11)) < (6443523 / 5000000) := by
  exact log_interval_bounds (by norm_num) (insert_11_log).1 (insert_11_log).2 log_literal_42.1
      log_literal_43.2

private theorem log_prime_13 :
    ((6412373 / 2500000) : ℝ) < Real.log 13 ∧ Real.log 13 < (5129899 / 2000000) := by
  refine rational_log_bounds 13 (13 / 8) _ _ 3 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

private theorem gain_13_1_bounds :
    ((370539 / 5000000) : ℝ) < Real.log (14 / 13) ∧ Real.log (14 / 13) < (741081 / 10000000) := by
  have hs := log_expansion_remainder_bound (y := ((14 / 13) : ℝ)) (by norm_num) (by norm_num) 8
  norm_num [logRemainder, atanhParameter, atanhPartial, Finset.sum_range_succ] at hs
  constructor <;> linarith only [hs.1, hs.2]

private theorem gain_13_1_identity :
    goldenLayerMarginal 13 1 * Real.log 13 = Real.log ((14 / 13) : ℝ) := by
  norm_num [goldenLayerMarginal]

private theorem gain_13_2_bounds :
    ((54793 / 10000000) : ℝ) < Real.log (183 / 182) ∧ Real.log (183 / 182) < (13699 / 2500000) := by
  have hs := log_expansion_remainder_bound (y := ((183 / 182) : ℝ)) (by norm_num) (by norm_num) 8
  norm_num [logRemainder, atanhParameter, atanhPartial, Finset.sum_range_succ] at hs
  constructor <;> linarith only [hs.1, hs.2]

private theorem gain_13_2_identity :
    goldenLayerMarginal 13 2 * Real.log 13 = Real.log ((183 / 182) : ℝ) := by
  norm_num [goldenLayerMarginal]

private theorem delete_13_clock :
    ((163388703 / 5000000) : ℝ) < L - Real.log 13 ∧ L - Real.log 13 < (81694353 / 2500000) := by
  have hn := clock_bounds
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

private theorem delete_13_log :
    ((1743347 / 500000) : ℝ) < Real.log (L - Real.log 13) ∧ Real.log (L - Real.log 13) <
        (34866943 / 10000000) := by
  exact log_interval_bounds (by norm_num) (delete_13_clock).1 (delete_13_clock).2
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

private theorem delete_13_f :
    ((12489539 / 10000000) : ℝ) < Real.log (Real.log (L - Real.log 13)) ∧ Real.log (Real.log (L
        - Real.log 13)) < (6244771 / 5000000) := by
  exact log_interval_bounds (by norm_num) (delete_13_log).1 (delete_13_log).2 log_literal_46.1
      log_literal_47.2

private theorem insert_13_clock :
    ((378076393 / 10000000) : ℝ) < L + Real.log 13 ∧ L + Real.log 13 < (378076399 / 10000000) := by
  have hn := clock_bounds
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

private theorem insert_13_log :
    ((3632511 / 1000000) : ℝ) < Real.log (L + Real.log 13) ∧ Real.log (L + Real.log 13) <
        (36325113 / 10000000) := by
  exact log_interval_bounds (by norm_num) (insert_13_clock).1 (insert_13_clock).2
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

private theorem insert_13_f :
    ((322481 / 250000) : ℝ) < Real.log (Real.log (L + Real.log 13)) ∧ Real.log (Real.log (L +
        Real.log 13)) < (3224811 / 2500000) := by
  exact log_interval_bounds (by norm_num) (insert_13_log).1 (insert_13_log).2 log_literal_50.1
      log_literal_51.2

private theorem log_prime_17 :
    ((7083033 / 2500000) : ℝ) < Real.log 17 ∧ Real.log 17 < (5666427 / 2000000) := by
  refine rational_log_bounds 17 (17 / 16) _ _ 4 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

private theorem gain_17_1_bounds :
    ((571583 / 10000000) : ℝ) < Real.log (18 / 17) ∧ Real.log (18 / 17) < (285793 / 5000000) := by
  have hs := log_expansion_remainder_bound (y := ((18 / 17) : ℝ)) (by norm_num) (by norm_num) 8
  norm_num [logRemainder, atanhParameter, atanhPartial, Finset.sum_range_succ] at hs
  constructor <;> linarith only [hs.1, hs.2]

private theorem gain_17_1_identity :
    goldenLayerMarginal 17 1 * Real.log 17 = Real.log ((18 / 17) : ℝ) := by
  norm_num [goldenLayerMarginal]

private theorem gain_17_2_bounds :
    ((261 / 80000) : ℝ) < Real.log (307 / 306) ∧ Real.log (307 / 306) < (8157 / 2500000) := by
  have hs := log_expansion_remainder_bound (y := ((307 / 306) : ℝ)) (by norm_num) (by norm_num) 8
  norm_num [logRemainder, atanhParameter, atanhPartial, Finset.sum_range_succ] at hs
  constructor <;> linarith only [hs.1, hs.2]

private theorem gain_17_2_identity :
    goldenLayerMarginal 17 2 * Real.log 17 = Real.log ((307 / 306) : ℝ) := by
  norm_num [goldenLayerMarginal]

private theorem delete_17_clock :
    ((162047383 / 5000000) : ℝ) < L - Real.log 17 ∧ L - Real.log 17 < (81023693 / 2500000) := by
  have hn := clock_bounds
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

private theorem delete_17_log :
    ((34784507 / 10000000) : ℝ) < Real.log (L - Real.log 17) ∧ Real.log (L - Real.log 17) <
        (3478451 / 1000000) := by
  exact log_interval_bounds (by norm_num) (delete_17_clock).1 (delete_17_clock).2
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

private theorem delete_17_f :
    ((3116467 / 2500000) : ℝ) < Real.log (Real.log (L - Real.log 17)) ∧ Real.log (Real.log (L -
        Real.log 17)) < (779117 / 625000) := by
  exact log_interval_bounds (by norm_num) (delete_17_log).1 (delete_17_log).2 log_literal_54.1
      log_literal_55.2

private theorem insert_17_clock :
    ((380759033 / 10000000) : ℝ) < L + Real.log 17 ∧ L + Real.log 17 < (380759039 / 10000000) := by
  have hn := clock_bounds
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

private theorem insert_17_log :
    ((7279163 / 2000000) : ℝ) < Real.log (L + Real.log 17) ∧ Real.log (L + Real.log 17) <
        (18197909 / 5000000) := by
  exact log_interval_bounds (by norm_num) (insert_17_clock).1 (insert_17_clock).2
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

private theorem insert_17_f :
    ((6459343 / 5000000) : ℝ) < Real.log (Real.log (L + Real.log 17)) ∧ Real.log (Real.log (L +
        Real.log 17)) < (12918689 / 10000000) := by
  exact log_interval_bounds (by norm_num) (insert_17_log).1 (insert_17_log).2 log_literal_58.1
      log_literal_59.2

private theorem log_prime_19 :
    ((7361097 / 2500000) : ℝ) < Real.log 19 ∧ Real.log 19 < (29444391 / 10000000) := by
  refine rational_log_bounds 19 (19 / 16) _ _ 4 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

private theorem gain_19_1_bounds :
    ((512931 / 10000000) : ℝ) < Real.log (20 / 19) ∧ Real.log (20 / 19) < (256467 / 5000000) := by
  have hs := log_expansion_remainder_bound (y := ((20 / 19) : ℝ)) (by norm_num) (by norm_num) 8
  norm_num [logRemainder, atanhParameter, atanhPartial, Finset.sum_range_succ] at hs
  constructor <;> linarith only [hs.1, hs.2]

private theorem gain_19_1_identity :
    goldenLayerMarginal 19 1 * Real.log 19 = Real.log ((20 / 19) : ℝ) := by
  norm_num [goldenLayerMarginal]

private theorem gain_19_2_bounds :
    ((657 / 250000) : ℝ) < Real.log (381 / 380) ∧ Real.log (381 / 380) < (26283 / 10000000) := by
  have hs := log_expansion_remainder_bound (y := ((381 / 380) : ℝ)) (by norm_num) (by norm_num) 8
  norm_num [logRemainder, atanhParameter, atanhPartial, Finset.sum_range_succ] at hs
  constructor <;> linarith only [hs.1, hs.2]

private theorem gain_19_2_identity :
    goldenLayerMarginal 19 2 * Real.log 19 = Real.log ((381 / 380) : ℝ) := by
  norm_num [goldenLayerMarginal]

private theorem delete_19_clock :
    ((32298251 / 1000000) : ℝ) < L - Real.log 19 ∧ L - Real.log 19 < (80745629 / 2500000) := by
  have hn := clock_bounds
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

private theorem delete_19_log :
    ((34750129 / 10000000) : ℝ) < Real.log (L - Real.log 19) ∧ Real.log (L - Real.log 19) <
        (8687533 / 2500000) := by
  exact log_interval_bounds (by norm_num) (delete_19_clock).1 (delete_19_clock).2
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

private theorem delete_19_f :
    ((622799 / 500000) : ℝ) < Real.log (Real.log (L - Real.log 19)) ∧ Real.log (Real.log (L -
        Real.log 19)) < (778499 / 625000) := by
  exact log_interval_bounds (by norm_num) (delete_19_log).1 (delete_19_log).2 log_literal_62.1
      log_literal_63.2

private theorem insert_19_clock :
    ((381871289 / 10000000) : ℝ) < L + Real.log 19 ∧ L + Real.log 19 < (76374259 / 2000000) := by
  have hn := clock_bounds
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

private theorem insert_19_log :
    ((4553123 / 1250000) : ℝ) < Real.log (L + Real.log 19) ∧ Real.log (L + Real.log 19) <
        (36424987 / 10000000) := by
  exact log_interval_bounds (by norm_num) (insert_19_clock).1 (insert_19_clock).2
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

private theorem insert_19_f :
    ((12926697 / 10000000) : ℝ) < Real.log (Real.log (L + Real.log 19)) ∧ Real.log (Real.log (L
        + Real.log 19)) < (12926701 / 10000000) := by
  exact log_interval_bounds (by norm_num) (insert_19_log).1 (insert_19_log).2 log_literal_66.1
      log_literal_67.2

private theorem log_prime_23 :
    ((31354941 / 10000000) : ℝ) < Real.log 23 ∧ Real.log 23 < (489921 / 156250) := by
  refine rational_log_bounds 23 (23 / 16) _ _ 4 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

private theorem gain_23_1_bounds :
    ((85119 / 2000000) : ℝ) < Real.log (24 / 23) ∧ Real.log (24 / 23) < (212799 / 5000000) := by
  have hs := log_expansion_remainder_bound (y := ((24 / 23) : ℝ)) (by norm_num) (by norm_num) 8
  norm_num [logRemainder, atanhParameter, atanhPartial, Finset.sum_range_succ] at hs
  constructor <;> linarith only [hs.1, hs.2]

private theorem gain_23_1_identity :
    goldenLayerMarginal 23 1 * Real.log 23 = Real.log ((24 / 23) : ℝ) := by
  norm_num [goldenLayerMarginal]

private theorem gain_23_2_bounds :
    ((9049 / 5000000) : ℝ) < Real.log (553 / 552) ∧ Real.log (553 / 552) < (18101 / 10000000) := by
  have hs := log_expansion_remainder_bound (y := ((553 / 552) : ℝ)) (by norm_num) (by norm_num) 8
  norm_num [logRemainder, atanhParameter, atanhPartial, Finset.sum_range_succ] at hs
  constructor <;> linarith only [hs.1, hs.2]

private theorem gain_23_2_identity :
    goldenLayerMarginal 23 2 * Real.log 23 = Real.log ((553 / 552) : ℝ) := by
  norm_num [goldenLayerMarginal]

private theorem delete_23_clock :
    ((321071957 / 10000000) : ℝ) < L - Real.log 23 ∧ L - Real.log 23 < (321071963 / 10000000) := by
  have hn := clock_bounds
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

private theorem delete_23_log :
    ((86727 / 25000) : ℝ) < Real.log (L - Real.log 23) ∧ Real.log (L - Real.log 23) < (34690803
        / 10000000) := by
  exact log_interval_bounds (by norm_num) (delete_23_clock).1 (delete_23_clock).2
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

private theorem delete_23_f :
    ((12438893 / 10000000) : ℝ) < Real.log (Real.log (L - Real.log 23)) ∧ Real.log (Real.log (L
        - Real.log 23)) < (12438897 / 10000000) := by
  exact log_interval_bounds (by norm_num) (delete_23_log).1 (delete_23_log).2 log_literal_70.1
      log_literal_71.2

private theorem insert_23_clock :
    ((191890921 / 5000000) : ℝ) < L + Real.log 23 ∧ L + Real.log 23 < (47972731 / 1250000) := by
  have hn := clock_bounds
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

private theorem insert_23_log :
    ((3647489 / 1000000) : ℝ) < Real.log (L + Real.log 23) ∧ Real.log (L + Real.log 23) <
        (36474893 / 10000000) := by
  exact log_interval_bounds (by norm_num) (insert_23_clock).1 (insert_23_clock).2
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

private theorem insert_23_f :
    ((3235097 / 2500000) : ℝ) < Real.log (Real.log (L + Real.log 23)) ∧ Real.log (Real.log (L +
        Real.log 23)) < (1617549 / 1250000) := by
  exact log_interval_bounds (by norm_num) (insert_23_log).1 (insert_23_log).2 log_literal_74.1
      log_literal_75.2

private theorem log_prime_29 :
    ((33672957 / 10000000) : ℝ) < Real.log 29 ∧ Real.log 29 < (52614 / 15625) := by
  refine rational_log_bounds 29 (29 / 16) _ _ 4 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

private theorem gain_29_1_bounds :
    ((169507 / 5000000) : ℝ) < Real.log (30 / 29) ∧ Real.log (30 / 29) < (339017 / 10000000) := by
  have hs := log_expansion_remainder_bound (y := ((30 / 29) : ℝ)) (by norm_num) (by norm_num) 8
  norm_num [logRemainder, atanhParameter, atanhPartial, Finset.sum_range_succ] at hs
  constructor <;> linarith only [hs.1, hs.2]

private theorem gain_29_1_identity :
    goldenLayerMarginal 29 1 * Real.log 29 = Real.log ((30 / 29) : ℝ) := by
  norm_num [goldenLayerMarginal]

private theorem gain_29_2_bounds :
    ((5743 / 5000000) : ℝ) < Real.log (871 / 870) ∧ Real.log (871 / 870) < (11489 / 10000000) := by
  have hs := log_expansion_remainder_bound (y := ((871 / 870) : ℝ)) (by norm_num) (by norm_num) 8
  norm_num [logRemainder, atanhParameter, atanhPartial, Finset.sum_range_succ] at hs
  constructor <;> linarith only [hs.1, hs.2]

private theorem gain_29_2_identity :
    goldenLayerMarginal 29 2 * Real.log 29 = Real.log ((871 / 870) : ℝ) := by
  norm_num [goldenLayerMarginal]

private theorem delete_29_clock :
    ((318753941 / 10000000) : ℝ) < L - Real.log 29 ∧ L - Real.log 29 < (318753947 / 10000000) := by
  have hn := clock_bounds
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

private theorem delete_29_log :
    ((17309171 / 5000000) : ℝ) < Real.log (L - Real.log 29) ∧ Real.log (L - Real.log 29) <
        (6923669 / 2000000) := by
  exact log_interval_bounds (by norm_num) (delete_29_clock).1 (delete_29_clock).2
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

private theorem delete_29_f :
    ((194031 / 156250) : ℝ) < Real.log (Real.log (L - Real.log 29)) ∧ Real.log (Real.log (L -
        Real.log 29)) < (3104497 / 2500000) := by
  exact log_interval_bounds (by norm_num) (delete_29_log).1 (delete_29_log).2 log_literal_78.1
      log_literal_79.2

private theorem insert_29_clock :
    ((193049929 / 5000000) : ℝ) < L + Real.log 29 ∧ L + Real.log 29 < (48262483 / 1250000) := by
  have hn := clock_bounds
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

private theorem insert_29_log :
    ((9133777 / 2500000) : ℝ) < Real.log (L + Real.log 29) ∧ Real.log (L + Real.log 29) <
        (36535111 / 10000000) := by
  exact log_interval_bounds (by norm_num) (insert_29_clock).1 (insert_29_clock).2
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

private theorem insert_29_f :
    ((3239221 / 2500000) : ℝ) < Real.log (Real.log (L + Real.log 29)) ∧ Real.log (Real.log (L +
        Real.log 29)) < (1619611 / 1250000) := by
  exact log_interval_bounds (by norm_num) (insert_29_log).1 (insert_29_log).2 log_literal_82.1
      log_literal_83.2

private theorem log_prime_31 :
    ((34339871 / 10000000) : ℝ) < Real.log 31 ∧ Real.log 31 < (17169937 / 5000000) := by
  refine rational_log_bounds 31 (31 / 16) _ _ 4 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

private theorem gain_31_1_bounds :
    ((63497 / 2000000) : ℝ) < Real.log (32 / 31) ∧ Real.log (32 / 31) < (19843 / 625000) := by
  have hs := log_expansion_remainder_bound (y := ((32 / 31) : ℝ)) (by norm_num) (by norm_num) 8
  norm_num [logRemainder, atanhParameter, atanhPartial, Finset.sum_range_succ] at hs
  constructor <;> linarith only [hs.1, hs.2]

private theorem gain_31_1_identity :
    goldenLayerMarginal 31 1 * Real.log 31 = Real.log ((32 / 31) : ℝ) := by
  norm_num [goldenLayerMarginal]

private theorem gain_31_2_bounds :
    ((5037 / 5000000) : ℝ) < Real.log (993 / 992) ∧ Real.log (993 / 992) < (10077 / 10000000) := by
  have hs := log_expansion_remainder_bound (y := ((993 / 992) : ℝ)) (by norm_num) (by norm_num) 8
  norm_num [logRemainder, atanhParameter, atanhPartial, Finset.sum_range_succ] at hs
  constructor <;> linarith only [hs.1, hs.2]

private theorem gain_31_2_identity :
    goldenLayerMarginal 31 2 * Real.log 31 = Real.log ((993 / 992) : ℝ) := by
  norm_num [goldenLayerMarginal]

private theorem delete_31_clock :
    ((318087027 / 10000000) : ℝ) < L - Real.log 31 ∧ L - Real.log 31 < (318087033 / 10000000) := by
  have hn := clock_bounds
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

private theorem delete_31_log :
    ((17298699 / 5000000) : ℝ) < Real.log (L - Real.log 31) ∧ Real.log (L - Real.log 31) <
        (34597401 / 10000000) := by
  exact log_interval_bounds (by norm_num) (delete_31_clock).1 (delete_31_clock).2
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

private theorem delete_31_f :
    ((3102983 / 2500000) : ℝ) < Real.log (Real.log (L - Real.log 31)) ∧ Real.log (Real.log (L -
        Real.log 31)) < (387873 / 312500) := by
  exact log_interval_bounds (by norm_num) (delete_31_log).1 (delete_31_log).2 log_literal_86.1
      log_literal_87.2

private theorem insert_31_clock :
    ((96691693 / 2500000) : ℝ) < L + Real.log 31 ∧ L + Real.log 31 < (193383389 / 5000000) := by
  have hn := clock_bounds
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

private theorem insert_31_log :
    ((18276183 / 5000000) : ℝ) < Real.log (L + Real.log 31) ∧ Real.log (L + Real.log 31) <
        (36552369 / 10000000) := by
  exact log_interval_bounds (by norm_num) (insert_31_clock).1 (insert_31_clock).2
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

private theorem insert_31_f :
    ((12961607 / 10000000) : ℝ) < Real.log (Real.log (L + Real.log 31)) ∧ Real.log (Real.log (L
        + Real.log 31)) < (12961611 / 10000000) := by
  exact log_interval_bounds (by norm_num) (insert_31_log).1 (insert_31_log).2 log_literal_90.1
      log_literal_91.2

private theorem log_prime_37 :
    ((18054589 / 5000000) : ℝ) < Real.log 37 ∧ Real.log 37 < (36109181 / 10000000) := by
  refine rational_log_bounds 37 (37 / 32) _ _ 5 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

private theorem gain_37_1_bounds :
    ((266681 / 10000000) : ℝ) < Real.log (38 / 37) ∧ Real.log (38 / 37) < (66671 / 2500000) := by
  have hs := log_expansion_remainder_bound (y := ((38 / 37) : ℝ)) (by norm_num) (by norm_num) 8
  norm_num [logRemainder, atanhParameter, atanhPartial, Finset.sum_range_succ] at hs
  constructor <;> linarith only [hs.1, hs.2]

private theorem gain_37_1_identity :
    goldenLayerMarginal 37 1 * Real.log 37 = Real.log ((38 / 37) : ℝ) := by
  norm_num [goldenLayerMarginal]

private theorem log_prime_34 :
    ((8815901 / 2500000) : ℝ) < Real.log 34 ∧ Real.log 34 < (35263607 / 10000000) := by
  refine rational_log_bounds 34 (17 / 16) _ _ 5 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

private theorem gain_34_1_bounds :
    ((144937 / 5000000) : ℝ) < Real.log (35 / 34) ∧ Real.log (35 / 34) < (289877 / 10000000) := by
  have hs := log_expansion_remainder_bound (y := ((35 / 34) : ℝ)) (by norm_num) (by norm_num) 8
  norm_num [logRemainder, atanhParameter, atanhPartial, Finset.sum_range_succ] at hs
  constructor <;> linarith only [hs.1, hs.2]

private theorem log_prime_35 :
    ((35553479 / 10000000) : ℝ) < Real.log 35 ∧ Real.log 35 < (17776741 / 5000000) := by
  refine rational_log_bounds 35 (35 / 32) _ _ 5 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

private theorem gain_35_1_bounds :
    ((281707 / 10000000) : ℝ) < Real.log (36 / 35) ∧ Real.log (36 / 35) < (28171 / 1000000) := by
  have hs := log_expansion_remainder_bound (y := ((36 / 35) : ℝ)) (by norm_num) (by norm_num) 8
  norm_num [logRemainder, atanhParameter, atanhPartial, Finset.sum_range_succ] at hs
  constructor <;> linarith only [hs.1, hs.2]

private theorem m_clock_bounds :
    ((250892639 / 5000000) : ℝ) < Real.log 6198089008491993412800 ∧ Real.log
        6198089008491993412800 < (501785281 / 10000000) := by
  refine rational_log_bounds 6198089008491993412800 (96845140757687397075 /
      73786976294838206464) _ _ 72 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

private theorem log_literal_96 :
    ((39155871 / 10000000) : ℝ) < Real.log (250892639 / 5000000) ∧ Real.log (250892639 /
        5000000) < (19577937 / 5000000) := by
  refine rational_log_bounds (250892639 / 5000000) (250892639 / 160000000) _ _ 5 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

private theorem log_literal_97 :
    ((39155871 / 10000000) : ℝ) < Real.log (501785281 / 10000000) ∧ Real.log (501785281 /
        10000000) < (19577937 / 5000000) := by
  refine rational_log_bounds (501785281 / 10000000) (501785281 / 320000000) _ _ 5 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

private theorem m_log_clock_bounds :
    ((39155871 / 10000000) : ℝ) < Real.log (Real.log (6198089008491993412800 : ℝ)) ∧ Real.log
        (Real.log (6198089008491993412800 : ℝ)) < (19577937 / 5000000) := by
  exact log_interval_bounds (by norm_num) (m_clock_bounds).1 (m_clock_bounds).2 log_literal_96.1
      log_literal_97.2

private theorem log_literal_98 :
    ((13649651 / 10000000) : ℝ) < Real.log (39155871 / 10000000) ∧ Real.log (39155871 /
        10000000) < (6824827 / 5000000) := by
  refine rational_log_bounds (39155871 / 10000000) (39155871 / 20000000) _ _ 1 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

private theorem log_literal_99 :
    ((3412413 / 2500000) : ℝ) < Real.log (19577937 / 5000000) ∧ Real.log (19577937 / 5000000) <
        (2729931 / 2000000) := by
  refine rational_log_bounds (19577937 / 5000000) (19577937 / 10000000) _ _ 1 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

private theorem m_f_clock_bounds :
    ((13649651 / 10000000) : ℝ) < Real.log (Real.log (Real.log (6198089008491993412800 : ℝ))) ∧
        Real.log (Real.log (Real.log (6198089008491993412800 : ℝ))) < (2729931 / 2000000) := by
  exact log_interval_bounds (by norm_num) (m_log_clock_bounds).1 (m_log_clock_bounds).2
      log_literal_98.1 log_literal_99.2

private theorem w_N_bounds_raw :
    ((18224697 / 10000000) : ℝ) < Real.log (70225920 / 11350339) ∧ Real.log (70225920 /
        11350339) < (182247 / 100000) := by
  refine rational_log_bounds (70225920 / 11350339) (17556480 / 11350339) _ _ 2 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

private theorem w_M_bounds_raw :
    ((1198299 / 625000) : ℝ) < Real.log (3074209873920 / 451928782799) ∧ Real.log (3074209873920
        / 451928782799) < (19172787 / 10000000) := by
  refine rational_log_bounds (3074209873920 / 451928782799) (768552468480 / 451928782799) _ _ 2 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]


private def support : Finset ℕ := {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31}

private def exponent (p : ℕ) : ℕ :=
  if p = 2 then 6 else if p = 3 then 3 else if p = 5 then 2 else if p = 7 then 2 else if p = 11
      then 1 else if p = 13 then 1 else if p = 17 then 1 else if p = 19 then 1 else if p = 23
      then 1 else if p = 29 then 1 else if p = 31 then 1 else 0

private theorem raw_factorization_N : witnessN.factorization = Finsupp.single 2 6 +
    Finsupp.single 3 3 + Finsupp.single 5 2 + Finsupp.single 7 2 + Finsupp.single 11 1 +
    Finsupp.single 13 1 + Finsupp.single 17 1 + Finsupp.single 19 1 + Finsupp.single 23 1 +
    Finsupp.single 29 1 + Finsupp.single 31 1 := by
  rw [show witnessN = 2 ^ 6 * 3 ^ 3 * 5 ^ 2 * 7 ^ 2 * 11 ^ 1 * 13 ^ 1 * 17 ^ 1 * 19 ^ 1 * 23 ^ 1
      * 29 ^ 1 * 31 ^ 1 by norm_num [witnessN]]
  rw [Nat.factorization_mul (by norm_num) (by norm_num)]
  rw [Nat.factorization_mul (by norm_num) (by norm_num)]
  rw [Nat.factorization_mul (by norm_num) (by norm_num)]
  rw [Nat.factorization_mul (by norm_num) (by norm_num)]
  rw [Nat.factorization_mul (by norm_num) (by norm_num)]
  rw [Nat.factorization_mul (by norm_num) (by norm_num)]
  rw [Nat.factorization_mul (by norm_num) (by norm_num)]
  rw [Nat.factorization_mul (by norm_num) (by norm_num)]
  rw [Nat.factorization_mul (by norm_num) (by norm_num)]
  rw [Nat.factorization_mul (by norm_num) (by norm_num)]
  rw [(by norm_num : Nat.Prime 2).factorization_pow, (by norm_num : Nat.Prime
      3).factorization_pow, (by norm_num : Nat.Prime 5).factorization_pow, (by norm_num :
      Nat.Prime 7).factorization_pow, (by norm_num : Nat.Prime 11).factorization_pow, (by
      norm_num : Nat.Prime 13).factorization_pow, (by norm_num : Nat.Prime
      17).factorization_pow, (by norm_num : Nat.Prime 19).factorization_pow, (by norm_num :
      Nat.Prime 23).factorization_pow, (by norm_num : Nat.Prime 29).factorization_pow, (by
      norm_num : Nat.Prime 31).factorization_pow]

private theorem factorization_N (p : ℕ) : witnessN.factorization p = exponent p := by
  rw [raw_factorization_N]
  simp only [Finsupp.add_apply, Finsupp.single_apply]
  by_cases h2 : p = 2
  · subst p
    norm_num [exponent]
  by_cases h3 : p = 3
  · subst p
    norm_num [exponent]
  by_cases h5 : p = 5
  · subst p
    norm_num [exponent]
  by_cases h7 : p = 7
  · subst p
    norm_num [exponent]
  by_cases h11 : p = 11
  · subst p
    norm_num [exponent]
  by_cases h13 : p = 13
  · subst p
    norm_num [exponent]
  by_cases h17 : p = 17
  · subst p
    norm_num [exponent]
  by_cases h19 : p = 19
  · subst p
    norm_num [exponent]
  by_cases h23 : p = 23
  · subst p
    norm_num [exponent]
  by_cases h29 : p = 29
  · subst p
    norm_num [exponent]
  by_cases h31 : p = 31
  · subst p
    norm_num [exponent]
  simp [exponent, eq_comm, h2, h3, h5, h7, h11, h13, h17, h19, h23, h29, h31]

private theorem support_N : witnessN.primeFactors = support := by
  classical
  ext p
  rw [← Nat.support_factorization, Finsupp.mem_support_iff, factorization_N]
  simp only [exponent, support, Finset.mem_insert, Finset.mem_singleton]
  split_ifs <;> simp_all

private theorem support_cover : Nat.primesLE 36 = support := by decide
private theorem support_floor : Nat.primesLE 34 = support := by decide

private theorem omitted_ge {p : ℕ} (hp : p.Prime) (hn : p ∉ support) : 37 ≤ p := by
  by_contra h
  have hm := Nat.mem_primesLE.mpr ⟨(by omega : p ≤ 36), hp⟩
  rw [support_cover] at hm
  exact hn hm

private theorem actual_cofactor {p : ℕ} (hp : p ∈ support) : 5040 < witnessN / p := by
  simp only [support, Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num [witnessN]

private theorem sigma_N : ArithmeticFunction.sigma 1 witnessN = 12508191424512000 := by
  rw [show witnessN = 2 ^ 6 * 3 ^ 3 * 5 ^ 2 * 7 ^ 2 * 11 ^ 1 * 13 ^ 1 * 17 ^ 1 * 19 ^ 1 * 23 ^ 1
      * 29 ^ 1 * 31 ^ 1 by norm_num [witnessN]]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2),
      ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3),
      ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 5),
      ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 7),
      ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 11),
      ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 13),
      ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 17),
      ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 19),
      ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 23),
      ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 29),
      ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 31)]
  norm_num

private theorem sigma_M : ArithmeticFunction.sigma 1 witnessM = 42162011260556673024000 := by
  rw [show witnessM = 2 ^ 6 * 3 ^ 3 * 5 ^ 2 * 7 ^ 2 * 11 ^ 1 * 13 ^ 1 * 17 ^ 1 * 19 ^ 1 * 23 ^ 1
      * 29 ^ 1 * 31 ^ 1 * 37 ^ 1 * 41 ^ 1 * 43 ^ 1 * 47 ^ 1 by norm_num [witnessM]]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2),
      ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3),
      ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 5),
      ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 7),
      ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 11),
      ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 13),
      ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 17),
      ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 19),
      ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 23),
      ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 29),
      ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 31),
      ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 37),
      ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 41),
      ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 43),
      ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 47)]
  norm_num

private theorem positive_clock : 16 < L := by
  have := clock_bounds.1
  norm_num at this ⊢
  linarith

private theorem price_positive : 0 < price L := price_pos (by have := positive_clock; linarith)

private theorem clock_product : (125 : ℝ) < L * Real.log L ∧ L * Real.log L < 126 := by
  have hn := clock_bounds
  have hl := log_clock_bounds
  constructor <;> nlinarith only [hn.1, hn.2, hl.1, hl.2]

private theorem threshold_2 :
    price L < goldenLayerMarginal 2 6 ∧
      goldenLayerMarginal 2 7 < price L := by
  have ht := clock_product
  have hp := log_prime_2
  have he := gain_2_6_bounds
  have hs := gain_2_7_bounds
  have hpos : 0 < L * Real.log L := by linarith only [ht.1]
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  constructor
  · apply (mul_lt_mul_iff_left₀ hlog).mp
    rw [gain_2_6_identity]
    change 1 / (L * Real.log L) * Real.log 2 < _
    rw [one_div_mul_eq_div, div_lt_iff₀ hpos]
    nlinarith only [ht.1, hp.2, he.1]
  · apply (mul_lt_mul_iff_left₀ hlog).mp
    rw [gain_2_7_identity]
    change _ < 1 / (L * Real.log L) * Real.log 2
    rw [one_div_mul_eq_div, lt_div_iff₀ hpos]
    nlinarith only [ht.2, hp.1, hs.1, hs.2]

private theorem threshold_3 :
    price L < goldenLayerMarginal 3 3 ∧
      goldenLayerMarginal 3 4 < price L := by
  have ht := clock_product
  have hp := log_prime_3
  have he := gain_3_3_bounds
  have hs := gain_3_4_bounds
  have hpos : 0 < L * Real.log L := by linarith only [ht.1]
  have hlog : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num)
  constructor
  · apply (mul_lt_mul_iff_left₀ hlog).mp
    rw [gain_3_3_identity]
    change 1 / (L * Real.log L) * Real.log 3 < _
    rw [one_div_mul_eq_div, div_lt_iff₀ hpos]
    nlinarith only [ht.1, hp.2, he.1]
  · apply (mul_lt_mul_iff_left₀ hlog).mp
    rw [gain_3_4_identity]
    change _ < 1 / (L * Real.log L) * Real.log 3
    rw [one_div_mul_eq_div, lt_div_iff₀ hpos]
    nlinarith only [ht.2, hp.1, hs.1, hs.2]

private theorem threshold_5 :
    price L < goldenLayerMarginal 5 2 ∧
      goldenLayerMarginal 5 3 < price L := by
  have ht := clock_product
  have hp := log_prime_5
  have he := gain_5_2_bounds
  have hs := gain_5_3_bounds
  have hpos : 0 < L * Real.log L := by linarith only [ht.1]
  have hlog : 0 < Real.log (5 : ℝ) := Real.log_pos (by norm_num)
  constructor
  · apply (mul_lt_mul_iff_left₀ hlog).mp
    rw [gain_5_2_identity]
    change 1 / (L * Real.log L) * Real.log 5 < _
    rw [one_div_mul_eq_div, div_lt_iff₀ hpos]
    nlinarith only [ht.1, hp.2, he.1]
  · apply (mul_lt_mul_iff_left₀ hlog).mp
    rw [gain_5_3_identity]
    change _ < 1 / (L * Real.log L) * Real.log 5
    rw [one_div_mul_eq_div, lt_div_iff₀ hpos]
    nlinarith only [ht.2, hp.1, hs.1, hs.2]

private theorem threshold_7 :
    price L < goldenLayerMarginal 7 2 ∧
      goldenLayerMarginal 7 3 < price L := by
  have ht := clock_product
  have hp := log_prime_7
  have he := gain_7_2_bounds
  have hs := gain_7_3_bounds
  have hpos : 0 < L * Real.log L := by linarith only [ht.1]
  have hlog : 0 < Real.log (7 : ℝ) := Real.log_pos (by norm_num)
  constructor
  · apply (mul_lt_mul_iff_left₀ hlog).mp
    rw [gain_7_2_identity]
    change 1 / (L * Real.log L) * Real.log 7 < _
    rw [one_div_mul_eq_div, div_lt_iff₀ hpos]
    nlinarith only [ht.1, hp.2, he.1]
  · apply (mul_lt_mul_iff_left₀ hlog).mp
    rw [gain_7_3_identity]
    change _ < 1 / (L * Real.log L) * Real.log 7
    rw [one_div_mul_eq_div, lt_div_iff₀ hpos]
    nlinarith only [ht.2, hp.1, hs.1, hs.2]

private theorem threshold_11 :
    price L < goldenLayerMarginal 11 1 ∧
      goldenLayerMarginal 11 2 < price L := by
  have ht := clock_product
  have hp := log_prime_11
  have he := gain_11_1_bounds
  have hs := gain_11_2_bounds
  have hpos : 0 < L * Real.log L := by linarith only [ht.1]
  have hlog : 0 < Real.log (11 : ℝ) := Real.log_pos (by norm_num)
  constructor
  · apply (mul_lt_mul_iff_left₀ hlog).mp
    rw [gain_11_1_identity]
    change 1 / (L * Real.log L) * Real.log 11 < _
    rw [one_div_mul_eq_div, div_lt_iff₀ hpos]
    nlinarith only [ht.1, hp.2, he.1]
  · apply (mul_lt_mul_iff_left₀ hlog).mp
    rw [gain_11_2_identity]
    change _ < 1 / (L * Real.log L) * Real.log 11
    rw [one_div_mul_eq_div, lt_div_iff₀ hpos]
    nlinarith only [ht.2, hp.1, hs.1, hs.2]

private theorem threshold_13 :
    price L < goldenLayerMarginal 13 1 ∧
      goldenLayerMarginal 13 2 < price L := by
  have ht := clock_product
  have hp := log_prime_13
  have he := gain_13_1_bounds
  have hs := gain_13_2_bounds
  have hpos : 0 < L * Real.log L := by linarith only [ht.1]
  have hlog : 0 < Real.log (13 : ℝ) := Real.log_pos (by norm_num)
  constructor
  · apply (mul_lt_mul_iff_left₀ hlog).mp
    rw [gain_13_1_identity]
    change 1 / (L * Real.log L) * Real.log 13 < _
    rw [one_div_mul_eq_div, div_lt_iff₀ hpos]
    nlinarith only [ht.1, hp.2, he.1]
  · apply (mul_lt_mul_iff_left₀ hlog).mp
    rw [gain_13_2_identity]
    change _ < 1 / (L * Real.log L) * Real.log 13
    rw [one_div_mul_eq_div, lt_div_iff₀ hpos]
    nlinarith only [ht.2, hp.1, hs.1, hs.2]

private theorem threshold_17 :
    price L < goldenLayerMarginal 17 1 ∧
      goldenLayerMarginal 17 2 < price L := by
  have ht := clock_product
  have hp := log_prime_17
  have he := gain_17_1_bounds
  have hs := gain_17_2_bounds
  have hpos : 0 < L * Real.log L := by linarith only [ht.1]
  have hlog : 0 < Real.log (17 : ℝ) := Real.log_pos (by norm_num)
  constructor
  · apply (mul_lt_mul_iff_left₀ hlog).mp
    rw [gain_17_1_identity]
    change 1 / (L * Real.log L) * Real.log 17 < _
    rw [one_div_mul_eq_div, div_lt_iff₀ hpos]
    nlinarith only [ht.1, hp.2, he.1]
  · apply (mul_lt_mul_iff_left₀ hlog).mp
    rw [gain_17_2_identity]
    change _ < 1 / (L * Real.log L) * Real.log 17
    rw [one_div_mul_eq_div, lt_div_iff₀ hpos]
    nlinarith only [ht.2, hp.1, hs.1, hs.2]

private theorem threshold_19 :
    price L < goldenLayerMarginal 19 1 ∧
      goldenLayerMarginal 19 2 < price L := by
  have ht := clock_product
  have hp := log_prime_19
  have he := gain_19_1_bounds
  have hs := gain_19_2_bounds
  have hpos : 0 < L * Real.log L := by linarith only [ht.1]
  have hlog : 0 < Real.log (19 : ℝ) := Real.log_pos (by norm_num)
  constructor
  · apply (mul_lt_mul_iff_left₀ hlog).mp
    rw [gain_19_1_identity]
    change 1 / (L * Real.log L) * Real.log 19 < _
    rw [one_div_mul_eq_div, div_lt_iff₀ hpos]
    nlinarith only [ht.1, hp.2, he.1]
  · apply (mul_lt_mul_iff_left₀ hlog).mp
    rw [gain_19_2_identity]
    change _ < 1 / (L * Real.log L) * Real.log 19
    rw [one_div_mul_eq_div, lt_div_iff₀ hpos]
    nlinarith only [ht.2, hp.1, hs.1, hs.2]

private theorem threshold_23 :
    price L < goldenLayerMarginal 23 1 ∧
      goldenLayerMarginal 23 2 < price L := by
  have ht := clock_product
  have hp := log_prime_23
  have he := gain_23_1_bounds
  have hs := gain_23_2_bounds
  have hpos : 0 < L * Real.log L := by linarith only [ht.1]
  have hlog : 0 < Real.log (23 : ℝ) := Real.log_pos (by norm_num)
  constructor
  · apply (mul_lt_mul_iff_left₀ hlog).mp
    rw [gain_23_1_identity]
    change 1 / (L * Real.log L) * Real.log 23 < _
    rw [one_div_mul_eq_div, div_lt_iff₀ hpos]
    nlinarith only [ht.1, hp.2, he.1]
  · apply (mul_lt_mul_iff_left₀ hlog).mp
    rw [gain_23_2_identity]
    change _ < 1 / (L * Real.log L) * Real.log 23
    rw [one_div_mul_eq_div, lt_div_iff₀ hpos]
    nlinarith only [ht.2, hp.1, hs.1, hs.2]

private theorem threshold_29 :
    price L < goldenLayerMarginal 29 1 ∧
      goldenLayerMarginal 29 2 < price L := by
  have ht := clock_product
  have hp := log_prime_29
  have he := gain_29_1_bounds
  have hs := gain_29_2_bounds
  have hpos : 0 < L * Real.log L := by linarith only [ht.1]
  have hlog : 0 < Real.log (29 : ℝ) := Real.log_pos (by norm_num)
  constructor
  · apply (mul_lt_mul_iff_left₀ hlog).mp
    rw [gain_29_1_identity]
    change 1 / (L * Real.log L) * Real.log 29 < _
    rw [one_div_mul_eq_div, div_lt_iff₀ hpos]
    nlinarith only [ht.1, hp.2, he.1]
  · apply (mul_lt_mul_iff_left₀ hlog).mp
    rw [gain_29_2_identity]
    change _ < 1 / (L * Real.log L) * Real.log 29
    rw [one_div_mul_eq_div, lt_div_iff₀ hpos]
    nlinarith only [ht.2, hp.1, hs.1, hs.2]

private theorem threshold_31 :
    price L < goldenLayerMarginal 31 1 ∧
      goldenLayerMarginal 31 2 < price L := by
  have ht := clock_product
  have hp := log_prime_31
  have he := gain_31_1_bounds
  have hs := gain_31_2_bounds
  have hpos : 0 < L * Real.log L := by linarith only [ht.1]
  have hlog : 0 < Real.log (31 : ℝ) := Real.log_pos (by norm_num)
  constructor
  · apply (mul_lt_mul_iff_left₀ hlog).mp
    rw [gain_31_1_identity]
    change 1 / (L * Real.log L) * Real.log 31 < _
    rw [one_div_mul_eq_div, div_lt_iff₀ hpos]
    nlinarith only [ht.1, hp.2, he.1]
  · apply (mul_lt_mul_iff_left₀ hlog).mp
    rw [gain_31_2_identity]
    change _ < 1 / (L * Real.log L) * Real.log 31
    rw [one_div_mul_eq_div, lt_div_iff₀ hpos]
    nlinarith only [ht.2, hp.1, hs.1, hs.2]


private theorem tail_threshold : goldenLayerMarginal 37 1 < price L := by
  have ht := clock_product
  have hp := log_prime_37
  have hs := gain_37_1_bounds
  have hpos : 0 < L * Real.log L := by linarith only [ht.1]
  apply (mul_lt_mul_iff_left₀ (Real.log_pos (by norm_num : (1 : ℝ) < 37))).mp
  rw [gain_37_1_identity]
  change _ < 1 / (L * Real.log L) * Real.log 37
  rw [one_div_mul_eq_div, lt_div_iff₀ hpos]
  nlinarith only [ht.2, hp.1, hs.1, hs.2]

private theorem supported_rows {p : ℕ} (hp : p ∈ support) :
    price L < goldenLayerMarginal p (exponent p) ∧
      goldenLayerMarginal p (exponent p + 1) < price L := by
  simp only [support, Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num [exponent]
  all_goals first | exact threshold_2 | exact threshold_3 | exact threshold_5 |
    exact threshold_7 | exact threshold_11 | exact threshold_13 | exact threshold_17 |
    exact threshold_19 | exact threshold_23 | exact threshold_29 | exact threshold_31

private theorem boundary_rows {p : ℕ} (hp : p.Prime) :
    goldenLayerMarginal p (witnessN.factorization p + 1) < price L ∧
      (p ∣ witnessN → price L < goldenLayerMarginal p (witnessN.factorization p)) := by
  classical
  by_cases hm : p ∈ support
  · rw [factorization_N]
    exact ⟨(supported_rows hm).2, fun _ => (supported_rows hm).1⟩
  · have hfac : witnessN.factorization p = 0 := by
      apply Nat.factorization_eq_zero_of_not_dvd
      intro hd
      exact hm (support_N ▸ hp.mem_primeFactors hd (by norm_num [witnessN]))
    have hge := omitted_ge hp hm
    have hμ : goldenLayerMarginal p 1 ≤ goldenLayerMarginal 37 1 := by
      rcases eq_or_lt_of_le hge with rfl | hlt
      · exact le_rfl
      · exact
          (golden_layer_marginal_one_strictAnti
          (by norm_num : Nat.Prime 37) hp hlt).le
    refine ⟨by simpa [hfac] using hμ.trans_lt tail_threshold, ?_⟩
    intro hd
    exact (hm (support_N ▸ hp.mem_primeFactors hd (by norm_num [witnessN]))).elim

private theorem all_layers {p k : ℕ} (hp : p.Prime) (hk : 1 ≤ k) :
    (k ≤ witnessN.factorization p → price L < goldenLayerMarginal p k) ∧
      (witnessN.factorization p < k → goldenLayerMarginal p k < price L) := by
  have hb := boundary_rows hp
  constructor
  · intro he
    have hd : p ∣ witnessN := Nat.dvd_of_factorization_pos (by omega)
    have hl := hb.2 hd
    rcases eq_or_lt_of_le he with rfl | hlt
    · exact hl
    · exact hl.trans (golden_layer_strict_decrease hp hk hlt)
  · intro he
    rcases eq_or_lt_of_le (show witnessN.factorization p + 1 ≤ k by omega) with heq | hlt
    · simpa [← heq] using hb.1
    · exact (golden_layer_strict_decrease hp (by omega) hlt).trans hb.1

private theorem no_ties (p k : ℕ) (hp : p.Prime) (hk : 1 ≤ k) :
    price L ≠ goldenLayerMarginal p k := by
  by_cases he : k ≤ witnessN.factorization p
  · exact (all_layers hp hk).1 he |>.ne
  · exact ((all_layers hp hk).2 (by omega)).ne'

private theorem strict_identity : witnessN = strictInteger (price L) := by
  have hpos : strictInteger (price L) ≠ 0 := by
    have := strictInteger_pos price_positive
    omega
  apply Nat.factorization_inj (by norm_num [witnessN]) hpos
  ext p
  by_cases hp : p.Prime
  · apply le_antisymm
    · by_cases hz : witnessN.factorization p = 0
      · simp [hz]
      · exact (strict_layer_iff price_positive hp (by omega)).mpr
          ((all_layers hp (by omega)).1 le_rfl)
    · by_cases hz : (strictInteger (price L)).factorization p = 0
      · simp [hz]
      · have ha := (strict_layer_iff price_positive hp (by omega)).mp (le_refl ((strictInteger
          (price L)).factorization p))
        by_contra h
        have hb := (all_layers (k := (strictInteger (price L)).factorization p) hp (by omega)).2
            (by omega)
        linarith
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

private theorem maximal_identity : witnessN = maximalInteger (price L) := by
  apply Nat.factorization_inj (by norm_num [witnessN]) (show maximalInteger (price L) ≠ 0 by
      have := (maximalInteger_spec price_positive).1; omega)
  ext p
  by_cases hp : p.Prime
  · apply le_antisymm
    · by_cases hz : witnessN.factorization p = 0
      · simp [hz]
      · exact (weak_layer_iff price_positive hp (by omega)).mpr
          (((all_layers hp (by omega)).1 le_rfl).le)
    · by_cases hz : (maximalInteger (price L)).factorization p = 0
      · simp [hz]
      · have ha := (weak_layer_iff price_positive hp (by omega)).mp (le_refl ((maximalInteger
          (price L)).factorization p))
        by_contra h
        have hb := (all_layers (k := (maximalInteger (price L)).factorization p) hp (by
            omega)).2 (by omega)
        linarith
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

private theorem own_optimal : IsGoldenResourceOptimal (price L) witnessN := by
  apply (golden_resource_optimal_iff_layer_thresholds price_positive (by norm_num [witnessN])).mpr
  exact ⟨fun p hp => (boundary_rows hp).1.le, fun p hp hd => ((boundary_rows hp).2 hd).le⟩

private theorem unique_optimal {m : ℕ} (hm : 1 ≤ m)
    (hopt : IsGoldenResourceOptimal (price L) m) : m = witnessN := by
  have hmrows := (golden_resource_optimal_iff_layer_thresholds price_positive hm).mp hopt
  apply Nat.factorization_inj (show m ≠ 0 by omega) (by norm_num [witnessN])
  ext p
  by_cases hp : p.Prime
  · apply le_antisymm
    · by_contra h
      have hgt : witnessN.factorization p < m.factorization p := by omega
      have hd := Nat.dvd_of_factorization_pos (by omega : m.factorization p ≠ 0)
      have ha := hmrows.2 p hp hd
      have hb := (all_layers hp (by omega)).2 hgt
      linarith
    · by_contra h
      have hgt : m.factorization p + 1 ≤ witnessN.factorization p := by omega
      have ha := hmrows.1 p hp
      have hb := (all_layers hp (by omega)).1 hgt
      linarith
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

private theorem strict_optimizer (m : ℕ) (hm : 1 ≤ m) (hne : m ≠ witnessN) :
    goldenResourceObjective (price L) m < goldenResourceObjective (price L) witnessN := by
  have hle := own_optimal m hm
  by_contra hn
  have he : goldenResourceObjective (price L) m = goldenResourceObjective (price L) witnessN :=
      by linarith
  have ho : IsGoldenResourceOptimal (price L) m := by
    intro k hk
    rw [he]
    exact own_optimal k hk
  exact hne (unique_optimal hm ho)

private theorem below_boundary : price L < boundaryPrice := by
  by_contra h
  have hd := strictInteger_dvd price_positive boundaryPrice_spec.1 (le_of_not_gt h)
  rw [← strict_identity] at hd
  have hlo := Nat.le_of_dvd (by have := strictInteger_pos boundaryPrice_spec.1; omega) hd
  have hhi := boundaryPrice_spec.2.1
  norm_num [witnessN] at hlo
  omega

private theorem gap32_x :
    ((17328679 / 5000000) : ℝ) < Real.log 32 ∧ Real.log 32 < (34657361 / 10000000) := by
  refine rational_log_bounds 32 1 _ _ 5 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

private theorem gap32_gain :
    ((61543 / 2000000) : ℝ) < Real.log (33 / 32) ∧ Real.log (33 / 32) < (153859 / 5000000) := by
  have hs := log_expansion_remainder_bound (y := ((33 / 32) : ℝ)) (by norm_num) (by norm_num) 8
  norm_num [logRemainder, atanhParameter, atanhPartial, Finset.sum_range_succ] at hs
  constructor <;> linarith only [hs.1, hs.2]

private theorem gap32_clock :
    ((15888477 / 500000) : ℝ) < L - Real.log (32 : ℝ) ∧ L - Real.log (32 : ℝ) < (158884773 /
        5000000) := by
  have hn := clock_bounds
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

private theorem gap32_log :
    ((8646853 / 2500000) : ℝ) < Real.log (L - Real.log (32 : ℝ)) ∧ Real.log (L - Real.log (32 :
        ℝ)) < (6917483 / 2000000) := by
  exact log_interval_bounds (by norm_num) (gap32_clock).1 (gap32_clock).2 extra_log_literal_0.1
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

private theorem gap32_f :
    ((6204523 / 5000000) : ℝ) < Real.log (Real.log (L - Real.log (32 : ℝ))) ∧ Real.log (Real.log
        (L - Real.log (32 : ℝ))) < (12409049 / 10000000) := by
  exact log_interval_bounds (by norm_num) (gap32_log).1 (gap32_log).2 extra_log_literal_2.1
      extra_log_literal_3.2

private theorem gap369_x :
    ((18041057 / 5000000) : ℝ) < Real.log (369 / 10) ∧ Real.log (369 / 10) < (36082117 /
        10000000) := by
  refine rational_log_bounds (369 / 10) (369 / 320) _ _ 5 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

private theorem gap369_gain :
    ((133697 / 5000000) : ℝ) < Real.log (379 / 369) ∧ Real.log (379 / 369) < (267397 / 10000000)
        := by
  have hs := log_expansion_remainder_bound (y := ((379 / 369) : ℝ)) (by norm_num) (by norm_num) 8
  norm_num [logRemainder, atanhParameter, atanhPartial, Finset.sum_range_succ] at hs
  constructor <;> linarith only [hs.1, hs.2]

private theorem gap369_clock :
    ((77701803 / 2000000) : ℝ) < L + Real.log ((369 / 10) : ℝ) ∧ L + Real.log ((369 / 10) : ℝ) <
        (388509021 / 10000000) := by
  have hn := clock_bounds
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

private theorem gap369_log :
    ((36597311 / 10000000) : ℝ) < Real.log (L + Real.log ((369 / 10) : ℝ)) ∧ Real.log (L +
        Real.log ((369 / 10) : ℝ)) < (18298657 / 5000000) := by
  exact log_interval_bounds (by norm_num) (gap369_clock).1 (gap369_clock).2
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

private theorem gap369_f :
    ((2594779 / 2000000) : ℝ) < Real.log (Real.log (L + Real.log ((369 / 10) : ℝ))) ∧ Real.log
        (Real.log (L + Real.log ((369 / 10) : ℝ))) < (12973899 / 10000000) := by
  exact log_interval_bounds (by norm_num) (gap369_log).1 (gap369_log).2 extra_log_literal_6.1
      extra_log_literal_7.2

private theorem W_step {n p : ℕ} (hn : 1 ≤ n) (hp : p.Prime) :
    W (n * p) - W n = goldenLayerMarginal p (n.factorization p + 1) * Real.log p := by
  have hd := golden_resource_objective_single_layer_delta 0 hn hp
  rw [golden_resource_sigma_identity 0 (by nlinarith [hp.one_lt] : 1 ≤ n * p),
    golden_resource_sigma_identity 0 hn] at hd
  simpa only [W, zero_mul, sub_zero] using hd

private theorem strict_insertion {x : ℝ} (hx : 1 < x)
    (hb : 0 < insertionBarrier L x) :
    Real.log (1 + 1 / x) < f (L + Real.log x) - f L := by
  have hL : 1 < L := by have := positive_clock; linarith
  have hL0 : 0 < L := by linarith
  have hx0 : 0 < x := by linarith
  have hlx := Real.log_pos hx
  have hy : 1 < L + Real.log x := by linarith
  have hc : 0 < 1 + 1 / x := by positivity
  change Real.log (1 + 1 / x) < Real.log (Real.log (L + Real.log x)) - Real.log (Real.log L)
  rw [← Real.log_div (Real.log_pos hy).ne' (Real.log_pos hL).ne',
    Real.log_lt_log_iff hc (div_pos (Real.log_pos hy) (Real.log_pos hL)),
    lt_div_iff₀ (Real.log_pos hL)]
  rw [← Real.log_rpow hL0,
    Real.log_lt_log_iff (Real.rpow_pos_of_pos hL0 _) (by linarith : 0 < L + Real.log x)]
  dsimp [insertionBarrier] at hb
  linarith only [hb]

private theorem barrier_slack : 0 < deletionBarrier L 31 ∧ 0 < insertionBarrier L 37 := by
  have hL : 1 < L := by have := positive_clock; linarith
  have h32 : 0 ≤ deletionBarrier L 32 := by
    apply (deletion_test hL (by norm_num) (by have := gap32_clock.1; linarith)).mpr
    have hf := f_clock_bounds
    have hg := gap32_gain
    have hc := gap32_f
    norm_num at hg ⊢
    linarith only [hf.2, hg.1, hc.1]
  have h369 : 0 ≤ insertionBarrier L (369 / 10) := by
    apply (insertion_test hL (by norm_num)).mpr
    have hf := f_clock_bounds
    have hg := gap369_gain
    have hc := gap369_f
    norm_num at hg ⊢
    linarith only [hf.2, hg.2, hc.1]
  constructor
  · have hm := deletion_strictAnti hL (by norm_num : (31 : ℝ) ∈ Set.Ioi 1)
      (by norm_num : (32 : ℝ) ∈ Set.Ioi 1) (by norm_num : (31 : ℝ) < 32)
    linarith
  · have hm := insertion_strictMono hL (by norm_num : (369 / 10 : ℝ) ∈ Set.Ioi 1)
      (by norm_num : (37 : ℝ) ∈ Set.Ioi 1) (by norm_num : (369 / 10 : ℝ) < 37)
    linarith

private theorem actual_steps_2 :
    f L - f (L - Real.log 2) < goldenLayerMarginal 2 6 * Real.log 2 ∧
      goldenLayerMarginal 2 7 * Real.log 2 < f (L + Real.log 2) - f L := by
  rw [gain_2_6_identity, gain_2_7_identity]
  have hf := f_clock_bounds
  have hd := delete_2_f
  have hi := insert_2_f
  have he := gain_2_6_bounds
  have hn := gain_2_7_bounds
  constructor <;> linarith only [hf.1, hf.2, hd.1, hi.1, he.1, hn.2]

private theorem actual_steps_3 :
    f L - f (L - Real.log 3) < goldenLayerMarginal 3 3 * Real.log 3 ∧
      goldenLayerMarginal 3 4 * Real.log 3 < f (L + Real.log 3) - f L := by
  rw [gain_3_3_identity, gain_3_4_identity]
  have hf := f_clock_bounds
  have hd := delete_3_f
  have hi := insert_3_f
  have he := gain_3_3_bounds
  have hn := gain_3_4_bounds
  constructor <;> linarith only [hf.1, hf.2, hd.1, hi.1, he.1, hn.2]

private theorem actual_steps_5 :
    f L - f (L - Real.log 5) < goldenLayerMarginal 5 2 * Real.log 5 ∧
      goldenLayerMarginal 5 3 * Real.log 5 < f (L + Real.log 5) - f L := by
  rw [gain_5_2_identity, gain_5_3_identity]
  have hf := f_clock_bounds
  have hd := delete_5_f
  have hi := insert_5_f
  have he := gain_5_2_bounds
  have hn := gain_5_3_bounds
  constructor <;> linarith only [hf.1, hf.2, hd.1, hi.1, he.1, hn.2]

private theorem actual_steps_7 :
    f L - f (L - Real.log 7) < goldenLayerMarginal 7 2 * Real.log 7 ∧
      goldenLayerMarginal 7 3 * Real.log 7 < f (L + Real.log 7) - f L := by
  rw [gain_7_2_identity, gain_7_3_identity]
  have hf := f_clock_bounds
  have hd := delete_7_f
  have hi := insert_7_f
  have he := gain_7_2_bounds
  have hn := gain_7_3_bounds
  constructor <;> linarith only [hf.1, hf.2, hd.1, hi.1, he.1, hn.2]

private theorem actual_steps_11 :
    f L - f (L - Real.log 11) < goldenLayerMarginal 11 1 * Real.log 11 ∧
      goldenLayerMarginal 11 2 * Real.log 11 < f (L + Real.log 11) - f L := by
  rw [gain_11_1_identity, gain_11_2_identity]
  have hf := f_clock_bounds
  have hd := delete_11_f
  have hi := insert_11_f
  have he := gain_11_1_bounds
  have hn := gain_11_2_bounds
  constructor <;> linarith only [hf.1, hf.2, hd.1, hi.1, he.1, hn.2]

private theorem actual_steps_13 :
    f L - f (L - Real.log 13) < goldenLayerMarginal 13 1 * Real.log 13 ∧
      goldenLayerMarginal 13 2 * Real.log 13 < f (L + Real.log 13) - f L := by
  rw [gain_13_1_identity, gain_13_2_identity]
  have hf := f_clock_bounds
  have hd := delete_13_f
  have hi := insert_13_f
  have he := gain_13_1_bounds
  have hn := gain_13_2_bounds
  constructor <;> linarith only [hf.1, hf.2, hd.1, hi.1, he.1, hn.2]

private theorem actual_steps_17 :
    f L - f (L - Real.log 17) < goldenLayerMarginal 17 1 * Real.log 17 ∧
      goldenLayerMarginal 17 2 * Real.log 17 < f (L + Real.log 17) - f L := by
  rw [gain_17_1_identity, gain_17_2_identity]
  have hf := f_clock_bounds
  have hd := delete_17_f
  have hi := insert_17_f
  have he := gain_17_1_bounds
  have hn := gain_17_2_bounds
  constructor <;> linarith only [hf.1, hf.2, hd.1, hi.1, he.1, hn.2]

private theorem actual_steps_19 :
    f L - f (L - Real.log 19) < goldenLayerMarginal 19 1 * Real.log 19 ∧
      goldenLayerMarginal 19 2 * Real.log 19 < f (L + Real.log 19) - f L := by
  rw [gain_19_1_identity, gain_19_2_identity]
  have hf := f_clock_bounds
  have hd := delete_19_f
  have hi := insert_19_f
  have he := gain_19_1_bounds
  have hn := gain_19_2_bounds
  constructor <;> linarith only [hf.1, hf.2, hd.1, hi.1, he.1, hn.2]

private theorem actual_steps_23 :
    f L - f (L - Real.log 23) < goldenLayerMarginal 23 1 * Real.log 23 ∧
      goldenLayerMarginal 23 2 * Real.log 23 < f (L + Real.log 23) - f L := by
  rw [gain_23_1_identity, gain_23_2_identity]
  have hf := f_clock_bounds
  have hd := delete_23_f
  have hi := insert_23_f
  have he := gain_23_1_bounds
  have hn := gain_23_2_bounds
  constructor <;> linarith only [hf.1, hf.2, hd.1, hi.1, he.1, hn.2]

private theorem actual_steps_29 :
    f L - f (L - Real.log 29) < goldenLayerMarginal 29 1 * Real.log 29 ∧
      goldenLayerMarginal 29 2 * Real.log 29 < f (L + Real.log 29) - f L := by
  rw [gain_29_1_identity, gain_29_2_identity]
  have hf := f_clock_bounds
  have hd := delete_29_f
  have hi := insert_29_f
  have he := gain_29_1_bounds
  have hn := gain_29_2_bounds
  constructor <;> linarith only [hf.1, hf.2, hd.1, hi.1, he.1, hn.2]

private theorem actual_steps_31 :
    f L - f (L - Real.log 31) < goldenLayerMarginal 31 1 * Real.log 31 ∧
      goldenLayerMarginal 31 2 * Real.log 31 < f (L + Real.log 31) - f L := by
  rw [gain_31_1_identity, gain_31_2_identity]
  have hf := f_clock_bounds
  have hd := delete_31_f
  have hi := insert_31_f
  have he := gain_31_1_bounds
  have hn := gain_31_2_bounds
  constructor <;> linarith only [hf.1, hf.2, hd.1, hi.1, he.1, hn.2]

private theorem supported_step_slacks {p : ℕ} (hp : p ∈ support) :
    f L - f (L - Real.log p) < goldenLayerMarginal p (witnessN.factorization p) * Real.log p ∧
      goldenLayerMarginal p (witnessN.factorization p + 1) * Real.log p < f (L + Real.log p) - f
          L := by
  rw [factorization_N]
  simp only [support, Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num [exponent]
  all_goals first | exact actual_steps_2 | exact actual_steps_3 | exact actual_steps_5 |
    exact actual_steps_7 | exact actual_steps_11 | exact actual_steps_13 | exact actual_steps_17 |
    exact actual_steps_19 | exact actual_steps_23 | exact actual_steps_29 | exact actual_steps_31

private theorem deletion_comparisons (p : ℕ) (hp : p.Prime) (hd : p ∣ witnessN) :
    5040 < witnessN / p ∧ robinLogMargin witnessN < robinLogMargin (witnessN / p) := by
  have hm : p ∈ support := support_N ▸ hp.mem_primeFactors hd (by norm_num [witnessN])
  have hc := actual_cofactor hm
  have heq : witnessN / p * p = witnessN := Nat.div_mul_cancel hd
  have hfac : (witnessN / p).factorization p + 1 = witnessN.factorization p := by
    have hh := congrArg (fun m : ℕ => m.factorization p) heq
    simp only [Nat.factorization_mul (by omega : witnessN / p ≠ 0) hp.ne_zero,
      Finsupp.coe_add, Pi.add_apply, hp.factorization, Finsupp.single_eq_same] at hh
    exact hh
  have hw := W_step (by omega : 1 ≤ witnessN / p) hp
  rw [heq, hfac] at hw
  have hclock : Real.log (witnessN / p : ℕ) = L - Real.log p := by
    have hh := congrArg (fun n : ℕ => Real.log (n : ℝ)) heq
    rw [Nat.cast_mul, Real.log_mul (Nat.cast_pos.mpr (by omega : 0 < witnessN / p)).ne'
      (Nat.cast_pos.mpr hp.pos).ne'] at hh
    change _ = Real.log (witnessN : ℝ) - Real.log p
    linarith only [hh]
  refine ⟨hc, ?_⟩
  have hs := (supported_step_slacks hm).1
  rw [margin_eq_threshold_sub_W, margin_eq_threshold_sub_W, hclock]
  change Real.eulerMascheroniConstant + f L - W witnessN <
    Real.eulerMascheroniConstant + f (L - Real.log p) - W (witnessN / p)
  linarith only [hw, hs]

private theorem insertion_comparisons (p : ℕ) (hp : p.Prime) :
    robinLogMargin witnessN < robinLogMargin (witnessN * p) := by
  classical
  have hw := W_step (by norm_num [witnessN] : 1 ≤ witnessN) hp
  have hclock : Real.log (witnessN * p : ℕ) = L + Real.log p := by
    rw [Nat.cast_mul, Real.log_mul (by norm_num [witnessN]) (Nat.cast_pos.mpr hp.pos).ne']
  have hs : goldenLayerMarginal p (witnessN.factorization p + 1) * Real.log p <
      f (L + Real.log p) - f L := by
    by_cases hm : p ∈ support
    · exact (supported_step_slacks hm).2
    · have hge := omitted_ge hp hm
      have hreal : (37 : ℝ) ≤ p := by exact_mod_cast hge
      have hbp : 0 < insertionBarrier L p := by
        have hm := (insertion_strictMono (by have := positive_clock; linarith)).monotoneOn
          (by norm_num : (37 : ℝ) ∈ Set.Ioi 1)
          (by change (1 : ℝ) < p; exact_mod_cast hp.one_lt) hreal
        exact barrier_slack.2.trans_le hm
      have hf : witnessN.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd (by
        intro hd; exact hm (support_N ▸ hp.mem_primeFactors hd (by norm_num [witnessN])))
      rw [hf, zero_add, golden_layer_marginal_one_eq_log_one_add_inv hp,
        div_mul_cancel₀ _ hp.log_pos.ne']
      exact strict_insertion (by exact_mod_cast hp.one_lt) hbp
  rw [margin_eq_threshold_sub_W, margin_eq_threshold_sub_W, hclock]
  change Real.eulerMascheroniConstant + f L - W witnessN <
    Real.eulerMascheroniConstant + f (L + Real.log p) - W (witnessN * p)
  linarith only [hw, hs]

private theorem cutoff_bracket : price L < firstLayerPrice 34 ∧ firstLayerPrice 35 < price L := by
  have ht := clock_product
  have hpos : 0 < L * Real.log L := by linarith only [ht.1]
  constructor
  · have hp := log_prime_34
    have hg := gain_34_1_bounds
    change 1 / (L * Real.log L) < Real.log (1 + 1 / (34 : ℝ)) / Real.log 34
    apply (div_lt_div_iff₀ hpos (Real.log_pos (by norm_num : (1 : ℝ) < 34))).mpr
    norm_num at hg ⊢
    nlinarith only [ht.1, hp.2, hg.1]
  · have hp := log_prime_35
    have hg := gain_35_1_bounds
    change Real.log (1 + 1 / (35 : ℝ)) / Real.log 35 < 1 / (L * Real.log L)
    apply (div_lt_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 35)) hpos).mpr
    norm_num at hg ⊢
    nlinarith only [ht.2, hp.1, hg.1, hg.2]

private theorem same_cutoff_gap :
    ∃ z α β : ℝ, 11 < z ∧ 0 < L - z ∧ L - z < 1 / 2 ∧
      firstLayerPrice z = price L ∧
      (∀ t : ℝ, 1 < t → firstLayerPrice t = price L → t = z) ∧
      34 < z ∧ z < 35 ∧ ⌊z⌋₊ = 34 ∧
      witnessN.primeFactors = Nat.primesLE ⌊z⌋₊ ∧
      NonlinearPrimeGap witnessN z α β ∧ 31 < α ∧ β < 37 := by
  obtain ⟨z, hz, hzl, hhalf, hroot, hu⟩ := half_shift_cutoff (by have := positive_clock; linarith)
  have hz1 : 1 < z := by linarith
  have hz34 : 34 < z := by
    by_contra hn
    have hm := firstLayerPrice_strictAnti.antitoneOn hz1 (by norm_num : (1 : ℝ) < 34)
        (le_of_not_gt hn)
    rw [hroot] at hm
    linarith only [hm, cutoff_bracket.1]
  have hz35 : z < 35 := by
    by_contra hn
    have hm := firstLayerPrice_strictAnti.antitoneOn (by norm_num : (1 : ℝ) < 35) hz1
        (le_of_not_gt hn)
    rw [hroot] at hm
    linarith only [hm, cutoff_bracket.2]
  have hfloor : ⌊z⌋₊ = 34 := by
    apply (Nat.floor_eq_iff (by linarith : 0 ≤ z)).mpr
    constructor
    · exact hz34.le
    · norm_num
      exact hz35
  have hL1 : 1 < L := by have := positive_clock; linarith
  obtain ⟨α, β, hαlo, hαz, hLβ, hα, hβ, huα, huβ⟩ :=
    barrier_roots positive_clock hz (by linarith only [hzl]) hhalf hroot
  have hα1 : 1 < α := by have := positive_clock; linarith
  have hβ1 : 1 < β := by have := positive_clock; linarith
  have h31 : 31 < α := by
    by_contra hn
    have hm := (deletion_strictAnti hL1).antitoneOn hα1 (by norm_num : (1 : ℝ) < 31)
        (le_of_not_gt hn)
    rw [hα] at hm
    linarith only [barrier_slack.1, hm]
  have h37 : β < 37 := by
    by_contra hn
    have hm := (insertion_strictMono hL1).monotoneOn (by norm_num : (1 : ℝ) < 37) hβ1
        (le_of_not_gt hn)
    rw [hβ] at hm
    linarith only [barrier_slack.2, hm]
  have hgap : NonlinearPrimeGap witnessN z α β := by
    refine ⟨hαlo, hαz, by linarith only [hzl], hLβ, hα, hβ, huα, huβ, ?_⟩
    intro p hp hap
    have hp31 : (31 : ℝ) < p := h31.trans hap
    have hpn : 31 < p := by exact_mod_cast hp31
    have hnot : p ∉ support := by
      simp only [support, Finset.mem_insert, Finset.mem_singleton]
      omega
    have hge : (37 : ℝ) ≤ p := by exact_mod_cast omitted_ge hp hnot
    exact h37.le.trans hge
  refine ⟨z, α, β, hz, hzl, hhalf, hroot, hu, hz34, hz35, hfloor, ?_, hgap, h31, h37⟩
  rw [hfloor, support_N, support_floor]

private theorem original_margins :
    0 < robinLogMargin witnessN ∧ 0 < robinLogMargin witnessM ∧
      robinLogMargin witnessM < robinLogMargin witnessN := by
  have hg := eulerMascheroni_decimal_bounds
  have hn := f_clock_bounds
  have hm := m_f_clock_bounds
  have hwn := w_N_bounds_raw
  have hwm := w_M_bounds_raw
  have hwNid : W witnessN = Real.log (70225920 / 11350339 : ℝ) := by
    unfold W
    rw [sigma_N]
    congr 1
    norm_num [witnessN]
  have hwMid : W witnessM = Real.log (3074209873920 / 451928782799 : ℝ) := by
    unfold W
    rw [sigma_M]
    congr 1
    norm_num [witnessM]
  rw [← hwNid] at hwn
  rw [← hwMid] at hwm
  have hwN := hwn
  have hwM := hwm
  rw [margin_eq_threshold_sub_W, margin_eq_threshold_sub_W]
  change 0 < Real.eulerMascheroniConstant + f L - W witnessN ∧
    0 < Real.eulerMascheroniConstant + f (Real.log (witnessM : ℝ)) - W witnessM ∧
    Real.eulerMascheroniConstant + f (Real.log (witnessM : ℝ)) - W witnessM <
      Real.eulerMascheroniConstant + f L - W witnessN
  change _ < f (Real.log (witnessM : ℝ)) ∧ f (Real.log (witnessM : ℝ)) < _ at hm
  constructor
  · linarith only [hg.1, hn.1, hwN.2]
  constructor
  · linarith only [hg.1, hm.1, hwM.2]
  · linarith only [hm.2, hn.1, hwN.2, hwM.1]

private theorem exact_products :
    witnessN = 2 ^ 6 * 3 ^ 3 * 5 ^ 2 * 7 ^ 2 * 11 * 13 * 17 * 19 * 23 * 29 * 31 ∧
      55440 < witnessN ∧ 55440 ∣ witnessN ∧
      (37 * 41 * 43 * 47 : ℕ) = 3065857 ∧
      witnessM = witnessN * (37 * 41 * 43 * 47) ∧
      (1 + 1 / (37 : ℝ)) * (1 + 1 / 41) * (1 + 1 / 43) * (1 + 1 / 47) = 3370752 / 3065857 ∧
      (∀ p ∈ ({37, 41, 43, 47} : Finset ℕ), p.Prime ∧ ¬p ∣ witnessN) := by
  norm_num [witnessN, witnessM]


/-- The complete original own-clock inventory and singleton bundle. It has no
Robin failure or global original-margin minimum hypothesis. -/
structure OwnClockInventorySingletons (n : ℕ) (z α β : ℝ) : Prop where
  large : 55440 < n
  base : 55440 ∣ n
  clock : 16 < Real.log (n : ℝ)
  log_factorization : Real.log (n : ℝ) =
    n.factorization.sum (fun p e => (e : ℝ) * Real.log p)
  price_positive : 0 < price (Real.log n)
  below_boundary : price (Real.log n) < boundaryPrice
  optimal : IsGoldenResourceOptimal (price (Real.log n)) n
  unique : ∀ m : ℕ, 1 ≤ m → m ≠ n →
    goldenResourceObjective (price (Real.log n)) m <
      goldenResourceObjective (price (Real.log n)) n
  strict_inventory : n = strictInteger (price (Real.log n))
  maximal_inventory : n = maximalInteger (price (Real.log n))
  layers : ∀ p k : ℕ, p.Prime → 1 ≤ k →
    (k ≤ n.factorization p → price (Real.log n) < goldenLayerMarginal p k) ∧
      (n.factorization p < k → goldenLayerMarginal p k < price (Real.log n))
  no_ties : ∀ p k : ℕ, p.Prime → 1 ≤ k →
    price (Real.log n) ≠ goldenLayerMarginal p k
  cutoff_large : 11 < z
  half_shift_lower : 0 < Real.log n - z
  half_shift_upper : Real.log n - z < 1 / 2
  root : firstLayerPrice z = 1 / (Real.log n * Real.log (Real.log n))
  cutoff_unique : ∀ t : ℝ, 1 < t →
    firstLayerPrice t = 1 / (Real.log n * Real.log (Real.log n)) → t = z
  support : n.primeFactors = Nat.primesLE ⌊z⌋₊
  gap : NonlinearPrimeGap n z α β
  positive_margin : 0 < robinLogMargin n
  deletion : ∀ p : ℕ, p.Prime → p ∣ n →
    5040 < n / p ∧ robinLogMargin n < robinLogMargin (n / p)
  insertion : ∀ p : ℕ, p.Prime → robinLogMargin n < robinLogMargin (n * p)

/-- The proposed replacement of all fresh finite-product comparisons by the
complete strict inventory, literal nonlinear gap, and actual singleton tests. -/
def inventory_singletons_imply_collective : Prop :=
  ∀ (n : ℕ) (z α β : ℝ), OwnClockInventorySingletons n z α β →
    ∀ s : Finset ℕ, (∀ p ∈ s, p.Prime ∧ ¬p ∣ n) →
      robinLogMargin n ≤ robinLogMargin (n * ∏ p ∈ s, p)

/-- Exact original-integer separator. All clocks, cutoffs, roots and valuation
layers belong to this same N. Both original margins are strictly positive. -/
theorem actual_witness :
    ∃ z α β : ℝ, OwnClockInventorySingletons witnessN z α β ∧
      34 < z ∧ z < 35 ∧ ⌊z⌋₊ = 34 ∧ 31 < α ∧ β < 37 ∧
      witnessN = 2 ^ 6 * 3 ^ 3 * 5 ^ 2 * 7 ^ 2 * 11 * 13 * 17 * 19 * 23 * 29 * 31 ∧
      (37 * 41 * 43 * 47 : ℕ) = 3065857 ∧
      witnessM = witnessN * (37 * 41 * 43 * 47) ∧
      (1 + 1 / (37 : ℝ)) * (1 + 1 / 41) * (1 + 1 / 43) * (1 + 1 / 47) =
        3370752 / 3065857 ∧
      (∀ p ∈ ({37, 41, 43, 47} : Finset ℕ), p.Prime ∧ ¬p ∣ witnessN) ∧
      0 < robinLogMargin witnessM ∧
      robinLogMargin witnessM < robinLogMargin witnessN := by
  obtain ⟨z, α, β, hz, hzl, hhalf, hroot, hu, hz34, hz35, hfloor, hsupp, hgap, h31, h37⟩ :=
    same_cutoff_gap
  obtain ⟨hfac, hlarge, hbase, hprod, hM, hgain, hfresh⟩ := exact_products
  have hb : OwnClockInventorySingletons witnessN z α β := {
    large := hlarge
    base := hbase
    clock := positive_clock
    log_factorization := Real.log_nat_eq_sum_factorization witnessN
    price_positive := price_positive
    below_boundary := below_boundary
    optimal := own_optimal
    unique := strict_optimizer
    strict_inventory := strict_identity
    maximal_inventory := maximal_identity
    layers := fun p k hp hk => all_layers hp hk
    no_ties := no_ties
    cutoff_large := hz
    half_shift_lower := hzl
    half_shift_upper := hhalf
    root := hroot
    cutoff_unique := hu
    support := hsupp
    gap := hgap
    positive_margin := original_margins.1
    deletion := deletion_comparisons
    insertion := insertion_comparisons }
  exact ⟨z, α, β, hb, hz34, hz35, hfloor, h31, h37, hfac, hprod, hM, hgain, hfresh,
    original_margins.2.1, original_margins.2.2⟩

/-- Full inventory and every actual prime singleton comparison do not imply
all collective fresh-prime comparisons for the original Robin margin. -/
theorem result : ¬ inventory_singletons_imply_collective := by
  intro h
  obtain ⟨z, α, β, hb, _, _, _, _, _, _, _, hM, _, hfresh, _, himprove⟩ := actual_witness
  have hcomp := h witnessN z α β hb {37, 41, 43, 47} hfresh
  have hprod : (∏ p ∈ ({37, 41, 43, 47} : Finset ℕ), p) = 37 * 41 * 43 * 47 := by norm_num
  rw [hprod, ← hM] at hcomp
  exact (not_lt_of_ge hcomp) himprove

#print axioms actual_witness
#print axioms result

end D5.S3.Arith.Robin.PriceRecord.ActualInventoryCollectiveSeparation
