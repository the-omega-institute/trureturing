/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover228
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem unmarked_context_12_75354_560797 : frontier 9 ⟨560797, by decide⟩
    (prefixCache 12 75354) (prefixPartial 12 75354) = false := by
  decide +kernel

theorem node_context_12_75354_560797 : EJMOriginalGlobalDAGData.nodes 9 ⟨560797, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨560697, by decide⟩,⟨560757, by decide⟩,⟨560796, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75354_560797 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75354 ⟨560797, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75354
    ⟨560797, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨560697, by decide⟩,⟨560757, by decide⟩,⟨560796, by decide⟩]) unmarked_context_12_75354_560797 node_context_12_75354_560797
  intro a
  fin_cases a
  · exact context_13_301416_3444
  · exact context_13_301417_560697
  · exact context_13_301418_560757
  · exact context_13_301419_560796

theorem selected_cut_21988 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 301420) = some ⟨13, 1, 0, 3444, 301420, 1, 16384⟩ := by
  decide +kernel

theorem context_13_301420_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301420 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 301420 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 301420, 1, 16384⟩
    (by decide) selected_cut_21988

theorem selected_cut_21989 : selected 8 ⟨560817, by decide⟩
    (prefixPartial 13 301421) = some ⟨13, 2, 0, 560817, 301421, 1625, 16384⟩ := by
  decide +kernel

theorem context_13_301421_560817 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301421 ⟨560817, by decide⟩ :=
  accepted_of_selected 13 301421 ⟨560817, by decide⟩ ⟨13, 2, 0, 560817, 301421, 1625, 16384⟩
    (by decide) selected_cut_21989

theorem selected_cut_21990 : selected 8 ⟨560836, by decide⟩
    (prefixPartial 13 301422) = some ⟨13, 2, 0, 560836, 301422, 1965, 16384⟩ := by
  decide +kernel

theorem context_13_301422_560836 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301422 ⟨560836, by decide⟩ :=
  accepted_of_selected 13 301422 ⟨560836, by decide⟩ ⟨13, 2, 0, 560836, 301422, 1965, 16384⟩
    (by decide) selected_cut_21990

theorem selected_cut_21991 : selected 8 ⟨560842, by decide⟩
    (prefixPartial 13 301423) = some ⟨13, 2, 0, 560842, 301423, 881, 16384⟩ := by
  decide +kernel

theorem context_13_301423_560842 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301423 ⟨560842, by decide⟩ :=
  accepted_of_selected 13 301423 ⟨560842, by decide⟩ ⟨13, 2, 0, 560842, 301423, 881, 16384⟩
    (by decide) selected_cut_21991

theorem unmarked_context_12_75355_560843 : frontier 9 ⟨560843, by decide⟩
    (prefixCache 12 75355) (prefixPartial 12 75355) = false := by
  decide +kernel

theorem node_context_12_75355_560843 : EJMOriginalGlobalDAGData.nodes 9 ⟨560843, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨560817, by decide⟩,⟨560836, by decide⟩,⟨560842, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75355_560843 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75355 ⟨560843, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75355
    ⟨560843, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨560817, by decide⟩,⟨560836, by decide⟩,⟨560842, by decide⟩]) unmarked_context_12_75355_560843 node_context_12_75355_560843
  intro a
  fin_cases a
  · exact context_13_301420_3444
  · exact context_13_301421_560817
  · exact context_13_301422_560836
  · exact context_13_301423_560842

theorem unmarked_context_11_18838_560844 : frontier 10 ⟨560844, by decide⟩
    (prefixCache 11 18838) (prefixPartial 11 18838) = false := by
  decide +kernel

theorem node_context_11_18838_560844 : EJMOriginalGlobalDAGData.nodes 10 ⟨560844, by decide⟩ =
    .split (coordinate 11) (![⟨560623, by decide⟩,⟨560663, by decide⟩,⟨560797, by decide⟩,⟨560843, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18838_560844 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18838 ⟨560844, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18838
    ⟨560844, by decide⟩ (by decide) (![⟨560623, by decide⟩,⟨560663, by decide⟩,⟨560797, by decide⟩,⟨560843, by decide⟩]) unmarked_context_11_18838_560844 node_context_11_18838_560844
  intro a
  fin_cases a
  · exact context_12_75352_560623
  · exact context_12_75353_560663
  · exact context_12_75354_560797
  · exact context_12_75355_560843

theorem selected_cut_21992 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 301424) = some ⟨13, 1, 0, 3444, 301424, 1, 16384⟩ := by
  decide +kernel

theorem context_13_301424_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301424 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 301424 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 301424, 1, 16384⟩
    (by decide) selected_cut_21992

theorem selected_cut_21993 : selected 8 ⟨560856, by decide⟩
    (prefixPartial 13 301425) = some ⟨13, 2, 0, 560856, 301425, 1393, 16384⟩ := by
  decide +kernel

theorem context_13_301425_560856 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301425 ⟨560856, by decide⟩ :=
  accepted_of_selected 13 301425 ⟨560856, by decide⟩ ⟨13, 2, 0, 560856, 301425, 1393, 16384⟩
    (by decide) selected_cut_21993

theorem selected_cut_21994 : selected 8 ⟨560884, by decide⟩
    (prefixPartial 13 301426) = some ⟨13, 2, 0, 560884, 301426, 1889, 16384⟩ := by
  decide +kernel

theorem context_13_301426_560884 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301426 ⟨560884, by decide⟩ :=
  accepted_of_selected 13 301426 ⟨560884, by decide⟩ ⟨13, 2, 0, 560884, 301426, 1889, 16384⟩
    (by decide) selected_cut_21994

theorem selected_cut_21995 : selected 8 ⟨560890, by decide⟩
    (prefixPartial 13 301427) = some ⟨13, 2, 0, 560890, 301427, 893, 16384⟩ := by
  decide +kernel

theorem context_13_301427_560890 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301427 ⟨560890, by decide⟩ :=
  accepted_of_selected 13 301427 ⟨560890, by decide⟩ ⟨13, 2, 0, 560890, 301427, 893, 16384⟩
    (by decide) selected_cut_21995

theorem unmarked_context_12_75356_560891 : frontier 9 ⟨560891, by decide⟩
    (prefixCache 12 75356) (prefixPartial 12 75356) = false := by
  decide +kernel

theorem node_context_12_75356_560891 : EJMOriginalGlobalDAGData.nodes 9 ⟨560891, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨560856, by decide⟩,⟨560884, by decide⟩,⟨560890, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75356_560891 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75356 ⟨560891, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75356
    ⟨560891, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨560856, by decide⟩,⟨560884, by decide⟩,⟨560890, by decide⟩]) unmarked_context_12_75356_560891 node_context_12_75356_560891
  intro a
  fin_cases a
  · exact context_13_301424_3444
  · exact context_13_301425_560856
  · exact context_13_301426_560884
  · exact context_13_301427_560890

theorem selected_cut_21996 : selected 9 ⟨560931, by decide⟩
    (prefixPartial 12 75357) = some ⟨12, 2, 0, 560931, 75357, 3865, 65536⟩ := by
  decide +kernel

theorem context_12_75357_560931 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75357 ⟨560931, by decide⟩ :=
  accepted_of_selected 12 75357 ⟨560931, by decide⟩ ⟨12, 2, 0, 560931, 75357, 3865, 65536⟩
    (by decide) selected_cut_21996

theorem selected_cut_21997 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 301432) = some ⟨13, 1, 0, 3444, 301432, 1, 16384⟩ := by
  decide +kernel

theorem context_13_301432_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301432 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 301432 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 301432, 1, 16384⟩
    (by decide) selected_cut_21997

theorem selected_cut_21998 : selected 8 ⟨560946, by decide⟩
    (prefixPartial 13 301433) = some ⟨13, 2, 0, 560946, 301433, 1525, 16384⟩ := by
  decide +kernel

theorem context_13_301433_560946 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301433 ⟨560946, by decide⟩ :=
  accepted_of_selected 13 301433 ⟨560946, by decide⟩ ⟨13, 2, 0, 560946, 301433, 1525, 16384⟩
    (by decide) selected_cut_21998

theorem selected_cut_21999 : selected 8 ⟨560970, by decide⟩
    (prefixPartial 13 301434) = some ⟨13, 2, 0, 560970, 301434, 1869, 16384⟩ := by
  decide +kernel

theorem context_13_301434_560970 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301434 ⟨560970, by decide⟩ :=
  accepted_of_selected 13 301434 ⟨560970, by decide⟩ ⟨13, 2, 0, 560970, 301434, 1869, 16384⟩
    (by decide) selected_cut_21999

theorem selected_cut_22000 : selected 8 ⟨560982, by decide⟩
    (prefixPartial 13 301435) = some ⟨13, 2, 0, 560982, 301435, 981, 16384⟩ := by
  decide +kernel

theorem context_13_301435_560982 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301435 ⟨560982, by decide⟩ :=
  accepted_of_selected 13 301435 ⟨560982, by decide⟩ ⟨13, 2, 0, 560982, 301435, 981, 16384⟩
    (by decide) selected_cut_22000

theorem unmarked_context_12_75358_560983 : frontier 9 ⟨560983, by decide⟩
    (prefixCache 12 75358) (prefixPartial 12 75358) = false := by
  decide +kernel

theorem node_context_12_75358_560983 : EJMOriginalGlobalDAGData.nodes 9 ⟨560983, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨560946, by decide⟩,⟨560970, by decide⟩,⟨560982, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75358_560983 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75358 ⟨560983, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75358
    ⟨560983, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨560946, by decide⟩,⟨560970, by decide⟩,⟨560982, by decide⟩]) unmarked_context_12_75358_560983 node_context_12_75358_560983
  intro a
  fin_cases a
  · exact context_13_301432_3444
  · exact context_13_301433_560946
  · exact context_13_301434_560970
  · exact context_13_301435_560982

theorem selected_cut_22001 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 301436) = some ⟨13, 1, 0, 3444, 301436, 1, 16384⟩ := by
  decide +kernel

theorem context_13_301436_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301436 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 301436 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 301436, 1, 16384⟩
    (by decide) selected_cut_22001

theorem selected_cut_22002 : selected 8 ⟨561001, by decide⟩
    (prefixPartial 13 301437) = some ⟨13, 2, 0, 561001, 301437, 1629, 16384⟩ := by
  decide +kernel

theorem context_13_301437_561001 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301437 ⟨561001, by decide⟩ :=
  accepted_of_selected 13 301437 ⟨561001, by decide⟩ ⟨13, 2, 0, 561001, 301437, 1629, 16384⟩
    (by decide) selected_cut_22002

theorem selected_cut_22003 : selected 8 ⟨561026, by decide⟩
    (prefixPartial 13 301438) = some ⟨13, 2, 0, 561026, 301438, 2277, 16384⟩ := by
  decide +kernel

theorem context_13_301438_561026 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301438 ⟨561026, by decide⟩ :=
  accepted_of_selected 13 301438 ⟨561026, by decide⟩ ⟨13, 2, 0, 561026, 301438, 2277, 16384⟩
    (by decide) selected_cut_22003

theorem selected_cut_22004 : selected 8 ⟨561032, by decide⟩
    (prefixPartial 13 301439) = some ⟨13, 2, 0, 561032, 301439, 921, 16384⟩ := by
  decide +kernel

theorem context_13_301439_561032 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301439 ⟨561032, by decide⟩ :=
  accepted_of_selected 13 301439 ⟨561032, by decide⟩ ⟨13, 2, 0, 561032, 301439, 921, 16384⟩
    (by decide) selected_cut_22004

theorem unmarked_context_12_75359_561033 : frontier 9 ⟨561033, by decide⟩
    (prefixCache 12 75359) (prefixPartial 12 75359) = false := by
  decide +kernel

theorem node_context_12_75359_561033 : EJMOriginalGlobalDAGData.nodes 9 ⟨561033, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨561001, by decide⟩,⟨561026, by decide⟩,⟨561032, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75359_561033 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75359 ⟨561033, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75359
    ⟨561033, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨561001, by decide⟩,⟨561026, by decide⟩,⟨561032, by decide⟩]) unmarked_context_12_75359_561033 node_context_12_75359_561033
  intro a
  fin_cases a
  · exact context_13_301436_3444
  · exact context_13_301437_561001
  · exact context_13_301438_561026
  · exact context_13_301439_561032

theorem unmarked_context_11_18839_561034 : frontier 10 ⟨561034, by decide⟩
    (prefixCache 11 18839) (prefixPartial 11 18839) = false := by
  decide +kernel

theorem node_context_11_18839_561034 : EJMOriginalGlobalDAGData.nodes 10 ⟨561034, by decide⟩ =
    .split (coordinate 11) (![⟨560891, by decide⟩,⟨560931, by decide⟩,⟨560983, by decide⟩,⟨561033, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18839_561034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18839 ⟨561034, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18839
    ⟨561034, by decide⟩ (by decide) (![⟨560891, by decide⟩,⟨560931, by decide⟩,⟨560983, by decide⟩,⟨561033, by decide⟩]) unmarked_context_11_18839_561034 node_context_11_18839_561034
  intro a
  fin_cases a
  · exact context_12_75356_560891
  · exact context_12_75357_560931
  · exact context_12_75358_560983
  · exact context_12_75359_561033

theorem unmarked_context_10_4709_561035 : frontier 11 ⟨561035, by decide⟩
    (prefixCache 10 4709) (prefixPartial 10 4709) = false := by
  decide +kernel

theorem node_context_10_4709_561035 : EJMOriginalGlobalDAGData.nodes 11 ⟨561035, by decide⟩ =
    .split (coordinate 10) (![⟨560581, by decide⟩,⟨451541, by decide⟩,⟨560844, by decide⟩,⟨561034, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4709_561035 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4709 ⟨561035, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4709
    ⟨561035, by decide⟩ (by decide) (![⟨560581, by decide⟩,⟨451541, by decide⟩,⟨560844, by decide⟩,⟨561034, by decide⟩]) unmarked_context_10_4709_561035 node_context_10_4709_561035
  intro a
  fin_cases a
  · exact context_11_18836_560581
  · exact context_11_18837_451541
  · exact context_11_18838_560844
  · exact context_11_18839_561034

theorem selected_cut_22005 : selected 9 ⟨561075, by decide⟩
    (prefixPartial 12 75360) = some ⟨12, 2, 0, 561075, 75360, 3721, 65536⟩ := by
  decide +kernel

theorem context_12_75360_561075 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75360 ⟨561075, by decide⟩ :=
  accepted_of_selected 12 75360 ⟨561075, by decide⟩ ⟨12, 2, 0, 561075, 75360, 3721, 65536⟩
    (by decide) selected_cut_22005

theorem selected_cut_22006 : selected 9 ⟨561123, by decide⟩
    (prefixPartial 12 75361) = some ⟨12, 2, 0, 561123, 75361, 3917, 65536⟩ := by
  decide +kernel

theorem context_12_75361_561123 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75361 ⟨561123, by decide⟩ :=
  accepted_of_selected 12 75361 ⟨561123, by decide⟩ ⟨12, 2, 0, 561123, 75361, 3917, 65536⟩
    (by decide) selected_cut_22006

theorem selected_cut_22007 : selected 9 ⟨561168, by decide⟩
    (prefixPartial 12 75362) = some ⟨12, 2, 0, 561168, 75362, 3825, 65536⟩ := by
  decide +kernel

theorem context_12_75362_561168 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75362 ⟨561168, by decide⟩ :=
  accepted_of_selected 12 75362 ⟨561168, by decide⟩ ⟨12, 2, 0, 561168, 75362, 3825, 65536⟩
    (by decide) selected_cut_22007

theorem selected_cut_22008 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 301452) = some ⟨13, 1, 0, 3444, 301452, 1, 16384⟩ := by
  decide +kernel

theorem context_13_301452_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301452 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 301452 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 301452, 1, 16384⟩
    (by decide) selected_cut_22008

theorem selected_cut_22009 : selected 8 ⟨561194, by decide⟩
    (prefixPartial 13 301453) = some ⟨13, 2, 0, 561194, 301453, 1693, 16384⟩ := by
  decide +kernel

theorem context_13_301453_561194 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301453 ⟨561194, by decide⟩ :=
  accepted_of_selected 13 301453 ⟨561194, by decide⟩ ⟨13, 2, 0, 561194, 301453, 1693, 16384⟩
    (by decide) selected_cut_22009

theorem selected_cut_22010 : selected 8 ⟨561217, by decide⟩
    (prefixPartial 13 301454) = some ⟨13, 2, 0, 561217, 301454, 2001, 16384⟩ := by
  decide +kernel

theorem context_13_301454_561217 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301454 ⟨561217, by decide⟩ :=
  accepted_of_selected 13 301454 ⟨561217, by decide⟩ ⟨13, 2, 0, 561217, 301454, 2001, 16384⟩
    (by decide) selected_cut_22010

theorem selected_cut_22011 : selected 8 ⟨561222, by decide⟩
    (prefixPartial 13 301455) = some ⟨13, 2, 0, 561222, 301455, 709, 16384⟩ := by
  decide +kernel

theorem context_13_301455_561222 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301455 ⟨561222, by decide⟩ :=
  accepted_of_selected 13 301455 ⟨561222, by decide⟩ ⟨13, 2, 0, 561222, 301455, 709, 16384⟩
    (by decide) selected_cut_22011

theorem unmarked_context_12_75363_561223 : frontier 9 ⟨561223, by decide⟩
    (prefixCache 12 75363) (prefixPartial 12 75363) = false := by
  decide +kernel

theorem node_context_12_75363_561223 : EJMOriginalGlobalDAGData.nodes 9 ⟨561223, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨561194, by decide⟩,⟨561217, by decide⟩,⟨561222, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75363_561223 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75363 ⟨561223, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75363
    ⟨561223, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨561194, by decide⟩,⟨561217, by decide⟩,⟨561222, by decide⟩]) unmarked_context_12_75363_561223 node_context_12_75363_561223
  intro a
  fin_cases a
  · exact context_13_301452_3444
  · exact context_13_301453_561194
  · exact context_13_301454_561217
  · exact context_13_301455_561222

theorem unmarked_context_11_18840_561224 : frontier 10 ⟨561224, by decide⟩
    (prefixCache 11 18840) (prefixPartial 11 18840) = false := by
  decide +kernel

theorem node_context_11_18840_561224 : EJMOriginalGlobalDAGData.nodes 10 ⟨561224, by decide⟩ =
    .split (coordinate 11) (![⟨561075, by decide⟩,⟨561123, by decide⟩,⟨561168, by decide⟩,⟨561223, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18840_561224 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18840 ⟨561224, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18840
    ⟨561224, by decide⟩ (by decide) (![⟨561075, by decide⟩,⟨561123, by decide⟩,⟨561168, by decide⟩,⟨561223, by decide⟩]) unmarked_context_11_18840_561224 node_context_11_18840_561224
  intro a
  fin_cases a
  · exact context_12_75360_561075
  · exact context_12_75361_561123
  · exact context_12_75362_561168
  · exact context_12_75363_561223

theorem selected_cut_22012 : selected 9 ⟨561265, by decide⟩
    (prefixPartial 12 75364) = some ⟨12, 2, 0, 561265, 75364, 3829, 65536⟩ := by
  decide +kernel

theorem context_12_75364_561265 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75364 ⟨561265, by decide⟩ :=
  accepted_of_selected 12 75364 ⟨561265, by decide⟩ ⟨12, 2, 0, 561265, 75364, 3829, 65536⟩
    (by decide) selected_cut_22012

theorem selected_cut_22013 : selected 9 ⟨561314, by decide⟩
    (prefixPartial 12 75365) = some ⟨12, 2, 0, 561314, 75365, 3693, 65536⟩ := by
  decide +kernel

theorem context_12_75365_561314 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75365 ⟨561314, by decide⟩ :=
  accepted_of_selected 12 75365 ⟨561314, by decide⟩ ⟨12, 2, 0, 561314, 75365, 3693, 65536⟩
    (by decide) selected_cut_22013

theorem selected_cut_22014 : selected 9 ⟨561359, by decide⟩
    (prefixPartial 12 75366) = some ⟨12, 2, 0, 561359, 75366, 3917, 65536⟩ := by
  decide +kernel

theorem context_12_75366_561359 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75366 ⟨561359, by decide⟩ :=
  accepted_of_selected 12 75366 ⟨561359, by decide⟩ ⟨12, 2, 0, 561359, 75366, 3917, 65536⟩
    (by decide) selected_cut_22014

theorem selected_cut_22015 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 301468) = some ⟨13, 1, 0, 3444, 301468, 1, 16384⟩ := by
  decide +kernel

theorem context_13_301468_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301468 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 301468 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 301468, 1, 16384⟩
    (by decide) selected_cut_22015

theorem selected_cut_22016 : selected 8 ⟨561377, by decide⟩
    (prefixPartial 13 301469) = some ⟨13, 2, 0, 561377, 301469, 1325, 16384⟩ := by
  decide +kernel

theorem context_13_301469_561377 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301469 ⟨561377, by decide⟩ :=
  accepted_of_selected 13 301469 ⟨561377, by decide⟩ ⟨13, 2, 0, 561377, 301469, 1325, 16384⟩
    (by decide) selected_cut_22016

theorem selected_cut_22017 : selected 8 ⟨561405, by decide⟩
    (prefixPartial 13 301470) = some ⟨13, 2, 0, 561405, 301470, 2185, 16384⟩ := by
  decide +kernel

theorem context_13_301470_561405 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301470 ⟨561405, by decide⟩ :=
  accepted_of_selected 13 301470 ⟨561405, by decide⟩ ⟨13, 2, 0, 561405, 301470, 2185, 16384⟩
    (by decide) selected_cut_22017

theorem selected_cut_22018 : selected 8 ⟨561413, by decide⟩
    (prefixPartial 13 301471) = some ⟨13, 2, 0, 561413, 301471, 837, 16384⟩ := by
  decide +kernel

theorem context_13_301471_561413 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301471 ⟨561413, by decide⟩ :=
  accepted_of_selected 13 301471 ⟨561413, by decide⟩ ⟨13, 2, 0, 561413, 301471, 837, 16384⟩
    (by decide) selected_cut_22018

theorem unmarked_context_12_75367_561414 : frontier 9 ⟨561414, by decide⟩
    (prefixCache 12 75367) (prefixPartial 12 75367) = false := by
  decide +kernel

theorem node_context_12_75367_561414 : EJMOriginalGlobalDAGData.nodes 9 ⟨561414, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨561377, by decide⟩,⟨561405, by decide⟩,⟨561413, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75367_561414 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75367 ⟨561414, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75367
    ⟨561414, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨561377, by decide⟩,⟨561405, by decide⟩,⟨561413, by decide⟩]) unmarked_context_12_75367_561414 node_context_12_75367_561414
  intro a
  fin_cases a
  · exact context_13_301468_3444
  · exact context_13_301469_561377
  · exact context_13_301470_561405
  · exact context_13_301471_561413

theorem unmarked_context_11_18841_561415 : frontier 10 ⟨561415, by decide⟩
    (prefixCache 11 18841) (prefixPartial 11 18841) = false := by
  decide +kernel

theorem node_context_11_18841_561415 : EJMOriginalGlobalDAGData.nodes 10 ⟨561415, by decide⟩ =
    .split (coordinate 11) (![⟨561265, by decide⟩,⟨561314, by decide⟩,⟨561359, by decide⟩,⟨561414, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18841_561415 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18841 ⟨561415, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18841
    ⟨561415, by decide⟩ (by decide) (![⟨561265, by decide⟩,⟨561314, by decide⟩,⟨561359, by decide⟩,⟨561414, by decide⟩]) unmarked_context_11_18841_561415 node_context_11_18841_561415
  intro a
  fin_cases a
  · exact context_12_75364_561265
  · exact context_12_75365_561314
  · exact context_12_75366_561359
  · exact context_12_75367_561414

theorem selected_cut_22019 : selected 9 ⟨561454, by decide⟩
    (prefixPartial 12 75368) = some ⟨12, 2, 0, 561454, 75368, 3577, 65536⟩ := by
  decide +kernel

theorem context_12_75368_561454 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75368 ⟨561454, by decide⟩ :=
  accepted_of_selected 12 75368 ⟨561454, by decide⟩ ⟨12, 2, 0, 561454, 75368, 3577, 65536⟩
    (by decide) selected_cut_22019

theorem selected_cut_22020 : selected 9 ⟨561489, by decide⟩
    (prefixPartial 12 75369) = some ⟨12, 2, 0, 561489, 75369, 3541, 65536⟩ := by
  decide +kernel

theorem context_12_75369_561489 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75369 ⟨561489, by decide⟩ :=
  accepted_of_selected 12 75369 ⟨561489, by decide⟩ ⟨12, 2, 0, 561489, 75369, 3541, 65536⟩
    (by decide) selected_cut_22020

theorem selected_cut_22021 : selected 9 ⟨445248, by decide⟩
    (prefixPartial 12 75370) = some ⟨12, 1, 0, 445248, 75370, 1, 65536⟩ := by
  decide +kernel

theorem context_12_75370_445248 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75370 ⟨445248, by decide⟩ :=
  accepted_of_selected 12 75370 ⟨445248, by decide⟩ ⟨12, 1, 0, 445248, 75370, 1, 65536⟩
    (by decide) selected_cut_22021

theorem selected_cut_22022 : selected 9 ⟨561528, by decide⟩
    (prefixPartial 12 75371) = some ⟨12, 2, 0, 561528, 75371, 3721, 65536⟩ := by
  decide +kernel

theorem context_12_75371_561528 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75371 ⟨561528, by decide⟩ :=
  accepted_of_selected 12 75371 ⟨561528, by decide⟩ ⟨12, 2, 0, 561528, 75371, 3721, 65536⟩
    (by decide) selected_cut_22022

theorem unmarked_context_11_18842_561529 : frontier 10 ⟨561529, by decide⟩
    (prefixCache 11 18842) (prefixPartial 11 18842) = false := by
  decide +kernel

theorem node_context_11_18842_561529 : EJMOriginalGlobalDAGData.nodes 10 ⟨561529, by decide⟩ =
    .split (coordinate 11) (![⟨561454, by decide⟩,⟨561489, by decide⟩,⟨445248, by decide⟩,⟨561528, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18842_561529 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18842 ⟨561529, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18842
    ⟨561529, by decide⟩ (by decide) (![⟨561454, by decide⟩,⟨561489, by decide⟩,⟨445248, by decide⟩,⟨561528, by decide⟩]) unmarked_context_11_18842_561529 node_context_11_18842_561529
  intro a
  fin_cases a
  · exact context_12_75368_561454
  · exact context_12_75369_561489
  · exact context_12_75370_445248
  · exact context_12_75371_561528

theorem selected_cut_22023 : selected 9 ⟨561577, by decide⟩
    (prefixPartial 12 75372) = some ⟨12, 2, 0, 561577, 75372, 3969, 65536⟩ := by
  decide +kernel

theorem context_12_75372_561577 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75372 ⟨561577, by decide⟩ :=
  accepted_of_selected 12 75372 ⟨561577, by decide⟩ ⟨12, 2, 0, 561577, 75372, 3969, 65536⟩
    (by decide) selected_cut_22023

theorem selected_cut_22024 : selected 9 ⟨561616, by decide⟩
    (prefixPartial 12 75373) = some ⟨12, 2, 0, 561616, 75373, 3817, 65536⟩ := by
  decide +kernel

theorem context_12_75373_561616 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75373 ⟨561616, by decide⟩ :=
  accepted_of_selected 12 75373 ⟨561616, by decide⟩ ⟨12, 2, 0, 561616, 75373, 3817, 65536⟩
    (by decide) selected_cut_22024

theorem selected_cut_22025 : selected 9 ⟨561663, by decide⟩
    (prefixPartial 12 75374) = some ⟨12, 2, 0, 561663, 75374, 3793, 65536⟩ := by
  decide +kernel

theorem context_12_75374_561663 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75374 ⟨561663, by decide⟩ :=
  accepted_of_selected 12 75374 ⟨561663, by decide⟩ ⟨12, 2, 0, 561663, 75374, 3793, 65536⟩
    (by decide) selected_cut_22025

theorem selected_cut_22026 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 301500) = some ⟨13, 1, 0, 3444, 301500, 1, 16384⟩ := by
  decide +kernel

theorem context_13_301500_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301500 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 301500 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 301500, 1, 16384⟩
    (by decide) selected_cut_22026

theorem selected_cut_22027 : selected 8 ⟨561673, by decide⟩
    (prefixPartial 13 301501) = some ⟨13, 2, 0, 561673, 301501, 973, 16384⟩ := by
  decide +kernel

theorem context_13_301501_561673 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301501 ⟨561673, by decide⟩ :=
  accepted_of_selected 13 301501 ⟨561673, by decide⟩ ⟨13, 2, 0, 561673, 301501, 973, 16384⟩
    (by decide) selected_cut_22027

theorem selected_cut_22028 : selected 8 ⟨561704, by decide⟩
    (prefixPartial 13 301502) = some ⟨13, 2, 0, 561704, 301502, 2253, 16384⟩ := by
  decide +kernel

theorem context_13_301502_561704 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301502 ⟨561704, by decide⟩ :=
  accepted_of_selected 13 301502 ⟨561704, by decide⟩ ⟨13, 2, 0, 561704, 301502, 2253, 16384⟩
    (by decide) selected_cut_22028

theorem selected_cut_22029 : selected 8 ⟨561710, by decide⟩
    (prefixPartial 13 301503) = some ⟨13, 2, 0, 561710, 301503, 885, 16384⟩ := by
  decide +kernel

theorem context_13_301503_561710 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301503 ⟨561710, by decide⟩ :=
  accepted_of_selected 13 301503 ⟨561710, by decide⟩ ⟨13, 2, 0, 561710, 301503, 885, 16384⟩
    (by decide) selected_cut_22029

theorem unmarked_context_12_75375_561711 : frontier 9 ⟨561711, by decide⟩
    (prefixCache 12 75375) (prefixPartial 12 75375) = false := by
  decide +kernel

theorem node_context_12_75375_561711 : EJMOriginalGlobalDAGData.nodes 9 ⟨561711, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨561673, by decide⟩,⟨561704, by decide⟩,⟨561710, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75375_561711 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75375 ⟨561711, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75375
    ⟨561711, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨561673, by decide⟩,⟨561704, by decide⟩,⟨561710, by decide⟩]) unmarked_context_12_75375_561711 node_context_12_75375_561711
  intro a
  fin_cases a
  · exact context_13_301500_3444
  · exact context_13_301501_561673
  · exact context_13_301502_561704
  · exact context_13_301503_561710

theorem unmarked_context_11_18843_561712 : frontier 10 ⟨561712, by decide⟩
    (prefixCache 11 18843) (prefixPartial 11 18843) = false := by
  decide +kernel

theorem node_context_11_18843_561712 : EJMOriginalGlobalDAGData.nodes 10 ⟨561712, by decide⟩ =
    .split (coordinate 11) (![⟨561577, by decide⟩,⟨561616, by decide⟩,⟨561663, by decide⟩,⟨561711, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18843_561712 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18843 ⟨561712, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18843
    ⟨561712, by decide⟩ (by decide) (![⟨561577, by decide⟩,⟨561616, by decide⟩,⟨561663, by decide⟩,⟨561711, by decide⟩]) unmarked_context_11_18843_561712 node_context_11_18843_561712
  intro a
  fin_cases a
  · exact context_12_75372_561577
  · exact context_12_75373_561616
  · exact context_12_75374_561663
  · exact context_12_75375_561711

theorem unmarked_context_10_4710_561713 : frontier 11 ⟨561713, by decide⟩
    (prefixCache 10 4710) (prefixPartial 10 4710) = false := by
  decide +kernel

theorem node_context_10_4710_561713 : EJMOriginalGlobalDAGData.nodes 11 ⟨561713, by decide⟩ =
    .split (coordinate 10) (![⟨561224, by decide⟩,⟨561415, by decide⟩,⟨561529, by decide⟩,⟨561712, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4710_561713 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4710 ⟨561713, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4710
    ⟨561713, by decide⟩ (by decide) (![⟨561224, by decide⟩,⟨561415, by decide⟩,⟨561529, by decide⟩,⟨561712, by decide⟩]) unmarked_context_10_4710_561713 node_context_10_4710_561713
  intro a
  fin_cases a
  · exact context_11_18840_561224
  · exact context_11_18841_561415
  · exact context_11_18842_561529
  · exact context_11_18843_561712

theorem selected_cut_22030 : selected 9 ⟨561743, by decide⟩
    (prefixPartial 12 75376) = some ⟨12, 2, 0, 561743, 75376, 2721, 65536⟩ := by
  decide +kernel

theorem context_12_75376_561743 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75376 ⟨561743, by decide⟩ :=
  accepted_of_selected 12 75376 ⟨561743, by decide⟩ ⟨12, 2, 0, 561743, 75376, 2721, 65536⟩
    (by decide) selected_cut_22030

theorem selected_cut_22031 : selected 9 ⟨561778, by decide⟩
    (prefixPartial 12 75377) = some ⟨12, 2, 0, 561778, 75377, 2893, 65536⟩ := by
  decide +kernel

theorem context_12_75377_561778 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75377 ⟨561778, by decide⟩ :=
  accepted_of_selected 12 75377 ⟨561778, by decide⟩ ⟨12, 2, 0, 561778, 75377, 2893, 65536⟩
    (by decide) selected_cut_22031

theorem selected_cut_22032 : selected 9 ⟨561817, by decide⟩
    (prefixPartial 12 75378) = some ⟨12, 2, 0, 561817, 75378, 2925, 65536⟩ := by
  decide +kernel

theorem context_12_75378_561817 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75378 ⟨561817, by decide⟩ :=
  accepted_of_selected 12 75378 ⟨561817, by decide⟩ ⟨12, 2, 0, 561817, 75378, 2925, 65536⟩
    (by decide) selected_cut_22032

theorem selected_cut_22033 : selected 9 ⟨561854, by decide⟩
    (prefixPartial 12 75379) = some ⟨12, 2, 0, 561854, 75379, 3181, 65536⟩ := by
  decide +kernel

theorem context_12_75379_561854 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75379 ⟨561854, by decide⟩ :=
  accepted_of_selected 12 75379 ⟨561854, by decide⟩ ⟨12, 2, 0, 561854, 75379, 3181, 65536⟩
    (by decide) selected_cut_22033

theorem unmarked_context_11_18844_561855 : frontier 10 ⟨561855, by decide⟩
    (prefixCache 11 18844) (prefixPartial 11 18844) = false := by
  decide +kernel

theorem node_context_11_18844_561855 : EJMOriginalGlobalDAGData.nodes 10 ⟨561855, by decide⟩ =
    .split (coordinate 11) (![⟨561743, by decide⟩,⟨561778, by decide⟩,⟨561817, by decide⟩,⟨561854, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18844_561855 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18844 ⟨561855, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18844
    ⟨561855, by decide⟩ (by decide) (![⟨561743, by decide⟩,⟨561778, by decide⟩,⟨561817, by decide⟩,⟨561854, by decide⟩]) unmarked_context_11_18844_561855 node_context_11_18844_561855
  intro a
  fin_cases a
  · exact context_12_75376_561743
  · exact context_12_75377_561778
  · exact context_12_75378_561817
  · exact context_12_75379_561854

theorem selected_cut_22034 : selected 9 ⟨561889, by decide⟩
    (prefixPartial 12 75380) = some ⟨12, 2, 0, 561889, 75380, 2749, 65536⟩ := by
  decide +kernel

theorem context_12_75380_561889 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75380 ⟨561889, by decide⟩ :=
  accepted_of_selected 12 75380 ⟨561889, by decide⟩ ⟨12, 2, 0, 561889, 75380, 2749, 65536⟩
    (by decide) selected_cut_22034

theorem selected_cut_22035 : selected 9 ⟨561922, by decide⟩
    (prefixPartial 12 75381) = some ⟨12, 2, 0, 561922, 75381, 2713, 65536⟩ := by
  decide +kernel

theorem context_12_75381_561922 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75381 ⟨561922, by decide⟩ :=
  accepted_of_selected 12 75381 ⟨561922, by decide⟩ ⟨12, 2, 0, 561922, 75381, 2713, 65536⟩
    (by decide) selected_cut_22035

theorem selected_cut_22036 : selected 9 ⟨561958, by decide⟩
    (prefixPartial 12 75382) = some ⟨12, 2, 0, 561958, 75382, 3033, 65536⟩ := by
  decide +kernel

theorem context_12_75382_561958 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75382 ⟨561958, by decide⟩ :=
  accepted_of_selected 12 75382 ⟨561958, by decide⟩ ⟨12, 2, 0, 561958, 75382, 3033, 65536⟩
    (by decide) selected_cut_22036

theorem selected_cut_22037 : selected 9 ⟨562004, by decide⟩
    (prefixPartial 12 75383) = some ⟨12, 2, 0, 562004, 75383, 3429, 65536⟩ := by
  decide +kernel

theorem context_12_75383_562004 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75383 ⟨562004, by decide⟩ :=
  accepted_of_selected 12 75383 ⟨562004, by decide⟩ ⟨12, 2, 0, 562004, 75383, 3429, 65536⟩
    (by decide) selected_cut_22037

theorem unmarked_context_11_18845_562005 : frontier 10 ⟨562005, by decide⟩
    (prefixCache 11 18845) (prefixPartial 11 18845) = false := by
  decide +kernel

theorem node_context_11_18845_562005 : EJMOriginalGlobalDAGData.nodes 10 ⟨562005, by decide⟩ =
    .split (coordinate 11) (![⟨561889, by decide⟩,⟨561922, by decide⟩,⟨561958, by decide⟩,⟨562004, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18845_562005 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18845 ⟨562005, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18845
    ⟨562005, by decide⟩ (by decide) (![⟨561889, by decide⟩,⟨561922, by decide⟩,⟨561958, by decide⟩,⟨562004, by decide⟩]) unmarked_context_11_18845_562005 node_context_11_18845_562005
  intro a
  fin_cases a
  · exact context_12_75380_561889
  · exact context_12_75381_561922
  · exact context_12_75382_561958
  · exact context_12_75383_562004

theorem selected_cut_22038 : selected 9 ⟨562034, by decide⟩
    (prefixPartial 12 75384) = some ⟨12, 2, 0, 562034, 75384, 2749, 65536⟩ := by
  decide +kernel

theorem context_12_75384_562034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75384 ⟨562034, by decide⟩ :=
  accepted_of_selected 12 75384 ⟨562034, by decide⟩ ⟨12, 2, 0, 562034, 75384, 2749, 65536⟩
    (by decide) selected_cut_22038

theorem selected_cut_22039 : selected 9 ⟨562068, by decide⟩
    (prefixPartial 12 75385) = some ⟨12, 2, 0, 562068, 75385, 2841, 65536⟩ := by
  decide +kernel

theorem context_12_75385_562068 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75385 ⟨562068, by decide⟩ :=
  accepted_of_selected 12 75385 ⟨562068, by decide⟩ ⟨12, 2, 0, 562068, 75385, 2841, 65536⟩
    (by decide) selected_cut_22039

theorem selected_cut_22040 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 301544) = some ⟨13, 1, 0, 3444, 301544, 1, 16384⟩ := by
  decide +kernel

theorem context_13_301544_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301544 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 301544 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 301544, 1, 16384⟩
    (by decide) selected_cut_22040

theorem selected_cut_22041 : selected 8 ⟨562076, by decide⟩
    (prefixPartial 13 301545) = some ⟨13, 2, 0, 562076, 301545, 453, 16384⟩ := by
  decide +kernel

theorem context_13_301545_562076 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301545 ⟨562076, by decide⟩ :=
  accepted_of_selected 13 301545 ⟨562076, by decide⟩ ⟨13, 2, 0, 562076, 301545, 453, 16384⟩
    (by decide) selected_cut_22041

theorem selected_cut_22042 : selected 8 ⟨562109, by decide⟩
    (prefixPartial 13 301546) = some ⟨13, 2, 0, 562109, 301546, 2497, 16384⟩ := by
  decide +kernel

theorem context_13_301546_562109 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301546 ⟨562109, by decide⟩ :=
  accepted_of_selected 13 301546 ⟨562109, by decide⟩ ⟨13, 2, 0, 562109, 301546, 2497, 16384⟩
    (by decide) selected_cut_22042

theorem selected_cut_22043 : selected 8 ⟨562151, by decide⟩
    (prefixPartial 13 301547) = some ⟨13, 2, 0, 562151, 301547, 1561, 16384⟩ := by
  decide +kernel

theorem context_13_301547_562151 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301547 ⟨562151, by decide⟩ :=
  accepted_of_selected 13 301547 ⟨562151, by decide⟩ ⟨13, 2, 0, 562151, 301547, 1561, 16384⟩
    (by decide) selected_cut_22043

theorem unmarked_context_12_75386_562152 : frontier 9 ⟨562152, by decide⟩
    (prefixCache 12 75386) (prefixPartial 12 75386) = false := by
  decide +kernel

theorem node_context_12_75386_562152 : EJMOriginalGlobalDAGData.nodes 9 ⟨562152, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨562076, by decide⟩,⟨562109, by decide⟩,⟨562151, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75386_562152 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75386 ⟨562152, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75386
    ⟨562152, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨562076, by decide⟩,⟨562109, by decide⟩,⟨562151, by decide⟩]) unmarked_context_12_75386_562152 node_context_12_75386_562152
  intro a
  fin_cases a
  · exact context_13_301544_3444
  · exact context_13_301545_562076
  · exact context_13_301546_562109
  · exact context_13_301547_562151

theorem selected_cut_22044 : selected 9 ⟨562185, by decide⟩
    (prefixPartial 12 75387) = some ⟨12, 2, 0, 562185, 75387, 2813, 65536⟩ := by
  decide +kernel

theorem context_12_75387_562185 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75387 ⟨562185, by decide⟩ :=
  accepted_of_selected 12 75387 ⟨562185, by decide⟩ ⟨12, 2, 0, 562185, 75387, 2813, 65536⟩
    (by decide) selected_cut_22044

theorem unmarked_context_11_18846_562186 : frontier 10 ⟨562186, by decide⟩
    (prefixCache 11 18846) (prefixPartial 11 18846) = false := by
  decide +kernel

theorem node_context_11_18846_562186 : EJMOriginalGlobalDAGData.nodes 10 ⟨562186, by decide⟩ =
    .split (coordinate 11) (![⟨562034, by decide⟩,⟨562068, by decide⟩,⟨562152, by decide⟩,⟨562185, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18846_562186 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18846 ⟨562186, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18846
    ⟨562186, by decide⟩ (by decide) (![⟨562034, by decide⟩,⟨562068, by decide⟩,⟨562152, by decide⟩,⟨562185, by decide⟩]) unmarked_context_11_18846_562186 node_context_11_18846_562186
  intro a
  fin_cases a
  · exact context_12_75384_562034
  · exact context_12_75385_562068
  · exact context_12_75386_562152
  · exact context_12_75387_562185

theorem selected_cut_22045 : selected 9 ⟨562217, by decide⟩
    (prefixPartial 12 75388) = some ⟨12, 2, 0, 562217, 75388, 2605, 65536⟩ := by
  decide +kernel

theorem context_12_75388_562217 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75388 ⟨562217, by decide⟩ :=
  accepted_of_selected 12 75388 ⟨562217, by decide⟩ ⟨12, 2, 0, 562217, 75388, 2605, 65536⟩
    (by decide) selected_cut_22045

theorem selected_cut_22046 : selected 9 ⟨562242, by decide⟩
    (prefixPartial 12 75389) = some ⟨12, 2, 0, 562242, 75389, 2481, 65536⟩ := by
  decide +kernel

theorem context_12_75389_562242 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75389 ⟨562242, by decide⟩ :=
  accepted_of_selected 12 75389 ⟨562242, by decide⟩ ⟨12, 2, 0, 562242, 75389, 2481, 65536⟩
    (by decide) selected_cut_22046

theorem selected_cut_22047 : selected 9 ⟨562275, by decide⟩
    (prefixPartial 12 75390) = some ⟨12, 2, 0, 562275, 75390, 2633, 65536⟩ := by
  decide +kernel

theorem context_12_75390_562275 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75390 ⟨562275, by decide⟩ :=
  accepted_of_selected 12 75390 ⟨562275, by decide⟩ ⟨12, 2, 0, 562275, 75390, 2633, 65536⟩
    (by decide) selected_cut_22047

theorem selected_cut_22048 : selected 9 ⟨562305, by decide⟩
    (prefixPartial 12 75391) = some ⟨12, 2, 0, 562305, 75391, 2893, 65536⟩ := by
  decide +kernel

theorem context_12_75391_562305 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75391 ⟨562305, by decide⟩ :=
  accepted_of_selected 12 75391 ⟨562305, by decide⟩ ⟨12, 2, 0, 562305, 75391, 2893, 65536⟩
    (by decide) selected_cut_22048

theorem unmarked_context_11_18847_562306 : frontier 10 ⟨562306, by decide⟩
    (prefixCache 11 18847) (prefixPartial 11 18847) = false := by
  decide +kernel

theorem node_context_11_18847_562306 : EJMOriginalGlobalDAGData.nodes 10 ⟨562306, by decide⟩ =
    .split (coordinate 11) (![⟨562217, by decide⟩,⟨562242, by decide⟩,⟨562275, by decide⟩,⟨562305, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18847_562306 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18847 ⟨562306, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18847
    ⟨562306, by decide⟩ (by decide) (![⟨562217, by decide⟩,⟨562242, by decide⟩,⟨562275, by decide⟩,⟨562305, by decide⟩]) unmarked_context_11_18847_562306 node_context_11_18847_562306
  intro a
  fin_cases a
  · exact context_12_75388_562217
  · exact context_12_75389_562242
  · exact context_12_75390_562275
  · exact context_12_75391_562305

theorem unmarked_context_10_4711_562307 : frontier 11 ⟨562307, by decide⟩
    (prefixCache 10 4711) (prefixPartial 10 4711) = false := by
  decide +kernel

theorem node_context_10_4711_562307 : EJMOriginalGlobalDAGData.nodes 11 ⟨562307, by decide⟩ =
    .split (coordinate 10) (![⟨561855, by decide⟩,⟨562005, by decide⟩,⟨562186, by decide⟩,⟨562306, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4711_562307 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4711 ⟨562307, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4711
    ⟨562307, by decide⟩ (by decide) (![⟨561855, by decide⟩,⟨562005, by decide⟩,⟨562186, by decide⟩,⟨562306, by decide⟩]) unmarked_context_10_4711_562307 node_context_10_4711_562307
  intro a
  fin_cases a
  · exact context_11_18844_561855
  · exact context_11_18845_562005
  · exact context_11_18846_562186
  · exact context_11_18847_562306

theorem unmarked_context_9_1177_562308 : frontier 12 ⟨562308, by decide⟩
    (prefixCache 9 1177) (prefixPartial 9 1177) = false := by
  decide +kernel

theorem node_context_9_1177_562308 : EJMOriginalGlobalDAGData.nodes 12 ⟨562308, by decide⟩ =
    .split (coordinate 9) (![⟨560365, by decide⟩,⟨561035, by decide⟩,⟨561713, by decide⟩,⟨562307, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1177_562308 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1177 ⟨562308, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1177
    ⟨562308, by decide⟩ (by decide) (![⟨560365, by decide⟩,⟨561035, by decide⟩,⟨561713, by decide⟩,⟨562307, by decide⟩]) unmarked_context_9_1177_562308 node_context_9_1177_562308
  intro a
  fin_cases a
  · exact context_10_4708_560365
  · exact context_10_4709_561035
  · exact context_10_4710_561713
  · exact context_10_4711_562307

theorem selected_cut_22049 : selected 9 ⟨562333, by decide⟩
    (prefixPartial 12 75392) = some ⟨12, 2, 0, 562333, 75392, 1741, 65536⟩ := by
  decide +kernel

theorem context_12_75392_562333 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75392 ⟨562333, by decide⟩ :=
  accepted_of_selected 12 75392 ⟨562333, by decide⟩ ⟨12, 2, 0, 562333, 75392, 1741, 65536⟩
    (by decide) selected_cut_22049

theorem selected_cut_22050 : selected 9 ⟨562353, by decide⟩
    (prefixPartial 12 75393) = some ⟨12, 2, 0, 562353, 75393, 1837, 65536⟩ := by
  decide +kernel

theorem context_12_75393_562353 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75393 ⟨562353, by decide⟩ :=
  accepted_of_selected 12 75393 ⟨562353, by decide⟩ ⟨12, 2, 0, 562353, 75393, 1837, 65536⟩
    (by decide) selected_cut_22050

theorem selected_cut_22051 : selected 9 ⟨562380, by decide⟩
    (prefixPartial 12 75394) = some ⟨12, 2, 0, 562380, 75394, 1749, 65536⟩ := by
  decide +kernel

theorem context_12_75394_562380 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75394 ⟨562380, by decide⟩ :=
  accepted_of_selected 12 75394 ⟨562380, by decide⟩ ⟨12, 2, 0, 562380, 75394, 1749, 65536⟩
    (by decide) selected_cut_22051

theorem selected_cut_22052 : selected 9 ⟨562405, by decide⟩
    (prefixPartial 12 75395) = some ⟨12, 2, 0, 562405, 75395, 1989, 65536⟩ := by
  decide +kernel

theorem context_12_75395_562405 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75395 ⟨562405, by decide⟩ :=
  accepted_of_selected 12 75395 ⟨562405, by decide⟩ ⟨12, 2, 0, 562405, 75395, 1989, 65536⟩
    (by decide) selected_cut_22052

theorem unmarked_context_11_18848_562406 : frontier 10 ⟨562406, by decide⟩
    (prefixCache 11 18848) (prefixPartial 11 18848) = false := by
  decide +kernel

theorem node_context_11_18848_562406 : EJMOriginalGlobalDAGData.nodes 10 ⟨562406, by decide⟩ =
    .split (coordinate 11) (![⟨562333, by decide⟩,⟨562353, by decide⟩,⟨562380, by decide⟩,⟨562405, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18848_562406 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18848 ⟨562406, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18848
    ⟨562406, by decide⟩ (by decide) (![⟨562333, by decide⟩,⟨562353, by decide⟩,⟨562380, by decide⟩,⟨562405, by decide⟩]) unmarked_context_11_18848_562406 node_context_11_18848_562406
  intro a
  fin_cases a
  · exact context_12_75392_562333
  · exact context_12_75393_562353
  · exact context_12_75394_562380
  · exact context_12_75395_562405

theorem selected_cut_22053 : selected 9 ⟨562426, by decide⟩
    (prefixPartial 12 75396) = some ⟨12, 2, 0, 562426, 75396, 1833, 65536⟩ := by
  decide +kernel

theorem context_12_75396_562426 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75396 ⟨562426, by decide⟩ :=
  accepted_of_selected 12 75396 ⟨562426, by decide⟩ ⟨12, 2, 0, 562426, 75396, 1833, 65536⟩
    (by decide) selected_cut_22053

theorem selected_cut_22054 : selected 9 ⟨562443, by decide⟩
    (prefixPartial 12 75397) = some ⟨12, 2, 0, 562443, 75397, 1849, 65536⟩ := by
  decide +kernel

theorem context_12_75397_562443 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75397 ⟨562443, by decide⟩ :=
  accepted_of_selected 12 75397 ⟨562443, by decide⟩ ⟨12, 2, 0, 562443, 75397, 1849, 65536⟩
    (by decide) selected_cut_22054

theorem selected_cut_22055 : selected 9 ⟨562468, by decide⟩
    (prefixPartial 12 75398) = some ⟨12, 2, 0, 562468, 75398, 1929, 65536⟩ := by
  decide +kernel

theorem context_12_75398_562468 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75398 ⟨562468, by decide⟩ :=
  accepted_of_selected 12 75398 ⟨562468, by decide⟩ ⟨12, 2, 0, 562468, 75398, 1929, 65536⟩
    (by decide) selected_cut_22055

theorem selected_cut_22056 : selected 9 ⟨562492, by decide⟩
    (prefixPartial 12 75399) = some ⟨12, 2, 0, 562492, 75399, 2129, 65536⟩ := by
  decide +kernel

theorem context_12_75399_562492 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75399 ⟨562492, by decide⟩ :=
  accepted_of_selected 12 75399 ⟨562492, by decide⟩ ⟨12, 2, 0, 562492, 75399, 2129, 65536⟩
    (by decide) selected_cut_22056

theorem unmarked_context_11_18849_562493 : frontier 10 ⟨562493, by decide⟩
    (prefixCache 11 18849) (prefixPartial 11 18849) = false := by
  decide +kernel

theorem node_context_11_18849_562493 : EJMOriginalGlobalDAGData.nodes 10 ⟨562493, by decide⟩ =
    .split (coordinate 11) (![⟨562426, by decide⟩,⟨562443, by decide⟩,⟨562468, by decide⟩,⟨562492, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18849_562493 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18849 ⟨562493, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18849
    ⟨562493, by decide⟩ (by decide) (![⟨562426, by decide⟩,⟨562443, by decide⟩,⟨562468, by decide⟩,⟨562492, by decide⟩]) unmarked_context_11_18849_562493 node_context_11_18849_562493
  intro a
  fin_cases a
  · exact context_12_75396_562426
  · exact context_12_75397_562443
  · exact context_12_75398_562468
  · exact context_12_75399_562492

theorem selected_cut_22057 : selected 9 ⟨562511, by decide⟩
    (prefixPartial 12 75400) = some ⟨12, 2, 0, 562511, 75400, 2045, 65536⟩ := by
  decide +kernel

theorem context_12_75400_562511 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75400 ⟨562511, by decide⟩ :=
  accepted_of_selected 12 75400 ⟨562511, by decide⟩ ⟨12, 2, 0, 562511, 75400, 2045, 65536⟩
    (by decide) selected_cut_22057

theorem selected_cut_22058 : selected 9 ⟨562531, by decide⟩
    (prefixPartial 12 75401) = some ⟨12, 2, 0, 562531, 75401, 2037, 65536⟩ := by
  decide +kernel

theorem context_12_75401_562531 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75401 ⟨562531, by decide⟩ :=
  accepted_of_selected 12 75401 ⟨562531, by decide⟩ ⟨12, 2, 0, 562531, 75401, 2037, 65536⟩
    (by decide) selected_cut_22058

theorem selected_cut_22059 : selected 9 ⟨448662, by decide⟩
    (prefixPartial 12 75402) = some ⟨12, 1, 0, 448662, 75402, 1, 65536⟩ := by
  decide +kernel

theorem context_12_75402_448662 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75402 ⟨448662, by decide⟩ :=
  accepted_of_selected 12 75402 ⟨448662, by decide⟩ ⟨12, 1, 0, 448662, 75402, 1, 65536⟩
    (by decide) selected_cut_22059

theorem selected_cut_22060 : selected 9 ⟨562556, by decide⟩
    (prefixPartial 12 75403) = some ⟨12, 2, 0, 562556, 75403, 2009, 65536⟩ := by
  decide +kernel

theorem context_12_75403_562556 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75403 ⟨562556, by decide⟩ :=
  accepted_of_selected 12 75403 ⟨562556, by decide⟩ ⟨12, 2, 0, 562556, 75403, 2009, 65536⟩
    (by decide) selected_cut_22060

theorem unmarked_context_11_18850_562557 : frontier 10 ⟨562557, by decide⟩
    (prefixCache 11 18850) (prefixPartial 11 18850) = false := by
  decide +kernel

theorem node_context_11_18850_562557 : EJMOriginalGlobalDAGData.nodes 10 ⟨562557, by decide⟩ =
    .split (coordinate 11) (![⟨562511, by decide⟩,⟨562531, by decide⟩,⟨448662, by decide⟩,⟨562556, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18850_562557 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18850 ⟨562557, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18850
    ⟨562557, by decide⟩ (by decide) (![⟨562511, by decide⟩,⟨562531, by decide⟩,⟨448662, by decide⟩,⟨562556, by decide⟩]) unmarked_context_11_18850_562557 node_context_11_18850_562557
  intro a
  fin_cases a
  · exact context_12_75400_562511
  · exact context_12_75401_562531
  · exact context_12_75402_448662
  · exact context_12_75403_562556

theorem selected_cut_22061 : selected 9 ⟨562575, by decide⟩
    (prefixPartial 12 75404) = some ⟨12, 2, 0, 562575, 75404, 1985, 65536⟩ := by
  decide +kernel

theorem context_12_75404_562575 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75404 ⟨562575, by decide⟩ :=
  accepted_of_selected 12 75404 ⟨562575, by decide⟩ ⟨12, 2, 0, 562575, 75404, 1985, 65536⟩
    (by decide) selected_cut_22061

theorem selected_cut_22062 : selected 9 ⟨562592, by decide⟩
    (prefixPartial 12 75405) = some ⟨12, 2, 0, 562592, 75405, 1913, 65536⟩ := by
  decide +kernel

theorem context_12_75405_562592 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75405 ⟨562592, by decide⟩ :=
  accepted_of_selected 12 75405 ⟨562592, by decide⟩ ⟨12, 2, 0, 562592, 75405, 1913, 65536⟩
    (by decide) selected_cut_22062

theorem selected_cut_22063 : selected 9 ⟨562617, by decide⟩
    (prefixPartial 12 75406) = some ⟨12, 2, 0, 562617, 75406, 1981, 65536⟩ := by
  decide +kernel

theorem context_12_75406_562617 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75406 ⟨562617, by decide⟩ :=
  accepted_of_selected 12 75406 ⟨562617, by decide⟩ ⟨12, 2, 0, 562617, 75406, 1981, 65536⟩
    (by decide) selected_cut_22063

theorem selected_cut_22064 : selected 9 ⟨562634, by decide⟩
    (prefixPartial 12 75407) = some ⟨12, 2, 0, 562634, 75407, 2117, 65536⟩ := by
  decide +kernel

theorem context_12_75407_562634 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75407 ⟨562634, by decide⟩ :=
  accepted_of_selected 12 75407 ⟨562634, by decide⟩ ⟨12, 2, 0, 562634, 75407, 2117, 65536⟩
    (by decide) selected_cut_22064

theorem unmarked_context_11_18851_562635 : frontier 10 ⟨562635, by decide⟩
    (prefixCache 11 18851) (prefixPartial 11 18851) = false := by
  decide +kernel

theorem node_context_11_18851_562635 : EJMOriginalGlobalDAGData.nodes 10 ⟨562635, by decide⟩ =
    .split (coordinate 11) (![⟨562575, by decide⟩,⟨562592, by decide⟩,⟨562617, by decide⟩,⟨562634, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18851_562635 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18851 ⟨562635, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18851
    ⟨562635, by decide⟩ (by decide) (![⟨562575, by decide⟩,⟨562592, by decide⟩,⟨562617, by decide⟩,⟨562634, by decide⟩]) unmarked_context_11_18851_562635 node_context_11_18851_562635
  intro a
  fin_cases a
  · exact context_12_75404_562575
  · exact context_12_75405_562592
  · exact context_12_75406_562617
  · exact context_12_75407_562634

theorem unmarked_context_10_4712_562636 : frontier 11 ⟨562636, by decide⟩
    (prefixCache 10 4712) (prefixPartial 10 4712) = false := by
  decide +kernel

theorem node_context_10_4712_562636 : EJMOriginalGlobalDAGData.nodes 11 ⟨562636, by decide⟩ =
    .split (coordinate 10) (![⟨562406, by decide⟩,⟨562493, by decide⟩,⟨562557, by decide⟩,⟨562635, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4712_562636 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4712 ⟨562636, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4712
    ⟨562636, by decide⟩ (by decide) (![⟨562406, by decide⟩,⟨562493, by decide⟩,⟨562557, by decide⟩,⟨562635, by decide⟩]) unmarked_context_10_4712_562636 node_context_10_4712_562636
  intro a
  fin_cases a
  · exact context_11_18848_562406
  · exact context_11_18849_562493
  · exact context_11_18850_562557
  · exact context_11_18851_562635

theorem selected_cut_22065 : selected 9 ⟨562658, by decide⟩
    (prefixPartial 12 75408) = some ⟨12, 2, 0, 562658, 75408, 1861, 65536⟩ := by
  decide +kernel

theorem context_12_75408_562658 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75408 ⟨562658, by decide⟩ :=
  accepted_of_selected 12 75408 ⟨562658, by decide⟩ ⟨12, 2, 0, 562658, 75408, 1861, 65536⟩
    (by decide) selected_cut_22065

theorem selected_cut_22066 : selected 9 ⟨562678, by decide⟩
    (prefixPartial 12 75409) = some ⟨12, 2, 0, 562678, 75409, 1885, 65536⟩ := by
  decide +kernel

theorem context_12_75409_562678 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75409 ⟨562678, by decide⟩ :=
  accepted_of_selected 12 75409 ⟨562678, by decide⟩ ⟨12, 2, 0, 562678, 75409, 1885, 65536⟩
    (by decide) selected_cut_22066

theorem selected_cut_22067 : selected 9 ⟨562699, by decide⟩
    (prefixPartial 12 75410) = some ⟨12, 2, 0, 562699, 75410, 1813, 65536⟩ := by
  decide +kernel

theorem context_12_75410_562699 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75410 ⟨562699, by decide⟩ :=
  accepted_of_selected 12 75410 ⟨562699, by decide⟩ ⟨12, 2, 0, 562699, 75410, 1813, 65536⟩
    (by decide) selected_cut_22067

theorem selected_cut_22068 : selected 9 ⟨562724, by decide⟩
    (prefixPartial 12 75411) = some ⟨12, 2, 0, 562724, 75411, 2117, 65536⟩ := by
  decide +kernel

theorem context_12_75411_562724 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75411 ⟨562724, by decide⟩ :=
  accepted_of_selected 12 75411 ⟨562724, by decide⟩ ⟨12, 2, 0, 562724, 75411, 2117, 65536⟩
    (by decide) selected_cut_22068

theorem unmarked_context_11_18852_562725 : frontier 10 ⟨562725, by decide⟩
    (prefixCache 11 18852) (prefixPartial 11 18852) = false := by
  decide +kernel

theorem node_context_11_18852_562725 : EJMOriginalGlobalDAGData.nodes 10 ⟨562725, by decide⟩ =
    .split (coordinate 11) (![⟨562658, by decide⟩,⟨562678, by decide⟩,⟨562699, by decide⟩,⟨562724, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18852_562725 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18852 ⟨562725, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18852
    ⟨562725, by decide⟩ (by decide) (![⟨562658, by decide⟩,⟨562678, by decide⟩,⟨562699, by decide⟩,⟨562724, by decide⟩]) unmarked_context_11_18852_562725 node_context_11_18852_562725
  intro a
  fin_cases a
  · exact context_12_75408_562658
  · exact context_12_75409_562678
  · exact context_12_75410_562699
  · exact context_12_75411_562724

theorem selected_cut_22069 : selected 9 ⟨562751, by decide⟩
    (prefixPartial 12 75412) = some ⟨12, 2, 0, 562751, 75412, 2597, 65536⟩ := by
  decide +kernel

theorem context_12_75412_562751 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75412 ⟨562751, by decide⟩ :=
  accepted_of_selected 12 75412 ⟨562751, by decide⟩ ⟨12, 2, 0, 562751, 75412, 2597, 65536⟩
    (by decide) selected_cut_22069

theorem selected_cut_22070 : selected 9 ⟨449506, by decide⟩
    (prefixPartial 12 75413) = some ⟨12, 1, 0, 449506, 75413, 1, 65536⟩ := by
  decide +kernel

theorem context_12_75413_449506 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75413 ⟨449506, by decide⟩ :=
  accepted_of_selected 12 75413 ⟨449506, by decide⟩ ⟨12, 1, 0, 449506, 75413, 1, 65536⟩
    (by decide) selected_cut_22070

theorem selected_cut_22071 : selected 9 ⟨562787, by decide⟩
    (prefixPartial 12 75414) = some ⟨12, 2, 0, 562787, 75414, 2553, 65536⟩ := by
  decide +kernel

theorem context_12_75414_562787 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75414 ⟨562787, by decide⟩ :=
  accepted_of_selected 12 75414 ⟨562787, by decide⟩ ⟨12, 2, 0, 562787, 75414, 2553, 65536⟩
    (by decide) selected_cut_22071

theorem selected_cut_22072 : selected 9 ⟨562832, by decide⟩
    (prefixPartial 12 75415) = some ⟨12, 2, 0, 562832, 75415, 2933, 65536⟩ := by
  decide +kernel

theorem context_12_75415_562832 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75415 ⟨562832, by decide⟩ :=
  accepted_of_selected 12 75415 ⟨562832, by decide⟩ ⟨12, 2, 0, 562832, 75415, 2933, 65536⟩
    (by decide) selected_cut_22072

theorem unmarked_context_11_18853_562833 : frontier 10 ⟨562833, by decide⟩
    (prefixCache 11 18853) (prefixPartial 11 18853) = false := by
  decide +kernel

theorem node_context_11_18853_562833 : EJMOriginalGlobalDAGData.nodes 10 ⟨562833, by decide⟩ =
    .split (coordinate 11) (![⟨562751, by decide⟩,⟨449506, by decide⟩,⟨562787, by decide⟩,⟨562832, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18853_562833 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18853 ⟨562833, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18853
    ⟨562833, by decide⟩ (by decide) (![⟨562751, by decide⟩,⟨449506, by decide⟩,⟨562787, by decide⟩,⟨562832, by decide⟩]) unmarked_context_11_18853_562833 node_context_11_18853_562833
  intro a
  fin_cases a
  · exact context_12_75412_562751
  · exact context_12_75413_449506
  · exact context_12_75414_562787
  · exact context_12_75415_562832

theorem selected_cut_22073 : selected 9 ⟨562853, by decide⟩
    (prefixPartial 12 75416) = some ⟨12, 2, 0, 562853, 75416, 2025, 65536⟩ := by
  decide +kernel

theorem context_12_75416_562853 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75416 ⟨562853, by decide⟩ :=
  accepted_of_selected 12 75416 ⟨562853, by decide⟩ ⟨12, 2, 0, 562853, 75416, 2025, 65536⟩
    (by decide) selected_cut_22073

theorem selected_cut_22074 : selected 9 ⟨562875, by decide⟩
    (prefixPartial 12 75417) = some ⟨12, 2, 0, 562875, 75417, 1957, 65536⟩ := by
  decide +kernel

theorem context_12_75417_562875 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75417 ⟨562875, by decide⟩ :=
  accepted_of_selected 12 75417 ⟨562875, by decide⟩ ⟨12, 2, 0, 562875, 75417, 1957, 65536⟩
    (by decide) selected_cut_22074

theorem selected_cut_22075 : selected 9 ⟨448662, by decide⟩
    (prefixPartial 12 75418) = some ⟨12, 1, 0, 448662, 75418, 1, 65536⟩ := by
  decide +kernel

theorem context_12_75418_448662 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75418 ⟨448662, by decide⟩ :=
  accepted_of_selected 12 75418 ⟨448662, by decide⟩ ⟨12, 1, 0, 448662, 75418, 1, 65536⟩
    (by decide) selected_cut_22075

theorem selected_cut_22076 : selected 9 ⟨562901, by decide⟩
    (prefixPartial 12 75419) = some ⟨12, 2, 0, 562901, 75419, 2057, 65536⟩ := by
  decide +kernel

theorem context_12_75419_562901 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75419 ⟨562901, by decide⟩ :=
  accepted_of_selected 12 75419 ⟨562901, by decide⟩ ⟨12, 2, 0, 562901, 75419, 2057, 65536⟩
    (by decide) selected_cut_22076

theorem unmarked_context_11_18854_562902 : frontier 10 ⟨562902, by decide⟩
    (prefixCache 11 18854) (prefixPartial 11 18854) = false := by
  decide +kernel

theorem node_context_11_18854_562902 : EJMOriginalGlobalDAGData.nodes 10 ⟨562902, by decide⟩ =
    .split (coordinate 11) (![⟨562853, by decide⟩,⟨562875, by decide⟩,⟨448662, by decide⟩,⟨562901, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18854_562902 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18854 ⟨562902, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18854
    ⟨562902, by decide⟩ (by decide) (![⟨562853, by decide⟩,⟨562875, by decide⟩,⟨448662, by decide⟩,⟨562901, by decide⟩]) unmarked_context_11_18854_562902 node_context_11_18854_562902
  intro a
  fin_cases a
  · exact context_12_75416_562853
  · exact context_12_75417_562875
  · exact context_12_75418_448662
  · exact context_12_75419_562901

theorem selected_cut_22077 : selected 9 ⟨562923, by decide⟩
    (prefixPartial 12 75420) = some ⟨12, 2, 0, 562923, 75420, 1893, 65536⟩ := by
  decide +kernel

theorem context_12_75420_562923 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75420 ⟨562923, by decide⟩ :=
  accepted_of_selected 12 75420 ⟨562923, by decide⟩ ⟨12, 2, 0, 562923, 75420, 1893, 65536⟩
    (by decide) selected_cut_22077

theorem selected_cut_22078 : selected 9 ⟨562939, by decide⟩
    (prefixPartial 12 75421) = some ⟨12, 2, 0, 562939, 75421, 1689, 65536⟩ := by
  decide +kernel

theorem context_12_75421_562939 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75421 ⟨562939, by decide⟩ :=
  accepted_of_selected 12 75421 ⟨562939, by decide⟩ ⟨12, 2, 0, 562939, 75421, 1689, 65536⟩
    (by decide) selected_cut_22078

theorem selected_cut_22079 : selected 9 ⟨562960, by decide⟩
    (prefixPartial 12 75422) = some ⟨12, 2, 0, 562960, 75422, 1785, 65536⟩ := by
  decide +kernel

theorem context_12_75422_562960 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75422 ⟨562960, by decide⟩ :=
  accepted_of_selected 12 75422 ⟨562960, by decide⟩ ⟨12, 2, 0, 562960, 75422, 1785, 65536⟩
    (by decide) selected_cut_22079

theorem selected_cut_22080 : selected 9 ⟨562982, by decide⟩
    (prefixPartial 12 75423) = some ⟨12, 2, 0, 562982, 75423, 2045, 65536⟩ := by
  decide +kernel

theorem context_12_75423_562982 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75423 ⟨562982, by decide⟩ :=
  accepted_of_selected 12 75423 ⟨562982, by decide⟩ ⟨12, 2, 0, 562982, 75423, 2045, 65536⟩
    (by decide) selected_cut_22080

theorem unmarked_context_11_18855_562983 : frontier 10 ⟨562983, by decide⟩
    (prefixCache 11 18855) (prefixPartial 11 18855) = false := by
  decide +kernel

theorem node_context_11_18855_562983 : EJMOriginalGlobalDAGData.nodes 10 ⟨562983, by decide⟩ =
    .split (coordinate 11) (![⟨562923, by decide⟩,⟨562939, by decide⟩,⟨562960, by decide⟩,⟨562982, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18855_562983 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18855 ⟨562983, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18855
    ⟨562983, by decide⟩ (by decide) (![⟨562923, by decide⟩,⟨562939, by decide⟩,⟨562960, by decide⟩,⟨562982, by decide⟩]) unmarked_context_11_18855_562983 node_context_11_18855_562983
  intro a
  fin_cases a
  · exact context_12_75420_562923
  · exact context_12_75421_562939
  · exact context_12_75422_562960
  · exact context_12_75423_562982

theorem unmarked_context_10_4713_562984 : frontier 11 ⟨562984, by decide⟩
    (prefixCache 10 4713) (prefixPartial 10 4713) = false := by
  decide +kernel

theorem node_context_10_4713_562984 : EJMOriginalGlobalDAGData.nodes 11 ⟨562984, by decide⟩ =
    .split (coordinate 10) (![⟨562725, by decide⟩,⟨562833, by decide⟩,⟨562902, by decide⟩,⟨562983, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4713_562984 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4713 ⟨562984, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4713
    ⟨562984, by decide⟩ (by decide) (![⟨562725, by decide⟩,⟨562833, by decide⟩,⟨562902, by decide⟩,⟨562983, by decide⟩]) unmarked_context_10_4713_562984 node_context_10_4713_562984
  intro a
  fin_cases a
  · exact context_11_18852_562725
  · exact context_11_18853_562833
  · exact context_11_18854_562902
  · exact context_11_18855_562983

theorem selected_cut_22081 : selected 9 ⟨562998, by decide⟩
    (prefixPartial 12 75424) = some ⟨12, 2, 0, 562998, 75424, 1421, 65536⟩ := by
  decide +kernel

theorem context_12_75424_562998 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75424 ⟨562998, by decide⟩ :=
  accepted_of_selected 12 75424 ⟨562998, by decide⟩ ⟨12, 2, 0, 562998, 75424, 1421, 65536⟩
    (by decide) selected_cut_22081

theorem selected_cut_22082 : selected 9 ⟨563011, by decide⟩
    (prefixPartial 12 75425) = some ⟨12, 2, 0, 563011, 75425, 1465, 65536⟩ := by
  decide +kernel

theorem context_12_75425_563011 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75425 ⟨563011, by decide⟩ :=
  accepted_of_selected 12 75425 ⟨563011, by decide⟩ ⟨12, 2, 0, 563011, 75425, 1465, 65536⟩
    (by decide) selected_cut_22082

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
