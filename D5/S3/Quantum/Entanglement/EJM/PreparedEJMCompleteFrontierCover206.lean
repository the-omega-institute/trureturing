/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover205
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_19779 : selected 9 ⟨505875, by decide⟩
    (prefixPartial 12 72345) = some ⟨12, 2, 0, 505875, 72345, 1873, 65536⟩ := by
  decide +kernel

theorem context_12_72345_505875 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72345 ⟨505875, by decide⟩ :=
  accepted_of_selected 12 72345 ⟨505875, by decide⟩ ⟨12, 2, 0, 505875, 72345, 1873, 65536⟩
    (by decide) selected_cut_19779

theorem selected_cut_19780 : selected 9 ⟨212113, by decide⟩
    (prefixPartial 12 72346) = some ⟨12, 1, 0, 212113, 72346, 1, 65536⟩ := by
  decide +kernel

theorem context_12_72346_212113 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72346 ⟨212113, by decide⟩ :=
  accepted_of_selected 12 72346 ⟨212113, by decide⟩ ⟨12, 1, 0, 212113, 72346, 1, 65536⟩
    (by decide) selected_cut_19780

theorem selected_cut_19781 : selected 9 ⟨505895, by decide⟩
    (prefixPartial 12 72347) = some ⟨12, 2, 0, 505895, 72347, 1733, 65536⟩ := by
  decide +kernel

theorem context_12_72347_505895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72347 ⟨505895, by decide⟩ :=
  accepted_of_selected 12 72347 ⟨505895, by decide⟩ ⟨12, 2, 0, 505895, 72347, 1733, 65536⟩
    (by decide) selected_cut_19781

theorem unmarked_context_11_18086_505896 : frontier 10 ⟨505896, by decide⟩
    (prefixCache 11 18086) (prefixPartial 11 18086) = false := by
  decide +kernel

theorem node_context_11_18086_505896 : EJMOriginalGlobalDAGData.nodes 10 ⟨505896, by decide⟩ =
    .split (coordinate 11) (![⟨505840, by decide⟩,⟨505875, by decide⟩,⟨212113, by decide⟩,⟨505895, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18086_505896 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18086 ⟨505896, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18086
    ⟨505896, by decide⟩ (by decide) (![⟨505840, by decide⟩,⟨505875, by decide⟩,⟨212113, by decide⟩,⟨505895, by decide⟩]) unmarked_context_11_18086_505896 node_context_11_18086_505896
  intro a
  fin_cases a
  · exact context_12_72344_505840
  · exact context_12_72345_505875
  · exact context_12_72346_212113
  · exact context_12_72347_505895

theorem selected_cut_19782 : selected 9 ⟨505933, by decide⟩
    (prefixPartial 12 72348) = some ⟨12, 2, 0, 505933, 72348, 1965, 65536⟩ := by
  decide +kernel

theorem context_12_72348_505933 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72348 ⟨505933, by decide⟩ :=
  accepted_of_selected 12 72348 ⟨505933, by decide⟩ ⟨12, 2, 0, 505933, 72348, 1965, 65536⟩
    (by decide) selected_cut_19782

theorem selected_cut_19783 : selected 9 ⟨505969, by decide⟩
    (prefixPartial 12 72349) = some ⟨12, 2, 0, 505969, 72349, 2085, 65536⟩ := by
  decide +kernel

theorem context_12_72349_505969 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72349 ⟨505969, by decide⟩ :=
  accepted_of_selected 12 72349 ⟨505969, by decide⟩ ⟨12, 2, 0, 505969, 72349, 2085, 65536⟩
    (by decide) selected_cut_19783

theorem selected_cut_19784 : selected 9 ⟨506006, by decide⟩
    (prefixPartial 12 72350) = some ⟨12, 2, 0, 506006, 72350, 2029, 65536⟩ := by
  decide +kernel

theorem context_12_72350_506006 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72350 ⟨506006, by decide⟩ :=
  accepted_of_selected 12 72350 ⟨506006, by decide⟩ ⟨12, 2, 0, 506006, 72350, 2029, 65536⟩
    (by decide) selected_cut_19784

theorem selected_cut_19785 : selected 9 ⟨506037, by decide⟩
    (prefixPartial 12 72351) = some ⟨12, 2, 0, 506037, 72351, 1981, 65536⟩ := by
  decide +kernel

theorem context_12_72351_506037 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72351 ⟨506037, by decide⟩ :=
  accepted_of_selected 12 72351 ⟨506037, by decide⟩ ⟨12, 2, 0, 506037, 72351, 1981, 65536⟩
    (by decide) selected_cut_19785

theorem unmarked_context_11_18087_506038 : frontier 10 ⟨506038, by decide⟩
    (prefixCache 11 18087) (prefixPartial 11 18087) = false := by
  decide +kernel

theorem node_context_11_18087_506038 : EJMOriginalGlobalDAGData.nodes 10 ⟨506038, by decide⟩ =
    .split (coordinate 11) (![⟨505933, by decide⟩,⟨505969, by decide⟩,⟨506006, by decide⟩,⟨506037, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18087_506038 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18087 ⟨506038, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18087
    ⟨506038, by decide⟩ (by decide) (![⟨505933, by decide⟩,⟨505969, by decide⟩,⟨506006, by decide⟩,⟨506037, by decide⟩]) unmarked_context_11_18087_506038 node_context_11_18087_506038
  intro a
  fin_cases a
  · exact context_12_72348_505933
  · exact context_12_72349_505969
  · exact context_12_72350_506006
  · exact context_12_72351_506037

theorem unmarked_context_10_4521_506039 : frontier 11 ⟨506039, by decide⟩
    (prefixCache 10 4521) (prefixPartial 10 4521) = false := by
  decide +kernel

theorem node_context_10_4521_506039 : EJMOriginalGlobalDAGData.nodes 11 ⟨506039, by decide⟩ =
    .split (coordinate 10) (![⟨505704, by decide⟩,⟨505823, by decide⟩,⟨505896, by decide⟩,⟨506038, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4521_506039 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4521 ⟨506039, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4521
    ⟨506039, by decide⟩ (by decide) (![⟨505704, by decide⟩,⟨505823, by decide⟩,⟨505896, by decide⟩,⟨506038, by decide⟩]) unmarked_context_10_4521_506039 node_context_10_4521_506039
  intro a
  fin_cases a
  · exact context_11_18084_505704
  · exact context_11_18085_505823
  · exact context_11_18086_505896
  · exact context_11_18087_506038

theorem selected_cut_19786 : selected 9 ⟨506056, by decide⟩
    (prefixPartial 12 72352) = some ⟨12, 2, 0, 506056, 72352, 1453, 65536⟩ := by
  decide +kernel

theorem context_12_72352_506056 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72352 ⟨506056, by decide⟩ :=
  accepted_of_selected 12 72352 ⟨506056, by decide⟩ ⟨12, 2, 0, 506056, 72352, 1453, 65536⟩
    (by decide) selected_cut_19786

theorem selected_cut_19787 : selected 9 ⟨506077, by decide⟩
    (prefixPartial 12 72353) = some ⟨12, 2, 0, 506077, 72353, 1793, 65536⟩ := by
  decide +kernel

theorem context_12_72353_506077 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72353 ⟨506077, by decide⟩ :=
  accepted_of_selected 12 72353 ⟨506077, by decide⟩ ⟨12, 2, 0, 506077, 72353, 1793, 65536⟩
    (by decide) selected_cut_19787

theorem selected_cut_19788 : selected 9 ⟨506095, by decide⟩
    (prefixPartial 12 72354) = some ⟨12, 2, 0, 506095, 72354, 1469, 65536⟩ := by
  decide +kernel

theorem context_12_72354_506095 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72354 ⟨506095, by decide⟩ :=
  accepted_of_selected 12 72354 ⟨506095, by decide⟩ ⟨12, 2, 0, 506095, 72354, 1469, 65536⟩
    (by decide) selected_cut_19788

theorem selected_cut_19789 : selected 9 ⟨506111, by decide⟩
    (prefixPartial 12 72355) = some ⟨12, 2, 0, 506111, 72355, 1661, 65536⟩ := by
  decide +kernel

theorem context_12_72355_506111 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72355 ⟨506111, by decide⟩ :=
  accepted_of_selected 12 72355 ⟨506111, by decide⟩ ⟨12, 2, 0, 506111, 72355, 1661, 65536⟩
    (by decide) selected_cut_19789

theorem unmarked_context_11_18088_506112 : frontier 10 ⟨506112, by decide⟩
    (prefixCache 11 18088) (prefixPartial 11 18088) = false := by
  decide +kernel

theorem node_context_11_18088_506112 : EJMOriginalGlobalDAGData.nodes 10 ⟨506112, by decide⟩ =
    .split (coordinate 11) (![⟨506056, by decide⟩,⟨506077, by decide⟩,⟨506095, by decide⟩,⟨506111, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18088_506112 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18088 ⟨506112, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18088
    ⟨506112, by decide⟩ (by decide) (![⟨506056, by decide⟩,⟨506077, by decide⟩,⟨506095, by decide⟩,⟨506111, by decide⟩]) unmarked_context_11_18088_506112 node_context_11_18088_506112
  intro a
  fin_cases a
  · exact context_12_72352_506056
  · exact context_12_72353_506077
  · exact context_12_72354_506095
  · exact context_12_72355_506111

theorem selected_cut_19790 : selected 9 ⟨506136, by decide⟩
    (prefixPartial 12 72356) = some ⟨12, 2, 0, 506136, 72356, 1673, 65536⟩ := by
  decide +kernel

theorem context_12_72356_506136 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72356 ⟨506136, by decide⟩ :=
  accepted_of_selected 12 72356 ⟨506136, by decide⟩ ⟨12, 2, 0, 506136, 72356, 1673, 65536⟩
    (by decide) selected_cut_19790

theorem selected_cut_19791 : selected 9 ⟨506155, by decide⟩
    (prefixPartial 12 72357) = some ⟨12, 2, 0, 506155, 72357, 1653, 65536⟩ := by
  decide +kernel

theorem context_12_72357_506155 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72357 ⟨506155, by decide⟩ :=
  accepted_of_selected 12 72357 ⟨506155, by decide⟩ ⟨12, 2, 0, 506155, 72357, 1653, 65536⟩
    (by decide) selected_cut_19791

theorem selected_cut_19792 : selected 9 ⟨506172, by decide⟩
    (prefixPartial 12 72358) = some ⟨12, 2, 0, 506172, 72358, 1513, 65536⟩ := by
  decide +kernel

theorem context_12_72358_506172 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72358 ⟨506172, by decide⟩ :=
  accepted_of_selected 12 72358 ⟨506172, by decide⟩ ⟨12, 2, 0, 506172, 72358, 1513, 65536⟩
    (by decide) selected_cut_19792

theorem selected_cut_19793 : selected 9 ⟨506190, by decide⟩
    (prefixPartial 12 72359) = some ⟨12, 2, 0, 506190, 72359, 1693, 65536⟩ := by
  decide +kernel

theorem context_12_72359_506190 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72359 ⟨506190, by decide⟩ :=
  accepted_of_selected 12 72359 ⟨506190, by decide⟩ ⟨12, 2, 0, 506190, 72359, 1693, 65536⟩
    (by decide) selected_cut_19793

theorem unmarked_context_11_18089_506191 : frontier 10 ⟨506191, by decide⟩
    (prefixCache 11 18089) (prefixPartial 11 18089) = false := by
  decide +kernel

theorem node_context_11_18089_506191 : EJMOriginalGlobalDAGData.nodes 10 ⟨506191, by decide⟩ =
    .split (coordinate 11) (![⟨506136, by decide⟩,⟨506155, by decide⟩,⟨506172, by decide⟩,⟨506190, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18089_506191 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18089 ⟨506191, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18089
    ⟨506191, by decide⟩ (by decide) (![⟨506136, by decide⟩,⟨506155, by decide⟩,⟨506172, by decide⟩,⟨506190, by decide⟩]) unmarked_context_11_18089_506191 node_context_11_18089_506191
  intro a
  fin_cases a
  · exact context_12_72356_506136
  · exact context_12_72357_506155
  · exact context_12_72358_506172
  · exact context_12_72359_506190

theorem selected_cut_19794 : selected 10 ⟨479708, by decide⟩
    (prefixPartial 11 18090) = some ⟨11, 1, 0, 479708, 18090, 1, 262144⟩ := by
  decide +kernel

theorem context_11_18090_479708 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18090 ⟨479708, by decide⟩ :=
  accepted_of_selected 11 18090 ⟨479708, by decide⟩ ⟨11, 1, 0, 479708, 18090, 1, 262144⟩
    (by decide) selected_cut_19794

theorem selected_cut_19795 : selected 9 ⟨506212, by decide⟩
    (prefixPartial 12 72364) = some ⟨12, 2, 0, 506212, 72364, 1641, 65536⟩ := by
  decide +kernel

theorem context_12_72364_506212 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72364 ⟨506212, by decide⟩ :=
  accepted_of_selected 12 72364 ⟨506212, by decide⟩ ⟨12, 2, 0, 506212, 72364, 1641, 65536⟩
    (by decide) selected_cut_19795

theorem selected_cut_19796 : selected 9 ⟨506230, by decide⟩
    (prefixPartial 12 72365) = some ⟨12, 2, 0, 506230, 72365, 1697, 65536⟩ := by
  decide +kernel

theorem context_12_72365_506230 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72365 ⟨506230, by decide⟩ :=
  accepted_of_selected 12 72365 ⟨506230, by decide⟩ ⟨12, 2, 0, 506230, 72365, 1697, 65536⟩
    (by decide) selected_cut_19796

theorem selected_cut_19797 : selected 9 ⟨506245, by decide⟩
    (prefixPartial 12 72366) = some ⟨12, 2, 0, 506245, 72366, 1409, 65536⟩ := by
  decide +kernel

theorem context_12_72366_506245 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72366 ⟨506245, by decide⟩ :=
  accepted_of_selected 12 72366 ⟨506245, by decide⟩ ⟨12, 2, 0, 506245, 72366, 1409, 65536⟩
    (by decide) selected_cut_19797

theorem selected_cut_19798 : selected 9 ⟨506255, by decide⟩
    (prefixPartial 12 72367) = some ⟨12, 2, 0, 506255, 72367, 1593, 65536⟩ := by
  decide +kernel

theorem context_12_72367_506255 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72367 ⟨506255, by decide⟩ :=
  accepted_of_selected 12 72367 ⟨506255, by decide⟩ ⟨12, 2, 0, 506255, 72367, 1593, 65536⟩
    (by decide) selected_cut_19798

theorem unmarked_context_11_18091_506256 : frontier 10 ⟨506256, by decide⟩
    (prefixCache 11 18091) (prefixPartial 11 18091) = false := by
  decide +kernel

theorem node_context_11_18091_506256 : EJMOriginalGlobalDAGData.nodes 10 ⟨506256, by decide⟩ =
    .split (coordinate 11) (![⟨506212, by decide⟩,⟨506230, by decide⟩,⟨506245, by decide⟩,⟨506255, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18091_506256 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18091 ⟨506256, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18091
    ⟨506256, by decide⟩ (by decide) (![⟨506212, by decide⟩,⟨506230, by decide⟩,⟨506245, by decide⟩,⟨506255, by decide⟩]) unmarked_context_11_18091_506256 node_context_11_18091_506256
  intro a
  fin_cases a
  · exact context_12_72364_506212
  · exact context_12_72365_506230
  · exact context_12_72366_506245
  · exact context_12_72367_506255

theorem unmarked_context_10_4522_506257 : frontier 11 ⟨506257, by decide⟩
    (prefixCache 10 4522) (prefixPartial 10 4522) = false := by
  decide +kernel

theorem node_context_10_4522_506257 : EJMOriginalGlobalDAGData.nodes 11 ⟨506257, by decide⟩ =
    .split (coordinate 10) (![⟨506112, by decide⟩,⟨506191, by decide⟩,⟨479708, by decide⟩,⟨506256, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4522_506257 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4522 ⟨506257, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4522
    ⟨506257, by decide⟩ (by decide) (![⟨506112, by decide⟩,⟨506191, by decide⟩,⟨479708, by decide⟩,⟨506256, by decide⟩]) unmarked_context_10_4522_506257 node_context_10_4522_506257
  intro a
  fin_cases a
  · exact context_11_18088_506112
  · exact context_11_18089_506191
  · exact context_11_18090_479708
  · exact context_11_18091_506256

theorem selected_cut_19799 : selected 9 ⟨506272, by decide⟩
    (prefixPartial 12 72368) = some ⟨12, 2, 0, 506272, 72368, 1149, 65536⟩ := by
  decide +kernel

theorem context_12_72368_506272 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72368 ⟨506272, by decide⟩ :=
  accepted_of_selected 12 72368 ⟨506272, by decide⟩ ⟨12, 2, 0, 506272, 72368, 1149, 65536⟩
    (by decide) selected_cut_19799

theorem selected_cut_19800 : selected 9 ⟨506296, by decide⟩
    (prefixPartial 12 72369) = some ⟨12, 2, 0, 506296, 72369, 1481, 65536⟩ := by
  decide +kernel

theorem context_12_72369_506296 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72369 ⟨506296, by decide⟩ :=
  accepted_of_selected 12 72369 ⟨506296, by decide⟩ ⟨12, 2, 0, 506296, 72369, 1481, 65536⟩
    (by decide) selected_cut_19800

theorem selected_cut_19801 : selected 9 ⟨506311, by decide⟩
    (prefixPartial 12 72370) = some ⟨12, 2, 0, 506311, 72370, 1253, 65536⟩ := by
  decide +kernel

theorem context_12_72370_506311 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72370 ⟨506311, by decide⟩ :=
  accepted_of_selected 12 72370 ⟨506311, by decide⟩ ⟨12, 2, 0, 506311, 72370, 1253, 65536⟩
    (by decide) selected_cut_19801

theorem selected_cut_19802 : selected 9 ⟨506323, by decide⟩
    (prefixPartial 12 72371) = some ⟨12, 2, 0, 506323, 72371, 1213, 65536⟩ := by
  decide +kernel

theorem context_12_72371_506323 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72371 ⟨506323, by decide⟩ :=
  accepted_of_selected 12 72371 ⟨506323, by decide⟩ ⟨12, 2, 0, 506323, 72371, 1213, 65536⟩
    (by decide) selected_cut_19802

theorem unmarked_context_11_18092_506324 : frontier 10 ⟨506324, by decide⟩
    (prefixCache 11 18092) (prefixPartial 11 18092) = false := by
  decide +kernel

theorem node_context_11_18092_506324 : EJMOriginalGlobalDAGData.nodes 10 ⟨506324, by decide⟩ =
    .split (coordinate 11) (![⟨506272, by decide⟩,⟨506296, by decide⟩,⟨506311, by decide⟩,⟨506323, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18092_506324 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18092 ⟨506324, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18092
    ⟨506324, by decide⟩ (by decide) (![⟨506272, by decide⟩,⟨506296, by decide⟩,⟨506311, by decide⟩,⟨506323, by decide⟩]) unmarked_context_11_18092_506324 node_context_11_18092_506324
  intro a
  fin_cases a
  · exact context_12_72368_506272
  · exact context_12_72369_506296
  · exact context_12_72370_506311
  · exact context_12_72371_506323

theorem selected_cut_19803 : selected 9 ⟨506338, by decide⟩
    (prefixPartial 12 72372) = some ⟨12, 2, 0, 506338, 72372, 1285, 65536⟩ := by
  decide +kernel

theorem context_12_72372_506338 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72372 ⟨506338, by decide⟩ :=
  accepted_of_selected 12 72372 ⟨506338, by decide⟩ ⟨12, 2, 0, 506338, 72372, 1285, 65536⟩
    (by decide) selected_cut_19803

theorem selected_cut_19804 : selected 9 ⟨506358, by decide⟩
    (prefixPartial 12 72373) = some ⟨12, 2, 0, 506358, 72373, 1365, 65536⟩ := by
  decide +kernel

theorem context_12_72373_506358 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72373 ⟨506358, by decide⟩ :=
  accepted_of_selected 12 72373 ⟨506358, by decide⟩ ⟨12, 2, 0, 506358, 72373, 1365, 65536⟩
    (by decide) selected_cut_19804

theorem selected_cut_19805 : selected 9 ⟨506377, by decide⟩
    (prefixPartial 12 72374) = some ⟨12, 2, 0, 506377, 72374, 1309, 65536⟩ := by
  decide +kernel

theorem context_12_72374_506377 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72374 ⟨506377, by decide⟩ :=
  accepted_of_selected 12 72374 ⟨506377, by decide⟩ ⟨12, 2, 0, 506377, 72374, 1309, 65536⟩
    (by decide) selected_cut_19805

theorem selected_cut_19806 : selected 9 ⟨506391, by decide⟩
    (prefixPartial 12 72375) = some ⟨12, 2, 0, 506391, 72375, 1253, 65536⟩ := by
  decide +kernel

theorem context_12_72375_506391 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72375 ⟨506391, by decide⟩ :=
  accepted_of_selected 12 72375 ⟨506391, by decide⟩ ⟨12, 2, 0, 506391, 72375, 1253, 65536⟩
    (by decide) selected_cut_19806

theorem unmarked_context_11_18093_506392 : frontier 10 ⟨506392, by decide⟩
    (prefixCache 11 18093) (prefixPartial 11 18093) = false := by
  decide +kernel

theorem node_context_11_18093_506392 : EJMOriginalGlobalDAGData.nodes 10 ⟨506392, by decide⟩ =
    .split (coordinate 11) (![⟨506338, by decide⟩,⟨506358, by decide⟩,⟨506377, by decide⟩,⟨506391, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18093_506392 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18093 ⟨506392, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18093
    ⟨506392, by decide⟩ (by decide) (![⟨506338, by decide⟩,⟨506358, by decide⟩,⟨506377, by decide⟩,⟨506391, by decide⟩]) unmarked_context_11_18093_506392 node_context_11_18093_506392
  intro a
  fin_cases a
  · exact context_12_72372_506338
  · exact context_12_72373_506358
  · exact context_12_72374_506377
  · exact context_12_72375_506391

theorem selected_cut_19807 : selected 10 ⟨506433, by decide⟩
    (prefixPartial 11 18094) = some ⟨11, 2, 0, 506433, 18094, 3333, 262144⟩ := by
  decide +kernel

theorem context_11_18094_506433 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18094 ⟨506433, by decide⟩ :=
  accepted_of_selected 11 18094 ⟨506433, by decide⟩ ⟨11, 2, 0, 506433, 18094, 3333, 262144⟩
    (by decide) selected_cut_19807

theorem selected_cut_19808 : selected 9 ⟨506447, by decide⟩
    (prefixPartial 12 72380) = some ⟨12, 2, 0, 506447, 72380, 1221, 65536⟩ := by
  decide +kernel

theorem context_12_72380_506447 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72380 ⟨506447, by decide⟩ :=
  accepted_of_selected 12 72380 ⟨506447, by decide⟩ ⟨12, 2, 0, 506447, 72380, 1221, 65536⟩
    (by decide) selected_cut_19808

theorem selected_cut_19809 : selected 9 ⟨506478, by decide⟩
    (prefixPartial 12 72381) = some ⟨12, 2, 0, 506478, 72381, 1333, 65536⟩ := by
  decide +kernel

theorem context_12_72381_506478 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72381 ⟨506478, by decide⟩ :=
  accepted_of_selected 12 72381 ⟨506478, by decide⟩ ⟨12, 2, 0, 506478, 72381, 1333, 65536⟩
    (by decide) selected_cut_19809

theorem selected_cut_19810 : selected 9 ⟨506497, by decide⟩
    (prefixPartial 12 72382) = some ⟨12, 2, 0, 506497, 72382, 1153, 65536⟩ := by
  decide +kernel

theorem context_12_72382_506497 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72382 ⟨506497, by decide⟩ :=
  accepted_of_selected 12 72382 ⟨506497, by decide⟩ ⟨12, 2, 0, 506497, 72382, 1153, 65536⟩
    (by decide) selected_cut_19810

theorem selected_cut_19811 : selected 9 ⟨506512, by decide⟩
    (prefixPartial 12 72383) = some ⟨12, 2, 0, 506512, 72383, 1093, 65536⟩ := by
  decide +kernel

theorem context_12_72383_506512 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72383 ⟨506512, by decide⟩ :=
  accepted_of_selected 12 72383 ⟨506512, by decide⟩ ⟨12, 2, 0, 506512, 72383, 1093, 65536⟩
    (by decide) selected_cut_19811

theorem unmarked_context_11_18095_506513 : frontier 10 ⟨506513, by decide⟩
    (prefixCache 11 18095) (prefixPartial 11 18095) = false := by
  decide +kernel

theorem node_context_11_18095_506513 : EJMOriginalGlobalDAGData.nodes 10 ⟨506513, by decide⟩ =
    .split (coordinate 11) (![⟨506447, by decide⟩,⟨506478, by decide⟩,⟨506497, by decide⟩,⟨506512, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18095_506513 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18095 ⟨506513, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18095
    ⟨506513, by decide⟩ (by decide) (![⟨506447, by decide⟩,⟨506478, by decide⟩,⟨506497, by decide⟩,⟨506512, by decide⟩]) unmarked_context_11_18095_506513 node_context_11_18095_506513
  intro a
  fin_cases a
  · exact context_12_72380_506447
  · exact context_12_72381_506478
  · exact context_12_72382_506497
  · exact context_12_72383_506512

theorem unmarked_context_10_4523_506514 : frontier 11 ⟨506514, by decide⟩
    (prefixCache 10 4523) (prefixPartial 10 4523) = false := by
  decide +kernel

theorem node_context_10_4523_506514 : EJMOriginalGlobalDAGData.nodes 11 ⟨506514, by decide⟩ =
    .split (coordinate 10) (![⟨506324, by decide⟩,⟨506392, by decide⟩,⟨506433, by decide⟩,⟨506513, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4523_506514 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4523 ⟨506514, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4523
    ⟨506514, by decide⟩ (by decide) (![⟨506324, by decide⟩,⟨506392, by decide⟩,⟨506433, by decide⟩,⟨506513, by decide⟩]) unmarked_context_10_4523_506514 node_context_10_4523_506514
  intro a
  fin_cases a
  · exact context_11_18092_506324
  · exact context_11_18093_506392
  · exact context_11_18094_506433
  · exact context_11_18095_506513

theorem unmarked_context_9_1130_506515 : frontier 12 ⟨506515, by decide⟩
    (prefixCache 9 1130) (prefixPartial 9 1130) = false := by
  decide +kernel

theorem node_context_9_1130_506515 : EJMOriginalGlobalDAGData.nodes 12 ⟨506515, by decide⟩ =
    .split (coordinate 9) (![⟨505570, by decide⟩,⟨506039, by decide⟩,⟨506257, by decide⟩,⟨506514, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1130_506515 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1130 ⟨506515, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1130
    ⟨506515, by decide⟩ (by decide) (![⟨505570, by decide⟩,⟨506039, by decide⟩,⟨506257, by decide⟩,⟨506514, by decide⟩]) unmarked_context_9_1130_506515 node_context_9_1130_506515
  intro a
  fin_cases a
  · exact context_10_4520_505570
  · exact context_10_4521_506039
  · exact context_10_4522_506257
  · exact context_10_4523_506514

theorem selected_cut_19812 : selected 9 ⟨506524, by decide⟩
    (prefixPartial 12 72384) = some ⟨12, 2, 0, 506524, 72384, 1057, 65536⟩ := by
  decide +kernel

theorem context_12_72384_506524 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72384 ⟨506524, by decide⟩ :=
  accepted_of_selected 12 72384 ⟨506524, by decide⟩ ⟨12, 2, 0, 506524, 72384, 1057, 65536⟩
    (by decide) selected_cut_19812

theorem selected_cut_19813 : selected 9 ⟨506545, by decide⟩
    (prefixPartial 12 72385) = some ⟨12, 2, 0, 506545, 72385, 1229, 65536⟩ := by
  decide +kernel

theorem context_12_72385_506545 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72385 ⟨506545, by decide⟩ :=
  accepted_of_selected 12 72385 ⟨506545, by decide⟩ ⟨12, 2, 0, 506545, 72385, 1229, 65536⟩
    (by decide) selected_cut_19813

theorem selected_cut_19814 : selected 9 ⟨506555, by decide⟩
    (prefixPartial 12 72386) = some ⟨12, 2, 0, 506555, 72386, 1113, 65536⟩ := by
  decide +kernel

theorem context_12_72386_506555 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72386 ⟨506555, by decide⟩ :=
  accepted_of_selected 12 72386 ⟨506555, by decide⟩ ⟨12, 2, 0, 506555, 72386, 1113, 65536⟩
    (by decide) selected_cut_19814

theorem selected_cut_19815 : selected 9 ⟨506562, by decide⟩
    (prefixPartial 12 72387) = some ⟨12, 2, 0, 506562, 72387, 1069, 65536⟩ := by
  decide +kernel

theorem context_12_72387_506562 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72387 ⟨506562, by decide⟩ :=
  accepted_of_selected 12 72387 ⟨506562, by decide⟩ ⟨12, 2, 0, 506562, 72387, 1069, 65536⟩
    (by decide) selected_cut_19815

theorem unmarked_context_11_18096_506563 : frontier 10 ⟨506563, by decide⟩
    (prefixCache 11 18096) (prefixPartial 11 18096) = false := by
  decide +kernel

theorem node_context_11_18096_506563 : EJMOriginalGlobalDAGData.nodes 10 ⟨506563, by decide⟩ =
    .split (coordinate 11) (![⟨506524, by decide⟩,⟨506545, by decide⟩,⟨506555, by decide⟩,⟨506562, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18096_506563 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18096 ⟨506563, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18096
    ⟨506563, by decide⟩ (by decide) (![⟨506524, by decide⟩,⟨506545, by decide⟩,⟨506555, by decide⟩,⟨506562, by decide⟩]) unmarked_context_11_18096_506563 node_context_11_18096_506563
  intro a
  fin_cases a
  · exact context_12_72384_506524
  · exact context_12_72385_506545
  · exact context_12_72386_506555
  · exact context_12_72387_506562

theorem selected_cut_19816 : selected 10 ⟨506625, by decide⟩
    (prefixPartial 11 18097) = some ⟨11, 2, 0, 506625, 18097, 3989, 262144⟩ := by
  decide +kernel

theorem context_11_18097_506625 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18097 ⟨506625, by decide⟩ :=
  accepted_of_selected 11 18097 ⟨506625, by decide⟩ ⟨11, 2, 0, 506625, 18097, 3989, 262144⟩
    (by decide) selected_cut_19816

theorem selected_cut_19817 : selected 10 ⟨506673, by decide⟩
    (prefixPartial 11 18098) = some ⟨11, 2, 0, 506673, 18098, 3553, 262144⟩ := by
  decide +kernel

theorem context_11_18098_506673 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18098 ⟨506673, by decide⟩ :=
  accepted_of_selected 11 18098 ⟨506673, by decide⟩ ⟨11, 2, 0, 506673, 18098, 3553, 262144⟩
    (by decide) selected_cut_19817

theorem selected_cut_19818 : selected 10 ⟨506729, by decide⟩
    (prefixPartial 11 18099) = some ⟨11, 2, 0, 506729, 18099, 3725, 262144⟩ := by
  decide +kernel

theorem context_11_18099_506729 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18099 ⟨506729, by decide⟩ :=
  accepted_of_selected 11 18099 ⟨506729, by decide⟩ ⟨11, 2, 0, 506729, 18099, 3725, 262144⟩
    (by decide) selected_cut_19818

theorem unmarked_context_10_4524_506730 : frontier 11 ⟨506730, by decide⟩
    (prefixCache 10 4524) (prefixPartial 10 4524) = false := by
  decide +kernel

theorem node_context_10_4524_506730 : EJMOriginalGlobalDAGData.nodes 11 ⟨506730, by decide⟩ =
    .split (coordinate 10) (![⟨506563, by decide⟩,⟨506625, by decide⟩,⟨506673, by decide⟩,⟨506729, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4524_506730 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4524 ⟨506730, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4524
    ⟨506730, by decide⟩ (by decide) (![⟨506563, by decide⟩,⟨506625, by decide⟩,⟨506673, by decide⟩,⟨506729, by decide⟩]) unmarked_context_10_4524_506730 node_context_10_4524_506730
  intro a
  fin_cases a
  · exact context_11_18096_506563
  · exact context_11_18097_506625
  · exact context_11_18098_506673
  · exact context_11_18099_506729

theorem selected_cut_19819 : selected 10 ⟨506782, by decide⟩
    (prefixPartial 11 18100) = some ⟨11, 2, 0, 506782, 18100, 3237, 262144⟩ := by
  decide +kernel

theorem context_11_18100_506782 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18100 ⟨506782, by decide⟩ :=
  accepted_of_selected 11 18100 ⟨506782, by decide⟩ ⟨11, 2, 0, 506782, 18100, 3237, 262144⟩
    (by decide) selected_cut_19819

theorem selected_cut_19820 : selected 10 ⟨506844, by decide⟩
    (prefixPartial 11 18101) = some ⟨11, 2, 0, 506844, 18101, 2885, 262144⟩ := by
  decide +kernel

theorem context_11_18101_506844 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18101 ⟨506844, by decide⟩ :=
  accepted_of_selected 11 18101 ⟨506844, by decide⟩ ⟨11, 2, 0, 506844, 18101, 2885, 262144⟩
    (by decide) selected_cut_19820

theorem selected_cut_19821 : selected 10 ⟨506900, by decide⟩
    (prefixPartial 11 18102) = some ⟨11, 2, 0, 506900, 18102, 2585, 262144⟩ := by
  decide +kernel

theorem context_11_18102_506900 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18102 ⟨506900, by decide⟩ :=
  accepted_of_selected 11 18102 ⟨506900, by decide⟩ ⟨11, 2, 0, 506900, 18102, 2585, 262144⟩
    (by decide) selected_cut_19821

theorem selected_cut_19822 : selected 10 ⟨506947, by decide⟩
    (prefixPartial 11 18103) = some ⟨11, 2, 0, 506947, 18103, 2325, 262144⟩ := by
  decide +kernel

theorem context_11_18103_506947 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18103 ⟨506947, by decide⟩ :=
  accepted_of_selected 11 18103 ⟨506947, by decide⟩ ⟨11, 2, 0, 506947, 18103, 2325, 262144⟩
    (by decide) selected_cut_19822

theorem unmarked_context_10_4525_506948 : frontier 11 ⟨506948, by decide⟩
    (prefixCache 10 4525) (prefixPartial 10 4525) = false := by
  decide +kernel

theorem node_context_10_4525_506948 : EJMOriginalGlobalDAGData.nodes 11 ⟨506948, by decide⟩ =
    .split (coordinate 10) (![⟨506782, by decide⟩,⟨506844, by decide⟩,⟨506900, by decide⟩,⟨506947, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4525_506948 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4525 ⟨506948, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4525
    ⟨506948, by decide⟩ (by decide) (![⟨506782, by decide⟩,⟨506844, by decide⟩,⟨506900, by decide⟩,⟨506947, by decide⟩]) unmarked_context_10_4525_506948 node_context_10_4525_506948
  intro a
  fin_cases a
  · exact context_11_18100_506782
  · exact context_11_18101_506844
  · exact context_11_18102_506900
  · exact context_11_18103_506947

theorem selected_cut_19823 : selected 10 ⟨506967, by decide⟩
    (prefixPartial 11 18104) = some ⟨11, 2, 0, 506967, 18104, 1489, 262144⟩ := by
  decide +kernel

theorem context_11_18104_506967 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18104 ⟨506967, by decide⟩ :=
  accepted_of_selected 11 18104 ⟨506967, by decide⟩ ⟨11, 2, 0, 506967, 18104, 1489, 262144⟩
    (by decide) selected_cut_19823

theorem selected_cut_19824 : selected 10 ⟨506984, by decide⟩
    (prefixPartial 11 18105) = some ⟨11, 2, 0, 506984, 18105, 1369, 262144⟩ := by
  decide +kernel

theorem context_11_18105_506984 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18105 ⟨506984, by decide⟩ :=
  accepted_of_selected 11 18105 ⟨506984, by decide⟩ ⟨11, 2, 0, 506984, 18105, 1369, 262144⟩
    (by decide) selected_cut_19824

theorem selected_cut_19825 : selected 10 ⟨506996, by decide⟩
    (prefixPartial 11 18106) = some ⟨11, 2, 0, 506996, 18106, 609, 262144⟩ := by
  decide +kernel

theorem context_11_18106_506996 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18106 ⟨506996, by decide⟩ :=
  accepted_of_selected 11 18106 ⟨506996, by decide⟩ ⟨11, 2, 0, 506996, 18106, 609, 262144⟩
    (by decide) selected_cut_19825

theorem selected_cut_19826 : selected 10 ⟨507008, by decide⟩
    (prefixPartial 11 18107) = some ⟨11, 2, 0, 507008, 18107, 925, 262144⟩ := by
  decide +kernel

theorem context_11_18107_507008 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18107 ⟨507008, by decide⟩ :=
  accepted_of_selected 11 18107 ⟨507008, by decide⟩ ⟨11, 2, 0, 507008, 18107, 925, 262144⟩
    (by decide) selected_cut_19826

theorem unmarked_context_10_4526_507009 : frontier 11 ⟨507009, by decide⟩
    (prefixCache 10 4526) (prefixPartial 10 4526) = false := by
  decide +kernel

theorem node_context_10_4526_507009 : EJMOriginalGlobalDAGData.nodes 11 ⟨507009, by decide⟩ =
    .split (coordinate 10) (![⟨506967, by decide⟩,⟨506984, by decide⟩,⟨506996, by decide⟩,⟨507008, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4526_507009 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4526 ⟨507009, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4526
    ⟨507009, by decide⟩ (by decide) (![⟨506967, by decide⟩,⟨506984, by decide⟩,⟨506996, by decide⟩,⟨507008, by decide⟩]) unmarked_context_10_4526_507009 node_context_10_4526_507009
  intro a
  fin_cases a
  · exact context_11_18104_506967
  · exact context_11_18105_506984
  · exact context_11_18106_506996
  · exact context_11_18107_507008

theorem selected_cut_19827 : selected 11 ⟨507051, by decide⟩
    (prefixPartial 10 4527) = some ⟨10, 2, 0, 507051, 4527, 1549, 1048576⟩ := by
  decide +kernel

theorem context_10_4527_507051 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4527 ⟨507051, by decide⟩ :=
  accepted_of_selected 10 4527 ⟨507051, by decide⟩ ⟨10, 2, 0, 507051, 4527, 1549, 1048576⟩
    (by decide) selected_cut_19827

theorem unmarked_context_9_1131_507052 : frontier 12 ⟨507052, by decide⟩
    (prefixCache 9 1131) (prefixPartial 9 1131) = false := by
  decide +kernel

theorem node_context_9_1131_507052 : EJMOriginalGlobalDAGData.nodes 12 ⟨507052, by decide⟩ =
    .split (coordinate 9) (![⟨506730, by decide⟩,⟨506948, by decide⟩,⟨507009, by decide⟩,⟨507051, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1131_507052 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1131 ⟨507052, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1131
    ⟨507052, by decide⟩ (by decide) (![⟨506730, by decide⟩,⟨506948, by decide⟩,⟨507009, by decide⟩,⟨507051, by decide⟩]) unmarked_context_9_1131_507052 node_context_9_1131_507052
  intro a
  fin_cases a
  · exact context_10_4524_506730
  · exact context_10_4525_506948
  · exact context_10_4526_507009
  · exact context_10_4527_507051

theorem unmarked_context_8_282_507053 : frontier 13 ⟨507053, by decide⟩
    (prefixCache 8 282) (prefixPartial 8 282) = false := by
  decide +kernel

theorem node_context_8_282_507053 : EJMOriginalGlobalDAGData.nodes 13 ⟨507053, by decide⟩ =
    .split (coordinate 8) (![⟨501333, by decide⟩,⟨505213, by decide⟩,⟨506515, by decide⟩,⟨507052, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_282_507053 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 282 ⟨507053, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 282
    ⟨507053, by decide⟩ (by decide) (![⟨501333, by decide⟩,⟨505213, by decide⟩,⟨506515, by decide⟩,⟨507052, by decide⟩]) unmarked_context_8_282_507053 node_context_8_282_507053
  intro a
  fin_cases a
  · exact context_9_1128_501333
  · exact context_9_1129_505213
  · exact context_9_1130_506515
  · exact context_9_1131_507052

theorem selected_cut_19828 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 18112) = some ⟨11, 1, 0, 434745, 18112, 1, 262144⟩ := by
  decide +kernel

theorem context_11_18112_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18112 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 18112 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 18112, 1, 262144⟩
    (by decide) selected_cut_19828

theorem selected_cut_19829 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 72452) = some ⟨12, 1, 0, 448748, 72452, 1, 65536⟩ := by
  decide +kernel

theorem context_12_72452_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72452 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 72452 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 72452, 1, 65536⟩
    (by decide) selected_cut_19829

theorem selected_cut_19830 : selected 8 ⟨507188, by decide⟩
    (prefixPartial 13 289812) = some ⟨13, 2, 0, 507188, 289812, 3897, 16384⟩ := by
  decide +kernel

theorem context_13_289812_507188 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289812 ⟨507188, by decide⟩ :=
  accepted_of_selected 13 289812 ⟨507188, by decide⟩ ⟨13, 2, 0, 507188, 289812, 3897, 16384⟩
    (by decide) selected_cut_19830

theorem selected_cut_19831 : selected 8 ⟨507259, by decide⟩
    (prefixPartial 13 289813) = some ⟨13, 2, 0, 507259, 289813, 3101, 16384⟩ := by
  decide +kernel

theorem context_13_289813_507259 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289813 ⟨507259, by decide⟩ :=
  accepted_of_selected 13 289813 ⟨507259, by decide⟩ ⟨13, 2, 0, 507259, 289813, 3101, 16384⟩
    (by decide) selected_cut_19831

theorem selected_cut_19832 : selected 8 ⟨507300, by decide⟩
    (prefixPartial 13 289814) = some ⟨13, 2, 0, 507300, 289814, 1941, 16384⟩ := by
  decide +kernel

theorem context_13_289814_507300 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289814 ⟨507300, by decide⟩ :=
  accepted_of_selected 13 289814 ⟨507300, by decide⟩ ⟨13, 2, 0, 507300, 289814, 1941, 16384⟩
    (by decide) selected_cut_19832

theorem selected_cut_19833 : selected 8 ⟨507312, by decide⟩
    (prefixPartial 13 289815) = some ⟨13, 2, 0, 507312, 289815, 841, 16384⟩ := by
  decide +kernel

theorem context_13_289815_507312 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289815 ⟨507312, by decide⟩ :=
  accepted_of_selected 13 289815 ⟨507312, by decide⟩ ⟨13, 2, 0, 507312, 289815, 841, 16384⟩
    (by decide) selected_cut_19833

theorem unmarked_context_12_72453_507313 : frontier 9 ⟨507313, by decide⟩
    (prefixCache 12 72453) (prefixPartial 12 72453) = false := by
  decide +kernel

theorem node_context_12_72453_507313 : EJMOriginalGlobalDAGData.nodes 9 ⟨507313, by decide⟩ =
    .split (coordinate 12) (![⟨507188, by decide⟩,⟨507259, by decide⟩,⟨507300, by decide⟩,⟨507312, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72453_507313 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72453 ⟨507313, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72453
    ⟨507313, by decide⟩ (by decide) (![⟨507188, by decide⟩,⟨507259, by decide⟩,⟨507300, by decide⟩,⟨507312, by decide⟩]) unmarked_context_12_72453_507313 node_context_12_72453_507313
  intro a
  fin_cases a
  · exact context_13_289812_507188
  · exact context_13_289813_507259
  · exact context_13_289814_507300
  · exact context_13_289815_507312

theorem selected_cut_19834 : selected 8 ⟨507416, by decide⟩
    (prefixPartial 13 289816) = some ⟨13, 2, 0, 507416, 289816, 3929, 16384⟩ := by
  decide +kernel

theorem context_13_289816_507416 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289816 ⟨507416, by decide⟩ :=
  accepted_of_selected 13 289816 ⟨507416, by decide⟩ ⟨13, 2, 0, 507416, 289816, 3929, 16384⟩
    (by decide) selected_cut_19834

theorem selected_cut_19835 : selected 8 ⟨507492, by decide⟩
    (prefixPartial 13 289817) = some ⟨13, 2, 0, 507492, 289817, 3437, 16384⟩ := by
  decide +kernel

theorem context_13_289817_507492 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289817 ⟨507492, by decide⟩ :=
  accepted_of_selected 13 289817 ⟨507492, by decide⟩ ⟨13, 2, 0, 507492, 289817, 3437, 16384⟩
    (by decide) selected_cut_19835

theorem selected_cut_19836 : selected 8 ⟨507568, by decide⟩
    (prefixPartial 13 289818) = some ⟨13, 2, 0, 507568, 289818, 2561, 16384⟩ := by
  decide +kernel

theorem context_13_289818_507568 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289818 ⟨507568, by decide⟩ :=
  accepted_of_selected 13 289818 ⟨507568, by decide⟩ ⟨13, 2, 0, 507568, 289818, 2561, 16384⟩
    (by decide) selected_cut_19836

theorem selected_cut_19837 : selected 8 ⟨507606, by decide⟩
    (prefixPartial 13 289819) = some ⟨13, 2, 0, 507606, 289819, 913, 16384⟩ := by
  decide +kernel

theorem context_13_289819_507606 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289819 ⟨507606, by decide⟩ :=
  accepted_of_selected 13 289819 ⟨507606, by decide⟩ ⟨13, 2, 0, 507606, 289819, 913, 16384⟩
    (by decide) selected_cut_19837

theorem unmarked_context_12_72454_507607 : frontier 9 ⟨507607, by decide⟩
    (prefixCache 12 72454) (prefixPartial 12 72454) = false := by
  decide +kernel

theorem node_context_12_72454_507607 : EJMOriginalGlobalDAGData.nodes 9 ⟨507607, by decide⟩ =
    .split (coordinate 12) (![⟨507416, by decide⟩,⟨507492, by decide⟩,⟨507568, by decide⟩,⟨507606, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72454_507607 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72454 ⟨507607, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72454
    ⟨507607, by decide⟩ (by decide) (![⟨507416, by decide⟩,⟨507492, by decide⟩,⟨507568, by decide⟩,⟨507606, by decide⟩]) unmarked_context_12_72454_507607 node_context_12_72454_507607
  intro a
  fin_cases a
  · exact context_13_289816_507416
  · exact context_13_289817_507492
  · exact context_13_289818_507568
  · exact context_13_289819_507606

theorem selected_cut_19838 : selected 8 ⟨507677, by decide⟩
    (prefixPartial 13 289820) = some ⟨13, 2, 0, 507677, 289820, 3041, 16384⟩ := by
  decide +kernel

theorem context_13_289820_507677 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289820 ⟨507677, by decide⟩ :=
  accepted_of_selected 13 289820 ⟨507677, by decide⟩ ⟨13, 2, 0, 507677, 289820, 3041, 16384⟩
    (by decide) selected_cut_19838

theorem selected_cut_19839 : selected 8 ⟨507721, by decide⟩
    (prefixPartial 13 289821) = some ⟨13, 2, 0, 507721, 289821, 3189, 16384⟩ := by
  decide +kernel

theorem context_13_289821_507721 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289821 ⟨507721, by decide⟩ :=
  accepted_of_selected 13 289821 ⟨507721, by decide⟩ ⟨13, 2, 0, 507721, 289821, 3189, 16384⟩
    (by decide) selected_cut_19839

theorem selected_cut_19840 : selected 8 ⟨507748, by decide⟩
    (prefixPartial 13 289822) = some ⟨13, 2, 0, 507748, 289822, 2141, 16384⟩ := by
  decide +kernel

theorem context_13_289822_507748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289822 ⟨507748, by decide⟩ :=
  accepted_of_selected 13 289822 ⟨507748, by decide⟩ ⟨13, 2, 0, 507748, 289822, 2141, 16384⟩
    (by decide) selected_cut_19840

theorem selected_cut_19841 : selected 8 ⟨507757, by decide⟩
    (prefixPartial 13 289823) = some ⟨13, 2, 0, 507757, 289823, 861, 16384⟩ := by
  decide +kernel

theorem context_13_289823_507757 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289823 ⟨507757, by decide⟩ :=
  accepted_of_selected 13 289823 ⟨507757, by decide⟩ ⟨13, 2, 0, 507757, 289823, 861, 16384⟩
    (by decide) selected_cut_19841

theorem unmarked_context_12_72455_507758 : frontier 9 ⟨507758, by decide⟩
    (prefixCache 12 72455) (prefixPartial 12 72455) = false := by
  decide +kernel

theorem node_context_12_72455_507758 : EJMOriginalGlobalDAGData.nodes 9 ⟨507758, by decide⟩ =
    .split (coordinate 12) (![⟨507677, by decide⟩,⟨507721, by decide⟩,⟨507748, by decide⟩,⟨507757, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72455_507758 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72455 ⟨507758, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72455
    ⟨507758, by decide⟩ (by decide) (![⟨507677, by decide⟩,⟨507721, by decide⟩,⟨507748, by decide⟩,⟨507757, by decide⟩]) unmarked_context_12_72455_507758 node_context_12_72455_507758
  intro a
  fin_cases a
  · exact context_13_289820_507677
  · exact context_13_289821_507721
  · exact context_13_289822_507748
  · exact context_13_289823_507757

theorem unmarked_context_11_18113_507759 : frontier 10 ⟨507759, by decide⟩
    (prefixCache 11 18113) (prefixPartial 11 18113) = false := by
  decide +kernel

theorem node_context_11_18113_507759 : EJMOriginalGlobalDAGData.nodes 10 ⟨507759, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨507313, by decide⟩,⟨507607, by decide⟩,⟨507758, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18113_507759 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18113 ⟨507759, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18113
    ⟨507759, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨507313, by decide⟩,⟨507607, by decide⟩,⟨507758, by decide⟩]) unmarked_context_11_18113_507759 node_context_11_18113_507759
  intro a
  fin_cases a
  · exact context_12_72452_448748
  · exact context_12_72453_507313
  · exact context_12_72454_507607
  · exact context_12_72455_507758

theorem selected_cut_19842 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 72456) = some ⟨12, 1, 0, 448748, 72456, 1, 65536⟩ := by
  decide +kernel

theorem context_12_72456_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72456 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 72456 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 72456, 1, 65536⟩
    (by decide) selected_cut_19842

theorem selected_cut_19843 : selected 8 ⟨507842, by decide⟩
    (prefixPartial 13 289828) = some ⟨13, 2, 0, 507842, 289828, 3361, 16384⟩ := by
  decide +kernel

theorem context_13_289828_507842 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289828 ⟨507842, by decide⟩ :=
  accepted_of_selected 13 289828 ⟨507842, by decide⟩ ⟨13, 2, 0, 507842, 289828, 3361, 16384⟩
    (by decide) selected_cut_19843

theorem selected_cut_19844 : selected 8 ⟨507889, by decide⟩
    (prefixPartial 13 289829) = some ⟨13, 2, 0, 507889, 289829, 2813, 16384⟩ := by
  decide +kernel

theorem context_13_289829_507889 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289829 ⟨507889, by decide⟩ :=
  accepted_of_selected 13 289829 ⟨507889, by decide⟩ ⟨13, 2, 0, 507889, 289829, 2813, 16384⟩
    (by decide) selected_cut_19844

theorem selected_cut_19845 : selected 8 ⟨507917, by decide⟩
    (prefixPartial 13 289830) = some ⟨13, 2, 0, 507917, 289830, 1921, 16384⟩ := by
  decide +kernel

theorem context_13_289830_507917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289830 ⟨507917, by decide⟩ :=
  accepted_of_selected 13 289830 ⟨507917, by decide⟩ ⟨13, 2, 0, 507917, 289830, 1921, 16384⟩
    (by decide) selected_cut_19845

theorem selected_cut_19846 : selected 8 ⟨507926, by decide⟩
    (prefixPartial 13 289831) = some ⟨13, 2, 0, 507926, 289831, 821, 16384⟩ := by
  decide +kernel

theorem context_13_289831_507926 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289831 ⟨507926, by decide⟩ :=
  accepted_of_selected 13 289831 ⟨507926, by decide⟩ ⟨13, 2, 0, 507926, 289831, 821, 16384⟩
    (by decide) selected_cut_19846

theorem unmarked_context_12_72457_507927 : frontier 9 ⟨507927, by decide⟩
    (prefixCache 12 72457) (prefixPartial 12 72457) = false := by
  decide +kernel

theorem node_context_12_72457_507927 : EJMOriginalGlobalDAGData.nodes 9 ⟨507927, by decide⟩ =
    .split (coordinate 12) (![⟨507842, by decide⟩,⟨507889, by decide⟩,⟨507917, by decide⟩,⟨507926, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72457_507927 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72457 ⟨507927, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72457
    ⟨507927, by decide⟩ (by decide) (![⟨507842, by decide⟩,⟨507889, by decide⟩,⟨507917, by decide⟩,⟨507926, by decide⟩]) unmarked_context_12_72457_507927 node_context_12_72457_507927
  intro a
  fin_cases a
  · exact context_13_289828_507842
  · exact context_13_289829_507889
  · exact context_13_289830_507917
  · exact context_13_289831_507926

theorem selected_cut_19847 : selected 9 ⟨88909, by decide⟩
    (prefixPartial 12 72458) = some ⟨12, 1, 0, 88909, 72458, 1, 65536⟩ := by
  decide +kernel

theorem context_12_72458_88909 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72458 ⟨88909, by decide⟩ :=
  accepted_of_selected 12 72458 ⟨88909, by decide⟩ ⟨12, 1, 0, 88909, 72458, 1, 65536⟩
    (by decide) selected_cut_19847

theorem selected_cut_19848 : selected 8 ⟨507986, by decide⟩
    (prefixPartial 13 289836) = some ⟨13, 2, 0, 507986, 289836, 2789, 16384⟩ := by
  decide +kernel

theorem context_13_289836_507986 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289836 ⟨507986, by decide⟩ :=
  accepted_of_selected 13 289836 ⟨507986, by decide⟩ ⟨13, 2, 0, 507986, 289836, 2789, 16384⟩
    (by decide) selected_cut_19848

theorem selected_cut_19849 : selected 8 ⟨508022, by decide⟩
    (prefixPartial 13 289837) = some ⟨13, 2, 0, 508022, 289837, 3173, 16384⟩ := by
  decide +kernel

theorem context_13_289837_508022 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289837 ⟨508022, by decide⟩ :=
  accepted_of_selected 13 289837 ⟨508022, by decide⟩ ⟨13, 2, 0, 508022, 289837, 3173, 16384⟩
    (by decide) selected_cut_19849

theorem selected_cut_19850 : selected 8 ⟨508043, by decide⟩
    (prefixPartial 13 289838) = some ⟨13, 2, 0, 508043, 289838, 2029, 16384⟩ := by
  decide +kernel

theorem context_13_289838_508043 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289838 ⟨508043, by decide⟩ :=
  accepted_of_selected 13 289838 ⟨508043, by decide⟩ ⟨13, 2, 0, 508043, 289838, 2029, 16384⟩
    (by decide) selected_cut_19850

theorem selected_cut_19851 : selected 8 ⟨508056, by decide⟩
    (prefixPartial 13 289839) = some ⟨13, 2, 0, 508056, 289839, 889, 16384⟩ := by
  decide +kernel

theorem context_13_289839_508056 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289839 ⟨508056, by decide⟩ :=
  accepted_of_selected 13 289839 ⟨508056, by decide⟩ ⟨13, 2, 0, 508056, 289839, 889, 16384⟩
    (by decide) selected_cut_19851

theorem unmarked_context_12_72459_508057 : frontier 9 ⟨508057, by decide⟩
    (prefixCache 12 72459) (prefixPartial 12 72459) = false := by
  decide +kernel

theorem node_context_12_72459_508057 : EJMOriginalGlobalDAGData.nodes 9 ⟨508057, by decide⟩ =
    .split (coordinate 12) (![⟨507986, by decide⟩,⟨508022, by decide⟩,⟨508043, by decide⟩,⟨508056, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72459_508057 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72459 ⟨508057, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72459
    ⟨508057, by decide⟩ (by decide) (![⟨507986, by decide⟩,⟨508022, by decide⟩,⟨508043, by decide⟩,⟨508056, by decide⟩]) unmarked_context_12_72459_508057 node_context_12_72459_508057
  intro a
  fin_cases a
  · exact context_13_289836_507986
  · exact context_13_289837_508022
  · exact context_13_289838_508043
  · exact context_13_289839_508056

theorem unmarked_context_11_18114_508058 : frontier 10 ⟨508058, by decide⟩
    (prefixCache 11 18114) (prefixPartial 11 18114) = false := by
  decide +kernel

theorem node_context_11_18114_508058 : EJMOriginalGlobalDAGData.nodes 10 ⟨508058, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨507927, by decide⟩,⟨88909, by decide⟩,⟨508057, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18114_508058 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18114 ⟨508058, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18114
    ⟨508058, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨507927, by decide⟩,⟨88909, by decide⟩,⟨508057, by decide⟩]) unmarked_context_11_18114_508058 node_context_11_18114_508058
  intro a
  fin_cases a
  · exact context_12_72456_448748
  · exact context_12_72457_507927
  · exact context_12_72458_88909
  · exact context_12_72459_508057

theorem selected_cut_19852 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 72460) = some ⟨12, 1, 0, 448748, 72460, 1, 65536⟩ := by
  decide +kernel

theorem context_12_72460_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72460 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 72460 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 72460, 1, 65536⟩
    (by decide) selected_cut_19852

theorem selected_cut_19853 : selected 8 ⟨508131, by decide⟩
    (prefixPartial 13 289844) = some ⟨13, 2, 0, 508131, 289844, 3077, 16384⟩ := by
  decide +kernel

theorem context_13_289844_508131 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289844 ⟨508131, by decide⟩ :=
  accepted_of_selected 13 289844 ⟨508131, by decide⟩ ⟨13, 2, 0, 508131, 289844, 3077, 16384⟩
    (by decide) selected_cut_19853

theorem selected_cut_19854 : selected 8 ⟨508176, by decide⟩
    (prefixPartial 13 289845) = some ⟨13, 2, 0, 508176, 289845, 2729, 16384⟩ := by
  decide +kernel

theorem context_13_289845_508176 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289845 ⟨508176, by decide⟩ :=
  accepted_of_selected 13 289845 ⟨508176, by decide⟩ ⟨13, 2, 0, 508176, 289845, 2729, 16384⟩
    (by decide) selected_cut_19854

theorem selected_cut_19855 : selected 8 ⟨508207, by decide⟩
    (prefixPartial 13 289846) = some ⟨13, 2, 0, 508207, 289846, 2157, 16384⟩ := by
  decide +kernel

theorem context_13_289846_508207 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289846 ⟨508207, by decide⟩ :=
  accepted_of_selected 13 289846 ⟨508207, by decide⟩ ⟨13, 2, 0, 508207, 289846, 2157, 16384⟩
    (by decide) selected_cut_19855

theorem selected_cut_19856 : selected 8 ⟨508223, by decide⟩
    (prefixPartial 13 289847) = some ⟨13, 2, 0, 508223, 289847, 869, 16384⟩ := by
  decide +kernel

theorem context_13_289847_508223 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289847 ⟨508223, by decide⟩ :=
  accepted_of_selected 13 289847 ⟨508223, by decide⟩ ⟨13, 2, 0, 508223, 289847, 869, 16384⟩
    (by decide) selected_cut_19856

theorem unmarked_context_12_72461_508224 : frontier 9 ⟨508224, by decide⟩
    (prefixCache 12 72461) (prefixPartial 12 72461) = false := by
  decide +kernel

theorem node_context_12_72461_508224 : EJMOriginalGlobalDAGData.nodes 9 ⟨508224, by decide⟩ =
    .split (coordinate 12) (![⟨508131, by decide⟩,⟨508176, by decide⟩,⟨508207, by decide⟩,⟨508223, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72461_508224 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72461 ⟨508224, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72461
    ⟨508224, by decide⟩ (by decide) (![⟨508131, by decide⟩,⟨508176, by decide⟩,⟨508207, by decide⟩,⟨508223, by decide⟩]) unmarked_context_12_72461_508224 node_context_12_72461_508224
  intro a
  fin_cases a
  · exact context_13_289844_508131
  · exact context_13_289845_508176
  · exact context_13_289846_508207
  · exact context_13_289847_508223

theorem selected_cut_19857 : selected 8 ⟨508289, by decide⟩
    (prefixPartial 13 289848) = some ⟨13, 2, 0, 508289, 289848, 3225, 16384⟩ := by
  decide +kernel

theorem context_13_289848_508289 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289848 ⟨508289, by decide⟩ :=
  accepted_of_selected 13 289848 ⟨508289, by decide⟩ ⟨13, 2, 0, 508289, 289848, 3225, 16384⟩
    (by decide) selected_cut_19857

theorem selected_cut_19858 : selected 8 ⟨508351, by decide⟩
    (prefixPartial 13 289849) = some ⟨13, 2, 0, 508351, 289849, 3509, 16384⟩ := by
  decide +kernel

theorem context_13_289849_508351 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289849 ⟨508351, by decide⟩ :=
  accepted_of_selected 13 289849 ⟨508351, by decide⟩ ⟨13, 2, 0, 508351, 289849, 3509, 16384⟩
    (by decide) selected_cut_19858

theorem selected_cut_19859 : selected 8 ⟨508405, by decide⟩
    (prefixPartial 13 289850) = some ⟨13, 2, 0, 508405, 289850, 2481, 16384⟩ := by
  decide +kernel

theorem context_13_289850_508405 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289850 ⟨508405, by decide⟩ :=
  accepted_of_selected 13 289850 ⟨508405, by decide⟩ ⟨13, 2, 0, 508405, 289850, 2481, 16384⟩
    (by decide) selected_cut_19859

theorem selected_cut_19860 : selected 8 ⟨508413, by decide⟩
    (prefixPartial 13 289851) = some ⟨13, 2, 0, 508413, 289851, 869, 16384⟩ := by
  decide +kernel

theorem context_13_289851_508413 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289851 ⟨508413, by decide⟩ :=
  accepted_of_selected 13 289851 ⟨508413, by decide⟩ ⟨13, 2, 0, 508413, 289851, 869, 16384⟩
    (by decide) selected_cut_19860

theorem unmarked_context_12_72462_508414 : frontier 9 ⟨508414, by decide⟩
    (prefixCache 12 72462) (prefixPartial 12 72462) = false := by
  decide +kernel

theorem node_context_12_72462_508414 : EJMOriginalGlobalDAGData.nodes 9 ⟨508414, by decide⟩ =
    .split (coordinate 12) (![⟨508289, by decide⟩,⟨508351, by decide⟩,⟨508405, by decide⟩,⟨508413, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72462_508414 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72462 ⟨508414, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72462
    ⟨508414, by decide⟩ (by decide) (![⟨508289, by decide⟩,⟨508351, by decide⟩,⟨508405, by decide⟩,⟨508413, by decide⟩]) unmarked_context_12_72462_508414 node_context_12_72462_508414
  intro a
  fin_cases a
  · exact context_13_289848_508289
  · exact context_13_289849_508351
  · exact context_13_289850_508405
  · exact context_13_289851_508413

theorem selected_cut_19861 : selected 9 ⟨508415, by decide⟩
    (prefixPartial 12 72463) = some ⟨12, 1, 0, 508415, 72463, 1, 65536⟩ := by
  decide +kernel

theorem context_12_72463_508415 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72463 ⟨508415, by decide⟩ :=
  accepted_of_selected 12 72463 ⟨508415, by decide⟩ ⟨12, 1, 0, 508415, 72463, 1, 65536⟩
    (by decide) selected_cut_19861

theorem unmarked_context_11_18115_508416 : frontier 10 ⟨508416, by decide⟩
    (prefixCache 11 18115) (prefixPartial 11 18115) = false := by
  decide +kernel

theorem node_context_11_18115_508416 : EJMOriginalGlobalDAGData.nodes 10 ⟨508416, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨508224, by decide⟩,⟨508414, by decide⟩,⟨508415, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18115_508416 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18115 ⟨508416, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18115
    ⟨508416, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨508224, by decide⟩,⟨508414, by decide⟩,⟨508415, by decide⟩]) unmarked_context_11_18115_508416 node_context_11_18115_508416
  intro a
  fin_cases a
  · exact context_12_72460_448748
  · exact context_12_72461_508224
  · exact context_12_72462_508414
  · exact context_12_72463_508415

theorem unmarked_context_10_4528_508417 : frontier 11 ⟨508417, by decide⟩
    (prefixCache 10 4528) (prefixPartial 10 4528) = false := by
  decide +kernel

theorem node_context_10_4528_508417 : EJMOriginalGlobalDAGData.nodes 11 ⟨508417, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨507759, by decide⟩,⟨508058, by decide⟩,⟨508416, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4528_508417 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4528 ⟨508417, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4528
    ⟨508417, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨507759, by decide⟩,⟨508058, by decide⟩,⟨508416, by decide⟩]) unmarked_context_10_4528_508417 node_context_10_4528_508417
  intro a
  fin_cases a
  · exact context_11_18112_434745
  · exact context_11_18113_507759
  · exact context_11_18114_508058
  · exact context_11_18115_508416

theorem selected_cut_19862 : selected 9 ⟨435160, by decide⟩
    (prefixPartial 12 72464) = some ⟨12, 1, 0, 435160, 72464, 1, 65536⟩ := by
  decide +kernel

theorem context_12_72464_435160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72464 ⟨435160, by decide⟩ :=
  accepted_of_selected 12 72464 ⟨435160, by decide⟩ ⟨12, 1, 0, 435160, 72464, 1, 65536⟩
    (by decide) selected_cut_19862

theorem selected_cut_19863 : selected 8 ⟨508478, by decide⟩
    (prefixPartial 13 289860) = some ⟨13, 2, 0, 508478, 289860, 2577, 16384⟩ := by
  decide +kernel

theorem context_13_289860_508478 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289860 ⟨508478, by decide⟩ :=
  accepted_of_selected 13 289860 ⟨508478, by decide⟩ ⟨13, 2, 0, 508478, 289860, 2577, 16384⟩
    (by decide) selected_cut_19863

theorem selected_cut_19864 : selected 8 ⟨508511, by decide⟩
    (prefixPartial 13 289861) = some ⟨13, 2, 0, 508511, 289861, 2001, 16384⟩ := by
  decide +kernel

theorem context_13_289861_508511 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289861 ⟨508511, by decide⟩ :=
  accepted_of_selected 13 289861 ⟨508511, by decide⟩ ⟨13, 2, 0, 508511, 289861, 2001, 16384⟩
    (by decide) selected_cut_19864

theorem selected_cut_19865 : selected 8 ⟨508537, by decide⟩
    (prefixPartial 13 289862) = some ⟨13, 2, 0, 508537, 289862, 1609, 16384⟩ := by
  decide +kernel

theorem context_13_289862_508537 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289862 ⟨508537, by decide⟩ :=
  accepted_of_selected 13 289862 ⟨508537, by decide⟩ ⟨13, 2, 0, 508537, 289862, 1609, 16384⟩
    (by decide) selected_cut_19865

theorem selected_cut_19866 : selected 8 ⟨508546, by decide⟩
    (prefixPartial 13 289863) = some ⟨13, 2, 0, 508546, 289863, 585, 16384⟩ := by
  decide +kernel

theorem context_13_289863_508546 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289863 ⟨508546, by decide⟩ :=
  accepted_of_selected 13 289863 ⟨508546, by decide⟩ ⟨13, 2, 0, 508546, 289863, 585, 16384⟩
    (by decide) selected_cut_19866

theorem unmarked_context_12_72465_508547 : frontier 9 ⟨508547, by decide⟩
    (prefixCache 12 72465) (prefixPartial 12 72465) = false := by
  decide +kernel

theorem node_context_12_72465_508547 : EJMOriginalGlobalDAGData.nodes 9 ⟨508547, by decide⟩ =
    .split (coordinate 12) (![⟨508478, by decide⟩,⟨508511, by decide⟩,⟨508537, by decide⟩,⟨508546, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72465_508547 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72465 ⟨508547, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72465
    ⟨508547, by decide⟩ (by decide) (![⟨508478, by decide⟩,⟨508511, by decide⟩,⟨508537, by decide⟩,⟨508546, by decide⟩]) unmarked_context_12_72465_508547 node_context_12_72465_508547
  intro a
  fin_cases a
  · exact context_13_289860_508478
  · exact context_13_289861_508511
  · exact context_13_289862_508537
  · exact context_13_289863_508546

theorem selected_cut_19867 : selected 8 ⟨508594, by decide⟩
    (prefixPartial 13 289864) = some ⟨13, 2, 0, 508594, 289864, 2649, 16384⟩ := by
  decide +kernel

theorem context_13_289864_508594 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289864 ⟨508594, by decide⟩ :=
  accepted_of_selected 13 289864 ⟨508594, by decide⟩ ⟨13, 2, 0, 508594, 289864, 2649, 16384⟩
    (by decide) selected_cut_19867

theorem selected_cut_19868 : selected 8 ⟨508626, by decide⟩
    (prefixPartial 13 289865) = some ⟨13, 2, 0, 508626, 289865, 2373, 16384⟩ := by
  decide +kernel

theorem context_13_289865_508626 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289865 ⟨508626, by decide⟩ :=
  accepted_of_selected 13 289865 ⟨508626, by decide⟩ ⟨13, 2, 0, 508626, 289865, 2373, 16384⟩
    (by decide) selected_cut_19868

theorem selected_cut_19869 : selected 8 ⟨508659, by decide⟩
    (prefixPartial 13 289866) = some ⟨13, 2, 0, 508659, 289866, 1897, 16384⟩ := by
  decide +kernel

theorem context_13_289866_508659 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289866 ⟨508659, by decide⟩ :=
  accepted_of_selected 13 289866 ⟨508659, by decide⟩ ⟨13, 2, 0, 508659, 289866, 1897, 16384⟩
    (by decide) selected_cut_19869

theorem selected_cut_19870 : selected 8 ⟨508668, by decide⟩
    (prefixPartial 13 289867) = some ⟨13, 2, 0, 508668, 289867, 625, 16384⟩ := by
  decide +kernel

theorem context_13_289867_508668 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289867 ⟨508668, by decide⟩ :=
  accepted_of_selected 13 289867 ⟨508668, by decide⟩ ⟨13, 2, 0, 508668, 289867, 625, 16384⟩
    (by decide) selected_cut_19870

theorem unmarked_context_12_72466_508669 : frontier 9 ⟨508669, by decide⟩
    (prefixCache 12 72466) (prefixPartial 12 72466) = false := by
  decide +kernel

theorem node_context_12_72466_508669 : EJMOriginalGlobalDAGData.nodes 9 ⟨508669, by decide⟩ =
    .split (coordinate 12) (![⟨508594, by decide⟩,⟨508626, by decide⟩,⟨508659, by decide⟩,⟨508668, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72466_508669 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72466 ⟨508669, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72466
    ⟨508669, by decide⟩ (by decide) (![⟨508594, by decide⟩,⟨508626, by decide⟩,⟨508659, by decide⟩,⟨508668, by decide⟩]) unmarked_context_12_72466_508669 node_context_12_72466_508669
  intro a
  fin_cases a
  · exact context_13_289864_508594
  · exact context_13_289865_508626
  · exact context_13_289866_508659
  · exact context_13_289867_508668

theorem selected_cut_19871 : selected 8 ⟨508708, by decide⟩
    (prefixPartial 13 289868) = some ⟨13, 2, 0, 508708, 289868, 2277, 16384⟩ := by
  decide +kernel

theorem context_13_289868_508708 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289868 ⟨508708, by decide⟩ :=
  accepted_of_selected 13 289868 ⟨508708, by decide⟩ ⟨13, 2, 0, 508708, 289868, 2277, 16384⟩
    (by decide) selected_cut_19871

theorem selected_cut_19872 : selected 8 ⟨508738, by decide⟩
    (prefixPartial 13 289869) = some ⟨13, 2, 0, 508738, 289869, 2205, 16384⟩ := by
  decide +kernel

theorem context_13_289869_508738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289869 ⟨508738, by decide⟩ :=
  accepted_of_selected 13 289869 ⟨508738, by decide⟩ ⟨13, 2, 0, 508738, 289869, 2205, 16384⟩
    (by decide) selected_cut_19872

theorem selected_cut_19873 : selected 8 ⟨508760, by decide⟩
    (prefixPartial 13 289870) = some ⟨13, 2, 0, 508760, 289870, 1605, 16384⟩ := by
  decide +kernel

theorem context_13_289870_508760 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289870 ⟨508760, by decide⟩ :=
  accepted_of_selected 13 289870 ⟨508760, by decide⟩ ⟨13, 2, 0, 508760, 289870, 1605, 16384⟩
    (by decide) selected_cut_19873

theorem selected_cut_19874 : selected 8 ⟨508767, by decide⟩
    (prefixPartial 13 289871) = some ⟨13, 2, 0, 508767, 289871, 577, 16384⟩ := by
  decide +kernel

theorem context_13_289871_508767 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289871 ⟨508767, by decide⟩ :=
  accepted_of_selected 13 289871 ⟨508767, by decide⟩ ⟨13, 2, 0, 508767, 289871, 577, 16384⟩
    (by decide) selected_cut_19874

theorem unmarked_context_12_72467_508768 : frontier 9 ⟨508768, by decide⟩
    (prefixCache 12 72467) (prefixPartial 12 72467) = false := by
  decide +kernel

theorem node_context_12_72467_508768 : EJMOriginalGlobalDAGData.nodes 9 ⟨508768, by decide⟩ =
    .split (coordinate 12) (![⟨508708, by decide⟩,⟨508738, by decide⟩,⟨508760, by decide⟩,⟨508767, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72467_508768 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72467 ⟨508768, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72467
    ⟨508768, by decide⟩ (by decide) (![⟨508708, by decide⟩,⟨508738, by decide⟩,⟨508760, by decide⟩,⟨508767, by decide⟩]) unmarked_context_12_72467_508768 node_context_12_72467_508768
  intro a
  fin_cases a
  · exact context_13_289868_508708
  · exact context_13_289869_508738
  · exact context_13_289870_508760
  · exact context_13_289871_508767

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
