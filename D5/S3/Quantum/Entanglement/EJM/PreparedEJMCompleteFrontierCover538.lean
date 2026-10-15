/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover537
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_51651 : selected 9 ⟨1491931, by decide⟩
    (prefixPartial 12 1133346) = some ⟨12, 2, 0, 1491931, 1133346, 1469, 65536⟩ := by
  decide +kernel

theorem context_12_1133346_1491931 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1133346 ⟨1491931, by decide⟩ :=
  accepted_of_selected 12 1133346 ⟨1491931, by decide⟩ ⟨12, 2, 0, 1491931, 1133346, 1469, 65536⟩
    (by decide) selected_cut_51651

theorem selected_cut_51652 : selected 9 ⟨1491962, by decide⟩
    (prefixPartial 12 1133347) = some ⟨12, 2, 0, 1491962, 1133347, 1505, 65536⟩ := by
  decide +kernel

theorem context_12_1133347_1491962 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1133347 ⟨1491962, by decide⟩ :=
  accepted_of_selected 12 1133347 ⟨1491962, by decide⟩ ⟨12, 2, 0, 1491962, 1133347, 1505, 65536⟩
    (by decide) selected_cut_51652

theorem unmarked_context_11_283336_1491963 : frontier 10 ⟨1491963, by decide⟩
    (prefixCache 11 283336) (prefixPartial 11 283336) = false := by
  decide +kernel

theorem node_context_11_283336_1491963 : EJMOriginalGlobalDAGData.nodes 10 ⟨1491963, by decide⟩ =
    .split (coordinate 11) (![⟨1469342, by decide⟩,⟨1491855, by decide⟩,⟨1491931, by decide⟩,⟨1491962, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_283336_1491963 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 283336 ⟨1491963, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 283336
    ⟨1491963, by decide⟩ (by decide) (![⟨1469342, by decide⟩,⟨1491855, by decide⟩,⟨1491931, by decide⟩,⟨1491962, by decide⟩]) unmarked_context_11_283336_1491963 node_context_11_283336_1491963
  intro a
  fin_cases a
  · exact context_12_1133344_1469342
  · exact context_12_1133345_1491855
  · exact context_12_1133346_1491931
  · exact context_12_1133347_1491962

theorem selected_cut_51653 : selected 10 ⟨1492039, by decide⟩
    (prefixPartial 11 283337) = some ⟨11, 2, 0, 1492039, 283337, 3277, 262144⟩ := by
  decide +kernel

theorem context_11_283337_1492039 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 283337 ⟨1492039, by decide⟩ :=
  accepted_of_selected 11 283337 ⟨1492039, by decide⟩ ⟨11, 2, 0, 1492039, 283337, 3277, 262144⟩
    (by decide) selected_cut_51653

theorem selected_cut_51654 : selected 10 ⟨1468743, by decide⟩
    (prefixPartial 11 283338) = some ⟨11, 1, 0, 1468743, 283338, 1, 262144⟩ := by
  decide +kernel

theorem context_11_283338_1468743 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 283338 ⟨1468743, by decide⟩ :=
  accepted_of_selected 11 283338 ⟨1468743, by decide⟩ ⟨11, 1, 0, 1468743, 283338, 1, 262144⟩
    (by decide) selected_cut_51654

theorem selected_cut_51655 : selected 10 ⟨1492103, by decide⟩
    (prefixPartial 11 283339) = some ⟨11, 2, 0, 1492103, 283339, 3121, 262144⟩ := by
  decide +kernel

theorem context_11_283339_1492103 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 283339 ⟨1492103, by decide⟩ :=
  accepted_of_selected 11 283339 ⟨1492103, by decide⟩ ⟨11, 2, 0, 1492103, 283339, 3121, 262144⟩
    (by decide) selected_cut_51655

theorem unmarked_context_10_70834_1492104 : frontier 11 ⟨1492104, by decide⟩
    (prefixCache 10 70834) (prefixPartial 10 70834) = false := by
  decide +kernel

theorem node_context_10_70834_1492104 : EJMOriginalGlobalDAGData.nodes 11 ⟨1492104, by decide⟩ =
    .split (coordinate 10) (![⟨1491963, by decide⟩,⟨1492039, by decide⟩,⟨1468743, by decide⟩,⟨1492103, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_70834_1492104 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70834 ⟨1492104, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 70834
    ⟨1492104, by decide⟩ (by decide) (![⟨1491963, by decide⟩,⟨1492039, by decide⟩,⟨1468743, by decide⟩,⟨1492103, by decide⟩]) unmarked_context_10_70834_1492104 node_context_10_70834_1492104
  intro a
  fin_cases a
  · exact context_11_283336_1491963
  · exact context_11_283337_1492039
  · exact context_11_283338_1468743
  · exact context_11_283339_1492103

theorem selected_cut_51656 : selected 9 ⟨1470651, by decide⟩
    (prefixPartial 12 1133360) = some ⟨12, 1, 0, 1470651, 1133360, 1, 65536⟩ := by
  decide +kernel

theorem context_12_1133360_1470651 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1133360 ⟨1470651, by decide⟩ :=
  accepted_of_selected 12 1133360 ⟨1470651, by decide⟩ ⟨12, 1, 0, 1470651, 1133360, 1, 65536⟩
    (by decide) selected_cut_51656

theorem selected_cut_51657 : selected 9 ⟨1492129, by decide⟩
    (prefixPartial 12 1133361) = some ⟨12, 2, 0, 1492129, 1133361, 1477, 65536⟩ := by
  decide +kernel

theorem context_12_1133361_1492129 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1133361 ⟨1492129, by decide⟩ :=
  accepted_of_selected 12 1133361 ⟨1492129, by decide⟩ ⟨12, 2, 0, 1492129, 1133361, 1477, 65536⟩
    (by decide) selected_cut_51657

theorem selected_cut_51658 : selected 9 ⟨1492159, by decide⟩
    (prefixPartial 12 1133362) = some ⟨12, 2, 0, 1492159, 1133362, 1385, 65536⟩ := by
  decide +kernel

theorem context_12_1133362_1492159 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1133362 ⟨1492159, by decide⟩ :=
  accepted_of_selected 12 1133362 ⟨1492159, by decide⟩ ⟨12, 2, 0, 1492159, 1133362, 1385, 65536⟩
    (by decide) selected_cut_51658

theorem selected_cut_51659 : selected 9 ⟨1492182, by decide⟩
    (prefixPartial 12 1133363) = some ⟨12, 2, 0, 1492182, 1133363, 1353, 65536⟩ := by
  decide +kernel

theorem context_12_1133363_1492182 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1133363 ⟨1492182, by decide⟩ :=
  accepted_of_selected 12 1133363 ⟨1492182, by decide⟩ ⟨12, 2, 0, 1492182, 1133363, 1353, 65536⟩
    (by decide) selected_cut_51659

theorem unmarked_context_11_283340_1492183 : frontier 10 ⟨1492183, by decide⟩
    (prefixCache 11 283340) (prefixPartial 11 283340) = false := by
  decide +kernel

theorem node_context_11_283340_1492183 : EJMOriginalGlobalDAGData.nodes 10 ⟨1492183, by decide⟩ =
    .split (coordinate 11) (![⟨1470651, by decide⟩,⟨1492129, by decide⟩,⟨1492159, by decide⟩,⟨1492182, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_283340_1492183 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 283340 ⟨1492183, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 283340
    ⟨1492183, by decide⟩ (by decide) (![⟨1470651, by decide⟩,⟨1492129, by decide⟩,⟨1492159, by decide⟩,⟨1492182, by decide⟩]) unmarked_context_11_283340_1492183 node_context_11_283340_1492183
  intro a
  fin_cases a
  · exact context_12_1133360_1470651
  · exact context_12_1133361_1492129
  · exact context_12_1133362_1492159
  · exact context_12_1133363_1492182

theorem selected_cut_51660 : selected 10 ⟨1492234, by decide⟩
    (prefixPartial 11 283341) = some ⟨11, 2, 0, 1492234, 283341, 2769, 262144⟩ := by
  decide +kernel

theorem context_11_283341_1492234 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 283341 ⟨1492234, by decide⟩ :=
  accepted_of_selected 11 283341 ⟨1492234, by decide⟩ ⟨11, 2, 0, 1492234, 283341, 2769, 262144⟩
    (by decide) selected_cut_51660

theorem selected_cut_51661 : selected 10 ⟨1492273, by decide⟩
    (prefixPartial 11 283342) = some ⟨11, 2, 0, 1492273, 283342, 2449, 262144⟩ := by
  decide +kernel

theorem context_11_283342_1492273 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 283342 ⟨1492273, by decide⟩ :=
  accepted_of_selected 11 283342 ⟨1492273, by decide⟩ ⟨11, 2, 0, 1492273, 283342, 2449, 262144⟩
    (by decide) selected_cut_51661

theorem selected_cut_51662 : selected 10 ⟨1470044, by decide⟩
    (prefixPartial 11 283343) = some ⟨11, 1, 0, 1470044, 283343, 1, 262144⟩ := by
  decide +kernel

theorem context_11_283343_1470044 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 283343 ⟨1470044, by decide⟩ :=
  accepted_of_selected 11 283343 ⟨1470044, by decide⟩ ⟨11, 1, 0, 1470044, 283343, 1, 262144⟩
    (by decide) selected_cut_51662

theorem unmarked_context_10_70835_1492274 : frontier 11 ⟨1492274, by decide⟩
    (prefixCache 10 70835) (prefixPartial 10 70835) = false := by
  decide +kernel

theorem node_context_10_70835_1492274 : EJMOriginalGlobalDAGData.nodes 11 ⟨1492274, by decide⟩ =
    .split (coordinate 10) (![⟨1492183, by decide⟩,⟨1492234, by decide⟩,⟨1492273, by decide⟩,⟨1470044, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_70835_1492274 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70835 ⟨1492274, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 70835
    ⟨1492274, by decide⟩ (by decide) (![⟨1492183, by decide⟩,⟨1492234, by decide⟩,⟨1492273, by decide⟩,⟨1470044, by decide⟩]) unmarked_context_10_70835_1492274 node_context_10_70835_1492274
  intro a
  fin_cases a
  · exact context_11_283340_1492183
  · exact context_11_283341_1492234
  · exact context_11_283342_1492273
  · exact context_11_283343_1470044

theorem unmarked_context_9_17708_1492275 : frontier 12 ⟨1492275, by decide⟩
    (prefixCache 9 17708) (prefixPartial 9 17708) = false := by
  decide +kernel

theorem node_context_9_17708_1492275 : EJMOriginalGlobalDAGData.nodes 12 ⟨1492275, by decide⟩ =
    .split (coordinate 9) (![⟨1468246, by decide⟩,⟨1491818, by decide⟩,⟨1492104, by decide⟩,⟨1492274, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_17708_1492275 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17708 ⟨1492275, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 17708
    ⟨1492275, by decide⟩ (by decide) (![⟨1468246, by decide⟩,⟨1491818, by decide⟩,⟨1492104, by decide⟩,⟨1492274, by decide⟩]) unmarked_context_9_17708_1492275 node_context_9_17708_1492275
  intro a
  fin_cases a
  · exact context_10_70832_1468246
  · exact context_10_70833_1491818
  · exact context_10_70834_1492104
  · exact context_10_70835_1492274

theorem selected_cut_51663 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 283344) = some ⟨11, 1, 0, 434745, 283344, 1, 262144⟩ := by
  decide +kernel

theorem context_11_283344_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 283344 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 283344 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 283344, 1, 262144⟩
    (by decide) selected_cut_51663

theorem selected_cut_51664 : selected 10 ⟨1492324, by decide⟩
    (prefixPartial 11 283345) = some ⟨11, 2, 0, 1492324, 283345, 2081, 262144⟩ := by
  decide +kernel

theorem context_11_283345_1492324 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 283345 ⟨1492324, by decide⟩ :=
  accepted_of_selected 11 283345 ⟨1492324, by decide⟩ ⟨11, 2, 0, 1492324, 283345, 2081, 262144⟩
    (by decide) selected_cut_51664

theorem selected_cut_51665 : selected 10 ⟨1492356, by decide⟩
    (prefixPartial 11 283346) = some ⟨11, 2, 0, 1492356, 283346, 1661, 262144⟩ := by
  decide +kernel

theorem context_11_283346_1492356 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 283346 ⟨1492356, by decide⟩ :=
  accepted_of_selected 11 283346 ⟨1492356, by decide⟩ ⟨11, 2, 0, 1492356, 283346, 1661, 262144⟩
    (by decide) selected_cut_51665

theorem selected_cut_51666 : selected 10 ⟨1492394, by decide⟩
    (prefixPartial 11 283347) = some ⟨11, 2, 0, 1492394, 283347, 1845, 262144⟩ := by
  decide +kernel

theorem context_11_283347_1492394 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 283347 ⟨1492394, by decide⟩ :=
  accepted_of_selected 11 283347 ⟨1492394, by decide⟩ ⟨11, 2, 0, 1492394, 283347, 1845, 262144⟩
    (by decide) selected_cut_51666

theorem unmarked_context_10_70836_1492395 : frontier 11 ⟨1492395, by decide⟩
    (prefixCache 10 70836) (prefixPartial 10 70836) = false := by
  decide +kernel

theorem node_context_10_70836_1492395 : EJMOriginalGlobalDAGData.nodes 11 ⟨1492395, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨1492324, by decide⟩,⟨1492356, by decide⟩,⟨1492394, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_70836_1492395 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70836 ⟨1492395, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 70836
    ⟨1492395, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨1492324, by decide⟩,⟨1492356, by decide⟩,⟨1492394, by decide⟩]) unmarked_context_10_70836_1492395 node_context_10_70836_1492395
  intro a
  fin_cases a
  · exact context_11_283344_434745
  · exact context_11_283345_1492324
  · exact context_11_283346_1492356
  · exact context_11_283347_1492394

theorem selected_cut_51667 : selected 11 ⟨1468874, by decide⟩
    (prefixPartial 10 70837) = some ⟨10, 1, 0, 1468874, 70837, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_70837_1468874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70837 ⟨1468874, by decide⟩ :=
  accepted_of_selected 10 70837 ⟨1468874, by decide⟩ ⟨10, 1, 0, 1468874, 70837, 1, 1048576⟩
    (by decide) selected_cut_51667

theorem selected_cut_51668 : selected 10 ⟨1492432, by decide⟩
    (prefixPartial 11 283352) = some ⟨11, 2, 0, 1492432, 283352, 1713, 262144⟩ := by
  decide +kernel

theorem context_11_283352_1492432 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 283352 ⟨1492432, by decide⟩ :=
  accepted_of_selected 11 283352 ⟨1492432, by decide⟩ ⟨11, 2, 0, 1492432, 283352, 1713, 262144⟩
    (by decide) selected_cut_51668

theorem selected_cut_51669 : selected 10 ⟨1492482, by decide⟩
    (prefixPartial 11 283353) = some ⟨11, 2, 0, 1492482, 283353, 2457, 262144⟩ := by
  decide +kernel

theorem context_11_283353_1492482 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 283353 ⟨1492482, by decide⟩ :=
  accepted_of_selected 11 283353 ⟨1492482, by decide⟩ ⟨11, 2, 0, 1492482, 283353, 2457, 262144⟩
    (by decide) selected_cut_51669

theorem selected_cut_51670 : selected 10 ⟨1468743, by decide⟩
    (prefixPartial 11 283354) = some ⟨11, 1, 0, 1468743, 283354, 1, 262144⟩ := by
  decide +kernel

theorem context_11_283354_1468743 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 283354 ⟨1468743, by decide⟩ :=
  accepted_of_selected 11 283354 ⟨1468743, by decide⟩ ⟨11, 1, 0, 1468743, 283354, 1, 262144⟩
    (by decide) selected_cut_51670

theorem selected_cut_51671 : selected 10 ⟨1492518, by decide⟩
    (prefixPartial 11 283355) = some ⟨11, 2, 0, 1492518, 283355, 1641, 262144⟩ := by
  decide +kernel

theorem context_11_283355_1492518 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 283355 ⟨1492518, by decide⟩ :=
  accepted_of_selected 11 283355 ⟨1492518, by decide⟩ ⟨11, 2, 0, 1492518, 283355, 1641, 262144⟩
    (by decide) selected_cut_51671

theorem unmarked_context_10_70838_1492519 : frontier 11 ⟨1492519, by decide⟩
    (prefixCache 10 70838) (prefixPartial 10 70838) = false := by
  decide +kernel

theorem node_context_10_70838_1492519 : EJMOriginalGlobalDAGData.nodes 11 ⟨1492519, by decide⟩ =
    .split (coordinate 10) (![⟨1492432, by decide⟩,⟨1492482, by decide⟩,⟨1468743, by decide⟩,⟨1492518, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_70838_1492519 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70838 ⟨1492519, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 70838
    ⟨1492519, by decide⟩ (by decide) (![⟨1492432, by decide⟩,⟨1492482, by decide⟩,⟨1468743, by decide⟩,⟨1492518, by decide⟩]) unmarked_context_10_70838_1492519 node_context_10_70838_1492519
  intro a
  fin_cases a
  · exact context_11_283352_1492432
  · exact context_11_283353_1492482
  · exact context_11_283354_1468743
  · exact context_11_283355_1492518

theorem selected_cut_51672 : selected 10 ⟨1492549, by decide⟩
    (prefixPartial 11 283356) = some ⟨11, 2, 0, 1492549, 283356, 1489, 262144⟩ := by
  decide +kernel

theorem context_11_283356_1492549 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 283356 ⟨1492549, by decide⟩ :=
  accepted_of_selected 11 283356 ⟨1492549, by decide⟩ ⟨11, 2, 0, 1492549, 283356, 1489, 262144⟩
    (by decide) selected_cut_51672

theorem selected_cut_51673 : selected 10 ⟨1492604, by decide⟩
    (prefixPartial 11 283357) = some ⟨11, 2, 0, 1492604, 283357, 1781, 262144⟩ := by
  decide +kernel

theorem context_11_283357_1492604 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 283357 ⟨1492604, by decide⟩ :=
  accepted_of_selected 11 283357 ⟨1492604, by decide⟩ ⟨11, 2, 0, 1492604, 283357, 1781, 262144⟩
    (by decide) selected_cut_51673

theorem selected_cut_51674 : selected 10 ⟨1492627, by decide⟩
    (prefixPartial 11 283358) = some ⟨11, 2, 0, 1492627, 283358, 1281, 262144⟩ := by
  decide +kernel

theorem context_11_283358_1492627 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 283358 ⟨1492627, by decide⟩ :=
  accepted_of_selected 11 283358 ⟨1492627, by decide⟩ ⟨11, 2, 0, 1492627, 283358, 1281, 262144⟩
    (by decide) selected_cut_51674

theorem selected_cut_51675 : selected 10 ⟨1470044, by decide⟩
    (prefixPartial 11 283359) = some ⟨11, 1, 0, 1470044, 283359, 1, 262144⟩ := by
  decide +kernel

theorem context_11_283359_1470044 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 283359 ⟨1470044, by decide⟩ :=
  accepted_of_selected 11 283359 ⟨1470044, by decide⟩ ⟨11, 1, 0, 1470044, 283359, 1, 262144⟩
    (by decide) selected_cut_51675

theorem unmarked_context_10_70839_1492628 : frontier 11 ⟨1492628, by decide⟩
    (prefixCache 10 70839) (prefixPartial 10 70839) = false := by
  decide +kernel

theorem node_context_10_70839_1492628 : EJMOriginalGlobalDAGData.nodes 11 ⟨1492628, by decide⟩ =
    .split (coordinate 10) (![⟨1492549, by decide⟩,⟨1492604, by decide⟩,⟨1492627, by decide⟩,⟨1470044, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_70839_1492628 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70839 ⟨1492628, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 70839
    ⟨1492628, by decide⟩ (by decide) (![⟨1492549, by decide⟩,⟨1492604, by decide⟩,⟨1492627, by decide⟩,⟨1470044, by decide⟩]) unmarked_context_10_70839_1492628 node_context_10_70839_1492628
  intro a
  fin_cases a
  · exact context_11_283356_1492549
  · exact context_11_283357_1492604
  · exact context_11_283358_1492627
  · exact context_11_283359_1470044

theorem unmarked_context_9_17709_1492629 : frontier 12 ⟨1492629, by decide⟩
    (prefixCache 9 17709) (prefixPartial 9 17709) = false := by
  decide +kernel

theorem node_context_9_17709_1492629 : EJMOriginalGlobalDAGData.nodes 12 ⟨1492629, by decide⟩ =
    .split (coordinate 9) (![⟨1492395, by decide⟩,⟨1468874, by decide⟩,⟨1492519, by decide⟩,⟨1492628, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_17709_1492629 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17709 ⟨1492629, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 17709
    ⟨1492629, by decide⟩ (by decide) (![⟨1492395, by decide⟩,⟨1468874, by decide⟩,⟨1492519, by decide⟩,⟨1492628, by decide⟩]) unmarked_context_9_17709_1492629 node_context_9_17709_1492629
  intro a
  fin_cases a
  · exact context_10_70836_1492395
  · exact context_10_70837_1468874
  · exact context_10_70838_1492519
  · exact context_10_70839_1492628

theorem selected_cut_51676 : selected 11 ⟨1492700, by decide⟩
    (prefixPartial 10 70840) = some ⟨10, 2, 0, 1492700, 70840, 3329, 1048576⟩ := by
  decide +kernel

theorem context_10_70840_1492700 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70840 ⟨1492700, by decide⟩ :=
  accepted_of_selected 10 70840 ⟨1492700, by decide⟩ ⟨10, 2, 0, 1492700, 70840, 3329, 1048576⟩
    (by decide) selected_cut_51676

theorem selected_cut_51677 : selected 11 ⟨1492767, by decide⟩
    (prefixPartial 10 70841) = some ⟨10, 2, 0, 1492767, 70841, 3221, 1048576⟩ := by
  decide +kernel

theorem context_10_70841_1492767 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70841 ⟨1492767, by decide⟩ :=
  accepted_of_selected 10 70841 ⟨1492767, by decide⟩ ⟨10, 2, 0, 1492767, 70841, 3221, 1048576⟩
    (by decide) selected_cut_51677

theorem selected_cut_51678 : selected 11 ⟨1469103, by decide⟩
    (prefixPartial 10 70842) = some ⟨10, 1, 0, 1469103, 70842, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_70842_1469103 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70842 ⟨1469103, by decide⟩ :=
  accepted_of_selected 10 70842 ⟨1469103, by decide⟩ ⟨10, 1, 0, 1469103, 70842, 1, 1048576⟩
    (by decide) selected_cut_51678

theorem selected_cut_51679 : selected 11 ⟨1492824, by decide⟩
    (prefixPartial 10 70843) = some ⟨10, 2, 0, 1492824, 70843, 2017, 1048576⟩ := by
  decide +kernel

theorem context_10_70843_1492824 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70843 ⟨1492824, by decide⟩ :=
  accepted_of_selected 10 70843 ⟨1492824, by decide⟩ ⟨10, 2, 0, 1492824, 70843, 2017, 1048576⟩
    (by decide) selected_cut_51679

theorem unmarked_context_9_17710_1492825 : frontier 12 ⟨1492825, by decide⟩
    (prefixCache 9 17710) (prefixPartial 9 17710) = false := by
  decide +kernel

theorem node_context_9_17710_1492825 : EJMOriginalGlobalDAGData.nodes 12 ⟨1492825, by decide⟩ =
    .split (coordinate 9) (![⟨1492700, by decide⟩,⟨1492767, by decide⟩,⟨1469103, by decide⟩,⟨1492824, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_17710_1492825 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17710 ⟨1492825, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 17710
    ⟨1492825, by decide⟩ (by decide) (![⟨1492700, by decide⟩,⟨1492767, by decide⟩,⟨1469103, by decide⟩,⟨1492824, by decide⟩]) unmarked_context_9_17710_1492825 node_context_9_17710_1492825
  intro a
  fin_cases a
  · exact context_10_70840_1492700
  · exact context_10_70841_1492767
  · exact context_10_70842_1469103
  · exact context_10_70843_1492824

theorem selected_cut_51680 : selected 12 ⟨1492905, by decide⟩
    (prefixPartial 9 17711) = some ⟨9, 2, 0, 1492905, 17711, 2693, 4194304⟩ := by
  decide +kernel

theorem context_9_17711_1492905 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17711 ⟨1492905, by decide⟩ :=
  accepted_of_selected 9 17711 ⟨1492905, by decide⟩ ⟨9, 2, 0, 1492905, 17711, 2693, 4194304⟩
    (by decide) selected_cut_51680

theorem unmarked_context_8_4427_1492906 : frontier 13 ⟨1492906, by decide⟩
    (prefixCache 8 4427) (prefixPartial 8 4427) = false := by
  decide +kernel

theorem node_context_8_4427_1492906 : EJMOriginalGlobalDAGData.nodes 13 ⟨1492906, by decide⟩ =
    .split (coordinate 8) (![⟨1492275, by decide⟩,⟨1492629, by decide⟩,⟨1492825, by decide⟩,⟨1492905, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_4427_1492906 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4427 ⟨1492906, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 4427
    ⟨1492906, by decide⟩ (by decide) (![⟨1492275, by decide⟩,⟨1492629, by decide⟩,⟨1492825, by decide⟩,⟨1492905, by decide⟩]) unmarked_context_8_4427_1492906 node_context_8_4427_1492906
  intro a
  fin_cases a
  · exact context_9_17708_1492275
  · exact context_9_17709_1492629
  · exact context_9_17710_1492825
  · exact context_9_17711_1492905

theorem unmarked_context_7_1106_1492907 : frontier 14 ⟨1492907, by decide⟩
    (prefixCache 7 1106) (prefixPartial 7 1106) = false := by
  decide +kernel

theorem node_context_7_1106_1492907 : EJMOriginalGlobalDAGData.nodes 14 ⟨1492907, by decide⟩ =
    .split (coordinate 7) (![⟨1490305, by decide⟩,⟨1487330, by decide⟩,⟨1491507, by decide⟩,⟨1492906, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_7_1106_1492907 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 1106 ⟨1492907, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 7 1106
    ⟨1492907, by decide⟩ (by decide) (![⟨1490305, by decide⟩,⟨1487330, by decide⟩,⟨1491507, by decide⟩,⟨1492906, by decide⟩]) unmarked_context_7_1106_1492907 node_context_7_1106_1492907
  intro a
  fin_cases a
  · exact context_8_4424_1490305
  · exact context_8_4425_1487330
  · exact context_8_4426_1491507
  · exact context_8_4427_1492906

theorem selected_cut_51681 : selected 14 ⟨34032, by decide⟩
    (prefixPartial 7 1107) = some ⟨7, 1, 0, 34032, 1107, 1, 67108864⟩ := by
  decide +kernel

theorem context_7_1107_34032 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 1107 ⟨34032, by decide⟩ :=
  accepted_of_selected 7 1107 ⟨34032, by decide⟩ ⟨7, 1, 0, 34032, 1107, 1, 67108864⟩
    (by decide) selected_cut_51681

theorem unmarked_context_6_276_1492908 : frontier 15 ⟨1492908, by decide⟩
    (prefixCache 6 276) (prefixPartial 6 276) = false := by
  decide +kernel

theorem node_context_6_276_1492908 : EJMOriginalGlobalDAGData.nodes 15 ⟨1492908, by decide⟩ =
    .split (coordinate 6) (![⟨1488620, by decide⟩,⟨1490304, by decide⟩,⟨1492907, by decide⟩,⟨34032, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_6_276_1492908 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 6 276 ⟨1492908, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 6 276
    ⟨1492908, by decide⟩ (by decide) (![⟨1488620, by decide⟩,⟨1490304, by decide⟩,⟨1492907, by decide⟩,⟨34032, by decide⟩]) unmarked_context_6_276_1492908 node_context_6_276_1492908
  intro a
  fin_cases a
  · exact context_7_1104_1488620
  · exact context_7_1105_1490304
  · exact context_7_1106_1492907
  · exact context_7_1107_34032

theorem selected_cut_51682 : selected 15 ⟨1475984, by decide⟩
    (prefixPartial 6 277) = some ⟨6, 1, 0, 1475984, 277, 1, 268435456⟩ := by
  decide +kernel

theorem context_6_277_1475984 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 6 277 ⟨1475984, by decide⟩ :=
  accepted_of_selected 6 277 ⟨1475984, by decide⟩ ⟨6, 1, 0, 1475984, 277, 1, 268435456⟩
    (by decide) selected_cut_51682

theorem selected_cut_51683 : selected 11 ⟨1468246, by decide⟩
    (prefixPartial 10 71168) = some ⟨10, 1, 0, 1468246, 71168, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_71168_1468246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71168 ⟨1468246, by decide⟩ :=
  accepted_of_selected 10 71168 ⟨1468246, by decide⟩ ⟨10, 1, 0, 1468246, 71168, 1, 1048576⟩
    (by decide) selected_cut_51683

theorem selected_cut_51684 : selected 10 ⟨1492980, by decide⟩
    (prefixPartial 11 284676) = some ⟨11, 2, 0, 1492980, 284676, 2297, 262144⟩ := by
  decide +kernel

theorem context_11_284676_1492980 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 284676 ⟨1492980, by decide⟩ :=
  accepted_of_selected 11 284676 ⟨1492980, by decide⟩ ⟨11, 2, 0, 1492980, 284676, 2297, 262144⟩
    (by decide) selected_cut_51684

theorem selected_cut_51685 : selected 10 ⟨1468419, by decide⟩
    (prefixPartial 11 284677) = some ⟨11, 1, 0, 1468419, 284677, 1, 262144⟩ := by
  decide +kernel

theorem context_11_284677_1468419 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 284677 ⟨1468419, by decide⟩ :=
  accepted_of_selected 11 284677 ⟨1468419, by decide⟩ ⟨11, 1, 0, 1468419, 284677, 1, 262144⟩
    (by decide) selected_cut_51685

theorem selected_cut_51686 : selected 10 ⟨1493069, by decide⟩
    (prefixPartial 11 284678) = some ⟨11, 2, 0, 1493069, 284678, 2649, 262144⟩ := by
  decide +kernel

theorem context_11_284678_1493069 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 284678 ⟨1493069, by decide⟩ :=
  accepted_of_selected 11 284678 ⟨1493069, by decide⟩ ⟨11, 2, 0, 1493069, 284678, 2649, 262144⟩
    (by decide) selected_cut_51686

theorem selected_cut_51687 : selected 10 ⟨1493127, by decide⟩
    (prefixPartial 11 284679) = some ⟨11, 2, 0, 1493127, 284679, 1801, 262144⟩ := by
  decide +kernel

theorem context_11_284679_1493127 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 284679 ⟨1493127, by decide⟩ :=
  accepted_of_selected 11 284679 ⟨1493127, by decide⟩ ⟨11, 2, 0, 1493127, 284679, 1801, 262144⟩
    (by decide) selected_cut_51687

theorem unmarked_context_10_71169_1493128 : frontier 11 ⟨1493128, by decide⟩
    (prefixCache 10 71169) (prefixPartial 10 71169) = false := by
  decide +kernel

theorem node_context_10_71169_1493128 : EJMOriginalGlobalDAGData.nodes 11 ⟨1493128, by decide⟩ =
    .split (coordinate 10) (![⟨1492980, by decide⟩,⟨1468419, by decide⟩,⟨1493069, by decide⟩,⟨1493127, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_71169_1493128 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71169 ⟨1493128, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 71169
    ⟨1493128, by decide⟩ (by decide) (![⟨1492980, by decide⟩,⟨1468419, by decide⟩,⟨1493069, by decide⟩,⟨1493127, by decide⟩]) unmarked_context_10_71169_1493128 node_context_10_71169_1493128
  intro a
  fin_cases a
  · exact context_11_284676_1492980
  · exact context_11_284677_1468419
  · exact context_11_284678_1493069
  · exact context_11_284679_1493127

theorem selected_cut_51688 : selected 10 ⟨1493177, by decide⟩
    (prefixPartial 11 284680) = some ⟨11, 2, 0, 1493177, 284680, 1989, 262144⟩ := by
  decide +kernel

theorem context_11_284680_1493177 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 284680 ⟨1493177, by decide⟩ :=
  accepted_of_selected 11 284680 ⟨1493177, by decide⟩ ⟨11, 2, 0, 1493177, 284680, 1989, 262144⟩
    (by decide) selected_cut_51688

theorem selected_cut_51689 : selected 10 ⟨1493243, by decide⟩
    (prefixPartial 11 284681) = some ⟨11, 2, 0, 1493243, 284681, 2309, 262144⟩ := by
  decide +kernel

theorem context_11_284681_1493243 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 284681 ⟨1493243, by decide⟩ :=
  accepted_of_selected 11 284681 ⟨1493243, by decide⟩ ⟨11, 2, 0, 1493243, 284681, 2309, 262144⟩
    (by decide) selected_cut_51689

theorem selected_cut_51690 : selected 10 ⟨1468743, by decide⟩
    (prefixPartial 11 284682) = some ⟨11, 1, 0, 1468743, 284682, 1, 262144⟩ := by
  decide +kernel

theorem context_11_284682_1468743 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 284682 ⟨1468743, by decide⟩ :=
  accepted_of_selected 11 284682 ⟨1468743, by decide⟩ ⟨11, 1, 0, 1468743, 284682, 1, 262144⟩
    (by decide) selected_cut_51690

theorem selected_cut_51691 : selected 10 ⟨1493289, by decide⟩
    (prefixPartial 11 284683) = some ⟨11, 2, 0, 1493289, 284683, 2009, 262144⟩ := by
  decide +kernel

theorem context_11_284683_1493289 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 284683 ⟨1493289, by decide⟩ :=
  accepted_of_selected 11 284683 ⟨1493289, by decide⟩ ⟨11, 2, 0, 1493289, 284683, 2009, 262144⟩
    (by decide) selected_cut_51691

theorem unmarked_context_10_71170_1493290 : frontier 11 ⟨1493290, by decide⟩
    (prefixCache 10 71170) (prefixPartial 10 71170) = false := by
  decide +kernel

theorem node_context_10_71170_1493290 : EJMOriginalGlobalDAGData.nodes 11 ⟨1493290, by decide⟩ =
    .split (coordinate 10) (![⟨1493177, by decide⟩,⟨1493243, by decide⟩,⟨1468743, by decide⟩,⟨1493289, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_71170_1493290 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71170 ⟨1493290, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 71170
    ⟨1493290, by decide⟩ (by decide) (![⟨1493177, by decide⟩,⟨1493243, by decide⟩,⟨1468743, by decide⟩,⟨1493289, by decide⟩]) unmarked_context_10_71170_1493290 node_context_10_71170_1493290
  intro a
  fin_cases a
  · exact context_11_284680_1493177
  · exact context_11_284681_1493243
  · exact context_11_284682_1468743
  · exact context_11_284683_1493289

theorem selected_cut_51692 : selected 10 ⟨1493319, by decide⟩
    (prefixPartial 11 284684) = some ⟨11, 2, 0, 1493319, 284684, 1761, 262144⟩ := by
  decide +kernel

theorem context_11_284684_1493319 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 284684 ⟨1493319, by decide⟩ :=
  accepted_of_selected 11 284684 ⟨1493319, by decide⟩ ⟨11, 2, 0, 1493319, 284684, 1761, 262144⟩
    (by decide) selected_cut_51692

theorem selected_cut_51693 : selected 10 ⟨1493386, by decide⟩
    (prefixPartial 11 284685) = some ⟨11, 2, 0, 1493386, 284685, 2173, 262144⟩ := by
  decide +kernel

theorem context_11_284685_1493386 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 284685 ⟨1493386, by decide⟩ :=
  accepted_of_selected 11 284685 ⟨1493386, by decide⟩ ⟨11, 2, 0, 1493386, 284685, 2173, 262144⟩
    (by decide) selected_cut_51693

theorem selected_cut_51694 : selected 10 ⟨1493425, by decide⟩
    (prefixPartial 11 284686) = some ⟨11, 2, 0, 1493425, 284686, 1845, 262144⟩ := by
  decide +kernel

theorem context_11_284686_1493425 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 284686 ⟨1493425, by decide⟩ :=
  accepted_of_selected 11 284686 ⟨1493425, by decide⟩ ⟨11, 2, 0, 1493425, 284686, 1845, 262144⟩
    (by decide) selected_cut_51694

theorem selected_cut_51695 : selected 10 ⟨1470044, by decide⟩
    (prefixPartial 11 284687) = some ⟨11, 1, 0, 1470044, 284687, 1, 262144⟩ := by
  decide +kernel

theorem context_11_284687_1470044 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 284687 ⟨1470044, by decide⟩ :=
  accepted_of_selected 11 284687 ⟨1470044, by decide⟩ ⟨11, 1, 0, 1470044, 284687, 1, 262144⟩
    (by decide) selected_cut_51695

theorem unmarked_context_10_71171_1493426 : frontier 11 ⟨1493426, by decide⟩
    (prefixCache 10 71171) (prefixPartial 10 71171) = false := by
  decide +kernel

theorem node_context_10_71171_1493426 : EJMOriginalGlobalDAGData.nodes 11 ⟨1493426, by decide⟩ =
    .split (coordinate 10) (![⟨1493319, by decide⟩,⟨1493386, by decide⟩,⟨1493425, by decide⟩,⟨1470044, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_71171_1493426 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71171 ⟨1493426, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 71171
    ⟨1493426, by decide⟩ (by decide) (![⟨1493319, by decide⟩,⟨1493386, by decide⟩,⟨1493425, by decide⟩,⟨1470044, by decide⟩]) unmarked_context_10_71171_1493426 node_context_10_71171_1493426
  intro a
  fin_cases a
  · exact context_11_284684_1493319
  · exact context_11_284685_1493386
  · exact context_11_284686_1493425
  · exact context_11_284687_1470044

theorem unmarked_context_9_17792_1493427 : frontier 12 ⟨1493427, by decide⟩
    (prefixCache 9 17792) (prefixPartial 9 17792) = false := by
  decide +kernel

theorem node_context_9_17792_1493427 : EJMOriginalGlobalDAGData.nodes 12 ⟨1493427, by decide⟩ =
    .split (coordinate 9) (![⟨1468246, by decide⟩,⟨1493128, by decide⟩,⟨1493290, by decide⟩,⟨1493426, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_17792_1493427 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17792 ⟨1493427, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 17792
    ⟨1493427, by decide⟩ (by decide) (![⟨1468246, by decide⟩,⟨1493128, by decide⟩,⟨1493290, by decide⟩,⟨1493426, by decide⟩]) unmarked_context_9_17792_1493427 node_context_9_17792_1493427
  intro a
  fin_cases a
  · exact context_10_71168_1468246
  · exact context_10_71169_1493128
  · exact context_10_71170_1493290
  · exact context_10_71171_1493426

theorem selected_cut_51696 : selected 11 ⟨1493494, by decide⟩
    (prefixPartial 10 71172) = some ⟨10, 2, 0, 1493494, 71172, 2569, 1048576⟩ := by
  decide +kernel

theorem context_10_71172_1493494 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71172 ⟨1493494, by decide⟩ :=
  accepted_of_selected 10 71172 ⟨1493494, by decide⟩ ⟨10, 2, 0, 1493494, 71172, 2569, 1048576⟩
    (by decide) selected_cut_51696

theorem selected_cut_51697 : selected 11 ⟨1468874, by decide⟩
    (prefixPartial 10 71173) = some ⟨10, 1, 0, 1468874, 71173, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_71173_1468874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71173 ⟨1468874, by decide⟩ :=
  accepted_of_selected 10 71173 ⟨1468874, by decide⟩ ⟨10, 1, 0, 1468874, 71173, 1, 1048576⟩
    (by decide) selected_cut_51697

theorem selected_cut_51698 : selected 11 ⟨1493598, by decide⟩
    (prefixPartial 10 71174) = some ⟨10, 2, 0, 1493598, 71174, 3669, 1048576⟩ := by
  decide +kernel

theorem context_10_71174_1493598 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71174 ⟨1493598, by decide⟩ :=
  accepted_of_selected 10 71174 ⟨1493598, by decide⟩ ⟨10, 2, 0, 1493598, 71174, 3669, 1048576⟩
    (by decide) selected_cut_51698

theorem selected_cut_51699 : selected 11 ⟨1493682, by decide⟩
    (prefixPartial 10 71175) = some ⟨10, 2, 0, 1493682, 71175, 2989, 1048576⟩ := by
  decide +kernel

theorem context_10_71175_1493682 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71175 ⟨1493682, by decide⟩ :=
  accepted_of_selected 10 71175 ⟨1493682, by decide⟩ ⟨10, 2, 0, 1493682, 71175, 2989, 1048576⟩
    (by decide) selected_cut_51699

theorem unmarked_context_9_17793_1493683 : frontier 12 ⟨1493683, by decide⟩
    (prefixCache 9 17793) (prefixPartial 9 17793) = false := by
  decide +kernel

theorem node_context_9_17793_1493683 : EJMOriginalGlobalDAGData.nodes 12 ⟨1493683, by decide⟩ =
    .split (coordinate 9) (![⟨1493494, by decide⟩,⟨1468874, by decide⟩,⟨1493598, by decide⟩,⟨1493682, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_17793_1493683 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17793 ⟨1493683, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 17793
    ⟨1493683, by decide⟩ (by decide) (![⟨1493494, by decide⟩,⟨1468874, by decide⟩,⟨1493598, by decide⟩,⟨1493682, by decide⟩]) unmarked_context_9_17793_1493683 node_context_9_17793_1493683
  intro a
  fin_cases a
  · exact context_10_71172_1493494
  · exact context_10_71173_1468874
  · exact context_10_71174_1493598
  · exact context_10_71175_1493682

theorem selected_cut_51700 : selected 11 ⟨1493725, by decide⟩
    (prefixPartial 10 71176) = some ⟨10, 2, 0, 1493725, 71176, 1861, 1048576⟩ := by
  decide +kernel

theorem context_10_71176_1493725 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71176 ⟨1493725, by decide⟩ :=
  accepted_of_selected 10 71176 ⟨1493725, by decide⟩ ⟨10, 2, 0, 1493725, 71176, 1861, 1048576⟩
    (by decide) selected_cut_51700

theorem selected_cut_51701 : selected 11 ⟨1493795, by decide⟩
    (prefixPartial 10 71177) = some ⟨10, 2, 0, 1493795, 71177, 2657, 1048576⟩ := by
  decide +kernel

theorem context_10_71177_1493795 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71177 ⟨1493795, by decide⟩ :=
  accepted_of_selected 10 71177 ⟨1493795, by decide⟩ ⟨10, 2, 0, 1493795, 71177, 2657, 1048576⟩
    (by decide) selected_cut_51701

theorem selected_cut_51702 : selected 11 ⟨1469103, by decide⟩
    (prefixPartial 10 71178) = some ⟨10, 1, 0, 1469103, 71178, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_71178_1469103 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71178 ⟨1469103, by decide⟩ :=
  accepted_of_selected 10 71178 ⟨1469103, by decide⟩ ⟨10, 1, 0, 1469103, 71178, 1, 1048576⟩
    (by decide) selected_cut_51702

theorem selected_cut_51703 : selected 11 ⟨1493852, by decide⟩
    (prefixPartial 10 71179) = some ⟨10, 2, 0, 1493852, 71179, 1889, 1048576⟩ := by
  decide +kernel

theorem context_10_71179_1493852 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71179 ⟨1493852, by decide⟩ :=
  accepted_of_selected 10 71179 ⟨1493852, by decide⟩ ⟨10, 2, 0, 1493852, 71179, 1889, 1048576⟩
    (by decide) selected_cut_51703

theorem unmarked_context_9_17794_1493853 : frontier 12 ⟨1493853, by decide⟩
    (prefixCache 9 17794) (prefixPartial 9 17794) = false := by
  decide +kernel

theorem node_context_9_17794_1493853 : EJMOriginalGlobalDAGData.nodes 12 ⟨1493853, by decide⟩ =
    .split (coordinate 9) (![⟨1493725, by decide⟩,⟨1493795, by decide⟩,⟨1469103, by decide⟩,⟨1493852, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_17794_1493853 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17794 ⟨1493853, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 17794
    ⟨1493853, by decide⟩ (by decide) (![⟨1493725, by decide⟩,⟨1493795, by decide⟩,⟨1469103, by decide⟩,⟨1493852, by decide⟩]) unmarked_context_9_17794_1493853 node_context_9_17794_1493853
  intro a
  fin_cases a
  · exact context_10_71176_1493725
  · exact context_10_71177_1493795
  · exact context_10_71178_1469103
  · exact context_10_71179_1493852

theorem selected_cut_51704 : selected 12 ⟨1493896, by decide⟩
    (prefixPartial 9 17795) = some ⟨9, 2, 0, 1493896, 17795, 1773, 4194304⟩ := by
  decide +kernel

theorem context_9_17795_1493896 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17795 ⟨1493896, by decide⟩ :=
  accepted_of_selected 9 17795 ⟨1493896, by decide⟩ ⟨9, 2, 0, 1493896, 17795, 1773, 4194304⟩
    (by decide) selected_cut_51704

theorem unmarked_context_8_4448_1493897 : frontier 13 ⟨1493897, by decide⟩
    (prefixCache 8 4448) (prefixPartial 8 4448) = false := by
  decide +kernel

theorem node_context_8_4448_1493897 : EJMOriginalGlobalDAGData.nodes 13 ⟨1493897, by decide⟩ =
    .split (coordinate 8) (![⟨1493427, by decide⟩,⟨1493683, by decide⟩,⟨1493853, by decide⟩,⟨1493896, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_4448_1493897 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4448 ⟨1493897, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 4448
    ⟨1493897, by decide⟩ (by decide) (![⟨1493427, by decide⟩,⟨1493683, by decide⟩,⟨1493853, by decide⟩,⟨1493896, by decide⟩]) unmarked_context_8_4448_1493897 node_context_8_4448_1493897
  intro a
  fin_cases a
  · exact context_9_17792_1493427
  · exact context_9_17793_1493683
  · exact context_9_17794_1493853
  · exact context_9_17795_1493896

theorem selected_cut_51705 : selected 11 ⟨1468246, by decide⟩
    (prefixPartial 10 71184) = some ⟨10, 1, 0, 1468246, 71184, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_71184_1468246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71184 ⟨1468246, by decide⟩ :=
  accepted_of_selected 10 71184 ⟨1468246, by decide⟩ ⟨10, 1, 0, 1468246, 71184, 1, 1048576⟩
    (by decide) selected_cut_51705

theorem selected_cut_51706 : selected 10 ⟨1493976, by decide⟩
    (prefixPartial 11 284740) = some ⟨11, 2, 0, 1493976, 284740, 2577, 262144⟩ := by
  decide +kernel

theorem context_11_284740_1493976 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 284740 ⟨1493976, by decide⟩ :=
  accepted_of_selected 11 284740 ⟨1493976, by decide⟩ ⟨11, 2, 0, 1493976, 284740, 2577, 262144⟩
    (by decide) selected_cut_51706

theorem selected_cut_51707 : selected 10 ⟨1468419, by decide⟩
    (prefixPartial 11 284741) = some ⟨11, 1, 0, 1468419, 284741, 1, 262144⟩ := by
  decide +kernel

theorem context_11_284741_1468419 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 284741 ⟨1468419, by decide⟩ :=
  accepted_of_selected 11 284741 ⟨1468419, by decide⟩ ⟨11, 1, 0, 1468419, 284741, 1, 262144⟩
    (by decide) selected_cut_51707

theorem selected_cut_51708 : selected 10 ⟨1494042, by decide⟩
    (prefixPartial 11 284742) = some ⟨11, 2, 0, 1494042, 284742, 2557, 262144⟩ := by
  decide +kernel

theorem context_11_284742_1494042 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 284742 ⟨1494042, by decide⟩ :=
  accepted_of_selected 11 284742 ⟨1494042, by decide⟩ ⟨11, 2, 0, 1494042, 284742, 2557, 262144⟩
    (by decide) selected_cut_51708

theorem selected_cut_51709 : selected 10 ⟨1494097, by decide⟩
    (prefixPartial 11 284743) = some ⟨11, 2, 0, 1494097, 284743, 1965, 262144⟩ := by
  decide +kernel

theorem context_11_284743_1494097 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 284743 ⟨1494097, by decide⟩ :=
  accepted_of_selected 11 284743 ⟨1494097, by decide⟩ ⟨11, 2, 0, 1494097, 284743, 1965, 262144⟩
    (by decide) selected_cut_51709

theorem unmarked_context_10_71185_1494098 : frontier 11 ⟨1494098, by decide⟩
    (prefixCache 10 71185) (prefixPartial 10 71185) = false := by
  decide +kernel

theorem node_context_10_71185_1494098 : EJMOriginalGlobalDAGData.nodes 11 ⟨1494098, by decide⟩ =
    .split (coordinate 10) (![⟨1493976, by decide⟩,⟨1468419, by decide⟩,⟨1494042, by decide⟩,⟨1494097, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_71185_1494098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71185 ⟨1494098, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 71185
    ⟨1494098, by decide⟩ (by decide) (![⟨1493976, by decide⟩,⟨1468419, by decide⟩,⟨1494042, by decide⟩,⟨1494097, by decide⟩]) unmarked_context_10_71185_1494098 node_context_10_71185_1494098
  intro a
  fin_cases a
  · exact context_11_284740_1493976
  · exact context_11_284741_1468419
  · exact context_11_284742_1494042
  · exact context_11_284743_1494097

theorem selected_cut_51710 : selected 10 ⟨1494168, by decide⟩
    (prefixPartial 11 284744) = some ⟨11, 2, 0, 1494168, 284744, 2581, 262144⟩ := by
  decide +kernel

theorem context_11_284744_1494168 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 284744 ⟨1494168, by decide⟩ :=
  accepted_of_selected 11 284744 ⟨1494168, by decide⟩ ⟨11, 2, 0, 1494168, 284744, 2581, 262144⟩
    (by decide) selected_cut_51710

theorem selected_cut_51711 : selected 10 ⟨1494217, by decide⟩
    (prefixPartial 11 284745) = some ⟨11, 2, 0, 1494217, 284745, 2353, 262144⟩ := by
  decide +kernel

theorem context_11_284745_1494217 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 284745 ⟨1494217, by decide⟩ :=
  accepted_of_selected 11 284745 ⟨1494217, by decide⟩ ⟨11, 2, 0, 1494217, 284745, 2353, 262144⟩
    (by decide) selected_cut_51711

theorem selected_cut_51712 : selected 10 ⟨1468743, by decide⟩
    (prefixPartial 11 284746) = some ⟨11, 1, 0, 1468743, 284746, 1, 262144⟩ := by
  decide +kernel

theorem context_11_284746_1468743 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 284746 ⟨1468743, by decide⟩ :=
  accepted_of_selected 11 284746 ⟨1468743, by decide⟩ ⟨11, 1, 0, 1468743, 284746, 1, 262144⟩
    (by decide) selected_cut_51712

theorem selected_cut_51713 : selected 10 ⟨1494271, by decide⟩
    (prefixPartial 11 284747) = some ⟨11, 2, 0, 1494271, 284747, 2437, 262144⟩ := by
  decide +kernel

theorem context_11_284747_1494271 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 284747 ⟨1494271, by decide⟩ :=
  accepted_of_selected 11 284747 ⟨1494271, by decide⟩ ⟨11, 2, 0, 1494271, 284747, 2437, 262144⟩
    (by decide) selected_cut_51713

theorem unmarked_context_10_71186_1494272 : frontier 11 ⟨1494272, by decide⟩
    (prefixCache 10 71186) (prefixPartial 10 71186) = false := by
  decide +kernel

theorem node_context_10_71186_1494272 : EJMOriginalGlobalDAGData.nodes 11 ⟨1494272, by decide⟩ =
    .split (coordinate 10) (![⟨1494168, by decide⟩,⟨1494217, by decide⟩,⟨1468743, by decide⟩,⟨1494271, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_71186_1494272 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71186 ⟨1494272, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 71186
    ⟨1494272, by decide⟩ (by decide) (![⟨1494168, by decide⟩,⟨1494217, by decide⟩,⟨1468743, by decide⟩,⟨1494271, by decide⟩]) unmarked_context_10_71186_1494272 node_context_10_71186_1494272
  intro a
  fin_cases a
  · exact context_11_284744_1494168
  · exact context_11_284745_1494217
  · exact context_11_284746_1468743
  · exact context_11_284747_1494271

theorem selected_cut_51714 : selected 10 ⟨1494346, by decide⟩
    (prefixPartial 11 284748) = some ⟨11, 2, 0, 1494346, 284748, 2493, 262144⟩ := by
  decide +kernel

theorem context_11_284748_1494346 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 284748 ⟨1494346, by decide⟩ :=
  accepted_of_selected 11 284748 ⟨1494346, by decide⟩ ⟨11, 2, 0, 1494346, 284748, 2493, 262144⟩
    (by decide) selected_cut_51714

theorem selected_cut_51715 : selected 10 ⟨1494415, by decide⟩
    (prefixPartial 11 284749) = some ⟨11, 2, 0, 1494415, 284749, 2237, 262144⟩ := by
  decide +kernel

theorem context_11_284749_1494415 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 284749 ⟨1494415, by decide⟩ :=
  accepted_of_selected 11 284749 ⟨1494415, by decide⟩ ⟨11, 2, 0, 1494415, 284749, 2237, 262144⟩
    (by decide) selected_cut_51715

theorem selected_cut_51716 : selected 10 ⟨1494471, by decide⟩
    (prefixPartial 11 284750) = some ⟨11, 2, 0, 1494471, 284750, 2197, 262144⟩ := by
  decide +kernel

theorem context_11_284750_1494471 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 284750 ⟨1494471, by decide⟩ :=
  accepted_of_selected 11 284750 ⟨1494471, by decide⟩ ⟨11, 2, 0, 1494471, 284750, 2197, 262144⟩
    (by decide) selected_cut_51716

theorem selected_cut_51717 : selected 10 ⟨1470044, by decide⟩
    (prefixPartial 11 284751) = some ⟨11, 1, 0, 1470044, 284751, 1, 262144⟩ := by
  decide +kernel

theorem context_11_284751_1470044 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 284751 ⟨1470044, by decide⟩ :=
  accepted_of_selected 11 284751 ⟨1470044, by decide⟩ ⟨11, 1, 0, 1470044, 284751, 1, 262144⟩
    (by decide) selected_cut_51717

theorem unmarked_context_10_71187_1494472 : frontier 11 ⟨1494472, by decide⟩
    (prefixCache 10 71187) (prefixPartial 10 71187) = false := by
  decide +kernel

theorem node_context_10_71187_1494472 : EJMOriginalGlobalDAGData.nodes 11 ⟨1494472, by decide⟩ =
    .split (coordinate 10) (![⟨1494346, by decide⟩,⟨1494415, by decide⟩,⟨1494471, by decide⟩,⟨1470044, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_71187_1494472 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71187 ⟨1494472, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 71187
    ⟨1494472, by decide⟩ (by decide) (![⟨1494346, by decide⟩,⟨1494415, by decide⟩,⟨1494471, by decide⟩,⟨1470044, by decide⟩]) unmarked_context_10_71187_1494472 node_context_10_71187_1494472
  intro a
  fin_cases a
  · exact context_11_284748_1494346
  · exact context_11_284749_1494415
  · exact context_11_284750_1494471
  · exact context_11_284751_1470044

theorem unmarked_context_9_17796_1494473 : frontier 12 ⟨1494473, by decide⟩
    (prefixCache 9 17796) (prefixPartial 9 17796) = false := by
  decide +kernel

theorem node_context_9_17796_1494473 : EJMOriginalGlobalDAGData.nodes 12 ⟨1494473, by decide⟩ =
    .split (coordinate 9) (![⟨1468246, by decide⟩,⟨1494098, by decide⟩,⟨1494272, by decide⟩,⟨1494472, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_17796_1494473 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17796 ⟨1494473, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 17796
    ⟨1494473, by decide⟩ (by decide) (![⟨1468246, by decide⟩,⟨1494098, by decide⟩,⟨1494272, by decide⟩,⟨1494472, by decide⟩]) unmarked_context_9_17796_1494473 node_context_9_17796_1494473
  intro a
  fin_cases a
  · exact context_10_71184_1468246
  · exact context_10_71185_1494098
  · exact context_10_71186_1494272
  · exact context_10_71187_1494472

theorem selected_cut_51718 : selected 11 ⟨1494532, by decide⟩
    (prefixPartial 10 71188) = some ⟨10, 2, 0, 1494532, 71188, 2097, 1048576⟩ := by
  decide +kernel

theorem context_10_71188_1494532 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71188 ⟨1494532, by decide⟩ :=
  accepted_of_selected 10 71188 ⟨1494532, by decide⟩ ⟨10, 2, 0, 1494532, 71188, 2097, 1048576⟩
    (by decide) selected_cut_51718

theorem selected_cut_51719 : selected 11 ⟨1468874, by decide⟩
    (prefixPartial 10 71189) = some ⟨10, 1, 0, 1468874, 71189, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_71189_1468874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71189 ⟨1468874, by decide⟩ :=
  accepted_of_selected 10 71189 ⟨1468874, by decide⟩ ⟨10, 1, 0, 1468874, 71189, 1, 1048576⟩
    (by decide) selected_cut_51719

theorem selected_cut_51720 : selected 10 ⟨1494570, by decide⟩
    (prefixPartial 11 284760) = some ⟨11, 2, 0, 1494570, 284760, 1621, 262144⟩ := by
  decide +kernel

theorem context_11_284760_1494570 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 284760 ⟨1494570, by decide⟩ :=
  accepted_of_selected 11 284760 ⟨1494570, by decide⟩ ⟨11, 2, 0, 1494570, 284760, 1621, 262144⟩
    (by decide) selected_cut_51720

theorem selected_cut_51721 : selected 10 ⟨1494615, by decide⟩
    (prefixPartial 11 284761) = some ⟨11, 2, 0, 1494615, 284761, 1893, 262144⟩ := by
  decide +kernel

theorem context_11_284761_1494615 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 284761 ⟨1494615, by decide⟩ :=
  accepted_of_selected 11 284761 ⟨1494615, by decide⟩ ⟨11, 2, 0, 1494615, 284761, 1893, 262144⟩
    (by decide) selected_cut_51721

theorem selected_cut_51722 : selected 10 ⟨1468743, by decide⟩
    (prefixPartial 11 284762) = some ⟨11, 1, 0, 1468743, 284762, 1, 262144⟩ := by
  decide +kernel

theorem context_11_284762_1468743 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 284762 ⟨1468743, by decide⟩ :=
  accepted_of_selected 11 284762 ⟨1468743, by decide⟩ ⟨11, 1, 0, 1468743, 284762, 1, 262144⟩
    (by decide) selected_cut_51722

theorem selected_cut_51723 : selected 10 ⟨1494652, by decide⟩
    (prefixPartial 11 284763) = some ⟨11, 2, 0, 1494652, 284763, 1369, 262144⟩ := by
  decide +kernel

theorem context_11_284763_1494652 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 284763 ⟨1494652, by decide⟩ :=
  accepted_of_selected 11 284763 ⟨1494652, by decide⟩ ⟨11, 2, 0, 1494652, 284763, 1369, 262144⟩
    (by decide) selected_cut_51723

theorem unmarked_context_10_71190_1494653 : frontier 11 ⟨1494653, by decide⟩
    (prefixCache 10 71190) (prefixPartial 10 71190) = false := by
  decide +kernel

theorem node_context_10_71190_1494653 : EJMOriginalGlobalDAGData.nodes 11 ⟨1494653, by decide⟩ =
    .split (coordinate 10) (![⟨1494570, by decide⟩,⟨1494615, by decide⟩,⟨1468743, by decide⟩,⟨1494652, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_71190_1494653 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71190 ⟨1494653, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 71190
    ⟨1494653, by decide⟩ (by decide) (![⟨1494570, by decide⟩,⟨1494615, by decide⟩,⟨1468743, by decide⟩,⟨1494652, by decide⟩]) unmarked_context_10_71190_1494653 node_context_10_71190_1494653
  intro a
  fin_cases a
  · exact context_11_284760_1494570
  · exact context_11_284761_1494615
  · exact context_11_284762_1468743
  · exact context_11_284763_1494652

theorem selected_cut_51724 : selected 11 ⟨1494753, by decide⟩
    (prefixPartial 10 71191) = some ⟨10, 2, 0, 1494753, 71191, 3989, 1048576⟩ := by
  decide +kernel

theorem context_10_71191_1494753 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71191 ⟨1494753, by decide⟩ :=
  accepted_of_selected 10 71191 ⟨1494753, by decide⟩ ⟨10, 2, 0, 1494753, 71191, 3989, 1048576⟩
    (by decide) selected_cut_51724

theorem unmarked_context_9_17797_1494754 : frontier 12 ⟨1494754, by decide⟩
    (prefixCache 9 17797) (prefixPartial 9 17797) = false := by
  decide +kernel

theorem node_context_9_17797_1494754 : EJMOriginalGlobalDAGData.nodes 12 ⟨1494754, by decide⟩ =
    .split (coordinate 9) (![⟨1494532, by decide⟩,⟨1468874, by decide⟩,⟨1494653, by decide⟩,⟨1494753, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_17797_1494754 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17797 ⟨1494754, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 17797
    ⟨1494754, by decide⟩ (by decide) (![⟨1494532, by decide⟩,⟨1468874, by decide⟩,⟨1494653, by decide⟩,⟨1494753, by decide⟩]) unmarked_context_9_17797_1494754 node_context_9_17797_1494754
  intro a
  fin_cases a
  · exact context_10_71188_1494532
  · exact context_10_71189_1468874
  · exact context_10_71190_1494653
  · exact context_10_71191_1494753

theorem selected_cut_51725 : selected 11 ⟨1494809, by decide⟩
    (prefixPartial 10 71192) = some ⟨10, 2, 0, 1494809, 71192, 1529, 1048576⟩ := by
  decide +kernel

theorem context_10_71192_1494809 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71192 ⟨1494809, by decide⟩ :=
  accepted_of_selected 10 71192 ⟨1494809, by decide⟩ ⟨10, 2, 0, 1494809, 71192, 1529, 1048576⟩
    (by decide) selected_cut_51725

theorem selected_cut_51726 : selected 11 ⟨1494855, by decide⟩
    (prefixPartial 10 71193) = some ⟨10, 2, 0, 1494855, 71193, 1961, 1048576⟩ := by
  decide +kernel

theorem context_10_71193_1494855 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71193 ⟨1494855, by decide⟩ :=
  accepted_of_selected 10 71193 ⟨1494855, by decide⟩ ⟨10, 2, 0, 1494855, 71193, 1961, 1048576⟩
    (by decide) selected_cut_51726

theorem selected_cut_51727 : selected 11 ⟨1469103, by decide⟩
    (prefixPartial 10 71194) = some ⟨10, 1, 0, 1469103, 71194, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_71194_1469103 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71194 ⟨1469103, by decide⟩ :=
  accepted_of_selected 10 71194 ⟨1469103, by decide⟩ ⟨10, 1, 0, 1469103, 71194, 1, 1048576⟩
    (by decide) selected_cut_51727

theorem selected_cut_51728 : selected 11 ⟨1494909, by decide⟩
    (prefixPartial 10 71195) = some ⟨10, 2, 0, 1494909, 71195, 1661, 1048576⟩ := by
  decide +kernel

theorem context_10_71195_1494909 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71195 ⟨1494909, by decide⟩ :=
  accepted_of_selected 10 71195 ⟨1494909, by decide⟩ ⟨10, 2, 0, 1494909, 71195, 1661, 1048576⟩
    (by decide) selected_cut_51728

theorem unmarked_context_9_17798_1494910 : frontier 12 ⟨1494910, by decide⟩
    (prefixCache 9 17798) (prefixPartial 9 17798) = false := by
  decide +kernel

theorem node_context_9_17798_1494910 : EJMOriginalGlobalDAGData.nodes 12 ⟨1494910, by decide⟩ =
    .split (coordinate 9) (![⟨1494809, by decide⟩,⟨1494855, by decide⟩,⟨1469103, by decide⟩,⟨1494909, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_17798_1494910 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17798 ⟨1494910, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 17798
    ⟨1494910, by decide⟩ (by decide) (![⟨1494809, by decide⟩,⟨1494855, by decide⟩,⟨1469103, by decide⟩,⟨1494909, by decide⟩]) unmarked_context_9_17798_1494910 node_context_9_17798_1494910
  intro a
  fin_cases a
  · exact context_10_71192_1494809
  · exact context_10_71193_1494855
  · exact context_10_71194_1469103
  · exact context_10_71195_1494909

theorem selected_cut_51729 : selected 12 ⟨1494972, by decide⟩
    (prefixPartial 9 17799) = some ⟨9, 2, 0, 1494972, 17799, 1465, 4194304⟩ := by
  decide +kernel

theorem context_9_17799_1494972 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17799 ⟨1494972, by decide⟩ :=
  accepted_of_selected 9 17799 ⟨1494972, by decide⟩ ⟨9, 2, 0, 1494972, 17799, 1465, 4194304⟩
    (by decide) selected_cut_51729

theorem unmarked_context_8_4449_1494973 : frontier 13 ⟨1494973, by decide⟩
    (prefixCache 8 4449) (prefixPartial 8 4449) = false := by
  decide +kernel

theorem node_context_8_4449_1494973 : EJMOriginalGlobalDAGData.nodes 13 ⟨1494973, by decide⟩ =
    .split (coordinate 8) (![⟨1494473, by decide⟩,⟨1494754, by decide⟩,⟨1494910, by decide⟩,⟨1494972, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_4449_1494973 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4449 ⟨1494973, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 4449
    ⟨1494973, by decide⟩ (by decide) (![⟨1494473, by decide⟩,⟨1494754, by decide⟩,⟨1494910, by decide⟩,⟨1494972, by decide⟩]) unmarked_context_8_4449_1494973 node_context_8_4449_1494973
  intro a
  fin_cases a
  · exact context_9_17796_1494473
  · exact context_9_17797_1494754
  · exact context_9_17798_1494910
  · exact context_9_17799_1494972

theorem selected_cut_51730 : selected 11 ⟨1468246, by decide⟩
    (prefixPartial 10 71200) = some ⟨10, 1, 0, 1468246, 71200, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_71200_1468246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71200 ⟨1468246, by decide⟩ :=
  accepted_of_selected 10 71200 ⟨1468246, by decide⟩ ⟨10, 1, 0, 1468246, 71200, 1, 1048576⟩
    (by decide) selected_cut_51730

theorem selected_cut_51731 : selected 10 ⟨1495033, by decide⟩
    (prefixPartial 11 284804) = some ⟨11, 2, 0, 1495033, 284804, 2961, 262144⟩ := by
  decide +kernel

theorem context_11_284804_1495033 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 284804 ⟨1495033, by decide⟩ :=
  accepted_of_selected 11 284804 ⟨1495033, by decide⟩ ⟨11, 2, 0, 1495033, 284804, 2961, 262144⟩
    (by decide) selected_cut_51731

theorem selected_cut_51732 : selected 10 ⟨1468419, by decide⟩
    (prefixPartial 11 284805) = some ⟨11, 1, 0, 1468419, 284805, 1, 262144⟩ := by
  decide +kernel

theorem context_11_284805_1468419 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 284805 ⟨1468419, by decide⟩ :=
  accepted_of_selected 11 284805 ⟨1468419, by decide⟩ ⟨11, 1, 0, 1468419, 284805, 1, 262144⟩
    (by decide) selected_cut_51732

theorem selected_cut_51733 : selected 10 ⟨1495113, by decide⟩
    (prefixPartial 11 284806) = some ⟨11, 2, 0, 1495113, 284806, 3233, 262144⟩ := by
  decide +kernel

theorem context_11_284806_1495113 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 284806 ⟨1495113, by decide⟩ :=
  accepted_of_selected 11 284806 ⟨1495113, by decide⟩ ⟨11, 2, 0, 1495113, 284806, 3233, 262144⟩
    (by decide) selected_cut_51733

theorem selected_cut_51734 : selected 10 ⟨1495179, by decide⟩
    (prefixPartial 11 284807) = some ⟨11, 2, 0, 1495179, 284807, 3081, 262144⟩ := by
  decide +kernel

theorem context_11_284807_1495179 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 284807 ⟨1495179, by decide⟩ :=
  accepted_of_selected 11 284807 ⟨1495179, by decide⟩ ⟨11, 2, 0, 1495179, 284807, 3081, 262144⟩
    (by decide) selected_cut_51734

theorem unmarked_context_10_71201_1495180 : frontier 11 ⟨1495180, by decide⟩
    (prefixCache 10 71201) (prefixPartial 10 71201) = false := by
  decide +kernel

theorem node_context_10_71201_1495180 : EJMOriginalGlobalDAGData.nodes 11 ⟨1495180, by decide⟩ =
    .split (coordinate 10) (![⟨1495033, by decide⟩,⟨1468419, by decide⟩,⟨1495113, by decide⟩,⟨1495179, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_71201_1495180 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71201 ⟨1495180, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 71201
    ⟨1495180, by decide⟩ (by decide) (![⟨1495033, by decide⟩,⟨1468419, by decide⟩,⟨1495113, by decide⟩,⟨1495179, by decide⟩]) unmarked_context_10_71201_1495180 node_context_10_71201_1495180
  intro a
  fin_cases a
  · exact context_11_284804_1495033
  · exact context_11_284805_1468419
  · exact context_11_284806_1495113
  · exact context_11_284807_1495179

theorem selected_cut_51735 : selected 10 ⟨1495239, by decide⟩
    (prefixPartial 11 284808) = some ⟨11, 2, 0, 1495239, 284808, 2517, 262144⟩ := by
  decide +kernel

theorem context_11_284808_1495239 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 284808 ⟨1495239, by decide⟩ :=
  accepted_of_selected 11 284808 ⟨1495239, by decide⟩ ⟨11, 2, 0, 1495239, 284808, 2517, 262144⟩
    (by decide) selected_cut_51735

theorem selected_cut_51736 : selected 10 ⟨1495293, by decide⟩
    (prefixPartial 11 284809) = some ⟨11, 2, 0, 1495293, 284809, 2613, 262144⟩ := by
  decide +kernel

theorem context_11_284809_1495293 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 284809 ⟨1495293, by decide⟩ :=
  accepted_of_selected 11 284809 ⟨1495293, by decide⟩ ⟨11, 2, 0, 1495293, 284809, 2613, 262144⟩
    (by decide) selected_cut_51736

theorem selected_cut_51737 : selected 10 ⟨1468743, by decide⟩
    (prefixPartial 11 284810) = some ⟨11, 1, 0, 1468743, 284810, 1, 262144⟩ := by
  decide +kernel

theorem context_11_284810_1468743 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 284810 ⟨1468743, by decide⟩ :=
  accepted_of_selected 11 284810 ⟨1468743, by decide⟩ ⟨11, 1, 0, 1468743, 284810, 1, 262144⟩
    (by decide) selected_cut_51737

theorem selected_cut_51738 : selected 10 ⟨1495345, by decide⟩
    (prefixPartial 11 284811) = some ⟨11, 2, 0, 1495345, 284811, 2533, 262144⟩ := by
  decide +kernel

theorem context_11_284811_1495345 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 284811 ⟨1495345, by decide⟩ :=
  accepted_of_selected 11 284811 ⟨1495345, by decide⟩ ⟨11, 2, 0, 1495345, 284811, 2533, 262144⟩
    (by decide) selected_cut_51738

theorem unmarked_context_10_71202_1495346 : frontier 11 ⟨1495346, by decide⟩
    (prefixCache 10 71202) (prefixPartial 10 71202) = false := by
  decide +kernel

theorem node_context_10_71202_1495346 : EJMOriginalGlobalDAGData.nodes 11 ⟨1495346, by decide⟩ =
    .split (coordinate 10) (![⟨1495239, by decide⟩,⟨1495293, by decide⟩,⟨1468743, by decide⟩,⟨1495345, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_71202_1495346 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71202 ⟨1495346, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 71202
    ⟨1495346, by decide⟩ (by decide) (![⟨1495239, by decide⟩,⟨1495293, by decide⟩,⟨1468743, by decide⟩,⟨1495345, by decide⟩]) unmarked_context_10_71202_1495346 node_context_10_71202_1495346
  intro a
  fin_cases a
  · exact context_11_284808_1495239
  · exact context_11_284809_1495293
  · exact context_11_284810_1468743
  · exact context_11_284811_1495345

theorem selected_cut_51739 : selected 10 ⟨1495432, by decide⟩
    (prefixPartial 11 284812) = some ⟨11, 2, 0, 1495432, 284812, 3637, 262144⟩ := by
  decide +kernel

theorem context_11_284812_1495432 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 284812 ⟨1495432, by decide⟩ :=
  accepted_of_selected 11 284812 ⟨1495432, by decide⟩ ⟨11, 2, 0, 1495432, 284812, 3637, 262144⟩
    (by decide) selected_cut_51739

theorem selected_cut_51740 : selected 10 ⟨1495502, by decide⟩
    (prefixPartial 11 284813) = some ⟨11, 2, 0, 1495502, 284813, 2517, 262144⟩ := by
  decide +kernel

theorem context_11_284813_1495502 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 284813 ⟨1495502, by decide⟩ :=
  accepted_of_selected 11 284813 ⟨1495502, by decide⟩ ⟨11, 2, 0, 1495502, 284813, 2517, 262144⟩
    (by decide) selected_cut_51740

theorem selected_cut_51741 : selected 10 ⟨1495552, by decide⟩
    (prefixPartial 11 284814) = some ⟨11, 2, 0, 1495552, 284814, 2197, 262144⟩ := by
  decide +kernel

theorem context_11_284814_1495552 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 284814 ⟨1495552, by decide⟩ :=
  accepted_of_selected 11 284814 ⟨1495552, by decide⟩ ⟨11, 2, 0, 1495552, 284814, 2197, 262144⟩
    (by decide) selected_cut_51741

theorem selected_cut_51742 : selected 10 ⟨1470044, by decide⟩
    (prefixPartial 11 284815) = some ⟨11, 1, 0, 1470044, 284815, 1, 262144⟩ := by
  decide +kernel

theorem context_11_284815_1470044 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 284815 ⟨1470044, by decide⟩ :=
  accepted_of_selected 11 284815 ⟨1470044, by decide⟩ ⟨11, 1, 0, 1470044, 284815, 1, 262144⟩
    (by decide) selected_cut_51742

theorem unmarked_context_10_71203_1495553 : frontier 11 ⟨1495553, by decide⟩
    (prefixCache 10 71203) (prefixPartial 10 71203) = false := by
  decide +kernel

theorem node_context_10_71203_1495553 : EJMOriginalGlobalDAGData.nodes 11 ⟨1495553, by decide⟩ =
    .split (coordinate 10) (![⟨1495432, by decide⟩,⟨1495502, by decide⟩,⟨1495552, by decide⟩,⟨1470044, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_71203_1495553 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71203 ⟨1495553, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 71203
    ⟨1495553, by decide⟩ (by decide) (![⟨1495432, by decide⟩,⟨1495502, by decide⟩,⟨1495552, by decide⟩,⟨1470044, by decide⟩]) unmarked_context_10_71203_1495553 node_context_10_71203_1495553
  intro a
  fin_cases a
  · exact context_11_284812_1495432
  · exact context_11_284813_1495502
  · exact context_11_284814_1495552
  · exact context_11_284815_1470044

theorem unmarked_context_9_17800_1495554 : frontier 12 ⟨1495554, by decide⟩
    (prefixCache 9 17800) (prefixPartial 9 17800) = false := by
  decide +kernel

theorem node_context_9_17800_1495554 : EJMOriginalGlobalDAGData.nodes 12 ⟨1495554, by decide⟩ =
    .split (coordinate 9) (![⟨1468246, by decide⟩,⟨1495180, by decide⟩,⟨1495346, by decide⟩,⟨1495553, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_17800_1495554 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17800 ⟨1495554, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 17800
    ⟨1495554, by decide⟩ (by decide) (![⟨1468246, by decide⟩,⟨1495180, by decide⟩,⟨1495346, by decide⟩,⟨1495553, by decide⟩]) unmarked_context_9_17800_1495554 node_context_9_17800_1495554
  intro a
  fin_cases a
  · exact context_10_71200_1468246
  · exact context_10_71201_1495180
  · exact context_10_71202_1495346
  · exact context_10_71203_1495553

theorem selected_cut_51743 : selected 11 ⟨1495597, by decide⟩
    (prefixPartial 10 71204) = some ⟨10, 2, 0, 1495597, 71204, 3029, 1048576⟩ := by
  decide +kernel

theorem context_10_71204_1495597 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71204 ⟨1495597, by decide⟩ :=
  accepted_of_selected 10 71204 ⟨1495597, by decide⟩ ⟨10, 2, 0, 1495597, 71204, 3029, 1048576⟩
    (by decide) selected_cut_51743

theorem selected_cut_51744 : selected 11 ⟨1468874, by decide⟩
    (prefixPartial 10 71205) = some ⟨10, 1, 0, 1468874, 71205, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_71205_1468874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71205 ⟨1468874, by decide⟩ :=
  accepted_of_selected 10 71205 ⟨1468874, by decide⟩ ⟨10, 1, 0, 1468874, 71205, 1, 1048576⟩
    (by decide) selected_cut_51744

theorem selected_cut_51745 : selected 10 ⟨1495655, by decide⟩
    (prefixPartial 11 284824) = some ⟨11, 2, 0, 1495655, 284824, 1353, 262144⟩ := by
  decide +kernel

theorem context_11_284824_1495655 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 284824 ⟨1495655, by decide⟩ :=
  accepted_of_selected 11 284824 ⟨1495655, by decide⟩ ⟨11, 2, 0, 1495655, 284824, 1353, 262144⟩
    (by decide) selected_cut_51745

theorem selected_cut_51746 : selected 10 ⟨1495682, by decide⟩
    (prefixPartial 11 284825) = some ⟨11, 2, 0, 1495682, 284825, 1569, 262144⟩ := by
  decide +kernel

theorem context_11_284825_1495682 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 284825 ⟨1495682, by decide⟩ :=
  accepted_of_selected 11 284825 ⟨1495682, by decide⟩ ⟨11, 2, 0, 1495682, 284825, 1569, 262144⟩
    (by decide) selected_cut_51746

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
