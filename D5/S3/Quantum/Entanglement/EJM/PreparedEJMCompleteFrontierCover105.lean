/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover104
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_10083 : selected 8 ⟨276340, by decide⟩
    (prefixPartial 13 99486) = some ⟨13, 2, 0, 276340, 99486, 1441, 16384⟩ := by
  decide +kernel

theorem context_13_99486_276340 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99486 ⟨276340, by decide⟩ :=
  accepted_of_selected 13 99486 ⟨276340, by decide⟩ ⟨13, 2, 0, 276340, 99486, 1441, 16384⟩
    (by decide) selected_cut_10083

theorem selected_cut_10084 : selected 8 ⟨276348, by decide⟩
    (prefixPartial 13 99487) = some ⟨13, 2, 0, 276348, 99487, 909, 16384⟩ := by
  decide +kernel

theorem context_13_99487_276348 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99487 ⟨276348, by decide⟩ :=
  accepted_of_selected 13 99487 ⟨276348, by decide⟩ ⟨13, 2, 0, 276348, 99487, 909, 16384⟩
    (by decide) selected_cut_10084

theorem unmarked_context_12_24871_276349 : frontier 9 ⟨276349, by decide⟩
    (prefixCache 12 24871) (prefixPartial 12 24871) = false := by
  decide +kernel

theorem node_context_12_24871_276349 : EJMOriginalGlobalDAGData.nodes 9 ⟨276349, by decide⟩ =
    .split (coordinate 12) (![⟨276296, by decide⟩,⟨276322, by decide⟩,⟨276340, by decide⟩,⟨276348, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_24871_276349 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24871 ⟨276349, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 24871
    ⟨276349, by decide⟩ (by decide) (![⟨276296, by decide⟩,⟨276322, by decide⟩,⟨276340, by decide⟩,⟨276348, by decide⟩]) unmarked_context_12_24871_276349 node_context_12_24871_276349
  intro a
  fin_cases a
  · exact context_13_99484_276296
  · exact context_13_99485_276322
  · exact context_13_99486_276340
  · exact context_13_99487_276348

theorem unmarked_context_11_6217_276350 : frontier 10 ⟨276350, by decide⟩
    (prefixCache 11 6217) (prefixPartial 11 6217) = false := by
  decide +kernel

theorem node_context_11_6217_276350 : EJMOriginalGlobalDAGData.nodes 10 ⟨276350, by decide⟩ =
    .split (coordinate 11) (![⟨276116, by decide⟩,⟨276208, by decide⟩,⟨276279, by decide⟩,⟨276349, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6217_276350 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6217 ⟨276350, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6217
    ⟨276350, by decide⟩ (by decide) (![⟨276116, by decide⟩,⟨276208, by decide⟩,⟨276279, by decide⟩,⟨276349, by decide⟩]) unmarked_context_11_6217_276350 node_context_11_6217_276350
  intro a
  fin_cases a
  · exact context_12_24868_276116
  · exact context_12_24869_276208
  · exact context_12_24870_276279
  · exact context_12_24871_276349

theorem selected_cut_10085 : selected 8 ⟨276371, by decide⟩
    (prefixPartial 13 99488) = some ⟨13, 2, 0, 276371, 99488, 1105, 16384⟩ := by
  decide +kernel

theorem context_13_99488_276371 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99488 ⟨276371, by decide⟩ :=
  accepted_of_selected 13 99488 ⟨276371, by decide⟩ ⟨13, 2, 0, 276371, 99488, 1105, 16384⟩
    (by decide) selected_cut_10085

theorem selected_cut_10086 : selected 8 ⟨276394, by decide⟩
    (prefixPartial 13 99489) = some ⟨13, 2, 0, 276394, 99489, 2053, 16384⟩ := by
  decide +kernel

theorem context_13_99489_276394 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99489 ⟨276394, by decide⟩ :=
  accepted_of_selected 13 99489 ⟨276394, by decide⟩ ⟨13, 2, 0, 276394, 99489, 2053, 16384⟩
    (by decide) selected_cut_10086

theorem selected_cut_10087 : selected 8 ⟨276412, by decide⟩
    (prefixPartial 13 99490) = some ⟨13, 2, 0, 276412, 99490, 1485, 16384⟩ := by
  decide +kernel

theorem context_13_99490_276412 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99490 ⟨276412, by decide⟩ :=
  accepted_of_selected 13 99490 ⟨276412, by decide⟩ ⟨13, 2, 0, 276412, 99490, 1485, 16384⟩
    (by decide) selected_cut_10087

theorem selected_cut_10088 : selected 8 ⟨276419, by decide⟩
    (prefixPartial 13 99491) = some ⟨13, 2, 0, 276419, 99491, 785, 16384⟩ := by
  decide +kernel

theorem context_13_99491_276419 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99491 ⟨276419, by decide⟩ :=
  accepted_of_selected 13 99491 ⟨276419, by decide⟩ ⟨13, 2, 0, 276419, 99491, 785, 16384⟩
    (by decide) selected_cut_10088

theorem unmarked_context_12_24872_276420 : frontier 9 ⟨276420, by decide⟩
    (prefixCache 12 24872) (prefixPartial 12 24872) = false := by
  decide +kernel

theorem node_context_12_24872_276420 : EJMOriginalGlobalDAGData.nodes 9 ⟨276420, by decide⟩ =
    .split (coordinate 12) (![⟨276371, by decide⟩,⟨276394, by decide⟩,⟨276412, by decide⟩,⟨276419, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_24872_276420 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24872 ⟨276420, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 24872
    ⟨276420, by decide⟩ (by decide) (![⟨276371, by decide⟩,⟨276394, by decide⟩,⟨276412, by decide⟩,⟨276419, by decide⟩]) unmarked_context_12_24872_276420 node_context_12_24872_276420
  intro a
  fin_cases a
  · exact context_13_99488_276371
  · exact context_13_99489_276394
  · exact context_13_99490_276412
  · exact context_13_99491_276419

theorem selected_cut_10089 : selected 8 ⟨276430, by decide⟩
    (prefixPartial 13 99492) = some ⟨13, 2, 0, 276430, 99492, 997, 16384⟩ := by
  decide +kernel

theorem context_13_99492_276430 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99492 ⟨276430, by decide⟩ :=
  accepted_of_selected 13 99492 ⟨276430, by decide⟩ ⟨13, 2, 0, 276430, 99492, 997, 16384⟩
    (by decide) selected_cut_10089

theorem selected_cut_10090 : selected 8 ⟨276451, by decide⟩
    (prefixPartial 13 99493) = some ⟨13, 2, 0, 276451, 99493, 2009, 16384⟩ := by
  decide +kernel

theorem context_13_99493_276451 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99493 ⟨276451, by decide⟩ :=
  accepted_of_selected 13 99493 ⟨276451, by decide⟩ ⟨13, 2, 0, 276451, 99493, 2009, 16384⟩
    (by decide) selected_cut_10090

theorem selected_cut_10091 : selected 8 ⟨276468, by decide⟩
    (prefixPartial 13 99494) = some ⟨13, 2, 0, 276468, 99494, 1505, 16384⟩ := by
  decide +kernel

theorem context_13_99494_276468 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99494 ⟨276468, by decide⟩ :=
  accepted_of_selected 13 99494 ⟨276468, by decide⟩ ⟨13, 2, 0, 276468, 99494, 1505, 16384⟩
    (by decide) selected_cut_10091

theorem selected_cut_10092 : selected 8 ⟨276475, by decide⟩
    (prefixPartial 13 99495) = some ⟨13, 2, 0, 276475, 99495, 893, 16384⟩ := by
  decide +kernel

theorem context_13_99495_276475 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99495 ⟨276475, by decide⟩ :=
  accepted_of_selected 13 99495 ⟨276475, by decide⟩ ⟨13, 2, 0, 276475, 99495, 893, 16384⟩
    (by decide) selected_cut_10092

theorem unmarked_context_12_24873_276476 : frontier 9 ⟨276476, by decide⟩
    (prefixCache 12 24873) (prefixPartial 12 24873) = false := by
  decide +kernel

theorem node_context_12_24873_276476 : EJMOriginalGlobalDAGData.nodes 9 ⟨276476, by decide⟩ =
    .split (coordinate 12) (![⟨276430, by decide⟩,⟨276451, by decide⟩,⟨276468, by decide⟩,⟨276475, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_24873_276476 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24873 ⟨276476, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 24873
    ⟨276476, by decide⟩ (by decide) (![⟨276430, by decide⟩,⟨276451, by decide⟩,⟨276468, by decide⟩,⟨276475, by decide⟩]) unmarked_context_12_24873_276476 node_context_12_24873_276476
  intro a
  fin_cases a
  · exact context_13_99492_276430
  · exact context_13_99493_276451
  · exact context_13_99494_276468
  · exact context_13_99495_276475

theorem selected_cut_10093 : selected 8 ⟨276488, by decide⟩
    (prefixPartial 13 99496) = some ⟨13, 2, 0, 276488, 99496, 1041, 16384⟩ := by
  decide +kernel

theorem context_13_99496_276488 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99496 ⟨276488, by decide⟩ :=
  accepted_of_selected 13 99496 ⟨276488, by decide⟩ ⟨13, 2, 0, 276488, 99496, 1041, 16384⟩
    (by decide) selected_cut_10093

theorem selected_cut_10094 : selected 8 ⟨276513, by decide⟩
    (prefixPartial 13 99497) = some ⟨13, 2, 0, 276513, 99497, 2293, 16384⟩ := by
  decide +kernel

theorem context_13_99497_276513 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99497 ⟨276513, by decide⟩ :=
  accepted_of_selected 13 99497 ⟨276513, by decide⟩ ⟨13, 2, 0, 276513, 99497, 2293, 16384⟩
    (by decide) selected_cut_10094

theorem selected_cut_10095 : selected 8 ⟨276532, by decide⟩
    (prefixPartial 13 99498) = some ⟨13, 2, 0, 276532, 99498, 1453, 16384⟩ := by
  decide +kernel

theorem context_13_99498_276532 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99498 ⟨276532, by decide⟩ :=
  accepted_of_selected 13 99498 ⟨276532, by decide⟩ ⟨13, 2, 0, 276532, 99498, 1453, 16384⟩
    (by decide) selected_cut_10095

theorem selected_cut_10096 : selected 8 ⟨276539, by decide⟩
    (prefixPartial 13 99499) = some ⟨13, 2, 0, 276539, 99499, 805, 16384⟩ := by
  decide +kernel

theorem context_13_99499_276539 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99499 ⟨276539, by decide⟩ :=
  accepted_of_selected 13 99499 ⟨276539, by decide⟩ ⟨13, 2, 0, 276539, 99499, 805, 16384⟩
    (by decide) selected_cut_10096

theorem unmarked_context_12_24874_276540 : frontier 9 ⟨276540, by decide⟩
    (prefixCache 12 24874) (prefixPartial 12 24874) = false := by
  decide +kernel

theorem node_context_12_24874_276540 : EJMOriginalGlobalDAGData.nodes 9 ⟨276540, by decide⟩ =
    .split (coordinate 12) (![⟨276488, by decide⟩,⟨276513, by decide⟩,⟨276532, by decide⟩,⟨276539, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_24874_276540 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24874 ⟨276540, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 24874
    ⟨276540, by decide⟩ (by decide) (![⟨276488, by decide⟩,⟨276513, by decide⟩,⟨276532, by decide⟩,⟨276539, by decide⟩]) unmarked_context_12_24874_276540 node_context_12_24874_276540
  intro a
  fin_cases a
  · exact context_13_99496_276488
  · exact context_13_99497_276513
  · exact context_13_99498_276532
  · exact context_13_99499_276539

theorem selected_cut_10097 : selected 8 ⟨276556, by decide⟩
    (prefixPartial 13 99500) = some ⟨13, 2, 0, 276556, 99500, 1241, 16384⟩ := by
  decide +kernel

theorem context_13_99500_276556 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99500 ⟨276556, by decide⟩ :=
  accepted_of_selected 13 99500 ⟨276556, by decide⟩ ⟨13, 2, 0, 276556, 99500, 1241, 16384⟩
    (by decide) selected_cut_10097

theorem selected_cut_10098 : selected 8 ⟨276584, by decide⟩
    (prefixPartial 13 99501) = some ⟨13, 2, 0, 276584, 99501, 2557, 16384⟩ := by
  decide +kernel

theorem context_13_99501_276584 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99501 ⟨276584, by decide⟩ :=
  accepted_of_selected 13 99501 ⟨276584, by decide⟩ ⟨13, 2, 0, 276584, 99501, 2557, 16384⟩
    (by decide) selected_cut_10098

theorem selected_cut_10099 : selected 8 ⟨276602, by decide⟩
    (prefixPartial 13 99502) = some ⟨13, 2, 0, 276602, 99502, 1433, 16384⟩ := by
  decide +kernel

theorem context_13_99502_276602 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99502 ⟨276602, by decide⟩ :=
  accepted_of_selected 13 99502 ⟨276602, by decide⟩ ⟨13, 2, 0, 276602, 99502, 1433, 16384⟩
    (by decide) selected_cut_10099

theorem selected_cut_10100 : selected 8 ⟨276609, by decide⟩
    (prefixPartial 13 99503) = some ⟨13, 2, 0, 276609, 99503, 849, 16384⟩ := by
  decide +kernel

theorem context_13_99503_276609 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99503 ⟨276609, by decide⟩ :=
  accepted_of_selected 13 99503 ⟨276609, by decide⟩ ⟨13, 2, 0, 276609, 99503, 849, 16384⟩
    (by decide) selected_cut_10100

theorem unmarked_context_12_24875_276610 : frontier 9 ⟨276610, by decide⟩
    (prefixCache 12 24875) (prefixPartial 12 24875) = false := by
  decide +kernel

theorem node_context_12_24875_276610 : EJMOriginalGlobalDAGData.nodes 9 ⟨276610, by decide⟩ =
    .split (coordinate 12) (![⟨276556, by decide⟩,⟨276584, by decide⟩,⟨276602, by decide⟩,⟨276609, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_24875_276610 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24875 ⟨276610, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 24875
    ⟨276610, by decide⟩ (by decide) (![⟨276556, by decide⟩,⟨276584, by decide⟩,⟨276602, by decide⟩,⟨276609, by decide⟩]) unmarked_context_12_24875_276610 node_context_12_24875_276610
  intro a
  fin_cases a
  · exact context_13_99500_276556
  · exact context_13_99501_276584
  · exact context_13_99502_276602
  · exact context_13_99503_276609

theorem unmarked_context_11_6218_276611 : frontier 10 ⟨276611, by decide⟩
    (prefixCache 11 6218) (prefixPartial 11 6218) = false := by
  decide +kernel

theorem node_context_11_6218_276611 : EJMOriginalGlobalDAGData.nodes 10 ⟨276611, by decide⟩ =
    .split (coordinate 11) (![⟨276420, by decide⟩,⟨276476, by decide⟩,⟨276540, by decide⟩,⟨276610, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6218_276611 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6218 ⟨276611, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6218
    ⟨276611, by decide⟩ (by decide) (![⟨276420, by decide⟩,⟨276476, by decide⟩,⟨276540, by decide⟩,⟨276610, by decide⟩]) unmarked_context_11_6218_276611 node_context_11_6218_276611
  intro a
  fin_cases a
  · exact context_12_24872_276420
  · exact context_12_24873_276476
  · exact context_12_24874_276540
  · exact context_12_24875_276610

theorem selected_cut_10101 : selected 8 ⟨276624, by decide⟩
    (prefixPartial 13 99504) = some ⟨13, 2, 0, 276624, 99504, 861, 16384⟩ := by
  decide +kernel

theorem context_13_99504_276624 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99504 ⟨276624, by decide⟩ :=
  accepted_of_selected 13 99504 ⟨276624, by decide⟩ ⟨13, 2, 0, 276624, 99504, 861, 16384⟩
    (by decide) selected_cut_10101

theorem selected_cut_10102 : selected 8 ⟨276652, by decide⟩
    (prefixPartial 13 99505) = some ⟨13, 2, 0, 276652, 99505, 2365, 16384⟩ := by
  decide +kernel

theorem context_13_99505_276652 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99505 ⟨276652, by decide⟩ :=
  accepted_of_selected 13 99505 ⟨276652, by decide⟩ ⟨13, 2, 0, 276652, 99505, 2365, 16384⟩
    (by decide) selected_cut_10102

theorem selected_cut_10103 : selected 8 ⟨276670, by decide⟩
    (prefixPartial 13 99506) = some ⟨13, 2, 0, 276670, 99506, 1425, 16384⟩ := by
  decide +kernel

theorem context_13_99506_276670 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99506 ⟨276670, by decide⟩ :=
  accepted_of_selected 13 99506 ⟨276670, by decide⟩ ⟨13, 2, 0, 276670, 99506, 1425, 16384⟩
    (by decide) selected_cut_10103

theorem selected_cut_10104 : selected 8 ⟨276676, by decide⟩
    (prefixPartial 13 99507) = some ⟨13, 2, 0, 276676, 99507, 1077, 16384⟩ := by
  decide +kernel

theorem context_13_99507_276676 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99507 ⟨276676, by decide⟩ :=
  accepted_of_selected 13 99507 ⟨276676, by decide⟩ ⟨13, 2, 0, 276676, 99507, 1077, 16384⟩
    (by decide) selected_cut_10104

theorem unmarked_context_12_24876_276677 : frontier 9 ⟨276677, by decide⟩
    (prefixCache 12 24876) (prefixPartial 12 24876) = false := by
  decide +kernel

theorem node_context_12_24876_276677 : EJMOriginalGlobalDAGData.nodes 9 ⟨276677, by decide⟩ =
    .split (coordinate 12) (![⟨276624, by decide⟩,⟨276652, by decide⟩,⟨276670, by decide⟩,⟨276676, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_24876_276677 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24876 ⟨276677, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 24876
    ⟨276677, by decide⟩ (by decide) (![⟨276624, by decide⟩,⟨276652, by decide⟩,⟨276670, by decide⟩,⟨276676, by decide⟩]) unmarked_context_12_24876_276677 node_context_12_24876_276677
  intro a
  fin_cases a
  · exact context_13_99504_276624
  · exact context_13_99505_276652
  · exact context_13_99506_276670
  · exact context_13_99507_276676

theorem selected_cut_10105 : selected 8 ⟨276688, by decide⟩
    (prefixPartial 13 99508) = some ⟨13, 2, 0, 276688, 99508, 893, 16384⟩ := by
  decide +kernel

theorem context_13_99508_276688 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99508 ⟨276688, by decide⟩ :=
  accepted_of_selected 13 99508 ⟨276688, by decide⟩ ⟨13, 2, 0, 276688, 99508, 893, 16384⟩
    (by decide) selected_cut_10105

theorem selected_cut_10106 : selected 8 ⟨276713, by decide⟩
    (prefixPartial 13 99509) = some ⟨13, 2, 0, 276713, 99509, 2553, 16384⟩ := by
  decide +kernel

theorem context_13_99509_276713 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99509 ⟨276713, by decide⟩ :=
  accepted_of_selected 13 99509 ⟨276713, by decide⟩ ⟨13, 2, 0, 276713, 99509, 2553, 16384⟩
    (by decide) selected_cut_10106

theorem selected_cut_10107 : selected 8 ⟨276735, by decide⟩
    (prefixPartial 13 99510) = some ⟨13, 2, 0, 276735, 99510, 1601, 16384⟩ := by
  decide +kernel

theorem context_13_99510_276735 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99510 ⟨276735, by decide⟩ :=
  accepted_of_selected 13 99510 ⟨276735, by decide⟩ ⟨13, 2, 0, 276735, 99510, 1601, 16384⟩
    (by decide) selected_cut_10107

theorem selected_cut_10108 : selected 8 ⟨276745, by decide⟩
    (prefixPartial 13 99511) = some ⟨13, 2, 0, 276745, 99511, 1037, 16384⟩ := by
  decide +kernel

theorem context_13_99511_276745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99511 ⟨276745, by decide⟩ :=
  accepted_of_selected 13 99511 ⟨276745, by decide⟩ ⟨13, 2, 0, 276745, 99511, 1037, 16384⟩
    (by decide) selected_cut_10108

theorem unmarked_context_12_24877_276746 : frontier 9 ⟨276746, by decide⟩
    (prefixCache 12 24877) (prefixPartial 12 24877) = false := by
  decide +kernel

theorem node_context_12_24877_276746 : EJMOriginalGlobalDAGData.nodes 9 ⟨276746, by decide⟩ =
    .split (coordinate 12) (![⟨276688, by decide⟩,⟨276713, by decide⟩,⟨276735, by decide⟩,⟨276745, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_24877_276746 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24877 ⟨276746, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 24877
    ⟨276746, by decide⟩ (by decide) (![⟨276688, by decide⟩,⟨276713, by decide⟩,⟨276735, by decide⟩,⟨276745, by decide⟩]) unmarked_context_12_24877_276746 node_context_12_24877_276746
  intro a
  fin_cases a
  · exact context_13_99508_276688
  · exact context_13_99509_276713
  · exact context_13_99510_276735
  · exact context_13_99511_276745

theorem selected_cut_10109 : selected 8 ⟨276762, by decide⟩
    (prefixPartial 13 99512) = some ⟨13, 2, 0, 276762, 99512, 845, 16384⟩ := by
  decide +kernel

theorem context_13_99512_276762 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99512 ⟨276762, by decide⟩ :=
  accepted_of_selected 13 99512 ⟨276762, by decide⟩ ⟨13, 2, 0, 276762, 99512, 845, 16384⟩
    (by decide) selected_cut_10109

theorem selected_cut_10110 : selected 8 ⟨276791, by decide⟩
    (prefixPartial 13 99513) = some ⟨13, 2, 0, 276791, 99513, 2685, 16384⟩ := by
  decide +kernel

theorem context_13_99513_276791 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99513 ⟨276791, by decide⟩ :=
  accepted_of_selected 13 99513 ⟨276791, by decide⟩ ⟨13, 2, 0, 276791, 99513, 2685, 16384⟩
    (by decide) selected_cut_10110

theorem selected_cut_10111 : selected 8 ⟨276809, by decide⟩
    (prefixPartial 13 99514) = some ⟨13, 2, 0, 276809, 99514, 1381, 16384⟩ := by
  decide +kernel

theorem context_13_99514_276809 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99514 ⟨276809, by decide⟩ :=
  accepted_of_selected 13 99514 ⟨276809, by decide⟩ ⟨13, 2, 0, 276809, 99514, 1381, 16384⟩
    (by decide) selected_cut_10111

theorem selected_cut_10112 : selected 8 ⟨276816, by decide⟩
    (prefixPartial 13 99515) = some ⟨13, 2, 0, 276816, 99515, 1025, 16384⟩ := by
  decide +kernel

theorem context_13_99515_276816 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99515 ⟨276816, by decide⟩ :=
  accepted_of_selected 13 99515 ⟨276816, by decide⟩ ⟨13, 2, 0, 276816, 99515, 1025, 16384⟩
    (by decide) selected_cut_10112

theorem unmarked_context_12_24878_276817 : frontier 9 ⟨276817, by decide⟩
    (prefixCache 12 24878) (prefixPartial 12 24878) = false := by
  decide +kernel

theorem node_context_12_24878_276817 : EJMOriginalGlobalDAGData.nodes 9 ⟨276817, by decide⟩ =
    .split (coordinate 12) (![⟨276762, by decide⟩,⟨276791, by decide⟩,⟨276809, by decide⟩,⟨276816, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_24878_276817 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24878 ⟨276817, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 24878
    ⟨276817, by decide⟩ (by decide) (![⟨276762, by decide⟩,⟨276791, by decide⟩,⟨276809, by decide⟩,⟨276816, by decide⟩]) unmarked_context_12_24878_276817 node_context_12_24878_276817
  intro a
  fin_cases a
  · exact context_13_99512_276762
  · exact context_13_99513_276791
  · exact context_13_99514_276809
  · exact context_13_99515_276816

theorem selected_cut_10113 : selected 8 ⟨276833, by decide⟩
    (prefixPartial 13 99516) = some ⟨13, 2, 0, 276833, 99516, 957, 16384⟩ := by
  decide +kernel

theorem context_13_99516_276833 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99516 ⟨276833, by decide⟩ :=
  accepted_of_selected 13 99516 ⟨276833, by decide⟩ ⟨13, 2, 0, 276833, 99516, 957, 16384⟩
    (by decide) selected_cut_10113

theorem selected_cut_10114 : selected 8 ⟨276859, by decide⟩
    (prefixPartial 13 99517) = some ⟨13, 2, 0, 276859, 99517, 2677, 16384⟩ := by
  decide +kernel

theorem context_13_99517_276859 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99517 ⟨276859, by decide⟩ :=
  accepted_of_selected 13 99517 ⟨276859, by decide⟩ ⟨13, 2, 0, 276859, 99517, 2677, 16384⟩
    (by decide) selected_cut_10114

theorem selected_cut_10115 : selected 8 ⟨276877, by decide⟩
    (prefixPartial 13 99518) = some ⟨13, 2, 0, 276877, 99518, 1509, 16384⟩ := by
  decide +kernel

theorem context_13_99518_276877 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99518 ⟨276877, by decide⟩ :=
  accepted_of_selected 13 99518 ⟨276877, by decide⟩ ⟨13, 2, 0, 276877, 99518, 1509, 16384⟩
    (by decide) selected_cut_10115

theorem selected_cut_10116 : selected 8 ⟨276882, by decide⟩
    (prefixPartial 13 99519) = some ⟨13, 2, 0, 276882, 99519, 1105, 16384⟩ := by
  decide +kernel

theorem context_13_99519_276882 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99519 ⟨276882, by decide⟩ :=
  accepted_of_selected 13 99519 ⟨276882, by decide⟩ ⟨13, 2, 0, 276882, 99519, 1105, 16384⟩
    (by decide) selected_cut_10116

theorem unmarked_context_12_24879_276883 : frontier 9 ⟨276883, by decide⟩
    (prefixCache 12 24879) (prefixPartial 12 24879) = false := by
  decide +kernel

theorem node_context_12_24879_276883 : EJMOriginalGlobalDAGData.nodes 9 ⟨276883, by decide⟩ =
    .split (coordinate 12) (![⟨276833, by decide⟩,⟨276859, by decide⟩,⟨276877, by decide⟩,⟨276882, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_24879_276883 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24879 ⟨276883, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 24879
    ⟨276883, by decide⟩ (by decide) (![⟨276833, by decide⟩,⟨276859, by decide⟩,⟨276877, by decide⟩,⟨276882, by decide⟩]) unmarked_context_12_24879_276883 node_context_12_24879_276883
  intro a
  fin_cases a
  · exact context_13_99516_276833
  · exact context_13_99517_276859
  · exact context_13_99518_276877
  · exact context_13_99519_276882

theorem unmarked_context_11_6219_276884 : frontier 10 ⟨276884, by decide⟩
    (prefixCache 11 6219) (prefixPartial 11 6219) = false := by
  decide +kernel

theorem node_context_11_6219_276884 : EJMOriginalGlobalDAGData.nodes 10 ⟨276884, by decide⟩ =
    .split (coordinate 11) (![⟨276677, by decide⟩,⟨276746, by decide⟩,⟨276817, by decide⟩,⟨276883, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6219_276884 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6219 ⟨276884, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6219
    ⟨276884, by decide⟩ (by decide) (![⟨276677, by decide⟩,⟨276746, by decide⟩,⟨276817, by decide⟩,⟨276883, by decide⟩]) unmarked_context_11_6219_276884 node_context_11_6219_276884
  intro a
  fin_cases a
  · exact context_12_24876_276677
  · exact context_12_24877_276746
  · exact context_12_24878_276817
  · exact context_12_24879_276883

theorem unmarked_context_10_1554_276885 : frontier 11 ⟨276885, by decide⟩
    (prefixCache 10 1554) (prefixPartial 10 1554) = false := by
  decide +kernel

theorem node_context_10_1554_276885 : EJMOriginalGlobalDAGData.nodes 11 ⟨276885, by decide⟩ =
    .split (coordinate 10) (![⟨276046, by decide⟩,⟨276350, by decide⟩,⟨276611, by decide⟩,⟨276884, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1554_276885 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1554 ⟨276885, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1554
    ⟨276885, by decide⟩ (by decide) (![⟨276046, by decide⟩,⟨276350, by decide⟩,⟨276611, by decide⟩,⟨276884, by decide⟩]) unmarked_context_10_1554_276885 node_context_10_1554_276885
  intro a
  fin_cases a
  · exact context_11_6216_276046
  · exact context_11_6217_276350
  · exact context_11_6218_276611
  · exact context_11_6219_276884

theorem selected_cut_10117 : selected 8 ⟨276895, by decide⟩
    (prefixPartial 13 99520) = some ⟨13, 2, 0, 276895, 99520, 821, 16384⟩ := by
  decide +kernel

theorem context_13_99520_276895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99520 ⟨276895, by decide⟩ :=
  accepted_of_selected 13 99520 ⟨276895, by decide⟩ ⟨13, 2, 0, 276895, 99520, 821, 16384⟩
    (by decide) selected_cut_10117

theorem selected_cut_10118 : selected 8 ⟨276919, by decide⟩
    (prefixPartial 13 99521) = some ⟨13, 2, 0, 276919, 99521, 1725, 16384⟩ := by
  decide +kernel

theorem context_13_99521_276919 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99521 ⟨276919, by decide⟩ :=
  accepted_of_selected 13 99521 ⟨276919, by decide⟩ ⟨13, 2, 0, 276919, 99521, 1725, 16384⟩
    (by decide) selected_cut_10118

theorem selected_cut_10119 : selected 8 ⟨276939, by decide⟩
    (prefixPartial 13 99522) = some ⟨13, 2, 0, 276939, 99522, 1221, 16384⟩ := by
  decide +kernel

theorem context_13_99522_276939 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99522 ⟨276939, by decide⟩ :=
  accepted_of_selected 13 99522 ⟨276939, by decide⟩ ⟨13, 2, 0, 276939, 99522, 1221, 16384⟩
    (by decide) selected_cut_10119

theorem selected_cut_10120 : selected 8 ⟨276945, by decide⟩
    (prefixPartial 13 99523) = some ⟨13, 2, 0, 276945, 99523, 653, 16384⟩ := by
  decide +kernel

theorem context_13_99523_276945 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99523 ⟨276945, by decide⟩ :=
  accepted_of_selected 13 99523 ⟨276945, by decide⟩ ⟨13, 2, 0, 276945, 99523, 653, 16384⟩
    (by decide) selected_cut_10120

theorem unmarked_context_12_24880_276946 : frontier 9 ⟨276946, by decide⟩
    (prefixCache 12 24880) (prefixPartial 12 24880) = false := by
  decide +kernel

theorem node_context_12_24880_276946 : EJMOriginalGlobalDAGData.nodes 9 ⟨276946, by decide⟩ =
    .split (coordinate 12) (![⟨276895, by decide⟩,⟨276919, by decide⟩,⟨276939, by decide⟩,⟨276945, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_24880_276946 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24880 ⟨276946, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 24880
    ⟨276946, by decide⟩ (by decide) (![⟨276895, by decide⟩,⟨276919, by decide⟩,⟨276939, by decide⟩,⟨276945, by decide⟩]) unmarked_context_12_24880_276946 node_context_12_24880_276946
  intro a
  fin_cases a
  · exact context_13_99520_276895
  · exact context_13_99521_276919
  · exact context_13_99522_276939
  · exact context_13_99523_276945

theorem selected_cut_10121 : selected 8 ⟨276954, by decide⟩
    (prefixPartial 13 99524) = some ⟨13, 2, 0, 276954, 99524, 569, 16384⟩ := by
  decide +kernel

theorem context_13_99524_276954 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99524 ⟨276954, by decide⟩ :=
  accepted_of_selected 13 99524 ⟨276954, by decide⟩ ⟨13, 2, 0, 276954, 99524, 569, 16384⟩
    (by decide) selected_cut_10121

theorem selected_cut_10122 : selected 8 ⟨276978, by decide⟩
    (prefixPartial 13 99525) = some ⟨13, 2, 0, 276978, 99525, 1873, 16384⟩ := by
  decide +kernel

theorem context_13_99525_276978 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99525 ⟨276978, by decide⟩ :=
  accepted_of_selected 13 99525 ⟨276978, by decide⟩ ⟨13, 2, 0, 276978, 99525, 1873, 16384⟩
    (by decide) selected_cut_10122

theorem selected_cut_10123 : selected 8 ⟨276998, by decide⟩
    (prefixPartial 13 99526) = some ⟨13, 2, 0, 276998, 99526, 1553, 16384⟩ := by
  decide +kernel

theorem context_13_99526_276998 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99526 ⟨276998, by decide⟩ :=
  accepted_of_selected 13 99526 ⟨276998, by decide⟩ ⟨13, 2, 0, 276998, 99526, 1553, 16384⟩
    (by decide) selected_cut_10123

theorem selected_cut_10124 : selected 8 ⟨277005, by decide⟩
    (prefixPartial 13 99527) = some ⟨13, 2, 0, 277005, 99527, 733, 16384⟩ := by
  decide +kernel

theorem context_13_99527_277005 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99527 ⟨277005, by decide⟩ :=
  accepted_of_selected 13 99527 ⟨277005, by decide⟩ ⟨13, 2, 0, 277005, 99527, 733, 16384⟩
    (by decide) selected_cut_10124

theorem unmarked_context_12_24881_277006 : frontier 9 ⟨277006, by decide⟩
    (prefixCache 12 24881) (prefixPartial 12 24881) = false := by
  decide +kernel

theorem node_context_12_24881_277006 : EJMOriginalGlobalDAGData.nodes 9 ⟨277006, by decide⟩ =
    .split (coordinate 12) (![⟨276954, by decide⟩,⟨276978, by decide⟩,⟨276998, by decide⟩,⟨277005, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_24881_277006 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24881 ⟨277006, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 24881
    ⟨277006, by decide⟩ (by decide) (![⟨276954, by decide⟩,⟨276978, by decide⟩,⟨276998, by decide⟩,⟨277005, by decide⟩]) unmarked_context_12_24881_277006 node_context_12_24881_277006
  intro a
  fin_cases a
  · exact context_13_99524_276954
  · exact context_13_99525_276978
  · exact context_13_99526_276998
  · exact context_13_99527_277005

theorem selected_cut_10125 : selected 8 ⟨277014, by decide⟩
    (prefixPartial 13 99528) = some ⟨13, 2, 0, 277014, 99528, 637, 16384⟩ := by
  decide +kernel

theorem context_13_99528_277014 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99528 ⟨277014, by decide⟩ :=
  accepted_of_selected 13 99528 ⟨277014, by decide⟩ ⟨13, 2, 0, 277014, 99528, 637, 16384⟩
    (by decide) selected_cut_10125

theorem selected_cut_10126 : selected 8 ⟨277045, by decide⟩
    (prefixPartial 13 99529) = some ⟨13, 2, 0, 277045, 99529, 2073, 16384⟩ := by
  decide +kernel

theorem context_13_99529_277045 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99529 ⟨277045, by decide⟩ :=
  accepted_of_selected 13 99529 ⟨277045, by decide⟩ ⟨13, 2, 0, 277045, 99529, 2073, 16384⟩
    (by decide) selected_cut_10126

theorem selected_cut_10127 : selected 8 ⟨277067, by decide⟩
    (prefixPartial 13 99530) = some ⟨13, 2, 0, 277067, 99530, 1445, 16384⟩ := by
  decide +kernel

theorem context_13_99530_277067 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99530 ⟨277067, by decide⟩ :=
  accepted_of_selected 13 99530 ⟨277067, by decide⟩ ⟨13, 2, 0, 277067, 99530, 1445, 16384⟩
    (by decide) selected_cut_10127

theorem selected_cut_10128 : selected 8 ⟨277072, by decide⟩
    (prefixPartial 13 99531) = some ⟨13, 2, 0, 277072, 99531, 721, 16384⟩ := by
  decide +kernel

theorem context_13_99531_277072 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99531 ⟨277072, by decide⟩ :=
  accepted_of_selected 13 99531 ⟨277072, by decide⟩ ⟨13, 2, 0, 277072, 99531, 721, 16384⟩
    (by decide) selected_cut_10128

theorem unmarked_context_12_24882_277073 : frontier 9 ⟨277073, by decide⟩
    (prefixCache 12 24882) (prefixPartial 12 24882) = false := by
  decide +kernel

theorem node_context_12_24882_277073 : EJMOriginalGlobalDAGData.nodes 9 ⟨277073, by decide⟩ =
    .split (coordinate 12) (![⟨277014, by decide⟩,⟨277045, by decide⟩,⟨277067, by decide⟩,⟨277072, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_24882_277073 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24882 ⟨277073, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 24882
    ⟨277073, by decide⟩ (by decide) (![⟨277014, by decide⟩,⟨277045, by decide⟩,⟨277067, by decide⟩,⟨277072, by decide⟩]) unmarked_context_12_24882_277073 node_context_12_24882_277073
  intro a
  fin_cases a
  · exact context_13_99528_277014
  · exact context_13_99529_277045
  · exact context_13_99530_277067
  · exact context_13_99531_277072

theorem selected_cut_10129 : selected 8 ⟨277083, by decide⟩
    (prefixPartial 13 99532) = some ⟨13, 2, 0, 277083, 99532, 741, 16384⟩ := by
  decide +kernel

theorem context_13_99532_277083 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99532 ⟨277083, by decide⟩ :=
  accepted_of_selected 13 99532 ⟨277083, by decide⟩ ⟨13, 2, 0, 277083, 99532, 741, 16384⟩
    (by decide) selected_cut_10129

theorem selected_cut_10130 : selected 8 ⟨277112, by decide⟩
    (prefixPartial 13 99533) = some ⟨13, 2, 0, 277112, 99533, 2333, 16384⟩ := by
  decide +kernel

theorem context_13_99533_277112 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99533 ⟨277112, by decide⟩ :=
  accepted_of_selected 13 99533 ⟨277112, by decide⟩ ⟨13, 2, 0, 277112, 99533, 2333, 16384⟩
    (by decide) selected_cut_10130

theorem selected_cut_10131 : selected 8 ⟨277131, by decide⟩
    (prefixPartial 13 99534) = some ⟨13, 2, 0, 277131, 99534, 1665, 16384⟩ := by
  decide +kernel

theorem context_13_99534_277131 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99534 ⟨277131, by decide⟩ :=
  accepted_of_selected 13 99534 ⟨277131, by decide⟩ ⟨13, 2, 0, 277131, 99534, 1665, 16384⟩
    (by decide) selected_cut_10131

theorem selected_cut_10132 : selected 8 ⟨277137, by decide⟩
    (prefixPartial 13 99535) = some ⟨13, 2, 0, 277137, 99535, 857, 16384⟩ := by
  decide +kernel

theorem context_13_99535_277137 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99535 ⟨277137, by decide⟩ :=
  accepted_of_selected 13 99535 ⟨277137, by decide⟩ ⟨13, 2, 0, 277137, 99535, 857, 16384⟩
    (by decide) selected_cut_10132

theorem unmarked_context_12_24883_277138 : frontier 9 ⟨277138, by decide⟩
    (prefixCache 12 24883) (prefixPartial 12 24883) = false := by
  decide +kernel

theorem node_context_12_24883_277138 : EJMOriginalGlobalDAGData.nodes 9 ⟨277138, by decide⟩ =
    .split (coordinate 12) (![⟨277083, by decide⟩,⟨277112, by decide⟩,⟨277131, by decide⟩,⟨277137, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_24883_277138 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24883 ⟨277138, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 24883
    ⟨277138, by decide⟩ (by decide) (![⟨277083, by decide⟩,⟨277112, by decide⟩,⟨277131, by decide⟩,⟨277137, by decide⟩]) unmarked_context_12_24883_277138 node_context_12_24883_277138
  intro a
  fin_cases a
  · exact context_13_99532_277083
  · exact context_13_99533_277112
  · exact context_13_99534_277131
  · exact context_13_99535_277137

theorem unmarked_context_11_6220_277139 : frontier 10 ⟨277139, by decide⟩
    (prefixCache 11 6220) (prefixPartial 11 6220) = false := by
  decide +kernel

theorem node_context_11_6220_277139 : EJMOriginalGlobalDAGData.nodes 10 ⟨277139, by decide⟩ =
    .split (coordinate 11) (![⟨276946, by decide⟩,⟨277006, by decide⟩,⟨277073, by decide⟩,⟨277138, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6220_277139 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6220 ⟨277139, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6220
    ⟨277139, by decide⟩ (by decide) (![⟨276946, by decide⟩,⟨277006, by decide⟩,⟨277073, by decide⟩,⟨277138, by decide⟩]) unmarked_context_11_6220_277139 node_context_11_6220_277139
  intro a
  fin_cases a
  · exact context_12_24880_276946
  · exact context_12_24881_277006
  · exact context_12_24882_277073
  · exact context_12_24883_277138

theorem selected_cut_10133 : selected 8 ⟨277148, by decide⟩
    (prefixPartial 13 99536) = some ⟨13, 2, 0, 277148, 99536, 633, 16384⟩ := by
  decide +kernel

theorem context_13_99536_277148 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99536 ⟨277148, by decide⟩ :=
  accepted_of_selected 13 99536 ⟨277148, by decide⟩ ⟨13, 2, 0, 277148, 99536, 633, 16384⟩
    (by decide) selected_cut_10133

theorem selected_cut_10134 : selected 8 ⟨277171, by decide⟩
    (prefixPartial 13 99537) = some ⟨13, 2, 0, 277171, 99537, 1893, 16384⟩ := by
  decide +kernel

theorem context_13_99537_277171 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99537 ⟨277171, by decide⟩ :=
  accepted_of_selected 13 99537 ⟨277171, by decide⟩ ⟨13, 2, 0, 277171, 99537, 1893, 16384⟩
    (by decide) selected_cut_10134

theorem selected_cut_10135 : selected 8 ⟨277186, by decide⟩
    (prefixPartial 13 99538) = some ⟨13, 2, 0, 277186, 99538, 1401, 16384⟩ := by
  decide +kernel

theorem context_13_99538_277186 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99538 ⟨277186, by decide⟩ :=
  accepted_of_selected 13 99538 ⟨277186, by decide⟩ ⟨13, 2, 0, 277186, 99538, 1401, 16384⟩
    (by decide) selected_cut_10135

theorem selected_cut_10136 : selected 8 ⟨277194, by decide⟩
    (prefixPartial 13 99539) = some ⟨13, 2, 0, 277194, 99539, 877, 16384⟩ := by
  decide +kernel

theorem context_13_99539_277194 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99539 ⟨277194, by decide⟩ :=
  accepted_of_selected 13 99539 ⟨277194, by decide⟩ ⟨13, 2, 0, 277194, 99539, 877, 16384⟩
    (by decide) selected_cut_10136

theorem unmarked_context_12_24884_277195 : frontier 9 ⟨277195, by decide⟩
    (prefixCache 12 24884) (prefixPartial 12 24884) = false := by
  decide +kernel

theorem node_context_12_24884_277195 : EJMOriginalGlobalDAGData.nodes 9 ⟨277195, by decide⟩ =
    .split (coordinate 12) (![⟨277148, by decide⟩,⟨277171, by decide⟩,⟨277186, by decide⟩,⟨277194, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_24884_277195 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24884 ⟨277195, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 24884
    ⟨277195, by decide⟩ (by decide) (![⟨277148, by decide⟩,⟨277171, by decide⟩,⟨277186, by decide⟩,⟨277194, by decide⟩]) unmarked_context_12_24884_277195 node_context_12_24884_277195
  intro a
  fin_cases a
  · exact context_13_99536_277148
  · exact context_13_99537_277171
  · exact context_13_99538_277186
  · exact context_13_99539_277194

theorem selected_cut_10137 : selected 8 ⟨277210, by decide⟩
    (prefixPartial 13 99540) = some ⟨13, 2, 0, 277210, 99540, 837, 16384⟩ := by
  decide +kernel

theorem context_13_99540_277210 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99540 ⟨277210, by decide⟩ :=
  accepted_of_selected 13 99540 ⟨277210, by decide⟩ ⟨13, 2, 0, 277210, 99540, 837, 16384⟩
    (by decide) selected_cut_10137

theorem selected_cut_10138 : selected 8 ⟨277252, by decide⟩
    (prefixPartial 13 99541) = some ⟨13, 2, 0, 277252, 99541, 3409, 16384⟩ := by
  decide +kernel

theorem context_13_99541_277252 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99541 ⟨277252, by decide⟩ :=
  accepted_of_selected 13 99541 ⟨277252, by decide⟩ ⟨13, 2, 0, 277252, 99541, 3409, 16384⟩
    (by decide) selected_cut_10138

theorem selected_cut_10139 : selected 8 ⟨277278, by decide⟩
    (prefixPartial 13 99542) = some ⟨13, 2, 0, 277278, 99542, 2281, 16384⟩ := by
  decide +kernel

theorem context_13_99542_277278 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99542 ⟨277278, by decide⟩ :=
  accepted_of_selected 13 99542 ⟨277278, by decide⟩ ⟨13, 2, 0, 277278, 99542, 2281, 16384⟩
    (by decide) selected_cut_10139

theorem selected_cut_10140 : selected 8 ⟨277289, by decide⟩
    (prefixPartial 13 99543) = some ⟨13, 2, 0, 277289, 99543, 1177, 16384⟩ := by
  decide +kernel

theorem context_13_99543_277289 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99543 ⟨277289, by decide⟩ :=
  accepted_of_selected 13 99543 ⟨277289, by decide⟩ ⟨13, 2, 0, 277289, 99543, 1177, 16384⟩
    (by decide) selected_cut_10140

theorem unmarked_context_12_24885_277290 : frontier 9 ⟨277290, by decide⟩
    (prefixCache 12 24885) (prefixPartial 12 24885) = false := by
  decide +kernel

theorem node_context_12_24885_277290 : EJMOriginalGlobalDAGData.nodes 9 ⟨277290, by decide⟩ =
    .split (coordinate 12) (![⟨277210, by decide⟩,⟨277252, by decide⟩,⟨277278, by decide⟩,⟨277289, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_24885_277290 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24885 ⟨277290, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 24885
    ⟨277290, by decide⟩ (by decide) (![⟨277210, by decide⟩,⟨277252, by decide⟩,⟨277278, by decide⟩,⟨277289, by decide⟩]) unmarked_context_12_24885_277290 node_context_12_24885_277290
  intro a
  fin_cases a
  · exact context_13_99540_277210
  · exact context_13_99541_277252
  · exact context_13_99542_277278
  · exact context_13_99543_277289

theorem selected_cut_10141 : selected 8 ⟨277297, by decide⟩
    (prefixPartial 13 99544) = some ⟨13, 2, 0, 277297, 99544, 561, 16384⟩ := by
  decide +kernel

theorem context_13_99544_277297 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99544 ⟨277297, by decide⟩ :=
  accepted_of_selected 13 99544 ⟨277297, by decide⟩ ⟨13, 2, 0, 277297, 99544, 561, 16384⟩
    (by decide) selected_cut_10141

theorem selected_cut_10142 : selected 8 ⟨277323, by decide⟩
    (prefixPartial 13 99545) = some ⟨13, 2, 0, 277323, 99545, 2121, 16384⟩ := by
  decide +kernel

theorem context_13_99545_277323 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99545 ⟨277323, by decide⟩ :=
  accepted_of_selected 13 99545 ⟨277323, by decide⟩ ⟨13, 2, 0, 277323, 99545, 2121, 16384⟩
    (by decide) selected_cut_10142

theorem selected_cut_10143 : selected 8 ⟨277346, by decide⟩
    (prefixPartial 13 99546) = some ⟨13, 2, 0, 277346, 99546, 1477, 16384⟩ := by
  decide +kernel

theorem context_13_99546_277346 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99546 ⟨277346, by decide⟩ :=
  accepted_of_selected 13 99546 ⟨277346, by decide⟩ ⟨13, 2, 0, 277346, 99546, 1477, 16384⟩
    (by decide) selected_cut_10143

theorem selected_cut_10144 : selected 8 ⟨277355, by decide⟩
    (prefixPartial 13 99547) = some ⟨13, 2, 0, 277355, 99547, 889, 16384⟩ := by
  decide +kernel

theorem context_13_99547_277355 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99547 ⟨277355, by decide⟩ :=
  accepted_of_selected 13 99547 ⟨277355, by decide⟩ ⟨13, 2, 0, 277355, 99547, 889, 16384⟩
    (by decide) selected_cut_10144

theorem unmarked_context_12_24886_277356 : frontier 9 ⟨277356, by decide⟩
    (prefixCache 12 24886) (prefixPartial 12 24886) = false := by
  decide +kernel

theorem node_context_12_24886_277356 : EJMOriginalGlobalDAGData.nodes 9 ⟨277356, by decide⟩ =
    .split (coordinate 12) (![⟨277297, by decide⟩,⟨277323, by decide⟩,⟨277346, by decide⟩,⟨277355, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_24886_277356 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24886 ⟨277356, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 24886
    ⟨277356, by decide⟩ (by decide) (![⟨277297, by decide⟩,⟨277323, by decide⟩,⟨277346, by decide⟩,⟨277355, by decide⟩]) unmarked_context_12_24886_277356 node_context_12_24886_277356
  intro a
  fin_cases a
  · exact context_13_99544_277297
  · exact context_13_99545_277323
  · exact context_13_99546_277346
  · exact context_13_99547_277355

theorem selected_cut_10145 : selected 8 ⟨277364, by decide⟩
    (prefixPartial 13 99548) = some ⟨13, 2, 0, 277364, 99548, 529, 16384⟩ := by
  decide +kernel

theorem context_13_99548_277364 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99548 ⟨277364, by decide⟩ :=
  accepted_of_selected 13 99548 ⟨277364, by decide⟩ ⟨13, 2, 0, 277364, 99548, 529, 16384⟩
    (by decide) selected_cut_10145

theorem selected_cut_10146 : selected 8 ⟨277391, by decide⟩
    (prefixPartial 13 99549) = some ⟨13, 2, 0, 277391, 99549, 2521, 16384⟩ := by
  decide +kernel

theorem context_13_99549_277391 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99549 ⟨277391, by decide⟩ :=
  accepted_of_selected 13 99549 ⟨277391, by decide⟩ ⟨13, 2, 0, 277391, 99549, 2521, 16384⟩
    (by decide) selected_cut_10146

theorem selected_cut_10147 : selected 8 ⟨277411, by decide⟩
    (prefixPartial 13 99550) = some ⟨13, 2, 0, 277411, 99550, 1733, 16384⟩ := by
  decide +kernel

theorem context_13_99550_277411 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99550 ⟨277411, by decide⟩ :=
  accepted_of_selected 13 99550 ⟨277411, by decide⟩ ⟨13, 2, 0, 277411, 99550, 1733, 16384⟩
    (by decide) selected_cut_10147

theorem selected_cut_10148 : selected 8 ⟨277422, by decide⟩
    (prefixPartial 13 99551) = some ⟨13, 2, 0, 277422, 99551, 973, 16384⟩ := by
  decide +kernel

theorem context_13_99551_277422 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99551 ⟨277422, by decide⟩ :=
  accepted_of_selected 13 99551 ⟨277422, by decide⟩ ⟨13, 2, 0, 277422, 99551, 973, 16384⟩
    (by decide) selected_cut_10148

theorem unmarked_context_12_24887_277423 : frontier 9 ⟨277423, by decide⟩
    (prefixCache 12 24887) (prefixPartial 12 24887) = false := by
  decide +kernel

theorem node_context_12_24887_277423 : EJMOriginalGlobalDAGData.nodes 9 ⟨277423, by decide⟩ =
    .split (coordinate 12) (![⟨277364, by decide⟩,⟨277391, by decide⟩,⟨277411, by decide⟩,⟨277422, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_24887_277423 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24887 ⟨277423, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 24887
    ⟨277423, by decide⟩ (by decide) (![⟨277364, by decide⟩,⟨277391, by decide⟩,⟨277411, by decide⟩,⟨277422, by decide⟩]) unmarked_context_12_24887_277423 node_context_12_24887_277423
  intro a
  fin_cases a
  · exact context_13_99548_277364
  · exact context_13_99549_277391
  · exact context_13_99550_277411
  · exact context_13_99551_277422

theorem unmarked_context_11_6221_277424 : frontier 10 ⟨277424, by decide⟩
    (prefixCache 11 6221) (prefixPartial 11 6221) = false := by
  decide +kernel

theorem node_context_11_6221_277424 : EJMOriginalGlobalDAGData.nodes 10 ⟨277424, by decide⟩ =
    .split (coordinate 11) (![⟨277195, by decide⟩,⟨277290, by decide⟩,⟨277356, by decide⟩,⟨277423, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6221_277424 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6221 ⟨277424, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6221
    ⟨277424, by decide⟩ (by decide) (![⟨277195, by decide⟩,⟨277290, by decide⟩,⟨277356, by decide⟩,⟨277423, by decide⟩]) unmarked_context_11_6221_277424 node_context_11_6221_277424
  intro a
  fin_cases a
  · exact context_12_24884_277195
  · exact context_12_24885_277290
  · exact context_12_24886_277356
  · exact context_12_24887_277423

theorem selected_cut_10149 : selected 8 ⟨277432, by decide⟩
    (prefixPartial 13 99552) = some ⟨13, 2, 0, 277432, 99552, 585, 16384⟩ := by
  decide +kernel

theorem context_13_99552_277432 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99552 ⟨277432, by decide⟩ :=
  accepted_of_selected 13 99552 ⟨277432, by decide⟩ ⟨13, 2, 0, 277432, 99552, 585, 16384⟩
    (by decide) selected_cut_10149

theorem selected_cut_10150 : selected 8 ⟨277460, by decide⟩
    (prefixPartial 13 99553) = some ⟨13, 2, 0, 277460, 99553, 2173, 16384⟩ := by
  decide +kernel

theorem context_13_99553_277460 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99553 ⟨277460, by decide⟩ :=
  accepted_of_selected 13 99553 ⟨277460, by decide⟩ ⟨13, 2, 0, 277460, 99553, 2173, 16384⟩
    (by decide) selected_cut_10150

theorem selected_cut_10151 : selected 8 ⟨277479, by decide⟩
    (prefixPartial 13 99554) = some ⟨13, 2, 0, 277479, 99554, 1813, 16384⟩ := by
  decide +kernel

theorem context_13_99554_277479 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99554 ⟨277479, by decide⟩ :=
  accepted_of_selected 13 99554 ⟨277479, by decide⟩ ⟨13, 2, 0, 277479, 99554, 1813, 16384⟩
    (by decide) selected_cut_10151

theorem selected_cut_10152 : selected 8 ⟨277486, by decide⟩
    (prefixPartial 13 99555) = some ⟨13, 2, 0, 277486, 99555, 861, 16384⟩ := by
  decide +kernel

theorem context_13_99555_277486 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99555 ⟨277486, by decide⟩ :=
  accepted_of_selected 13 99555 ⟨277486, by decide⟩ ⟨13, 2, 0, 277486, 99555, 861, 16384⟩
    (by decide) selected_cut_10152

theorem unmarked_context_12_24888_277487 : frontier 9 ⟨277487, by decide⟩
    (prefixCache 12 24888) (prefixPartial 12 24888) = false := by
  decide +kernel

theorem node_context_12_24888_277487 : EJMOriginalGlobalDAGData.nodes 9 ⟨277487, by decide⟩ =
    .split (coordinate 12) (![⟨277432, by decide⟩,⟨277460, by decide⟩,⟨277479, by decide⟩,⟨277486, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_24888_277487 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24888 ⟨277487, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 24888
    ⟨277487, by decide⟩ (by decide) (![⟨277432, by decide⟩,⟨277460, by decide⟩,⟨277479, by decide⟩,⟨277486, by decide⟩]) unmarked_context_12_24888_277487 node_context_12_24888_277487
  intro a
  fin_cases a
  · exact context_13_99552_277432
  · exact context_13_99553_277460
  · exact context_13_99554_277479
  · exact context_13_99555_277486

theorem selected_cut_10153 : selected 8 ⟨277491, by decide⟩
    (prefixPartial 13 99556) = some ⟨13, 2, 0, 277491, 99556, 445, 16384⟩ := by
  decide +kernel

theorem context_13_99556_277491 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99556 ⟨277491, by decide⟩ :=
  accepted_of_selected 13 99556 ⟨277491, by decide⟩ ⟨13, 2, 0, 277491, 99556, 445, 16384⟩
    (by decide) selected_cut_10153

theorem selected_cut_10154 : selected 8 ⟨277518, by decide⟩
    (prefixPartial 13 99557) = some ⟨13, 2, 0, 277518, 99557, 2041, 16384⟩ := by
  decide +kernel

theorem context_13_99557_277518 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99557 ⟨277518, by decide⟩ :=
  accepted_of_selected 13 99557 ⟨277518, by decide⟩ ⟨13, 2, 0, 277518, 99557, 2041, 16384⟩
    (by decide) selected_cut_10154

theorem selected_cut_10155 : selected 8 ⟨277540, by decide⟩
    (prefixPartial 13 99558) = some ⟨13, 2, 0, 277540, 99558, 1757, 16384⟩ := by
  decide +kernel

theorem context_13_99558_277540 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99558 ⟨277540, by decide⟩ :=
  accepted_of_selected 13 99558 ⟨277540, by decide⟩ ⟨13, 2, 0, 277540, 99558, 1757, 16384⟩
    (by decide) selected_cut_10155

theorem selected_cut_10156 : selected 8 ⟨277549, by decide⟩
    (prefixPartial 13 99559) = some ⟨13, 2, 0, 277549, 99559, 845, 16384⟩ := by
  decide +kernel

theorem context_13_99559_277549 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99559 ⟨277549, by decide⟩ :=
  accepted_of_selected 13 99559 ⟨277549, by decide⟩ ⟨13, 2, 0, 277549, 99559, 845, 16384⟩
    (by decide) selected_cut_10156

theorem unmarked_context_12_24889_277550 : frontier 9 ⟨277550, by decide⟩
    (prefixCache 12 24889) (prefixPartial 12 24889) = false := by
  decide +kernel

theorem node_context_12_24889_277550 : EJMOriginalGlobalDAGData.nodes 9 ⟨277550, by decide⟩ =
    .split (coordinate 12) (![⟨277491, by decide⟩,⟨277518, by decide⟩,⟨277540, by decide⟩,⟨277549, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_24889_277550 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24889 ⟨277550, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 24889
    ⟨277550, by decide⟩ (by decide) (![⟨277491, by decide⟩,⟨277518, by decide⟩,⟨277540, by decide⟩,⟨277549, by decide⟩]) unmarked_context_12_24889_277550 node_context_12_24889_277550
  intro a
  fin_cases a
  · exact context_13_99556_277491
  · exact context_13_99557_277518
  · exact context_13_99558_277540
  · exact context_13_99559_277549

theorem selected_cut_10157 : selected 8 ⟨277554, by decide⟩
    (prefixPartial 13 99560) = some ⟨13, 2, 0, 277554, 99560, 397, 16384⟩ := by
  decide +kernel

theorem context_13_99560_277554 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99560 ⟨277554, by decide⟩ :=
  accepted_of_selected 13 99560 ⟨277554, by decide⟩ ⟨13, 2, 0, 277554, 99560, 397, 16384⟩
    (by decide) selected_cut_10157

theorem selected_cut_10158 : selected 8 ⟨277578, by decide⟩
    (prefixPartial 13 99561) = some ⟨13, 2, 0, 277578, 99561, 2453, 16384⟩ := by
  decide +kernel

theorem context_13_99561_277578 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99561 ⟨277578, by decide⟩ :=
  accepted_of_selected 13 99561 ⟨277578, by decide⟩ ⟨13, 2, 0, 277578, 99561, 2453, 16384⟩
    (by decide) selected_cut_10158

theorem selected_cut_10159 : selected 8 ⟨277597, by decide⟩
    (prefixPartial 13 99562) = some ⟨13, 2, 0, 277597, 99562, 1709, 16384⟩ := by
  decide +kernel

theorem context_13_99562_277597 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99562 ⟨277597, by decide⟩ :=
  accepted_of_selected 13 99562 ⟨277597, by decide⟩ ⟨13, 2, 0, 277597, 99562, 1709, 16384⟩
    (by decide) selected_cut_10159

theorem selected_cut_10160 : selected 8 ⟨277604, by decide⟩
    (prefixPartial 13 99563) = some ⟨13, 2, 0, 277604, 99563, 801, 16384⟩ := by
  decide +kernel

theorem context_13_99563_277604 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99563 ⟨277604, by decide⟩ :=
  accepted_of_selected 13 99563 ⟨277604, by decide⟩ ⟨13, 2, 0, 277604, 99563, 801, 16384⟩
    (by decide) selected_cut_10160

theorem unmarked_context_12_24890_277605 : frontier 9 ⟨277605, by decide⟩
    (prefixCache 12 24890) (prefixPartial 12 24890) = false := by
  decide +kernel

theorem node_context_12_24890_277605 : EJMOriginalGlobalDAGData.nodes 9 ⟨277605, by decide⟩ =
    .split (coordinate 12) (![⟨277554, by decide⟩,⟨277578, by decide⟩,⟨277597, by decide⟩,⟨277604, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_24890_277605 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24890 ⟨277605, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 24890
    ⟨277605, by decide⟩ (by decide) (![⟨277554, by decide⟩,⟨277578, by decide⟩,⟨277597, by decide⟩,⟨277604, by decide⟩]) unmarked_context_12_24890_277605 node_context_12_24890_277605
  intro a
  fin_cases a
  · exact context_13_99560_277554
  · exact context_13_99561_277578
  · exact context_13_99562_277597
  · exact context_13_99563_277604

theorem selected_cut_10161 : selected 8 ⟨277610, by decide⟩
    (prefixPartial 13 99564) = some ⟨13, 2, 0, 277610, 99564, 377, 16384⟩ := by
  decide +kernel

theorem context_13_99564_277610 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99564 ⟨277610, by decide⟩ :=
  accepted_of_selected 13 99564 ⟨277610, by decide⟩ ⟨13, 2, 0, 277610, 99564, 377, 16384⟩
    (by decide) selected_cut_10161

theorem selected_cut_10162 : selected 8 ⟨277639, by decide⟩
    (prefixPartial 13 99565) = some ⟨13, 2, 0, 277639, 99565, 2837, 16384⟩ := by
  decide +kernel

theorem context_13_99565_277639 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99565 ⟨277639, by decide⟩ :=
  accepted_of_selected 13 99565 ⟨277639, by decide⟩ ⟨13, 2, 0, 277639, 99565, 2837, 16384⟩
    (by decide) selected_cut_10162

theorem selected_cut_10163 : selected 8 ⟨277659, by decide⟩
    (prefixPartial 13 99566) = some ⟨13, 2, 0, 277659, 99566, 1793, 16384⟩ := by
  decide +kernel

theorem context_13_99566_277659 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99566 ⟨277659, by decide⟩ :=
  accepted_of_selected 13 99566 ⟨277659, by decide⟩ ⟨13, 2, 0, 277659, 99566, 1793, 16384⟩
    (by decide) selected_cut_10163

theorem selected_cut_10164 : selected 8 ⟨277665, by decide⟩
    (prefixPartial 13 99567) = some ⟨13, 2, 0, 277665, 99567, 893, 16384⟩ := by
  decide +kernel

theorem context_13_99567_277665 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99567 ⟨277665, by decide⟩ :=
  accepted_of_selected 13 99567 ⟨277665, by decide⟩ ⟨13, 2, 0, 277665, 99567, 893, 16384⟩
    (by decide) selected_cut_10164

theorem unmarked_context_12_24891_277666 : frontier 9 ⟨277666, by decide⟩
    (prefixCache 12 24891) (prefixPartial 12 24891) = false := by
  decide +kernel

theorem node_context_12_24891_277666 : EJMOriginalGlobalDAGData.nodes 9 ⟨277666, by decide⟩ =
    .split (coordinate 12) (![⟨277610, by decide⟩,⟨277639, by decide⟩,⟨277659, by decide⟩,⟨277665, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_24891_277666 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24891 ⟨277666, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 24891
    ⟨277666, by decide⟩ (by decide) (![⟨277610, by decide⟩,⟨277639, by decide⟩,⟨277659, by decide⟩,⟨277665, by decide⟩]) unmarked_context_12_24891_277666 node_context_12_24891_277666
  intro a
  fin_cases a
  · exact context_13_99564_277610
  · exact context_13_99565_277639
  · exact context_13_99566_277659
  · exact context_13_99567_277665

theorem unmarked_context_11_6222_277667 : frontier 10 ⟨277667, by decide⟩
    (prefixCache 11 6222) (prefixPartial 11 6222) = false := by
  decide +kernel

theorem node_context_11_6222_277667 : EJMOriginalGlobalDAGData.nodes 10 ⟨277667, by decide⟩ =
    .split (coordinate 11) (![⟨277487, by decide⟩,⟨277550, by decide⟩,⟨277605, by decide⟩,⟨277666, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6222_277667 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6222 ⟨277667, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6222
    ⟨277667, by decide⟩ (by decide) (![⟨277487, by decide⟩,⟨277550, by decide⟩,⟨277605, by decide⟩,⟨277666, by decide⟩]) unmarked_context_11_6222_277667 node_context_11_6222_277667
  intro a
  fin_cases a
  · exact context_12_24888_277487
  · exact context_12_24889_277550
  · exact context_12_24890_277605
  · exact context_12_24891_277666

theorem selected_cut_10165 : selected 8 ⟨277670, by decide⟩
    (prefixPartial 13 99568) = some ⟨13, 2, 0, 277670, 99568, 193, 16384⟩ := by
  decide +kernel

theorem context_13_99568_277670 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99568 ⟨277670, by decide⟩ :=
  accepted_of_selected 13 99568 ⟨277670, by decide⟩ ⟨13, 2, 0, 277670, 99568, 193, 16384⟩
    (by decide) selected_cut_10165

theorem selected_cut_10166 : selected 8 ⟨277695, by decide⟩
    (prefixPartial 13 99569) = some ⟨13, 2, 0, 277695, 99569, 2333, 16384⟩ := by
  decide +kernel

theorem context_13_99569_277695 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99569 ⟨277695, by decide⟩ :=
  accepted_of_selected 13 99569 ⟨277695, by decide⟩ ⟨13, 2, 0, 277695, 99569, 2333, 16384⟩
    (by decide) selected_cut_10166

theorem selected_cut_10167 : selected 8 ⟨277716, by decide⟩
    (prefixPartial 13 99570) = some ⟨13, 2, 0, 277716, 99570, 1721, 16384⟩ := by
  decide +kernel

theorem context_13_99570_277716 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99570 ⟨277716, by decide⟩ :=
  accepted_of_selected 13 99570 ⟨277716, by decide⟩ ⟨13, 2, 0, 277716, 99570, 1721, 16384⟩
    (by decide) selected_cut_10167

theorem selected_cut_10168 : selected 8 ⟨277724, by decide⟩
    (prefixPartial 13 99571) = some ⟨13, 2, 0, 277724, 99571, 973, 16384⟩ := by
  decide +kernel

theorem context_13_99571_277724 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99571 ⟨277724, by decide⟩ :=
  accepted_of_selected 13 99571 ⟨277724, by decide⟩ ⟨13, 2, 0, 277724, 99571, 973, 16384⟩
    (by decide) selected_cut_10168

theorem unmarked_context_12_24892_277725 : frontier 9 ⟨277725, by decide⟩
    (prefixCache 12 24892) (prefixPartial 12 24892) = false := by
  decide +kernel

theorem node_context_12_24892_277725 : EJMOriginalGlobalDAGData.nodes 9 ⟨277725, by decide⟩ =
    .split (coordinate 12) (![⟨277670, by decide⟩,⟨277695, by decide⟩,⟨277716, by decide⟩,⟨277724, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_24892_277725 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24892 ⟨277725, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 24892
    ⟨277725, by decide⟩ (by decide) (![⟨277670, by decide⟩,⟨277695, by decide⟩,⟨277716, by decide⟩,⟨277724, by decide⟩]) unmarked_context_12_24892_277725 node_context_12_24892_277725
  intro a
  fin_cases a
  · exact context_13_99568_277670
  · exact context_13_99569_277695
  · exact context_13_99570_277716
  · exact context_13_99571_277724

theorem selected_cut_10169 : selected 8 ⟨277729, by decide⟩
    (prefixPartial 13 99572) = some ⟨13, 2, 0, 277729, 99572, 129, 16384⟩ := by
  decide +kernel

theorem context_13_99572_277729 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99572 ⟨277729, by decide⟩ :=
  accepted_of_selected 13 99572 ⟨277729, by decide⟩ ⟨13, 2, 0, 277729, 99572, 129, 16384⟩
    (by decide) selected_cut_10169

theorem selected_cut_10170 : selected 8 ⟨277752, by decide⟩
    (prefixPartial 13 99573) = some ⟨13, 2, 0, 277752, 99573, 2513, 16384⟩ := by
  decide +kernel

theorem context_13_99573_277752 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99573 ⟨277752, by decide⟩ :=
  accepted_of_selected 13 99573 ⟨277752, by decide⟩ ⟨13, 2, 0, 277752, 99573, 2513, 16384⟩
    (by decide) selected_cut_10170

theorem selected_cut_10171 : selected 8 ⟨277774, by decide⟩
    (prefixPartial 13 99574) = some ⟨13, 2, 0, 277774, 99574, 1857, 16384⟩ := by
  decide +kernel

theorem context_13_99574_277774 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99574 ⟨277774, by decide⟩ :=
  accepted_of_selected 13 99574 ⟨277774, by decide⟩ ⟨13, 2, 0, 277774, 99574, 1857, 16384⟩
    (by decide) selected_cut_10171

theorem selected_cut_10172 : selected 8 ⟨277783, by decide⟩
    (prefixPartial 13 99575) = some ⟨13, 2, 0, 277783, 99575, 909, 16384⟩ := by
  decide +kernel

theorem context_13_99575_277783 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99575 ⟨277783, by decide⟩ :=
  accepted_of_selected 13 99575 ⟨277783, by decide⟩ ⟨13, 2, 0, 277783, 99575, 909, 16384⟩
    (by decide) selected_cut_10172

theorem unmarked_context_12_24893_277784 : frontier 9 ⟨277784, by decide⟩
    (prefixCache 12 24893) (prefixPartial 12 24893) = false := by
  decide +kernel

theorem node_context_12_24893_277784 : EJMOriginalGlobalDAGData.nodes 9 ⟨277784, by decide⟩ =
    .split (coordinate 12) (![⟨277729, by decide⟩,⟨277752, by decide⟩,⟨277774, by decide⟩,⟨277783, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_24893_277784 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24893 ⟨277784, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 24893
    ⟨277784, by decide⟩ (by decide) (![⟨277729, by decide⟩,⟨277752, by decide⟩,⟨277774, by decide⟩,⟨277783, by decide⟩]) unmarked_context_12_24893_277784 node_context_12_24893_277784
  intro a
  fin_cases a
  · exact context_13_99572_277729
  · exact context_13_99573_277752
  · exact context_13_99574_277774
  · exact context_13_99575_277783

theorem selected_cut_10173 : selected 8 ⟨277788, by decide⟩
    (prefixPartial 13 99576) = some ⟨13, 2, 0, 277788, 99576, 121, 16384⟩ := by
  decide +kernel

theorem context_13_99576_277788 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99576 ⟨277788, by decide⟩ :=
  accepted_of_selected 13 99576 ⟨277788, by decide⟩ ⟨13, 2, 0, 277788, 99576, 121, 16384⟩
    (by decide) selected_cut_10173

theorem selected_cut_10174 : selected 8 ⟨277814, by decide⟩
    (prefixPartial 13 99577) = some ⟨13, 2, 0, 277814, 99577, 2693, 16384⟩ := by
  decide +kernel

theorem context_13_99577_277814 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99577 ⟨277814, by decide⟩ :=
  accepted_of_selected 13 99577 ⟨277814, by decide⟩ ⟨13, 2, 0, 277814, 99577, 2693, 16384⟩
    (by decide) selected_cut_10174

theorem selected_cut_10175 : selected 8 ⟨277836, by decide⟩
    (prefixPartial 13 99578) = some ⟨13, 2, 0, 277836, 99578, 1617, 16384⟩ := by
  decide +kernel

theorem context_13_99578_277836 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99578 ⟨277836, by decide⟩ :=
  accepted_of_selected 13 99578 ⟨277836, by decide⟩ ⟨13, 2, 0, 277836, 99578, 1617, 16384⟩
    (by decide) selected_cut_10175

theorem selected_cut_10176 : selected 8 ⟨277843, by decide⟩
    (prefixPartial 13 99579) = some ⟨13, 2, 0, 277843, 99579, 877, 16384⟩ := by
  decide +kernel

theorem context_13_99579_277843 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99579 ⟨277843, by decide⟩ :=
  accepted_of_selected 13 99579 ⟨277843, by decide⟩ ⟨13, 2, 0, 277843, 99579, 877, 16384⟩
    (by decide) selected_cut_10176

theorem unmarked_context_12_24894_277844 : frontier 9 ⟨277844, by decide⟩
    (prefixCache 12 24894) (prefixPartial 12 24894) = false := by
  decide +kernel

theorem node_context_12_24894_277844 : EJMOriginalGlobalDAGData.nodes 9 ⟨277844, by decide⟩ =
    .split (coordinate 12) (![⟨277788, by decide⟩,⟨277814, by decide⟩,⟨277836, by decide⟩,⟨277843, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_24894_277844 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24894 ⟨277844, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 24894
    ⟨277844, by decide⟩ (by decide) (![⟨277788, by decide⟩,⟨277814, by decide⟩,⟨277836, by decide⟩,⟨277843, by decide⟩]) unmarked_context_12_24894_277844 node_context_12_24894_277844
  intro a
  fin_cases a
  · exact context_13_99576_277788
  · exact context_13_99577_277814
  · exact context_13_99578_277836
  · exact context_13_99579_277843

theorem selected_cut_10177 : selected 8 ⟨277847, by decide⟩
    (prefixPartial 13 99580) = some ⟨13, 2, 0, 277847, 99580, 81, 16384⟩ := by
  decide +kernel

theorem context_13_99580_277847 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99580 ⟨277847, by decide⟩ :=
  accepted_of_selected 13 99580 ⟨277847, by decide⟩ ⟨13, 2, 0, 277847, 99580, 81, 16384⟩
    (by decide) selected_cut_10177

theorem selected_cut_10178 : selected 8 ⟨277871, by decide⟩
    (prefixPartial 13 99581) = some ⟨13, 2, 0, 277871, 99581, 2709, 16384⟩ := by
  decide +kernel

theorem context_13_99581_277871 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99581 ⟨277871, by decide⟩ :=
  accepted_of_selected 13 99581 ⟨277871, by decide⟩ ⟨13, 2, 0, 277871, 99581, 2709, 16384⟩
    (by decide) selected_cut_10178

theorem selected_cut_10179 : selected 8 ⟨277891, by decide⟩
    (prefixPartial 13 99582) = some ⟨13, 2, 0, 277891, 99582, 1797, 16384⟩ := by
  decide +kernel

theorem context_13_99582_277891 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99582 ⟨277891, by decide⟩ :=
  accepted_of_selected 13 99582 ⟨277891, by decide⟩ ⟨13, 2, 0, 277891, 99582, 1797, 16384⟩
    (by decide) selected_cut_10179

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
