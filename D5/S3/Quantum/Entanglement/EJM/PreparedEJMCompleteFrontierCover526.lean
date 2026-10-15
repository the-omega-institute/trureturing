/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover525
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_50499 : selected 10 ⟨1443364, by decide⟩
    (prefixPartial 11 106320) = some ⟨11, 2, 0, 1443364, 106320, 1365, 262144⟩ := by
  decide +kernel

theorem context_11_106320_1443364 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106320 ⟨1443364, by decide⟩ :=
  accepted_of_selected 11 106320 ⟨1443364, by decide⟩ ⟨11, 2, 0, 1443364, 106320, 1365, 262144⟩
    (by decide) selected_cut_50499

theorem selected_cut_50500 : selected 10 ⟨1443442, by decide⟩
    (prefixPartial 11 106321) = some ⟨11, 2, 0, 1443442, 106321, 3485, 262144⟩ := by
  decide +kernel

theorem context_11_106321_1443442 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106321 ⟨1443442, by decide⟩ :=
  accepted_of_selected 11 106321 ⟨1443442, by decide⟩ ⟨11, 2, 0, 1443442, 106321, 3485, 262144⟩
    (by decide) selected_cut_50500

theorem selected_cut_50501 : selected 10 ⟨1443501, by decide⟩
    (prefixPartial 11 106322) = some ⟨11, 2, 0, 1443501, 106322, 2389, 262144⟩ := by
  decide +kernel

theorem context_11_106322_1443501 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106322 ⟨1443501, by decide⟩ :=
  accepted_of_selected 11 106322 ⟨1443501, by decide⟩ ⟨11, 2, 0, 1443501, 106322, 2389, 262144⟩
    (by decide) selected_cut_50501

theorem selected_cut_50502 : selected 10 ⟨1443554, by decide⟩
    (prefixPartial 11 106323) = some ⟨11, 2, 0, 1443554, 106323, 2389, 262144⟩ := by
  decide +kernel

theorem context_11_106323_1443554 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106323 ⟨1443554, by decide⟩ :=
  accepted_of_selected 11 106323 ⟨1443554, by decide⟩ ⟨11, 2, 0, 1443554, 106323, 2389, 262144⟩
    (by decide) selected_cut_50502

theorem unmarked_context_10_26580_1443555 : frontier 11 ⟨1443555, by decide⟩
    (prefixCache 10 26580) (prefixPartial 10 26580) = false := by
  decide +kernel

theorem node_context_10_26580_1443555 : EJMOriginalGlobalDAGData.nodes 11 ⟨1443555, by decide⟩ =
    .split (coordinate 10) (![⟨1443364, by decide⟩,⟨1443442, by decide⟩,⟨1443501, by decide⟩,⟨1443554, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_26580_1443555 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26580 ⟨1443555, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 26580
    ⟨1443555, by decide⟩ (by decide) (![⟨1443364, by decide⟩,⟨1443442, by decide⟩,⟨1443501, by decide⟩,⟨1443554, by decide⟩]) unmarked_context_10_26580_1443555 node_context_10_26580_1443555
  intro a
  fin_cases a
  · exact context_11_106320_1443364
  · exact context_11_106321_1443442
  · exact context_11_106322_1443501
  · exact context_11_106323_1443554

theorem selected_cut_50503 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 26581) = some ⟨10, 1, 0, 893098, 26581, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_26581_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26581 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 26581 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 26581, 1, 1048576⟩
    (by decide) selected_cut_50503

theorem selected_cut_50504 : selected 10 ⟨1443626, by decide⟩
    (prefixPartial 11 106328) = some ⟨11, 2, 0, 1443626, 106328, 2421, 262144⟩ := by
  decide +kernel

theorem context_11_106328_1443626 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106328 ⟨1443626, by decide⟩ :=
  accepted_of_selected 11 106328 ⟨1443626, by decide⟩ ⟨11, 2, 0, 1443626, 106328, 2421, 262144⟩
    (by decide) selected_cut_50504

theorem selected_cut_50505 : selected 10 ⟨1443699, by decide⟩
    (prefixPartial 11 106329) = some ⟨11, 2, 0, 1443699, 106329, 2865, 262144⟩ := by
  decide +kernel

theorem context_11_106329_1443699 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106329 ⟨1443699, by decide⟩ :=
  accepted_of_selected 11 106329 ⟨1443699, by decide⟩ ⟨11, 2, 0, 1443699, 106329, 2865, 262144⟩
    (by decide) selected_cut_50505

theorem selected_cut_50506 : selected 10 ⟨1443722, by decide⟩
    (prefixPartial 11 106330) = some ⟨11, 2, 0, 1443722, 106330, 969, 262144⟩ := by
  decide +kernel

theorem context_11_106330_1443722 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106330 ⟨1443722, by decide⟩ :=
  accepted_of_selected 11 106330 ⟨1443722, by decide⟩ ⟨11, 2, 0, 1443722, 106330, 969, 262144⟩
    (by decide) selected_cut_50506

theorem selected_cut_50507 : selected 10 ⟨1443761, by decide⟩
    (prefixPartial 11 106331) = some ⟨11, 2, 0, 1443761, 106331, 1753, 262144⟩ := by
  decide +kernel

theorem context_11_106331_1443761 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106331 ⟨1443761, by decide⟩ :=
  accepted_of_selected 11 106331 ⟨1443761, by decide⟩ ⟨11, 2, 0, 1443761, 106331, 1753, 262144⟩
    (by decide) selected_cut_50507

theorem unmarked_context_10_26582_1443762 : frontier 11 ⟨1443762, by decide⟩
    (prefixCache 10 26582) (prefixPartial 10 26582) = false := by
  decide +kernel

theorem node_context_10_26582_1443762 : EJMOriginalGlobalDAGData.nodes 11 ⟨1443762, by decide⟩ =
    .split (coordinate 10) (![⟨1443626, by decide⟩,⟨1443699, by decide⟩,⟨1443722, by decide⟩,⟨1443761, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_26582_1443762 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26582 ⟨1443762, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 26582
    ⟨1443762, by decide⟩ (by decide) (![⟨1443626, by decide⟩,⟨1443699, by decide⟩,⟨1443722, by decide⟩,⟨1443761, by decide⟩]) unmarked_context_10_26582_1443762 node_context_10_26582_1443762
  intro a
  fin_cases a
  · exact context_11_106328_1443626
  · exact context_11_106329_1443699
  · exact context_11_106330_1443722
  · exact context_11_106331_1443761

theorem selected_cut_50508 : selected 10 ⟨1443801, by decide⟩
    (prefixPartial 11 106332) = some ⟨11, 2, 0, 1443801, 106332, 1645, 262144⟩ := by
  decide +kernel

theorem context_11_106332_1443801 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106332 ⟨1443801, by decide⟩ :=
  accepted_of_selected 11 106332 ⟨1443801, by decide⟩ ⟨11, 2, 0, 1443801, 106332, 1645, 262144⟩
    (by decide) selected_cut_50508

theorem selected_cut_50509 : selected 10 ⟨1443843, by decide⟩
    (prefixPartial 11 106333) = some ⟨11, 2, 0, 1443843, 106333, 2041, 262144⟩ := by
  decide +kernel

theorem context_11_106333_1443843 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106333 ⟨1443843, by decide⟩ :=
  accepted_of_selected 11 106333 ⟨1443843, by decide⟩ ⟨11, 2, 0, 1443843, 106333, 2041, 262144⟩
    (by decide) selected_cut_50509

theorem selected_cut_50510 : selected 10 ⟨1443879, by decide⟩
    (prefixPartial 11 106334) = some ⟨11, 2, 0, 1443879, 106334, 1397, 262144⟩ := by
  decide +kernel

theorem context_11_106334_1443879 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106334 ⟨1443879, by decide⟩ :=
  accepted_of_selected 11 106334 ⟨1443879, by decide⟩ ⟨11, 2, 0, 1443879, 106334, 1397, 262144⟩
    (by decide) selected_cut_50510

theorem selected_cut_50511 : selected 10 ⟨977886, by decide⟩
    (prefixPartial 11 106335) = some ⟨11, 1, 0, 977886, 106335, 1, 262144⟩ := by
  decide +kernel

theorem context_11_106335_977886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106335 ⟨977886, by decide⟩ :=
  accepted_of_selected 11 106335 ⟨977886, by decide⟩ ⟨11, 1, 0, 977886, 106335, 1, 262144⟩
    (by decide) selected_cut_50511

theorem unmarked_context_10_26583_1443880 : frontier 11 ⟨1443880, by decide⟩
    (prefixCache 10 26583) (prefixPartial 10 26583) = false := by
  decide +kernel

theorem node_context_10_26583_1443880 : EJMOriginalGlobalDAGData.nodes 11 ⟨1443880, by decide⟩ =
    .split (coordinate 10) (![⟨1443801, by decide⟩,⟨1443843, by decide⟩,⟨1443879, by decide⟩,⟨977886, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_26583_1443880 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26583 ⟨1443880, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 26583
    ⟨1443880, by decide⟩ (by decide) (![⟨1443801, by decide⟩,⟨1443843, by decide⟩,⟨1443879, by decide⟩,⟨977886, by decide⟩]) unmarked_context_10_26583_1443880 node_context_10_26583_1443880
  intro a
  fin_cases a
  · exact context_11_106332_1443801
  · exact context_11_106333_1443843
  · exact context_11_106334_1443879
  · exact context_11_106335_977886

theorem unmarked_context_9_6645_1443881 : frontier 12 ⟨1443881, by decide⟩
    (prefixCache 9 6645) (prefixPartial 9 6645) = false := by
  decide +kernel

theorem node_context_9_6645_1443881 : EJMOriginalGlobalDAGData.nodes 12 ⟨1443881, by decide⟩ =
    .split (coordinate 9) (![⟨1443555, by decide⟩,⟨893098, by decide⟩,⟨1443762, by decide⟩,⟨1443880, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6645_1443881 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6645 ⟨1443881, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6645
    ⟨1443881, by decide⟩ (by decide) (![⟨1443555, by decide⟩,⟨893098, by decide⟩,⟨1443762, by decide⟩,⟨1443880, by decide⟩]) unmarked_context_9_6645_1443881 node_context_9_6645_1443881
  intro a
  fin_cases a
  · exact context_10_26580_1443555
  · exact context_10_26581_893098
  · exact context_10_26582_1443762
  · exact context_10_26583_1443880

theorem selected_cut_50512 : selected 10 ⟨1443909, by decide⟩
    (prefixPartial 11 106336) = some ⟨11, 2, 0, 1443909, 106336, 853, 262144⟩ := by
  decide +kernel

theorem context_11_106336_1443909 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106336 ⟨1443909, by decide⟩ :=
  accepted_of_selected 11 106336 ⟨1443909, by decide⟩ ⟨11, 2, 0, 1443909, 106336, 853, 262144⟩
    (by decide) selected_cut_50512

theorem selected_cut_50513 : selected 10 ⟨1443949, by decide⟩
    (prefixPartial 11 106337) = some ⟨11, 2, 0, 1443949, 106337, 1533, 262144⟩ := by
  decide +kernel

theorem context_11_106337_1443949 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106337 ⟨1443949, by decide⟩ :=
  accepted_of_selected 11 106337 ⟨1443949, by decide⟩ ⟨11, 2, 0, 1443949, 106337, 1533, 262144⟩
    (by decide) selected_cut_50513

theorem selected_cut_50514 : selected 10 ⟨1443998, by decide⟩
    (prefixPartial 11 106338) = some ⟨11, 2, 0, 1443998, 106338, 2225, 262144⟩ := by
  decide +kernel

theorem context_11_106338_1443998 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106338 ⟨1443998, by decide⟩ :=
  accepted_of_selected 11 106338 ⟨1443998, by decide⟩ ⟨11, 2, 0, 1443998, 106338, 2225, 262144⟩
    (by decide) selected_cut_50514

theorem selected_cut_50515 : selected 10 ⟨1444034, by decide⟩
    (prefixPartial 11 106339) = some ⟨11, 2, 0, 1444034, 106339, 1245, 262144⟩ := by
  decide +kernel

theorem context_11_106339_1444034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106339 ⟨1444034, by decide⟩ :=
  accepted_of_selected 11 106339 ⟨1444034, by decide⟩ ⟨11, 2, 0, 1444034, 106339, 1245, 262144⟩
    (by decide) selected_cut_50515

theorem unmarked_context_10_26584_1444035 : frontier 11 ⟨1444035, by decide⟩
    (prefixCache 10 26584) (prefixPartial 10 26584) = false := by
  decide +kernel

theorem node_context_10_26584_1444035 : EJMOriginalGlobalDAGData.nodes 11 ⟨1444035, by decide⟩ =
    .split (coordinate 10) (![⟨1443909, by decide⟩,⟨1443949, by decide⟩,⟨1443998, by decide⟩,⟨1444034, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_26584_1444035 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26584 ⟨1444035, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 26584
    ⟨1444035, by decide⟩ (by decide) (![⟨1443909, by decide⟩,⟨1443949, by decide⟩,⟨1443998, by decide⟩,⟨1444034, by decide⟩]) unmarked_context_10_26584_1444035 node_context_10_26584_1444035
  intro a
  fin_cases a
  · exact context_11_106336_1443909
  · exact context_11_106337_1443949
  · exact context_11_106338_1443998
  · exact context_11_106339_1444034

theorem selected_cut_50516 : selected 11 ⟨1444112, by decide⟩
    (prefixPartial 10 26585) = some ⟨10, 2, 0, 1444112, 26585, 3333, 1048576⟩ := by
  decide +kernel

theorem context_10_26585_1444112 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26585 ⟨1444112, by decide⟩ :=
  accepted_of_selected 10 26585 ⟨1444112, by decide⟩ ⟨10, 2, 0, 1444112, 26585, 3333, 1048576⟩
    (by decide) selected_cut_50516

theorem selected_cut_50517 : selected 11 ⟨1444124, by decide⟩
    (prefixPartial 10 26586) = some ⟨10, 2, 0, 1444124, 26586, 145, 1048576⟩ := by
  decide +kernel

theorem context_10_26586_1444124 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26586 ⟨1444124, by decide⟩ :=
  accepted_of_selected 10 26586 ⟨1444124, by decide⟩ ⟨10, 2, 0, 1444124, 26586, 145, 1048576⟩
    (by decide) selected_cut_50517

theorem selected_cut_50518 : selected 11 ⟨1444175, by decide⟩
    (prefixPartial 10 26587) = some ⟨10, 2, 0, 1444175, 26587, 2157, 1048576⟩ := by
  decide +kernel

theorem context_10_26587_1444175 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26587 ⟨1444175, by decide⟩ :=
  accepted_of_selected 10 26587 ⟨1444175, by decide⟩ ⟨10, 2, 0, 1444175, 26587, 2157, 1048576⟩
    (by decide) selected_cut_50518

theorem unmarked_context_9_6646_1444176 : frontier 12 ⟨1444176, by decide⟩
    (prefixCache 9 6646) (prefixPartial 9 6646) = false := by
  decide +kernel

theorem node_context_9_6646_1444176 : EJMOriginalGlobalDAGData.nodes 12 ⟨1444176, by decide⟩ =
    .split (coordinate 9) (![⟨1444035, by decide⟩,⟨1444112, by decide⟩,⟨1444124, by decide⟩,⟨1444175, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6646_1444176 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6646 ⟨1444176, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6646
    ⟨1444176, by decide⟩ (by decide) (![⟨1444035, by decide⟩,⟨1444112, by decide⟩,⟨1444124, by decide⟩,⟨1444175, by decide⟩]) unmarked_context_9_6646_1444176 node_context_9_6646_1444176
  intro a
  fin_cases a
  · exact context_10_26584_1444035
  · exact context_10_26585_1444112
  · exact context_10_26586_1444124
  · exact context_10_26587_1444175

theorem selected_cut_50519 : selected 12 ⟨1444273, by decide⟩
    (prefixPartial 9 6647) = some ⟨9, 2, 0, 1444273, 6647, 3225, 4194304⟩ := by
  decide +kernel

theorem context_9_6647_1444273 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6647 ⟨1444273, by decide⟩ :=
  accepted_of_selected 9 6647 ⟨1444273, by decide⟩ ⟨9, 2, 0, 1444273, 6647, 3225, 4194304⟩
    (by decide) selected_cut_50519

theorem unmarked_context_8_1661_1444274 : frontier 13 ⟨1444274, by decide⟩
    (prefixCache 8 1661) (prefixPartial 8 1661) = false := by
  decide +kernel

theorem node_context_8_1661_1444274 : EJMOriginalGlobalDAGData.nodes 13 ⟨1444274, by decide⟩ =
    .split (coordinate 8) (![⟨1443332, by decide⟩,⟨1443881, by decide⟩,⟨1444176, by decide⟩,⟨1444273, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1661_1444274 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1661 ⟨1444274, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1661
    ⟨1444274, by decide⟩ (by decide) (![⟨1443332, by decide⟩,⟨1443881, by decide⟩,⟨1444176, by decide⟩,⟨1444273, by decide⟩]) unmarked_context_8_1661_1444274 node_context_8_1661_1444274
  intro a
  fin_cases a
  · exact context_9_6644_1443332
  · exact context_9_6645_1443881
  · exact context_9_6646_1444176
  · exact context_9_6647_1444273

theorem selected_cut_50520 : selected 11 ⟨1444361, by decide⟩
    (prefixPartial 10 26592) = some ⟨10, 2, 0, 1444361, 26592, 2517, 1048576⟩ := by
  decide +kernel

theorem context_10_26592_1444361 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26592 ⟨1444361, by decide⟩ :=
  accepted_of_selected 10 26592 ⟨1444361, by decide⟩ ⟨10, 2, 0, 1444361, 26592, 2517, 1048576⟩
    (by decide) selected_cut_50520

theorem selected_cut_50521 : selected 9 ⟨1415033, by decide⟩
    (prefixPartial 12 425488) = some ⟨12, 1, 0, 1415033, 425488, 1, 65536⟩ := by
  decide +kernel

theorem context_12_425488_1415033 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 425488 ⟨1415033, by decide⟩ :=
  accepted_of_selected 12 425488 ⟨1415033, by decide⟩ ⟨12, 1, 0, 1415033, 425488, 1, 65536⟩
    (by decide) selected_cut_50521

theorem selected_cut_50522 : selected 9 ⟨1444420, by decide⟩
    (prefixPartial 12 425489) = some ⟨12, 2, 0, 1444420, 425489, 2365, 65536⟩ := by
  decide +kernel

theorem context_12_425489_1444420 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 425489 ⟨1444420, by decide⟩ :=
  accepted_of_selected 12 425489 ⟨1444420, by decide⟩ ⟨12, 2, 0, 1444420, 425489, 2365, 65536⟩
    (by decide) selected_cut_50522

theorem selected_cut_50523 : selected 9 ⟨1444475, by decide⟩
    (prefixPartial 12 425490) = some ⟨12, 2, 0, 1444475, 425490, 2369, 65536⟩ := by
  decide +kernel

theorem context_12_425490_1444475 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 425490 ⟨1444475, by decide⟩ :=
  accepted_of_selected 12 425490 ⟨1444475, by decide⟩ ⟨12, 2, 0, 1444475, 425490, 2369, 65536⟩
    (by decide) selected_cut_50523

theorem selected_cut_50524 : selected 9 ⟨1444538, by decide⟩
    (prefixPartial 12 425491) = some ⟨12, 2, 0, 1444538, 425491, 2397, 65536⟩ := by
  decide +kernel

theorem context_12_425491_1444538 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 425491 ⟨1444538, by decide⟩ :=
  accepted_of_selected 12 425491 ⟨1444538, by decide⟩ ⟨12, 2, 0, 1444538, 425491, 2397, 65536⟩
    (by decide) selected_cut_50524

theorem unmarked_context_11_106372_1444539 : frontier 10 ⟨1444539, by decide⟩
    (prefixCache 11 106372) (prefixPartial 11 106372) = false := by
  decide +kernel

theorem node_context_11_106372_1444539 : EJMOriginalGlobalDAGData.nodes 10 ⟨1444539, by decide⟩ =
    .split (coordinate 11) (![⟨1415033, by decide⟩,⟨1444420, by decide⟩,⟨1444475, by decide⟩,⟨1444538, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_106372_1444539 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106372 ⟨1444539, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 106372
    ⟨1444539, by decide⟩ (by decide) (![⟨1415033, by decide⟩,⟨1444420, by decide⟩,⟨1444475, by decide⟩,⟨1444538, by decide⟩]) unmarked_context_11_106372_1444539 node_context_11_106372_1444539
  intro a
  fin_cases a
  · exact context_12_425488_1415033
  · exact context_12_425489_1444420
  · exact context_12_425490_1444475
  · exact context_12_425491_1444538

theorem selected_cut_50525 : selected 10 ⟨1241271, by decide⟩
    (prefixPartial 11 106373) = some ⟨11, 1, 0, 1241271, 106373, 1, 262144⟩ := by
  decide +kernel

theorem context_11_106373_1241271 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106373 ⟨1241271, by decide⟩ :=
  accepted_of_selected 11 106373 ⟨1241271, by decide⟩ ⟨11, 1, 0, 1241271, 106373, 1, 262144⟩
    (by decide) selected_cut_50525

theorem selected_cut_50526 : selected 9 ⟨1415033, by decide⟩
    (prefixPartial 12 425496) = some ⟨12, 1, 0, 1415033, 425496, 1, 65536⟩ := by
  decide +kernel

theorem context_12_425496_1415033 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 425496 ⟨1415033, by decide⟩ :=
  accepted_of_selected 12 425496 ⟨1415033, by decide⟩ ⟨12, 1, 0, 1415033, 425496, 1, 65536⟩
    (by decide) selected_cut_50526

theorem selected_cut_50527 : selected 9 ⟨1444585, by decide⟩
    (prefixPartial 12 425497) = some ⟨12, 2, 0, 1444585, 425497, 2021, 65536⟩ := by
  decide +kernel

theorem context_12_425497_1444585 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 425497 ⟨1444585, by decide⟩ :=
  accepted_of_selected 12 425497 ⟨1444585, by decide⟩ ⟨12, 2, 0, 1444585, 425497, 2021, 65536⟩
    (by decide) selected_cut_50527

theorem selected_cut_50528 : selected 9 ⟨893903, by decide⟩
    (prefixPartial 12 425498) = some ⟨12, 1, 0, 893903, 425498, 1, 65536⟩ := by
  decide +kernel

theorem context_12_425498_893903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 425498 ⟨893903, by decide⟩ :=
  accepted_of_selected 12 425498 ⟨893903, by decide⟩ ⟨12, 1, 0, 893903, 425498, 1, 65536⟩
    (by decide) selected_cut_50528

theorem selected_cut_50529 : selected 9 ⟨1444635, by decide⟩
    (prefixPartial 12 425499) = some ⟨12, 2, 0, 1444635, 425499, 2077, 65536⟩ := by
  decide +kernel

theorem context_12_425499_1444635 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 425499 ⟨1444635, by decide⟩ :=
  accepted_of_selected 12 425499 ⟨1444635, by decide⟩ ⟨12, 2, 0, 1444635, 425499, 2077, 65536⟩
    (by decide) selected_cut_50529

theorem unmarked_context_11_106374_1444636 : frontier 10 ⟨1444636, by decide⟩
    (prefixCache 11 106374) (prefixPartial 11 106374) = false := by
  decide +kernel

theorem node_context_11_106374_1444636 : EJMOriginalGlobalDAGData.nodes 10 ⟨1444636, by decide⟩ =
    .split (coordinate 11) (![⟨1415033, by decide⟩,⟨1444585, by decide⟩,⟨893903, by decide⟩,⟨1444635, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_106374_1444636 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106374 ⟨1444636, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 106374
    ⟨1444636, by decide⟩ (by decide) (![⟨1415033, by decide⟩,⟨1444585, by decide⟩,⟨893903, by decide⟩,⟨1444635, by decide⟩]) unmarked_context_11_106374_1444636 node_context_11_106374_1444636
  intro a
  fin_cases a
  · exact context_12_425496_1415033
  · exact context_12_425497_1444585
  · exact context_12_425498_893903
  · exact context_12_425499_1444635

theorem selected_cut_50530 : selected 9 ⟨1415033, by decide⟩
    (prefixPartial 12 425500) = some ⟨12, 1, 0, 1415033, 425500, 1, 65536⟩ := by
  decide +kernel

theorem context_12_425500_1415033 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 425500 ⟨1415033, by decide⟩ :=
  accepted_of_selected 12 425500 ⟨1415033, by decide⟩ ⟨12, 1, 0, 1415033, 425500, 1, 65536⟩
    (by decide) selected_cut_50530

theorem selected_cut_50531 : selected 9 ⟨1444684, by decide⟩
    (prefixPartial 12 425501) = some ⟨12, 2, 0, 1444684, 425501, 2045, 65536⟩ := by
  decide +kernel

theorem context_12_425501_1444684 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 425501 ⟨1444684, by decide⟩ :=
  accepted_of_selected 12 425501 ⟨1444684, by decide⟩ ⟨12, 2, 0, 1444684, 425501, 2045, 65536⟩
    (by decide) selected_cut_50531

theorem selected_cut_50532 : selected 9 ⟨1444742, by decide⟩
    (prefixPartial 12 425502) = some ⟨12, 2, 0, 1444742, 425502, 2133, 65536⟩ := by
  decide +kernel

theorem context_12_425502_1444742 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 425502 ⟨1444742, by decide⟩ :=
  accepted_of_selected 12 425502 ⟨1444742, by decide⟩ ⟨12, 2, 0, 1444742, 425502, 2133, 65536⟩
    (by decide) selected_cut_50532

theorem selected_cut_50533 : selected 9 ⟨1444743, by decide⟩
    (prefixPartial 12 425503) = some ⟨12, 1, 0, 1444743, 425503, 1, 65536⟩ := by
  decide +kernel

theorem context_12_425503_1444743 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 425503 ⟨1444743, by decide⟩ :=
  accepted_of_selected 12 425503 ⟨1444743, by decide⟩ ⟨12, 1, 0, 1444743, 425503, 1, 65536⟩
    (by decide) selected_cut_50533

theorem unmarked_context_11_106375_1444744 : frontier 10 ⟨1444744, by decide⟩
    (prefixCache 11 106375) (prefixPartial 11 106375) = false := by
  decide +kernel

theorem node_context_11_106375_1444744 : EJMOriginalGlobalDAGData.nodes 10 ⟨1444744, by decide⟩ =
    .split (coordinate 11) (![⟨1415033, by decide⟩,⟨1444684, by decide⟩,⟨1444742, by decide⟩,⟨1444743, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_106375_1444744 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106375 ⟨1444744, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 106375
    ⟨1444744, by decide⟩ (by decide) (![⟨1415033, by decide⟩,⟨1444684, by decide⟩,⟨1444742, by decide⟩,⟨1444743, by decide⟩]) unmarked_context_11_106375_1444744 node_context_11_106375_1444744
  intro a
  fin_cases a
  · exact context_12_425500_1415033
  · exact context_12_425501_1444684
  · exact context_12_425502_1444742
  · exact context_12_425503_1444743

theorem unmarked_context_10_26593_1444745 : frontier 11 ⟨1444745, by decide⟩
    (prefixCache 10 26593) (prefixPartial 10 26593) = false := by
  decide +kernel

theorem node_context_10_26593_1444745 : EJMOriginalGlobalDAGData.nodes 11 ⟨1444745, by decide⟩ =
    .split (coordinate 10) (![⟨1444539, by decide⟩,⟨1241271, by decide⟩,⟨1444636, by decide⟩,⟨1444744, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_26593_1444745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26593 ⟨1444745, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 26593
    ⟨1444745, by decide⟩ (by decide) (![⟨1444539, by decide⟩,⟨1241271, by decide⟩,⟨1444636, by decide⟩,⟨1444744, by decide⟩]) unmarked_context_10_26593_1444745 node_context_10_26593_1444745
  intro a
  fin_cases a
  · exact context_11_106372_1444539
  · exact context_11_106373_1241271
  · exact context_11_106374_1444636
  · exact context_11_106375_1444744

theorem selected_cut_50534 : selected 9 ⟨435160, by decide⟩
    (prefixPartial 12 425504) = some ⟨12, 1, 0, 435160, 425504, 1, 65536⟩ := by
  decide +kernel

theorem context_12_425504_435160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 425504 ⟨435160, by decide⟩ :=
  accepted_of_selected 12 425504 ⟨435160, by decide⟩ ⟨12, 1, 0, 435160, 425504, 1, 65536⟩
    (by decide) selected_cut_50534

theorem selected_cut_50535 : selected 9 ⟨1444793, by decide⟩
    (prefixPartial 12 425505) = some ⟨12, 2, 0, 1444793, 425505, 2253, 65536⟩ := by
  decide +kernel

theorem context_12_425505_1444793 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 425505 ⟨1444793, by decide⟩ :=
  accepted_of_selected 12 425505 ⟨1444793, by decide⟩ ⟨12, 2, 0, 1444793, 425505, 2253, 65536⟩
    (by decide) selected_cut_50535

theorem selected_cut_50536 : selected 9 ⟨1444848, by decide⟩
    (prefixPartial 12 425506) = some ⟨12, 2, 0, 1444848, 425506, 2289, 65536⟩ := by
  decide +kernel

theorem context_12_425506_1444848 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 425506 ⟨1444848, by decide⟩ :=
  accepted_of_selected 12 425506 ⟨1444848, by decide⟩ ⟨12, 2, 0, 1444848, 425506, 2289, 65536⟩
    (by decide) selected_cut_50536

theorem selected_cut_50537 : selected 9 ⟨1444896, by decide⟩
    (prefixPartial 12 425507) = some ⟨12, 2, 0, 1444896, 425507, 2017, 65536⟩ := by
  decide +kernel

theorem context_12_425507_1444896 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 425507 ⟨1444896, by decide⟩ :=
  accepted_of_selected 12 425507 ⟨1444896, by decide⟩ ⟨12, 2, 0, 1444896, 425507, 2017, 65536⟩
    (by decide) selected_cut_50537

theorem unmarked_context_11_106376_1444897 : frontier 10 ⟨1444897, by decide⟩
    (prefixCache 11 106376) (prefixPartial 11 106376) = false := by
  decide +kernel

theorem node_context_11_106376_1444897 : EJMOriginalGlobalDAGData.nodes 10 ⟨1444897, by decide⟩ =
    .split (coordinate 11) (![⟨435160, by decide⟩,⟨1444793, by decide⟩,⟨1444848, by decide⟩,⟨1444896, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_106376_1444897 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106376 ⟨1444897, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 106376
    ⟨1444897, by decide⟩ (by decide) (![⟨435160, by decide⟩,⟨1444793, by decide⟩,⟨1444848, by decide⟩,⟨1444896, by decide⟩]) unmarked_context_11_106376_1444897 node_context_11_106376_1444897
  intro a
  fin_cases a
  · exact context_12_425504_435160
  · exact context_12_425505_1444793
  · exact context_12_425506_1444848
  · exact context_12_425507_1444896

theorem selected_cut_50538 : selected 10 ⟨1444983, by decide⟩
    (prefixPartial 11 106377) = some ⟨11, 2, 0, 1444983, 106377, 3545, 262144⟩ := by
  decide +kernel

theorem context_11_106377_1444983 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106377 ⟨1444983, by decide⟩ :=
  accepted_of_selected 11 106377 ⟨1444983, by decide⟩ ⟨11, 2, 0, 1444983, 106377, 3545, 262144⟩
    (by decide) selected_cut_50538

theorem selected_cut_50539 : selected 10 ⟨1444985, by decide⟩
    (prefixPartial 11 106378) = some ⟨11, 2, 0, 1444985, 106378, 5, 262144⟩ := by
  decide +kernel

theorem context_11_106378_1444985 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106378 ⟨1444985, by decide⟩ :=
  accepted_of_selected 11 106378 ⟨1444985, by decide⟩ ⟨11, 2, 0, 1444985, 106378, 5, 262144⟩
    (by decide) selected_cut_50539

theorem selected_cut_50540 : selected 10 ⟨1445072, by decide⟩
    (prefixPartial 11 106379) = some ⟨11, 2, 0, 1445072, 106379, 3641, 262144⟩ := by
  decide +kernel

theorem context_11_106379_1445072 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106379 ⟨1445072, by decide⟩ :=
  accepted_of_selected 11 106379 ⟨1445072, by decide⟩ ⟨11, 2, 0, 1445072, 106379, 3641, 262144⟩
    (by decide) selected_cut_50540

theorem unmarked_context_10_26594_1445073 : frontier 11 ⟨1445073, by decide⟩
    (prefixCache 10 26594) (prefixPartial 10 26594) = false := by
  decide +kernel

theorem node_context_10_26594_1445073 : EJMOriginalGlobalDAGData.nodes 11 ⟨1445073, by decide⟩ =
    .split (coordinate 10) (![⟨1444897, by decide⟩,⟨1444983, by decide⟩,⟨1444985, by decide⟩,⟨1445072, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_26594_1445073 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26594 ⟨1445073, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 26594
    ⟨1445073, by decide⟩ (by decide) (![⟨1444897, by decide⟩,⟨1444983, by decide⟩,⟨1444985, by decide⟩,⟨1445072, by decide⟩]) unmarked_context_10_26594_1445073 node_context_10_26594_1445073
  intro a
  fin_cases a
  · exact context_11_106376_1444897
  · exact context_11_106377_1444983
  · exact context_11_106378_1444985
  · exact context_11_106379_1445072

theorem selected_cut_50541 : selected 9 ⟨1416143, by decide⟩
    (prefixPartial 12 425520) = some ⟨12, 1, 0, 1416143, 425520, 1, 65536⟩ := by
  decide +kernel

theorem context_12_425520_1416143 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 425520 ⟨1416143, by decide⟩ :=
  accepted_of_selected 12 425520 ⟨1416143, by decide⟩ ⟨12, 1, 0, 1416143, 425520, 1, 65536⟩
    (by decide) selected_cut_50541

theorem selected_cut_50542 : selected 9 ⟨1445107, by decide⟩
    (prefixPartial 12 425521) = some ⟨12, 2, 0, 1445107, 425521, 1493, 65536⟩ := by
  decide +kernel

theorem context_12_425521_1445107 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 425521 ⟨1445107, by decide⟩ :=
  accepted_of_selected 12 425521 ⟨1445107, by decide⟩ ⟨12, 2, 0, 1445107, 425521, 1493, 65536⟩
    (by decide) selected_cut_50542

theorem selected_cut_50543 : selected 9 ⟨1445138, by decide⟩
    (prefixPartial 12 425522) = some ⟨12, 2, 0, 1445138, 425522, 1417, 65536⟩ := by
  decide +kernel

theorem context_12_425522_1445138 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 425522 ⟨1445138, by decide⟩ :=
  accepted_of_selected 12 425522 ⟨1445138, by decide⟩ ⟨12, 2, 0, 1445138, 425522, 1417, 65536⟩
    (by decide) selected_cut_50543

theorem selected_cut_50544 : selected 9 ⟨1445170, by decide⟩
    (prefixPartial 12 425523) = some ⟨12, 2, 0, 1445170, 425523, 1429, 65536⟩ := by
  decide +kernel

theorem context_12_425523_1445170 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 425523 ⟨1445170, by decide⟩ :=
  accepted_of_selected 12 425523 ⟨1445170, by decide⟩ ⟨12, 2, 0, 1445170, 425523, 1429, 65536⟩
    (by decide) selected_cut_50544

theorem unmarked_context_11_106380_1445171 : frontier 10 ⟨1445171, by decide⟩
    (prefixCache 11 106380) (prefixPartial 11 106380) = false := by
  decide +kernel

theorem node_context_11_106380_1445171 : EJMOriginalGlobalDAGData.nodes 10 ⟨1445171, by decide⟩ =
    .split (coordinate 11) (![⟨1416143, by decide⟩,⟨1445107, by decide⟩,⟨1445138, by decide⟩,⟨1445170, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_106380_1445171 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106380 ⟨1445171, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 106380
    ⟨1445171, by decide⟩ (by decide) (![⟨1416143, by decide⟩,⟨1445107, by decide⟩,⟨1445138, by decide⟩,⟨1445170, by decide⟩]) unmarked_context_11_106380_1445171 node_context_11_106380_1445171
  intro a
  fin_cases a
  · exact context_12_425520_1416143
  · exact context_12_425521_1445107
  · exact context_12_425522_1445138
  · exact context_12_425523_1445170

theorem selected_cut_50545 : selected 10 ⟨1445230, by decide⟩
    (prefixPartial 11 106381) = some ⟨11, 2, 0, 1445230, 106381, 2493, 262144⟩ := by
  decide +kernel

theorem context_11_106381_1445230 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106381 ⟨1445230, by decide⟩ :=
  accepted_of_selected 11 106381 ⟨1445230, by decide⟩ ⟨11, 2, 0, 1445230, 106381, 2493, 262144⟩
    (by decide) selected_cut_50545

theorem selected_cut_50546 : selected 10 ⟨1445304, by decide⟩
    (prefixPartial 11 106382) = some ⟨11, 2, 0, 1445304, 106382, 3081, 262144⟩ := by
  decide +kernel

theorem context_11_106382_1445304 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106382 ⟨1445304, by decide⟩ :=
  accepted_of_selected 11 106382 ⟨1445304, by decide⟩ ⟨11, 2, 0, 1445304, 106382, 3081, 262144⟩
    (by decide) selected_cut_50546

theorem selected_cut_50547 : selected 10 ⟨977886, by decide⟩
    (prefixPartial 11 106383) = some ⟨11, 1, 0, 977886, 106383, 1, 262144⟩ := by
  decide +kernel

theorem context_11_106383_977886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106383 ⟨977886, by decide⟩ :=
  accepted_of_selected 11 106383 ⟨977886, by decide⟩ ⟨11, 1, 0, 977886, 106383, 1, 262144⟩
    (by decide) selected_cut_50547

theorem unmarked_context_10_26595_1445305 : frontier 11 ⟨1445305, by decide⟩
    (prefixCache 10 26595) (prefixPartial 10 26595) = false := by
  decide +kernel

theorem node_context_10_26595_1445305 : EJMOriginalGlobalDAGData.nodes 11 ⟨1445305, by decide⟩ =
    .split (coordinate 10) (![⟨1445171, by decide⟩,⟨1445230, by decide⟩,⟨1445304, by decide⟩,⟨977886, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_26595_1445305 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26595 ⟨1445305, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 26595
    ⟨1445305, by decide⟩ (by decide) (![⟨1445171, by decide⟩,⟨1445230, by decide⟩,⟨1445304, by decide⟩,⟨977886, by decide⟩]) unmarked_context_10_26595_1445305 node_context_10_26595_1445305
  intro a
  fin_cases a
  · exact context_11_106380_1445171
  · exact context_11_106381_1445230
  · exact context_11_106382_1445304
  · exact context_11_106383_977886

theorem unmarked_context_9_6648_1445306 : frontier 12 ⟨1445306, by decide⟩
    (prefixCache 9 6648) (prefixPartial 9 6648) = false := by
  decide +kernel

theorem node_context_9_6648_1445306 : EJMOriginalGlobalDAGData.nodes 12 ⟨1445306, by decide⟩ =
    .split (coordinate 9) (![⟨1444361, by decide⟩,⟨1444745, by decide⟩,⟨1445073, by decide⟩,⟨1445305, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6648_1445306 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6648 ⟨1445306, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6648
    ⟨1445306, by decide⟩ (by decide) (![⟨1444361, by decide⟩,⟨1444745, by decide⟩,⟨1445073, by decide⟩,⟨1445305, by decide⟩]) unmarked_context_9_6648_1445306 node_context_9_6648_1445306
  intro a
  fin_cases a
  · exact context_10_26592_1444361
  · exact context_10_26593_1444745
  · exact context_10_26594_1445073
  · exact context_10_26595_1445305

theorem selected_cut_50548 : selected 10 ⟨1445340, by decide⟩
    (prefixPartial 11 106384) = some ⟨11, 2, 0, 1445340, 106384, 1349, 262144⟩ := by
  decide +kernel

theorem context_11_106384_1445340 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106384 ⟨1445340, by decide⟩ :=
  accepted_of_selected 11 106384 ⟨1445340, by decide⟩ ⟨11, 2, 0, 1445340, 106384, 1349, 262144⟩
    (by decide) selected_cut_50548

theorem selected_cut_50549 : selected 10 ⟨1445431, by decide⟩
    (prefixPartial 11 106385) = some ⟨11, 2, 0, 1445431, 106385, 3837, 262144⟩ := by
  decide +kernel

theorem context_11_106385_1445431 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106385 ⟨1445431, by decide⟩ :=
  accepted_of_selected 11 106385 ⟨1445431, by decide⟩ ⟨11, 2, 0, 1445431, 106385, 3837, 262144⟩
    (by decide) selected_cut_50549

theorem selected_cut_50550 : selected 10 ⟨1445489, by decide⟩
    (prefixPartial 11 106386) = some ⟨11, 2, 0, 1445489, 106386, 2373, 262144⟩ := by
  decide +kernel

theorem context_11_106386_1445489 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106386 ⟨1445489, by decide⟩ :=
  accepted_of_selected 11 106386 ⟨1445489, by decide⟩ ⟨11, 2, 0, 1445489, 106386, 2373, 262144⟩
    (by decide) selected_cut_50550

theorem selected_cut_50551 : selected 10 ⟨1445539, by decide⟩
    (prefixPartial 11 106387) = some ⟨11, 2, 0, 1445539, 106387, 2413, 262144⟩ := by
  decide +kernel

theorem context_11_106387_1445539 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106387 ⟨1445539, by decide⟩ :=
  accepted_of_selected 11 106387 ⟨1445539, by decide⟩ ⟨11, 2, 0, 1445539, 106387, 2413, 262144⟩
    (by decide) selected_cut_50551

theorem unmarked_context_10_26596_1445540 : frontier 11 ⟨1445540, by decide⟩
    (prefixCache 10 26596) (prefixPartial 10 26596) = false := by
  decide +kernel

theorem node_context_10_26596_1445540 : EJMOriginalGlobalDAGData.nodes 11 ⟨1445540, by decide⟩ =
    .split (coordinate 10) (![⟨1445340, by decide⟩,⟨1445431, by decide⟩,⟨1445489, by decide⟩,⟨1445539, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_26596_1445540 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26596 ⟨1445540, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 26596
    ⟨1445540, by decide⟩ (by decide) (![⟨1445340, by decide⟩,⟨1445431, by decide⟩,⟨1445489, by decide⟩,⟨1445539, by decide⟩]) unmarked_context_10_26596_1445540 node_context_10_26596_1445540
  intro a
  fin_cases a
  · exact context_11_106384_1445340
  · exact context_11_106385_1445431
  · exact context_11_106386_1445489
  · exact context_11_106387_1445539

theorem selected_cut_50552 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 26597) = some ⟨10, 1, 0, 893098, 26597, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_26597_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26597 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 26597 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 26597, 1, 1048576⟩
    (by decide) selected_cut_50552

theorem selected_cut_50553 : selected 10 ⟨1445586, by decide⟩
    (prefixPartial 11 106392) = some ⟨11, 2, 0, 1445586, 106392, 2165, 262144⟩ := by
  decide +kernel

theorem context_11_106392_1445586 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106392 ⟨1445586, by decide⟩ :=
  accepted_of_selected 11 106392 ⟨1445586, by decide⟩ ⟨11, 2, 0, 1445586, 106392, 2165, 262144⟩
    (by decide) selected_cut_50553

theorem selected_cut_50554 : selected 10 ⟨1445655, by decide⟩
    (prefixPartial 11 106393) = some ⟨11, 2, 0, 1445655, 106393, 3005, 262144⟩ := by
  decide +kernel

theorem context_11_106393_1445655 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106393 ⟨1445655, by decide⟩ :=
  accepted_of_selected 11 106393 ⟨1445655, by decide⟩ ⟨11, 2, 0, 1445655, 106393, 3005, 262144⟩
    (by decide) selected_cut_50554

theorem selected_cut_50555 : selected 10 ⟨1445656, by decide⟩
    (prefixPartial 11 106394) = some ⟨11, 2, 0, 1445656, 106394, 5, 262144⟩ := by
  decide +kernel

theorem context_11_106394_1445656 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106394 ⟨1445656, by decide⟩ :=
  accepted_of_selected 11 106394 ⟨1445656, by decide⟩ ⟨11, 2, 0, 1445656, 106394, 5, 262144⟩
    (by decide) selected_cut_50555

theorem selected_cut_50556 : selected 10 ⟨1445694, by decide⟩
    (prefixPartial 11 106395) = some ⟨11, 2, 0, 1445694, 106395, 1749, 262144⟩ := by
  decide +kernel

theorem context_11_106395_1445694 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106395 ⟨1445694, by decide⟩ :=
  accepted_of_selected 11 106395 ⟨1445694, by decide⟩ ⟨11, 2, 0, 1445694, 106395, 1749, 262144⟩
    (by decide) selected_cut_50556

theorem unmarked_context_10_26598_1445695 : frontier 11 ⟨1445695, by decide⟩
    (prefixCache 10 26598) (prefixPartial 10 26598) = false := by
  decide +kernel

theorem node_context_10_26598_1445695 : EJMOriginalGlobalDAGData.nodes 11 ⟨1445695, by decide⟩ =
    .split (coordinate 10) (![⟨1445586, by decide⟩,⟨1445655, by decide⟩,⟨1445656, by decide⟩,⟨1445694, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_26598_1445695 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26598 ⟨1445695, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 26598
    ⟨1445695, by decide⟩ (by decide) (![⟨1445586, by decide⟩,⟨1445655, by decide⟩,⟨1445656, by decide⟩,⟨1445694, by decide⟩]) unmarked_context_10_26598_1445695 node_context_10_26598_1445695
  intro a
  fin_cases a
  · exact context_11_106392_1445586
  · exact context_11_106393_1445655
  · exact context_11_106394_1445656
  · exact context_11_106395_1445694

theorem selected_cut_50557 : selected 10 ⟨1445736, by decide⟩
    (prefixPartial 11 106396) = some ⟨11, 2, 0, 1445736, 106396, 2149, 262144⟩ := by
  decide +kernel

theorem context_11_106396_1445736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106396 ⟨1445736, by decide⟩ :=
  accepted_of_selected 11 106396 ⟨1445736, by decide⟩ ⟨11, 2, 0, 1445736, 106396, 2149, 262144⟩
    (by decide) selected_cut_50557

theorem selected_cut_50558 : selected 10 ⟨1445776, by decide⟩
    (prefixPartial 11 106397) = some ⟨11, 2, 0, 1445776, 106397, 1917, 262144⟩ := by
  decide +kernel

theorem context_11_106397_1445776 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106397 ⟨1445776, by decide⟩ :=
  accepted_of_selected 11 106397 ⟨1445776, by decide⟩ ⟨11, 2, 0, 1445776, 106397, 1917, 262144⟩
    (by decide) selected_cut_50558

theorem selected_cut_50559 : selected 10 ⟨1445801, by decide⟩
    (prefixPartial 11 106398) = some ⟨11, 2, 0, 1445801, 106398, 1077, 262144⟩ := by
  decide +kernel

theorem context_11_106398_1445801 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106398 ⟨1445801, by decide⟩ :=
  accepted_of_selected 11 106398 ⟨1445801, by decide⟩ ⟨11, 2, 0, 1445801, 106398, 1077, 262144⟩
    (by decide) selected_cut_50559

theorem selected_cut_50560 : selected 10 ⟨977886, by decide⟩
    (prefixPartial 11 106399) = some ⟨11, 1, 0, 977886, 106399, 1, 262144⟩ := by
  decide +kernel

theorem context_11_106399_977886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106399 ⟨977886, by decide⟩ :=
  accepted_of_selected 11 106399 ⟨977886, by decide⟩ ⟨11, 1, 0, 977886, 106399, 1, 262144⟩
    (by decide) selected_cut_50560

theorem unmarked_context_10_26599_1445802 : frontier 11 ⟨1445802, by decide⟩
    (prefixCache 10 26599) (prefixPartial 10 26599) = false := by
  decide +kernel

theorem node_context_10_26599_1445802 : EJMOriginalGlobalDAGData.nodes 11 ⟨1445802, by decide⟩ =
    .split (coordinate 10) (![⟨1445736, by decide⟩,⟨1445776, by decide⟩,⟨1445801, by decide⟩,⟨977886, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_26599_1445802 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26599 ⟨1445802, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 26599
    ⟨1445802, by decide⟩ (by decide) (![⟨1445736, by decide⟩,⟨1445776, by decide⟩,⟨1445801, by decide⟩,⟨977886, by decide⟩]) unmarked_context_10_26599_1445802 node_context_10_26599_1445802
  intro a
  fin_cases a
  · exact context_11_106396_1445736
  · exact context_11_106397_1445776
  · exact context_11_106398_1445801
  · exact context_11_106399_977886

theorem unmarked_context_9_6649_1445803 : frontier 12 ⟨1445803, by decide⟩
    (prefixCache 9 6649) (prefixPartial 9 6649) = false := by
  decide +kernel

theorem node_context_9_6649_1445803 : EJMOriginalGlobalDAGData.nodes 12 ⟨1445803, by decide⟩ =
    .split (coordinate 9) (![⟨1445540, by decide⟩,⟨893098, by decide⟩,⟨1445695, by decide⟩,⟨1445802, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6649_1445803 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6649 ⟨1445803, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6649
    ⟨1445803, by decide⟩ (by decide) (![⟨1445540, by decide⟩,⟨893098, by decide⟩,⟨1445695, by decide⟩,⟨1445802, by decide⟩]) unmarked_context_9_6649_1445803 node_context_9_6649_1445803
  intro a
  fin_cases a
  · exact context_10_26596_1445540
  · exact context_10_26597_893098
  · exact context_10_26598_1445695
  · exact context_10_26599_1445802

theorem selected_cut_50561 : selected 10 ⟨1445831, by decide⟩
    (prefixPartial 11 106400) = some ⟨11, 2, 0, 1445831, 106400, 897, 262144⟩ := by
  decide +kernel

theorem context_11_106400_1445831 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106400 ⟨1445831, by decide⟩ :=
  accepted_of_selected 11 106400 ⟨1445831, by decide⟩ ⟨11, 2, 0, 1445831, 106400, 897, 262144⟩
    (by decide) selected_cut_50561

theorem selected_cut_50562 : selected 10 ⟨1445879, by decide⟩
    (prefixPartial 11 106401) = some ⟨11, 2, 0, 1445879, 106401, 1717, 262144⟩ := by
  decide +kernel

theorem context_11_106401_1445879 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106401 ⟨1445879, by decide⟩ :=
  accepted_of_selected 11 106401 ⟨1445879, by decide⟩ ⟨11, 2, 0, 1445879, 106401, 1717, 262144⟩
    (by decide) selected_cut_50562

theorem selected_cut_50563 : selected 10 ⟨1445932, by decide⟩
    (prefixPartial 11 106402) = some ⟨11, 2, 0, 1445932, 106402, 2217, 262144⟩ := by
  decide +kernel

theorem context_11_106402_1445932 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106402 ⟨1445932, by decide⟩ :=
  accepted_of_selected 11 106402 ⟨1445932, by decide⟩ ⟨11, 2, 0, 1445932, 106402, 2217, 262144⟩
    (by decide) selected_cut_50563

theorem selected_cut_50564 : selected 10 ⟨1445965, by decide⟩
    (prefixPartial 11 106403) = some ⟨11, 2, 0, 1445965, 106403, 1341, 262144⟩ := by
  decide +kernel

theorem context_11_106403_1445965 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106403 ⟨1445965, by decide⟩ :=
  accepted_of_selected 11 106403 ⟨1445965, by decide⟩ ⟨11, 2, 0, 1445965, 106403, 1341, 262144⟩
    (by decide) selected_cut_50564

theorem unmarked_context_10_26600_1445966 : frontier 11 ⟨1445966, by decide⟩
    (prefixCache 10 26600) (prefixPartial 10 26600) = false := by
  decide +kernel

theorem node_context_10_26600_1445966 : EJMOriginalGlobalDAGData.nodes 11 ⟨1445966, by decide⟩ =
    .split (coordinate 10) (![⟨1445831, by decide⟩,⟨1445879, by decide⟩,⟨1445932, by decide⟩,⟨1445965, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_26600_1445966 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26600 ⟨1445966, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 26600
    ⟨1445966, by decide⟩ (by decide) (![⟨1445831, by decide⟩,⟨1445879, by decide⟩,⟨1445932, by decide⟩,⟨1445965, by decide⟩]) unmarked_context_10_26600_1445966 node_context_10_26600_1445966
  intro a
  fin_cases a
  · exact context_11_106400_1445831
  · exact context_11_106401_1445879
  · exact context_11_106402_1445932
  · exact context_11_106403_1445965

theorem selected_cut_50565 : selected 11 ⟨1446074, by decide⟩
    (prefixPartial 10 26601) = some ⟨10, 2, 0, 1446074, 26601, 4021, 1048576⟩ := by
  decide +kernel

theorem context_10_26601_1446074 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26601 ⟨1446074, by decide⟩ :=
  accepted_of_selected 10 26601 ⟨1446074, by decide⟩ ⟨10, 2, 0, 1446074, 26601, 4021, 1048576⟩
    (by decide) selected_cut_50565

theorem selected_cut_50566 : selected 11 ⟨1446075, by decide⟩
    (prefixPartial 10 26602) = some ⟨10, 2, 0, 1446075, 26602, 13, 1048576⟩ := by
  decide +kernel

theorem context_10_26602_1446075 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26602 ⟨1446075, by decide⟩ :=
  accepted_of_selected 10 26602 ⟨1446075, by decide⟩ ⟨10, 2, 0, 1446075, 26602, 13, 1048576⟩
    (by decide) selected_cut_50566

theorem selected_cut_50567 : selected 11 ⟨1446127, by decide⟩
    (prefixPartial 10 26603) = some ⟨10, 2, 0, 1446127, 26603, 2377, 1048576⟩ := by
  decide +kernel

theorem context_10_26603_1446127 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26603 ⟨1446127, by decide⟩ :=
  accepted_of_selected 10 26603 ⟨1446127, by decide⟩ ⟨10, 2, 0, 1446127, 26603, 2377, 1048576⟩
    (by decide) selected_cut_50567

theorem unmarked_context_9_6650_1446128 : frontier 12 ⟨1446128, by decide⟩
    (prefixCache 9 6650) (prefixPartial 9 6650) = false := by
  decide +kernel

theorem node_context_9_6650_1446128 : EJMOriginalGlobalDAGData.nodes 12 ⟨1446128, by decide⟩ =
    .split (coordinate 9) (![⟨1445966, by decide⟩,⟨1446074, by decide⟩,⟨1446075, by decide⟩,⟨1446127, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6650_1446128 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6650 ⟨1446128, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6650
    ⟨1446128, by decide⟩ (by decide) (![⟨1445966, by decide⟩,⟨1446074, by decide⟩,⟨1446075, by decide⟩,⟨1446127, by decide⟩]) unmarked_context_9_6650_1446128 node_context_9_6650_1446128
  intro a
  fin_cases a
  · exact context_10_26600_1445966
  · exact context_10_26601_1446074
  · exact context_10_26602_1446075
  · exact context_10_26603_1446127

theorem selected_cut_50568 : selected 12 ⟨1446219, by decide⟩
    (prefixPartial 9 6651) = some ⟨9, 2, 0, 1446219, 6651, 3425, 4194304⟩ := by
  decide +kernel

theorem context_9_6651_1446219 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6651 ⟨1446219, by decide⟩ :=
  accepted_of_selected 9 6651 ⟨1446219, by decide⟩ ⟨9, 2, 0, 1446219, 6651, 3425, 4194304⟩
    (by decide) selected_cut_50568

theorem unmarked_context_8_1662_1446220 : frontier 13 ⟨1446220, by decide⟩
    (prefixCache 8 1662) (prefixPartial 8 1662) = false := by
  decide +kernel

theorem node_context_8_1662_1446220 : EJMOriginalGlobalDAGData.nodes 13 ⟨1446220, by decide⟩ =
    .split (coordinate 8) (![⟨1445306, by decide⟩,⟨1445803, by decide⟩,⟨1446128, by decide⟩,⟨1446219, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1662_1446220 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1662 ⟨1446220, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1662
    ⟨1446220, by decide⟩ (by decide) (![⟨1445306, by decide⟩,⟨1445803, by decide⟩,⟨1446128, by decide⟩,⟨1446219, by decide⟩]) unmarked_context_8_1662_1446220 node_context_8_1662_1446220
  intro a
  fin_cases a
  · exact context_9_6648_1445306
  · exact context_9_6649_1445803
  · exact context_9_6650_1446128
  · exact context_9_6651_1446219

theorem selected_cut_50569 : selected 11 ⟨1446307, by decide⟩
    (prefixPartial 10 26608) = some ⟨10, 2, 0, 1446307, 26608, 2513, 1048576⟩ := by
  decide +kernel

theorem context_10_26608_1446307 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26608 ⟨1446307, by decide⟩ :=
  accepted_of_selected 10 26608 ⟨1446307, by decide⟩ ⟨10, 2, 0, 1446307, 26608, 2513, 1048576⟩
    (by decide) selected_cut_50569

theorem selected_cut_50570 : selected 9 ⟨1415033, by decide⟩
    (prefixPartial 12 425744) = some ⟨12, 1, 0, 1415033, 425744, 1, 65536⟩ := by
  decide +kernel

theorem context_12_425744_1415033 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 425744 ⟨1415033, by decide⟩ :=
  accepted_of_selected 12 425744 ⟨1415033, by decide⟩ ⟨12, 1, 0, 1415033, 425744, 1, 65536⟩
    (by decide) selected_cut_50570

theorem selected_cut_50571 : selected 9 ⟨1446368, by decide⟩
    (prefixPartial 12 425745) = some ⟨12, 2, 0, 1446368, 425745, 2381, 65536⟩ := by
  decide +kernel

theorem context_12_425745_1446368 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 425745 ⟨1446368, by decide⟩ :=
  accepted_of_selected 12 425745 ⟨1446368, by decide⟩ ⟨12, 2, 0, 1446368, 425745, 2381, 65536⟩
    (by decide) selected_cut_50571

theorem selected_cut_50572 : selected 9 ⟨1446425, by decide⟩
    (prefixPartial 12 425746) = some ⟨12, 2, 0, 1446425, 425746, 2705, 65536⟩ := by
  decide +kernel

theorem context_12_425746_1446425 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 425746 ⟨1446425, by decide⟩ :=
  accepted_of_selected 12 425746 ⟨1446425, by decide⟩ ⟨12, 2, 0, 1446425, 425746, 2705, 65536⟩
    (by decide) selected_cut_50572

theorem selected_cut_50573 : selected 9 ⟨1446477, by decide⟩
    (prefixPartial 12 425747) = some ⟨12, 2, 0, 1446477, 425747, 2469, 65536⟩ := by
  decide +kernel

theorem context_12_425747_1446477 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 425747 ⟨1446477, by decide⟩ :=
  accepted_of_selected 12 425747 ⟨1446477, by decide⟩ ⟨12, 2, 0, 1446477, 425747, 2469, 65536⟩
    (by decide) selected_cut_50573

theorem unmarked_context_11_106436_1446478 : frontier 10 ⟨1446478, by decide⟩
    (prefixCache 11 106436) (prefixPartial 11 106436) = false := by
  decide +kernel

theorem node_context_11_106436_1446478 : EJMOriginalGlobalDAGData.nodes 10 ⟨1446478, by decide⟩ =
    .split (coordinate 11) (![⟨1415033, by decide⟩,⟨1446368, by decide⟩,⟨1446425, by decide⟩,⟨1446477, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_106436_1446478 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106436 ⟨1446478, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 106436
    ⟨1446478, by decide⟩ (by decide) (![⟨1415033, by decide⟩,⟨1446368, by decide⟩,⟨1446425, by decide⟩,⟨1446477, by decide⟩]) unmarked_context_11_106436_1446478 node_context_11_106436_1446478
  intro a
  fin_cases a
  · exact context_12_425744_1415033
  · exact context_12_425745_1446368
  · exact context_12_425746_1446425
  · exact context_12_425747_1446477

theorem selected_cut_50574 : selected 10 ⟨1241271, by decide⟩
    (prefixPartial 11 106437) = some ⟨11, 1, 0, 1241271, 106437, 1, 262144⟩ := by
  decide +kernel

theorem context_11_106437_1241271 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106437 ⟨1241271, by decide⟩ :=
  accepted_of_selected 11 106437 ⟨1241271, by decide⟩ ⟨11, 1, 0, 1241271, 106437, 1, 262144⟩
    (by decide) selected_cut_50574

theorem selected_cut_50575 : selected 9 ⟨1415033, by decide⟩
    (prefixPartial 12 425752) = some ⟨12, 1, 0, 1415033, 425752, 1, 65536⟩ := by
  decide +kernel

theorem context_12_425752_1415033 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 425752 ⟨1415033, by decide⟩ :=
  accepted_of_selected 12 425752 ⟨1415033, by decide⟩ ⟨12, 1, 0, 1415033, 425752, 1, 65536⟩
    (by decide) selected_cut_50575

theorem selected_cut_50576 : selected 9 ⟨1446531, by decide⟩
    (prefixPartial 12 425753) = some ⟨12, 2, 0, 1446531, 425753, 2241, 65536⟩ := by
  decide +kernel

theorem context_12_425753_1446531 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 425753 ⟨1446531, by decide⟩ :=
  accepted_of_selected 12 425753 ⟨1446531, by decide⟩ ⟨12, 2, 0, 1446531, 425753, 2241, 65536⟩
    (by decide) selected_cut_50576

theorem selected_cut_50577 : selected 9 ⟨419292, by decide⟩
    (prefixPartial 12 425754) = some ⟨12, 1, 0, 419292, 425754, 1, 65536⟩ := by
  decide +kernel

theorem context_12_425754_419292 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 425754 ⟨419292, by decide⟩ :=
  accepted_of_selected 12 425754 ⟨419292, by decide⟩ ⟨12, 1, 0, 419292, 425754, 1, 65536⟩
    (by decide) selected_cut_50577

theorem selected_cut_50578 : selected 9 ⟨1446596, by decide⟩
    (prefixPartial 12 425755) = some ⟨12, 2, 0, 1446596, 425755, 2237, 65536⟩ := by
  decide +kernel

theorem context_12_425755_1446596 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 425755 ⟨1446596, by decide⟩ :=
  accepted_of_selected 12 425755 ⟨1446596, by decide⟩ ⟨12, 2, 0, 1446596, 425755, 2237, 65536⟩
    (by decide) selected_cut_50578

theorem unmarked_context_11_106438_1446597 : frontier 10 ⟨1446597, by decide⟩
    (prefixCache 11 106438) (prefixPartial 11 106438) = false := by
  decide +kernel

theorem node_context_11_106438_1446597 : EJMOriginalGlobalDAGData.nodes 10 ⟨1446597, by decide⟩ =
    .split (coordinate 11) (![⟨1415033, by decide⟩,⟨1446531, by decide⟩,⟨419292, by decide⟩,⟨1446596, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_106438_1446597 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106438 ⟨1446597, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 106438
    ⟨1446597, by decide⟩ (by decide) (![⟨1415033, by decide⟩,⟨1446531, by decide⟩,⟨419292, by decide⟩,⟨1446596, by decide⟩]) unmarked_context_11_106438_1446597 node_context_11_106438_1446597
  intro a
  fin_cases a
  · exact context_12_425752_1415033
  · exact context_12_425753_1446531
  · exact context_12_425754_419292
  · exact context_12_425755_1446596

theorem selected_cut_50579 : selected 9 ⟨1415033, by decide⟩
    (prefixPartial 12 425756) = some ⟨12, 1, 0, 1415033, 425756, 1, 65536⟩ := by
  decide +kernel

theorem context_12_425756_1415033 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 425756 ⟨1415033, by decide⟩ :=
  accepted_of_selected 12 425756 ⟨1415033, by decide⟩ ⟨12, 1, 0, 1415033, 425756, 1, 65536⟩
    (by decide) selected_cut_50579

theorem selected_cut_50580 : selected 9 ⟨1446647, by decide⟩
    (prefixPartial 12 425757) = some ⟨12, 2, 0, 1446647, 425757, 2045, 65536⟩ := by
  decide +kernel

theorem context_12_425757_1446647 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 425757 ⟨1446647, by decide⟩ :=
  accepted_of_selected 12 425757 ⟨1446647, by decide⟩ ⟨12, 2, 0, 1446647, 425757, 2045, 65536⟩
    (by decide) selected_cut_50580

theorem selected_cut_50581 : selected 9 ⟨1446709, by decide⟩
    (prefixPartial 12 425758) = some ⟨12, 2, 0, 1446709, 425758, 2353, 65536⟩ := by
  decide +kernel

theorem context_12_425758_1446709 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 425758 ⟨1446709, by decide⟩ :=
  accepted_of_selected 12 425758 ⟨1446709, by decide⟩ ⟨12, 2, 0, 1446709, 425758, 2353, 65536⟩
    (by decide) selected_cut_50581

theorem selected_cut_50582 : selected 9 ⟨903806, by decide⟩
    (prefixPartial 12 425759) = some ⟨12, 1, 0, 903806, 425759, 1, 65536⟩ := by
  decide +kernel

theorem context_12_425759_903806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 425759 ⟨903806, by decide⟩ :=
  accepted_of_selected 12 425759 ⟨903806, by decide⟩ ⟨12, 1, 0, 903806, 425759, 1, 65536⟩
    (by decide) selected_cut_50582

theorem unmarked_context_11_106439_1446710 : frontier 10 ⟨1446710, by decide⟩
    (prefixCache 11 106439) (prefixPartial 11 106439) = false := by
  decide +kernel

theorem node_context_11_106439_1446710 : EJMOriginalGlobalDAGData.nodes 10 ⟨1446710, by decide⟩ =
    .split (coordinate 11) (![⟨1415033, by decide⟩,⟨1446647, by decide⟩,⟨1446709, by decide⟩,⟨903806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_106439_1446710 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106439 ⟨1446710, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 106439
    ⟨1446710, by decide⟩ (by decide) (![⟨1415033, by decide⟩,⟨1446647, by decide⟩,⟨1446709, by decide⟩,⟨903806, by decide⟩]) unmarked_context_11_106439_1446710 node_context_11_106439_1446710
  intro a
  fin_cases a
  · exact context_12_425756_1415033
  · exact context_12_425757_1446647
  · exact context_12_425758_1446709
  · exact context_12_425759_903806

theorem unmarked_context_10_26609_1446711 : frontier 11 ⟨1446711, by decide⟩
    (prefixCache 10 26609) (prefixPartial 10 26609) = false := by
  decide +kernel

theorem node_context_10_26609_1446711 : EJMOriginalGlobalDAGData.nodes 11 ⟨1446711, by decide⟩ =
    .split (coordinate 10) (![⟨1446478, by decide⟩,⟨1241271, by decide⟩,⟨1446597, by decide⟩,⟨1446710, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_26609_1446711 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26609 ⟨1446711, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 26609
    ⟨1446711, by decide⟩ (by decide) (![⟨1446478, by decide⟩,⟨1241271, by decide⟩,⟨1446597, by decide⟩,⟨1446710, by decide⟩]) unmarked_context_10_26609_1446711 node_context_10_26609_1446711
  intro a
  fin_cases a
  · exact context_11_106436_1446478
  · exact context_11_106437_1241271
  · exact context_11_106438_1446597
  · exact context_11_106439_1446710

theorem selected_cut_50583 : selected 9 ⟨435160, by decide⟩
    (prefixPartial 12 425760) = some ⟨12, 1, 0, 435160, 425760, 1, 65536⟩ := by
  decide +kernel

theorem context_12_425760_435160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 425760 ⟨435160, by decide⟩ :=
  accepted_of_selected 12 425760 ⟨435160, by decide⟩ ⟨12, 1, 0, 435160, 425760, 1, 65536⟩
    (by decide) selected_cut_50583

theorem selected_cut_50584 : selected 9 ⟨1446771, by decide⟩
    (prefixPartial 12 425761) = some ⟨12, 2, 0, 1446771, 425761, 2273, 65536⟩ := by
  decide +kernel

theorem context_12_425761_1446771 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 425761 ⟨1446771, by decide⟩ :=
  accepted_of_selected 12 425761 ⟨1446771, by decide⟩ ⟨12, 2, 0, 1446771, 425761, 2273, 65536⟩
    (by decide) selected_cut_50584

theorem selected_cut_50585 : selected 9 ⟨1446850, by decide⟩
    (prefixPartial 12 425762) = some ⟨12, 2, 0, 1446850, 425762, 2545, 65536⟩ := by
  decide +kernel

theorem context_12_425762_1446850 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 425762 ⟨1446850, by decide⟩ :=
  accepted_of_selected 12 425762 ⟨1446850, by decide⟩ ⟨12, 2, 0, 1446850, 425762, 2545, 65536⟩
    (by decide) selected_cut_50585

theorem selected_cut_50586 : selected 9 ⟨1446889, by decide⟩
    (prefixPartial 12 425763) = some ⟨12, 2, 0, 1446889, 425763, 1957, 65536⟩ := by
  decide +kernel

theorem context_12_425763_1446889 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 425763 ⟨1446889, by decide⟩ :=
  accepted_of_selected 12 425763 ⟨1446889, by decide⟩ ⟨12, 2, 0, 1446889, 425763, 1957, 65536⟩
    (by decide) selected_cut_50586

theorem unmarked_context_11_106440_1446890 : frontier 10 ⟨1446890, by decide⟩
    (prefixCache 11 106440) (prefixPartial 11 106440) = false := by
  decide +kernel

theorem node_context_11_106440_1446890 : EJMOriginalGlobalDAGData.nodes 10 ⟨1446890, by decide⟩ =
    .split (coordinate 11) (![⟨435160, by decide⟩,⟨1446771, by decide⟩,⟨1446850, by decide⟩,⟨1446889, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_106440_1446890 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106440 ⟨1446890, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 106440
    ⟨1446890, by decide⟩ (by decide) (![⟨435160, by decide⟩,⟨1446771, by decide⟩,⟨1446850, by decide⟩,⟨1446889, by decide⟩]) unmarked_context_11_106440_1446890 node_context_11_106440_1446890
  intro a
  fin_cases a
  · exact context_12_425760_435160
  · exact context_12_425761_1446771
  · exact context_12_425762_1446850
  · exact context_12_425763_1446889

theorem selected_cut_50587 : selected 10 ⟨1446965, by decide⟩
    (prefixPartial 11 106441) = some ⟨11, 2, 0, 1446965, 106441, 3461, 262144⟩ := by
  decide +kernel

theorem context_11_106441_1446965 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106441 ⟨1446965, by decide⟩ :=
  accepted_of_selected 11 106441 ⟨1446965, by decide⟩ ⟨11, 2, 0, 1446965, 106441, 3461, 262144⟩
    (by decide) selected_cut_50587

theorem selected_cut_50588 : selected 10 ⟨1446966, by decide⟩
    (prefixPartial 11 106442) = some ⟨11, 2, 0, 1446966, 106442, 5, 262144⟩ := by
  decide +kernel

theorem context_11_106442_1446966 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106442 ⟨1446966, by decide⟩ :=
  accepted_of_selected 11 106442 ⟨1446966, by decide⟩ ⟨11, 2, 0, 1446966, 106442, 5, 262144⟩
    (by decide) selected_cut_50588

theorem selected_cut_50589 : selected 9 ⟨1447011, by decide⟩
    (prefixPartial 12 425772) = some ⟨12, 2, 0, 1447011, 425772, 1237, 65536⟩ := by
  decide +kernel

theorem context_12_425772_1447011 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 425772 ⟨1447011, by decide⟩ :=
  accepted_of_selected 12 425772 ⟨1447011, by decide⟩ ⟨12, 2, 0, 1447011, 425772, 1237, 65536⟩
    (by decide) selected_cut_50589

theorem selected_cut_50590 : selected 9 ⟨1447053, by decide⟩
    (prefixPartial 12 425773) = some ⟨12, 2, 0, 1447053, 425773, 1813, 65536⟩ := by
  decide +kernel

theorem context_12_425773_1447053 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 425773 ⟨1447053, by decide⟩ :=
  accepted_of_selected 12 425773 ⟨1447053, by decide⟩ ⟨12, 2, 0, 1447053, 425773, 1813, 65536⟩
    (by decide) selected_cut_50590

theorem selected_cut_50591 : selected 9 ⟨1447098, by decide⟩
    (prefixPartial 12 425774) = some ⟨12, 2, 0, 1447098, 425774, 1933, 65536⟩ := by
  decide +kernel

theorem context_12_425774_1447098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 425774 ⟨1447098, by decide⟩ :=
  accepted_of_selected 12 425774 ⟨1447098, by decide⟩ ⟨12, 2, 0, 1447098, 425774, 1933, 65536⟩
    (by decide) selected_cut_50591

theorem selected_cut_50592 : selected 9 ⟨903806, by decide⟩
    (prefixPartial 12 425775) = some ⟨12, 1, 0, 903806, 425775, 1, 65536⟩ := by
  decide +kernel

theorem context_12_425775_903806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 425775 ⟨903806, by decide⟩ :=
  accepted_of_selected 12 425775 ⟨903806, by decide⟩ ⟨12, 1, 0, 903806, 425775, 1, 65536⟩
    (by decide) selected_cut_50592

theorem unmarked_context_11_106443_1447099 : frontier 10 ⟨1447099, by decide⟩
    (prefixCache 11 106443) (prefixPartial 11 106443) = false := by
  decide +kernel

theorem node_context_11_106443_1447099 : EJMOriginalGlobalDAGData.nodes 10 ⟨1447099, by decide⟩ =
    .split (coordinate 11) (![⟨1447011, by decide⟩,⟨1447053, by decide⟩,⟨1447098, by decide⟩,⟨903806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_106443_1447099 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106443 ⟨1447099, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 106443
    ⟨1447099, by decide⟩ (by decide) (![⟨1447011, by decide⟩,⟨1447053, by decide⟩,⟨1447098, by decide⟩,⟨903806, by decide⟩]) unmarked_context_11_106443_1447099 node_context_11_106443_1447099
  intro a
  fin_cases a
  · exact context_12_425772_1447011
  · exact context_12_425773_1447053
  · exact context_12_425774_1447098
  · exact context_12_425775_903806

theorem unmarked_context_10_26610_1447100 : frontier 11 ⟨1447100, by decide⟩
    (prefixCache 10 26610) (prefixPartial 10 26610) = false := by
  decide +kernel

theorem node_context_10_26610_1447100 : EJMOriginalGlobalDAGData.nodes 11 ⟨1447100, by decide⟩ =
    .split (coordinate 10) (![⟨1446890, by decide⟩,⟨1446965, by decide⟩,⟨1446966, by decide⟩,⟨1447099, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_26610_1447100 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26610 ⟨1447100, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 26610
    ⟨1447100, by decide⟩ (by decide) (![⟨1446890, by decide⟩,⟨1446965, by decide⟩,⟨1446966, by decide⟩,⟨1447099, by decide⟩]) unmarked_context_10_26610_1447100 node_context_10_26610_1447100
  intro a
  fin_cases a
  · exact context_11_106440_1446890
  · exact context_11_106441_1446965
  · exact context_11_106442_1446966
  · exact context_11_106443_1447099

theorem selected_cut_50593 : selected 9 ⟨1416143, by decide⟩
    (prefixPartial 12 425776) = some ⟨12, 1, 0, 1416143, 425776, 1, 65536⟩ := by
  decide +kernel

theorem context_12_425776_1416143 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 425776 ⟨1416143, by decide⟩ :=
  accepted_of_selected 12 425776 ⟨1416143, by decide⟩ ⟨12, 1, 0, 1416143, 425776, 1, 65536⟩
    (by decide) selected_cut_50593

theorem selected_cut_50594 : selected 9 ⟨1447138, by decide⟩
    (prefixPartial 12 425777) = some ⟨12, 2, 0, 1447138, 425777, 1653, 65536⟩ := by
  decide +kernel

theorem context_12_425777_1447138 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 425777 ⟨1447138, by decide⟩ :=
  accepted_of_selected 12 425777 ⟨1447138, by decide⟩ ⟨12, 2, 0, 1447138, 425777, 1653, 65536⟩
    (by decide) selected_cut_50594

theorem selected_cut_50595 : selected 9 ⟨1447176, by decide⟩
    (prefixPartial 12 425778) = some ⟨12, 2, 0, 1447176, 425778, 1597, 65536⟩ := by
  decide +kernel

theorem context_12_425778_1447176 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 425778 ⟨1447176, by decide⟩ :=
  accepted_of_selected 12 425778 ⟨1447176, by decide⟩ ⟨12, 2, 0, 1447176, 425778, 1597, 65536⟩
    (by decide) selected_cut_50595

theorem selected_cut_50596 : selected 9 ⟨1447208, by decide⟩
    (prefixPartial 12 425779) = some ⟨12, 2, 0, 1447208, 425779, 1365, 65536⟩ := by
  decide +kernel

theorem context_12_425779_1447208 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 425779 ⟨1447208, by decide⟩ :=
  accepted_of_selected 12 425779 ⟨1447208, by decide⟩ ⟨12, 2, 0, 1447208, 425779, 1365, 65536⟩
    (by decide) selected_cut_50596

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
