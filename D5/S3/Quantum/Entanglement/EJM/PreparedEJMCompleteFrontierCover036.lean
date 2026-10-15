/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover035
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_03460 : selected 8 ⟨108805, by decide⟩
    (prefixPartial 13 27823) = some ⟨13, 2, 0, 108805, 27823, 1225, 16384⟩ := by
  decide +kernel

theorem context_13_27823_108805 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27823 ⟨108805, by decide⟩ :=
  accepted_of_selected 13 27823 ⟨108805, by decide⟩ ⟨13, 2, 0, 108805, 27823, 1225, 16384⟩
    (by decide) selected_cut_03460

theorem unmarked_context_12_6955_108806 : frontier 9 ⟨108806, by decide⟩
    (prefixCache 12 6955) (prefixPartial 12 6955) = false := by
  decide +kernel

theorem node_context_12_6955_108806 : EJMOriginalGlobalDAGData.nodes 9 ⟨108806, by decide⟩ =
    .split (coordinate 12) (![⟨108656, by decide⟩,⟨108745, by decide⟩,⟨108792, by decide⟩,⟨108805, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_6955_108806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6955 ⟨108806, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 6955
    ⟨108806, by decide⟩ (by decide) (![⟨108656, by decide⟩,⟨108745, by decide⟩,⟨108792, by decide⟩,⟨108805, by decide⟩]) unmarked_context_12_6955_108806 node_context_12_6955_108806
  intro a
  fin_cases a
  · exact context_13_27820_108656
  · exact context_13_27821_108745
  · exact context_13_27822_108792
  · exact context_13_27823_108805

theorem unmarked_context_11_1738_108807 : frontier 10 ⟨108807, by decide⟩
    (prefixCache 11 1738) (prefixPartial 11 1738) = false := by
  decide +kernel

theorem node_context_11_1738_108807 : EJMOriginalGlobalDAGData.nodes 10 ⟨108807, by decide⟩ =
    .split (coordinate 11) (![⟨106538, by decide⟩,⟨106538, by decide⟩,⟨108639, by decide⟩,⟨108806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1738_108807 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1738 ⟨108807, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1738
    ⟨108807, by decide⟩ (by decide) (![⟨106538, by decide⟩,⟨106538, by decide⟩,⟨108639, by decide⟩,⟨108806, by decide⟩]) unmarked_context_11_1738_108807 node_context_11_1738_108807
  intro a
  fin_cases a
  · exact context_12_6952_106538
  · exact context_12_6953_106538
  · exact context_12_6954_108639
  · exact context_12_6955_108806

theorem selected_cut_03461 : selected 9 ⟨106538, by decide⟩
    (prefixPartial 12 6956) = some ⟨12, 1, 0, 106538, 6956, 1, 65536⟩ := by
  decide +kernel

theorem context_12_6956_106538 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6956 ⟨106538, by decide⟩ :=
  accepted_of_selected 12 6956 ⟨106538, by decide⟩ ⟨12, 1, 0, 106538, 6956, 1, 65536⟩
    (by decide) selected_cut_03461

theorem selected_cut_03462 : selected 9 ⟨106538, by decide⟩
    (prefixPartial 12 6957) = some ⟨12, 1, 0, 106538, 6957, 1, 65536⟩ := by
  decide +kernel

theorem context_12_6957_106538 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6957 ⟨106538, by decide⟩ :=
  accepted_of_selected 12 6957 ⟨106538, by decide⟩ ⟨12, 1, 0, 106538, 6957, 1, 65536⟩
    (by decide) selected_cut_03462

theorem selected_cut_03463 : selected 8 ⟨108819, by decide⟩
    (prefixPartial 13 27832) = some ⟨13, 2, 0, 108819, 27832, 349, 16384⟩ := by
  decide +kernel

theorem context_13_27832_108819 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27832 ⟨108819, by decide⟩ :=
  accepted_of_selected 13 27832 ⟨108819, by decide⟩ ⟨13, 2, 0, 108819, 27832, 349, 16384⟩
    (by decide) selected_cut_03463

theorem selected_cut_03464 : selected 8 ⟨108872, by decide⟩
    (prefixPartial 13 27833) = some ⟨13, 2, 0, 108872, 27833, 3337, 16384⟩ := by
  decide +kernel

theorem context_13_27833_108872 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27833 ⟨108872, by decide⟩ :=
  accepted_of_selected 13 27833 ⟨108872, by decide⟩ ⟨13, 2, 0, 108872, 27833, 3337, 16384⟩
    (by decide) selected_cut_03464

theorem selected_cut_03465 : selected 8 ⟨108903, by decide⟩
    (prefixPartial 13 27834) = some ⟨13, 2, 0, 108903, 27834, 1821, 16384⟩ := by
  decide +kernel

theorem context_13_27834_108903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27834 ⟨108903, by decide⟩ :=
  accepted_of_selected 13 27834 ⟨108903, by decide⟩ ⟨13, 2, 0, 108903, 27834, 1821, 16384⟩
    (by decide) selected_cut_03465

theorem selected_cut_03466 : selected 8 ⟨108912, by decide⟩
    (prefixPartial 13 27835) = some ⟨13, 2, 0, 108912, 27835, 985, 16384⟩ := by
  decide +kernel

theorem context_13_27835_108912 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27835 ⟨108912, by decide⟩ :=
  accepted_of_selected 13 27835 ⟨108912, by decide⟩ ⟨13, 2, 0, 108912, 27835, 985, 16384⟩
    (by decide) selected_cut_03466

theorem unmarked_context_12_6958_108913 : frontier 9 ⟨108913, by decide⟩
    (prefixCache 12 6958) (prefixPartial 12 6958) = false := by
  decide +kernel

theorem node_context_12_6958_108913 : EJMOriginalGlobalDAGData.nodes 9 ⟨108913, by decide⟩ =
    .split (coordinate 12) (![⟨108819, by decide⟩,⟨108872, by decide⟩,⟨108903, by decide⟩,⟨108912, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_6958_108913 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6958 ⟨108913, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 6958
    ⟨108913, by decide⟩ (by decide) (![⟨108819, by decide⟩,⟨108872, by decide⟩,⟨108903, by decide⟩,⟨108912, by decide⟩]) unmarked_context_12_6958_108913 node_context_12_6958_108913
  intro a
  fin_cases a
  · exact context_13_27832_108819
  · exact context_13_27833_108872
  · exact context_13_27834_108903
  · exact context_13_27835_108912

theorem selected_cut_03467 : selected 9 ⟨4596, by decide⟩
    (prefixPartial 12 6959) = some ⟨12, 1, 0, 4596, 6959, 1, 65536⟩ := by
  decide +kernel

theorem context_12_6959_4596 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6959 ⟨4596, by decide⟩ :=
  accepted_of_selected 12 6959 ⟨4596, by decide⟩ ⟨12, 1, 0, 4596, 6959, 1, 65536⟩
    (by decide) selected_cut_03467

theorem unmarked_context_11_1739_108914 : frontier 10 ⟨108914, by decide⟩
    (prefixCache 11 1739) (prefixPartial 11 1739) = false := by
  decide +kernel

theorem node_context_11_1739_108914 : EJMOriginalGlobalDAGData.nodes 10 ⟨108914, by decide⟩ =
    .split (coordinate 11) (![⟨106538, by decide⟩,⟨106538, by decide⟩,⟨108913, by decide⟩,⟨4596, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1739_108914 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1739 ⟨108914, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1739
    ⟨108914, by decide⟩ (by decide) (![⟨106538, by decide⟩,⟨106538, by decide⟩,⟨108913, by decide⟩,⟨4596, by decide⟩]) unmarked_context_11_1739_108914 node_context_11_1739_108914
  intro a
  fin_cases a
  · exact context_12_6956_106538
  · exact context_12_6957_106538
  · exact context_12_6958_108913
  · exact context_12_6959_4596

theorem unmarked_context_10_434_108915 : frontier 11 ⟨108915, by decide⟩
    (prefixCache 10 434) (prefixPartial 10 434) = false := by
  decide +kernel

theorem node_context_10_434_108915 : EJMOriginalGlobalDAGData.nodes 11 ⟨108915, by decide⟩ =
    .split (coordinate 10) (![⟨108226, by decide⟩,⟨108442, by decide⟩,⟨108807, by decide⟩,⟨108914, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_434_108915 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 434 ⟨108915, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 434
    ⟨108915, by decide⟩ (by decide) (![⟨108226, by decide⟩,⟨108442, by decide⟩,⟨108807, by decide⟩,⟨108914, by decide⟩]) unmarked_context_10_434_108915 node_context_10_434_108915
  intro a
  fin_cases a
  · exact context_11_1736_108226
  · exact context_11_1737_108442
  · exact context_11_1738_108807
  · exact context_11_1739_108914

theorem selected_cut_03468 : selected 10 ⟨109000, by decide⟩
    (prefixPartial 11 1740) = some ⟨11, 2, 0, 109000, 1740, 3981, 262144⟩ := by
  decide +kernel

theorem context_11_1740_109000 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1740 ⟨109000, by decide⟩ :=
  accepted_of_selected 11 1740 ⟨109000, by decide⟩ ⟨11, 2, 0, 109000, 1740, 3981, 262144⟩
    (by decide) selected_cut_03468

theorem selected_cut_03469 : selected 9 ⟨106538, by decide⟩
    (prefixPartial 12 6964) = some ⟨12, 1, 0, 106538, 6964, 1, 65536⟩ := by
  decide +kernel

theorem context_12_6964_106538 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6964 ⟨106538, by decide⟩ :=
  accepted_of_selected 12 6964 ⟨106538, by decide⟩ ⟨12, 1, 0, 106538, 6964, 1, 65536⟩
    (by decide) selected_cut_03469

theorem selected_cut_03470 : selected 9 ⟨106538, by decide⟩
    (prefixPartial 12 6965) = some ⟨12, 1, 0, 106538, 6965, 1, 65536⟩ := by
  decide +kernel

theorem context_12_6965_106538 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6965 ⟨106538, by decide⟩ :=
  accepted_of_selected 12 6965 ⟨106538, by decide⟩ ⟨12, 1, 0, 106538, 6965, 1, 65536⟩
    (by decide) selected_cut_03470

theorem selected_cut_03471 : selected 8 ⟨109004, by decide⟩
    (prefixPartial 13 27864) = some ⟨13, 2, 0, 109004, 27864, 109, 16384⟩ := by
  decide +kernel

theorem context_13_27864_109004 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27864 ⟨109004, by decide⟩ :=
  accepted_of_selected 13 27864 ⟨109004, by decide⟩ ⟨13, 2, 0, 109004, 27864, 109, 16384⟩
    (by decide) selected_cut_03471

theorem selected_cut_03472 : selected 8 ⟨109050, by decide⟩
    (prefixPartial 13 27865) = some ⟨13, 2, 0, 109050, 27865, 1777, 16384⟩ := by
  decide +kernel

theorem context_13_27865_109050 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27865 ⟨109050, by decide⟩ :=
  accepted_of_selected 13 27865 ⟨109050, by decide⟩ ⟨13, 2, 0, 109050, 27865, 1777, 16384⟩
    (by decide) selected_cut_03472

theorem selected_cut_03473 : selected 8 ⟨109120, by decide⟩
    (prefixPartial 13 27866) = some ⟨13, 2, 0, 109120, 27866, 2597, 16384⟩ := by
  decide +kernel

theorem context_13_27866_109120 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27866 ⟨109120, by decide⟩ :=
  accepted_of_selected 13 27866 ⟨109120, by decide⟩ ⟨13, 2, 0, 109120, 27866, 2597, 16384⟩
    (by decide) selected_cut_03473

theorem selected_cut_03474 : selected 8 ⟨4592, by decide⟩
    (prefixPartial 13 27867) = some ⟨13, 1, 0, 4592, 27867, 1, 16384⟩ := by
  decide +kernel

theorem context_13_27867_4592 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27867 ⟨4592, by decide⟩ :=
  accepted_of_selected 13 27867 ⟨4592, by decide⟩ ⟨13, 1, 0, 4592, 27867, 1, 16384⟩
    (by decide) selected_cut_03474

theorem unmarked_context_12_6966_109121 : frontier 9 ⟨109121, by decide⟩
    (prefixCache 12 6966) (prefixPartial 12 6966) = false := by
  decide +kernel

theorem node_context_12_6966_109121 : EJMOriginalGlobalDAGData.nodes 9 ⟨109121, by decide⟩ =
    .split (coordinate 12) (![⟨109004, by decide⟩,⟨109050, by decide⟩,⟨109120, by decide⟩,⟨4592, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_6966_109121 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6966 ⟨109121, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 6966
    ⟨109121, by decide⟩ (by decide) (![⟨109004, by decide⟩,⟨109050, by decide⟩,⟨109120, by decide⟩,⟨4592, by decide⟩]) unmarked_context_12_6966_109121 node_context_12_6966_109121
  intro a
  fin_cases a
  · exact context_13_27864_109004
  · exact context_13_27865_109050
  · exact context_13_27866_109120
  · exact context_13_27867_4592

theorem selected_cut_03475 : selected 9 ⟨106538, by decide⟩
    (prefixPartial 12 6967) = some ⟨12, 1, 0, 106538, 6967, 1, 65536⟩ := by
  decide +kernel

theorem context_12_6967_106538 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6967 ⟨106538, by decide⟩ :=
  accepted_of_selected 12 6967 ⟨106538, by decide⟩ ⟨12, 1, 0, 106538, 6967, 1, 65536⟩
    (by decide) selected_cut_03475

theorem unmarked_context_11_1741_109122 : frontier 10 ⟨109122, by decide⟩
    (prefixCache 11 1741) (prefixPartial 11 1741) = false := by
  decide +kernel

theorem node_context_11_1741_109122 : EJMOriginalGlobalDAGData.nodes 10 ⟨109122, by decide⟩ =
    .split (coordinate 11) (![⟨106538, by decide⟩,⟨106538, by decide⟩,⟨109121, by decide⟩,⟨106538, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1741_109122 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1741 ⟨109122, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1741
    ⟨109122, by decide⟩ (by decide) (![⟨106538, by decide⟩,⟨106538, by decide⟩,⟨109121, by decide⟩,⟨106538, by decide⟩]) unmarked_context_11_1741_109122 node_context_11_1741_109122
  intro a
  fin_cases a
  · exact context_12_6964_106538
  · exact context_12_6965_106538
  · exact context_12_6966_109121
  · exact context_12_6967_106538

theorem selected_cut_03476 : selected 9 ⟨106538, by decide⟩
    (prefixPartial 12 6968) = some ⟨12, 1, 0, 106538, 6968, 1, 65536⟩ := by
  decide +kernel

theorem context_12_6968_106538 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6968 ⟨106538, by decide⟩ :=
  accepted_of_selected 12 6968 ⟨106538, by decide⟩ ⟨12, 1, 0, 106538, 6968, 1, 65536⟩
    (by decide) selected_cut_03476

theorem selected_cut_03477 : selected 9 ⟨106538, by decide⟩
    (prefixPartial 12 6969) = some ⟨12, 1, 0, 106538, 6969, 1, 65536⟩ := by
  decide +kernel

theorem context_12_6969_106538 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6969 ⟨106538, by decide⟩ :=
  accepted_of_selected 12 6969 ⟨106538, by decide⟩ ⟨12, 1, 0, 106538, 6969, 1, 65536⟩
    (by decide) selected_cut_03477

theorem selected_cut_03478 : selected 8 ⟨109128, by decide⟩
    (prefixPartial 13 27880) = some ⟨13, 2, 0, 109128, 27880, 89, 16384⟩ := by
  decide +kernel

theorem context_13_27880_109128 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27880 ⟨109128, by decide⟩ :=
  accepted_of_selected 13 27880 ⟨109128, by decide⟩ ⟨13, 2, 0, 109128, 27880, 89, 16384⟩
    (by decide) selected_cut_03478

theorem selected_cut_03479 : selected 8 ⟨109176, by decide⟩
    (prefixPartial 13 27881) = some ⟨13, 2, 0, 109176, 27881, 3221, 16384⟩ := by
  decide +kernel

theorem context_13_27881_109176 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27881 ⟨109176, by decide⟩ :=
  accepted_of_selected 13 27881 ⟨109176, by decide⟩ ⟨13, 2, 0, 109176, 27881, 3221, 16384⟩
    (by decide) selected_cut_03479

theorem selected_cut_03480 : selected 8 ⟨109201, by decide⟩
    (prefixPartial 13 27882) = some ⟨13, 2, 0, 109201, 27882, 2129, 16384⟩ := by
  decide +kernel

theorem context_13_27882_109201 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27882 ⟨109201, by decide⟩ :=
  accepted_of_selected 13 27882 ⟨109201, by decide⟩ ⟨13, 2, 0, 109201, 27882, 2129, 16384⟩
    (by decide) selected_cut_03480

theorem selected_cut_03481 : selected 8 ⟨109213, by decide⟩
    (prefixPartial 13 27883) = some ⟨13, 2, 0, 109213, 27883, 1065, 16384⟩ := by
  decide +kernel

theorem context_13_27883_109213 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27883 ⟨109213, by decide⟩ :=
  accepted_of_selected 13 27883 ⟨109213, by decide⟩ ⟨13, 2, 0, 109213, 27883, 1065, 16384⟩
    (by decide) selected_cut_03481

theorem unmarked_context_12_6970_109214 : frontier 9 ⟨109214, by decide⟩
    (prefixCache 12 6970) (prefixPartial 12 6970) = false := by
  decide +kernel

theorem node_context_12_6970_109214 : EJMOriginalGlobalDAGData.nodes 9 ⟨109214, by decide⟩ =
    .split (coordinate 12) (![⟨109128, by decide⟩,⟨109176, by decide⟩,⟨109201, by decide⟩,⟨109213, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_6970_109214 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6970 ⟨109214, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 6970
    ⟨109214, by decide⟩ (by decide) (![⟨109128, by decide⟩,⟨109176, by decide⟩,⟨109201, by decide⟩,⟨109213, by decide⟩]) unmarked_context_12_6970_109214 node_context_12_6970_109214
  intro a
  fin_cases a
  · exact context_13_27880_109128
  · exact context_13_27881_109176
  · exact context_13_27882_109201
  · exact context_13_27883_109213

theorem selected_cut_03482 : selected 9 ⟨106538, by decide⟩
    (prefixPartial 12 6971) = some ⟨12, 1, 0, 106538, 6971, 1, 65536⟩ := by
  decide +kernel

theorem context_12_6971_106538 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6971 ⟨106538, by decide⟩ :=
  accepted_of_selected 12 6971 ⟨106538, by decide⟩ ⟨12, 1, 0, 106538, 6971, 1, 65536⟩
    (by decide) selected_cut_03482

theorem unmarked_context_11_1742_109215 : frontier 10 ⟨109215, by decide⟩
    (prefixCache 11 1742) (prefixPartial 11 1742) = false := by
  decide +kernel

theorem node_context_11_1742_109215 : EJMOriginalGlobalDAGData.nodes 10 ⟨109215, by decide⟩ =
    .split (coordinate 11) (![⟨106538, by decide⟩,⟨106538, by decide⟩,⟨109214, by decide⟩,⟨106538, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1742_109215 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1742 ⟨109215, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1742
    ⟨109215, by decide⟩ (by decide) (![⟨106538, by decide⟩,⟨106538, by decide⟩,⟨109214, by decide⟩,⟨106538, by decide⟩]) unmarked_context_11_1742_109215 node_context_11_1742_109215
  intro a
  fin_cases a
  · exact context_12_6968_106538
  · exact context_12_6969_106538
  · exact context_12_6970_109214
  · exact context_12_6971_106538

theorem selected_cut_03483 : selected 10 ⟨109216, by decide⟩
    (prefixPartial 11 1743) = some ⟨11, 2, 0, 109216, 1743, 5, 262144⟩ := by
  decide +kernel

theorem context_11_1743_109216 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1743 ⟨109216, by decide⟩ :=
  accepted_of_selected 11 1743 ⟨109216, by decide⟩ ⟨11, 2, 0, 109216, 1743, 5, 262144⟩
    (by decide) selected_cut_03483

theorem unmarked_context_10_435_109217 : frontier 11 ⟨109217, by decide⟩
    (prefixCache 10 435) (prefixPartial 10 435) = false := by
  decide +kernel

theorem node_context_10_435_109217 : EJMOriginalGlobalDAGData.nodes 11 ⟨109217, by decide⟩ =
    .split (coordinate 10) (![⟨109000, by decide⟩,⟨109122, by decide⟩,⟨109215, by decide⟩,⟨109216, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_435_109217 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 435 ⟨109217, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 435
    ⟨109217, by decide⟩ (by decide) (![⟨109000, by decide⟩,⟨109122, by decide⟩,⟨109215, by decide⟩,⟨109216, by decide⟩]) unmarked_context_10_435_109217 node_context_10_435_109217
  intro a
  fin_cases a
  · exact context_11_1740_109000
  · exact context_11_1741_109122
  · exact context_11_1742_109215
  · exact context_11_1743_109216

theorem unmarked_context_9_108_109218 : frontier 12 ⟨109218, by decide⟩
    (prefixCache 9 108) (prefixPartial 9 108) = false := by
  decide +kernel

theorem node_context_9_108_109218 : EJMOriginalGlobalDAGData.nodes 12 ⟨109218, by decide⟩ =
    .split (coordinate 9) (![⟨106537, by decide⟩,⟨108038, by decide⟩,⟨108915, by decide⟩,⟨109217, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_108_109218 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 108 ⟨109218, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 108
    ⟨109218, by decide⟩ (by decide) (![⟨106537, by decide⟩,⟨108038, by decide⟩,⟨108915, by decide⟩,⟨109217, by decide⟩]) unmarked_context_9_108_109218 node_context_9_108_109218
  intro a
  fin_cases a
  · exact context_10_432_106537
  · exact context_10_433_108038
  · exact context_10_434_108915
  · exact context_10_435_109217

theorem selected_cut_03484 : selected 9 ⟨109288, by decide⟩
    (prefixPartial 12 6976) = some ⟨12, 2, 0, 109288, 6976, 3537, 65536⟩ := by
  decide +kernel

theorem context_12_6976_109288 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6976 ⟨109288, by decide⟩ :=
  accepted_of_selected 12 6976 ⟨109288, by decide⟩ ⟨12, 2, 0, 109288, 6976, 3537, 65536⟩
    (by decide) selected_cut_03484

theorem selected_cut_03485 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 27908) = some ⟨13, 1, 0, 3444, 27908, 1, 16384⟩ := by
  decide +kernel

theorem context_13_27908_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27908 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 27908 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 27908, 1, 16384⟩
    (by decide) selected_cut_03485

theorem selected_cut_03486 : selected 8 ⟨109344, by decide⟩
    (prefixPartial 13 27909) = some ⟨13, 2, 0, 109344, 27909, 3521, 16384⟩ := by
  decide +kernel

theorem context_13_27909_109344 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27909 ⟨109344, by decide⟩ :=
  accepted_of_selected 13 27909 ⟨109344, by decide⟩ ⟨13, 2, 0, 109344, 27909, 3521, 16384⟩
    (by decide) selected_cut_03486

theorem selected_cut_03487 : selected 8 ⟨109368, by decide⟩
    (prefixPartial 13 27910) = some ⟨13, 2, 0, 109368, 27910, 2033, 16384⟩ := by
  decide +kernel

theorem context_13_27910_109368 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27910 ⟨109368, by decide⟩ :=
  accepted_of_selected 13 27910 ⟨109368, by decide⟩ ⟨13, 2, 0, 109368, 27910, 2033, 16384⟩
    (by decide) selected_cut_03487

theorem selected_cut_03488 : selected 8 ⟨109382, by decide⟩
    (prefixPartial 13 27911) = some ⟨13, 2, 0, 109382, 27911, 813, 16384⟩ := by
  decide +kernel

theorem context_13_27911_109382 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27911 ⟨109382, by decide⟩ :=
  accepted_of_selected 13 27911 ⟨109382, by decide⟩ ⟨13, 2, 0, 109382, 27911, 813, 16384⟩
    (by decide) selected_cut_03488

theorem unmarked_context_12_6977_109383 : frontier 9 ⟨109383, by decide⟩
    (prefixCache 12 6977) (prefixPartial 12 6977) = false := by
  decide +kernel

theorem node_context_12_6977_109383 : EJMOriginalGlobalDAGData.nodes 9 ⟨109383, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨109344, by decide⟩,⟨109368, by decide⟩,⟨109382, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_6977_109383 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6977 ⟨109383, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 6977
    ⟨109383, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨109344, by decide⟩,⟨109368, by decide⟩,⟨109382, by decide⟩]) unmarked_context_12_6977_109383 node_context_12_6977_109383
  intro a
  fin_cases a
  · exact context_13_27908_3444
  · exact context_13_27909_109344
  · exact context_13_27910_109368
  · exact context_13_27911_109382

theorem selected_cut_03489 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 27912) = some ⟨13, 1, 0, 3444, 27912, 1, 16384⟩ := by
  decide +kernel

theorem context_13_27912_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27912 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 27912 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 27912, 1, 16384⟩
    (by decide) selected_cut_03489

theorem selected_cut_03490 : selected 8 ⟨109450, by decide⟩
    (prefixPartial 13 27913) = some ⟨13, 2, 0, 109450, 27913, 3769, 16384⟩ := by
  decide +kernel

theorem context_13_27913_109450 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27913 ⟨109450, by decide⟩ :=
  accepted_of_selected 13 27913 ⟨109450, by decide⟩ ⟨13, 2, 0, 109450, 27913, 3769, 16384⟩
    (by decide) selected_cut_03490

theorem selected_cut_03491 : selected 8 ⟨109482, by decide⟩
    (prefixPartial 13 27914) = some ⟨13, 2, 0, 109482, 27914, 2169, 16384⟩ := by
  decide +kernel

theorem context_13_27914_109482 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27914 ⟨109482, by decide⟩ :=
  accepted_of_selected 13 27914 ⟨109482, by decide⟩ ⟨13, 2, 0, 109482, 27914, 2169, 16384⟩
    (by decide) selected_cut_03491

theorem selected_cut_03492 : selected 8 ⟨109492, by decide⟩
    (prefixPartial 13 27915) = some ⟨13, 2, 0, 109492, 27915, 773, 16384⟩ := by
  decide +kernel

theorem context_13_27915_109492 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27915 ⟨109492, by decide⟩ :=
  accepted_of_selected 13 27915 ⟨109492, by decide⟩ ⟨13, 2, 0, 109492, 27915, 773, 16384⟩
    (by decide) selected_cut_03492

theorem unmarked_context_12_6978_109493 : frontier 9 ⟨109493, by decide⟩
    (prefixCache 12 6978) (prefixPartial 12 6978) = false := by
  decide +kernel

theorem node_context_12_6978_109493 : EJMOriginalGlobalDAGData.nodes 9 ⟨109493, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨109450, by decide⟩,⟨109482, by decide⟩,⟨109492, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_6978_109493 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6978 ⟨109493, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 6978
    ⟨109493, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨109450, by decide⟩,⟨109482, by decide⟩,⟨109492, by decide⟩]) unmarked_context_12_6978_109493 node_context_12_6978_109493
  intro a
  fin_cases a
  · exact context_13_27912_3444
  · exact context_13_27913_109450
  · exact context_13_27914_109482
  · exact context_13_27915_109492

theorem selected_cut_03493 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 27916) = some ⟨13, 1, 0, 3444, 27916, 1, 16384⟩ := by
  decide +kernel

theorem context_13_27916_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27916 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 27916 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 27916, 1, 16384⟩
    (by decide) selected_cut_03493

theorem selected_cut_03494 : selected 8 ⟨109545, by decide⟩
    (prefixPartial 13 27917) = some ⟨13, 2, 0, 109545, 27917, 3433, 16384⟩ := by
  decide +kernel

theorem context_13_27917_109545 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27917 ⟨109545, by decide⟩ :=
  accepted_of_selected 13 27917 ⟨109545, by decide⟩ ⟨13, 2, 0, 109545, 27917, 3433, 16384⟩
    (by decide) selected_cut_03494

theorem selected_cut_03495 : selected 8 ⟨109573, by decide⟩
    (prefixPartial 13 27918) = some ⟨13, 2, 0, 109573, 27918, 2233, 16384⟩ := by
  decide +kernel

theorem context_13_27918_109573 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27918 ⟨109573, by decide⟩ :=
  accepted_of_selected 13 27918 ⟨109573, by decide⟩ ⟨13, 2, 0, 109573, 27918, 2233, 16384⟩
    (by decide) selected_cut_03495

theorem selected_cut_03496 : selected 8 ⟨109582, by decide⟩
    (prefixPartial 13 27919) = some ⟨13, 2, 0, 109582, 27919, 729, 16384⟩ := by
  decide +kernel

theorem context_13_27919_109582 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27919 ⟨109582, by decide⟩ :=
  accepted_of_selected 13 27919 ⟨109582, by decide⟩ ⟨13, 2, 0, 109582, 27919, 729, 16384⟩
    (by decide) selected_cut_03496

theorem unmarked_context_12_6979_109583 : frontier 9 ⟨109583, by decide⟩
    (prefixCache 12 6979) (prefixPartial 12 6979) = false := by
  decide +kernel

theorem node_context_12_6979_109583 : EJMOriginalGlobalDAGData.nodes 9 ⟨109583, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨109545, by decide⟩,⟨109573, by decide⟩,⟨109582, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_6979_109583 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6979 ⟨109583, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 6979
    ⟨109583, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨109545, by decide⟩,⟨109573, by decide⟩,⟨109582, by decide⟩]) unmarked_context_12_6979_109583 node_context_12_6979_109583
  intro a
  fin_cases a
  · exact context_13_27916_3444
  · exact context_13_27917_109545
  · exact context_13_27918_109573
  · exact context_13_27919_109582

theorem unmarked_context_11_1744_109584 : frontier 10 ⟨109584, by decide⟩
    (prefixCache 11 1744) (prefixPartial 11 1744) = false := by
  decide +kernel

theorem node_context_11_1744_109584 : EJMOriginalGlobalDAGData.nodes 10 ⟨109584, by decide⟩ =
    .split (coordinate 11) (![⟨109288, by decide⟩,⟨109383, by decide⟩,⟨109493, by decide⟩,⟨109583, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1744_109584 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1744 ⟨109584, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1744
    ⟨109584, by decide⟩ (by decide) (![⟨109288, by decide⟩,⟨109383, by decide⟩,⟨109493, by decide⟩,⟨109583, by decide⟩]) unmarked_context_11_1744_109584 node_context_11_1744_109584
  intro a
  fin_cases a
  · exact context_12_6976_109288
  · exact context_12_6977_109383
  · exact context_12_6978_109493
  · exact context_12_6979_109583

theorem selected_cut_03497 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 27920) = some ⟨13, 1, 0, 3444, 27920, 1, 16384⟩ := by
  decide +kernel

theorem context_13_27920_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27920 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 27920 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 27920, 1, 16384⟩
    (by decide) selected_cut_03497

theorem selected_cut_03498 : selected 8 ⟨109642, by decide⟩
    (prefixPartial 13 27921) = some ⟨13, 2, 0, 109642, 27921, 2253, 16384⟩ := by
  decide +kernel

theorem context_13_27921_109642 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27921 ⟨109642, by decide⟩ :=
  accepted_of_selected 13 27921 ⟨109642, by decide⟩ ⟨13, 2, 0, 109642, 27921, 2253, 16384⟩
    (by decide) selected_cut_03498

theorem selected_cut_03499 : selected 8 ⟨109702, by decide⟩
    (prefixPartial 13 27922) = some ⟨13, 2, 0, 109702, 27922, 2553, 16384⟩ := by
  decide +kernel

theorem context_13_27922_109702 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27922 ⟨109702, by decide⟩ :=
  accepted_of_selected 13 27922 ⟨109702, by decide⟩ ⟨13, 2, 0, 109702, 27922, 2553, 16384⟩
    (by decide) selected_cut_03499

theorem selected_cut_03500 : selected 8 ⟨4592, by decide⟩
    (prefixPartial 13 27923) = some ⟨13, 1, 0, 4592, 27923, 1, 16384⟩ := by
  decide +kernel

theorem context_13_27923_4592 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27923 ⟨4592, by decide⟩ :=
  accepted_of_selected 13 27923 ⟨4592, by decide⟩ ⟨13, 1, 0, 4592, 27923, 1, 16384⟩
    (by decide) selected_cut_03500

theorem unmarked_context_12_6980_109703 : frontier 9 ⟨109703, by decide⟩
    (prefixCache 12 6980) (prefixPartial 12 6980) = false := by
  decide +kernel

theorem node_context_12_6980_109703 : EJMOriginalGlobalDAGData.nodes 9 ⟨109703, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨109642, by decide⟩,⟨109702, by decide⟩,⟨4592, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_6980_109703 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6980 ⟨109703, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 6980
    ⟨109703, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨109642, by decide⟩,⟨109702, by decide⟩,⟨4592, by decide⟩]) unmarked_context_12_6980_109703 node_context_12_6980_109703
  intro a
  fin_cases a
  · exact context_13_27920_3444
  · exact context_13_27921_109642
  · exact context_13_27922_109702
  · exact context_13_27923_4592

theorem selected_cut_03501 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 27924) = some ⟨13, 1, 0, 3444, 27924, 1, 16384⟩ := by
  decide +kernel

theorem context_13_27924_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27924 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 27924 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 27924, 1, 16384⟩
    (by decide) selected_cut_03501

theorem selected_cut_03502 : selected 8 ⟨109770, by decide⟩
    (prefixPartial 13 27925) = some ⟨13, 2, 0, 109770, 27925, 3793, 16384⟩ := by
  decide +kernel

theorem context_13_27925_109770 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27925 ⟨109770, by decide⟩ :=
  accepted_of_selected 13 27925 ⟨109770, by decide⟩ ⟨13, 2, 0, 109770, 27925, 3793, 16384⟩
    (by decide) selected_cut_03502

theorem selected_cut_03503 : selected 8 ⟨109808, by decide⟩
    (prefixPartial 13 27926) = some ⟨13, 2, 0, 109808, 27926, 2741, 16384⟩ := by
  decide +kernel

theorem context_13_27926_109808 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27926 ⟨109808, by decide⟩ :=
  accepted_of_selected 13 27926 ⟨109808, by decide⟩ ⟨13, 2, 0, 109808, 27926, 2741, 16384⟩
    (by decide) selected_cut_03503

theorem selected_cut_03504 : selected 8 ⟨109822, by decide⟩
    (prefixPartial 13 27927) = some ⟨13, 2, 0, 109822, 27927, 1205, 16384⟩ := by
  decide +kernel

theorem context_13_27927_109822 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27927 ⟨109822, by decide⟩ :=
  accepted_of_selected 13 27927 ⟨109822, by decide⟩ ⟨13, 2, 0, 109822, 27927, 1205, 16384⟩
    (by decide) selected_cut_03504

theorem unmarked_context_12_6981_109823 : frontier 9 ⟨109823, by decide⟩
    (prefixCache 12 6981) (prefixPartial 12 6981) = false := by
  decide +kernel

theorem node_context_12_6981_109823 : EJMOriginalGlobalDAGData.nodes 9 ⟨109823, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨109770, by decide⟩,⟨109808, by decide⟩,⟨109822, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_6981_109823 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6981 ⟨109823, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 6981
    ⟨109823, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨109770, by decide⟩,⟨109808, by decide⟩,⟨109822, by decide⟩]) unmarked_context_12_6981_109823 node_context_12_6981_109823
  intro a
  fin_cases a
  · exact context_13_27924_3444
  · exact context_13_27925_109770
  · exact context_13_27926_109808
  · exact context_13_27927_109822

theorem selected_cut_03505 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 27928) = some ⟨13, 1, 0, 3444, 27928, 1, 16384⟩ := by
  decide +kernel

theorem context_13_27928_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27928 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 27928 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 27928, 1, 16384⟩
    (by decide) selected_cut_03505

theorem selected_cut_03506 : selected 7 ⟨109842, by decide⟩
    (prefixPartial 14 111716) = some ⟨14, 2, 0, 109842, 111716, 813, 4096⟩ := by
  decide +kernel

theorem context_14_111716_109842 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 111716 ⟨109842, by decide⟩ :=
  accepted_of_selected 14 111716 ⟨109842, by decide⟩ ⟨14, 2, 0, 109842, 111716, 813, 4096⟩
    (by decide) selected_cut_03506

theorem selected_cut_03507 : selected 7 ⟨109858, by decide⟩
    (prefixPartial 14 111717) = some ⟨14, 2, 0, 109858, 111717, 865, 4096⟩ := by
  decide +kernel

theorem context_14_111717_109858 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 111717 ⟨109858, by decide⟩ :=
  accepted_of_selected 14 111717 ⟨109858, by decide⟩ ⟨14, 2, 0, 109858, 111717, 865, 4096⟩
    (by decide) selected_cut_03507

theorem selected_cut_03508 : selected 7 ⟨109890, by decide⟩
    (prefixPartial 14 111718) = some ⟨14, 2, 0, 109890, 111718, 1489, 4096⟩ := by
  decide +kernel

theorem context_14_111718_109890 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 111718 ⟨109890, by decide⟩ :=
  accepted_of_selected 14 111718 ⟨109890, by decide⟩ ⟨14, 2, 0, 109890, 111718, 1489, 4096⟩
    (by decide) selected_cut_03508

theorem selected_cut_03509 : selected 7 ⟨109910, by decide⟩
    (prefixPartial 14 111719) = some ⟨14, 2, 0, 109910, 111719, 1061, 4096⟩ := by
  decide +kernel

theorem context_14_111719_109910 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 111719 ⟨109910, by decide⟩ :=
  accepted_of_selected 14 111719 ⟨109910, by decide⟩ ⟨14, 2, 0, 109910, 111719, 1061, 4096⟩
    (by decide) selected_cut_03509

theorem unmarked_context_13_27929_109911 : frontier 8 ⟨109911, by decide⟩
    (prefixCache 13 27929) (prefixPartial 13 27929) = false := by
  decide +kernel

theorem node_context_13_27929_109911 : EJMOriginalGlobalDAGData.nodes 8 ⟨109911, by decide⟩ =
    .split (coordinate 13) (![⟨109842, by decide⟩,⟨109858, by decide⟩,⟨109890, by decide⟩,⟨109910, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_27929_109911 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27929 ⟨109911, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 27929
    ⟨109911, by decide⟩ (by decide) (![⟨109842, by decide⟩,⟨109858, by decide⟩,⟨109890, by decide⟩,⟨109910, by decide⟩]) unmarked_context_13_27929_109911 node_context_13_27929_109911
  intro a
  fin_cases a
  · exact context_14_111716_109842
  · exact context_14_111717_109858
  · exact context_14_111718_109890
  · exact context_14_111719_109910

theorem selected_cut_03510 : selected 8 ⟨109977, by decide⟩
    (prefixPartial 13 27930) = some ⟨13, 2, 0, 109977, 27930, 3033, 16384⟩ := by
  decide +kernel

theorem context_13_27930_109977 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27930 ⟨109977, by decide⟩ :=
  accepted_of_selected 13 27930 ⟨109977, by decide⟩ ⟨13, 2, 0, 109977, 27930, 3033, 16384⟩
    (by decide) selected_cut_03510

theorem selected_cut_03511 : selected 8 ⟨109992, by decide⟩
    (prefixPartial 13 27931) = some ⟨13, 2, 0, 109992, 27931, 1125, 16384⟩ := by
  decide +kernel

theorem context_13_27931_109992 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27931 ⟨109992, by decide⟩ :=
  accepted_of_selected 13 27931 ⟨109992, by decide⟩ ⟨13, 2, 0, 109992, 27931, 1125, 16384⟩
    (by decide) selected_cut_03511

theorem unmarked_context_12_6982_109993 : frontier 9 ⟨109993, by decide⟩
    (prefixCache 12 6982) (prefixPartial 12 6982) = false := by
  decide +kernel

theorem node_context_12_6982_109993 : EJMOriginalGlobalDAGData.nodes 9 ⟨109993, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨109911, by decide⟩,⟨109977, by decide⟩,⟨109992, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_6982_109993 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6982 ⟨109993, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 6982
    ⟨109993, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨109911, by decide⟩,⟨109977, by decide⟩,⟨109992, by decide⟩]) unmarked_context_12_6982_109993 node_context_12_6982_109993
  intro a
  fin_cases a
  · exact context_13_27928_3444
  · exact context_13_27929_109911
  · exact context_13_27930_109977
  · exact context_13_27931_109992

theorem selected_cut_03512 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 27932) = some ⟨13, 1, 0, 3444, 27932, 1, 16384⟩ := by
  decide +kernel

theorem context_13_27932_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27932 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 27932 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 27932, 1, 16384⟩
    (by decide) selected_cut_03512

theorem selected_cut_03513 : selected 8 ⟨110067, by decide⟩
    (prefixPartial 13 27933) = some ⟨13, 2, 0, 110067, 27933, 3621, 16384⟩ := by
  decide +kernel

theorem context_13_27933_110067 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27933 ⟨110067, by decide⟩ :=
  accepted_of_selected 13 27933 ⟨110067, by decide⟩ ⟨13, 2, 0, 110067, 27933, 3621, 16384⟩
    (by decide) selected_cut_03513

theorem selected_cut_03514 : selected 8 ⟨110124, by decide⟩
    (prefixPartial 13 27934) = some ⟨13, 2, 0, 110124, 27934, 3109, 16384⟩ := by
  decide +kernel

theorem context_13_27934_110124 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27934 ⟨110124, by decide⟩ :=
  accepted_of_selected 13 27934 ⟨110124, by decide⟩ ⟨13, 2, 0, 110124, 27934, 3109, 16384⟩
    (by decide) selected_cut_03514

theorem selected_cut_03515 : selected 8 ⟨110135, by decide⟩
    (prefixPartial 13 27935) = some ⟨13, 2, 0, 110135, 27935, 1049, 16384⟩ := by
  decide +kernel

theorem context_13_27935_110135 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27935 ⟨110135, by decide⟩ :=
  accepted_of_selected 13 27935 ⟨110135, by decide⟩ ⟨13, 2, 0, 110135, 27935, 1049, 16384⟩
    (by decide) selected_cut_03515

theorem unmarked_context_12_6983_110136 : frontier 9 ⟨110136, by decide⟩
    (prefixCache 12 6983) (prefixPartial 12 6983) = false := by
  decide +kernel

theorem node_context_12_6983_110136 : EJMOriginalGlobalDAGData.nodes 9 ⟨110136, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨110067, by decide⟩,⟨110124, by decide⟩,⟨110135, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_6983_110136 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6983 ⟨110136, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 6983
    ⟨110136, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨110067, by decide⟩,⟨110124, by decide⟩,⟨110135, by decide⟩]) unmarked_context_12_6983_110136 node_context_12_6983_110136
  intro a
  fin_cases a
  · exact context_13_27932_3444
  · exact context_13_27933_110067
  · exact context_13_27934_110124
  · exact context_13_27935_110135

theorem unmarked_context_11_1745_110137 : frontier 10 ⟨110137, by decide⟩
    (prefixCache 11 1745) (prefixPartial 11 1745) = false := by
  decide +kernel

theorem node_context_11_1745_110137 : EJMOriginalGlobalDAGData.nodes 10 ⟨110137, by decide⟩ =
    .split (coordinate 11) (![⟨109703, by decide⟩,⟨109823, by decide⟩,⟨109993, by decide⟩,⟨110136, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1745_110137 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1745 ⟨110137, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1745
    ⟨110137, by decide⟩ (by decide) (![⟨109703, by decide⟩,⟨109823, by decide⟩,⟨109993, by decide⟩,⟨110136, by decide⟩]) unmarked_context_11_1745_110137 node_context_11_1745_110137
  intro a
  fin_cases a
  · exact context_12_6980_109703
  · exact context_12_6981_109823
  · exact context_12_6982_109993
  · exact context_12_6983_110136

theorem selected_cut_03516 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 27936) = some ⟨13, 1, 0, 3444, 27936, 1, 16384⟩ := by
  decide +kernel

theorem context_13_27936_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27936 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 27936 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 27936, 1, 16384⟩
    (by decide) selected_cut_03516

theorem selected_cut_03517 : selected 8 ⟨110180, by decide⟩
    (prefixPartial 13 27937) = some ⟨13, 2, 0, 110180, 27937, 2605, 16384⟩ := by
  decide +kernel

theorem context_13_27937_110180 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27937 ⟨110180, by decide⟩ :=
  accepted_of_selected 13 27937 ⟨110180, by decide⟩ ⟨13, 2, 0, 110180, 27937, 2605, 16384⟩
    (by decide) selected_cut_03517

theorem selected_cut_03518 : selected 8 ⟨110211, by decide⟩
    (prefixPartial 13 27938) = some ⟨13, 2, 0, 110211, 27938, 2269, 16384⟩ := by
  decide +kernel

theorem context_13_27938_110211 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27938 ⟨110211, by decide⟩ :=
  accepted_of_selected 13 27938 ⟨110211, by decide⟩ ⟨13, 2, 0, 110211, 27938, 2269, 16384⟩
    (by decide) selected_cut_03518

theorem selected_cut_03519 : selected 8 ⟨110224, by decide⟩
    (prefixPartial 13 27939) = some ⟨13, 2, 0, 110224, 27939, 1045, 16384⟩ := by
  decide +kernel

theorem context_13_27939_110224 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27939 ⟨110224, by decide⟩ :=
  accepted_of_selected 13 27939 ⟨110224, by decide⟩ ⟨13, 2, 0, 110224, 27939, 1045, 16384⟩
    (by decide) selected_cut_03519

theorem unmarked_context_12_6984_110225 : frontier 9 ⟨110225, by decide⟩
    (prefixCache 12 6984) (prefixPartial 12 6984) = false := by
  decide +kernel

theorem node_context_12_6984_110225 : EJMOriginalGlobalDAGData.nodes 9 ⟨110225, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨110180, by decide⟩,⟨110211, by decide⟩,⟨110224, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_6984_110225 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6984 ⟨110225, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 6984
    ⟨110225, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨110180, by decide⟩,⟨110211, by decide⟩,⟨110224, by decide⟩]) unmarked_context_12_6984_110225 node_context_12_6984_110225
  intro a
  fin_cases a
  · exact context_13_27936_3444
  · exact context_13_27937_110180
  · exact context_13_27938_110211
  · exact context_13_27939_110224

theorem selected_cut_03520 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 27940) = some ⟨13, 1, 0, 3444, 27940, 1, 16384⟩ := by
  decide +kernel

theorem context_13_27940_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27940 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 27940 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 27940, 1, 16384⟩
    (by decide) selected_cut_03520

theorem selected_cut_03521 : selected 8 ⟨110261, by decide⟩
    (prefixPartial 13 27941) = some ⟨13, 2, 0, 110261, 27941, 2617, 16384⟩ := by
  decide +kernel

theorem context_13_27941_110261 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27941 ⟨110261, by decide⟩ :=
  accepted_of_selected 13 27941 ⟨110261, by decide⟩ ⟨13, 2, 0, 110261, 27941, 2617, 16384⟩
    (by decide) selected_cut_03521

theorem selected_cut_03522 : selected 8 ⟨110290, by decide⟩
    (prefixPartial 13 27942) = some ⟨13, 2, 0, 110290, 27942, 2425, 16384⟩ := by
  decide +kernel

theorem context_13_27942_110290 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27942 ⟨110290, by decide⟩ :=
  accepted_of_selected 13 27942 ⟨110290, by decide⟩ ⟨13, 2, 0, 110290, 27942, 2425, 16384⟩
    (by decide) selected_cut_03522

theorem selected_cut_03523 : selected 8 ⟨110298, by decide⟩
    (prefixPartial 13 27943) = some ⟨13, 2, 0, 110298, 27943, 1177, 16384⟩ := by
  decide +kernel

theorem context_13_27943_110298 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27943 ⟨110298, by decide⟩ :=
  accepted_of_selected 13 27943 ⟨110298, by decide⟩ ⟨13, 2, 0, 110298, 27943, 1177, 16384⟩
    (by decide) selected_cut_03523

theorem unmarked_context_12_6985_110299 : frontier 9 ⟨110299, by decide⟩
    (prefixCache 12 6985) (prefixPartial 12 6985) = false := by
  decide +kernel

theorem node_context_12_6985_110299 : EJMOriginalGlobalDAGData.nodes 9 ⟨110299, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨110261, by decide⟩,⟨110290, by decide⟩,⟨110298, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_6985_110299 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6985 ⟨110299, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 6985
    ⟨110299, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨110261, by decide⟩,⟨110290, by decide⟩,⟨110298, by decide⟩]) unmarked_context_12_6985_110299 node_context_12_6985_110299
  intro a
  fin_cases a
  · exact context_13_27940_3444
  · exact context_13_27941_110261
  · exact context_13_27942_110290
  · exact context_13_27943_110298

theorem selected_cut_03524 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 27944) = some ⟨13, 1, 0, 3444, 27944, 1, 16384⟩ := by
  decide +kernel

theorem context_13_27944_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27944 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 27944 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 27944, 1, 16384⟩
    (by decide) selected_cut_03524

theorem selected_cut_03525 : selected 8 ⟨110344, by decide⟩
    (prefixPartial 13 27945) = some ⟨13, 2, 0, 110344, 27945, 2601, 16384⟩ := by
  decide +kernel

theorem context_13_27945_110344 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27945 ⟨110344, by decide⟩ :=
  accepted_of_selected 13 27945 ⟨110344, by decide⟩ ⟨13, 2, 0, 110344, 27945, 2601, 16384⟩
    (by decide) selected_cut_03525

theorem selected_cut_03526 : selected 8 ⟨110375, by decide⟩
    (prefixPartial 13 27946) = some ⟨13, 2, 0, 110375, 27946, 2401, 16384⟩ := by
  decide +kernel

theorem context_13_27946_110375 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27946 ⟨110375, by decide⟩ :=
  accepted_of_selected 13 27946 ⟨110375, by decide⟩ ⟨13, 2, 0, 110375, 27946, 2401, 16384⟩
    (by decide) selected_cut_03526

theorem selected_cut_03527 : selected 8 ⟨110384, by decide⟩
    (prefixPartial 13 27947) = some ⟨13, 2, 0, 110384, 27947, 981, 16384⟩ := by
  decide +kernel

theorem context_13_27947_110384 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27947 ⟨110384, by decide⟩ :=
  accepted_of_selected 13 27947 ⟨110384, by decide⟩ ⟨13, 2, 0, 110384, 27947, 981, 16384⟩
    (by decide) selected_cut_03527

theorem unmarked_context_12_6986_110385 : frontier 9 ⟨110385, by decide⟩
    (prefixCache 12 6986) (prefixPartial 12 6986) = false := by
  decide +kernel

theorem node_context_12_6986_110385 : EJMOriginalGlobalDAGData.nodes 9 ⟨110385, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨110344, by decide⟩,⟨110375, by decide⟩,⟨110384, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_6986_110385 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6986 ⟨110385, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 6986
    ⟨110385, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨110344, by decide⟩,⟨110375, by decide⟩,⟨110384, by decide⟩]) unmarked_context_12_6986_110385 node_context_12_6986_110385
  intro a
  fin_cases a
  · exact context_13_27944_3444
  · exact context_13_27945_110344
  · exact context_13_27946_110375
  · exact context_13_27947_110384

theorem selected_cut_03528 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 27948) = some ⟨13, 1, 0, 3444, 27948, 1, 16384⟩ := by
  decide +kernel

theorem context_13_27948_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27948 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 27948 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 27948, 1, 16384⟩
    (by decide) selected_cut_03528

theorem selected_cut_03529 : selected 8 ⟨110421, by decide⟩
    (prefixPartial 13 27949) = some ⟨13, 2, 0, 110421, 27949, 2481, 16384⟩ := by
  decide +kernel

theorem context_13_27949_110421 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27949 ⟨110421, by decide⟩ :=
  accepted_of_selected 13 27949 ⟨110421, by decide⟩ ⟨13, 2, 0, 110421, 27949, 2481, 16384⟩
    (by decide) selected_cut_03529

theorem selected_cut_03530 : selected 8 ⟨110449, by decide⟩
    (prefixPartial 13 27950) = some ⟨13, 2, 0, 110449, 27950, 2397, 16384⟩ := by
  decide +kernel

theorem context_13_27950_110449 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27950 ⟨110449, by decide⟩ :=
  accepted_of_selected 13 27950 ⟨110449, by decide⟩ ⟨13, 2, 0, 110449, 27950, 2397, 16384⟩
    (by decide) selected_cut_03530

theorem selected_cut_03531 : selected 8 ⟨110456, by decide⟩
    (prefixPartial 13 27951) = some ⟨13, 2, 0, 110456, 27951, 1041, 16384⟩ := by
  decide +kernel

theorem context_13_27951_110456 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27951 ⟨110456, by decide⟩ :=
  accepted_of_selected 13 27951 ⟨110456, by decide⟩ ⟨13, 2, 0, 110456, 27951, 1041, 16384⟩
    (by decide) selected_cut_03531

theorem unmarked_context_12_6987_110457 : frontier 9 ⟨110457, by decide⟩
    (prefixCache 12 6987) (prefixPartial 12 6987) = false := by
  decide +kernel

theorem node_context_12_6987_110457 : EJMOriginalGlobalDAGData.nodes 9 ⟨110457, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨110421, by decide⟩,⟨110449, by decide⟩,⟨110456, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_6987_110457 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6987 ⟨110457, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 6987
    ⟨110457, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨110421, by decide⟩,⟨110449, by decide⟩,⟨110456, by decide⟩]) unmarked_context_12_6987_110457 node_context_12_6987_110457
  intro a
  fin_cases a
  · exact context_13_27948_3444
  · exact context_13_27949_110421
  · exact context_13_27950_110449
  · exact context_13_27951_110456

theorem unmarked_context_11_1746_110458 : frontier 10 ⟨110458, by decide⟩
    (prefixCache 11 1746) (prefixPartial 11 1746) = false := by
  decide +kernel

theorem node_context_11_1746_110458 : EJMOriginalGlobalDAGData.nodes 10 ⟨110458, by decide⟩ =
    .split (coordinate 11) (![⟨110225, by decide⟩,⟨110299, by decide⟩,⟨110385, by decide⟩,⟨110457, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1746_110458 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1746 ⟨110458, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1746
    ⟨110458, by decide⟩ (by decide) (![⟨110225, by decide⟩,⟨110299, by decide⟩,⟨110385, by decide⟩,⟨110457, by decide⟩]) unmarked_context_11_1746_110458 node_context_11_1746_110458
  intro a
  fin_cases a
  · exact context_12_6984_110225
  · exact context_12_6985_110299
  · exact context_12_6986_110385
  · exact context_12_6987_110457

theorem selected_cut_03532 : selected 9 ⟨4596, by decide⟩
    (prefixPartial 12 6988) = some ⟨12, 1, 0, 4596, 6988, 1, 65536⟩ := by
  decide +kernel

theorem context_12_6988_4596 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6988 ⟨4596, by decide⟩ :=
  accepted_of_selected 12 6988 ⟨4596, by decide⟩ ⟨12, 1, 0, 4596, 6988, 1, 65536⟩
    (by decide) selected_cut_03532

theorem selected_cut_03533 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 27956) = some ⟨13, 1, 0, 3444, 27956, 1, 16384⟩ := by
  decide +kernel

theorem context_13_27956_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27956 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 27956 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 27956, 1, 16384⟩
    (by decide) selected_cut_03533

theorem selected_cut_03534 : selected 8 ⟨110501, by decide⟩
    (prefixPartial 13 27957) = some ⟨13, 2, 0, 110501, 27957, 2401, 16384⟩ := by
  decide +kernel

theorem context_13_27957_110501 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27957 ⟨110501, by decide⟩ :=
  accepted_of_selected 13 27957 ⟨110501, by decide⟩ ⟨13, 2, 0, 110501, 27957, 2401, 16384⟩
    (by decide) selected_cut_03534

theorem selected_cut_03535 : selected 8 ⟨110531, by decide⟩
    (prefixPartial 13 27958) = some ⟨13, 2, 0, 110531, 27958, 2653, 16384⟩ := by
  decide +kernel

theorem context_13_27958_110531 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27958 ⟨110531, by decide⟩ :=
  accepted_of_selected 13 27958 ⟨110531, by decide⟩ ⟨13, 2, 0, 110531, 27958, 2653, 16384⟩
    (by decide) selected_cut_03535

theorem selected_cut_03536 : selected 8 ⟨110542, by decide⟩
    (prefixPartial 13 27959) = some ⟨13, 2, 0, 110542, 27959, 1157, 16384⟩ := by
  decide +kernel

theorem context_13_27959_110542 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27959 ⟨110542, by decide⟩ :=
  accepted_of_selected 13 27959 ⟨110542, by decide⟩ ⟨13, 2, 0, 110542, 27959, 1157, 16384⟩
    (by decide) selected_cut_03536

theorem unmarked_context_12_6989_110543 : frontier 9 ⟨110543, by decide⟩
    (prefixCache 12 6989) (prefixPartial 12 6989) = false := by
  decide +kernel

theorem node_context_12_6989_110543 : EJMOriginalGlobalDAGData.nodes 9 ⟨110543, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨110501, by decide⟩,⟨110531, by decide⟩,⟨110542, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_6989_110543 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6989 ⟨110543, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 6989
    ⟨110543, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨110501, by decide⟩,⟨110531, by decide⟩,⟨110542, by decide⟩]) unmarked_context_12_6989_110543 node_context_12_6989_110543
  intro a
  fin_cases a
  · exact context_13_27956_3444
  · exact context_13_27957_110501
  · exact context_13_27958_110531
  · exact context_13_27959_110542

theorem selected_cut_03537 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 27960) = some ⟨13, 1, 0, 3444, 27960, 1, 16384⟩ := by
  decide +kernel

theorem context_13_27960_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27960 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 27960 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 27960, 1, 16384⟩
    (by decide) selected_cut_03537

theorem selected_cut_03538 : selected 8 ⟨110604, by decide⟩
    (prefixPartial 13 27961) = some ⟨13, 2, 0, 110604, 27961, 2821, 16384⟩ := by
  decide +kernel

theorem context_13_27961_110604 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27961 ⟨110604, by decide⟩ :=
  accepted_of_selected 13 27961 ⟨110604, by decide⟩ ⟨13, 2, 0, 110604, 27961, 2821, 16384⟩
    (by decide) selected_cut_03538

theorem selected_cut_03539 : selected 8 ⟨110643, by decide⟩
    (prefixPartial 13 27962) = some ⟨13, 2, 0, 110643, 27962, 2565, 16384⟩ := by
  decide +kernel

theorem context_13_27962_110643 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27962 ⟨110643, by decide⟩ :=
  accepted_of_selected 13 27962 ⟨110643, by decide⟩ ⟨13, 2, 0, 110643, 27962, 2565, 16384⟩
    (by decide) selected_cut_03539

theorem selected_cut_03540 : selected 8 ⟨110655, by decide⟩
    (prefixPartial 13 27963) = some ⟨13, 2, 0, 110655, 27963, 1069, 16384⟩ := by
  decide +kernel

theorem context_13_27963_110655 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27963 ⟨110655, by decide⟩ :=
  accepted_of_selected 13 27963 ⟨110655, by decide⟩ ⟨13, 2, 0, 110655, 27963, 1069, 16384⟩
    (by decide) selected_cut_03540

theorem unmarked_context_12_6990_110656 : frontier 9 ⟨110656, by decide⟩
    (prefixCache 12 6990) (prefixPartial 12 6990) = false := by
  decide +kernel

theorem node_context_12_6990_110656 : EJMOriginalGlobalDAGData.nodes 9 ⟨110656, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨110604, by decide⟩,⟨110643, by decide⟩,⟨110655, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_6990_110656 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6990 ⟨110656, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 6990
    ⟨110656, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨110604, by decide⟩,⟨110643, by decide⟩,⟨110655, by decide⟩]) unmarked_context_12_6990_110656 node_context_12_6990_110656
  intro a
  fin_cases a
  · exact context_13_27960_3444
  · exact context_13_27961_110604
  · exact context_13_27962_110643
  · exact context_13_27963_110655

theorem selected_cut_03541 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 27964) = some ⟨13, 1, 0, 3444, 27964, 1, 16384⟩ := by
  decide +kernel

theorem context_13_27964_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27964 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 27964 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 27964, 1, 16384⟩
    (by decide) selected_cut_03541

theorem selected_cut_03542 : selected 8 ⟨110744, by decide⟩
    (prefixPartial 13 27965) = some ⟨13, 2, 0, 110744, 27965, 3985, 16384⟩ := by
  decide +kernel

theorem context_13_27965_110744 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27965 ⟨110744, by decide⟩ :=
  accepted_of_selected 13 27965 ⟨110744, by decide⟩ ⟨13, 2, 0, 110744, 27965, 3985, 16384⟩
    (by decide) selected_cut_03542

theorem selected_cut_03543 : selected 7 ⟨110775, by decide⟩
    (prefixPartial 14 111864) = some ⟨14, 2, 0, 110775, 111864, 1257, 4096⟩ := by
  decide +kernel

theorem context_14_111864_110775 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 111864 ⟨110775, by decide⟩ :=
  accepted_of_selected 14 111864 ⟨110775, by decide⟩ ⟨14, 2, 0, 110775, 111864, 1257, 4096⟩
    (by decide) selected_cut_03543

theorem selected_cut_03544 : selected 7 ⟨110803, by decide⟩
    (prefixPartial 14 111865) = some ⟨14, 2, 0, 110803, 111865, 1193, 4096⟩ := by
  decide +kernel

theorem context_14_111865_110803 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 111865 ⟨110803, by decide⟩ :=
  accepted_of_selected 14 111865 ⟨110803, by decide⟩ ⟨14, 2, 0, 110803, 111865, 1193, 4096⟩
    (by decide) selected_cut_03544

theorem selected_cut_03545 : selected 7 ⟨110826, by decide⟩
    (prefixPartial 14 111866) = some ⟨14, 2, 0, 110826, 111866, 1093, 4096⟩ := by
  decide +kernel

theorem context_14_111866_110826 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 111866 ⟨110826, by decide⟩ :=
  accepted_of_selected 14 111866 ⟨110826, by decide⟩ ⟨14, 2, 0, 110826, 111866, 1093, 4096⟩
    (by decide) selected_cut_03545

theorem selected_cut_03546 : selected 7 ⟨110850, by decide⟩
    (prefixPartial 14 111867) = some ⟨14, 2, 0, 110850, 111867, 1009, 4096⟩ := by
  decide +kernel

theorem context_14_111867_110850 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 111867 ⟨110850, by decide⟩ :=
  accepted_of_selected 14 111867 ⟨110850, by decide⟩ ⟨14, 2, 0, 110850, 111867, 1009, 4096⟩
    (by decide) selected_cut_03546

theorem unmarked_context_13_27966_110851 : frontier 8 ⟨110851, by decide⟩
    (prefixCache 13 27966) (prefixPartial 13 27966) = false := by
  decide +kernel

theorem node_context_13_27966_110851 : EJMOriginalGlobalDAGData.nodes 8 ⟨110851, by decide⟩ =
    .split (coordinate 13) (![⟨110775, by decide⟩,⟨110803, by decide⟩,⟨110826, by decide⟩,⟨110850, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_27966_110851 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27966 ⟨110851, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 27966
    ⟨110851, by decide⟩ (by decide) (![⟨110775, by decide⟩,⟨110803, by decide⟩,⟨110826, by decide⟩,⟨110850, by decide⟩]) unmarked_context_13_27966_110851 node_context_13_27966_110851
  intro a
  fin_cases a
  · exact context_14_111864_110775
  · exact context_14_111865_110803
  · exact context_14_111866_110826
  · exact context_14_111867_110850

theorem selected_cut_03547 : selected 8 ⟨110899, by decide⟩
    (prefixPartial 13 27967) = some ⟨13, 2, 0, 110899, 27967, 1721, 16384⟩ := by
  decide +kernel

theorem context_13_27967_110899 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27967 ⟨110899, by decide⟩ :=
  accepted_of_selected 13 27967 ⟨110899, by decide⟩ ⟨13, 2, 0, 110899, 27967, 1721, 16384⟩
    (by decide) selected_cut_03547

theorem unmarked_context_12_6991_110900 : frontier 9 ⟨110900, by decide⟩
    (prefixCache 12 6991) (prefixPartial 12 6991) = false := by
  decide +kernel

theorem node_context_12_6991_110900 : EJMOriginalGlobalDAGData.nodes 9 ⟨110900, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨110744, by decide⟩,⟨110851, by decide⟩,⟨110899, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_6991_110900 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6991 ⟨110900, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 6991
    ⟨110900, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨110744, by decide⟩,⟨110851, by decide⟩,⟨110899, by decide⟩]) unmarked_context_12_6991_110900 node_context_12_6991_110900
  intro a
  fin_cases a
  · exact context_13_27964_3444
  · exact context_13_27965_110744
  · exact context_13_27966_110851
  · exact context_13_27967_110899

theorem unmarked_context_11_1747_110901 : frontier 10 ⟨110901, by decide⟩
    (prefixCache 11 1747) (prefixPartial 11 1747) = false := by
  decide +kernel

theorem node_context_11_1747_110901 : EJMOriginalGlobalDAGData.nodes 10 ⟨110901, by decide⟩ =
    .split (coordinate 11) (![⟨4596, by decide⟩,⟨110543, by decide⟩,⟨110656, by decide⟩,⟨110900, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1747_110901 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1747 ⟨110901, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1747
    ⟨110901, by decide⟩ (by decide) (![⟨4596, by decide⟩,⟨110543, by decide⟩,⟨110656, by decide⟩,⟨110900, by decide⟩]) unmarked_context_11_1747_110901 node_context_11_1747_110901
  intro a
  fin_cases a
  · exact context_12_6988_4596
  · exact context_12_6989_110543
  · exact context_12_6990_110656
  · exact context_12_6991_110900

theorem unmarked_context_10_436_110902 : frontier 11 ⟨110902, by decide⟩
    (prefixCache 10 436) (prefixPartial 10 436) = false := by
  decide +kernel

theorem node_context_10_436_110902 : EJMOriginalGlobalDAGData.nodes 11 ⟨110902, by decide⟩ =
    .split (coordinate 10) (![⟨109584, by decide⟩,⟨110137, by decide⟩,⟨110458, by decide⟩,⟨110901, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_436_110902 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 436 ⟨110902, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 436
    ⟨110902, by decide⟩ (by decide) (![⟨109584, by decide⟩,⟨110137, by decide⟩,⟨110458, by decide⟩,⟨110901, by decide⟩]) unmarked_context_10_436_110902 node_context_10_436_110902
  intro a
  fin_cases a
  · exact context_11_1744_109584
  · exact context_11_1745_110137
  · exact context_11_1746_110458
  · exact context_11_1747_110901

theorem selected_cut_03548 : selected 9 ⟨106538, by decide⟩
    (prefixPartial 12 6992) = some ⟨12, 1, 0, 106538, 6992, 1, 65536⟩ := by
  decide +kernel

theorem context_12_6992_106538 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6992 ⟨106538, by decide⟩ :=
  accepted_of_selected 12 6992 ⟨106538, by decide⟩ ⟨12, 1, 0, 106538, 6992, 1, 65536⟩
    (by decide) selected_cut_03548

theorem selected_cut_03549 : selected 9 ⟨110998, by decide⟩
    (prefixPartial 12 6993) = some ⟨12, 2, 0, 110998, 6993, 3385, 65536⟩ := by
  decide +kernel

theorem context_12_6993_110998 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6993 ⟨110998, by decide⟩ :=
  accepted_of_selected 12 6993 ⟨110998, by decide⟩ ⟨12, 2, 0, 110998, 6993, 3385, 65536⟩
    (by decide) selected_cut_03549

theorem selected_cut_03550 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 27976) = some ⟨13, 1, 0, 3444, 27976, 1, 16384⟩ := by
  decide +kernel

theorem context_13_27976_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27976 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 27976 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 27976, 1, 16384⟩
    (by decide) selected_cut_03550

theorem selected_cut_03551 : selected 8 ⟨111066, by decide⟩
    (prefixPartial 13 27977) = some ⟨13, 2, 0, 111066, 27977, 2865, 16384⟩ := by
  decide +kernel

theorem context_13_27977_111066 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27977 ⟨111066, by decide⟩ :=
  accepted_of_selected 13 27977 ⟨111066, by decide⟩ ⟨13, 2, 0, 111066, 27977, 2865, 16384⟩
    (by decide) selected_cut_03551

theorem selected_cut_03552 : selected 8 ⟨111102, by decide⟩
    (prefixPartial 13 27978) = some ⟨13, 2, 0, 111102, 27978, 2325, 16384⟩ := by
  decide +kernel

theorem context_13_27978_111102 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27978 ⟨111102, by decide⟩ :=
  accepted_of_selected 13 27978 ⟨111102, by decide⟩ ⟨13, 2, 0, 111102, 27978, 2325, 16384⟩
    (by decide) selected_cut_03552

theorem selected_cut_03553 : selected 8 ⟨111108, by decide⟩
    (prefixPartial 13 27979) = some ⟨13, 2, 0, 111108, 27979, 905, 16384⟩ := by
  decide +kernel

theorem context_13_27979_111108 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27979 ⟨111108, by decide⟩ :=
  accepted_of_selected 13 27979 ⟨111108, by decide⟩ ⟨13, 2, 0, 111108, 27979, 905, 16384⟩
    (by decide) selected_cut_03553

theorem unmarked_context_12_6994_111109 : frontier 9 ⟨111109, by decide⟩
    (prefixCache 12 6994) (prefixPartial 12 6994) = false := by
  decide +kernel

theorem node_context_12_6994_111109 : EJMOriginalGlobalDAGData.nodes 9 ⟨111109, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨111066, by decide⟩,⟨111102, by decide⟩,⟨111108, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_6994_111109 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6994 ⟨111109, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 6994
    ⟨111109, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨111066, by decide⟩,⟨111102, by decide⟩,⟨111108, by decide⟩]) unmarked_context_12_6994_111109 node_context_12_6994_111109
  intro a
  fin_cases a
  · exact context_13_27976_3444
  · exact context_13_27977_111066
  · exact context_13_27978_111102
  · exact context_13_27979_111108

theorem selected_cut_03554 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 27980) = some ⟨13, 1, 0, 3444, 27980, 1, 16384⟩ := by
  decide +kernel

theorem context_13_27980_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27980 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 27980 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 27980, 1, 16384⟩
    (by decide) selected_cut_03554

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
