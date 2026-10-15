/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover412
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_39651 : selected 10 ⟨1076019, by decide⟩
    (prefixPartial 11 76914) = some ⟨11, 2, 0, 1076019, 76914, 1849, 262144⟩ := by
  decide +kernel

theorem context_11_76914_1076019 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76914 ⟨1076019, by decide⟩ :=
  accepted_of_selected 11 76914 ⟨1076019, by decide⟩ ⟨11, 2, 0, 1076019, 76914, 1849, 262144⟩
    (by decide) selected_cut_39651

theorem selected_cut_39652 : selected 10 ⟨1076047, by decide⟩
    (prefixPartial 11 76915) = some ⟨11, 2, 0, 1076047, 76915, 2009, 262144⟩ := by
  decide +kernel

theorem context_11_76915_1076047 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76915 ⟨1076047, by decide⟩ :=
  accepted_of_selected 11 76915 ⟨1076047, by decide⟩ ⟨11, 2, 0, 1076047, 76915, 2009, 262144⟩
    (by decide) selected_cut_39652

theorem unmarked_context_10_19228_1076048 : frontier 11 ⟨1076048, by decide⟩
    (prefixCache 10 19228) (prefixPartial 10 19228) = false := by
  decide +kernel

theorem node_context_10_19228_1076048 : EJMOriginalGlobalDAGData.nodes 11 ⟨1076048, by decide⟩ =
    .split (coordinate 10) (![⟨907917, by decide⟩,⟨1076002, by decide⟩,⟨1076019, by decide⟩,⟨1076047, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_19228_1076048 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19228 ⟨1076048, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 19228
    ⟨1076048, by decide⟩ (by decide) (![⟨907917, by decide⟩,⟨1076002, by decide⟩,⟨1076019, by decide⟩,⟨1076047, by decide⟩]) unmarked_context_10_19228_1076048 node_context_10_19228_1076048
  intro a
  fin_cases a
  · exact context_11_76912_907917
  · exact context_11_76913_1076002
  · exact context_11_76914_1076019
  · exact context_11_76915_1076047

theorem selected_cut_39653 : selected 10 ⟨1076068, by decide⟩
    (prefixPartial 11 76916) = some ⟨11, 2, 0, 1076068, 76916, 1481, 262144⟩ := by
  decide +kernel

theorem context_11_76916_1076068 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76916 ⟨1076068, by decide⟩ :=
  accepted_of_selected 11 76916 ⟨1076068, by decide⟩ ⟨11, 2, 0, 1076068, 76916, 1481, 262144⟩
    (by decide) selected_cut_39653

theorem selected_cut_39654 : selected 10 ⟨1076079, by decide⟩
    (prefixPartial 11 76917) = some ⟨11, 2, 0, 1076079, 76917, 961, 262144⟩ := by
  decide +kernel

theorem context_11_76917_1076079 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76917 ⟨1076079, by decide⟩ :=
  accepted_of_selected 11 76917 ⟨1076079, by decide⟩ ⟨11, 2, 0, 1076079, 76917, 961, 262144⟩
    (by decide) selected_cut_39654

theorem selected_cut_39655 : selected 10 ⟨1076092, by decide⟩
    (prefixPartial 11 76918) = some ⟨11, 2, 0, 1076092, 76918, 1141, 262144⟩ := by
  decide +kernel

theorem context_11_76918_1076092 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76918 ⟨1076092, by decide⟩ :=
  accepted_of_selected 11 76918 ⟨1076092, by decide⟩ ⟨11, 2, 0, 1076092, 76918, 1141, 262144⟩
    (by decide) selected_cut_39655

theorem selected_cut_39656 : selected 10 ⟨1076115, by decide⟩
    (prefixPartial 11 76919) = some ⟨11, 2, 0, 1076115, 76919, 901, 262144⟩ := by
  decide +kernel

theorem context_11_76919_1076115 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76919 ⟨1076115, by decide⟩ :=
  accepted_of_selected 11 76919 ⟨1076115, by decide⟩ ⟨11, 2, 0, 1076115, 76919, 901, 262144⟩
    (by decide) selected_cut_39656

theorem unmarked_context_10_19229_1076116 : frontier 11 ⟨1076116, by decide⟩
    (prefixCache 10 19229) (prefixPartial 10 19229) = false := by
  decide +kernel

theorem node_context_10_19229_1076116 : EJMOriginalGlobalDAGData.nodes 11 ⟨1076116, by decide⟩ =
    .split (coordinate 10) (![⟨1076068, by decide⟩,⟨1076079, by decide⟩,⟨1076092, by decide⟩,⟨1076115, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_19229_1076116 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19229 ⟨1076116, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 19229
    ⟨1076116, by decide⟩ (by decide) (![⟨1076068, by decide⟩,⟨1076079, by decide⟩,⟨1076092, by decide⟩,⟨1076115, by decide⟩]) unmarked_context_10_19229_1076116 node_context_10_19229_1076116
  intro a
  fin_cases a
  · exact context_11_76916_1076068
  · exact context_11_76917_1076079
  · exact context_11_76918_1076092
  · exact context_11_76919_1076115

theorem selected_cut_39657 : selected 11 ⟨1076167, by decide⟩
    (prefixPartial 10 19230) = some ⟨10, 2, 0, 1076167, 19230, 2457, 1048576⟩ := by
  decide +kernel

theorem context_10_19230_1076167 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19230 ⟨1076167, by decide⟩ :=
  accepted_of_selected 10 19230 ⟨1076167, by decide⟩ ⟨10, 2, 0, 1076167, 19230, 2457, 1048576⟩
    (by decide) selected_cut_39657

theorem selected_cut_39658 : selected 11 ⟨1076198, by decide⟩
    (prefixPartial 10 19231) = some ⟨10, 2, 0, 1076198, 19231, 661, 1048576⟩ := by
  decide +kernel

theorem context_10_19231_1076198 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19231 ⟨1076198, by decide⟩ :=
  accepted_of_selected 10 19231 ⟨1076198, by decide⟩ ⟨10, 2, 0, 1076198, 19231, 661, 1048576⟩
    (by decide) selected_cut_39658

theorem unmarked_context_9_4807_1076199 : frontier 12 ⟨1076199, by decide⟩
    (prefixCache 9 4807) (prefixPartial 9 4807) = false := by
  decide +kernel

theorem node_context_9_4807_1076199 : EJMOriginalGlobalDAGData.nodes 12 ⟨1076199, by decide⟩ =
    .split (coordinate 9) (![⟨1076048, by decide⟩,⟨1076116, by decide⟩,⟨1076167, by decide⟩,⟨1076198, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4807_1076199 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4807 ⟨1076199, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4807
    ⟨1076199, by decide⟩ (by decide) (![⟨1076048, by decide⟩,⟨1076116, by decide⟩,⟨1076167, by decide⟩,⟨1076198, by decide⟩]) unmarked_context_9_4807_1076199 node_context_9_4807_1076199
  intro a
  fin_cases a
  · exact context_10_19228_1076048
  · exact context_10_19229_1076116
  · exact context_10_19230_1076167
  · exact context_10_19231_1076198

theorem unmarked_context_8_1201_1076200 : frontier 13 ⟨1076200, by decide⟩
    (prefixCache 8 1201) (prefixPartial 8 1201) = false := by
  decide +kernel

theorem node_context_8_1201_1076200 : EJMOriginalGlobalDAGData.nodes 13 ⟨1076200, by decide⟩ =
    .split (coordinate 8) (![⟨1074551, by decide⟩,⟨1075550, by decide⟩,⟨1075981, by decide⟩,⟨1076199, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1201_1076200 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1201 ⟨1076200, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1201
    ⟨1076200, by decide⟩ (by decide) (![⟨1074551, by decide⟩,⟨1075550, by decide⟩,⟨1075981, by decide⟩,⟨1076199, by decide⟩]) unmarked_context_8_1201_1076200 node_context_8_1201_1076200
  intro a
  fin_cases a
  · exact context_9_4804_1074551
  · exact context_9_4805_1075550
  · exact context_9_4806_1075981
  · exact context_9_4807_1076199

theorem selected_cut_39659 : selected 10 ⟨167448, by decide⟩
    (prefixPartial 11 76928) = some ⟨11, 1, 0, 167448, 76928, 1, 262144⟩ := by
  decide +kernel

theorem context_11_76928_167448 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76928 ⟨167448, by decide⟩ :=
  accepted_of_selected 11 76928 ⟨167448, by decide⟩ ⟨11, 1, 0, 167448, 76928, 1, 262144⟩
    (by decide) selected_cut_39659

theorem selected_cut_39660 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 307716) = some ⟨12, 1, 0, 34034, 307716, 1, 65536⟩ := by
  decide +kernel

theorem context_12_307716_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307716 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 307716 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 307716, 1, 65536⟩
    (by decide) selected_cut_39660

theorem selected_cut_39661 : selected 8 ⟨1076242, by decide⟩
    (prefixPartial 13 1230868) = some ⟨13, 2, 0, 1076242, 1230868, 2381, 16384⟩ := by
  decide +kernel

theorem context_13_1230868_1076242 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1230868 ⟨1076242, by decide⟩ :=
  accepted_of_selected 13 1230868 ⟨1076242, by decide⟩ ⟨13, 2, 0, 1076242, 1230868, 2381, 16384⟩
    (by decide) selected_cut_39661

theorem selected_cut_39662 : selected 8 ⟨1076258, by decide⟩
    (prefixPartial 13 1230869) = some ⟨13, 2, 0, 1076258, 1230869, 1217, 16384⟩ := by
  decide +kernel

theorem context_13_1230869_1076258 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1230869 ⟨1076258, by decide⟩ :=
  accepted_of_selected 13 1230869 ⟨1076258, by decide⟩ ⟨13, 2, 0, 1076258, 1230869, 1217, 16384⟩
    (by decide) selected_cut_39662

theorem selected_cut_39663 : selected 8 ⟨1076274, by decide⟩
    (prefixPartial 13 1230870) = some ⟨13, 2, 0, 1076274, 1230870, 929, 16384⟩ := by
  decide +kernel

theorem context_13_1230870_1076274 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1230870 ⟨1076274, by decide⟩ :=
  accepted_of_selected 13 1230870 ⟨1076274, by decide⟩ ⟨13, 2, 0, 1076274, 1230870, 929, 16384⟩
    (by decide) selected_cut_39663

theorem selected_cut_39664 : selected 8 ⟨1076282, by decide⟩
    (prefixPartial 13 1230871) = some ⟨13, 2, 0, 1076282, 1230871, 589, 16384⟩ := by
  decide +kernel

theorem context_13_1230871_1076282 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1230871 ⟨1076282, by decide⟩ :=
  accepted_of_selected 13 1230871 ⟨1076282, by decide⟩ ⟨13, 2, 0, 1076282, 1230871, 589, 16384⟩
    (by decide) selected_cut_39664

theorem unmarked_context_12_307717_1076283 : frontier 9 ⟨1076283, by decide⟩
    (prefixCache 12 307717) (prefixPartial 12 307717) = false := by
  decide +kernel

theorem node_context_12_307717_1076283 : EJMOriginalGlobalDAGData.nodes 9 ⟨1076283, by decide⟩ =
    .split (coordinate 12) (![⟨1076242, by decide⟩,⟨1076258, by decide⟩,⟨1076274, by decide⟩,⟨1076282, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_307717_1076283 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307717 ⟨1076283, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 307717
    ⟨1076283, by decide⟩ (by decide) (![⟨1076242, by decide⟩,⟨1076258, by decide⟩,⟨1076274, by decide⟩,⟨1076282, by decide⟩]) unmarked_context_12_307717_1076283 node_context_12_307717_1076283
  intro a
  fin_cases a
  · exact context_13_1230868_1076242
  · exact context_13_1230869_1076258
  · exact context_13_1230870_1076274
  · exact context_13_1230871_1076282

theorem selected_cut_39665 : selected 8 ⟨1076320, by decide⟩
    (prefixPartial 13 1230872) = some ⟨13, 2, 0, 1076320, 1230872, 1889, 16384⟩ := by
  decide +kernel

theorem context_13_1230872_1076320 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1230872 ⟨1076320, by decide⟩ :=
  accepted_of_selected 13 1230872 ⟨1076320, by decide⟩ ⟨13, 2, 0, 1076320, 1230872, 1889, 16384⟩
    (by decide) selected_cut_39665

theorem selected_cut_39666 : selected 8 ⟨1076338, by decide⟩
    (prefixPartial 13 1230873) = some ⟨13, 2, 0, 1076338, 1230873, 1145, 16384⟩ := by
  decide +kernel

theorem context_13_1230873_1076338 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1230873 ⟨1076338, by decide⟩ :=
  accepted_of_selected 13 1230873 ⟨1076338, by decide⟩ ⟨13, 2, 0, 1076338, 1230873, 1145, 16384⟩
    (by decide) selected_cut_39666

theorem selected_cut_39667 : selected 8 ⟨1076349, by decide⟩
    (prefixPartial 13 1230874) = some ⟨13, 2, 0, 1076349, 1230874, 973, 16384⟩ := by
  decide +kernel

theorem context_13_1230874_1076349 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1230874 ⟨1076349, by decide⟩ :=
  accepted_of_selected 13 1230874 ⟨1076349, by decide⟩ ⟨13, 2, 0, 1076349, 1230874, 973, 16384⟩
    (by decide) selected_cut_39667

theorem selected_cut_39668 : selected 8 ⟨1076358, by decide⟩
    (prefixPartial 13 1230875) = some ⟨13, 2, 0, 1076358, 1230875, 613, 16384⟩ := by
  decide +kernel

theorem context_13_1230875_1076358 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1230875 ⟨1076358, by decide⟩ :=
  accepted_of_selected 13 1230875 ⟨1076358, by decide⟩ ⟨13, 2, 0, 1076358, 1230875, 613, 16384⟩
    (by decide) selected_cut_39668

theorem unmarked_context_12_307718_1076359 : frontier 9 ⟨1076359, by decide⟩
    (prefixCache 12 307718) (prefixPartial 12 307718) = false := by
  decide +kernel

theorem node_context_12_307718_1076359 : EJMOriginalGlobalDAGData.nodes 9 ⟨1076359, by decide⟩ =
    .split (coordinate 12) (![⟨1076320, by decide⟩,⟨1076338, by decide⟩,⟨1076349, by decide⟩,⟨1076358, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_307718_1076359 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307718 ⟨1076359, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 307718
    ⟨1076359, by decide⟩ (by decide) (![⟨1076320, by decide⟩,⟨1076338, by decide⟩,⟨1076349, by decide⟩,⟨1076358, by decide⟩]) unmarked_context_12_307718_1076359 node_context_12_307718_1076359
  intro a
  fin_cases a
  · exact context_13_1230872_1076320
  · exact context_13_1230873_1076338
  · exact context_13_1230874_1076349
  · exact context_13_1230875_1076358

theorem selected_cut_39669 : selected 8 ⟨1076393, by decide⟩
    (prefixPartial 13 1230876) = some ⟨13, 2, 0, 1076393, 1230876, 1657, 16384⟩ := by
  decide +kernel

theorem context_13_1230876_1076393 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1230876 ⟨1076393, by decide⟩ :=
  accepted_of_selected 13 1230876 ⟨1076393, by decide⟩ ⟨13, 2, 0, 1076393, 1230876, 1657, 16384⟩
    (by decide) selected_cut_39669

theorem selected_cut_39670 : selected 8 ⟨1076404, by decide⟩
    (prefixPartial 13 1230877) = some ⟨13, 2, 0, 1076404, 1230877, 985, 16384⟩ := by
  decide +kernel

theorem context_13_1230877_1076404 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1230877 ⟨1076404, by decide⟩ :=
  accepted_of_selected 13 1230877 ⟨1076404, by decide⟩ ⟨13, 2, 0, 1076404, 1230877, 985, 16384⟩
    (by decide) selected_cut_39670

theorem selected_cut_39671 : selected 8 ⟨1076424, by decide⟩
    (prefixPartial 13 1230878) = some ⟨13, 2, 0, 1076424, 1230878, 909, 16384⟩ := by
  decide +kernel

theorem context_13_1230878_1076424 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1230878 ⟨1076424, by decide⟩ :=
  accepted_of_selected 13 1230878 ⟨1076424, by decide⟩ ⟨13, 2, 0, 1076424, 1230878, 909, 16384⟩
    (by decide) selected_cut_39671

theorem selected_cut_39672 : selected 8 ⟨1076432, by decide⟩
    (prefixPartial 13 1230879) = some ⟨13, 2, 0, 1076432, 1230879, 593, 16384⟩ := by
  decide +kernel

theorem context_13_1230879_1076432 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1230879 ⟨1076432, by decide⟩ :=
  accepted_of_selected 13 1230879 ⟨1076432, by decide⟩ ⟨13, 2, 0, 1076432, 1230879, 593, 16384⟩
    (by decide) selected_cut_39672

theorem unmarked_context_12_307719_1076433 : frontier 9 ⟨1076433, by decide⟩
    (prefixCache 12 307719) (prefixPartial 12 307719) = false := by
  decide +kernel

theorem node_context_12_307719_1076433 : EJMOriginalGlobalDAGData.nodes 9 ⟨1076433, by decide⟩ =
    .split (coordinate 12) (![⟨1076393, by decide⟩,⟨1076404, by decide⟩,⟨1076424, by decide⟩,⟨1076432, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_307719_1076433 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307719 ⟨1076433, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 307719
    ⟨1076433, by decide⟩ (by decide) (![⟨1076393, by decide⟩,⟨1076404, by decide⟩,⟨1076424, by decide⟩,⟨1076432, by decide⟩]) unmarked_context_12_307719_1076433 node_context_12_307719_1076433
  intro a
  fin_cases a
  · exact context_13_1230876_1076393
  · exact context_13_1230877_1076404
  · exact context_13_1230878_1076424
  · exact context_13_1230879_1076432

theorem unmarked_context_11_76929_1076434 : frontier 10 ⟨1076434, by decide⟩
    (prefixCache 11 76929) (prefixPartial 11 76929) = false := by
  decide +kernel

theorem node_context_11_76929_1076434 : EJMOriginalGlobalDAGData.nodes 10 ⟨1076434, by decide⟩ =
    .split (coordinate 11) (![⟨34034, by decide⟩,⟨1076283, by decide⟩,⟨1076359, by decide⟩,⟨1076433, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_76929_1076434 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76929 ⟨1076434, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 76929
    ⟨1076434, by decide⟩ (by decide) (![⟨34034, by decide⟩,⟨1076283, by decide⟩,⟨1076359, by decide⟩,⟨1076433, by decide⟩]) unmarked_context_11_76929_1076434 node_context_11_76929_1076434
  intro a
  fin_cases a
  · exact context_12_307716_34034
  · exact context_12_307717_1076283
  · exact context_12_307718_1076359
  · exact context_12_307719_1076433

theorem selected_cut_39673 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 307720) = some ⟨12, 1, 0, 34034, 307720, 1, 65536⟩ := by
  decide +kernel

theorem context_12_307720_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307720 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 307720 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 307720, 1, 65536⟩
    (by decide) selected_cut_39673

theorem selected_cut_39674 : selected 8 ⟨1076465, by decide⟩
    (prefixPartial 13 1230884) = some ⟨13, 2, 0, 1076465, 1230884, 1745, 16384⟩ := by
  decide +kernel

theorem context_13_1230884_1076465 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1230884 ⟨1076465, by decide⟩ :=
  accepted_of_selected 13 1230884 ⟨1076465, by decide⟩ ⟨13, 2, 0, 1076465, 1230884, 1745, 16384⟩
    (by decide) selected_cut_39674

theorem selected_cut_39675 : selected 8 ⟨1076480, by decide⟩
    (prefixPartial 13 1230885) = some ⟨13, 2, 0, 1076480, 1230885, 1177, 16384⟩ := by
  decide +kernel

theorem context_13_1230885_1076480 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1230885 ⟨1076480, by decide⟩ :=
  accepted_of_selected 13 1230885 ⟨1076480, by decide⟩ ⟨13, 2, 0, 1076480, 1230885, 1177, 16384⟩
    (by decide) selected_cut_39675

theorem selected_cut_39676 : selected 8 ⟨1076496, by decide⟩
    (prefixPartial 13 1230886) = some ⟨13, 2, 0, 1076496, 1230886, 801, 16384⟩ := by
  decide +kernel

theorem context_13_1230886_1076496 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1230886 ⟨1076496, by decide⟩ :=
  accepted_of_selected 13 1230886 ⟨1076496, by decide⟩ ⟨13, 2, 0, 1076496, 1230886, 801, 16384⟩
    (by decide) selected_cut_39676

theorem selected_cut_39677 : selected 8 ⟨1076502, by decide⟩
    (prefixPartial 13 1230887) = some ⟨13, 2, 0, 1076502, 1230887, 549, 16384⟩ := by
  decide +kernel

theorem context_13_1230887_1076502 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1230887 ⟨1076502, by decide⟩ :=
  accepted_of_selected 13 1230887 ⟨1076502, by decide⟩ ⟨13, 2, 0, 1076502, 1230887, 549, 16384⟩
    (by decide) selected_cut_39677

theorem unmarked_context_12_307721_1076503 : frontier 9 ⟨1076503, by decide⟩
    (prefixCache 12 307721) (prefixPartial 12 307721) = false := by
  decide +kernel

theorem node_context_12_307721_1076503 : EJMOriginalGlobalDAGData.nodes 9 ⟨1076503, by decide⟩ =
    .split (coordinate 12) (![⟨1076465, by decide⟩,⟨1076480, by decide⟩,⟨1076496, by decide⟩,⟨1076502, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_307721_1076503 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307721 ⟨1076503, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 307721
    ⟨1076503, by decide⟩ (by decide) (![⟨1076465, by decide⟩,⟨1076480, by decide⟩,⟨1076496, by decide⟩,⟨1076502, by decide⟩]) unmarked_context_12_307721_1076503 node_context_12_307721_1076503
  intro a
  fin_cases a
  · exact context_13_1230884_1076465
  · exact context_13_1230885_1076480
  · exact context_13_1230886_1076496
  · exact context_13_1230887_1076502

theorem selected_cut_39678 : selected 9 ⟨893903, by decide⟩
    (prefixPartial 12 307722) = some ⟨12, 1, 0, 893903, 307722, 1, 65536⟩ := by
  decide +kernel

theorem context_12_307722_893903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307722 ⟨893903, by decide⟩ :=
  accepted_of_selected 12 307722 ⟨893903, by decide⟩ ⟨12, 1, 0, 893903, 307722, 1, 65536⟩
    (by decide) selected_cut_39678

theorem selected_cut_39679 : selected 9 ⟨1076561, by decide⟩
    (prefixPartial 12 307723) = some ⟨12, 2, 0, 1076561, 307723, 3909, 65536⟩ := by
  decide +kernel

theorem context_12_307723_1076561 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307723 ⟨1076561, by decide⟩ :=
  accepted_of_selected 12 307723 ⟨1076561, by decide⟩ ⟨12, 2, 0, 1076561, 307723, 3909, 65536⟩
    (by decide) selected_cut_39679

theorem unmarked_context_11_76930_1076562 : frontier 10 ⟨1076562, by decide⟩
    (prefixCache 11 76930) (prefixPartial 11 76930) = false := by
  decide +kernel

theorem node_context_11_76930_1076562 : EJMOriginalGlobalDAGData.nodes 10 ⟨1076562, by decide⟩ =
    .split (coordinate 11) (![⟨34034, by decide⟩,⟨1076503, by decide⟩,⟨893903, by decide⟩,⟨1076561, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_76930_1076562 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76930 ⟨1076562, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 76930
    ⟨1076562, by decide⟩ (by decide) (![⟨34034, by decide⟩,⟨1076503, by decide⟩,⟨893903, by decide⟩,⟨1076561, by decide⟩]) unmarked_context_11_76930_1076562 node_context_11_76930_1076562
  intro a
  fin_cases a
  · exact context_12_307720_34034
  · exact context_12_307721_1076503
  · exact context_12_307722_893903
  · exact context_12_307723_1076561

theorem selected_cut_39680 : selected 8 ⟨1076613, by decide⟩
    (prefixPartial 13 1230896) = some ⟨13, 2, 0, 1076613, 1230896, 2085, 16384⟩ := by
  decide +kernel

theorem context_13_1230896_1076613 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1230896 ⟨1076613, by decide⟩ :=
  accepted_of_selected 13 1230896 ⟨1076613, by decide⟩ ⟨13, 2, 0, 1076613, 1230896, 2085, 16384⟩
    (by decide) selected_cut_39680

theorem selected_cut_39681 : selected 8 ⟨1076657, by decide⟩
    (prefixPartial 13 1230897) = some ⟨13, 2, 0, 1076657, 1230897, 1677, 16384⟩ := by
  decide +kernel

theorem context_13_1230897_1076657 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1230897 ⟨1076657, by decide⟩ :=
  accepted_of_selected 13 1230897 ⟨1076657, by decide⟩ ⟨13, 2, 0, 1076657, 1230897, 1677, 16384⟩
    (by decide) selected_cut_39681

theorem selected_cut_39682 : selected 8 ⟨1076693, by decide⟩
    (prefixPartial 13 1230898) = some ⟨13, 2, 0, 1076693, 1230898, 1377, 16384⟩ := by
  decide +kernel

theorem context_13_1230898_1076693 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1230898 ⟨1076693, by decide⟩ :=
  accepted_of_selected 13 1230898 ⟨1076693, by decide⟩ ⟨13, 2, 0, 1076693, 1230898, 1377, 16384⟩
    (by decide) selected_cut_39682

theorem selected_cut_39683 : selected 8 ⟨1076706, by decide⟩
    (prefixPartial 13 1230899) = some ⟨13, 2, 0, 1076706, 1230899, 737, 16384⟩ := by
  decide +kernel

theorem context_13_1230899_1076706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1230899 ⟨1076706, by decide⟩ :=
  accepted_of_selected 13 1230899 ⟨1076706, by decide⟩ ⟨13, 2, 0, 1076706, 1230899, 737, 16384⟩
    (by decide) selected_cut_39683

theorem unmarked_context_12_307724_1076707 : frontier 9 ⟨1076707, by decide⟩
    (prefixCache 12 307724) (prefixPartial 12 307724) = false := by
  decide +kernel

theorem node_context_12_307724_1076707 : EJMOriginalGlobalDAGData.nodes 9 ⟨1076707, by decide⟩ =
    .split (coordinate 12) (![⟨1076613, by decide⟩,⟨1076657, by decide⟩,⟨1076693, by decide⟩,⟨1076706, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_307724_1076707 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307724 ⟨1076707, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 307724
    ⟨1076707, by decide⟩ (by decide) (![⟨1076613, by decide⟩,⟨1076657, by decide⟩,⟨1076693, by decide⟩,⟨1076706, by decide⟩]) unmarked_context_12_307724_1076707 node_context_12_307724_1076707
  intro a
  fin_cases a
  · exact context_13_1230896_1076613
  · exact context_13_1230897_1076657
  · exact context_13_1230898_1076693
  · exact context_13_1230899_1076706

theorem selected_cut_39684 : selected 8 ⟨1076735, by decide⟩
    (prefixPartial 13 1230900) = some ⟨13, 2, 0, 1076735, 1230900, 1821, 16384⟩ := by
  decide +kernel

theorem context_13_1230900_1076735 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1230900 ⟨1076735, by decide⟩ :=
  accepted_of_selected 13 1230900 ⟨1076735, by decide⟩ ⟨13, 2, 0, 1076735, 1230900, 1821, 16384⟩
    (by decide) selected_cut_39684

theorem selected_cut_39685 : selected 8 ⟨1076751, by decide⟩
    (prefixPartial 13 1230901) = some ⟨13, 2, 0, 1076751, 1230901, 1345, 16384⟩ := by
  decide +kernel

theorem context_13_1230901_1076751 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1230901 ⟨1076751, by decide⟩ :=
  accepted_of_selected 13 1230901 ⟨1076751, by decide⟩ ⟨13, 2, 0, 1076751, 1230901, 1345, 16384⟩
    (by decide) selected_cut_39685

theorem selected_cut_39686 : selected 8 ⟨1076770, by decide⟩
    (prefixPartial 13 1230902) = some ⟨13, 2, 0, 1076770, 1230902, 1145, 16384⟩ := by
  decide +kernel

theorem context_13_1230902_1076770 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1230902 ⟨1076770, by decide⟩ :=
  accepted_of_selected 13 1230902 ⟨1076770, by decide⟩ ⟨13, 2, 0, 1076770, 1230902, 1145, 16384⟩
    (by decide) selected_cut_39686

theorem selected_cut_39687 : selected 8 ⟨1076775, by decide⟩
    (prefixPartial 13 1230903) = some ⟨13, 2, 0, 1076775, 1230903, 589, 16384⟩ := by
  decide +kernel

theorem context_13_1230903_1076775 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1230903 ⟨1076775, by decide⟩ :=
  accepted_of_selected 13 1230903 ⟨1076775, by decide⟩ ⟨13, 2, 0, 1076775, 1230903, 589, 16384⟩
    (by decide) selected_cut_39687

theorem unmarked_context_12_307725_1076776 : frontier 9 ⟨1076776, by decide⟩
    (prefixCache 12 307725) (prefixPartial 12 307725) = false := by
  decide +kernel

theorem node_context_12_307725_1076776 : EJMOriginalGlobalDAGData.nodes 9 ⟨1076776, by decide⟩ =
    .split (coordinate 12) (![⟨1076735, by decide⟩,⟨1076751, by decide⟩,⟨1076770, by decide⟩,⟨1076775, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_307725_1076776 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307725 ⟨1076776, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 307725
    ⟨1076776, by decide⟩ (by decide) (![⟨1076735, by decide⟩,⟨1076751, by decide⟩,⟨1076770, by decide⟩,⟨1076775, by decide⟩]) unmarked_context_12_307725_1076776 node_context_12_307725_1076776
  intro a
  fin_cases a
  · exact context_13_1230900_1076735
  · exact context_13_1230901_1076751
  · exact context_13_1230902_1076770
  · exact context_13_1230903_1076775

theorem selected_cut_39688 : selected 8 ⟨1076805, by decide⟩
    (prefixPartial 13 1230904) = some ⟨13, 2, 0, 1076805, 1230904, 1581, 16384⟩ := by
  decide +kernel

theorem context_13_1230904_1076805 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1230904 ⟨1076805, by decide⟩ :=
  accepted_of_selected 13 1230904 ⟨1076805, by decide⟩ ⟨13, 2, 0, 1076805, 1230904, 1581, 16384⟩
    (by decide) selected_cut_39688

theorem selected_cut_39689 : selected 8 ⟨1076821, by decide⟩
    (prefixPartial 13 1230905) = some ⟨13, 2, 0, 1076821, 1230905, 1385, 16384⟩ := by
  decide +kernel

theorem context_13_1230905_1076821 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1230905 ⟨1076821, by decide⟩ :=
  accepted_of_selected 13 1230905 ⟨1076821, by decide⟩ ⟨13, 2, 0, 1076821, 1230905, 1385, 16384⟩
    (by decide) selected_cut_39689

theorem selected_cut_39690 : selected 8 ⟨1076839, by decide⟩
    (prefixPartial 13 1230906) = some ⟨13, 2, 0, 1076839, 1230906, 1129, 16384⟩ := by
  decide +kernel

theorem context_13_1230906_1076839 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1230906 ⟨1076839, by decide⟩ :=
  accepted_of_selected 13 1230906 ⟨1076839, by decide⟩ ⟨13, 2, 0, 1076839, 1230906, 1129, 16384⟩
    (by decide) selected_cut_39690

theorem selected_cut_39691 : selected 8 ⟨1076849, by decide⟩
    (prefixPartial 13 1230907) = some ⟨13, 2, 0, 1076849, 1230907, 709, 16384⟩ := by
  decide +kernel

theorem context_13_1230907_1076849 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1230907 ⟨1076849, by decide⟩ :=
  accepted_of_selected 13 1230907 ⟨1076849, by decide⟩ ⟨13, 2, 0, 1076849, 1230907, 709, 16384⟩
    (by decide) selected_cut_39691

theorem unmarked_context_12_307726_1076850 : frontier 9 ⟨1076850, by decide⟩
    (prefixCache 12 307726) (prefixPartial 12 307726) = false := by
  decide +kernel

theorem node_context_12_307726_1076850 : EJMOriginalGlobalDAGData.nodes 9 ⟨1076850, by decide⟩ =
    .split (coordinate 12) (![⟨1076805, by decide⟩,⟨1076821, by decide⟩,⟨1076839, by decide⟩,⟨1076849, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_307726_1076850 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307726 ⟨1076850, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 307726
    ⟨1076850, by decide⟩ (by decide) (![⟨1076805, by decide⟩,⟨1076821, by decide⟩,⟨1076839, by decide⟩,⟨1076849, by decide⟩]) unmarked_context_12_307726_1076850 node_context_12_307726_1076850
  intro a
  fin_cases a
  · exact context_13_1230904_1076805
  · exact context_13_1230905_1076821
  · exact context_13_1230906_1076839
  · exact context_13_1230907_1076849

theorem selected_cut_39692 : selected 9 ⟨1076916, by decide⟩
    (prefixPartial 12 307727) = some ⟨12, 2, 0, 1076916, 307727, 4009, 65536⟩ := by
  decide +kernel

theorem context_12_307727_1076916 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307727 ⟨1076916, by decide⟩ :=
  accepted_of_selected 12 307727 ⟨1076916, by decide⟩ ⟨12, 2, 0, 1076916, 307727, 4009, 65536⟩
    (by decide) selected_cut_39692

theorem unmarked_context_11_76931_1076917 : frontier 10 ⟨1076917, by decide⟩
    (prefixCache 11 76931) (prefixPartial 11 76931) = false := by
  decide +kernel

theorem node_context_11_76931_1076917 : EJMOriginalGlobalDAGData.nodes 10 ⟨1076917, by decide⟩ =
    .split (coordinate 11) (![⟨1076707, by decide⟩,⟨1076776, by decide⟩,⟨1076850, by decide⟩,⟨1076916, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_76931_1076917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76931 ⟨1076917, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 76931
    ⟨1076917, by decide⟩ (by decide) (![⟨1076707, by decide⟩,⟨1076776, by decide⟩,⟨1076850, by decide⟩,⟨1076916, by decide⟩]) unmarked_context_11_76931_1076917 node_context_11_76931_1076917
  intro a
  fin_cases a
  · exact context_12_307724_1076707
  · exact context_12_307725_1076776
  · exact context_12_307726_1076850
  · exact context_12_307727_1076916

theorem unmarked_context_10_19232_1076918 : frontier 11 ⟨1076918, by decide⟩
    (prefixCache 10 19232) (prefixPartial 10 19232) = false := by
  decide +kernel

theorem node_context_10_19232_1076918 : EJMOriginalGlobalDAGData.nodes 11 ⟨1076918, by decide⟩ =
    .split (coordinate 10) (![⟨167448, by decide⟩,⟨1076434, by decide⟩,⟨1076562, by decide⟩,⟨1076917, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_19232_1076918 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19232 ⟨1076918, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 19232
    ⟨1076918, by decide⟩ (by decide) (![⟨167448, by decide⟩,⟨1076434, by decide⟩,⟨1076562, by decide⟩,⟨1076917, by decide⟩]) unmarked_context_10_19232_1076918 node_context_10_19232_1076918
  intro a
  fin_cases a
  · exact context_11_76928_167448
  · exact context_11_76929_1076434
  · exact context_11_76930_1076562
  · exact context_11_76931_1076917

theorem selected_cut_39693 : selected 9 ⟨994572, by decide⟩
    (prefixPartial 12 307728) = some ⟨12, 1, 0, 994572, 307728, 1, 65536⟩ := by
  decide +kernel

theorem context_12_307728_994572 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307728 ⟨994572, by decide⟩ :=
  accepted_of_selected 12 307728 ⟨994572, by decide⟩ ⟨12, 1, 0, 994572, 307728, 1, 65536⟩
    (by decide) selected_cut_39693

theorem selected_cut_39694 : selected 9 ⟨1076974, by decide⟩
    (prefixPartial 12 307729) = some ⟨12, 2, 0, 1076974, 307729, 3649, 65536⟩ := by
  decide +kernel

theorem context_12_307729_1076974 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307729 ⟨1076974, by decide⟩ :=
  accepted_of_selected 12 307729 ⟨1076974, by decide⟩ ⟨12, 2, 0, 1076974, 307729, 3649, 65536⟩
    (by decide) selected_cut_39694

theorem selected_cut_39695 : selected 9 ⟨1077023, by decide⟩
    (prefixPartial 12 307730) = some ⟨12, 2, 0, 1077023, 307730, 3209, 65536⟩ := by
  decide +kernel

theorem context_12_307730_1077023 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307730 ⟨1077023, by decide⟩ :=
  accepted_of_selected 12 307730 ⟨1077023, by decide⟩ ⟨12, 2, 0, 1077023, 307730, 3209, 65536⟩
    (by decide) selected_cut_39695

theorem selected_cut_39696 : selected 9 ⟨1077073, by decide⟩
    (prefixPartial 12 307731) = some ⟨12, 2, 0, 1077073, 307731, 3705, 65536⟩ := by
  decide +kernel

theorem context_12_307731_1077073 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307731 ⟨1077073, by decide⟩ :=
  accepted_of_selected 12 307731 ⟨1077073, by decide⟩ ⟨12, 2, 0, 1077073, 307731, 3705, 65536⟩
    (by decide) selected_cut_39696

theorem unmarked_context_11_76932_1077074 : frontier 10 ⟨1077074, by decide⟩
    (prefixCache 11 76932) (prefixPartial 11 76932) = false := by
  decide +kernel

theorem node_context_11_76932_1077074 : EJMOriginalGlobalDAGData.nodes 10 ⟨1077074, by decide⟩ =
    .split (coordinate 11) (![⟨994572, by decide⟩,⟨1076974, by decide⟩,⟨1077023, by decide⟩,⟨1077073, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_76932_1077074 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76932 ⟨1077074, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 76932
    ⟨1077074, by decide⟩ (by decide) (![⟨994572, by decide⟩,⟨1076974, by decide⟩,⟨1077023, by decide⟩,⟨1077073, by decide⟩]) unmarked_context_11_76932_1077074 node_context_11_76932_1077074
  intro a
  fin_cases a
  · exact context_12_307728_994572
  · exact context_12_307729_1076974
  · exact context_12_307730_1077023
  · exact context_12_307731_1077073

theorem selected_cut_39697 : selected 8 ⟨1077112, by decide⟩
    (prefixPartial 13 1230928) = some ⟨13, 2, 0, 1077112, 1230928, 2149, 16384⟩ := by
  decide +kernel

theorem context_13_1230928_1077112 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1230928 ⟨1077112, by decide⟩ :=
  accepted_of_selected 13 1230928 ⟨1077112, by decide⟩ ⟨13, 2, 0, 1077112, 1230928, 2149, 16384⟩
    (by decide) selected_cut_39697

theorem selected_cut_39698 : selected 8 ⟨1077135, by decide⟩
    (prefixPartial 13 1230929) = some ⟨13, 2, 0, 1077135, 1230929, 1393, 16384⟩ := by
  decide +kernel

theorem context_13_1230929_1077135 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1230929 ⟨1077135, by decide⟩ :=
  accepted_of_selected 13 1230929 ⟨1077135, by decide⟩ ⟨13, 2, 0, 1077135, 1230929, 1393, 16384⟩
    (by decide) selected_cut_39698

theorem selected_cut_39699 : selected 8 ⟨1077154, by decide⟩
    (prefixPartial 13 1230930) = some ⟨13, 2, 0, 1077154, 1230930, 1089, 16384⟩ := by
  decide +kernel

theorem context_13_1230930_1077154 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1230930 ⟨1077154, by decide⟩ :=
  accepted_of_selected 13 1230930 ⟨1077154, by decide⟩ ⟨13, 2, 0, 1077154, 1230930, 1089, 16384⟩
    (by decide) selected_cut_39699

theorem selected_cut_39700 : selected 8 ⟨1077164, by decide⟩
    (prefixPartial 13 1230931) = some ⟨13, 2, 0, 1077164, 1230931, 565, 16384⟩ := by
  decide +kernel

theorem context_13_1230931_1077164 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1230931 ⟨1077164, by decide⟩ :=
  accepted_of_selected 13 1230931 ⟨1077164, by decide⟩ ⟨13, 2, 0, 1077164, 1230931, 565, 16384⟩
    (by decide) selected_cut_39700

theorem unmarked_context_12_307732_1077165 : frontier 9 ⟨1077165, by decide⟩
    (prefixCache 12 307732) (prefixPartial 12 307732) = false := by
  decide +kernel

theorem node_context_12_307732_1077165 : EJMOriginalGlobalDAGData.nodes 9 ⟨1077165, by decide⟩ =
    .split (coordinate 12) (![⟨1077112, by decide⟩,⟨1077135, by decide⟩,⟨1077154, by decide⟩,⟨1077164, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_307732_1077165 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307732 ⟨1077165, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 307732
    ⟨1077165, by decide⟩ (by decide) (![⟨1077112, by decide⟩,⟨1077135, by decide⟩,⟨1077154, by decide⟩,⟨1077164, by decide⟩]) unmarked_context_12_307732_1077165 node_context_12_307732_1077165
  intro a
  fin_cases a
  · exact context_13_1230928_1077112
  · exact context_13_1230929_1077135
  · exact context_13_1230930_1077154
  · exact context_13_1230931_1077164

theorem selected_cut_39701 : selected 9 ⟨68180, by decide⟩
    (prefixPartial 12 307733) = some ⟨12, 1, 0, 68180, 307733, 1, 65536⟩ := by
  decide +kernel

theorem context_12_307733_68180 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307733 ⟨68180, by decide⟩ :=
  accepted_of_selected 12 307733 ⟨68180, by decide⟩ ⟨12, 1, 0, 68180, 307733, 1, 65536⟩
    (by decide) selected_cut_39701

theorem selected_cut_39702 : selected 8 ⟨1077188, by decide⟩
    (prefixPartial 13 1230936) = some ⟨13, 2, 0, 1077188, 1230936, 1485, 16384⟩ := by
  decide +kernel

theorem context_13_1230936_1077188 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1230936 ⟨1077188, by decide⟩ :=
  accepted_of_selected 13 1230936 ⟨1077188, by decide⟩ ⟨13, 2, 0, 1077188, 1230936, 1485, 16384⟩
    (by decide) selected_cut_39702

theorem selected_cut_39703 : selected 8 ⟨1077203, by decide⟩
    (prefixPartial 13 1230937) = some ⟨13, 2, 0, 1077203, 1230937, 1145, 16384⟩ := by
  decide +kernel

theorem context_13_1230937_1077203 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1230937 ⟨1077203, by decide⟩ :=
  accepted_of_selected 13 1230937 ⟨1077203, by decide⟩ ⟨13, 2, 0, 1077203, 1230937, 1145, 16384⟩
    (by decide) selected_cut_39703

theorem selected_cut_39704 : selected 8 ⟨1077217, by decide⟩
    (prefixPartial 13 1230938) = some ⟨13, 2, 0, 1077217, 1230938, 953, 16384⟩ := by
  decide +kernel

theorem context_13_1230938_1077217 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1230938 ⟨1077217, by decide⟩ :=
  accepted_of_selected 13 1230938 ⟨1077217, by decide⟩ ⟨13, 2, 0, 1077217, 1230938, 953, 16384⟩
    (by decide) selected_cut_39704

theorem selected_cut_39705 : selected 8 ⟨1077222, by decide⟩
    (prefixPartial 13 1230939) = some ⟨13, 2, 0, 1077222, 1230939, 553, 16384⟩ := by
  decide +kernel

theorem context_13_1230939_1077222 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1230939 ⟨1077222, by decide⟩ :=
  accepted_of_selected 13 1230939 ⟨1077222, by decide⟩ ⟨13, 2, 0, 1077222, 1230939, 553, 16384⟩
    (by decide) selected_cut_39705

theorem unmarked_context_12_307734_1077223 : frontier 9 ⟨1077223, by decide⟩
    (prefixCache 12 307734) (prefixPartial 12 307734) = false := by
  decide +kernel

theorem node_context_12_307734_1077223 : EJMOriginalGlobalDAGData.nodes 9 ⟨1077223, by decide⟩ =
    .split (coordinate 12) (![⟨1077188, by decide⟩,⟨1077203, by decide⟩,⟨1077217, by decide⟩,⟨1077222, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_307734_1077223 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307734 ⟨1077223, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 307734
    ⟨1077223, by decide⟩ (by decide) (![⟨1077188, by decide⟩,⟨1077203, by decide⟩,⟨1077217, by decide⟩,⟨1077222, by decide⟩]) unmarked_context_12_307734_1077223 node_context_12_307734_1077223
  intro a
  fin_cases a
  · exact context_13_1230936_1077188
  · exact context_13_1230937_1077203
  · exact context_13_1230938_1077217
  · exact context_13_1230939_1077222

theorem selected_cut_39706 : selected 8 ⟨1077243, by decide⟩
    (prefixPartial 13 1230940) = some ⟨13, 2, 0, 1077243, 1230940, 1617, 16384⟩ := by
  decide +kernel

theorem context_13_1230940_1077243 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1230940 ⟨1077243, by decide⟩ :=
  accepted_of_selected 13 1230940 ⟨1077243, by decide⟩ ⟨13, 2, 0, 1077243, 1230940, 1617, 16384⟩
    (by decide) selected_cut_39706

theorem selected_cut_39707 : selected 8 ⟨1077256, by decide⟩
    (prefixPartial 13 1230941) = some ⟨13, 2, 0, 1077256, 1230941, 1121, 16384⟩ := by
  decide +kernel

theorem context_13_1230941_1077256 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1230941 ⟨1077256, by decide⟩ :=
  accepted_of_selected 13 1230941 ⟨1077256, by decide⟩ ⟨13, 2, 0, 1077256, 1230941, 1121, 16384⟩
    (by decide) selected_cut_39707

theorem selected_cut_39708 : selected 8 ⟨1077275, by decide⟩
    (prefixPartial 13 1230942) = some ⟨13, 2, 0, 1077275, 1230942, 981, 16384⟩ := by
  decide +kernel

theorem context_13_1230942_1077275 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1230942 ⟨1077275, by decide⟩ :=
  accepted_of_selected 13 1230942 ⟨1077275, by decide⟩ ⟨13, 2, 0, 1077275, 1230942, 981, 16384⟩
    (by decide) selected_cut_39708

theorem selected_cut_39709 : selected 8 ⟨1077281, by decide⟩
    (prefixPartial 13 1230943) = some ⟨13, 2, 0, 1077281, 1230943, 545, 16384⟩ := by
  decide +kernel

theorem context_13_1230943_1077281 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1230943 ⟨1077281, by decide⟩ :=
  accepted_of_selected 13 1230943 ⟨1077281, by decide⟩ ⟨13, 2, 0, 1077281, 1230943, 545, 16384⟩
    (by decide) selected_cut_39709

theorem unmarked_context_12_307735_1077282 : frontier 9 ⟨1077282, by decide⟩
    (prefixCache 12 307735) (prefixPartial 12 307735) = false := by
  decide +kernel

theorem node_context_12_307735_1077282 : EJMOriginalGlobalDAGData.nodes 9 ⟨1077282, by decide⟩ =
    .split (coordinate 12) (![⟨1077243, by decide⟩,⟨1077256, by decide⟩,⟨1077275, by decide⟩,⟨1077281, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_307735_1077282 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307735 ⟨1077282, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 307735
    ⟨1077282, by decide⟩ (by decide) (![⟨1077243, by decide⟩,⟨1077256, by decide⟩,⟨1077275, by decide⟩,⟨1077281, by decide⟩]) unmarked_context_12_307735_1077282 node_context_12_307735_1077282
  intro a
  fin_cases a
  · exact context_13_1230940_1077243
  · exact context_13_1230941_1077256
  · exact context_13_1230942_1077275
  · exact context_13_1230943_1077281

theorem unmarked_context_11_76933_1077283 : frontier 10 ⟨1077283, by decide⟩
    (prefixCache 11 76933) (prefixPartial 11 76933) = false := by
  decide +kernel

theorem node_context_11_76933_1077283 : EJMOriginalGlobalDAGData.nodes 10 ⟨1077283, by decide⟩ =
    .split (coordinate 11) (![⟨1077165, by decide⟩,⟨68180, by decide⟩,⟨1077223, by decide⟩,⟨1077282, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_76933_1077283 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76933 ⟨1077283, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 76933
    ⟨1077283, by decide⟩ (by decide) (![⟨1077165, by decide⟩,⟨68180, by decide⟩,⟨1077223, by decide⟩,⟨1077282, by decide⟩]) unmarked_context_11_76933_1077283 node_context_11_76933_1077283
  intro a
  fin_cases a
  · exact context_12_307732_1077165
  · exact context_12_307733_68180
  · exact context_12_307734_1077223
  · exact context_12_307735_1077282

theorem selected_cut_39710 : selected 8 ⟨1077302, by decide⟩
    (prefixPartial 13 1230944) = some ⟨13, 2, 0, 1077302, 1230944, 1493, 16384⟩ := by
  decide +kernel

theorem context_13_1230944_1077302 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1230944 ⟨1077302, by decide⟩ :=
  accepted_of_selected 13 1230944 ⟨1077302, by decide⟩ ⟨13, 2, 0, 1077302, 1230944, 1493, 16384⟩
    (by decide) selected_cut_39710

theorem selected_cut_39711 : selected 8 ⟨1077322, by decide⟩
    (prefixPartial 13 1230945) = some ⟨13, 2, 0, 1077322, 1230945, 1401, 16384⟩ := by
  decide +kernel

theorem context_13_1230945_1077322 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1230945 ⟨1077322, by decide⟩ :=
  accepted_of_selected 13 1230945 ⟨1077322, by decide⟩ ⟨13, 2, 0, 1077322, 1230945, 1401, 16384⟩
    (by decide) selected_cut_39711

theorem selected_cut_39712 : selected 8 ⟨1077344, by decide⟩
    (prefixPartial 13 1230946) = some ⟨13, 2, 0, 1077344, 1230946, 941, 16384⟩ := by
  decide +kernel

theorem context_13_1230946_1077344 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1230946 ⟨1077344, by decide⟩ :=
  accepted_of_selected 13 1230946 ⟨1077344, by decide⟩ ⟨13, 2, 0, 1077344, 1230946, 941, 16384⟩
    (by decide) selected_cut_39712

theorem selected_cut_39713 : selected 8 ⟨1077348, by decide⟩
    (prefixPartial 13 1230947) = some ⟨13, 2, 0, 1077348, 1230947, 541, 16384⟩ := by
  decide +kernel

theorem context_13_1230947_1077348 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1230947 ⟨1077348, by decide⟩ :=
  accepted_of_selected 13 1230947 ⟨1077348, by decide⟩ ⟨13, 2, 0, 1077348, 1230947, 541, 16384⟩
    (by decide) selected_cut_39713

theorem unmarked_context_12_307736_1077349 : frontier 9 ⟨1077349, by decide⟩
    (prefixCache 12 307736) (prefixPartial 12 307736) = false := by
  decide +kernel

theorem node_context_12_307736_1077349 : EJMOriginalGlobalDAGData.nodes 9 ⟨1077349, by decide⟩ =
    .split (coordinate 12) (![⟨1077302, by decide⟩,⟨1077322, by decide⟩,⟨1077344, by decide⟩,⟨1077348, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_307736_1077349 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307736 ⟨1077349, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 307736
    ⟨1077349, by decide⟩ (by decide) (![⟨1077302, by decide⟩,⟨1077322, by decide⟩,⟨1077344, by decide⟩,⟨1077348, by decide⟩]) unmarked_context_12_307736_1077349 node_context_12_307736_1077349
  intro a
  fin_cases a
  · exact context_13_1230944_1077302
  · exact context_13_1230945_1077322
  · exact context_13_1230946_1077344
  · exact context_13_1230947_1077348

theorem selected_cut_39714 : selected 9 ⟨1077401, by decide⟩
    (prefixPartial 12 307737) = some ⟨12, 2, 0, 1077401, 307737, 3861, 65536⟩ := by
  decide +kernel

theorem context_12_307737_1077401 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307737 ⟨1077401, by decide⟩ :=
  accepted_of_selected 12 307737 ⟨1077401, by decide⟩ ⟨12, 2, 0, 1077401, 307737, 3861, 65536⟩
    (by decide) selected_cut_39714

theorem selected_cut_39715 : selected 9 ⟨893903, by decide⟩
    (prefixPartial 12 307738) = some ⟨12, 1, 0, 893903, 307738, 1, 65536⟩ := by
  decide +kernel

theorem context_12_307738_893903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307738 ⟨893903, by decide⟩ :=
  accepted_of_selected 12 307738 ⟨893903, by decide⟩ ⟨12, 1, 0, 893903, 307738, 1, 65536⟩
    (by decide) selected_cut_39715

theorem selected_cut_39716 : selected 9 ⟨1077450, by decide⟩
    (prefixPartial 12 307739) = some ⟨12, 2, 0, 1077450, 307739, 3781, 65536⟩ := by
  decide +kernel

theorem context_12_307739_1077450 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307739 ⟨1077450, by decide⟩ :=
  accepted_of_selected 12 307739 ⟨1077450, by decide⟩ ⟨12, 2, 0, 1077450, 307739, 3781, 65536⟩
    (by decide) selected_cut_39716

theorem unmarked_context_11_76934_1077451 : frontier 10 ⟨1077451, by decide⟩
    (prefixCache 11 76934) (prefixPartial 11 76934) = false := by
  decide +kernel

theorem node_context_11_76934_1077451 : EJMOriginalGlobalDAGData.nodes 10 ⟨1077451, by decide⟩ =
    .split (coordinate 11) (![⟨1077349, by decide⟩,⟨1077401, by decide⟩,⟨893903, by decide⟩,⟨1077450, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_76934_1077451 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76934 ⟨1077451, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 76934
    ⟨1077451, by decide⟩ (by decide) (![⟨1077349, by decide⟩,⟨1077401, by decide⟩,⟨893903, by decide⟩,⟨1077450, by decide⟩]) unmarked_context_11_76934_1077451 node_context_11_76934_1077451
  intro a
  fin_cases a
  · exact context_12_307736_1077349
  · exact context_12_307737_1077401
  · exact context_12_307738_893903
  · exact context_12_307739_1077450

theorem selected_cut_39717 : selected 8 ⟨1077480, by decide⟩
    (prefixPartial 13 1230960) = some ⟨13, 2, 0, 1077480, 1230960, 1821, 16384⟩ := by
  decide +kernel

theorem context_13_1230960_1077480 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1230960 ⟨1077480, by decide⟩ :=
  accepted_of_selected 13 1230960 ⟨1077480, by decide⟩ ⟨13, 2, 0, 1077480, 1230960, 1821, 16384⟩
    (by decide) selected_cut_39717

theorem selected_cut_39718 : selected 8 ⟨1077501, by decide⟩
    (prefixPartial 13 1230961) = some ⟨13, 2, 0, 1077501, 1230961, 1553, 16384⟩ := by
  decide +kernel

theorem context_13_1230961_1077501 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1230961 ⟨1077501, by decide⟩ :=
  accepted_of_selected 13 1230961 ⟨1077501, by decide⟩ ⟨13, 2, 0, 1077501, 1230961, 1553, 16384⟩
    (by decide) selected_cut_39718

theorem selected_cut_39719 : selected 8 ⟨1077529, by decide⟩
    (prefixPartial 13 1230962) = some ⟨13, 2, 0, 1077529, 1230962, 1249, 16384⟩ := by
  decide +kernel

theorem context_13_1230962_1077529 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1230962 ⟨1077529, by decide⟩ :=
  accepted_of_selected 13 1230962 ⟨1077529, by decide⟩ ⟨13, 2, 0, 1077529, 1230962, 1249, 16384⟩
    (by decide) selected_cut_39719

theorem selected_cut_39720 : selected 8 ⟨1077536, by decide⟩
    (prefixPartial 13 1230963) = some ⟨13, 2, 0, 1077536, 1230963, 645, 16384⟩ := by
  decide +kernel

theorem context_13_1230963_1077536 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1230963 ⟨1077536, by decide⟩ :=
  accepted_of_selected 13 1230963 ⟨1077536, by decide⟩ ⟨13, 2, 0, 1077536, 1230963, 645, 16384⟩
    (by decide) selected_cut_39720

theorem unmarked_context_12_307740_1077537 : frontier 9 ⟨1077537, by decide⟩
    (prefixCache 12 307740) (prefixPartial 12 307740) = false := by
  decide +kernel

theorem node_context_12_307740_1077537 : EJMOriginalGlobalDAGData.nodes 9 ⟨1077537, by decide⟩ =
    .split (coordinate 12) (![⟨1077480, by decide⟩,⟨1077501, by decide⟩,⟨1077529, by decide⟩,⟨1077536, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_307740_1077537 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307740 ⟨1077537, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 307740
    ⟨1077537, by decide⟩ (by decide) (![⟨1077480, by decide⟩,⟨1077501, by decide⟩,⟨1077529, by decide⟩,⟨1077536, by decide⟩]) unmarked_context_12_307740_1077537 node_context_12_307740_1077537
  intro a
  fin_cases a
  · exact context_13_1230960_1077480
  · exact context_13_1230961_1077501
  · exact context_13_1230962_1077529
  · exact context_13_1230963_1077536

theorem selected_cut_39721 : selected 8 ⟨1077556, by decide⟩
    (prefixPartial 13 1230964) = some ⟨13, 2, 0, 1077556, 1230964, 1473, 16384⟩ := by
  decide +kernel

theorem context_13_1230964_1077556 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1230964 ⟨1077556, by decide⟩ :=
  accepted_of_selected 13 1230964 ⟨1077556, by decide⟩ ⟨13, 2, 0, 1077556, 1230964, 1473, 16384⟩
    (by decide) selected_cut_39721

theorem selected_cut_39722 : selected 8 ⟨1077576, by decide⟩
    (prefixPartial 13 1230965) = some ⟨13, 2, 0, 1077576, 1230965, 1385, 16384⟩ := by
  decide +kernel

theorem context_13_1230965_1077576 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1230965 ⟨1077576, by decide⟩ :=
  accepted_of_selected 13 1230965 ⟨1077576, by decide⟩ ⟨13, 2, 0, 1077576, 1230965, 1385, 16384⟩
    (by decide) selected_cut_39722

theorem selected_cut_39723 : selected 8 ⟨1077594, by decide⟩
    (prefixPartial 13 1230966) = some ⟨13, 2, 0, 1077594, 1230966, 1157, 16384⟩ := by
  decide +kernel

theorem context_13_1230966_1077594 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1230966 ⟨1077594, by decide⟩ :=
  accepted_of_selected 13 1230966 ⟨1077594, by decide⟩ ⟨13, 2, 0, 1077594, 1230966, 1157, 16384⟩
    (by decide) selected_cut_39723

theorem selected_cut_39724 : selected 8 ⟨1077599, by decide⟩
    (prefixPartial 13 1230967) = some ⟨13, 2, 0, 1077599, 1230967, 573, 16384⟩ := by
  decide +kernel

theorem context_13_1230967_1077599 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1230967 ⟨1077599, by decide⟩ :=
  accepted_of_selected 13 1230967 ⟨1077599, by decide⟩ ⟨13, 2, 0, 1077599, 1230967, 573, 16384⟩
    (by decide) selected_cut_39724

theorem unmarked_context_12_307741_1077600 : frontier 9 ⟨1077600, by decide⟩
    (prefixCache 12 307741) (prefixPartial 12 307741) = false := by
  decide +kernel

theorem node_context_12_307741_1077600 : EJMOriginalGlobalDAGData.nodes 9 ⟨1077600, by decide⟩ =
    .split (coordinate 12) (![⟨1077556, by decide⟩,⟨1077576, by decide⟩,⟨1077594, by decide⟩,⟨1077599, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_307741_1077600 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307741 ⟨1077600, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 307741
    ⟨1077600, by decide⟩ (by decide) (![⟨1077556, by decide⟩,⟨1077576, by decide⟩,⟨1077594, by decide⟩,⟨1077599, by decide⟩]) unmarked_context_12_307741_1077600 node_context_12_307741_1077600
  intro a
  fin_cases a
  · exact context_13_1230964_1077556
  · exact context_13_1230965_1077576
  · exact context_13_1230966_1077594
  · exact context_13_1230967_1077599

theorem selected_cut_39725 : selected 8 ⟨1077617, by decide⟩
    (prefixPartial 13 1230968) = some ⟨13, 2, 0, 1077617, 1230968, 1269, 16384⟩ := by
  decide +kernel

theorem context_13_1230968_1077617 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1230968 ⟨1077617, by decide⟩ :=
  accepted_of_selected 13 1230968 ⟨1077617, by decide⟩ ⟨13, 2, 0, 1077617, 1230968, 1269, 16384⟩
    (by decide) selected_cut_39725

theorem selected_cut_39726 : selected 8 ⟨1077637, by decide⟩
    (prefixPartial 13 1230969) = some ⟨13, 2, 0, 1077637, 1230969, 1469, 16384⟩ := by
  decide +kernel

theorem context_13_1230969_1077637 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1230969 ⟨1077637, by decide⟩ :=
  accepted_of_selected 13 1230969 ⟨1077637, by decide⟩ ⟨13, 2, 0, 1077637, 1230969, 1469, 16384⟩
    (by decide) selected_cut_39726

theorem selected_cut_39727 : selected 8 ⟨1077653, by decide⟩
    (prefixPartial 13 1230970) = some ⟨13, 2, 0, 1077653, 1230970, 1005, 16384⟩ := by
  decide +kernel

theorem context_13_1230970_1077653 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1230970 ⟨1077653, by decide⟩ :=
  accepted_of_selected 13 1230970 ⟨1077653, by decide⟩ ⟨13, 2, 0, 1077653, 1230970, 1005, 16384⟩
    (by decide) selected_cut_39727

theorem selected_cut_39728 : selected 8 ⟨1077661, by decide⟩
    (prefixPartial 13 1230971) = some ⟨13, 2, 0, 1077661, 1230971, 649, 16384⟩ := by
  decide +kernel

theorem context_13_1230971_1077661 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1230971 ⟨1077661, by decide⟩ :=
  accepted_of_selected 13 1230971 ⟨1077661, by decide⟩ ⟨13, 2, 0, 1077661, 1230971, 649, 16384⟩
    (by decide) selected_cut_39728

theorem unmarked_context_12_307742_1077662 : frontier 9 ⟨1077662, by decide⟩
    (prefixCache 12 307742) (prefixPartial 12 307742) = false := by
  decide +kernel

theorem node_context_12_307742_1077662 : EJMOriginalGlobalDAGData.nodes 9 ⟨1077662, by decide⟩ =
    .split (coordinate 12) (![⟨1077617, by decide⟩,⟨1077637, by decide⟩,⟨1077653, by decide⟩,⟨1077661, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_307742_1077662 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307742 ⟨1077662, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 307742
    ⟨1077662, by decide⟩ (by decide) (![⟨1077617, by decide⟩,⟨1077637, by decide⟩,⟨1077653, by decide⟩,⟨1077661, by decide⟩]) unmarked_context_12_307742_1077662 node_context_12_307742_1077662
  intro a
  fin_cases a
  · exact context_13_1230968_1077617
  · exact context_13_1230969_1077637
  · exact context_13_1230970_1077653
  · exact context_13_1230971_1077661

theorem selected_cut_39729 : selected 9 ⟨1077719, by decide⟩
    (prefixPartial 12 307743) = some ⟨12, 2, 0, 1077719, 307743, 4029, 65536⟩ := by
  decide +kernel

theorem context_12_307743_1077719 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307743 ⟨1077719, by decide⟩ :=
  accepted_of_selected 12 307743 ⟨1077719, by decide⟩ ⟨12, 2, 0, 1077719, 307743, 4029, 65536⟩
    (by decide) selected_cut_39729

theorem unmarked_context_11_76935_1077720 : frontier 10 ⟨1077720, by decide⟩
    (prefixCache 11 76935) (prefixPartial 11 76935) = false := by
  decide +kernel

theorem node_context_11_76935_1077720 : EJMOriginalGlobalDAGData.nodes 10 ⟨1077720, by decide⟩ =
    .split (coordinate 11) (![⟨1077537, by decide⟩,⟨1077600, by decide⟩,⟨1077662, by decide⟩,⟨1077719, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_76935_1077720 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76935 ⟨1077720, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 76935
    ⟨1077720, by decide⟩ (by decide) (![⟨1077537, by decide⟩,⟨1077600, by decide⟩,⟨1077662, by decide⟩,⟨1077719, by decide⟩]) unmarked_context_11_76935_1077720 node_context_11_76935_1077720
  intro a
  fin_cases a
  · exact context_12_307740_1077537
  · exact context_12_307741_1077600
  · exact context_12_307742_1077662
  · exact context_12_307743_1077719

theorem unmarked_context_10_19233_1077721 : frontier 11 ⟨1077721, by decide⟩
    (prefixCache 10 19233) (prefixPartial 10 19233) = false := by
  decide +kernel

theorem node_context_10_19233_1077721 : EJMOriginalGlobalDAGData.nodes 11 ⟨1077721, by decide⟩ =
    .split (coordinate 10) (![⟨1077074, by decide⟩,⟨1077283, by decide⟩,⟨1077451, by decide⟩,⟨1077720, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_19233_1077721 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19233 ⟨1077721, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 19233
    ⟨1077721, by decide⟩ (by decide) (![⟨1077074, by decide⟩,⟨1077283, by decide⟩,⟨1077451, by decide⟩,⟨1077720, by decide⟩]) unmarked_context_10_19233_1077721 node_context_10_19233_1077721
  intro a
  fin_cases a
  · exact context_11_76932_1077074
  · exact context_11_76933_1077283
  · exact context_11_76934_1077451
  · exact context_11_76935_1077720

theorem selected_cut_39730 : selected 9 ⟨994572, by decide⟩
    (prefixPartial 12 307744) = some ⟨12, 1, 0, 994572, 307744, 1, 65536⟩ := by
  decide +kernel

theorem context_12_307744_994572 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307744 ⟨994572, by decide⟩ :=
  accepted_of_selected 12 307744 ⟨994572, by decide⟩ ⟨12, 1, 0, 994572, 307744, 1, 65536⟩
    (by decide) selected_cut_39730

theorem selected_cut_39731 : selected 9 ⟨1077763, by decide⟩
    (prefixPartial 12 307745) = some ⟨12, 2, 0, 1077763, 307745, 3089, 65536⟩ := by
  decide +kernel

theorem context_12_307745_1077763 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307745 ⟨1077763, by decide⟩ :=
  accepted_of_selected 12 307745 ⟨1077763, by decide⟩ ⟨12, 2, 0, 1077763, 307745, 3089, 65536⟩
    (by decide) selected_cut_39731

theorem selected_cut_39732 : selected 9 ⟨1077802, by decide⟩
    (prefixPartial 12 307746) = some ⟨12, 2, 0, 1077802, 307746, 2749, 65536⟩ := by
  decide +kernel

theorem context_12_307746_1077802 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307746 ⟨1077802, by decide⟩ :=
  accepted_of_selected 12 307746 ⟨1077802, by decide⟩ ⟨12, 2, 0, 1077802, 307746, 2749, 65536⟩
    (by decide) selected_cut_39732

theorem selected_cut_39733 : selected 9 ⟨1077843, by decide⟩
    (prefixPartial 12 307747) = some ⟨12, 2, 0, 1077843, 307747, 2965, 65536⟩ := by
  decide +kernel

theorem context_12_307747_1077843 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307747 ⟨1077843, by decide⟩ :=
  accepted_of_selected 12 307747 ⟨1077843, by decide⟩ ⟨12, 2, 0, 1077843, 307747, 2965, 65536⟩
    (by decide) selected_cut_39733

theorem unmarked_context_11_76936_1077844 : frontier 10 ⟨1077844, by decide⟩
    (prefixCache 11 76936) (prefixPartial 11 76936) = false := by
  decide +kernel

theorem node_context_11_76936_1077844 : EJMOriginalGlobalDAGData.nodes 10 ⟨1077844, by decide⟩ =
    .split (coordinate 11) (![⟨994572, by decide⟩,⟨1077763, by decide⟩,⟨1077802, by decide⟩,⟨1077843, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_76936_1077844 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76936 ⟨1077844, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 76936
    ⟨1077844, by decide⟩ (by decide) (![⟨994572, by decide⟩,⟨1077763, by decide⟩,⟨1077802, by decide⟩,⟨1077843, by decide⟩]) unmarked_context_11_76936_1077844 node_context_11_76936_1077844
  intro a
  fin_cases a
  · exact context_12_307744_994572
  · exact context_12_307745_1077763
  · exact context_12_307746_1077802
  · exact context_12_307747_1077843

theorem selected_cut_39734 : selected 9 ⟨1077907, by decide⟩
    (prefixPartial 12 307748) = some ⟨12, 2, 0, 1077907, 307748, 3913, 65536⟩ := by
  decide +kernel

theorem context_12_307748_1077907 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307748 ⟨1077907, by decide⟩ :=
  accepted_of_selected 12 307748 ⟨1077907, by decide⟩ ⟨12, 2, 0, 1077907, 307748, 3913, 65536⟩
    (by decide) selected_cut_39734

theorem selected_cut_39735 : selected 9 ⟨1077961, by decide⟩
    (prefixPartial 12 307749) = some ⟨12, 2, 0, 1077961, 307749, 3869, 65536⟩ := by
  decide +kernel

theorem context_12_307749_1077961 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307749 ⟨1077961, by decide⟩ :=
  accepted_of_selected 12 307749 ⟨1077961, by decide⟩ ⟨12, 2, 0, 1077961, 307749, 3869, 65536⟩
    (by decide) selected_cut_39735

theorem selected_cut_39736 : selected 9 ⟨1078005, by decide⟩
    (prefixPartial 12 307750) = some ⟨12, 2, 0, 1078005, 307750, 3261, 65536⟩ := by
  decide +kernel

theorem context_12_307750_1078005 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307750 ⟨1078005, by decide⟩ :=
  accepted_of_selected 12 307750 ⟨1078005, by decide⟩ ⟨12, 2, 0, 1078005, 307750, 3261, 65536⟩
    (by decide) selected_cut_39736

theorem selected_cut_39737 : selected 9 ⟨1078048, by decide⟩
    (prefixPartial 12 307751) = some ⟨12, 2, 0, 1078048, 307751, 3241, 65536⟩ := by
  decide +kernel

theorem context_12_307751_1078048 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307751 ⟨1078048, by decide⟩ :=
  accepted_of_selected 12 307751 ⟨1078048, by decide⟩ ⟨12, 2, 0, 1078048, 307751, 3241, 65536⟩
    (by decide) selected_cut_39737

theorem unmarked_context_11_76937_1078049 : frontier 10 ⟨1078049, by decide⟩
    (prefixCache 11 76937) (prefixPartial 11 76937) = false := by
  decide +kernel

theorem node_context_11_76937_1078049 : EJMOriginalGlobalDAGData.nodes 10 ⟨1078049, by decide⟩ =
    .split (coordinate 11) (![⟨1077907, by decide⟩,⟨1077961, by decide⟩,⟨1078005, by decide⟩,⟨1078048, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_76937_1078049 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76937 ⟨1078049, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 76937
    ⟨1078049, by decide⟩ (by decide) (![⟨1077907, by decide⟩,⟨1077961, by decide⟩,⟨1078005, by decide⟩,⟨1078048, by decide⟩]) unmarked_context_11_76937_1078049 node_context_11_76937_1078049
  intro a
  fin_cases a
  · exact context_12_307748_1077907
  · exact context_12_307749_1077961
  · exact context_12_307750_1078005
  · exact context_12_307751_1078048

theorem selected_cut_39738 : selected 9 ⟨1078092, by decide⟩
    (prefixPartial 12 307752) = some ⟨12, 2, 0, 1078092, 307752, 3329, 65536⟩ := by
  decide +kernel

theorem context_12_307752_1078092 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307752 ⟨1078092, by decide⟩ :=
  accepted_of_selected 12 307752 ⟨1078092, by decide⟩ ⟨12, 2, 0, 1078092, 307752, 3329, 65536⟩
    (by decide) selected_cut_39738

theorem selected_cut_39739 : selected 9 ⟨1078133, by decide⟩
    (prefixPartial 12 307753) = some ⟨12, 2, 0, 1078133, 307753, 3153, 65536⟩ := by
  decide +kernel

theorem context_12_307753_1078133 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307753 ⟨1078133, by decide⟩ :=
  accepted_of_selected 12 307753 ⟨1078133, by decide⟩ ⟨12, 2, 0, 1078133, 307753, 3153, 65536⟩
    (by decide) selected_cut_39739

theorem selected_cut_39740 : selected 9 ⟨242157, by decide⟩
    (prefixPartial 12 307754) = some ⟨12, 1, 0, 242157, 307754, 1, 65536⟩ := by
  decide +kernel

theorem context_12_307754_242157 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307754 ⟨242157, by decide⟩ :=
  accepted_of_selected 12 307754 ⟨242157, by decide⟩ ⟨12, 1, 0, 242157, 307754, 1, 65536⟩
    (by decide) selected_cut_39740

theorem selected_cut_39741 : selected 9 ⟨1078168, by decide⟩
    (prefixPartial 12 307755) = some ⟨12, 2, 0, 1078168, 307755, 2969, 65536⟩ := by
  decide +kernel

theorem context_12_307755_1078168 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307755 ⟨1078168, by decide⟩ :=
  accepted_of_selected 12 307755 ⟨1078168, by decide⟩ ⟨12, 2, 0, 1078168, 307755, 2969, 65536⟩
    (by decide) selected_cut_39741

theorem unmarked_context_11_76938_1078169 : frontier 10 ⟨1078169, by decide⟩
    (prefixCache 11 76938) (prefixPartial 11 76938) = false := by
  decide +kernel

theorem node_context_11_76938_1078169 : EJMOriginalGlobalDAGData.nodes 10 ⟨1078169, by decide⟩ =
    .split (coordinate 11) (![⟨1078092, by decide⟩,⟨1078133, by decide⟩,⟨242157, by decide⟩,⟨1078168, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_76938_1078169 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76938 ⟨1078169, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 76938
    ⟨1078169, by decide⟩ (by decide) (![⟨1078092, by decide⟩,⟨1078133, by decide⟩,⟨242157, by decide⟩,⟨1078168, by decide⟩]) unmarked_context_11_76938_1078169 node_context_11_76938_1078169
  intro a
  fin_cases a
  · exact context_12_307752_1078092
  · exact context_12_307753_1078133
  · exact context_12_307754_242157
  · exact context_12_307755_1078168

theorem selected_cut_39742 : selected 9 ⟨1078229, by decide⟩
    (prefixPartial 12 307756) = some ⟨12, 2, 0, 1078229, 307756, 3625, 65536⟩ := by
  decide +kernel

theorem context_12_307756_1078229 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307756 ⟨1078229, by decide⟩ :=
  accepted_of_selected 12 307756 ⟨1078229, by decide⟩ ⟨12, 2, 0, 1078229, 307756, 3625, 65536⟩
    (by decide) selected_cut_39742

theorem selected_cut_39743 : selected 9 ⟨1078281, by decide⟩
    (prefixPartial 12 307757) = some ⟨12, 2, 0, 1078281, 307757, 3485, 65536⟩ := by
  decide +kernel

theorem context_12_307757_1078281 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307757 ⟨1078281, by decide⟩ :=
  accepted_of_selected 12 307757 ⟨1078281, by decide⟩ ⟨12, 2, 0, 1078281, 307757, 3485, 65536⟩
    (by decide) selected_cut_39743

theorem selected_cut_39744 : selected 9 ⟨1078326, by decide⟩
    (prefixPartial 12 307758) = some ⟨12, 2, 0, 1078326, 307758, 3169, 65536⟩ := by
  decide +kernel

theorem context_12_307758_1078326 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307758 ⟨1078326, by decide⟩ :=
  accepted_of_selected 12 307758 ⟨1078326, by decide⟩ ⟨12, 2, 0, 1078326, 307758, 3169, 65536⟩
    (by decide) selected_cut_39744

theorem selected_cut_39745 : selected 9 ⟨1078369, by decide⟩
    (prefixPartial 12 307759) = some ⟨12, 2, 0, 1078369, 307759, 2929, 65536⟩ := by
  decide +kernel

theorem context_12_307759_1078369 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307759 ⟨1078369, by decide⟩ :=
  accepted_of_selected 12 307759 ⟨1078369, by decide⟩ ⟨12, 2, 0, 1078369, 307759, 2929, 65536⟩
    (by decide) selected_cut_39745

theorem unmarked_context_11_76939_1078370 : frontier 10 ⟨1078370, by decide⟩
    (prefixCache 11 76939) (prefixPartial 11 76939) = false := by
  decide +kernel

theorem node_context_11_76939_1078370 : EJMOriginalGlobalDAGData.nodes 10 ⟨1078370, by decide⟩ =
    .split (coordinate 11) (![⟨1078229, by decide⟩,⟨1078281, by decide⟩,⟨1078326, by decide⟩,⟨1078369, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_76939_1078370 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76939 ⟨1078370, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 76939
    ⟨1078370, by decide⟩ (by decide) (![⟨1078229, by decide⟩,⟨1078281, by decide⟩,⟨1078326, by decide⟩,⟨1078369, by decide⟩]) unmarked_context_11_76939_1078370 node_context_11_76939_1078370
  intro a
  fin_cases a
  · exact context_12_307756_1078229
  · exact context_12_307757_1078281
  · exact context_12_307758_1078326
  · exact context_12_307759_1078369

theorem unmarked_context_10_19234_1078371 : frontier 11 ⟨1078371, by decide⟩
    (prefixCache 10 19234) (prefixPartial 10 19234) = false := by
  decide +kernel

theorem node_context_10_19234_1078371 : EJMOriginalGlobalDAGData.nodes 11 ⟨1078371, by decide⟩ =
    .split (coordinate 10) (![⟨1077844, by decide⟩,⟨1078049, by decide⟩,⟨1078169, by decide⟩,⟨1078370, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_19234_1078371 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19234 ⟨1078371, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 19234
    ⟨1078371, by decide⟩ (by decide) (![⟨1077844, by decide⟩,⟨1078049, by decide⟩,⟨1078169, by decide⟩,⟨1078370, by decide⟩]) unmarked_context_10_19234_1078371 node_context_10_19234_1078371
  intro a
  fin_cases a
  · exact context_11_76936_1077844
  · exact context_11_76937_1078049
  · exact context_11_76938_1078169
  · exact context_11_76939_1078370

theorem selected_cut_39746 : selected 9 ⟨994572, by decide⟩
    (prefixPartial 12 307760) = some ⟨12, 1, 0, 994572, 307760, 1, 65536⟩ := by
  decide +kernel

theorem context_12_307760_994572 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307760 ⟨994572, by decide⟩ :=
  accepted_of_selected 12 307760 ⟨994572, by decide⟩ ⟨12, 1, 0, 994572, 307760, 1, 65536⟩
    (by decide) selected_cut_39746

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
