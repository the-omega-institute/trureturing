/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover156
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem unmarked_context_11_6885_387902 : frontier 10 ⟨387902, by decide⟩
    (prefixCache 11 6885) (prefixPartial 11 6885) = false := by
  decide +kernel

theorem node_context_11_6885_387902 : EJMOriginalGlobalDAGData.nodes 10 ⟨387902, by decide⟩ =
    .split (coordinate 11) (![⟨387835, by decide⟩,⟨387854, by decide⟩,⟨387881, by decide⟩,⟨387901, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6885_387902 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6885 ⟨387902, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6885
    ⟨387902, by decide⟩ (by decide) (![⟨387835, by decide⟩,⟨387854, by decide⟩,⟨387881, by decide⟩,⟨387901, by decide⟩]) unmarked_context_11_6885_387902 node_context_11_6885_387902
  intro a
  fin_cases a
  · exact context_12_27540_387835
  · exact context_12_27541_387854
  · exact context_12_27542_387881
  · exact context_12_27543_387901

theorem selected_cut_15076 : selected 9 ⟨387920, by decide⟩
    (prefixPartial 12 27544) = some ⟨12, 2, 0, 387920, 27544, 1817, 65536⟩ := by
  decide +kernel

theorem context_12_27544_387920 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27544 ⟨387920, by decide⟩ :=
  accepted_of_selected 12 27544 ⟨387920, by decide⟩ ⟨12, 2, 0, 387920, 27544, 1817, 65536⟩
    (by decide) selected_cut_15076

theorem selected_cut_15077 : selected 9 ⟨387940, by decide⟩
    (prefixPartial 12 27545) = some ⟨12, 2, 0, 387940, 27545, 1853, 65536⟩ := by
  decide +kernel

theorem context_12_27545_387940 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27545 ⟨387940, by decide⟩ :=
  accepted_of_selected 12 27545 ⟨387940, by decide⟩ ⟨12, 2, 0, 387940, 27545, 1853, 65536⟩
    (by decide) selected_cut_15077

theorem selected_cut_15078 : selected 9 ⟨387964, by decide⟩
    (prefixPartial 12 27546) = some ⟨12, 2, 0, 387964, 27546, 1897, 65536⟩ := by
  decide +kernel

theorem context_12_27546_387964 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27546 ⟨387964, by decide⟩ :=
  accepted_of_selected 12 27546 ⟨387964, by decide⟩ ⟨12, 2, 0, 387964, 27546, 1897, 65536⟩
    (by decide) selected_cut_15078

theorem selected_cut_15079 : selected 9 ⟨387981, by decide⟩
    (prefixPartial 12 27547) = some ⟨12, 2, 0, 387981, 27547, 1517, 65536⟩ := by
  decide +kernel

theorem context_12_27547_387981 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27547 ⟨387981, by decide⟩ :=
  accepted_of_selected 12 27547 ⟨387981, by decide⟩ ⟨12, 2, 0, 387981, 27547, 1517, 65536⟩
    (by decide) selected_cut_15079

theorem unmarked_context_11_6886_387982 : frontier 10 ⟨387982, by decide⟩
    (prefixCache 11 6886) (prefixPartial 11 6886) = false := by
  decide +kernel

theorem node_context_11_6886_387982 : EJMOriginalGlobalDAGData.nodes 10 ⟨387982, by decide⟩ =
    .split (coordinate 11) (![⟨387920, by decide⟩,⟨387940, by decide⟩,⟨387964, by decide⟩,⟨387981, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6886_387982 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6886 ⟨387982, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6886
    ⟨387982, by decide⟩ (by decide) (![⟨387920, by decide⟩,⟨387940, by decide⟩,⟨387964, by decide⟩,⟨387981, by decide⟩]) unmarked_context_11_6886_387982 node_context_11_6886_387982
  intro a
  fin_cases a
  · exact context_12_27544_387920
  · exact context_12_27545_387940
  · exact context_12_27546_387964
  · exact context_12_27547_387981

theorem selected_cut_15080 : selected 9 ⟨388000, by decide⟩
    (prefixPartial 12 27548) = some ⟨12, 2, 0, 388000, 27548, 1625, 65536⟩ := by
  decide +kernel

theorem context_12_27548_388000 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27548 ⟨388000, by decide⟩ :=
  accepted_of_selected 12 27548 ⟨388000, by decide⟩ ⟨12, 2, 0, 388000, 27548, 1625, 65536⟩
    (by decide) selected_cut_15080

theorem selected_cut_15081 : selected 9 ⟨388015, by decide⟩
    (prefixPartial 12 27549) = some ⟨12, 2, 0, 388015, 27549, 1613, 65536⟩ := by
  decide +kernel

theorem context_12_27549_388015 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27549 ⟨388015, by decide⟩ :=
  accepted_of_selected 12 27549 ⟨388015, by decide⟩ ⟨12, 2, 0, 388015, 27549, 1613, 65536⟩
    (by decide) selected_cut_15081

theorem selected_cut_15082 : selected 9 ⟨388031, by decide⟩
    (prefixPartial 12 27550) = some ⟨12, 2, 0, 388031, 27550, 1633, 65536⟩ := by
  decide +kernel

theorem context_12_27550_388031 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27550 ⟨388031, by decide⟩ :=
  accepted_of_selected 12 27550 ⟨388031, by decide⟩ ⟨12, 2, 0, 388031, 27550, 1633, 65536⟩
    (by decide) selected_cut_15082

theorem selected_cut_15083 : selected 9 ⟨388073, by decide⟩
    (prefixPartial 12 27551) = some ⟨12, 2, 0, 388073, 27551, 2205, 65536⟩ := by
  decide +kernel

theorem context_12_27551_388073 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27551 ⟨388073, by decide⟩ :=
  accepted_of_selected 12 27551 ⟨388073, by decide⟩ ⟨12, 2, 0, 388073, 27551, 2205, 65536⟩
    (by decide) selected_cut_15083

theorem unmarked_context_11_6887_388074 : frontier 10 ⟨388074, by decide⟩
    (prefixCache 11 6887) (prefixPartial 11 6887) = false := by
  decide +kernel

theorem node_context_11_6887_388074 : EJMOriginalGlobalDAGData.nodes 10 ⟨388074, by decide⟩ =
    .split (coordinate 11) (![⟨388000, by decide⟩,⟨388015, by decide⟩,⟨388031, by decide⟩,⟨388073, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6887_388074 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6887 ⟨388074, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6887
    ⟨388074, by decide⟩ (by decide) (![⟨388000, by decide⟩,⟨388015, by decide⟩,⟨388031, by decide⟩,⟨388073, by decide⟩]) unmarked_context_11_6887_388074 node_context_11_6887_388074
  intro a
  fin_cases a
  · exact context_12_27548_388000
  · exact context_12_27549_388015
  · exact context_12_27550_388031
  · exact context_12_27551_388073

theorem unmarked_context_10_1721_388075 : frontier 11 ⟨388075, by decide⟩
    (prefixCache 10 1721) (prefixPartial 10 1721) = false := by
  decide +kernel

theorem node_context_10_1721_388075 : EJMOriginalGlobalDAGData.nodes 11 ⟨388075, by decide⟩ =
    .split (coordinate 10) (![⟨387813, by decide⟩,⟨387902, by decide⟩,⟨387982, by decide⟩,⟨388074, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1721_388075 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1721 ⟨388075, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1721
    ⟨388075, by decide⟩ (by decide) (![⟨387813, by decide⟩,⟨387902, by decide⟩,⟨387982, by decide⟩,⟨388074, by decide⟩]) unmarked_context_10_1721_388075 node_context_10_1721_388075
  intro a
  fin_cases a
  · exact context_11_6884_387813
  · exact context_11_6885_387902
  · exact context_11_6886_387982
  · exact context_11_6887_388074

theorem selected_cut_15084 : selected 9 ⟨388089, by decide⟩
    (prefixPartial 12 27552) = some ⟨12, 2, 0, 388089, 27552, 1425, 65536⟩ := by
  decide +kernel

theorem context_12_27552_388089 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27552 ⟨388089, by decide⟩ :=
  accepted_of_selected 12 27552 ⟨388089, by decide⟩ ⟨12, 2, 0, 388089, 27552, 1425, 65536⟩
    (by decide) selected_cut_15084

theorem selected_cut_15085 : selected 9 ⟨388103, by decide⟩
    (prefixPartial 12 27553) = some ⟨12, 2, 0, 388103, 27553, 1353, 65536⟩ := by
  decide +kernel

theorem context_12_27553_388103 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27553 ⟨388103, by decide⟩ :=
  accepted_of_selected 12 27553 ⟨388103, by decide⟩ ⟨12, 2, 0, 388103, 27553, 1353, 65536⟩
    (by decide) selected_cut_15085

theorem selected_cut_15086 : selected 9 ⟨388113, by decide⟩
    (prefixPartial 12 27554) = some ⟨12, 2, 0, 388113, 27554, 1269, 65536⟩ := by
  decide +kernel

theorem context_12_27554_388113 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27554 ⟨388113, by decide⟩ :=
  accepted_of_selected 12 27554 ⟨388113, by decide⟩ ⟨12, 2, 0, 388113, 27554, 1269, 65536⟩
    (by decide) selected_cut_15086

theorem selected_cut_15087 : selected 9 ⟨388123, by decide⟩
    (prefixPartial 12 27555) = some ⟨12, 2, 0, 388123, 27555, 1173, 65536⟩ := by
  decide +kernel

theorem context_12_27555_388123 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27555 ⟨388123, by decide⟩ :=
  accepted_of_selected 12 27555 ⟨388123, by decide⟩ ⟨12, 2, 0, 388123, 27555, 1173, 65536⟩
    (by decide) selected_cut_15087

theorem unmarked_context_11_6888_388124 : frontier 10 ⟨388124, by decide⟩
    (prefixCache 11 6888) (prefixPartial 11 6888) = false := by
  decide +kernel

theorem node_context_11_6888_388124 : EJMOriginalGlobalDAGData.nodes 10 ⟨388124, by decide⟩ =
    .split (coordinate 11) (![⟨388089, by decide⟩,⟨388103, by decide⟩,⟨388113, by decide⟩,⟨388123, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6888_388124 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6888 ⟨388124, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6888
    ⟨388124, by decide⟩ (by decide) (![⟨388089, by decide⟩,⟨388103, by decide⟩,⟨388113, by decide⟩,⟨388123, by decide⟩]) unmarked_context_11_6888_388124 node_context_11_6888_388124
  intro a
  fin_cases a
  · exact context_12_27552_388089
  · exact context_12_27553_388103
  · exact context_12_27554_388113
  · exact context_12_27555_388123

theorem selected_cut_15088 : selected 9 ⟨388143, by decide⟩
    (prefixPartial 12 27556) = some ⟨12, 2, 0, 388143, 27556, 1541, 65536⟩ := by
  decide +kernel

theorem context_12_27556_388143 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27556 ⟨388143, by decide⟩ :=
  accepted_of_selected 12 27556 ⟨388143, by decide⟩ ⟨12, 2, 0, 388143, 27556, 1541, 65536⟩
    (by decide) selected_cut_15088

theorem selected_cut_15089 : selected 9 ⟨388156, by decide⟩
    (prefixPartial 12 27557) = some ⟨12, 2, 0, 388156, 27557, 1469, 65536⟩ := by
  decide +kernel

theorem context_12_27557_388156 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27557 ⟨388156, by decide⟩ :=
  accepted_of_selected 12 27557 ⟨388156, by decide⟩ ⟨12, 2, 0, 388156, 27557, 1469, 65536⟩
    (by decide) selected_cut_15089

theorem selected_cut_15090 : selected 9 ⟨388168, by decide⟩
    (prefixPartial 12 27558) = some ⟨12, 2, 0, 388168, 27558, 1453, 65536⟩ := by
  decide +kernel

theorem context_12_27558_388168 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27558 ⟨388168, by decide⟩ :=
  accepted_of_selected 12 27558 ⟨388168, by decide⟩ ⟨12, 2, 0, 388168, 27558, 1453, 65536⟩
    (by decide) selected_cut_15090

theorem selected_cut_15091 : selected 9 ⟨388182, by decide⟩
    (prefixPartial 12 27559) = some ⟨12, 2, 0, 388182, 27559, 1341, 65536⟩ := by
  decide +kernel

theorem context_12_27559_388182 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27559 ⟨388182, by decide⟩ :=
  accepted_of_selected 12 27559 ⟨388182, by decide⟩ ⟨12, 2, 0, 388182, 27559, 1341, 65536⟩
    (by decide) selected_cut_15091

theorem unmarked_context_11_6889_388183 : frontier 10 ⟨388183, by decide⟩
    (prefixCache 11 6889) (prefixPartial 11 6889) = false := by
  decide +kernel

theorem node_context_11_6889_388183 : EJMOriginalGlobalDAGData.nodes 10 ⟨388183, by decide⟩ =
    .split (coordinate 11) (![⟨388143, by decide⟩,⟨388156, by decide⟩,⟨388168, by decide⟩,⟨388182, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6889_388183 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6889 ⟨388183, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6889
    ⟨388183, by decide⟩ (by decide) (![⟨388143, by decide⟩,⟨388156, by decide⟩,⟨388168, by decide⟩,⟨388182, by decide⟩]) unmarked_context_11_6889_388183 node_context_11_6889_388183
  intro a
  fin_cases a
  · exact context_12_27556_388143
  · exact context_12_27557_388156
  · exact context_12_27558_388168
  · exact context_12_27559_388182

theorem selected_cut_15092 : selected 10 ⟨388210, by decide⟩
    (prefixPartial 11 6890) = some ⟨11, 2, 0, 388210, 6890, 1765, 262144⟩ := by
  decide +kernel

theorem context_11_6890_388210 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6890 ⟨388210, by decide⟩ :=
  accepted_of_selected 11 6890 ⟨388210, by decide⟩ ⟨11, 2, 0, 388210, 6890, 1765, 262144⟩
    (by decide) selected_cut_15092

theorem selected_cut_15093 : selected 9 ⟨388221, by decide⟩
    (prefixPartial 12 27564) = some ⟨12, 2, 0, 388221, 27564, 1345, 65536⟩ := by
  decide +kernel

theorem context_12_27564_388221 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27564 ⟨388221, by decide⟩ :=
  accepted_of_selected 12 27564 ⟨388221, by decide⟩ ⟨12, 2, 0, 388221, 27564, 1345, 65536⟩
    (by decide) selected_cut_15093

theorem selected_cut_15094 : selected 9 ⟨388232, by decide⟩
    (prefixPartial 12 27565) = some ⟨12, 2, 0, 388232, 27565, 1285, 65536⟩ := by
  decide +kernel

theorem context_12_27565_388232 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27565 ⟨388232, by decide⟩ :=
  accepted_of_selected 12 27565 ⟨388232, by decide⟩ ⟨12, 2, 0, 388232, 27565, 1285, 65536⟩
    (by decide) selected_cut_15094

theorem selected_cut_15095 : selected 9 ⟨388241, by decide⟩
    (prefixPartial 12 27566) = some ⟨12, 2, 0, 388241, 27566, 1181, 65536⟩ := by
  decide +kernel

theorem context_12_27566_388241 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27566 ⟨388241, by decide⟩ :=
  accepted_of_selected 12 27566 ⟨388241, by decide⟩ ⟨12, 2, 0, 388241, 27566, 1181, 65536⟩
    (by decide) selected_cut_15095

theorem selected_cut_15096 : selected 9 ⟨388261, by decide⟩
    (prefixPartial 12 27567) = some ⟨12, 2, 0, 388261, 27567, 1665, 65536⟩ := by
  decide +kernel

theorem context_12_27567_388261 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27567 ⟨388261, by decide⟩ :=
  accepted_of_selected 12 27567 ⟨388261, by decide⟩ ⟨12, 2, 0, 388261, 27567, 1665, 65536⟩
    (by decide) selected_cut_15096

theorem unmarked_context_11_6891_388262 : frontier 10 ⟨388262, by decide⟩
    (prefixCache 11 6891) (prefixPartial 11 6891) = false := by
  decide +kernel

theorem node_context_11_6891_388262 : EJMOriginalGlobalDAGData.nodes 10 ⟨388262, by decide⟩ =
    .split (coordinate 11) (![⟨388221, by decide⟩,⟨388232, by decide⟩,⟨388241, by decide⟩,⟨388261, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6891_388262 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6891 ⟨388262, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6891
    ⟨388262, by decide⟩ (by decide) (![⟨388221, by decide⟩,⟨388232, by decide⟩,⟨388241, by decide⟩,⟨388261, by decide⟩]) unmarked_context_11_6891_388262 node_context_11_6891_388262
  intro a
  fin_cases a
  · exact context_12_27564_388221
  · exact context_12_27565_388232
  · exact context_12_27566_388241
  · exact context_12_27567_388261

theorem unmarked_context_10_1722_388263 : frontier 11 ⟨388263, by decide⟩
    (prefixCache 10 1722) (prefixPartial 10 1722) = false := by
  decide +kernel

theorem node_context_10_1722_388263 : EJMOriginalGlobalDAGData.nodes 11 ⟨388263, by decide⟩ =
    .split (coordinate 10) (![⟨388124, by decide⟩,⟨388183, by decide⟩,⟨388210, by decide⟩,⟨388262, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1722_388263 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1722 ⟨388263, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1722
    ⟨388263, by decide⟩ (by decide) (![⟨388124, by decide⟩,⟨388183, by decide⟩,⟨388210, by decide⟩,⟨388262, by decide⟩]) unmarked_context_10_1722_388263 node_context_10_1722_388263
  intro a
  fin_cases a
  · exact context_11_6888_388124
  · exact context_11_6889_388183
  · exact context_11_6890_388210
  · exact context_11_6891_388262

theorem selected_cut_15097 : selected 9 ⟨388280, by decide⟩
    (prefixPartial 12 27568) = some ⟨12, 2, 0, 388280, 27568, 1445, 65536⟩ := by
  decide +kernel

theorem context_12_27568_388280 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27568 ⟨388280, by decide⟩ :=
  accepted_of_selected 12 27568 ⟨388280, by decide⟩ ⟨12, 2, 0, 388280, 27568, 1445, 65536⟩
    (by decide) selected_cut_15097

theorem selected_cut_15098 : selected 9 ⟨388295, by decide⟩
    (prefixPartial 12 27569) = some ⟨12, 2, 0, 388295, 27569, 1385, 65536⟩ := by
  decide +kernel

theorem context_12_27569_388295 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27569 ⟨388295, by decide⟩ :=
  accepted_of_selected 12 27569 ⟨388295, by decide⟩ ⟨12, 2, 0, 388295, 27569, 1385, 65536⟩
    (by decide) selected_cut_15098

theorem selected_cut_15099 : selected 9 ⟨388311, by decide⟩
    (prefixPartial 12 27570) = some ⟨12, 2, 0, 388311, 27570, 1269, 65536⟩ := by
  decide +kernel

theorem context_12_27570_388311 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27570 ⟨388311, by decide⟩ :=
  accepted_of_selected 12 27570 ⟨388311, by decide⟩ ⟨12, 2, 0, 388311, 27570, 1269, 65536⟩
    (by decide) selected_cut_15099

theorem selected_cut_15100 : selected 9 ⟨388324, by decide⟩
    (prefixPartial 12 27571) = some ⟨12, 2, 0, 388324, 27571, 1213, 65536⟩ := by
  decide +kernel

theorem context_12_27571_388324 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27571 ⟨388324, by decide⟩ :=
  accepted_of_selected 12 27571 ⟨388324, by decide⟩ ⟨12, 2, 0, 388324, 27571, 1213, 65536⟩
    (by decide) selected_cut_15100

theorem unmarked_context_11_6892_388325 : frontier 10 ⟨388325, by decide⟩
    (prefixCache 11 6892) (prefixPartial 11 6892) = false := by
  decide +kernel

theorem node_context_11_6892_388325 : EJMOriginalGlobalDAGData.nodes 10 ⟨388325, by decide⟩ =
    .split (coordinate 11) (![⟨388280, by decide⟩,⟨388295, by decide⟩,⟨388311, by decide⟩,⟨388324, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6892_388325 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6892 ⟨388325, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6892
    ⟨388325, by decide⟩ (by decide) (![⟨388280, by decide⟩,⟨388295, by decide⟩,⟨388311, by decide⟩,⟨388324, by decide⟩]) unmarked_context_11_6892_388325 node_context_11_6892_388325
  intro a
  fin_cases a
  · exact context_12_27568_388280
  · exact context_12_27569_388295
  · exact context_12_27570_388311
  · exact context_12_27571_388324

theorem selected_cut_15101 : selected 9 ⟨388335, by decide⟩
    (prefixPartial 12 27572) = some ⟨12, 2, 0, 388335, 27572, 1341, 65536⟩ := by
  decide +kernel

theorem context_12_27572_388335 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27572 ⟨388335, by decide⟩ :=
  accepted_of_selected 12 27572 ⟨388335, by decide⟩ ⟨12, 2, 0, 388335, 27572, 1341, 65536⟩
    (by decide) selected_cut_15101

theorem selected_cut_15102 : selected 9 ⟨388346, by decide⟩
    (prefixPartial 12 27573) = some ⟨12, 2, 0, 388346, 27573, 1313, 65536⟩ := by
  decide +kernel

theorem context_12_27573_388346 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27573 ⟨388346, by decide⟩ :=
  accepted_of_selected 12 27573 ⟨388346, by decide⟩ ⟨12, 2, 0, 388346, 27573, 1313, 65536⟩
    (by decide) selected_cut_15102

theorem selected_cut_15103 : selected 9 ⟨388363, by decide⟩
    (prefixPartial 12 27574) = some ⟨12, 2, 0, 388363, 27574, 1325, 65536⟩ := by
  decide +kernel

theorem context_12_27574_388363 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27574 ⟨388363, by decide⟩ :=
  accepted_of_selected 12 27574 ⟨388363, by decide⟩ ⟨12, 2, 0, 388363, 27574, 1325, 65536⟩
    (by decide) selected_cut_15103

theorem selected_cut_15104 : selected 9 ⟨388377, by decide⟩
    (prefixPartial 12 27575) = some ⟨12, 2, 0, 388377, 27575, 1237, 65536⟩ := by
  decide +kernel

theorem context_12_27575_388377 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27575 ⟨388377, by decide⟩ :=
  accepted_of_selected 12 27575 ⟨388377, by decide⟩ ⟨12, 2, 0, 388377, 27575, 1237, 65536⟩
    (by decide) selected_cut_15104

theorem unmarked_context_11_6893_388378 : frontier 10 ⟨388378, by decide⟩
    (prefixCache 11 6893) (prefixPartial 11 6893) = false := by
  decide +kernel

theorem node_context_11_6893_388378 : EJMOriginalGlobalDAGData.nodes 10 ⟨388378, by decide⟩ =
    .split (coordinate 11) (![⟨388335, by decide⟩,⟨388346, by decide⟩,⟨388363, by decide⟩,⟨388377, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6893_388378 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6893 ⟨388378, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6893
    ⟨388378, by decide⟩ (by decide) (![⟨388335, by decide⟩,⟨388346, by decide⟩,⟨388363, by decide⟩,⟨388377, by decide⟩]) unmarked_context_11_6893_388378 node_context_11_6893_388378
  intro a
  fin_cases a
  · exact context_12_27572_388335
  · exact context_12_27573_388346
  · exact context_12_27574_388363
  · exact context_12_27575_388377

theorem selected_cut_15105 : selected 9 ⟨388406, by decide⟩
    (prefixPartial 12 27576) = some ⟨12, 2, 0, 388406, 27576, 1297, 65536⟩ := by
  decide +kernel

theorem context_12_27576_388406 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27576 ⟨388406, by decide⟩ :=
  accepted_of_selected 12 27576 ⟨388406, by decide⟩ ⟨12, 2, 0, 388406, 27576, 1297, 65536⟩
    (by decide) selected_cut_15105

theorem selected_cut_15106 : selected 9 ⟨388427, by decide⟩
    (prefixPartial 12 27577) = some ⟨12, 2, 0, 388427, 27577, 1361, 65536⟩ := by
  decide +kernel

theorem context_12_27577_388427 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27577 ⟨388427, by decide⟩ :=
  accepted_of_selected 12 27577 ⟨388427, by decide⟩ ⟨12, 2, 0, 388427, 27577, 1361, 65536⟩
    (by decide) selected_cut_15106

theorem selected_cut_15107 : selected 9 ⟨388441, by decide⟩
    (prefixPartial 12 27578) = some ⟨12, 2, 0, 388441, 27578, 1173, 65536⟩ := by
  decide +kernel

theorem context_12_27578_388441 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27578 ⟨388441, by decide⟩ :=
  accepted_of_selected 12 27578 ⟨388441, by decide⟩ ⟨12, 2, 0, 388441, 27578, 1173, 65536⟩
    (by decide) selected_cut_15107

theorem selected_cut_15108 : selected 9 ⟨388452, by decide⟩
    (prefixPartial 12 27579) = some ⟨12, 2, 0, 388452, 27579, 1101, 65536⟩ := by
  decide +kernel

theorem context_12_27579_388452 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27579 ⟨388452, by decide⟩ :=
  accepted_of_selected 12 27579 ⟨388452, by decide⟩ ⟨12, 2, 0, 388452, 27579, 1101, 65536⟩
    (by decide) selected_cut_15108

theorem unmarked_context_11_6894_388453 : frontier 10 ⟨388453, by decide⟩
    (prefixCache 11 6894) (prefixPartial 11 6894) = false := by
  decide +kernel

theorem node_context_11_6894_388453 : EJMOriginalGlobalDAGData.nodes 10 ⟨388453, by decide⟩ =
    .split (coordinate 11) (![⟨388406, by decide⟩,⟨388427, by decide⟩,⟨388441, by decide⟩,⟨388452, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6894_388453 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6894 ⟨388453, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6894
    ⟨388453, by decide⟩ (by decide) (![⟨388406, by decide⟩,⟨388427, by decide⟩,⟨388441, by decide⟩,⟨388452, by decide⟩]) unmarked_context_11_6894_388453 node_context_11_6894_388453
  intro a
  fin_cases a
  · exact context_12_27576_388406
  · exact context_12_27577_388427
  · exact context_12_27578_388441
  · exact context_12_27579_388452

theorem selected_cut_15109 : selected 10 ⟨388490, by decide⟩
    (prefixPartial 11 6895) = some ⟨11, 2, 0, 388490, 6895, 3193, 262144⟩ := by
  decide +kernel

theorem context_11_6895_388490 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6895 ⟨388490, by decide⟩ :=
  accepted_of_selected 11 6895 ⟨388490, by decide⟩ ⟨11, 2, 0, 388490, 6895, 3193, 262144⟩
    (by decide) selected_cut_15109

theorem unmarked_context_10_1723_388491 : frontier 11 ⟨388491, by decide⟩
    (prefixCache 10 1723) (prefixPartial 10 1723) = false := by
  decide +kernel

theorem node_context_10_1723_388491 : EJMOriginalGlobalDAGData.nodes 11 ⟨388491, by decide⟩ =
    .split (coordinate 10) (![⟨388325, by decide⟩,⟨388378, by decide⟩,⟨388453, by decide⟩,⟨388490, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1723_388491 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1723 ⟨388491, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1723
    ⟨388491, by decide⟩ (by decide) (![⟨388325, by decide⟩,⟨388378, by decide⟩,⟨388453, by decide⟩,⟨388490, by decide⟩]) unmarked_context_10_1723_388491 node_context_10_1723_388491
  intro a
  fin_cases a
  · exact context_11_6892_388325
  · exact context_11_6893_388378
  · exact context_11_6894_388453
  · exact context_11_6895_388490

theorem unmarked_context_9_430_388492 : frontier 12 ⟨388492, by decide⟩
    (prefixCache 9 430) (prefixPartial 9 430) = false := by
  decide +kernel

theorem node_context_9_430_388492 : EJMOriginalGlobalDAGData.nodes 12 ⟨388492, by decide⟩ =
    .split (coordinate 9) (![⟨387722, by decide⟩,⟨388075, by decide⟩,⟨388263, by decide⟩,⟨388491, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_430_388492 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 430 ⟨388492, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 430
    ⟨388492, by decide⟩ (by decide) (![⟨387722, by decide⟩,⟨388075, by decide⟩,⟨388263, by decide⟩,⟨388491, by decide⟩]) unmarked_context_9_430_388492 node_context_9_430_388492
  intro a
  fin_cases a
  · exact context_10_1720_387722
  · exact context_10_1721_388075
  · exact context_10_1722_388263
  · exact context_10_1723_388491

theorem selected_cut_15110 : selected 10 ⟨388515, by decide⟩
    (prefixPartial 11 6896) = some ⟨11, 2, 0, 388515, 6896, 2565, 262144⟩ := by
  decide +kernel

theorem context_11_6896_388515 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6896 ⟨388515, by decide⟩ :=
  accepted_of_selected 11 6896 ⟨388515, by decide⟩ ⟨11, 2, 0, 388515, 6896, 2565, 262144⟩
    (by decide) selected_cut_15110

theorem selected_cut_15111 : selected 10 ⟨388545, by decide⟩
    (prefixPartial 11 6897) = some ⟨11, 2, 0, 388545, 6897, 2837, 262144⟩ := by
  decide +kernel

theorem context_11_6897_388545 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6897 ⟨388545, by decide⟩ :=
  accepted_of_selected 11 6897 ⟨388545, by decide⟩ ⟨11, 2, 0, 388545, 6897, 2837, 262144⟩
    (by decide) selected_cut_15111

theorem selected_cut_15112 : selected 10 ⟨388574, by decide⟩
    (prefixPartial 11 6898) = some ⟨11, 2, 0, 388574, 6898, 2629, 262144⟩ := by
  decide +kernel

theorem context_11_6898_388574 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6898 ⟨388574, by decide⟩ :=
  accepted_of_selected 11 6898 ⟨388574, by decide⟩ ⟨11, 2, 0, 388574, 6898, 2629, 262144⟩
    (by decide) selected_cut_15112

theorem selected_cut_15113 : selected 10 ⟨388604, by decide⟩
    (prefixPartial 11 6899) = some ⟨11, 2, 0, 388604, 6899, 2561, 262144⟩ := by
  decide +kernel

theorem context_11_6899_388604 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6899 ⟨388604, by decide⟩ :=
  accepted_of_selected 11 6899 ⟨388604, by decide⟩ ⟨11, 2, 0, 388604, 6899, 2561, 262144⟩
    (by decide) selected_cut_15113

theorem unmarked_context_10_1724_388605 : frontier 11 ⟨388605, by decide⟩
    (prefixCache 10 1724) (prefixPartial 10 1724) = false := by
  decide +kernel

theorem node_context_10_1724_388605 : EJMOriginalGlobalDAGData.nodes 11 ⟨388605, by decide⟩ =
    .split (coordinate 10) (![⟨388515, by decide⟩,⟨388545, by decide⟩,⟨388574, by decide⟩,⟨388604, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1724_388605 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1724 ⟨388605, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1724
    ⟨388605, by decide⟩ (by decide) (![⟨388515, by decide⟩,⟨388545, by decide⟩,⟨388574, by decide⟩,⟨388604, by decide⟩]) unmarked_context_10_1724_388605 node_context_10_1724_388605
  intro a
  fin_cases a
  · exact context_11_6896_388515
  · exact context_11_6897_388545
  · exact context_11_6898_388574
  · exact context_11_6899_388604

theorem selected_cut_15114 : selected 10 ⟨388635, by decide⟩
    (prefixPartial 11 6900) = some ⟨11, 2, 0, 388635, 6900, 2429, 262144⟩ := by
  decide +kernel

theorem context_11_6900_388635 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6900 ⟨388635, by decide⟩ :=
  accepted_of_selected 11 6900 ⟨388635, by decide⟩ ⟨11, 2, 0, 388635, 6900, 2429, 262144⟩
    (by decide) selected_cut_15114

theorem selected_cut_15115 : selected 10 ⟨388660, by decide⟩
    (prefixPartial 11 6901) = some ⟨11, 2, 0, 388660, 6901, 2461, 262144⟩ := by
  decide +kernel

theorem context_11_6901_388660 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6901 ⟨388660, by decide⟩ :=
  accepted_of_selected 11 6901 ⟨388660, by decide⟩ ⟨11, 2, 0, 388660, 6901, 2461, 262144⟩
    (by decide) selected_cut_15115

theorem selected_cut_15116 : selected 10 ⟨388684, by decide⟩
    (prefixPartial 11 6902) = some ⟨11, 2, 0, 388684, 6902, 1953, 262144⟩ := by
  decide +kernel

theorem context_11_6902_388684 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6902 ⟨388684, by decide⟩ :=
  accepted_of_selected 11 6902 ⟨388684, by decide⟩ ⟨11, 2, 0, 388684, 6902, 1953, 262144⟩
    (by decide) selected_cut_15116

theorem selected_cut_15117 : selected 10 ⟨388704, by decide⟩
    (prefixPartial 11 6903) = some ⟨11, 2, 0, 388704, 6903, 1261, 262144⟩ := by
  decide +kernel

theorem context_11_6903_388704 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6903 ⟨388704, by decide⟩ :=
  accepted_of_selected 11 6903 ⟨388704, by decide⟩ ⟨11, 2, 0, 388704, 6903, 1261, 262144⟩
    (by decide) selected_cut_15117

theorem unmarked_context_10_1725_388705 : frontier 11 ⟨388705, by decide⟩
    (prefixCache 10 1725) (prefixPartial 10 1725) = false := by
  decide +kernel

theorem node_context_10_1725_388705 : EJMOriginalGlobalDAGData.nodes 11 ⟨388705, by decide⟩ =
    .split (coordinate 10) (![⟨388635, by decide⟩,⟨388660, by decide⟩,⟨388684, by decide⟩,⟨388704, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1725_388705 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1725 ⟨388705, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1725
    ⟨388705, by decide⟩ (by decide) (![⟨388635, by decide⟩,⟨388660, by decide⟩,⟨388684, by decide⟩,⟨388704, by decide⟩]) unmarked_context_10_1725_388705 node_context_10_1725_388705
  intro a
  fin_cases a
  · exact context_11_6900_388635
  · exact context_11_6901_388660
  · exact context_11_6902_388684
  · exact context_11_6903_388704

theorem selected_cut_15118 : selected 10 ⟨388728, by decide⟩
    (prefixPartial 11 6904) = some ⟨11, 2, 0, 388728, 6904, 1429, 262144⟩ := by
  decide +kernel

theorem context_11_6904_388728 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6904 ⟨388728, by decide⟩ :=
  accepted_of_selected 11 6904 ⟨388728, by decide⟩ ⟨11, 2, 0, 388728, 6904, 1429, 262144⟩
    (by decide) selected_cut_15118

theorem selected_cut_15119 : selected 10 ⟨388747, by decide⟩
    (prefixPartial 11 6905) = some ⟨11, 2, 0, 388747, 6905, 1277, 262144⟩ := by
  decide +kernel

theorem context_11_6905_388747 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6905 ⟨388747, by decide⟩ :=
  accepted_of_selected 11 6905 ⟨388747, by decide⟩ ⟨11, 2, 0, 388747, 6905, 1277, 262144⟩
    (by decide) selected_cut_15119

theorem selected_cut_15120 : selected 10 ⟨388769, by decide⟩
    (prefixPartial 11 6906) = some ⟨11, 2, 0, 388769, 6906, 961, 262144⟩ := by
  decide +kernel

theorem context_11_6906_388769 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6906 ⟨388769, by decide⟩ :=
  accepted_of_selected 11 6906 ⟨388769, by decide⟩ ⟨11, 2, 0, 388769, 6906, 961, 262144⟩
    (by decide) selected_cut_15120

theorem selected_cut_15121 : selected 10 ⟨388783, by decide⟩
    (prefixPartial 11 6907) = some ⟨11, 2, 0, 388783, 6907, 665, 262144⟩ := by
  decide +kernel

theorem context_11_6907_388783 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6907 ⟨388783, by decide⟩ :=
  accepted_of_selected 11 6907 ⟨388783, by decide⟩ ⟨11, 2, 0, 388783, 6907, 665, 262144⟩
    (by decide) selected_cut_15121

theorem unmarked_context_10_1726_388784 : frontier 11 ⟨388784, by decide⟩
    (prefixCache 10 1726) (prefixPartial 10 1726) = false := by
  decide +kernel

theorem node_context_10_1726_388784 : EJMOriginalGlobalDAGData.nodes 11 ⟨388784, by decide⟩ =
    .split (coordinate 10) (![⟨388728, by decide⟩,⟨388747, by decide⟩,⟨388769, by decide⟩,⟨388783, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1726_388784 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1726 ⟨388784, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1726
    ⟨388784, by decide⟩ (by decide) (![⟨388728, by decide⟩,⟨388747, by decide⟩,⟨388769, by decide⟩,⟨388783, by decide⟩]) unmarked_context_10_1726_388784 node_context_10_1726_388784
  intro a
  fin_cases a
  · exact context_11_6904_388728
  · exact context_11_6905_388747
  · exact context_11_6906_388769
  · exact context_11_6907_388783

theorem selected_cut_15122 : selected 11 ⟨388825, by decide⟩
    (prefixPartial 10 1727) = some ⟨10, 2, 0, 388825, 1727, 1553, 1048576⟩ := by
  decide +kernel

theorem context_10_1727_388825 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1727 ⟨388825, by decide⟩ :=
  accepted_of_selected 10 1727 ⟨388825, by decide⟩ ⟨10, 2, 0, 388825, 1727, 1553, 1048576⟩
    (by decide) selected_cut_15122

theorem unmarked_context_9_431_388826 : frontier 12 ⟨388826, by decide⟩
    (prefixCache 9 431) (prefixPartial 9 431) = false := by
  decide +kernel

theorem node_context_9_431_388826 : EJMOriginalGlobalDAGData.nodes 12 ⟨388826, by decide⟩ =
    .split (coordinate 9) (![⟨388605, by decide⟩,⟨388705, by decide⟩,⟨388784, by decide⟩,⟨388825, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_431_388826 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 431 ⟨388826, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 431
    ⟨388826, by decide⟩ (by decide) (![⟨388605, by decide⟩,⟨388705, by decide⟩,⟨388784, by decide⟩,⟨388825, by decide⟩]) unmarked_context_9_431_388826 node_context_9_431_388826
  intro a
  fin_cases a
  · exact context_10_1724_388605
  · exact context_10_1725_388705
  · exact context_10_1726_388784
  · exact context_10_1727_388825

theorem unmarked_context_8_107_388827 : frontier 13 ⟨388827, by decide⟩
    (prefixCache 8 107) (prefixPartial 8 107) = false := by
  decide +kernel

theorem node_context_8_107_388827 : EJMOriginalGlobalDAGData.nodes 13 ⟨388827, by decide⟩ =
    .split (coordinate 8) (![⟨383026, by decide⟩,⟨387264, by decide⟩,⟨388492, by decide⟩,⟨388826, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_107_388827 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 107 ⟨388827, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 107
    ⟨388827, by decide⟩ (by decide) (![⟨383026, by decide⟩,⟨387264, by decide⟩,⟨388492, by decide⟩,⟨388826, by decide⟩]) unmarked_context_8_107_388827 node_context_8_107_388827
  intro a
  fin_cases a
  · exact context_9_428_383026
  · exact context_9_429_387264
  · exact context_9_430_388492
  · exact context_9_431_388826

theorem unmarked_context_7_26_388828 : frontier 14 ⟨388828, by decide⟩
    (prefixCache 7 26) (prefixPartial 7 26) = false := by
  decide +kernel

theorem node_context_7_26_388828 : EJMOriginalGlobalDAGData.nodes 14 ⟨388828, by decide⟩ =
    .split (coordinate 7) (![⟨357146, by decide⟩,⟨366891, by decide⟩,⟨376679, by decide⟩,⟨388827, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_7_26_388828 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 26 ⟨388828, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 7 26
    ⟨388828, by decide⟩ (by decide) (![⟨357146, by decide⟩,⟨366891, by decide⟩,⟨376679, by decide⟩,⟨388827, by decide⟩]) unmarked_context_7_26_388828 node_context_7_26_388828
  intro a
  fin_cases a
  · exact context_8_104_357146
  · exact context_8_105_366891
  · exact context_8_106_376679
  · exact context_8_107_388827

theorem selected_cut_15123 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 27648) = some ⟨12, 1, 0, 34034, 27648, 1, 65536⟩ := by
  decide +kernel

theorem context_12_27648_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27648 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 27648 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 27648, 1, 65536⟩
    (by decide) selected_cut_15123

theorem selected_cut_15124 : selected 9 ⟨388829, by decide⟩
    (prefixPartial 12 27649) = some ⟨12, 1, 0, 388829, 27649, 1, 65536⟩ := by
  decide +kernel

theorem context_12_27649_388829 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27649 ⟨388829, by decide⟩ :=
  accepted_of_selected 12 27649 ⟨388829, by decide⟩ ⟨12, 1, 0, 388829, 27649, 1, 65536⟩
    (by decide) selected_cut_15124

theorem selected_cut_15125 : selected 8 ⟨388928, by decide⟩
    (prefixPartial 13 110600) = some ⟨13, 2, 0, 388928, 110600, 2833, 16384⟩ := by
  decide +kernel

theorem context_13_110600_388928 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110600 ⟨388928, by decide⟩ :=
  accepted_of_selected 13 110600 ⟨388928, by decide⟩ ⟨13, 2, 0, 388928, 110600, 2833, 16384⟩
    (by decide) selected_cut_15125

theorem selected_cut_15126 : selected 8 ⟨389011, by decide⟩
    (prefixPartial 13 110601) = some ⟨13, 2, 0, 389011, 110601, 1941, 16384⟩ := by
  decide +kernel

theorem context_13_110601_389011 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110601 ⟨389011, by decide⟩ :=
  accepted_of_selected 13 110601 ⟨389011, by decide⟩ ⟨13, 2, 0, 389011, 110601, 1941, 16384⟩
    (by decide) selected_cut_15126

theorem selected_cut_15127 : selected 8 ⟨389042, by decide⟩
    (prefixPartial 13 110602) = some ⟨13, 2, 0, 389042, 110602, 605, 16384⟩ := by
  decide +kernel

theorem context_13_110602_389042 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110602 ⟨389042, by decide⟩ :=
  accepted_of_selected 13 110602 ⟨389042, by decide⟩ ⟨13, 2, 0, 389042, 110602, 605, 16384⟩
    (by decide) selected_cut_15127

theorem selected_cut_15128 : selected 8 ⟨389059, by decide⟩
    (prefixPartial 13 110603) = some ⟨13, 2, 0, 389059, 110603, 141, 16384⟩ := by
  decide +kernel

theorem context_13_110603_389059 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110603 ⟨389059, by decide⟩ :=
  accepted_of_selected 13 110603 ⟨389059, by decide⟩ ⟨13, 2, 0, 389059, 110603, 141, 16384⟩
    (by decide) selected_cut_15128

theorem unmarked_context_12_27650_389060 : frontier 9 ⟨389060, by decide⟩
    (prefixCache 12 27650) (prefixPartial 12 27650) = false := by
  decide +kernel

theorem node_context_12_27650_389060 : EJMOriginalGlobalDAGData.nodes 9 ⟨389060, by decide⟩ =
    .split (coordinate 12) (![⟨388928, by decide⟩,⟨389011, by decide⟩,⟨389042, by decide⟩,⟨389059, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27650_389060 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27650 ⟨389060, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27650
    ⟨389060, by decide⟩ (by decide) (![⟨388928, by decide⟩,⟨389011, by decide⟩,⟨389042, by decide⟩,⟨389059, by decide⟩]) unmarked_context_12_27650_389060 node_context_12_27650_389060
  intro a
  fin_cases a
  · exact context_13_110600_388928
  · exact context_13_110601_389011
  · exact context_13_110602_389042
  · exact context_13_110603_389059

theorem selected_cut_15129 : selected 9 ⟨389061, by decide⟩
    (prefixPartial 12 27651) = some ⟨12, 1, 0, 389061, 27651, 1, 65536⟩ := by
  decide +kernel

theorem context_12_27651_389061 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27651 ⟨389061, by decide⟩ :=
  accepted_of_selected 12 27651 ⟨389061, by decide⟩ ⟨12, 1, 0, 389061, 27651, 1, 65536⟩
    (by decide) selected_cut_15129

theorem unmarked_context_11_6912_389062 : frontier 10 ⟨389062, by decide⟩
    (prefixCache 11 6912) (prefixPartial 11 6912) = false := by
  decide +kernel

theorem node_context_11_6912_389062 : EJMOriginalGlobalDAGData.nodes 10 ⟨389062, by decide⟩ =
    .split (coordinate 11) (![⟨34034, by decide⟩,⟨388829, by decide⟩,⟨389060, by decide⟩,⟨389061, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6912_389062 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6912 ⟨389062, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6912
    ⟨389062, by decide⟩ (by decide) (![⟨34034, by decide⟩,⟨388829, by decide⟩,⟨389060, by decide⟩,⟨389061, by decide⟩]) unmarked_context_11_6912_389062 node_context_11_6912_389062
  intro a
  fin_cases a
  · exact context_12_27648_34034
  · exact context_12_27649_388829
  · exact context_12_27650_389060
  · exact context_12_27651_389061

theorem selected_cut_15130 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 27652) = some ⟨12, 1, 0, 34034, 27652, 1, 65536⟩ := by
  decide +kernel

theorem context_12_27652_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27652 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 27652 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 27652, 1, 65536⟩
    (by decide) selected_cut_15130

theorem selected_cut_15131 : selected 8 ⟨389128, by decide⟩
    (prefixPartial 13 110612) = some ⟨13, 2, 0, 389128, 110612, 3249, 16384⟩ := by
  decide +kernel

theorem context_13_110612_389128 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110612 ⟨389128, by decide⟩ :=
  accepted_of_selected 13 110612 ⟨389128, by decide⟩ ⟨13, 2, 0, 389128, 110612, 3249, 16384⟩
    (by decide) selected_cut_15131

theorem selected_cut_15132 : selected 8 ⟨389214, by decide⟩
    (prefixPartial 13 110613) = some ⟨13, 2, 0, 389214, 110613, 3181, 16384⟩ := by
  decide +kernel

theorem context_13_110613_389214 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110613 ⟨389214, by decide⟩ :=
  accepted_of_selected 13 110613 ⟨389214, by decide⟩ ⟨13, 2, 0, 389214, 110613, 3181, 16384⟩
    (by decide) selected_cut_15132

theorem selected_cut_15133 : selected 8 ⟨389244, by decide⟩
    (prefixPartial 13 110614) = some ⟨13, 2, 0, 389244, 110614, 2457, 16384⟩ := by
  decide +kernel

theorem context_13_110614_389244 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110614 ⟨389244, by decide⟩ :=
  accepted_of_selected 13 110614 ⟨389244, by decide⟩ ⟨13, 2, 0, 389244, 110614, 2457, 16384⟩
    (by decide) selected_cut_15133

theorem selected_cut_15134 : selected 8 ⟨389261, by decide⟩
    (prefixPartial 13 110615) = some ⟨13, 2, 0, 389261, 110615, 1013, 16384⟩ := by
  decide +kernel

theorem context_13_110615_389261 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110615 ⟨389261, by decide⟩ :=
  accepted_of_selected 13 110615 ⟨389261, by decide⟩ ⟨13, 2, 0, 389261, 110615, 1013, 16384⟩
    (by decide) selected_cut_15134

theorem unmarked_context_12_27653_389262 : frontier 9 ⟨389262, by decide⟩
    (prefixCache 12 27653) (prefixPartial 12 27653) = false := by
  decide +kernel

theorem node_context_12_27653_389262 : EJMOriginalGlobalDAGData.nodes 9 ⟨389262, by decide⟩ =
    .split (coordinate 12) (![⟨389128, by decide⟩,⟨389214, by decide⟩,⟨389244, by decide⟩,⟨389261, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27653_389262 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27653 ⟨389262, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27653
    ⟨389262, by decide⟩ (by decide) (![⟨389128, by decide⟩,⟨389214, by decide⟩,⟨389244, by decide⟩,⟨389261, by decide⟩]) unmarked_context_12_27653_389262 node_context_12_27653_389262
  intro a
  fin_cases a
  · exact context_13_110612_389128
  · exact context_13_110613_389214
  · exact context_13_110614_389244
  · exact context_13_110615_389261

theorem selected_cut_15135 : selected 8 ⟨389340, by decide⟩
    (prefixPartial 13 110616) = some ⟨13, 2, 0, 389340, 110616, 3529, 16384⟩ := by
  decide +kernel

theorem context_13_110616_389340 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110616 ⟨389340, by decide⟩ :=
  accepted_of_selected 13 110616 ⟨389340, by decide⟩ ⟨13, 2, 0, 389340, 110616, 3529, 16384⟩
    (by decide) selected_cut_15135

theorem selected_cut_15136 : selected 8 ⟨389426, by decide⟩
    (prefixPartial 13 110617) = some ⟨13, 2, 0, 389426, 110617, 3649, 16384⟩ := by
  decide +kernel

theorem context_13_110617_389426 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110617 ⟨389426, by decide⟩ :=
  accepted_of_selected 13 110617 ⟨389426, by decide⟩ ⟨13, 2, 0, 389426, 110617, 3649, 16384⟩
    (by decide) selected_cut_15136

theorem selected_cut_15137 : selected 8 ⟨389457, by decide⟩
    (prefixPartial 13 110618) = some ⟨13, 2, 0, 389457, 110618, 2293, 16384⟩ := by
  decide +kernel

theorem context_13_110618_389457 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110618 ⟨389457, by decide⟩ :=
  accepted_of_selected 13 110618 ⟨389457, by decide⟩ ⟨13, 2, 0, 389457, 110618, 2293, 16384⟩
    (by decide) selected_cut_15137

theorem selected_cut_15138 : selected 8 ⟨389466, by decide⟩
    (prefixPartial 13 110619) = some ⟨13, 2, 0, 389466, 110619, 1029, 16384⟩ := by
  decide +kernel

theorem context_13_110619_389466 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110619 ⟨389466, by decide⟩ :=
  accepted_of_selected 13 110619 ⟨389466, by decide⟩ ⟨13, 2, 0, 389466, 110619, 1029, 16384⟩
    (by decide) selected_cut_15138

theorem unmarked_context_12_27654_389467 : frontier 9 ⟨389467, by decide⟩
    (prefixCache 12 27654) (prefixPartial 12 27654) = false := by
  decide +kernel

theorem node_context_12_27654_389467 : EJMOriginalGlobalDAGData.nodes 9 ⟨389467, by decide⟩ =
    .split (coordinate 12) (![⟨389340, by decide⟩,⟨389426, by decide⟩,⟨389457, by decide⟩,⟨389466, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27654_389467 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27654 ⟨389467, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27654
    ⟨389467, by decide⟩ (by decide) (![⟨389340, by decide⟩,⟨389426, by decide⟩,⟨389457, by decide⟩,⟨389466, by decide⟩]) unmarked_context_12_27654_389467 node_context_12_27654_389467
  intro a
  fin_cases a
  · exact context_13_110616_389340
  · exact context_13_110617_389426
  · exact context_13_110618_389457
  · exact context_13_110619_389466

theorem selected_cut_15139 : selected 8 ⟨389532, by decide⟩
    (prefixPartial 13 110620) = some ⟨13, 2, 0, 389532, 110620, 3541, 16384⟩ := by
  decide +kernel

theorem context_13_110620_389532 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110620 ⟨389532, by decide⟩ :=
  accepted_of_selected 13 110620 ⟨389532, by decide⟩ ⟨13, 2, 0, 389532, 110620, 3541, 16384⟩
    (by decide) selected_cut_15139

theorem selected_cut_15140 : selected 8 ⟨389622, by decide⟩
    (prefixPartial 13 110621) = some ⟨13, 2, 0, 389622, 110621, 3985, 16384⟩ := by
  decide +kernel

theorem context_13_110621_389622 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110621 ⟨389622, by decide⟩ :=
  accepted_of_selected 13 110621 ⟨389622, by decide⟩ ⟨13, 2, 0, 389622, 110621, 3985, 16384⟩
    (by decide) selected_cut_15140

theorem selected_cut_15141 : selected 8 ⟨389662, by decide⟩
    (prefixPartial 13 110622) = some ⟨13, 2, 0, 389662, 110622, 2605, 16384⟩ := by
  decide +kernel

theorem context_13_110622_389662 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110622 ⟨389662, by decide⟩ :=
  accepted_of_selected 13 110622 ⟨389662, by decide⟩ ⟨13, 2, 0, 389662, 110622, 2605, 16384⟩
    (by decide) selected_cut_15141

theorem selected_cut_15142 : selected 8 ⟨389674, by decide⟩
    (prefixPartial 13 110623) = some ⟨13, 2, 0, 389674, 110623, 1225, 16384⟩ := by
  decide +kernel

theorem context_13_110623_389674 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110623 ⟨389674, by decide⟩ :=
  accepted_of_selected 13 110623 ⟨389674, by decide⟩ ⟨13, 2, 0, 389674, 110623, 1225, 16384⟩
    (by decide) selected_cut_15142

theorem unmarked_context_12_27655_389675 : frontier 9 ⟨389675, by decide⟩
    (prefixCache 12 27655) (prefixPartial 12 27655) = false := by
  decide +kernel

theorem node_context_12_27655_389675 : EJMOriginalGlobalDAGData.nodes 9 ⟨389675, by decide⟩ =
    .split (coordinate 12) (![⟨389532, by decide⟩,⟨389622, by decide⟩,⟨389662, by decide⟩,⟨389674, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27655_389675 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27655 ⟨389675, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27655
    ⟨389675, by decide⟩ (by decide) (![⟨389532, by decide⟩,⟨389622, by decide⟩,⟨389662, by decide⟩,⟨389674, by decide⟩]) unmarked_context_12_27655_389675 node_context_12_27655_389675
  intro a
  fin_cases a
  · exact context_13_110620_389532
  · exact context_13_110621_389622
  · exact context_13_110622_389662
  · exact context_13_110623_389674

theorem unmarked_context_11_6913_389676 : frontier 10 ⟨389676, by decide⟩
    (prefixCache 11 6913) (prefixPartial 11 6913) = false := by
  decide +kernel

theorem node_context_11_6913_389676 : EJMOriginalGlobalDAGData.nodes 10 ⟨389676, by decide⟩ =
    .split (coordinate 11) (![⟨34034, by decide⟩,⟨389262, by decide⟩,⟨389467, by decide⟩,⟨389675, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6913_389676 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6913 ⟨389676, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6913
    ⟨389676, by decide⟩ (by decide) (![⟨34034, by decide⟩,⟨389262, by decide⟩,⟨389467, by decide⟩,⟨389675, by decide⟩]) unmarked_context_11_6913_389676 node_context_11_6913_389676
  intro a
  fin_cases a
  · exact context_12_27652_34034
  · exact context_12_27653_389262
  · exact context_12_27654_389467
  · exact context_12_27655_389675

theorem selected_cut_15143 : selected 8 ⟨389728, by decide⟩
    (prefixPartial 13 110624) = some ⟨13, 2, 0, 389728, 110624, 2453, 16384⟩ := by
  decide +kernel

theorem context_13_110624_389728 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110624 ⟨389728, by decide⟩ :=
  accepted_of_selected 13 110624 ⟨389728, by decide⟩ ⟨13, 2, 0, 389728, 110624, 2453, 16384⟩
    (by decide) selected_cut_15143

theorem selected_cut_15144 : selected 7 ⟨389759, by decide⟩
    (prefixPartial 14 442500) = some ⟨14, 2, 0, 389759, 442500, 1257, 4096⟩ := by
  decide +kernel

theorem context_14_442500_389759 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 442500 ⟨389759, by decide⟩ :=
  accepted_of_selected 14 442500 ⟨389759, by decide⟩ ⟨14, 2, 0, 389759, 442500, 1257, 4096⟩
    (by decide) selected_cut_15144

theorem selected_cut_15145 : selected 7 ⟨389774, by decide⟩
    (prefixPartial 14 442501) = some ⟨14, 2, 0, 389774, 442501, 801, 4096⟩ := by
  decide +kernel

theorem context_14_442501_389774 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 442501 ⟨389774, by decide⟩ :=
  accepted_of_selected 14 442501 ⟨389774, by decide⟩ ⟨14, 2, 0, 389774, 442501, 801, 4096⟩
    (by decide) selected_cut_15145

theorem selected_cut_15146 : selected 7 ⟨389804, by decide⟩
    (prefixPartial 14 442502) = some ⟨14, 2, 0, 389804, 442502, 1217, 4096⟩ := by
  decide +kernel

theorem context_14_442502_389804 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 442502 ⟨389804, by decide⟩ :=
  accepted_of_selected 14 442502 ⟨389804, by decide⟩ ⟨14, 2, 0, 389804, 442502, 1217, 4096⟩
    (by decide) selected_cut_15146

theorem selected_cut_15147 : selected 7 ⟨389823, by decide⟩
    (prefixPartial 14 442503) = some ⟨14, 2, 0, 389823, 442503, 1025, 4096⟩ := by
  decide +kernel

theorem context_14_442503_389823 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 442503 ⟨389823, by decide⟩ :=
  accepted_of_selected 14 442503 ⟨389823, by decide⟩ ⟨14, 2, 0, 389823, 442503, 1025, 4096⟩
    (by decide) selected_cut_15147

theorem unmarked_context_13_110625_389824 : frontier 8 ⟨389824, by decide⟩
    (prefixCache 13 110625) (prefixPartial 13 110625) = false := by
  decide +kernel

theorem node_context_13_110625_389824 : EJMOriginalGlobalDAGData.nodes 8 ⟨389824, by decide⟩ =
    .split (coordinate 13) (![⟨389759, by decide⟩,⟨389774, by decide⟩,⟨389804, by decide⟩,⟨389823, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_110625_389824 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110625 ⟨389824, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 110625
    ⟨389824, by decide⟩ (by decide) (![⟨389759, by decide⟩,⟨389774, by decide⟩,⟨389804, by decide⟩,⟨389823, by decide⟩]) unmarked_context_13_110625_389824 node_context_13_110625_389824
  intro a
  fin_cases a
  · exact context_14_442500_389759
  · exact context_14_442501_389774
  · exact context_14_442502_389804
  · exact context_14_442503_389823

theorem selected_cut_15148 : selected 8 ⟨389861, by decide⟩
    (prefixPartial 13 110626) = some ⟨13, 2, 0, 389861, 110626, 2325, 16384⟩ := by
  decide +kernel

theorem context_13_110626_389861 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110626 ⟨389861, by decide⟩ :=
  accepted_of_selected 13 110626 ⟨389861, by decide⟩ ⟨13, 2, 0, 389861, 110626, 2325, 16384⟩
    (by decide) selected_cut_15148

theorem selected_cut_15149 : selected 8 ⟨389874, by decide⟩
    (prefixPartial 13 110627) = some ⟨13, 2, 0, 389874, 110627, 1093, 16384⟩ := by
  decide +kernel

theorem context_13_110627_389874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110627 ⟨389874, by decide⟩ :=
  accepted_of_selected 13 110627 ⟨389874, by decide⟩ ⟨13, 2, 0, 389874, 110627, 1093, 16384⟩
    (by decide) selected_cut_15149

theorem unmarked_context_12_27656_389875 : frontier 9 ⟨389875, by decide⟩
    (prefixCache 12 27656) (prefixPartial 12 27656) = false := by
  decide +kernel

theorem node_context_12_27656_389875 : EJMOriginalGlobalDAGData.nodes 9 ⟨389875, by decide⟩ =
    .split (coordinate 12) (![⟨389728, by decide⟩,⟨389824, by decide⟩,⟨389861, by decide⟩,⟨389874, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27656_389875 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27656 ⟨389875, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27656
    ⟨389875, by decide⟩ (by decide) (![⟨389728, by decide⟩,⟨389824, by decide⟩,⟨389861, by decide⟩,⟨389874, by decide⟩]) unmarked_context_12_27656_389875 node_context_12_27656_389875
  intro a
  fin_cases a
  · exact context_13_110624_389728
  · exact context_13_110625_389824
  · exact context_13_110626_389861
  · exact context_13_110627_389874

theorem selected_cut_15150 : selected 8 ⟨389936, by decide⟩
    (prefixPartial 13 110628) = some ⟨13, 2, 0, 389936, 110628, 3077, 16384⟩ := by
  decide +kernel

theorem context_13_110628_389936 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110628 ⟨389936, by decide⟩ :=
  accepted_of_selected 13 110628 ⟨389936, by decide⟩ ⟨13, 2, 0, 389936, 110628, 3077, 16384⟩
    (by decide) selected_cut_15150

theorem selected_cut_15151 : selected 8 ⟨390016, by decide⟩
    (prefixPartial 13 110629) = some ⟨13, 2, 0, 390016, 110629, 3981, 16384⟩ := by
  decide +kernel

theorem context_13_110629_390016 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110629 ⟨390016, by decide⟩ :=
  accepted_of_selected 13 110629 ⟨390016, by decide⟩ ⟨13, 2, 0, 390016, 110629, 3981, 16384⟩
    (by decide) selected_cut_15151

theorem selected_cut_15152 : selected 8 ⟨390038, by decide⟩
    (prefixPartial 13 110630) = some ⟨13, 2, 0, 390038, 110630, 2337, 16384⟩ := by
  decide +kernel

theorem context_13_110630_390038 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110630 ⟨390038, by decide⟩ :=
  accepted_of_selected 13 110630 ⟨390038, by decide⟩ ⟨13, 2, 0, 390038, 110630, 2337, 16384⟩
    (by decide) selected_cut_15152

theorem selected_cut_15153 : selected 8 ⟨390049, by decide⟩
    (prefixPartial 13 110631) = some ⟨13, 2, 0, 390049, 110631, 1141, 16384⟩ := by
  decide +kernel

theorem context_13_110631_390049 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110631 ⟨390049, by decide⟩ :=
  accepted_of_selected 13 110631 ⟨390049, by decide⟩ ⟨13, 2, 0, 390049, 110631, 1141, 16384⟩
    (by decide) selected_cut_15153

theorem unmarked_context_12_27657_390050 : frontier 9 ⟨390050, by decide⟩
    (prefixCache 12 27657) (prefixPartial 12 27657) = false := by
  decide +kernel

theorem node_context_12_27657_390050 : EJMOriginalGlobalDAGData.nodes 9 ⟨390050, by decide⟩ =
    .split (coordinate 12) (![⟨389936, by decide⟩,⟨390016, by decide⟩,⟨390038, by decide⟩,⟨390049, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27657_390050 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27657 ⟨390050, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27657
    ⟨390050, by decide⟩ (by decide) (![⟨389936, by decide⟩,⟨390016, by decide⟩,⟨390038, by decide⟩,⟨390049, by decide⟩]) unmarked_context_12_27657_390050 node_context_12_27657_390050
  intro a
  fin_cases a
  · exact context_13_110628_389936
  · exact context_13_110629_390016
  · exact context_13_110630_390038
  · exact context_13_110631_390049

theorem selected_cut_15154 : selected 8 ⟨390115, by decide⟩
    (prefixPartial 13 110632) = some ⟨13, 2, 0, 390115, 110632, 2829, 16384⟩ := by
  decide +kernel

theorem context_13_110632_390115 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110632 ⟨390115, by decide⟩ :=
  accepted_of_selected 13 110632 ⟨390115, by decide⟩ ⟨13, 2, 0, 390115, 110632, 2829, 16384⟩
    (by decide) selected_cut_15154

theorem selected_cut_15155 : selected 8 ⟨390196, by decide⟩
    (prefixPartial 13 110633) = some ⟨13, 2, 0, 390196, 110633, 3861, 16384⟩ := by
  decide +kernel

theorem context_13_110633_390196 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110633 ⟨390196, by decide⟩ :=
  accepted_of_selected 13 110633 ⟨390196, by decide⟩ ⟨13, 2, 0, 390196, 110633, 3861, 16384⟩
    (by decide) selected_cut_15155

theorem selected_cut_15156 : selected 8 ⟨390222, by decide⟩
    (prefixPartial 13 110634) = some ⟨13, 2, 0, 390222, 110634, 2049, 16384⟩ := by
  decide +kernel

theorem context_13_110634_390222 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110634 ⟨390222, by decide⟩ :=
  accepted_of_selected 13 110634 ⟨390222, by decide⟩ ⟨13, 2, 0, 390222, 110634, 2049, 16384⟩
    (by decide) selected_cut_15156

theorem selected_cut_15157 : selected 8 ⟨390232, by decide⟩
    (prefixPartial 13 110635) = some ⟨13, 2, 0, 390232, 110635, 1153, 16384⟩ := by
  decide +kernel

theorem context_13_110635_390232 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110635 ⟨390232, by decide⟩ :=
  accepted_of_selected 13 110635 ⟨390232, by decide⟩ ⟨13, 2, 0, 390232, 110635, 1153, 16384⟩
    (by decide) selected_cut_15157

theorem unmarked_context_12_27658_390233 : frontier 9 ⟨390233, by decide⟩
    (prefixCache 12 27658) (prefixPartial 12 27658) = false := by
  decide +kernel

theorem node_context_12_27658_390233 : EJMOriginalGlobalDAGData.nodes 9 ⟨390233, by decide⟩ =
    .split (coordinate 12) (![⟨390115, by decide⟩,⟨390196, by decide⟩,⟨390222, by decide⟩,⟨390232, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27658_390233 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27658 ⟨390233, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27658
    ⟨390233, by decide⟩ (by decide) (![⟨390115, by decide⟩,⟨390196, by decide⟩,⟨390222, by decide⟩,⟨390232, by decide⟩]) unmarked_context_12_27658_390233 node_context_12_27658_390233
  intro a
  fin_cases a
  · exact context_13_110632_390115
  · exact context_13_110633_390196
  · exact context_13_110634_390222
  · exact context_13_110635_390232

theorem selected_cut_15158 : selected 8 ⟨390291, by decide⟩
    (prefixPartial 13 110636) = some ⟨13, 2, 0, 390291, 110636, 2973, 16384⟩ := by
  decide +kernel

theorem context_13_110636_390291 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110636 ⟨390291, by decide⟩ :=
  accepted_of_selected 13 110636 ⟨390291, by decide⟩ ⟨13, 2, 0, 390291, 110636, 2973, 16384⟩
    (by decide) selected_cut_15158

theorem selected_cut_15159 : selected 7 ⟨390316, by decide⟩
    (prefixPartial 14 442548) = some ⟨14, 2, 0, 390316, 442548, 1253, 4096⟩ := by
  decide +kernel

theorem context_14_442548_390316 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 442548 ⟨390316, by decide⟩ :=
  accepted_of_selected 14 442548 ⟨390316, by decide⟩ ⟨14, 2, 0, 390316, 442548, 1253, 4096⟩
    (by decide) selected_cut_15159

theorem selected_cut_15160 : selected 7 ⟨390335, by decide⟩
    (prefixPartial 14 442549) = some ⟨14, 2, 0, 390335, 442549, 929, 4096⟩ := by
  decide +kernel

theorem context_14_442549_390335 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 442549 ⟨390335, by decide⟩ :=
  accepted_of_selected 14 442549 ⟨390335, by decide⟩ ⟨14, 2, 0, 390335, 442549, 929, 4096⟩
    (by decide) selected_cut_15160

theorem selected_cut_15161 : selected 7 ⟨390358, by decide⟩
    (prefixPartial 14 442550) = some ⟨14, 2, 0, 390358, 442550, 1185, 4096⟩ := by
  decide +kernel

theorem context_14_442550_390358 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 442550 ⟨390358, by decide⟩ :=
  accepted_of_selected 14 442550 ⟨390358, by decide⟩ ⟨14, 2, 0, 390358, 442550, 1185, 4096⟩
    (by decide) selected_cut_15161

theorem selected_cut_15162 : selected 7 ⟨390374, by decide⟩
    (prefixPartial 14 442551) = some ⟨14, 2, 0, 390374, 442551, 1041, 4096⟩ := by
  decide +kernel

theorem context_14_442551_390374 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 442551 ⟨390374, by decide⟩ :=
  accepted_of_selected 14 442551 ⟨390374, by decide⟩ ⟨14, 2, 0, 390374, 442551, 1041, 4096⟩
    (by decide) selected_cut_15162

theorem unmarked_context_13_110637_390375 : frontier 8 ⟨390375, by decide⟩
    (prefixCache 13 110637) (prefixPartial 13 110637) = false := by
  decide +kernel

theorem node_context_13_110637_390375 : EJMOriginalGlobalDAGData.nodes 8 ⟨390375, by decide⟩ =
    .split (coordinate 13) (![⟨390316, by decide⟩,⟨390335, by decide⟩,⟨390358, by decide⟩,⟨390374, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_110637_390375 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110637 ⟨390375, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 110637
    ⟨390375, by decide⟩ (by decide) (![⟨390316, by decide⟩,⟨390335, by decide⟩,⟨390358, by decide⟩,⟨390374, by decide⟩]) unmarked_context_13_110637_390375 node_context_13_110637_390375
  intro a
  fin_cases a
  · exact context_14_442548_390316
  · exact context_14_442549_390335
  · exact context_14_442550_390358
  · exact context_14_442551_390374

theorem selected_cut_15163 : selected 8 ⟨390407, by decide⟩
    (prefixPartial 13 110638) = some ⟨13, 2, 0, 390407, 110638, 2461, 16384⟩ := by
  decide +kernel

theorem context_13_110638_390407 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110638 ⟨390407, by decide⟩ :=
  accepted_of_selected 13 110638 ⟨390407, by decide⟩ ⟨13, 2, 0, 390407, 110638, 2461, 16384⟩
    (by decide) selected_cut_15163

theorem selected_cut_15164 : selected 8 ⟨390431, by decide⟩
    (prefixPartial 13 110639) = some ⟨13, 2, 0, 390431, 110639, 1341, 16384⟩ := by
  decide +kernel

theorem context_13_110639_390431 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110639 ⟨390431, by decide⟩ :=
  accepted_of_selected 13 110639 ⟨390431, by decide⟩ ⟨13, 2, 0, 390431, 110639, 1341, 16384⟩
    (by decide) selected_cut_15164

theorem unmarked_context_12_27659_390432 : frontier 9 ⟨390432, by decide⟩
    (prefixCache 12 27659) (prefixPartial 12 27659) = false := by
  decide +kernel

theorem node_context_12_27659_390432 : EJMOriginalGlobalDAGData.nodes 9 ⟨390432, by decide⟩ =
    .split (coordinate 12) (![⟨390291, by decide⟩,⟨390375, by decide⟩,⟨390407, by decide⟩,⟨390431, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27659_390432 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27659 ⟨390432, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27659
    ⟨390432, by decide⟩ (by decide) (![⟨390291, by decide⟩,⟨390375, by decide⟩,⟨390407, by decide⟩,⟨390431, by decide⟩]) unmarked_context_12_27659_390432 node_context_12_27659_390432
  intro a
  fin_cases a
  · exact context_13_110636_390291
  · exact context_13_110637_390375
  · exact context_13_110638_390407
  · exact context_13_110639_390431

theorem unmarked_context_11_6914_390433 : frontier 10 ⟨390433, by decide⟩
    (prefixCache 11 6914) (prefixPartial 11 6914) = false := by
  decide +kernel

theorem node_context_11_6914_390433 : EJMOriginalGlobalDAGData.nodes 10 ⟨390433, by decide⟩ =
    .split (coordinate 11) (![⟨389875, by decide⟩,⟨390050, by decide⟩,⟨390233, by decide⟩,⟨390432, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6914_390433 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6914 ⟨390433, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6914
    ⟨390433, by decide⟩ (by decide) (![⟨389875, by decide⟩,⟨390050, by decide⟩,⟨390233, by decide⟩,⟨390432, by decide⟩]) unmarked_context_11_6914_390433 node_context_11_6914_390433
  intro a
  fin_cases a
  · exact context_12_27656_389875
  · exact context_12_27657_390050
  · exact context_12_27658_390233
  · exact context_12_27659_390432

theorem selected_cut_15165 : selected 9 ⟨390434, by decide⟩
    (prefixPartial 12 27660) = some ⟨12, 1, 0, 390434, 27660, 1, 65536⟩ := by
  decide +kernel

theorem context_12_27660_390434 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27660 ⟨390434, by decide⟩ :=
  accepted_of_selected 12 27660 ⟨390434, by decide⟩ ⟨12, 1, 0, 390434, 27660, 1, 65536⟩
    (by decide) selected_cut_15165

theorem selected_cut_15166 : selected 8 ⟨390479, by decide⟩
    (prefixPartial 13 110644) = some ⟨13, 2, 0, 390479, 110644, 2949, 16384⟩ := by
  decide +kernel

theorem context_13_110644_390479 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110644 ⟨390479, by decide⟩ :=
  accepted_of_selected 13 110644 ⟨390479, by decide⟩ ⟨13, 2, 0, 390479, 110644, 2949, 16384⟩
    (by decide) selected_cut_15166

theorem selected_cut_15167 : selected 8 ⟨390532, by decide⟩
    (prefixPartial 13 110645) = some ⟨13, 2, 0, 390532, 110645, 3617, 16384⟩ := by
  decide +kernel

theorem context_13_110645_390532 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110645 ⟨390532, by decide⟩ :=
  accepted_of_selected 13 110645 ⟨390532, by decide⟩ ⟨13, 2, 0, 390532, 110645, 3617, 16384⟩
    (by decide) selected_cut_15167

theorem selected_cut_15168 : selected 8 ⟨390557, by decide⟩
    (prefixPartial 13 110646) = some ⟨13, 2, 0, 390557, 110646, 2365, 16384⟩ := by
  decide +kernel

theorem context_13_110646_390557 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110646 ⟨390557, by decide⟩ :=
  accepted_of_selected 13 110646 ⟨390557, by decide⟩ ⟨13, 2, 0, 390557, 110646, 2365, 16384⟩
    (by decide) selected_cut_15168

theorem selected_cut_15169 : selected 8 ⟨390564, by decide⟩
    (prefixPartial 13 110647) = some ⟨13, 2, 0, 390564, 110647, 1073, 16384⟩ := by
  decide +kernel

theorem context_13_110647_390564 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110647 ⟨390564, by decide⟩ :=
  accepted_of_selected 13 110647 ⟨390564, by decide⟩ ⟨13, 2, 0, 390564, 110647, 1073, 16384⟩
    (by decide) selected_cut_15169

theorem unmarked_context_12_27661_390565 : frontier 9 ⟨390565, by decide⟩
    (prefixCache 12 27661) (prefixPartial 12 27661) = false := by
  decide +kernel

theorem node_context_12_27661_390565 : EJMOriginalGlobalDAGData.nodes 9 ⟨390565, by decide⟩ =
    .split (coordinate 12) (![⟨390479, by decide⟩,⟨390532, by decide⟩,⟨390557, by decide⟩,⟨390564, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27661_390565 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27661 ⟨390565, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27661
    ⟨390565, by decide⟩ (by decide) (![⟨390479, by decide⟩,⟨390532, by decide⟩,⟨390557, by decide⟩,⟨390564, by decide⟩]) unmarked_context_12_27661_390565 node_context_12_27661_390565
  intro a
  fin_cases a
  · exact context_13_110644_390479
  · exact context_13_110645_390532
  · exact context_13_110646_390557
  · exact context_13_110647_390564

theorem selected_cut_15170 : selected 8 ⟨390617, by decide⟩
    (prefixPartial 13 110648) = some ⟨13, 2, 0, 390617, 110648, 2933, 16384⟩ := by
  decide +kernel

theorem context_13_110648_390617 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110648 ⟨390617, by decide⟩ :=
  accepted_of_selected 13 110648 ⟨390617, by decide⟩ ⟨13, 2, 0, 390617, 110648, 2933, 16384⟩
    (by decide) selected_cut_15170

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
