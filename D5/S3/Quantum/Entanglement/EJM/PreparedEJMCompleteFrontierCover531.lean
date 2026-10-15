/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover530
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_50980 : selected 9 ⟨1462968, by decide⟩
    (prefixPartial 12 456733) = some ⟨12, 2, 0, 1462968, 456733, 2089, 65536⟩ := by
  decide +kernel

theorem context_12_456733_1462968 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 456733 ⟨1462968, by decide⟩ :=
  accepted_of_selected 12 456733 ⟨1462968, by decide⟩ ⟨12, 2, 0, 1462968, 456733, 2089, 65536⟩
    (by decide) selected_cut_50980

theorem selected_cut_50981 : selected 9 ⟨1463037, by decide⟩
    (prefixPartial 12 456734) = some ⟨12, 2, 0, 1463037, 456734, 2057, 65536⟩ := by
  decide +kernel

theorem context_12_456734_1463037 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 456734 ⟨1463037, by decide⟩ :=
  accepted_of_selected 12 456734 ⟨1463037, by decide⟩ ⟨12, 2, 0, 1463037, 456734, 2057, 65536⟩
    (by decide) selected_cut_50981

theorem selected_cut_50982 : selected 9 ⟨296530, by decide⟩
    (prefixPartial 12 456735) = some ⟨12, 1, 0, 296530, 456735, 1, 65536⟩ := by
  decide +kernel

theorem context_12_456735_296530 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 456735 ⟨296530, by decide⟩ :=
  accepted_of_selected 12 456735 ⟨296530, by decide⟩ ⟨12, 1, 0, 296530, 456735, 1, 65536⟩
    (by decide) selected_cut_50982

theorem unmarked_context_11_114183_1463038 : frontier 10 ⟨1463038, by decide⟩
    (prefixCache 11 114183) (prefixPartial 11 114183) = false := by
  decide +kernel

theorem node_context_11_114183_1463038 : EJMOriginalGlobalDAGData.nodes 10 ⟨1463038, by decide⟩ =
    .split (coordinate 11) (![⟨1461226, by decide⟩,⟨1462968, by decide⟩,⟨1463037, by decide⟩,⟨296530, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_114183_1463038 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 114183 ⟨1463038, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 114183
    ⟨1463038, by decide⟩ (by decide) (![⟨1461226, by decide⟩,⟨1462968, by decide⟩,⟨1463037, by decide⟩,⟨296530, by decide⟩]) unmarked_context_11_114183_1463038 node_context_11_114183_1463038
  intro a
  fin_cases a
  · exact context_12_456732_1461226
  · exact context_12_456733_1462968
  · exact context_12_456734_1463037
  · exact context_12_456735_296530

theorem unmarked_context_10_28545_1463039 : frontier 11 ⟨1463039, by decide⟩
    (prefixCache 10 28545) (prefixPartial 10 28545) = false := by
  decide +kernel

theorem node_context_10_28545_1463039 : EJMOriginalGlobalDAGData.nodes 11 ⟨1463039, by decide⟩ =
    .split (coordinate 10) (![⟨1462747, by decide⟩,⟨1192826, by decide⟩,⟨1462901, by decide⟩,⟨1463038, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_28545_1463039 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 28545 ⟨1463039, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 28545
    ⟨1463039, by decide⟩ (by decide) (![⟨1462747, by decide⟩,⟨1192826, by decide⟩,⟨1462901, by decide⟩,⟨1463038, by decide⟩]) unmarked_context_10_28545_1463039 node_context_10_28545_1463039
  intro a
  fin_cases a
  · exact context_11_114180_1462747
  · exact context_11_114181_1192826
  · exact context_11_114182_1462901
  · exact context_11_114183_1463038

theorem selected_cut_50983 : selected 9 ⟨1461661, by decide⟩
    (prefixPartial 12 456736) = some ⟨12, 1, 0, 1461661, 456736, 1, 65536⟩ := by
  decide +kernel

theorem context_12_456736_1461661 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 456736 ⟨1461661, by decide⟩ :=
  accepted_of_selected 12 456736 ⟨1461661, by decide⟩ ⟨12, 1, 0, 1461661, 456736, 1, 65536⟩
    (by decide) selected_cut_50983

theorem selected_cut_50984 : selected 9 ⟨1463110, by decide⟩
    (prefixPartial 12 456737) = some ⟨12, 2, 0, 1463110, 456737, 2053, 65536⟩ := by
  decide +kernel

theorem context_12_456737_1463110 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 456737 ⟨1463110, by decide⟩ :=
  accepted_of_selected 12 456737 ⟨1463110, by decide⟩ ⟨12, 2, 0, 1463110, 456737, 2053, 65536⟩
    (by decide) selected_cut_50984

theorem selected_cut_50985 : selected 9 ⟨1463164, by decide⟩
    (prefixPartial 12 456738) = some ⟨12, 2, 0, 1463164, 456738, 1817, 65536⟩ := by
  decide +kernel

theorem context_12_456738_1463164 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 456738 ⟨1463164, by decide⟩ :=
  accepted_of_selected 12 456738 ⟨1463164, by decide⟩ ⟨12, 2, 0, 1463164, 456738, 1817, 65536⟩
    (by decide) selected_cut_50985

theorem selected_cut_50986 : selected 9 ⟨1463224, by decide⟩
    (prefixPartial 12 456739) = some ⟨12, 2, 0, 1463224, 456739, 1669, 65536⟩ := by
  decide +kernel

theorem context_12_456739_1463224 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 456739 ⟨1463224, by decide⟩ :=
  accepted_of_selected 12 456739 ⟨1463224, by decide⟩ ⟨12, 2, 0, 1463224, 456739, 1669, 65536⟩
    (by decide) selected_cut_50986

theorem unmarked_context_11_114184_1463225 : frontier 10 ⟨1463225, by decide⟩
    (prefixCache 11 114184) (prefixPartial 11 114184) = false := by
  decide +kernel

theorem node_context_11_114184_1463225 : EJMOriginalGlobalDAGData.nodes 10 ⟨1463225, by decide⟩ =
    .split (coordinate 11) (![⟨1461661, by decide⟩,⟨1463110, by decide⟩,⟨1463164, by decide⟩,⟨1463224, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_114184_1463225 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 114184 ⟨1463225, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 114184
    ⟨1463225, by decide⟩ (by decide) (![⟨1461661, by decide⟩,⟨1463110, by decide⟩,⟨1463164, by decide⟩,⟨1463224, by decide⟩]) unmarked_context_11_114184_1463225 node_context_11_114184_1463225
  intro a
  fin_cases a
  · exact context_12_456736_1461661
  · exact context_12_456737_1463110
  · exact context_12_456738_1463164
  · exact context_12_456739_1463224

theorem selected_cut_50987 : selected 10 ⟨1463392, by decide⟩
    (prefixPartial 11 114185) = some ⟨11, 2, 0, 1463392, 114185, 3781, 262144⟩ := by
  decide +kernel

theorem context_11_114185_1463392 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 114185 ⟨1463392, by decide⟩ :=
  accepted_of_selected 11 114185 ⟨1463392, by decide⟩ ⟨11, 2, 0, 1463392, 114185, 3781, 262144⟩
    (by decide) selected_cut_50987

theorem selected_cut_50988 : selected 10 ⟨900587, by decide⟩
    (prefixPartial 11 114186) = some ⟨11, 1, 0, 900587, 114186, 1, 262144⟩ := by
  decide +kernel

theorem context_11_114186_900587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 114186 ⟨900587, by decide⟩ :=
  accepted_of_selected 11 114186 ⟨900587, by decide⟩ ⟨11, 1, 0, 900587, 114186, 1, 262144⟩
    (by decide) selected_cut_50988

theorem selected_cut_50989 : selected 10 ⟨1463488, by decide⟩
    (prefixPartial 11 114187) = some ⟨11, 2, 0, 1463488, 114187, 3249, 262144⟩ := by
  decide +kernel

theorem context_11_114187_1463488 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 114187 ⟨1463488, by decide⟩ :=
  accepted_of_selected 11 114187 ⟨1463488, by decide⟩ ⟨11, 2, 0, 1463488, 114187, 3249, 262144⟩
    (by decide) selected_cut_50989

theorem unmarked_context_10_28546_1463489 : frontier 11 ⟨1463489, by decide⟩
    (prefixCache 10 28546) (prefixPartial 10 28546) = false := by
  decide +kernel

theorem node_context_10_28546_1463489 : EJMOriginalGlobalDAGData.nodes 11 ⟨1463489, by decide⟩ =
    .split (coordinate 10) (![⟨1463225, by decide⟩,⟨1463392, by decide⟩,⟨900587, by decide⟩,⟨1463488, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_28546_1463489 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 28546 ⟨1463489, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 28546
    ⟨1463489, by decide⟩ (by decide) (![⟨1463225, by decide⟩,⟨1463392, by decide⟩,⟨900587, by decide⟩,⟨1463488, by decide⟩]) unmarked_context_10_28546_1463489 node_context_10_28546_1463489
  intro a
  fin_cases a
  · exact context_11_114184_1463225
  · exact context_11_114185_1463392
  · exact context_11_114186_900587
  · exact context_11_114187_1463488

theorem selected_cut_50990 : selected 9 ⟨1462014, by decide⟩
    (prefixPartial 12 456752) = some ⟨12, 1, 0, 1462014, 456752, 1, 65536⟩ := by
  decide +kernel

theorem context_12_456752_1462014 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 456752 ⟨1462014, by decide⟩ :=
  accepted_of_selected 12 456752 ⟨1462014, by decide⟩ ⟨12, 1, 0, 1462014, 456752, 1, 65536⟩
    (by decide) selected_cut_50990

theorem selected_cut_50991 : selected 9 ⟨1463563, by decide⟩
    (prefixPartial 12 456753) = some ⟨12, 2, 0, 1463563, 456753, 1553, 65536⟩ := by
  decide +kernel

theorem context_12_456753_1463563 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 456753 ⟨1463563, by decide⟩ :=
  accepted_of_selected 12 456753 ⟨1463563, by decide⟩ ⟨12, 2, 0, 1463563, 456753, 1553, 65536⟩
    (by decide) selected_cut_50991

theorem selected_cut_50992 : selected 9 ⟨1463610, by decide⟩
    (prefixPartial 12 456754) = some ⟨12, 2, 0, 1463610, 456754, 1377, 65536⟩ := by
  decide +kernel

theorem context_12_456754_1463610 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 456754 ⟨1463610, by decide⟩ :=
  accepted_of_selected 12 456754 ⟨1463610, by decide⟩ ⟨12, 2, 0, 1463610, 456754, 1377, 65536⟩
    (by decide) selected_cut_50992

theorem selected_cut_50993 : selected 9 ⟨1463658, by decide⟩
    (prefixPartial 12 456755) = some ⟨12, 2, 0, 1463658, 456755, 1253, 65536⟩ := by
  decide +kernel

theorem context_12_456755_1463658 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 456755 ⟨1463658, by decide⟩ :=
  accepted_of_selected 12 456755 ⟨1463658, by decide⟩ ⟨12, 2, 0, 1463658, 456755, 1253, 65536⟩
    (by decide) selected_cut_50993

theorem unmarked_context_11_114188_1463659 : frontier 10 ⟨1463659, by decide⟩
    (prefixCache 11 114188) (prefixPartial 11 114188) = false := by
  decide +kernel

theorem node_context_11_114188_1463659 : EJMOriginalGlobalDAGData.nodes 10 ⟨1463659, by decide⟩ =
    .split (coordinate 11) (![⟨1462014, by decide⟩,⟨1463563, by decide⟩,⟨1463610, by decide⟩,⟨1463658, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_114188_1463659 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 114188 ⟨1463659, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 114188
    ⟨1463659, by decide⟩ (by decide) (![⟨1462014, by decide⟩,⟨1463563, by decide⟩,⟨1463610, by decide⟩,⟨1463658, by decide⟩]) unmarked_context_11_114188_1463659 node_context_11_114188_1463659
  intro a
  fin_cases a
  · exact context_12_456752_1462014
  · exact context_12_456753_1463563
  · exact context_12_456754_1463610
  · exact context_12_456755_1463658

theorem selected_cut_50994 : selected 10 ⟨1463778, by decide⟩
    (prefixPartial 11 114189) = some ⟨11, 2, 0, 1463778, 114189, 2681, 262144⟩ := by
  decide +kernel

theorem context_11_114189_1463778 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 114189 ⟨1463778, by decide⟩ :=
  accepted_of_selected 11 114189 ⟨1463778, by decide⟩ ⟨11, 2, 0, 1463778, 114189, 2681, 262144⟩
    (by decide) selected_cut_50994

theorem selected_cut_50995 : selected 10 ⟨1463867, by decide⟩
    (prefixPartial 11 114190) = some ⟨11, 2, 0, 1463867, 114190, 2201, 262144⟩ := by
  decide +kernel

theorem context_11_114190_1463867 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 114190 ⟨1463867, by decide⟩ :=
  accepted_of_selected 11 114190 ⟨1463867, by decide⟩ ⟨11, 2, 0, 1463867, 114190, 2201, 262144⟩
    (by decide) selected_cut_50995

theorem selected_cut_50996 : selected 10 ⟨1463907, by decide⟩
    (prefixPartial 11 114191) = some ⟨11, 2, 0, 1463907, 114191, 305, 262144⟩ := by
  decide +kernel

theorem context_11_114191_1463907 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 114191 ⟨1463907, by decide⟩ :=
  accepted_of_selected 11 114191 ⟨1463907, by decide⟩ ⟨11, 2, 0, 1463907, 114191, 305, 262144⟩
    (by decide) selected_cut_50996

theorem unmarked_context_10_28547_1463908 : frontier 11 ⟨1463908, by decide⟩
    (prefixCache 10 28547) (prefixPartial 10 28547) = false := by
  decide +kernel

theorem node_context_10_28547_1463908 : EJMOriginalGlobalDAGData.nodes 11 ⟨1463908, by decide⟩ =
    .split (coordinate 10) (![⟨1463659, by decide⟩,⟨1463778, by decide⟩,⟨1463867, by decide⟩,⟨1463907, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_28547_1463908 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 28547 ⟨1463908, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 28547
    ⟨1463908, by decide⟩ (by decide) (![⟨1463659, by decide⟩,⟨1463778, by decide⟩,⟨1463867, by decide⟩,⟨1463907, by decide⟩]) unmarked_context_10_28547_1463908 node_context_10_28547_1463908
  intro a
  fin_cases a
  · exact context_11_114188_1463659
  · exact context_11_114189_1463778
  · exact context_11_114190_1463867
  · exact context_11_114191_1463907

theorem unmarked_context_9_7136_1463909 : frontier 12 ⟨1463909, by decide⟩
    (prefixCache 9 7136) (prefixPartial 9 7136) = false := by
  decide +kernel

theorem node_context_9_7136_1463909 : EJMOriginalGlobalDAGData.nodes 12 ⟨1463909, by decide⟩ =
    .split (coordinate 9) (![⟨1462509, by decide⟩,⟨1463039, by decide⟩,⟨1463489, by decide⟩,⟨1463908, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_7136_1463909 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 7136 ⟨1463909, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 7136
    ⟨1463909, by decide⟩ (by decide) (![⟨1462509, by decide⟩,⟨1463039, by decide⟩,⟨1463489, by decide⟩,⟨1463908, by decide⟩]) unmarked_context_9_7136_1463909 node_context_9_7136_1463909
  intro a
  fin_cases a
  · exact context_10_28544_1462509
  · exact context_10_28545_1463039
  · exact context_10_28546_1463489
  · exact context_10_28547_1463908

theorem selected_cut_50997 : selected 11 ⟨793297, by decide⟩
    (prefixPartial 10 28548) = some ⟨10, 1, 0, 793297, 28548, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_28548_793297 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 28548 ⟨793297, by decide⟩ :=
  accepted_of_selected 10 28548 ⟨793297, by decide⟩ ⟨10, 1, 0, 793297, 28548, 1, 1048576⟩
    (by decide) selected_cut_50997

theorem selected_cut_50998 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 28549) = some ⟨10, 1, 0, 893098, 28549, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_28549_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 28549 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 28549 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 28549, 1, 1048576⟩
    (by decide) selected_cut_50998

theorem selected_cut_50999 : selected 10 ⟨1464001, by decide⟩
    (prefixPartial 11 114200) = some ⟨11, 2, 0, 1464001, 114200, 1853, 262144⟩ := by
  decide +kernel

theorem context_11_114200_1464001 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 114200 ⟨1464001, by decide⟩ :=
  accepted_of_selected 11 114200 ⟨1464001, by decide⟩ ⟨11, 2, 0, 1464001, 114200, 1853, 262144⟩
    (by decide) selected_cut_50999

theorem selected_cut_51000 : selected 10 ⟨1464093, by decide⟩
    (prefixPartial 11 114201) = some ⟨11, 2, 0, 1464093, 114201, 2401, 262144⟩ := by
  decide +kernel

theorem context_11_114201_1464093 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 114201 ⟨1464093, by decide⟩ :=
  accepted_of_selected 11 114201 ⟨1464093, by decide⟩ ⟨11, 2, 0, 1464093, 114201, 2401, 262144⟩
    (by decide) selected_cut_51000

theorem selected_cut_51001 : selected 10 ⟨900587, by decide⟩
    (prefixPartial 11 114202) = some ⟨11, 1, 0, 900587, 114202, 1, 262144⟩ := by
  decide +kernel

theorem context_11_114202_900587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 114202 ⟨900587, by decide⟩ :=
  accepted_of_selected 11 114202 ⟨900587, by decide⟩ ⟨11, 1, 0, 900587, 114202, 1, 262144⟩
    (by decide) selected_cut_51001

theorem selected_cut_51002 : selected 10 ⟨1464148, by decide⟩
    (prefixPartial 11 114203) = some ⟨11, 2, 0, 1464148, 114203, 1293, 262144⟩ := by
  decide +kernel

theorem context_11_114203_1464148 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 114203 ⟨1464148, by decide⟩ :=
  accepted_of_selected 11 114203 ⟨1464148, by decide⟩ ⟨11, 2, 0, 1464148, 114203, 1293, 262144⟩
    (by decide) selected_cut_51002

theorem unmarked_context_10_28550_1464149 : frontier 11 ⟨1464149, by decide⟩
    (prefixCache 10 28550) (prefixPartial 10 28550) = false := by
  decide +kernel

theorem node_context_10_28550_1464149 : EJMOriginalGlobalDAGData.nodes 11 ⟨1464149, by decide⟩ =
    .split (coordinate 10) (![⟨1464001, by decide⟩,⟨1464093, by decide⟩,⟨900587, by decide⟩,⟨1464148, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_28550_1464149 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 28550 ⟨1464149, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 28550
    ⟨1464149, by decide⟩ (by decide) (![⟨1464001, by decide⟩,⟨1464093, by decide⟩,⟨900587, by decide⟩,⟨1464148, by decide⟩]) unmarked_context_10_28550_1464149 node_context_10_28550_1464149
  intro a
  fin_cases a
  · exact context_11_114200_1464001
  · exact context_11_114201_1464093
  · exact context_11_114202_900587
  · exact context_11_114203_1464148

theorem selected_cut_51003 : selected 11 ⟨1464295, by decide⟩
    (prefixPartial 10 28551) = some ⟨10, 2, 0, 1464295, 28551, 3129, 1048576⟩ := by
  decide +kernel

theorem context_10_28551_1464295 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 28551 ⟨1464295, by decide⟩ :=
  accepted_of_selected 10 28551 ⟨1464295, by decide⟩ ⟨10, 2, 0, 1464295, 28551, 3129, 1048576⟩
    (by decide) selected_cut_51003

theorem unmarked_context_9_7137_1464296 : frontier 12 ⟨1464296, by decide⟩
    (prefixCache 9 7137) (prefixPartial 9 7137) = false := by
  decide +kernel

theorem node_context_9_7137_1464296 : EJMOriginalGlobalDAGData.nodes 12 ⟨1464296, by decide⟩ =
    .split (coordinate 9) (![⟨793297, by decide⟩,⟨893098, by decide⟩,⟨1464149, by decide⟩,⟨1464295, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_7137_1464296 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 7137 ⟨1464296, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 7137
    ⟨1464296, by decide⟩ (by decide) (![⟨793297, by decide⟩,⟨893098, by decide⟩,⟨1464149, by decide⟩,⟨1464295, by decide⟩]) unmarked_context_9_7137_1464296 node_context_9_7137_1464296
  intro a
  fin_cases a
  · exact context_10_28548_793297
  · exact context_10_28549_893098
  · exact context_10_28550_1464149
  · exact context_10_28551_1464295

theorem selected_cut_51004 : selected 12 ⟨1464348, by decide⟩
    (prefixPartial 9 7138) = some ⟨9, 2, 0, 1464348, 7138, 741, 4194304⟩ := by
  decide +kernel

theorem context_9_7138_1464348 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 7138 ⟨1464348, by decide⟩ :=
  accepted_of_selected 9 7138 ⟨1464348, by decide⟩ ⟨9, 2, 0, 1464348, 7138, 741, 4194304⟩
    (by decide) selected_cut_51004

theorem selected_cut_51005 : selected 12 ⟨1464376, by decide⟩
    (prefixPartial 9 7139) = some ⟨9, 2, 0, 1464376, 7139, 253, 4194304⟩ := by
  decide +kernel

theorem context_9_7139_1464376 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 7139 ⟨1464376, by decide⟩ :=
  accepted_of_selected 9 7139 ⟨1464376, by decide⟩ ⟨9, 2, 0, 1464376, 7139, 253, 4194304⟩
    (by decide) selected_cut_51005

theorem unmarked_context_8_1784_1464377 : frontier 13 ⟨1464377, by decide⟩
    (prefixCache 8 1784) (prefixPartial 8 1784) = false := by
  decide +kernel

theorem node_context_8_1784_1464377 : EJMOriginalGlobalDAGData.nodes 13 ⟨1464377, by decide⟩ =
    .split (coordinate 8) (![⟨1463909, by decide⟩,⟨1464296, by decide⟩,⟨1464348, by decide⟩,⟨1464376, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1784_1464377 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1784 ⟨1464377, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1784
    ⟨1464377, by decide⟩ (by decide) (![⟨1463909, by decide⟩,⟨1464296, by decide⟩,⟨1464348, by decide⟩,⟨1464376, by decide⟩]) unmarked_context_8_1784_1464377 node_context_8_1784_1464377
  intro a
  fin_cases a
  · exact context_9_7136_1463909
  · exact context_9_7137_1464296
  · exact context_9_7138_1464348
  · exact context_9_7139_1464376

theorem selected_cut_51006 : selected 11 ⟨1464436, by decide⟩
    (prefixPartial 10 28560) = some ⟨10, 2, 0, 1464436, 28560, 1345, 1048576⟩ := by
  decide +kernel

theorem context_10_28560_1464436 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 28560 ⟨1464436, by decide⟩ :=
  accepted_of_selected 10 28560 ⟨1464436, by decide⟩ ⟨10, 2, 0, 1464436, 28560, 1345, 1048576⟩
    (by decide) selected_cut_51006

theorem selected_cut_51007 : selected 9 ⟨1461226, by decide⟩
    (prefixPartial 12 456976) = some ⟨12, 1, 0, 1461226, 456976, 1, 65536⟩ := by
  decide +kernel

theorem context_12_456976_1461226 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 456976 ⟨1461226, by decide⟩ :=
  accepted_of_selected 12 456976 ⟨1461226, by decide⟩ ⟨12, 1, 0, 1461226, 456976, 1, 65536⟩
    (by decide) selected_cut_51007

theorem selected_cut_51008 : selected 9 ⟨1464497, by decide⟩
    (prefixPartial 12 456977) = some ⟨12, 2, 0, 1464497, 456977, 2041, 65536⟩ := by
  decide +kernel

theorem context_12_456977_1464497 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 456977 ⟨1464497, by decide⟩ :=
  accepted_of_selected 12 456977 ⟨1464497, by decide⟩ ⟨12, 2, 0, 1464497, 456977, 2041, 65536⟩
    (by decide) selected_cut_51008

theorem selected_cut_51009 : selected 9 ⟨1464555, by decide⟩
    (prefixPartial 12 456978) = some ⟨12, 2, 0, 1464555, 456978, 2009, 65536⟩ := by
  decide +kernel

theorem context_12_456978_1464555 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 456978 ⟨1464555, by decide⟩ :=
  accepted_of_selected 12 456978 ⟨1464555, by decide⟩ ⟨12, 2, 0, 1464555, 456978, 2009, 65536⟩
    (by decide) selected_cut_51009

theorem selected_cut_51010 : selected 9 ⟨1464606, by decide⟩
    (prefixPartial 12 456979) = some ⟨12, 2, 0, 1464606, 456979, 1705, 65536⟩ := by
  decide +kernel

theorem context_12_456979_1464606 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 456979 ⟨1464606, by decide⟩ :=
  accepted_of_selected 12 456979 ⟨1464606, by decide⟩ ⟨12, 2, 0, 1464606, 456979, 1705, 65536⟩
    (by decide) selected_cut_51010

theorem unmarked_context_11_114244_1464607 : frontier 10 ⟨1464607, by decide⟩
    (prefixCache 11 114244) (prefixPartial 11 114244) = false := by
  decide +kernel

theorem node_context_11_114244_1464607 : EJMOriginalGlobalDAGData.nodes 10 ⟨1464607, by decide⟩ =
    .split (coordinate 11) (![⟨1461226, by decide⟩,⟨1464497, by decide⟩,⟨1464555, by decide⟩,⟨1464606, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_114244_1464607 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 114244 ⟨1464607, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 114244
    ⟨1464607, by decide⟩ (by decide) (![⟨1461226, by decide⟩,⟨1464497, by decide⟩,⟨1464555, by decide⟩,⟨1464606, by decide⟩]) unmarked_context_11_114244_1464607 node_context_11_114244_1464607
  intro a
  fin_cases a
  · exact context_12_456976_1461226
  · exact context_12_456977_1464497
  · exact context_12_456978_1464555
  · exact context_12_456979_1464606

theorem selected_cut_51011 : selected 10 ⟨1192826, by decide⟩
    (prefixPartial 11 114245) = some ⟨11, 1, 0, 1192826, 114245, 1, 262144⟩ := by
  decide +kernel

theorem context_11_114245_1192826 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 114245 ⟨1192826, by decide⟩ :=
  accepted_of_selected 11 114245 ⟨1192826, by decide⟩ ⟨11, 1, 0, 1192826, 114245, 1, 262144⟩
    (by decide) selected_cut_51011

theorem selected_cut_51012 : selected 10 ⟨1464709, by decide⟩
    (prefixPartial 11 114246) = some ⟨11, 2, 0, 1464709, 114246, 3389, 262144⟩ := by
  decide +kernel

theorem context_11_114246_1464709 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 114246 ⟨1464709, by decide⟩ :=
  accepted_of_selected 11 114246 ⟨1464709, by decide⟩ ⟨11, 2, 0, 1464709, 114246, 3389, 262144⟩
    (by decide) selected_cut_51012

theorem selected_cut_51013 : selected 10 ⟨1464803, by decide⟩
    (prefixPartial 11 114247) = some ⟨11, 2, 0, 1464803, 114247, 3409, 262144⟩ := by
  decide +kernel

theorem context_11_114247_1464803 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 114247 ⟨1464803, by decide⟩ :=
  accepted_of_selected 11 114247 ⟨1464803, by decide⟩ ⟨11, 2, 0, 1464803, 114247, 3409, 262144⟩
    (by decide) selected_cut_51013

theorem unmarked_context_10_28561_1464804 : frontier 11 ⟨1464804, by decide⟩
    (prefixCache 10 28561) (prefixPartial 10 28561) = false := by
  decide +kernel

theorem node_context_10_28561_1464804 : EJMOriginalGlobalDAGData.nodes 11 ⟨1464804, by decide⟩ =
    .split (coordinate 10) (![⟨1464607, by decide⟩,⟨1192826, by decide⟩,⟨1464709, by decide⟩,⟨1464803, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_28561_1464804 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 28561 ⟨1464804, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 28561
    ⟨1464804, by decide⟩ (by decide) (![⟨1464607, by decide⟩,⟨1192826, by decide⟩,⟨1464709, by decide⟩,⟨1464803, by decide⟩]) unmarked_context_10_28561_1464804 node_context_10_28561_1464804
  intro a
  fin_cases a
  · exact context_11_114244_1464607
  · exact context_11_114245_1192826
  · exact context_11_114246_1464709
  · exact context_11_114247_1464803

theorem selected_cut_51014 : selected 9 ⟨1461661, by decide⟩
    (prefixPartial 12 456992) = some ⟨12, 1, 0, 1461661, 456992, 1, 65536⟩ := by
  decide +kernel

theorem context_12_456992_1461661 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 456992 ⟨1461661, by decide⟩ :=
  accepted_of_selected 12 456992 ⟨1461661, by decide⟩ ⟨12, 1, 0, 1461661, 456992, 1, 65536⟩
    (by decide) selected_cut_51014

theorem selected_cut_51015 : selected 9 ⟨1464857, by decide⟩
    (prefixPartial 12 456993) = some ⟨12, 2, 0, 1464857, 456993, 1737, 65536⟩ := by
  decide +kernel

theorem context_12_456993_1464857 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 456993 ⟨1464857, by decide⟩ :=
  accepted_of_selected 12 456993 ⟨1464857, by decide⟩ ⟨12, 2, 0, 1464857, 456993, 1737, 65536⟩
    (by decide) selected_cut_51015

theorem selected_cut_51016 : selected 9 ⟨1464903, by decide⟩
    (prefixPartial 12 456994) = some ⟨12, 2, 0, 1464903, 456994, 1673, 65536⟩ := by
  decide +kernel

theorem context_12_456994_1464903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 456994 ⟨1464903, by decide⟩ :=
  accepted_of_selected 12 456994 ⟨1464903, by decide⟩ ⟨12, 2, 0, 1464903, 456994, 1673, 65536⟩
    (by decide) selected_cut_51016

theorem selected_cut_51017 : selected 9 ⟨1464951, by decide⟩
    (prefixPartial 12 456995) = some ⟨12, 2, 0, 1464951, 456995, 1497, 65536⟩ := by
  decide +kernel

theorem context_12_456995_1464951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 456995 ⟨1464951, by decide⟩ :=
  accepted_of_selected 12 456995 ⟨1464951, by decide⟩ ⟨12, 2, 0, 1464951, 456995, 1497, 65536⟩
    (by decide) selected_cut_51017

theorem unmarked_context_11_114248_1464952 : frontier 10 ⟨1464952, by decide⟩
    (prefixCache 11 114248) (prefixPartial 11 114248) = false := by
  decide +kernel

theorem node_context_11_114248_1464952 : EJMOriginalGlobalDAGData.nodes 10 ⟨1464952, by decide⟩ =
    .split (coordinate 11) (![⟨1461661, by decide⟩,⟨1464857, by decide⟩,⟨1464903, by decide⟩,⟨1464951, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_114248_1464952 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 114248 ⟨1464952, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 114248
    ⟨1464952, by decide⟩ (by decide) (![⟨1461661, by decide⟩,⟨1464857, by decide⟩,⟨1464903, by decide⟩,⟨1464951, by decide⟩]) unmarked_context_11_114248_1464952 node_context_11_114248_1464952
  intro a
  fin_cases a
  · exact context_12_456992_1461661
  · exact context_12_456993_1464857
  · exact context_12_456994_1464903
  · exact context_12_456995_1464951

theorem selected_cut_51018 : selected 10 ⟨1465067, by decide⟩
    (prefixPartial 11 114249) = some ⟨11, 2, 0, 1465067, 114249, 3169, 262144⟩ := by
  decide +kernel

theorem context_11_114249_1465067 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 114249 ⟨1465067, by decide⟩ :=
  accepted_of_selected 11 114249 ⟨1465067, by decide⟩ ⟨11, 2, 0, 1465067, 114249, 3169, 262144⟩
    (by decide) selected_cut_51018

theorem selected_cut_51019 : selected 10 ⟨900587, by decide⟩
    (prefixPartial 11 114250) = some ⟨11, 1, 0, 900587, 114250, 1, 262144⟩ := by
  decide +kernel

theorem context_11_114250_900587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 114250 ⟨900587, by decide⟩ :=
  accepted_of_selected 11 114250 ⟨900587, by decide⟩ ⟨11, 1, 0, 900587, 114250, 1, 262144⟩
    (by decide) selected_cut_51019

theorem selected_cut_51020 : selected 10 ⟨1465151, by decide⟩
    (prefixPartial 11 114251) = some ⟨11, 2, 0, 1465151, 114251, 2857, 262144⟩ := by
  decide +kernel

theorem context_11_114251_1465151 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 114251 ⟨1465151, by decide⟩ :=
  accepted_of_selected 11 114251 ⟨1465151, by decide⟩ ⟨11, 2, 0, 1465151, 114251, 2857, 262144⟩
    (by decide) selected_cut_51020

theorem unmarked_context_10_28562_1465152 : frontier 11 ⟨1465152, by decide⟩
    (prefixCache 10 28562) (prefixPartial 10 28562) = false := by
  decide +kernel

theorem node_context_10_28562_1465152 : EJMOriginalGlobalDAGData.nodes 11 ⟨1465152, by decide⟩ =
    .split (coordinate 10) (![⟨1464952, by decide⟩,⟨1465067, by decide⟩,⟨900587, by decide⟩,⟨1465151, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_28562_1465152 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 28562 ⟨1465152, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 28562
    ⟨1465152, by decide⟩ (by decide) (![⟨1464952, by decide⟩,⟨1465067, by decide⟩,⟨900587, by decide⟩,⟨1465151, by decide⟩]) unmarked_context_10_28562_1465152 node_context_10_28562_1465152
  intro a
  fin_cases a
  · exact context_11_114248_1464952
  · exact context_11_114249_1465067
  · exact context_11_114250_900587
  · exact context_11_114251_1465151

theorem selected_cut_51021 : selected 10 ⟨1465279, by decide⟩
    (prefixPartial 11 114252) = some ⟨11, 2, 0, 1465279, 114252, 3793, 262144⟩ := by
  decide +kernel

theorem context_11_114252_1465279 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 114252 ⟨1465279, by decide⟩ :=
  accepted_of_selected 11 114252 ⟨1465279, by decide⟩ ⟨11, 2, 0, 1465279, 114252, 3793, 262144⟩
    (by decide) selected_cut_51021

theorem selected_cut_51022 : selected 10 ⟨1465357, by decide⟩
    (prefixPartial 11 114253) = some ⟨11, 2, 0, 1465357, 114253, 2369, 262144⟩ := by
  decide +kernel

theorem context_11_114253_1465357 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 114253 ⟨1465357, by decide⟩ :=
  accepted_of_selected 11 114253 ⟨1465357, by decide⟩ ⟨11, 2, 0, 1465357, 114253, 2369, 262144⟩
    (by decide) selected_cut_51022

theorem selected_cut_51023 : selected 10 ⟨1465430, by decide⟩
    (prefixPartial 11 114254) = some ⟨11, 2, 0, 1465430, 114254, 1897, 262144⟩ := by
  decide +kernel

theorem context_11_114254_1465430 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 114254 ⟨1465430, by decide⟩ :=
  accepted_of_selected 11 114254 ⟨1465430, by decide⟩ ⟨11, 2, 0, 1465430, 114254, 1897, 262144⟩
    (by decide) selected_cut_51023

theorem selected_cut_51024 : selected 10 ⟨1465431, by decide⟩
    (prefixPartial 11 114255) = some ⟨11, 2, 0, 1465431, 114255, 5, 262144⟩ := by
  decide +kernel

theorem context_11_114255_1465431 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 114255 ⟨1465431, by decide⟩ :=
  accepted_of_selected 11 114255 ⟨1465431, by decide⟩ ⟨11, 2, 0, 1465431, 114255, 5, 262144⟩
    (by decide) selected_cut_51024

theorem unmarked_context_10_28563_1465432 : frontier 11 ⟨1465432, by decide⟩
    (prefixCache 10 28563) (prefixPartial 10 28563) = false := by
  decide +kernel

theorem node_context_10_28563_1465432 : EJMOriginalGlobalDAGData.nodes 11 ⟨1465432, by decide⟩ =
    .split (coordinate 10) (![⟨1465279, by decide⟩,⟨1465357, by decide⟩,⟨1465430, by decide⟩,⟨1465431, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_28563_1465432 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 28563 ⟨1465432, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 28563
    ⟨1465432, by decide⟩ (by decide) (![⟨1465279, by decide⟩,⟨1465357, by decide⟩,⟨1465430, by decide⟩,⟨1465431, by decide⟩]) unmarked_context_10_28563_1465432 node_context_10_28563_1465432
  intro a
  fin_cases a
  · exact context_11_114252_1465279
  · exact context_11_114253_1465357
  · exact context_11_114254_1465430
  · exact context_11_114255_1465431

theorem unmarked_context_9_7140_1465433 : frontier 12 ⟨1465433, by decide⟩
    (prefixCache 9 7140) (prefixPartial 9 7140) = false := by
  decide +kernel

theorem node_context_9_7140_1465433 : EJMOriginalGlobalDAGData.nodes 12 ⟨1465433, by decide⟩ =
    .split (coordinate 9) (![⟨1464436, by decide⟩,⟨1464804, by decide⟩,⟨1465152, by decide⟩,⟨1465432, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_7140_1465433 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 7140 ⟨1465433, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 7140
    ⟨1465433, by decide⟩ (by decide) (![⟨1464436, by decide⟩,⟨1464804, by decide⟩,⟨1465152, by decide⟩,⟨1465432, by decide⟩]) unmarked_context_9_7140_1465433 node_context_9_7140_1465433
  intro a
  fin_cases a
  · exact context_10_28560_1464436
  · exact context_10_28561_1464804
  · exact context_10_28562_1465152
  · exact context_10_28563_1465432

theorem selected_cut_51025 : selected 11 ⟨793297, by decide⟩
    (prefixPartial 10 28564) = some ⟨10, 1, 0, 793297, 28564, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_28564_793297 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 28564 ⟨793297, by decide⟩ :=
  accepted_of_selected 10 28564 ⟨793297, by decide⟩ ⟨10, 1, 0, 793297, 28564, 1, 1048576⟩
    (by decide) selected_cut_51025

theorem selected_cut_51026 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 28565) = some ⟨10, 1, 0, 893098, 28565, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_28565_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 28565 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 28565 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 28565, 1, 1048576⟩
    (by decide) selected_cut_51026

theorem selected_cut_51027 : selected 10 ⟨1465493, by decide⟩
    (prefixPartial 11 114264) = some ⟨11, 2, 0, 1465493, 114264, 1753, 262144⟩ := by
  decide +kernel

theorem context_11_114264_1465493 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 114264 ⟨1465493, by decide⟩ :=
  accepted_of_selected 11 114264 ⟨1465493, by decide⟩ ⟨11, 2, 0, 1465493, 114264, 1753, 262144⟩
    (by decide) selected_cut_51027

theorem selected_cut_51028 : selected 10 ⟨1465572, by decide⟩
    (prefixPartial 11 114265) = some ⟨11, 2, 0, 1465572, 114265, 2317, 262144⟩ := by
  decide +kernel

theorem context_11_114265_1465572 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 114265 ⟨1465572, by decide⟩ :=
  accepted_of_selected 11 114265 ⟨1465572, by decide⟩ ⟨11, 2, 0, 1465572, 114265, 2317, 262144⟩
    (by decide) selected_cut_51028

theorem selected_cut_51029 : selected 10 ⟨900587, by decide⟩
    (prefixPartial 11 114266) = some ⟨11, 1, 0, 900587, 114266, 1, 262144⟩ := by
  decide +kernel

theorem context_11_114266_900587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 114266 ⟨900587, by decide⟩ :=
  accepted_of_selected 11 114266 ⟨900587, by decide⟩ ⟨11, 1, 0, 900587, 114266, 1, 262144⟩
    (by decide) selected_cut_51029

theorem selected_cut_51030 : selected 10 ⟨1465619, by decide⟩
    (prefixPartial 11 114267) = some ⟨11, 2, 0, 1465619, 114267, 1281, 262144⟩ := by
  decide +kernel

theorem context_11_114267_1465619 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 114267 ⟨1465619, by decide⟩ :=
  accepted_of_selected 11 114267 ⟨1465619, by decide⟩ ⟨11, 2, 0, 1465619, 114267, 1281, 262144⟩
    (by decide) selected_cut_51030

theorem unmarked_context_10_28566_1465620 : frontier 11 ⟨1465620, by decide⟩
    (prefixCache 10 28566) (prefixPartial 10 28566) = false := by
  decide +kernel

theorem node_context_10_28566_1465620 : EJMOriginalGlobalDAGData.nodes 11 ⟨1465620, by decide⟩ =
    .split (coordinate 10) (![⟨1465493, by decide⟩,⟨1465572, by decide⟩,⟨900587, by decide⟩,⟨1465619, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_28566_1465620 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 28566 ⟨1465620, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 28566
    ⟨1465620, by decide⟩ (by decide) (![⟨1465493, by decide⟩,⟨1465572, by decide⟩,⟨900587, by decide⟩,⟨1465619, by decide⟩]) unmarked_context_10_28566_1465620 node_context_10_28566_1465620
  intro a
  fin_cases a
  · exact context_11_114264_1465493
  · exact context_11_114265_1465572
  · exact context_11_114266_900587
  · exact context_11_114267_1465619

theorem selected_cut_51031 : selected 11 ⟨1465727, by decide⟩
    (prefixPartial 10 28567) = some ⟨10, 2, 0, 1465727, 28567, 3081, 1048576⟩ := by
  decide +kernel

theorem context_10_28567_1465727 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 28567 ⟨1465727, by decide⟩ :=
  accepted_of_selected 10 28567 ⟨1465727, by decide⟩ ⟨10, 2, 0, 1465727, 28567, 3081, 1048576⟩
    (by decide) selected_cut_51031

theorem unmarked_context_9_7141_1465728 : frontier 12 ⟨1465728, by decide⟩
    (prefixCache 9 7141) (prefixPartial 9 7141) = false := by
  decide +kernel

theorem node_context_9_7141_1465728 : EJMOriginalGlobalDAGData.nodes 12 ⟨1465728, by decide⟩ =
    .split (coordinate 9) (![⟨793297, by decide⟩,⟨893098, by decide⟩,⟨1465620, by decide⟩,⟨1465727, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_7141_1465728 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 7141 ⟨1465728, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 7141
    ⟨1465728, by decide⟩ (by decide) (![⟨793297, by decide⟩,⟨893098, by decide⟩,⟨1465620, by decide⟩,⟨1465727, by decide⟩]) unmarked_context_9_7141_1465728 node_context_9_7141_1465728
  intro a
  fin_cases a
  · exact context_10_28564_793297
  · exact context_10_28565_893098
  · exact context_10_28566_1465620
  · exact context_10_28567_1465727

theorem selected_cut_51032 : selected 12 ⟨1465772, by decide⟩
    (prefixPartial 9 7142) = some ⟨9, 2, 0, 1465772, 7142, 709, 4194304⟩ := by
  decide +kernel

theorem context_9_7142_1465772 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 7142 ⟨1465772, by decide⟩ :=
  accepted_of_selected 9 7142 ⟨1465772, by decide⟩ ⟨9, 2, 0, 1465772, 7142, 709, 4194304⟩
    (by decide) selected_cut_51032

theorem selected_cut_51033 : selected 12 ⟨1465792, by decide⟩
    (prefixPartial 9 7143) = some ⟨9, 2, 0, 1465792, 7143, 289, 4194304⟩ := by
  decide +kernel

theorem context_9_7143_1465792 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 7143 ⟨1465792, by decide⟩ :=
  accepted_of_selected 9 7143 ⟨1465792, by decide⟩ ⟨9, 2, 0, 1465792, 7143, 289, 4194304⟩
    (by decide) selected_cut_51033

theorem unmarked_context_8_1785_1465793 : frontier 13 ⟨1465793, by decide⟩
    (prefixCache 8 1785) (prefixPartial 8 1785) = false := by
  decide +kernel

theorem node_context_8_1785_1465793 : EJMOriginalGlobalDAGData.nodes 13 ⟨1465793, by decide⟩ =
    .split (coordinate 8) (![⟨1465433, by decide⟩,⟨1465728, by decide⟩,⟨1465772, by decide⟩,⟨1465792, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1785_1465793 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1785 ⟨1465793, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1785
    ⟨1465793, by decide⟩ (by decide) (![⟨1465433, by decide⟩,⟨1465728, by decide⟩,⟨1465772, by decide⟩,⟨1465792, by decide⟩]) unmarked_context_8_1785_1465793 node_context_8_1785_1465793
  intro a
  fin_cases a
  · exact context_9_7140_1465433
  · exact context_9_7141_1465728
  · exact context_9_7142_1465772
  · exact context_9_7143_1465792

theorem selected_cut_51034 : selected 11 ⟨1465887, by decide⟩
    (prefixPartial 10 28576) = some ⟨10, 2, 0, 1465887, 28576, 2725, 1048576⟩ := by
  decide +kernel

theorem context_10_28576_1465887 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 28576 ⟨1465887, by decide⟩ :=
  accepted_of_selected 10 28576 ⟨1465887, by decide⟩ ⟨10, 2, 0, 1465887, 28576, 2725, 1048576⟩
    (by decide) selected_cut_51034

theorem selected_cut_51035 : selected 9 ⟨1461226, by decide⟩
    (prefixPartial 12 457232) = some ⟨12, 1, 0, 1461226, 457232, 1, 65536⟩ := by
  decide +kernel

theorem context_12_457232_1461226 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 457232 ⟨1461226, by decide⟩ :=
  accepted_of_selected 12 457232 ⟨1461226, by decide⟩ ⟨12, 1, 0, 1461226, 457232, 1, 65536⟩
    (by decide) selected_cut_51035

theorem selected_cut_51036 : selected 9 ⟨1465960, by decide⟩
    (prefixPartial 12 457233) = some ⟨12, 2, 0, 1465960, 457233, 2649, 65536⟩ := by
  decide +kernel

theorem context_12_457233_1465960 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 457233 ⟨1465960, by decide⟩ :=
  accepted_of_selected 12 457233 ⟨1465960, by decide⟩ ⟨12, 2, 0, 1465960, 457233, 2649, 65536⟩
    (by decide) selected_cut_51036

theorem selected_cut_51037 : selected 9 ⟨1466027, by decide⟩
    (prefixPartial 12 457234) = some ⟨12, 2, 0, 1466027, 457234, 2429, 65536⟩ := by
  decide +kernel

theorem context_12_457234_1466027 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 457234 ⟨1466027, by decide⟩ :=
  accepted_of_selected 12 457234 ⟨1466027, by decide⟩ ⟨12, 2, 0, 1466027, 457234, 2429, 65536⟩
    (by decide) selected_cut_51037

theorem selected_cut_51038 : selected 9 ⟨1466100, by decide⟩
    (prefixPartial 12 457235) = some ⟨12, 2, 0, 1466100, 457235, 2257, 65536⟩ := by
  decide +kernel

theorem context_12_457235_1466100 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 457235 ⟨1466100, by decide⟩ :=
  accepted_of_selected 12 457235 ⟨1466100, by decide⟩ ⟨12, 2, 0, 1466100, 457235, 2257, 65536⟩
    (by decide) selected_cut_51038

theorem unmarked_context_11_114308_1466101 : frontier 10 ⟨1466101, by decide⟩
    (prefixCache 11 114308) (prefixPartial 11 114308) = false := by
  decide +kernel

theorem node_context_11_114308_1466101 : EJMOriginalGlobalDAGData.nodes 10 ⟨1466101, by decide⟩ =
    .split (coordinate 11) (![⟨1461226, by decide⟩,⟨1465960, by decide⟩,⟨1466027, by decide⟩,⟨1466100, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_114308_1466101 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 114308 ⟨1466101, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 114308
    ⟨1466101, by decide⟩ (by decide) (![⟨1461226, by decide⟩,⟨1465960, by decide⟩,⟨1466027, by decide⟩,⟨1466100, by decide⟩]) unmarked_context_11_114308_1466101 node_context_11_114308_1466101
  intro a
  fin_cases a
  · exact context_12_457232_1461226
  · exact context_12_457233_1465960
  · exact context_12_457234_1466027
  · exact context_12_457235_1466100

theorem selected_cut_51039 : selected 10 ⟨1192826, by decide⟩
    (prefixPartial 11 114309) = some ⟨11, 1, 0, 1192826, 114309, 1, 262144⟩ := by
  decide +kernel

theorem context_11_114309_1192826 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 114309 ⟨1192826, by decide⟩ :=
  accepted_of_selected 11 114309 ⟨1192826, by decide⟩ ⟨11, 1, 0, 1192826, 114309, 1, 262144⟩
    (by decide) selected_cut_51039

theorem selected_cut_51040 : selected 10 ⟨1466209, by decide⟩
    (prefixPartial 11 114310) = some ⟨11, 2, 0, 1466209, 114310, 3957, 262144⟩ := by
  decide +kernel

theorem context_11_114310_1466209 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 114310 ⟨1466209, by decide⟩ :=
  accepted_of_selected 11 114310 ⟨1466209, by decide⟩ ⟨11, 2, 0, 1466209, 114310, 3957, 262144⟩
    (by decide) selected_cut_51040

theorem selected_cut_51041 : selected 9 ⟨1461226, by decide⟩
    (prefixPartial 12 457244) = some ⟨12, 1, 0, 1461226, 457244, 1, 65536⟩ := by
  decide +kernel

theorem context_12_457244_1461226 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 457244 ⟨1461226, by decide⟩ :=
  accepted_of_selected 12 457244 ⟨1461226, by decide⟩ ⟨12, 1, 0, 1461226, 457244, 1, 65536⟩
    (by decide) selected_cut_51041

theorem selected_cut_51042 : selected 9 ⟨1466272, by decide⟩
    (prefixPartial 12 457245) = some ⟨12, 2, 0, 1466272, 457245, 2313, 65536⟩ := by
  decide +kernel

theorem context_12_457245_1466272 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 457245 ⟨1466272, by decide⟩ :=
  accepted_of_selected 12 457245 ⟨1466272, by decide⟩ ⟨12, 2, 0, 1466272, 457245, 2313, 65536⟩
    (by decide) selected_cut_51042

theorem selected_cut_51043 : selected 9 ⟨1466324, by decide⟩
    (prefixPartial 12 457246) = some ⟨12, 2, 0, 1466324, 457246, 2065, 65536⟩ := by
  decide +kernel

theorem context_12_457246_1466324 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 457246 ⟨1466324, by decide⟩ :=
  accepted_of_selected 12 457246 ⟨1466324, by decide⟩ ⟨12, 2, 0, 1466324, 457246, 2065, 65536⟩
    (by decide) selected_cut_51043

theorem selected_cut_51044 : selected 9 ⟨1444743, by decide⟩
    (prefixPartial 12 457247) = some ⟨12, 1, 0, 1444743, 457247, 1, 65536⟩ := by
  decide +kernel

theorem context_12_457247_1444743 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 457247 ⟨1444743, by decide⟩ :=
  accepted_of_selected 12 457247 ⟨1444743, by decide⟩ ⟨12, 1, 0, 1444743, 457247, 1, 65536⟩
    (by decide) selected_cut_51044

theorem unmarked_context_11_114311_1466325 : frontier 10 ⟨1466325, by decide⟩
    (prefixCache 11 114311) (prefixPartial 11 114311) = false := by
  decide +kernel

theorem node_context_11_114311_1466325 : EJMOriginalGlobalDAGData.nodes 10 ⟨1466325, by decide⟩ =
    .split (coordinate 11) (![⟨1461226, by decide⟩,⟨1466272, by decide⟩,⟨1466324, by decide⟩,⟨1444743, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_114311_1466325 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 114311 ⟨1466325, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 114311
    ⟨1466325, by decide⟩ (by decide) (![⟨1461226, by decide⟩,⟨1466272, by decide⟩,⟨1466324, by decide⟩,⟨1444743, by decide⟩]) unmarked_context_11_114311_1466325 node_context_11_114311_1466325
  intro a
  fin_cases a
  · exact context_12_457244_1461226
  · exact context_12_457245_1466272
  · exact context_12_457246_1466324
  · exact context_12_457247_1444743

theorem unmarked_context_10_28577_1466326 : frontier 11 ⟨1466326, by decide⟩
    (prefixCache 10 28577) (prefixPartial 10 28577) = false := by
  decide +kernel

theorem node_context_10_28577_1466326 : EJMOriginalGlobalDAGData.nodes 11 ⟨1466326, by decide⟩ =
    .split (coordinate 10) (![⟨1466101, by decide⟩,⟨1192826, by decide⟩,⟨1466209, by decide⟩,⟨1466325, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_28577_1466326 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 28577 ⟨1466326, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 28577
    ⟨1466326, by decide⟩ (by decide) (![⟨1466101, by decide⟩,⟨1192826, by decide⟩,⟨1466209, by decide⟩,⟨1466325, by decide⟩]) unmarked_context_10_28577_1466326 node_context_10_28577_1466326
  intro a
  fin_cases a
  · exact context_11_114308_1466101
  · exact context_11_114309_1192826
  · exact context_11_114310_1466209
  · exact context_11_114311_1466325

theorem selected_cut_51045 : selected 9 ⟨1461661, by decide⟩
    (prefixPartial 12 457248) = some ⟨12, 1, 0, 1461661, 457248, 1, 65536⟩ := by
  decide +kernel

theorem context_12_457248_1461661 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 457248 ⟨1461661, by decide⟩ :=
  accepted_of_selected 12 457248 ⟨1461661, by decide⟩ ⟨12, 1, 0, 1461661, 457248, 1, 65536⟩
    (by decide) selected_cut_51045

theorem selected_cut_51046 : selected 9 ⟨1466385, by decide⟩
    (prefixPartial 12 457249) = some ⟨12, 2, 0, 1466385, 457249, 2313, 65536⟩ := by
  decide +kernel

theorem context_12_457249_1466385 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 457249 ⟨1466385, by decide⟩ :=
  accepted_of_selected 12 457249 ⟨1466385, by decide⟩ ⟨12, 2, 0, 1466385, 457249, 2313, 65536⟩
    (by decide) selected_cut_51046

theorem selected_cut_51047 : selected 9 ⟨1466438, by decide⟩
    (prefixPartial 12 457250) = some ⟨12, 2, 0, 1466438, 457250, 2013, 65536⟩ := by
  decide +kernel

theorem context_12_457250_1466438 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 457250 ⟨1466438, by decide⟩ :=
  accepted_of_selected 12 457250 ⟨1466438, by decide⟩ ⟨12, 2, 0, 1466438, 457250, 2013, 65536⟩
    (by decide) selected_cut_51047

theorem selected_cut_51048 : selected 9 ⟨1466493, by decide⟩
    (prefixPartial 12 457251) = some ⟨12, 2, 0, 1466493, 457251, 1861, 65536⟩ := by
  decide +kernel

theorem context_12_457251_1466493 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 457251 ⟨1466493, by decide⟩ :=
  accepted_of_selected 12 457251 ⟨1466493, by decide⟩ ⟨12, 2, 0, 1466493, 457251, 1861, 65536⟩
    (by decide) selected_cut_51048

theorem unmarked_context_11_114312_1466494 : frontier 10 ⟨1466494, by decide⟩
    (prefixCache 11 114312) (prefixPartial 11 114312) = false := by
  decide +kernel

theorem node_context_11_114312_1466494 : EJMOriginalGlobalDAGData.nodes 10 ⟨1466494, by decide⟩ =
    .split (coordinate 11) (![⟨1461661, by decide⟩,⟨1466385, by decide⟩,⟨1466438, by decide⟩,⟨1466493, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_114312_1466494 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 114312 ⟨1466494, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 114312
    ⟨1466494, by decide⟩ (by decide) (![⟨1461661, by decide⟩,⟨1466385, by decide⟩,⟨1466438, by decide⟩,⟨1466493, by decide⟩]) unmarked_context_11_114312_1466494 node_context_11_114312_1466494
  intro a
  fin_cases a
  · exact context_12_457248_1461661
  · exact context_12_457249_1466385
  · exact context_12_457250_1466438
  · exact context_12_457251_1466493

theorem selected_cut_51049 : selected 9 ⟨1466548, by decide⟩
    (prefixPartial 12 457252) = some ⟨12, 2, 0, 1466548, 457252, 1113, 65536⟩ := by
  decide +kernel

theorem context_12_457252_1466548 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 457252 ⟨1466548, by decide⟩ :=
  accepted_of_selected 12 457252 ⟨1466548, by decide⟩ ⟨12, 2, 0, 1466548, 457252, 1113, 65536⟩
    (by decide) selected_cut_51049

theorem selected_cut_51050 : selected 9 ⟨1387565, by decide⟩
    (prefixPartial 12 457253) = some ⟨12, 1, 0, 1387565, 457253, 1, 65536⟩ := by
  decide +kernel

theorem context_12_457253_1387565 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 457253 ⟨1387565, by decide⟩ :=
  accepted_of_selected 12 457253 ⟨1387565, by decide⟩ ⟨12, 1, 0, 1387565, 457253, 1, 65536⟩
    (by decide) selected_cut_51050

theorem selected_cut_51051 : selected 9 ⟨1466612, by decide⟩
    (prefixPartial 12 457254) = some ⟨12, 2, 0, 1466612, 457254, 2081, 65536⟩ := by
  decide +kernel

theorem context_12_457254_1466612 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 457254 ⟨1466612, by decide⟩ :=
  accepted_of_selected 12 457254 ⟨1466612, by decide⟩ ⟨12, 2, 0, 1466612, 457254, 2081, 65536⟩
    (by decide) selected_cut_51051

theorem selected_cut_51052 : selected 9 ⟨1466690, by decide⟩
    (prefixPartial 12 457255) = some ⟨12, 2, 0, 1466690, 457255, 2069, 65536⟩ := by
  decide +kernel

theorem context_12_457255_1466690 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 457255 ⟨1466690, by decide⟩ :=
  accepted_of_selected 12 457255 ⟨1466690, by decide⟩ ⟨12, 2, 0, 1466690, 457255, 2069, 65536⟩
    (by decide) selected_cut_51052

theorem unmarked_context_11_114313_1466691 : frontier 10 ⟨1466691, by decide⟩
    (prefixCache 11 114313) (prefixPartial 11 114313) = false := by
  decide +kernel

theorem node_context_11_114313_1466691 : EJMOriginalGlobalDAGData.nodes 10 ⟨1466691, by decide⟩ =
    .split (coordinate 11) (![⟨1466548, by decide⟩,⟨1387565, by decide⟩,⟨1466612, by decide⟩,⟨1466690, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_114313_1466691 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 114313 ⟨1466691, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 114313
    ⟨1466691, by decide⟩ (by decide) (![⟨1466548, by decide⟩,⟨1387565, by decide⟩,⟨1466612, by decide⟩,⟨1466690, by decide⟩]) unmarked_context_11_114313_1466691 node_context_11_114313_1466691
  intro a
  fin_cases a
  · exact context_12_457252_1466548
  · exact context_12_457253_1387565
  · exact context_12_457254_1466612
  · exact context_12_457255_1466690

theorem selected_cut_51053 : selected 10 ⟨900587, by decide⟩
    (prefixPartial 11 114314) = some ⟨11, 1, 0, 900587, 114314, 1, 262144⟩ := by
  decide +kernel

theorem context_11_114314_900587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 114314 ⟨900587, by decide⟩ :=
  accepted_of_selected 11 114314 ⟨900587, by decide⟩ ⟨11, 1, 0, 900587, 114314, 1, 262144⟩
    (by decide) selected_cut_51053

theorem selected_cut_51054 : selected 10 ⟨1466801, by decide⟩
    (prefixPartial 11 114315) = some ⟨11, 2, 0, 1466801, 114315, 3685, 262144⟩ := by
  decide +kernel

theorem context_11_114315_1466801 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 114315 ⟨1466801, by decide⟩ :=
  accepted_of_selected 11 114315 ⟨1466801, by decide⟩ ⟨11, 2, 0, 1466801, 114315, 3685, 262144⟩
    (by decide) selected_cut_51054

theorem unmarked_context_10_28578_1466802 : frontier 11 ⟨1466802, by decide⟩
    (prefixCache 10 28578) (prefixPartial 10 28578) = false := by
  decide +kernel

theorem node_context_10_28578_1466802 : EJMOriginalGlobalDAGData.nodes 11 ⟨1466802, by decide⟩ =
    .split (coordinate 10) (![⟨1466494, by decide⟩,⟨1466691, by decide⟩,⟨900587, by decide⟩,⟨1466801, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_28578_1466802 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 28578 ⟨1466802, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 28578
    ⟨1466802, by decide⟩ (by decide) (![⟨1466494, by decide⟩,⟨1466691, by decide⟩,⟨900587, by decide⟩,⟨1466801, by decide⟩]) unmarked_context_10_28578_1466802 node_context_10_28578_1466802
  intro a
  fin_cases a
  · exact context_11_114312_1466494
  · exact context_11_114313_1466691
  · exact context_11_114314_900587
  · exact context_11_114315_1466801

theorem selected_cut_51055 : selected 9 ⟨1462014, by decide⟩
    (prefixPartial 12 457264) = some ⟨12, 1, 0, 1462014, 457264, 1, 65536⟩ := by
  decide +kernel

theorem context_12_457264_1462014 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 457264 ⟨1462014, by decide⟩ :=
  accepted_of_selected 12 457264 ⟨1462014, by decide⟩ ⟨12, 1, 0, 1462014, 457264, 1, 65536⟩
    (by decide) selected_cut_51055

theorem selected_cut_51056 : selected 9 ⟨1466851, by decide⟩
    (prefixPartial 12 457265) = some ⟨12, 2, 0, 1466851, 457265, 2057, 65536⟩ := by
  decide +kernel

theorem context_12_457265_1466851 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 457265 ⟨1466851, by decide⟩ :=
  accepted_of_selected 12 457265 ⟨1466851, by decide⟩ ⟨12, 2, 0, 1466851, 457265, 2057, 65536⟩
    (by decide) selected_cut_51056

theorem selected_cut_51057 : selected 9 ⟨1466899, by decide⟩
    (prefixPartial 12 457266) = some ⟨12, 2, 0, 1466899, 457266, 1781, 65536⟩ := by
  decide +kernel

theorem context_12_457266_1466899 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 457266 ⟨1466899, by decide⟩ :=
  accepted_of_selected 12 457266 ⟨1466899, by decide⟩ ⟨12, 2, 0, 1466899, 457266, 1781, 65536⟩
    (by decide) selected_cut_51057

theorem selected_cut_51058 : selected 9 ⟨1466939, by decide⟩
    (prefixPartial 12 457267) = some ⟨12, 2, 0, 1466939, 457267, 1497, 65536⟩ := by
  decide +kernel

theorem context_12_457267_1466939 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 457267 ⟨1466939, by decide⟩ :=
  accepted_of_selected 12 457267 ⟨1466939, by decide⟩ ⟨12, 2, 0, 1466939, 457267, 1497, 65536⟩
    (by decide) selected_cut_51058

theorem unmarked_context_11_114316_1466940 : frontier 10 ⟨1466940, by decide⟩
    (prefixCache 11 114316) (prefixPartial 11 114316) = false := by
  decide +kernel

theorem node_context_11_114316_1466940 : EJMOriginalGlobalDAGData.nodes 10 ⟨1466940, by decide⟩ =
    .split (coordinate 11) (![⟨1462014, by decide⟩,⟨1466851, by decide⟩,⟨1466899, by decide⟩,⟨1466939, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_114316_1466940 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 114316 ⟨1466940, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 114316
    ⟨1466940, by decide⟩ (by decide) (![⟨1462014, by decide⟩,⟨1466851, by decide⟩,⟨1466899, by decide⟩,⟨1466939, by decide⟩]) unmarked_context_11_114316_1466940 node_context_11_114316_1466940
  intro a
  fin_cases a
  · exact context_12_457264_1462014
  · exact context_12_457265_1466851
  · exact context_12_457266_1466899
  · exact context_12_457267_1466939

theorem selected_cut_51059 : selected 10 ⟨1467039, by decide⟩
    (prefixPartial 11 114317) = some ⟨11, 2, 0, 1467039, 114317, 3545, 262144⟩ := by
  decide +kernel

theorem context_11_114317_1467039 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 114317 ⟨1467039, by decide⟩ :=
  accepted_of_selected 11 114317 ⟨1467039, by decide⟩ ⟨11, 2, 0, 1467039, 114317, 3545, 262144⟩
    (by decide) selected_cut_51059

theorem selected_cut_51060 : selected 10 ⟨1467125, by decide⟩
    (prefixPartial 11 114318) = some ⟨11, 2, 0, 1467125, 114318, 3041, 262144⟩ := by
  decide +kernel

theorem context_11_114318_1467125 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 114318 ⟨1467125, by decide⟩ :=
  accepted_of_selected 11 114318 ⟨1467125, by decide⟩ ⟨11, 2, 0, 1467125, 114318, 3041, 262144⟩
    (by decide) selected_cut_51060

theorem selected_cut_51061 : selected 10 ⟨1467126, by decide⟩
    (prefixPartial 11 114319) = some ⟨11, 2, 0, 1467126, 114319, 5, 262144⟩ := by
  decide +kernel

theorem context_11_114319_1467126 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 114319 ⟨1467126, by decide⟩ :=
  accepted_of_selected 11 114319 ⟨1467126, by decide⟩ ⟨11, 2, 0, 1467126, 114319, 5, 262144⟩
    (by decide) selected_cut_51061

theorem unmarked_context_10_28579_1467127 : frontier 11 ⟨1467127, by decide⟩
    (prefixCache 10 28579) (prefixPartial 10 28579) = false := by
  decide +kernel

theorem node_context_10_28579_1467127 : EJMOriginalGlobalDAGData.nodes 11 ⟨1467127, by decide⟩ =
    .split (coordinate 10) (![⟨1466940, by decide⟩,⟨1467039, by decide⟩,⟨1467125, by decide⟩,⟨1467126, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_28579_1467127 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 28579 ⟨1467127, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 28579
    ⟨1467127, by decide⟩ (by decide) (![⟨1466940, by decide⟩,⟨1467039, by decide⟩,⟨1467125, by decide⟩,⟨1467126, by decide⟩]) unmarked_context_10_28579_1467127 node_context_10_28579_1467127
  intro a
  fin_cases a
  · exact context_11_114316_1466940
  · exact context_11_114317_1467039
  · exact context_11_114318_1467125
  · exact context_11_114319_1467126

theorem unmarked_context_9_7144_1467128 : frontier 12 ⟨1467128, by decide⟩
    (prefixCache 9 7144) (prefixPartial 9 7144) = false := by
  decide +kernel

theorem node_context_9_7144_1467128 : EJMOriginalGlobalDAGData.nodes 12 ⟨1467128, by decide⟩ =
    .split (coordinate 9) (![⟨1465887, by decide⟩,⟨1466326, by decide⟩,⟨1466802, by decide⟩,⟨1467127, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_7144_1467128 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 7144 ⟨1467128, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 7144
    ⟨1467128, by decide⟩ (by decide) (![⟨1465887, by decide⟩,⟨1466326, by decide⟩,⟨1466802, by decide⟩,⟨1467127, by decide⟩]) unmarked_context_9_7144_1467128 node_context_9_7144_1467128
  intro a
  fin_cases a
  · exact context_10_28576_1465887
  · exact context_10_28577_1466326
  · exact context_10_28578_1466802
  · exact context_10_28579_1467127

theorem selected_cut_51062 : selected 10 ⟨1467129, by decide⟩
    (prefixPartial 11 114320) = some ⟨11, 1, 0, 1467129, 114320, 1, 262144⟩ := by
  decide +kernel

theorem context_11_114320_1467129 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 114320 ⟨1467129, by decide⟩ :=
  accepted_of_selected 11 114320 ⟨1467129, by decide⟩ ⟨11, 1, 0, 1467129, 114320, 1, 262144⟩
    (by decide) selected_cut_51062

theorem selected_cut_51063 : selected 9 ⟨1467173, by decide⟩
    (prefixPartial 12 457284) = some ⟨12, 2, 0, 1467173, 457284, 1853, 65536⟩ := by
  decide +kernel

theorem context_12_457284_1467173 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 457284 ⟨1467173, by decide⟩ :=
  accepted_of_selected 12 457284 ⟨1467173, by decide⟩ ⟨12, 2, 0, 1467173, 457284, 1853, 65536⟩
    (by decide) selected_cut_51063

theorem selected_cut_51064 : selected 9 ⟨1467174, by decide⟩
    (prefixPartial 12 457285) = some ⟨12, 1, 0, 1467174, 457285, 1, 65536⟩ := by
  decide +kernel

theorem context_12_457285_1467174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 457285 ⟨1467174, by decide⟩ :=
  accepted_of_selected 12 457285 ⟨1467174, by decide⟩ ⟨12, 1, 0, 1467174, 457285, 1, 65536⟩
    (by decide) selected_cut_51064

theorem selected_cut_51065 : selected 9 ⟨1467211, by decide⟩
    (prefixPartial 12 457286) = some ⟨12, 2, 0, 1467211, 457286, 1605, 65536⟩ := by
  decide +kernel

theorem context_12_457286_1467211 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 457286 ⟨1467211, by decide⟩ :=
  accepted_of_selected 12 457286 ⟨1467211, by decide⟩ ⟨12, 2, 0, 1467211, 457286, 1605, 65536⟩
    (by decide) selected_cut_51065

theorem selected_cut_51066 : selected 9 ⟨1467245, by decide⟩
    (prefixPartial 12 457287) = some ⟨12, 2, 0, 1467245, 457287, 1573, 65536⟩ := by
  decide +kernel

theorem context_12_457287_1467245 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 457287 ⟨1467245, by decide⟩ :=
  accepted_of_selected 12 457287 ⟨1467245, by decide⟩ ⟨12, 2, 0, 1467245, 457287, 1573, 65536⟩
    (by decide) selected_cut_51066

theorem unmarked_context_11_114321_1467246 : frontier 10 ⟨1467246, by decide⟩
    (prefixCache 11 114321) (prefixPartial 11 114321) = false := by
  decide +kernel

theorem node_context_11_114321_1467246 : EJMOriginalGlobalDAGData.nodes 10 ⟨1467246, by decide⟩ =
    .split (coordinate 11) (![⟨1467173, by decide⟩,⟨1467174, by decide⟩,⟨1467211, by decide⟩,⟨1467245, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_114321_1467246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 114321 ⟨1467246, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 114321
    ⟨1467246, by decide⟩ (by decide) (![⟨1467173, by decide⟩,⟨1467174, by decide⟩,⟨1467211, by decide⟩,⟨1467245, by decide⟩]) unmarked_context_11_114321_1467246 node_context_11_114321_1467246
  intro a
  fin_cases a
  · exact context_12_457284_1467173
  · exact context_12_457285_1467174
  · exact context_12_457286_1467211
  · exact context_12_457287_1467245

theorem selected_cut_51067 : selected 10 ⟨1467327, by decide⟩
    (prefixPartial 11 114322) = some ⟨11, 2, 0, 1467327, 114322, 2729, 262144⟩ := by
  decide +kernel

theorem context_11_114322_1467327 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 114322 ⟨1467327, by decide⟩ :=
  accepted_of_selected 11 114322 ⟨1467327, by decide⟩ ⟨11, 2, 0, 1467327, 114322, 2729, 262144⟩
    (by decide) selected_cut_51067

theorem selected_cut_51068 : selected 10 ⟨1467382, by decide⟩
    (prefixPartial 11 114323) = some ⟨11, 2, 0, 1467382, 114323, 2897, 262144⟩ := by
  decide +kernel

theorem context_11_114323_1467382 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 114323 ⟨1467382, by decide⟩ :=
  accepted_of_selected 11 114323 ⟨1467382, by decide⟩ ⟨11, 2, 0, 1467382, 114323, 2897, 262144⟩
    (by decide) selected_cut_51068

theorem unmarked_context_10_28580_1467383 : frontier 11 ⟨1467383, by decide⟩
    (prefixCache 10 28580) (prefixPartial 10 28580) = false := by
  decide +kernel

theorem node_context_10_28580_1467383 : EJMOriginalGlobalDAGData.nodes 11 ⟨1467383, by decide⟩ =
    .split (coordinate 10) (![⟨1467129, by decide⟩,⟨1467246, by decide⟩,⟨1467327, by decide⟩,⟨1467382, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_28580_1467383 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 28580 ⟨1467383, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 28580
    ⟨1467383, by decide⟩ (by decide) (![⟨1467129, by decide⟩,⟨1467246, by decide⟩,⟨1467327, by decide⟩,⟨1467382, by decide⟩]) unmarked_context_10_28580_1467383 node_context_10_28580_1467383
  intro a
  fin_cases a
  · exact context_11_114320_1467129
  · exact context_11_114321_1467246
  · exact context_11_114322_1467327
  · exact context_11_114323_1467382

theorem selected_cut_51069 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 28581) = some ⟨10, 1, 0, 893098, 28581, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_28581_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 28581 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 28581 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 28581, 1, 1048576⟩
    (by decide) selected_cut_51069

theorem selected_cut_51070 : selected 10 ⟨1467444, by decide⟩
    (prefixPartial 11 114328) = some ⟨11, 2, 0, 1467444, 114328, 2317, 262144⟩ := by
  decide +kernel

theorem context_11_114328_1467444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 114328 ⟨1467444, by decide⟩ :=
  accepted_of_selected 11 114328 ⟨1467444, by decide⟩ ⟨11, 2, 0, 1467444, 114328, 2317, 262144⟩
    (by decide) selected_cut_51070

theorem selected_cut_51071 : selected 10 ⟨1467530, by decide⟩
    (prefixPartial 11 114329) = some ⟨11, 2, 0, 1467530, 114329, 3521, 262144⟩ := by
  decide +kernel

theorem context_11_114329_1467530 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 114329 ⟨1467530, by decide⟩ :=
  accepted_of_selected 11 114329 ⟨1467530, by decide⟩ ⟨11, 2, 0, 1467530, 114329, 3521, 262144⟩
    (by decide) selected_cut_51071

theorem selected_cut_51072 : selected 10 ⟨900587, by decide⟩
    (prefixPartial 11 114330) = some ⟨11, 1, 0, 900587, 114330, 1, 262144⟩ := by
  decide +kernel

theorem context_11_114330_900587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 114330 ⟨900587, by decide⟩ :=
  accepted_of_selected 11 114330 ⟨900587, by decide⟩ ⟨11, 1, 0, 900587, 114330, 1, 262144⟩
    (by decide) selected_cut_51072

theorem selected_cut_51073 : selected 10 ⟨1467580, by decide⟩
    (prefixPartial 11 114331) = some ⟨11, 2, 0, 1467580, 114331, 1981, 262144⟩ := by
  decide +kernel

theorem context_11_114331_1467580 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 114331 ⟨1467580, by decide⟩ :=
  accepted_of_selected 11 114331 ⟨1467580, by decide⟩ ⟨11, 2, 0, 1467580, 114331, 1981, 262144⟩
    (by decide) selected_cut_51073

theorem unmarked_context_10_28582_1467581 : frontier 11 ⟨1467581, by decide⟩
    (prefixCache 10 28582) (prefixPartial 10 28582) = false := by
  decide +kernel

theorem node_context_10_28582_1467581 : EJMOriginalGlobalDAGData.nodes 11 ⟨1467581, by decide⟩ =
    .split (coordinate 10) (![⟨1467444, by decide⟩,⟨1467530, by decide⟩,⟨900587, by decide⟩,⟨1467580, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_28582_1467581 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 28582 ⟨1467581, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 28582
    ⟨1467581, by decide⟩ (by decide) (![⟨1467444, by decide⟩,⟨1467530, by decide⟩,⟨900587, by decide⟩,⟨1467580, by decide⟩]) unmarked_context_10_28582_1467581 node_context_10_28582_1467581
  intro a
  fin_cases a
  · exact context_11_114328_1467444
  · exact context_11_114329_1467530
  · exact context_11_114330_900587
  · exact context_11_114331_1467580

theorem selected_cut_51074 : selected 10 ⟨1467623, by decide⟩
    (prefixPartial 11 114332) = some ⟨11, 2, 0, 1467623, 114332, 1785, 262144⟩ := by
  decide +kernel

theorem context_11_114332_1467623 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 114332 ⟨1467623, by decide⟩ :=
  accepted_of_selected 11 114332 ⟨1467623, by decide⟩ ⟨11, 2, 0, 1467623, 114332, 1785, 262144⟩
    (by decide) selected_cut_51074

theorem selected_cut_51075 : selected 10 ⟨1467688, by decide⟩
    (prefixPartial 11 114333) = some ⟨11, 2, 0, 1467688, 114333, 3005, 262144⟩ := by
  decide +kernel

theorem context_11_114333_1467688 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 114333 ⟨1467688, by decide⟩ :=
  accepted_of_selected 11 114333 ⟨1467688, by decide⟩ ⟨11, 2, 0, 1467688, 114333, 3005, 262144⟩
    (by decide) selected_cut_51075

theorem selected_cut_51076 : selected 10 ⟨1467734, by decide⟩
    (prefixPartial 11 114334) = some ⟨11, 2, 0, 1467734, 114334, 1593, 262144⟩ := by
  decide +kernel

theorem context_11_114334_1467734 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 114334 ⟨1467734, by decide⟩ :=
  accepted_of_selected 11 114334 ⟨1467734, by decide⟩ ⟨11, 2, 0, 1467734, 114334, 1593, 262144⟩
    (by decide) selected_cut_51076

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
