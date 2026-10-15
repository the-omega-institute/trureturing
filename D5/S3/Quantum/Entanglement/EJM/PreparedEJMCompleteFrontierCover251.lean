/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover250
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem unmarked_context_11_19220_608749 : frontier 10 ⟨608749, by decide⟩
    (prefixCache 11 19220) (prefixPartial 11 19220) = false := by
  decide +kernel

theorem node_context_11_19220_608749 : EJMOriginalGlobalDAGData.nodes 10 ⟨608749, by decide⟩ =
    .split (coordinate 11) (![⟨266170, by decide⟩,⟨608648, by decide⟩,⟨608699, by decide⟩,⟨608748, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19220_608749 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19220 ⟨608749, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19220
    ⟨608749, by decide⟩ (by decide) (![⟨266170, by decide⟩,⟨608648, by decide⟩,⟨608699, by decide⟩,⟨608748, by decide⟩]) unmarked_context_11_19220_608749 node_context_11_19220_608749
  intro a
  fin_cases a
  · exact context_12_76880_266170
  · exact context_12_76881_608648
  · exact context_12_76882_608699
  · exact context_12_76883_608748

theorem selected_cut_24099 : selected 9 ⟨608798, by decide⟩
    (prefixPartial 12 76884) = some ⟨12, 2, 0, 608798, 76884, 3849, 65536⟩ := by
  decide +kernel

theorem context_12_76884_608798 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76884 ⟨608798, by decide⟩ :=
  accepted_of_selected 12 76884 ⟨608798, by decide⟩ ⟨12, 2, 0, 608798, 76884, 3849, 65536⟩
    (by decide) selected_cut_24099

theorem selected_cut_24100 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 307540) = some ⟨13, 1, 0, 3444, 307540, 1, 16384⟩ := by
  decide +kernel

theorem context_13_307540_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307540 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 307540 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 307540, 1, 16384⟩
    (by decide) selected_cut_24100

theorem selected_cut_24101 : selected 8 ⟨608815, by decide⟩
    (prefixPartial 13 307541) = some ⟨13, 2, 0, 608815, 307541, 1529, 16384⟩ := by
  decide +kernel

theorem context_13_307541_608815 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307541 ⟨608815, by decide⟩ :=
  accepted_of_selected 13 307541 ⟨608815, by decide⟩ ⟨13, 2, 0, 608815, 307541, 1529, 16384⟩
    (by decide) selected_cut_24101

theorem selected_cut_24102 : selected 8 ⟨608852, by decide⟩
    (prefixPartial 13 307542) = some ⟨13, 2, 0, 608852, 307542, 2033, 16384⟩ := by
  decide +kernel

theorem context_13_307542_608852 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307542 ⟨608852, by decide⟩ :=
  accepted_of_selected 13 307542 ⟨608852, by decide⟩ ⟨13, 2, 0, 608852, 307542, 2033, 16384⟩
    (by decide) selected_cut_24102

theorem selected_cut_24103 : selected 8 ⟨608862, by decide⟩
    (prefixPartial 13 307543) = some ⟨13, 2, 0, 608862, 307543, 697, 16384⟩ := by
  decide +kernel

theorem context_13_307543_608862 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307543 ⟨608862, by decide⟩ :=
  accepted_of_selected 13 307543 ⟨608862, by decide⟩ ⟨13, 2, 0, 608862, 307543, 697, 16384⟩
    (by decide) selected_cut_24103

theorem unmarked_context_12_76885_608863 : frontier 9 ⟨608863, by decide⟩
    (prefixCache 12 76885) (prefixPartial 12 76885) = false := by
  decide +kernel

theorem node_context_12_76885_608863 : EJMOriginalGlobalDAGData.nodes 9 ⟨608863, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨608815, by decide⟩,⟨608852, by decide⟩,⟨608862, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76885_608863 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76885 ⟨608863, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76885
    ⟨608863, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨608815, by decide⟩,⟨608852, by decide⟩,⟨608862, by decide⟩]) unmarked_context_12_76885_608863 node_context_12_76885_608863
  intro a
  fin_cases a
  · exact context_13_307540_3444
  · exact context_13_307541_608815
  · exact context_13_307542_608852
  · exact context_13_307543_608862

theorem selected_cut_24104 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 307544) = some ⟨13, 1, 0, 3444, 307544, 1, 16384⟩ := by
  decide +kernel

theorem context_13_307544_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307544 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 307544 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 307544, 1, 16384⟩
    (by decide) selected_cut_24104

theorem selected_cut_24105 : selected 8 ⟨608889, by decide⟩
    (prefixPartial 13 307545) = some ⟨13, 2, 0, 608889, 307545, 1761, 16384⟩ := by
  decide +kernel

theorem context_13_307545_608889 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307545 ⟨608889, by decide⟩ :=
  accepted_of_selected 13 307545 ⟨608889, by decide⟩ ⟨13, 2, 0, 608889, 307545, 1761, 16384⟩
    (by decide) selected_cut_24105

theorem selected_cut_24106 : selected 8 ⟨608917, by decide⟩
    (prefixPartial 13 307546) = some ⟨13, 2, 0, 608917, 307546, 1929, 16384⟩ := by
  decide +kernel

theorem context_13_307546_608917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307546 ⟨608917, by decide⟩ :=
  accepted_of_selected 13 307546 ⟨608917, by decide⟩ ⟨13, 2, 0, 608917, 307546, 1929, 16384⟩
    (by decide) selected_cut_24106

theorem selected_cut_24107 : selected 8 ⟨608925, by decide⟩
    (prefixPartial 13 307547) = some ⟨13, 2, 0, 608925, 307547, 909, 16384⟩ := by
  decide +kernel

theorem context_13_307547_608925 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307547 ⟨608925, by decide⟩ :=
  accepted_of_selected 13 307547 ⟨608925, by decide⟩ ⟨13, 2, 0, 608925, 307547, 909, 16384⟩
    (by decide) selected_cut_24107

theorem unmarked_context_12_76886_608926 : frontier 9 ⟨608926, by decide⟩
    (prefixCache 12 76886) (prefixPartial 12 76886) = false := by
  decide +kernel

theorem node_context_12_76886_608926 : EJMOriginalGlobalDAGData.nodes 9 ⟨608926, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨608889, by decide⟩,⟨608917, by decide⟩,⟨608925, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76886_608926 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76886 ⟨608926, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76886
    ⟨608926, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨608889, by decide⟩,⟨608917, by decide⟩,⟨608925, by decide⟩]) unmarked_context_12_76886_608926 node_context_12_76886_608926
  intro a
  fin_cases a
  · exact context_13_307544_3444
  · exact context_13_307545_608889
  · exact context_13_307546_608917
  · exact context_13_307547_608925

theorem selected_cut_24108 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 307548) = some ⟨13, 1, 0, 3444, 307548, 1, 16384⟩ := by
  decide +kernel

theorem context_13_307548_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307548 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 307548 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 307548, 1, 16384⟩
    (by decide) selected_cut_24108

theorem selected_cut_24109 : selected 8 ⟨608950, by decide⟩
    (prefixPartial 13 307549) = some ⟨13, 2, 0, 608950, 307549, 1785, 16384⟩ := by
  decide +kernel

theorem context_13_307549_608950 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307549 ⟨608950, by decide⟩ :=
  accepted_of_selected 13 307549 ⟨608950, by decide⟩ ⟨13, 2, 0, 608950, 307549, 1785, 16384⟩
    (by decide) selected_cut_24109

theorem selected_cut_24110 : selected 8 ⟨608988, by decide⟩
    (prefixPartial 13 307550) = some ⟨13, 2, 0, 608988, 307550, 2065, 16384⟩ := by
  decide +kernel

theorem context_13_307550_608988 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307550 ⟨608988, by decide⟩ :=
  accepted_of_selected 13 307550 ⟨608988, by decide⟩ ⟨13, 2, 0, 608988, 307550, 2065, 16384⟩
    (by decide) selected_cut_24110

theorem selected_cut_24111 : selected 8 ⟨608998, by decide⟩
    (prefixPartial 13 307551) = some ⟨13, 2, 0, 608998, 307551, 869, 16384⟩ := by
  decide +kernel

theorem context_13_307551_608998 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307551 ⟨608998, by decide⟩ :=
  accepted_of_selected 13 307551 ⟨608998, by decide⟩ ⟨13, 2, 0, 608998, 307551, 869, 16384⟩
    (by decide) selected_cut_24111

theorem unmarked_context_12_76887_608999 : frontier 9 ⟨608999, by decide⟩
    (prefixCache 12 76887) (prefixPartial 12 76887) = false := by
  decide +kernel

theorem node_context_12_76887_608999 : EJMOriginalGlobalDAGData.nodes 9 ⟨608999, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨608950, by decide⟩,⟨608988, by decide⟩,⟨608998, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76887_608999 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76887 ⟨608999, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76887
    ⟨608999, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨608950, by decide⟩,⟨608988, by decide⟩,⟨608998, by decide⟩]) unmarked_context_12_76887_608999 node_context_12_76887_608999
  intro a
  fin_cases a
  · exact context_13_307548_3444
  · exact context_13_307549_608950
  · exact context_13_307550_608988
  · exact context_13_307551_608998

theorem unmarked_context_11_19221_609000 : frontier 10 ⟨609000, by decide⟩
    (prefixCache 11 19221) (prefixPartial 11 19221) = false := by
  decide +kernel

theorem node_context_11_19221_609000 : EJMOriginalGlobalDAGData.nodes 10 ⟨609000, by decide⟩ =
    .split (coordinate 11) (![⟨608798, by decide⟩,⟨608863, by decide⟩,⟨608926, by decide⟩,⟨608999, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19221_609000 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19221 ⟨609000, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19221
    ⟨609000, by decide⟩ (by decide) (![⟨608798, by decide⟩,⟨608863, by decide⟩,⟨608926, by decide⟩,⟨608999, by decide⟩]) unmarked_context_11_19221_609000 node_context_11_19221_609000
  intro a
  fin_cases a
  · exact context_12_76884_608798
  · exact context_12_76885_608863
  · exact context_12_76886_608926
  · exact context_12_76887_608999

theorem selected_cut_24112 : selected 9 ⟨609045, by decide⟩
    (prefixPartial 12 76888) = some ⟨12, 2, 0, 609045, 76888, 3637, 65536⟩ := by
  decide +kernel

theorem context_12_76888_609045 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76888 ⟨609045, by decide⟩ :=
  accepted_of_selected 12 76888 ⟨609045, by decide⟩ ⟨12, 2, 0, 609045, 76888, 3637, 65536⟩
    (by decide) selected_cut_24112

theorem selected_cut_24113 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 307556) = some ⟨13, 1, 0, 3444, 307556, 1, 16384⟩ := by
  decide +kernel

theorem context_13_307556_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307556 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 307556 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 307556, 1, 16384⟩
    (by decide) selected_cut_24113

theorem selected_cut_24114 : selected 8 ⟨609063, by decide⟩
    (prefixPartial 13 307557) = some ⟨13, 2, 0, 609063, 307557, 1321, 16384⟩ := by
  decide +kernel

theorem context_13_307557_609063 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307557 ⟨609063, by decide⟩ :=
  accepted_of_selected 13 307557 ⟨609063, by decide⟩ ⟨13, 2, 0, 609063, 307557, 1321, 16384⟩
    (by decide) selected_cut_24114

theorem selected_cut_24115 : selected 8 ⟨609105, by decide⟩
    (prefixPartial 13 307558) = some ⟨13, 2, 0, 609105, 307558, 2053, 16384⟩ := by
  decide +kernel

theorem context_13_307558_609105 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307558 ⟨609105, by decide⟩ :=
  accepted_of_selected 13 307558 ⟨609105, by decide⟩ ⟨13, 2, 0, 609105, 307558, 2053, 16384⟩
    (by decide) selected_cut_24115

theorem selected_cut_24116 : selected 8 ⟨609120, by decide⟩
    (prefixPartial 13 307559) = some ⟨13, 2, 0, 609120, 307559, 845, 16384⟩ := by
  decide +kernel

theorem context_13_307559_609120 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307559 ⟨609120, by decide⟩ :=
  accepted_of_selected 13 307559 ⟨609120, by decide⟩ ⟨13, 2, 0, 609120, 307559, 845, 16384⟩
    (by decide) selected_cut_24116

theorem unmarked_context_12_76889_609121 : frontier 9 ⟨609121, by decide⟩
    (prefixCache 12 76889) (prefixPartial 12 76889) = false := by
  decide +kernel

theorem node_context_12_76889_609121 : EJMOriginalGlobalDAGData.nodes 9 ⟨609121, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨609063, by decide⟩,⟨609105, by decide⟩,⟨609120, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76889_609121 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76889 ⟨609121, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76889
    ⟨609121, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨609063, by decide⟩,⟨609105, by decide⟩,⟨609120, by decide⟩]) unmarked_context_12_76889_609121 node_context_12_76889_609121
  intro a
  fin_cases a
  · exact context_13_307556_3444
  · exact context_13_307557_609063
  · exact context_13_307558_609105
  · exact context_13_307559_609120

theorem selected_cut_24117 : selected 9 ⟨609173, by decide⟩
    (prefixPartial 12 76890) = some ⟨12, 2, 0, 609173, 76890, 3949, 65536⟩ := by
  decide +kernel

theorem context_12_76890_609173 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76890 ⟨609173, by decide⟩ :=
  accepted_of_selected 12 76890 ⟨609173, by decide⟩ ⟨12, 2, 0, 609173, 76890, 3949, 65536⟩
    (by decide) selected_cut_24117

theorem selected_cut_24118 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 307564) = some ⟨13, 1, 0, 3444, 307564, 1, 16384⟩ := by
  decide +kernel

theorem context_13_307564_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307564 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 307564 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 307564, 1, 16384⟩
    (by decide) selected_cut_24118

theorem selected_cut_24119 : selected 8 ⟨609195, by decide⟩
    (prefixPartial 13 307565) = some ⟨13, 2, 0, 609195, 307565, 1617, 16384⟩ := by
  decide +kernel

theorem context_13_307565_609195 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307565 ⟨609195, by decide⟩ :=
  accepted_of_selected 13 307565 ⟨609195, by decide⟩ ⟨13, 2, 0, 609195, 307565, 1617, 16384⟩
    (by decide) selected_cut_24119

theorem selected_cut_24120 : selected 8 ⟨609223, by decide⟩
    (prefixPartial 13 307566) = some ⟨13, 2, 0, 609223, 307566, 1869, 16384⟩ := by
  decide +kernel

theorem context_13_307566_609223 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307566 ⟨609223, by decide⟩ :=
  accepted_of_selected 13 307566 ⟨609223, by decide⟩ ⟨13, 2, 0, 609223, 307566, 1869, 16384⟩
    (by decide) selected_cut_24120

theorem selected_cut_24121 : selected 8 ⟨609236, by decide⟩
    (prefixPartial 13 307567) = some ⟨13, 2, 0, 609236, 307567, 857, 16384⟩ := by
  decide +kernel

theorem context_13_307567_609236 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307567 ⟨609236, by decide⟩ :=
  accepted_of_selected 13 307567 ⟨609236, by decide⟩ ⟨13, 2, 0, 609236, 307567, 857, 16384⟩
    (by decide) selected_cut_24121

theorem unmarked_context_12_76891_609237 : frontier 9 ⟨609237, by decide⟩
    (prefixCache 12 76891) (prefixPartial 12 76891) = false := by
  decide +kernel

theorem node_context_12_76891_609237 : EJMOriginalGlobalDAGData.nodes 9 ⟨609237, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨609195, by decide⟩,⟨609223, by decide⟩,⟨609236, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76891_609237 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76891 ⟨609237, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76891
    ⟨609237, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨609195, by decide⟩,⟨609223, by decide⟩,⟨609236, by decide⟩]) unmarked_context_12_76891_609237 node_context_12_76891_609237
  intro a
  fin_cases a
  · exact context_13_307564_3444
  · exact context_13_307565_609195
  · exact context_13_307566_609223
  · exact context_13_307567_609236

theorem unmarked_context_11_19222_609238 : frontier 10 ⟨609238, by decide⟩
    (prefixCache 11 19222) (prefixPartial 11 19222) = false := by
  decide +kernel

theorem node_context_11_19222_609238 : EJMOriginalGlobalDAGData.nodes 10 ⟨609238, by decide⟩ =
    .split (coordinate 11) (![⟨609045, by decide⟩,⟨609121, by decide⟩,⟨609173, by decide⟩,⟨609237, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19222_609238 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19222 ⟨609238, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19222
    ⟨609238, by decide⟩ (by decide) (![⟨609045, by decide⟩,⟨609121, by decide⟩,⟨609173, by decide⟩,⟨609237, by decide⟩]) unmarked_context_11_19222_609238 node_context_11_19222_609238
  intro a
  fin_cases a
  · exact context_12_76888_609045
  · exact context_12_76889_609121
  · exact context_12_76890_609173
  · exact context_12_76891_609237

theorem selected_cut_24122 : selected 9 ⟨609280, by decide⟩
    (prefixPartial 12 76892) = some ⟨12, 2, 0, 609280, 76892, 3281, 65536⟩ := by
  decide +kernel

theorem context_12_76892_609280 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76892 ⟨609280, by decide⟩ :=
  accepted_of_selected 12 76892 ⟨609280, by decide⟩ ⟨12, 2, 0, 609280, 76892, 3281, 65536⟩
    (by decide) selected_cut_24122

theorem selected_cut_24123 : selected 9 ⟨609341, by decide⟩
    (prefixPartial 12 76893) = some ⟨12, 2, 0, 609341, 76893, 3973, 65536⟩ := by
  decide +kernel

theorem context_12_76893_609341 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76893 ⟨609341, by decide⟩ :=
  accepted_of_selected 12 76893 ⟨609341, by decide⟩ ⟨12, 2, 0, 609341, 76893, 3973, 65536⟩
    (by decide) selected_cut_24123

theorem selected_cut_24124 : selected 9 ⟨609394, by decide⟩
    (prefixPartial 12 76894) = some ⟨12, 2, 0, 609394, 76894, 4049, 65536⟩ := by
  decide +kernel

theorem context_12_76894_609394 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76894 ⟨609394, by decide⟩ :=
  accepted_of_selected 12 76894 ⟨609394, by decide⟩ ⟨12, 2, 0, 609394, 76894, 4049, 65536⟩
    (by decide) selected_cut_24124

theorem selected_cut_24125 : selected 9 ⟨609436, by decide⟩
    (prefixPartial 12 76895) = some ⟨12, 2, 0, 609436, 76895, 4025, 65536⟩ := by
  decide +kernel

theorem context_12_76895_609436 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76895 ⟨609436, by decide⟩ :=
  accepted_of_selected 12 76895 ⟨609436, by decide⟩ ⟨12, 2, 0, 609436, 76895, 4025, 65536⟩
    (by decide) selected_cut_24125

theorem unmarked_context_11_19223_609437 : frontier 10 ⟨609437, by decide⟩
    (prefixCache 11 19223) (prefixPartial 11 19223) = false := by
  decide +kernel

theorem node_context_11_19223_609437 : EJMOriginalGlobalDAGData.nodes 10 ⟨609437, by decide⟩ =
    .split (coordinate 11) (![⟨609280, by decide⟩,⟨609341, by decide⟩,⟨609394, by decide⟩,⟨609436, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19223_609437 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19223 ⟨609437, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19223
    ⟨609437, by decide⟩ (by decide) (![⟨609280, by decide⟩,⟨609341, by decide⟩,⟨609394, by decide⟩,⟨609436, by decide⟩]) unmarked_context_11_19223_609437 node_context_11_19223_609437
  intro a
  fin_cases a
  · exact context_12_76892_609280
  · exact context_12_76893_609341
  · exact context_12_76894_609394
  · exact context_12_76895_609436

theorem unmarked_context_10_4805_609438 : frontier 11 ⟨609438, by decide⟩
    (prefixCache 10 4805) (prefixPartial 10 4805) = false := by
  decide +kernel

theorem node_context_10_4805_609438 : EJMOriginalGlobalDAGData.nodes 11 ⟨609438, by decide⟩ =
    .split (coordinate 10) (![⟨608749, by decide⟩,⟨609000, by decide⟩,⟨609238, by decide⟩,⟨609437, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4805_609438 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4805 ⟨609438, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4805
    ⟨609438, by decide⟩ (by decide) (![⟨608749, by decide⟩,⟨609000, by decide⟩,⟨609238, by decide⟩,⟨609437, by decide⟩]) unmarked_context_10_4805_609438 node_context_10_4805_609438
  intro a
  fin_cases a
  · exact context_11_19220_608749
  · exact context_11_19221_609000
  · exact context_11_19222_609238
  · exact context_11_19223_609437

theorem selected_cut_24126 : selected 9 ⟨609549, by decide⟩
    (prefixPartial 12 76896) = some ⟨12, 2, 0, 609549, 76896, 2361, 65536⟩ := by
  decide +kernel

theorem context_12_76896_609549 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76896 ⟨609549, by decide⟩ :=
  accepted_of_selected 12 76896 ⟨609549, by decide⟩ ⟨12, 2, 0, 609549, 76896, 2361, 65536⟩
    (by decide) selected_cut_24126

theorem selected_cut_24127 : selected 9 ⟨609595, by decide⟩
    (prefixPartial 12 76897) = some ⟨12, 2, 0, 609595, 76897, 3401, 65536⟩ := by
  decide +kernel

theorem context_12_76897_609595 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76897 ⟨609595, by decide⟩ :=
  accepted_of_selected 12 76897 ⟨609595, by decide⟩ ⟨12, 2, 0, 609595, 76897, 3401, 65536⟩
    (by decide) selected_cut_24127

theorem selected_cut_24128 : selected 9 ⟨609636, by decide⟩
    (prefixPartial 12 76898) = some ⟨12, 2, 0, 609636, 76898, 3313, 65536⟩ := by
  decide +kernel

theorem context_12_76898_609636 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76898 ⟨609636, by decide⟩ :=
  accepted_of_selected 12 76898 ⟨609636, by decide⟩ ⟨12, 2, 0, 609636, 76898, 3313, 65536⟩
    (by decide) selected_cut_24128

theorem selected_cut_24129 : selected 9 ⟨609676, by decide⟩
    (prefixPartial 12 76899) = some ⟨12, 2, 0, 609676, 76899, 3613, 65536⟩ := by
  decide +kernel

theorem context_12_76899_609676 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76899 ⟨609676, by decide⟩ :=
  accepted_of_selected 12 76899 ⟨609676, by decide⟩ ⟨12, 2, 0, 609676, 76899, 3613, 65536⟩
    (by decide) selected_cut_24129

theorem unmarked_context_11_19224_609677 : frontier 10 ⟨609677, by decide⟩
    (prefixCache 11 19224) (prefixPartial 11 19224) = false := by
  decide +kernel

theorem node_context_11_19224_609677 : EJMOriginalGlobalDAGData.nodes 10 ⟨609677, by decide⟩ =
    .split (coordinate 11) (![⟨609549, by decide⟩,⟨609595, by decide⟩,⟨609636, by decide⟩,⟨609676, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19224_609677 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19224 ⟨609677, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19224
    ⟨609677, by decide⟩ (by decide) (![⟨609549, by decide⟩,⟨609595, by decide⟩,⟨609636, by decide⟩,⟨609676, by decide⟩]) unmarked_context_11_19224_609677 node_context_11_19224_609677
  intro a
  fin_cases a
  · exact context_12_76896_609549
  · exact context_12_76897_609595
  · exact context_12_76898_609636
  · exact context_12_76899_609676

theorem selected_cut_24130 : selected 9 ⟨609732, by decide⟩
    (prefixPartial 12 76900) = some ⟨12, 2, 0, 609732, 76900, 3437, 65536⟩ := by
  decide +kernel

theorem context_12_76900_609732 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76900 ⟨609732, by decide⟩ :=
  accepted_of_selected 12 76900 ⟨609732, by decide⟩ ⟨12, 2, 0, 609732, 76900, 3437, 65536⟩
    (by decide) selected_cut_24130

theorem selected_cut_24131 : selected 9 ⟨609777, by decide⟩
    (prefixPartial 12 76901) = some ⟨12, 2, 0, 609777, 76901, 3557, 65536⟩ := by
  decide +kernel

theorem context_12_76901_609777 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76901 ⟨609777, by decide⟩ :=
  accepted_of_selected 12 76901 ⟨609777, by decide⟩ ⟨12, 2, 0, 609777, 76901, 3557, 65536⟩
    (by decide) selected_cut_24131

theorem selected_cut_24132 : selected 9 ⟨609844, by decide⟩
    (prefixPartial 12 76902) = some ⟨12, 2, 0, 609844, 76902, 3877, 65536⟩ := by
  decide +kernel

theorem context_12_76902_609844 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76902 ⟨609844, by decide⟩ :=
  accepted_of_selected 12 76902 ⟨609844, by decide⟩ ⟨12, 2, 0, 609844, 76902, 3877, 65536⟩
    (by decide) selected_cut_24132

theorem selected_cut_24133 : selected 9 ⟨609907, by decide⟩
    (prefixPartial 12 76903) = some ⟨12, 2, 0, 609907, 76903, 3949, 65536⟩ := by
  decide +kernel

theorem context_12_76903_609907 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76903 ⟨609907, by decide⟩ :=
  accepted_of_selected 12 76903 ⟨609907, by decide⟩ ⟨12, 2, 0, 609907, 76903, 3949, 65536⟩
    (by decide) selected_cut_24133

theorem unmarked_context_11_19225_609908 : frontier 10 ⟨609908, by decide⟩
    (prefixCache 11 19225) (prefixPartial 11 19225) = false := by
  decide +kernel

theorem node_context_11_19225_609908 : EJMOriginalGlobalDAGData.nodes 10 ⟨609908, by decide⟩ =
    .split (coordinate 11) (![⟨609732, by decide⟩,⟨609777, by decide⟩,⟨609844, by decide⟩,⟨609907, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19225_609908 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19225 ⟨609908, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19225
    ⟨609908, by decide⟩ (by decide) (![⟨609732, by decide⟩,⟨609777, by decide⟩,⟨609844, by decide⟩,⟨609907, by decide⟩]) unmarked_context_11_19225_609908 node_context_11_19225_609908
  intro a
  fin_cases a
  · exact context_12_76900_609732
  · exact context_12_76901_609777
  · exact context_12_76902_609844
  · exact context_12_76903_609907

theorem selected_cut_24134 : selected 9 ⟨609949, by decide⟩
    (prefixPartial 12 76904) = some ⟨12, 2, 0, 609949, 76904, 3149, 65536⟩ := by
  decide +kernel

theorem context_12_76904_609949 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76904 ⟨609949, by decide⟩ :=
  accepted_of_selected 12 76904 ⟨609949, by decide⟩ ⟨12, 2, 0, 609949, 76904, 3149, 65536⟩
    (by decide) selected_cut_24134

theorem selected_cut_24135 : selected 9 ⟨609990, by decide⟩
    (prefixPartial 12 76905) = some ⟨12, 2, 0, 609990, 76905, 3525, 65536⟩ := by
  decide +kernel

theorem context_12_76905_609990 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76905 ⟨609990, by decide⟩ :=
  accepted_of_selected 12 76905 ⟨609990, by decide⟩ ⟨12, 2, 0, 609990, 76905, 3525, 65536⟩
    (by decide) selected_cut_24135

theorem selected_cut_24136 : selected 9 ⟨610039, by decide⟩
    (prefixPartial 12 76906) = some ⟨12, 2, 0, 610039, 76906, 3329, 65536⟩ := by
  decide +kernel

theorem context_12_76906_610039 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76906 ⟨610039, by decide⟩ :=
  accepted_of_selected 12 76906 ⟨610039, by decide⟩ ⟨12, 2, 0, 610039, 76906, 3329, 65536⟩
    (by decide) selected_cut_24136

theorem selected_cut_24137 : selected 9 ⟨610080, by decide⟩
    (prefixPartial 12 76907) = some ⟨12, 2, 0, 610080, 76907, 3581, 65536⟩ := by
  decide +kernel

theorem context_12_76907_610080 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76907 ⟨610080, by decide⟩ :=
  accepted_of_selected 12 76907 ⟨610080, by decide⟩ ⟨12, 2, 0, 610080, 76907, 3581, 65536⟩
    (by decide) selected_cut_24137

theorem unmarked_context_11_19226_610081 : frontier 10 ⟨610081, by decide⟩
    (prefixCache 11 19226) (prefixPartial 11 19226) = false := by
  decide +kernel

theorem node_context_11_19226_610081 : EJMOriginalGlobalDAGData.nodes 10 ⟨610081, by decide⟩ =
    .split (coordinate 11) (![⟨609949, by decide⟩,⟨609990, by decide⟩,⟨610039, by decide⟩,⟨610080, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19226_610081 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19226 ⟨610081, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19226
    ⟨610081, by decide⟩ (by decide) (![⟨609949, by decide⟩,⟨609990, by decide⟩,⟨610039, by decide⟩,⟨610080, by decide⟩]) unmarked_context_11_19226_610081 node_context_11_19226_610081
  intro a
  fin_cases a
  · exact context_12_76904_609949
  · exact context_12_76905_609990
  · exact context_12_76906_610039
  · exact context_12_76907_610080

theorem selected_cut_24138 : selected 9 ⟨610123, by decide⟩
    (prefixPartial 12 76908) = some ⟨12, 2, 0, 610123, 76908, 2785, 65536⟩ := by
  decide +kernel

theorem context_12_76908_610123 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76908 ⟨610123, by decide⟩ :=
  accepted_of_selected 12 76908 ⟨610123, by decide⟩ ⟨12, 2, 0, 610123, 76908, 2785, 65536⟩
    (by decide) selected_cut_24138

theorem selected_cut_24139 : selected 9 ⟨610162, by decide⟩
    (prefixPartial 12 76909) = some ⟨12, 2, 0, 610162, 76909, 3101, 65536⟩ := by
  decide +kernel

theorem context_12_76909_610162 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76909 ⟨610162, by decide⟩ :=
  accepted_of_selected 12 76909 ⟨610162, by decide⟩ ⟨12, 2, 0, 610162, 76909, 3101, 65536⟩
    (by decide) selected_cut_24139

theorem selected_cut_24140 : selected 9 ⟨610219, by decide⟩
    (prefixPartial 12 76910) = some ⟨12, 2, 0, 610219, 76910, 3249, 65536⟩ := by
  decide +kernel

theorem context_12_76910_610219 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76910 ⟨610219, by decide⟩ :=
  accepted_of_selected 12 76910 ⟨610219, by decide⟩ ⟨12, 2, 0, 610219, 76910, 3249, 65536⟩
    (by decide) selected_cut_24140

theorem selected_cut_24141 : selected 9 ⟨610253, by decide⟩
    (prefixPartial 12 76911) = some ⟨12, 2, 0, 610253, 76911, 3097, 65536⟩ := by
  decide +kernel

theorem context_12_76911_610253 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76911 ⟨610253, by decide⟩ :=
  accepted_of_selected 12 76911 ⟨610253, by decide⟩ ⟨12, 2, 0, 610253, 76911, 3097, 65536⟩
    (by decide) selected_cut_24141

theorem unmarked_context_11_19227_610254 : frontier 10 ⟨610254, by decide⟩
    (prefixCache 11 19227) (prefixPartial 11 19227) = false := by
  decide +kernel

theorem node_context_11_19227_610254 : EJMOriginalGlobalDAGData.nodes 10 ⟨610254, by decide⟩ =
    .split (coordinate 11) (![⟨610123, by decide⟩,⟨610162, by decide⟩,⟨610219, by decide⟩,⟨610253, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19227_610254 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19227 ⟨610254, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19227
    ⟨610254, by decide⟩ (by decide) (![⟨610123, by decide⟩,⟨610162, by decide⟩,⟨610219, by decide⟩,⟨610253, by decide⟩]) unmarked_context_11_19227_610254 node_context_11_19227_610254
  intro a
  fin_cases a
  · exact context_12_76908_610123
  · exact context_12_76909_610162
  · exact context_12_76910_610219
  · exact context_12_76911_610253

theorem unmarked_context_10_4806_610255 : frontier 11 ⟨610255, by decide⟩
    (prefixCache 10 4806) (prefixPartial 10 4806) = false := by
  decide +kernel

theorem node_context_10_4806_610255 : EJMOriginalGlobalDAGData.nodes 11 ⟨610255, by decide⟩ =
    .split (coordinate 10) (![⟨609677, by decide⟩,⟨609908, by decide⟩,⟨610081, by decide⟩,⟨610254, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4806_610255 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4806 ⟨610255, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4806
    ⟨610255, by decide⟩ (by decide) (![⟨609677, by decide⟩,⟨609908, by decide⟩,⟨610081, by decide⟩,⟨610254, by decide⟩]) unmarked_context_10_4806_610255 node_context_10_4806_610255
  intro a
  fin_cases a
  · exact context_11_19224_609677
  · exact context_11_19225_609908
  · exact context_11_19226_610081
  · exact context_11_19227_610254

theorem selected_cut_24142 : selected 9 ⟨393180, by decide⟩
    (prefixPartial 12 76912) = some ⟨12, 1, 0, 393180, 76912, 1, 65536⟩ := by
  decide +kernel

theorem context_12_76912_393180 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76912 ⟨393180, by decide⟩ :=
  accepted_of_selected 12 76912 ⟨393180, by decide⟩ ⟨12, 1, 0, 393180, 76912, 1, 65536⟩
    (by decide) selected_cut_24142

theorem selected_cut_24143 : selected 9 ⟨610295, by decide⟩
    (prefixPartial 12 76913) = some ⟨12, 2, 0, 610295, 76913, 3233, 65536⟩ := by
  decide +kernel

theorem context_12_76913_610295 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76913 ⟨610295, by decide⟩ :=
  accepted_of_selected 12 76913 ⟨610295, by decide⟩ ⟨12, 2, 0, 610295, 76913, 3233, 65536⟩
    (by decide) selected_cut_24143

theorem selected_cut_24144 : selected 9 ⟨610343, by decide⟩
    (prefixPartial 12 76914) = some ⟨12, 2, 0, 610343, 76914, 3125, 65536⟩ := by
  decide +kernel

theorem context_12_76914_610343 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76914 ⟨610343, by decide⟩ :=
  accepted_of_selected 12 76914 ⟨610343, by decide⟩ ⟨12, 2, 0, 610343, 76914, 3125, 65536⟩
    (by decide) selected_cut_24144

theorem selected_cut_24145 : selected 9 ⟨610395, by decide⟩
    (prefixPartial 12 76915) = some ⟨12, 2, 0, 610395, 76915, 3253, 65536⟩ := by
  decide +kernel

theorem context_12_76915_610395 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76915 ⟨610395, by decide⟩ :=
  accepted_of_selected 12 76915 ⟨610395, by decide⟩ ⟨12, 2, 0, 610395, 76915, 3253, 65536⟩
    (by decide) selected_cut_24145

theorem unmarked_context_11_19228_610396 : frontier 10 ⟨610396, by decide⟩
    (prefixCache 11 19228) (prefixPartial 11 19228) = false := by
  decide +kernel

theorem node_context_11_19228_610396 : EJMOriginalGlobalDAGData.nodes 10 ⟨610396, by decide⟩ =
    .split (coordinate 11) (![⟨393180, by decide⟩,⟨610295, by decide⟩,⟨610343, by decide⟩,⟨610395, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19228_610396 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19228 ⟨610396, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19228
    ⟨610396, by decide⟩ (by decide) (![⟨393180, by decide⟩,⟨610295, by decide⟩,⟨610343, by decide⟩,⟨610395, by decide⟩]) unmarked_context_11_19228_610396 node_context_11_19228_610396
  intro a
  fin_cases a
  · exact context_12_76912_393180
  · exact context_12_76913_610295
  · exact context_12_76914_610343
  · exact context_12_76915_610395

theorem selected_cut_24146 : selected 9 ⟨610435, by decide⟩
    (prefixPartial 12 76916) = some ⟨12, 2, 0, 610435, 76916, 2961, 65536⟩ := by
  decide +kernel

theorem context_12_76916_610435 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76916 ⟨610435, by decide⟩ :=
  accepted_of_selected 12 76916 ⟨610435, by decide⟩ ⟨12, 2, 0, 610435, 76916, 2961, 65536⟩
    (by decide) selected_cut_24146

theorem selected_cut_24147 : selected 9 ⟨610473, by decide⟩
    (prefixPartial 12 76917) = some ⟨12, 2, 0, 610473, 76917, 3333, 65536⟩ := by
  decide +kernel

theorem context_12_76917_610473 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76917 ⟨610473, by decide⟩ :=
  accepted_of_selected 12 76917 ⟨610473, by decide⟩ ⟨12, 2, 0, 610473, 76917, 3333, 65536⟩
    (by decide) selected_cut_24147

theorem selected_cut_24148 : selected 9 ⟨610512, by decide⟩
    (prefixPartial 12 76918) = some ⟨12, 2, 0, 610512, 76918, 3397, 65536⟩ := by
  decide +kernel

theorem context_12_76918_610512 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76918 ⟨610512, by decide⟩ :=
  accepted_of_selected 12 76918 ⟨610512, by decide⟩ ⟨12, 2, 0, 610512, 76918, 3397, 65536⟩
    (by decide) selected_cut_24148

theorem selected_cut_24149 : selected 9 ⟨610565, by decide⟩
    (prefixPartial 12 76919) = some ⟨12, 2, 0, 610565, 76919, 3445, 65536⟩ := by
  decide +kernel

theorem context_12_76919_610565 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76919 ⟨610565, by decide⟩ :=
  accepted_of_selected 12 76919 ⟨610565, by decide⟩ ⟨12, 2, 0, 610565, 76919, 3445, 65536⟩
    (by decide) selected_cut_24149

theorem unmarked_context_11_19229_610566 : frontier 10 ⟨610566, by decide⟩
    (prefixCache 11 19229) (prefixPartial 11 19229) = false := by
  decide +kernel

theorem node_context_11_19229_610566 : EJMOriginalGlobalDAGData.nodes 10 ⟨610566, by decide⟩ =
    .split (coordinate 11) (![⟨610435, by decide⟩,⟨610473, by decide⟩,⟨610512, by decide⟩,⟨610565, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19229_610566 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19229 ⟨610566, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19229
    ⟨610566, by decide⟩ (by decide) (![⟨610435, by decide⟩,⟨610473, by decide⟩,⟨610512, by decide⟩,⟨610565, by decide⟩]) unmarked_context_11_19229_610566 node_context_11_19229_610566
  intro a
  fin_cases a
  · exact context_12_76916_610435
  · exact context_12_76917_610473
  · exact context_12_76918_610512
  · exact context_12_76919_610565

theorem selected_cut_24150 : selected 9 ⟨610605, by decide⟩
    (prefixPartial 12 76920) = some ⟨12, 2, 0, 610605, 76920, 2693, 65536⟩ := by
  decide +kernel

theorem context_12_76920_610605 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76920 ⟨610605, by decide⟩ :=
  accepted_of_selected 12 76920 ⟨610605, by decide⟩ ⟨12, 2, 0, 610605, 76920, 2693, 65536⟩
    (by decide) selected_cut_24150

theorem selected_cut_24151 : selected 9 ⟨610643, by decide⟩
    (prefixPartial 12 76921) = some ⟨12, 2, 0, 610643, 76921, 3197, 65536⟩ := by
  decide +kernel

theorem context_12_76921_610643 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76921 ⟨610643, by decide⟩ :=
  accepted_of_selected 12 76921 ⟨610643, by decide⟩ ⟨12, 2, 0, 610643, 76921, 3197, 65536⟩
    (by decide) selected_cut_24151

theorem selected_cut_24152 : selected 9 ⟨610677, by decide⟩
    (prefixPartial 12 76922) = some ⟨12, 2, 0, 610677, 76922, 2913, 65536⟩ := by
  decide +kernel

theorem context_12_76922_610677 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76922 ⟨610677, by decide⟩ :=
  accepted_of_selected 12 76922 ⟨610677, by decide⟩ ⟨12, 2, 0, 610677, 76922, 2913, 65536⟩
    (by decide) selected_cut_24152

theorem selected_cut_24153 : selected 9 ⟨610719, by decide⟩
    (prefixPartial 12 76923) = some ⟨12, 2, 0, 610719, 76923, 2973, 65536⟩ := by
  decide +kernel

theorem context_12_76923_610719 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76923 ⟨610719, by decide⟩ :=
  accepted_of_selected 12 76923 ⟨610719, by decide⟩ ⟨12, 2, 0, 610719, 76923, 2973, 65536⟩
    (by decide) selected_cut_24153

theorem unmarked_context_11_19230_610720 : frontier 10 ⟨610720, by decide⟩
    (prefixCache 11 19230) (prefixPartial 11 19230) = false := by
  decide +kernel

theorem node_context_11_19230_610720 : EJMOriginalGlobalDAGData.nodes 10 ⟨610720, by decide⟩ =
    .split (coordinate 11) (![⟨610605, by decide⟩,⟨610643, by decide⟩,⟨610677, by decide⟩,⟨610719, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19230_610720 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19230 ⟨610720, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19230
    ⟨610720, by decide⟩ (by decide) (![⟨610605, by decide⟩,⟨610643, by decide⟩,⟨610677, by decide⟩,⟨610719, by decide⟩]) unmarked_context_11_19230_610720 node_context_11_19230_610720
  intro a
  fin_cases a
  · exact context_12_76920_610605
  · exact context_12_76921_610643
  · exact context_12_76922_610677
  · exact context_12_76923_610719

theorem selected_cut_24154 : selected 9 ⟨610787, by decide⟩
    (prefixPartial 12 76924) = some ⟨12, 2, 0, 610787, 76924, 3169, 65536⟩ := by
  decide +kernel

theorem context_12_76924_610787 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76924 ⟨610787, by decide⟩ :=
  accepted_of_selected 12 76924 ⟨610787, by decide⟩ ⟨12, 2, 0, 610787, 76924, 3169, 65536⟩
    (by decide) selected_cut_24154

theorem selected_cut_24155 : selected 9 ⟨610869, by decide⟩
    (prefixPartial 12 76925) = some ⟨12, 2, 0, 610869, 76925, 3753, 65536⟩ := by
  decide +kernel

theorem context_12_76925_610869 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76925 ⟨610869, by decide⟩ :=
  accepted_of_selected 12 76925 ⟨610869, by decide⟩ ⟨12, 2, 0, 610869, 76925, 3753, 65536⟩
    (by decide) selected_cut_24155

theorem selected_cut_24156 : selected 9 ⟨610937, by decide⟩
    (prefixPartial 12 76926) = some ⟨12, 2, 0, 610937, 76926, 3545, 65536⟩ := by
  decide +kernel

theorem context_12_76926_610937 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76926 ⟨610937, by decide⟩ :=
  accepted_of_selected 12 76926 ⟨610937, by decide⟩ ⟨12, 2, 0, 610937, 76926, 3545, 65536⟩
    (by decide) selected_cut_24156

theorem selected_cut_24157 : selected 9 ⟨607719, by decide⟩
    (prefixPartial 12 76927) = some ⟨12, 1, 0, 607719, 76927, 1, 65536⟩ := by
  decide +kernel

theorem context_12_76927_607719 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76927 ⟨607719, by decide⟩ :=
  accepted_of_selected 12 76927 ⟨607719, by decide⟩ ⟨12, 1, 0, 607719, 76927, 1, 65536⟩
    (by decide) selected_cut_24157

theorem unmarked_context_11_19231_610938 : frontier 10 ⟨610938, by decide⟩
    (prefixCache 11 19231) (prefixPartial 11 19231) = false := by
  decide +kernel

theorem node_context_11_19231_610938 : EJMOriginalGlobalDAGData.nodes 10 ⟨610938, by decide⟩ =
    .split (coordinate 11) (![⟨610787, by decide⟩,⟨610869, by decide⟩,⟨610937, by decide⟩,⟨607719, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19231_610938 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19231 ⟨610938, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19231
    ⟨610938, by decide⟩ (by decide) (![⟨610787, by decide⟩,⟨610869, by decide⟩,⟨610937, by decide⟩,⟨607719, by decide⟩]) unmarked_context_11_19231_610938 node_context_11_19231_610938
  intro a
  fin_cases a
  · exact context_12_76924_610787
  · exact context_12_76925_610869
  · exact context_12_76926_610937
  · exact context_12_76927_607719

theorem unmarked_context_10_4807_610939 : frontier 11 ⟨610939, by decide⟩
    (prefixCache 10 4807) (prefixPartial 10 4807) = false := by
  decide +kernel

theorem node_context_10_4807_610939 : EJMOriginalGlobalDAGData.nodes 11 ⟨610939, by decide⟩ =
    .split (coordinate 10) (![⟨610396, by decide⟩,⟨610566, by decide⟩,⟨610720, by decide⟩,⟨610938, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4807_610939 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4807 ⟨610939, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4807
    ⟨610939, by decide⟩ (by decide) (![⟨610396, by decide⟩,⟨610566, by decide⟩,⟨610720, by decide⟩,⟨610938, by decide⟩]) unmarked_context_10_4807_610939 node_context_10_4807_610939
  intro a
  fin_cases a
  · exact context_11_19228_610396
  · exact context_11_19229_610566
  · exact context_11_19230_610720
  · exact context_11_19231_610938

theorem unmarked_context_9_1201_610940 : frontier 12 ⟨610940, by decide⟩
    (prefixCache 9 1201) (prefixPartial 9 1201) = false := by
  decide +kernel

theorem node_context_9_1201_610940 : EJMOriginalGlobalDAGData.nodes 12 ⟨610940, by decide⟩ =
    .split (coordinate 9) (![⟨608587, by decide⟩,⟨609438, by decide⟩,⟨610255, by decide⟩,⟨610939, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1201_610940 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1201 ⟨610940, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1201
    ⟨610940, by decide⟩ (by decide) (![⟨608587, by decide⟩,⟨609438, by decide⟩,⟨610255, by decide⟩,⟨610939, by decide⟩]) unmarked_context_9_1201_610940 node_context_9_1201_610940
  intro a
  fin_cases a
  · exact context_10_4804_608587
  · exact context_10_4805_609438
  · exact context_10_4806_610255
  · exact context_10_4807_610939

theorem selected_cut_24158 : selected 9 ⟨450982, by decide⟩
    (prefixPartial 12 76928) = some ⟨12, 1, 0, 450982, 76928, 1, 65536⟩ := by
  decide +kernel

theorem context_12_76928_450982 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76928 ⟨450982, by decide⟩ :=
  accepted_of_selected 12 76928 ⟨450982, by decide⟩ ⟨12, 1, 0, 450982, 76928, 1, 65536⟩
    (by decide) selected_cut_24158

theorem selected_cut_24159 : selected 9 ⟨610970, by decide⟩
    (prefixPartial 12 76929) = some ⟨12, 2, 0, 610970, 76929, 2141, 65536⟩ := by
  decide +kernel

theorem context_12_76929_610970 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76929 ⟨610970, by decide⟩ :=
  accepted_of_selected 12 76929 ⟨610970, by decide⟩ ⟨12, 2, 0, 610970, 76929, 2141, 65536⟩
    (by decide) selected_cut_24159

theorem selected_cut_24160 : selected 9 ⟨610998, by decide⟩
    (prefixPartial 12 76930) = some ⟨12, 2, 0, 610998, 76930, 1897, 65536⟩ := by
  decide +kernel

theorem context_12_76930_610998 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76930 ⟨610998, by decide⟩ :=
  accepted_of_selected 12 76930 ⟨610998, by decide⟩ ⟨12, 2, 0, 610998, 76930, 1897, 65536⟩
    (by decide) selected_cut_24160

theorem selected_cut_24161 : selected 9 ⟨611026, by decide⟩
    (prefixPartial 12 76931) = some ⟨12, 2, 0, 611026, 76931, 2149, 65536⟩ := by
  decide +kernel

theorem context_12_76931_611026 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76931 ⟨611026, by decide⟩ :=
  accepted_of_selected 12 76931 ⟨611026, by decide⟩ ⟨12, 2, 0, 611026, 76931, 2149, 65536⟩
    (by decide) selected_cut_24161

theorem unmarked_context_11_19232_611027 : frontier 10 ⟨611027, by decide⟩
    (prefixCache 11 19232) (prefixPartial 11 19232) = false := by
  decide +kernel

theorem node_context_11_19232_611027 : EJMOriginalGlobalDAGData.nodes 10 ⟨611027, by decide⟩ =
    .split (coordinate 11) (![⟨450982, by decide⟩,⟨610970, by decide⟩,⟨610998, by decide⟩,⟨611026, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19232_611027 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19232 ⟨611027, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19232
    ⟨611027, by decide⟩ (by decide) (![⟨450982, by decide⟩,⟨610970, by decide⟩,⟨610998, by decide⟩,⟨611026, by decide⟩]) unmarked_context_11_19232_611027 node_context_11_19232_611027
  intro a
  fin_cases a
  · exact context_12_76928_450982
  · exact context_12_76929_610970
  · exact context_12_76930_610998
  · exact context_12_76931_611026

theorem selected_cut_24162 : selected 9 ⟨611051, by decide⟩
    (prefixPartial 12 76932) = some ⟨12, 2, 0, 611051, 76932, 1805, 65536⟩ := by
  decide +kernel

theorem context_12_76932_611051 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76932 ⟨611051, by decide⟩ :=
  accepted_of_selected 12 76932 ⟨611051, by decide⟩ ⟨12, 2, 0, 611051, 76932, 1805, 65536⟩
    (by decide) selected_cut_24162

theorem selected_cut_24163 : selected 9 ⟨611088, by decide⟩
    (prefixPartial 12 76933) = some ⟨12, 2, 0, 611088, 76933, 2241, 65536⟩ := by
  decide +kernel

theorem context_12_76933_611088 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76933 ⟨611088, by decide⟩ :=
  accepted_of_selected 12 76933 ⟨611088, by decide⟩ ⟨12, 2, 0, 611088, 76933, 2241, 65536⟩
    (by decide) selected_cut_24163

theorem selected_cut_24164 : selected 9 ⟨611122, by decide⟩
    (prefixPartial 12 76934) = some ⟨12, 2, 0, 611122, 76934, 2181, 65536⟩ := by
  decide +kernel

theorem context_12_76934_611122 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76934 ⟨611122, by decide⟩ :=
  accepted_of_selected 12 76934 ⟨611122, by decide⟩ ⟨12, 2, 0, 611122, 76934, 2181, 65536⟩
    (by decide) selected_cut_24164

theorem selected_cut_24165 : selected 9 ⟨611151, by decide⟩
    (prefixPartial 12 76935) = some ⟨12, 2, 0, 611151, 76935, 2417, 65536⟩ := by
  decide +kernel

theorem context_12_76935_611151 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76935 ⟨611151, by decide⟩ :=
  accepted_of_selected 12 76935 ⟨611151, by decide⟩ ⟨12, 2, 0, 611151, 76935, 2417, 65536⟩
    (by decide) selected_cut_24165

theorem unmarked_context_11_19233_611152 : frontier 10 ⟨611152, by decide⟩
    (prefixCache 11 19233) (prefixPartial 11 19233) = false := by
  decide +kernel

theorem node_context_11_19233_611152 : EJMOriginalGlobalDAGData.nodes 10 ⟨611152, by decide⟩ =
    .split (coordinate 11) (![⟨611051, by decide⟩,⟨611088, by decide⟩,⟨611122, by decide⟩,⟨611151, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19233_611152 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19233 ⟨611152, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19233
    ⟨611152, by decide⟩ (by decide) (![⟨611051, by decide⟩,⟨611088, by decide⟩,⟨611122, by decide⟩,⟨611151, by decide⟩]) unmarked_context_11_19233_611152 node_context_11_19233_611152
  intro a
  fin_cases a
  · exact context_12_76932_611051
  · exact context_12_76933_611088
  · exact context_12_76934_611122
  · exact context_12_76935_611151

theorem selected_cut_24166 : selected 9 ⟨611177, by decide⟩
    (prefixPartial 12 76936) = some ⟨12, 2, 0, 611177, 76936, 1853, 65536⟩ := by
  decide +kernel

theorem context_12_76936_611177 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76936 ⟨611177, by decide⟩ :=
  accepted_of_selected 12 76936 ⟨611177, by decide⟩ ⟨12, 2, 0, 611177, 76936, 1853, 65536⟩
    (by decide) selected_cut_24166

theorem selected_cut_24167 : selected 9 ⟨611229, by decide⟩
    (prefixPartial 12 76937) = some ⟨12, 2, 0, 611229, 76937, 2597, 65536⟩ := by
  decide +kernel

theorem context_12_76937_611229 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76937 ⟨611229, by decide⟩ :=
  accepted_of_selected 12 76937 ⟨611229, by decide⟩ ⟨12, 2, 0, 611229, 76937, 2597, 65536⟩
    (by decide) selected_cut_24167

theorem selected_cut_24168 : selected 9 ⟨611269, by decide⟩
    (prefixPartial 12 76938) = some ⟨12, 2, 0, 611269, 76938, 2125, 65536⟩ := by
  decide +kernel

theorem context_12_76938_611269 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76938 ⟨611269, by decide⟩ :=
  accepted_of_selected 12 76938 ⟨611269, by decide⟩ ⟨12, 2, 0, 611269, 76938, 2125, 65536⟩
    (by decide) selected_cut_24168

theorem selected_cut_24169 : selected 9 ⟨611315, by decide⟩
    (prefixPartial 12 76939) = some ⟨12, 2, 0, 611315, 76939, 2421, 65536⟩ := by
  decide +kernel

theorem context_12_76939_611315 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76939 ⟨611315, by decide⟩ :=
  accepted_of_selected 12 76939 ⟨611315, by decide⟩ ⟨12, 2, 0, 611315, 76939, 2421, 65536⟩
    (by decide) selected_cut_24169

theorem unmarked_context_11_19234_611316 : frontier 10 ⟨611316, by decide⟩
    (prefixCache 11 19234) (prefixPartial 11 19234) = false := by
  decide +kernel

theorem node_context_11_19234_611316 : EJMOriginalGlobalDAGData.nodes 10 ⟨611316, by decide⟩ =
    .split (coordinate 11) (![⟨611177, by decide⟩,⟨611229, by decide⟩,⟨611269, by decide⟩,⟨611315, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19234_611316 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19234 ⟨611316, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19234
    ⟨611316, by decide⟩ (by decide) (![⟨611177, by decide⟩,⟨611229, by decide⟩,⟨611269, by decide⟩,⟨611315, by decide⟩]) unmarked_context_11_19234_611316 node_context_11_19234_611316
  intro a
  fin_cases a
  · exact context_12_76936_611177
  · exact context_12_76937_611229
  · exact context_12_76938_611269
  · exact context_12_76939_611315

theorem selected_cut_24170 : selected 9 ⟨611340, by decide⟩
    (prefixPartial 12 76940) = some ⟨12, 2, 0, 611340, 76940, 1477, 65536⟩ := by
  decide +kernel

theorem context_12_76940_611340 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76940 ⟨611340, by decide⟩ :=
  accepted_of_selected 12 76940 ⟨611340, by decide⟩ ⟨12, 2, 0, 611340, 76940, 1477, 65536⟩
    (by decide) selected_cut_24170

theorem selected_cut_24171 : selected 9 ⟨611372, by decide⟩
    (prefixPartial 12 76941) = some ⟨12, 2, 0, 611372, 76941, 1953, 65536⟩ := by
  decide +kernel

theorem context_12_76941_611372 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76941 ⟨611372, by decide⟩ :=
  accepted_of_selected 12 76941 ⟨611372, by decide⟩ ⟨12, 2, 0, 611372, 76941, 1953, 65536⟩
    (by decide) selected_cut_24171

theorem selected_cut_24172 : selected 9 ⟨611399, by decide⟩
    (prefixPartial 12 76942) = some ⟨12, 2, 0, 611399, 76942, 1853, 65536⟩ := by
  decide +kernel

theorem context_12_76942_611399 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76942 ⟨611399, by decide⟩ :=
  accepted_of_selected 12 76942 ⟨611399, by decide⟩ ⟨12, 2, 0, 611399, 76942, 1853, 65536⟩
    (by decide) selected_cut_24172

theorem selected_cut_24173 : selected 9 ⟨611429, by decide⟩
    (prefixPartial 12 76943) = some ⟨12, 2, 0, 611429, 76943, 2005, 65536⟩ := by
  decide +kernel

theorem context_12_76943_611429 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76943 ⟨611429, by decide⟩ :=
  accepted_of_selected 12 76943 ⟨611429, by decide⟩ ⟨12, 2, 0, 611429, 76943, 2005, 65536⟩
    (by decide) selected_cut_24173

theorem unmarked_context_11_19235_611430 : frontier 10 ⟨611430, by decide⟩
    (prefixCache 11 19235) (prefixPartial 11 19235) = false := by
  decide +kernel

theorem node_context_11_19235_611430 : EJMOriginalGlobalDAGData.nodes 10 ⟨611430, by decide⟩ =
    .split (coordinate 11) (![⟨611340, by decide⟩,⟨611372, by decide⟩,⟨611399, by decide⟩,⟨611429, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19235_611430 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19235 ⟨611430, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19235
    ⟨611430, by decide⟩ (by decide) (![⟨611340, by decide⟩,⟨611372, by decide⟩,⟨611399, by decide⟩,⟨611429, by decide⟩]) unmarked_context_11_19235_611430 node_context_11_19235_611430
  intro a
  fin_cases a
  · exact context_12_76940_611340
  · exact context_12_76941_611372
  · exact context_12_76942_611399
  · exact context_12_76943_611429

theorem unmarked_context_10_4808_611431 : frontier 11 ⟨611431, by decide⟩
    (prefixCache 10 4808) (prefixPartial 10 4808) = false := by
  decide +kernel

theorem node_context_10_4808_611431 : EJMOriginalGlobalDAGData.nodes 11 ⟨611431, by decide⟩ =
    .split (coordinate 10) (![⟨611027, by decide⟩,⟨611152, by decide⟩,⟨611316, by decide⟩,⟨611430, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4808_611431 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4808 ⟨611431, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4808
    ⟨611431, by decide⟩ (by decide) (![⟨611027, by decide⟩,⟨611152, by decide⟩,⟨611316, by decide⟩,⟨611430, by decide⟩]) unmarked_context_10_4808_611431 node_context_10_4808_611431
  intro a
  fin_cases a
  · exact context_11_19232_611027
  · exact context_11_19233_611152
  · exact context_11_19234_611316
  · exact context_11_19235_611430

theorem selected_cut_24174 : selected 9 ⟨611536, by decide⟩
    (prefixPartial 12 76944) = some ⟨12, 2, 0, 611536, 76944, 1117, 65536⟩ := by
  decide +kernel

theorem context_12_76944_611536 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76944 ⟨611536, by decide⟩ :=
  accepted_of_selected 12 76944 ⟨611536, by decide⟩ ⟨12, 2, 0, 611536, 76944, 1117, 65536⟩
    (by decide) selected_cut_24174

theorem selected_cut_24175 : selected 9 ⟨611572, by decide⟩
    (prefixPartial 12 76945) = some ⟨12, 2, 0, 611572, 76945, 2517, 65536⟩ := by
  decide +kernel

theorem context_12_76945_611572 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76945 ⟨611572, by decide⟩ :=
  accepted_of_selected 12 76945 ⟨611572, by decide⟩ ⟨12, 2, 0, 611572, 76945, 2517, 65536⟩
    (by decide) selected_cut_24175

theorem selected_cut_24176 : selected 9 ⟨611594, by decide⟩
    (prefixPartial 12 76946) = some ⟨12, 2, 0, 611594, 76946, 2181, 65536⟩ := by
  decide +kernel

theorem context_12_76946_611594 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76946 ⟨611594, by decide⟩ :=
  accepted_of_selected 12 76946 ⟨611594, by decide⟩ ⟨12, 2, 0, 611594, 76946, 2181, 65536⟩
    (by decide) selected_cut_24176

theorem selected_cut_24177 : selected 9 ⟨611629, by decide⟩
    (prefixPartial 12 76947) = some ⟨12, 2, 0, 611629, 76947, 2389, 65536⟩ := by
  decide +kernel

theorem context_12_76947_611629 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76947 ⟨611629, by decide⟩ :=
  accepted_of_selected 12 76947 ⟨611629, by decide⟩ ⟨12, 2, 0, 611629, 76947, 2389, 65536⟩
    (by decide) selected_cut_24177

theorem unmarked_context_11_19236_611630 : frontier 10 ⟨611630, by decide⟩
    (prefixCache 11 19236) (prefixPartial 11 19236) = false := by
  decide +kernel

theorem node_context_11_19236_611630 : EJMOriginalGlobalDAGData.nodes 10 ⟨611630, by decide⟩ =
    .split (coordinate 11) (![⟨611536, by decide⟩,⟨611572, by decide⟩,⟨611594, by decide⟩,⟨611629, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19236_611630 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19236 ⟨611630, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19236
    ⟨611630, by decide⟩ (by decide) (![⟨611536, by decide⟩,⟨611572, by decide⟩,⟨611594, by decide⟩,⟨611629, by decide⟩]) unmarked_context_11_19236_611630 node_context_11_19236_611630
  intro a
  fin_cases a
  · exact context_12_76944_611536
  · exact context_12_76945_611572
  · exact context_12_76946_611594
  · exact context_12_76947_611629

theorem selected_cut_24178 : selected 9 ⟨611652, by decide⟩
    (prefixPartial 12 76948) = some ⟨12, 2, 0, 611652, 76948, 2225, 65536⟩ := by
  decide +kernel

theorem context_12_76948_611652 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76948 ⟨611652, by decide⟩ :=
  accepted_of_selected 12 76948 ⟨611652, by decide⟩ ⟨12, 2, 0, 611652, 76948, 2225, 65536⟩
    (by decide) selected_cut_24178

theorem selected_cut_24179 : selected 9 ⟨611692, by decide⟩
    (prefixPartial 12 76949) = some ⟨12, 2, 0, 611692, 76949, 2581, 65536⟩ := by
  decide +kernel

theorem context_12_76949_611692 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76949 ⟨611692, by decide⟩ :=
  accepted_of_selected 12 76949 ⟨611692, by decide⟩ ⟨12, 2, 0, 611692, 76949, 2581, 65536⟩
    (by decide) selected_cut_24179

theorem selected_cut_24180 : selected 9 ⟨611717, by decide⟩
    (prefixPartial 12 76950) = some ⟨12, 2, 0, 611717, 76950, 2313, 65536⟩ := by
  decide +kernel

theorem context_12_76950_611717 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76950 ⟨611717, by decide⟩ :=
  accepted_of_selected 12 76950 ⟨611717, by decide⟩ ⟨12, 2, 0, 611717, 76950, 2313, 65536⟩
    (by decide) selected_cut_24180

theorem selected_cut_24181 : selected 9 ⟨611770, by decide⟩
    (prefixPartial 12 76951) = some ⟨12, 2, 0, 611770, 76951, 2545, 65536⟩ := by
  decide +kernel

theorem context_12_76951_611770 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76951 ⟨611770, by decide⟩ :=
  accepted_of_selected 12 76951 ⟨611770, by decide⟩ ⟨12, 2, 0, 611770, 76951, 2545, 65536⟩
    (by decide) selected_cut_24181

theorem unmarked_context_11_19237_611771 : frontier 10 ⟨611771, by decide⟩
    (prefixCache 11 19237) (prefixPartial 11 19237) = false := by
  decide +kernel

theorem node_context_11_19237_611771 : EJMOriginalGlobalDAGData.nodes 10 ⟨611771, by decide⟩ =
    .split (coordinate 11) (![⟨611652, by decide⟩,⟨611692, by decide⟩,⟨611717, by decide⟩,⟨611770, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19237_611771 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19237 ⟨611771, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19237
    ⟨611771, by decide⟩ (by decide) (![⟨611652, by decide⟩,⟨611692, by decide⟩,⟨611717, by decide⟩,⟨611770, by decide⟩]) unmarked_context_11_19237_611771 node_context_11_19237_611771
  intro a
  fin_cases a
  · exact context_12_76948_611652
  · exact context_12_76949_611692
  · exact context_12_76950_611717
  · exact context_12_76951_611770

theorem selected_cut_24182 : selected 9 ⟨611805, by decide⟩
    (prefixPartial 12 76952) = some ⟨12, 2, 0, 611805, 76952, 2209, 65536⟩ := by
  decide +kernel

theorem context_12_76952_611805 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76952 ⟨611805, by decide⟩ :=
  accepted_of_selected 12 76952 ⟨611805, by decide⟩ ⟨12, 2, 0, 611805, 76952, 2209, 65536⟩
    (by decide) selected_cut_24182

theorem selected_cut_24183 : selected 9 ⟨611863, by decide⟩
    (prefixPartial 12 76953) = some ⟨12, 2, 0, 611863, 76953, 2777, 65536⟩ := by
  decide +kernel

theorem context_12_76953_611863 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76953 ⟨611863, by decide⟩ :=
  accepted_of_selected 12 76953 ⟨611863, by decide⟩ ⟨12, 2, 0, 611863, 76953, 2777, 65536⟩
    (by decide) selected_cut_24183

theorem selected_cut_24184 : selected 9 ⟨611890, by decide⟩
    (prefixPartial 12 76954) = some ⟨12, 2, 0, 611890, 76954, 2161, 65536⟩ := by
  decide +kernel

theorem context_12_76954_611890 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76954 ⟨611890, by decide⟩ :=
  accepted_of_selected 12 76954 ⟨611890, by decide⟩ ⟨12, 2, 0, 611890, 76954, 2161, 65536⟩
    (by decide) selected_cut_24184

theorem selected_cut_24185 : selected 9 ⟨611939, by decide⟩
    (prefixPartial 12 76955) = some ⟨12, 2, 0, 611939, 76955, 2445, 65536⟩ := by
  decide +kernel

theorem context_12_76955_611939 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76955 ⟨611939, by decide⟩ :=
  accepted_of_selected 12 76955 ⟨611939, by decide⟩ ⟨12, 2, 0, 611939, 76955, 2445, 65536⟩
    (by decide) selected_cut_24185

theorem unmarked_context_11_19238_611940 : frontier 10 ⟨611940, by decide⟩
    (prefixCache 11 19238) (prefixPartial 11 19238) = false := by
  decide +kernel

theorem node_context_11_19238_611940 : EJMOriginalGlobalDAGData.nodes 10 ⟨611940, by decide⟩ =
    .split (coordinate 11) (![⟨611805, by decide⟩,⟨611863, by decide⟩,⟨611890, by decide⟩,⟨611939, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19238_611940 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19238 ⟨611940, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19238
    ⟨611940, by decide⟩ (by decide) (![⟨611805, by decide⟩,⟨611863, by decide⟩,⟨611890, by decide⟩,⟨611939, by decide⟩]) unmarked_context_11_19238_611940 node_context_11_19238_611940
  intro a
  fin_cases a
  · exact context_12_76952_611805
  · exact context_12_76953_611863
  · exact context_12_76954_611890
  · exact context_12_76955_611939

theorem selected_cut_24186 : selected 9 ⟨611964, by decide⟩
    (prefixPartial 12 76956) = some ⟨12, 2, 0, 611964, 76956, 1797, 65536⟩ := by
  decide +kernel

theorem context_12_76956_611964 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76956 ⟨611964, by decide⟩ :=
  accepted_of_selected 12 76956 ⟨611964, by decide⟩ ⟨12, 2, 0, 611964, 76956, 1797, 65536⟩
    (by decide) selected_cut_24186

theorem selected_cut_24187 : selected 9 ⟨611989, by decide⟩
    (prefixPartial 12 76957) = some ⟨12, 2, 0, 611989, 76957, 2157, 65536⟩ := by
  decide +kernel

theorem context_12_76957_611989 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76957 ⟨611989, by decide⟩ :=
  accepted_of_selected 12 76957 ⟨611989, by decide⟩ ⟨12, 2, 0, 611989, 76957, 2157, 65536⟩
    (by decide) selected_cut_24187

theorem selected_cut_24188 : selected 9 ⟨612008, by decide⟩
    (prefixPartial 12 76958) = some ⟨12, 2, 0, 612008, 76958, 1985, 65536⟩ := by
  decide +kernel

theorem context_12_76958_612008 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76958 ⟨612008, by decide⟩ :=
  accepted_of_selected 12 76958 ⟨612008, by decide⟩ ⟨12, 2, 0, 612008, 76958, 1985, 65536⟩
    (by decide) selected_cut_24188

theorem selected_cut_24189 : selected 9 ⟨612027, by decide⟩
    (prefixPartial 12 76959) = some ⟨12, 2, 0, 612027, 76959, 1997, 65536⟩ := by
  decide +kernel

theorem context_12_76959_612027 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76959 ⟨612027, by decide⟩ :=
  accepted_of_selected 12 76959 ⟨612027, by decide⟩ ⟨12, 2, 0, 612027, 76959, 1997, 65536⟩
    (by decide) selected_cut_24189

theorem unmarked_context_11_19239_612028 : frontier 10 ⟨612028, by decide⟩
    (prefixCache 11 19239) (prefixPartial 11 19239) = false := by
  decide +kernel

theorem node_context_11_19239_612028 : EJMOriginalGlobalDAGData.nodes 10 ⟨612028, by decide⟩ =
    .split (coordinate 11) (![⟨611964, by decide⟩,⟨611989, by decide⟩,⟨612008, by decide⟩,⟨612027, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19239_612028 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19239 ⟨612028, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19239
    ⟨612028, by decide⟩ (by decide) (![⟨611964, by decide⟩,⟨611989, by decide⟩,⟨612008, by decide⟩,⟨612027, by decide⟩]) unmarked_context_11_19239_612028 node_context_11_19239_612028
  intro a
  fin_cases a
  · exact context_12_76956_611964
  · exact context_12_76957_611989
  · exact context_12_76958_612008
  · exact context_12_76959_612027

theorem unmarked_context_10_4809_612029 : frontier 11 ⟨612029, by decide⟩
    (prefixCache 10 4809) (prefixPartial 10 4809) = false := by
  decide +kernel

theorem node_context_10_4809_612029 : EJMOriginalGlobalDAGData.nodes 11 ⟨612029, by decide⟩ =
    .split (coordinate 10) (![⟨611630, by decide⟩,⟨611771, by decide⟩,⟨611940, by decide⟩,⟨612028, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4809_612029 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4809 ⟨612029, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4809
    ⟨612029, by decide⟩ (by decide) (![⟨611630, by decide⟩,⟨611771, by decide⟩,⟨611940, by decide⟩,⟨612028, by decide⟩]) unmarked_context_10_4809_612029 node_context_10_4809_612029
  intro a
  fin_cases a
  · exact context_11_19236_611630
  · exact context_11_19237_611771
  · exact context_11_19238_611940
  · exact context_11_19239_612028

theorem selected_cut_24190 : selected 9 ⟨544742, by decide⟩
    (prefixPartial 12 76960) = some ⟨12, 1, 0, 544742, 76960, 1, 65536⟩ := by
  decide +kernel

theorem context_12_76960_544742 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76960 ⟨544742, by decide⟩ :=
  accepted_of_selected 12 76960 ⟨544742, by decide⟩ ⟨12, 1, 0, 544742, 76960, 1, 65536⟩
    (by decide) selected_cut_24190

theorem selected_cut_24191 : selected 9 ⟨612053, by decide⟩
    (prefixPartial 12 76961) = some ⟨12, 2, 0, 612053, 76961, 1653, 65536⟩ := by
  decide +kernel

theorem context_12_76961_612053 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76961 ⟨612053, by decide⟩ :=
  accepted_of_selected 12 76961 ⟨612053, by decide⟩ ⟨12, 2, 0, 612053, 76961, 1653, 65536⟩
    (by decide) selected_cut_24191

theorem selected_cut_24192 : selected 9 ⟨612070, by decide⟩
    (prefixPartial 12 76962) = some ⟨12, 2, 0, 612070, 76962, 1489, 65536⟩ := by
  decide +kernel

theorem context_12_76962_612070 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76962 ⟨612070, by decide⟩ :=
  accepted_of_selected 12 76962 ⟨612070, by decide⟩ ⟨12, 2, 0, 612070, 76962, 1489, 65536⟩
    (by decide) selected_cut_24192

theorem selected_cut_24193 : selected 9 ⟨612089, by decide⟩
    (prefixPartial 12 76963) = some ⟨12, 2, 0, 612089, 76963, 1665, 65536⟩ := by
  decide +kernel

theorem context_12_76963_612089 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76963 ⟨612089, by decide⟩ :=
  accepted_of_selected 12 76963 ⟨612089, by decide⟩ ⟨12, 2, 0, 612089, 76963, 1665, 65536⟩
    (by decide) selected_cut_24193

theorem unmarked_context_11_19240_612090 : frontier 10 ⟨612090, by decide⟩
    (prefixCache 11 19240) (prefixPartial 11 19240) = false := by
  decide +kernel

theorem node_context_11_19240_612090 : EJMOriginalGlobalDAGData.nodes 10 ⟨612090, by decide⟩ =
    .split (coordinate 11) (![⟨544742, by decide⟩,⟨612053, by decide⟩,⟨612070, by decide⟩,⟨612089, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19240_612090 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19240 ⟨612090, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19240
    ⟨612090, by decide⟩ (by decide) (![⟨544742, by decide⟩,⟨612053, by decide⟩,⟨612070, by decide⟩,⟨612089, by decide⟩]) unmarked_context_11_19240_612090 node_context_11_19240_612090
  intro a
  fin_cases a
  · exact context_12_76960_544742
  · exact context_12_76961_612053
  · exact context_12_76962_612070
  · exact context_12_76963_612089

theorem selected_cut_24194 : selected 9 ⟨612109, by decide⟩
    (prefixPartial 12 76964) = some ⟨12, 2, 0, 612109, 76964, 1701, 65536⟩ := by
  decide +kernel

theorem context_12_76964_612109 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76964 ⟨612109, by decide⟩ :=
  accepted_of_selected 12 76964 ⟨612109, by decide⟩ ⟨12, 2, 0, 612109, 76964, 1701, 65536⟩
    (by decide) selected_cut_24194

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
