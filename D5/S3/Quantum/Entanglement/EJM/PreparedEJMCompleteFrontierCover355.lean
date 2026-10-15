/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover354
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_34084 : selected 8 ⟨880159, by decide⟩
    (prefixPartial 13 451738) = some ⟨13, 2, 0, 880159, 451738, 753, 16384⟩ := by
  decide +kernel

theorem context_13_451738_880159 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 451738 ⟨880159, by decide⟩ :=
  accepted_of_selected 13 451738 ⟨880159, by decide⟩ ⟨13, 2, 0, 880159, 451738, 753, 16384⟩
    (by decide) selected_cut_34084

theorem selected_cut_34085 : selected 8 ⟨880170, by decide⟩
    (prefixPartial 13 451739) = some ⟨13, 2, 0, 880170, 451739, 885, 16384⟩ := by
  decide +kernel

theorem context_13_451739_880170 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 451739 ⟨880170, by decide⟩ :=
  accepted_of_selected 13 451739 ⟨880170, by decide⟩ ⟨13, 2, 0, 880170, 451739, 885, 16384⟩
    (by decide) selected_cut_34085

theorem unmarked_context_12_112934_880171 : frontier 9 ⟨880171, by decide⟩
    (prefixCache 12 112934) (prefixPartial 12 112934) = false := by
  decide +kernel

theorem node_context_12_112934_880171 : EJMOriginalGlobalDAGData.nodes 9 ⟨880171, by decide⟩ =
    .split (coordinate 12) (![⟨880120, by decide⟩,⟨880142, by decide⟩,⟨880159, by decide⟩,⟨880170, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_112934_880171 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112934 ⟨880171, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 112934
    ⟨880171, by decide⟩ (by decide) (![⟨880120, by decide⟩,⟨880142, by decide⟩,⟨880159, by decide⟩,⟨880170, by decide⟩]) unmarked_context_12_112934_880171 node_context_12_112934_880171
  intro a
  fin_cases a
  · exact context_13_451736_880120
  · exact context_13_451737_880142
  · exact context_13_451738_880159
  · exact context_13_451739_880170

theorem selected_cut_34086 : selected 8 ⟨880184, by decide⟩
    (prefixPartial 13 451740) = some ⟨13, 2, 0, 880184, 451740, 873, 16384⟩ := by
  decide +kernel

theorem context_13_451740_880184 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 451740 ⟨880184, by decide⟩ :=
  accepted_of_selected 13 451740 ⟨880184, by decide⟩ ⟨13, 2, 0, 880184, 451740, 873, 16384⟩
    (by decide) selected_cut_34086

theorem selected_cut_34087 : selected 8 ⟨880209, by decide⟩
    (prefixPartial 13 451741) = some ⟨13, 2, 0, 880209, 451741, 1773, 16384⟩ := by
  decide +kernel

theorem context_13_451741_880209 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 451741 ⟨880209, by decide⟩ :=
  accepted_of_selected 13 451741 ⟨880209, by decide⟩ ⟨13, 2, 0, 880209, 451741, 1773, 16384⟩
    (by decide) selected_cut_34087

theorem selected_cut_34088 : selected 8 ⟨880223, by decide⟩
    (prefixPartial 13 451742) = some ⟨13, 2, 0, 880223, 451742, 757, 16384⟩ := by
  decide +kernel

theorem context_13_451742_880223 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 451742 ⟨880223, by decide⟩ :=
  accepted_of_selected 13 451742 ⟨880223, by decide⟩ ⟨13, 2, 0, 880223, 451742, 757, 16384⟩
    (by decide) selected_cut_34088

theorem selected_cut_34089 : selected 8 ⟨880230, by decide⟩
    (prefixPartial 13 451743) = some ⟨13, 2, 0, 880230, 451743, 717, 16384⟩ := by
  decide +kernel

theorem context_13_451743_880230 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 451743 ⟨880230, by decide⟩ :=
  accepted_of_selected 13 451743 ⟨880230, by decide⟩ ⟨13, 2, 0, 880230, 451743, 717, 16384⟩
    (by decide) selected_cut_34089

theorem unmarked_context_12_112935_880231 : frontier 9 ⟨880231, by decide⟩
    (prefixCache 12 112935) (prefixPartial 12 112935) = false := by
  decide +kernel

theorem node_context_12_112935_880231 : EJMOriginalGlobalDAGData.nodes 9 ⟨880231, by decide⟩ =
    .split (coordinate 12) (![⟨880184, by decide⟩,⟨880209, by decide⟩,⟨880223, by decide⟩,⟨880230, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_112935_880231 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112935 ⟨880231, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 112935
    ⟨880231, by decide⟩ (by decide) (![⟨880184, by decide⟩,⟨880209, by decide⟩,⟨880223, by decide⟩,⟨880230, by decide⟩]) unmarked_context_12_112935_880231 node_context_12_112935_880231
  intro a
  fin_cases a
  · exact context_13_451740_880184
  · exact context_13_451741_880209
  · exact context_13_451742_880223
  · exact context_13_451743_880230

theorem unmarked_context_11_28233_880232 : frontier 10 ⟨880232, by decide⟩
    (prefixCache 11 28233) (prefixPartial 11 28233) = false := by
  decide +kernel

theorem node_context_11_28233_880232 : EJMOriginalGlobalDAGData.nodes 10 ⟨880232, by decide⟩ =
    .split (coordinate 11) (![⟨880105, by decide⟩,⟨688903, by decide⟩,⟨880171, by decide⟩,⟨880231, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_28233_880232 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 28233 ⟨880232, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 28233
    ⟨880232, by decide⟩ (by decide) (![⟨880105, by decide⟩,⟨688903, by decide⟩,⟨880171, by decide⟩,⟨880231, by decide⟩]) unmarked_context_11_28233_880232 node_context_11_28233_880232
  intro a
  fin_cases a
  · exact context_12_112932_880105
  · exact context_12_112933_688903
  · exact context_12_112934_880171
  · exact context_12_112935_880231

theorem selected_cut_34090 : selected 10 ⟨766338, by decide⟩
    (prefixPartial 11 28234) = some ⟨11, 1, 0, 766338, 28234, 1, 262144⟩ := by
  decide +kernel

theorem context_11_28234_766338 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 28234 ⟨766338, by decide⟩ :=
  accepted_of_selected 11 28234 ⟨766338, by decide⟩ ⟨11, 1, 0, 766338, 28234, 1, 262144⟩
    (by decide) selected_cut_34090

theorem selected_cut_34091 : selected 8 ⟨880243, by decide⟩
    (prefixPartial 13 451760) = some ⟨13, 2, 0, 880243, 451760, 849, 16384⟩ := by
  decide +kernel

theorem context_13_451760_880243 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 451760 ⟨880243, by decide⟩ :=
  accepted_of_selected 13 451760 ⟨880243, by decide⟩ ⟨13, 2, 0, 880243, 451760, 849, 16384⟩
    (by decide) selected_cut_34091

theorem selected_cut_34092 : selected 8 ⟨880271, by decide⟩
    (prefixPartial 13 451761) = some ⟨13, 2, 0, 880271, 451761, 2141, 16384⟩ := by
  decide +kernel

theorem context_13_451761_880271 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 451761 ⟨880271, by decide⟩ :=
  accepted_of_selected 13 451761 ⟨880271, by decide⟩ ⟨13, 2, 0, 880271, 451761, 2141, 16384⟩
    (by decide) selected_cut_34092

theorem selected_cut_34093 : selected 8 ⟨880292, by decide⟩
    (prefixPartial 13 451762) = some ⟨13, 2, 0, 880292, 451762, 993, 16384⟩ := by
  decide +kernel

theorem context_13_451762_880292 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 451762 ⟨880292, by decide⟩ :=
  accepted_of_selected 13 451762 ⟨880292, by decide⟩ ⟨13, 2, 0, 880292, 451762, 993, 16384⟩
    (by decide) selected_cut_34093

theorem selected_cut_34094 : selected 8 ⟨880298, by decide⟩
    (prefixPartial 13 451763) = some ⟨13, 2, 0, 880298, 451763, 873, 16384⟩ := by
  decide +kernel

theorem context_13_451763_880298 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 451763 ⟨880298, by decide⟩ :=
  accepted_of_selected 13 451763 ⟨880298, by decide⟩ ⟨13, 2, 0, 880298, 451763, 873, 16384⟩
    (by decide) selected_cut_34094

theorem unmarked_context_12_112940_880299 : frontier 9 ⟨880299, by decide⟩
    (prefixCache 12 112940) (prefixPartial 12 112940) = false := by
  decide +kernel

theorem node_context_12_112940_880299 : EJMOriginalGlobalDAGData.nodes 9 ⟨880299, by decide⟩ =
    .split (coordinate 12) (![⟨880243, by decide⟩,⟨880271, by decide⟩,⟨880292, by decide⟩,⟨880298, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_112940_880299 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112940 ⟨880299, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 112940
    ⟨880299, by decide⟩ (by decide) (![⟨880243, by decide⟩,⟨880271, by decide⟩,⟨880292, by decide⟩,⟨880298, by decide⟩]) unmarked_context_12_112940_880299 node_context_12_112940_880299
  intro a
  fin_cases a
  · exact context_13_451760_880243
  · exact context_13_451761_880271
  · exact context_13_451762_880292
  · exact context_13_451763_880298

theorem selected_cut_34095 : selected 8 ⟨880312, by decide⟩
    (prefixPartial 13 451764) = some ⟨13, 2, 0, 880312, 451764, 937, 16384⟩ := by
  decide +kernel

theorem context_13_451764_880312 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 451764 ⟨880312, by decide⟩ :=
  accepted_of_selected 13 451764 ⟨880312, by decide⟩ ⟨13, 2, 0, 880312, 451764, 937, 16384⟩
    (by decide) selected_cut_34095

theorem selected_cut_34096 : selected 8 ⟨880337, by decide⟩
    (prefixPartial 13 451765) = some ⟨13, 2, 0, 880337, 451765, 2153, 16384⟩ := by
  decide +kernel

theorem context_13_451765_880337 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 451765 ⟨880337, by decide⟩ :=
  accepted_of_selected 13 451765 ⟨880337, by decide⟩ ⟨13, 2, 0, 880337, 451765, 2153, 16384⟩
    (by decide) selected_cut_34096

theorem selected_cut_34097 : selected 8 ⟨880353, by decide⟩
    (prefixPartial 13 451766) = some ⟨13, 2, 0, 880353, 451766, 1137, 16384⟩ := by
  decide +kernel

theorem context_13_451766_880353 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 451766 ⟨880353, by decide⟩ :=
  accepted_of_selected 13 451766 ⟨880353, by decide⟩ ⟨13, 2, 0, 880353, 451766, 1137, 16384⟩
    (by decide) selected_cut_34097

theorem selected_cut_34098 : selected 8 ⟨880363, by decide⟩
    (prefixPartial 13 451767) = some ⟨13, 2, 0, 880363, 451767, 1021, 16384⟩ := by
  decide +kernel

theorem context_13_451767_880363 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 451767 ⟨880363, by decide⟩ :=
  accepted_of_selected 13 451767 ⟨880363, by decide⟩ ⟨13, 2, 0, 880363, 451767, 1021, 16384⟩
    (by decide) selected_cut_34098

theorem unmarked_context_12_112941_880364 : frontier 9 ⟨880364, by decide⟩
    (prefixCache 12 112941) (prefixPartial 12 112941) = false := by
  decide +kernel

theorem node_context_12_112941_880364 : EJMOriginalGlobalDAGData.nodes 9 ⟨880364, by decide⟩ =
    .split (coordinate 12) (![⟨880312, by decide⟩,⟨880337, by decide⟩,⟨880353, by decide⟩,⟨880363, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_112941_880364 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112941 ⟨880364, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 112941
    ⟨880364, by decide⟩ (by decide) (![⟨880312, by decide⟩,⟨880337, by decide⟩,⟨880353, by decide⟩,⟨880363, by decide⟩]) unmarked_context_12_112941_880364 node_context_12_112941_880364
  intro a
  fin_cases a
  · exact context_13_451764_880312
  · exact context_13_451765_880337
  · exact context_13_451766_880353
  · exact context_13_451767_880363

theorem selected_cut_34099 : selected 8 ⟨880375, by decide⟩
    (prefixPartial 13 451768) = some ⟨13, 2, 0, 880375, 451768, 825, 16384⟩ := by
  decide +kernel

theorem context_13_451768_880375 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 451768 ⟨880375, by decide⟩ :=
  accepted_of_selected 13 451768 ⟨880375, by decide⟩ ⟨13, 2, 0, 880375, 451768, 825, 16384⟩
    (by decide) selected_cut_34099

theorem selected_cut_34100 : selected 8 ⟨880404, by decide⟩
    (prefixPartial 13 451769) = some ⟨13, 2, 0, 880404, 451769, 2229, 16384⟩ := by
  decide +kernel

theorem context_13_451769_880404 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 451769 ⟨880404, by decide⟩ :=
  accepted_of_selected 13 451769 ⟨880404, by decide⟩ ⟨13, 2, 0, 880404, 451769, 2229, 16384⟩
    (by decide) selected_cut_34100

theorem selected_cut_34101 : selected 8 ⟨880422, by decide⟩
    (prefixPartial 13 451770) = some ⟨13, 2, 0, 880422, 451770, 1045, 16384⟩ := by
  decide +kernel

theorem context_13_451770_880422 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 451770 ⟨880422, by decide⟩ :=
  accepted_of_selected 13 451770 ⟨880422, by decide⟩ ⟨13, 2, 0, 880422, 451770, 1045, 16384⟩
    (by decide) selected_cut_34101

theorem selected_cut_34102 : selected 8 ⟨880428, by decide⟩
    (prefixPartial 13 451771) = some ⟨13, 2, 0, 880428, 451771, 981, 16384⟩ := by
  decide +kernel

theorem context_13_451771_880428 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 451771 ⟨880428, by decide⟩ :=
  accepted_of_selected 13 451771 ⟨880428, by decide⟩ ⟨13, 2, 0, 880428, 451771, 981, 16384⟩
    (by decide) selected_cut_34102

theorem unmarked_context_12_112942_880429 : frontier 9 ⟨880429, by decide⟩
    (prefixCache 12 112942) (prefixPartial 12 112942) = false := by
  decide +kernel

theorem node_context_12_112942_880429 : EJMOriginalGlobalDAGData.nodes 9 ⟨880429, by decide⟩ =
    .split (coordinate 12) (![⟨880375, by decide⟩,⟨880404, by decide⟩,⟨880422, by decide⟩,⟨880428, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_112942_880429 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112942 ⟨880429, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 112942
    ⟨880429, by decide⟩ (by decide) (![⟨880375, by decide⟩,⟨880404, by decide⟩,⟨880422, by decide⟩,⟨880428, by decide⟩]) unmarked_context_12_112942_880429 node_context_12_112942_880429
  intro a
  fin_cases a
  · exact context_13_451768_880375
  · exact context_13_451769_880404
  · exact context_13_451770_880422
  · exact context_13_451771_880428

theorem selected_cut_34103 : selected 8 ⟨880443, by decide⟩
    (prefixPartial 13 451772) = some ⟨13, 2, 0, 880443, 451772, 677, 16384⟩ := by
  decide +kernel

theorem context_13_451772_880443 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 451772 ⟨880443, by decide⟩ :=
  accepted_of_selected 13 451772 ⟨880443, by decide⟩ ⟨13, 2, 0, 880443, 451772, 677, 16384⟩
    (by decide) selected_cut_34103

theorem selected_cut_34104 : selected 8 ⟨880469, by decide⟩
    (prefixPartial 13 451773) = some ⟨13, 2, 0, 880469, 451773, 2089, 16384⟩ := by
  decide +kernel

theorem context_13_451773_880469 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 451773 ⟨880469, by decide⟩ :=
  accepted_of_selected 13 451773 ⟨880469, by decide⟩ ⟨13, 2, 0, 880469, 451773, 2089, 16384⟩
    (by decide) selected_cut_34104

theorem selected_cut_34105 : selected 8 ⟨880484, by decide⟩
    (prefixPartial 13 451774) = some ⟨13, 2, 0, 880484, 451774, 929, 16384⟩ := by
  decide +kernel

theorem context_13_451774_880484 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 451774 ⟨880484, by decide⟩ :=
  accepted_of_selected 13 451774 ⟨880484, by decide⟩ ⟨13, 2, 0, 880484, 451774, 929, 16384⟩
    (by decide) selected_cut_34105

theorem selected_cut_34106 : selected 8 ⟨880490, by decide⟩
    (prefixPartial 13 451775) = some ⟨13, 2, 0, 880490, 451775, 885, 16384⟩ := by
  decide +kernel

theorem context_13_451775_880490 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 451775 ⟨880490, by decide⟩ :=
  accepted_of_selected 13 451775 ⟨880490, by decide⟩ ⟨13, 2, 0, 880490, 451775, 885, 16384⟩
    (by decide) selected_cut_34106

theorem unmarked_context_12_112943_880491 : frontier 9 ⟨880491, by decide⟩
    (prefixCache 12 112943) (prefixPartial 12 112943) = false := by
  decide +kernel

theorem node_context_12_112943_880491 : EJMOriginalGlobalDAGData.nodes 9 ⟨880491, by decide⟩ =
    .split (coordinate 12) (![⟨880443, by decide⟩,⟨880469, by decide⟩,⟨880484, by decide⟩,⟨880490, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_112943_880491 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112943 ⟨880491, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 112943
    ⟨880491, by decide⟩ (by decide) (![⟨880443, by decide⟩,⟨880469, by decide⟩,⟨880484, by decide⟩,⟨880490, by decide⟩]) unmarked_context_12_112943_880491 node_context_12_112943_880491
  intro a
  fin_cases a
  · exact context_13_451772_880443
  · exact context_13_451773_880469
  · exact context_13_451774_880484
  · exact context_13_451775_880490

theorem unmarked_context_11_28235_880492 : frontier 10 ⟨880492, by decide⟩
    (prefixCache 11 28235) (prefixPartial 11 28235) = false := by
  decide +kernel

theorem node_context_11_28235_880492 : EJMOriginalGlobalDAGData.nodes 10 ⟨880492, by decide⟩ =
    .split (coordinate 11) (![⟨880299, by decide⟩,⟨880364, by decide⟩,⟨880429, by decide⟩,⟨880491, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_28235_880492 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 28235 ⟨880492, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 28235
    ⟨880492, by decide⟩ (by decide) (![⟨880299, by decide⟩,⟨880364, by decide⟩,⟨880429, by decide⟩,⟨880491, by decide⟩]) unmarked_context_11_28235_880492 node_context_11_28235_880492
  intro a
  fin_cases a
  · exact context_12_112940_880299
  · exact context_12_112941_880364
  · exact context_12_112942_880429
  · exact context_12_112943_880491

theorem unmarked_context_10_7058_880493 : frontier 11 ⟨880493, by decide⟩
    (prefixCache 10 7058) (prefixPartial 10 7058) = false := by
  decide +kernel

theorem node_context_10_7058_880493 : EJMOriginalGlobalDAGData.nodes 11 ⟨880493, by decide⟩ =
    .split (coordinate 10) (![⟨880048, by decide⟩,⟨880232, by decide⟩,⟨766338, by decide⟩,⟨880492, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_7058_880493 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 7058 ⟨880493, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 7058
    ⟨880493, by decide⟩ (by decide) (![⟨880048, by decide⟩,⟨880232, by decide⟩,⟨766338, by decide⟩,⟨880492, by decide⟩]) unmarked_context_10_7058_880493 node_context_10_7058_880493
  intro a
  fin_cases a
  · exact context_11_28232_880048
  · exact context_11_28233_880232
  · exact context_11_28234_766338
  · exact context_11_28235_880492

theorem selected_cut_34107 : selected 8 ⟨880513, by decide⟩
    (prefixPartial 13 451776) = some ⟨13, 2, 0, 880513, 451776, 833, 16384⟩ := by
  decide +kernel

theorem context_13_451776_880513 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 451776 ⟨880513, by decide⟩ :=
  accepted_of_selected 13 451776 ⟨880513, by decide⟩ ⟨13, 2, 0, 880513, 451776, 833, 16384⟩
    (by decide) selected_cut_34107

theorem selected_cut_34108 : selected 8 ⟨880537, by decide⟩
    (prefixPartial 13 451777) = some ⟨13, 2, 0, 880537, 451777, 1789, 16384⟩ := by
  decide +kernel

theorem context_13_451777_880537 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 451777 ⟨880537, by decide⟩ :=
  accepted_of_selected 13 451777 ⟨880537, by decide⟩ ⟨13, 2, 0, 880537, 451777, 1789, 16384⟩
    (by decide) selected_cut_34108

theorem selected_cut_34109 : selected 8 ⟨880553, by decide⟩
    (prefixPartial 13 451778) = some ⟨13, 2, 0, 880553, 451778, 941, 16384⟩ := by
  decide +kernel

theorem context_13_451778_880553 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 451778 ⟨880553, by decide⟩ :=
  accepted_of_selected 13 451778 ⟨880553, by decide⟩ ⟨13, 2, 0, 880553, 451778, 941, 16384⟩
    (by decide) selected_cut_34109

theorem selected_cut_34110 : selected 8 ⟨880558, by decide⟩
    (prefixPartial 13 451779) = some ⟨13, 2, 0, 880558, 451779, 609, 16384⟩ := by
  decide +kernel

theorem context_13_451779_880558 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 451779 ⟨880558, by decide⟩ :=
  accepted_of_selected 13 451779 ⟨880558, by decide⟩ ⟨13, 2, 0, 880558, 451779, 609, 16384⟩
    (by decide) selected_cut_34110

theorem unmarked_context_12_112944_880559 : frontier 9 ⟨880559, by decide⟩
    (prefixCache 12 112944) (prefixPartial 12 112944) = false := by
  decide +kernel

theorem node_context_12_112944_880559 : EJMOriginalGlobalDAGData.nodes 9 ⟨880559, by decide⟩ =
    .split (coordinate 12) (![⟨880513, by decide⟩,⟨880537, by decide⟩,⟨880553, by decide⟩,⟨880558, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_112944_880559 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112944 ⟨880559, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 112944
    ⟨880559, by decide⟩ (by decide) (![⟨880513, by decide⟩,⟨880537, by decide⟩,⟨880553, by decide⟩,⟨880558, by decide⟩]) unmarked_context_12_112944_880559 node_context_12_112944_880559
  intro a
  fin_cases a
  · exact context_13_451776_880513
  · exact context_13_451777_880537
  · exact context_13_451778_880553
  · exact context_13_451779_880558

theorem selected_cut_34111 : selected 8 ⟨880566, by decide⟩
    (prefixPartial 13 451780) = some ⟨13, 2, 0, 880566, 451780, 725, 16384⟩ := by
  decide +kernel

theorem context_13_451780_880566 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 451780 ⟨880566, by decide⟩ :=
  accepted_of_selected 13 451780 ⟨880566, by decide⟩ ⟨13, 2, 0, 880566, 451780, 725, 16384⟩
    (by decide) selected_cut_34111

theorem selected_cut_34112 : selected 8 ⟨880589, by decide⟩
    (prefixPartial 13 451781) = some ⟨13, 2, 0, 880589, 451781, 2093, 16384⟩ := by
  decide +kernel

theorem context_13_451781_880589 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 451781 ⟨880589, by decide⟩ :=
  accepted_of_selected 13 451781 ⟨880589, by decide⟩ ⟨13, 2, 0, 880589, 451781, 2093, 16384⟩
    (by decide) selected_cut_34112

theorem selected_cut_34113 : selected 8 ⟨880606, by decide⟩
    (prefixPartial 13 451782) = some ⟨13, 2, 0, 880606, 451782, 973, 16384⟩ := by
  decide +kernel

theorem context_13_451782_880606 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 451782 ⟨880606, by decide⟩ :=
  accepted_of_selected 13 451782 ⟨880606, by decide⟩ ⟨13, 2, 0, 880606, 451782, 973, 16384⟩
    (by decide) selected_cut_34113

theorem selected_cut_34114 : selected 8 ⟨880612, by decide⟩
    (prefixPartial 13 451783) = some ⟨13, 2, 0, 880612, 451783, 797, 16384⟩ := by
  decide +kernel

theorem context_13_451783_880612 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 451783 ⟨880612, by decide⟩ :=
  accepted_of_selected 13 451783 ⟨880612, by decide⟩ ⟨13, 2, 0, 880612, 451783, 797, 16384⟩
    (by decide) selected_cut_34114

theorem unmarked_context_12_112945_880613 : frontier 9 ⟨880613, by decide⟩
    (prefixCache 12 112945) (prefixPartial 12 112945) = false := by
  decide +kernel

theorem node_context_12_112945_880613 : EJMOriginalGlobalDAGData.nodes 9 ⟨880613, by decide⟩ =
    .split (coordinate 12) (![⟨880566, by decide⟩,⟨880589, by decide⟩,⟨880606, by decide⟩,⟨880612, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_112945_880613 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112945 ⟨880613, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 112945
    ⟨880613, by decide⟩ (by decide) (![⟨880566, by decide⟩,⟨880589, by decide⟩,⟨880606, by decide⟩,⟨880612, by decide⟩]) unmarked_context_12_112945_880613 node_context_12_112945_880613
  intro a
  fin_cases a
  · exact context_13_451780_880566
  · exact context_13_451781_880589
  · exact context_13_451782_880606
  · exact context_13_451783_880612

theorem selected_cut_34115 : selected 8 ⟨880624, by decide⟩
    (prefixPartial 13 451784) = some ⟨13, 2, 0, 880624, 451784, 713, 16384⟩ := by
  decide +kernel

theorem context_13_451784_880624 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 451784 ⟨880624, by decide⟩ :=
  accepted_of_selected 13 451784 ⟨880624, by decide⟩ ⟨13, 2, 0, 880624, 451784, 713, 16384⟩
    (by decide) selected_cut_34115

theorem selected_cut_34116 : selected 8 ⟨880650, by decide⟩
    (prefixPartial 13 451785) = some ⟨13, 2, 0, 880650, 451785, 1857, 16384⟩ := by
  decide +kernel

theorem context_13_451785_880650 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 451785 ⟨880650, by decide⟩ :=
  accepted_of_selected 13 451785 ⟨880650, by decide⟩ ⟨13, 2, 0, 880650, 451785, 1857, 16384⟩
    (by decide) selected_cut_34116

theorem selected_cut_34117 : selected 8 ⟨880669, by decide⟩
    (prefixPartial 13 451786) = some ⟨13, 2, 0, 880669, 451786, 1061, 16384⟩ := by
  decide +kernel

theorem context_13_451786_880669 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 451786 ⟨880669, by decide⟩ :=
  accepted_of_selected 13 451786 ⟨880669, by decide⟩ ⟨13, 2, 0, 880669, 451786, 1061, 16384⟩
    (by decide) selected_cut_34117

theorem selected_cut_34118 : selected 8 ⟨880674, by decide⟩
    (prefixPartial 13 451787) = some ⟨13, 2, 0, 880674, 451787, 697, 16384⟩ := by
  decide +kernel

theorem context_13_451787_880674 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 451787 ⟨880674, by decide⟩ :=
  accepted_of_selected 13 451787 ⟨880674, by decide⟩ ⟨13, 2, 0, 880674, 451787, 697, 16384⟩
    (by decide) selected_cut_34118

theorem unmarked_context_12_112946_880675 : frontier 9 ⟨880675, by decide⟩
    (prefixCache 12 112946) (prefixPartial 12 112946) = false := by
  decide +kernel

theorem node_context_12_112946_880675 : EJMOriginalGlobalDAGData.nodes 9 ⟨880675, by decide⟩ =
    .split (coordinate 12) (![⟨880624, by decide⟩,⟨880650, by decide⟩,⟨880669, by decide⟩,⟨880674, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_112946_880675 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112946 ⟨880675, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 112946
    ⟨880675, by decide⟩ (by decide) (![⟨880624, by decide⟩,⟨880650, by decide⟩,⟨880669, by decide⟩,⟨880674, by decide⟩]) unmarked_context_12_112946_880675 node_context_12_112946_880675
  intro a
  fin_cases a
  · exact context_13_451784_880624
  · exact context_13_451785_880650
  · exact context_13_451786_880669
  · exact context_13_451787_880674

theorem selected_cut_34119 : selected 8 ⟨880687, by decide⟩
    (prefixPartial 13 451788) = some ⟨13, 2, 0, 880687, 451788, 725, 16384⟩ := by
  decide +kernel

theorem context_13_451788_880687 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 451788 ⟨880687, by decide⟩ :=
  accepted_of_selected 13 451788 ⟨880687, by decide⟩ ⟨13, 2, 0, 880687, 451788, 725, 16384⟩
    (by decide) selected_cut_34119

theorem selected_cut_34120 : selected 8 ⟨880712, by decide⟩
    (prefixPartial 13 451789) = some ⟨13, 2, 0, 880712, 451789, 2101, 16384⟩ := by
  decide +kernel

theorem context_13_451789_880712 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 451789 ⟨880712, by decide⟩ :=
  accepted_of_selected 13 451789 ⟨880712, by decide⟩ ⟨13, 2, 0, 880712, 451789, 2101, 16384⟩
    (by decide) selected_cut_34120

theorem selected_cut_34121 : selected 8 ⟨880729, by decide⟩
    (prefixPartial 13 451790) = some ⟨13, 2, 0, 880729, 451790, 1025, 16384⟩ := by
  decide +kernel

theorem context_13_451790_880729 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 451790 ⟨880729, by decide⟩ :=
  accepted_of_selected 13 451790 ⟨880729, by decide⟩ ⟨13, 2, 0, 880729, 451790, 1025, 16384⟩
    (by decide) selected_cut_34121

theorem selected_cut_34122 : selected 8 ⟨880734, by decide⟩
    (prefixPartial 13 451791) = some ⟨13, 2, 0, 880734, 451791, 729, 16384⟩ := by
  decide +kernel

theorem context_13_451791_880734 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 451791 ⟨880734, by decide⟩ :=
  accepted_of_selected 13 451791 ⟨880734, by decide⟩ ⟨13, 2, 0, 880734, 451791, 729, 16384⟩
    (by decide) selected_cut_34122

theorem unmarked_context_12_112947_880735 : frontier 9 ⟨880735, by decide⟩
    (prefixCache 12 112947) (prefixPartial 12 112947) = false := by
  decide +kernel

theorem node_context_12_112947_880735 : EJMOriginalGlobalDAGData.nodes 9 ⟨880735, by decide⟩ =
    .split (coordinate 12) (![⟨880687, by decide⟩,⟨880712, by decide⟩,⟨880729, by decide⟩,⟨880734, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_112947_880735 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112947 ⟨880735, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 112947
    ⟨880735, by decide⟩ (by decide) (![⟨880687, by decide⟩,⟨880712, by decide⟩,⟨880729, by decide⟩,⟨880734, by decide⟩]) unmarked_context_12_112947_880735 node_context_12_112947_880735
  intro a
  fin_cases a
  · exact context_13_451788_880687
  · exact context_13_451789_880712
  · exact context_13_451790_880729
  · exact context_13_451791_880734

theorem unmarked_context_11_28236_880736 : frontier 10 ⟨880736, by decide⟩
    (prefixCache 11 28236) (prefixPartial 11 28236) = false := by
  decide +kernel

theorem node_context_11_28236_880736 : EJMOriginalGlobalDAGData.nodes 10 ⟨880736, by decide⟩ =
    .split (coordinate 11) (![⟨880559, by decide⟩,⟨880613, by decide⟩,⟨880675, by decide⟩,⟨880735, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_28236_880736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 28236 ⟨880736, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 28236
    ⟨880736, by decide⟩ (by decide) (![⟨880559, by decide⟩,⟨880613, by decide⟩,⟨880675, by decide⟩,⟨880735, by decide⟩]) unmarked_context_11_28236_880736 node_context_11_28236_880736
  intro a
  fin_cases a
  · exact context_12_112944_880559
  · exact context_12_112945_880613
  · exact context_12_112946_880675
  · exact context_12_112947_880735

theorem selected_cut_34123 : selected 9 ⟨880789, by decide⟩
    (prefixPartial 12 112948) = some ⟨12, 2, 0, 880789, 112948, 3537, 65536⟩ := by
  decide +kernel

theorem context_12_112948_880789 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112948 ⟨880789, by decide⟩ :=
  accepted_of_selected 12 112948 ⟨880789, by decide⟩ ⟨12, 2, 0, 880789, 112948, 3537, 65536⟩
    (by decide) selected_cut_34123

theorem selected_cut_34124 : selected 9 ⟨880948, by decide⟩
    (prefixPartial 12 112949) = some ⟨12, 2, 0, 880948, 112949, 3809, 65536⟩ := by
  decide +kernel

theorem context_12_112949_880948 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112949 ⟨880948, by decide⟩ :=
  accepted_of_selected 12 112949 ⟨880948, by decide⟩ ⟨12, 2, 0, 880948, 112949, 3809, 65536⟩
    (by decide) selected_cut_34124

theorem selected_cut_34125 : selected 9 ⟨881004, by decide⟩
    (prefixPartial 12 112950) = some ⟨12, 2, 0, 881004, 112950, 3625, 65536⟩ := by
  decide +kernel

theorem context_12_112950_881004 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112950 ⟨881004, by decide⟩ :=
  accepted_of_selected 12 112950 ⟨881004, by decide⟩ ⟨12, 2, 0, 881004, 112950, 3625, 65536⟩
    (by decide) selected_cut_34125

theorem selected_cut_34126 : selected 9 ⟨881063, by decide⟩
    (prefixPartial 12 112951) = some ⟨12, 2, 0, 881063, 112951, 3841, 65536⟩ := by
  decide +kernel

theorem context_12_112951_881063 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112951 ⟨881063, by decide⟩ :=
  accepted_of_selected 12 112951 ⟨881063, by decide⟩ ⟨12, 2, 0, 881063, 112951, 3841, 65536⟩
    (by decide) selected_cut_34126

theorem unmarked_context_11_28237_881064 : frontier 10 ⟨881064, by decide⟩
    (prefixCache 11 28237) (prefixPartial 11 28237) = false := by
  decide +kernel

theorem node_context_11_28237_881064 : EJMOriginalGlobalDAGData.nodes 10 ⟨881064, by decide⟩ =
    .split (coordinate 11) (![⟨880789, by decide⟩,⟨880948, by decide⟩,⟨881004, by decide⟩,⟨881063, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_28237_881064 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 28237 ⟨881064, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 28237
    ⟨881064, by decide⟩ (by decide) (![⟨880789, by decide⟩,⟨880948, by decide⟩,⟨881004, by decide⟩,⟨881063, by decide⟩]) unmarked_context_11_28237_881064 node_context_11_28237_881064
  intro a
  fin_cases a
  · exact context_12_112948_880789
  · exact context_12_112949_880948
  · exact context_12_112950_881004
  · exact context_12_112951_881063

theorem selected_cut_34127 : selected 9 ⟨881117, by decide⟩
    (prefixPartial 12 112952) = some ⟨12, 2, 0, 881117, 112952, 3761, 65536⟩ := by
  decide +kernel

theorem context_12_112952_881117 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112952 ⟨881117, by decide⟩ :=
  accepted_of_selected 12 112952 ⟨881117, by decide⟩ ⟨12, 2, 0, 881117, 112952, 3761, 65536⟩
    (by decide) selected_cut_34127

theorem selected_cut_34128 : selected 9 ⟨881167, by decide⟩
    (prefixPartial 12 112953) = some ⟨12, 2, 0, 881167, 112953, 4001, 65536⟩ := by
  decide +kernel

theorem context_12_112953_881167 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112953 ⟨881167, by decide⟩ :=
  accepted_of_selected 12 112953 ⟨881167, by decide⟩ ⟨12, 2, 0, 881167, 112953, 4001, 65536⟩
    (by decide) selected_cut_34128

theorem selected_cut_34129 : selected 9 ⟨881219, by decide⟩
    (prefixPartial 12 112954) = some ⟨12, 2, 0, 881219, 112954, 3821, 65536⟩ := by
  decide +kernel

theorem context_12_112954_881219 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112954 ⟨881219, by decide⟩ :=
  accepted_of_selected 12 112954 ⟨881219, by decide⟩ ⟨12, 2, 0, 881219, 112954, 3821, 65536⟩
    (by decide) selected_cut_34129

theorem selected_cut_34130 : selected 9 ⟨881266, by decide⟩
    (prefixPartial 12 112955) = some ⟨12, 2, 0, 881266, 112955, 3849, 65536⟩ := by
  decide +kernel

theorem context_12_112955_881266 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112955 ⟨881266, by decide⟩ :=
  accepted_of_selected 12 112955 ⟨881266, by decide⟩ ⟨12, 2, 0, 881266, 112955, 3849, 65536⟩
    (by decide) selected_cut_34130

theorem unmarked_context_11_28238_881267 : frontier 10 ⟨881267, by decide⟩
    (prefixCache 11 28238) (prefixPartial 11 28238) = false := by
  decide +kernel

theorem node_context_11_28238_881267 : EJMOriginalGlobalDAGData.nodes 10 ⟨881267, by decide⟩ =
    .split (coordinate 11) (![⟨881117, by decide⟩,⟨881167, by decide⟩,⟨881219, by decide⟩,⟨881266, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_28238_881267 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 28238 ⟨881267, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 28238
    ⟨881267, by decide⟩ (by decide) (![⟨881117, by decide⟩,⟨881167, by decide⟩,⟨881219, by decide⟩,⟨881266, by decide⟩]) unmarked_context_11_28238_881267 node_context_11_28238_881267
  intro a
  fin_cases a
  · exact context_12_112952_881117
  · exact context_12_112953_881167
  · exact context_12_112954_881219
  · exact context_12_112955_881266

theorem selected_cut_34131 : selected 9 ⟨881315, by decide⟩
    (prefixPartial 12 112956) = some ⟨12, 2, 0, 881315, 112956, 3789, 65536⟩ := by
  decide +kernel

theorem context_12_112956_881315 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112956 ⟨881315, by decide⟩ :=
  accepted_of_selected 12 112956 ⟨881315, by decide⟩ ⟨12, 2, 0, 881315, 112956, 3789, 65536⟩
    (by decide) selected_cut_34131

theorem selected_cut_34132 : selected 8 ⟨881318, by decide⟩
    (prefixPartial 13 451828) = some ⟨13, 2, 0, 881318, 451828, 97, 16384⟩ := by
  decide +kernel

theorem context_13_451828_881318 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 451828 ⟨881318, by decide⟩ :=
  accepted_of_selected 13 451828 ⟨881318, by decide⟩ ⟨13, 2, 0, 881318, 451828, 97, 16384⟩
    (by decide) selected_cut_34132

theorem selected_cut_34133 : selected 8 ⟨881342, by decide⟩
    (prefixPartial 13 451829) = some ⟨13, 2, 0, 881342, 451829, 2005, 16384⟩ := by
  decide +kernel

theorem context_13_451829_881342 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 451829 ⟨881342, by decide⟩ :=
  accepted_of_selected 13 451829 ⟨881342, by decide⟩ ⟨13, 2, 0, 881342, 451829, 2005, 16384⟩
    (by decide) selected_cut_34133

theorem selected_cut_34134 : selected 8 ⟨881363, by decide⟩
    (prefixPartial 13 451830) = some ⟨13, 2, 0, 881363, 451830, 1185, 16384⟩ := by
  decide +kernel

theorem context_13_451830_881363 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 451830 ⟨881363, by decide⟩ :=
  accepted_of_selected 13 451830 ⟨881363, by decide⟩ ⟨13, 2, 0, 881363, 451830, 1185, 16384⟩
    (by decide) selected_cut_34134

theorem selected_cut_34135 : selected 8 ⟨881370, by decide⟩
    (prefixPartial 13 451831) = some ⟨13, 2, 0, 881370, 451831, 937, 16384⟩ := by
  decide +kernel

theorem context_13_451831_881370 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 451831 ⟨881370, by decide⟩ :=
  accepted_of_selected 13 451831 ⟨881370, by decide⟩ ⟨13, 2, 0, 881370, 451831, 937, 16384⟩
    (by decide) selected_cut_34135

theorem unmarked_context_12_112957_881371 : frontier 9 ⟨881371, by decide⟩
    (prefixCache 12 112957) (prefixPartial 12 112957) = false := by
  decide +kernel

theorem node_context_12_112957_881371 : EJMOriginalGlobalDAGData.nodes 9 ⟨881371, by decide⟩ =
    .split (coordinate 12) (![⟨881318, by decide⟩,⟨881342, by decide⟩,⟨881363, by decide⟩,⟨881370, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_112957_881371 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112957 ⟨881371, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 112957
    ⟨881371, by decide⟩ (by decide) (![⟨881318, by decide⟩,⟨881342, by decide⟩,⟨881363, by decide⟩,⟨881370, by decide⟩]) unmarked_context_12_112957_881371 node_context_12_112957_881371
  intro a
  fin_cases a
  · exact context_13_451828_881318
  · exact context_13_451829_881342
  · exact context_13_451830_881363
  · exact context_13_451831_881370

theorem selected_cut_34136 : selected 9 ⟨881428, by decide⟩
    (prefixPartial 12 112958) = some ⟨12, 2, 0, 881428, 112958, 4033, 65536⟩ := by
  decide +kernel

theorem context_12_112958_881428 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112958 ⟨881428, by decide⟩ :=
  accepted_of_selected 12 112958 ⟨881428, by decide⟩ ⟨12, 2, 0, 881428, 112958, 4033, 65536⟩
    (by decide) selected_cut_34136

theorem selected_cut_34137 : selected 9 ⟨881473, by decide⟩
    (prefixPartial 12 112959) = some ⟨12, 2, 0, 881473, 112959, 4005, 65536⟩ := by
  decide +kernel

theorem context_12_112959_881473 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112959 ⟨881473, by decide⟩ :=
  accepted_of_selected 12 112959 ⟨881473, by decide⟩ ⟨12, 2, 0, 881473, 112959, 4005, 65536⟩
    (by decide) selected_cut_34137

theorem unmarked_context_11_28239_881474 : frontier 10 ⟨881474, by decide⟩
    (prefixCache 11 28239) (prefixPartial 11 28239) = false := by
  decide +kernel

theorem node_context_11_28239_881474 : EJMOriginalGlobalDAGData.nodes 10 ⟨881474, by decide⟩ =
    .split (coordinate 11) (![⟨881315, by decide⟩,⟨881371, by decide⟩,⟨881428, by decide⟩,⟨881473, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_28239_881474 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 28239 ⟨881474, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 28239
    ⟨881474, by decide⟩ (by decide) (![⟨881315, by decide⟩,⟨881371, by decide⟩,⟨881428, by decide⟩,⟨881473, by decide⟩]) unmarked_context_11_28239_881474 node_context_11_28239_881474
  intro a
  fin_cases a
  · exact context_12_112956_881315
  · exact context_12_112957_881371
  · exact context_12_112958_881428
  · exact context_12_112959_881473

theorem unmarked_context_10_7059_881475 : frontier 11 ⟨881475, by decide⟩
    (prefixCache 10 7059) (prefixPartial 10 7059) = false := by
  decide +kernel

theorem node_context_10_7059_881475 : EJMOriginalGlobalDAGData.nodes 11 ⟨881475, by decide⟩ =
    .split (coordinate 10) (![⟨880736, by decide⟩,⟨881064, by decide⟩,⟨881267, by decide⟩,⟨881474, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_7059_881475 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 7059 ⟨881475, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 7059
    ⟨881475, by decide⟩ (by decide) (![⟨880736, by decide⟩,⟨881064, by decide⟩,⟨881267, by decide⟩,⟨881474, by decide⟩]) unmarked_context_10_7059_881475 node_context_10_7059_881475
  intro a
  fin_cases a
  · exact context_11_28236_880736
  · exact context_11_28237_881064
  · exact context_11_28238_881267
  · exact context_11_28239_881474

theorem unmarked_context_9_1764_881476 : frontier 12 ⟨881476, by decide⟩
    (prefixCache 9 1764) (prefixPartial 9 1764) = false := by
  decide +kernel

theorem node_context_9_1764_881476 : EJMOriginalGlobalDAGData.nodes 12 ⟨881476, by decide⟩ =
    .split (coordinate 9) (![⟨878652, by decide⟩,⟨879793, by decide⟩,⟨880493, by decide⟩,⟨881475, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1764_881476 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1764 ⟨881476, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1764
    ⟨881476, by decide⟩ (by decide) (![⟨878652, by decide⟩,⟨879793, by decide⟩,⟨880493, by decide⟩,⟨881475, by decide⟩]) unmarked_context_9_1764_881476 node_context_9_1764_881476
  intro a
  fin_cases a
  · exact context_10_7056_878652
  · exact context_10_7057_879793
  · exact context_10_7058_880493
  · exact context_10_7059_881475

theorem selected_cut_34138 : selected 9 ⟨881522, by decide⟩
    (prefixPartial 12 112960) = some ⟨12, 2, 0, 881522, 112960, 3565, 65536⟩ := by
  decide +kernel

theorem context_12_112960_881522 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112960 ⟨881522, by decide⟩ :=
  accepted_of_selected 12 112960 ⟨881522, by decide⟩ ⟨12, 2, 0, 881522, 112960, 3565, 65536⟩
    (by decide) selected_cut_34138

theorem selected_cut_34139 : selected 9 ⟨881568, by decide⟩
    (prefixPartial 12 112961) = some ⟨12, 2, 0, 881568, 112961, 3277, 65536⟩ := by
  decide +kernel

theorem context_12_112961_881568 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112961 ⟨881568, by decide⟩ :=
  accepted_of_selected 12 112961 ⟨881568, by decide⟩ ⟨12, 2, 0, 881568, 112961, 3277, 65536⟩
    (by decide) selected_cut_34139

theorem selected_cut_34140 : selected 9 ⟨881616, by decide⟩
    (prefixPartial 12 112962) = some ⟨12, 2, 0, 881616, 112962, 3609, 65536⟩ := by
  decide +kernel

theorem context_12_112962_881616 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112962 ⟨881616, by decide⟩ :=
  accepted_of_selected 12 112962 ⟨881616, by decide⟩ ⟨12, 2, 0, 881616, 112962, 3609, 65536⟩
    (by decide) selected_cut_34140

theorem selected_cut_34141 : selected 9 ⟨881666, by decide⟩
    (prefixPartial 12 112963) = some ⟨12, 2, 0, 881666, 112963, 3745, 65536⟩ := by
  decide +kernel

theorem context_12_112963_881666 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112963 ⟨881666, by decide⟩ :=
  accepted_of_selected 12 112963 ⟨881666, by decide⟩ ⟨12, 2, 0, 881666, 112963, 3745, 65536⟩
    (by decide) selected_cut_34141

theorem unmarked_context_11_28240_881667 : frontier 10 ⟨881667, by decide⟩
    (prefixCache 11 28240) (prefixPartial 11 28240) = false := by
  decide +kernel

theorem node_context_11_28240_881667 : EJMOriginalGlobalDAGData.nodes 10 ⟨881667, by decide⟩ =
    .split (coordinate 11) (![⟨881522, by decide⟩,⟨881568, by decide⟩,⟨881616, by decide⟩,⟨881666, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_28240_881667 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 28240 ⟨881667, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 28240
    ⟨881667, by decide⟩ (by decide) (![⟨881522, by decide⟩,⟨881568, by decide⟩,⟨881616, by decide⟩,⟨881666, by decide⟩]) unmarked_context_11_28240_881667 node_context_11_28240_881667
  intro a
  fin_cases a
  · exact context_12_112960_881522
  · exact context_12_112961_881568
  · exact context_12_112962_881616
  · exact context_12_112963_881666

theorem selected_cut_34142 : selected 9 ⟨881705, by decide⟩
    (prefixPartial 12 112964) = some ⟨12, 2, 0, 881705, 112964, 3161, 65536⟩ := by
  decide +kernel

theorem context_12_112964_881705 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112964 ⟨881705, by decide⟩ :=
  accepted_of_selected 12 112964 ⟨881705, by decide⟩ ⟨12, 2, 0, 881705, 112964, 3161, 65536⟩
    (by decide) selected_cut_34142

theorem selected_cut_34143 : selected 9 ⟨275013, by decide⟩
    (prefixPartial 12 112965) = some ⟨12, 1, 0, 275013, 112965, 1, 65536⟩ := by
  decide +kernel

theorem context_12_112965_275013 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112965 ⟨275013, by decide⟩ :=
  accepted_of_selected 12 112965 ⟨275013, by decide⟩ ⟨12, 1, 0, 275013, 112965, 1, 65536⟩
    (by decide) selected_cut_34143

theorem selected_cut_34144 : selected 9 ⟨881754, by decide⟩
    (prefixPartial 12 112966) = some ⟨12, 2, 0, 881754, 112966, 3249, 65536⟩ := by
  decide +kernel

theorem context_12_112966_881754 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112966 ⟨881754, by decide⟩ :=
  accepted_of_selected 12 112966 ⟨881754, by decide⟩ ⟨12, 2, 0, 881754, 112966, 3249, 65536⟩
    (by decide) selected_cut_34144

theorem selected_cut_34145 : selected 9 ⟨881796, by decide⟩
    (prefixPartial 12 112967) = some ⟨12, 2, 0, 881796, 112967, 3217, 65536⟩ := by
  decide +kernel

theorem context_12_112967_881796 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112967 ⟨881796, by decide⟩ :=
  accepted_of_selected 12 112967 ⟨881796, by decide⟩ ⟨12, 2, 0, 881796, 112967, 3217, 65536⟩
    (by decide) selected_cut_34145

theorem unmarked_context_11_28241_881797 : frontier 10 ⟨881797, by decide⟩
    (prefixCache 11 28241) (prefixPartial 11 28241) = false := by
  decide +kernel

theorem node_context_11_28241_881797 : EJMOriginalGlobalDAGData.nodes 10 ⟨881797, by decide⟩ =
    .split (coordinate 11) (![⟨881705, by decide⟩,⟨275013, by decide⟩,⟨881754, by decide⟩,⟨881796, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_28241_881797 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 28241 ⟨881797, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 28241
    ⟨881797, by decide⟩ (by decide) (![⟨881705, by decide⟩,⟨275013, by decide⟩,⟨881754, by decide⟩,⟨881796, by decide⟩]) unmarked_context_11_28241_881797 node_context_11_28241_881797
  intro a
  fin_cases a
  · exact context_12_112964_881705
  · exact context_12_112965_275013
  · exact context_12_112966_881754
  · exact context_12_112967_881796

theorem selected_cut_34146 : selected 9 ⟨881844, by decide⟩
    (prefixPartial 12 112968) = some ⟨12, 2, 0, 881844, 112968, 3797, 65536⟩ := by
  decide +kernel

theorem context_12_112968_881844 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112968 ⟨881844, by decide⟩ :=
  accepted_of_selected 12 112968 ⟨881844, by decide⟩ ⟨12, 2, 0, 881844, 112968, 3797, 65536⟩
    (by decide) selected_cut_34146

theorem selected_cut_34147 : selected 9 ⟨881895, by decide⟩
    (prefixPartial 12 112969) = some ⟨12, 2, 0, 881895, 112969, 3353, 65536⟩ := by
  decide +kernel

theorem context_12_112969_881895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112969 ⟨881895, by decide⟩ :=
  accepted_of_selected 12 112969 ⟨881895, by decide⟩ ⟨12, 2, 0, 881895, 112969, 3353, 65536⟩
    (by decide) selected_cut_34147

theorem selected_cut_34148 : selected 9 ⟨881945, by decide⟩
    (prefixPartial 12 112970) = some ⟨12, 2, 0, 881945, 112970, 3757, 65536⟩ := by
  decide +kernel

theorem context_12_112970_881945 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112970 ⟨881945, by decide⟩ :=
  accepted_of_selected 12 112970 ⟨881945, by decide⟩ ⟨12, 2, 0, 881945, 112970, 3757, 65536⟩
    (by decide) selected_cut_34148

theorem selected_cut_34149 : selected 9 ⟨881995, by decide⟩
    (prefixPartial 12 112971) = some ⟨12, 2, 0, 881995, 112971, 3649, 65536⟩ := by
  decide +kernel

theorem context_12_112971_881995 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112971 ⟨881995, by decide⟩ :=
  accepted_of_selected 12 112971 ⟨881995, by decide⟩ ⟨12, 2, 0, 881995, 112971, 3649, 65536⟩
    (by decide) selected_cut_34149

theorem unmarked_context_11_28242_881996 : frontier 10 ⟨881996, by decide⟩
    (prefixCache 11 28242) (prefixPartial 11 28242) = false := by
  decide +kernel

theorem node_context_11_28242_881996 : EJMOriginalGlobalDAGData.nodes 10 ⟨881996, by decide⟩ =
    .split (coordinate 11) (![⟨881844, by decide⟩,⟨881895, by decide⟩,⟨881945, by decide⟩,⟨881995, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_28242_881996 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 28242 ⟨881996, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 28242
    ⟨881996, by decide⟩ (by decide) (![⟨881844, by decide⟩,⟨881895, by decide⟩,⟨881945, by decide⟩,⟨881995, by decide⟩]) unmarked_context_11_28242_881996 node_context_11_28242_881996
  intro a
  fin_cases a
  · exact context_12_112968_881844
  · exact context_12_112969_881895
  · exact context_12_112970_881945
  · exact context_12_112971_881995

theorem selected_cut_34150 : selected 9 ⟨882049, by decide⟩
    (prefixPartial 12 112972) = some ⟨12, 2, 0, 882049, 112972, 3965, 65536⟩ := by
  decide +kernel

theorem context_12_112972_882049 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112972 ⟨882049, by decide⟩ :=
  accepted_of_selected 12 112972 ⟨882049, by decide⟩ ⟨12, 2, 0, 882049, 112972, 3965, 65536⟩
    (by decide) selected_cut_34150

theorem selected_cut_34151 : selected 9 ⟨882098, by decide⟩
    (prefixPartial 12 112973) = some ⟨12, 2, 0, 882098, 112973, 3777, 65536⟩ := by
  decide +kernel

theorem context_12_112973_882098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112973 ⟨882098, by decide⟩ :=
  accepted_of_selected 12 112973 ⟨882098, by decide⟩ ⟨12, 2, 0, 882098, 112973, 3777, 65536⟩
    (by decide) selected_cut_34151

theorem selected_cut_34152 : selected 9 ⟨882153, by decide⟩
    (prefixPartial 12 112974) = some ⟨12, 2, 0, 882153, 112974, 3889, 65536⟩ := by
  decide +kernel

theorem context_12_112974_882153 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112974 ⟨882153, by decide⟩ :=
  accepted_of_selected 12 112974 ⟨882153, by decide⟩ ⟨12, 2, 0, 882153, 112974, 3889, 65536⟩
    (by decide) selected_cut_34152

theorem selected_cut_34153 : selected 9 ⟨882197, by decide⟩
    (prefixPartial 12 112975) = some ⟨12, 2, 0, 882197, 112975, 3849, 65536⟩ := by
  decide +kernel

theorem context_12_112975_882197 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112975 ⟨882197, by decide⟩ :=
  accepted_of_selected 12 112975 ⟨882197, by decide⟩ ⟨12, 2, 0, 882197, 112975, 3849, 65536⟩
    (by decide) selected_cut_34153

theorem unmarked_context_11_28243_882198 : frontier 10 ⟨882198, by decide⟩
    (prefixCache 11 28243) (prefixPartial 11 28243) = false := by
  decide +kernel

theorem node_context_11_28243_882198 : EJMOriginalGlobalDAGData.nodes 10 ⟨882198, by decide⟩ =
    .split (coordinate 11) (![⟨882049, by decide⟩,⟨882098, by decide⟩,⟨882153, by decide⟩,⟨882197, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_28243_882198 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 28243 ⟨882198, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 28243
    ⟨882198, by decide⟩ (by decide) (![⟨882049, by decide⟩,⟨882098, by decide⟩,⟨882153, by decide⟩,⟨882197, by decide⟩]) unmarked_context_11_28243_882198 node_context_11_28243_882198
  intro a
  fin_cases a
  · exact context_12_112972_882049
  · exact context_12_112973_882098
  · exact context_12_112974_882153
  · exact context_12_112975_882197

theorem unmarked_context_10_7060_882199 : frontier 11 ⟨882199, by decide⟩
    (prefixCache 10 7060) (prefixPartial 10 7060) = false := by
  decide +kernel

theorem node_context_10_7060_882199 : EJMOriginalGlobalDAGData.nodes 11 ⟨882199, by decide⟩ =
    .split (coordinate 10) (![⟨881667, by decide⟩,⟨881797, by decide⟩,⟨881996, by decide⟩,⟨882198, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_7060_882199 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 7060 ⟨882199, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 7060
    ⟨882199, by decide⟩ (by decide) (![⟨881667, by decide⟩,⟨881797, by decide⟩,⟨881996, by decide⟩,⟨882198, by decide⟩]) unmarked_context_10_7060_882199 node_context_10_7060_882199
  intro a
  fin_cases a
  · exact context_11_28240_881667
  · exact context_11_28241_881797
  · exact context_11_28242_881996
  · exact context_11_28243_882198

theorem selected_cut_34154 : selected 9 ⟨882236, by decide⟩
    (prefixPartial 12 112976) = some ⟨12, 2, 0, 882236, 112976, 3485, 65536⟩ := by
  decide +kernel

theorem context_12_112976_882236 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112976 ⟨882236, by decide⟩ :=
  accepted_of_selected 12 112976 ⟨882236, by decide⟩ ⟨12, 2, 0, 882236, 112976, 3485, 65536⟩
    (by decide) selected_cut_34154

theorem selected_cut_34155 : selected 9 ⟨882275, by decide⟩
    (prefixPartial 12 112977) = some ⟨12, 2, 0, 882275, 112977, 3733, 65536⟩ := by
  decide +kernel

theorem context_12_112977_882275 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112977 ⟨882275, by decide⟩ :=
  accepted_of_selected 12 112977 ⟨882275, by decide⟩ ⟨12, 2, 0, 882275, 112977, 3733, 65536⟩
    (by decide) selected_cut_34155

theorem selected_cut_34156 : selected 9 ⟨882326, by decide⟩
    (prefixPartial 12 112978) = some ⟨12, 2, 0, 882326, 112978, 3829, 65536⟩ := by
  decide +kernel

theorem context_12_112978_882326 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112978 ⟨882326, by decide⟩ :=
  accepted_of_selected 12 112978 ⟨882326, by decide⟩ ⟨12, 2, 0, 882326, 112978, 3829, 65536⟩
    (by decide) selected_cut_34156

theorem selected_cut_34157 : selected 9 ⟨882369, by decide⟩
    (prefixPartial 12 112979) = some ⟨12, 2, 0, 882369, 112979, 3845, 65536⟩ := by
  decide +kernel

theorem context_12_112979_882369 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112979 ⟨882369, by decide⟩ :=
  accepted_of_selected 12 112979 ⟨882369, by decide⟩ ⟨12, 2, 0, 882369, 112979, 3845, 65536⟩
    (by decide) selected_cut_34157

theorem unmarked_context_11_28244_882370 : frontier 10 ⟨882370, by decide⟩
    (prefixCache 11 28244) (prefixPartial 11 28244) = false := by
  decide +kernel

theorem node_context_11_28244_882370 : EJMOriginalGlobalDAGData.nodes 10 ⟨882370, by decide⟩ =
    .split (coordinate 11) (![⟨882236, by decide⟩,⟨882275, by decide⟩,⟨882326, by decide⟩,⟨882369, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_28244_882370 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 28244 ⟨882370, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 28244
    ⟨882370, by decide⟩ (by decide) (![⟨882236, by decide⟩,⟨882275, by decide⟩,⟨882326, by decide⟩,⟨882369, by decide⟩]) unmarked_context_11_28244_882370 node_context_11_28244_882370
  intro a
  fin_cases a
  · exact context_12_112976_882236
  · exact context_12_112977_882275
  · exact context_12_112978_882326
  · exact context_12_112979_882369

theorem selected_cut_34158 : selected 9 ⟨882404, by decide⟩
    (prefixPartial 12 112980) = some ⟨12, 2, 0, 882404, 112980, 2489, 65536⟩ := by
  decide +kernel

theorem context_12_112980_882404 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112980 ⟨882404, by decide⟩ :=
  accepted_of_selected 12 112980 ⟨882404, by decide⟩ ⟨12, 2, 0, 882404, 112980, 2489, 65536⟩
    (by decide) selected_cut_34158

theorem selected_cut_34159 : selected 9 ⟨439069, by decide⟩
    (prefixPartial 12 112981) = some ⟨12, 1, 0, 439069, 112981, 1, 65536⟩ := by
  decide +kernel

theorem context_12_112981_439069 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112981 ⟨439069, by decide⟩ :=
  accepted_of_selected 12 112981 ⟨439069, by decide⟩ ⟨12, 1, 0, 439069, 112981, 1, 65536⟩
    (by decide) selected_cut_34159

theorem selected_cut_34160 : selected 9 ⟨882444, by decide⟩
    (prefixPartial 12 112982) = some ⟨12, 2, 0, 882444, 112982, 2869, 65536⟩ := by
  decide +kernel

theorem context_12_112982_882444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112982 ⟨882444, by decide⟩ :=
  accepted_of_selected 12 112982 ⟨882444, by decide⟩ ⟨12, 2, 0, 882444, 112982, 2869, 65536⟩
    (by decide) selected_cut_34160

theorem selected_cut_34161 : selected 9 ⟨882482, by decide⟩
    (prefixPartial 12 112983) = some ⟨12, 2, 0, 882482, 112983, 2729, 65536⟩ := by
  decide +kernel

theorem context_12_112983_882482 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112983 ⟨882482, by decide⟩ :=
  accepted_of_selected 12 112983 ⟨882482, by decide⟩ ⟨12, 2, 0, 882482, 112983, 2729, 65536⟩
    (by decide) selected_cut_34161

theorem unmarked_context_11_28245_882483 : frontier 10 ⟨882483, by decide⟩
    (prefixCache 11 28245) (prefixPartial 11 28245) = false := by
  decide +kernel

theorem node_context_11_28245_882483 : EJMOriginalGlobalDAGData.nodes 10 ⟨882483, by decide⟩ =
    .split (coordinate 11) (![⟨882404, by decide⟩,⟨439069, by decide⟩,⟨882444, by decide⟩,⟨882482, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_28245_882483 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 28245 ⟨882483, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 28245
    ⟨882483, by decide⟩ (by decide) (![⟨882404, by decide⟩,⟨439069, by decide⟩,⟨882444, by decide⟩,⟨882482, by decide⟩]) unmarked_context_11_28245_882483 node_context_11_28245_882483
  intro a
  fin_cases a
  · exact context_12_112980_882404
  · exact context_12_112981_439069
  · exact context_12_112982_882444
  · exact context_12_112983_882482

theorem selected_cut_34162 : selected 9 ⟨882522, by decide⟩
    (prefixPartial 12 112984) = some ⟨12, 2, 0, 882522, 112984, 3229, 65536⟩ := by
  decide +kernel

theorem context_12_112984_882522 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112984 ⟨882522, by decide⟩ :=
  accepted_of_selected 12 112984 ⟨882522, by decide⟩ ⟨12, 2, 0, 882522, 112984, 3229, 65536⟩
    (by decide) selected_cut_34162

theorem selected_cut_34163 : selected 9 ⟨882565, by decide⟩
    (prefixPartial 12 112985) = some ⟨12, 2, 0, 882565, 112985, 3329, 65536⟩ := by
  decide +kernel

theorem context_12_112985_882565 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112985 ⟨882565, by decide⟩ :=
  accepted_of_selected 12 112985 ⟨882565, by decide⟩ ⟨12, 2, 0, 882565, 112985, 3329, 65536⟩
    (by decide) selected_cut_34163

theorem selected_cut_34164 : selected 9 ⟨882605, by decide⟩
    (prefixPartial 12 112986) = some ⟨12, 2, 0, 882605, 112986, 3437, 65536⟩ := by
  decide +kernel

theorem context_12_112986_882605 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112986 ⟨882605, by decide⟩ :=
  accepted_of_selected 12 112986 ⟨882605, by decide⟩ ⟨12, 2, 0, 882605, 112986, 3437, 65536⟩
    (by decide) selected_cut_34164

theorem selected_cut_34165 : selected 9 ⟨882645, by decide⟩
    (prefixPartial 12 112987) = some ⟨12, 2, 0, 882645, 112987, 3325, 65536⟩ := by
  decide +kernel

theorem context_12_112987_882645 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112987 ⟨882645, by decide⟩ :=
  accepted_of_selected 12 112987 ⟨882645, by decide⟩ ⟨12, 2, 0, 882645, 112987, 3325, 65536⟩
    (by decide) selected_cut_34165

theorem unmarked_context_11_28246_882646 : frontier 10 ⟨882646, by decide⟩
    (prefixCache 11 28246) (prefixPartial 11 28246) = false := by
  decide +kernel

theorem node_context_11_28246_882646 : EJMOriginalGlobalDAGData.nodes 10 ⟨882646, by decide⟩ =
    .split (coordinate 11) (![⟨882522, by decide⟩,⟨882565, by decide⟩,⟨882605, by decide⟩,⟨882645, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_28246_882646 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 28246 ⟨882646, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 28246
    ⟨882646, by decide⟩ (by decide) (![⟨882522, by decide⟩,⟨882565, by decide⟩,⟨882605, by decide⟩,⟨882645, by decide⟩]) unmarked_context_11_28246_882646 node_context_11_28246_882646
  intro a
  fin_cases a
  · exact context_12_112984_882522
  · exact context_12_112985_882565
  · exact context_12_112986_882605
  · exact context_12_112987_882645

theorem selected_cut_34166 : selected 9 ⟨882690, by decide⟩
    (prefixPartial 12 112988) = some ⟨12, 2, 0, 882690, 112988, 3181, 65536⟩ := by
  decide +kernel

theorem context_12_112988_882690 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112988 ⟨882690, by decide⟩ :=
  accepted_of_selected 12 112988 ⟨882690, by decide⟩ ⟨12, 2, 0, 882690, 112988, 3181, 65536⟩
    (by decide) selected_cut_34166

theorem selected_cut_34167 : selected 9 ⟨882725, by decide⟩
    (prefixPartial 12 112989) = some ⟨12, 2, 0, 882725, 112989, 3345, 65536⟩ := by
  decide +kernel

theorem context_12_112989_882725 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112989 ⟨882725, by decide⟩ :=
  accepted_of_selected 12 112989 ⟨882725, by decide⟩ ⟨12, 2, 0, 882725, 112989, 3345, 65536⟩
    (by decide) selected_cut_34167

theorem selected_cut_34168 : selected 9 ⟨882773, by decide⟩
    (prefixPartial 12 112990) = some ⟨12, 2, 0, 882773, 112990, 3473, 65536⟩ := by
  decide +kernel

theorem context_12_112990_882773 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112990 ⟨882773, by decide⟩ :=
  accepted_of_selected 12 112990 ⟨882773, by decide⟩ ⟨12, 2, 0, 882773, 112990, 3473, 65536⟩
    (by decide) selected_cut_34168

theorem selected_cut_34169 : selected 9 ⟨882815, by decide⟩
    (prefixPartial 12 112991) = some ⟨12, 2, 0, 882815, 112991, 3285, 65536⟩ := by
  decide +kernel

theorem context_12_112991_882815 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112991 ⟨882815, by decide⟩ :=
  accepted_of_selected 12 112991 ⟨882815, by decide⟩ ⟨12, 2, 0, 882815, 112991, 3285, 65536⟩
    (by decide) selected_cut_34169

theorem unmarked_context_11_28247_882816 : frontier 10 ⟨882816, by decide⟩
    (prefixCache 11 28247) (prefixPartial 11 28247) = false := by
  decide +kernel

theorem node_context_11_28247_882816 : EJMOriginalGlobalDAGData.nodes 10 ⟨882816, by decide⟩ =
    .split (coordinate 11) (![⟨882690, by decide⟩,⟨882725, by decide⟩,⟨882773, by decide⟩,⟨882815, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_28247_882816 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 28247 ⟨882816, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 28247
    ⟨882816, by decide⟩ (by decide) (![⟨882690, by decide⟩,⟨882725, by decide⟩,⟨882773, by decide⟩,⟨882815, by decide⟩]) unmarked_context_11_28247_882816 node_context_11_28247_882816
  intro a
  fin_cases a
  · exact context_12_112988_882690
  · exact context_12_112989_882725
  · exact context_12_112990_882773
  · exact context_12_112991_882815

theorem unmarked_context_10_7061_882817 : frontier 11 ⟨882817, by decide⟩
    (prefixCache 10 7061) (prefixPartial 10 7061) = false := by
  decide +kernel

theorem node_context_10_7061_882817 : EJMOriginalGlobalDAGData.nodes 11 ⟨882817, by decide⟩ =
    .split (coordinate 10) (![⟨882370, by decide⟩,⟨882483, by decide⟩,⟨882646, by decide⟩,⟨882816, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_7061_882817 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 7061 ⟨882817, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 7061
    ⟨882817, by decide⟩ (by decide) (![⟨882370, by decide⟩,⟨882483, by decide⟩,⟨882646, by decide⟩,⟨882816, by decide⟩]) unmarked_context_10_7061_882817 node_context_10_7061_882817
  intro a
  fin_cases a
  · exact context_11_28244_882370
  · exact context_11_28245_882483
  · exact context_11_28246_882646
  · exact context_11_28247_882816

theorem selected_cut_34170 : selected 9 ⟨882848, by decide⟩
    (prefixPartial 12 112992) = some ⟨12, 2, 0, 882848, 112992, 2625, 65536⟩ := by
  decide +kernel

theorem context_12_112992_882848 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112992 ⟨882848, by decide⟩ :=
  accepted_of_selected 12 112992 ⟨882848, by decide⟩ ⟨12, 2, 0, 882848, 112992, 2625, 65536⟩
    (by decide) selected_cut_34170

theorem selected_cut_34171 : selected 9 ⟨882884, by decide⟩
    (prefixPartial 12 112993) = some ⟨12, 2, 0, 882884, 112993, 2661, 65536⟩ := by
  decide +kernel

theorem context_12_112993_882884 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112993 ⟨882884, by decide⟩ :=
  accepted_of_selected 12 112993 ⟨882884, by decide⟩ ⟨12, 2, 0, 882884, 112993, 2661, 65536⟩
    (by decide) selected_cut_34171

theorem selected_cut_34172 : selected 9 ⟨882919, by decide⟩
    (prefixPartial 12 112994) = some ⟨12, 2, 0, 882919, 112994, 2773, 65536⟩ := by
  decide +kernel

theorem context_12_112994_882919 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112994 ⟨882919, by decide⟩ :=
  accepted_of_selected 12 112994 ⟨882919, by decide⟩ ⟨12, 2, 0, 882919, 112994, 2773, 65536⟩
    (by decide) selected_cut_34172

theorem selected_cut_34173 : selected 9 ⟨882947, by decide⟩
    (prefixPartial 12 112995) = some ⟨12, 2, 0, 882947, 112995, 2785, 65536⟩ := by
  decide +kernel

theorem context_12_112995_882947 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112995 ⟨882947, by decide⟩ :=
  accepted_of_selected 12 112995 ⟨882947, by decide⟩ ⟨12, 2, 0, 882947, 112995, 2785, 65536⟩
    (by decide) selected_cut_34173

theorem unmarked_context_11_28248_882948 : frontier 10 ⟨882948, by decide⟩
    (prefixCache 11 28248) (prefixPartial 11 28248) = false := by
  decide +kernel

theorem node_context_11_28248_882948 : EJMOriginalGlobalDAGData.nodes 10 ⟨882948, by decide⟩ =
    .split (coordinate 11) (![⟨882848, by decide⟩,⟨882884, by decide⟩,⟨882919, by decide⟩,⟨882947, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_28248_882948 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 28248 ⟨882948, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 28248
    ⟨882948, by decide⟩ (by decide) (![⟨882848, by decide⟩,⟨882884, by decide⟩,⟨882919, by decide⟩,⟨882947, by decide⟩]) unmarked_context_11_28248_882948 node_context_11_28248_882948
  intro a
  fin_cases a
  · exact context_12_112992_882848
  · exact context_12_112993_882884
  · exact context_12_112994_882919
  · exact context_12_112995_882947

theorem selected_cut_34174 : selected 9 ⟨882979, by decide⟩
    (prefixPartial 12 112996) = some ⟨12, 2, 0, 882979, 112996, 2185, 65536⟩ := by
  decide +kernel

theorem context_12_112996_882979 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112996 ⟨882979, by decide⟩ :=
  accepted_of_selected 12 112996 ⟨882979, by decide⟩ ⟨12, 2, 0, 882979, 112996, 2185, 65536⟩
    (by decide) selected_cut_34174

theorem selected_cut_34175 : selected 9 ⟨688903, by decide⟩
    (prefixPartial 12 112997) = some ⟨12, 1, 0, 688903, 112997, 1, 65536⟩ := by
  decide +kernel

theorem context_12_112997_688903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112997 ⟨688903, by decide⟩ :=
  accepted_of_selected 12 112997 ⟨688903, by decide⟩ ⟨12, 1, 0, 688903, 112997, 1, 65536⟩
    (by decide) selected_cut_34175

theorem selected_cut_34176 : selected 9 ⟨883016, by decide⟩
    (prefixPartial 12 112998) = some ⟨12, 2, 0, 883016, 112998, 2417, 65536⟩ := by
  decide +kernel

theorem context_12_112998_883016 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112998 ⟨883016, by decide⟩ :=
  accepted_of_selected 12 112998 ⟨883016, by decide⟩ ⟨12, 2, 0, 883016, 112998, 2417, 65536⟩
    (by decide) selected_cut_34176

theorem selected_cut_34177 : selected 9 ⟨883046, by decide⟩
    (prefixPartial 12 112999) = some ⟨12, 2, 0, 883046, 112999, 2173, 65536⟩ := by
  decide +kernel

theorem context_12_112999_883046 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112999 ⟨883046, by decide⟩ :=
  accepted_of_selected 12 112999 ⟨883046, by decide⟩ ⟨12, 2, 0, 883046, 112999, 2173, 65536⟩
    (by decide) selected_cut_34177

theorem unmarked_context_11_28249_883047 : frontier 10 ⟨883047, by decide⟩
    (prefixCache 11 28249) (prefixPartial 11 28249) = false := by
  decide +kernel

theorem node_context_11_28249_883047 : EJMOriginalGlobalDAGData.nodes 10 ⟨883047, by decide⟩ =
    .split (coordinate 11) (![⟨882979, by decide⟩,⟨688903, by decide⟩,⟨883016, by decide⟩,⟨883046, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_28249_883047 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 28249 ⟨883047, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 28249
    ⟨883047, by decide⟩ (by decide) (![⟨882979, by decide⟩,⟨688903, by decide⟩,⟨883016, by decide⟩,⟨883046, by decide⟩]) unmarked_context_11_28249_883047 node_context_11_28249_883047
  intro a
  fin_cases a
  · exact context_12_112996_882979
  · exact context_12_112997_688903
  · exact context_12_112998_883016
  · exact context_12_112999_883046

theorem selected_cut_34178 : selected 10 ⟨883048, by decide⟩
    (prefixPartial 11 28250) = some ⟨11, 2, 0, 883048, 28250, 5, 262144⟩ := by
  decide +kernel

theorem context_11_28250_883048 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 28250 ⟨883048, by decide⟩ :=
  accepted_of_selected 11 28250 ⟨883048, by decide⟩ ⟨11, 2, 0, 883048, 28250, 5, 262144⟩
    (by decide) selected_cut_34178

theorem selected_cut_34179 : selected 9 ⟨883082, by decide⟩
    (prefixPartial 12 113004) = some ⟨12, 2, 0, 883082, 113004, 2617, 65536⟩ := by
  decide +kernel

theorem context_12_113004_883082 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 113004 ⟨883082, by decide⟩ :=
  accepted_of_selected 12 113004 ⟨883082, by decide⟩ ⟨12, 2, 0, 883082, 113004, 2617, 65536⟩
    (by decide) selected_cut_34179

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
