/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover370
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_35619 : selected 9 ⟨937972, by decide⟩
    (prefixPartial 12 287055) = some ⟨12, 2, 0, 937972, 287055, 2069, 65536⟩ := by
  decide +kernel

theorem context_12_287055_937972 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287055 ⟨937972, by decide⟩ :=
  accepted_of_selected 12 287055 ⟨937972, by decide⟩ ⟨12, 2, 0, 937972, 287055, 2069, 65536⟩
    (by decide) selected_cut_35619

theorem unmarked_context_11_71763_937973 : frontier 10 ⟨937973, by decide⟩
    (prefixCache 11 71763) (prefixPartial 11 71763) = false := by
  decide +kernel

theorem node_context_11_71763_937973 : EJMOriginalGlobalDAGData.nodes 10 ⟨937973, by decide⟩ =
    .split (coordinate 11) (![⟨937918, by decide⟩,⟨896706, by decide⟩,⟨937943, by decide⟩,⟨937972, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71763_937973 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71763 ⟨937973, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71763
    ⟨937973, by decide⟩ (by decide) (![⟨937918, by decide⟩,⟨896706, by decide⟩,⟨937943, by decide⟩,⟨937972, by decide⟩]) unmarked_context_11_71763_937973 node_context_11_71763_937973
  intro a
  fin_cases a
  · exact context_12_287052_937918
  · exact context_12_287053_896706
  · exact context_12_287054_937943
  · exact context_12_287055_937972

theorem unmarked_context_10_17940_937974 : frontier 11 ⟨937974, by decide⟩
    (prefixCache 10 17940) (prefixPartial 10 17940) = false := by
  decide +kernel

theorem node_context_10_17940_937974 : EJMOriginalGlobalDAGData.nodes 11 ⟨937974, by decide⟩ =
    .split (coordinate 10) (![⟨907917, by decide⟩,⟨937763, by decide⟩,⟨937885, by decide⟩,⟨937973, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17940_937974 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17940 ⟨937974, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17940
    ⟨937974, by decide⟩ (by decide) (![⟨907917, by decide⟩,⟨937763, by decide⟩,⟨937885, by decide⟩,⟨937973, by decide⟩]) unmarked_context_10_17940_937974 node_context_10_17940_937974
  intro a
  fin_cases a
  · exact context_11_71760_907917
  · exact context_11_71761_937763
  · exact context_11_71762_937885
  · exact context_11_71763_937973

theorem selected_cut_35620 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 17941) = some ⟨10, 1, 0, 893098, 17941, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_17941_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17941 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 17941 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 17941, 1, 1048576⟩
    (by decide) selected_cut_35620

theorem selected_cut_35621 : selected 9 ⟨937996, by decide⟩
    (prefixPartial 12 287072) = some ⟨12, 2, 0, 937996, 287072, 1889, 65536⟩ := by
  decide +kernel

theorem context_12_287072_937996 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287072 ⟨937996, by decide⟩ :=
  accepted_of_selected 12 287072 ⟨937996, by decide⟩ ⟨12, 2, 0, 937996, 287072, 1889, 65536⟩
    (by decide) selected_cut_35621

theorem selected_cut_35622 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 287073) = some ⟨12, 1, 0, 896706, 287073, 1, 65536⟩ := by
  decide +kernel

theorem context_12_287073_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287073 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 287073 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 287073, 1, 65536⟩
    (by decide) selected_cut_35622

theorem selected_cut_35623 : selected 9 ⟨938027, by decide⟩
    (prefixPartial 12 287074) = some ⟨12, 2, 0, 938027, 287074, 1957, 65536⟩ := by
  decide +kernel

theorem context_12_287074_938027 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287074 ⟨938027, by decide⟩ :=
  accepted_of_selected 12 287074 ⟨938027, by decide⟩ ⟨12, 2, 0, 938027, 287074, 1957, 65536⟩
    (by decide) selected_cut_35623

theorem selected_cut_35624 : selected 9 ⟨938057, by decide⟩
    (prefixPartial 12 287075) = some ⟨12, 2, 0, 938057, 287075, 1997, 65536⟩ := by
  decide +kernel

theorem context_12_287075_938057 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287075 ⟨938057, by decide⟩ :=
  accepted_of_selected 12 287075 ⟨938057, by decide⟩ ⟨12, 2, 0, 938057, 287075, 1997, 65536⟩
    (by decide) selected_cut_35624

theorem unmarked_context_11_71768_938058 : frontier 10 ⟨938058, by decide⟩
    (prefixCache 11 71768) (prefixPartial 11 71768) = false := by
  decide +kernel

theorem node_context_11_71768_938058 : EJMOriginalGlobalDAGData.nodes 10 ⟨938058, by decide⟩ =
    .split (coordinate 11) (![⟨937996, by decide⟩,⟨896706, by decide⟩,⟨938027, by decide⟩,⟨938057, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71768_938058 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71768 ⟨938058, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71768
    ⟨938058, by decide⟩ (by decide) (![⟨937996, by decide⟩,⟨896706, by decide⟩,⟨938027, by decide⟩,⟨938057, by decide⟩]) unmarked_context_11_71768_938058 node_context_11_71768_938058
  intro a
  fin_cases a
  · exact context_12_287072_937996
  · exact context_12_287073_896706
  · exact context_12_287074_938027
  · exact context_12_287075_938057

theorem selected_cut_35625 : selected 9 ⟨938077, by decide⟩
    (prefixPartial 12 287076) = some ⟨12, 2, 0, 938077, 287076, 1805, 65536⟩ := by
  decide +kernel

theorem context_12_287076_938077 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287076 ⟨938077, by decide⟩ :=
  accepted_of_selected 12 287076 ⟨938077, by decide⟩ ⟨12, 2, 0, 938077, 287076, 1805, 65536⟩
    (by decide) selected_cut_35625

theorem selected_cut_35626 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 287077) = some ⟨12, 1, 0, 896706, 287077, 1, 65536⟩ := by
  decide +kernel

theorem context_12_287077_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287077 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 287077 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 287077, 1, 65536⟩
    (by decide) selected_cut_35626

theorem selected_cut_35627 : selected 9 ⟨938105, by decide⟩
    (prefixPartial 12 287078) = some ⟨12, 2, 0, 938105, 287078, 1749, 65536⟩ := by
  decide +kernel

theorem context_12_287078_938105 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287078 ⟨938105, by decide⟩ :=
  accepted_of_selected 12 287078 ⟨938105, by decide⟩ ⟨12, 2, 0, 938105, 287078, 1749, 65536⟩
    (by decide) selected_cut_35627

theorem selected_cut_35628 : selected 9 ⟨938126, by decide⟩
    (prefixPartial 12 287079) = some ⟨12, 2, 0, 938126, 287079, 1649, 65536⟩ := by
  decide +kernel

theorem context_12_287079_938126 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287079 ⟨938126, by decide⟩ :=
  accepted_of_selected 12 287079 ⟨938126, by decide⟩ ⟨12, 2, 0, 938126, 287079, 1649, 65536⟩
    (by decide) selected_cut_35628

theorem unmarked_context_11_71769_938127 : frontier 10 ⟨938127, by decide⟩
    (prefixCache 11 71769) (prefixPartial 11 71769) = false := by
  decide +kernel

theorem node_context_11_71769_938127 : EJMOriginalGlobalDAGData.nodes 10 ⟨938127, by decide⟩ =
    .split (coordinate 11) (![⟨938077, by decide⟩,⟨896706, by decide⟩,⟨938105, by decide⟩,⟨938126, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71769_938127 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71769 ⟨938127, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71769
    ⟨938127, by decide⟩ (by decide) (![⟨938077, by decide⟩,⟨896706, by decide⟩,⟨938105, by decide⟩,⟨938126, by decide⟩]) unmarked_context_11_71769_938127 node_context_11_71769_938127
  intro a
  fin_cases a
  · exact context_12_287076_938077
  · exact context_12_287077_896706
  · exact context_12_287078_938105
  · exact context_12_287079_938126

theorem selected_cut_35629 : selected 9 ⟨938155, by decide⟩
    (prefixPartial 12 287080) = some ⟨12, 2, 0, 938155, 287080, 2073, 65536⟩ := by
  decide +kernel

theorem context_12_287080_938155 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287080 ⟨938155, by decide⟩ :=
  accepted_of_selected 12 287080 ⟨938155, by decide⟩ ⟨12, 2, 0, 938155, 287080, 2073, 65536⟩
    (by decide) selected_cut_35629

theorem selected_cut_35630 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 287081) = some ⟨12, 1, 0, 896706, 287081, 1, 65536⟩ := by
  decide +kernel

theorem context_12_287081_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287081 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 287081 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 287081, 1, 65536⟩
    (by decide) selected_cut_35630

theorem selected_cut_35631 : selected 9 ⟨938180, by decide⟩
    (prefixPartial 12 287082) = some ⟨12, 2, 0, 938180, 287082, 1989, 65536⟩ := by
  decide +kernel

theorem context_12_287082_938180 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287082 ⟨938180, by decide⟩ :=
  accepted_of_selected 12 287082 ⟨938180, by decide⟩ ⟨12, 2, 0, 938180, 287082, 1989, 65536⟩
    (by decide) selected_cut_35631

theorem selected_cut_35632 : selected 9 ⟨938213, by decide⟩
    (prefixPartial 12 287083) = some ⟨12, 2, 0, 938213, 287083, 1977, 65536⟩ := by
  decide +kernel

theorem context_12_287083_938213 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287083 ⟨938213, by decide⟩ :=
  accepted_of_selected 12 287083 ⟨938213, by decide⟩ ⟨12, 2, 0, 938213, 287083, 1977, 65536⟩
    (by decide) selected_cut_35632

theorem unmarked_context_11_71770_938214 : frontier 10 ⟨938214, by decide⟩
    (prefixCache 11 71770) (prefixPartial 11 71770) = false := by
  decide +kernel

theorem node_context_11_71770_938214 : EJMOriginalGlobalDAGData.nodes 10 ⟨938214, by decide⟩ =
    .split (coordinate 11) (![⟨938155, by decide⟩,⟨896706, by decide⟩,⟨938180, by decide⟩,⟨938213, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71770_938214 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71770 ⟨938214, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71770
    ⟨938214, by decide⟩ (by decide) (![⟨938155, by decide⟩,⟨896706, by decide⟩,⟨938180, by decide⟩,⟨938213, by decide⟩]) unmarked_context_11_71770_938214 node_context_11_71770_938214
  intro a
  fin_cases a
  · exact context_12_287080_938155
  · exact context_12_287081_896706
  · exact context_12_287082_938180
  · exact context_12_287083_938213

theorem selected_cut_35633 : selected 9 ⟨938246, by decide⟩
    (prefixPartial 12 287084) = some ⟨12, 2, 0, 938246, 287084, 2053, 65536⟩ := by
  decide +kernel

theorem context_12_287084_938246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287084 ⟨938246, by decide⟩ :=
  accepted_of_selected 12 287084 ⟨938246, by decide⟩ ⟨12, 2, 0, 938246, 287084, 2053, 65536⟩
    (by decide) selected_cut_35633

theorem selected_cut_35634 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 287085) = some ⟨12, 1, 0, 896706, 287085, 1, 65536⟩ := by
  decide +kernel

theorem context_12_287085_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287085 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 287085 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 287085, 1, 65536⟩
    (by decide) selected_cut_35634

theorem selected_cut_35635 : selected 9 ⟨938283, by decide⟩
    (prefixPartial 12 287086) = some ⟨12, 2, 0, 938283, 287086, 2149, 65536⟩ := by
  decide +kernel

theorem context_12_287086_938283 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287086 ⟨938283, by decide⟩ :=
  accepted_of_selected 12 287086 ⟨938283, by decide⟩ ⟨12, 2, 0, 938283, 287086, 2149, 65536⟩
    (by decide) selected_cut_35635

theorem selected_cut_35636 : selected 9 ⟨938314, by decide⟩
    (prefixPartial 12 287087) = some ⟨12, 2, 0, 938314, 287087, 2101, 65536⟩ := by
  decide +kernel

theorem context_12_287087_938314 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287087 ⟨938314, by decide⟩ :=
  accepted_of_selected 12 287087 ⟨938314, by decide⟩ ⟨12, 2, 0, 938314, 287087, 2101, 65536⟩
    (by decide) selected_cut_35636

theorem unmarked_context_11_71771_938315 : frontier 10 ⟨938315, by decide⟩
    (prefixCache 11 71771) (prefixPartial 11 71771) = false := by
  decide +kernel

theorem node_context_11_71771_938315 : EJMOriginalGlobalDAGData.nodes 10 ⟨938315, by decide⟩ =
    .split (coordinate 11) (![⟨938246, by decide⟩,⟨896706, by decide⟩,⟨938283, by decide⟩,⟨938314, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71771_938315 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71771 ⟨938315, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71771
    ⟨938315, by decide⟩ (by decide) (![⟨938246, by decide⟩,⟨896706, by decide⟩,⟨938283, by decide⟩,⟨938314, by decide⟩]) unmarked_context_11_71771_938315 node_context_11_71771_938315
  intro a
  fin_cases a
  · exact context_12_287084_938246
  · exact context_12_287085_896706
  · exact context_12_287086_938283
  · exact context_12_287087_938314

theorem unmarked_context_10_17942_938316 : frontier 11 ⟨938316, by decide⟩
    (prefixCache 10 17942) (prefixPartial 10 17942) = false := by
  decide +kernel

theorem node_context_10_17942_938316 : EJMOriginalGlobalDAGData.nodes 11 ⟨938316, by decide⟩ =
    .split (coordinate 10) (![⟨938058, by decide⟩,⟨938127, by decide⟩,⟨938214, by decide⟩,⟨938315, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17942_938316 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17942 ⟨938316, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17942
    ⟨938316, by decide⟩ (by decide) (![⟨938058, by decide⟩,⟨938127, by decide⟩,⟨938214, by decide⟩,⟨938315, by decide⟩]) unmarked_context_10_17942_938316 node_context_10_17942_938316
  intro a
  fin_cases a
  · exact context_11_71768_938058
  · exact context_11_71769_938127
  · exact context_11_71770_938214
  · exact context_11_71771_938315

theorem selected_cut_35637 : selected 9 ⟨938340, by decide⟩
    (prefixPartial 12 287088) = some ⟨12, 2, 0, 938340, 287088, 1821, 65536⟩ := by
  decide +kernel

theorem context_12_287088_938340 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287088 ⟨938340, by decide⟩ :=
  accepted_of_selected 12 287088 ⟨938340, by decide⟩ ⟨12, 2, 0, 938340, 287088, 1821, 65536⟩
    (by decide) selected_cut_35637

theorem selected_cut_35638 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 287089) = some ⟨12, 1, 0, 896706, 287089, 1, 65536⟩ := by
  decide +kernel

theorem context_12_287089_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287089 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 287089 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 287089, 1, 65536⟩
    (by decide) selected_cut_35638

theorem selected_cut_35639 : selected 9 ⟨938364, by decide⟩
    (prefixPartial 12 287090) = some ⟨12, 2, 0, 938364, 287090, 1697, 65536⟩ := by
  decide +kernel

theorem context_12_287090_938364 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287090 ⟨938364, by decide⟩ :=
  accepted_of_selected 12 287090 ⟨938364, by decide⟩ ⟨12, 2, 0, 938364, 287090, 1697, 65536⟩
    (by decide) selected_cut_35639

theorem selected_cut_35640 : selected 9 ⟨938400, by decide⟩
    (prefixPartial 12 287091) = some ⟨12, 2, 0, 938400, 287091, 2005, 65536⟩ := by
  decide +kernel

theorem context_12_287091_938400 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287091 ⟨938400, by decide⟩ :=
  accepted_of_selected 12 287091 ⟨938400, by decide⟩ ⟨12, 2, 0, 938400, 287091, 2005, 65536⟩
    (by decide) selected_cut_35640

theorem unmarked_context_11_71772_938401 : frontier 10 ⟨938401, by decide⟩
    (prefixCache 11 71772) (prefixPartial 11 71772) = false := by
  decide +kernel

theorem node_context_11_71772_938401 : EJMOriginalGlobalDAGData.nodes 10 ⟨938401, by decide⟩ =
    .split (coordinate 11) (![⟨938340, by decide⟩,⟨896706, by decide⟩,⟨938364, by decide⟩,⟨938400, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71772_938401 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71772 ⟨938401, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71772
    ⟨938401, by decide⟩ (by decide) (![⟨938340, by decide⟩,⟨896706, by decide⟩,⟨938364, by decide⟩,⟨938400, by decide⟩]) unmarked_context_11_71772_938401 node_context_11_71772_938401
  intro a
  fin_cases a
  · exact context_12_287088_938340
  · exact context_12_287089_896706
  · exact context_12_287090_938364
  · exact context_12_287091_938400

theorem selected_cut_35641 : selected 9 ⟨938424, by decide⟩
    (prefixPartial 12 287092) = some ⟨12, 2, 0, 938424, 287092, 1621, 65536⟩ := by
  decide +kernel

theorem context_12_287092_938424 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287092 ⟨938424, by decide⟩ :=
  accepted_of_selected 12 287092 ⟨938424, by decide⟩ ⟨12, 2, 0, 938424, 287092, 1621, 65536⟩
    (by decide) selected_cut_35641

theorem selected_cut_35642 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 287093) = some ⟨12, 1, 0, 896706, 287093, 1, 65536⟩ := by
  decide +kernel

theorem context_12_287093_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287093 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 287093 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 287093, 1, 65536⟩
    (by decide) selected_cut_35642

theorem selected_cut_35643 : selected 9 ⟨938444, by decide⟩
    (prefixPartial 12 287094) = some ⟨12, 2, 0, 938444, 287094, 1505, 65536⟩ := by
  decide +kernel

theorem context_12_287094_938444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287094 ⟨938444, by decide⟩ :=
  accepted_of_selected 12 287094 ⟨938444, by decide⟩ ⟨12, 2, 0, 938444, 287094, 1505, 65536⟩
    (by decide) selected_cut_35643

theorem selected_cut_35644 : selected 9 ⟨938464, by decide⟩
    (prefixPartial 12 287095) = some ⟨12, 2, 0, 938464, 287095, 1565, 65536⟩ := by
  decide +kernel

theorem context_12_287095_938464 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287095 ⟨938464, by decide⟩ :=
  accepted_of_selected 12 287095 ⟨938464, by decide⟩ ⟨12, 2, 0, 938464, 287095, 1565, 65536⟩
    (by decide) selected_cut_35644

theorem unmarked_context_11_71773_938465 : frontier 10 ⟨938465, by decide⟩
    (prefixCache 11 71773) (prefixPartial 11 71773) = false := by
  decide +kernel

theorem node_context_11_71773_938465 : EJMOriginalGlobalDAGData.nodes 10 ⟨938465, by decide⟩ =
    .split (coordinate 11) (![⟨938424, by decide⟩,⟨896706, by decide⟩,⟨938444, by decide⟩,⟨938464, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71773_938465 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71773 ⟨938465, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71773
    ⟨938465, by decide⟩ (by decide) (![⟨938424, by decide⟩,⟨896706, by decide⟩,⟨938444, by decide⟩,⟨938464, by decide⟩]) unmarked_context_11_71773_938465 node_context_11_71773_938465
  intro a
  fin_cases a
  · exact context_12_287092_938424
  · exact context_12_287093_896706
  · exact context_12_287094_938444
  · exact context_12_287095_938464

theorem selected_cut_35645 : selected 9 ⟨938492, by decide⟩
    (prefixPartial 12 287096) = some ⟨12, 2, 0, 938492, 287096, 2009, 65536⟩ := by
  decide +kernel

theorem context_12_287096_938492 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287096 ⟨938492, by decide⟩ :=
  accepted_of_selected 12 287096 ⟨938492, by decide⟩ ⟨12, 2, 0, 938492, 287096, 2009, 65536⟩
    (by decide) selected_cut_35645

theorem selected_cut_35646 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 287097) = some ⟨12, 1, 0, 896706, 287097, 1, 65536⟩ := by
  decide +kernel

theorem context_12_287097_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287097 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 287097 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 287097, 1, 65536⟩
    (by decide) selected_cut_35646

theorem selected_cut_35647 : selected 9 ⟨938519, by decide⟩
    (prefixPartial 12 287098) = some ⟨12, 2, 0, 938519, 287098, 1805, 65536⟩ := by
  decide +kernel

theorem context_12_287098_938519 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287098 ⟨938519, by decide⟩ :=
  accepted_of_selected 12 287098 ⟨938519, by decide⟩ ⟨12, 2, 0, 938519, 287098, 1805, 65536⟩
    (by decide) selected_cut_35647

theorem selected_cut_35648 : selected 9 ⟨938549, by decide⟩
    (prefixPartial 12 287099) = some ⟨12, 2, 0, 938549, 287099, 1977, 65536⟩ := by
  decide +kernel

theorem context_12_287099_938549 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287099 ⟨938549, by decide⟩ :=
  accepted_of_selected 12 287099 ⟨938549, by decide⟩ ⟨12, 2, 0, 938549, 287099, 1977, 65536⟩
    (by decide) selected_cut_35648

theorem unmarked_context_11_71774_938550 : frontier 10 ⟨938550, by decide⟩
    (prefixCache 11 71774) (prefixPartial 11 71774) = false := by
  decide +kernel

theorem node_context_11_71774_938550 : EJMOriginalGlobalDAGData.nodes 10 ⟨938550, by decide⟩ =
    .split (coordinate 11) (![⟨938492, by decide⟩,⟨896706, by decide⟩,⟨938519, by decide⟩,⟨938549, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71774_938550 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71774 ⟨938550, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71774
    ⟨938550, by decide⟩ (by decide) (![⟨938492, by decide⟩,⟨896706, by decide⟩,⟨938519, by decide⟩,⟨938549, by decide⟩]) unmarked_context_11_71774_938550 node_context_11_71774_938550
  intro a
  fin_cases a
  · exact context_12_287096_938492
  · exact context_12_287097_896706
  · exact context_12_287098_938519
  · exact context_12_287099_938549

theorem selected_cut_35649 : selected 9 ⟨938574, by decide⟩
    (prefixPartial 12 287100) = some ⟨12, 2, 0, 938574, 287100, 1713, 65536⟩ := by
  decide +kernel

theorem context_12_287100_938574 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287100 ⟨938574, by decide⟩ :=
  accepted_of_selected 12 287100 ⟨938574, by decide⟩ ⟨12, 2, 0, 938574, 287100, 1713, 65536⟩
    (by decide) selected_cut_35649

theorem selected_cut_35650 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 287101) = some ⟨12, 1, 0, 896706, 287101, 1, 65536⟩ := by
  decide +kernel

theorem context_12_287101_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287101 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 287101 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 287101, 1, 65536⟩
    (by decide) selected_cut_35650

theorem selected_cut_35651 : selected 9 ⟨938596, by decide⟩
    (prefixPartial 12 287102) = some ⟨12, 2, 0, 938596, 287102, 1697, 65536⟩ := by
  decide +kernel

theorem context_12_287102_938596 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287102 ⟨938596, by decide⟩ :=
  accepted_of_selected 12 287102 ⟨938596, by decide⟩ ⟨12, 2, 0, 938596, 287102, 1697, 65536⟩
    (by decide) selected_cut_35651

theorem selected_cut_35652 : selected 9 ⟨938623, by decide⟩
    (prefixPartial 12 287103) = some ⟨12, 2, 0, 938623, 287103, 1813, 65536⟩ := by
  decide +kernel

theorem context_12_287103_938623 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287103 ⟨938623, by decide⟩ :=
  accepted_of_selected 12 287103 ⟨938623, by decide⟩ ⟨12, 2, 0, 938623, 287103, 1813, 65536⟩
    (by decide) selected_cut_35652

theorem unmarked_context_11_71775_938624 : frontier 10 ⟨938624, by decide⟩
    (prefixCache 11 71775) (prefixPartial 11 71775) = false := by
  decide +kernel

theorem node_context_11_71775_938624 : EJMOriginalGlobalDAGData.nodes 10 ⟨938624, by decide⟩ =
    .split (coordinate 11) (![⟨938574, by decide⟩,⟨896706, by decide⟩,⟨938596, by decide⟩,⟨938623, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71775_938624 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71775 ⟨938624, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71775
    ⟨938624, by decide⟩ (by decide) (![⟨938574, by decide⟩,⟨896706, by decide⟩,⟨938596, by decide⟩,⟨938623, by decide⟩]) unmarked_context_11_71775_938624 node_context_11_71775_938624
  intro a
  fin_cases a
  · exact context_12_287100_938574
  · exact context_12_287101_896706
  · exact context_12_287102_938596
  · exact context_12_287103_938623

theorem unmarked_context_10_17943_938625 : frontier 11 ⟨938625, by decide⟩
    (prefixCache 10 17943) (prefixPartial 10 17943) = false := by
  decide +kernel

theorem node_context_10_17943_938625 : EJMOriginalGlobalDAGData.nodes 11 ⟨938625, by decide⟩ =
    .split (coordinate 10) (![⟨938401, by decide⟩,⟨938465, by decide⟩,⟨938550, by decide⟩,⟨938624, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17943_938625 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17943 ⟨938625, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17943
    ⟨938625, by decide⟩ (by decide) (![⟨938401, by decide⟩,⟨938465, by decide⟩,⟨938550, by decide⟩,⟨938624, by decide⟩]) unmarked_context_10_17943_938625 node_context_10_17943_938625
  intro a
  fin_cases a
  · exact context_11_71772_938401
  · exact context_11_71773_938465
  · exact context_11_71774_938550
  · exact context_11_71775_938624

theorem unmarked_context_9_4485_938626 : frontier 12 ⟨938626, by decide⟩
    (prefixCache 9 4485) (prefixPartial 9 4485) = false := by
  decide +kernel

theorem node_context_9_4485_938626 : EJMOriginalGlobalDAGData.nodes 12 ⟨938626, by decide⟩ =
    .split (coordinate 9) (![⟨937974, by decide⟩,⟨893098, by decide⟩,⟨938316, by decide⟩,⟨938625, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4485_938626 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4485 ⟨938626, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4485
    ⟨938626, by decide⟩ (by decide) (![⟨937974, by decide⟩,⟨893098, by decide⟩,⟨938316, by decide⟩,⟨938625, by decide⟩]) unmarked_context_9_4485_938626 node_context_9_4485_938626
  intro a
  fin_cases a
  · exact context_10_17940_937974
  · exact context_10_17941_893098
  · exact context_10_17942_938316
  · exact context_10_17943_938625

theorem selected_cut_35653 : selected 10 ⟨907917, by decide⟩
    (prefixPartial 11 71776) = some ⟨11, 1, 0, 907917, 71776, 1, 262144⟩ := by
  decide +kernel

theorem context_11_71776_907917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71776 ⟨907917, by decide⟩ :=
  accepted_of_selected 11 71776 ⟨907917, by decide⟩ ⟨11, 1, 0, 907917, 71776, 1, 262144⟩
    (by decide) selected_cut_35653

theorem selected_cut_35654 : selected 9 ⟨938651, by decide⟩
    (prefixPartial 12 287108) = some ⟨12, 2, 0, 938651, 287108, 1769, 65536⟩ := by
  decide +kernel

theorem context_12_287108_938651 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287108 ⟨938651, by decide⟩ :=
  accepted_of_selected 12 287108 ⟨938651, by decide⟩ ⟨12, 2, 0, 938651, 287108, 1769, 65536⟩
    (by decide) selected_cut_35654

theorem selected_cut_35655 : selected 9 ⟨891951, by decide⟩
    (prefixPartial 12 287109) = some ⟨12, 1, 0, 891951, 287109, 1, 65536⟩ := by
  decide +kernel

theorem context_12_287109_891951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287109 ⟨891951, by decide⟩ :=
  accepted_of_selected 12 287109 ⟨891951, by decide⟩ ⟨12, 1, 0, 891951, 287109, 1, 65536⟩
    (by decide) selected_cut_35655

theorem selected_cut_35656 : selected 9 ⟨938670, by decide⟩
    (prefixPartial 12 287110) = some ⟨12, 2, 0, 938670, 287110, 1505, 65536⟩ := by
  decide +kernel

theorem context_12_287110_938670 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287110 ⟨938670, by decide⟩ :=
  accepted_of_selected 12 287110 ⟨938670, by decide⟩ ⟨12, 2, 0, 938670, 287110, 1505, 65536⟩
    (by decide) selected_cut_35656

theorem selected_cut_35657 : selected 9 ⟨938686, by decide⟩
    (prefixPartial 12 287111) = some ⟨12, 2, 0, 938686, 287111, 1417, 65536⟩ := by
  decide +kernel

theorem context_12_287111_938686 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287111 ⟨938686, by decide⟩ :=
  accepted_of_selected 12 287111 ⟨938686, by decide⟩ ⟨12, 2, 0, 938686, 287111, 1417, 65536⟩
    (by decide) selected_cut_35657

theorem unmarked_context_11_71777_938687 : frontier 10 ⟨938687, by decide⟩
    (prefixCache 11 71777) (prefixPartial 11 71777) = false := by
  decide +kernel

theorem node_context_11_71777_938687 : EJMOriginalGlobalDAGData.nodes 10 ⟨938687, by decide⟩ =
    .split (coordinate 11) (![⟨938651, by decide⟩,⟨891951, by decide⟩,⟨938670, by decide⟩,⟨938686, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71777_938687 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71777 ⟨938687, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71777
    ⟨938687, by decide⟩ (by decide) (![⟨938651, by decide⟩,⟨891951, by decide⟩,⟨938670, by decide⟩,⟨938686, by decide⟩]) unmarked_context_11_71777_938687 node_context_11_71777_938687
  intro a
  fin_cases a
  · exact context_12_287108_938651
  · exact context_12_287109_891951
  · exact context_12_287110_938670
  · exact context_12_287111_938686

theorem selected_cut_35658 : selected 9 ⟨938726, by decide⟩
    (prefixPartial 12 287112) = some ⟨12, 2, 0, 938726, 287112, 1825, 65536⟩ := by
  decide +kernel

theorem context_12_287112_938726 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287112 ⟨938726, by decide⟩ :=
  accepted_of_selected 12 287112 ⟨938726, by decide⟩ ⟨12, 2, 0, 938726, 287112, 1825, 65536⟩
    (by decide) selected_cut_35658

theorem selected_cut_35659 : selected 9 ⟨938747, by decide⟩
    (prefixPartial 12 287113) = some ⟨12, 2, 0, 938747, 287113, 1573, 65536⟩ := by
  decide +kernel

theorem context_12_287113_938747 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287113 ⟨938747, by decide⟩ :=
  accepted_of_selected 12 287113 ⟨938747, by decide⟩ ⟨12, 2, 0, 938747, 287113, 1573, 65536⟩
    (by decide) selected_cut_35659

theorem selected_cut_35660 : selected 9 ⟨938767, by decide⟩
    (prefixPartial 12 287114) = some ⟨12, 2, 0, 938767, 287114, 1525, 65536⟩ := by
  decide +kernel

theorem context_12_287114_938767 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287114 ⟨938767, by decide⟩ :=
  accepted_of_selected 12 287114 ⟨938767, by decide⟩ ⟨12, 2, 0, 938767, 287114, 1525, 65536⟩
    (by decide) selected_cut_35660

theorem selected_cut_35661 : selected 9 ⟨938790, by decide⟩
    (prefixPartial 12 287115) = some ⟨12, 2, 0, 938790, 287115, 1533, 65536⟩ := by
  decide +kernel

theorem context_12_287115_938790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287115 ⟨938790, by decide⟩ :=
  accepted_of_selected 12 287115 ⟨938790, by decide⟩ ⟨12, 2, 0, 938790, 287115, 1533, 65536⟩
    (by decide) selected_cut_35661

theorem unmarked_context_11_71778_938791 : frontier 10 ⟨938791, by decide⟩
    (prefixCache 11 71778) (prefixPartial 11 71778) = false := by
  decide +kernel

theorem node_context_11_71778_938791 : EJMOriginalGlobalDAGData.nodes 10 ⟨938791, by decide⟩ =
    .split (coordinate 11) (![⟨938726, by decide⟩,⟨938747, by decide⟩,⟨938767, by decide⟩,⟨938790, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71778_938791 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71778 ⟨938791, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71778
    ⟨938791, by decide⟩ (by decide) (![⟨938726, by decide⟩,⟨938747, by decide⟩,⟨938767, by decide⟩,⟨938790, by decide⟩]) unmarked_context_11_71778_938791 node_context_11_71778_938791
  intro a
  fin_cases a
  · exact context_12_287112_938726
  · exact context_12_287113_938747
  · exact context_12_287114_938767
  · exact context_12_287115_938790

theorem selected_cut_35662 : selected 9 ⟨938813, by decide⟩
    (prefixPartial 12 287116) = some ⟨12, 2, 0, 938813, 287116, 1477, 65536⟩ := by
  decide +kernel

theorem context_12_287116_938813 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287116 ⟨938813, by decide⟩ :=
  accepted_of_selected 12 287116 ⟨938813, by decide⟩ ⟨12, 2, 0, 938813, 287116, 1477, 65536⟩
    (by decide) selected_cut_35662

theorem selected_cut_35663 : selected 9 ⟨938829, by decide⟩
    (prefixPartial 12 287117) = some ⟨12, 2, 0, 938829, 287117, 1245, 65536⟩ := by
  decide +kernel

theorem context_12_287117_938829 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287117 ⟨938829, by decide⟩ :=
  accepted_of_selected 12 287117 ⟨938829, by decide⟩ ⟨12, 2, 0, 938829, 287117, 1245, 65536⟩
    (by decide) selected_cut_35663

theorem selected_cut_35664 : selected 9 ⟨938844, by decide⟩
    (prefixPartial 12 287118) = some ⟨12, 2, 0, 938844, 287118, 1337, 65536⟩ := by
  decide +kernel

theorem context_12_287118_938844 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287118 ⟨938844, by decide⟩ :=
  accepted_of_selected 12 287118 ⟨938844, by decide⟩ ⟨12, 2, 0, 938844, 287118, 1337, 65536⟩
    (by decide) selected_cut_35664

theorem selected_cut_35665 : selected 9 ⟨938859, by decide⟩
    (prefixPartial 12 287119) = some ⟨12, 2, 0, 938859, 287119, 1305, 65536⟩ := by
  decide +kernel

theorem context_12_287119_938859 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287119 ⟨938859, by decide⟩ :=
  accepted_of_selected 12 287119 ⟨938859, by decide⟩ ⟨12, 2, 0, 938859, 287119, 1305, 65536⟩
    (by decide) selected_cut_35665

theorem unmarked_context_11_71779_938860 : frontier 10 ⟨938860, by decide⟩
    (prefixCache 11 71779) (prefixPartial 11 71779) = false := by
  decide +kernel

theorem node_context_11_71779_938860 : EJMOriginalGlobalDAGData.nodes 10 ⟨938860, by decide⟩ =
    .split (coordinate 11) (![⟨938813, by decide⟩,⟨938829, by decide⟩,⟨938844, by decide⟩,⟨938859, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71779_938860 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71779 ⟨938860, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71779
    ⟨938860, by decide⟩ (by decide) (![⟨938813, by decide⟩,⟨938829, by decide⟩,⟨938844, by decide⟩,⟨938859, by decide⟩]) unmarked_context_11_71779_938860 node_context_11_71779_938860
  intro a
  fin_cases a
  · exact context_12_287116_938813
  · exact context_12_287117_938829
  · exact context_12_287118_938844
  · exact context_12_287119_938859

theorem unmarked_context_10_17944_938861 : frontier 11 ⟨938861, by decide⟩
    (prefixCache 10 17944) (prefixPartial 10 17944) = false := by
  decide +kernel

theorem node_context_10_17944_938861 : EJMOriginalGlobalDAGData.nodes 11 ⟨938861, by decide⟩ =
    .split (coordinate 10) (![⟨907917, by decide⟩,⟨938687, by decide⟩,⟨938791, by decide⟩,⟨938860, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17944_938861 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17944 ⟨938861, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17944
    ⟨938861, by decide⟩ (by decide) (![⟨907917, by decide⟩,⟨938687, by decide⟩,⟨938791, by decide⟩,⟨938860, by decide⟩]) unmarked_context_10_17944_938861 node_context_10_17944_938861
  intro a
  fin_cases a
  · exact context_11_71776_907917
  · exact context_11_71777_938687
  · exact context_11_71778_938791
  · exact context_11_71779_938860

theorem selected_cut_35666 : selected 9 ⟨938874, by decide⟩
    (prefixPartial 12 287120) = some ⟨12, 2, 0, 938874, 287120, 1177, 65536⟩ := by
  decide +kernel

theorem context_12_287120_938874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287120 ⟨938874, by decide⟩ :=
  accepted_of_selected 12 287120 ⟨938874, by decide⟩ ⟨12, 2, 0, 938874, 287120, 1177, 65536⟩
    (by decide) selected_cut_35666

theorem selected_cut_35667 : selected 9 ⟨938889, by decide⟩
    (prefixPartial 12 287121) = some ⟨12, 2, 0, 938889, 287121, 1113, 65536⟩ := by
  decide +kernel

theorem context_12_287121_938889 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287121 ⟨938889, by decide⟩ :=
  accepted_of_selected 12 287121 ⟨938889, by decide⟩ ⟨12, 2, 0, 938889, 287121, 1113, 65536⟩
    (by decide) selected_cut_35667

theorem selected_cut_35668 : selected 9 ⟨938901, by decide⟩
    (prefixPartial 12 287122) = some ⟨12, 2, 0, 938901, 287122, 1117, 65536⟩ := by
  decide +kernel

theorem context_12_287122_938901 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287122 ⟨938901, by decide⟩ :=
  accepted_of_selected 12 287122 ⟨938901, by decide⟩ ⟨12, 2, 0, 938901, 287122, 1117, 65536⟩
    (by decide) selected_cut_35668

theorem selected_cut_35669 : selected 9 ⟨938913, by decide⟩
    (prefixPartial 12 287123) = some ⟨12, 2, 0, 938913, 287123, 1157, 65536⟩ := by
  decide +kernel

theorem context_12_287123_938913 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287123 ⟨938913, by decide⟩ :=
  accepted_of_selected 12 287123 ⟨938913, by decide⟩ ⟨12, 2, 0, 938913, 287123, 1157, 65536⟩
    (by decide) selected_cut_35669

theorem unmarked_context_11_71780_938914 : frontier 10 ⟨938914, by decide⟩
    (prefixCache 11 71780) (prefixPartial 11 71780) = false := by
  decide +kernel

theorem node_context_11_71780_938914 : EJMOriginalGlobalDAGData.nodes 10 ⟨938914, by decide⟩ =
    .split (coordinate 11) (![⟨938874, by decide⟩,⟨938889, by decide⟩,⟨938901, by decide⟩,⟨938913, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71780_938914 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71780 ⟨938914, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71780
    ⟨938914, by decide⟩ (by decide) (![⟨938874, by decide⟩,⟨938889, by decide⟩,⟨938901, by decide⟩,⟨938913, by decide⟩]) unmarked_context_11_71780_938914 node_context_11_71780_938914
  intro a
  fin_cases a
  · exact context_12_287120_938874
  · exact context_12_287121_938889
  · exact context_12_287122_938901
  · exact context_12_287123_938913

theorem selected_cut_35670 : selected 10 ⟨938948, by decide⟩
    (prefixPartial 11 71781) = some ⟨11, 2, 0, 938948, 71781, 3169, 262144⟩ := by
  decide +kernel

theorem context_11_71781_938948 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71781 ⟨938948, by decide⟩ :=
  accepted_of_selected 11 71781 ⟨938948, by decide⟩ ⟨11, 2, 0, 938948, 71781, 3169, 262144⟩
    (by decide) selected_cut_35670

theorem selected_cut_35671 : selected 10 ⟨938982, by decide⟩
    (prefixPartial 11 71782) = some ⟨11, 2, 0, 938982, 71782, 3277, 262144⟩ := by
  decide +kernel

theorem context_11_71782_938982 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71782 ⟨938982, by decide⟩ :=
  accepted_of_selected 11 71782 ⟨938982, by decide⟩ ⟨11, 2, 0, 938982, 71782, 3277, 262144⟩
    (by decide) selected_cut_35671

theorem selected_cut_35672 : selected 10 ⟨939021, by decide⟩
    (prefixPartial 11 71783) = some ⟨11, 2, 0, 939021, 71783, 3841, 262144⟩ := by
  decide +kernel

theorem context_11_71783_939021 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71783 ⟨939021, by decide⟩ :=
  accepted_of_selected 11 71783 ⟨939021, by decide⟩ ⟨11, 2, 0, 939021, 71783, 3841, 262144⟩
    (by decide) selected_cut_35672

theorem unmarked_context_10_17945_939022 : frontier 11 ⟨939022, by decide⟩
    (prefixCache 10 17945) (prefixPartial 10 17945) = false := by
  decide +kernel

theorem node_context_10_17945_939022 : EJMOriginalGlobalDAGData.nodes 11 ⟨939022, by decide⟩ =
    .split (coordinate 10) (![⟨938914, by decide⟩,⟨938948, by decide⟩,⟨938982, by decide⟩,⟨939021, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17945_939022 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17945 ⟨939022, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17945
    ⟨939022, by decide⟩ (by decide) (![⟨938914, by decide⟩,⟨938948, by decide⟩,⟨938982, by decide⟩,⟨939021, by decide⟩]) unmarked_context_10_17945_939022 node_context_10_17945_939022
  intro a
  fin_cases a
  · exact context_11_71780_938914
  · exact context_11_71781_938948
  · exact context_11_71782_938982
  · exact context_11_71783_939021

theorem selected_cut_35673 : selected 10 ⟨939067, by decide⟩
    (prefixPartial 11 71784) = some ⟨11, 2, 0, 939067, 71784, 3909, 262144⟩ := by
  decide +kernel

theorem context_11_71784_939067 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71784 ⟨939067, by decide⟩ :=
  accepted_of_selected 11 71784 ⟨939067, by decide⟩ ⟨11, 2, 0, 939067, 71784, 3909, 262144⟩
    (by decide) selected_cut_35673

theorem selected_cut_35674 : selected 10 ⟨939086, by decide⟩
    (prefixPartial 11 71785) = some ⟨11, 2, 0, 939086, 71785, 1861, 262144⟩ := by
  decide +kernel

theorem context_11_71785_939086 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71785 ⟨939086, by decide⟩ :=
  accepted_of_selected 11 71785 ⟨939086, by decide⟩ ⟨11, 2, 0, 939086, 71785, 1861, 262144⟩
    (by decide) selected_cut_35674

theorem selected_cut_35675 : selected 10 ⟨939119, by decide⟩
    (prefixPartial 11 71786) = some ⟨11, 2, 0, 939119, 71786, 2861, 262144⟩ := by
  decide +kernel

theorem context_11_71786_939119 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71786 ⟨939119, by decide⟩ :=
  accepted_of_selected 11 71786 ⟨939119, by decide⟩ ⟨11, 2, 0, 939119, 71786, 2861, 262144⟩
    (by decide) selected_cut_35675

theorem selected_cut_35676 : selected 10 ⟨939170, by decide⟩
    (prefixPartial 11 71787) = some ⟨11, 2, 0, 939170, 71787, 3809, 262144⟩ := by
  decide +kernel

theorem context_11_71787_939170 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71787 ⟨939170, by decide⟩ :=
  accepted_of_selected 11 71787 ⟨939170, by decide⟩ ⟨11, 2, 0, 939170, 71787, 3809, 262144⟩
    (by decide) selected_cut_35676

theorem unmarked_context_10_17946_939171 : frontier 11 ⟨939171, by decide⟩
    (prefixCache 10 17946) (prefixPartial 10 17946) = false := by
  decide +kernel

theorem node_context_10_17946_939171 : EJMOriginalGlobalDAGData.nodes 11 ⟨939171, by decide⟩ =
    .split (coordinate 10) (![⟨939067, by decide⟩,⟨939086, by decide⟩,⟨939119, by decide⟩,⟨939170, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17946_939171 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17946 ⟨939171, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17946
    ⟨939171, by decide⟩ (by decide) (![⟨939067, by decide⟩,⟨939086, by decide⟩,⟨939119, by decide⟩,⟨939170, by decide⟩]) unmarked_context_10_17946_939171 node_context_10_17946_939171
  intro a
  fin_cases a
  · exact context_11_71784_939067
  · exact context_11_71785_939086
  · exact context_11_71786_939119
  · exact context_11_71787_939170

theorem selected_cut_35677 : selected 10 ⟨939219, by decide⟩
    (prefixPartial 11 71788) = some ⟨11, 2, 0, 939219, 71788, 3385, 262144⟩ := by
  decide +kernel

theorem context_11_71788_939219 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71788 ⟨939219, by decide⟩ :=
  accepted_of_selected 11 71788 ⟨939219, by decide⟩ ⟨11, 2, 0, 939219, 71788, 3385, 262144⟩
    (by decide) selected_cut_35677

theorem selected_cut_35678 : selected 10 ⟨939251, by decide⟩
    (prefixPartial 11 71789) = some ⟨11, 2, 0, 939251, 71789, 2345, 262144⟩ := by
  decide +kernel

theorem context_11_71789_939251 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71789 ⟨939251, by decide⟩ :=
  accepted_of_selected 11 71789 ⟨939251, by decide⟩ ⟨11, 2, 0, 939251, 71789, 2345, 262144⟩
    (by decide) selected_cut_35678

theorem selected_cut_35679 : selected 10 ⟨939288, by decide⟩
    (prefixPartial 11 71790) = some ⟨11, 2, 0, 939288, 71790, 2925, 262144⟩ := by
  decide +kernel

theorem context_11_71790_939288 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71790 ⟨939288, by decide⟩ :=
  accepted_of_selected 11 71790 ⟨939288, by decide⟩ ⟨11, 2, 0, 939288, 71790, 2925, 262144⟩
    (by decide) selected_cut_35679

theorem selected_cut_35680 : selected 10 ⟨939320, by decide⟩
    (prefixPartial 11 71791) = some ⟨11, 2, 0, 939320, 71791, 2633, 262144⟩ := by
  decide +kernel

theorem context_11_71791_939320 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71791 ⟨939320, by decide⟩ :=
  accepted_of_selected 11 71791 ⟨939320, by decide⟩ ⟨11, 2, 0, 939320, 71791, 2633, 262144⟩
    (by decide) selected_cut_35680

theorem unmarked_context_10_17947_939321 : frontier 11 ⟨939321, by decide⟩
    (prefixCache 10 17947) (prefixPartial 10 17947) = false := by
  decide +kernel

theorem node_context_10_17947_939321 : EJMOriginalGlobalDAGData.nodes 11 ⟨939321, by decide⟩ =
    .split (coordinate 10) (![⟨939219, by decide⟩,⟨939251, by decide⟩,⟨939288, by decide⟩,⟨939320, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17947_939321 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17947 ⟨939321, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17947
    ⟨939321, by decide⟩ (by decide) (![⟨939219, by decide⟩,⟨939251, by decide⟩,⟨939288, by decide⟩,⟨939320, by decide⟩]) unmarked_context_10_17947_939321 node_context_10_17947_939321
  intro a
  fin_cases a
  · exact context_11_71788_939219
  · exact context_11_71789_939251
  · exact context_11_71790_939288
  · exact context_11_71791_939320

theorem unmarked_context_9_4486_939322 : frontier 12 ⟨939322, by decide⟩
    (prefixCache 9 4486) (prefixPartial 9 4486) = false := by
  decide +kernel

theorem node_context_9_4486_939322 : EJMOriginalGlobalDAGData.nodes 12 ⟨939322, by decide⟩ =
    .split (coordinate 9) (![⟨938861, by decide⟩,⟨939022, by decide⟩,⟨939171, by decide⟩,⟨939321, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4486_939322 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4486 ⟨939322, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4486
    ⟨939322, by decide⟩ (by decide) (![⟨938861, by decide⟩,⟨939022, by decide⟩,⟨939171, by decide⟩,⟨939321, by decide⟩]) unmarked_context_9_4486_939322 node_context_9_4486_939322
  intro a
  fin_cases a
  · exact context_10_17944_938861
  · exact context_10_17945_939022
  · exact context_10_17946_939171
  · exact context_10_17947_939321

theorem selected_cut_35681 : selected 10 ⟨907917, by decide⟩
    (prefixPartial 11 71792) = some ⟨11, 1, 0, 907917, 71792, 1, 262144⟩ := by
  decide +kernel

theorem context_11_71792_907917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71792 ⟨907917, by decide⟩ :=
  accepted_of_selected 11 71792 ⟨907917, by decide⟩ ⟨11, 1, 0, 907917, 71792, 1, 262144⟩
    (by decide) selected_cut_35681

theorem selected_cut_35682 : selected 10 ⟨939342, by decide⟩
    (prefixPartial 11 71793) = some ⟨11, 2, 0, 939342, 71793, 1713, 262144⟩ := by
  decide +kernel

theorem context_11_71793_939342 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71793 ⟨939342, by decide⟩ :=
  accepted_of_selected 11 71793 ⟨939342, by decide⟩ ⟨11, 2, 0, 939342, 71793, 1713, 262144⟩
    (by decide) selected_cut_35682

theorem selected_cut_35683 : selected 10 ⟨939368, by decide⟩
    (prefixPartial 11 71794) = some ⟨11, 2, 0, 939368, 71794, 2221, 262144⟩ := by
  decide +kernel

theorem context_11_71794_939368 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71794 ⟨939368, by decide⟩ :=
  accepted_of_selected 11 71794 ⟨939368, by decide⟩ ⟨11, 2, 0, 939368, 71794, 2221, 262144⟩
    (by decide) selected_cut_35683

theorem selected_cut_35684 : selected 10 ⟨939396, by decide⟩
    (prefixPartial 11 71795) = some ⟨11, 2, 0, 939396, 71795, 2053, 262144⟩ := by
  decide +kernel

theorem context_11_71795_939396 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71795 ⟨939396, by decide⟩ :=
  accepted_of_selected 11 71795 ⟨939396, by decide⟩ ⟨11, 2, 0, 939396, 71795, 2053, 262144⟩
    (by decide) selected_cut_35684

theorem unmarked_context_10_17948_939397 : frontier 11 ⟨939397, by decide⟩
    (prefixCache 10 17948) (prefixPartial 10 17948) = false := by
  decide +kernel

theorem node_context_10_17948_939397 : EJMOriginalGlobalDAGData.nodes 11 ⟨939397, by decide⟩ =
    .split (coordinate 10) (![⟨907917, by decide⟩,⟨939342, by decide⟩,⟨939368, by decide⟩,⟨939396, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17948_939397 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17948 ⟨939397, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17948
    ⟨939397, by decide⟩ (by decide) (![⟨907917, by decide⟩,⟨939342, by decide⟩,⟨939368, by decide⟩,⟨939396, by decide⟩]) unmarked_context_10_17948_939397 node_context_10_17948_939397
  intro a
  fin_cases a
  · exact context_11_71792_907917
  · exact context_11_71793_939342
  · exact context_11_71794_939368
  · exact context_11_71795_939396

theorem selected_cut_35685 : selected 10 ⟨939415, by decide⟩
    (prefixPartial 11 71796) = some ⟨11, 2, 0, 939415, 71796, 1661, 262144⟩ := by
  decide +kernel

theorem context_11_71796_939415 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71796 ⟨939415, by decide⟩ :=
  accepted_of_selected 11 71796 ⟨939415, by decide⟩ ⟨11, 2, 0, 939415, 71796, 1661, 262144⟩
    (by decide) selected_cut_35685

theorem selected_cut_35686 : selected 10 ⟨939430, by decide⟩
    (prefixPartial 11 71797) = some ⟨11, 2, 0, 939430, 71797, 1085, 262144⟩ := by
  decide +kernel

theorem context_11_71797_939430 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71797 ⟨939430, by decide⟩ :=
  accepted_of_selected 11 71797 ⟨939430, by decide⟩ ⟨11, 2, 0, 939430, 71797, 1085, 262144⟩
    (by decide) selected_cut_35686

theorem selected_cut_35687 : selected 10 ⟨939447, by decide⟩
    (prefixPartial 11 71798) = some ⟨11, 2, 0, 939447, 71798, 1417, 262144⟩ := by
  decide +kernel

theorem context_11_71798_939447 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71798 ⟨939447, by decide⟩ :=
  accepted_of_selected 11 71798 ⟨939447, by decide⟩ ⟨11, 2, 0, 939447, 71798, 1417, 262144⟩
    (by decide) selected_cut_35687

theorem selected_cut_35688 : selected 10 ⟨939464, by decide⟩
    (prefixPartial 11 71799) = some ⟨11, 2, 0, 939464, 71799, 1009, 262144⟩ := by
  decide +kernel

theorem context_11_71799_939464 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71799 ⟨939464, by decide⟩ :=
  accepted_of_selected 11 71799 ⟨939464, by decide⟩ ⟨11, 2, 0, 939464, 71799, 1009, 262144⟩
    (by decide) selected_cut_35688

theorem unmarked_context_10_17949_939465 : frontier 11 ⟨939465, by decide⟩
    (prefixCache 10 17949) (prefixPartial 10 17949) = false := by
  decide +kernel

theorem node_context_10_17949_939465 : EJMOriginalGlobalDAGData.nodes 11 ⟨939465, by decide⟩ =
    .split (coordinate 10) (![⟨939415, by decide⟩,⟨939430, by decide⟩,⟨939447, by decide⟩,⟨939464, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17949_939465 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17949 ⟨939465, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17949
    ⟨939465, by decide⟩ (by decide) (![⟨939415, by decide⟩,⟨939430, by decide⟩,⟨939447, by decide⟩,⟨939464, by decide⟩]) unmarked_context_10_17949_939465 node_context_10_17949_939465
  intro a
  fin_cases a
  · exact context_11_71796_939415
  · exact context_11_71797_939430
  · exact context_11_71798_939447
  · exact context_11_71799_939464

theorem selected_cut_35689 : selected 11 ⟨939516, by decide⟩
    (prefixPartial 10 17950) = some ⟨10, 2, 0, 939516, 17950, 3569, 1048576⟩ := by
  decide +kernel

theorem context_10_17950_939516 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17950 ⟨939516, by decide⟩ :=
  accepted_of_selected 10 17950 ⟨939516, by decide⟩ ⟨10, 2, 0, 939516, 17950, 3569, 1048576⟩
    (by decide) selected_cut_35689

theorem selected_cut_35690 : selected 11 ⟨939547, by decide⟩
    (prefixPartial 10 17951) = some ⟨10, 2, 0, 939547, 17951, 1033, 1048576⟩ := by
  decide +kernel

theorem context_10_17951_939547 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17951 ⟨939547, by decide⟩ :=
  accepted_of_selected 10 17951 ⟨939547, by decide⟩ ⟨10, 2, 0, 939547, 17951, 1033, 1048576⟩
    (by decide) selected_cut_35690

theorem unmarked_context_9_4487_939548 : frontier 12 ⟨939548, by decide⟩
    (prefixCache 9 4487) (prefixPartial 9 4487) = false := by
  decide +kernel

theorem node_context_9_4487_939548 : EJMOriginalGlobalDAGData.nodes 12 ⟨939548, by decide⟩ =
    .split (coordinate 9) (![⟨939397, by decide⟩,⟨939465, by decide⟩,⟨939516, by decide⟩,⟨939547, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4487_939548 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4487 ⟨939548, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4487
    ⟨939548, by decide⟩ (by decide) (![⟨939397, by decide⟩,⟨939465, by decide⟩,⟨939516, by decide⟩,⟨939547, by decide⟩]) unmarked_context_9_4487_939548 node_context_9_4487_939548
  intro a
  fin_cases a
  · exact context_10_17948_939397
  · exact context_10_17949_939465
  · exact context_10_17950_939516
  · exact context_10_17951_939547

theorem unmarked_context_8_1121_939549 : frontier 13 ⟨939549, by decide⟩
    (prefixCache 8 1121) (prefixPartial 8 1121) = false := by
  decide +kernel

theorem node_context_8_1121_939549 : EJMOriginalGlobalDAGData.nodes 13 ⟨939549, by decide⟩ =
    .split (coordinate 8) (![⟨937674, by decide⟩,⟨938626, by decide⟩,⟨939322, by decide⟩,⟨939548, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1121_939549 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1121 ⟨939549, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1121
    ⟨939549, by decide⟩ (by decide) (![⟨937674, by decide⟩,⟨938626, by decide⟩,⟨939322, by decide⟩,⟨939548, by decide⟩]) unmarked_context_8_1121_939549 node_context_8_1121_939549
  intro a
  fin_cases a
  · exact context_9_4484_937674
  · exact context_9_4485_938626
  · exact context_9_4486_939322
  · exact context_9_4487_939548

theorem selected_cut_35691 : selected 10 ⟨167448, by decide⟩
    (prefixPartial 11 71808) = some ⟨11, 1, 0, 167448, 71808, 1, 262144⟩ := by
  decide +kernel

theorem context_11_71808_167448 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71808 ⟨167448, by decide⟩ :=
  accepted_of_selected 11 71808 ⟨167448, by decide⟩ ⟨11, 1, 0, 167448, 71808, 1, 262144⟩
    (by decide) selected_cut_35691

theorem selected_cut_35692 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 287236) = some ⟨12, 1, 0, 34034, 287236, 1, 65536⟩ := by
  decide +kernel

theorem context_12_287236_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287236 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 287236 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 287236, 1, 65536⟩
    (by decide) selected_cut_35692

theorem selected_cut_35693 : selected 9 ⟨939609, by decide⟩
    (prefixPartial 12 287237) = some ⟨12, 2, 0, 939609, 287237, 3821, 65536⟩ := by
  decide +kernel

theorem context_12_287237_939609 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287237 ⟨939609, by decide⟩ :=
  accepted_of_selected 12 287237 ⟨939609, by decide⟩ ⟨12, 2, 0, 939609, 287237, 3821, 65536⟩
    (by decide) selected_cut_35693

theorem selected_cut_35694 : selected 9 ⟨939668, by decide⟩
    (prefixPartial 12 287238) = some ⟨12, 2, 0, 939668, 287238, 3709, 65536⟩ := by
  decide +kernel

theorem context_12_287238_939668 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287238 ⟨939668, by decide⟩ :=
  accepted_of_selected 12 287238 ⟨939668, by decide⟩ ⟨12, 2, 0, 939668, 287238, 3709, 65536⟩
    (by decide) selected_cut_35694

theorem selected_cut_35695 : selected 8 ⟨939712, by decide⟩
    (prefixPartial 13 1148956) = some ⟨13, 2, 0, 939712, 1148956, 2129, 16384⟩ := by
  decide +kernel

theorem context_13_1148956_939712 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1148956 ⟨939712, by decide⟩ :=
  accepted_of_selected 13 1148956 ⟨939712, by decide⟩ ⟨13, 2, 0, 939712, 1148956, 2129, 16384⟩
    (by decide) selected_cut_35695

theorem selected_cut_35696 : selected 8 ⟨939719, by decide⟩
    (prefixPartial 13 1148957) = some ⟨13, 2, 0, 939719, 1148957, 601, 16384⟩ := by
  decide +kernel

theorem context_13_1148957_939719 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1148957 ⟨939719, by decide⟩ :=
  accepted_of_selected 13 1148957 ⟨939719, by decide⟩ ⟨13, 2, 0, 939719, 1148957, 601, 16384⟩
    (by decide) selected_cut_35696

theorem selected_cut_35697 : selected 8 ⟨939736, by decide⟩
    (prefixPartial 13 1148958) = some ⟨13, 2, 0, 939736, 1148958, 1109, 16384⟩ := by
  decide +kernel

theorem context_13_1148958_939736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1148958 ⟨939736, by decide⟩ :=
  accepted_of_selected 13 1148958 ⟨939736, by decide⟩ ⟨13, 2, 0, 939736, 1148958, 1109, 16384⟩
    (by decide) selected_cut_35697

theorem selected_cut_35698 : selected 8 ⟨939743, by decide⟩
    (prefixPartial 13 1148959) = some ⟨13, 2, 0, 939743, 1148959, 545, 16384⟩ := by
  decide +kernel

theorem context_13_1148959_939743 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1148959 ⟨939743, by decide⟩ :=
  accepted_of_selected 13 1148959 ⟨939743, by decide⟩ ⟨13, 2, 0, 939743, 1148959, 545, 16384⟩
    (by decide) selected_cut_35698

theorem unmarked_context_12_287239_939744 : frontier 9 ⟨939744, by decide⟩
    (prefixCache 12 287239) (prefixPartial 12 287239) = false := by
  decide +kernel

theorem node_context_12_287239_939744 : EJMOriginalGlobalDAGData.nodes 9 ⟨939744, by decide⟩ =
    .split (coordinate 12) (![⟨939712, by decide⟩,⟨939719, by decide⟩,⟨939736, by decide⟩,⟨939743, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_287239_939744 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287239 ⟨939744, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 287239
    ⟨939744, by decide⟩ (by decide) (![⟨939712, by decide⟩,⟨939719, by decide⟩,⟨939736, by decide⟩,⟨939743, by decide⟩]) unmarked_context_12_287239_939744 node_context_12_287239_939744
  intro a
  fin_cases a
  · exact context_13_1148956_939712
  · exact context_13_1148957_939719
  · exact context_13_1148958_939736
  · exact context_13_1148959_939743

theorem unmarked_context_11_71809_939745 : frontier 10 ⟨939745, by decide⟩
    (prefixCache 11 71809) (prefixPartial 11 71809) = false := by
  decide +kernel

theorem node_context_11_71809_939745 : EJMOriginalGlobalDAGData.nodes 10 ⟨939745, by decide⟩ =
    .split (coordinate 11) (![⟨34034, by decide⟩,⟨939609, by decide⟩,⟨939668, by decide⟩,⟨939744, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71809_939745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71809 ⟨939745, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71809
    ⟨939745, by decide⟩ (by decide) (![⟨34034, by decide⟩,⟨939609, by decide⟩,⟨939668, by decide⟩,⟨939744, by decide⟩]) unmarked_context_11_71809_939745 node_context_11_71809_939745
  intro a
  fin_cases a
  · exact context_12_287236_34034
  · exact context_12_287237_939609
  · exact context_12_287238_939668
  · exact context_12_287239_939744

theorem selected_cut_35699 : selected 8 ⟨939797, by decide⟩
    (prefixPartial 13 1148960) = some ⟨13, 2, 0, 939797, 1148960, 2041, 16384⟩ := by
  decide +kernel

theorem context_13_1148960_939797 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1148960 ⟨939797, by decide⟩ :=
  accepted_of_selected 13 1148960 ⟨939797, by decide⟩ ⟨13, 2, 0, 939797, 1148960, 2041, 16384⟩
    (by decide) selected_cut_35699

theorem selected_cut_35700 : selected 8 ⟨939829, by decide⟩
    (prefixPartial 13 1148961) = some ⟨13, 2, 0, 939829, 1148961, 1193, 16384⟩ := by
  decide +kernel

theorem context_13_1148961_939829 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1148961 ⟨939829, by decide⟩ :=
  accepted_of_selected 13 1148961 ⟨939829, by decide⟩ ⟨13, 2, 0, 939829, 1148961, 1193, 16384⟩
    (by decide) selected_cut_35700

theorem selected_cut_35701 : selected 8 ⟨939865, by decide⟩
    (prefixPartial 13 1148962) = some ⟨13, 2, 0, 939865, 1148962, 1441, 16384⟩ := by
  decide +kernel

theorem context_13_1148962_939865 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1148962 ⟨939865, by decide⟩ :=
  accepted_of_selected 13 1148962 ⟨939865, by decide⟩ ⟨13, 2, 0, 939865, 1148962, 1441, 16384⟩
    (by decide) selected_cut_35701

theorem selected_cut_35702 : selected 8 ⟨939873, by decide⟩
    (prefixPartial 13 1148963) = some ⟨13, 2, 0, 939873, 1148963, 749, 16384⟩ := by
  decide +kernel

theorem context_13_1148963_939873 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1148963 ⟨939873, by decide⟩ :=
  accepted_of_selected 13 1148963 ⟨939873, by decide⟩ ⟨13, 2, 0, 939873, 1148963, 749, 16384⟩
    (by decide) selected_cut_35702

theorem unmarked_context_12_287240_939874 : frontier 9 ⟨939874, by decide⟩
    (prefixCache 12 287240) (prefixPartial 12 287240) = false := by
  decide +kernel

theorem node_context_12_287240_939874 : EJMOriginalGlobalDAGData.nodes 9 ⟨939874, by decide⟩ =
    .split (coordinate 12) (![⟨939797, by decide⟩,⟨939829, by decide⟩,⟨939865, by decide⟩,⟨939873, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_287240_939874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287240 ⟨939874, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 287240
    ⟨939874, by decide⟩ (by decide) (![⟨939797, by decide⟩,⟨939829, by decide⟩,⟨939865, by decide⟩,⟨939873, by decide⟩]) unmarked_context_12_287240_939874 node_context_12_287240_939874
  intro a
  fin_cases a
  · exact context_13_1148960_939797
  · exact context_13_1148961_939829
  · exact context_13_1148962_939865
  · exact context_13_1148963_939873

theorem selected_cut_35703 : selected 8 ⟨939901, by decide⟩
    (prefixPartial 13 1148964) = some ⟨13, 2, 0, 939901, 1148964, 1509, 16384⟩ := by
  decide +kernel

theorem context_13_1148964_939901 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1148964 ⟨939901, by decide⟩ :=
  accepted_of_selected 13 1148964 ⟨939901, by decide⟩ ⟨13, 2, 0, 939901, 1148964, 1509, 16384⟩
    (by decide) selected_cut_35703

theorem selected_cut_35704 : selected 8 ⟨939919, by decide⟩
    (prefixPartial 13 1148965) = some ⟨13, 2, 0, 939919, 1148965, 853, 16384⟩ := by
  decide +kernel

theorem context_13_1148965_939919 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1148965 ⟨939919, by decide⟩ :=
  accepted_of_selected 13 1148965 ⟨939919, by decide⟩ ⟨13, 2, 0, 939919, 1148965, 853, 16384⟩
    (by decide) selected_cut_35704

theorem selected_cut_35705 : selected 8 ⟨939937, by decide⟩
    (prefixPartial 13 1148966) = some ⟨13, 2, 0, 939937, 1148966, 1177, 16384⟩ := by
  decide +kernel

theorem context_13_1148966_939937 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1148966 ⟨939937, by decide⟩ :=
  accepted_of_selected 13 1148966 ⟨939937, by decide⟩ ⟨13, 2, 0, 939937, 1148966, 1177, 16384⟩
    (by decide) selected_cut_35705

theorem selected_cut_35706 : selected 8 ⟨939943, by decide⟩
    (prefixPartial 13 1148967) = some ⟨13, 2, 0, 939943, 1148967, 597, 16384⟩ := by
  decide +kernel

theorem context_13_1148967_939943 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1148967 ⟨939943, by decide⟩ :=
  accepted_of_selected 13 1148967 ⟨939943, by decide⟩ ⟨13, 2, 0, 939943, 1148967, 597, 16384⟩
    (by decide) selected_cut_35706

theorem unmarked_context_12_287241_939944 : frontier 9 ⟨939944, by decide⟩
    (prefixCache 12 287241) (prefixPartial 12 287241) = false := by
  decide +kernel

theorem node_context_12_287241_939944 : EJMOriginalGlobalDAGData.nodes 9 ⟨939944, by decide⟩ =
    .split (coordinate 12) (![⟨939901, by decide⟩,⟨939919, by decide⟩,⟨939937, by decide⟩,⟨939943, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_287241_939944 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287241 ⟨939944, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 287241
    ⟨939944, by decide⟩ (by decide) (![⟨939901, by decide⟩,⟨939919, by decide⟩,⟨939937, by decide⟩,⟨939943, by decide⟩]) unmarked_context_12_287241_939944 node_context_12_287241_939944
  intro a
  fin_cases a
  · exact context_13_1148964_939901
  · exact context_13_1148965_939919
  · exact context_13_1148966_939937
  · exact context_13_1148967_939943

theorem selected_cut_35707 : selected 9 ⟨893903, by decide⟩
    (prefixPartial 12 287242) = some ⟨12, 1, 0, 893903, 287242, 1, 65536⟩ := by
  decide +kernel

theorem context_12_287242_893903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287242 ⟨893903, by decide⟩ :=
  accepted_of_selected 12 287242 ⟨893903, by decide⟩ ⟨12, 1, 0, 893903, 287242, 1, 65536⟩
    (by decide) selected_cut_35707

theorem selected_cut_35708 : selected 8 ⟨939977, by decide⟩
    (prefixPartial 13 1148972) = some ⟨13, 2, 0, 939977, 1148972, 1817, 16384⟩ := by
  decide +kernel

theorem context_13_1148972_939977 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1148972 ⟨939977, by decide⟩ :=
  accepted_of_selected 13 1148972 ⟨939977, by decide⟩ ⟨13, 2, 0, 939977, 1148972, 1817, 16384⟩
    (by decide) selected_cut_35708

theorem selected_cut_35709 : selected 8 ⟨939996, by decide⟩
    (prefixPartial 13 1148973) = some ⟨13, 2, 0, 939996, 1148973, 845, 16384⟩ := by
  decide +kernel

theorem context_13_1148973_939996 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1148973 ⟨939996, by decide⟩ :=
  accepted_of_selected 13 1148973 ⟨939996, by decide⟩ ⟨13, 2, 0, 939996, 1148973, 845, 16384⟩
    (by decide) selected_cut_35709

theorem selected_cut_35710 : selected 8 ⟨940016, by decide⟩
    (prefixPartial 13 1148974) = some ⟨13, 2, 0, 940016, 1148974, 1213, 16384⟩ := by
  decide +kernel

theorem context_13_1148974_940016 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1148974 ⟨940016, by decide⟩ :=
  accepted_of_selected 13 1148974 ⟨940016, by decide⟩ ⟨13, 2, 0, 940016, 1148974, 1213, 16384⟩
    (by decide) selected_cut_35710

theorem selected_cut_35711 : selected 8 ⟨940023, by decide⟩
    (prefixPartial 13 1148975) = some ⟨13, 2, 0, 940023, 1148975, 661, 16384⟩ := by
  decide +kernel

theorem context_13_1148975_940023 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1148975 ⟨940023, by decide⟩ :=
  accepted_of_selected 13 1148975 ⟨940023, by decide⟩ ⟨13, 2, 0, 940023, 1148975, 661, 16384⟩
    (by decide) selected_cut_35711

theorem unmarked_context_12_287243_940024 : frontier 9 ⟨940024, by decide⟩
    (prefixCache 12 287243) (prefixPartial 12 287243) = false := by
  decide +kernel

theorem node_context_12_287243_940024 : EJMOriginalGlobalDAGData.nodes 9 ⟨940024, by decide⟩ =
    .split (coordinate 12) (![⟨939977, by decide⟩,⟨939996, by decide⟩,⟨940016, by decide⟩,⟨940023, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_287243_940024 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287243 ⟨940024, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 287243
    ⟨940024, by decide⟩ (by decide) (![⟨939977, by decide⟩,⟨939996, by decide⟩,⟨940016, by decide⟩,⟨940023, by decide⟩]) unmarked_context_12_287243_940024 node_context_12_287243_940024
  intro a
  fin_cases a
  · exact context_13_1148972_939977
  · exact context_13_1148973_939996
  · exact context_13_1148974_940016
  · exact context_13_1148975_940023

theorem unmarked_context_11_71810_940025 : frontier 10 ⟨940025, by decide⟩
    (prefixCache 11 71810) (prefixPartial 11 71810) = false := by
  decide +kernel

theorem node_context_11_71810_940025 : EJMOriginalGlobalDAGData.nodes 10 ⟨940025, by decide⟩ =
    .split (coordinate 11) (![⟨939874, by decide⟩,⟨939944, by decide⟩,⟨893903, by decide⟩,⟨940024, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71810_940025 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71810 ⟨940025, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71810
    ⟨940025, by decide⟩ (by decide) (![⟨939874, by decide⟩,⟨939944, by decide⟩,⟨893903, by decide⟩,⟨940024, by decide⟩]) unmarked_context_11_71810_940025 node_context_11_71810_940025
  intro a
  fin_cases a
  · exact context_12_287240_939874
  · exact context_12_287241_939944
  · exact context_12_287242_893903
  · exact context_12_287243_940024

theorem selected_cut_35712 : selected 8 ⟨940059, by decide⟩
    (prefixPartial 13 1148976) = some ⟨13, 2, 0, 940059, 1148976, 1833, 16384⟩ := by
  decide +kernel

theorem context_13_1148976_940059 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1148976 ⟨940059, by decide⟩ :=
  accepted_of_selected 13 1148976 ⟨940059, by decide⟩ ⟨13, 2, 0, 940059, 1148976, 1833, 16384⟩
    (by decide) selected_cut_35712

theorem selected_cut_35713 : selected 8 ⟨940080, by decide⟩
    (prefixPartial 13 1148977) = some ⟨13, 2, 0, 940080, 1148977, 885, 16384⟩ := by
  decide +kernel

theorem context_13_1148977_940080 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1148977 ⟨940080, by decide⟩ :=
  accepted_of_selected 13 1148977 ⟨940080, by decide⟩ ⟨13, 2, 0, 940080, 1148977, 885, 16384⟩
    (by decide) selected_cut_35713

theorem selected_cut_35714 : selected 8 ⟨940102, by decide⟩
    (prefixPartial 13 1148978) = some ⟨13, 2, 0, 940102, 1148978, 1257, 16384⟩ := by
  decide +kernel

theorem context_13_1148978_940102 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1148978 ⟨940102, by decide⟩ :=
  accepted_of_selected 13 1148978 ⟨940102, by decide⟩ ⟨13, 2, 0, 940102, 1148978, 1257, 16384⟩
    (by decide) selected_cut_35714

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
