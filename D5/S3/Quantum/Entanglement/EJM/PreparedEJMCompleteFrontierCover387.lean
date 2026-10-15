/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover386
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_37155 : selected 9 ⟨992671, by decide⟩
    (prefixPartial 12 299382) = some ⟨12, 2, 0, 992671, 299382, 1509, 65536⟩ := by
  decide +kernel

theorem context_12_299382_992671 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299382 ⟨992671, by decide⟩ :=
  accepted_of_selected 12 299382 ⟨992671, by decide⟩ ⟨12, 2, 0, 992671, 299382, 1509, 65536⟩
    (by decide) selected_cut_37155

theorem selected_cut_37156 : selected 9 ⟨992690, by decide⟩
    (prefixPartial 12 299383) = some ⟨12, 2, 0, 992690, 299383, 1581, 65536⟩ := by
  decide +kernel

theorem context_12_299383_992690 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299383 ⟨992690, by decide⟩ :=
  accepted_of_selected 12 299383 ⟨992690, by decide⟩ ⟨12, 2, 0, 992690, 299383, 1581, 65536⟩
    (by decide) selected_cut_37156

theorem unmarked_context_11_74845_992691 : frontier 10 ⟨992691, by decide⟩
    (prefixCache 11 74845) (prefixPartial 11 74845) = false := by
  decide +kernel

theorem node_context_11_74845_992691 : EJMOriginalGlobalDAGData.nodes 10 ⟨992691, by decide⟩ =
    .split (coordinate 11) (![⟨992651, by decide⟩,⟨891951, by decide⟩,⟨992671, by decide⟩,⟨992690, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_74845_992691 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74845 ⟨992691, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 74845
    ⟨992691, by decide⟩ (by decide) (![⟨992651, by decide⟩,⟨891951, by decide⟩,⟨992671, by decide⟩,⟨992690, by decide⟩]) unmarked_context_11_74845_992691 node_context_11_74845_992691
  intro a
  fin_cases a
  · exact context_12_299380_992651
  · exact context_12_299381_891951
  · exact context_12_299382_992671
  · exact context_12_299383_992690

theorem selected_cut_37157 : selected 9 ⟨992712, by decide⟩
    (prefixPartial 12 299384) = some ⟨12, 2, 0, 992712, 299384, 1661, 65536⟩ := by
  decide +kernel

theorem context_12_299384_992712 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299384 ⟨992712, by decide⟩ :=
  accepted_of_selected 12 299384 ⟨992712, by decide⟩ ⟨12, 2, 0, 992712, 299384, 1661, 65536⟩
    (by decide) selected_cut_37157

theorem selected_cut_37158 : selected 9 ⟨992735, by decide⟩
    (prefixPartial 12 299385) = some ⟨12, 2, 0, 992735, 299385, 1785, 65536⟩ := by
  decide +kernel

theorem context_12_299385_992735 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299385 ⟨992735, by decide⟩ :=
  accepted_of_selected 12 299385 ⟨992735, by decide⟩ ⟨12, 2, 0, 992735, 299385, 1785, 65536⟩
    (by decide) selected_cut_37158

theorem selected_cut_37159 : selected 9 ⟨992757, by decide⟩
    (prefixPartial 12 299386) = some ⟨12, 2, 0, 992757, 299386, 1585, 65536⟩ := by
  decide +kernel

theorem context_12_299386_992757 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299386 ⟨992757, by decide⟩ :=
  accepted_of_selected 12 299386 ⟨992757, by decide⟩ ⟨12, 2, 0, 992757, 299386, 1585, 65536⟩
    (by decide) selected_cut_37159

theorem selected_cut_37160 : selected 9 ⟨992779, by decide⟩
    (prefixPartial 12 299387) = some ⟨12, 2, 0, 992779, 299387, 1573, 65536⟩ := by
  decide +kernel

theorem context_12_299387_992779 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299387 ⟨992779, by decide⟩ :=
  accepted_of_selected 12 299387 ⟨992779, by decide⟩ ⟨12, 2, 0, 992779, 299387, 1573, 65536⟩
    (by decide) selected_cut_37160

theorem unmarked_context_11_74846_992780 : frontier 10 ⟨992780, by decide⟩
    (prefixCache 11 74846) (prefixPartial 11 74846) = false := by
  decide +kernel

theorem node_context_11_74846_992780 : EJMOriginalGlobalDAGData.nodes 10 ⟨992780, by decide⟩ =
    .split (coordinate 11) (![⟨992712, by decide⟩,⟨992735, by decide⟩,⟨992757, by decide⟩,⟨992779, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_74846_992780 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74846 ⟨992780, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 74846
    ⟨992780, by decide⟩ (by decide) (![⟨992712, by decide⟩,⟨992735, by decide⟩,⟨992757, by decide⟩,⟨992779, by decide⟩]) unmarked_context_11_74846_992780 node_context_11_74846_992780
  intro a
  fin_cases a
  · exact context_12_299384_992712
  · exact context_12_299385_992735
  · exact context_12_299386_992757
  · exact context_12_299387_992779

theorem selected_cut_37161 : selected 9 ⟨992798, by decide⟩
    (prefixPartial 12 299388) = some ⟨12, 2, 0, 992798, 299388, 1501, 65536⟩ := by
  decide +kernel

theorem context_12_299388_992798 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299388 ⟨992798, by decide⟩ :=
  accepted_of_selected 12 299388 ⟨992798, by decide⟩ ⟨12, 2, 0, 992798, 299388, 1501, 65536⟩
    (by decide) selected_cut_37161

theorem selected_cut_37162 : selected 9 ⟨992829, by decide⟩
    (prefixPartial 12 299389) = some ⟨12, 2, 0, 992829, 299389, 1669, 65536⟩ := by
  decide +kernel

theorem context_12_299389_992829 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299389 ⟨992829, by decide⟩ :=
  accepted_of_selected 12 299389 ⟨992829, by decide⟩ ⟨12, 2, 0, 992829, 299389, 1669, 65536⟩
    (by decide) selected_cut_37162

theorem selected_cut_37163 : selected 9 ⟨992846, by decide⟩
    (prefixPartial 12 299390) = some ⟨12, 2, 0, 992846, 299390, 1341, 65536⟩ := by
  decide +kernel

theorem context_12_299390_992846 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299390 ⟨992846, by decide⟩ :=
  accepted_of_selected 12 299390 ⟨992846, by decide⟩ ⟨12, 2, 0, 992846, 299390, 1341, 65536⟩
    (by decide) selected_cut_37163

theorem selected_cut_37164 : selected 9 ⟨992869, by decide⟩
    (prefixPartial 12 299391) = some ⟨12, 2, 0, 992869, 299391, 1489, 65536⟩ := by
  decide +kernel

theorem context_12_299391_992869 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299391 ⟨992869, by decide⟩ :=
  accepted_of_selected 12 299391 ⟨992869, by decide⟩ ⟨12, 2, 0, 992869, 299391, 1489, 65536⟩
    (by decide) selected_cut_37164

theorem unmarked_context_11_74847_992870 : frontier 10 ⟨992870, by decide⟩
    (prefixCache 11 74847) (prefixPartial 11 74847) = false := by
  decide +kernel

theorem node_context_11_74847_992870 : EJMOriginalGlobalDAGData.nodes 10 ⟨992870, by decide⟩ =
    .split (coordinate 11) (![⟨992798, by decide⟩,⟨992829, by decide⟩,⟨992846, by decide⟩,⟨992869, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_74847_992870 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74847 ⟨992870, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 74847
    ⟨992870, by decide⟩ (by decide) (![⟨992798, by decide⟩,⟨992829, by decide⟩,⟨992846, by decide⟩,⟨992869, by decide⟩]) unmarked_context_11_74847_992870 node_context_11_74847_992870
  intro a
  fin_cases a
  · exact context_12_299388_992798
  · exact context_12_299389_992829
  · exact context_12_299390_992846
  · exact context_12_299391_992869

theorem unmarked_context_10_18711_992871 : frontier 11 ⟨992871, by decide⟩
    (prefixCache 10 18711) (prefixPartial 10 18711) = false := by
  decide +kernel

theorem node_context_10_18711_992871 : EJMOriginalGlobalDAGData.nodes 11 ⟨992871, by decide⟩ =
    .split (coordinate 10) (![⟨992626, by decide⟩,⟨992691, by decide⟩,⟨992780, by decide⟩,⟨992870, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18711_992871 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18711 ⟨992871, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18711
    ⟨992871, by decide⟩ (by decide) (![⟨992626, by decide⟩,⟨992691, by decide⟩,⟨992780, by decide⟩,⟨992870, by decide⟩]) unmarked_context_10_18711_992871 node_context_10_18711_992871
  intro a
  fin_cases a
  · exact context_11_74844_992626
  · exact context_11_74845_992691
  · exact context_11_74846_992780
  · exact context_11_74847_992870

theorem unmarked_context_9_4677_992872 : frontier 12 ⟨992872, by decide⟩
    (prefixCache 9 4677) (prefixPartial 9 4677) = false := by
  decide +kernel

theorem node_context_9_4677_992872 : EJMOriginalGlobalDAGData.nodes 12 ⟨992872, by decide⟩ =
    .split (coordinate 9) (![⟨992128, by decide⟩,⟨893098, by decide⟩,⟨992548, by decide⟩,⟨992871, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4677_992872 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4677 ⟨992872, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4677
    ⟨992872, by decide⟩ (by decide) (![⟨992128, by decide⟩,⟨893098, by decide⟩,⟨992548, by decide⟩,⟨992871, by decide⟩]) unmarked_context_9_4677_992872 node_context_9_4677_992872
  intro a
  fin_cases a
  · exact context_10_18708_992128
  · exact context_10_18709_893098
  · exact context_10_18710_992548
  · exact context_10_18711_992871

theorem selected_cut_37165 : selected 10 ⟨907917, by decide⟩
    (prefixPartial 11 74848) = some ⟨11, 1, 0, 907917, 74848, 1, 262144⟩ := by
  decide +kernel

theorem context_11_74848_907917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74848 ⟨907917, by decide⟩ :=
  accepted_of_selected 11 74848 ⟨907917, by decide⟩ ⟨11, 1, 0, 907917, 74848, 1, 262144⟩
    (by decide) selected_cut_37165

theorem selected_cut_37166 : selected 10 ⟨992912, by decide⟩
    (prefixPartial 11 74849) = some ⟨11, 2, 0, 992912, 74849, 2637, 262144⟩ := by
  decide +kernel

theorem context_11_74849_992912 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74849 ⟨992912, by decide⟩ :=
  accepted_of_selected 11 74849 ⟨992912, by decide⟩ ⟨11, 2, 0, 992912, 74849, 2637, 262144⟩
    (by decide) selected_cut_37166

theorem selected_cut_37167 : selected 10 ⟨992962, by decide⟩
    (prefixPartial 11 74850) = some ⟨11, 2, 0, 992962, 74850, 3605, 262144⟩ := by
  decide +kernel

theorem context_11_74850_992962 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74850 ⟨992962, by decide⟩ :=
  accepted_of_selected 11 74850 ⟨992962, by decide⟩ ⟨11, 2, 0, 992962, 74850, 3605, 262144⟩
    (by decide) selected_cut_37167

theorem selected_cut_37168 : selected 10 ⟨993000, by decide⟩
    (prefixPartial 11 74851) = some ⟨11, 2, 0, 993000, 74851, 3281, 262144⟩ := by
  decide +kernel

theorem context_11_74851_993000 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74851 ⟨993000, by decide⟩ :=
  accepted_of_selected 11 74851 ⟨993000, by decide⟩ ⟨11, 2, 0, 993000, 74851, 3281, 262144⟩
    (by decide) selected_cut_37168

theorem unmarked_context_10_18712_993001 : frontier 11 ⟨993001, by decide⟩
    (prefixCache 10 18712) (prefixPartial 10 18712) = false := by
  decide +kernel

theorem node_context_10_18712_993001 : EJMOriginalGlobalDAGData.nodes 11 ⟨993001, by decide⟩ =
    .split (coordinate 10) (![⟨907917, by decide⟩,⟨992912, by decide⟩,⟨992962, by decide⟩,⟨993000, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18712_993001 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18712 ⟨993001, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18712
    ⟨993001, by decide⟩ (by decide) (![⟨907917, by decide⟩,⟨992912, by decide⟩,⟨992962, by decide⟩,⟨993000, by decide⟩]) unmarked_context_10_18712_993001 node_context_10_18712_993001
  intro a
  fin_cases a
  · exact context_11_74848_907917
  · exact context_11_74849_992912
  · exact context_11_74850_992962
  · exact context_11_74851_993000

theorem selected_cut_37169 : selected 10 ⟨993043, by decide⟩
    (prefixPartial 11 74852) = some ⟨11, 2, 0, 993043, 74852, 2625, 262144⟩ := by
  decide +kernel

theorem context_11_74852_993043 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74852 ⟨993043, by decide⟩ :=
  accepted_of_selected 11 74852 ⟨993043, by decide⟩ ⟨11, 2, 0, 993043, 74852, 2625, 262144⟩
    (by decide) selected_cut_37169

theorem selected_cut_37170 : selected 10 ⟨993068, by decide⟩
    (prefixPartial 11 74853) = some ⟨11, 2, 0, 993068, 74853, 1801, 262144⟩ := by
  decide +kernel

theorem context_11_74853_993068 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74853 ⟨993068, by decide⟩ :=
  accepted_of_selected 11 74853 ⟨993068, by decide⟩ ⟨11, 2, 0, 993068, 74853, 1801, 262144⟩
    (by decide) selected_cut_37170

theorem selected_cut_37171 : selected 10 ⟨993098, by decide⟩
    (prefixPartial 11 74854) = some ⟨11, 2, 0, 993098, 74854, 2741, 262144⟩ := by
  decide +kernel

theorem context_11_74854_993098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74854 ⟨993098, by decide⟩ :=
  accepted_of_selected 11 74854 ⟨993098, by decide⟩ ⟨11, 2, 0, 993098, 74854, 2741, 262144⟩
    (by decide) selected_cut_37171

theorem selected_cut_37172 : selected 10 ⟨993131, by decide⟩
    (prefixPartial 11 74855) = some ⟨11, 2, 0, 993131, 74855, 2661, 262144⟩ := by
  decide +kernel

theorem context_11_74855_993131 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74855 ⟨993131, by decide⟩ :=
  accepted_of_selected 11 74855 ⟨993131, by decide⟩ ⟨11, 2, 0, 993131, 74855, 2661, 262144⟩
    (by decide) selected_cut_37172

theorem unmarked_context_10_18713_993132 : frontier 11 ⟨993132, by decide⟩
    (prefixCache 10 18713) (prefixPartial 10 18713) = false := by
  decide +kernel

theorem node_context_10_18713_993132 : EJMOriginalGlobalDAGData.nodes 11 ⟨993132, by decide⟩ =
    .split (coordinate 10) (![⟨993043, by decide⟩,⟨993068, by decide⟩,⟨993098, by decide⟩,⟨993131, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18713_993132 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18713 ⟨993132, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18713
    ⟨993132, by decide⟩ (by decide) (![⟨993043, by decide⟩,⟨993068, by decide⟩,⟨993098, by decide⟩,⟨993131, by decide⟩]) unmarked_context_10_18713_993132 node_context_10_18713_993132
  intro a
  fin_cases a
  · exact context_11_74852_993043
  · exact context_11_74853_993068
  · exact context_11_74854_993098
  · exact context_11_74855_993131

theorem selected_cut_37173 : selected 10 ⟨993162, by decide⟩
    (prefixPartial 11 74856) = some ⟨11, 2, 0, 993162, 74856, 2461, 262144⟩ := by
  decide +kernel

theorem context_11_74856_993162 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74856 ⟨993162, by decide⟩ :=
  accepted_of_selected 11 74856 ⟨993162, by decide⟩ ⟨11, 2, 0, 993162, 74856, 2461, 262144⟩
    (by decide) selected_cut_37173

theorem selected_cut_37174 : selected 10 ⟨993182, by decide⟩
    (prefixPartial 11 74857) = some ⟨11, 2, 0, 993182, 74857, 1637, 262144⟩ := by
  decide +kernel

theorem context_11_74857_993182 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74857 ⟨993182, by decide⟩ :=
  accepted_of_selected 11 74857 ⟨993182, by decide⟩ ⟨11, 2, 0, 993182, 74857, 1637, 262144⟩
    (by decide) selected_cut_37174

theorem selected_cut_37175 : selected 10 ⟨993226, by decide⟩
    (prefixPartial 11 74858) = some ⟨11, 2, 0, 993226, 74858, 1953, 262144⟩ := by
  decide +kernel

theorem context_11_74858_993226 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74858 ⟨993226, by decide⟩ :=
  accepted_of_selected 11 74858 ⟨993226, by decide⟩ ⟨11, 2, 0, 993226, 74858, 1953, 262144⟩
    (by decide) selected_cut_37175

theorem selected_cut_37176 : selected 10 ⟨993253, by decide⟩
    (prefixPartial 11 74859) = some ⟨11, 2, 0, 993253, 74859, 2313, 262144⟩ := by
  decide +kernel

theorem context_11_74859_993253 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74859 ⟨993253, by decide⟩ :=
  accepted_of_selected 11 74859 ⟨993253, by decide⟩ ⟨11, 2, 0, 993253, 74859, 2313, 262144⟩
    (by decide) selected_cut_37176

theorem unmarked_context_10_18714_993254 : frontier 11 ⟨993254, by decide⟩
    (prefixCache 10 18714) (prefixPartial 10 18714) = false := by
  decide +kernel

theorem node_context_10_18714_993254 : EJMOriginalGlobalDAGData.nodes 11 ⟨993254, by decide⟩ =
    .split (coordinate 10) (![⟨993162, by decide⟩,⟨993182, by decide⟩,⟨993226, by decide⟩,⟨993253, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18714_993254 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18714 ⟨993254, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18714
    ⟨993254, by decide⟩ (by decide) (![⟨993162, by decide⟩,⟨993182, by decide⟩,⟨993226, by decide⟩,⟨993253, by decide⟩]) unmarked_context_10_18714_993254 node_context_10_18714_993254
  intro a
  fin_cases a
  · exact context_11_74856_993162
  · exact context_11_74857_993182
  · exact context_11_74858_993226
  · exact context_11_74859_993253

theorem selected_cut_37177 : selected 10 ⟨993279, by decide⟩
    (prefixPartial 11 74860) = some ⟨11, 2, 0, 993279, 74860, 1925, 262144⟩ := by
  decide +kernel

theorem context_11_74860_993279 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74860 ⟨993279, by decide⟩ :=
  accepted_of_selected 11 74860 ⟨993279, by decide⟩ ⟨11, 2, 0, 993279, 74860, 1925, 262144⟩
    (by decide) selected_cut_37177

theorem selected_cut_37178 : selected 10 ⟨993298, by decide⟩
    (prefixPartial 11 74861) = some ⟨11, 2, 0, 993298, 74861, 1333, 262144⟩ := by
  decide +kernel

theorem context_11_74861_993298 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74861 ⟨993298, by decide⟩ :=
  accepted_of_selected 11 74861 ⟨993298, by decide⟩ ⟨11, 2, 0, 993298, 74861, 1333, 262144⟩
    (by decide) selected_cut_37178

theorem selected_cut_37179 : selected 10 ⟨993322, by decide⟩
    (prefixPartial 11 74862) = some ⟨11, 2, 0, 993322, 74862, 1981, 262144⟩ := by
  decide +kernel

theorem context_11_74862_993322 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74862 ⟨993322, by decide⟩ :=
  accepted_of_selected 11 74862 ⟨993322, by decide⟩ ⟨11, 2, 0, 993322, 74862, 1981, 262144⟩
    (by decide) selected_cut_37179

theorem selected_cut_37180 : selected 10 ⟨993339, by decide⟩
    (prefixPartial 11 74863) = some ⟨11, 2, 0, 993339, 74863, 1745, 262144⟩ := by
  decide +kernel

theorem context_11_74863_993339 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74863 ⟨993339, by decide⟩ :=
  accepted_of_selected 11 74863 ⟨993339, by decide⟩ ⟨11, 2, 0, 993339, 74863, 1745, 262144⟩
    (by decide) selected_cut_37180

theorem unmarked_context_10_18715_993340 : frontier 11 ⟨993340, by decide⟩
    (prefixCache 10 18715) (prefixPartial 10 18715) = false := by
  decide +kernel

theorem node_context_10_18715_993340 : EJMOriginalGlobalDAGData.nodes 11 ⟨993340, by decide⟩ =
    .split (coordinate 10) (![⟨993279, by decide⟩,⟨993298, by decide⟩,⟨993322, by decide⟩,⟨993339, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18715_993340 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18715 ⟨993340, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18715
    ⟨993340, by decide⟩ (by decide) (![⟨993279, by decide⟩,⟨993298, by decide⟩,⟨993322, by decide⟩,⟨993339, by decide⟩]) unmarked_context_10_18715_993340 node_context_10_18715_993340
  intro a
  fin_cases a
  · exact context_11_74860_993279
  · exact context_11_74861_993298
  · exact context_11_74862_993322
  · exact context_11_74863_993339

theorem unmarked_context_9_4678_993341 : frontier 12 ⟨993341, by decide⟩
    (prefixCache 9 4678) (prefixPartial 9 4678) = false := by
  decide +kernel

theorem node_context_9_4678_993341 : EJMOriginalGlobalDAGData.nodes 12 ⟨993341, by decide⟩ =
    .split (coordinate 9) (![⟨993001, by decide⟩,⟨993132, by decide⟩,⟨993254, by decide⟩,⟨993340, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4678_993341 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4678 ⟨993341, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4678
    ⟨993341, by decide⟩ (by decide) (![⟨993001, by decide⟩,⟨993132, by decide⟩,⟨993254, by decide⟩,⟨993340, by decide⟩]) unmarked_context_9_4678_993341 node_context_9_4678_993341
  intro a
  fin_cases a
  · exact context_10_18712_993001
  · exact context_10_18713_993132
  · exact context_10_18714_993254
  · exact context_10_18715_993340

theorem selected_cut_37181 : selected 10 ⟨907917, by decide⟩
    (prefixPartial 11 74864) = some ⟨11, 1, 0, 907917, 74864, 1, 262144⟩ := by
  decide +kernel

theorem context_11_74864_907917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74864 ⟨907917, by decide⟩ :=
  accepted_of_selected 11 74864 ⟨907917, by decide⟩ ⟨11, 1, 0, 907917, 74864, 1, 262144⟩
    (by decide) selected_cut_37181

theorem selected_cut_37182 : selected 10 ⟨993359, by decide⟩
    (prefixPartial 11 74865) = some ⟨11, 2, 0, 993359, 74865, 1693, 262144⟩ := by
  decide +kernel

theorem context_11_74865_993359 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74865 ⟨993359, by decide⟩ :=
  accepted_of_selected 11 74865 ⟨993359, by decide⟩ ⟨11, 2, 0, 993359, 74865, 1693, 262144⟩
    (by decide) selected_cut_37182

theorem selected_cut_37183 : selected 10 ⟨993376, by decide⟩
    (prefixPartial 11 74866) = some ⟨11, 2, 0, 993376, 74866, 2117, 262144⟩ := by
  decide +kernel

theorem context_11_74866_993376 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74866 ⟨993376, by decide⟩ :=
  accepted_of_selected 11 74866 ⟨993376, by decide⟩ ⟨11, 2, 0, 993376, 74866, 2117, 262144⟩
    (by decide) selected_cut_37183

theorem selected_cut_37184 : selected 10 ⟨993399, by decide⟩
    (prefixPartial 11 74867) = some ⟨11, 2, 0, 993399, 74867, 2141, 262144⟩ := by
  decide +kernel

theorem context_11_74867_993399 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74867 ⟨993399, by decide⟩ :=
  accepted_of_selected 11 74867 ⟨993399, by decide⟩ ⟨11, 2, 0, 993399, 74867, 2141, 262144⟩
    (by decide) selected_cut_37184

theorem unmarked_context_10_18716_993400 : frontier 11 ⟨993400, by decide⟩
    (prefixCache 10 18716) (prefixPartial 10 18716) = false := by
  decide +kernel

theorem node_context_10_18716_993400 : EJMOriginalGlobalDAGData.nodes 11 ⟨993400, by decide⟩ =
    .split (coordinate 10) (![⟨907917, by decide⟩,⟨993359, by decide⟩,⟨993376, by decide⟩,⟨993399, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18716_993400 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18716 ⟨993400, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18716
    ⟨993400, by decide⟩ (by decide) (![⟨907917, by decide⟩,⟨993359, by decide⟩,⟨993376, by decide⟩,⟨993399, by decide⟩]) unmarked_context_10_18716_993400 node_context_10_18716_993400
  intro a
  fin_cases a
  · exact context_11_74864_907917
  · exact context_11_74865_993359
  · exact context_11_74866_993376
  · exact context_11_74867_993399

theorem selected_cut_37185 : selected 10 ⟨993418, by decide⟩
    (prefixPartial 11 74868) = some ⟨11, 2, 0, 993418, 74868, 1661, 262144⟩ := by
  decide +kernel

theorem context_11_74868_993418 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74868 ⟨993418, by decide⟩ :=
  accepted_of_selected 11 74868 ⟨993418, by decide⟩ ⟨11, 2, 0, 993418, 74868, 1661, 262144⟩
    (by decide) selected_cut_37185

theorem selected_cut_37186 : selected 10 ⟨993433, by decide⟩
    (prefixPartial 11 74869) = some ⟨11, 2, 0, 993433, 74869, 1109, 262144⟩ := by
  decide +kernel

theorem context_11_74869_993433 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74869 ⟨993433, by decide⟩ :=
  accepted_of_selected 11 74869 ⟨993433, by decide⟩ ⟨11, 2, 0, 993433, 74869, 1109, 262144⟩
    (by decide) selected_cut_37186

theorem selected_cut_37187 : selected 10 ⟨993449, by decide⟩
    (prefixPartial 11 74870) = some ⟨11, 2, 0, 993449, 74870, 1449, 262144⟩ := by
  decide +kernel

theorem context_11_74870_993449 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74870 ⟨993449, by decide⟩ :=
  accepted_of_selected 11 74870 ⟨993449, by decide⟩ ⟨11, 2, 0, 993449, 74870, 1449, 262144⟩
    (by decide) selected_cut_37187

theorem selected_cut_37188 : selected 10 ⟨993467, by decide⟩
    (prefixPartial 11 74871) = some ⟨11, 2, 0, 993467, 74871, 1457, 262144⟩ := by
  decide +kernel

theorem context_11_74871_993467 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74871 ⟨993467, by decide⟩ :=
  accepted_of_selected 11 74871 ⟨993467, by decide⟩ ⟨11, 2, 0, 993467, 74871, 1457, 262144⟩
    (by decide) selected_cut_37188

theorem unmarked_context_10_18717_993468 : frontier 11 ⟨993468, by decide⟩
    (prefixCache 10 18717) (prefixPartial 10 18717) = false := by
  decide +kernel

theorem node_context_10_18717_993468 : EJMOriginalGlobalDAGData.nodes 11 ⟨993468, by decide⟩ =
    .split (coordinate 10) (![⟨993418, by decide⟩,⟨993433, by decide⟩,⟨993449, by decide⟩,⟨993467, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18717_993468 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18717 ⟨993468, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18717
    ⟨993468, by decide⟩ (by decide) (![⟨993418, by decide⟩,⟨993433, by decide⟩,⟨993449, by decide⟩,⟨993467, by decide⟩]) unmarked_context_10_18717_993468 node_context_10_18717_993468
  intro a
  fin_cases a
  · exact context_11_74868_993418
  · exact context_11_74869_993433
  · exact context_11_74870_993449
  · exact context_11_74871_993467

theorem selected_cut_37189 : selected 11 ⟨993521, by decide⟩
    (prefixPartial 10 18718) = some ⟨10, 2, 0, 993521, 18718, 3673, 1048576⟩ := by
  decide +kernel

theorem context_10_18718_993521 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18718 ⟨993521, by decide⟩ :=
  accepted_of_selected 10 18718 ⟨993521, by decide⟩ ⟨10, 2, 0, 993521, 18718, 3673, 1048576⟩
    (by decide) selected_cut_37189

theorem selected_cut_37190 : selected 11 ⟨993567, by decide⟩
    (prefixPartial 10 18719) = some ⟨10, 2, 0, 993567, 18719, 1133, 1048576⟩ := by
  decide +kernel

theorem context_10_18719_993567 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18719 ⟨993567, by decide⟩ :=
  accepted_of_selected 10 18719 ⟨993567, by decide⟩ ⟨10, 2, 0, 993567, 18719, 1133, 1048576⟩
    (by decide) selected_cut_37190

theorem unmarked_context_9_4679_993568 : frontier 12 ⟨993568, by decide⟩
    (prefixCache 9 4679) (prefixPartial 9 4679) = false := by
  decide +kernel

theorem node_context_9_4679_993568 : EJMOriginalGlobalDAGData.nodes 12 ⟨993568, by decide⟩ =
    .split (coordinate 9) (![⟨993400, by decide⟩,⟨993468, by decide⟩,⟨993521, by decide⟩,⟨993567, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4679_993568 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4679 ⟨993568, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4679
    ⟨993568, by decide⟩ (by decide) (![⟨993400, by decide⟩,⟨993468, by decide⟩,⟨993521, by decide⟩,⟨993567, by decide⟩]) unmarked_context_9_4679_993568 node_context_9_4679_993568
  intro a
  fin_cases a
  · exact context_10_18716_993400
  · exact context_10_18717_993468
  · exact context_10_18718_993521
  · exact context_10_18719_993567

theorem unmarked_context_8_1169_993569 : frontier 13 ⟨993569, by decide⟩
    (prefixCache 8 1169) (prefixPartial 8 1169) = false := by
  decide +kernel

theorem node_context_8_1169_993569 : EJMOriginalGlobalDAGData.nodes 13 ⟨993569, by decide⟩ =
    .split (coordinate 8) (![⟨991770, by decide⟩,⟨992872, by decide⟩,⟨993341, by decide⟩,⟨993568, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1169_993569 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1169 ⟨993569, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1169
    ⟨993569, by decide⟩ (by decide) (![⟨991770, by decide⟩,⟨992872, by decide⟩,⟨993341, by decide⟩,⟨993568, by decide⟩]) unmarked_context_8_1169_993569 node_context_8_1169_993569
  intro a
  fin_cases a
  · exact context_9_4676_991770
  · exact context_9_4677_992872
  · exact context_9_4678_993341
  · exact context_9_4679_993568

theorem selected_cut_37191 : selected 10 ⟨167448, by decide⟩
    (prefixPartial 11 74880) = some ⟨11, 1, 0, 167448, 74880, 1, 262144⟩ := by
  decide +kernel

theorem context_11_74880_167448 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74880 ⟨167448, by decide⟩ :=
  accepted_of_selected 11 74880 ⟨167448, by decide⟩ ⟨11, 1, 0, 167448, 74880, 1, 262144⟩
    (by decide) selected_cut_37191

theorem selected_cut_37192 : selected 8 ⟨993624, by decide⟩
    (prefixPartial 13 1198096) = some ⟨13, 2, 0, 993624, 1198096, 2337, 16384⟩ := by
  decide +kernel

theorem context_13_1198096_993624 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1198096 ⟨993624, by decide⟩ :=
  accepted_of_selected 13 1198096 ⟨993624, by decide⟩ ⟨13, 2, 0, 993624, 1198096, 2337, 16384⟩
    (by decide) selected_cut_37192

theorem selected_cut_37193 : selected 8 ⟨993656, by decide⟩
    (prefixPartial 13 1198097) = some ⟨13, 2, 0, 993656, 1198097, 1389, 16384⟩ := by
  decide +kernel

theorem context_13_1198097_993656 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1198097 ⟨993656, by decide⟩ :=
  accepted_of_selected 13 1198097 ⟨993656, by decide⟩ ⟨13, 2, 0, 993656, 1198097, 1389, 16384⟩
    (by decide) selected_cut_37193

theorem selected_cut_37194 : selected 8 ⟨993692, by decide⟩
    (prefixPartial 13 1198098) = some ⟨13, 2, 0, 993692, 1198098, 1253, 16384⟩ := by
  decide +kernel

theorem context_13_1198098_993692 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1198098 ⟨993692, by decide⟩ :=
  accepted_of_selected 13 1198098 ⟨993692, by decide⟩ ⟨13, 2, 0, 993692, 1198098, 1253, 16384⟩
    (by decide) selected_cut_37194

theorem selected_cut_37195 : selected 8 ⟨993702, by decide⟩
    (prefixPartial 13 1198099) = some ⟨13, 2, 0, 993702, 1198099, 685, 16384⟩ := by
  decide +kernel

theorem context_13_1198099_993702 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1198099 ⟨993702, by decide⟩ :=
  accepted_of_selected 13 1198099 ⟨993702, by decide⟩ ⟨13, 2, 0, 993702, 1198099, 685, 16384⟩
    (by decide) selected_cut_37195

theorem unmarked_context_12_299524_993703 : frontier 9 ⟨993703, by decide⟩
    (prefixCache 12 299524) (prefixPartial 12 299524) = false := by
  decide +kernel

theorem node_context_12_299524_993703 : EJMOriginalGlobalDAGData.nodes 9 ⟨993703, by decide⟩ =
    .split (coordinate 12) (![⟨993624, by decide⟩,⟨993656, by decide⟩,⟨993692, by decide⟩,⟨993702, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_299524_993703 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299524 ⟨993703, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 299524
    ⟨993703, by decide⟩ (by decide) (![⟨993624, by decide⟩,⟨993656, by decide⟩,⟨993692, by decide⟩,⟨993702, by decide⟩]) unmarked_context_12_299524_993703 node_context_12_299524_993703
  intro a
  fin_cases a
  · exact context_13_1198096_993624
  · exact context_13_1198097_993656
  · exact context_13_1198098_993692
  · exact context_13_1198099_993702

theorem selected_cut_37196 : selected 8 ⟨993737, by decide⟩
    (prefixPartial 13 1198100) = some ⟨13, 2, 0, 993737, 1198100, 1933, 16384⟩ := by
  decide +kernel

theorem context_13_1198100_993737 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1198100 ⟨993737, by decide⟩ :=
  accepted_of_selected 13 1198100 ⟨993737, by decide⟩ ⟨13, 2, 0, 993737, 1198100, 1933, 16384⟩
    (by decide) selected_cut_37196

theorem selected_cut_37197 : selected 8 ⟨993760, by decide⟩
    (prefixPartial 13 1198101) = some ⟨13, 2, 0, 993760, 1198101, 1369, 16384⟩ := by
  decide +kernel

theorem context_13_1198101_993760 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1198101 ⟨993760, by decide⟩ :=
  accepted_of_selected 13 1198101 ⟨993760, by decide⟩ ⟨13, 2, 0, 993760, 1198101, 1369, 16384⟩
    (by decide) selected_cut_37197

theorem selected_cut_37198 : selected 8 ⟨993778, by decide⟩
    (prefixPartial 13 1198102) = some ⟨13, 2, 0, 993778, 1198102, 1017, 16384⟩ := by
  decide +kernel

theorem context_13_1198102_993778 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1198102 ⟨993778, by decide⟩ :=
  accepted_of_selected 13 1198102 ⟨993778, by decide⟩ ⟨13, 2, 0, 993778, 1198102, 1017, 16384⟩
    (by decide) selected_cut_37198

theorem selected_cut_37199 : selected 8 ⟨993786, by decide⟩
    (prefixPartial 13 1198103) = some ⟨13, 2, 0, 993786, 1198103, 609, 16384⟩ := by
  decide +kernel

theorem context_13_1198103_993786 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1198103 ⟨993786, by decide⟩ :=
  accepted_of_selected 13 1198103 ⟨993786, by decide⟩ ⟨13, 2, 0, 993786, 1198103, 609, 16384⟩
    (by decide) selected_cut_37199

theorem unmarked_context_12_299525_993787 : frontier 9 ⟨993787, by decide⟩
    (prefixCache 12 299525) (prefixPartial 12 299525) = false := by
  decide +kernel

theorem node_context_12_299525_993787 : EJMOriginalGlobalDAGData.nodes 9 ⟨993787, by decide⟩ =
    .split (coordinate 12) (![⟨993737, by decide⟩,⟨993760, by decide⟩,⟨993778, by decide⟩,⟨993786, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_299525_993787 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299525 ⟨993787, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 299525
    ⟨993787, by decide⟩ (by decide) (![⟨993737, by decide⟩,⟨993760, by decide⟩,⟨993778, by decide⟩,⟨993786, by decide⟩]) unmarked_context_12_299525_993787 node_context_12_299525_993787
  intro a
  fin_cases a
  · exact context_13_1198100_993737
  · exact context_13_1198101_993760
  · exact context_13_1198102_993778
  · exact context_13_1198103_993786

theorem selected_cut_37200 : selected 8 ⟨993818, by decide⟩
    (prefixPartial 13 1198104) = some ⟨13, 2, 0, 993818, 1198104, 1669, 16384⟩ := by
  decide +kernel

theorem context_13_1198104_993818 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1198104 ⟨993818, by decide⟩ :=
  accepted_of_selected 13 1198104 ⟨993818, by decide⟩ ⟨13, 2, 0, 993818, 1198104, 1669, 16384⟩
    (by decide) selected_cut_37200

theorem selected_cut_37201 : selected 8 ⟨993838, by decide⟩
    (prefixPartial 13 1198105) = some ⟨13, 2, 0, 993838, 1198105, 1149, 16384⟩ := by
  decide +kernel

theorem context_13_1198105_993838 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1198105 ⟨993838, by decide⟩ :=
  accepted_of_selected 13 1198105 ⟨993838, by decide⟩ ⟨13, 2, 0, 993838, 1198105, 1149, 16384⟩
    (by decide) selected_cut_37201

theorem selected_cut_37202 : selected 8 ⟨993857, by decide⟩
    (prefixPartial 13 1198106) = some ⟨13, 2, 0, 993857, 1198106, 1065, 16384⟩ := by
  decide +kernel

theorem context_13_1198106_993857 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1198106 ⟨993857, by decide⟩ :=
  accepted_of_selected 13 1198106 ⟨993857, by decide⟩ ⟨13, 2, 0, 993857, 1198106, 1065, 16384⟩
    (by decide) selected_cut_37202

theorem selected_cut_37203 : selected 8 ⟨993865, by decide⟩
    (prefixPartial 13 1198107) = some ⟨13, 2, 0, 993865, 1198107, 637, 16384⟩ := by
  decide +kernel

theorem context_13_1198107_993865 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1198107 ⟨993865, by decide⟩ :=
  accepted_of_selected 13 1198107 ⟨993865, by decide⟩ ⟨13, 2, 0, 993865, 1198107, 637, 16384⟩
    (by decide) selected_cut_37203

theorem unmarked_context_12_299526_993866 : frontier 9 ⟨993866, by decide⟩
    (prefixCache 12 299526) (prefixPartial 12 299526) = false := by
  decide +kernel

theorem node_context_12_299526_993866 : EJMOriginalGlobalDAGData.nodes 9 ⟨993866, by decide⟩ =
    .split (coordinate 12) (![⟨993818, by decide⟩,⟨993838, by decide⟩,⟨993857, by decide⟩,⟨993865, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_299526_993866 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299526 ⟨993866, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 299526
    ⟨993866, by decide⟩ (by decide) (![⟨993818, by decide⟩,⟨993838, by decide⟩,⟨993857, by decide⟩,⟨993865, by decide⟩]) unmarked_context_12_299526_993866 node_context_12_299526_993866
  intro a
  fin_cases a
  · exact context_13_1198104_993818
  · exact context_13_1198105_993838
  · exact context_13_1198106_993857
  · exact context_13_1198107_993865

theorem selected_cut_37204 : selected 8 ⟨993906, by decide⟩
    (prefixPartial 13 1198108) = some ⟨13, 2, 0, 993906, 1198108, 1965, 16384⟩ := by
  decide +kernel

theorem context_13_1198108_993906 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1198108 ⟨993906, by decide⟩ :=
  accepted_of_selected 13 1198108 ⟨993906, by decide⟩ ⟨13, 2, 0, 993906, 1198108, 1965, 16384⟩
    (by decide) selected_cut_37204

theorem selected_cut_37205 : selected 8 ⟨993921, by decide⟩
    (prefixPartial 13 1198109) = some ⟨13, 2, 0, 993921, 1198109, 1017, 16384⟩ := by
  decide +kernel

theorem context_13_1198109_993921 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1198109 ⟨993921, by decide⟩ :=
  accepted_of_selected 13 1198109 ⟨993921, by decide⟩ ⟨13, 2, 0, 993921, 1198109, 1017, 16384⟩
    (by decide) selected_cut_37205

theorem selected_cut_37206 : selected 8 ⟨993941, by decide⟩
    (prefixPartial 13 1198110) = some ⟨13, 2, 0, 993941, 1198110, 1113, 16384⟩ := by
  decide +kernel

theorem context_13_1198110_993941 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1198110 ⟨993941, by decide⟩ :=
  accepted_of_selected 13 1198110 ⟨993941, by decide⟩ ⟨13, 2, 0, 993941, 1198110, 1113, 16384⟩
    (by decide) selected_cut_37206

theorem selected_cut_37207 : selected 8 ⟨993951, by decide⟩
    (prefixPartial 13 1198111) = some ⟨13, 2, 0, 993951, 1198111, 545, 16384⟩ := by
  decide +kernel

theorem context_13_1198111_993951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1198111 ⟨993951, by decide⟩ :=
  accepted_of_selected 13 1198111 ⟨993951, by decide⟩ ⟨13, 2, 0, 993951, 1198111, 545, 16384⟩
    (by decide) selected_cut_37207

theorem unmarked_context_12_299527_993952 : frontier 9 ⟨993952, by decide⟩
    (prefixCache 12 299527) (prefixPartial 12 299527) = false := by
  decide +kernel

theorem node_context_12_299527_993952 : EJMOriginalGlobalDAGData.nodes 9 ⟨993952, by decide⟩ =
    .split (coordinate 12) (![⟨993906, by decide⟩,⟨993921, by decide⟩,⟨993941, by decide⟩,⟨993951, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_299527_993952 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299527 ⟨993952, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 299527
    ⟨993952, by decide⟩ (by decide) (![⟨993906, by decide⟩,⟨993921, by decide⟩,⟨993941, by decide⟩,⟨993951, by decide⟩]) unmarked_context_12_299527_993952 node_context_12_299527_993952
  intro a
  fin_cases a
  · exact context_13_1198108_993906
  · exact context_13_1198109_993921
  · exact context_13_1198110_993941
  · exact context_13_1198111_993951

theorem unmarked_context_11_74881_993953 : frontier 10 ⟨993953, by decide⟩
    (prefixCache 11 74881) (prefixPartial 11 74881) = false := by
  decide +kernel

theorem node_context_11_74881_993953 : EJMOriginalGlobalDAGData.nodes 10 ⟨993953, by decide⟩ =
    .split (coordinate 11) (![⟨993703, by decide⟩,⟨993787, by decide⟩,⟨993866, by decide⟩,⟨993952, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_74881_993953 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74881 ⟨993953, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 74881
    ⟨993953, by decide⟩ (by decide) (![⟨993703, by decide⟩,⟨993787, by decide⟩,⟨993866, by decide⟩,⟨993952, by decide⟩]) unmarked_context_11_74881_993953 node_context_11_74881_993953
  intro a
  fin_cases a
  · exact context_12_299524_993703
  · exact context_12_299525_993787
  · exact context_12_299526_993866
  · exact context_12_299527_993952

theorem selected_cut_37208 : selected 8 ⟨993992, by decide⟩
    (prefixPartial 13 1198112) = some ⟨13, 2, 0, 993992, 1198112, 2061, 16384⟩ := by
  decide +kernel

theorem context_13_1198112_993992 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1198112 ⟨993992, by decide⟩ :=
  accepted_of_selected 13 1198112 ⟨993992, by decide⟩ ⟨13, 2, 0, 993992, 1198112, 2061, 16384⟩
    (by decide) selected_cut_37208

theorem selected_cut_37209 : selected 8 ⟨994015, by decide⟩
    (prefixPartial 13 1198113) = some ⟨13, 2, 0, 994015, 1198113, 1325, 16384⟩ := by
  decide +kernel

theorem context_13_1198113_994015 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1198113 ⟨994015, by decide⟩ :=
  accepted_of_selected 13 1198113 ⟨994015, by decide⟩ ⟨13, 2, 0, 994015, 1198113, 1325, 16384⟩
    (by decide) selected_cut_37209

theorem selected_cut_37210 : selected 8 ⟨994034, by decide⟩
    (prefixPartial 13 1198114) = some ⟨13, 2, 0, 994034, 1198114, 1181, 16384⟩ := by
  decide +kernel

theorem context_13_1198114_994034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1198114 ⟨994034, by decide⟩ :=
  accepted_of_selected 13 1198114 ⟨994034, by decide⟩ ⟨13, 2, 0, 994034, 1198114, 1181, 16384⟩
    (by decide) selected_cut_37210

theorem selected_cut_37211 : selected 8 ⟨994042, by decide⟩
    (prefixPartial 13 1198115) = some ⟨13, 2, 0, 994042, 1198115, 601, 16384⟩ := by
  decide +kernel

theorem context_13_1198115_994042 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1198115 ⟨994042, by decide⟩ :=
  accepted_of_selected 13 1198115 ⟨994042, by decide⟩ ⟨13, 2, 0, 994042, 1198115, 601, 16384⟩
    (by decide) selected_cut_37211

theorem unmarked_context_12_299528_994043 : frontier 9 ⟨994043, by decide⟩
    (prefixCache 12 299528) (prefixPartial 12 299528) = false := by
  decide +kernel

theorem node_context_12_299528_994043 : EJMOriginalGlobalDAGData.nodes 9 ⟨994043, by decide⟩ =
    .split (coordinate 12) (![⟨993992, by decide⟩,⟨994015, by decide⟩,⟨994034, by decide⟩,⟨994042, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_299528_994043 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299528 ⟨994043, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 299528
    ⟨994043, by decide⟩ (by decide) (![⟨993992, by decide⟩,⟨994015, by decide⟩,⟨994034, by decide⟩,⟨994042, by decide⟩]) unmarked_context_12_299528_994043 node_context_12_299528_994043
  intro a
  fin_cases a
  · exact context_13_1198112_993992
  · exact context_13_1198113_994015
  · exact context_13_1198114_994034
  · exact context_13_1198115_994042

theorem selected_cut_37212 : selected 8 ⟨994079, by decide⟩
    (prefixPartial 13 1198116) = some ⟨13, 2, 0, 994079, 1198116, 1889, 16384⟩ := by
  decide +kernel

theorem context_13_1198116_994079 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1198116 ⟨994079, by decide⟩ :=
  accepted_of_selected 13 1198116 ⟨994079, by decide⟩ ⟨13, 2, 0, 994079, 1198116, 1889, 16384⟩
    (by decide) selected_cut_37212

theorem selected_cut_37213 : selected 8 ⟨994100, by decide⟩
    (prefixPartial 13 1198117) = some ⟨13, 2, 0, 994100, 1198117, 1365, 16384⟩ := by
  decide +kernel

theorem context_13_1198117_994100 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1198117 ⟨994100, by decide⟩ :=
  accepted_of_selected 13 1198117 ⟨994100, by decide⟩ ⟨13, 2, 0, 994100, 1198117, 1365, 16384⟩
    (by decide) selected_cut_37213

theorem selected_cut_37214 : selected 8 ⟨994117, by decide⟩
    (prefixPartial 13 1198118) = some ⟨13, 2, 0, 994117, 1198118, 1057, 16384⟩ := by
  decide +kernel

theorem context_13_1198118_994117 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1198118 ⟨994117, by decide⟩ :=
  accepted_of_selected 13 1198118 ⟨994117, by decide⟩ ⟨13, 2, 0, 994117, 1198118, 1057, 16384⟩
    (by decide) selected_cut_37214

theorem selected_cut_37215 : selected 8 ⟨994125, by decide⟩
    (prefixPartial 13 1198119) = some ⟨13, 2, 0, 994125, 1198119, 593, 16384⟩ := by
  decide +kernel

theorem context_13_1198119_994125 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1198119 ⟨994125, by decide⟩ :=
  accepted_of_selected 13 1198119 ⟨994125, by decide⟩ ⟨13, 2, 0, 994125, 1198119, 593, 16384⟩
    (by decide) selected_cut_37215

theorem unmarked_context_12_299529_994126 : frontier 9 ⟨994126, by decide⟩
    (prefixCache 12 299529) (prefixPartial 12 299529) = false := by
  decide +kernel

theorem node_context_12_299529_994126 : EJMOriginalGlobalDAGData.nodes 9 ⟨994126, by decide⟩ =
    .split (coordinate 12) (![⟨994079, by decide⟩,⟨994100, by decide⟩,⟨994117, by decide⟩,⟨994125, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_299529_994126 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299529 ⟨994126, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 299529
    ⟨994126, by decide⟩ (by decide) (![⟨994079, by decide⟩,⟨994100, by decide⟩,⟨994117, by decide⟩,⟨994125, by decide⟩]) unmarked_context_12_299529_994126 node_context_12_299529_994126
  intro a
  fin_cases a
  · exact context_13_1198116_994079
  · exact context_13_1198117_994100
  · exact context_13_1198118_994117
  · exact context_13_1198119_994125

theorem selected_cut_37216 : selected 9 ⟨893903, by decide⟩
    (prefixPartial 12 299530) = some ⟨12, 1, 0, 893903, 299530, 1, 65536⟩ := by
  decide +kernel

theorem context_12_299530_893903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299530 ⟨893903, by decide⟩ :=
  accepted_of_selected 12 299530 ⟨893903, by decide⟩ ⟨12, 1, 0, 893903, 299530, 1, 65536⟩
    (by decide) selected_cut_37216

theorem selected_cut_37217 : selected 8 ⟨994166, by decide⟩
    (prefixPartial 13 1198124) = some ⟨13, 2, 0, 994166, 1198124, 1837, 16384⟩ := by
  decide +kernel

theorem context_13_1198124_994166 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1198124 ⟨994166, by decide⟩ :=
  accepted_of_selected 13 1198124 ⟨994166, by decide⟩ ⟨13, 2, 0, 994166, 1198124, 1837, 16384⟩
    (by decide) selected_cut_37217

theorem selected_cut_37218 : selected 8 ⟨994182, by decide⟩
    (prefixPartial 13 1198125) = some ⟨13, 2, 0, 994182, 1198125, 1113, 16384⟩ := by
  decide +kernel

theorem context_13_1198125_994182 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1198125 ⟨994182, by decide⟩ :=
  accepted_of_selected 13 1198125 ⟨994182, by decide⟩ ⟨13, 2, 0, 994182, 1198125, 1113, 16384⟩
    (by decide) selected_cut_37218

theorem selected_cut_37219 : selected 8 ⟨994200, by decide⟩
    (prefixPartial 13 1198126) = some ⟨13, 2, 0, 994200, 1198126, 1045, 16384⟩ := by
  decide +kernel

theorem context_13_1198126_994200 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1198126 ⟨994200, by decide⟩ :=
  accepted_of_selected 13 1198126 ⟨994200, by decide⟩ ⟨13, 2, 0, 994200, 1198126, 1045, 16384⟩
    (by decide) selected_cut_37219

theorem selected_cut_37220 : selected 8 ⟨994208, by decide⟩
    (prefixPartial 13 1198127) = some ⟨13, 2, 0, 994208, 1198127, 545, 16384⟩ := by
  decide +kernel

theorem context_13_1198127_994208 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1198127 ⟨994208, by decide⟩ :=
  accepted_of_selected 13 1198127 ⟨994208, by decide⟩ ⟨13, 2, 0, 994208, 1198127, 545, 16384⟩
    (by decide) selected_cut_37220

theorem unmarked_context_12_299531_994209 : frontier 9 ⟨994209, by decide⟩
    (prefixCache 12 299531) (prefixPartial 12 299531) = false := by
  decide +kernel

theorem node_context_12_299531_994209 : EJMOriginalGlobalDAGData.nodes 9 ⟨994209, by decide⟩ =
    .split (coordinate 12) (![⟨994166, by decide⟩,⟨994182, by decide⟩,⟨994200, by decide⟩,⟨994208, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_299531_994209 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299531 ⟨994209, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 299531
    ⟨994209, by decide⟩ (by decide) (![⟨994166, by decide⟩,⟨994182, by decide⟩,⟨994200, by decide⟩,⟨994208, by decide⟩]) unmarked_context_12_299531_994209 node_context_12_299531_994209
  intro a
  fin_cases a
  · exact context_13_1198124_994166
  · exact context_13_1198125_994182
  · exact context_13_1198126_994200
  · exact context_13_1198127_994208

theorem unmarked_context_11_74882_994210 : frontier 10 ⟨994210, by decide⟩
    (prefixCache 11 74882) (prefixPartial 11 74882) = false := by
  decide +kernel

theorem node_context_11_74882_994210 : EJMOriginalGlobalDAGData.nodes 10 ⟨994210, by decide⟩ =
    .split (coordinate 11) (![⟨994043, by decide⟩,⟨994126, by decide⟩,⟨893903, by decide⟩,⟨994209, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_74882_994210 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74882 ⟨994210, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 74882
    ⟨994210, by decide⟩ (by decide) (![⟨994043, by decide⟩,⟨994126, by decide⟩,⟨893903, by decide⟩,⟨994209, by decide⟩]) unmarked_context_11_74882_994210 node_context_11_74882_994210
  intro a
  fin_cases a
  · exact context_12_299528_994043
  · exact context_12_299529_994126
  · exact context_12_299530_893903
  · exact context_12_299531_994209

theorem selected_cut_37221 : selected 8 ⟨994264, by decide⟩
    (prefixPartial 13 1198128) = some ⟨13, 2, 0, 994264, 1198128, 2181, 16384⟩ := by
  decide +kernel

theorem context_13_1198128_994264 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1198128 ⟨994264, by decide⟩ :=
  accepted_of_selected 13 1198128 ⟨994264, by decide⟩ ⟨13, 2, 0, 994264, 1198128, 2181, 16384⟩
    (by decide) selected_cut_37221

theorem selected_cut_37222 : selected 8 ⟨994287, by decide⟩
    (prefixPartial 13 1198129) = some ⟨13, 2, 0, 994287, 1198129, 1449, 16384⟩ := by
  decide +kernel

theorem context_13_1198129_994287 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1198129 ⟨994287, by decide⟩ :=
  accepted_of_selected 13 1198129 ⟨994287, by decide⟩ ⟨13, 2, 0, 994287, 1198129, 1449, 16384⟩
    (by decide) selected_cut_37222

theorem selected_cut_37223 : selected 8 ⟨994311, by decide⟩
    (prefixPartial 13 1198130) = some ⟨13, 2, 0, 994311, 1198130, 1201, 16384⟩ := by
  decide +kernel

theorem context_13_1198130_994311 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1198130 ⟨994311, by decide⟩ :=
  accepted_of_selected 13 1198130 ⟨994311, by decide⟩ ⟨13, 2, 0, 994311, 1198130, 1201, 16384⟩
    (by decide) selected_cut_37223

theorem selected_cut_37224 : selected 8 ⟨994322, by decide⟩
    (prefixPartial 13 1198131) = some ⟨13, 2, 0, 994322, 1198131, 769, 16384⟩ := by
  decide +kernel

theorem context_13_1198131_994322 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1198131 ⟨994322, by decide⟩ :=
  accepted_of_selected 13 1198131 ⟨994322, by decide⟩ ⟨13, 2, 0, 994322, 1198131, 769, 16384⟩
    (by decide) selected_cut_37224

theorem unmarked_context_12_299532_994323 : frontier 9 ⟨994323, by decide⟩
    (prefixCache 12 299532) (prefixPartial 12 299532) = false := by
  decide +kernel

theorem node_context_12_299532_994323 : EJMOriginalGlobalDAGData.nodes 9 ⟨994323, by decide⟩ =
    .split (coordinate 12) (![⟨994264, by decide⟩,⟨994287, by decide⟩,⟨994311, by decide⟩,⟨994322, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_299532_994323 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299532 ⟨994323, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 299532
    ⟨994323, by decide⟩ (by decide) (![⟨994264, by decide⟩,⟨994287, by decide⟩,⟨994311, by decide⟩,⟨994322, by decide⟩]) unmarked_context_12_299532_994323 node_context_12_299532_994323
  intro a
  fin_cases a
  · exact context_13_1198128_994264
  · exact context_13_1198129_994287
  · exact context_13_1198130_994311
  · exact context_13_1198131_994322

theorem selected_cut_37225 : selected 8 ⟨994361, by decide⟩
    (prefixPartial 13 1198132) = some ⟨13, 2, 0, 994361, 1198132, 1917, 16384⟩ := by
  decide +kernel

theorem context_13_1198132_994361 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1198132 ⟨994361, by decide⟩ :=
  accepted_of_selected 13 1198132 ⟨994361, by decide⟩ ⟨13, 2, 0, 994361, 1198132, 1917, 16384⟩
    (by decide) selected_cut_37225

theorem selected_cut_37226 : selected 8 ⟨994383, by decide⟩
    (prefixPartial 13 1198133) = some ⟨13, 2, 0, 994383, 1198133, 1425, 16384⟩ := by
  decide +kernel

theorem context_13_1198133_994383 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1198133 ⟨994383, by decide⟩ :=
  accepted_of_selected 13 1198133 ⟨994383, by decide⟩ ⟨13, 2, 0, 994383, 1198133, 1425, 16384⟩
    (by decide) selected_cut_37226

theorem selected_cut_37227 : selected 8 ⟨994403, by decide⟩
    (prefixPartial 13 1198134) = some ⟨13, 2, 0, 994403, 1198134, 1093, 16384⟩ := by
  decide +kernel

theorem context_13_1198134_994403 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1198134 ⟨994403, by decide⟩ :=
  accepted_of_selected 13 1198134 ⟨994403, by decide⟩ ⟨13, 2, 0, 994403, 1198134, 1093, 16384⟩
    (by decide) selected_cut_37227

theorem selected_cut_37228 : selected 8 ⟨994412, by decide⟩
    (prefixPartial 13 1198135) = some ⟨13, 2, 0, 994412, 1198135, 617, 16384⟩ := by
  decide +kernel

theorem context_13_1198135_994412 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1198135 ⟨994412, by decide⟩ :=
  accepted_of_selected 13 1198135 ⟨994412, by decide⟩ ⟨13, 2, 0, 994412, 1198135, 617, 16384⟩
    (by decide) selected_cut_37228

theorem unmarked_context_12_299533_994413 : frontier 9 ⟨994413, by decide⟩
    (prefixCache 12 299533) (prefixPartial 12 299533) = false := by
  decide +kernel

theorem node_context_12_299533_994413 : EJMOriginalGlobalDAGData.nodes 9 ⟨994413, by decide⟩ =
    .split (coordinate 12) (![⟨994361, by decide⟩,⟨994383, by decide⟩,⟨994403, by decide⟩,⟨994412, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_299533_994413 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299533 ⟨994413, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 299533
    ⟨994413, by decide⟩ (by decide) (![⟨994361, by decide⟩,⟨994383, by decide⟩,⟨994403, by decide⟩,⟨994412, by decide⟩]) unmarked_context_12_299533_994413 node_context_12_299533_994413
  intro a
  fin_cases a
  · exact context_13_1198132_994361
  · exact context_13_1198133_994383
  · exact context_13_1198134_994403
  · exact context_13_1198135_994412

theorem selected_cut_37229 : selected 8 ⟨994447, by decide⟩
    (prefixPartial 13 1198136) = some ⟨13, 2, 0, 994447, 1198136, 1805, 16384⟩ := by
  decide +kernel

theorem context_13_1198136_994447 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1198136 ⟨994447, by decide⟩ :=
  accepted_of_selected 13 1198136 ⟨994447, by decide⟩ ⟨13, 2, 0, 994447, 1198136, 1805, 16384⟩
    (by decide) selected_cut_37229

theorem selected_cut_37230 : selected 8 ⟨994470, by decide⟩
    (prefixPartial 13 1198137) = some ⟨13, 2, 0, 994470, 1198137, 1289, 16384⟩ := by
  decide +kernel

theorem context_13_1198137_994470 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1198137 ⟨994470, by decide⟩ :=
  accepted_of_selected 13 1198137 ⟨994470, by decide⟩ ⟨13, 2, 0, 994470, 1198137, 1289, 16384⟩
    (by decide) selected_cut_37230

theorem selected_cut_37231 : selected 8 ⟨994489, by decide⟩
    (prefixPartial 13 1198138) = some ⟨13, 2, 0, 994489, 1198138, 1113, 16384⟩ := by
  decide +kernel

theorem context_13_1198138_994489 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1198138 ⟨994489, by decide⟩ :=
  accepted_of_selected 13 1198138 ⟨994489, by decide⟩ ⟨13, 2, 0, 994489, 1198138, 1113, 16384⟩
    (by decide) selected_cut_37231

theorem selected_cut_37232 : selected 8 ⟨994497, by decide⟩
    (prefixPartial 13 1198139) = some ⟨13, 2, 0, 994497, 1198139, 669, 16384⟩ := by
  decide +kernel

theorem context_13_1198139_994497 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1198139 ⟨994497, by decide⟩ :=
  accepted_of_selected 13 1198139 ⟨994497, by decide⟩ ⟨13, 2, 0, 994497, 1198139, 669, 16384⟩
    (by decide) selected_cut_37232

theorem unmarked_context_12_299534_994498 : frontier 9 ⟨994498, by decide⟩
    (prefixCache 12 299534) (prefixPartial 12 299534) = false := by
  decide +kernel

theorem node_context_12_299534_994498 : EJMOriginalGlobalDAGData.nodes 9 ⟨994498, by decide⟩ =
    .split (coordinate 12) (![⟨994447, by decide⟩,⟨994470, by decide⟩,⟨994489, by decide⟩,⟨994497, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_299534_994498 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299534 ⟨994498, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 299534
    ⟨994498, by decide⟩ (by decide) (![⟨994447, by decide⟩,⟨994470, by decide⟩,⟨994489, by decide⟩,⟨994497, by decide⟩]) unmarked_context_12_299534_994498 node_context_12_299534_994498
  intro a
  fin_cases a
  · exact context_13_1198136_994447
  · exact context_13_1198137_994470
  · exact context_13_1198138_994489
  · exact context_13_1198139_994497

theorem selected_cut_37233 : selected 8 ⟨994525, by decide⟩
    (prefixPartial 13 1198140) = some ⟨13, 2, 0, 994525, 1198140, 1805, 16384⟩ := by
  decide +kernel

theorem context_13_1198140_994525 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1198140 ⟨994525, by decide⟩ :=
  accepted_of_selected 13 1198140 ⟨994525, by decide⟩ ⟨13, 2, 0, 994525, 1198140, 1805, 16384⟩
    (by decide) selected_cut_37233

theorem selected_cut_37234 : selected 8 ⟨994542, by decide⟩
    (prefixPartial 13 1198141) = some ⟨13, 2, 0, 994542, 1198141, 1117, 16384⟩ := by
  decide +kernel

theorem context_13_1198141_994542 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1198141 ⟨994542, by decide⟩ :=
  accepted_of_selected 13 1198141 ⟨994542, by decide⟩ ⟨13, 2, 0, 994542, 1198141, 1117, 16384⟩
    (by decide) selected_cut_37234

theorem selected_cut_37235 : selected 8 ⟨994562, by decide⟩
    (prefixPartial 13 1198142) = some ⟨13, 2, 0, 994562, 1198142, 977, 16384⟩ := by
  decide +kernel

theorem context_13_1198142_994562 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1198142 ⟨994562, by decide⟩ :=
  accepted_of_selected 13 1198142 ⟨994562, by decide⟩ ⟨13, 2, 0, 994562, 1198142, 977, 16384⟩
    (by decide) selected_cut_37235

theorem selected_cut_37236 : selected 8 ⟨994568, by decide⟩
    (prefixPartial 13 1198143) = some ⟨13, 2, 0, 994568, 1198143, 577, 16384⟩ := by
  decide +kernel

theorem context_13_1198143_994568 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1198143 ⟨994568, by decide⟩ :=
  accepted_of_selected 13 1198143 ⟨994568, by decide⟩ ⟨13, 2, 0, 994568, 1198143, 577, 16384⟩
    (by decide) selected_cut_37236

theorem unmarked_context_12_299535_994569 : frontier 9 ⟨994569, by decide⟩
    (prefixCache 12 299535) (prefixPartial 12 299535) = false := by
  decide +kernel

theorem node_context_12_299535_994569 : EJMOriginalGlobalDAGData.nodes 9 ⟨994569, by decide⟩ =
    .split (coordinate 12) (![⟨994525, by decide⟩,⟨994542, by decide⟩,⟨994562, by decide⟩,⟨994568, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_299535_994569 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299535 ⟨994569, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 299535
    ⟨994569, by decide⟩ (by decide) (![⟨994525, by decide⟩,⟨994542, by decide⟩,⟨994562, by decide⟩,⟨994568, by decide⟩]) unmarked_context_12_299535_994569 node_context_12_299535_994569
  intro a
  fin_cases a
  · exact context_13_1198140_994525
  · exact context_13_1198141_994542
  · exact context_13_1198142_994562
  · exact context_13_1198143_994568

theorem unmarked_context_11_74883_994570 : frontier 10 ⟨994570, by decide⟩
    (prefixCache 11 74883) (prefixPartial 11 74883) = false := by
  decide +kernel

theorem node_context_11_74883_994570 : EJMOriginalGlobalDAGData.nodes 10 ⟨994570, by decide⟩ =
    .split (coordinate 11) (![⟨994323, by decide⟩,⟨994413, by decide⟩,⟨994498, by decide⟩,⟨994569, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_74883_994570 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74883 ⟨994570, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 74883
    ⟨994570, by decide⟩ (by decide) (![⟨994323, by decide⟩,⟨994413, by decide⟩,⟨994498, by decide⟩,⟨994569, by decide⟩]) unmarked_context_11_74883_994570 node_context_11_74883_994570
  intro a
  fin_cases a
  · exact context_12_299532_994323
  · exact context_12_299533_994413
  · exact context_12_299534_994498
  · exact context_12_299535_994569

theorem unmarked_context_10_18720_994571 : frontier 11 ⟨994571, by decide⟩
    (prefixCache 10 18720) (prefixPartial 10 18720) = false := by
  decide +kernel

theorem node_context_10_18720_994571 : EJMOriginalGlobalDAGData.nodes 11 ⟨994571, by decide⟩ =
    .split (coordinate 10) (![⟨167448, by decide⟩,⟨993953, by decide⟩,⟨994210, by decide⟩,⟨994570, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18720_994571 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18720 ⟨994571, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18720
    ⟨994571, by decide⟩ (by decide) (![⟨167448, by decide⟩,⟨993953, by decide⟩,⟨994210, by decide⟩,⟨994570, by decide⟩]) unmarked_context_10_18720_994571 node_context_10_18720_994571
  intro a
  fin_cases a
  · exact context_11_74880_167448
  · exact context_11_74881_993953
  · exact context_11_74882_994210
  · exact context_11_74883_994570

theorem selected_cut_37237 : selected 9 ⟨994572, by decide⟩
    (prefixPartial 12 299536) = some ⟨12, 1, 0, 994572, 299536, 1, 65536⟩ := by
  decide +kernel

theorem context_12_299536_994572 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299536 ⟨994572, by decide⟩ :=
  accepted_of_selected 12 299536 ⟨994572, by decide⟩ ⟨12, 1, 0, 994572, 299536, 1, 65536⟩
    (by decide) selected_cut_37237

theorem selected_cut_37238 : selected 9 ⟨994629, by decide⟩
    (prefixPartial 12 299537) = some ⟨12, 2, 0, 994629, 299537, 3485, 65536⟩ := by
  decide +kernel

theorem context_12_299537_994629 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299537 ⟨994629, by decide⟩ :=
  accepted_of_selected 12 299537 ⟨994629, by decide⟩ ⟨12, 2, 0, 994629, 299537, 3485, 65536⟩
    (by decide) selected_cut_37238

theorem selected_cut_37239 : selected 9 ⟨994679, by decide⟩
    (prefixPartial 12 299538) = some ⟨12, 2, 0, 994679, 299538, 3097, 65536⟩ := by
  decide +kernel

theorem context_12_299538_994679 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299538 ⟨994679, by decide⟩ :=
  accepted_of_selected 12 299538 ⟨994679, by decide⟩ ⟨12, 2, 0, 994679, 299538, 3097, 65536⟩
    (by decide) selected_cut_37239

theorem selected_cut_37240 : selected 9 ⟨994727, by decide⟩
    (prefixPartial 12 299539) = some ⟨12, 2, 0, 994727, 299539, 3565, 65536⟩ := by
  decide +kernel

theorem context_12_299539_994727 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299539 ⟨994727, by decide⟩ :=
  accepted_of_selected 12 299539 ⟨994727, by decide⟩ ⟨12, 2, 0, 994727, 299539, 3565, 65536⟩
    (by decide) selected_cut_37240

theorem unmarked_context_11_74884_994728 : frontier 10 ⟨994728, by decide⟩
    (prefixCache 11 74884) (prefixPartial 11 74884) = false := by
  decide +kernel

theorem node_context_11_74884_994728 : EJMOriginalGlobalDAGData.nodes 10 ⟨994728, by decide⟩ =
    .split (coordinate 11) (![⟨994572, by decide⟩,⟨994629, by decide⟩,⟨994679, by decide⟩,⟨994727, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_74884_994728 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74884 ⟨994728, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 74884
    ⟨994728, by decide⟩ (by decide) (![⟨994572, by decide⟩,⟨994629, by decide⟩,⟨994679, by decide⟩,⟨994727, by decide⟩]) unmarked_context_11_74884_994728 node_context_11_74884_994728
  intro a
  fin_cases a
  · exact context_12_299536_994572
  · exact context_12_299537_994629
  · exact context_12_299538_994679
  · exact context_12_299539_994727

theorem selected_cut_37241 : selected 8 ⟨994764, by decide⟩
    (prefixPartial 13 1198160) = some ⟨13, 2, 0, 994764, 1198160, 1949, 16384⟩ := by
  decide +kernel

theorem context_13_1198160_994764 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1198160 ⟨994764, by decide⟩ :=
  accepted_of_selected 13 1198160 ⟨994764, by decide⟩ ⟨13, 2, 0, 994764, 1198160, 1949, 16384⟩
    (by decide) selected_cut_37241

theorem selected_cut_37242 : selected 8 ⟨994782, by decide⟩
    (prefixPartial 13 1198161) = some ⟨13, 2, 0, 994782, 1198161, 1125, 16384⟩ := by
  decide +kernel

theorem context_13_1198161_994782 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1198161 ⟨994782, by decide⟩ :=
  accepted_of_selected 13 1198161 ⟨994782, by decide⟩ ⟨13, 2, 0, 994782, 1198161, 1125, 16384⟩
    (by decide) selected_cut_37242

theorem selected_cut_37243 : selected 8 ⟨994800, by decide⟩
    (prefixPartial 13 1198162) = some ⟨13, 2, 0, 994800, 1198162, 1101, 16384⟩ := by
  decide +kernel

theorem context_13_1198162_994800 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1198162 ⟨994800, by decide⟩ :=
  accepted_of_selected 13 1198162 ⟨994800, by decide⟩ ⟨13, 2, 0, 994800, 1198162, 1101, 16384⟩
    (by decide) selected_cut_37243

theorem selected_cut_37244 : selected 8 ⟨994807, by decide⟩
    (prefixPartial 13 1198163) = some ⟨13, 2, 0, 994807, 1198163, 561, 16384⟩ := by
  decide +kernel

theorem context_13_1198163_994807 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1198163 ⟨994807, by decide⟩ :=
  accepted_of_selected 13 1198163 ⟨994807, by decide⟩ ⟨13, 2, 0, 994807, 1198163, 561, 16384⟩
    (by decide) selected_cut_37244

theorem unmarked_context_12_299540_994808 : frontier 9 ⟨994808, by decide⟩
    (prefixCache 12 299540) (prefixPartial 12 299540) = false := by
  decide +kernel

theorem node_context_12_299540_994808 : EJMOriginalGlobalDAGData.nodes 9 ⟨994808, by decide⟩ =
    .split (coordinate 12) (![⟨994764, by decide⟩,⟨994782, by decide⟩,⟨994800, by decide⟩,⟨994807, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_299540_994808 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299540 ⟨994808, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 299540
    ⟨994808, by decide⟩ (by decide) (![⟨994764, by decide⟩,⟨994782, by decide⟩,⟨994800, by decide⟩,⟨994807, by decide⟩]) unmarked_context_12_299540_994808 node_context_12_299540_994808
  intro a
  fin_cases a
  · exact context_13_1198160_994764
  · exact context_13_1198161_994782
  · exact context_13_1198162_994800
  · exact context_13_1198163_994807

theorem selected_cut_37245 : selected 9 ⟨994956, by decide⟩
    (prefixPartial 12 299541) = some ⟨12, 2, 0, 994956, 299541, 2757, 65536⟩ := by
  decide +kernel

theorem context_12_299541_994956 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299541 ⟨994956, by decide⟩ :=
  accepted_of_selected 12 299541 ⟨994956, by decide⟩ ⟨12, 2, 0, 994956, 299541, 2757, 65536⟩
    (by decide) selected_cut_37245

theorem selected_cut_37246 : selected 9 ⟨995010, by decide⟩
    (prefixPartial 12 299542) = some ⟨12, 2, 0, 995010, 299542, 3845, 65536⟩ := by
  decide +kernel

theorem context_12_299542_995010 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299542 ⟨995010, by decide⟩ :=
  accepted_of_selected 12 299542 ⟨995010, by decide⟩ ⟨12, 2, 0, 995010, 299542, 3845, 65536⟩
    (by decide) selected_cut_37246

theorem selected_cut_37247 : selected 8 ⟨995036, by decide⟩
    (prefixPartial 13 1198172) = some ⟨13, 2, 0, 995036, 1198172, 1597, 16384⟩ := by
  decide +kernel

theorem context_13_1198172_995036 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1198172 ⟨995036, by decide⟩ :=
  accepted_of_selected 13 1198172 ⟨995036, by decide⟩ ⟨13, 2, 0, 995036, 1198172, 1597, 16384⟩
    (by decide) selected_cut_37247

theorem selected_cut_37248 : selected 8 ⟨995050, by decide⟩
    (prefixPartial 13 1198173) = some ⟨13, 2, 0, 995050, 1198173, 1049, 16384⟩ := by
  decide +kernel

theorem context_13_1198173_995050 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1198173 ⟨995050, by decide⟩ :=
  accepted_of_selected 13 1198173 ⟨995050, by decide⟩ ⟨13, 2, 0, 995050, 1198173, 1049, 16384⟩
    (by decide) selected_cut_37248

theorem selected_cut_37249 : selected 8 ⟨995069, by decide⟩
    (prefixPartial 13 1198174) = some ⟨13, 2, 0, 995069, 1198174, 1085, 16384⟩ := by
  decide +kernel

theorem context_13_1198174_995069 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1198174 ⟨995069, by decide⟩ :=
  accepted_of_selected 13 1198174 ⟨995069, by decide⟩ ⟨13, 2, 0, 995069, 1198174, 1085, 16384⟩
    (by decide) selected_cut_37249

theorem selected_cut_37250 : selected 8 ⟨995074, by decide⟩
    (prefixPartial 13 1198175) = some ⟨13, 2, 0, 995074, 1198175, 525, 16384⟩ := by
  decide +kernel

theorem context_13_1198175_995074 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1198175 ⟨995074, by decide⟩ :=
  accepted_of_selected 13 1198175 ⟨995074, by decide⟩ ⟨13, 2, 0, 995074, 1198175, 525, 16384⟩
    (by decide) selected_cut_37250

theorem unmarked_context_12_299543_995075 : frontier 9 ⟨995075, by decide⟩
    (prefixCache 12 299543) (prefixPartial 12 299543) = false := by
  decide +kernel

theorem node_context_12_299543_995075 : EJMOriginalGlobalDAGData.nodes 9 ⟨995075, by decide⟩ =
    .split (coordinate 12) (![⟨995036, by decide⟩,⟨995050, by decide⟩,⟨995069, by decide⟩,⟨995074, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_299543_995075 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299543 ⟨995075, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 299543
    ⟨995075, by decide⟩ (by decide) (![⟨995036, by decide⟩,⟨995050, by decide⟩,⟨995069, by decide⟩,⟨995074, by decide⟩]) unmarked_context_12_299543_995075 node_context_12_299543_995075
  intro a
  fin_cases a
  · exact context_13_1198172_995036
  · exact context_13_1198173_995050
  · exact context_13_1198174_995069
  · exact context_13_1198175_995074

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
