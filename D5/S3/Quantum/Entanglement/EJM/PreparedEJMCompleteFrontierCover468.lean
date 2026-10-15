/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover467
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_44931 : selected 10 ⟨1239890, by decide⟩
    (prefixPartial 11 88851) = some ⟨11, 2, 0, 1239890, 88851, 3033, 262144⟩ := by
  decide +kernel

theorem context_11_88851_1239890 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88851 ⟨1239890, by decide⟩ :=
  accepted_of_selected 11 88851 ⟨1239890, by decide⟩ ⟨11, 2, 0, 1239890, 88851, 3033, 262144⟩
    (by decide) selected_cut_44931

theorem unmarked_context_10_22212_1239891 : frontier 11 ⟨1239891, by decide⟩
    (prefixCache 10 22212) (prefixPartial 10 22212) = false := by
  decide +kernel

theorem node_context_10_22212_1239891 : EJMOriginalGlobalDAGData.nodes 11 ⟨1239891, by decide⟩ =
    .split (coordinate 10) (![⟨1239619, by decide⟩,⟨1239713, by decide⟩,⟨1239831, by decide⟩,⟨1239890, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22212_1239891 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22212 ⟨1239891, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22212
    ⟨1239891, by decide⟩ (by decide) (![⟨1239619, by decide⟩,⟨1239713, by decide⟩,⟨1239831, by decide⟩,⟨1239890, by decide⟩]) unmarked_context_10_22212_1239891 node_context_10_22212_1239891
  intro a
  fin_cases a
  · exact context_11_88848_1239619
  · exact context_11_88849_1239713
  · exact context_11_88850_1239831
  · exact context_11_88851_1239890

theorem selected_cut_44932 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 22213) = some ⟨10, 1, 0, 893098, 22213, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_22213_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22213 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 22213 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 22213, 1, 1048576⟩
    (by decide) selected_cut_44932

theorem selected_cut_44933 : selected 10 ⟨1239956, by decide⟩
    (prefixPartial 11 88856) = some ⟨11, 2, 0, 1239956, 88856, 3005, 262144⟩ := by
  decide +kernel

theorem context_11_88856_1239956 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88856 ⟨1239956, by decide⟩ :=
  accepted_of_selected 11 88856 ⟨1239956, by decide⟩ ⟨11, 2, 0, 1239956, 88856, 3005, 262144⟩
    (by decide) selected_cut_44933

theorem selected_cut_44934 : selected 9 ⟨1239982, by decide⟩
    (prefixPartial 12 355428) = some ⟨12, 2, 0, 1239982, 355428, 1369, 65536⟩ := by
  decide +kernel

theorem context_12_355428_1239982 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355428 ⟨1239982, by decide⟩ :=
  accepted_of_selected 12 355428 ⟨1239982, by decide⟩ ⟨12, 2, 0, 1239982, 355428, 1369, 65536⟩
    (by decide) selected_cut_44934

theorem selected_cut_44935 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 355429) = some ⟨12, 1, 0, 896706, 355429, 1, 65536⟩ := by
  decide +kernel

theorem context_12_355429_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355429 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 355429 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 355429, 1, 65536⟩
    (by decide) selected_cut_44935

theorem selected_cut_44936 : selected 9 ⟨1240012, by decide⟩
    (prefixPartial 12 355430) = some ⟨12, 2, 0, 1240012, 355430, 1357, 65536⟩ := by
  decide +kernel

theorem context_12_355430_1240012 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355430 ⟨1240012, by decide⟩ :=
  accepted_of_selected 12 355430 ⟨1240012, by decide⟩ ⟨12, 2, 0, 1240012, 355430, 1357, 65536⟩
    (by decide) selected_cut_44936

theorem selected_cut_44937 : selected 9 ⟨1240044, by decide⟩
    (prefixPartial 12 355431) = some ⟨12, 2, 0, 1240044, 355431, 1421, 65536⟩ := by
  decide +kernel

theorem context_12_355431_1240044 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355431 ⟨1240044, by decide⟩ :=
  accepted_of_selected 12 355431 ⟨1240044, by decide⟩ ⟨12, 2, 0, 1240044, 355431, 1421, 65536⟩
    (by decide) selected_cut_44937

theorem unmarked_context_11_88857_1240045 : frontier 10 ⟨1240045, by decide⟩
    (prefixCache 11 88857) (prefixPartial 11 88857) = false := by
  decide +kernel

theorem node_context_11_88857_1240045 : EJMOriginalGlobalDAGData.nodes 10 ⟨1240045, by decide⟩ =
    .split (coordinate 11) (![⟨1239982, by decide⟩,⟨896706, by decide⟩,⟨1240012, by decide⟩,⟨1240044, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88857_1240045 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88857 ⟨1240045, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88857
    ⟨1240045, by decide⟩ (by decide) (![⟨1239982, by decide⟩,⟨896706, by decide⟩,⟨1240012, by decide⟩,⟨1240044, by decide⟩]) unmarked_context_11_88857_1240045 node_context_11_88857_1240045
  intro a
  fin_cases a
  · exact context_12_355428_1239982
  · exact context_12_355429_896706
  · exact context_12_355430_1240012
  · exact context_12_355431_1240044

theorem selected_cut_44938 : selected 10 ⟨1240106, by decide⟩
    (prefixPartial 11 88858) = some ⟨11, 2, 0, 1240106, 88858, 2913, 262144⟩ := by
  decide +kernel

theorem context_11_88858_1240106 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88858 ⟨1240106, by decide⟩ :=
  accepted_of_selected 11 88858 ⟨1240106, by decide⟩ ⟨11, 2, 0, 1240106, 88858, 2913, 262144⟩
    (by decide) selected_cut_44938

theorem selected_cut_44939 : selected 9 ⟨1240130, by decide⟩
    (prefixPartial 12 355436) = some ⟨12, 2, 0, 1240130, 355436, 1297, 65536⟩ := by
  decide +kernel

theorem context_12_355436_1240130 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355436 ⟨1240130, by decide⟩ :=
  accepted_of_selected 12 355436 ⟨1240130, by decide⟩ ⟨12, 2, 0, 1240130, 355436, 1297, 65536⟩
    (by decide) selected_cut_44939

theorem selected_cut_44940 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 355437) = some ⟨12, 1, 0, 896706, 355437, 1, 65536⟩ := by
  decide +kernel

theorem context_12_355437_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355437 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 355437 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 355437, 1, 65536⟩
    (by decide) selected_cut_44940

theorem selected_cut_44941 : selected 9 ⟨1240158, by decide⟩
    (prefixPartial 12 355438) = some ⟨12, 2, 0, 1240158, 355438, 1369, 65536⟩ := by
  decide +kernel

theorem context_12_355438_1240158 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355438 ⟨1240158, by decide⟩ :=
  accepted_of_selected 12 355438 ⟨1240158, by decide⟩ ⟨12, 2, 0, 1240158, 355438, 1369, 65536⟩
    (by decide) selected_cut_44941

theorem selected_cut_44942 : selected 9 ⟨1240180, by decide⟩
    (prefixPartial 12 355439) = some ⟨12, 2, 0, 1240180, 355439, 1437, 65536⟩ := by
  decide +kernel

theorem context_12_355439_1240180 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355439 ⟨1240180, by decide⟩ :=
  accepted_of_selected 12 355439 ⟨1240180, by decide⟩ ⟨12, 2, 0, 1240180, 355439, 1437, 65536⟩
    (by decide) selected_cut_44942

theorem unmarked_context_11_88859_1240181 : frontier 10 ⟨1240181, by decide⟩
    (prefixCache 11 88859) (prefixPartial 11 88859) = false := by
  decide +kernel

theorem node_context_11_88859_1240181 : EJMOriginalGlobalDAGData.nodes 10 ⟨1240181, by decide⟩ =
    .split (coordinate 11) (![⟨1240130, by decide⟩,⟨896706, by decide⟩,⟨1240158, by decide⟩,⟨1240180, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88859_1240181 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88859 ⟨1240181, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88859
    ⟨1240181, by decide⟩ (by decide) (![⟨1240130, by decide⟩,⟨896706, by decide⟩,⟨1240158, by decide⟩,⟨1240180, by decide⟩]) unmarked_context_11_88859_1240181 node_context_11_88859_1240181
  intro a
  fin_cases a
  · exact context_12_355436_1240130
  · exact context_12_355437_896706
  · exact context_12_355438_1240158
  · exact context_12_355439_1240180

theorem unmarked_context_10_22214_1240182 : frontier 11 ⟨1240182, by decide⟩
    (prefixCache 10 22214) (prefixPartial 10 22214) = false := by
  decide +kernel

theorem node_context_10_22214_1240182 : EJMOriginalGlobalDAGData.nodes 11 ⟨1240182, by decide⟩ =
    .split (coordinate 10) (![⟨1239956, by decide⟩,⟨1240045, by decide⟩,⟨1240106, by decide⟩,⟨1240181, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22214_1240182 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22214 ⟨1240182, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22214
    ⟨1240182, by decide⟩ (by decide) (![⟨1239956, by decide⟩,⟨1240045, by decide⟩,⟨1240106, by decide⟩,⟨1240181, by decide⟩]) unmarked_context_10_22214_1240182 node_context_10_22214_1240182
  intro a
  fin_cases a
  · exact context_11_88856_1239956
  · exact context_11_88857_1240045
  · exact context_11_88858_1240106
  · exact context_11_88859_1240181

theorem selected_cut_44943 : selected 10 ⟨1240245, by decide⟩
    (prefixPartial 11 88860) = some ⟨11, 2, 0, 1240245, 88860, 2853, 262144⟩ := by
  decide +kernel

theorem context_11_88860_1240245 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88860 ⟨1240245, by decide⟩ :=
  accepted_of_selected 11 88860 ⟨1240245, by decide⟩ ⟨11, 2, 0, 1240245, 88860, 2853, 262144⟩
    (by decide) selected_cut_44943

theorem selected_cut_44944 : selected 10 ⟨1240313, by decide⟩
    (prefixPartial 11 88861) = some ⟨11, 2, 0, 1240313, 88861, 3661, 262144⟩ := by
  decide +kernel

theorem context_11_88861_1240313 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88861 ⟨1240313, by decide⟩ :=
  accepted_of_selected 11 88861 ⟨1240313, by decide⟩ ⟨11, 2, 0, 1240313, 88861, 3661, 262144⟩
    (by decide) selected_cut_44944

theorem selected_cut_44945 : selected 10 ⟨1240386, by decide⟩
    (prefixPartial 11 88862) = some ⟨11, 2, 0, 1240386, 88862, 3669, 262144⟩ := by
  decide +kernel

theorem context_11_88862_1240386 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88862 ⟨1240386, by decide⟩ :=
  accepted_of_selected 11 88862 ⟨1240386, by decide⟩ ⟨11, 2, 0, 1240386, 88862, 3669, 262144⟩
    (by decide) selected_cut_44945

theorem selected_cut_44946 : selected 10 ⟨977886, by decide⟩
    (prefixPartial 11 88863) = some ⟨11, 1, 0, 977886, 88863, 1, 262144⟩ := by
  decide +kernel

theorem context_11_88863_977886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88863 ⟨977886, by decide⟩ :=
  accepted_of_selected 11 88863 ⟨977886, by decide⟩ ⟨11, 1, 0, 977886, 88863, 1, 262144⟩
    (by decide) selected_cut_44946

theorem unmarked_context_10_22215_1240387 : frontier 11 ⟨1240387, by decide⟩
    (prefixCache 10 22215) (prefixPartial 10 22215) = false := by
  decide +kernel

theorem node_context_10_22215_1240387 : EJMOriginalGlobalDAGData.nodes 11 ⟨1240387, by decide⟩ =
    .split (coordinate 10) (![⟨1240245, by decide⟩,⟨1240313, by decide⟩,⟨1240386, by decide⟩,⟨977886, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22215_1240387 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22215 ⟨1240387, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22215
    ⟨1240387, by decide⟩ (by decide) (![⟨1240245, by decide⟩,⟨1240313, by decide⟩,⟨1240386, by decide⟩,⟨977886, by decide⟩]) unmarked_context_10_22215_1240387 node_context_10_22215_1240387
  intro a
  fin_cases a
  · exact context_11_88860_1240245
  · exact context_11_88861_1240313
  · exact context_11_88862_1240386
  · exact context_11_88863_977886

theorem unmarked_context_9_5553_1240388 : frontier 12 ⟨1240388, by decide⟩
    (prefixCache 9 5553) (prefixPartial 9 5553) = false := by
  decide +kernel

theorem node_context_9_5553_1240388 : EJMOriginalGlobalDAGData.nodes 12 ⟨1240388, by decide⟩ =
    .split (coordinate 9) (![⟨1239891, by decide⟩,⟨893098, by decide⟩,⟨1240182, by decide⟩,⟨1240387, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5553_1240388 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5553 ⟨1240388, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5553
    ⟨1240388, by decide⟩ (by decide) (![⟨1239891, by decide⟩,⟨893098, by decide⟩,⟨1240182, by decide⟩,⟨1240387, by decide⟩]) unmarked_context_9_5553_1240388 node_context_9_5553_1240388
  intro a
  fin_cases a
  · exact context_10_22212_1239891
  · exact context_10_22213_893098
  · exact context_10_22214_1240182
  · exact context_10_22215_1240387

theorem selected_cut_44947 : selected 10 ⟨1240449, by decide⟩
    (prefixPartial 11 88864) = some ⟨11, 2, 0, 1240449, 88864, 2617, 262144⟩ := by
  decide +kernel

theorem context_11_88864_1240449 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88864 ⟨1240449, by decide⟩ :=
  accepted_of_selected 11 88864 ⟨1240449, by decide⟩ ⟨11, 2, 0, 1240449, 88864, 2617, 262144⟩
    (by decide) selected_cut_44947

theorem selected_cut_44948 : selected 9 ⟨1240474, by decide⟩
    (prefixPartial 12 355460) = some ⟨12, 2, 0, 1240474, 355460, 1333, 65536⟩ := by
  decide +kernel

theorem context_12_355460_1240474 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355460 ⟨1240474, by decide⟩ :=
  accepted_of_selected 12 355460 ⟨1240474, by decide⟩ ⟨12, 2, 0, 1240474, 355460, 1333, 65536⟩
    (by decide) selected_cut_44948

theorem selected_cut_44949 : selected 9 ⟨1240493, by decide⟩
    (prefixPartial 12 355461) = some ⟨12, 2, 0, 1240493, 355461, 1157, 65536⟩ := by
  decide +kernel

theorem context_12_355461_1240493 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355461 ⟨1240493, by decide⟩ :=
  accepted_of_selected 12 355461 ⟨1240493, by decide⟩ ⟨12, 2, 0, 1240493, 355461, 1157, 65536⟩
    (by decide) selected_cut_44949

theorem selected_cut_44950 : selected 9 ⟨1240514, by decide⟩
    (prefixPartial 12 355462) = some ⟨12, 2, 0, 1240514, 355462, 1333, 65536⟩ := by
  decide +kernel

theorem context_12_355462_1240514 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355462 ⟨1240514, by decide⟩ :=
  accepted_of_selected 12 355462 ⟨1240514, by decide⟩ ⟨12, 2, 0, 1240514, 355462, 1333, 65536⟩
    (by decide) selected_cut_44950

theorem selected_cut_44951 : selected 9 ⟨1240540, by decide⟩
    (prefixPartial 12 355463) = some ⟨12, 2, 0, 1240540, 355463, 1437, 65536⟩ := by
  decide +kernel

theorem context_12_355463_1240540 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355463 ⟨1240540, by decide⟩ :=
  accepted_of_selected 12 355463 ⟨1240540, by decide⟩ ⟨12, 2, 0, 1240540, 355463, 1437, 65536⟩
    (by decide) selected_cut_44951

theorem unmarked_context_11_88865_1240541 : frontier 10 ⟨1240541, by decide⟩
    (prefixCache 11 88865) (prefixPartial 11 88865) = false := by
  decide +kernel

theorem node_context_11_88865_1240541 : EJMOriginalGlobalDAGData.nodes 10 ⟨1240541, by decide⟩ =
    .split (coordinate 11) (![⟨1240474, by decide⟩,⟨1240493, by decide⟩,⟨1240514, by decide⟩,⟨1240540, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88865_1240541 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88865 ⟨1240541, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88865
    ⟨1240541, by decide⟩ (by decide) (![⟨1240474, by decide⟩,⟨1240493, by decide⟩,⟨1240514, by decide⟩,⟨1240540, by decide⟩]) unmarked_context_11_88865_1240541 node_context_11_88865_1240541
  intro a
  fin_cases a
  · exact context_12_355460_1240474
  · exact context_12_355461_1240493
  · exact context_12_355462_1240514
  · exact context_12_355463_1240540

theorem selected_cut_44952 : selected 9 ⟨1240569, by decide⟩
    (prefixPartial 12 355464) = some ⟨12, 2, 0, 1240569, 355464, 1313, 65536⟩ := by
  decide +kernel

theorem context_12_355464_1240569 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355464 ⟨1240569, by decide⟩ :=
  accepted_of_selected 12 355464 ⟨1240569, by decide⟩ ⟨12, 2, 0, 1240569, 355464, 1313, 65536⟩
    (by decide) selected_cut_44952

theorem selected_cut_44953 : selected 9 ⟨1240594, by decide⟩
    (prefixPartial 12 355465) = some ⟨12, 2, 0, 1240594, 355465, 1301, 65536⟩ := by
  decide +kernel

theorem context_12_355465_1240594 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355465 ⟨1240594, by decide⟩ :=
  accepted_of_selected 12 355465 ⟨1240594, by decide⟩ ⟨12, 2, 0, 1240594, 355465, 1301, 65536⟩
    (by decide) selected_cut_44953

theorem selected_cut_44954 : selected 9 ⟨1196232, by decide⟩
    (prefixPartial 12 355466) = some ⟨12, 1, 0, 1196232, 355466, 1, 65536⟩ := by
  decide +kernel

theorem context_12_355466_1196232 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355466 ⟨1196232, by decide⟩ :=
  accepted_of_selected 12 355466 ⟨1196232, by decide⟩ ⟨12, 1, 0, 1196232, 355466, 1, 65536⟩
    (by decide) selected_cut_44954

theorem selected_cut_44955 : selected 9 ⟨1240632, by decide⟩
    (prefixPartial 12 355467) = some ⟨12, 2, 0, 1240632, 355467, 1581, 65536⟩ := by
  decide +kernel

theorem context_12_355467_1240632 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355467 ⟨1240632, by decide⟩ :=
  accepted_of_selected 12 355467 ⟨1240632, by decide⟩ ⟨12, 2, 0, 1240632, 355467, 1581, 65536⟩
    (by decide) selected_cut_44955

theorem unmarked_context_11_88866_1240633 : frontier 10 ⟨1240633, by decide⟩
    (prefixCache 11 88866) (prefixPartial 11 88866) = false := by
  decide +kernel

theorem node_context_11_88866_1240633 : EJMOriginalGlobalDAGData.nodes 10 ⟨1240633, by decide⟩ =
    .split (coordinate 11) (![⟨1240569, by decide⟩,⟨1240594, by decide⟩,⟨1196232, by decide⟩,⟨1240632, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88866_1240633 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88866 ⟨1240633, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88866
    ⟨1240633, by decide⟩ (by decide) (![⟨1240569, by decide⟩,⟨1240594, by decide⟩,⟨1196232, by decide⟩,⟨1240632, by decide⟩]) unmarked_context_11_88866_1240633 node_context_11_88866_1240633
  intro a
  fin_cases a
  · exact context_12_355464_1240569
  · exact context_12_355465_1240594
  · exact context_12_355466_1196232
  · exact context_12_355467_1240632

theorem selected_cut_44956 : selected 10 ⟨1240707, by decide⟩
    (prefixPartial 11 88867) = some ⟨11, 2, 0, 1240707, 88867, 3441, 262144⟩ := by
  decide +kernel

theorem context_11_88867_1240707 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88867 ⟨1240707, by decide⟩ :=
  accepted_of_selected 11 88867 ⟨1240707, by decide⟩ ⟨11, 2, 0, 1240707, 88867, 3441, 262144⟩
    (by decide) selected_cut_44956

theorem unmarked_context_10_22216_1240708 : frontier 11 ⟨1240708, by decide⟩
    (prefixCache 10 22216) (prefixPartial 10 22216) = false := by
  decide +kernel

theorem node_context_10_22216_1240708 : EJMOriginalGlobalDAGData.nodes 11 ⟨1240708, by decide⟩ =
    .split (coordinate 10) (![⟨1240449, by decide⟩,⟨1240541, by decide⟩,⟨1240633, by decide⟩,⟨1240707, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22216_1240708 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22216 ⟨1240708, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22216
    ⟨1240708, by decide⟩ (by decide) (![⟨1240449, by decide⟩,⟨1240541, by decide⟩,⟨1240633, by decide⟩,⟨1240707, by decide⟩]) unmarked_context_10_22216_1240708 node_context_10_22216_1240708
  intro a
  fin_cases a
  · exact context_11_88864_1240449
  · exact context_11_88865_1240541
  · exact context_11_88866_1240633
  · exact context_11_88867_1240707

theorem selected_cut_44957 : selected 10 ⟨1240751, by decide⟩
    (prefixPartial 11 88868) = some ⟨11, 2, 0, 1240751, 88868, 2317, 262144⟩ := by
  decide +kernel

theorem context_11_88868_1240751 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88868 ⟨1240751, by decide⟩ :=
  accepted_of_selected 11 88868 ⟨1240751, by decide⟩ ⟨11, 2, 0, 1240751, 88868, 2317, 262144⟩
    (by decide) selected_cut_44957

theorem selected_cut_44958 : selected 10 ⟨1240787, by decide⟩
    (prefixPartial 11 88869) = some ⟨11, 2, 0, 1240787, 88869, 2129, 262144⟩ := by
  decide +kernel

theorem context_11_88869_1240787 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88869 ⟨1240787, by decide⟩ :=
  accepted_of_selected 11 88869 ⟨1240787, by decide⟩ ⟨11, 2, 0, 1240787, 88869, 2129, 262144⟩
    (by decide) selected_cut_44958

theorem selected_cut_44959 : selected 10 ⟨1240847, by decide⟩
    (prefixPartial 11 88870) = some ⟨11, 2, 0, 1240847, 88870, 3217, 262144⟩ := by
  decide +kernel

theorem context_11_88870_1240847 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88870 ⟨1240847, by decide⟩ :=
  accepted_of_selected 11 88870 ⟨1240847, by decide⟩ ⟨11, 2, 0, 1240847, 88870, 3217, 262144⟩
    (by decide) selected_cut_44959

theorem selected_cut_44960 : selected 10 ⟨1240915, by decide⟩
    (prefixPartial 11 88871) = some ⟨11, 2, 0, 1240915, 88871, 3729, 262144⟩ := by
  decide +kernel

theorem context_11_88871_1240915 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88871 ⟨1240915, by decide⟩ :=
  accepted_of_selected 11 88871 ⟨1240915, by decide⟩ ⟨11, 2, 0, 1240915, 88871, 3729, 262144⟩
    (by decide) selected_cut_44960

theorem unmarked_context_10_22217_1240916 : frontier 11 ⟨1240916, by decide⟩
    (prefixCache 10 22217) (prefixPartial 10 22217) = false := by
  decide +kernel

theorem node_context_10_22217_1240916 : EJMOriginalGlobalDAGData.nodes 11 ⟨1240916, by decide⟩ =
    .split (coordinate 10) (![⟨1240751, by decide⟩,⟨1240787, by decide⟩,⟨1240847, by decide⟩,⟨1240915, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22217_1240916 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22217 ⟨1240916, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22217
    ⟨1240916, by decide⟩ (by decide) (![⟨1240751, by decide⟩,⟨1240787, by decide⟩,⟨1240847, by decide⟩,⟨1240915, by decide⟩]) unmarked_context_10_22217_1240916 node_context_10_22217_1240916
  intro a
  fin_cases a
  · exact context_11_88868_1240751
  · exact context_11_88869_1240787
  · exact context_11_88870_1240847
  · exact context_11_88871_1240915

theorem selected_cut_44961 : selected 10 ⟨1240954, by decide⟩
    (prefixPartial 11 88872) = some ⟨11, 2, 0, 1240954, 88872, 1753, 262144⟩ := by
  decide +kernel

theorem context_11_88872_1240954 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88872 ⟨1240954, by decide⟩ :=
  accepted_of_selected 11 88872 ⟨1240954, by decide⟩ ⟨11, 2, 0, 1240954, 88872, 1753, 262144⟩
    (by decide) selected_cut_44961

theorem selected_cut_44962 : selected 10 ⟨1240989, by decide⟩
    (prefixPartial 11 88873) = some ⟨11, 2, 0, 1240989, 88873, 1653, 262144⟩ := by
  decide +kernel

theorem context_11_88873_1240989 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88873 ⟨1240989, by decide⟩ :=
  accepted_of_selected 11 88873 ⟨1240989, by decide⟩ ⟨11, 2, 0, 1240989, 88873, 1653, 262144⟩
    (by decide) selected_cut_44962

theorem selected_cut_44963 : selected 10 ⟨1109453, by decide⟩
    (prefixPartial 11 88874) = some ⟨11, 1, 0, 1109453, 88874, 1, 262144⟩ := by
  decide +kernel

theorem context_11_88874_1109453 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88874 ⟨1109453, by decide⟩ :=
  accepted_of_selected 11 88874 ⟨1109453, by decide⟩ ⟨11, 1, 0, 1109453, 88874, 1, 262144⟩
    (by decide) selected_cut_44963

theorem selected_cut_44964 : selected 10 ⟨1241023, by decide⟩
    (prefixPartial 11 88875) = some ⟨11, 2, 0, 1241023, 88875, 1717, 262144⟩ := by
  decide +kernel

theorem context_11_88875_1241023 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88875 ⟨1241023, by decide⟩ :=
  accepted_of_selected 11 88875 ⟨1241023, by decide⟩ ⟨11, 2, 0, 1241023, 88875, 1717, 262144⟩
    (by decide) selected_cut_44964

theorem unmarked_context_10_22218_1241024 : frontier 11 ⟨1241024, by decide⟩
    (prefixCache 10 22218) (prefixPartial 10 22218) = false := by
  decide +kernel

theorem node_context_10_22218_1241024 : EJMOriginalGlobalDAGData.nodes 11 ⟨1241024, by decide⟩ =
    .split (coordinate 10) (![⟨1240954, by decide⟩,⟨1240989, by decide⟩,⟨1109453, by decide⟩,⟨1241023, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22218_1241024 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22218 ⟨1241024, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22218
    ⟨1241024, by decide⟩ (by decide) (![⟨1240954, by decide⟩,⟨1240989, by decide⟩,⟨1109453, by decide⟩,⟨1241023, by decide⟩]) unmarked_context_10_22218_1241024 node_context_10_22218_1241024
  intro a
  fin_cases a
  · exact context_11_88872_1240954
  · exact context_11_88873_1240989
  · exact context_11_88874_1109453
  · exact context_11_88875_1241023

theorem selected_cut_44965 : selected 10 ⟨1241061, by decide⟩
    (prefixPartial 11 88876) = some ⟨11, 2, 0, 1241061, 88876, 2137, 262144⟩ := by
  decide +kernel

theorem context_11_88876_1241061 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88876 ⟨1241061, by decide⟩ :=
  accepted_of_selected 11 88876 ⟨1241061, by decide⟩ ⟨11, 2, 0, 1241061, 88876, 2137, 262144⟩
    (by decide) selected_cut_44965

theorem selected_cut_44966 : selected 10 ⟨1241103, by decide⟩
    (prefixPartial 11 88877) = some ⟨11, 2, 0, 1241103, 88877, 2293, 262144⟩ := by
  decide +kernel

theorem context_11_88877_1241103 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88877 ⟨1241103, by decide⟩ :=
  accepted_of_selected 11 88877 ⟨1241103, by decide⟩ ⟨11, 2, 0, 1241103, 88877, 2293, 262144⟩
    (by decide) selected_cut_44966

theorem selected_cut_44967 : selected 10 ⟨1241147, by decide⟩
    (prefixPartial 11 88878) = some ⟨11, 2, 0, 1241147, 88878, 1793, 262144⟩ := by
  decide +kernel

theorem context_11_88878_1241147 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88878 ⟨1241147, by decide⟩ :=
  accepted_of_selected 11 88878 ⟨1241147, by decide⟩ ⟨11, 2, 0, 1241147, 88878, 1793, 262144⟩
    (by decide) selected_cut_44967

theorem selected_cut_44968 : selected 10 ⟨977886, by decide⟩
    (prefixPartial 11 88879) = some ⟨11, 1, 0, 977886, 88879, 1, 262144⟩ := by
  decide +kernel

theorem context_11_88879_977886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88879 ⟨977886, by decide⟩ :=
  accepted_of_selected 11 88879 ⟨977886, by decide⟩ ⟨11, 1, 0, 977886, 88879, 1, 262144⟩
    (by decide) selected_cut_44968

theorem unmarked_context_10_22219_1241148 : frontier 11 ⟨1241148, by decide⟩
    (prefixCache 10 22219) (prefixPartial 10 22219) = false := by
  decide +kernel

theorem node_context_10_22219_1241148 : EJMOriginalGlobalDAGData.nodes 11 ⟨1241148, by decide⟩ =
    .split (coordinate 10) (![⟨1241061, by decide⟩,⟨1241103, by decide⟩,⟨1241147, by decide⟩,⟨977886, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22219_1241148 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22219 ⟨1241148, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22219
    ⟨1241148, by decide⟩ (by decide) (![⟨1241061, by decide⟩,⟨1241103, by decide⟩,⟨1241147, by decide⟩,⟨977886, by decide⟩]) unmarked_context_10_22219_1241148 node_context_10_22219_1241148
  intro a
  fin_cases a
  · exact context_11_88876_1241061
  · exact context_11_88877_1241103
  · exact context_11_88878_1241147
  · exact context_11_88879_977886

theorem unmarked_context_9_5554_1241149 : frontier 12 ⟨1241149, by decide⟩
    (prefixCache 9 5554) (prefixPartial 9 5554) = false := by
  decide +kernel

theorem node_context_9_5554_1241149 : EJMOriginalGlobalDAGData.nodes 12 ⟨1241149, by decide⟩ =
    .split (coordinate 9) (![⟨1240708, by decide⟩,⟨1240916, by decide⟩,⟨1241024, by decide⟩,⟨1241148, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5554_1241149 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5554 ⟨1241149, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5554
    ⟨1241149, by decide⟩ (by decide) (![⟨1240708, by decide⟩,⟨1240916, by decide⟩,⟨1241024, by decide⟩,⟨1241148, by decide⟩]) unmarked_context_9_5554_1241149 node_context_9_5554_1241149
  intro a
  fin_cases a
  · exact context_10_22216_1240708
  · exact context_10_22217_1240916
  · exact context_10_22218_1241024
  · exact context_10_22219_1241148

theorem selected_cut_44969 : selected 10 ⟨1241170, by decide⟩
    (prefixPartial 11 88880) = some ⟨11, 2, 0, 1241170, 88880, 833, 262144⟩ := by
  decide +kernel

theorem context_11_88880_1241170 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88880 ⟨1241170, by decide⟩ :=
  accepted_of_selected 11 88880 ⟨1241170, by decide⟩ ⟨11, 2, 0, 1241170, 88880, 833, 262144⟩
    (by decide) selected_cut_44969

theorem selected_cut_44970 : selected 10 ⟨1241202, by decide⟩
    (prefixPartial 11 88881) = some ⟨11, 2, 0, 1241202, 88881, 1569, 262144⟩ := by
  decide +kernel

theorem context_11_88881_1241202 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88881 ⟨1241202, by decide⟩ :=
  accepted_of_selected 11 88881 ⟨1241202, by decide⟩ ⟨11, 2, 0, 1241202, 88881, 1569, 262144⟩
    (by decide) selected_cut_44970

theorem selected_cut_44971 : selected 10 ⟨1241239, by decide⟩
    (prefixPartial 11 88882) = some ⟨11, 2, 0, 1241239, 88882, 1677, 262144⟩ := by
  decide +kernel

theorem context_11_88882_1241239 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88882 ⟨1241239, by decide⟩ :=
  accepted_of_selected 11 88882 ⟨1241239, by decide⟩ ⟨11, 2, 0, 1241239, 88882, 1677, 262144⟩
    (by decide) selected_cut_44971

theorem selected_cut_44972 : selected 10 ⟨1241260, by decide⟩
    (prefixPartial 11 88883) = some ⟨11, 2, 0, 1241260, 88883, 993, 262144⟩ := by
  decide +kernel

theorem context_11_88883_1241260 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88883 ⟨1241260, by decide⟩ :=
  accepted_of_selected 11 88883 ⟨1241260, by decide⟩ ⟨11, 2, 0, 1241260, 88883, 993, 262144⟩
    (by decide) selected_cut_44972

theorem unmarked_context_10_22220_1241261 : frontier 11 ⟨1241261, by decide⟩
    (prefixCache 10 22220) (prefixPartial 10 22220) = false := by
  decide +kernel

theorem node_context_10_22220_1241261 : EJMOriginalGlobalDAGData.nodes 11 ⟨1241261, by decide⟩ =
    .split (coordinate 10) (![⟨1241170, by decide⟩,⟨1241202, by decide⟩,⟨1241239, by decide⟩,⟨1241260, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22220_1241261 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22220 ⟨1241261, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22220
    ⟨1241261, by decide⟩ (by decide) (![⟨1241170, by decide⟩,⟨1241202, by decide⟩,⟨1241239, by decide⟩,⟨1241260, by decide⟩]) unmarked_context_10_22220_1241261 node_context_10_22220_1241261
  intro a
  fin_cases a
  · exact context_11_88880_1241170
  · exact context_11_88881_1241202
  · exact context_11_88882_1241239
  · exact context_11_88883_1241260

theorem selected_cut_44973 : selected 11 ⟨1241297, by decide⟩
    (prefixPartial 10 22221) = some ⟨10, 2, 0, 1241297, 22221, 1993, 1048576⟩ := by
  decide +kernel

theorem context_10_22221_1241297 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22221 ⟨1241297, by decide⟩ :=
  accepted_of_selected 10 22221 ⟨1241297, by decide⟩ ⟨10, 2, 0, 1241297, 22221, 1993, 1048576⟩
    (by decide) selected_cut_44973

theorem selected_cut_44974 : selected 11 ⟨1241347, by decide⟩
    (prefixPartial 10 22222) = some ⟨10, 2, 0, 1241347, 22222, 1637, 1048576⟩ := by
  decide +kernel

theorem context_10_22222_1241347 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22222 ⟨1241347, by decide⟩ :=
  accepted_of_selected 10 22222 ⟨1241347, by decide⟩ ⟨10, 2, 0, 1241347, 22222, 1637, 1048576⟩
    (by decide) selected_cut_44974

theorem selected_cut_44975 : selected 11 ⟨1241357, by decide⟩
    (prefixPartial 10 22223) = some ⟨10, 2, 0, 1241357, 22223, 129, 1048576⟩ := by
  decide +kernel

theorem context_10_22223_1241357 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22223 ⟨1241357, by decide⟩ :=
  accepted_of_selected 10 22223 ⟨1241357, by decide⟩ ⟨10, 2, 0, 1241357, 22223, 129, 1048576⟩
    (by decide) selected_cut_44975

theorem unmarked_context_9_5555_1241358 : frontier 12 ⟨1241358, by decide⟩
    (prefixCache 9 5555) (prefixPartial 9 5555) = false := by
  decide +kernel

theorem node_context_9_5555_1241358 : EJMOriginalGlobalDAGData.nodes 12 ⟨1241358, by decide⟩ =
    .split (coordinate 9) (![⟨1241261, by decide⟩,⟨1241297, by decide⟩,⟨1241347, by decide⟩,⟨1241357, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5555_1241358 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5555 ⟨1241358, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5555
    ⟨1241358, by decide⟩ (by decide) (![⟨1241261, by decide⟩,⟨1241297, by decide⟩,⟨1241347, by decide⟩,⟨1241357, by decide⟩]) unmarked_context_9_5555_1241358 node_context_9_5555_1241358
  intro a
  fin_cases a
  · exact context_10_22220_1241261
  · exact context_10_22221_1241297
  · exact context_10_22222_1241347
  · exact context_10_22223_1241357

theorem unmarked_context_8_1388_1241359 : frontier 13 ⟨1241359, by decide⟩
    (prefixCache 8 1388) (prefixPartial 8 1388) = false := by
  decide +kernel

theorem node_context_8_1388_1241359 : EJMOriginalGlobalDAGData.nodes 13 ⟨1241359, by decide⟩ =
    .split (coordinate 8) (![⟨1239568, by decide⟩,⟨1240388, by decide⟩,⟨1241149, by decide⟩,⟨1241358, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1388_1241359 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1388 ⟨1241359, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1388
    ⟨1241359, by decide⟩ (by decide) (![⟨1239568, by decide⟩,⟨1240388, by decide⟩,⟨1241149, by decide⟩,⟨1241358, by decide⟩]) unmarked_context_8_1388_1241359 node_context_8_1388_1241359
  intro a
  fin_cases a
  · exact context_9_5552_1239568
  · exact context_9_5553_1240388
  · exact context_9_5554_1241149
  · exact context_9_5555_1241358

theorem selected_cut_44976 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 88896) = some ⟨11, 1, 0, 434745, 88896, 1, 262144⟩ := by
  decide +kernel

theorem context_11_88896_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88896 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 88896 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 88896, 1, 262144⟩
    (by decide) selected_cut_44976

theorem selected_cut_44977 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 355588) = some ⟨12, 1, 0, 448748, 355588, 1, 65536⟩ := by
  decide +kernel

theorem context_12_355588_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355588 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 355588 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 355588, 1, 65536⟩
    (by decide) selected_cut_44977

theorem selected_cut_44978 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 355589) = some ⟨12, 1, 0, 34034, 355589, 1, 65536⟩ := by
  decide +kernel

theorem context_12_355589_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355589 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 355589 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 355589, 1, 65536⟩
    (by decide) selected_cut_44978

theorem selected_cut_44979 : selected 9 ⟨1241428, by decide⟩
    (prefixPartial 12 355590) = some ⟨12, 2, 0, 1241428, 355590, 2681, 65536⟩ := by
  decide +kernel

theorem context_12_355590_1241428 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355590 ⟨1241428, by decide⟩ :=
  accepted_of_selected 12 355590 ⟨1241428, by decide⟩ ⟨12, 2, 0, 1241428, 355590, 2681, 65536⟩
    (by decide) selected_cut_44979

theorem selected_cut_44980 : selected 9 ⟨1241493, by decide⟩
    (prefixPartial 12 355591) = some ⟨12, 2, 0, 1241493, 355591, 2757, 65536⟩ := by
  decide +kernel

theorem context_12_355591_1241493 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355591 ⟨1241493, by decide⟩ :=
  accepted_of_selected 12 355591 ⟨1241493, by decide⟩ ⟨12, 2, 0, 1241493, 355591, 2757, 65536⟩
    (by decide) selected_cut_44980

theorem unmarked_context_11_88897_1241494 : frontier 10 ⟨1241494, by decide⟩
    (prefixCache 11 88897) (prefixPartial 11 88897) = false := by
  decide +kernel

theorem node_context_11_88897_1241494 : EJMOriginalGlobalDAGData.nodes 10 ⟨1241494, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨34034, by decide⟩,⟨1241428, by decide⟩,⟨1241493, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88897_1241494 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88897 ⟨1241494, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88897
    ⟨1241494, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨34034, by decide⟩,⟨1241428, by decide⟩,⟨1241493, by decide⟩]) unmarked_context_11_88897_1241494 node_context_11_88897_1241494
  intro a
  fin_cases a
  · exact context_12_355588_448748
  · exact context_12_355589_34034
  · exact context_12_355590_1241428
  · exact context_12_355591_1241493

theorem selected_cut_44981 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 355592) = some ⟨12, 1, 0, 448748, 355592, 1, 65536⟩ := by
  decide +kernel

theorem context_12_355592_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355592 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 355592 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 355592, 1, 65536⟩
    (by decide) selected_cut_44981

theorem selected_cut_44982 : selected 9 ⟨1241590, by decide⟩
    (prefixPartial 12 355593) = some ⟨12, 2, 0, 1241590, 355593, 3097, 65536⟩ := by
  decide +kernel

theorem context_12_355593_1241590 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355593 ⟨1241590, by decide⟩ :=
  accepted_of_selected 12 355593 ⟨1241590, by decide⟩ ⟨12, 2, 0, 1241590, 355593, 3097, 65536⟩
    (by decide) selected_cut_44982

theorem selected_cut_44983 : selected 9 ⟨1241661, by decide⟩
    (prefixPartial 12 355594) = some ⟨12, 2, 0, 1241661, 355594, 2961, 65536⟩ := by
  decide +kernel

theorem context_12_355594_1241661 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355594 ⟨1241661, by decide⟩ :=
  accepted_of_selected 12 355594 ⟨1241661, by decide⟩ ⟨12, 2, 0, 1241661, 355594, 2961, 65536⟩
    (by decide) selected_cut_44983

theorem selected_cut_44984 : selected 9 ⟨1241732, by decide⟩
    (prefixPartial 12 355595) = some ⟨12, 2, 0, 1241732, 355595, 3173, 65536⟩ := by
  decide +kernel

theorem context_12_355595_1241732 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355595 ⟨1241732, by decide⟩ :=
  accepted_of_selected 12 355595 ⟨1241732, by decide⟩ ⟨12, 2, 0, 1241732, 355595, 3173, 65536⟩
    (by decide) selected_cut_44984

theorem unmarked_context_11_88898_1241733 : frontier 10 ⟨1241733, by decide⟩
    (prefixCache 11 88898) (prefixPartial 11 88898) = false := by
  decide +kernel

theorem node_context_11_88898_1241733 : EJMOriginalGlobalDAGData.nodes 10 ⟨1241733, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨1241590, by decide⟩,⟨1241661, by decide⟩,⟨1241732, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88898_1241733 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88898 ⟨1241733, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88898
    ⟨1241733, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨1241590, by decide⟩,⟨1241661, by decide⟩,⟨1241732, by decide⟩]) unmarked_context_11_88898_1241733 node_context_11_88898_1241733
  intro a
  fin_cases a
  · exact context_12_355592_448748
  · exact context_12_355593_1241590
  · exact context_12_355594_1241661
  · exact context_12_355595_1241732

theorem selected_cut_44985 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 355596) = some ⟨12, 1, 0, 448748, 355596, 1, 65536⟩ := by
  decide +kernel

theorem context_12_355596_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355596 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 355596 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 355596, 1, 65536⟩
    (by decide) selected_cut_44985

theorem selected_cut_44986 : selected 9 ⟨390434, by decide⟩
    (prefixPartial 12 355597) = some ⟨12, 1, 0, 390434, 355597, 1, 65536⟩ := by
  decide +kernel

theorem context_12_355597_390434 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355597 ⟨390434, by decide⟩ :=
  accepted_of_selected 12 355597 ⟨390434, by decide⟩ ⟨12, 1, 0, 390434, 355597, 1, 65536⟩
    (by decide) selected_cut_44986

theorem selected_cut_44987 : selected 9 ⟨1241787, by decide⟩
    (prefixPartial 12 355598) = some ⟨12, 2, 0, 1241787, 355598, 2621, 65536⟩ := by
  decide +kernel

theorem context_12_355598_1241787 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355598 ⟨1241787, by decide⟩ :=
  accepted_of_selected 12 355598 ⟨1241787, by decide⟩ ⟨12, 2, 0, 1241787, 355598, 2621, 65536⟩
    (by decide) selected_cut_44987

theorem selected_cut_44988 : selected 9 ⟨1241850, by decide⟩
    (prefixPartial 12 355599) = some ⟨12, 2, 0, 1241850, 355599, 2905, 65536⟩ := by
  decide +kernel

theorem context_12_355599_1241850 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355599 ⟨1241850, by decide⟩ :=
  accepted_of_selected 12 355599 ⟨1241850, by decide⟩ ⟨12, 2, 0, 1241850, 355599, 2905, 65536⟩
    (by decide) selected_cut_44988

theorem unmarked_context_11_88899_1241851 : frontier 10 ⟨1241851, by decide⟩
    (prefixCache 11 88899) (prefixPartial 11 88899) = false := by
  decide +kernel

theorem node_context_11_88899_1241851 : EJMOriginalGlobalDAGData.nodes 10 ⟨1241851, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨390434, by decide⟩,⟨1241787, by decide⟩,⟨1241850, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88899_1241851 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88899 ⟨1241851, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88899
    ⟨1241851, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨390434, by decide⟩,⟨1241787, by decide⟩,⟨1241850, by decide⟩]) unmarked_context_11_88899_1241851 node_context_11_88899_1241851
  intro a
  fin_cases a
  · exact context_12_355596_448748
  · exact context_12_355597_390434
  · exact context_12_355598_1241787
  · exact context_12_355599_1241850

theorem unmarked_context_10_22224_1241852 : frontier 11 ⟨1241852, by decide⟩
    (prefixCache 10 22224) (prefixPartial 10 22224) = false := by
  decide +kernel

theorem node_context_10_22224_1241852 : EJMOriginalGlobalDAGData.nodes 11 ⟨1241852, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨1241494, by decide⟩,⟨1241733, by decide⟩,⟨1241851, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22224_1241852 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22224 ⟨1241852, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22224
    ⟨1241852, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨1241494, by decide⟩,⟨1241733, by decide⟩,⟨1241851, by decide⟩]) unmarked_context_10_22224_1241852 node_context_10_22224_1241852
  intro a
  fin_cases a
  · exact context_11_88896_434745
  · exact context_11_88897_1241494
  · exact context_11_88898_1241733
  · exact context_11_88899_1241851

theorem selected_cut_44989 : selected 9 ⟨435160, by decide⟩
    (prefixPartial 12 355600) = some ⟨12, 1, 0, 435160, 355600, 1, 65536⟩ := by
  decide +kernel

theorem context_12_355600_435160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355600 ⟨435160, by decide⟩ :=
  accepted_of_selected 12 355600 ⟨435160, by decide⟩ ⟨12, 1, 0, 435160, 355600, 1, 65536⟩
    (by decide) selected_cut_44989

theorem selected_cut_44990 : selected 9 ⟨1241910, by decide⟩
    (prefixPartial 12 355601) = some ⟨12, 2, 0, 1241910, 355601, 2657, 65536⟩ := by
  decide +kernel

theorem context_12_355601_1241910 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355601 ⟨1241910, by decide⟩ :=
  accepted_of_selected 12 355601 ⟨1241910, by decide⟩ ⟨12, 2, 0, 1241910, 355601, 2657, 65536⟩
    (by decide) selected_cut_44990

theorem selected_cut_44991 : selected 9 ⟨1241963, by decide⟩
    (prefixPartial 12 355602) = some ⟨12, 2, 0, 1241963, 355602, 2613, 65536⟩ := by
  decide +kernel

theorem context_12_355602_1241963 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355602 ⟨1241963, by decide⟩ :=
  accepted_of_selected 12 355602 ⟨1241963, by decide⟩ ⟨12, 2, 0, 1241963, 355602, 2613, 65536⟩
    (by decide) selected_cut_44991

theorem selected_cut_44992 : selected 9 ⟨1242019, by decide⟩
    (prefixPartial 12 355603) = some ⟨12, 2, 0, 1242019, 355603, 2789, 65536⟩ := by
  decide +kernel

theorem context_12_355603_1242019 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355603 ⟨1242019, by decide⟩ :=
  accepted_of_selected 12 355603 ⟨1242019, by decide⟩ ⟨12, 2, 0, 1242019, 355603, 2789, 65536⟩
    (by decide) selected_cut_44992

theorem unmarked_context_11_88900_1242020 : frontier 10 ⟨1242020, by decide⟩
    (prefixCache 11 88900) (prefixPartial 11 88900) = false := by
  decide +kernel

theorem node_context_11_88900_1242020 : EJMOriginalGlobalDAGData.nodes 10 ⟨1242020, by decide⟩ =
    .split (coordinate 11) (![⟨435160, by decide⟩,⟨1241910, by decide⟩,⟨1241963, by decide⟩,⟨1242019, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88900_1242020 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88900 ⟨1242020, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88900
    ⟨1242020, by decide⟩ (by decide) (![⟨435160, by decide⟩,⟨1241910, by decide⟩,⟨1241963, by decide⟩,⟨1242019, by decide⟩]) unmarked_context_11_88900_1242020 node_context_11_88900_1242020
  intro a
  fin_cases a
  · exact context_12_355600_435160
  · exact context_12_355601_1241910
  · exact context_12_355602_1241963
  · exact context_12_355603_1242019

theorem selected_cut_44993 : selected 10 ⟨1242071, by decide⟩
    (prefixPartial 11 88901) = some ⟨11, 2, 0, 1242071, 88901, 2493, 262144⟩ := by
  decide +kernel

theorem context_11_88901_1242071 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88901 ⟨1242071, by decide⟩ :=
  accepted_of_selected 11 88901 ⟨1242071, by decide⟩ ⟨11, 2, 0, 1242071, 88901, 2493, 262144⟩
    (by decide) selected_cut_44993

theorem selected_cut_44994 : selected 9 ⟨449505, by decide⟩
    (prefixPartial 12 355608) = some ⟨12, 1, 0, 449505, 355608, 1, 65536⟩ := by
  decide +kernel

theorem context_12_355608_449505 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355608 ⟨449505, by decide⟩ :=
  accepted_of_selected 12 355608 ⟨449505, by decide⟩ ⟨12, 1, 0, 449505, 355608, 1, 65536⟩
    (by decide) selected_cut_44994

theorem selected_cut_44995 : selected 9 ⟨1242118, by decide⟩
    (prefixPartial 12 355609) = some ⟨12, 2, 0, 1242118, 355609, 2481, 65536⟩ := by
  decide +kernel

theorem context_12_355609_1242118 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355609 ⟨1242118, by decide⟩ :=
  accepted_of_selected 12 355609 ⟨1242118, by decide⟩ ⟨12, 2, 0, 1242118, 355609, 2481, 65536⟩
    (by decide) selected_cut_44995

theorem selected_cut_44996 : selected 9 ⟨1242169, by decide⟩
    (prefixPartial 12 355610) = some ⟨12, 2, 0, 1242169, 355610, 2577, 65536⟩ := by
  decide +kernel

theorem context_12_355610_1242169 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355610 ⟨1242169, by decide⟩ :=
  accepted_of_selected 12 355610 ⟨1242169, by decide⟩ ⟨12, 2, 0, 1242169, 355610, 2577, 65536⟩
    (by decide) selected_cut_44996

theorem selected_cut_44997 : selected 9 ⟨1242220, by decide⟩
    (prefixPartial 12 355611) = some ⟨12, 2, 0, 1242220, 355611, 2745, 65536⟩ := by
  decide +kernel

theorem context_12_355611_1242220 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355611 ⟨1242220, by decide⟩ :=
  accepted_of_selected 12 355611 ⟨1242220, by decide⟩ ⟨12, 2, 0, 1242220, 355611, 2745, 65536⟩
    (by decide) selected_cut_44997

theorem unmarked_context_11_88902_1242221 : frontier 10 ⟨1242221, by decide⟩
    (prefixCache 11 88902) (prefixPartial 11 88902) = false := by
  decide +kernel

theorem node_context_11_88902_1242221 : EJMOriginalGlobalDAGData.nodes 10 ⟨1242221, by decide⟩ =
    .split (coordinate 11) (![⟨449505, by decide⟩,⟨1242118, by decide⟩,⟨1242169, by decide⟩,⟨1242220, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88902_1242221 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88902 ⟨1242221, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88902
    ⟨1242221, by decide⟩ (by decide) (![⟨449505, by decide⟩,⟨1242118, by decide⟩,⟨1242169, by decide⟩,⟨1242220, by decide⟩]) unmarked_context_11_88902_1242221 node_context_11_88902_1242221
  intro a
  fin_cases a
  · exact context_12_355608_449505
  · exact context_12_355609_1242118
  · exact context_12_355610_1242169
  · exact context_12_355611_1242220

theorem selected_cut_44998 : selected 9 ⟨539296, by decide⟩
    (prefixPartial 12 355612) = some ⟨12, 1, 0, 539296, 355612, 1, 65536⟩ := by
  decide +kernel

theorem context_12_355612_539296 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355612 ⟨539296, by decide⟩ :=
  accepted_of_selected 12 355612 ⟨539296, by decide⟩ ⟨12, 1, 0, 539296, 355612, 1, 65536⟩
    (by decide) selected_cut_44998

theorem selected_cut_44999 : selected 9 ⟨1242257, by decide⟩
    (prefixPartial 12 355613) = some ⟨12, 2, 0, 1242257, 355613, 2193, 65536⟩ := by
  decide +kernel

theorem context_12_355613_1242257 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355613 ⟨1242257, by decide⟩ :=
  accepted_of_selected 12 355613 ⟨1242257, by decide⟩ ⟨12, 2, 0, 1242257, 355613, 2193, 65536⟩
    (by decide) selected_cut_44999

theorem selected_cut_45000 : selected 9 ⟨1242296, by decide⟩
    (prefixPartial 12 355614) = some ⟨12, 2, 0, 1242296, 355614, 2377, 65536⟩ := by
  decide +kernel

theorem context_12_355614_1242296 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355614 ⟨1242296, by decide⟩ :=
  accepted_of_selected 12 355614 ⟨1242296, by decide⟩ ⟨12, 2, 0, 1242296, 355614, 2377, 65536⟩
    (by decide) selected_cut_45000

theorem selected_cut_45001 : selected 9 ⟨757807, by decide⟩
    (prefixPartial 12 355615) = some ⟨12, 1, 0, 757807, 355615, 1, 65536⟩ := by
  decide +kernel

theorem context_12_355615_757807 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355615 ⟨757807, by decide⟩ :=
  accepted_of_selected 12 355615 ⟨757807, by decide⟩ ⟨12, 1, 0, 757807, 355615, 1, 65536⟩
    (by decide) selected_cut_45001

theorem unmarked_context_11_88903_1242297 : frontier 10 ⟨1242297, by decide⟩
    (prefixCache 11 88903) (prefixPartial 11 88903) = false := by
  decide +kernel

theorem node_context_11_88903_1242297 : EJMOriginalGlobalDAGData.nodes 10 ⟨1242297, by decide⟩ =
    .split (coordinate 11) (![⟨539296, by decide⟩,⟨1242257, by decide⟩,⟨1242296, by decide⟩,⟨757807, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88903_1242297 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88903 ⟨1242297, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88903
    ⟨1242297, by decide⟩ (by decide) (![⟨539296, by decide⟩,⟨1242257, by decide⟩,⟨1242296, by decide⟩,⟨757807, by decide⟩]) unmarked_context_11_88903_1242297 node_context_11_88903_1242297
  intro a
  fin_cases a
  · exact context_12_355612_539296
  · exact context_12_355613_1242257
  · exact context_12_355614_1242296
  · exact context_12_355615_757807

theorem unmarked_context_10_22225_1242298 : frontier 11 ⟨1242298, by decide⟩
    (prefixCache 10 22225) (prefixPartial 10 22225) = false := by
  decide +kernel

theorem node_context_10_22225_1242298 : EJMOriginalGlobalDAGData.nodes 11 ⟨1242298, by decide⟩ =
    .split (coordinate 10) (![⟨1242020, by decide⟩,⟨1242071, by decide⟩,⟨1242221, by decide⟩,⟨1242297, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22225_1242298 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22225 ⟨1242298, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22225
    ⟨1242298, by decide⟩ (by decide) (![⟨1242020, by decide⟩,⟨1242071, by decide⟩,⟨1242221, by decide⟩,⟨1242297, by decide⟩]) unmarked_context_10_22225_1242298 node_context_10_22225_1242298
  intro a
  fin_cases a
  · exact context_11_88900_1242020
  · exact context_11_88901_1242071
  · exact context_11_88902_1242221
  · exact context_11_88903_1242297

theorem selected_cut_45002 : selected 9 ⟨1187656, by decide⟩
    (prefixPartial 12 355616) = some ⟨12, 1, 0, 1187656, 355616, 1, 65536⟩ := by
  decide +kernel

theorem context_12_355616_1187656 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355616 ⟨1187656, by decide⟩ :=
  accepted_of_selected 12 355616 ⟨1187656, by decide⟩ ⟨12, 1, 0, 1187656, 355616, 1, 65536⟩
    (by decide) selected_cut_45002

theorem selected_cut_45003 : selected 9 ⟨1242353, by decide⟩
    (prefixPartial 12 355617) = some ⟨12, 2, 0, 1242353, 355617, 2753, 65536⟩ := by
  decide +kernel

theorem context_12_355617_1242353 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355617 ⟨1242353, by decide⟩ :=
  accepted_of_selected 12 355617 ⟨1242353, by decide⟩ ⟨12, 2, 0, 1242353, 355617, 2753, 65536⟩
    (by decide) selected_cut_45003

theorem selected_cut_45004 : selected 9 ⟨1242403, by decide⟩
    (prefixPartial 12 355618) = some ⟨12, 2, 0, 1242403, 355618, 2577, 65536⟩ := by
  decide +kernel

theorem context_12_355618_1242403 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355618 ⟨1242403, by decide⟩ :=
  accepted_of_selected 12 355618 ⟨1242403, by decide⟩ ⟨12, 2, 0, 1242403, 355618, 2577, 65536⟩
    (by decide) selected_cut_45004

theorem selected_cut_45005 : selected 9 ⟨1242459, by decide⟩
    (prefixPartial 12 355619) = some ⟨12, 2, 0, 1242459, 355619, 2785, 65536⟩ := by
  decide +kernel

theorem context_12_355619_1242459 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355619 ⟨1242459, by decide⟩ :=
  accepted_of_selected 12 355619 ⟨1242459, by decide⟩ ⟨12, 2, 0, 1242459, 355619, 2785, 65536⟩
    (by decide) selected_cut_45005

theorem unmarked_context_11_88904_1242460 : frontier 10 ⟨1242460, by decide⟩
    (prefixCache 11 88904) (prefixPartial 11 88904) = false := by
  decide +kernel

theorem node_context_11_88904_1242460 : EJMOriginalGlobalDAGData.nodes 10 ⟨1242460, by decide⟩ =
    .split (coordinate 11) (![⟨1187656, by decide⟩,⟨1242353, by decide⟩,⟨1242403, by decide⟩,⟨1242459, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88904_1242460 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88904 ⟨1242460, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88904
    ⟨1242460, by decide⟩ (by decide) (![⟨1187656, by decide⟩,⟨1242353, by decide⟩,⟨1242403, by decide⟩,⟨1242459, by decide⟩]) unmarked_context_11_88904_1242460 node_context_11_88904_1242460
  intro a
  fin_cases a
  · exact context_12_355616_1187656
  · exact context_12_355617_1242353
  · exact context_12_355618_1242403
  · exact context_12_355619_1242459

theorem selected_cut_45006 : selected 9 ⟨1228238, by decide⟩
    (prefixPartial 12 355620) = some ⟨12, 1, 0, 1228238, 355620, 1, 65536⟩ := by
  decide +kernel

theorem context_12_355620_1228238 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355620 ⟨1228238, by decide⟩ :=
  accepted_of_selected 12 355620 ⟨1228238, by decide⟩ ⟨12, 1, 0, 1228238, 355620, 1, 65536⟩
    (by decide) selected_cut_45006

theorem selected_cut_45007 : selected 9 ⟨891951, by decide⟩
    (prefixPartial 12 355621) = some ⟨12, 1, 0, 891951, 355621, 1, 65536⟩ := by
  decide +kernel

theorem context_12_355621_891951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355621 ⟨891951, by decide⟩ :=
  accepted_of_selected 12 355621 ⟨891951, by decide⟩ ⟨12, 1, 0, 891951, 355621, 1, 65536⟩
    (by decide) selected_cut_45007

theorem selected_cut_45008 : selected 9 ⟨1242503, by decide⟩
    (prefixPartial 12 355622) = some ⟨12, 2, 0, 1242503, 355622, 2381, 65536⟩ := by
  decide +kernel

theorem context_12_355622_1242503 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355622 ⟨1242503, by decide⟩ :=
  accepted_of_selected 12 355622 ⟨1242503, by decide⟩ ⟨12, 2, 0, 1242503, 355622, 2381, 65536⟩
    (by decide) selected_cut_45008

theorem selected_cut_45009 : selected 9 ⟨1242548, by decide⟩
    (prefixPartial 12 355623) = some ⟨12, 2, 0, 1242548, 355623, 2585, 65536⟩ := by
  decide +kernel

theorem context_12_355623_1242548 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355623 ⟨1242548, by decide⟩ :=
  accepted_of_selected 12 355623 ⟨1242548, by decide⟩ ⟨12, 2, 0, 1242548, 355623, 2585, 65536⟩
    (by decide) selected_cut_45009

theorem unmarked_context_11_88905_1242549 : frontier 10 ⟨1242549, by decide⟩
    (prefixCache 11 88905) (prefixPartial 11 88905) = false := by
  decide +kernel

theorem node_context_11_88905_1242549 : EJMOriginalGlobalDAGData.nodes 10 ⟨1242549, by decide⟩ =
    .split (coordinate 11) (![⟨1228238, by decide⟩,⟨891951, by decide⟩,⟨1242503, by decide⟩,⟨1242548, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88905_1242549 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88905 ⟨1242549, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88905
    ⟨1242549, by decide⟩ (by decide) (![⟨1228238, by decide⟩,⟨891951, by decide⟩,⟨1242503, by decide⟩,⟨1242548, by decide⟩]) unmarked_context_11_88905_1242549 node_context_11_88905_1242549
  intro a
  fin_cases a
  · exact context_12_355620_1228238
  · exact context_12_355621_891951
  · exact context_12_355622_1242503
  · exact context_12_355623_1242548

theorem selected_cut_45010 : selected 9 ⟨1242597, by decide⟩
    (prefixPartial 12 355624) = some ⟨12, 2, 0, 1242597, 355624, 2497, 65536⟩ := by
  decide +kernel

theorem context_12_355624_1242597 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355624 ⟨1242597, by decide⟩ :=
  accepted_of_selected 12 355624 ⟨1242597, by decide⟩ ⟨12, 2, 0, 1242597, 355624, 2497, 65536⟩
    (by decide) selected_cut_45010

theorem selected_cut_45011 : selected 9 ⟨1242643, by decide⟩
    (prefixPartial 12 355625) = some ⟨12, 2, 0, 1242643, 355625, 2589, 65536⟩ := by
  decide +kernel

theorem context_12_355625_1242643 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355625 ⟨1242643, by decide⟩ :=
  accepted_of_selected 12 355625 ⟨1242643, by decide⟩ ⟨12, 2, 0, 1242643, 355625, 2589, 65536⟩
    (by decide) selected_cut_45011

theorem selected_cut_45012 : selected 9 ⟨1172910, by decide⟩
    (prefixPartial 12 355626) = some ⟨12, 1, 0, 1172910, 355626, 1, 65536⟩ := by
  decide +kernel

theorem context_12_355626_1172910 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355626 ⟨1172910, by decide⟩ :=
  accepted_of_selected 12 355626 ⟨1172910, by decide⟩ ⟨12, 1, 0, 1172910, 355626, 1, 65536⟩
    (by decide) selected_cut_45012

theorem selected_cut_45013 : selected 9 ⟨1242698, by decide⟩
    (prefixPartial 12 355627) = some ⟨12, 2, 0, 1242698, 355627, 2765, 65536⟩ := by
  decide +kernel

theorem context_12_355627_1242698 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355627 ⟨1242698, by decide⟩ :=
  accepted_of_selected 12 355627 ⟨1242698, by decide⟩ ⟨12, 2, 0, 1242698, 355627, 2765, 65536⟩
    (by decide) selected_cut_45013

theorem unmarked_context_11_88906_1242699 : frontier 10 ⟨1242699, by decide⟩
    (prefixCache 11 88906) (prefixPartial 11 88906) = false := by
  decide +kernel

theorem node_context_11_88906_1242699 : EJMOriginalGlobalDAGData.nodes 10 ⟨1242699, by decide⟩ =
    .split (coordinate 11) (![⟨1242597, by decide⟩,⟨1242643, by decide⟩,⟨1172910, by decide⟩,⟨1242698, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88906_1242699 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88906 ⟨1242699, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88906
    ⟨1242699, by decide⟩ (by decide) (![⟨1242597, by decide⟩,⟨1242643, by decide⟩,⟨1172910, by decide⟩,⟨1242698, by decide⟩]) unmarked_context_11_88906_1242699 node_context_11_88906_1242699
  intro a
  fin_cases a
  · exact context_12_355624_1242597
  · exact context_12_355625_1242643
  · exact context_12_355626_1172910
  · exact context_12_355627_1242698

theorem selected_cut_45014 : selected 9 ⟨1242729, by decide⟩
    (prefixPartial 12 355628) = some ⟨12, 2, 0, 1242729, 355628, 2177, 65536⟩ := by
  decide +kernel

theorem context_12_355628_1242729 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355628 ⟨1242729, by decide⟩ :=
  accepted_of_selected 12 355628 ⟨1242729, by decide⟩ ⟨12, 2, 0, 1242729, 355628, 2177, 65536⟩
    (by decide) selected_cut_45014

theorem selected_cut_45015 : selected 9 ⟨1242767, by decide⟩
    (prefixPartial 12 355629) = some ⟨12, 2, 0, 1242767, 355629, 2189, 65536⟩ := by
  decide +kernel

theorem context_12_355629_1242767 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355629 ⟨1242767, by decide⟩ :=
  accepted_of_selected 12 355629 ⟨1242767, by decide⟩ ⟨12, 2, 0, 1242767, 355629, 2189, 65536⟩
    (by decide) selected_cut_45015

theorem selected_cut_45016 : selected 9 ⟨1242808, by decide⟩
    (prefixPartial 12 355630) = some ⟨12, 2, 0, 1242808, 355630, 2229, 65536⟩ := by
  decide +kernel

theorem context_12_355630_1242808 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355630 ⟨1242808, by decide⟩ :=
  accepted_of_selected 12 355630 ⟨1242808, by decide⟩ ⟨12, 2, 0, 1242808, 355630, 2229, 65536⟩
    (by decide) selected_cut_45016

theorem selected_cut_45017 : selected 9 ⟨1242857, by decide⟩
    (prefixPartial 12 355631) = some ⟨12, 2, 0, 1242857, 355631, 2497, 65536⟩ := by
  decide +kernel

theorem context_12_355631_1242857 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355631 ⟨1242857, by decide⟩ :=
  accepted_of_selected 12 355631 ⟨1242857, by decide⟩ ⟨12, 2, 0, 1242857, 355631, 2497, 65536⟩
    (by decide) selected_cut_45017

theorem unmarked_context_11_88907_1242858 : frontier 10 ⟨1242858, by decide⟩
    (prefixCache 11 88907) (prefixPartial 11 88907) = false := by
  decide +kernel

theorem node_context_11_88907_1242858 : EJMOriginalGlobalDAGData.nodes 10 ⟨1242858, by decide⟩ =
    .split (coordinate 11) (![⟨1242729, by decide⟩,⟨1242767, by decide⟩,⟨1242808, by decide⟩,⟨1242857, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88907_1242858 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88907 ⟨1242858, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88907
    ⟨1242858, by decide⟩ (by decide) (![⟨1242729, by decide⟩,⟨1242767, by decide⟩,⟨1242808, by decide⟩,⟨1242857, by decide⟩]) unmarked_context_11_88907_1242858 node_context_11_88907_1242858
  intro a
  fin_cases a
  · exact context_12_355628_1242729
  · exact context_12_355629_1242767
  · exact context_12_355630_1242808
  · exact context_12_355631_1242857

theorem unmarked_context_10_22226_1242859 : frontier 11 ⟨1242859, by decide⟩
    (prefixCache 10 22226) (prefixPartial 10 22226) = false := by
  decide +kernel

theorem node_context_10_22226_1242859 : EJMOriginalGlobalDAGData.nodes 11 ⟨1242859, by decide⟩ =
    .split (coordinate 10) (![⟨1242460, by decide⟩,⟨1242549, by decide⟩,⟨1242699, by decide⟩,⟨1242858, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22226_1242859 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22226 ⟨1242859, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22226
    ⟨1242859, by decide⟩ (by decide) (![⟨1242460, by decide⟩,⟨1242549, by decide⟩,⟨1242699, by decide⟩,⟨1242858, by decide⟩]) unmarked_context_10_22226_1242859 node_context_10_22226_1242859
  intro a
  fin_cases a
  · exact context_11_88904_1242460
  · exact context_11_88905_1242549
  · exact context_11_88906_1242699
  · exact context_11_88907_1242858

theorem selected_cut_45018 : selected 9 ⟨1187656, by decide⟩
    (prefixPartial 12 355632) = some ⟨12, 1, 0, 1187656, 355632, 1, 65536⟩ := by
  decide +kernel

theorem context_12_355632_1187656 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355632 ⟨1187656, by decide⟩ :=
  accepted_of_selected 12 355632 ⟨1187656, by decide⟩ ⟨12, 1, 0, 1187656, 355632, 1, 65536⟩
    (by decide) selected_cut_45018

theorem selected_cut_45019 : selected 9 ⟨1242901, by decide⟩
    (prefixPartial 12 355633) = some ⟨12, 2, 0, 1242901, 355633, 2177, 65536⟩ := by
  decide +kernel

theorem context_12_355633_1242901 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355633 ⟨1242901, by decide⟩ :=
  accepted_of_selected 12 355633 ⟨1242901, by decide⟩ ⟨12, 2, 0, 1242901, 355633, 2177, 65536⟩
    (by decide) selected_cut_45019

theorem selected_cut_45020 : selected 9 ⟨1242940, by decide⟩
    (prefixPartial 12 355634) = some ⟨12, 2, 0, 1242940, 355634, 2025, 65536⟩ := by
  decide +kernel

theorem context_12_355634_1242940 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355634 ⟨1242940, by decide⟩ :=
  accepted_of_selected 12 355634 ⟨1242940, by decide⟩ ⟨12, 2, 0, 1242940, 355634, 2025, 65536⟩
    (by decide) selected_cut_45020

theorem selected_cut_45021 : selected 9 ⟨1242979, by decide⟩
    (prefixPartial 12 355635) = some ⟨12, 2, 0, 1242979, 355635, 2201, 65536⟩ := by
  decide +kernel

theorem context_12_355635_1242979 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355635 ⟨1242979, by decide⟩ :=
  accepted_of_selected 12 355635 ⟨1242979, by decide⟩ ⟨12, 2, 0, 1242979, 355635, 2201, 65536⟩
    (by decide) selected_cut_45021

theorem unmarked_context_11_88908_1242980 : frontier 10 ⟨1242980, by decide⟩
    (prefixCache 11 88908) (prefixPartial 11 88908) = false := by
  decide +kernel

theorem node_context_11_88908_1242980 : EJMOriginalGlobalDAGData.nodes 10 ⟨1242980, by decide⟩ =
    .split (coordinate 11) (![⟨1187656, by decide⟩,⟨1242901, by decide⟩,⟨1242940, by decide⟩,⟨1242979, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88908_1242980 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88908 ⟨1242980, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88908
    ⟨1242980, by decide⟩ (by decide) (![⟨1187656, by decide⟩,⟨1242901, by decide⟩,⟨1242940, by decide⟩,⟨1242979, by decide⟩]) unmarked_context_11_88908_1242980 node_context_11_88908_1242980
  intro a
  fin_cases a
  · exact context_12_355632_1187656
  · exact context_12_355633_1242901
  · exact context_12_355634_1242940
  · exact context_12_355635_1242979

theorem selected_cut_45022 : selected 10 ⟨1243045, by decide⟩
    (prefixPartial 11 88909) = some ⟨11, 2, 0, 1243045, 88909, 3949, 262144⟩ := by
  decide +kernel

theorem context_11_88909_1243045 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88909 ⟨1243045, by decide⟩ :=
  accepted_of_selected 11 88909 ⟨1243045, by decide⟩ ⟨11, 2, 0, 1243045, 88909, 3949, 262144⟩
    (by decide) selected_cut_45022

theorem selected_cut_45023 : selected 9 ⟨1243082, by decide⟩
    (prefixPartial 12 355640) = some ⟨12, 2, 0, 1243082, 355640, 2065, 65536⟩ := by
  decide +kernel

theorem context_12_355640_1243082 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355640 ⟨1243082, by decide⟩ :=
  accepted_of_selected 12 355640 ⟨1243082, by decide⟩ ⟨12, 2, 0, 1243082, 355640, 2065, 65536⟩
    (by decide) selected_cut_45023

theorem selected_cut_45024 : selected 9 ⟨1243121, by decide⟩
    (prefixPartial 12 355641) = some ⟨12, 2, 0, 1243121, 355641, 2097, 65536⟩ := by
  decide +kernel

theorem context_12_355641_1243121 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355641 ⟨1243121, by decide⟩ :=
  accepted_of_selected 12 355641 ⟨1243121, by decide⟩ ⟨12, 2, 0, 1243121, 355641, 2097, 65536⟩
    (by decide) selected_cut_45024

theorem selected_cut_45025 : selected 9 ⟨1243162, by decide⟩
    (prefixPartial 12 355642) = some ⟨12, 2, 0, 1243162, 355642, 2013, 65536⟩ := by
  decide +kernel

theorem context_12_355642_1243162 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355642 ⟨1243162, by decide⟩ :=
  accepted_of_selected 12 355642 ⟨1243162, by decide⟩ ⟨12, 2, 0, 1243162, 355642, 2013, 65536⟩
    (by decide) selected_cut_45025

theorem selected_cut_45026 : selected 9 ⟨1243192, by decide⟩
    (prefixPartial 12 355643) = some ⟨12, 2, 0, 1243192, 355643, 2085, 65536⟩ := by
  decide +kernel

theorem context_12_355643_1243192 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355643 ⟨1243192, by decide⟩ :=
  accepted_of_selected 12 355643 ⟨1243192, by decide⟩ ⟨12, 2, 0, 1243192, 355643, 2085, 65536⟩
    (by decide) selected_cut_45026

theorem unmarked_context_11_88910_1243193 : frontier 10 ⟨1243193, by decide⟩
    (prefixCache 11 88910) (prefixPartial 11 88910) = false := by
  decide +kernel

theorem node_context_11_88910_1243193 : EJMOriginalGlobalDAGData.nodes 10 ⟨1243193, by decide⟩ =
    .split (coordinate 11) (![⟨1243082, by decide⟩,⟨1243121, by decide⟩,⟨1243162, by decide⟩,⟨1243192, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88910_1243193 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88910 ⟨1243193, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88910
    ⟨1243193, by decide⟩ (by decide) (![⟨1243082, by decide⟩,⟨1243121, by decide⟩,⟨1243162, by decide⟩,⟨1243192, by decide⟩]) unmarked_context_11_88910_1243193 node_context_11_88910_1243193
  intro a
  fin_cases a
  · exact context_12_355640_1243082
  · exact context_12_355641_1243121
  · exact context_12_355642_1243162
  · exact context_12_355643_1243192

theorem selected_cut_45027 : selected 10 ⟨977886, by decide⟩
    (prefixPartial 11 88911) = some ⟨11, 1, 0, 977886, 88911, 1, 262144⟩ := by
  decide +kernel

theorem context_11_88911_977886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88911 ⟨977886, by decide⟩ :=
  accepted_of_selected 11 88911 ⟨977886, by decide⟩ ⟨11, 1, 0, 977886, 88911, 1, 262144⟩
    (by decide) selected_cut_45027

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
