/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover150
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_14500 : selected 8 ⟨373952, by decide⟩
    (prefixPartial 13 108919) = some ⟨13, 2, 0, 373952, 108919, 1101, 16384⟩ := by
  decide +kernel

theorem context_13_108919_373952 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108919 ⟨373952, by decide⟩ :=
  accepted_of_selected 13 108919 ⟨373952, by decide⟩ ⟨13, 2, 0, 373952, 108919, 1101, 16384⟩
    (by decide) selected_cut_14500

theorem unmarked_context_12_27229_373953 : frontier 9 ⟨373953, by decide⟩
    (prefixCache 12 27229) (prefixPartial 12 27229) = false := by
  decide +kernel

theorem node_context_12_27229_373953 : EJMOriginalGlobalDAGData.nodes 9 ⟨373953, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨373915, by decide⟩,⟨373939, by decide⟩,⟨373952, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27229_373953 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27229 ⟨373953, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27229
    ⟨373953, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨373915, by decide⟩,⟨373939, by decide⟩,⟨373952, by decide⟩]) unmarked_context_12_27229_373953 node_context_12_27229_373953
  intro a
  fin_cases a
  · exact context_13_108916_3444
  · exact context_13_108917_373915
  · exact context_13_108918_373939
  · exact context_13_108919_373952

theorem selected_cut_14501 : selected 9 ⟨373990, by decide⟩
    (prefixPartial 12 27230) = some ⟨12, 2, 0, 373990, 27230, 3193, 65536⟩ := by
  decide +kernel

theorem context_12_27230_373990 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27230 ⟨373990, by decide⟩ :=
  accepted_of_selected 12 27230 ⟨373990, by decide⟩ ⟨12, 2, 0, 373990, 27230, 3193, 65536⟩
    (by decide) selected_cut_14501

theorem selected_cut_14502 : selected 9 ⟨374038, by decide⟩
    (prefixPartial 12 27231) = some ⟨12, 2, 0, 374038, 27231, 3677, 65536⟩ := by
  decide +kernel

theorem context_12_27231_374038 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27231 ⟨374038, by decide⟩ :=
  accepted_of_selected 12 27231 ⟨374038, by decide⟩ ⟨12, 2, 0, 374038, 27231, 3677, 65536⟩
    (by decide) selected_cut_14502

theorem unmarked_context_11_6807_374039 : frontier 10 ⟨374039, by decide⟩
    (prefixCache 11 6807) (prefixPartial 11 6807) = false := by
  decide +kernel

theorem node_context_11_6807_374039 : EJMOriginalGlobalDAGData.nodes 10 ⟨374039, by decide⟩ =
    .split (coordinate 11) (![⟨373889, by decide⟩,⟨373953, by decide⟩,⟨373990, by decide⟩,⟨374038, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6807_374039 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6807 ⟨374039, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6807
    ⟨374039, by decide⟩ (by decide) (![⟨373889, by decide⟩,⟨373953, by decide⟩,⟨373990, by decide⟩,⟨374038, by decide⟩]) unmarked_context_11_6807_374039 node_context_11_6807_374039
  intro a
  fin_cases a
  · exact context_12_27228_373889
  · exact context_12_27229_373953
  · exact context_12_27230_373990
  · exact context_12_27231_374038

theorem unmarked_context_10_1701_374040 : frontier 11 ⟨374040, by decide⟩
    (prefixCache 10 1701) (prefixPartial 10 1701) = false := by
  decide +kernel

theorem node_context_10_1701_374040 : EJMOriginalGlobalDAGData.nodes 11 ⟨374040, by decide⟩ =
    .split (coordinate 10) (![⟨373521, by decide⟩,⟨373666, by decide⟩,⟨373847, by decide⟩,⟨374039, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1701_374040 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1701 ⟨374040, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1701
    ⟨374040, by decide⟩ (by decide) (![⟨373521, by decide⟩,⟨373666, by decide⟩,⟨373847, by decide⟩,⟨374039, by decide⟩]) unmarked_context_10_1701_374040 node_context_10_1701_374040
  intro a
  fin_cases a
  · exact context_11_6804_373521
  · exact context_11_6805_373666
  · exact context_11_6806_373847
  · exact context_11_6807_374039

theorem selected_cut_14503 : selected 9 ⟨374075, by decide⟩
    (prefixPartial 12 27232) = some ⟨12, 2, 0, 374075, 27232, 3273, 65536⟩ := by
  decide +kernel

theorem context_12_27232_374075 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27232 ⟨374075, by decide⟩ :=
  accepted_of_selected 12 27232 ⟨374075, by decide⟩ ⟨12, 2, 0, 374075, 27232, 3273, 65536⟩
    (by decide) selected_cut_14503

theorem selected_cut_14504 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 108932) = some ⟨13, 1, 0, 3444, 108932, 1, 16384⟩ := by
  decide +kernel

theorem context_13_108932_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108932 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 108932 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 108932, 1, 16384⟩
    (by decide) selected_cut_14504

theorem selected_cut_14505 : selected 8 ⟨374109, by decide⟩
    (prefixPartial 13 108933) = some ⟨13, 2, 0, 374109, 108933, 2025, 16384⟩ := by
  decide +kernel

theorem context_13_108933_374109 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108933 ⟨374109, by decide⟩ :=
  accepted_of_selected 13 108933 ⟨374109, by decide⟩ ⟨13, 2, 0, 374109, 108933, 2025, 16384⟩
    (by decide) selected_cut_14505

theorem selected_cut_14506 : selected 8 ⟨374127, by decide⟩
    (prefixPartial 13 108934) = some ⟨13, 2, 0, 374127, 108934, 1713, 16384⟩ := by
  decide +kernel

theorem context_13_108934_374127 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108934 ⟨374127, by decide⟩ :=
  accepted_of_selected 13 108934 ⟨374127, by decide⟩ ⟨13, 2, 0, 374127, 108934, 1713, 16384⟩
    (by decide) selected_cut_14506

theorem selected_cut_14507 : selected 8 ⟨374139, by decide⟩
    (prefixPartial 13 108935) = some ⟨13, 2, 0, 374139, 108935, 1097, 16384⟩ := by
  decide +kernel

theorem context_13_108935_374139 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108935 ⟨374139, by decide⟩ :=
  accepted_of_selected 13 108935 ⟨374139, by decide⟩ ⟨13, 2, 0, 374139, 108935, 1097, 16384⟩
    (by decide) selected_cut_14507

theorem unmarked_context_12_27233_374140 : frontier 9 ⟨374140, by decide⟩
    (prefixCache 12 27233) (prefixPartial 12 27233) = false := by
  decide +kernel

theorem node_context_12_27233_374140 : EJMOriginalGlobalDAGData.nodes 9 ⟨374140, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨374109, by decide⟩,⟨374127, by decide⟩,⟨374139, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27233_374140 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27233 ⟨374140, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27233
    ⟨374140, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨374109, by decide⟩,⟨374127, by decide⟩,⟨374139, by decide⟩]) unmarked_context_12_27233_374140 node_context_12_27233_374140
  intro a
  fin_cases a
  · exact context_13_108932_3444
  · exact context_13_108933_374109
  · exact context_13_108934_374127
  · exact context_13_108935_374139

theorem selected_cut_14508 : selected 9 ⟨374177, by decide⟩
    (prefixPartial 12 27234) = some ⟨12, 2, 0, 374177, 27234, 2765, 65536⟩ := by
  decide +kernel

theorem context_12_27234_374177 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27234 ⟨374177, by decide⟩ :=
  accepted_of_selected 12 27234 ⟨374177, by decide⟩ ⟨12, 2, 0, 374177, 27234, 2765, 65536⟩
    (by decide) selected_cut_14508

theorem selected_cut_14509 : selected 9 ⟨374230, by decide⟩
    (prefixPartial 12 27235) = some ⟨12, 2, 0, 374230, 27235, 3937, 65536⟩ := by
  decide +kernel

theorem context_12_27235_374230 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27235 ⟨374230, by decide⟩ :=
  accepted_of_selected 12 27235 ⟨374230, by decide⟩ ⟨12, 2, 0, 374230, 27235, 3937, 65536⟩
    (by decide) selected_cut_14509

theorem unmarked_context_11_6808_374231 : frontier 10 ⟨374231, by decide⟩
    (prefixCache 11 6808) (prefixPartial 11 6808) = false := by
  decide +kernel

theorem node_context_11_6808_374231 : EJMOriginalGlobalDAGData.nodes 10 ⟨374231, by decide⟩ =
    .split (coordinate 11) (![⟨374075, by decide⟩,⟨374140, by decide⟩,⟨374177, by decide⟩,⟨374230, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6808_374231 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6808 ⟨374231, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6808
    ⟨374231, by decide⟩ (by decide) (![⟨374075, by decide⟩,⟨374140, by decide⟩,⟨374177, by decide⟩,⟨374230, by decide⟩]) unmarked_context_11_6808_374231 node_context_11_6808_374231
  intro a
  fin_cases a
  · exact context_12_27232_374075
  · exact context_12_27233_374140
  · exact context_12_27234_374177
  · exact context_12_27235_374230

theorem selected_cut_14510 : selected 9 ⟨374271, by decide⟩
    (prefixPartial 12 27236) = some ⟨12, 2, 0, 374271, 27236, 3433, 65536⟩ := by
  decide +kernel

theorem context_12_27236_374271 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27236 ⟨374271, by decide⟩ :=
  accepted_of_selected 12 27236 ⟨374271, by decide⟩ ⟨12, 2, 0, 374271, 27236, 3433, 65536⟩
    (by decide) selected_cut_14510

theorem selected_cut_14511 : selected 9 ⟨289098, by decide⟩
    (prefixPartial 12 27237) = some ⟨12, 1, 0, 289098, 27237, 1, 65536⟩ := by
  decide +kernel

theorem context_12_27237_289098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27237 ⟨289098, by decide⟩ :=
  accepted_of_selected 12 27237 ⟨289098, by decide⟩ ⟨12, 1, 0, 289098, 27237, 1, 65536⟩
    (by decide) selected_cut_14511

theorem selected_cut_14512 : selected 9 ⟨374307, by decide⟩
    (prefixPartial 12 27238) = some ⟨12, 2, 0, 374307, 27238, 3049, 65536⟩ := by
  decide +kernel

theorem context_12_27238_374307 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27238 ⟨374307, by decide⟩ :=
  accepted_of_selected 12 27238 ⟨374307, by decide⟩ ⟨12, 2, 0, 374307, 27238, 3049, 65536⟩
    (by decide) selected_cut_14512

theorem selected_cut_14513 : selected 9 ⟨374350, by decide⟩
    (prefixPartial 12 27239) = some ⟨12, 2, 0, 374350, 27239, 3949, 65536⟩ := by
  decide +kernel

theorem context_12_27239_374350 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27239 ⟨374350, by decide⟩ :=
  accepted_of_selected 12 27239 ⟨374350, by decide⟩ ⟨12, 2, 0, 374350, 27239, 3949, 65536⟩
    (by decide) selected_cut_14513

theorem unmarked_context_11_6809_374351 : frontier 10 ⟨374351, by decide⟩
    (prefixCache 11 6809) (prefixPartial 11 6809) = false := by
  decide +kernel

theorem node_context_11_6809_374351 : EJMOriginalGlobalDAGData.nodes 10 ⟨374351, by decide⟩ =
    .split (coordinate 11) (![⟨374271, by decide⟩,⟨289098, by decide⟩,⟨374307, by decide⟩,⟨374350, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6809_374351 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6809 ⟨374351, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6809
    ⟨374351, by decide⟩ (by decide) (![⟨374271, by decide⟩,⟨289098, by decide⟩,⟨374307, by decide⟩,⟨374350, by decide⟩]) unmarked_context_11_6809_374351 node_context_11_6809_374351
  intro a
  fin_cases a
  · exact context_12_27236_374271
  · exact context_12_27237_289098
  · exact context_12_27238_374307
  · exact context_12_27239_374350

theorem selected_cut_14514 : selected 9 ⟨374397, by decide⟩
    (prefixPartial 12 27240) = some ⟨12, 2, 0, 374397, 27240, 3961, 65536⟩ := by
  decide +kernel

theorem context_12_27240_374397 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27240 ⟨374397, by decide⟩ :=
  accepted_of_selected 12 27240 ⟨374397, by decide⟩ ⟨12, 2, 0, 374397, 27240, 3961, 65536⟩
    (by decide) selected_cut_14514

theorem selected_cut_14515 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 108964) = some ⟨13, 1, 0, 3444, 108964, 1, 16384⟩ := by
  decide +kernel

theorem context_13_108964_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108964 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 108964 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 108964, 1, 16384⟩
    (by decide) selected_cut_14515

theorem selected_cut_14516 : selected 8 ⟨374423, by decide⟩
    (prefixPartial 13 108965) = some ⟨13, 2, 0, 374423, 108965, 1725, 16384⟩ := by
  decide +kernel

theorem context_13_108965_374423 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108965 ⟨374423, by decide⟩ :=
  accepted_of_selected 13 108965 ⟨374423, by decide⟩ ⟨13, 2, 0, 374423, 108965, 1725, 16384⟩
    (by decide) selected_cut_14516

theorem selected_cut_14517 : selected 8 ⟨374452, by decide⟩
    (prefixPartial 13 108966) = some ⟨13, 2, 0, 374452, 108966, 2405, 16384⟩ := by
  decide +kernel

theorem context_13_108966_374452 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108966 ⟨374452, by decide⟩ :=
  accepted_of_selected 13 108966 ⟨374452, by decide⟩ ⟨13, 2, 0, 374452, 108966, 2405, 16384⟩
    (by decide) selected_cut_14517

theorem selected_cut_14518 : selected 8 ⟨374471, by decide⟩
    (prefixPartial 13 108967) = some ⟨13, 2, 0, 374471, 108967, 1433, 16384⟩ := by
  decide +kernel

theorem context_13_108967_374471 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108967 ⟨374471, by decide⟩ :=
  accepted_of_selected 13 108967 ⟨374471, by decide⟩ ⟨13, 2, 0, 374471, 108967, 1433, 16384⟩
    (by decide) selected_cut_14518

theorem unmarked_context_12_27241_374472 : frontier 9 ⟨374472, by decide⟩
    (prefixCache 12 27241) (prefixPartial 12 27241) = false := by
  decide +kernel

theorem node_context_12_27241_374472 : EJMOriginalGlobalDAGData.nodes 9 ⟨374472, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨374423, by decide⟩,⟨374452, by decide⟩,⟨374471, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27241_374472 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27241 ⟨374472, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27241
    ⟨374472, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨374423, by decide⟩,⟨374452, by decide⟩,⟨374471, by decide⟩]) unmarked_context_12_27241_374472 node_context_12_27241_374472
  intro a
  fin_cases a
  · exact context_13_108964_3444
  · exact context_13_108965_374423
  · exact context_13_108966_374452
  · exact context_13_108967_374471

theorem selected_cut_14519 : selected 9 ⟨242157, by decide⟩
    (prefixPartial 12 27242) = some ⟨12, 1, 0, 242157, 27242, 1, 65536⟩ := by
  decide +kernel

theorem context_12_27242_242157 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27242 ⟨242157, by decide⟩ :=
  accepted_of_selected 12 27242 ⟨242157, by decide⟩ ⟨12, 1, 0, 242157, 27242, 1, 65536⟩
    (by decide) selected_cut_14519

theorem selected_cut_14520 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 108972) = some ⟨13, 1, 0, 3444, 108972, 1, 16384⟩ := by
  decide +kernel

theorem context_13_108972_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108972 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 108972 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 108972, 1, 16384⟩
    (by decide) selected_cut_14520

theorem selected_cut_14521 : selected 8 ⟨374494, by decide⟩
    (prefixPartial 13 108973) = some ⟨13, 2, 0, 374494, 108973, 1209, 16384⟩ := by
  decide +kernel

theorem context_13_108973_374494 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108973 ⟨374494, by decide⟩ :=
  accepted_of_selected 13 108973 ⟨374494, by decide⟩ ⟨13, 2, 0, 374494, 108973, 1209, 16384⟩
    (by decide) selected_cut_14521

theorem selected_cut_14522 : selected 8 ⟨374517, by decide⟩
    (prefixPartial 13 108974) = some ⟨13, 2, 0, 374517, 108974, 1961, 16384⟩ := by
  decide +kernel

theorem context_13_108974_374517 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108974 ⟨374517, by decide⟩ :=
  accepted_of_selected 13 108974 ⟨374517, by decide⟩ ⟨13, 2, 0, 374517, 108974, 1961, 16384⟩
    (by decide) selected_cut_14522

theorem selected_cut_14523 : selected 8 ⟨374524, by decide⟩
    (prefixPartial 13 108975) = some ⟨13, 2, 0, 374524, 108975, 1133, 16384⟩ := by
  decide +kernel

theorem context_13_108975_374524 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108975 ⟨374524, by decide⟩ :=
  accepted_of_selected 13 108975 ⟨374524, by decide⟩ ⟨13, 2, 0, 374524, 108975, 1133, 16384⟩
    (by decide) selected_cut_14523

theorem unmarked_context_12_27243_374525 : frontier 9 ⟨374525, by decide⟩
    (prefixCache 12 27243) (prefixPartial 12 27243) = false := by
  decide +kernel

theorem node_context_12_27243_374525 : EJMOriginalGlobalDAGData.nodes 9 ⟨374525, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨374494, by decide⟩,⟨374517, by decide⟩,⟨374524, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27243_374525 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27243 ⟨374525, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27243
    ⟨374525, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨374494, by decide⟩,⟨374517, by decide⟩,⟨374524, by decide⟩]) unmarked_context_12_27243_374525 node_context_12_27243_374525
  intro a
  fin_cases a
  · exact context_13_108972_3444
  · exact context_13_108973_374494
  · exact context_13_108974_374517
  · exact context_13_108975_374524

theorem unmarked_context_11_6810_374526 : frontier 10 ⟨374526, by decide⟩
    (prefixCache 11 6810) (prefixPartial 11 6810) = false := by
  decide +kernel

theorem node_context_11_6810_374526 : EJMOriginalGlobalDAGData.nodes 10 ⟨374526, by decide⟩ =
    .split (coordinate 11) (![⟨374397, by decide⟩,⟨374472, by decide⟩,⟨242157, by decide⟩,⟨374525, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6810_374526 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6810 ⟨374526, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6810
    ⟨374526, by decide⟩ (by decide) (![⟨374397, by decide⟩,⟨374472, by decide⟩,⟨242157, by decide⟩,⟨374525, by decide⟩]) unmarked_context_11_6810_374526 node_context_11_6810_374526
  intro a
  fin_cases a
  · exact context_12_27240_374397
  · exact context_12_27241_374472
  · exact context_12_27242_242157
  · exact context_12_27243_374525

theorem selected_cut_14524 : selected 9 ⟨374565, by decide⟩
    (prefixPartial 12 27244) = some ⟨12, 2, 0, 374565, 27244, 3261, 65536⟩ := by
  decide +kernel

theorem context_12_27244_374565 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27244 ⟨374565, by decide⟩ :=
  accepted_of_selected 12 27244 ⟨374565, by decide⟩ ⟨12, 2, 0, 374565, 27244, 3261, 65536⟩
    (by decide) selected_cut_14524

theorem selected_cut_14525 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 108980) = some ⟨13, 1, 0, 3444, 108980, 1, 16384⟩ := by
  decide +kernel

theorem context_13_108980_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108980 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 108980 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 108980, 1, 16384⟩
    (by decide) selected_cut_14525

theorem selected_cut_14526 : selected 8 ⟨374580, by decide⟩
    (prefixPartial 13 108981) = some ⟨13, 2, 0, 374580, 108981, 1153, 16384⟩ := by
  decide +kernel

theorem context_13_108981_374580 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108981 ⟨374580, by decide⟩ :=
  accepted_of_selected 13 108981 ⟨374580, by decide⟩ ⟨13, 2, 0, 374580, 108981, 1153, 16384⟩
    (by decide) selected_cut_14526

theorem selected_cut_14527 : selected 8 ⟨374602, by decide⟩
    (prefixPartial 13 108982) = some ⟨13, 2, 0, 374602, 108982, 2057, 16384⟩ := by
  decide +kernel

theorem context_13_108982_374602 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108982 ⟨374602, by decide⟩ :=
  accepted_of_selected 13 108982 ⟨374602, by decide⟩ ⟨13, 2, 0, 374602, 108982, 2057, 16384⟩
    (by decide) selected_cut_14527

theorem selected_cut_14528 : selected 8 ⟨374616, by decide⟩
    (prefixPartial 13 108983) = some ⟨13, 2, 0, 374616, 108983, 1185, 16384⟩ := by
  decide +kernel

theorem context_13_108983_374616 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108983 ⟨374616, by decide⟩ :=
  accepted_of_selected 13 108983 ⟨374616, by decide⟩ ⟨13, 2, 0, 374616, 108983, 1185, 16384⟩
    (by decide) selected_cut_14528

theorem unmarked_context_12_27245_374617 : frontier 9 ⟨374617, by decide⟩
    (prefixCache 12 27245) (prefixPartial 12 27245) = false := by
  decide +kernel

theorem node_context_12_27245_374617 : EJMOriginalGlobalDAGData.nodes 9 ⟨374617, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨374580, by decide⟩,⟨374602, by decide⟩,⟨374616, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27245_374617 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27245 ⟨374617, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27245
    ⟨374617, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨374580, by decide⟩,⟨374602, by decide⟩,⟨374616, by decide⟩]) unmarked_context_12_27245_374617 node_context_12_27245_374617
  intro a
  fin_cases a
  · exact context_13_108980_3444
  · exact context_13_108981_374580
  · exact context_13_108982_374602
  · exact context_13_108983_374616

theorem selected_cut_14529 : selected 9 ⟨374650, by decide⟩
    (prefixPartial 12 27246) = some ⟨12, 2, 0, 374650, 27246, 2461, 65536⟩ := by
  decide +kernel

theorem context_12_27246_374650 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27246 ⟨374650, by decide⟩ :=
  accepted_of_selected 12 27246 ⟨374650, by decide⟩ ⟨12, 2, 0, 374650, 27246, 2461, 65536⟩
    (by decide) selected_cut_14529

theorem selected_cut_14530 : selected 9 ⟨374691, by decide⟩
    (prefixPartial 12 27247) = some ⟨12, 2, 0, 374691, 27247, 3333, 65536⟩ := by
  decide +kernel

theorem context_12_27247_374691 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27247 ⟨374691, by decide⟩ :=
  accepted_of_selected 12 27247 ⟨374691, by decide⟩ ⟨12, 2, 0, 374691, 27247, 3333, 65536⟩
    (by decide) selected_cut_14530

theorem unmarked_context_11_6811_374692 : frontier 10 ⟨374692, by decide⟩
    (prefixCache 11 6811) (prefixPartial 11 6811) = false := by
  decide +kernel

theorem node_context_11_6811_374692 : EJMOriginalGlobalDAGData.nodes 10 ⟨374692, by decide⟩ =
    .split (coordinate 11) (![⟨374565, by decide⟩,⟨374617, by decide⟩,⟨374650, by decide⟩,⟨374691, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6811_374692 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6811 ⟨374692, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6811
    ⟨374692, by decide⟩ (by decide) (![⟨374565, by decide⟩,⟨374617, by decide⟩,⟨374650, by decide⟩,⟨374691, by decide⟩]) unmarked_context_11_6811_374692 node_context_11_6811_374692
  intro a
  fin_cases a
  · exact context_12_27244_374565
  · exact context_12_27245_374617
  · exact context_12_27246_374650
  · exact context_12_27247_374691

theorem unmarked_context_10_1702_374693 : frontier 11 ⟨374693, by decide⟩
    (prefixCache 10 1702) (prefixPartial 10 1702) = false := by
  decide +kernel

theorem node_context_10_1702_374693 : EJMOriginalGlobalDAGData.nodes 11 ⟨374693, by decide⟩ =
    .split (coordinate 10) (![⟨374231, by decide⟩,⟨374351, by decide⟩,⟨374526, by decide⟩,⟨374692, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1702_374693 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1702 ⟨374693, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1702
    ⟨374693, by decide⟩ (by decide) (![⟨374231, by decide⟩,⟨374351, by decide⟩,⟨374526, by decide⟩,⟨374692, by decide⟩]) unmarked_context_10_1702_374693 node_context_10_1702_374693
  intro a
  fin_cases a
  · exact context_11_6808_374231
  · exact context_11_6809_374351
  · exact context_11_6810_374526
  · exact context_11_6811_374692

theorem selected_cut_14531 : selected 9 ⟨374726, by decide⟩
    (prefixPartial 12 27248) = some ⟨12, 2, 0, 374726, 27248, 2993, 65536⟩ := by
  decide +kernel

theorem context_12_27248_374726 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27248 ⟨374726, by decide⟩ :=
  accepted_of_selected 12 27248 ⟨374726, by decide⟩ ⟨12, 2, 0, 374726, 27248, 2993, 65536⟩
    (by decide) selected_cut_14531

theorem selected_cut_14532 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 108996) = some ⟨13, 1, 0, 3444, 108996, 1, 16384⟩ := by
  decide +kernel

theorem context_13_108996_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108996 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 108996 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 108996, 1, 16384⟩
    (by decide) selected_cut_14532

theorem selected_cut_14533 : selected 8 ⟨374740, by decide⟩
    (prefixPartial 13 108997) = some ⟨13, 2, 0, 374740, 108997, 1013, 16384⟩ := by
  decide +kernel

theorem context_13_108997_374740 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108997 ⟨374740, by decide⟩ :=
  accepted_of_selected 13 108997 ⟨374740, by decide⟩ ⟨13, 2, 0, 374740, 108997, 1013, 16384⟩
    (by decide) selected_cut_14533

theorem selected_cut_14534 : selected 8 ⟨374763, by decide⟩
    (prefixPartial 13 108998) = some ⟨13, 2, 0, 374763, 108998, 2025, 16384⟩ := by
  decide +kernel

theorem context_13_108998_374763 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108998 ⟨374763, by decide⟩ :=
  accepted_of_selected 13 108998 ⟨374763, by decide⟩ ⟨13, 2, 0, 374763, 108998, 2025, 16384⟩
    (by decide) selected_cut_14534

theorem selected_cut_14535 : selected 8 ⟨374774, by decide⟩
    (prefixPartial 13 108999) = some ⟨13, 2, 0, 374774, 108999, 1229, 16384⟩ := by
  decide +kernel

theorem context_13_108999_374774 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108999 ⟨374774, by decide⟩ :=
  accepted_of_selected 13 108999 ⟨374774, by decide⟩ ⟨13, 2, 0, 374774, 108999, 1229, 16384⟩
    (by decide) selected_cut_14535

theorem unmarked_context_12_27249_374775 : frontier 9 ⟨374775, by decide⟩
    (prefixCache 12 27249) (prefixPartial 12 27249) = false := by
  decide +kernel

theorem node_context_12_27249_374775 : EJMOriginalGlobalDAGData.nodes 9 ⟨374775, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨374740, by decide⟩,⟨374763, by decide⟩,⟨374774, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27249_374775 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27249 ⟨374775, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27249
    ⟨374775, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨374740, by decide⟩,⟨374763, by decide⟩,⟨374774, by decide⟩]) unmarked_context_12_27249_374775 node_context_12_27249_374775
  intro a
  fin_cases a
  · exact context_13_108996_3444
  · exact context_13_108997_374740
  · exact context_13_108998_374763
  · exact context_13_108999_374774

theorem selected_cut_14536 : selected 9 ⟨374810, by decide⟩
    (prefixPartial 12 27250) = some ⟨12, 2, 0, 374810, 27250, 2937, 65536⟩ := by
  decide +kernel

theorem context_12_27250_374810 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27250 ⟨374810, by decide⟩ :=
  accepted_of_selected 12 27250 ⟨374810, by decide⟩ ⟨12, 2, 0, 374810, 27250, 2937, 65536⟩
    (by decide) selected_cut_14536

theorem selected_cut_14537 : selected 9 ⟨374847, by decide⟩
    (prefixPartial 12 27251) = some ⟨12, 2, 0, 374847, 27251, 3585, 65536⟩ := by
  decide +kernel

theorem context_12_27251_374847 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27251 ⟨374847, by decide⟩ :=
  accepted_of_selected 12 27251 ⟨374847, by decide⟩ ⟨12, 2, 0, 374847, 27251, 3585, 65536⟩
    (by decide) selected_cut_14537

theorem unmarked_context_11_6812_374848 : frontier 10 ⟨374848, by decide⟩
    (prefixCache 11 6812) (prefixPartial 11 6812) = false := by
  decide +kernel

theorem node_context_11_6812_374848 : EJMOriginalGlobalDAGData.nodes 10 ⟨374848, by decide⟩ =
    .split (coordinate 11) (![⟨374726, by decide⟩,⟨374775, by decide⟩,⟨374810, by decide⟩,⟨374847, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6812_374848 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6812 ⟨374848, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6812
    ⟨374848, by decide⟩ (by decide) (![⟨374726, by decide⟩,⟨374775, by decide⟩,⟨374810, by decide⟩,⟨374847, by decide⟩]) unmarked_context_11_6812_374848 node_context_11_6812_374848
  intro a
  fin_cases a
  · exact context_12_27248_374726
  · exact context_12_27249_374775
  · exact context_12_27250_374810
  · exact context_12_27251_374847

theorem selected_cut_14538 : selected 9 ⟨374879, by decide⟩
    (prefixPartial 12 27252) = some ⟨12, 2, 0, 374879, 27252, 2917, 65536⟩ := by
  decide +kernel

theorem context_12_27252_374879 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27252 ⟨374879, by decide⟩ :=
  accepted_of_selected 12 27252 ⟨374879, by decide⟩ ⟨12, 2, 0, 374879, 27252, 2917, 65536⟩
    (by decide) selected_cut_14538

theorem selected_cut_14539 : selected 9 ⟨374921, by decide⟩
    (prefixPartial 12 27253) = some ⟨12, 2, 0, 374921, 27253, 3925, 65536⟩ := by
  decide +kernel

theorem context_12_27253_374921 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27253 ⟨374921, by decide⟩ :=
  accepted_of_selected 12 27253 ⟨374921, by decide⟩ ⟨12, 2, 0, 374921, 27253, 3925, 65536⟩
    (by decide) selected_cut_14539

theorem selected_cut_14540 : selected 9 ⟨374959, by decide⟩
    (prefixPartial 12 27254) = some ⟨12, 2, 0, 374959, 27254, 2901, 65536⟩ := by
  decide +kernel

theorem context_12_27254_374959 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27254 ⟨374959, by decide⟩ :=
  accepted_of_selected 12 27254 ⟨374959, by decide⟩ ⟨12, 2, 0, 374959, 27254, 2901, 65536⟩
    (by decide) selected_cut_14540

theorem selected_cut_14541 : selected 9 ⟨374995, by decide⟩
    (prefixPartial 12 27255) = some ⟨12, 2, 0, 374995, 27255, 3433, 65536⟩ := by
  decide +kernel

theorem context_12_27255_374995 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27255 ⟨374995, by decide⟩ :=
  accepted_of_selected 12 27255 ⟨374995, by decide⟩ ⟨12, 2, 0, 374995, 27255, 3433, 65536⟩
    (by decide) selected_cut_14541

theorem unmarked_context_11_6813_374996 : frontier 10 ⟨374996, by decide⟩
    (prefixCache 11 6813) (prefixPartial 11 6813) = false := by
  decide +kernel

theorem node_context_11_6813_374996 : EJMOriginalGlobalDAGData.nodes 10 ⟨374996, by decide⟩ =
    .split (coordinate 11) (![⟨374879, by decide⟩,⟨374921, by decide⟩,⟨374959, by decide⟩,⟨374995, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6813_374996 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6813 ⟨374996, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6813
    ⟨374996, by decide⟩ (by decide) (![⟨374879, by decide⟩,⟨374921, by decide⟩,⟨374959, by decide⟩,⟨374995, by decide⟩]) unmarked_context_11_6813_374996 node_context_11_6813_374996
  intro a
  fin_cases a
  · exact context_12_27252_374879
  · exact context_12_27253_374921
  · exact context_12_27254_374959
  · exact context_12_27255_374995

theorem selected_cut_14542 : selected 9 ⟨375026, by decide⟩
    (prefixPartial 12 27256) = some ⟨12, 2, 0, 375026, 27256, 2441, 65536⟩ := by
  decide +kernel

theorem context_12_27256_375026 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27256 ⟨375026, by decide⟩ :=
  accepted_of_selected 12 27256 ⟨375026, by decide⟩ ⟨12, 2, 0, 375026, 27256, 2441, 65536⟩
    (by decide) selected_cut_14542

theorem selected_cut_14543 : selected 9 ⟨375061, by decide⟩
    (prefixPartial 12 27257) = some ⟨12, 2, 0, 375061, 27257, 3537, 65536⟩ := by
  decide +kernel

theorem context_12_27257_375061 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27257 ⟨375061, by decide⟩ :=
  accepted_of_selected 12 27257 ⟨375061, by decide⟩ ⟨12, 2, 0, 375061, 27257, 3537, 65536⟩
    (by decide) selected_cut_14543

theorem selected_cut_14544 : selected 9 ⟨375121, by decide⟩
    (prefixPartial 12 27258) = some ⟨12, 2, 0, 375121, 27258, 4093, 65536⟩ := by
  decide +kernel

theorem context_12_27258_375121 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27258 ⟨375121, by decide⟩ :=
  accepted_of_selected 12 27258 ⟨375121, by decide⟩ ⟨12, 2, 0, 375121, 27258, 4093, 65536⟩
    (by decide) selected_cut_14544

theorem selected_cut_14545 : selected 9 ⟨375159, by decide⟩
    (prefixPartial 12 27259) = some ⟨12, 2, 0, 375159, 27259, 2861, 65536⟩ := by
  decide +kernel

theorem context_12_27259_375159 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27259 ⟨375159, by decide⟩ :=
  accepted_of_selected 12 27259 ⟨375159, by decide⟩ ⟨12, 2, 0, 375159, 27259, 2861, 65536⟩
    (by decide) selected_cut_14545

theorem unmarked_context_11_6814_375160 : frontier 10 ⟨375160, by decide⟩
    (prefixCache 11 6814) (prefixPartial 11 6814) = false := by
  decide +kernel

theorem node_context_11_6814_375160 : EJMOriginalGlobalDAGData.nodes 10 ⟨375160, by decide⟩ =
    .split (coordinate 11) (![⟨375026, by decide⟩,⟨375061, by decide⟩,⟨375121, by decide⟩,⟨375159, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6814_375160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6814 ⟨375160, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6814
    ⟨375160, by decide⟩ (by decide) (![⟨375026, by decide⟩,⟨375061, by decide⟩,⟨375121, by decide⟩,⟨375159, by decide⟩]) unmarked_context_11_6814_375160 node_context_11_6814_375160
  intro a
  fin_cases a
  · exact context_12_27256_375026
  · exact context_12_27257_375061
  · exact context_12_27258_375121
  · exact context_12_27259_375159

theorem selected_cut_14546 : selected 9 ⟨375190, by decide⟩
    (prefixPartial 12 27260) = some ⟨12, 2, 0, 375190, 27260, 2509, 65536⟩ := by
  decide +kernel

theorem context_12_27260_375190 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27260 ⟨375190, by decide⟩ :=
  accepted_of_selected 12 27260 ⟨375190, by decide⟩ ⟨12, 2, 0, 375190, 27260, 2509, 65536⟩
    (by decide) selected_cut_14546

theorem selected_cut_14547 : selected 9 ⟨375230, by decide⟩
    (prefixPartial 12 27261) = some ⟨12, 2, 0, 375230, 27261, 3369, 65536⟩ := by
  decide +kernel

theorem context_12_27261_375230 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27261 ⟨375230, by decide⟩ :=
  accepted_of_selected 12 27261 ⟨375230, by decide⟩ ⟨12, 2, 0, 375230, 27261, 3369, 65536⟩
    (by decide) selected_cut_14547

theorem selected_cut_14548 : selected 9 ⟨375259, by decide⟩
    (prefixPartial 12 27262) = some ⟨12, 2, 0, 375259, 27262, 2301, 65536⟩ := by
  decide +kernel

theorem context_12_27262_375259 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27262 ⟨375259, by decide⟩ :=
  accepted_of_selected 12 27262 ⟨375259, by decide⟩ ⟨12, 2, 0, 375259, 27262, 2301, 65536⟩
    (by decide) selected_cut_14548

theorem selected_cut_14549 : selected 9 ⟨375294, by decide⟩
    (prefixPartial 12 27263) = some ⟨12, 2, 0, 375294, 27263, 2745, 65536⟩ := by
  decide +kernel

theorem context_12_27263_375294 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27263 ⟨375294, by decide⟩ :=
  accepted_of_selected 12 27263 ⟨375294, by decide⟩ ⟨12, 2, 0, 375294, 27263, 2745, 65536⟩
    (by decide) selected_cut_14549

theorem unmarked_context_11_6815_375295 : frontier 10 ⟨375295, by decide⟩
    (prefixCache 11 6815) (prefixPartial 11 6815) = false := by
  decide +kernel

theorem node_context_11_6815_375295 : EJMOriginalGlobalDAGData.nodes 10 ⟨375295, by decide⟩ =
    .split (coordinate 11) (![⟨375190, by decide⟩,⟨375230, by decide⟩,⟨375259, by decide⟩,⟨375294, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6815_375295 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6815 ⟨375295, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6815
    ⟨375295, by decide⟩ (by decide) (![⟨375190, by decide⟩,⟨375230, by decide⟩,⟨375259, by decide⟩,⟨375294, by decide⟩]) unmarked_context_11_6815_375295 node_context_11_6815_375295
  intro a
  fin_cases a
  · exact context_12_27260_375190
  · exact context_12_27261_375230
  · exact context_12_27262_375259
  · exact context_12_27263_375294

theorem unmarked_context_10_1703_375296 : frontier 11 ⟨375296, by decide⟩
    (prefixCache 10 1703) (prefixPartial 10 1703) = false := by
  decide +kernel

theorem node_context_10_1703_375296 : EJMOriginalGlobalDAGData.nodes 11 ⟨375296, by decide⟩ =
    .split (coordinate 10) (![⟨374848, by decide⟩,⟨374996, by decide⟩,⟨375160, by decide⟩,⟨375295, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1703_375296 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1703 ⟨375296, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1703
    ⟨375296, by decide⟩ (by decide) (![⟨374848, by decide⟩,⟨374996, by decide⟩,⟨375160, by decide⟩,⟨375295, by decide⟩]) unmarked_context_10_1703_375296 node_context_10_1703_375296
  intro a
  fin_cases a
  · exact context_11_6812_374848
  · exact context_11_6813_374996
  · exact context_11_6814_375160
  · exact context_11_6815_375295

theorem unmarked_context_9_425_375297 : frontier 12 ⟨375297, by decide⟩
    (prefixCache 9 425) (prefixPartial 9 425) = false := by
  decide +kernel

theorem node_context_9_425_375297 : EJMOriginalGlobalDAGData.nodes 12 ⟨375297, by decide⟩ =
    .split (coordinate 9) (![⟨373365, by decide⟩,⟨374040, by decide⟩,⟨374693, by decide⟩,⟨375296, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_425_375297 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 425 ⟨375297, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 425
    ⟨375297, by decide⟩ (by decide) (![⟨373365, by decide⟩,⟨374040, by decide⟩,⟨374693, by decide⟩,⟨375296, by decide⟩]) unmarked_context_9_425_375297 node_context_9_425_375297
  intro a
  fin_cases a
  · exact context_10_1700_373365
  · exact context_10_1701_374040
  · exact context_10_1702_374693
  · exact context_10_1703_375296

theorem selected_cut_14550 : selected 9 ⟨375324, by decide⟩
    (prefixPartial 12 27264) = some ⟨12, 2, 0, 375324, 27264, 2089, 65536⟩ := by
  decide +kernel

theorem context_12_27264_375324 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27264 ⟨375324, by decide⟩ :=
  accepted_of_selected 12 27264 ⟨375324, by decide⟩ ⟨12, 2, 0, 375324, 27264, 2089, 65536⟩
    (by decide) selected_cut_14550

theorem selected_cut_14551 : selected 9 ⟨375348, by decide⟩
    (prefixPartial 12 27265) = some ⟨12, 2, 0, 375348, 27265, 2017, 65536⟩ := by
  decide +kernel

theorem context_12_27265_375348 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27265 ⟨375348, by decide⟩ :=
  accepted_of_selected 12 27265 ⟨375348, by decide⟩ ⟨12, 2, 0, 375348, 27265, 2017, 65536⟩
    (by decide) selected_cut_14551

theorem selected_cut_14552 : selected 9 ⟨375372, by decide⟩
    (prefixPartial 12 27266) = some ⟨12, 2, 0, 375372, 27266, 1845, 65536⟩ := by
  decide +kernel

theorem context_12_27266_375372 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27266 ⟨375372, by decide⟩ :=
  accepted_of_selected 12 27266 ⟨375372, by decide⟩ ⟨12, 2, 0, 375372, 27266, 1845, 65536⟩
    (by decide) selected_cut_14552

theorem selected_cut_14553 : selected 9 ⟨375394, by decide⟩
    (prefixPartial 12 27267) = some ⟨12, 2, 0, 375394, 27267, 2089, 65536⟩ := by
  decide +kernel

theorem context_12_27267_375394 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27267 ⟨375394, by decide⟩ :=
  accepted_of_selected 12 27267 ⟨375394, by decide⟩ ⟨12, 2, 0, 375394, 27267, 2089, 65536⟩
    (by decide) selected_cut_14553

theorem unmarked_context_11_6816_375395 : frontier 10 ⟨375395, by decide⟩
    (prefixCache 11 6816) (prefixPartial 11 6816) = false := by
  decide +kernel

theorem node_context_11_6816_375395 : EJMOriginalGlobalDAGData.nodes 10 ⟨375395, by decide⟩ =
    .split (coordinate 11) (![⟨375324, by decide⟩,⟨375348, by decide⟩,⟨375372, by decide⟩,⟨375394, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6816_375395 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6816 ⟨375395, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6816
    ⟨375395, by decide⟩ (by decide) (![⟨375324, by decide⟩,⟨375348, by decide⟩,⟨375372, by decide⟩,⟨375394, by decide⟩]) unmarked_context_11_6816_375395 node_context_11_6816_375395
  intro a
  fin_cases a
  · exact context_12_27264_375324
  · exact context_12_27265_375348
  · exact context_12_27266_375372
  · exact context_12_27267_375394

theorem selected_cut_14554 : selected 9 ⟨375422, by decide⟩
    (prefixPartial 12 27268) = some ⟨12, 2, 0, 375422, 27268, 2245, 65536⟩ := by
  decide +kernel

theorem context_12_27268_375422 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27268 ⟨375422, by decide⟩ :=
  accepted_of_selected 12 27268 ⟨375422, by decide⟩ ⟨12, 2, 0, 375422, 27268, 2245, 65536⟩
    (by decide) selected_cut_14554

theorem selected_cut_14555 : selected 9 ⟨375448, by decide⟩
    (prefixPartial 12 27269) = some ⟨12, 2, 0, 375448, 27269, 2029, 65536⟩ := by
  decide +kernel

theorem context_12_27269_375448 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27269 ⟨375448, by decide⟩ :=
  accepted_of_selected 12 27269 ⟨375448, by decide⟩ ⟨12, 2, 0, 375448, 27269, 2029, 65536⟩
    (by decide) selected_cut_14555

theorem selected_cut_14556 : selected 9 ⟨375474, by decide⟩
    (prefixPartial 12 27270) = some ⟨12, 2, 0, 375474, 27270, 2033, 65536⟩ := by
  decide +kernel

theorem context_12_27270_375474 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27270 ⟨375474, by decide⟩ :=
  accepted_of_selected 12 27270 ⟨375474, by decide⟩ ⟨12, 2, 0, 375474, 27270, 2033, 65536⟩
    (by decide) selected_cut_14556

theorem selected_cut_14557 : selected 9 ⟨375497, by decide⟩
    (prefixPartial 12 27271) = some ⟨12, 2, 0, 375497, 27271, 2109, 65536⟩ := by
  decide +kernel

theorem context_12_27271_375497 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27271 ⟨375497, by decide⟩ :=
  accepted_of_selected 12 27271 ⟨375497, by decide⟩ ⟨12, 2, 0, 375497, 27271, 2109, 65536⟩
    (by decide) selected_cut_14557

theorem unmarked_context_11_6817_375498 : frontier 10 ⟨375498, by decide⟩
    (prefixCache 11 6817) (prefixPartial 11 6817) = false := by
  decide +kernel

theorem node_context_11_6817_375498 : EJMOriginalGlobalDAGData.nodes 10 ⟨375498, by decide⟩ =
    .split (coordinate 11) (![⟨375422, by decide⟩,⟨375448, by decide⟩,⟨375474, by decide⟩,⟨375497, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6817_375498 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6817 ⟨375498, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6817
    ⟨375498, by decide⟩ (by decide) (![⟨375422, by decide⟩,⟨375448, by decide⟩,⟨375474, by decide⟩,⟨375497, by decide⟩]) unmarked_context_11_6817_375498 node_context_11_6817_375498
  intro a
  fin_cases a
  · exact context_12_27268_375422
  · exact context_12_27269_375448
  · exact context_12_27270_375474
  · exact context_12_27271_375497

theorem selected_cut_14558 : selected 9 ⟨375525, by decide⟩
    (prefixPartial 12 27272) = some ⟨12, 2, 0, 375525, 27272, 1909, 65536⟩ := by
  decide +kernel

theorem context_12_27272_375525 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27272 ⟨375525, by decide⟩ :=
  accepted_of_selected 12 27272 ⟨375525, by decide⟩ ⟨12, 2, 0, 375525, 27272, 1909, 65536⟩
    (by decide) selected_cut_14558

theorem selected_cut_14559 : selected 9 ⟨375551, by decide⟩
    (prefixPartial 12 27273) = some ⟨12, 2, 0, 375551, 27273, 1753, 65536⟩ := by
  decide +kernel

theorem context_12_27273_375551 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27273 ⟨375551, by decide⟩ :=
  accepted_of_selected 12 27273 ⟨375551, by decide⟩ ⟨12, 2, 0, 375551, 27273, 1753, 65536⟩
    (by decide) selected_cut_14559

theorem selected_cut_14560 : selected 9 ⟨248765, by decide⟩
    (prefixPartial 12 27274) = some ⟨12, 1, 0, 248765, 27274, 1, 65536⟩ := by
  decide +kernel

theorem context_12_27274_248765 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27274 ⟨248765, by decide⟩ :=
  accepted_of_selected 12 27274 ⟨248765, by decide⟩ ⟨12, 1, 0, 248765, 27274, 1, 65536⟩
    (by decide) selected_cut_14560

theorem selected_cut_14561 : selected 9 ⟨375574, by decide⟩
    (prefixPartial 12 27275) = some ⟨12, 2, 0, 375574, 27275, 1729, 65536⟩ := by
  decide +kernel

theorem context_12_27275_375574 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27275 ⟨375574, by decide⟩ :=
  accepted_of_selected 12 27275 ⟨375574, by decide⟩ ⟨12, 2, 0, 375574, 27275, 1729, 65536⟩
    (by decide) selected_cut_14561

theorem unmarked_context_11_6818_375575 : frontier 10 ⟨375575, by decide⟩
    (prefixCache 11 6818) (prefixPartial 11 6818) = false := by
  decide +kernel

theorem node_context_11_6818_375575 : EJMOriginalGlobalDAGData.nodes 10 ⟨375575, by decide⟩ =
    .split (coordinate 11) (![⟨375525, by decide⟩,⟨375551, by decide⟩,⟨248765, by decide⟩,⟨375574, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6818_375575 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6818 ⟨375575, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6818
    ⟨375575, by decide⟩ (by decide) (![⟨375525, by decide⟩,⟨375551, by decide⟩,⟨248765, by decide⟩,⟨375574, by decide⟩]) unmarked_context_11_6818_375575 node_context_11_6818_375575
  intro a
  fin_cases a
  · exact context_12_27272_375525
  · exact context_12_27273_375551
  · exact context_12_27274_248765
  · exact context_12_27275_375574

theorem selected_cut_14562 : selected 9 ⟨375597, by decide⟩
    (prefixPartial 12 27276) = some ⟨12, 2, 0, 375597, 27276, 2233, 65536⟩ := by
  decide +kernel

theorem context_12_27276_375597 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27276 ⟨375597, by decide⟩ :=
  accepted_of_selected 12 27276 ⟨375597, by decide⟩ ⟨12, 2, 0, 375597, 27276, 2233, 65536⟩
    (by decide) selected_cut_14562

theorem selected_cut_14563 : selected 9 ⟨375622, by decide⟩
    (prefixPartial 12 27277) = some ⟨12, 2, 0, 375622, 27277, 1945, 65536⟩ := by
  decide +kernel

theorem context_12_27277_375622 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27277 ⟨375622, by decide⟩ :=
  accepted_of_selected 12 27277 ⟨375622, by decide⟩ ⟨12, 2, 0, 375622, 27277, 1945, 65536⟩
    (by decide) selected_cut_14563

theorem selected_cut_14564 : selected 9 ⟨375645, by decide⟩
    (prefixPartial 12 27278) = some ⟨12, 2, 0, 375645, 27278, 1833, 65536⟩ := by
  decide +kernel

theorem context_12_27278_375645 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27278 ⟨375645, by decide⟩ :=
  accepted_of_selected 12 27278 ⟨375645, by decide⟩ ⟨12, 2, 0, 375645, 27278, 1833, 65536⟩
    (by decide) selected_cut_14564

theorem selected_cut_14565 : selected 9 ⟨375666, by decide⟩
    (prefixPartial 12 27279) = some ⟨12, 2, 0, 375666, 27279, 1949, 65536⟩ := by
  decide +kernel

theorem context_12_27279_375666 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27279 ⟨375666, by decide⟩ :=
  accepted_of_selected 12 27279 ⟨375666, by decide⟩ ⟨12, 2, 0, 375666, 27279, 1949, 65536⟩
    (by decide) selected_cut_14565

theorem unmarked_context_11_6819_375667 : frontier 10 ⟨375667, by decide⟩
    (prefixCache 11 6819) (prefixPartial 11 6819) = false := by
  decide +kernel

theorem node_context_11_6819_375667 : EJMOriginalGlobalDAGData.nodes 10 ⟨375667, by decide⟩ =
    .split (coordinate 11) (![⟨375597, by decide⟩,⟨375622, by decide⟩,⟨375645, by decide⟩,⟨375666, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6819_375667 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6819 ⟨375667, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6819
    ⟨375667, by decide⟩ (by decide) (![⟨375597, by decide⟩,⟨375622, by decide⟩,⟨375645, by decide⟩,⟨375666, by decide⟩]) unmarked_context_11_6819_375667 node_context_11_6819_375667
  intro a
  fin_cases a
  · exact context_12_27276_375597
  · exact context_12_27277_375622
  · exact context_12_27278_375645
  · exact context_12_27279_375666

theorem unmarked_context_10_1704_375668 : frontier 11 ⟨375668, by decide⟩
    (prefixCache 10 1704) (prefixPartial 10 1704) = false := by
  decide +kernel

theorem node_context_10_1704_375668 : EJMOriginalGlobalDAGData.nodes 11 ⟨375668, by decide⟩ =
    .split (coordinate 10) (![⟨375395, by decide⟩,⟨375498, by decide⟩,⟨375575, by decide⟩,⟨375667, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1704_375668 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1704 ⟨375668, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1704
    ⟨375668, by decide⟩ (by decide) (![⟨375395, by decide⟩,⟨375498, by decide⟩,⟨375575, by decide⟩,⟨375667, by decide⟩]) unmarked_context_10_1704_375668 node_context_10_1704_375668
  intro a
  fin_cases a
  · exact context_11_6816_375395
  · exact context_11_6817_375498
  · exact context_11_6818_375575
  · exact context_11_6819_375667

theorem selected_cut_14566 : selected 9 ⟨375690, by decide⟩
    (prefixPartial 12 27280) = some ⟨12, 2, 0, 375690, 27280, 1909, 65536⟩ := by
  decide +kernel

theorem context_12_27280_375690 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27280 ⟨375690, by decide⟩ :=
  accepted_of_selected 12 27280 ⟨375690, by decide⟩ ⟨12, 2, 0, 375690, 27280, 1909, 65536⟩
    (by decide) selected_cut_14566

theorem selected_cut_14567 : selected 9 ⟨375716, by decide⟩
    (prefixPartial 12 27281) = some ⟨12, 2, 0, 375716, 27281, 2041, 65536⟩ := by
  decide +kernel

theorem context_12_27281_375716 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27281 ⟨375716, by decide⟩ :=
  accepted_of_selected 12 27281 ⟨375716, by decide⟩ ⟨12, 2, 0, 375716, 27281, 2041, 65536⟩
    (by decide) selected_cut_14567

theorem selected_cut_14568 : selected 9 ⟨375733, by decide⟩
    (prefixPartial 12 27282) = some ⟨12, 2, 0, 375733, 27282, 1877, 65536⟩ := by
  decide +kernel

theorem context_12_27282_375733 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27282 ⟨375733, by decide⟩ :=
  accepted_of_selected 12 27282 ⟨375733, by decide⟩ ⟨12, 2, 0, 375733, 27282, 1877, 65536⟩
    (by decide) selected_cut_14568

theorem selected_cut_14569 : selected 9 ⟨375760, by decide⟩
    (prefixPartial 12 27283) = some ⟨12, 2, 0, 375760, 27283, 2073, 65536⟩ := by
  decide +kernel

theorem context_12_27283_375760 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27283 ⟨375760, by decide⟩ :=
  accepted_of_selected 12 27283 ⟨375760, by decide⟩ ⟨12, 2, 0, 375760, 27283, 2073, 65536⟩
    (by decide) selected_cut_14569

theorem unmarked_context_11_6820_375761 : frontier 10 ⟨375761, by decide⟩
    (prefixCache 11 6820) (prefixPartial 11 6820) = false := by
  decide +kernel

theorem node_context_11_6820_375761 : EJMOriginalGlobalDAGData.nodes 10 ⟨375761, by decide⟩ =
    .split (coordinate 11) (![⟨375690, by decide⟩,⟨375716, by decide⟩,⟨375733, by decide⟩,⟨375760, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6820_375761 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6820 ⟨375761, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6820
    ⟨375761, by decide⟩ (by decide) (![⟨375690, by decide⟩,⟨375716, by decide⟩,⟨375733, by decide⟩,⟨375760, by decide⟩]) unmarked_context_11_6820_375761 node_context_11_6820_375761
  intro a
  fin_cases a
  · exact context_12_27280_375690
  · exact context_12_27281_375716
  · exact context_12_27282_375733
  · exact context_12_27283_375760

theorem selected_cut_14570 : selected 9 ⟨375787, by decide⟩
    (prefixPartial 12 27284) = some ⟨12, 2, 0, 375787, 27284, 2005, 65536⟩ := by
  decide +kernel

theorem context_12_27284_375787 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27284 ⟨375787, by decide⟩ :=
  accepted_of_selected 12 27284 ⟨375787, by decide⟩ ⟨12, 2, 0, 375787, 27284, 2005, 65536⟩
    (by decide) selected_cut_14570

theorem selected_cut_14571 : selected 9 ⟨375809, by decide⟩
    (prefixPartial 12 27285) = some ⟨12, 2, 0, 375809, 27285, 2053, 65536⟩ := by
  decide +kernel

theorem context_12_27285_375809 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27285 ⟨375809, by decide⟩ :=
  accepted_of_selected 12 27285 ⟨375809, by decide⟩ ⟨12, 2, 0, 375809, 27285, 2053, 65536⟩
    (by decide) selected_cut_14571

theorem selected_cut_14572 : selected 9 ⟨375831, by decide⟩
    (prefixPartial 12 27286) = some ⟨12, 2, 0, 375831, 27286, 1989, 65536⟩ := by
  decide +kernel

theorem context_12_27286_375831 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27286 ⟨375831, by decide⟩ :=
  accepted_of_selected 12 27286 ⟨375831, by decide⟩ ⟨12, 2, 0, 375831, 27286, 1989, 65536⟩
    (by decide) selected_cut_14572

theorem selected_cut_14573 : selected 9 ⟨375856, by decide⟩
    (prefixPartial 12 27287) = some ⟨12, 2, 0, 375856, 27287, 2077, 65536⟩ := by
  decide +kernel

theorem context_12_27287_375856 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27287 ⟨375856, by decide⟩ :=
  accepted_of_selected 12 27287 ⟨375856, by decide⟩ ⟨12, 2, 0, 375856, 27287, 2077, 65536⟩
    (by decide) selected_cut_14573

theorem unmarked_context_11_6821_375857 : frontier 10 ⟨375857, by decide⟩
    (prefixCache 11 6821) (prefixPartial 11 6821) = false := by
  decide +kernel

theorem node_context_11_6821_375857 : EJMOriginalGlobalDAGData.nodes 10 ⟨375857, by decide⟩ =
    .split (coordinate 11) (![⟨375787, by decide⟩,⟨375809, by decide⟩,⟨375831, by decide⟩,⟨375856, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6821_375857 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6821 ⟨375857, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6821
    ⟨375857, by decide⟩ (by decide) (![⟨375787, by decide⟩,⟨375809, by decide⟩,⟨375831, by decide⟩,⟨375856, by decide⟩]) unmarked_context_11_6821_375857 node_context_11_6821_375857
  intro a
  fin_cases a
  · exact context_12_27284_375787
  · exact context_12_27285_375809
  · exact context_12_27286_375831
  · exact context_12_27287_375856

theorem selected_cut_14574 : selected 9 ⟨375873, by decide⟩
    (prefixPartial 12 27288) = some ⟨12, 2, 0, 375873, 27288, 1513, 65536⟩ := by
  decide +kernel

theorem context_12_27288_375873 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27288 ⟨375873, by decide⟩ :=
  accepted_of_selected 12 27288 ⟨375873, by decide⟩ ⟨12, 2, 0, 375873, 27288, 1513, 65536⟩
    (by decide) selected_cut_14574

theorem selected_cut_14575 : selected 9 ⟨375891, by decide⟩
    (prefixPartial 12 27289) = some ⟨12, 2, 0, 375891, 27289, 1649, 65536⟩ := by
  decide +kernel

theorem context_12_27289_375891 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27289 ⟨375891, by decide⟩ :=
  accepted_of_selected 12 27289 ⟨375891, by decide⟩ ⟨12, 2, 0, 375891, 27289, 1649, 65536⟩
    (by decide) selected_cut_14575

theorem selected_cut_14576 : selected 9 ⟨290673, by decide⟩
    (prefixPartial 12 27290) = some ⟨12, 1, 0, 290673, 27290, 1, 65536⟩ := by
  decide +kernel

theorem context_12_27290_290673 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27290 ⟨290673, by decide⟩ :=
  accepted_of_selected 12 27290 ⟨290673, by decide⟩ ⟨12, 1, 0, 290673, 27290, 1, 65536⟩
    (by decide) selected_cut_14576

theorem selected_cut_14577 : selected 9 ⟨375910, by decide⟩
    (prefixPartial 12 27291) = some ⟨12, 2, 0, 375910, 27291, 1581, 65536⟩ := by
  decide +kernel

theorem context_12_27291_375910 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27291 ⟨375910, by decide⟩ :=
  accepted_of_selected 12 27291 ⟨375910, by decide⟩ ⟨12, 2, 0, 375910, 27291, 1581, 65536⟩
    (by decide) selected_cut_14577

theorem unmarked_context_11_6822_375911 : frontier 10 ⟨375911, by decide⟩
    (prefixCache 11 6822) (prefixPartial 11 6822) = false := by
  decide +kernel

theorem node_context_11_6822_375911 : EJMOriginalGlobalDAGData.nodes 10 ⟨375911, by decide⟩ =
    .split (coordinate 11) (![⟨375873, by decide⟩,⟨375891, by decide⟩,⟨290673, by decide⟩,⟨375910, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6822_375911 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6822 ⟨375911, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6822
    ⟨375911, by decide⟩ (by decide) (![⟨375873, by decide⟩,⟨375891, by decide⟩,⟨290673, by decide⟩,⟨375910, by decide⟩]) unmarked_context_11_6822_375911 node_context_11_6822_375911
  intro a
  fin_cases a
  · exact context_12_27288_375873
  · exact context_12_27289_375891
  · exact context_12_27290_290673
  · exact context_12_27291_375910

theorem selected_cut_14578 : selected 9 ⟨375932, by decide⟩
    (prefixPartial 12 27292) = some ⟨12, 2, 0, 375932, 27292, 1813, 65536⟩ := by
  decide +kernel

theorem context_12_27292_375932 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27292 ⟨375932, by decide⟩ :=
  accepted_of_selected 12 27292 ⟨375932, by decide⟩ ⟨12, 2, 0, 375932, 27292, 1813, 65536⟩
    (by decide) selected_cut_14578

theorem selected_cut_14579 : selected 9 ⟨375951, by decide⟩
    (prefixPartial 12 27293) = some ⟨12, 2, 0, 375951, 27293, 1689, 65536⟩ := by
  decide +kernel

theorem context_12_27293_375951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27293 ⟨375951, by decide⟩ :=
  accepted_of_selected 12 27293 ⟨375951, by decide⟩ ⟨12, 2, 0, 375951, 27293, 1689, 65536⟩
    (by decide) selected_cut_14579

theorem selected_cut_14580 : selected 9 ⟨375965, by decide⟩
    (prefixPartial 12 27294) = some ⟨12, 2, 0, 375965, 27294, 1573, 65536⟩ := by
  decide +kernel

theorem context_12_27294_375965 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27294 ⟨375965, by decide⟩ :=
  accepted_of_selected 12 27294 ⟨375965, by decide⟩ ⟨12, 2, 0, 375965, 27294, 1573, 65536⟩
    (by decide) selected_cut_14580

theorem selected_cut_14581 : selected 9 ⟨375985, by decide⟩
    (prefixPartial 12 27295) = some ⟨12, 2, 0, 375985, 27295, 1725, 65536⟩ := by
  decide +kernel

theorem context_12_27295_375985 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27295 ⟨375985, by decide⟩ :=
  accepted_of_selected 12 27295 ⟨375985, by decide⟩ ⟨12, 2, 0, 375985, 27295, 1725, 65536⟩
    (by decide) selected_cut_14581

theorem unmarked_context_11_6823_375986 : frontier 10 ⟨375986, by decide⟩
    (prefixCache 11 6823) (prefixPartial 11 6823) = false := by
  decide +kernel

theorem node_context_11_6823_375986 : EJMOriginalGlobalDAGData.nodes 10 ⟨375986, by decide⟩ =
    .split (coordinate 11) (![⟨375932, by decide⟩,⟨375951, by decide⟩,⟨375965, by decide⟩,⟨375985, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6823_375986 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6823 ⟨375986, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6823
    ⟨375986, by decide⟩ (by decide) (![⟨375932, by decide⟩,⟨375951, by decide⟩,⟨375965, by decide⟩,⟨375985, by decide⟩]) unmarked_context_11_6823_375986 node_context_11_6823_375986
  intro a
  fin_cases a
  · exact context_12_27292_375932
  · exact context_12_27293_375951
  · exact context_12_27294_375965
  · exact context_12_27295_375985

theorem unmarked_context_10_1705_375987 : frontier 11 ⟨375987, by decide⟩
    (prefixCache 10 1705) (prefixPartial 10 1705) = false := by
  decide +kernel

theorem node_context_10_1705_375987 : EJMOriginalGlobalDAGData.nodes 11 ⟨375987, by decide⟩ =
    .split (coordinate 10) (![⟨375761, by decide⟩,⟨375857, by decide⟩,⟨375911, by decide⟩,⟨375986, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1705_375987 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1705 ⟨375987, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1705
    ⟨375987, by decide⟩ (by decide) (![⟨375761, by decide⟩,⟨375857, by decide⟩,⟨375911, by decide⟩,⟨375986, by decide⟩]) unmarked_context_10_1705_375987 node_context_10_1705_375987
  intro a
  fin_cases a
  · exact context_11_6820_375761
  · exact context_11_6821_375857
  · exact context_11_6822_375911
  · exact context_11_6823_375986

theorem selected_cut_14582 : selected 9 ⟨376000, by decide⟩
    (prefixPartial 12 27296) = some ⟨12, 2, 0, 376000, 27296, 1369, 65536⟩ := by
  decide +kernel

theorem context_12_27296_376000 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27296 ⟨376000, by decide⟩ :=
  accepted_of_selected 12 27296 ⟨376000, by decide⟩ ⟨12, 2, 0, 376000, 27296, 1369, 65536⟩
    (by decide) selected_cut_14582

theorem selected_cut_14583 : selected 9 ⟨376018, by decide⟩
    (prefixPartial 12 27297) = some ⟨12, 2, 0, 376018, 27297, 1485, 65536⟩ := by
  decide +kernel

theorem context_12_27297_376018 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27297 ⟨376018, by decide⟩ :=
  accepted_of_selected 12 27297 ⟨376018, by decide⟩ ⟨12, 2, 0, 376018, 27297, 1485, 65536⟩
    (by decide) selected_cut_14583

theorem selected_cut_14584 : selected 9 ⟨376031, by decide⟩
    (prefixPartial 12 27298) = some ⟨12, 2, 0, 376031, 27298, 1193, 65536⟩ := by
  decide +kernel

theorem context_12_27298_376031 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27298 ⟨376031, by decide⟩ :=
  accepted_of_selected 12 27298 ⟨376031, by decide⟩ ⟨12, 2, 0, 376031, 27298, 1193, 65536⟩
    (by decide) selected_cut_14584

theorem selected_cut_14585 : selected 9 ⟨376048, by decide⟩
    (prefixPartial 12 27299) = some ⟨12, 2, 0, 376048, 27299, 1469, 65536⟩ := by
  decide +kernel

theorem context_12_27299_376048 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27299 ⟨376048, by decide⟩ :=
  accepted_of_selected 12 27299 ⟨376048, by decide⟩ ⟨12, 2, 0, 376048, 27299, 1469, 65536⟩
    (by decide) selected_cut_14585

theorem unmarked_context_11_6824_376049 : frontier 10 ⟨376049, by decide⟩
    (prefixCache 11 6824) (prefixPartial 11 6824) = false := by
  decide +kernel

theorem node_context_11_6824_376049 : EJMOriginalGlobalDAGData.nodes 10 ⟨376049, by decide⟩ =
    .split (coordinate 11) (![⟨376000, by decide⟩,⟨376018, by decide⟩,⟨376031, by decide⟩,⟨376048, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6824_376049 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6824 ⟨376049, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6824
    ⟨376049, by decide⟩ (by decide) (![⟨376000, by decide⟩,⟨376018, by decide⟩,⟨376031, by decide⟩,⟨376048, by decide⟩]) unmarked_context_11_6824_376049 node_context_11_6824_376049
  intro a
  fin_cases a
  · exact context_12_27296_376000
  · exact context_12_27297_376018
  · exact context_12_27298_376031
  · exact context_12_27299_376048

theorem selected_cut_14586 : selected 9 ⟨376070, by decide⟩
    (prefixPartial 12 27300) = some ⟨12, 2, 0, 376070, 27300, 1489, 65536⟩ := by
  decide +kernel

theorem context_12_27300_376070 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27300 ⟨376070, by decide⟩ :=
  accepted_of_selected 12 27300 ⟨376070, by decide⟩ ⟨12, 2, 0, 376070, 27300, 1489, 65536⟩
    (by decide) selected_cut_14586

theorem selected_cut_14587 : selected 9 ⟨376089, by decide⟩
    (prefixPartial 12 27301) = some ⟨12, 2, 0, 376089, 27301, 1501, 65536⟩ := by
  decide +kernel

theorem context_12_27301_376089 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27301 ⟨376089, by decide⟩ :=
  accepted_of_selected 12 27301 ⟨376089, by decide⟩ ⟨12, 2, 0, 376089, 27301, 1501, 65536⟩
    (by decide) selected_cut_14587

theorem selected_cut_14588 : selected 9 ⟨376100, by decide⟩
    (prefixPartial 12 27302) = some ⟨12, 2, 0, 376100, 27302, 1301, 65536⟩ := by
  decide +kernel

theorem context_12_27302_376100 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27302 ⟨376100, by decide⟩ :=
  accepted_of_selected 12 27302 ⟨376100, by decide⟩ ⟨12, 2, 0, 376100, 27302, 1301, 65536⟩
    (by decide) selected_cut_14588

theorem selected_cut_14589 : selected 9 ⟨376117, by decide⟩
    (prefixPartial 12 27303) = some ⟨12, 2, 0, 376117, 27303, 1557, 65536⟩ := by
  decide +kernel

theorem context_12_27303_376117 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27303 ⟨376117, by decide⟩ :=
  accepted_of_selected 12 27303 ⟨376117, by decide⟩ ⟨12, 2, 0, 376117, 27303, 1557, 65536⟩
    (by decide) selected_cut_14589

theorem unmarked_context_11_6825_376118 : frontier 10 ⟨376118, by decide⟩
    (prefixCache 11 6825) (prefixPartial 11 6825) = false := by
  decide +kernel

theorem node_context_11_6825_376118 : EJMOriginalGlobalDAGData.nodes 10 ⟨376118, by decide⟩ =
    .split (coordinate 11) (![⟨376070, by decide⟩,⟨376089, by decide⟩,⟨376100, by decide⟩,⟨376117, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6825_376118 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6825 ⟨376118, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6825
    ⟨376118, by decide⟩ (by decide) (![⟨376070, by decide⟩,⟨376089, by decide⟩,⟨376100, by decide⟩,⟨376117, by decide⟩]) unmarked_context_11_6825_376118 node_context_11_6825_376118
  intro a
  fin_cases a
  · exact context_12_27300_376070
  · exact context_12_27301_376089
  · exact context_12_27302_376100
  · exact context_12_27303_376117

theorem selected_cut_14590 : selected 10 ⟨356516, by decide⟩
    (prefixPartial 11 6826) = some ⟨11, 2, 0, 356516, 6826, 5, 262144⟩ := by
  decide +kernel

theorem context_11_6826_356516 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6826 ⟨356516, by decide⟩ :=
  accepted_of_selected 11 6826 ⟨356516, by decide⟩ ⟨11, 2, 0, 356516, 6826, 5, 262144⟩
    (by decide) selected_cut_14590

theorem selected_cut_14591 : selected 9 ⟨376132, by decide⟩
    (prefixPartial 12 27308) = some ⟨12, 2, 0, 376132, 27308, 1529, 65536⟩ := by
  decide +kernel

theorem context_12_27308_376132 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27308 ⟨376132, by decide⟩ :=
  accepted_of_selected 12 27308 ⟨376132, by decide⟩ ⟨12, 2, 0, 376132, 27308, 1529, 65536⟩
    (by decide) selected_cut_14591

theorem selected_cut_14592 : selected 9 ⟨376144, by decide⟩
    (prefixPartial 12 27309) = some ⟨12, 2, 0, 376144, 27309, 1489, 65536⟩ := by
  decide +kernel

theorem context_12_27309_376144 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27309 ⟨376144, by decide⟩ :=
  accepted_of_selected 12 27309 ⟨376144, by decide⟩ ⟨12, 2, 0, 376144, 27309, 1489, 65536⟩
    (by decide) selected_cut_14592

theorem selected_cut_14593 : selected 9 ⟨376158, by decide⟩
    (prefixPartial 12 27310) = some ⟨12, 2, 0, 376158, 27310, 1205, 65536⟩ := by
  decide +kernel

theorem context_12_27310_376158 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27310 ⟨376158, by decide⟩ :=
  accepted_of_selected 12 27310 ⟨376158, by decide⟩ ⟨12, 2, 0, 376158, 27310, 1205, 65536⟩
    (by decide) selected_cut_14593

theorem selected_cut_14594 : selected 9 ⟨376172, by decide⟩
    (prefixPartial 12 27311) = some ⟨12, 2, 0, 376172, 27311, 1433, 65536⟩ := by
  decide +kernel

theorem context_12_27311_376172 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27311 ⟨376172, by decide⟩ :=
  accepted_of_selected 12 27311 ⟨376172, by decide⟩ ⟨12, 2, 0, 376172, 27311, 1433, 65536⟩
    (by decide) selected_cut_14594

theorem unmarked_context_11_6827_376173 : frontier 10 ⟨376173, by decide⟩
    (prefixCache 11 6827) (prefixPartial 11 6827) = false := by
  decide +kernel

theorem node_context_11_6827_376173 : EJMOriginalGlobalDAGData.nodes 10 ⟨376173, by decide⟩ =
    .split (coordinate 11) (![⟨376132, by decide⟩,⟨376144, by decide⟩,⟨376158, by decide⟩,⟨376172, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6827_376173 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6827 ⟨376173, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6827
    ⟨376173, by decide⟩ (by decide) (![⟨376132, by decide⟩,⟨376144, by decide⟩,⟨376158, by decide⟩,⟨376172, by decide⟩]) unmarked_context_11_6827_376173 node_context_11_6827_376173
  intro a
  fin_cases a
  · exact context_12_27308_376132
  · exact context_12_27309_376144
  · exact context_12_27310_376158
  · exact context_12_27311_376172

theorem unmarked_context_10_1706_376174 : frontier 11 ⟨376174, by decide⟩
    (prefixCache 10 1706) (prefixPartial 10 1706) = false := by
  decide +kernel

theorem node_context_10_1706_376174 : EJMOriginalGlobalDAGData.nodes 11 ⟨376174, by decide⟩ =
    .split (coordinate 10) (![⟨376049, by decide⟩,⟨376118, by decide⟩,⟨356516, by decide⟩,⟨376173, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1706_376174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1706 ⟨376174, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1706
    ⟨376174, by decide⟩ (by decide) (![⟨376049, by decide⟩,⟨376118, by decide⟩,⟨356516, by decide⟩,⟨376173, by decide⟩]) unmarked_context_10_1706_376174 node_context_10_1706_376174
  intro a
  fin_cases a
  · exact context_11_6824_376049
  · exact context_11_6825_376118
  · exact context_11_6826_356516
  · exact context_11_6827_376173

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
