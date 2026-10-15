/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover048
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_04706 : selected 8 ⟨151241, by decide⟩
    (prefixPartial 13 74897) = some ⟨13, 2, 0, 151241, 74897, 2385, 16384⟩ := by
  decide +kernel

theorem context_13_74897_151241 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74897 ⟨151241, by decide⟩ :=
  accepted_of_selected 13 74897 ⟨151241, by decide⟩ ⟨13, 2, 0, 151241, 74897, 2385, 16384⟩
    (by decide) selected_cut_04706

theorem selected_cut_04707 : selected 8 ⟨151261, by decide⟩
    (prefixPartial 13 74898) = some ⟨13, 2, 0, 151261, 74898, 1553, 16384⟩ := by
  decide +kernel

theorem context_13_74898_151261 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74898 ⟨151261, by decide⟩ :=
  accepted_of_selected 13 74898 ⟨151261, by decide⟩ ⟨13, 2, 0, 151261, 74898, 1553, 16384⟩
    (by decide) selected_cut_04707

theorem selected_cut_04708 : selected 8 ⟨151265, by decide⟩
    (prefixPartial 13 74899) = some ⟨13, 2, 0, 151265, 74899, 929, 16384⟩ := by
  decide +kernel

theorem context_13_74899_151265 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74899 ⟨151265, by decide⟩ :=
  accepted_of_selected 13 74899 ⟨151265, by decide⟩ ⟨13, 2, 0, 151265, 74899, 929, 16384⟩
    (by decide) selected_cut_04708

theorem unmarked_context_12_18724_151266 : frontier 9 ⟨151266, by decide⟩
    (prefixCache 12 18724) (prefixPartial 12 18724) = false := by
  decide +kernel

theorem node_context_12_18724_151266 : EJMOriginalGlobalDAGData.nodes 9 ⟨151266, by decide⟩ =
    .split (coordinate 12) (![⟨151215, by decide⟩,⟨151241, by decide⟩,⟨151261, by decide⟩,⟨151265, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18724_151266 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18724 ⟨151266, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18724
    ⟨151266, by decide⟩ (by decide) (![⟨151215, by decide⟩,⟨151241, by decide⟩,⟨151261, by decide⟩,⟨151265, by decide⟩]) unmarked_context_12_18724_151266 node_context_12_18724_151266
  intro a
  fin_cases a
  · exact context_13_74896_151215
  · exact context_13_74897_151241
  · exact context_13_74898_151261
  · exact context_13_74899_151265

theorem selected_cut_04709 : selected 8 ⟨151285, by decide⟩
    (prefixPartial 13 74900) = some ⟨13, 2, 0, 151285, 74900, 1669, 16384⟩ := by
  decide +kernel

theorem context_13_74900_151285 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74900 ⟨151285, by decide⟩ :=
  accepted_of_selected 13 74900 ⟨151285, by decide⟩ ⟨13, 2, 0, 151285, 74900, 1669, 16384⟩
    (by decide) selected_cut_04709

theorem selected_cut_04710 : selected 8 ⟨151310, by decide⟩
    (prefixPartial 13 74901) = some ⟨13, 2, 0, 151310, 74901, 3217, 16384⟩ := by
  decide +kernel

theorem context_13_74901_151310 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74901 ⟨151310, by decide⟩ :=
  accepted_of_selected 13 74901 ⟨151310, by decide⟩ ⟨13, 2, 0, 151310, 74901, 3217, 16384⟩
    (by decide) selected_cut_04710

theorem selected_cut_04711 : selected 8 ⟨151331, by decide⟩
    (prefixPartial 13 74902) = some ⟨13, 2, 0, 151331, 74902, 2213, 16384⟩ := by
  decide +kernel

theorem context_13_74902_151331 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74902 ⟨151331, by decide⟩ :=
  accepted_of_selected 13 74902 ⟨151331, by decide⟩ ⟨13, 2, 0, 151331, 74902, 2213, 16384⟩
    (by decide) selected_cut_04711

theorem selected_cut_04712 : selected 8 ⟨151335, by decide⟩
    (prefixPartial 13 74903) = some ⟨13, 2, 0, 151335, 74903, 1129, 16384⟩ := by
  decide +kernel

theorem context_13_74903_151335 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74903 ⟨151335, by decide⟩ :=
  accepted_of_selected 13 74903 ⟨151335, by decide⟩ ⟨13, 2, 0, 151335, 74903, 1129, 16384⟩
    (by decide) selected_cut_04712

theorem unmarked_context_12_18725_151336 : frontier 9 ⟨151336, by decide⟩
    (prefixCache 12 18725) (prefixPartial 12 18725) = false := by
  decide +kernel

theorem node_context_12_18725_151336 : EJMOriginalGlobalDAGData.nodes 9 ⟨151336, by decide⟩ =
    .split (coordinate 12) (![⟨151285, by decide⟩,⟨151310, by decide⟩,⟨151331, by decide⟩,⟨151335, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18725_151336 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18725 ⟨151336, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18725
    ⟨151336, by decide⟩ (by decide) (![⟨151285, by decide⟩,⟨151310, by decide⟩,⟨151331, by decide⟩,⟨151335, by decide⟩]) unmarked_context_12_18725_151336 node_context_12_18725_151336
  intro a
  fin_cases a
  · exact context_13_74900_151285
  · exact context_13_74901_151310
  · exact context_13_74902_151331
  · exact context_13_74903_151335

theorem selected_cut_04713 : selected 8 ⟨151357, by decide⟩
    (prefixPartial 13 74904) = some ⟨13, 2, 0, 151357, 74904, 1389, 16384⟩ := by
  decide +kernel

theorem context_13_74904_151357 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74904 ⟨151357, by decide⟩ :=
  accepted_of_selected 13 74904 ⟨151357, by decide⟩ ⟨13, 2, 0, 151357, 74904, 1389, 16384⟩
    (by decide) selected_cut_04713

theorem selected_cut_04714 : selected 8 ⟨151383, by decide⟩
    (prefixPartial 13 74905) = some ⟨13, 2, 0, 151383, 74905, 2573, 16384⟩ := by
  decide +kernel

theorem context_13_74905_151383 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74905 ⟨151383, by decide⟩ :=
  accepted_of_selected 13 74905 ⟨151383, by decide⟩ ⟨13, 2, 0, 151383, 74905, 2573, 16384⟩
    (by decide) selected_cut_04714

theorem selected_cut_04715 : selected 8 ⟨151402, by decide⟩
    (prefixPartial 13 74906) = some ⟨13, 2, 0, 151402, 74906, 1717, 16384⟩ := by
  decide +kernel

theorem context_13_74906_151402 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74906 ⟨151402, by decide⟩ :=
  accepted_of_selected 13 74906 ⟨151402, by decide⟩ ⟨13, 2, 0, 151402, 74906, 1717, 16384⟩
    (by decide) selected_cut_04715

theorem selected_cut_04716 : selected 8 ⟨151410, by decide⟩
    (prefixPartial 13 74907) = some ⟨13, 2, 0, 151410, 74907, 985, 16384⟩ := by
  decide +kernel

theorem context_13_74907_151410 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74907 ⟨151410, by decide⟩ :=
  accepted_of_selected 13 74907 ⟨151410, by decide⟩ ⟨13, 2, 0, 151410, 74907, 985, 16384⟩
    (by decide) selected_cut_04716

theorem unmarked_context_12_18726_151411 : frontier 9 ⟨151411, by decide⟩
    (prefixCache 12 18726) (prefixPartial 12 18726) = false := by
  decide +kernel

theorem node_context_12_18726_151411 : EJMOriginalGlobalDAGData.nodes 9 ⟨151411, by decide⟩ =
    .split (coordinate 12) (![⟨151357, by decide⟩,⟨151383, by decide⟩,⟨151402, by decide⟩,⟨151410, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18726_151411 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18726 ⟨151411, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18726
    ⟨151411, by decide⟩ (by decide) (![⟨151357, by decide⟩,⟨151383, by decide⟩,⟨151402, by decide⟩,⟨151410, by decide⟩]) unmarked_context_12_18726_151411 node_context_12_18726_151411
  intro a
  fin_cases a
  · exact context_13_74904_151357
  · exact context_13_74905_151383
  · exact context_13_74906_151402
  · exact context_13_74907_151410

theorem selected_cut_04717 : selected 8 ⟨151432, by decide⟩
    (prefixPartial 13 74908) = some ⟨13, 2, 0, 151432, 74908, 1277, 16384⟩ := by
  decide +kernel

theorem context_13_74908_151432 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74908 ⟨151432, by decide⟩ :=
  accepted_of_selected 13 74908 ⟨151432, by decide⟩ ⟨13, 2, 0, 151432, 74908, 1277, 16384⟩
    (by decide) selected_cut_04717

theorem selected_cut_04718 : selected 8 ⟨151464, by decide⟩
    (prefixPartial 13 74909) = some ⟨13, 2, 0, 151464, 74909, 2625, 16384⟩ := by
  decide +kernel

theorem context_13_74909_151464 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74909 ⟨151464, by decide⟩ :=
  accepted_of_selected 13 74909 ⟨151464, by decide⟩ ⟨13, 2, 0, 151464, 74909, 2625, 16384⟩
    (by decide) selected_cut_04718

theorem selected_cut_04719 : selected 8 ⟨151485, by decide⟩
    (prefixPartial 13 74910) = some ⟨13, 2, 0, 151485, 74910, 1793, 16384⟩ := by
  decide +kernel

theorem context_13_74910_151485 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74910 ⟨151485, by decide⟩ :=
  accepted_of_selected 13 74910 ⟨151485, by decide⟩ ⟨13, 2, 0, 151485, 74910, 1793, 16384⟩
    (by decide) selected_cut_04719

theorem selected_cut_04720 : selected 8 ⟨151490, by decide⟩
    (prefixPartial 13 74911) = some ⟨13, 2, 0, 151490, 74911, 945, 16384⟩ := by
  decide +kernel

theorem context_13_74911_151490 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74911 ⟨151490, by decide⟩ :=
  accepted_of_selected 13 74911 ⟨151490, by decide⟩ ⟨13, 2, 0, 151490, 74911, 945, 16384⟩
    (by decide) selected_cut_04720

theorem unmarked_context_12_18727_151491 : frontier 9 ⟨151491, by decide⟩
    (prefixCache 12 18727) (prefixPartial 12 18727) = false := by
  decide +kernel

theorem node_context_12_18727_151491 : EJMOriginalGlobalDAGData.nodes 9 ⟨151491, by decide⟩ =
    .split (coordinate 12) (![⟨151432, by decide⟩,⟨151464, by decide⟩,⟨151485, by decide⟩,⟨151490, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18727_151491 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18727 ⟨151491, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18727
    ⟨151491, by decide⟩ (by decide) (![⟨151432, by decide⟩,⟨151464, by decide⟩,⟨151485, by decide⟩,⟨151490, by decide⟩]) unmarked_context_12_18727_151491 node_context_12_18727_151491
  intro a
  fin_cases a
  · exact context_13_74908_151432
  · exact context_13_74909_151464
  · exact context_13_74910_151485
  · exact context_13_74911_151490

theorem unmarked_context_11_4681_151492 : frontier 10 ⟨151492, by decide⟩
    (prefixCache 11 4681) (prefixPartial 11 4681) = false := by
  decide +kernel

theorem node_context_11_4681_151492 : EJMOriginalGlobalDAGData.nodes 10 ⟨151492, by decide⟩ =
    .split (coordinate 11) (![⟨151266, by decide⟩,⟨151336, by decide⟩,⟨151411, by decide⟩,⟨151491, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4681_151492 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4681 ⟨151492, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4681
    ⟨151492, by decide⟩ (by decide) (![⟨151266, by decide⟩,⟨151336, by decide⟩,⟨151411, by decide⟩,⟨151491, by decide⟩]) unmarked_context_11_4681_151492 node_context_11_4681_151492
  intro a
  fin_cases a
  · exact context_12_18724_151266
  · exact context_12_18725_151336
  · exact context_12_18726_151411
  · exact context_12_18727_151491

theorem selected_cut_04721 : selected 8 ⟨151521, by decide⟩
    (prefixPartial 13 74912) = some ⟨13, 2, 0, 151521, 74912, 1521, 16384⟩ := by
  decide +kernel

theorem context_13_74912_151521 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74912 ⟨151521, by decide⟩ :=
  accepted_of_selected 13 74912 ⟨151521, by decide⟩ ⟨13, 2, 0, 151521, 74912, 1521, 16384⟩
    (by decide) selected_cut_04721

theorem selected_cut_04722 : selected 8 ⟨151584, by decide⟩
    (prefixPartial 13 74913) = some ⟨13, 2, 0, 151584, 74913, 3737, 16384⟩ := by
  decide +kernel

theorem context_13_74913_151584 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74913 ⟨151584, by decide⟩ :=
  accepted_of_selected 13 74913 ⟨151584, by decide⟩ ⟨13, 2, 0, 151584, 74913, 3737, 16384⟩
    (by decide) selected_cut_04722

theorem selected_cut_04723 : selected 8 ⟨151607, by decide⟩
    (prefixPartial 13 74914) = some ⟨13, 2, 0, 151607, 74914, 2129, 16384⟩ := by
  decide +kernel

theorem context_13_74914_151607 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74914 ⟨151607, by decide⟩ :=
  accepted_of_selected 13 74914 ⟨151607, by decide⟩ ⟨13, 2, 0, 151607, 74914, 2129, 16384⟩
    (by decide) selected_cut_04723

theorem selected_cut_04724 : selected 8 ⟨151615, by decide⟩
    (prefixPartial 13 74915) = some ⟨13, 2, 0, 151615, 74915, 1137, 16384⟩ := by
  decide +kernel

theorem context_13_74915_151615 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74915 ⟨151615, by decide⟩ :=
  accepted_of_selected 13 74915 ⟨151615, by decide⟩ ⟨13, 2, 0, 151615, 74915, 1137, 16384⟩
    (by decide) selected_cut_04724

theorem unmarked_context_12_18728_151616 : frontier 9 ⟨151616, by decide⟩
    (prefixCache 12 18728) (prefixPartial 12 18728) = false := by
  decide +kernel

theorem node_context_12_18728_151616 : EJMOriginalGlobalDAGData.nodes 9 ⟨151616, by decide⟩ =
    .split (coordinate 12) (![⟨151521, by decide⟩,⟨151584, by decide⟩,⟨151607, by decide⟩,⟨151615, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18728_151616 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18728 ⟨151616, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18728
    ⟨151616, by decide⟩ (by decide) (![⟨151521, by decide⟩,⟨151584, by decide⟩,⟨151607, by decide⟩,⟨151615, by decide⟩]) unmarked_context_12_18728_151616 node_context_12_18728_151616
  intro a
  fin_cases a
  · exact context_13_74912_151521
  · exact context_13_74913_151584
  · exact context_13_74914_151607
  · exact context_13_74915_151615

theorem selected_cut_04725 : selected 8 ⟨151633, by decide⟩
    (prefixPartial 13 74916) = some ⟨13, 2, 0, 151633, 74916, 1581, 16384⟩ := by
  decide +kernel

theorem context_13_74916_151633 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74916 ⟨151633, by decide⟩ :=
  accepted_of_selected 13 74916 ⟨151633, by decide⟩ ⟨13, 2, 0, 151633, 74916, 1581, 16384⟩
    (by decide) selected_cut_04725

theorem selected_cut_04726 : selected 8 ⟨151667, by decide⟩
    (prefixPartial 13 74917) = some ⟨13, 2, 0, 151667, 74917, 3225, 16384⟩ := by
  decide +kernel

theorem context_13_74917_151667 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74917 ⟨151667, by decide⟩ :=
  accepted_of_selected 13 74917 ⟨151667, by decide⟩ ⟨13, 2, 0, 151667, 74917, 3225, 16384⟩
    (by decide) selected_cut_04726

theorem selected_cut_04727 : selected 8 ⟨151690, by decide⟩
    (prefixPartial 13 74918) = some ⟨13, 2, 0, 151690, 74918, 2173, 16384⟩ := by
  decide +kernel

theorem context_13_74918_151690 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74918 ⟨151690, by decide⟩ :=
  accepted_of_selected 13 74918 ⟨151690, by decide⟩ ⟨13, 2, 0, 151690, 74918, 2173, 16384⟩
    (by decide) selected_cut_04727

theorem selected_cut_04728 : selected 8 ⟨151697, by decide⟩
    (prefixPartial 13 74919) = some ⟨13, 2, 0, 151697, 74919, 1125, 16384⟩ := by
  decide +kernel

theorem context_13_74919_151697 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74919 ⟨151697, by decide⟩ :=
  accepted_of_selected 13 74919 ⟨151697, by decide⟩ ⟨13, 2, 0, 151697, 74919, 1125, 16384⟩
    (by decide) selected_cut_04728

theorem unmarked_context_12_18729_151698 : frontier 9 ⟨151698, by decide⟩
    (prefixCache 12 18729) (prefixPartial 12 18729) = false := by
  decide +kernel

theorem node_context_12_18729_151698 : EJMOriginalGlobalDAGData.nodes 9 ⟨151698, by decide⟩ =
    .split (coordinate 12) (![⟨151633, by decide⟩,⟨151667, by decide⟩,⟨151690, by decide⟩,⟨151697, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18729_151698 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18729 ⟨151698, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18729
    ⟨151698, by decide⟩ (by decide) (![⟨151633, by decide⟩,⟨151667, by decide⟩,⟨151690, by decide⟩,⟨151697, by decide⟩]) unmarked_context_12_18729_151698 node_context_12_18729_151698
  intro a
  fin_cases a
  · exact context_13_74916_151633
  · exact context_13_74917_151667
  · exact context_13_74918_151690
  · exact context_13_74919_151697

theorem selected_cut_04729 : selected 8 ⟨151722, by decide⟩
    (prefixPartial 13 74920) = some ⟨13, 2, 0, 151722, 74920, 1689, 16384⟩ := by
  decide +kernel

theorem context_13_74920_151722 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74920 ⟨151722, by decide⟩ :=
  accepted_of_selected 13 74920 ⟨151722, by decide⟩ ⟨13, 2, 0, 151722, 74920, 1689, 16384⟩
    (by decide) selected_cut_04729

theorem selected_cut_04730 : selected 8 ⟨151769, by decide⟩
    (prefixPartial 13 74921) = some ⟨13, 2, 0, 151769, 74921, 3605, 16384⟩ := by
  decide +kernel

theorem context_13_74921_151769 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74921 ⟨151769, by decide⟩ :=
  accepted_of_selected 13 74921 ⟨151769, by decide⟩ ⟨13, 2, 0, 151769, 74921, 3605, 16384⟩
    (by decide) selected_cut_04730

theorem selected_cut_04731 : selected 8 ⟨151794, by decide⟩
    (prefixPartial 13 74922) = some ⟨13, 2, 0, 151794, 74922, 2189, 16384⟩ := by
  decide +kernel

theorem context_13_74922_151794 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74922 ⟨151794, by decide⟩ :=
  accepted_of_selected 13 74922 ⟨151794, by decide⟩ ⟨13, 2, 0, 151794, 74922, 2189, 16384⟩
    (by decide) selected_cut_04731

theorem selected_cut_04732 : selected 8 ⟨151802, by decide⟩
    (prefixPartial 13 74923) = some ⟨13, 2, 0, 151802, 74923, 1149, 16384⟩ := by
  decide +kernel

theorem context_13_74923_151802 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74923 ⟨151802, by decide⟩ :=
  accepted_of_selected 13 74923 ⟨151802, by decide⟩ ⟨13, 2, 0, 151802, 74923, 1149, 16384⟩
    (by decide) selected_cut_04732

theorem unmarked_context_12_18730_151803 : frontier 9 ⟨151803, by decide⟩
    (prefixCache 12 18730) (prefixPartial 12 18730) = false := by
  decide +kernel

theorem node_context_12_18730_151803 : EJMOriginalGlobalDAGData.nodes 9 ⟨151803, by decide⟩ =
    .split (coordinate 12) (![⟨151722, by decide⟩,⟨151769, by decide⟩,⟨151794, by decide⟩,⟨151802, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18730_151803 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18730 ⟨151803, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18730
    ⟨151803, by decide⟩ (by decide) (![⟨151722, by decide⟩,⟨151769, by decide⟩,⟨151794, by decide⟩,⟨151802, by decide⟩]) unmarked_context_12_18730_151803 node_context_12_18730_151803
  intro a
  fin_cases a
  · exact context_13_74920_151722
  · exact context_13_74921_151769
  · exact context_13_74922_151794
  · exact context_13_74923_151802

theorem selected_cut_04733 : selected 8 ⟨151834, by decide⟩
    (prefixPartial 13 74924) = some ⟨13, 2, 0, 151834, 74924, 1797, 16384⟩ := by
  decide +kernel

theorem context_13_74924_151834 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74924 ⟨151834, by decide⟩ :=
  accepted_of_selected 13 74924 ⟨151834, by decide⟩ ⟨13, 2, 0, 151834, 74924, 1797, 16384⟩
    (by decide) selected_cut_04733

theorem selected_cut_04734 : selected 7 ⟨151853, by decide⟩
    (prefixPartial 14 299700) = some ⟨14, 2, 0, 151853, 299700, 1069, 4096⟩ := by
  decide +kernel

theorem context_14_299700_151853 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 299700 ⟨151853, by decide⟩ :=
  accepted_of_selected 14 299700 ⟨151853, by decide⟩ ⟨14, 2, 0, 151853, 299700, 1069, 4096⟩
    (by decide) selected_cut_04734

theorem selected_cut_04735 : selected 7 ⟨151876, by decide⟩
    (prefixPartial 14 299701) = some ⟨14, 2, 0, 151876, 299701, 1077, 4096⟩ := by
  decide +kernel

theorem context_14_299701_151876 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 299701 ⟨151876, by decide⟩ :=
  accepted_of_selected 14 299701 ⟨151876, by decide⟩ ⟨14, 2, 0, 151876, 299701, 1077, 4096⟩
    (by decide) selected_cut_04735

theorem selected_cut_04736 : selected 7 ⟨151892, by decide⟩
    (prefixPartial 14 299702) = some ⟨14, 2, 0, 151892, 299702, 1041, 4096⟩ := by
  decide +kernel

theorem context_14_299702_151892 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 299702 ⟨151892, by decide⟩ :=
  accepted_of_selected 14 299702 ⟨151892, by decide⟩ ⟨14, 2, 0, 151892, 299702, 1041, 4096⟩
    (by decide) selected_cut_04736

theorem selected_cut_04737 : selected 7 ⟨151904, by decide⟩
    (prefixPartial 14 299703) = some ⟨14, 2, 0, 151904, 299703, 969, 4096⟩ := by
  decide +kernel

theorem context_14_299703_151904 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 299703 ⟨151904, by decide⟩ :=
  accepted_of_selected 14 299703 ⟨151904, by decide⟩ ⟨14, 2, 0, 151904, 299703, 969, 4096⟩
    (by decide) selected_cut_04737

theorem unmarked_context_13_74925_151905 : frontier 8 ⟨151905, by decide⟩
    (prefixCache 13 74925) (prefixPartial 13 74925) = false := by
  decide +kernel

theorem node_context_13_74925_151905 : EJMOriginalGlobalDAGData.nodes 8 ⟨151905, by decide⟩ =
    .split (coordinate 13) (![⟨151853, by decide⟩,⟨151876, by decide⟩,⟨151892, by decide⟩,⟨151904, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_74925_151905 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74925 ⟨151905, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 74925
    ⟨151905, by decide⟩ (by decide) (![⟨151853, by decide⟩,⟨151876, by decide⟩,⟨151892, by decide⟩,⟨151904, by decide⟩]) unmarked_context_13_74925_151905 node_context_13_74925_151905
  intro a
  fin_cases a
  · exact context_14_299700_151853
  · exact context_14_299701_151876
  · exact context_14_299702_151892
  · exact context_14_299703_151904

theorem selected_cut_04738 : selected 8 ⟨151937, by decide⟩
    (prefixPartial 13 74926) = some ⟨13, 2, 0, 151937, 74926, 2529, 16384⟩ := by
  decide +kernel

theorem context_13_74926_151937 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74926 ⟨151937, by decide⟩ :=
  accepted_of_selected 13 74926 ⟨151937, by decide⟩ ⟨13, 2, 0, 151937, 74926, 2529, 16384⟩
    (by decide) selected_cut_04738

theorem selected_cut_04739 : selected 8 ⟨151947, by decide⟩
    (prefixPartial 13 74927) = some ⟨13, 2, 0, 151947, 74927, 1181, 16384⟩ := by
  decide +kernel

theorem context_13_74927_151947 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74927 ⟨151947, by decide⟩ :=
  accepted_of_selected 13 74927 ⟨151947, by decide⟩ ⟨13, 2, 0, 151947, 74927, 1181, 16384⟩
    (by decide) selected_cut_04739

theorem unmarked_context_12_18731_151948 : frontier 9 ⟨151948, by decide⟩
    (prefixCache 12 18731) (prefixPartial 12 18731) = false := by
  decide +kernel

theorem node_context_12_18731_151948 : EJMOriginalGlobalDAGData.nodes 9 ⟨151948, by decide⟩ =
    .split (coordinate 12) (![⟨151834, by decide⟩,⟨151905, by decide⟩,⟨151937, by decide⟩,⟨151947, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18731_151948 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18731 ⟨151948, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18731
    ⟨151948, by decide⟩ (by decide) (![⟨151834, by decide⟩,⟨151905, by decide⟩,⟨151937, by decide⟩,⟨151947, by decide⟩]) unmarked_context_12_18731_151948 node_context_12_18731_151948
  intro a
  fin_cases a
  · exact context_13_74924_151834
  · exact context_13_74925_151905
  · exact context_13_74926_151937
  · exact context_13_74927_151947

theorem unmarked_context_11_4682_151949 : frontier 10 ⟨151949, by decide⟩
    (prefixCache 11 4682) (prefixPartial 11 4682) = false := by
  decide +kernel

theorem node_context_11_4682_151949 : EJMOriginalGlobalDAGData.nodes 10 ⟨151949, by decide⟩ =
    .split (coordinate 11) (![⟨151616, by decide⟩,⟨151698, by decide⟩,⟨151803, by decide⟩,⟨151948, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4682_151949 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4682 ⟨151949, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4682
    ⟨151949, by decide⟩ (by decide) (![⟨151616, by decide⟩,⟨151698, by decide⟩,⟨151803, by decide⟩,⟨151948, by decide⟩]) unmarked_context_11_4682_151949 node_context_11_4682_151949
  intro a
  fin_cases a
  · exact context_12_18728_151616
  · exact context_12_18729_151698
  · exact context_12_18730_151803
  · exact context_12_18731_151948

theorem selected_cut_04740 : selected 8 ⟨151960, by decide⟩
    (prefixPartial 13 74928) = some ⟨13, 2, 0, 151960, 74928, 805, 16384⟩ := by
  decide +kernel

theorem context_13_74928_151960 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74928 ⟨151960, by decide⟩ :=
  accepted_of_selected 13 74928 ⟨151960, by decide⟩ ⟨13, 2, 0, 151960, 74928, 805, 16384⟩
    (by decide) selected_cut_04740

theorem selected_cut_04741 : selected 8 ⟨151980, by decide⟩
    (prefixPartial 13 74929) = some ⟨13, 2, 0, 151980, 74929, 3009, 16384⟩ := by
  decide +kernel

theorem context_13_74929_151980 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74929 ⟨151980, by decide⟩ :=
  accepted_of_selected 13 74929 ⟨151980, by decide⟩ ⟨13, 2, 0, 151980, 74929, 3009, 16384⟩
    (by decide) selected_cut_04741

theorem selected_cut_04742 : selected 8 ⟨152001, by decide⟩
    (prefixPartial 13 74930) = some ⟨13, 2, 0, 152001, 74930, 1705, 16384⟩ := by
  decide +kernel

theorem context_13_74930_152001 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74930 ⟨152001, by decide⟩ :=
  accepted_of_selected 13 74930 ⟨152001, by decide⟩ ⟨13, 2, 0, 152001, 74930, 1705, 16384⟩
    (by decide) selected_cut_04742

theorem selected_cut_04743 : selected 8 ⟨152012, by decide⟩
    (prefixPartial 13 74931) = some ⟨13, 2, 0, 152012, 74931, 1049, 16384⟩ := by
  decide +kernel

theorem context_13_74931_152012 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74931 ⟨152012, by decide⟩ :=
  accepted_of_selected 13 74931 ⟨152012, by decide⟩ ⟨13, 2, 0, 152012, 74931, 1049, 16384⟩
    (by decide) selected_cut_04743

theorem unmarked_context_12_18732_152013 : frontier 9 ⟨152013, by decide⟩
    (prefixCache 12 18732) (prefixPartial 12 18732) = false := by
  decide +kernel

theorem node_context_12_18732_152013 : EJMOriginalGlobalDAGData.nodes 9 ⟨152013, by decide⟩ =
    .split (coordinate 12) (![⟨151960, by decide⟩,⟨151980, by decide⟩,⟨152001, by decide⟩,⟨152012, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18732_152013 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18732 ⟨152013, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18732
    ⟨152013, by decide⟩ (by decide) (![⟨151960, by decide⟩,⟨151980, by decide⟩,⟨152001, by decide⟩,⟨152012, by decide⟩]) unmarked_context_12_18732_152013 node_context_12_18732_152013
  intro a
  fin_cases a
  · exact context_13_74928_151960
  · exact context_13_74929_151980
  · exact context_13_74930_152001
  · exact context_13_74931_152012

theorem selected_cut_04744 : selected 8 ⟨152030, by decide⟩
    (prefixPartial 13 74932) = some ⟨13, 2, 0, 152030, 74932, 869, 16384⟩ := by
  decide +kernel

theorem context_13_74932_152030 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74932 ⟨152030, by decide⟩ :=
  accepted_of_selected 13 74932 ⟨152030, by decide⟩ ⟨13, 2, 0, 152030, 74932, 869, 16384⟩
    (by decide) selected_cut_04744

theorem selected_cut_04745 : selected 8 ⟨152064, by decide⟩
    (prefixPartial 13 74933) = some ⟨13, 2, 0, 152064, 74933, 2625, 16384⟩ := by
  decide +kernel

theorem context_13_74933_152064 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74933 ⟨152064, by decide⟩ :=
  accepted_of_selected 13 74933 ⟨152064, by decide⟩ ⟨13, 2, 0, 152064, 74933, 2625, 16384⟩
    (by decide) selected_cut_04745

theorem selected_cut_04746 : selected 8 ⟨152085, by decide⟩
    (prefixPartial 13 74934) = some ⟨13, 2, 0, 152085, 74934, 1881, 16384⟩ := by
  decide +kernel

theorem context_13_74934_152085 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74934 ⟨152085, by decide⟩ :=
  accepted_of_selected 13 74934 ⟨152085, by decide⟩ ⟨13, 2, 0, 152085, 74934, 1881, 16384⟩
    (by decide) selected_cut_04746

theorem selected_cut_04747 : selected 8 ⟨152095, by decide⟩
    (prefixPartial 13 74935) = some ⟨13, 2, 0, 152095, 74935, 945, 16384⟩ := by
  decide +kernel

theorem context_13_74935_152095 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74935 ⟨152095, by decide⟩ :=
  accepted_of_selected 13 74935 ⟨152095, by decide⟩ ⟨13, 2, 0, 152095, 74935, 945, 16384⟩
    (by decide) selected_cut_04747

theorem unmarked_context_12_18733_152096 : frontier 9 ⟨152096, by decide⟩
    (prefixCache 12 18733) (prefixPartial 12 18733) = false := by
  decide +kernel

theorem node_context_12_18733_152096 : EJMOriginalGlobalDAGData.nodes 9 ⟨152096, by decide⟩ =
    .split (coordinate 12) (![⟨152030, by decide⟩,⟨152064, by decide⟩,⟨152085, by decide⟩,⟨152095, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18733_152096 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18733 ⟨152096, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18733
    ⟨152096, by decide⟩ (by decide) (![⟨152030, by decide⟩,⟨152064, by decide⟩,⟨152085, by decide⟩,⟨152095, by decide⟩]) unmarked_context_12_18733_152096 node_context_12_18733_152096
  intro a
  fin_cases a
  · exact context_13_74932_152030
  · exact context_13_74933_152064
  · exact context_13_74934_152085
  · exact context_13_74935_152095

theorem selected_cut_04748 : selected 8 ⟨152111, by decide⟩
    (prefixPartial 13 74936) = some ⟨13, 2, 0, 152111, 74936, 1073, 16384⟩ := by
  decide +kernel

theorem context_13_74936_152111 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74936 ⟨152111, by decide⟩ :=
  accepted_of_selected 13 74936 ⟨152111, by decide⟩ ⟨13, 2, 0, 152111, 74936, 1073, 16384⟩
    (by decide) selected_cut_04748

theorem selected_cut_04749 : selected 8 ⟨152136, by decide⟩
    (prefixPartial 13 74937) = some ⟨13, 2, 0, 152136, 74937, 3121, 16384⟩ := by
  decide +kernel

theorem context_13_74937_152136 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74937 ⟨152136, by decide⟩ :=
  accepted_of_selected 13 74937 ⟨152136, by decide⟩ ⟨13, 2, 0, 152136, 74937, 3121, 16384⟩
    (by decide) selected_cut_04749

theorem selected_cut_04750 : selected 8 ⟨152154, by decide⟩
    (prefixPartial 13 74938) = some ⟨13, 2, 0, 152154, 74938, 2017, 16384⟩ := by
  decide +kernel

theorem context_13_74938_152154 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74938 ⟨152154, by decide⟩ :=
  accepted_of_selected 13 74938 ⟨152154, by decide⟩ ⟨13, 2, 0, 152154, 74938, 2017, 16384⟩
    (by decide) selected_cut_04750

theorem selected_cut_04751 : selected 8 ⟨152162, by decide⟩
    (prefixPartial 13 74939) = some ⟨13, 2, 0, 152162, 74939, 1077, 16384⟩ := by
  decide +kernel

theorem context_13_74939_152162 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74939 ⟨152162, by decide⟩ :=
  accepted_of_selected 13 74939 ⟨152162, by decide⟩ ⟨13, 2, 0, 152162, 74939, 1077, 16384⟩
    (by decide) selected_cut_04751

theorem unmarked_context_12_18734_152163 : frontier 9 ⟨152163, by decide⟩
    (prefixCache 12 18734) (prefixPartial 12 18734) = false := by
  decide +kernel

theorem node_context_12_18734_152163 : EJMOriginalGlobalDAGData.nodes 9 ⟨152163, by decide⟩ =
    .split (coordinate 12) (![⟨152111, by decide⟩,⟨152136, by decide⟩,⟨152154, by decide⟩,⟨152162, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18734_152163 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18734 ⟨152163, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18734
    ⟨152163, by decide⟩ (by decide) (![⟨152111, by decide⟩,⟨152136, by decide⟩,⟨152154, by decide⟩,⟨152162, by decide⟩]) unmarked_context_12_18734_152163 node_context_12_18734_152163
  intro a
  fin_cases a
  · exact context_13_74936_152111
  · exact context_13_74937_152136
  · exact context_13_74938_152154
  · exact context_13_74939_152162

theorem selected_cut_04752 : selected 8 ⟨152179, by decide⟩
    (prefixPartial 13 74940) = some ⟨13, 2, 0, 152179, 74940, 877, 16384⟩ := by
  decide +kernel

theorem context_13_74940_152179 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74940 ⟨152179, by decide⟩ :=
  accepted_of_selected 13 74940 ⟨152179, by decide⟩ ⟨13, 2, 0, 152179, 74940, 877, 16384⟩
    (by decide) selected_cut_04752

theorem selected_cut_04753 : selected 8 ⟨152203, by decide⟩
    (prefixPartial 13 74941) = some ⟨13, 2, 0, 152203, 74941, 2873, 16384⟩ := by
  decide +kernel

theorem context_13_74941_152203 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74941 ⟨152203, by decide⟩ :=
  accepted_of_selected 13 74941 ⟨152203, by decide⟩ ⟨13, 2, 0, 152203, 74941, 2873, 16384⟩
    (by decide) selected_cut_04753

theorem selected_cut_04754 : selected 8 ⟨152223, by decide⟩
    (prefixPartial 13 74942) = some ⟨13, 2, 0, 152223, 74942, 1789, 16384⟩ := by
  decide +kernel

theorem context_13_74942_152223 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74942 ⟨152223, by decide⟩ :=
  accepted_of_selected 13 74942 ⟨152223, by decide⟩ ⟨13, 2, 0, 152223, 74942, 1789, 16384⟩
    (by decide) selected_cut_04754

theorem selected_cut_04755 : selected 8 ⟨152229, by decide⟩
    (prefixPartial 13 74943) = some ⟨13, 2, 0, 152229, 74943, 985, 16384⟩ := by
  decide +kernel

theorem context_13_74943_152229 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74943 ⟨152229, by decide⟩ :=
  accepted_of_selected 13 74943 ⟨152229, by decide⟩ ⟨13, 2, 0, 152229, 74943, 985, 16384⟩
    (by decide) selected_cut_04755

theorem unmarked_context_12_18735_152230 : frontier 9 ⟨152230, by decide⟩
    (prefixCache 12 18735) (prefixPartial 12 18735) = false := by
  decide +kernel

theorem node_context_12_18735_152230 : EJMOriginalGlobalDAGData.nodes 9 ⟨152230, by decide⟩ =
    .split (coordinate 12) (![⟨152179, by decide⟩,⟨152203, by decide⟩,⟨152223, by decide⟩,⟨152229, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18735_152230 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18735 ⟨152230, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18735
    ⟨152230, by decide⟩ (by decide) (![⟨152179, by decide⟩,⟨152203, by decide⟩,⟨152223, by decide⟩,⟨152229, by decide⟩]) unmarked_context_12_18735_152230 node_context_12_18735_152230
  intro a
  fin_cases a
  · exact context_13_74940_152179
  · exact context_13_74941_152203
  · exact context_13_74942_152223
  · exact context_13_74943_152229

theorem unmarked_context_11_4683_152231 : frontier 10 ⟨152231, by decide⟩
    (prefixCache 11 4683) (prefixPartial 11 4683) = false := by
  decide +kernel

theorem node_context_11_4683_152231 : EJMOriginalGlobalDAGData.nodes 10 ⟨152231, by decide⟩ =
    .split (coordinate 11) (![⟨152013, by decide⟩,⟨152096, by decide⟩,⟨152163, by decide⟩,⟨152230, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4683_152231 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4683 ⟨152231, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4683
    ⟨152231, by decide⟩ (by decide) (![⟨152013, by decide⟩,⟨152096, by decide⟩,⟨152163, by decide⟩,⟨152230, by decide⟩]) unmarked_context_11_4683_152231 node_context_11_4683_152231
  intro a
  fin_cases a
  · exact context_12_18732_152013
  · exact context_12_18733_152096
  · exact context_12_18734_152163
  · exact context_12_18735_152230

theorem unmarked_context_10_1170_152232 : frontier 11 ⟨152232, by decide⟩
    (prefixCache 10 1170) (prefixPartial 10 1170) = false := by
  decide +kernel

theorem node_context_10_1170_152232 : EJMOriginalGlobalDAGData.nodes 11 ⟨152232, by decide⟩ =
    .split (coordinate 10) (![⟨151198, by decide⟩,⟨151492, by decide⟩,⟨151949, by decide⟩,⟨152231, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1170_152232 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1170 ⟨152232, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1170
    ⟨152232, by decide⟩ (by decide) (![⟨151198, by decide⟩,⟨151492, by decide⟩,⟨151949, by decide⟩,⟨152231, by decide⟩]) unmarked_context_10_1170_152232 node_context_10_1170_152232
  intro a
  fin_cases a
  · exact context_11_4680_151198
  · exact context_11_4681_151492
  · exact context_11_4682_151949
  · exact context_11_4683_152231

theorem selected_cut_04756 : selected 8 ⟨152243, by decide⟩
    (prefixPartial 13 74944) = some ⟨13, 2, 0, 152243, 74944, 881, 16384⟩ := by
  decide +kernel

theorem context_13_74944_152243 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74944 ⟨152243, by decide⟩ :=
  accepted_of_selected 13 74944 ⟨152243, by decide⟩ ⟨13, 2, 0, 152243, 74944, 881, 16384⟩
    (by decide) selected_cut_04756

theorem selected_cut_04757 : selected 8 ⟨152274, by decide⟩
    (prefixPartial 13 74945) = some ⟨13, 2, 0, 152274, 74945, 2881, 16384⟩ := by
  decide +kernel

theorem context_13_74945_152274 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74945 ⟨152274, by decide⟩ :=
  accepted_of_selected 13 74945 ⟨152274, by decide⟩ ⟨13, 2, 0, 152274, 74945, 2881, 16384⟩
    (by decide) selected_cut_04757

theorem selected_cut_04758 : selected 8 ⟨152296, by decide⟩
    (prefixPartial 13 74946) = some ⟨13, 2, 0, 152296, 74946, 1817, 16384⟩ := by
  decide +kernel

theorem context_13_74946_152296 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74946 ⟨152296, by decide⟩ :=
  accepted_of_selected 13 74946 ⟨152296, by decide⟩ ⟨13, 2, 0, 152296, 74946, 1817, 16384⟩
    (by decide) selected_cut_04758

theorem selected_cut_04759 : selected 8 ⟨152305, by decide⟩
    (prefixPartial 13 74947) = some ⟨13, 2, 0, 152305, 74947, 937, 16384⟩ := by
  decide +kernel

theorem context_13_74947_152305 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74947 ⟨152305, by decide⟩ :=
  accepted_of_selected 13 74947 ⟨152305, by decide⟩ ⟨13, 2, 0, 152305, 74947, 937, 16384⟩
    (by decide) selected_cut_04759

theorem unmarked_context_12_18736_152306 : frontier 9 ⟨152306, by decide⟩
    (prefixCache 12 18736) (prefixPartial 12 18736) = false := by
  decide +kernel

theorem node_context_12_18736_152306 : EJMOriginalGlobalDAGData.nodes 9 ⟨152306, by decide⟩ =
    .split (coordinate 12) (![⟨152243, by decide⟩,⟨152274, by decide⟩,⟨152296, by decide⟩,⟨152305, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18736_152306 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18736 ⟨152306, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18736
    ⟨152306, by decide⟩ (by decide) (![⟨152243, by decide⟩,⟨152274, by decide⟩,⟨152296, by decide⟩,⟨152305, by decide⟩]) unmarked_context_12_18736_152306 node_context_12_18736_152306
  intro a
  fin_cases a
  · exact context_13_74944_152243
  · exact context_13_74945_152274
  · exact context_13_74946_152296
  · exact context_13_74947_152305

theorem selected_cut_04760 : selected 8 ⟨152316, by decide⟩
    (prefixPartial 13 74948) = some ⟨13, 2, 0, 152316, 74948, 737, 16384⟩ := by
  decide +kernel

theorem context_13_74948_152316 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74948 ⟨152316, by decide⟩ :=
  accepted_of_selected 13 74948 ⟨152316, by decide⟩ ⟨13, 2, 0, 152316, 74948, 737, 16384⟩
    (by decide) selected_cut_04760

theorem selected_cut_04761 : selected 8 ⟨152341, by decide⟩
    (prefixPartial 13 74949) = some ⟨13, 2, 0, 152341, 74949, 1937, 16384⟩ := by
  decide +kernel

theorem context_13_74949_152341 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74949 ⟨152341, by decide⟩ :=
  accepted_of_selected 13 74949 ⟨152341, by decide⟩ ⟨13, 2, 0, 152341, 74949, 1937, 16384⟩
    (by decide) selected_cut_04761

theorem selected_cut_04762 : selected 8 ⟨152360, by decide⟩
    (prefixPartial 13 74950) = some ⟨13, 2, 0, 152360, 74950, 1837, 16384⟩ := by
  decide +kernel

theorem context_13_74950_152360 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74950 ⟨152360, by decide⟩ :=
  accepted_of_selected 13 74950 ⟨152360, by decide⟩ ⟨13, 2, 0, 152360, 74950, 1837, 16384⟩
    (by decide) selected_cut_04762

theorem selected_cut_04763 : selected 8 ⟨152368, by decide⟩
    (prefixPartial 13 74951) = some ⟨13, 2, 0, 152368, 74951, 861, 16384⟩ := by
  decide +kernel

theorem context_13_74951_152368 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74951 ⟨152368, by decide⟩ :=
  accepted_of_selected 13 74951 ⟨152368, by decide⟩ ⟨13, 2, 0, 152368, 74951, 861, 16384⟩
    (by decide) selected_cut_04763

theorem unmarked_context_12_18737_152369 : frontier 9 ⟨152369, by decide⟩
    (prefixCache 12 18737) (prefixPartial 12 18737) = false := by
  decide +kernel

theorem node_context_12_18737_152369 : EJMOriginalGlobalDAGData.nodes 9 ⟨152369, by decide⟩ =
    .split (coordinate 12) (![⟨152316, by decide⟩,⟨152341, by decide⟩,⟨152360, by decide⟩,⟨152368, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18737_152369 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18737 ⟨152369, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18737
    ⟨152369, by decide⟩ (by decide) (![⟨152316, by decide⟩,⟨152341, by decide⟩,⟨152360, by decide⟩,⟨152368, by decide⟩]) unmarked_context_12_18737_152369 node_context_12_18737_152369
  intro a
  fin_cases a
  · exact context_13_74948_152316
  · exact context_13_74949_152341
  · exact context_13_74950_152360
  · exact context_13_74951_152368

theorem selected_cut_04764 : selected 8 ⟨152377, by decide⟩
    (prefixPartial 13 74952) = some ⟨13, 2, 0, 152377, 74952, 737, 16384⟩ := by
  decide +kernel

theorem context_13_74952_152377 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74952 ⟨152377, by decide⟩ :=
  accepted_of_selected 13 74952 ⟨152377, by decide⟩ ⟨13, 2, 0, 152377, 74952, 737, 16384⟩
    (by decide) selected_cut_04764

theorem selected_cut_04765 : selected 8 ⟨152416, by decide⟩
    (prefixPartial 13 74953) = some ⟨13, 2, 0, 152416, 74953, 2493, 16384⟩ := by
  decide +kernel

theorem context_13_74953_152416 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74953 ⟨152416, by decide⟩ :=
  accepted_of_selected 13 74953 ⟨152416, by decide⟩ ⟨13, 2, 0, 152416, 74953, 2493, 16384⟩
    (by decide) selected_cut_04765

theorem selected_cut_04766 : selected 8 ⟨152445, by decide⟩
    (prefixPartial 13 74954) = some ⟨13, 2, 0, 152445, 74954, 2037, 16384⟩ := by
  decide +kernel

theorem context_13_74954_152445 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74954 ⟨152445, by decide⟩ :=
  accepted_of_selected 13 74954 ⟨152445, by decide⟩ ⟨13, 2, 0, 152445, 74954, 2037, 16384⟩
    (by decide) selected_cut_04766

theorem selected_cut_04767 : selected 8 ⟨152456, by decide⟩
    (prefixPartial 13 74955) = some ⟨13, 2, 0, 152456, 74955, 989, 16384⟩ := by
  decide +kernel

theorem context_13_74955_152456 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74955 ⟨152456, by decide⟩ :=
  accepted_of_selected 13 74955 ⟨152456, by decide⟩ ⟨13, 2, 0, 152456, 74955, 989, 16384⟩
    (by decide) selected_cut_04767

theorem unmarked_context_12_18738_152457 : frontier 9 ⟨152457, by decide⟩
    (prefixCache 12 18738) (prefixPartial 12 18738) = false := by
  decide +kernel

theorem node_context_12_18738_152457 : EJMOriginalGlobalDAGData.nodes 9 ⟨152457, by decide⟩ =
    .split (coordinate 12) (![⟨152377, by decide⟩,⟨152416, by decide⟩,⟨152445, by decide⟩,⟨152456, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18738_152457 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18738 ⟨152457, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18738
    ⟨152457, by decide⟩ (by decide) (![⟨152377, by decide⟩,⟨152416, by decide⟩,⟨152445, by decide⟩,⟨152456, by decide⟩]) unmarked_context_12_18738_152457 node_context_12_18738_152457
  intro a
  fin_cases a
  · exact context_13_74952_152377
  · exact context_13_74953_152416
  · exact context_13_74954_152445
  · exact context_13_74955_152456

theorem selected_cut_04768 : selected 8 ⟨152470, by decide⟩
    (prefixPartial 13 74956) = some ⟨13, 2, 0, 152470, 74956, 845, 16384⟩ := by
  decide +kernel

theorem context_13_74956_152470 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74956 ⟨152470, by decide⟩ :=
  accepted_of_selected 13 74956 ⟨152470, by decide⟩ ⟨13, 2, 0, 152470, 74956, 845, 16384⟩
    (by decide) selected_cut_04768

theorem selected_cut_04769 : selected 8 ⟨152507, by decide⟩
    (prefixPartial 13 74957) = some ⟨13, 2, 0, 152507, 74957, 2537, 16384⟩ := by
  decide +kernel

theorem context_13_74957_152507 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74957 ⟨152507, by decide⟩ :=
  accepted_of_selected 13 74957 ⟨152507, by decide⟩ ⟨13, 2, 0, 152507, 74957, 2537, 16384⟩
    (by decide) selected_cut_04769

theorem selected_cut_04770 : selected 8 ⟨152532, by decide⟩
    (prefixPartial 13 74958) = some ⟨13, 2, 0, 152532, 74958, 2185, 16384⟩ := by
  decide +kernel

theorem context_13_74958_152532 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74958 ⟨152532, by decide⟩ :=
  accepted_of_selected 13 74958 ⟨152532, by decide⟩ ⟨13, 2, 0, 152532, 74958, 2185, 16384⟩
    (by decide) selected_cut_04770

theorem selected_cut_04771 : selected 8 ⟨152542, by decide⟩
    (prefixPartial 13 74959) = some ⟨13, 2, 0, 152542, 74959, 909, 16384⟩ := by
  decide +kernel

theorem context_13_74959_152542 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74959 ⟨152542, by decide⟩ :=
  accepted_of_selected 13 74959 ⟨152542, by decide⟩ ⟨13, 2, 0, 152542, 74959, 909, 16384⟩
    (by decide) selected_cut_04771

theorem unmarked_context_12_18739_152543 : frontier 9 ⟨152543, by decide⟩
    (prefixCache 12 18739) (prefixPartial 12 18739) = false := by
  decide +kernel

theorem node_context_12_18739_152543 : EJMOriginalGlobalDAGData.nodes 9 ⟨152543, by decide⟩ =
    .split (coordinate 12) (![⟨152470, by decide⟩,⟨152507, by decide⟩,⟨152532, by decide⟩,⟨152542, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18739_152543 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18739 ⟨152543, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18739
    ⟨152543, by decide⟩ (by decide) (![⟨152470, by decide⟩,⟨152507, by decide⟩,⟨152532, by decide⟩,⟨152542, by decide⟩]) unmarked_context_12_18739_152543 node_context_12_18739_152543
  intro a
  fin_cases a
  · exact context_13_74956_152470
  · exact context_13_74957_152507
  · exact context_13_74958_152532
  · exact context_13_74959_152542

theorem unmarked_context_11_4684_152544 : frontier 10 ⟨152544, by decide⟩
    (prefixCache 11 4684) (prefixPartial 11 4684) = false := by
  decide +kernel

theorem node_context_11_4684_152544 : EJMOriginalGlobalDAGData.nodes 10 ⟨152544, by decide⟩ =
    .split (coordinate 11) (![⟨152306, by decide⟩,⟨152369, by decide⟩,⟨152457, by decide⟩,⟨152543, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4684_152544 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4684 ⟨152544, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4684
    ⟨152544, by decide⟩ (by decide) (![⟨152306, by decide⟩,⟨152369, by decide⟩,⟨152457, by decide⟩,⟨152543, by decide⟩]) unmarked_context_11_4684_152544 node_context_11_4684_152544
  intro a
  fin_cases a
  · exact context_12_18736_152306
  · exact context_12_18737_152369
  · exact context_12_18738_152457
  · exact context_12_18739_152543

theorem selected_cut_04772 : selected 8 ⟨152550, by decide⟩
    (prefixPartial 13 74960) = some ⟨13, 2, 0, 152550, 74960, 517, 16384⟩ := by
  decide +kernel

theorem context_13_74960_152550 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74960 ⟨152550, by decide⟩ :=
  accepted_of_selected 13 74960 ⟨152550, by decide⟩ ⟨13, 2, 0, 152550, 74960, 517, 16384⟩
    (by decide) selected_cut_04772

theorem selected_cut_04773 : selected 8 ⟨152575, by decide⟩
    (prefixPartial 13 74961) = some ⟨13, 2, 0, 152575, 74961, 2385, 16384⟩ := by
  decide +kernel

theorem context_13_74961_152575 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74961 ⟨152575, by decide⟩ :=
  accepted_of_selected 13 74961 ⟨152575, by decide⟩ ⟨13, 2, 0, 152575, 74961, 2385, 16384⟩
    (by decide) selected_cut_04773

theorem selected_cut_04774 : selected 8 ⟨152598, by decide⟩
    (prefixPartial 13 74962) = some ⟨13, 2, 0, 152598, 74962, 1549, 16384⟩ := by
  decide +kernel

theorem context_13_74962_152598 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74962 ⟨152598, by decide⟩ :=
  accepted_of_selected 13 74962 ⟨152598, by decide⟩ ⟨13, 2, 0, 152598, 74962, 1549, 16384⟩
    (by decide) selected_cut_04774

theorem selected_cut_04775 : selected 8 ⟨152607, by decide⟩
    (prefixPartial 13 74963) = some ⟨13, 2, 0, 152607, 74963, 905, 16384⟩ := by
  decide +kernel

theorem context_13_74963_152607 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74963 ⟨152607, by decide⟩ :=
  accepted_of_selected 13 74963 ⟨152607, by decide⟩ ⟨13, 2, 0, 152607, 74963, 905, 16384⟩
    (by decide) selected_cut_04775

theorem unmarked_context_12_18740_152608 : frontier 9 ⟨152608, by decide⟩
    (prefixCache 12 18740) (prefixPartial 12 18740) = false := by
  decide +kernel

theorem node_context_12_18740_152608 : EJMOriginalGlobalDAGData.nodes 9 ⟨152608, by decide⟩ =
    .split (coordinate 12) (![⟨152550, by decide⟩,⟨152575, by decide⟩,⟨152598, by decide⟩,⟨152607, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18740_152608 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18740 ⟨152608, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18740
    ⟨152608, by decide⟩ (by decide) (![⟨152550, by decide⟩,⟨152575, by decide⟩,⟨152598, by decide⟩,⟨152607, by decide⟩]) unmarked_context_12_18740_152608 node_context_12_18740_152608
  intro a
  fin_cases a
  · exact context_13_74960_152550
  · exact context_13_74961_152575
  · exact context_13_74962_152598
  · exact context_13_74963_152607

theorem selected_cut_04776 : selected 8 ⟨152617, by decide⟩
    (prefixPartial 13 74964) = some ⟨13, 2, 0, 152617, 74964, 773, 16384⟩ := by
  decide +kernel

theorem context_13_74964_152617 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74964 ⟨152617, by decide⟩ :=
  accepted_of_selected 13 74964 ⟨152617, by decide⟩ ⟨13, 2, 0, 152617, 74964, 773, 16384⟩
    (by decide) selected_cut_04776

theorem selected_cut_04777 : selected 8 ⟨152657, by decide⟩
    (prefixPartial 13 74965) = some ⟨13, 2, 0, 152657, 74965, 3333, 16384⟩ := by
  decide +kernel

theorem context_13_74965_152657 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74965 ⟨152657, by decide⟩ :=
  accepted_of_selected 13 74965 ⟨152657, by decide⟩ ⟨13, 2, 0, 152657, 74965, 3333, 16384⟩
    (by decide) selected_cut_04777

theorem selected_cut_04778 : selected 8 ⟨152677, by decide⟩
    (prefixPartial 13 74966) = some ⟨13, 2, 0, 152677, 74966, 2237, 16384⟩ := by
  decide +kernel

theorem context_13_74966_152677 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74966 ⟨152677, by decide⟩ :=
  accepted_of_selected 13 74966 ⟨152677, by decide⟩ ⟨13, 2, 0, 152677, 74966, 2237, 16384⟩
    (by decide) selected_cut_04778

theorem selected_cut_04779 : selected 8 ⟨152682, by decide⟩
    (prefixPartial 13 74967) = some ⟨13, 2, 0, 152682, 74967, 1129, 16384⟩ := by
  decide +kernel

theorem context_13_74967_152682 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74967 ⟨152682, by decide⟩ :=
  accepted_of_selected 13 74967 ⟨152682, by decide⟩ ⟨13, 2, 0, 152682, 74967, 1129, 16384⟩
    (by decide) selected_cut_04779

theorem unmarked_context_12_18741_152683 : frontier 9 ⟨152683, by decide⟩
    (prefixCache 12 18741) (prefixPartial 12 18741) = false := by
  decide +kernel

theorem node_context_12_18741_152683 : EJMOriginalGlobalDAGData.nodes 9 ⟨152683, by decide⟩ =
    .split (coordinate 12) (![⟨152617, by decide⟩,⟨152657, by decide⟩,⟨152677, by decide⟩,⟨152682, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18741_152683 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18741 ⟨152683, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18741
    ⟨152683, by decide⟩ (by decide) (![⟨152617, by decide⟩,⟨152657, by decide⟩,⟨152677, by decide⟩,⟨152682, by decide⟩]) unmarked_context_12_18741_152683 node_context_12_18741_152683
  intro a
  fin_cases a
  · exact context_13_74964_152617
  · exact context_13_74965_152657
  · exact context_13_74966_152677
  · exact context_13_74967_152682

theorem selected_cut_04780 : selected 8 ⟨152693, by decide⟩
    (prefixPartial 13 74968) = some ⟨13, 2, 0, 152693, 74968, 521, 16384⟩ := by
  decide +kernel

theorem context_13_74968_152693 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74968 ⟨152693, by decide⟩ :=
  accepted_of_selected 13 74968 ⟨152693, by decide⟩ ⟨13, 2, 0, 152693, 74968, 521, 16384⟩
    (by decide) selected_cut_04780

theorem selected_cut_04781 : selected 8 ⟨152726, by decide⟩
    (prefixPartial 13 74969) = some ⟨13, 2, 0, 152726, 74969, 2665, 16384⟩ := by
  decide +kernel

theorem context_13_74969_152726 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74969 ⟨152726, by decide⟩ :=
  accepted_of_selected 13 74969 ⟨152726, by decide⟩ ⟨13, 2, 0, 152726, 74969, 2665, 16384⟩
    (by decide) selected_cut_04781

theorem selected_cut_04782 : selected 8 ⟨152748, by decide⟩
    (prefixPartial 13 74970) = some ⟨13, 2, 0, 152748, 74970, 1801, 16384⟩ := by
  decide +kernel

theorem context_13_74970_152748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74970 ⟨152748, by decide⟩ :=
  accepted_of_selected 13 74970 ⟨152748, by decide⟩ ⟨13, 2, 0, 152748, 74970, 1801, 16384⟩
    (by decide) selected_cut_04782

theorem selected_cut_04783 : selected 8 ⟨152755, by decide⟩
    (prefixPartial 13 74971) = some ⟨13, 2, 0, 152755, 74971, 945, 16384⟩ := by
  decide +kernel

theorem context_13_74971_152755 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74971 ⟨152755, by decide⟩ :=
  accepted_of_selected 13 74971 ⟨152755, by decide⟩ ⟨13, 2, 0, 152755, 74971, 945, 16384⟩
    (by decide) selected_cut_04783

theorem unmarked_context_12_18742_152756 : frontier 9 ⟨152756, by decide⟩
    (prefixCache 12 18742) (prefixPartial 12 18742) = false := by
  decide +kernel

theorem node_context_12_18742_152756 : EJMOriginalGlobalDAGData.nodes 9 ⟨152756, by decide⟩ =
    .split (coordinate 12) (![⟨152693, by decide⟩,⟨152726, by decide⟩,⟨152748, by decide⟩,⟨152755, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18742_152756 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18742 ⟨152756, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18742
    ⟨152756, by decide⟩ (by decide) (![⟨152693, by decide⟩,⟨152726, by decide⟩,⟨152748, by decide⟩,⟨152755, by decide⟩]) unmarked_context_12_18742_152756 node_context_12_18742_152756
  intro a
  fin_cases a
  · exact context_13_74968_152693
  · exact context_13_74969_152726
  · exact context_13_74970_152748
  · exact context_13_74971_152755

theorem selected_cut_04784 : selected 8 ⟨152767, by decide⟩
    (prefixPartial 13 74972) = some ⟨13, 2, 0, 152767, 74972, 505, 16384⟩ := by
  decide +kernel

theorem context_13_74972_152767 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74972 ⟨152767, by decide⟩ :=
  accepted_of_selected 13 74972 ⟨152767, by decide⟩ ⟨13, 2, 0, 152767, 74972, 505, 16384⟩
    (by decide) selected_cut_04784

theorem selected_cut_04785 : selected 8 ⟨152791, by decide⟩
    (prefixPartial 13 74973) = some ⟨13, 2, 0, 152791, 74973, 2669, 16384⟩ := by
  decide +kernel

theorem context_13_74973_152791 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74973 ⟨152791, by decide⟩ :=
  accepted_of_selected 13 74973 ⟨152791, by decide⟩ ⟨13, 2, 0, 152791, 74973, 2669, 16384⟩
    (by decide) selected_cut_04785

theorem selected_cut_04786 : selected 8 ⟨152809, by decide⟩
    (prefixPartial 13 74974) = some ⟨13, 2, 0, 152809, 74974, 1821, 16384⟩ := by
  decide +kernel

theorem context_13_74974_152809 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74974 ⟨152809, by decide⟩ :=
  accepted_of_selected 13 74974 ⟨152809, by decide⟩ ⟨13, 2, 0, 152809, 74974, 1821, 16384⟩
    (by decide) selected_cut_04786

theorem selected_cut_04787 : selected 8 ⟨152815, by decide⟩
    (prefixPartial 13 74975) = some ⟨13, 2, 0, 152815, 74975, 861, 16384⟩ := by
  decide +kernel

theorem context_13_74975_152815 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74975 ⟨152815, by decide⟩ :=
  accepted_of_selected 13 74975 ⟨152815, by decide⟩ ⟨13, 2, 0, 152815, 74975, 861, 16384⟩
    (by decide) selected_cut_04787

theorem unmarked_context_12_18743_152816 : frontier 9 ⟨152816, by decide⟩
    (prefixCache 12 18743) (prefixPartial 12 18743) = false := by
  decide +kernel

theorem node_context_12_18743_152816 : EJMOriginalGlobalDAGData.nodes 9 ⟨152816, by decide⟩ =
    .split (coordinate 12) (![⟨152767, by decide⟩,⟨152791, by decide⟩,⟨152809, by decide⟩,⟨152815, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18743_152816 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18743 ⟨152816, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18743
    ⟨152816, by decide⟩ (by decide) (![⟨152767, by decide⟩,⟨152791, by decide⟩,⟨152809, by decide⟩,⟨152815, by decide⟩]) unmarked_context_12_18743_152816 node_context_12_18743_152816
  intro a
  fin_cases a
  · exact context_13_74972_152767
  · exact context_13_74973_152791
  · exact context_13_74974_152809
  · exact context_13_74975_152815

theorem unmarked_context_11_4685_152817 : frontier 10 ⟨152817, by decide⟩
    (prefixCache 11 4685) (prefixPartial 11 4685) = false := by
  decide +kernel

theorem node_context_11_4685_152817 : EJMOriginalGlobalDAGData.nodes 10 ⟨152817, by decide⟩ =
    .split (coordinate 11) (![⟨152608, by decide⟩,⟨152683, by decide⟩,⟨152756, by decide⟩,⟨152816, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4685_152817 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4685 ⟨152817, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4685
    ⟨152817, by decide⟩ (by decide) (![⟨152608, by decide⟩,⟨152683, by decide⟩,⟨152756, by decide⟩,⟨152816, by decide⟩]) unmarked_context_11_4685_152817 node_context_11_4685_152817
  intro a
  fin_cases a
  · exact context_12_18740_152608
  · exact context_12_18741_152683
  · exact context_12_18742_152756
  · exact context_12_18743_152816

theorem selected_cut_04788 : selected 8 ⟨152823, by decide⟩
    (prefixPartial 13 74976) = some ⟨13, 2, 0, 152823, 74976, 461, 16384⟩ := by
  decide +kernel

theorem context_13_74976_152823 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74976 ⟨152823, by decide⟩ :=
  accepted_of_selected 13 74976 ⟨152823, by decide⟩ ⟨13, 2, 0, 152823, 74976, 461, 16384⟩
    (by decide) selected_cut_04788

theorem selected_cut_04789 : selected 8 ⟨152851, by decide⟩
    (prefixPartial 13 74977) = some ⟨13, 2, 0, 152851, 74977, 2965, 16384⟩ := by
  decide +kernel

theorem context_13_74977_152851 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74977 ⟨152851, by decide⟩ :=
  accepted_of_selected 13 74977 ⟨152851, by decide⟩ ⟨13, 2, 0, 152851, 74977, 2965, 16384⟩
    (by decide) selected_cut_04789

theorem selected_cut_04790 : selected 8 ⟨152873, by decide⟩
    (prefixPartial 13 74978) = some ⟨13, 2, 0, 152873, 74978, 1849, 16384⟩ := by
  decide +kernel

theorem context_13_74978_152873 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74978 ⟨152873, by decide⟩ :=
  accepted_of_selected 13 74978 ⟨152873, by decide⟩ ⟨13, 2, 0, 152873, 74978, 1849, 16384⟩
    (by decide) selected_cut_04790

theorem selected_cut_04791 : selected 8 ⟨152882, by decide⟩
    (prefixPartial 13 74979) = some ⟨13, 2, 0, 152882, 74979, 1009, 16384⟩ := by
  decide +kernel

theorem context_13_74979_152882 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74979 ⟨152882, by decide⟩ :=
  accepted_of_selected 13 74979 ⟨152882, by decide⟩ ⟨13, 2, 0, 152882, 74979, 1009, 16384⟩
    (by decide) selected_cut_04791

theorem unmarked_context_12_18744_152883 : frontier 9 ⟨152883, by decide⟩
    (prefixCache 12 18744) (prefixPartial 12 18744) = false := by
  decide +kernel

theorem node_context_12_18744_152883 : EJMOriginalGlobalDAGData.nodes 9 ⟨152883, by decide⟩ =
    .split (coordinate 12) (![⟨152823, by decide⟩,⟨152851, by decide⟩,⟨152873, by decide⟩,⟨152882, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18744_152883 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18744 ⟨152883, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18744
    ⟨152883, by decide⟩ (by decide) (![⟨152823, by decide⟩,⟨152851, by decide⟩,⟨152873, by decide⟩,⟨152882, by decide⟩]) unmarked_context_12_18744_152883 node_context_12_18744_152883
  intro a
  fin_cases a
  · exact context_13_74976_152823
  · exact context_13_74977_152851
  · exact context_13_74978_152873
  · exact context_13_74979_152882

theorem selected_cut_04792 : selected 8 ⟨152890, by decide⟩
    (prefixPartial 13 74980) = some ⟨13, 2, 0, 152890, 74980, 409, 16384⟩ := by
  decide +kernel

theorem context_13_74980_152890 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74980 ⟨152890, by decide⟩ :=
  accepted_of_selected 13 74980 ⟨152890, by decide⟩ ⟨13, 2, 0, 152890, 74980, 409, 16384⟩
    (by decide) selected_cut_04792

theorem selected_cut_04793 : selected 8 ⟨152921, by decide⟩
    (prefixPartial 13 74981) = some ⟨13, 2, 0, 152921, 74981, 2509, 16384⟩ := by
  decide +kernel

theorem context_13_74981_152921 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74981 ⟨152921, by decide⟩ :=
  accepted_of_selected 13 74981 ⟨152921, by decide⟩ ⟨13, 2, 0, 152921, 74981, 2509, 16384⟩
    (by decide) selected_cut_04793

theorem selected_cut_04794 : selected 8 ⟨152944, by decide⟩
    (prefixPartial 13 74982) = some ⟨13, 2, 0, 152944, 74982, 1905, 16384⟩ := by
  decide +kernel

theorem context_13_74982_152944 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74982 ⟨152944, by decide⟩ :=
  accepted_of_selected 13 74982 ⟨152944, by decide⟩ ⟨13, 2, 0, 152944, 74982, 1905, 16384⟩
    (by decide) selected_cut_04794

theorem selected_cut_04795 : selected 8 ⟨152953, by decide⟩
    (prefixPartial 13 74983) = some ⟨13, 2, 0, 152953, 74983, 989, 16384⟩ := by
  decide +kernel

theorem context_13_74983_152953 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74983 ⟨152953, by decide⟩ :=
  accepted_of_selected 13 74983 ⟨152953, by decide⟩ ⟨13, 2, 0, 152953, 74983, 989, 16384⟩
    (by decide) selected_cut_04795

theorem unmarked_context_12_18745_152954 : frontier 9 ⟨152954, by decide⟩
    (prefixCache 12 18745) (prefixPartial 12 18745) = false := by
  decide +kernel

theorem node_context_12_18745_152954 : EJMOriginalGlobalDAGData.nodes 9 ⟨152954, by decide⟩ =
    .split (coordinate 12) (![⟨152890, by decide⟩,⟨152921, by decide⟩,⟨152944, by decide⟩,⟨152953, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18745_152954 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18745 ⟨152954, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18745
    ⟨152954, by decide⟩ (by decide) (![⟨152890, by decide⟩,⟨152921, by decide⟩,⟨152944, by decide⟩,⟨152953, by decide⟩]) unmarked_context_12_18745_152954 node_context_12_18745_152954
  intro a
  fin_cases a
  · exact context_13_74980_152890
  · exact context_13_74981_152921
  · exact context_13_74982_152944
  · exact context_13_74983_152953

theorem selected_cut_04796 : selected 8 ⟨152959, by decide⟩
    (prefixPartial 13 74984) = some ⟨13, 2, 0, 152959, 74984, 317, 16384⟩ := by
  decide +kernel

theorem context_13_74984_152959 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74984 ⟨152959, by decide⟩ :=
  accepted_of_selected 13 74984 ⟨152959, by decide⟩ ⟨13, 2, 0, 152959, 74984, 317, 16384⟩
    (by decide) selected_cut_04796

theorem selected_cut_04797 : selected 8 ⟨152997, by decide⟩
    (prefixPartial 13 74985) = some ⟨13, 2, 0, 152997, 74985, 2773, 16384⟩ := by
  decide +kernel

theorem context_13_74985_152997 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74985 ⟨152997, by decide⟩ :=
  accepted_of_selected 13 74985 ⟨152997, by decide⟩ ⟨13, 2, 0, 152997, 74985, 2773, 16384⟩
    (by decide) selected_cut_04797

theorem selected_cut_04798 : selected 8 ⟨153020, by decide⟩
    (prefixPartial 13 74986) = some ⟨13, 2, 0, 153020, 74986, 1893, 16384⟩ := by
  decide +kernel

theorem context_13_74986_153020 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74986 ⟨153020, by decide⟩ :=
  accepted_of_selected 13 74986 ⟨153020, by decide⟩ ⟨13, 2, 0, 153020, 74986, 1893, 16384⟩
    (by decide) selected_cut_04798

theorem selected_cut_04799 : selected 8 ⟨153028, by decide⟩
    (prefixPartial 13 74987) = some ⟨13, 2, 0, 153028, 74987, 965, 16384⟩ := by
  decide +kernel

theorem context_13_74987_153028 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74987 ⟨153028, by decide⟩ :=
  accepted_of_selected 13 74987 ⟨153028, by decide⟩ ⟨13, 2, 0, 153028, 74987, 965, 16384⟩
    (by decide) selected_cut_04799

theorem unmarked_context_12_18746_153029 : frontier 9 ⟨153029, by decide⟩
    (prefixCache 12 18746) (prefixPartial 12 18746) = false := by
  decide +kernel

theorem node_context_12_18746_153029 : EJMOriginalGlobalDAGData.nodes 9 ⟨153029, by decide⟩ =
    .split (coordinate 12) (![⟨152959, by decide⟩,⟨152997, by decide⟩,⟨153020, by decide⟩,⟨153028, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18746_153029 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18746 ⟨153029, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18746
    ⟨153029, by decide⟩ (by decide) (![⟨152959, by decide⟩,⟨152997, by decide⟩,⟨153020, by decide⟩,⟨153028, by decide⟩]) unmarked_context_12_18746_153029 node_context_12_18746_153029
  intro a
  fin_cases a
  · exact context_13_74984_152959
  · exact context_13_74985_152997
  · exact context_13_74986_153020
  · exact context_13_74987_153028

theorem selected_cut_04800 : selected 8 ⟨153036, by decide⟩
    (prefixPartial 13 74988) = some ⟨13, 2, 0, 153036, 74988, 317, 16384⟩ := by
  decide +kernel

theorem context_13_74988_153036 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74988 ⟨153036, by decide⟩ :=
  accepted_of_selected 13 74988 ⟨153036, by decide⟩ ⟨13, 2, 0, 153036, 74988, 317, 16384⟩
    (by decide) selected_cut_04800

theorem selected_cut_04801 : selected 8 ⟨153076, by decide⟩
    (prefixPartial 13 74989) = some ⟨13, 2, 0, 153076, 74989, 3149, 16384⟩ := by
  decide +kernel

theorem context_13_74989_153076 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74989 ⟨153076, by decide⟩ :=
  accepted_of_selected 13 74989 ⟨153076, by decide⟩ ⟨13, 2, 0, 153076, 74989, 3149, 16384⟩
    (by decide) selected_cut_04801

theorem selected_cut_04802 : selected 8 ⟨153107, by decide⟩
    (prefixPartial 13 74990) = some ⟨13, 2, 0, 153107, 74990, 2153, 16384⟩ := by
  decide +kernel

theorem context_13_74990_153107 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74990 ⟨153107, by decide⟩ :=
  accepted_of_selected 13 74990 ⟨153107, by decide⟩ ⟨13, 2, 0, 153107, 74990, 2153, 16384⟩
    (by decide) selected_cut_04802

theorem selected_cut_04803 : selected 8 ⟨153114, by decide⟩
    (prefixPartial 13 74991) = some ⟨13, 2, 0, 153114, 74991, 1017, 16384⟩ := by
  decide +kernel

theorem context_13_74991_153114 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74991 ⟨153114, by decide⟩ :=
  accepted_of_selected 13 74991 ⟨153114, by decide⟩ ⟨13, 2, 0, 153114, 74991, 1017, 16384⟩
    (by decide) selected_cut_04803

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
