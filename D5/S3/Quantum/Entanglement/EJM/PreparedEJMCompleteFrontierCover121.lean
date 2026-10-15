/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover120
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_11618 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 102848) = some ⟨13, 1, 0, 3444, 102848, 1, 16384⟩ := by
  decide +kernel

theorem context_13_102848_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102848 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 102848 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 102848, 1, 16384⟩
    (by decide) selected_cut_11618

theorem selected_cut_11619 : selected 8 ⟨310415, by decide⟩
    (prefixPartial 13 102849) = some ⟨13, 2, 0, 310415, 102849, 1337, 16384⟩ := by
  decide +kernel

theorem context_13_102849_310415 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102849 ⟨310415, by decide⟩ :=
  accepted_of_selected 13 102849 ⟨310415, by decide⟩ ⟨13, 2, 0, 310415, 102849, 1337, 16384⟩
    (by decide) selected_cut_11619

theorem selected_cut_11620 : selected 8 ⟨310493, by decide⟩
    (prefixPartial 13 102850) = some ⟨13, 2, 0, 310493, 102850, 3069, 16384⟩ := by
  decide +kernel

theorem context_13_102850_310493 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102850 ⟨310493, by decide⟩ :=
  accepted_of_selected 13 102850 ⟨310493, by decide⟩ ⟨13, 2, 0, 310493, 102850, 3069, 16384⟩
    (by decide) selected_cut_11620

theorem selected_cut_11621 : selected 8 ⟨310515, by decide⟩
    (prefixPartial 13 102851) = some ⟨13, 2, 0, 310515, 102851, 1329, 16384⟩ := by
  decide +kernel

theorem context_13_102851_310515 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102851 ⟨310515, by decide⟩ :=
  accepted_of_selected 13 102851 ⟨310515, by decide⟩ ⟨13, 2, 0, 310515, 102851, 1329, 16384⟩
    (by decide) selected_cut_11621

theorem unmarked_context_12_25712_310516 : frontier 9 ⟨310516, by decide⟩
    (prefixCache 12 25712) (prefixPartial 12 25712) = false := by
  decide +kernel

theorem node_context_12_25712_310516 : EJMOriginalGlobalDAGData.nodes 9 ⟨310516, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨310415, by decide⟩,⟨310493, by decide⟩,⟨310515, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25712_310516 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25712 ⟨310516, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25712
    ⟨310516, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨310415, by decide⟩,⟨310493, by decide⟩,⟨310515, by decide⟩]) unmarked_context_12_25712_310516 node_context_12_25712_310516
  intro a
  fin_cases a
  · exact context_13_102848_3444
  · exact context_13_102849_310415
  · exact context_13_102850_310493
  · exact context_13_102851_310515

theorem selected_cut_11622 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 102852) = some ⟨13, 1, 0, 3444, 102852, 1, 16384⟩ := by
  decide +kernel

theorem context_13_102852_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102852 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 102852 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 102852, 1, 16384⟩
    (by decide) selected_cut_11622

theorem selected_cut_11623 : selected 8 ⟨310535, by decide⟩
    (prefixPartial 13 102853) = some ⟨13, 2, 0, 310535, 102853, 973, 16384⟩ := by
  decide +kernel

theorem context_13_102853_310535 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102853 ⟨310535, by decide⟩ :=
  accepted_of_selected 13 102853 ⟨310535, by decide⟩ ⟨13, 2, 0, 310535, 102853, 973, 16384⟩
    (by decide) selected_cut_11623

theorem selected_cut_11624 : selected 8 ⟨310587, by decide⟩
    (prefixPartial 13 102854) = some ⟨13, 2, 0, 310587, 102854, 2809, 16384⟩ := by
  decide +kernel

theorem context_13_102854_310587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102854 ⟨310587, by decide⟩ :=
  accepted_of_selected 13 102854 ⟨310587, by decide⟩ ⟨13, 2, 0, 310587, 102854, 2809, 16384⟩
    (by decide) selected_cut_11624

theorem selected_cut_11625 : selected 8 ⟨310602, by decide⟩
    (prefixPartial 13 102855) = some ⟨13, 2, 0, 310602, 102855, 1133, 16384⟩ := by
  decide +kernel

theorem context_13_102855_310602 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102855 ⟨310602, by decide⟩ :=
  accepted_of_selected 13 102855 ⟨310602, by decide⟩ ⟨13, 2, 0, 310602, 102855, 1133, 16384⟩
    (by decide) selected_cut_11625

theorem unmarked_context_12_25713_310603 : frontier 9 ⟨310603, by decide⟩
    (prefixCache 12 25713) (prefixPartial 12 25713) = false := by
  decide +kernel

theorem node_context_12_25713_310603 : EJMOriginalGlobalDAGData.nodes 9 ⟨310603, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨310535, by decide⟩,⟨310587, by decide⟩,⟨310602, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25713_310603 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25713 ⟨310603, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25713
    ⟨310603, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨310535, by decide⟩,⟨310587, by decide⟩,⟨310602, by decide⟩]) unmarked_context_12_25713_310603 node_context_12_25713_310603
  intro a
  fin_cases a
  · exact context_13_102852_3444
  · exact context_13_102853_310535
  · exact context_13_102854_310587
  · exact context_13_102855_310602

theorem selected_cut_11626 : selected 9 ⟨310644, by decide⟩
    (prefixPartial 12 25714) = some ⟨12, 2, 0, 310644, 25714, 3249, 65536⟩ := by
  decide +kernel

theorem context_12_25714_310644 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25714 ⟨310644, by decide⟩ :=
  accepted_of_selected 12 25714 ⟨310644, by decide⟩ ⟨12, 2, 0, 310644, 25714, 3249, 65536⟩
    (by decide) selected_cut_11626

theorem selected_cut_11627 : selected 9 ⟨310693, by decide⟩
    (prefixPartial 12 25715) = some ⟨12, 2, 0, 310693, 25715, 3593, 65536⟩ := by
  decide +kernel

theorem context_12_25715_310693 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25715 ⟨310693, by decide⟩ :=
  accepted_of_selected 12 25715 ⟨310693, by decide⟩ ⟨12, 2, 0, 310693, 25715, 3593, 65536⟩
    (by decide) selected_cut_11627

theorem unmarked_context_11_6428_310694 : frontier 10 ⟨310694, by decide⟩
    (prefixCache 11 6428) (prefixPartial 11 6428) = false := by
  decide +kernel

theorem node_context_11_6428_310694 : EJMOriginalGlobalDAGData.nodes 10 ⟨310694, by decide⟩ =
    .split (coordinate 11) (![⟨310516, by decide⟩,⟨310603, by decide⟩,⟨310644, by decide⟩,⟨310693, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6428_310694 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6428 ⟨310694, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6428
    ⟨310694, by decide⟩ (by decide) (![⟨310516, by decide⟩,⟨310603, by decide⟩,⟨310644, by decide⟩,⟨310693, by decide⟩]) unmarked_context_11_6428_310694 node_context_11_6428_310694
  intro a
  fin_cases a
  · exact context_12_25712_310516
  · exact context_12_25713_310603
  · exact context_12_25714_310644
  · exact context_12_25715_310693

theorem selected_cut_11628 : selected 9 ⟨310738, by decide⟩
    (prefixPartial 12 25716) = some ⟨12, 2, 0, 310738, 25716, 2941, 65536⟩ := by
  decide +kernel

theorem context_12_25716_310738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25716 ⟨310738, by decide⟩ :=
  accepted_of_selected 12 25716 ⟨310738, by decide⟩ ⟨12, 2, 0, 310738, 25716, 2941, 65536⟩
    (by decide) selected_cut_11628

theorem selected_cut_11629 : selected 9 ⟨310739, by decide⟩
    (prefixPartial 12 25717) = some ⟨12, 1, 0, 310739, 25717, 1, 65536⟩ := by
  decide +kernel

theorem context_12_25717_310739 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25717 ⟨310739, by decide⟩ :=
  accepted_of_selected 12 25717 ⟨310739, by decide⟩ ⟨12, 1, 0, 310739, 25717, 1, 65536⟩
    (by decide) selected_cut_11629

theorem selected_cut_11630 : selected 9 ⟨310781, by decide⟩
    (prefixPartial 12 25718) = some ⟨12, 2, 0, 310781, 25718, 3137, 65536⟩ := by
  decide +kernel

theorem context_12_25718_310781 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25718 ⟨310781, by decide⟩ :=
  accepted_of_selected 12 25718 ⟨310781, by decide⟩ ⟨12, 2, 0, 310781, 25718, 3137, 65536⟩
    (by decide) selected_cut_11630

theorem selected_cut_11631 : selected 9 ⟨310823, by decide⟩
    (prefixPartial 12 25719) = some ⟨12, 2, 0, 310823, 25719, 3425, 65536⟩ := by
  decide +kernel

theorem context_12_25719_310823 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25719 ⟨310823, by decide⟩ :=
  accepted_of_selected 12 25719 ⟨310823, by decide⟩ ⟨12, 2, 0, 310823, 25719, 3425, 65536⟩
    (by decide) selected_cut_11631

theorem unmarked_context_11_6429_310824 : frontier 10 ⟨310824, by decide⟩
    (prefixCache 11 6429) (prefixPartial 11 6429) = false := by
  decide +kernel

theorem node_context_11_6429_310824 : EJMOriginalGlobalDAGData.nodes 10 ⟨310824, by decide⟩ =
    .split (coordinate 11) (![⟨310738, by decide⟩,⟨310739, by decide⟩,⟨310781, by decide⟩,⟨310823, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6429_310824 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6429 ⟨310824, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6429
    ⟨310824, by decide⟩ (by decide) (![⟨310738, by decide⟩,⟨310739, by decide⟩,⟨310781, by decide⟩,⟨310823, by decide⟩]) unmarked_context_11_6429_310824 node_context_11_6429_310824
  intro a
  fin_cases a
  · exact context_12_25716_310738
  · exact context_12_25717_310739
  · exact context_12_25718_310781
  · exact context_12_25719_310823

theorem selected_cut_11632 : selected 9 ⟨310876, by decide⟩
    (prefixPartial 12 25720) = some ⟨12, 2, 0, 310876, 25720, 3593, 65536⟩ := by
  decide +kernel

theorem context_12_25720_310876 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25720 ⟨310876, by decide⟩ :=
  accepted_of_selected 12 25720 ⟨310876, by decide⟩ ⟨12, 2, 0, 310876, 25720, 3593, 65536⟩
    (by decide) selected_cut_11632

theorem selected_cut_11633 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 102884) = some ⟨13, 1, 0, 3444, 102884, 1, 16384⟩ := by
  decide +kernel

theorem context_13_102884_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102884 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 102884 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 102884, 1, 16384⟩
    (by decide) selected_cut_11633

theorem selected_cut_11634 : selected 8 ⟨310886, by decide⟩
    (prefixPartial 13 102885) = some ⟨13, 2, 0, 310886, 102885, 573, 16384⟩ := by
  decide +kernel

theorem context_13_102885_310886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102885 ⟨310886, by decide⟩ :=
  accepted_of_selected 13 102885 ⟨310886, by decide⟩ ⟨13, 2, 0, 310886, 102885, 573, 16384⟩
    (by decide) selected_cut_11634

theorem selected_cut_11635 : selected 8 ⟨310955, by decide⟩
    (prefixPartial 13 102886) = some ⟨13, 2, 0, 310955, 102886, 3057, 16384⟩ := by
  decide +kernel

theorem context_13_102886_310955 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102886 ⟨310955, by decide⟩ :=
  accepted_of_selected 13 102886 ⟨310955, by decide⟩ ⟨13, 2, 0, 310955, 102886, 3057, 16384⟩
    (by decide) selected_cut_11635

theorem selected_cut_11636 : selected 8 ⟨310975, by decide⟩
    (prefixPartial 13 102887) = some ⟨13, 2, 0, 310975, 102887, 1305, 16384⟩ := by
  decide +kernel

theorem context_13_102887_310975 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102887 ⟨310975, by decide⟩ :=
  accepted_of_selected 13 102887 ⟨310975, by decide⟩ ⟨13, 2, 0, 310975, 102887, 1305, 16384⟩
    (by decide) selected_cut_11636

theorem unmarked_context_12_25721_310976 : frontier 9 ⟨310976, by decide⟩
    (prefixCache 12 25721) (prefixPartial 12 25721) = false := by
  decide +kernel

theorem node_context_12_25721_310976 : EJMOriginalGlobalDAGData.nodes 9 ⟨310976, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨310886, by decide⟩,⟨310955, by decide⟩,⟨310975, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25721_310976 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25721 ⟨310976, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25721
    ⟨310976, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨310886, by decide⟩,⟨310955, by decide⟩,⟨310975, by decide⟩]) unmarked_context_12_25721_310976 node_context_12_25721_310976
  intro a
  fin_cases a
  · exact context_13_102884_3444
  · exact context_13_102885_310886
  · exact context_13_102886_310955
  · exact context_13_102887_310975

theorem selected_cut_11637 : selected 9 ⟨311029, by decide⟩
    (prefixPartial 12 25722) = some ⟨12, 2, 0, 311029, 25722, 3177, 65536⟩ := by
  decide +kernel

theorem context_12_25722_311029 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25722 ⟨311029, by decide⟩ :=
  accepted_of_selected 12 25722 ⟨311029, by decide⟩ ⟨12, 2, 0, 311029, 25722, 3177, 65536⟩
    (by decide) selected_cut_11637

theorem selected_cut_11638 : selected 9 ⟨311079, by decide⟩
    (prefixPartial 12 25723) = some ⟨12, 2, 0, 311079, 25723, 3657, 65536⟩ := by
  decide +kernel

theorem context_12_25723_311079 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25723 ⟨311079, by decide⟩ :=
  accepted_of_selected 12 25723 ⟨311079, by decide⟩ ⟨12, 2, 0, 311079, 25723, 3657, 65536⟩
    (by decide) selected_cut_11638

theorem unmarked_context_11_6430_311080 : frontier 10 ⟨311080, by decide⟩
    (prefixCache 11 6430) (prefixPartial 11 6430) = false := by
  decide +kernel

theorem node_context_11_6430_311080 : EJMOriginalGlobalDAGData.nodes 10 ⟨311080, by decide⟩ =
    .split (coordinate 11) (![⟨310876, by decide⟩,⟨310976, by decide⟩,⟨311029, by decide⟩,⟨311079, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6430_311080 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6430 ⟨311080, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6430
    ⟨311080, by decide⟩ (by decide) (![⟨310876, by decide⟩,⟨310976, by decide⟩,⟨311029, by decide⟩,⟨311079, by decide⟩]) unmarked_context_11_6430_311080 node_context_11_6430_311080
  intro a
  fin_cases a
  · exact context_12_25720_310876
  · exact context_12_25721_310976
  · exact context_12_25722_311029
  · exact context_12_25723_311079

theorem selected_cut_11639 : selected 9 ⟨311121, by decide⟩
    (prefixPartial 12 25724) = some ⟨12, 2, 0, 311121, 25724, 3017, 65536⟩ := by
  decide +kernel

theorem context_12_25724_311121 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25724 ⟨311121, by decide⟩ :=
  accepted_of_selected 12 25724 ⟨311121, by decide⟩ ⟨12, 2, 0, 311121, 25724, 3017, 65536⟩
    (by decide) selected_cut_11639

theorem selected_cut_11640 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 102900) = some ⟨13, 1, 0, 3444, 102900, 1, 16384⟩ := by
  decide +kernel

theorem context_13_102900_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102900 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 102900 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 102900, 1, 16384⟩
    (by decide) selected_cut_11640

theorem selected_cut_11641 : selected 8 ⟨311127, by decide⟩
    (prefixPartial 13 102901) = some ⟨13, 2, 0, 311127, 102901, 225, 16384⟩ := by
  decide +kernel

theorem context_13_102901_311127 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102901 ⟨311127, by decide⟩ :=
  accepted_of_selected 13 102901 ⟨311127, by decide⟩ ⟨13, 2, 0, 311127, 102901, 225, 16384⟩
    (by decide) selected_cut_11641

theorem selected_cut_11642 : selected 8 ⟨311176, by decide⟩
    (prefixPartial 13 102902) = some ⟨13, 2, 0, 311176, 102902, 2697, 16384⟩ := by
  decide +kernel

theorem context_13_102902_311176 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102902 ⟨311176, by decide⟩ :=
  accepted_of_selected 13 102902 ⟨311176, by decide⟩ ⟨13, 2, 0, 311176, 102902, 2697, 16384⟩
    (by decide) selected_cut_11642

theorem selected_cut_11643 : selected 8 ⟨311188, by decide⟩
    (prefixPartial 13 102903) = some ⟨13, 2, 0, 311188, 102903, 1209, 16384⟩ := by
  decide +kernel

theorem context_13_102903_311188 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102903 ⟨311188, by decide⟩ :=
  accepted_of_selected 13 102903 ⟨311188, by decide⟩ ⟨13, 2, 0, 311188, 102903, 1209, 16384⟩
    (by decide) selected_cut_11643

theorem unmarked_context_12_25725_311189 : frontier 9 ⟨311189, by decide⟩
    (prefixCache 12 25725) (prefixPartial 12 25725) = false := by
  decide +kernel

theorem node_context_12_25725_311189 : EJMOriginalGlobalDAGData.nodes 9 ⟨311189, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨311127, by decide⟩,⟨311176, by decide⟩,⟨311188, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25725_311189 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25725 ⟨311189, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25725
    ⟨311189, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨311127, by decide⟩,⟨311176, by decide⟩,⟨311188, by decide⟩]) unmarked_context_12_25725_311189 node_context_12_25725_311189
  intro a
  fin_cases a
  · exact context_13_102900_3444
  · exact context_13_102901_311127
  · exact context_13_102902_311176
  · exact context_13_102903_311188

theorem selected_cut_11644 : selected 9 ⟨311222, by decide⟩
    (prefixPartial 12 25726) = some ⟨12, 2, 0, 311222, 25726, 3013, 65536⟩ := by
  decide +kernel

theorem context_12_25726_311222 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25726 ⟨311222, by decide⟩ :=
  accepted_of_selected 12 25726 ⟨311222, by decide⟩ ⟨12, 2, 0, 311222, 25726, 3013, 65536⟩
    (by decide) selected_cut_11644

theorem selected_cut_11645 : selected 9 ⟨311256, by decide⟩
    (prefixPartial 12 25727) = some ⟨12, 2, 0, 311256, 25727, 3141, 65536⟩ := by
  decide +kernel

theorem context_12_25727_311256 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25727 ⟨311256, by decide⟩ :=
  accepted_of_selected 12 25727 ⟨311256, by decide⟩ ⟨12, 2, 0, 311256, 25727, 3141, 65536⟩
    (by decide) selected_cut_11645

theorem unmarked_context_11_6431_311257 : frontier 10 ⟨311257, by decide⟩
    (prefixCache 11 6431) (prefixPartial 11 6431) = false := by
  decide +kernel

theorem node_context_11_6431_311257 : EJMOriginalGlobalDAGData.nodes 10 ⟨311257, by decide⟩ =
    .split (coordinate 11) (![⟨311121, by decide⟩,⟨311189, by decide⟩,⟨311222, by decide⟩,⟨311256, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6431_311257 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6431 ⟨311257, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6431
    ⟨311257, by decide⟩ (by decide) (![⟨311121, by decide⟩,⟨311189, by decide⟩,⟨311222, by decide⟩,⟨311256, by decide⟩]) unmarked_context_11_6431_311257 node_context_11_6431_311257
  intro a
  fin_cases a
  · exact context_12_25724_311121
  · exact context_12_25725_311189
  · exact context_12_25726_311222
  · exact context_12_25727_311256

theorem unmarked_context_10_1607_311258 : frontier 11 ⟨311258, by decide⟩
    (prefixCache 10 1607) (prefixPartial 10 1607) = false := by
  decide +kernel

theorem node_context_10_1607_311258 : EJMOriginalGlobalDAGData.nodes 11 ⟨311258, by decide⟩ =
    .split (coordinate 10) (![⟨310694, by decide⟩,⟨310824, by decide⟩,⟨311080, by decide⟩,⟨311257, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1607_311258 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1607 ⟨311258, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1607
    ⟨311258, by decide⟩ (by decide) (![⟨310694, by decide⟩,⟨310824, by decide⟩,⟨311080, by decide⟩,⟨311257, by decide⟩]) unmarked_context_10_1607_311258 node_context_10_1607_311258
  intro a
  fin_cases a
  · exact context_11_6428_310694
  · exact context_11_6429_310824
  · exact context_11_6430_311080
  · exact context_11_6431_311257

theorem unmarked_context_9_401_311259 : frontier 12 ⟨311259, by decide⟩
    (prefixCache 9 401) (prefixPartial 9 401) = false := by
  decide +kernel

theorem node_context_9_401_311259 : EJMOriginalGlobalDAGData.nodes 12 ⟨311259, by decide⟩ =
    .split (coordinate 9) (![⟨308480, by decide⟩,⟨309460, by decide⟩,⟨310377, by decide⟩,⟨311258, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_401_311259 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 401 ⟨311259, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 401
    ⟨311259, by decide⟩ (by decide) (![⟨308480, by decide⟩,⟨309460, by decide⟩,⟨310377, by decide⟩,⟨311258, by decide⟩]) unmarked_context_9_401_311259 node_context_9_401_311259
  intro a
  fin_cases a
  · exact context_10_1604_308480
  · exact context_10_1605_309460
  · exact context_10_1606_310377
  · exact context_10_1607_311258

theorem selected_cut_11646 : selected 9 ⟨311342, by decide⟩
    (prefixPartial 12 25728) = some ⟨12, 2, 0, 311342, 25728, 1301, 65536⟩ := by
  decide +kernel

theorem context_12_25728_311342 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25728 ⟨311342, by decide⟩ :=
  accepted_of_selected 12 25728 ⟨311342, by decide⟩ ⟨12, 2, 0, 311342, 25728, 1301, 65536⟩
    (by decide) selected_cut_11646

theorem selected_cut_11647 : selected 9 ⟨311373, by decide⟩
    (prefixPartial 12 25729) = some ⟨12, 2, 0, 311373, 25729, 2229, 65536⟩ := by
  decide +kernel

theorem context_12_25729_311373 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25729 ⟨311373, by decide⟩ :=
  accepted_of_selected 12 25729 ⟨311373, by decide⟩ ⟨12, 2, 0, 311373, 25729, 2229, 65536⟩
    (by decide) selected_cut_11647

theorem selected_cut_11648 : selected 9 ⟨311404, by decide⟩
    (prefixPartial 12 25730) = some ⟨12, 2, 0, 311404, 25730, 2101, 65536⟩ := by
  decide +kernel

theorem context_12_25730_311404 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25730 ⟨311404, by decide⟩ :=
  accepted_of_selected 12 25730 ⟨311404, by decide⟩ ⟨12, 2, 0, 311404, 25730, 2101, 65536⟩
    (by decide) selected_cut_11648

theorem selected_cut_11649 : selected 9 ⟨311437, by decide⟩
    (prefixPartial 12 25731) = some ⟨12, 2, 0, 311437, 25731, 2277, 65536⟩ := by
  decide +kernel

theorem context_12_25731_311437 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25731 ⟨311437, by decide⟩ :=
  accepted_of_selected 12 25731 ⟨311437, by decide⟩ ⟨12, 2, 0, 311437, 25731, 2277, 65536⟩
    (by decide) selected_cut_11649

theorem unmarked_context_11_6432_311438 : frontier 10 ⟨311438, by decide⟩
    (prefixCache 11 6432) (prefixPartial 11 6432) = false := by
  decide +kernel

theorem node_context_11_6432_311438 : EJMOriginalGlobalDAGData.nodes 10 ⟨311438, by decide⟩ =
    .split (coordinate 11) (![⟨311342, by decide⟩,⟨311373, by decide⟩,⟨311404, by decide⟩,⟨311437, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6432_311438 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6432 ⟨311438, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6432
    ⟨311438, by decide⟩ (by decide) (![⟨311342, by decide⟩,⟨311373, by decide⟩,⟨311404, by decide⟩,⟨311437, by decide⟩]) unmarked_context_11_6432_311438 node_context_11_6432_311438
  intro a
  fin_cases a
  · exact context_12_25728_311342
  · exact context_12_25729_311373
  · exact context_12_25730_311404
  · exact context_12_25731_311437

theorem selected_cut_11650 : selected 9 ⟨311466, by decide⟩
    (prefixPartial 12 25732) = some ⟨12, 2, 0, 311466, 25732, 2281, 65536⟩ := by
  decide +kernel

theorem context_12_25732_311466 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25732 ⟨311466, by decide⟩ :=
  accepted_of_selected 12 25732 ⟨311466, by decide⟩ ⟨12, 2, 0, 311466, 25732, 2281, 65536⟩
    (by decide) selected_cut_11650

theorem selected_cut_11651 : selected 9 ⟨311492, by decide⟩
    (prefixPartial 12 25733) = some ⟨12, 2, 0, 311492, 25733, 2193, 65536⟩ := by
  decide +kernel

theorem context_12_25733_311492 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25733 ⟨311492, by decide⟩ :=
  accepted_of_selected 12 25733 ⟨311492, by decide⟩ ⟨12, 2, 0, 311492, 25733, 2193, 65536⟩
    (by decide) selected_cut_11651

theorem selected_cut_11652 : selected 9 ⟨311517, by decide⟩
    (prefixPartial 12 25734) = some ⟨12, 2, 0, 311517, 25734, 2133, 65536⟩ := by
  decide +kernel

theorem context_12_25734_311517 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25734 ⟨311517, by decide⟩ :=
  accepted_of_selected 12 25734 ⟨311517, by decide⟩ ⟨12, 2, 0, 311517, 25734, 2133, 65536⟩
    (by decide) selected_cut_11652

theorem selected_cut_11653 : selected 9 ⟨311548, by decide⟩
    (prefixPartial 12 25735) = some ⟨12, 2, 0, 311548, 25735, 2337, 65536⟩ := by
  decide +kernel

theorem context_12_25735_311548 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25735 ⟨311548, by decide⟩ :=
  accepted_of_selected 12 25735 ⟨311548, by decide⟩ ⟨12, 2, 0, 311548, 25735, 2337, 65536⟩
    (by decide) selected_cut_11653

theorem unmarked_context_11_6433_311549 : frontier 10 ⟨311549, by decide⟩
    (prefixCache 11 6433) (prefixPartial 11 6433) = false := by
  decide +kernel

theorem node_context_11_6433_311549 : EJMOriginalGlobalDAGData.nodes 10 ⟨311549, by decide⟩ =
    .split (coordinate 11) (![⟨311466, by decide⟩,⟨311492, by decide⟩,⟨311517, by decide⟩,⟨311548, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6433_311549 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6433 ⟨311549, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6433
    ⟨311549, by decide⟩ (by decide) (![⟨311466, by decide⟩,⟨311492, by decide⟩,⟨311517, by decide⟩,⟨311548, by decide⟩]) unmarked_context_11_6433_311549 node_context_11_6433_311549
  intro a
  fin_cases a
  · exact context_12_25732_311466
  · exact context_12_25733_311492
  · exact context_12_25734_311517
  · exact context_12_25735_311548

theorem selected_cut_11654 : selected 9 ⟨311595, by decide⟩
    (prefixPartial 12 25736) = some ⟨12, 2, 0, 311595, 25736, 2673, 65536⟩ := by
  decide +kernel

theorem context_12_25736_311595 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25736 ⟨311595, by decide⟩ :=
  accepted_of_selected 12 25736 ⟨311595, by decide⟩ ⟨12, 2, 0, 311595, 25736, 2673, 65536⟩
    (by decide) selected_cut_11654

theorem selected_cut_11655 : selected 9 ⟨311627, by decide⟩
    (prefixPartial 12 25737) = some ⟨12, 2, 0, 311627, 25737, 2349, 65536⟩ := by
  decide +kernel

theorem context_12_25737_311627 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25737 ⟨311627, by decide⟩ :=
  accepted_of_selected 12 25737 ⟨311627, by decide⟩ ⟨12, 2, 0, 311627, 25737, 2349, 65536⟩
    (by decide) selected_cut_11655

theorem selected_cut_11656 : selected 9 ⟨311664, by decide⟩
    (prefixPartial 12 25738) = some ⟨12, 2, 0, 311664, 25738, 2205, 65536⟩ := by
  decide +kernel

theorem context_12_25738_311664 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25738 ⟨311664, by decide⟩ :=
  accepted_of_selected 12 25738 ⟨311664, by decide⟩ ⟨12, 2, 0, 311664, 25738, 2205, 65536⟩
    (by decide) selected_cut_11656

theorem selected_cut_11657 : selected 9 ⟨311699, by decide⟩
    (prefixPartial 12 25739) = some ⟨12, 2, 0, 311699, 25739, 2517, 65536⟩ := by
  decide +kernel

theorem context_12_25739_311699 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25739 ⟨311699, by decide⟩ :=
  accepted_of_selected 12 25739 ⟨311699, by decide⟩ ⟨12, 2, 0, 311699, 25739, 2517, 65536⟩
    (by decide) selected_cut_11657

theorem unmarked_context_11_6434_311700 : frontier 10 ⟨311700, by decide⟩
    (prefixCache 11 6434) (prefixPartial 11 6434) = false := by
  decide +kernel

theorem node_context_11_6434_311700 : EJMOriginalGlobalDAGData.nodes 10 ⟨311700, by decide⟩ =
    .split (coordinate 11) (![⟨311595, by decide⟩,⟨311627, by decide⟩,⟨311664, by decide⟩,⟨311699, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6434_311700 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6434 ⟨311700, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6434
    ⟨311700, by decide⟩ (by decide) (![⟨311595, by decide⟩,⟨311627, by decide⟩,⟨311664, by decide⟩,⟨311699, by decide⟩]) unmarked_context_11_6434_311700 node_context_11_6434_311700
  intro a
  fin_cases a
  · exact context_12_25736_311595
  · exact context_12_25737_311627
  · exact context_12_25738_311664
  · exact context_12_25739_311699

theorem selected_cut_11658 : selected 9 ⟨311732, by decide⟩
    (prefixPartial 12 25740) = some ⟨12, 2, 0, 311732, 25740, 2121, 65536⟩ := by
  decide +kernel

theorem context_12_25740_311732 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25740 ⟨311732, by decide⟩ :=
  accepted_of_selected 12 25740 ⟨311732, by decide⟩ ⟨12, 2, 0, 311732, 25740, 2121, 65536⟩
    (by decide) selected_cut_11658

theorem selected_cut_11659 : selected 9 ⟨311767, by decide⟩
    (prefixPartial 12 25741) = some ⟨12, 2, 0, 311767, 25741, 1969, 65536⟩ := by
  decide +kernel

theorem context_12_25741_311767 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25741 ⟨311767, by decide⟩ :=
  accepted_of_selected 12 25741 ⟨311767, by decide⟩ ⟨12, 2, 0, 311767, 25741, 1969, 65536⟩
    (by decide) selected_cut_11659

theorem selected_cut_11660 : selected 9 ⟨311794, by decide⟩
    (prefixPartial 12 25742) = some ⟨12, 2, 0, 311794, 25742, 1977, 65536⟩ := by
  decide +kernel

theorem context_12_25742_311794 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25742 ⟨311794, by decide⟩ :=
  accepted_of_selected 12 25742 ⟨311794, by decide⟩ ⟨12, 2, 0, 311794, 25742, 1977, 65536⟩
    (by decide) selected_cut_11660

theorem selected_cut_11661 : selected 9 ⟨311826, by decide⟩
    (prefixPartial 12 25743) = some ⟨12, 2, 0, 311826, 25743, 2129, 65536⟩ := by
  decide +kernel

theorem context_12_25743_311826 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25743 ⟨311826, by decide⟩ :=
  accepted_of_selected 12 25743 ⟨311826, by decide⟩ ⟨12, 2, 0, 311826, 25743, 2129, 65536⟩
    (by decide) selected_cut_11661

theorem unmarked_context_11_6435_311827 : frontier 10 ⟨311827, by decide⟩
    (prefixCache 11 6435) (prefixPartial 11 6435) = false := by
  decide +kernel

theorem node_context_11_6435_311827 : EJMOriginalGlobalDAGData.nodes 10 ⟨311827, by decide⟩ =
    .split (coordinate 11) (![⟨311732, by decide⟩,⟨311767, by decide⟩,⟨311794, by decide⟩,⟨311826, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6435_311827 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6435 ⟨311827, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6435
    ⟨311827, by decide⟩ (by decide) (![⟨311732, by decide⟩,⟨311767, by decide⟩,⟨311794, by decide⟩,⟨311826, by decide⟩]) unmarked_context_11_6435_311827 node_context_11_6435_311827
  intro a
  fin_cases a
  · exact context_12_25740_311732
  · exact context_12_25741_311767
  · exact context_12_25742_311794
  · exact context_12_25743_311826

theorem unmarked_context_10_1608_311828 : frontier 11 ⟨311828, by decide⟩
    (prefixCache 10 1608) (prefixPartial 10 1608) = false := by
  decide +kernel

theorem node_context_10_1608_311828 : EJMOriginalGlobalDAGData.nodes 11 ⟨311828, by decide⟩ =
    .split (coordinate 10) (![⟨311438, by decide⟩,⟨311549, by decide⟩,⟨311700, by decide⟩,⟨311827, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1608_311828 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1608 ⟨311828, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1608
    ⟨311828, by decide⟩ (by decide) (![⟨311438, by decide⟩,⟨311549, by decide⟩,⟨311700, by decide⟩,⟨311827, by decide⟩]) unmarked_context_10_1608_311828 node_context_10_1608_311828
  intro a
  fin_cases a
  · exact context_11_6432_311438
  · exact context_11_6433_311549
  · exact context_11_6434_311700
  · exact context_11_6435_311827

theorem selected_cut_11662 : selected 9 ⟨311885, by decide⟩
    (prefixPartial 12 25744) = some ⟨12, 2, 0, 311885, 25744, 3293, 65536⟩ := by
  decide +kernel

theorem context_12_25744_311885 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25744 ⟨311885, by decide⟩ :=
  accepted_of_selected 12 25744 ⟨311885, by decide⟩ ⟨12, 2, 0, 311885, 25744, 3293, 65536⟩
    (by decide) selected_cut_11662

theorem selected_cut_11663 : selected 9 ⟨311912, by decide⟩
    (prefixPartial 12 25745) = some ⟨12, 2, 0, 311912, 25745, 2293, 65536⟩ := by
  decide +kernel

theorem context_12_25745_311912 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25745 ⟨311912, by decide⟩ :=
  accepted_of_selected 12 25745 ⟨311912, by decide⟩ ⟨12, 2, 0, 311912, 25745, 2293, 65536⟩
    (by decide) selected_cut_11663

theorem selected_cut_11664 : selected 9 ⟨311938, by decide⟩
    (prefixPartial 12 25746) = some ⟨12, 2, 0, 311938, 25746, 2245, 65536⟩ := by
  decide +kernel

theorem context_12_25746_311938 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25746 ⟨311938, by decide⟩ :=
  accepted_of_selected 12 25746 ⟨311938, by decide⟩ ⟨12, 2, 0, 311938, 25746, 2245, 65536⟩
    (by decide) selected_cut_11664

theorem selected_cut_11665 : selected 9 ⟨311967, by decide⟩
    (prefixPartial 12 25747) = some ⟨12, 2, 0, 311967, 25747, 2213, 65536⟩ := by
  decide +kernel

theorem context_12_25747_311967 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25747 ⟨311967, by decide⟩ :=
  accepted_of_selected 12 25747 ⟨311967, by decide⟩ ⟨12, 2, 0, 311967, 25747, 2213, 65536⟩
    (by decide) selected_cut_11665

theorem unmarked_context_11_6436_311968 : frontier 10 ⟨311968, by decide⟩
    (prefixCache 11 6436) (prefixPartial 11 6436) = false := by
  decide +kernel

theorem node_context_11_6436_311968 : EJMOriginalGlobalDAGData.nodes 10 ⟨311968, by decide⟩ =
    .split (coordinate 11) (![⟨311885, by decide⟩,⟨311912, by decide⟩,⟨311938, by decide⟩,⟨311967, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6436_311968 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6436 ⟨311968, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6436
    ⟨311968, by decide⟩ (by decide) (![⟨311885, by decide⟩,⟨311912, by decide⟩,⟨311938, by decide⟩,⟨311967, by decide⟩]) unmarked_context_11_6436_311968 node_context_11_6436_311968
  intro a
  fin_cases a
  · exact context_12_25744_311885
  · exact context_12_25745_311912
  · exact context_12_25746_311938
  · exact context_12_25747_311967

theorem selected_cut_11666 : selected 9 ⟨312001, by decide⟩
    (prefixPartial 12 25748) = some ⟨12, 2, 0, 312001, 25748, 2681, 65536⟩ := by
  decide +kernel

theorem context_12_25748_312001 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25748 ⟨312001, by decide⟩ :=
  accepted_of_selected 12 25748 ⟨312001, by decide⟩ ⟨12, 2, 0, 312001, 25748, 2681, 65536⟩
    (by decide) selected_cut_11666

theorem selected_cut_11667 : selected 9 ⟨312048, by decide⟩
    (prefixPartial 12 25749) = some ⟨12, 2, 0, 312048, 25749, 889, 65536⟩ := by
  decide +kernel

theorem context_12_25749_312048 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25749 ⟨312048, by decide⟩ :=
  accepted_of_selected 12 25749 ⟨312048, by decide⟩ ⟨12, 2, 0, 312048, 25749, 889, 65536⟩
    (by decide) selected_cut_11667

theorem selected_cut_11668 : selected 9 ⟨312079, by decide⟩
    (prefixPartial 12 25750) = some ⟨12, 2, 0, 312079, 25750, 2845, 65536⟩ := by
  decide +kernel

theorem context_12_25750_312079 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25750 ⟨312079, by decide⟩ :=
  accepted_of_selected 12 25750 ⟨312079, by decide⟩ ⟨12, 2, 0, 312079, 25750, 2845, 65536⟩
    (by decide) selected_cut_11668

theorem selected_cut_11669 : selected 9 ⟨312119, by decide⟩
    (prefixPartial 12 25751) = some ⟨12, 2, 0, 312119, 25751, 2997, 65536⟩ := by
  decide +kernel

theorem context_12_25751_312119 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25751 ⟨312119, by decide⟩ :=
  accepted_of_selected 12 25751 ⟨312119, by decide⟩ ⟨12, 2, 0, 312119, 25751, 2997, 65536⟩
    (by decide) selected_cut_11669

theorem unmarked_context_11_6437_312120 : frontier 10 ⟨312120, by decide⟩
    (prefixCache 11 6437) (prefixPartial 11 6437) = false := by
  decide +kernel

theorem node_context_11_6437_312120 : EJMOriginalGlobalDAGData.nodes 10 ⟨312120, by decide⟩ =
    .split (coordinate 11) (![⟨312001, by decide⟩,⟨312048, by decide⟩,⟨312079, by decide⟩,⟨312119, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6437_312120 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6437 ⟨312120, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6437
    ⟨312120, by decide⟩ (by decide) (![⟨312001, by decide⟩,⟨312048, by decide⟩,⟨312079, by decide⟩,⟨312119, by decide⟩]) unmarked_context_11_6437_312120 node_context_11_6437_312120
  intro a
  fin_cases a
  · exact context_12_25748_312001
  · exact context_12_25749_312048
  · exact context_12_25750_312079
  · exact context_12_25751_312119

theorem selected_cut_11670 : selected 9 ⟨312152, by decide⟩
    (prefixPartial 12 25752) = some ⟨12, 2, 0, 312152, 25752, 2277, 65536⟩ := by
  decide +kernel

theorem context_12_25752_312152 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25752 ⟨312152, by decide⟩ :=
  accepted_of_selected 12 25752 ⟨312152, by decide⟩ ⟨12, 2, 0, 312152, 25752, 2277, 65536⟩
    (by decide) selected_cut_11670

theorem selected_cut_11671 : selected 9 ⟨312180, by decide⟩
    (prefixPartial 12 25753) = some ⟨12, 2, 0, 312180, 25753, 2301, 65536⟩ := by
  decide +kernel

theorem context_12_25753_312180 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25753 ⟨312180, by decide⟩ :=
  accepted_of_selected 12 25753 ⟨312180, by decide⟩ ⟨12, 2, 0, 312180, 25753, 2301, 65536⟩
    (by decide) selected_cut_11671

theorem selected_cut_11672 : selected 9 ⟨312204, by decide⟩
    (prefixPartial 12 25754) = some ⟨12, 2, 0, 312204, 25754, 2205, 65536⟩ := by
  decide +kernel

theorem context_12_25754_312204 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25754 ⟨312204, by decide⟩ :=
  accepted_of_selected 12 25754 ⟨312204, by decide⟩ ⟨12, 2, 0, 312204, 25754, 2205, 65536⟩
    (by decide) selected_cut_11672

theorem selected_cut_11673 : selected 9 ⟨312236, by decide⟩
    (prefixPartial 12 25755) = some ⟨12, 2, 0, 312236, 25755, 2325, 65536⟩ := by
  decide +kernel

theorem context_12_25755_312236 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25755 ⟨312236, by decide⟩ :=
  accepted_of_selected 12 25755 ⟨312236, by decide⟩ ⟨12, 2, 0, 312236, 25755, 2325, 65536⟩
    (by decide) selected_cut_11673

theorem unmarked_context_11_6438_312237 : frontier 10 ⟨312237, by decide⟩
    (prefixCache 11 6438) (prefixPartial 11 6438) = false := by
  decide +kernel

theorem node_context_11_6438_312237 : EJMOriginalGlobalDAGData.nodes 10 ⟨312237, by decide⟩ =
    .split (coordinate 11) (![⟨312152, by decide⟩,⟨312180, by decide⟩,⟨312204, by decide⟩,⟨312236, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6438_312237 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6438 ⟨312237, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6438
    ⟨312237, by decide⟩ (by decide) (![⟨312152, by decide⟩,⟨312180, by decide⟩,⟨312204, by decide⟩,⟨312236, by decide⟩]) unmarked_context_11_6438_312237 node_context_11_6438_312237
  intro a
  fin_cases a
  · exact context_12_25752_312152
  · exact context_12_25753_312180
  · exact context_12_25754_312204
  · exact context_12_25755_312236

theorem selected_cut_11674 : selected 9 ⟨312261, by decide⟩
    (prefixPartial 12 25756) = some ⟨12, 2, 0, 312261, 25756, 1785, 65536⟩ := by
  decide +kernel

theorem context_12_25756_312261 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25756 ⟨312261, by decide⟩ :=
  accepted_of_selected 12 25756 ⟨312261, by decide⟩ ⟨12, 2, 0, 312261, 25756, 1785, 65536⟩
    (by decide) selected_cut_11674

theorem selected_cut_11675 : selected 9 ⟨312286, by decide⟩
    (prefixPartial 12 25757) = some ⟨12, 2, 0, 312286, 25757, 1949, 65536⟩ := by
  decide +kernel

theorem context_12_25757_312286 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25757 ⟨312286, by decide⟩ :=
  accepted_of_selected 12 25757 ⟨312286, by decide⟩ ⟨12, 2, 0, 312286, 25757, 1949, 65536⟩
    (by decide) selected_cut_11675

theorem selected_cut_11676 : selected 9 ⟨312307, by decide⟩
    (prefixPartial 12 25758) = some ⟨12, 2, 0, 312307, 25758, 1957, 65536⟩ := by
  decide +kernel

theorem context_12_25758_312307 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25758 ⟨312307, by decide⟩ :=
  accepted_of_selected 12 25758 ⟨312307, by decide⟩ ⟨12, 2, 0, 312307, 25758, 1957, 65536⟩
    (by decide) selected_cut_11676

theorem selected_cut_11677 : selected 9 ⟨312327, by decide⟩
    (prefixPartial 12 25759) = some ⟨12, 2, 0, 312327, 25759, 1925, 65536⟩ := by
  decide +kernel

theorem context_12_25759_312327 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25759 ⟨312327, by decide⟩ :=
  accepted_of_selected 12 25759 ⟨312327, by decide⟩ ⟨12, 2, 0, 312327, 25759, 1925, 65536⟩
    (by decide) selected_cut_11677

theorem unmarked_context_11_6439_312328 : frontier 10 ⟨312328, by decide⟩
    (prefixCache 11 6439) (prefixPartial 11 6439) = false := by
  decide +kernel

theorem node_context_11_6439_312328 : EJMOriginalGlobalDAGData.nodes 10 ⟨312328, by decide⟩ =
    .split (coordinate 11) (![⟨312261, by decide⟩,⟨312286, by decide⟩,⟨312307, by decide⟩,⟨312327, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6439_312328 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6439 ⟨312328, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6439
    ⟨312328, by decide⟩ (by decide) (![⟨312261, by decide⟩,⟨312286, by decide⟩,⟨312307, by decide⟩,⟨312327, by decide⟩]) unmarked_context_11_6439_312328 node_context_11_6439_312328
  intro a
  fin_cases a
  · exact context_12_25756_312261
  · exact context_12_25757_312286
  · exact context_12_25758_312307
  · exact context_12_25759_312327

theorem unmarked_context_10_1609_312329 : frontier 11 ⟨312329, by decide⟩
    (prefixCache 10 1609) (prefixPartial 10 1609) = false := by
  decide +kernel

theorem node_context_10_1609_312329 : EJMOriginalGlobalDAGData.nodes 11 ⟨312329, by decide⟩ =
    .split (coordinate 10) (![⟨311968, by decide⟩,⟨312120, by decide⟩,⟨312237, by decide⟩,⟨312328, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1609_312329 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1609 ⟨312329, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1609
    ⟨312329, by decide⟩ (by decide) (![⟨311968, by decide⟩,⟨312120, by decide⟩,⟨312237, by decide⟩,⟨312328, by decide⟩]) unmarked_context_10_1609_312329 node_context_10_1609_312329
  intro a
  fin_cases a
  · exact context_11_6436_311968
  · exact context_11_6437_312120
  · exact context_11_6438_312237
  · exact context_11_6439_312328

theorem selected_cut_11678 : selected 9 ⟨312356, by decide⟩
    (prefixPartial 12 25760) = some ⟨12, 2, 0, 312356, 25760, 2413, 65536⟩ := by
  decide +kernel

theorem context_12_25760_312356 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25760 ⟨312356, by decide⟩ :=
  accepted_of_selected 12 25760 ⟨312356, by decide⟩ ⟨12, 2, 0, 312356, 25760, 2413, 65536⟩
    (by decide) selected_cut_11678

theorem selected_cut_11679 : selected 9 ⟨312379, by decide⟩
    (prefixPartial 12 25761) = some ⟨12, 2, 0, 312379, 25761, 1665, 65536⟩ := by
  decide +kernel

theorem context_12_25761_312379 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25761 ⟨312379, by decide⟩ :=
  accepted_of_selected 12 25761 ⟨312379, by decide⟩ ⟨12, 2, 0, 312379, 25761, 1665, 65536⟩
    (by decide) selected_cut_11679

theorem selected_cut_11680 : selected 9 ⟨312402, by decide⟩
    (prefixPartial 12 25762) = some ⟨12, 2, 0, 312402, 25762, 1485, 65536⟩ := by
  decide +kernel

theorem context_12_25762_312402 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25762 ⟨312402, by decide⟩ :=
  accepted_of_selected 12 25762 ⟨312402, by decide⟩ ⟨12, 2, 0, 312402, 25762, 1485, 65536⟩
    (by decide) selected_cut_11680

theorem selected_cut_11681 : selected 9 ⟨312423, by decide⟩
    (prefixPartial 12 25763) = some ⟨12, 2, 0, 312423, 25763, 1453, 65536⟩ := by
  decide +kernel

theorem context_12_25763_312423 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25763 ⟨312423, by decide⟩ :=
  accepted_of_selected 12 25763 ⟨312423, by decide⟩ ⟨12, 2, 0, 312423, 25763, 1453, 65536⟩
    (by decide) selected_cut_11681

theorem unmarked_context_11_6440_312424 : frontier 10 ⟨312424, by decide⟩
    (prefixCache 11 6440) (prefixPartial 11 6440) = false := by
  decide +kernel

theorem node_context_11_6440_312424 : EJMOriginalGlobalDAGData.nodes 10 ⟨312424, by decide⟩ =
    .split (coordinate 11) (![⟨312356, by decide⟩,⟨312379, by decide⟩,⟨312402, by decide⟩,⟨312423, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6440_312424 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6440 ⟨312424, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6440
    ⟨312424, by decide⟩ (by decide) (![⟨312356, by decide⟩,⟨312379, by decide⟩,⟨312402, by decide⟩,⟨312423, by decide⟩]) unmarked_context_11_6440_312424 node_context_11_6440_312424
  intro a
  fin_cases a
  · exact context_12_25760_312356
  · exact context_12_25761_312379
  · exact context_12_25762_312402
  · exact context_12_25763_312423

theorem selected_cut_11682 : selected 9 ⟨312443, by decide⟩
    (prefixPartial 12 25764) = some ⟨12, 2, 0, 312443, 25764, 1381, 65536⟩ := by
  decide +kernel

theorem context_12_25764_312443 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25764 ⟨312443, by decide⟩ :=
  accepted_of_selected 12 25764 ⟨312443, by decide⟩ ⟨12, 2, 0, 312443, 25764, 1381, 65536⟩
    (by decide) selected_cut_11682

theorem selected_cut_11683 : selected 9 ⟨312463, by decide⟩
    (prefixPartial 12 25765) = some ⟨12, 2, 0, 312463, 25765, 1533, 65536⟩ := by
  decide +kernel

theorem context_12_25765_312463 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25765 ⟨312463, by decide⟩ :=
  accepted_of_selected 12 25765 ⟨312463, by decide⟩ ⟨12, 2, 0, 312463, 25765, 1533, 65536⟩
    (by decide) selected_cut_11683

theorem selected_cut_11684 : selected 9 ⟨312481, by decide⟩
    (prefixPartial 12 25766) = some ⟨12, 2, 0, 312481, 25766, 1397, 65536⟩ := by
  decide +kernel

theorem context_12_25766_312481 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25766 ⟨312481, by decide⟩ :=
  accepted_of_selected 12 25766 ⟨312481, by decide⟩ ⟨12, 2, 0, 312481, 25766, 1397, 65536⟩
    (by decide) selected_cut_11684

theorem selected_cut_11685 : selected 9 ⟨312503, by decide⟩
    (prefixPartial 12 25767) = some ⟨12, 2, 0, 312503, 25767, 1469, 65536⟩ := by
  decide +kernel

theorem context_12_25767_312503 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25767 ⟨312503, by decide⟩ :=
  accepted_of_selected 12 25767 ⟨312503, by decide⟩ ⟨12, 2, 0, 312503, 25767, 1469, 65536⟩
    (by decide) selected_cut_11685

theorem unmarked_context_11_6441_312504 : frontier 10 ⟨312504, by decide⟩
    (prefixCache 11 6441) (prefixPartial 11 6441) = false := by
  decide +kernel

theorem node_context_11_6441_312504 : EJMOriginalGlobalDAGData.nodes 10 ⟨312504, by decide⟩ =
    .split (coordinate 11) (![⟨312443, by decide⟩,⟨312463, by decide⟩,⟨312481, by decide⟩,⟨312503, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6441_312504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6441 ⟨312504, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6441
    ⟨312504, by decide⟩ (by decide) (![⟨312443, by decide⟩,⟨312463, by decide⟩,⟨312481, by decide⟩,⟨312503, by decide⟩]) unmarked_context_11_6441_312504 node_context_11_6441_312504
  intro a
  fin_cases a
  · exact context_12_25764_312443
  · exact context_12_25765_312463
  · exact context_12_25766_312481
  · exact context_12_25767_312503

theorem selected_cut_11686 : selected 9 ⟨312527, by decide⟩
    (prefixPartial 12 25768) = some ⟨12, 2, 0, 312527, 25768, 1649, 65536⟩ := by
  decide +kernel

theorem context_12_25768_312527 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25768 ⟨312527, by decide⟩ :=
  accepted_of_selected 12 25768 ⟨312527, by decide⟩ ⟨12, 2, 0, 312527, 25768, 1649, 65536⟩
    (by decide) selected_cut_11686

theorem selected_cut_11687 : selected 9 ⟨312546, by decide⟩
    (prefixPartial 12 25769) = some ⟨12, 2, 0, 312546, 25769, 1705, 65536⟩ := by
  decide +kernel

theorem context_12_25769_312546 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25769 ⟨312546, by decide⟩ :=
  accepted_of_selected 12 25769 ⟨312546, by decide⟩ ⟨12, 2, 0, 312546, 25769, 1705, 65536⟩
    (by decide) selected_cut_11687

theorem selected_cut_11688 : selected 9 ⟨312564, by decide⟩
    (prefixPartial 12 25770) = some ⟨12, 2, 0, 312564, 25770, 1529, 65536⟩ := by
  decide +kernel

theorem context_12_25770_312564 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25770 ⟨312564, by decide⟩ :=
  accepted_of_selected 12 25770 ⟨312564, by decide⟩ ⟨12, 2, 0, 312564, 25770, 1529, 65536⟩
    (by decide) selected_cut_11688

theorem selected_cut_11689 : selected 9 ⟨312584, by decide⟩
    (prefixPartial 12 25771) = some ⟨12, 2, 0, 312584, 25771, 1565, 65536⟩ := by
  decide +kernel

theorem context_12_25771_312584 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25771 ⟨312584, by decide⟩ :=
  accepted_of_selected 12 25771 ⟨312584, by decide⟩ ⟨12, 2, 0, 312584, 25771, 1565, 65536⟩
    (by decide) selected_cut_11689

theorem unmarked_context_11_6442_312585 : frontier 10 ⟨312585, by decide⟩
    (prefixCache 11 6442) (prefixPartial 11 6442) = false := by
  decide +kernel

theorem node_context_11_6442_312585 : EJMOriginalGlobalDAGData.nodes 10 ⟨312585, by decide⟩ =
    .split (coordinate 11) (![⟨312527, by decide⟩,⟨312546, by decide⟩,⟨312564, by decide⟩,⟨312584, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6442_312585 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6442 ⟨312585, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6442
    ⟨312585, by decide⟩ (by decide) (![⟨312527, by decide⟩,⟨312546, by decide⟩,⟨312564, by decide⟩,⟨312584, by decide⟩]) unmarked_context_11_6442_312585 node_context_11_6442_312585
  intro a
  fin_cases a
  · exact context_12_25768_312527
  · exact context_12_25769_312546
  · exact context_12_25770_312564
  · exact context_12_25771_312584

theorem selected_cut_11690 : selected 9 ⟨312609, by decide⟩
    (prefixPartial 12 25772) = some ⟨12, 2, 0, 312609, 25772, 1377, 65536⟩ := by
  decide +kernel

theorem context_12_25772_312609 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25772 ⟨312609, by decide⟩ :=
  accepted_of_selected 12 25772 ⟨312609, by decide⟩ ⟨12, 2, 0, 312609, 25772, 1377, 65536⟩
    (by decide) selected_cut_11690

theorem selected_cut_11691 : selected 9 ⟨312623, by decide⟩
    (prefixPartial 12 25773) = some ⟨12, 2, 0, 312623, 25773, 1441, 65536⟩ := by
  decide +kernel

theorem context_12_25773_312623 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25773 ⟨312623, by decide⟩ :=
  accepted_of_selected 12 25773 ⟨312623, by decide⟩ ⟨12, 2, 0, 312623, 25773, 1441, 65536⟩
    (by decide) selected_cut_11691

theorem selected_cut_11692 : selected 9 ⟨312640, by decide⟩
    (prefixPartial 12 25774) = some ⟨12, 2, 0, 312640, 25774, 1333, 65536⟩ := by
  decide +kernel

theorem context_12_25774_312640 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25774 ⟨312640, by decide⟩ :=
  accepted_of_selected 12 25774 ⟨312640, by decide⟩ ⟨12, 2, 0, 312640, 25774, 1333, 65536⟩
    (by decide) selected_cut_11692

theorem selected_cut_11693 : selected 9 ⟨312658, by decide⟩
    (prefixPartial 12 25775) = some ⟨12, 2, 0, 312658, 25775, 1353, 65536⟩ := by
  decide +kernel

theorem context_12_25775_312658 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25775 ⟨312658, by decide⟩ :=
  accepted_of_selected 12 25775 ⟨312658, by decide⟩ ⟨12, 2, 0, 312658, 25775, 1353, 65536⟩
    (by decide) selected_cut_11693

theorem unmarked_context_11_6443_312659 : frontier 10 ⟨312659, by decide⟩
    (prefixCache 11 6443) (prefixPartial 11 6443) = false := by
  decide +kernel

theorem node_context_11_6443_312659 : EJMOriginalGlobalDAGData.nodes 10 ⟨312659, by decide⟩ =
    .split (coordinate 11) (![⟨312609, by decide⟩,⟨312623, by decide⟩,⟨312640, by decide⟩,⟨312658, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6443_312659 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6443 ⟨312659, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6443
    ⟨312659, by decide⟩ (by decide) (![⟨312609, by decide⟩,⟨312623, by decide⟩,⟨312640, by decide⟩,⟨312658, by decide⟩]) unmarked_context_11_6443_312659 node_context_11_6443_312659
  intro a
  fin_cases a
  · exact context_12_25772_312609
  · exact context_12_25773_312623
  · exact context_12_25774_312640
  · exact context_12_25775_312658

theorem unmarked_context_10_1610_312660 : frontier 11 ⟨312660, by decide⟩
    (prefixCache 10 1610) (prefixPartial 10 1610) = false := by
  decide +kernel

theorem node_context_10_1610_312660 : EJMOriginalGlobalDAGData.nodes 11 ⟨312660, by decide⟩ =
    .split (coordinate 10) (![⟨312424, by decide⟩,⟨312504, by decide⟩,⟨312585, by decide⟩,⟨312659, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1610_312660 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1610 ⟨312660, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1610
    ⟨312660, by decide⟩ (by decide) (![⟨312424, by decide⟩,⟨312504, by decide⟩,⟨312585, by decide⟩,⟨312659, by decide⟩]) unmarked_context_10_1610_312660 node_context_10_1610_312660
  intro a
  fin_cases a
  · exact context_11_6440_312424
  · exact context_11_6441_312504
  · exact context_11_6442_312585
  · exact context_11_6443_312659

theorem selected_cut_11694 : selected 9 ⟨312691, by decide⟩
    (prefixPartial 12 25776) = some ⟨12, 2, 0, 312691, 25776, 2001, 65536⟩ := by
  decide +kernel

theorem context_12_25776_312691 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25776 ⟨312691, by decide⟩ :=
  accepted_of_selected 12 25776 ⟨312691, by decide⟩ ⟨12, 2, 0, 312691, 25776, 2001, 65536⟩
    (by decide) selected_cut_11694

theorem selected_cut_11695 : selected 9 ⟨312707, by decide⟩
    (prefixPartial 12 25777) = some ⟨12, 2, 0, 312707, 25777, 1253, 65536⟩ := by
  decide +kernel

theorem context_12_25777_312707 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25777 ⟨312707, by decide⟩ :=
  accepted_of_selected 12 25777 ⟨312707, by decide⟩ ⟨12, 2, 0, 312707, 25777, 1253, 65536⟩
    (by decide) selected_cut_11695

theorem selected_cut_11696 : selected 9 ⟨312721, by decide⟩
    (prefixPartial 12 25778) = some ⟨12, 2, 0, 312721, 25778, 1221, 65536⟩ := by
  decide +kernel

theorem context_12_25778_312721 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25778 ⟨312721, by decide⟩ :=
  accepted_of_selected 12 25778 ⟨312721, by decide⟩ ⟨12, 2, 0, 312721, 25778, 1221, 65536⟩
    (by decide) selected_cut_11696

theorem selected_cut_11697 : selected 9 ⟨312737, by decide⟩
    (prefixPartial 12 25779) = some ⟨12, 2, 0, 312737, 25779, 1209, 65536⟩ := by
  decide +kernel

theorem context_12_25779_312737 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25779 ⟨312737, by decide⟩ :=
  accepted_of_selected 12 25779 ⟨312737, by decide⟩ ⟨12, 2, 0, 312737, 25779, 1209, 65536⟩
    (by decide) selected_cut_11697

theorem unmarked_context_11_6444_312738 : frontier 10 ⟨312738, by decide⟩
    (prefixCache 11 6444) (prefixPartial 11 6444) = false := by
  decide +kernel

theorem node_context_11_6444_312738 : EJMOriginalGlobalDAGData.nodes 10 ⟨312738, by decide⟩ =
    .split (coordinate 11) (![⟨312691, by decide⟩,⟨312707, by decide⟩,⟨312721, by decide⟩,⟨312737, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6444_312738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6444 ⟨312738, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6444
    ⟨312738, by decide⟩ (by decide) (![⟨312691, by decide⟩,⟨312707, by decide⟩,⟨312721, by decide⟩,⟨312737, by decide⟩]) unmarked_context_11_6444_312738 node_context_11_6444_312738
  intro a
  fin_cases a
  · exact context_12_25776_312691
  · exact context_12_25777_312707
  · exact context_12_25778_312721
  · exact context_12_25779_312737

theorem selected_cut_11698 : selected 9 ⟨312755, by decide⟩
    (prefixPartial 12 25780) = some ⟨12, 2, 0, 312755, 25780, 1169, 65536⟩ := by
  decide +kernel

theorem context_12_25780_312755 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25780 ⟨312755, by decide⟩ :=
  accepted_of_selected 12 25780 ⟨312755, by decide⟩ ⟨12, 2, 0, 312755, 25780, 1169, 65536⟩
    (by decide) selected_cut_11698

theorem selected_cut_11699 : selected 9 ⟨312768, by decide⟩
    (prefixPartial 12 25781) = some ⟨12, 2, 0, 312768, 25781, 1153, 65536⟩ := by
  decide +kernel

theorem context_12_25781_312768 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25781 ⟨312768, by decide⟩ :=
  accepted_of_selected 12 25781 ⟨312768, by decide⟩ ⟨12, 2, 0, 312768, 25781, 1153, 65536⟩
    (by decide) selected_cut_11699

theorem selected_cut_11700 : selected 9 ⟨312784, by decide⟩
    (prefixPartial 12 25782) = some ⟨12, 2, 0, 312784, 25782, 1157, 65536⟩ := by
  decide +kernel

theorem context_12_25782_312784 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25782 ⟨312784, by decide⟩ :=
  accepted_of_selected 12 25782 ⟨312784, by decide⟩ ⟨12, 2, 0, 312784, 25782, 1157, 65536⟩
    (by decide) selected_cut_11700

theorem selected_cut_11701 : selected 9 ⟨312802, by decide⟩
    (prefixPartial 12 25783) = some ⟨12, 2, 0, 312802, 25783, 1233, 65536⟩ := by
  decide +kernel

theorem context_12_25783_312802 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25783 ⟨312802, by decide⟩ :=
  accepted_of_selected 12 25783 ⟨312802, by decide⟩ ⟨12, 2, 0, 312802, 25783, 1233, 65536⟩
    (by decide) selected_cut_11701

theorem unmarked_context_11_6445_312803 : frontier 10 ⟨312803, by decide⟩
    (prefixCache 11 6445) (prefixPartial 11 6445) = false := by
  decide +kernel

theorem node_context_11_6445_312803 : EJMOriginalGlobalDAGData.nodes 10 ⟨312803, by decide⟩ =
    .split (coordinate 11) (![⟨312755, by decide⟩,⟨312768, by decide⟩,⟨312784, by decide⟩,⟨312802, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6445_312803 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6445 ⟨312803, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6445
    ⟨312803, by decide⟩ (by decide) (![⟨312755, by decide⟩,⟨312768, by decide⟩,⟨312784, by decide⟩,⟨312802, by decide⟩]) unmarked_context_11_6445_312803 node_context_11_6445_312803
  intro a
  fin_cases a
  · exact context_12_25780_312755
  · exact context_12_25781_312768
  · exact context_12_25782_312784
  · exact context_12_25783_312802

theorem selected_cut_11702 : selected 9 ⟨312824, by decide⟩
    (prefixPartial 12 25784) = some ⟨12, 2, 0, 312824, 25784, 1289, 65536⟩ := by
  decide +kernel

theorem context_12_25784_312824 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25784 ⟨312824, by decide⟩ :=
  accepted_of_selected 12 25784 ⟨312824, by decide⟩ ⟨12, 2, 0, 312824, 25784, 1289, 65536⟩
    (by decide) selected_cut_11702

theorem selected_cut_11703 : selected 9 ⟨312837, by decide⟩
    (prefixPartial 12 25785) = some ⟨12, 2, 0, 312837, 25785, 1209, 65536⟩ := by
  decide +kernel

theorem context_12_25785_312837 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25785 ⟨312837, by decide⟩ :=
  accepted_of_selected 12 25785 ⟨312837, by decide⟩ ⟨12, 2, 0, 312837, 25785, 1209, 65536⟩
    (by decide) selected_cut_11703

theorem selected_cut_11704 : selected 9 ⟨312850, by decide⟩
    (prefixPartial 12 25786) = some ⟨12, 2, 0, 312850, 25786, 1181, 65536⟩ := by
  decide +kernel

theorem context_12_25786_312850 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25786 ⟨312850, by decide⟩ :=
  accepted_of_selected 12 25786 ⟨312850, by decide⟩ ⟨12, 2, 0, 312850, 25786, 1181, 65536⟩
    (by decide) selected_cut_11704

theorem selected_cut_11705 : selected 9 ⟨312867, by decide⟩
    (prefixPartial 12 25787) = some ⟨12, 2, 0, 312867, 25787, 1269, 65536⟩ := by
  decide +kernel

theorem context_12_25787_312867 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25787 ⟨312867, by decide⟩ :=
  accepted_of_selected 12 25787 ⟨312867, by decide⟩ ⟨12, 2, 0, 312867, 25787, 1269, 65536⟩
    (by decide) selected_cut_11705

theorem unmarked_context_11_6446_312868 : frontier 10 ⟨312868, by decide⟩
    (prefixCache 11 6446) (prefixPartial 11 6446) = false := by
  decide +kernel

theorem node_context_11_6446_312868 : EJMOriginalGlobalDAGData.nodes 10 ⟨312868, by decide⟩ =
    .split (coordinate 11) (![⟨312824, by decide⟩,⟨312837, by decide⟩,⟨312850, by decide⟩,⟨312867, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6446_312868 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6446 ⟨312868, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6446
    ⟨312868, by decide⟩ (by decide) (![⟨312824, by decide⟩,⟨312837, by decide⟩,⟨312850, by decide⟩,⟨312867, by decide⟩]) unmarked_context_11_6446_312868 node_context_11_6446_312868
  intro a
  fin_cases a
  · exact context_12_25784_312824
  · exact context_12_25785_312837
  · exact context_12_25786_312850
  · exact context_12_25787_312867

theorem selected_cut_11706 : selected 10 ⟨312924, by decide⟩
    (prefixPartial 11 6447) = some ⟨11, 2, 0, 312924, 6447, 4093, 262144⟩ := by
  decide +kernel

theorem context_11_6447_312924 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6447 ⟨312924, by decide⟩ :=
  accepted_of_selected 11 6447 ⟨312924, by decide⟩ ⟨11, 2, 0, 312924, 6447, 4093, 262144⟩
    (by decide) selected_cut_11706

theorem unmarked_context_10_1611_312925 : frontier 11 ⟨312925, by decide⟩
    (prefixCache 10 1611) (prefixPartial 10 1611) = false := by
  decide +kernel

theorem node_context_10_1611_312925 : EJMOriginalGlobalDAGData.nodes 11 ⟨312925, by decide⟩ =
    .split (coordinate 10) (![⟨312738, by decide⟩,⟨312803, by decide⟩,⟨312868, by decide⟩,⟨312924, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1611_312925 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1611 ⟨312925, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1611
    ⟨312925, by decide⟩ (by decide) (![⟨312738, by decide⟩,⟨312803, by decide⟩,⟨312868, by decide⟩,⟨312924, by decide⟩]) unmarked_context_10_1611_312925 node_context_10_1611_312925
  intro a
  fin_cases a
  · exact context_11_6444_312738
  · exact context_11_6445_312803
  · exact context_11_6446_312868
  · exact context_11_6447_312924

theorem unmarked_context_9_402_312926 : frontier 12 ⟨312926, by decide⟩
    (prefixCache 9 402) (prefixPartial 9 402) = false := by
  decide +kernel

theorem node_context_9_402_312926 : EJMOriginalGlobalDAGData.nodes 12 ⟨312926, by decide⟩ =
    .split (coordinate 9) (![⟨311828, by decide⟩,⟨312329, by decide⟩,⟨312660, by decide⟩,⟨312925, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_402_312926 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 402 ⟨312926, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 402
    ⟨312926, by decide⟩ (by decide) (![⟨311828, by decide⟩,⟨312329, by decide⟩,⟨312660, by decide⟩,⟨312925, by decide⟩]) unmarked_context_9_402_312926 node_context_9_402_312926
  intro a
  fin_cases a
  · exact context_10_1608_311828
  · exact context_10_1609_312329
  · exact context_10_1610_312660
  · exact context_10_1611_312925

theorem selected_cut_11707 : selected 10 ⟨312988, by decide⟩
    (prefixPartial 11 6448) = some ⟨11, 2, 0, 312988, 6448, 2801, 262144⟩ := by
  decide +kernel

theorem context_11_6448_312988 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6448 ⟨312988, by decide⟩ :=
  accepted_of_selected 11 6448 ⟨312988, by decide⟩ ⟨11, 2, 0, 312988, 6448, 2801, 262144⟩
    (by decide) selected_cut_11707

theorem selected_cut_11708 : selected 10 ⟨313024, by decide⟩
    (prefixPartial 11 6449) = some ⟨11, 2, 0, 313024, 6449, 3117, 262144⟩ := by
  decide +kernel

theorem context_11_6449_313024 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6449 ⟨313024, by decide⟩ :=
  accepted_of_selected 11 6449 ⟨313024, by decide⟩ ⟨11, 2, 0, 313024, 6449, 3117, 262144⟩
    (by decide) selected_cut_11708

theorem selected_cut_11709 : selected 10 ⟨313070, by decide⟩
    (prefixPartial 11 6450) = some ⟨11, 2, 0, 313070, 6450, 3129, 262144⟩ := by
  decide +kernel

theorem context_11_6450_313070 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6450 ⟨313070, by decide⟩ :=
  accepted_of_selected 11 6450 ⟨313070, by decide⟩ ⟨11, 2, 0, 313070, 6450, 3129, 262144⟩
    (by decide) selected_cut_11709

theorem selected_cut_11710 : selected 10 ⟨313104, by decide⟩
    (prefixPartial 11 6451) = some ⟨11, 2, 0, 313104, 6451, 2689, 262144⟩ := by
  decide +kernel

theorem context_11_6451_313104 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6451 ⟨313104, by decide⟩ :=
  accepted_of_selected 11 6451 ⟨313104, by decide⟩ ⟨11, 2, 0, 313104, 6451, 2689, 262144⟩
    (by decide) selected_cut_11710

theorem unmarked_context_10_1612_313105 : frontier 11 ⟨313105, by decide⟩
    (prefixCache 10 1612) (prefixPartial 10 1612) = false := by
  decide +kernel

theorem node_context_10_1612_313105 : EJMOriginalGlobalDAGData.nodes 11 ⟨313105, by decide⟩ =
    .split (coordinate 10) (![⟨312988, by decide⟩,⟨313024, by decide⟩,⟨313070, by decide⟩,⟨313104, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1612_313105 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1612 ⟨313105, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1612
    ⟨313105, by decide⟩ (by decide) (![⟨312988, by decide⟩,⟨313024, by decide⟩,⟨313070, by decide⟩,⟨313104, by decide⟩]) unmarked_context_10_1612_313105 node_context_10_1612_313105
  intro a
  fin_cases a
  · exact context_11_6448_312988
  · exact context_11_6449_313024
  · exact context_11_6450_313070
  · exact context_11_6451_313104

theorem selected_cut_11711 : selected 10 ⟨313136, by decide⟩
    (prefixPartial 11 6452) = some ⟨11, 2, 0, 313136, 6452, 2917, 262144⟩ := by
  decide +kernel

theorem context_11_6452_313136 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6452 ⟨313136, by decide⟩ :=
  accepted_of_selected 11 6452 ⟨313136, by decide⟩ ⟨11, 2, 0, 313136, 6452, 2917, 262144⟩
    (by decide) selected_cut_11711

theorem selected_cut_11712 : selected 10 ⟨313166, by decide⟩
    (prefixPartial 11 6453) = some ⟨11, 2, 0, 313166, 6453, 2265, 262144⟩ := by
  decide +kernel

theorem context_11_6453_313166 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6453 ⟨313166, by decide⟩ :=
  accepted_of_selected 11 6453 ⟨313166, by decide⟩ ⟨11, 2, 0, 313166, 6453, 2265, 262144⟩
    (by decide) selected_cut_11712

theorem selected_cut_11713 : selected 10 ⟨313189, by decide⟩
    (prefixPartial 11 6454) = some ⟨11, 2, 0, 313189, 6454, 2241, 262144⟩ := by
  decide +kernel

theorem context_11_6454_313189 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6454 ⟨313189, by decide⟩ :=
  accepted_of_selected 11 6454 ⟨313189, by decide⟩ ⟨11, 2, 0, 313189, 6454, 2241, 262144⟩
    (by decide) selected_cut_11713

theorem selected_cut_11714 : selected 10 ⟨313207, by decide⟩
    (prefixPartial 11 6455) = some ⟨11, 2, 0, 313207, 6455, 1801, 262144⟩ := by
  decide +kernel

theorem context_11_6455_313207 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6455 ⟨313207, by decide⟩ :=
  accepted_of_selected 11 6455 ⟨313207, by decide⟩ ⟨11, 2, 0, 313207, 6455, 1801, 262144⟩
    (by decide) selected_cut_11714

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
