/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover287
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_27651 : selected 8 ⟨698565, by decide⟩
    (prefixPartial 13 366885) = some ⟨13, 2, 0, 698565, 366885, 2629, 16384⟩ := by
  decide +kernel

theorem context_13_366885_698565 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366885 ⟨698565, by decide⟩ :=
  accepted_of_selected 13 366885 ⟨698565, by decide⟩ ⟨13, 2, 0, 698565, 366885, 2629, 16384⟩
    (by decide) selected_cut_27651

theorem selected_cut_27652 : selected 8 ⟨698591, by decide⟩
    (prefixPartial 13 366886) = some ⟨13, 2, 0, 698591, 366886, 1773, 16384⟩ := by
  decide +kernel

theorem context_13_366886_698591 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366886 ⟨698591, by decide⟩ :=
  accepted_of_selected 13 366886 ⟨698591, by decide⟩ ⟨13, 2, 0, 698591, 366886, 1773, 16384⟩
    (by decide) selected_cut_27652

theorem selected_cut_27653 : selected 8 ⟨698604, by decide⟩
    (prefixPartial 13 366887) = some ⟨13, 2, 0, 698604, 366887, 1077, 16384⟩ := by
  decide +kernel

theorem context_13_366887_698604 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366887 ⟨698604, by decide⟩ :=
  accepted_of_selected 13 366887 ⟨698604, by decide⟩ ⟨13, 2, 0, 698604, 366887, 1077, 16384⟩
    (by decide) selected_cut_27653

theorem unmarked_context_12_91721_698605 : frontier 9 ⟨698605, by decide⟩
    (prefixCache 12 91721) (prefixPartial 12 91721) = false := by
  decide +kernel

theorem node_context_12_91721_698605 : EJMOriginalGlobalDAGData.nodes 9 ⟨698605, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨698565, by decide⟩,⟨698591, by decide⟩,⟨698604, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91721_698605 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91721 ⟨698605, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91721
    ⟨698605, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨698565, by decide⟩,⟨698591, by decide⟩,⟨698604, by decide⟩]) unmarked_context_12_91721_698605 node_context_12_91721_698605
  intro a
  fin_cases a
  · exact context_13_366884_3444
  · exact context_13_366885_698565
  · exact context_13_366886_698591
  · exact context_13_366887_698604

theorem selected_cut_27654 : selected 9 ⟨698760, by decide⟩
    (prefixPartial 12 91722) = some ⟨12, 2, 0, 698760, 91722, 3373, 65536⟩ := by
  decide +kernel

theorem context_12_91722_698760 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91722 ⟨698760, by decide⟩ :=
  accepted_of_selected 12 91722 ⟨698760, by decide⟩ ⟨12, 2, 0, 698760, 91722, 3373, 65536⟩
    (by decide) selected_cut_27654

theorem selected_cut_27655 : selected 9 ⟨698816, by decide⟩
    (prefixPartial 12 91723) = some ⟨12, 2, 0, 698816, 91723, 3677, 65536⟩ := by
  decide +kernel

theorem context_12_91723_698816 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91723 ⟨698816, by decide⟩ :=
  accepted_of_selected 12 91723 ⟨698816, by decide⟩ ⟨12, 2, 0, 698816, 91723, 3677, 65536⟩
    (by decide) selected_cut_27655

theorem unmarked_context_11_22930_698817 : frontier 10 ⟨698817, by decide⟩
    (prefixCache 11 22930) (prefixPartial 11 22930) = false := by
  decide +kernel

theorem node_context_11_22930_698817 : EJMOriginalGlobalDAGData.nodes 10 ⟨698817, by decide⟩ =
    .split (coordinate 11) (![⟨698509, by decide⟩,⟨698605, by decide⟩,⟨698760, by decide⟩,⟨698816, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22930_698817 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22930 ⟨698817, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22930
    ⟨698817, by decide⟩ (by decide) (![⟨698509, by decide⟩,⟨698605, by decide⟩,⟨698760, by decide⟩,⟨698816, by decide⟩]) unmarked_context_11_22930_698817 node_context_11_22930_698817
  intro a
  fin_cases a
  · exact context_12_91720_698509
  · exact context_12_91721_698605
  · exact context_12_91722_698760
  · exact context_12_91723_698816

theorem selected_cut_27656 : selected 9 ⟨698866, by decide⟩
    (prefixPartial 12 91724) = some ⟨12, 2, 0, 698866, 91724, 3597, 65536⟩ := by
  decide +kernel

theorem context_12_91724_698866 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91724 ⟨698866, by decide⟩ :=
  accepted_of_selected 12 91724 ⟨698866, by decide⟩ ⟨12, 2, 0, 698866, 91724, 3597, 65536⟩
    (by decide) selected_cut_27656

theorem selected_cut_27657 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 366900) = some ⟨13, 1, 0, 3444, 366900, 1, 16384⟩ := by
  decide +kernel

theorem context_13_366900_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366900 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 366900 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 366900, 1, 16384⟩
    (by decide) selected_cut_27657

theorem selected_cut_27658 : selected 8 ⟨698908, by decide⟩
    (prefixPartial 13 366901) = some ⟨13, 2, 0, 698908, 366901, 2513, 16384⟩ := by
  decide +kernel

theorem context_13_366901_698908 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366901 ⟨698908, by decide⟩ :=
  accepted_of_selected 13 366901 ⟨698908, by decide⟩ ⟨13, 2, 0, 698908, 366901, 2513, 16384⟩
    (by decide) selected_cut_27658

theorem selected_cut_27659 : selected 8 ⟨698936, by decide⟩
    (prefixPartial 13 366902) = some ⟨13, 2, 0, 698936, 366902, 1937, 16384⟩ := by
  decide +kernel

theorem context_13_366902_698936 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366902 ⟨698936, by decide⟩ :=
  accepted_of_selected 13 366902 ⟨698936, by decide⟩ ⟨13, 2, 0, 698936, 366902, 1937, 16384⟩
    (by decide) selected_cut_27659

theorem selected_cut_27660 : selected 8 ⟨698946, by decide⟩
    (prefixPartial 13 366903) = some ⟨13, 2, 0, 698946, 366903, 1057, 16384⟩ := by
  decide +kernel

theorem context_13_366903_698946 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366903 ⟨698946, by decide⟩ :=
  accepted_of_selected 13 366903 ⟨698946, by decide⟩ ⟨13, 2, 0, 698946, 366903, 1057, 16384⟩
    (by decide) selected_cut_27660

theorem unmarked_context_12_91725_698947 : frontier 9 ⟨698947, by decide⟩
    (prefixCache 12 91725) (prefixPartial 12 91725) = false := by
  decide +kernel

theorem node_context_12_91725_698947 : EJMOriginalGlobalDAGData.nodes 9 ⟨698947, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨698908, by decide⟩,⟨698936, by decide⟩,⟨698946, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91725_698947 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91725 ⟨698947, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91725
    ⟨698947, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨698908, by decide⟩,⟨698936, by decide⟩,⟨698946, by decide⟩]) unmarked_context_12_91725_698947 node_context_12_91725_698947
  intro a
  fin_cases a
  · exact context_13_366900_3444
  · exact context_13_366901_698908
  · exact context_13_366902_698936
  · exact context_13_366903_698946

theorem selected_cut_27661 : selected 9 ⟨698988, by decide⟩
    (prefixPartial 12 91726) = some ⟨12, 2, 0, 698988, 91726, 3241, 65536⟩ := by
  decide +kernel

theorem context_12_91726_698988 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91726 ⟨698988, by decide⟩ :=
  accepted_of_selected 12 91726 ⟨698988, by decide⟩ ⟨12, 2, 0, 698988, 91726, 3241, 65536⟩
    (by decide) selected_cut_27661

theorem selected_cut_27662 : selected 9 ⟨699037, by decide⟩
    (prefixPartial 12 91727) = some ⟨12, 2, 0, 699037, 91727, 3641, 65536⟩ := by
  decide +kernel

theorem context_12_91727_699037 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91727 ⟨699037, by decide⟩ :=
  accepted_of_selected 12 91727 ⟨699037, by decide⟩ ⟨12, 2, 0, 699037, 91727, 3641, 65536⟩
    (by decide) selected_cut_27662

theorem unmarked_context_11_22931_699038 : frontier 10 ⟨699038, by decide⟩
    (prefixCache 11 22931) (prefixPartial 11 22931) = false := by
  decide +kernel

theorem node_context_11_22931_699038 : EJMOriginalGlobalDAGData.nodes 10 ⟨699038, by decide⟩ =
    .split (coordinate 11) (![⟨698866, by decide⟩,⟨698947, by decide⟩,⟨698988, by decide⟩,⟨699037, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22931_699038 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22931 ⟨699038, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22931
    ⟨699038, by decide⟩ (by decide) (![⟨698866, by decide⟩,⟨698947, by decide⟩,⟨698988, by decide⟩,⟨699037, by decide⟩]) unmarked_context_11_22931_699038 node_context_11_22931_699038
  intro a
  fin_cases a
  · exact context_12_91724_698866
  · exact context_12_91725_698947
  · exact context_12_91726_698988
  · exact context_12_91727_699037

theorem unmarked_context_10_5732_699039 : frontier 11 ⟨699039, by decide⟩
    (prefixCache 10 5732) (prefixPartial 10 5732) = false := by
  decide +kernel

theorem node_context_10_5732_699039 : EJMOriginalGlobalDAGData.nodes 11 ⟨699039, by decide⟩ =
    .split (coordinate 10) (![⟨698294, by decide⟩,⟨698452, by decide⟩,⟨698817, by decide⟩,⟨699038, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5732_699039 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5732 ⟨699039, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5732
    ⟨699039, by decide⟩ (by decide) (![⟨698294, by decide⟩,⟨698452, by decide⟩,⟨698817, by decide⟩,⟨699038, by decide⟩]) unmarked_context_10_5732_699039 node_context_10_5732_699039
  intro a
  fin_cases a
  · exact context_11_22928_698294
  · exact context_11_22929_698452
  · exact context_11_22930_698817
  · exact context_11_22931_699038

theorem selected_cut_27663 : selected 9 ⟨699081, by decide⟩
    (prefixPartial 12 91728) = some ⟨12, 2, 0, 699081, 91728, 3161, 65536⟩ := by
  decide +kernel

theorem context_12_91728_699081 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91728 ⟨699081, by decide⟩ :=
  accepted_of_selected 12 91728 ⟨699081, by decide⟩ ⟨12, 2, 0, 699081, 91728, 3161, 65536⟩
    (by decide) selected_cut_27663

theorem selected_cut_27664 : selected 9 ⟨642341, by decide⟩
    (prefixPartial 12 91729) = some ⟨12, 1, 0, 642341, 91729, 1, 65536⟩ := by
  decide +kernel

theorem context_12_91729_642341 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91729 ⟨642341, by decide⟩ :=
  accepted_of_selected 12 91729 ⟨642341, by decide⟩ ⟨12, 1, 0, 642341, 91729, 1, 65536⟩
    (by decide) selected_cut_27664

theorem selected_cut_27665 : selected 9 ⟨699117, by decide⟩
    (prefixPartial 12 91730) = some ⟨12, 2, 0, 699117, 91730, 2821, 65536⟩ := by
  decide +kernel

theorem context_12_91730_699117 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91730 ⟨699117, by decide⟩ :=
  accepted_of_selected 12 91730 ⟨699117, by decide⟩ ⟨12, 2, 0, 699117, 91730, 2821, 65536⟩
    (by decide) selected_cut_27665

theorem selected_cut_27666 : selected 9 ⟨699165, by decide⟩
    (prefixPartial 12 91731) = some ⟨12, 2, 0, 699165, 91731, 3877, 65536⟩ := by
  decide +kernel

theorem context_12_91731_699165 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91731 ⟨699165, by decide⟩ :=
  accepted_of_selected 12 91731 ⟨699165, by decide⟩ ⟨12, 2, 0, 699165, 91731, 3877, 65536⟩
    (by decide) selected_cut_27666

theorem unmarked_context_11_22932_699166 : frontier 10 ⟨699166, by decide⟩
    (prefixCache 11 22932) (prefixPartial 11 22932) = false := by
  decide +kernel

theorem node_context_11_22932_699166 : EJMOriginalGlobalDAGData.nodes 10 ⟨699166, by decide⟩ =
    .split (coordinate 11) (![⟨699081, by decide⟩,⟨642341, by decide⟩,⟨699117, by decide⟩,⟨699165, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22932_699166 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22932 ⟨699166, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22932
    ⟨699166, by decide⟩ (by decide) (![⟨699081, by decide⟩,⟨642341, by decide⟩,⟨699117, by decide⟩,⟨699165, by decide⟩]) unmarked_context_11_22932_699166 node_context_11_22932_699166
  intro a
  fin_cases a
  · exact context_12_91728_699081
  · exact context_12_91729_642341
  · exact context_12_91730_699117
  · exact context_12_91731_699165

theorem selected_cut_27667 : selected 10 ⟨451541, by decide⟩
    (prefixPartial 11 22933) = some ⟨11, 1, 0, 451541, 22933, 1, 262144⟩ := by
  decide +kernel

theorem context_11_22933_451541 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22933 ⟨451541, by decide⟩ :=
  accepted_of_selected 11 22933 ⟨451541, by decide⟩ ⟨11, 1, 0, 451541, 22933, 1, 262144⟩
    (by decide) selected_cut_27667

theorem selected_cut_27668 : selected 9 ⟨699204, by decide⟩
    (prefixPartial 12 91736) = some ⟨12, 2, 0, 699204, 91736, 2921, 65536⟩ := by
  decide +kernel

theorem context_12_91736_699204 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91736 ⟨699204, by decide⟩ :=
  accepted_of_selected 12 91736 ⟨699204, by decide⟩ ⟨12, 2, 0, 699204, 91736, 2921, 65536⟩
    (by decide) selected_cut_27668

theorem selected_cut_27669 : selected 9 ⟨642341, by decide⟩
    (prefixPartial 12 91737) = some ⟨12, 1, 0, 642341, 91737, 1, 65536⟩ := by
  decide +kernel

theorem context_12_91737_642341 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91737 ⟨642341, by decide⟩ :=
  accepted_of_selected 12 91737 ⟨642341, by decide⟩ ⟨12, 1, 0, 642341, 91737, 1, 65536⟩
    (by decide) selected_cut_27669

theorem selected_cut_27670 : selected 9 ⟨212113, by decide⟩
    (prefixPartial 12 91738) = some ⟨12, 1, 0, 212113, 91738, 1, 65536⟩ := by
  decide +kernel

theorem context_12_91738_212113 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91738 ⟨212113, by decide⟩ :=
  accepted_of_selected 12 91738 ⟨212113, by decide⟩ ⟨12, 1, 0, 212113, 91738, 1, 65536⟩
    (by decide) selected_cut_27670

theorem selected_cut_27671 : selected 9 ⟨699250, by decide⟩
    (prefixPartial 12 91739) = some ⟨12, 2, 0, 699250, 91739, 3097, 65536⟩ := by
  decide +kernel

theorem context_12_91739_699250 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91739 ⟨699250, by decide⟩ :=
  accepted_of_selected 12 91739 ⟨699250, by decide⟩ ⟨12, 2, 0, 699250, 91739, 3097, 65536⟩
    (by decide) selected_cut_27671

theorem unmarked_context_11_22934_699251 : frontier 10 ⟨699251, by decide⟩
    (prefixCache 11 22934) (prefixPartial 11 22934) = false := by
  decide +kernel

theorem node_context_11_22934_699251 : EJMOriginalGlobalDAGData.nodes 10 ⟨699251, by decide⟩ =
    .split (coordinate 11) (![⟨699204, by decide⟩,⟨642341, by decide⟩,⟨212113, by decide⟩,⟨699250, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22934_699251 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22934 ⟨699251, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22934
    ⟨699251, by decide⟩ (by decide) (![⟨699204, by decide⟩,⟨642341, by decide⟩,⟨212113, by decide⟩,⟨699250, by decide⟩]) unmarked_context_11_22934_699251 node_context_11_22934_699251
  intro a
  fin_cases a
  · exact context_12_91736_699204
  · exact context_12_91737_642341
  · exact context_12_91738_212113
  · exact context_12_91739_699250

theorem selected_cut_27672 : selected 9 ⟨699294, by decide⟩
    (prefixPartial 12 91740) = some ⟨12, 2, 0, 699294, 91740, 3213, 65536⟩ := by
  decide +kernel

theorem context_12_91740_699294 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91740 ⟨699294, by decide⟩ :=
  accepted_of_selected 12 91740 ⟨699294, by decide⟩ ⟨12, 2, 0, 699294, 91740, 3213, 65536⟩
    (by decide) selected_cut_27672

theorem selected_cut_27673 : selected 9 ⟨642341, by decide⟩
    (prefixPartial 12 91741) = some ⟨12, 1, 0, 642341, 91741, 1, 65536⟩ := by
  decide +kernel

theorem context_12_91741_642341 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91741 ⟨642341, by decide⟩ :=
  accepted_of_selected 12 91741 ⟨642341, by decide⟩ ⟨12, 1, 0, 642341, 91741, 1, 65536⟩
    (by decide) selected_cut_27673

theorem selected_cut_27674 : selected 9 ⟨699333, by decide⟩
    (prefixPartial 12 91742) = some ⟨12, 2, 0, 699333, 91742, 2757, 65536⟩ := by
  decide +kernel

theorem context_12_91742_699333 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91742 ⟨699333, by decide⟩ :=
  accepted_of_selected 12 91742 ⟨699333, by decide⟩ ⟨12, 2, 0, 699333, 91742, 2757, 65536⟩
    (by decide) selected_cut_27674

theorem selected_cut_27675 : selected 9 ⟨699375, by decide⟩
    (prefixPartial 12 91743) = some ⟨12, 2, 0, 699375, 91743, 3497, 65536⟩ := by
  decide +kernel

theorem context_12_91743_699375 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91743 ⟨699375, by decide⟩ :=
  accepted_of_selected 12 91743 ⟨699375, by decide⟩ ⟨12, 2, 0, 699375, 91743, 3497, 65536⟩
    (by decide) selected_cut_27675

theorem unmarked_context_11_22935_699376 : frontier 10 ⟨699376, by decide⟩
    (prefixCache 11 22935) (prefixPartial 11 22935) = false := by
  decide +kernel

theorem node_context_11_22935_699376 : EJMOriginalGlobalDAGData.nodes 10 ⟨699376, by decide⟩ =
    .split (coordinate 11) (![⟨699294, by decide⟩,⟨642341, by decide⟩,⟨699333, by decide⟩,⟨699375, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22935_699376 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22935 ⟨699376, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22935
    ⟨699376, by decide⟩ (by decide) (![⟨699294, by decide⟩,⟨642341, by decide⟩,⟨699333, by decide⟩,⟨699375, by decide⟩]) unmarked_context_11_22935_699376 node_context_11_22935_699376
  intro a
  fin_cases a
  · exact context_12_91740_699294
  · exact context_12_91741_642341
  · exact context_12_91742_699333
  · exact context_12_91743_699375

theorem unmarked_context_10_5733_699377 : frontier 11 ⟨699377, by decide⟩
    (prefixCache 10 5733) (prefixPartial 10 5733) = false := by
  decide +kernel

theorem node_context_10_5733_699377 : EJMOriginalGlobalDAGData.nodes 11 ⟨699377, by decide⟩ =
    .split (coordinate 10) (![⟨699166, by decide⟩,⟨451541, by decide⟩,⟨699251, by decide⟩,⟨699376, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5733_699377 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5733 ⟨699377, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5733
    ⟨699377, by decide⟩ (by decide) (![⟨699166, by decide⟩,⟨451541, by decide⟩,⟨699251, by decide⟩,⟨699376, by decide⟩]) unmarked_context_10_5733_699377 node_context_10_5733_699377
  intro a
  fin_cases a
  · exact context_11_22932_699166
  · exact context_11_22933_451541
  · exact context_11_22934_699251
  · exact context_11_22935_699376

theorem selected_cut_27676 : selected 9 ⟨699414, by decide⟩
    (prefixPartial 12 91744) = some ⟨12, 2, 0, 699414, 91744, 3261, 65536⟩ := by
  decide +kernel

theorem context_12_91744_699414 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91744 ⟨699414, by decide⟩ :=
  accepted_of_selected 12 91744 ⟨699414, by decide⟩ ⟨12, 2, 0, 699414, 91744, 3261, 65536⟩
    (by decide) selected_cut_27676

theorem selected_cut_27677 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 366980) = some ⟨13, 1, 0, 3444, 366980, 1, 16384⟩ := by
  decide +kernel

theorem context_13_366980_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366980 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 366980 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 366980, 1, 16384⟩
    (by decide) selected_cut_27677

theorem selected_cut_27678 : selected 8 ⟨699443, by decide⟩
    (prefixPartial 13 366981) = some ⟨13, 2, 0, 699443, 366981, 1745, 16384⟩ := by
  decide +kernel

theorem context_13_366981_699443 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366981 ⟨699443, by decide⟩ :=
  accepted_of_selected 13 366981 ⟨699443, by decide⟩ ⟨13, 2, 0, 699443, 366981, 1745, 16384⟩
    (by decide) selected_cut_27678

theorem selected_cut_27679 : selected 8 ⟨699489, by decide⟩
    (prefixPartial 13 366982) = some ⟨13, 2, 0, 699489, 366982, 2125, 16384⟩ := by
  decide +kernel

theorem context_13_366982_699489 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366982 ⟨699489, by decide⟩ :=
  accepted_of_selected 13 366982 ⟨699489, by decide⟩ ⟨13, 2, 0, 699489, 366982, 2125, 16384⟩
    (by decide) selected_cut_27679

theorem selected_cut_27680 : selected 8 ⟨699498, by decide⟩
    (prefixPartial 13 366983) = some ⟨13, 2, 0, 699498, 366983, 941, 16384⟩ := by
  decide +kernel

theorem context_13_366983_699498 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366983 ⟨699498, by decide⟩ :=
  accepted_of_selected 13 366983 ⟨699498, by decide⟩ ⟨13, 2, 0, 699498, 366983, 941, 16384⟩
    (by decide) selected_cut_27680

theorem unmarked_context_12_91745_699499 : frontier 9 ⟨699499, by decide⟩
    (prefixCache 12 91745) (prefixPartial 12 91745) = false := by
  decide +kernel

theorem node_context_12_91745_699499 : EJMOriginalGlobalDAGData.nodes 9 ⟨699499, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨699443, by decide⟩,⟨699489, by decide⟩,⟨699498, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91745_699499 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91745 ⟨699499, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91745
    ⟨699499, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨699443, by decide⟩,⟨699489, by decide⟩,⟨699498, by decide⟩]) unmarked_context_12_91745_699499 node_context_12_91745_699499
  intro a
  fin_cases a
  · exact context_13_366980_3444
  · exact context_13_366981_699443
  · exact context_13_366982_699489
  · exact context_13_366983_699498

theorem selected_cut_27681 : selected 9 ⟨699529, by decide⟩
    (prefixPartial 12 91746) = some ⟨12, 2, 0, 699529, 91746, 2833, 65536⟩ := by
  decide +kernel

theorem context_12_91746_699529 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91746 ⟨699529, by decide⟩ :=
  accepted_of_selected 12 91746 ⟨699529, by decide⟩ ⟨12, 2, 0, 699529, 91746, 2833, 65536⟩
    (by decide) selected_cut_27681

theorem selected_cut_27682 : selected 9 ⟨699579, by decide⟩
    (prefixPartial 12 91747) = some ⟨12, 2, 0, 699579, 91747, 3517, 65536⟩ := by
  decide +kernel

theorem context_12_91747_699579 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91747 ⟨699579, by decide⟩ :=
  accepted_of_selected 12 91747 ⟨699579, by decide⟩ ⟨12, 2, 0, 699579, 91747, 3517, 65536⟩
    (by decide) selected_cut_27682

theorem unmarked_context_11_22936_699580 : frontier 10 ⟨699580, by decide⟩
    (prefixCache 11 22936) (prefixPartial 11 22936) = false := by
  decide +kernel

theorem node_context_11_22936_699580 : EJMOriginalGlobalDAGData.nodes 10 ⟨699580, by decide⟩ =
    .split (coordinate 11) (![⟨699414, by decide⟩,⟨699499, by decide⟩,⟨699529, by decide⟩,⟨699579, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22936_699580 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22936 ⟨699580, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22936
    ⟨699580, by decide⟩ (by decide) (![⟨699414, by decide⟩,⟨699499, by decide⟩,⟨699529, by decide⟩,⟨699579, by decide⟩]) unmarked_context_11_22936_699580 node_context_11_22936_699580
  intro a
  fin_cases a
  · exact context_12_91744_699414
  · exact context_12_91745_699499
  · exact context_12_91746_699529
  · exact context_12_91747_699579

theorem selected_cut_27683 : selected 9 ⟨699617, by decide⟩
    (prefixPartial 12 91748) = some ⟨12, 2, 0, 699617, 91748, 2885, 65536⟩ := by
  decide +kernel

theorem context_12_91748_699617 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91748 ⟨699617, by decide⟩ :=
  accepted_of_selected 12 91748 ⟨699617, by decide⟩ ⟨12, 2, 0, 699617, 91748, 2885, 65536⟩
    (by decide) selected_cut_27683

theorem selected_cut_27684 : selected 9 ⟨642794, by decide⟩
    (prefixPartial 12 91749) = some ⟨12, 1, 0, 642794, 91749, 1, 65536⟩ := by
  decide +kernel

theorem context_12_91749_642794 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91749 ⟨642794, by decide⟩ :=
  accepted_of_selected 12 91749 ⟨642794, by decide⟩ ⟨12, 1, 0, 642794, 91749, 1, 65536⟩
    (by decide) selected_cut_27684

theorem selected_cut_27685 : selected 9 ⟨699649, by decide⟩
    (prefixPartial 12 91750) = some ⟨12, 2, 0, 699649, 91750, 2561, 65536⟩ := by
  decide +kernel

theorem context_12_91750_699649 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91750 ⟨699649, by decide⟩ :=
  accepted_of_selected 12 91750 ⟨699649, by decide⟩ ⟨12, 2, 0, 699649, 91750, 2561, 65536⟩
    (by decide) selected_cut_27685

theorem selected_cut_27686 : selected 9 ⟨699686, by decide⟩
    (prefixPartial 12 91751) = some ⟨12, 2, 0, 699686, 91751, 3057, 65536⟩ := by
  decide +kernel

theorem context_12_91751_699686 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91751 ⟨699686, by decide⟩ :=
  accepted_of_selected 12 91751 ⟨699686, by decide⟩ ⟨12, 2, 0, 699686, 91751, 3057, 65536⟩
    (by decide) selected_cut_27686

theorem unmarked_context_11_22937_699687 : frontier 10 ⟨699687, by decide⟩
    (prefixCache 11 22937) (prefixPartial 11 22937) = false := by
  decide +kernel

theorem node_context_11_22937_699687 : EJMOriginalGlobalDAGData.nodes 10 ⟨699687, by decide⟩ =
    .split (coordinate 11) (![⟨699617, by decide⟩,⟨642794, by decide⟩,⟨699649, by decide⟩,⟨699686, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22937_699687 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22937 ⟨699687, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22937
    ⟨699687, by decide⟩ (by decide) (![⟨699617, by decide⟩,⟨642794, by decide⟩,⟨699649, by decide⟩,⟨699686, by decide⟩]) unmarked_context_11_22937_699687 node_context_11_22937_699687
  intro a
  fin_cases a
  · exact context_12_91748_699617
  · exact context_12_91749_642794
  · exact context_12_91750_699649
  · exact context_12_91751_699686

theorem selected_cut_27687 : selected 9 ⟨699721, by decide⟩
    (prefixPartial 12 91752) = some ⟨12, 2, 0, 699721, 91752, 2709, 65536⟩ := by
  decide +kernel

theorem context_12_91752_699721 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91752 ⟨699721, by decide⟩ :=
  accepted_of_selected 12 91752 ⟨699721, by decide⟩ ⟨12, 2, 0, 699721, 91752, 2709, 65536⟩
    (by decide) selected_cut_27687

theorem selected_cut_27688 : selected 9 ⟨289098, by decide⟩
    (prefixPartial 12 91753) = some ⟨12, 1, 0, 289098, 91753, 1, 65536⟩ := by
  decide +kernel

theorem context_12_91753_289098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91753 ⟨289098, by decide⟩ :=
  accepted_of_selected 12 91753 ⟨289098, by decide⟩ ⟨12, 1, 0, 289098, 91753, 1, 65536⟩
    (by decide) selected_cut_27688

theorem selected_cut_27689 : selected 9 ⟨445248, by decide⟩
    (prefixPartial 12 91754) = some ⟨12, 1, 0, 445248, 91754, 1, 65536⟩ := by
  decide +kernel

theorem context_12_91754_445248 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91754 ⟨445248, by decide⟩ :=
  accepted_of_selected 12 91754 ⟨445248, by decide⟩ ⟨12, 1, 0, 445248, 91754, 1, 65536⟩
    (by decide) selected_cut_27689

theorem selected_cut_27690 : selected 9 ⟨699753, by decide⟩
    (prefixPartial 12 91755) = some ⟨12, 2, 0, 699753, 91755, 2557, 65536⟩ := by
  decide +kernel

theorem context_12_91755_699753 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91755 ⟨699753, by decide⟩ :=
  accepted_of_selected 12 91755 ⟨699753, by decide⟩ ⟨12, 2, 0, 699753, 91755, 2557, 65536⟩
    (by decide) selected_cut_27690

theorem unmarked_context_11_22938_699754 : frontier 10 ⟨699754, by decide⟩
    (prefixCache 11 22938) (prefixPartial 11 22938) = false := by
  decide +kernel

theorem node_context_11_22938_699754 : EJMOriginalGlobalDAGData.nodes 10 ⟨699754, by decide⟩ =
    .split (coordinate 11) (![⟨699721, by decide⟩,⟨289098, by decide⟩,⟨445248, by decide⟩,⟨699753, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22938_699754 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22938 ⟨699754, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22938
    ⟨699754, by decide⟩ (by decide) (![⟨699721, by decide⟩,⟨289098, by decide⟩,⟨445248, by decide⟩,⟨699753, by decide⟩]) unmarked_context_11_22938_699754 node_context_11_22938_699754
  intro a
  fin_cases a
  · exact context_12_91752_699721
  · exact context_12_91753_289098
  · exact context_12_91754_445248
  · exact context_12_91755_699753

theorem selected_cut_27691 : selected 9 ⟨699790, by decide⟩
    (prefixPartial 12 91756) = some ⟨12, 2, 0, 699790, 91756, 3105, 65536⟩ := by
  decide +kernel

theorem context_12_91756_699790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91756 ⟨699790, by decide⟩ :=
  accepted_of_selected 12 91756 ⟨699790, by decide⟩ ⟨12, 2, 0, 699790, 91756, 3105, 65536⟩
    (by decide) selected_cut_27691

theorem selected_cut_27692 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 367028) = some ⟨13, 1, 0, 3444, 367028, 1, 16384⟩ := by
  decide +kernel

theorem context_13_367028_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367028 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 367028 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 367028, 1, 16384⟩
    (by decide) selected_cut_27692

theorem selected_cut_27693 : selected 8 ⟨699808, by decide⟩
    (prefixPartial 13 367029) = some ⟨13, 2, 0, 699808, 367029, 1133, 16384⟩ := by
  decide +kernel

theorem context_13_367029_699808 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367029 ⟨699808, by decide⟩ :=
  accepted_of_selected 13 367029 ⟨699808, by decide⟩ ⟨13, 2, 0, 699808, 367029, 1133, 16384⟩
    (by decide) selected_cut_27693

theorem selected_cut_27694 : selected 8 ⟨699853, by decide⟩
    (prefixPartial 13 367030) = some ⟨13, 2, 0, 699853, 367030, 2189, 16384⟩ := by
  decide +kernel

theorem context_13_367030_699853 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367030 ⟨699853, by decide⟩ :=
  accepted_of_selected 13 367030 ⟨699853, by decide⟩ ⟨13, 2, 0, 699853, 367030, 2189, 16384⟩
    (by decide) selected_cut_27694

theorem selected_cut_27695 : selected 8 ⟨699869, by decide⟩
    (prefixPartial 13 367031) = some ⟨13, 2, 0, 699869, 367031, 1057, 16384⟩ := by
  decide +kernel

theorem context_13_367031_699869 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367031 ⟨699869, by decide⟩ :=
  accepted_of_selected 13 367031 ⟨699869, by decide⟩ ⟨13, 2, 0, 699869, 367031, 1057, 16384⟩
    (by decide) selected_cut_27695

theorem unmarked_context_12_91757_699870 : frontier 9 ⟨699870, by decide⟩
    (prefixCache 12 91757) (prefixPartial 12 91757) = false := by
  decide +kernel

theorem node_context_12_91757_699870 : EJMOriginalGlobalDAGData.nodes 9 ⟨699870, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨699808, by decide⟩,⟨699853, by decide⟩,⟨699869, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91757_699870 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91757 ⟨699870, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91757
    ⟨699870, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨699808, by decide⟩,⟨699853, by decide⟩,⟨699869, by decide⟩]) unmarked_context_12_91757_699870 node_context_12_91757_699870
  intro a
  fin_cases a
  · exact context_13_367028_3444
  · exact context_13_367029_699808
  · exact context_13_367030_699853
  · exact context_13_367031_699869

theorem selected_cut_27696 : selected 9 ⟨699905, by decide⟩
    (prefixPartial 12 91758) = some ⟨12, 2, 0, 699905, 91758, 2569, 65536⟩ := by
  decide +kernel

theorem context_12_91758_699905 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91758 ⟨699905, by decide⟩ :=
  accepted_of_selected 12 91758 ⟨699905, by decide⟩ ⟨12, 2, 0, 699905, 91758, 2569, 65536⟩
    (by decide) selected_cut_27696

theorem selected_cut_27697 : selected 9 ⟨699938, by decide⟩
    (prefixPartial 12 91759) = some ⟨12, 2, 0, 699938, 91759, 2929, 65536⟩ := by
  decide +kernel

theorem context_12_91759_699938 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91759 ⟨699938, by decide⟩ :=
  accepted_of_selected 12 91759 ⟨699938, by decide⟩ ⟨12, 2, 0, 699938, 91759, 2929, 65536⟩
    (by decide) selected_cut_27697

theorem unmarked_context_11_22939_699939 : frontier 10 ⟨699939, by decide⟩
    (prefixCache 11 22939) (prefixPartial 11 22939) = false := by
  decide +kernel

theorem node_context_11_22939_699939 : EJMOriginalGlobalDAGData.nodes 10 ⟨699939, by decide⟩ =
    .split (coordinate 11) (![⟨699790, by decide⟩,⟨699870, by decide⟩,⟨699905, by decide⟩,⟨699938, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22939_699939 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22939 ⟨699939, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22939
    ⟨699939, by decide⟩ (by decide) (![⟨699790, by decide⟩,⟨699870, by decide⟩,⟨699905, by decide⟩,⟨699938, by decide⟩]) unmarked_context_11_22939_699939 node_context_11_22939_699939
  intro a
  fin_cases a
  · exact context_12_91756_699790
  · exact context_12_91757_699870
  · exact context_12_91758_699905
  · exact context_12_91759_699938

theorem unmarked_context_10_5734_699940 : frontier 11 ⟨699940, by decide⟩
    (prefixCache 10 5734) (prefixPartial 10 5734) = false := by
  decide +kernel

theorem node_context_10_5734_699940 : EJMOriginalGlobalDAGData.nodes 11 ⟨699940, by decide⟩ =
    .split (coordinate 10) (![⟨699580, by decide⟩,⟨699687, by decide⟩,⟨699754, by decide⟩,⟨699939, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5734_699940 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5734 ⟨699940, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5734
    ⟨699940, by decide⟩ (by decide) (![⟨699580, by decide⟩,⟨699687, by decide⟩,⟨699754, by decide⟩,⟨699939, by decide⟩]) unmarked_context_10_5734_699940 node_context_10_5734_699940
  intro a
  fin_cases a
  · exact context_11_22936_699580
  · exact context_11_22937_699687
  · exact context_11_22938_699754
  · exact context_11_22939_699939

theorem selected_cut_27698 : selected 9 ⟨699974, by decide⟩
    (prefixPartial 12 91760) = some ⟨12, 2, 0, 699974, 91760, 2657, 65536⟩ := by
  decide +kernel

theorem context_12_91760_699974 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91760 ⟨699974, by decide⟩ :=
  accepted_of_selected 12 91760 ⟨699974, by decide⟩ ⟨12, 2, 0, 699974, 91760, 2657, 65536⟩
    (by decide) selected_cut_27698

theorem selected_cut_27699 : selected 9 ⟨700034, by decide⟩
    (prefixPartial 12 91761) = some ⟨12, 2, 0, 700034, 91761, 4093, 65536⟩ := by
  decide +kernel

theorem context_12_91761_700034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91761 ⟨700034, by decide⟩ :=
  accepted_of_selected 12 91761 ⟨700034, by decide⟩ ⟨12, 2, 0, 700034, 91761, 4093, 65536⟩
    (by decide) selected_cut_27699

theorem selected_cut_27700 : selected 9 ⟨700067, by decide⟩
    (prefixPartial 12 91762) = some ⟨12, 2, 0, 700067, 91762, 2285, 65536⟩ := by
  decide +kernel

theorem context_12_91762_700067 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91762 ⟨700067, by decide⟩ :=
  accepted_of_selected 12 91762 ⟨700067, by decide⟩ ⟨12, 2, 0, 700067, 91762, 2285, 65536⟩
    (by decide) selected_cut_27700

theorem selected_cut_27701 : selected 9 ⟨700112, by decide⟩
    (prefixPartial 12 91763) = some ⟨12, 2, 0, 700112, 91763, 2961, 65536⟩ := by
  decide +kernel

theorem context_12_91763_700112 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91763 ⟨700112, by decide⟩ :=
  accepted_of_selected 12 91763 ⟨700112, by decide⟩ ⟨12, 2, 0, 700112, 91763, 2961, 65536⟩
    (by decide) selected_cut_27701

theorem unmarked_context_11_22940_700113 : frontier 10 ⟨700113, by decide⟩
    (prefixCache 11 22940) (prefixPartial 11 22940) = false := by
  decide +kernel

theorem node_context_11_22940_700113 : EJMOriginalGlobalDAGData.nodes 10 ⟨700113, by decide⟩ =
    .split (coordinate 11) (![⟨699974, by decide⟩,⟨700034, by decide⟩,⟨700067, by decide⟩,⟨700112, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22940_700113 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22940 ⟨700113, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22940
    ⟨700113, by decide⟩ (by decide) (![⟨699974, by decide⟩,⟨700034, by decide⟩,⟨700067, by decide⟩,⟨700112, by decide⟩]) unmarked_context_11_22940_700113 node_context_11_22940_700113
  intro a
  fin_cases a
  · exact context_12_91760_699974
  · exact context_12_91761_700034
  · exact context_12_91762_700067
  · exact context_12_91763_700112

theorem selected_cut_27702 : selected 9 ⟨700138, by decide⟩
    (prefixPartial 12 91764) = some ⟨12, 2, 0, 700138, 91764, 2137, 65536⟩ := by
  decide +kernel

theorem context_12_91764_700138 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91764 ⟨700138, by decide⟩ :=
  accepted_of_selected 12 91764 ⟨700138, by decide⟩ ⟨12, 2, 0, 700138, 91764, 2137, 65536⟩
    (by decide) selected_cut_27702

theorem selected_cut_27703 : selected 9 ⟨642794, by decide⟩
    (prefixPartial 12 91765) = some ⟨12, 1, 0, 642794, 91765, 1, 65536⟩ := by
  decide +kernel

theorem context_12_91765_642794 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91765 ⟨642794, by decide⟩ :=
  accepted_of_selected 12 91765 ⟨642794, by decide⟩ ⟨12, 1, 0, 642794, 91765, 1, 65536⟩
    (by decide) selected_cut_27703

theorem selected_cut_27704 : selected 9 ⟨700167, by decide⟩
    (prefixPartial 12 91766) = some ⟨12, 2, 0, 700167, 91766, 1965, 65536⟩ := by
  decide +kernel

theorem context_12_91766_700167 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91766 ⟨700167, by decide⟩ :=
  accepted_of_selected 12 91766 ⟨700167, by decide⟩ ⟨12, 2, 0, 700167, 91766, 1965, 65536⟩
    (by decide) selected_cut_27704

theorem selected_cut_27705 : selected 9 ⟨700208, by decide⟩
    (prefixPartial 12 91767) = some ⟨12, 2, 0, 700208, 91767, 2541, 65536⟩ := by
  decide +kernel

theorem context_12_91767_700208 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91767 ⟨700208, by decide⟩ :=
  accepted_of_selected 12 91767 ⟨700208, by decide⟩ ⟨12, 2, 0, 700208, 91767, 2541, 65536⟩
    (by decide) selected_cut_27705

theorem unmarked_context_11_22941_700209 : frontier 10 ⟨700209, by decide⟩
    (prefixCache 11 22941) (prefixPartial 11 22941) = false := by
  decide +kernel

theorem node_context_11_22941_700209 : EJMOriginalGlobalDAGData.nodes 10 ⟨700209, by decide⟩ =
    .split (coordinate 11) (![⟨700138, by decide⟩,⟨642794, by decide⟩,⟨700167, by decide⟩,⟨700208, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22941_700209 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22941 ⟨700209, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22941
    ⟨700209, by decide⟩ (by decide) (![⟨700138, by decide⟩,⟨642794, by decide⟩,⟨700167, by decide⟩,⟨700208, by decide⟩]) unmarked_context_11_22941_700209 node_context_11_22941_700209
  intro a
  fin_cases a
  · exact context_12_91764_700138
  · exact context_12_91765_642794
  · exact context_12_91766_700167
  · exact context_12_91767_700208

theorem selected_cut_27706 : selected 9 ⟨700239, by decide⟩
    (prefixPartial 12 91768) = some ⟨12, 2, 0, 700239, 91768, 2185, 65536⟩ := by
  decide +kernel

theorem context_12_91768_700239 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91768 ⟨700239, by decide⟩ :=
  accepted_of_selected 12 91768 ⟨700239, by decide⟩ ⟨12, 2, 0, 700239, 91768, 2185, 65536⟩
    (by decide) selected_cut_27706

theorem selected_cut_27707 : selected 9 ⟨700285, by decide⟩
    (prefixPartial 12 91769) = some ⟨12, 2, 0, 700285, 91769, 3373, 65536⟩ := by
  decide +kernel

theorem context_12_91769_700285 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91769 ⟨700285, by decide⟩ :=
  accepted_of_selected 12 91769 ⟨700285, by decide⟩ ⟨12, 2, 0, 700285, 91769, 3373, 65536⟩
    (by decide) selected_cut_27707

theorem selected_cut_27708 : selected 9 ⟨700321, by decide⟩
    (prefixPartial 12 91770) = some ⟨12, 2, 0, 700321, 91770, 3385, 65536⟩ := by
  decide +kernel

theorem context_12_91770_700321 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91770 ⟨700321, by decide⟩ :=
  accepted_of_selected 12 91770 ⟨700321, by decide⟩ ⟨12, 2, 0, 700321, 91770, 3385, 65536⟩
    (by decide) selected_cut_27708

theorem selected_cut_27709 : selected 9 ⟨700350, by decide⟩
    (prefixPartial 12 91771) = some ⟨12, 2, 0, 700350, 91771, 2121, 65536⟩ := by
  decide +kernel

theorem context_12_91771_700350 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91771 ⟨700350, by decide⟩ :=
  accepted_of_selected 12 91771 ⟨700350, by decide⟩ ⟨12, 2, 0, 700350, 91771, 2121, 65536⟩
    (by decide) selected_cut_27709

theorem unmarked_context_11_22942_700351 : frontier 10 ⟨700351, by decide⟩
    (prefixCache 11 22942) (prefixPartial 11 22942) = false := by
  decide +kernel

theorem node_context_11_22942_700351 : EJMOriginalGlobalDAGData.nodes 10 ⟨700351, by decide⟩ =
    .split (coordinate 11) (![⟨700239, by decide⟩,⟨700285, by decide⟩,⟨700321, by decide⟩,⟨700350, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22942_700351 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22942 ⟨700351, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22942
    ⟨700351, by decide⟩ (by decide) (![⟨700239, by decide⟩,⟨700285, by decide⟩,⟨700321, by decide⟩,⟨700350, by decide⟩]) unmarked_context_11_22942_700351 node_context_11_22942_700351
  intro a
  fin_cases a
  · exact context_12_91768_700239
  · exact context_12_91769_700285
  · exact context_12_91770_700321
  · exact context_12_91771_700350

theorem selected_cut_27710 : selected 9 ⟨700382, by decide⟩
    (prefixPartial 12 91772) = some ⟨12, 2, 0, 700382, 91772, 2061, 65536⟩ := by
  decide +kernel

theorem context_12_91772_700382 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91772 ⟨700382, by decide⟩ :=
  accepted_of_selected 12 91772 ⟨700382, by decide⟩ ⟨12, 2, 0, 700382, 91772, 2061, 65536⟩
    (by decide) selected_cut_27710

theorem selected_cut_27711 : selected 9 ⟨700424, by decide⟩
    (prefixPartial 12 91773) = some ⟨12, 2, 0, 700424, 91773, 3217, 65536⟩ := by
  decide +kernel

theorem context_12_91773_700424 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91773 ⟨700424, by decide⟩ :=
  accepted_of_selected 12 91773 ⟨700424, by decide⟩ ⟨12, 2, 0, 700424, 91773, 3217, 65536⟩
    (by decide) selected_cut_27711

theorem selected_cut_27712 : selected 9 ⟨700446, by decide⟩
    (prefixPartial 12 91774) = some ⟨12, 2, 0, 700446, 91774, 1737, 65536⟩ := by
  decide +kernel

theorem context_12_91774_700446 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91774 ⟨700446, by decide⟩ :=
  accepted_of_selected 12 91774 ⟨700446, by decide⟩ ⟨12, 2, 0, 700446, 91774, 1737, 65536⟩
    (by decide) selected_cut_27712

theorem selected_cut_27713 : selected 9 ⟨700474, by decide⟩
    (prefixPartial 12 91775) = some ⟨12, 2, 0, 700474, 91775, 2289, 65536⟩ := by
  decide +kernel

theorem context_12_91775_700474 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91775 ⟨700474, by decide⟩ :=
  accepted_of_selected 12 91775 ⟨700474, by decide⟩ ⟨12, 2, 0, 700474, 91775, 2289, 65536⟩
    (by decide) selected_cut_27713

theorem unmarked_context_11_22943_700475 : frontier 10 ⟨700475, by decide⟩
    (prefixCache 11 22943) (prefixPartial 11 22943) = false := by
  decide +kernel

theorem node_context_11_22943_700475 : EJMOriginalGlobalDAGData.nodes 10 ⟨700475, by decide⟩ =
    .split (coordinate 11) (![⟨700382, by decide⟩,⟨700424, by decide⟩,⟨700446, by decide⟩,⟨700474, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22943_700475 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22943 ⟨700475, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22943
    ⟨700475, by decide⟩ (by decide) (![⟨700382, by decide⟩,⟨700424, by decide⟩,⟨700446, by decide⟩,⟨700474, by decide⟩]) unmarked_context_11_22943_700475 node_context_11_22943_700475
  intro a
  fin_cases a
  · exact context_12_91772_700382
  · exact context_12_91773_700424
  · exact context_12_91774_700446
  · exact context_12_91775_700474

theorem unmarked_context_10_5735_700476 : frontier 11 ⟨700476, by decide⟩
    (prefixCache 10 5735) (prefixPartial 10 5735) = false := by
  decide +kernel

theorem node_context_10_5735_700476 : EJMOriginalGlobalDAGData.nodes 11 ⟨700476, by decide⟩ =
    .split (coordinate 10) (![⟨700113, by decide⟩,⟨700209, by decide⟩,⟨700351, by decide⟩,⟨700475, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5735_700476 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5735 ⟨700476, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5735
    ⟨700476, by decide⟩ (by decide) (![⟨700113, by decide⟩,⟨700209, by decide⟩,⟨700351, by decide⟩,⟨700475, by decide⟩]) unmarked_context_10_5735_700476 node_context_10_5735_700476
  intro a
  fin_cases a
  · exact context_11_22940_700113
  · exact context_11_22941_700209
  · exact context_11_22942_700351
  · exact context_11_22943_700475

theorem unmarked_context_9_1433_700477 : frontier 12 ⟨700477, by decide⟩
    (prefixCache 9 1433) (prefixPartial 9 1433) = false := by
  decide +kernel

theorem node_context_9_1433_700477 : EJMOriginalGlobalDAGData.nodes 12 ⟨700477, by decide⟩ =
    .split (coordinate 9) (![⟨699039, by decide⟩,⟨699377, by decide⟩,⟨699940, by decide⟩,⟨700476, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1433_700477 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1433 ⟨700477, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1433
    ⟨700477, by decide⟩ (by decide) (![⟨699039, by decide⟩,⟨699377, by decide⟩,⟨699940, by decide⟩,⟨700476, by decide⟩]) unmarked_context_9_1433_700477 node_context_9_1433_700477
  intro a
  fin_cases a
  · exact context_10_5732_699039
  · exact context_10_5733_699377
  · exact context_10_5734_699940
  · exact context_10_5735_700476

theorem selected_cut_27714 : selected 9 ⟨700495, by decide⟩
    (prefixPartial 12 91776) = some ⟨12, 2, 0, 700495, 91776, 1553, 65536⟩ := by
  decide +kernel

theorem context_12_91776_700495 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91776 ⟨700495, by decide⟩ :=
  accepted_of_selected 12 91776 ⟨700495, by decide⟩ ⟨12, 2, 0, 700495, 91776, 1553, 65536⟩
    (by decide) selected_cut_27714

theorem selected_cut_27715 : selected 9 ⟨700520, by decide⟩
    (prefixPartial 12 91777) = some ⟨12, 2, 0, 700520, 91777, 1689, 65536⟩ := by
  decide +kernel

theorem context_12_91777_700520 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91777 ⟨700520, by decide⟩ :=
  accepted_of_selected 12 91777 ⟨700520, by decide⟩ ⟨12, 2, 0, 700520, 91777, 1689, 65536⟩
    (by decide) selected_cut_27715

theorem selected_cut_27716 : selected 9 ⟨700543, by decide⟩
    (prefixPartial 12 91778) = some ⟨12, 2, 0, 700543, 91778, 1521, 65536⟩ := by
  decide +kernel

theorem context_12_91778_700543 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91778 ⟨700543, by decide⟩ :=
  accepted_of_selected 12 91778 ⟨700543, by decide⟩ ⟨12, 2, 0, 700543, 91778, 1521, 65536⟩
    (by decide) selected_cut_27716

theorem selected_cut_27717 : selected 9 ⟨700568, by decide⟩
    (prefixPartial 12 91779) = some ⟨12, 2, 0, 700568, 91779, 1753, 65536⟩ := by
  decide +kernel

theorem context_12_91779_700568 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91779 ⟨700568, by decide⟩ :=
  accepted_of_selected 12 91779 ⟨700568, by decide⟩ ⟨12, 2, 0, 700568, 91779, 1753, 65536⟩
    (by decide) selected_cut_27717

theorem unmarked_context_11_22944_700569 : frontier 10 ⟨700569, by decide⟩
    (prefixCache 11 22944) (prefixPartial 11 22944) = false := by
  decide +kernel

theorem node_context_11_22944_700569 : EJMOriginalGlobalDAGData.nodes 10 ⟨700569, by decide⟩ =
    .split (coordinate 11) (![⟨700495, by decide⟩,⟨700520, by decide⟩,⟨700543, by decide⟩,⟨700568, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22944_700569 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22944 ⟨700569, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22944
    ⟨700569, by decide⟩ (by decide) (![⟨700495, by decide⟩,⟨700520, by decide⟩,⟨700543, by decide⟩,⟨700568, by decide⟩]) unmarked_context_11_22944_700569 node_context_11_22944_700569
  intro a
  fin_cases a
  · exact context_12_91776_700495
  · exact context_12_91777_700520
  · exact context_12_91778_700543
  · exact context_12_91779_700568

theorem selected_cut_27718 : selected 9 ⟨700588, by decide⟩
    (prefixPartial 12 91780) = some ⟨12, 2, 0, 700588, 91780, 1789, 65536⟩ := by
  decide +kernel

theorem context_12_91780_700588 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91780 ⟨700588, by decide⟩ :=
  accepted_of_selected 12 91780 ⟨700588, by decide⟩ ⟨12, 2, 0, 700588, 91780, 1789, 65536⟩
    (by decide) selected_cut_27718

theorem selected_cut_27719 : selected 9 ⟨700610, by decide⟩
    (prefixPartial 12 91781) = some ⟨12, 2, 0, 700610, 91781, 1653, 65536⟩ := by
  decide +kernel

theorem context_12_91781_700610 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91781 ⟨700610, by decide⟩ :=
  accepted_of_selected 12 91781 ⟨700610, by decide⟩ ⟨12, 2, 0, 700610, 91781, 1653, 65536⟩
    (by decide) selected_cut_27719

theorem selected_cut_27720 : selected 9 ⟨700631, by decide⟩
    (prefixPartial 12 91782) = some ⟨12, 2, 0, 700631, 91782, 1649, 65536⟩ := by
  decide +kernel

theorem context_12_91782_700631 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91782 ⟨700631, by decide⟩ :=
  accepted_of_selected 12 91782 ⟨700631, by decide⟩ ⟨12, 2, 0, 700631, 91782, 1649, 65536⟩
    (by decide) selected_cut_27720

theorem selected_cut_27721 : selected 9 ⟨700651, by decide⟩
    (prefixPartial 12 91783) = some ⟨12, 2, 0, 700651, 91783, 1873, 65536⟩ := by
  decide +kernel

theorem context_12_91783_700651 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91783 ⟨700651, by decide⟩ :=
  accepted_of_selected 12 91783 ⟨700651, by decide⟩ ⟨12, 2, 0, 700651, 91783, 1873, 65536⟩
    (by decide) selected_cut_27721

theorem unmarked_context_11_22945_700652 : frontier 10 ⟨700652, by decide⟩
    (prefixCache 11 22945) (prefixPartial 11 22945) = false := by
  decide +kernel

theorem node_context_11_22945_700652 : EJMOriginalGlobalDAGData.nodes 10 ⟨700652, by decide⟩ =
    .split (coordinate 11) (![⟨700588, by decide⟩,⟨700610, by decide⟩,⟨700631, by decide⟩,⟨700651, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22945_700652 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22945 ⟨700652, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22945
    ⟨700652, by decide⟩ (by decide) (![⟨700588, by decide⟩,⟨700610, by decide⟩,⟨700631, by decide⟩,⟨700651, by decide⟩]) unmarked_context_11_22945_700652 node_context_11_22945_700652
  intro a
  fin_cases a
  · exact context_12_91780_700588
  · exact context_12_91781_700610
  · exact context_12_91782_700631
  · exact context_12_91783_700651

theorem selected_cut_27722 : selected 9 ⟨700676, by decide⟩
    (prefixPartial 12 91784) = some ⟨12, 2, 0, 700676, 91784, 1865, 65536⟩ := by
  decide +kernel

theorem context_12_91784_700676 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91784 ⟨700676, by decide⟩ :=
  accepted_of_selected 12 91784 ⟨700676, by decide⟩ ⟨12, 2, 0, 700676, 91784, 1865, 65536⟩
    (by decide) selected_cut_27722

theorem selected_cut_27723 : selected 9 ⟨700699, by decide⟩
    (prefixPartial 12 91785) = some ⟨12, 2, 0, 700699, 91785, 1849, 65536⟩ := by
  decide +kernel

theorem context_12_91785_700699 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91785 ⟨700699, by decide⟩ :=
  accepted_of_selected 12 91785 ⟨700699, by decide⟩ ⟨12, 2, 0, 700699, 91785, 1849, 65536⟩
    (by decide) selected_cut_27723

theorem selected_cut_27724 : selected 9 ⟨448662, by decide⟩
    (prefixPartial 12 91786) = some ⟨12, 1, 0, 448662, 91786, 1, 65536⟩ := by
  decide +kernel

theorem context_12_91786_448662 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91786 ⟨448662, by decide⟩ :=
  accepted_of_selected 12 91786 ⟨448662, by decide⟩ ⟨12, 1, 0, 448662, 91786, 1, 65536⟩
    (by decide) selected_cut_27724

theorem selected_cut_27725 : selected 9 ⟨700723, by decide⟩
    (prefixPartial 12 91787) = some ⟨12, 2, 0, 700723, 91787, 1749, 65536⟩ := by
  decide +kernel

theorem context_12_91787_700723 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91787 ⟨700723, by decide⟩ :=
  accepted_of_selected 12 91787 ⟨700723, by decide⟩ ⟨12, 2, 0, 700723, 91787, 1749, 65536⟩
    (by decide) selected_cut_27725

theorem unmarked_context_11_22946_700724 : frontier 10 ⟨700724, by decide⟩
    (prefixCache 11 22946) (prefixPartial 11 22946) = false := by
  decide +kernel

theorem node_context_11_22946_700724 : EJMOriginalGlobalDAGData.nodes 10 ⟨700724, by decide⟩ =
    .split (coordinate 11) (![⟨700676, by decide⟩,⟨700699, by decide⟩,⟨448662, by decide⟩,⟨700723, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22946_700724 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22946 ⟨700724, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22946
    ⟨700724, by decide⟩ (by decide) (![⟨700676, by decide⟩,⟨700699, by decide⟩,⟨448662, by decide⟩,⟨700723, by decide⟩]) unmarked_context_11_22946_700724 node_context_11_22946_700724
  intro a
  fin_cases a
  · exact context_12_91784_700676
  · exact context_12_91785_700699
  · exact context_12_91786_448662
  · exact context_12_91787_700723

theorem selected_cut_27726 : selected 9 ⟨700746, by decide⟩
    (prefixPartial 12 91788) = some ⟨12, 2, 0, 700746, 91788, 1825, 65536⟩ := by
  decide +kernel

theorem context_12_91788_700746 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91788 ⟨700746, by decide⟩ :=
  accepted_of_selected 12 91788 ⟨700746, by decide⟩ ⟨12, 2, 0, 700746, 91788, 1825, 65536⟩
    (by decide) selected_cut_27726

theorem selected_cut_27727 : selected 9 ⟨700769, by decide⟩
    (prefixPartial 12 91789) = some ⟨12, 2, 0, 700769, 91789, 1733, 65536⟩ := by
  decide +kernel

theorem context_12_91789_700769 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91789 ⟨700769, by decide⟩ :=
  accepted_of_selected 12 91789 ⟨700769, by decide⟩ ⟨12, 2, 0, 700769, 91789, 1733, 65536⟩
    (by decide) selected_cut_27727

theorem selected_cut_27728 : selected 9 ⟨700790, by decide⟩
    (prefixPartial 12 91790) = some ⟨12, 2, 0, 700790, 91790, 1637, 65536⟩ := by
  decide +kernel

theorem context_12_91790_700790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91790 ⟨700790, by decide⟩ :=
  accepted_of_selected 12 91790 ⟨700790, by decide⟩ ⟨12, 2, 0, 700790, 91790, 1637, 65536⟩
    (by decide) selected_cut_27728

theorem selected_cut_27729 : selected 9 ⟨700809, by decide⟩
    (prefixPartial 12 91791) = some ⟨12, 2, 0, 700809, 91791, 1857, 65536⟩ := by
  decide +kernel

theorem context_12_91791_700809 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91791 ⟨700809, by decide⟩ :=
  accepted_of_selected 12 91791 ⟨700809, by decide⟩ ⟨12, 2, 0, 700809, 91791, 1857, 65536⟩
    (by decide) selected_cut_27729

theorem unmarked_context_11_22947_700810 : frontier 10 ⟨700810, by decide⟩
    (prefixCache 11 22947) (prefixPartial 11 22947) = false := by
  decide +kernel

theorem node_context_11_22947_700810 : EJMOriginalGlobalDAGData.nodes 10 ⟨700810, by decide⟩ =
    .split (coordinate 11) (![⟨700746, by decide⟩,⟨700769, by decide⟩,⟨700790, by decide⟩,⟨700809, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22947_700810 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22947 ⟨700810, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22947
    ⟨700810, by decide⟩ (by decide) (![⟨700746, by decide⟩,⟨700769, by decide⟩,⟨700790, by decide⟩,⟨700809, by decide⟩]) unmarked_context_11_22947_700810 node_context_11_22947_700810
  intro a
  fin_cases a
  · exact context_12_91788_700746
  · exact context_12_91789_700769
  · exact context_12_91790_700790
  · exact context_12_91791_700809

theorem unmarked_context_10_5736_700811 : frontier 11 ⟨700811, by decide⟩
    (prefixCache 10 5736) (prefixPartial 10 5736) = false := by
  decide +kernel

theorem node_context_10_5736_700811 : EJMOriginalGlobalDAGData.nodes 11 ⟨700811, by decide⟩ =
    .split (coordinate 10) (![⟨700569, by decide⟩,⟨700652, by decide⟩,⟨700724, by decide⟩,⟨700810, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5736_700811 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5736 ⟨700811, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5736
    ⟨700811, by decide⟩ (by decide) (![⟨700569, by decide⟩,⟨700652, by decide⟩,⟨700724, by decide⟩,⟨700810, by decide⟩]) unmarked_context_10_5736_700811 node_context_10_5736_700811
  intro a
  fin_cases a
  · exact context_11_22944_700569
  · exact context_11_22945_700652
  · exact context_11_22946_700724
  · exact context_11_22947_700810

theorem selected_cut_27730 : selected 9 ⟨700829, by decide⟩
    (prefixPartial 12 91792) = some ⟨12, 2, 0, 700829, 91792, 1845, 65536⟩ := by
  decide +kernel

theorem context_12_91792_700829 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91792 ⟨700829, by decide⟩ :=
  accepted_of_selected 12 91792 ⟨700829, by decide⟩ ⟨12, 2, 0, 700829, 91792, 1845, 65536⟩
    (by decide) selected_cut_27730

theorem selected_cut_27731 : selected 9 ⟨700850, by decide⟩
    (prefixPartial 12 91793) = some ⟨12, 2, 0, 700850, 91793, 1897, 65536⟩ := by
  decide +kernel

theorem context_12_91793_700850 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91793 ⟨700850, by decide⟩ :=
  accepted_of_selected 12 91793 ⟨700850, by decide⟩ ⟨12, 2, 0, 700850, 91793, 1897, 65536⟩
    (by decide) selected_cut_27731

theorem selected_cut_27732 : selected 9 ⟨700871, by decide⟩
    (prefixPartial 12 91794) = some ⟨12, 2, 0, 700871, 91794, 1621, 65536⟩ := by
  decide +kernel

theorem context_12_91794_700871 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91794 ⟨700871, by decide⟩ :=
  accepted_of_selected 12 91794 ⟨700871, by decide⟩ ⟨12, 2, 0, 700871, 91794, 1621, 65536⟩
    (by decide) selected_cut_27732

theorem selected_cut_27733 : selected 9 ⟨700893, by decide⟩
    (prefixPartial 12 91795) = some ⟨12, 2, 0, 700893, 91795, 2045, 65536⟩ := by
  decide +kernel

theorem context_12_91795_700893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91795 ⟨700893, by decide⟩ :=
  accepted_of_selected 12 91795 ⟨700893, by decide⟩ ⟨12, 2, 0, 700893, 91795, 2045, 65536⟩
    (by decide) selected_cut_27733

theorem unmarked_context_11_22948_700894 : frontier 10 ⟨700894, by decide⟩
    (prefixCache 11 22948) (prefixPartial 11 22948) = false := by
  decide +kernel

theorem node_context_11_22948_700894 : EJMOriginalGlobalDAGData.nodes 10 ⟨700894, by decide⟩ =
    .split (coordinate 11) (![⟨700829, by decide⟩,⟨700850, by decide⟩,⟨700871, by decide⟩,⟨700893, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22948_700894 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22948 ⟨700894, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22948
    ⟨700894, by decide⟩ (by decide) (![⟨700829, by decide⟩,⟨700850, by decide⟩,⟨700871, by decide⟩,⟨700893, by decide⟩]) unmarked_context_11_22948_700894 node_context_11_22948_700894
  intro a
  fin_cases a
  · exact context_12_91792_700829
  · exact context_12_91793_700850
  · exact context_12_91794_700871
  · exact context_12_91795_700893

theorem selected_cut_27734 : selected 9 ⟨700922, by decide⟩
    (prefixPartial 12 91796) = some ⟨12, 2, 0, 700922, 91796, 2549, 65536⟩ := by
  decide +kernel

theorem context_12_91796_700922 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91796 ⟨700922, by decide⟩ :=
  accepted_of_selected 12 91796 ⟨700922, by decide⟩ ⟨12, 2, 0, 700922, 91796, 2549, 65536⟩
    (by decide) selected_cut_27734

theorem selected_cut_27735 : selected 9 ⟨449506, by decide⟩
    (prefixPartial 12 91797) = some ⟨12, 1, 0, 449506, 91797, 1, 65536⟩ := by
  decide +kernel

theorem context_12_91797_449506 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91797 ⟨449506, by decide⟩ :=
  accepted_of_selected 12 91797 ⟨449506, by decide⟩ ⟨12, 1, 0, 449506, 91797, 1, 65536⟩
    (by decide) selected_cut_27735

theorem selected_cut_27736 : selected 9 ⟨333638, by decide⟩
    (prefixPartial 12 91798) = some ⟨12, 1, 0, 333638, 91798, 1, 65536⟩ := by
  decide +kernel

theorem context_12_91798_333638 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91798 ⟨333638, by decide⟩ :=
  accepted_of_selected 12 91798 ⟨333638, by decide⟩ ⟨12, 1, 0, 333638, 91798, 1, 65536⟩
    (by decide) selected_cut_27736

theorem selected_cut_27737 : selected 9 ⟨700955, by decide⟩
    (prefixPartial 12 91799) = some ⟨12, 2, 0, 700955, 91799, 2749, 65536⟩ := by
  decide +kernel

theorem context_12_91799_700955 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91799 ⟨700955, by decide⟩ :=
  accepted_of_selected 12 91799 ⟨700955, by decide⟩ ⟨12, 2, 0, 700955, 91799, 2749, 65536⟩
    (by decide) selected_cut_27737

theorem unmarked_context_11_22949_700956 : frontier 10 ⟨700956, by decide⟩
    (prefixCache 11 22949) (prefixPartial 11 22949) = false := by
  decide +kernel

theorem node_context_11_22949_700956 : EJMOriginalGlobalDAGData.nodes 10 ⟨700956, by decide⟩ =
    .split (coordinate 11) (![⟨700922, by decide⟩,⟨449506, by decide⟩,⟨333638, by decide⟩,⟨700955, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22949_700956 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22949 ⟨700956, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22949
    ⟨700956, by decide⟩ (by decide) (![⟨700922, by decide⟩,⟨449506, by decide⟩,⟨333638, by decide⟩,⟨700955, by decide⟩]) unmarked_context_11_22949_700956 node_context_11_22949_700956
  intro a
  fin_cases a
  · exact context_12_91796_700922
  · exact context_12_91797_449506
  · exact context_12_91798_333638
  · exact context_12_91799_700955

theorem selected_cut_27738 : selected 9 ⟨700977, by decide⟩
    (prefixPartial 12 91800) = some ⟨12, 2, 0, 700977, 91800, 1833, 65536⟩ := by
  decide +kernel

theorem context_12_91800_700977 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91800 ⟨700977, by decide⟩ :=
  accepted_of_selected 12 91800 ⟨700977, by decide⟩ ⟨12, 2, 0, 700977, 91800, 1833, 65536⟩
    (by decide) selected_cut_27738

theorem selected_cut_27739 : selected 9 ⟨700995, by decide⟩
    (prefixPartial 12 91801) = some ⟨12, 2, 0, 700995, 91801, 1845, 65536⟩ := by
  decide +kernel

theorem context_12_91801_700995 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91801 ⟨700995, by decide⟩ :=
  accepted_of_selected 12 91801 ⟨700995, by decide⟩ ⟨12, 2, 0, 700995, 91801, 1845, 65536⟩
    (by decide) selected_cut_27739

theorem selected_cut_27740 : selected 9 ⟨212113, by decide⟩
    (prefixPartial 12 91802) = some ⟨12, 1, 0, 212113, 91802, 1, 65536⟩ := by
  decide +kernel

theorem context_12_91802_212113 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91802 ⟨212113, by decide⟩ :=
  accepted_of_selected 12 91802 ⟨212113, by decide⟩ ⟨12, 1, 0, 212113, 91802, 1, 65536⟩
    (by decide) selected_cut_27740

theorem selected_cut_27741 : selected 9 ⟨701016, by decide⟩
    (prefixPartial 12 91803) = some ⟨12, 2, 0, 701016, 91803, 1793, 65536⟩ := by
  decide +kernel

theorem context_12_91803_701016 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91803 ⟨701016, by decide⟩ :=
  accepted_of_selected 12 91803 ⟨701016, by decide⟩ ⟨12, 2, 0, 701016, 91803, 1793, 65536⟩
    (by decide) selected_cut_27741

theorem unmarked_context_11_22950_701017 : frontier 10 ⟨701017, by decide⟩
    (prefixCache 11 22950) (prefixPartial 11 22950) = false := by
  decide +kernel

theorem node_context_11_22950_701017 : EJMOriginalGlobalDAGData.nodes 10 ⟨701017, by decide⟩ =
    .split (coordinate 11) (![⟨700977, by decide⟩,⟨700995, by decide⟩,⟨212113, by decide⟩,⟨701016, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22950_701017 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22950 ⟨701017, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22950
    ⟨701017, by decide⟩ (by decide) (![⟨700977, by decide⟩,⟨700995, by decide⟩,⟨212113, by decide⟩,⟨701016, by decide⟩]) unmarked_context_11_22950_701017 node_context_11_22950_701017
  intro a
  fin_cases a
  · exact context_12_91800_700977
  · exact context_12_91801_700995
  · exact context_12_91802_212113
  · exact context_12_91803_701016

theorem selected_cut_27742 : selected 9 ⟨701038, by decide⟩
    (prefixPartial 12 91804) = some ⟨12, 2, 0, 701038, 91804, 1813, 65536⟩ := by
  decide +kernel

theorem context_12_91804_701038 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91804 ⟨701038, by decide⟩ :=
  accepted_of_selected 12 91804 ⟨701038, by decide⟩ ⟨12, 2, 0, 701038, 91804, 1813, 65536⟩
    (by decide) selected_cut_27742

theorem selected_cut_27743 : selected 9 ⟨701057, by decide⟩
    (prefixPartial 12 91805) = some ⟨12, 2, 0, 701057, 91805, 1661, 65536⟩ := by
  decide +kernel

theorem context_12_91805_701057 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91805 ⟨701057, by decide⟩ :=
  accepted_of_selected 12 91805 ⟨701057, by decide⟩ ⟨12, 2, 0, 701057, 91805, 1661, 65536⟩
    (by decide) selected_cut_27743

theorem selected_cut_27744 : selected 9 ⟨701075, by decide⟩
    (prefixPartial 12 91806) = some ⟨12, 2, 0, 701075, 91806, 1577, 65536⟩ := by
  decide +kernel

theorem context_12_91806_701075 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91806 ⟨701075, by decide⟩ :=
  accepted_of_selected 12 91806 ⟨701075, by decide⟩ ⟨12, 2, 0, 701075, 91806, 1577, 65536⟩
    (by decide) selected_cut_27744

theorem selected_cut_27745 : selected 9 ⟨701089, by decide⟩
    (prefixPartial 12 91807) = some ⟨12, 2, 0, 701089, 91807, 1901, 65536⟩ := by
  decide +kernel

theorem context_12_91807_701089 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91807 ⟨701089, by decide⟩ :=
  accepted_of_selected 12 91807 ⟨701089, by decide⟩ ⟨12, 2, 0, 701089, 91807, 1901, 65536⟩
    (by decide) selected_cut_27745

theorem unmarked_context_11_22951_701090 : frontier 10 ⟨701090, by decide⟩
    (prefixCache 11 22951) (prefixPartial 11 22951) = false := by
  decide +kernel

theorem node_context_11_22951_701090 : EJMOriginalGlobalDAGData.nodes 10 ⟨701090, by decide⟩ =
    .split (coordinate 11) (![⟨701038, by decide⟩,⟨701057, by decide⟩,⟨701075, by decide⟩,⟨701089, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22951_701090 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22951 ⟨701090, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22951
    ⟨701090, by decide⟩ (by decide) (![⟨701038, by decide⟩,⟨701057, by decide⟩,⟨701075, by decide⟩,⟨701089, by decide⟩]) unmarked_context_11_22951_701090 node_context_11_22951_701090
  intro a
  fin_cases a
  · exact context_12_91804_701038
  · exact context_12_91805_701057
  · exact context_12_91806_701075
  · exact context_12_91807_701089

theorem unmarked_context_10_5737_701091 : frontier 11 ⟨701091, by decide⟩
    (prefixCache 10 5737) (prefixPartial 10 5737) = false := by
  decide +kernel

theorem node_context_10_5737_701091 : EJMOriginalGlobalDAGData.nodes 11 ⟨701091, by decide⟩ =
    .split (coordinate 10) (![⟨700894, by decide⟩,⟨700956, by decide⟩,⟨701017, by decide⟩,⟨701090, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5737_701091 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5737 ⟨701091, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5737
    ⟨701091, by decide⟩ (by decide) (![⟨700894, by decide⟩,⟨700956, by decide⟩,⟨701017, by decide⟩,⟨701090, by decide⟩]) unmarked_context_10_5737_701091 node_context_10_5737_701091
  intro a
  fin_cases a
  · exact context_11_22948_700894
  · exact context_11_22949_700956
  · exact context_11_22950_701017
  · exact context_11_22951_701090

theorem selected_cut_27746 : selected 9 ⟨701103, by decide⟩
    (prefixPartial 12 91808) = some ⟨12, 2, 0, 701103, 91808, 1345, 65536⟩ := by
  decide +kernel

theorem context_12_91808_701103 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91808 ⟨701103, by decide⟩ :=
  accepted_of_selected 12 91808 ⟨701103, by decide⟩ ⟨12, 2, 0, 701103, 91808, 1345, 65536⟩
    (by decide) selected_cut_27746

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
