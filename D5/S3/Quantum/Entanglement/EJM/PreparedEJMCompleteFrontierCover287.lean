/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover286
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem unmarked_context_12_91683_696449 : frontier 9 ⟨696449, by decide⟩
    (prefixCache 12 91683) (prefixPartial 12 91683) = false := by
  decide +kernel

theorem node_context_12_91683_696449 : EJMOriginalGlobalDAGData.nodes 9 ⟨696449, by decide⟩ =
    .split (coordinate 12) (![⟨696395, by decide⟩,⟨696421, by decide⟩,⟨696443, by decide⟩,⟨696448, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91683_696449 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91683 ⟨696449, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91683
    ⟨696449, by decide⟩ (by decide) (![⟨696395, by decide⟩,⟨696421, by decide⟩,⟨696443, by decide⟩,⟨696448, by decide⟩]) unmarked_context_12_91683_696449 node_context_12_91683_696449
  intro a
  fin_cases a
  · exact context_13_366732_696395
  · exact context_13_366733_696421
  · exact context_13_366734_696443
  · exact context_13_366735_696448

theorem unmarked_context_11_22920_696450 : frontier 10 ⟨696450, by decide⟩
    (prefixCache 11 22920) (prefixPartial 11 22920) = false := by
  decide +kernel

theorem node_context_11_22920_696450 : EJMOriginalGlobalDAGData.nodes 10 ⟨696450, by decide⟩ =
    .split (coordinate 11) (![⟨696264, by decide⟩,⟨696328, by decide⟩,⟨696378, by decide⟩,⟨696449, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22920_696450 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22920 ⟨696450, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22920
    ⟨696450, by decide⟩ (by decide) (![⟨696264, by decide⟩,⟨696328, by decide⟩,⟨696378, by decide⟩,⟨696449, by decide⟩]) unmarked_context_11_22920_696450 node_context_11_22920_696450
  intro a
  fin_cases a
  · exact context_12_91680_696264
  · exact context_12_91681_696328
  · exact context_12_91682_696378
  · exact context_12_91683_696449

theorem selected_cut_27556 : selected 9 ⟨696507, by decide⟩
    (prefixPartial 12 91684) = some ⟨12, 2, 0, 696507, 91684, 4017, 65536⟩ := by
  decide +kernel

theorem context_12_91684_696507 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91684 ⟨696507, by decide⟩ :=
  accepted_of_selected 12 91684 ⟨696507, by decide⟩ ⟨12, 2, 0, 696507, 91684, 4017, 65536⟩
    (by decide) selected_cut_27556

theorem selected_cut_27557 : selected 8 ⟨696519, by decide⟩
    (prefixPartial 13 366740) = some ⟨13, 2, 0, 696519, 366740, 933, 16384⟩ := by
  decide +kernel

theorem context_13_366740_696519 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366740 ⟨696519, by decide⟩ :=
  accepted_of_selected 13 366740 ⟨696519, by decide⟩ ⟨13, 2, 0, 696519, 366740, 933, 16384⟩
    (by decide) selected_cut_27557

theorem selected_cut_27558 : selected 8 ⟨696544, by decide⟩
    (prefixPartial 13 366741) = some ⟨13, 2, 0, 696544, 366741, 1537, 16384⟩ := by
  decide +kernel

theorem context_13_366741_696544 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366741 ⟨696544, by decide⟩ :=
  accepted_of_selected 13 366741 ⟨696544, by decide⟩ ⟨13, 2, 0, 696544, 366741, 1537, 16384⟩
    (by decide) selected_cut_27558

theorem selected_cut_27559 : selected 8 ⟨696560, by decide⟩
    (prefixPartial 13 366742) = some ⟨13, 2, 0, 696560, 366742, 1105, 16384⟩ := by
  decide +kernel

theorem context_13_366742_696560 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366742 ⟨696560, by decide⟩ :=
  accepted_of_selected 13 366742 ⟨696560, by decide⟩ ⟨13, 2, 0, 696560, 366742, 1105, 16384⟩
    (by decide) selected_cut_27559

theorem selected_cut_27560 : selected 8 ⟨696563, by decide⟩
    (prefixPartial 13 366743) = some ⟨13, 2, 0, 696563, 366743, 737, 16384⟩ := by
  decide +kernel

theorem context_13_366743_696563 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366743 ⟨696563, by decide⟩ :=
  accepted_of_selected 13 366743 ⟨696563, by decide⟩ ⟨13, 2, 0, 696563, 366743, 737, 16384⟩
    (by decide) selected_cut_27560

theorem unmarked_context_12_91685_696564 : frontier 9 ⟨696564, by decide⟩
    (prefixCache 12 91685) (prefixPartial 12 91685) = false := by
  decide +kernel

theorem node_context_12_91685_696564 : EJMOriginalGlobalDAGData.nodes 9 ⟨696564, by decide⟩ =
    .split (coordinate 12) (![⟨696519, by decide⟩,⟨696544, by decide⟩,⟨696560, by decide⟩,⟨696563, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91685_696564 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91685 ⟨696564, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91685
    ⟨696564, by decide⟩ (by decide) (![⟨696519, by decide⟩,⟨696544, by decide⟩,⟨696560, by decide⟩,⟨696563, by decide⟩]) unmarked_context_12_91685_696564 node_context_12_91685_696564
  intro a
  fin_cases a
  · exact context_13_366740_696519
  · exact context_13_366741_696544
  · exact context_13_366742_696560
  · exact context_13_366743_696563

theorem selected_cut_27561 : selected 9 ⟨696611, by decide⟩
    (prefixPartial 12 91686) = some ⟨12, 2, 0, 696611, 91686, 3669, 65536⟩ := by
  decide +kernel

theorem context_12_91686_696611 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91686 ⟨696611, by decide⟩ :=
  accepted_of_selected 12 91686 ⟨696611, by decide⟩ ⟨12, 2, 0, 696611, 91686, 3669, 65536⟩
    (by decide) selected_cut_27561

theorem selected_cut_27562 : selected 8 ⟨696624, by decide⟩
    (prefixPartial 13 366748) = some ⟨13, 2, 0, 696624, 366748, 921, 16384⟩ := by
  decide +kernel

theorem context_13_366748_696624 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366748 ⟨696624, by decide⟩ :=
  accepted_of_selected 13 366748 ⟨696624, by decide⟩ ⟨13, 2, 0, 696624, 366748, 921, 16384⟩
    (by decide) selected_cut_27562

theorem selected_cut_27563 : selected 8 ⟨696650, by decide⟩
    (prefixPartial 13 366749) = some ⟨13, 2, 0, 696650, 366749, 1705, 16384⟩ := by
  decide +kernel

theorem context_13_366749_696650 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366749 ⟨696650, by decide⟩ :=
  accepted_of_selected 13 366749 ⟨696650, by decide⟩ ⟨13, 2, 0, 696650, 366749, 1705, 16384⟩
    (by decide) selected_cut_27563

theorem selected_cut_27564 : selected 8 ⟨696667, by decide⟩
    (prefixPartial 13 366750) = some ⟨13, 2, 0, 696667, 366750, 1301, 16384⟩ := by
  decide +kernel

theorem context_13_366750_696667 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366750 ⟨696667, by decide⟩ :=
  accepted_of_selected 13 366750 ⟨696667, by decide⟩ ⟨13, 2, 0, 696667, 366750, 1301, 16384⟩
    (by decide) selected_cut_27564

theorem selected_cut_27565 : selected 8 ⟨696672, by decide⟩
    (prefixPartial 13 366751) = some ⟨13, 2, 0, 696672, 366751, 677, 16384⟩ := by
  decide +kernel

theorem context_13_366751_696672 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366751 ⟨696672, by decide⟩ :=
  accepted_of_selected 13 366751 ⟨696672, by decide⟩ ⟨13, 2, 0, 696672, 366751, 677, 16384⟩
    (by decide) selected_cut_27565

theorem unmarked_context_12_91687_696673 : frontier 9 ⟨696673, by decide⟩
    (prefixCache 12 91687) (prefixPartial 12 91687) = false := by
  decide +kernel

theorem node_context_12_91687_696673 : EJMOriginalGlobalDAGData.nodes 9 ⟨696673, by decide⟩ =
    .split (coordinate 12) (![⟨696624, by decide⟩,⟨696650, by decide⟩,⟨696667, by decide⟩,⟨696672, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91687_696673 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91687 ⟨696673, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91687
    ⟨696673, by decide⟩ (by decide) (![⟨696624, by decide⟩,⟨696650, by decide⟩,⟨696667, by decide⟩,⟨696672, by decide⟩]) unmarked_context_12_91687_696673 node_context_12_91687_696673
  intro a
  fin_cases a
  · exact context_13_366748_696624
  · exact context_13_366749_696650
  · exact context_13_366750_696667
  · exact context_13_366751_696672

theorem unmarked_context_11_22921_696674 : frontier 10 ⟨696674, by decide⟩
    (prefixCache 11 22921) (prefixPartial 11 22921) = false := by
  decide +kernel

theorem node_context_11_22921_696674 : EJMOriginalGlobalDAGData.nodes 10 ⟨696674, by decide⟩ =
    .split (coordinate 11) (![⟨696507, by decide⟩,⟨696564, by decide⟩,⟨696611, by decide⟩,⟨696673, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22921_696674 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22921 ⟨696674, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22921
    ⟨696674, by decide⟩ (by decide) (![⟨696507, by decide⟩,⟨696564, by decide⟩,⟨696611, by decide⟩,⟨696673, by decide⟩]) unmarked_context_11_22921_696674 node_context_11_22921_696674
  intro a
  fin_cases a
  · exact context_12_91684_696507
  · exact context_12_91685_696564
  · exact context_12_91686_696611
  · exact context_12_91687_696673

theorem selected_cut_27566 : selected 9 ⟨696727, by decide⟩
    (prefixPartial 12 91688) = some ⟨12, 2, 0, 696727, 91688, 4033, 65536⟩ := by
  decide +kernel

theorem context_12_91688_696727 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91688 ⟨696727, by decide⟩ :=
  accepted_of_selected 12 91688 ⟨696727, by decide⟩ ⟨12, 2, 0, 696727, 91688, 4033, 65536⟩
    (by decide) selected_cut_27566

theorem selected_cut_27567 : selected 8 ⟨696737, by decide⟩
    (prefixPartial 13 366756) = some ⟨13, 2, 0, 696737, 366756, 841, 16384⟩ := by
  decide +kernel

theorem context_13_366756_696737 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366756 ⟨696737, by decide⟩ :=
  accepted_of_selected 13 366756 ⟨696737, by decide⟩ ⟨13, 2, 0, 696737, 366756, 841, 16384⟩
    (by decide) selected_cut_27567

theorem selected_cut_27568 : selected 8 ⟨696771, by decide⟩
    (prefixPartial 13 366757) = some ⟨13, 2, 0, 696771, 366757, 1637, 16384⟩ := by
  decide +kernel

theorem context_13_366757_696771 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366757 ⟨696771, by decide⟩ :=
  accepted_of_selected 13 366757 ⟨696771, by decide⟩ ⟨13, 2, 0, 696771, 366757, 1637, 16384⟩
    (by decide) selected_cut_27568

theorem selected_cut_27569 : selected 8 ⟨696788, by decide⟩
    (prefixPartial 13 366758) = some ⟨13, 2, 0, 696788, 366758, 1297, 16384⟩ := by
  decide +kernel

theorem context_13_366758_696788 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366758 ⟨696788, by decide⟩ :=
  accepted_of_selected 13 366758 ⟨696788, by decide⟩ ⟨13, 2, 0, 696788, 366758, 1297, 16384⟩
    (by decide) selected_cut_27569

theorem selected_cut_27570 : selected 8 ⟨696792, by decide⟩
    (prefixPartial 13 366759) = some ⟨13, 2, 0, 696792, 366759, 833, 16384⟩ := by
  decide +kernel

theorem context_13_366759_696792 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366759 ⟨696792, by decide⟩ :=
  accepted_of_selected 13 366759 ⟨696792, by decide⟩ ⟨13, 2, 0, 696792, 366759, 833, 16384⟩
    (by decide) selected_cut_27570

theorem unmarked_context_12_91689_696793 : frontier 9 ⟨696793, by decide⟩
    (prefixCache 12 91689) (prefixPartial 12 91689) = false := by
  decide +kernel

theorem node_context_12_91689_696793 : EJMOriginalGlobalDAGData.nodes 9 ⟨696793, by decide⟩ =
    .split (coordinate 12) (![⟨696737, by decide⟩,⟨696771, by decide⟩,⟨696788, by decide⟩,⟨696792, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91689_696793 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91689 ⟨696793, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91689
    ⟨696793, by decide⟩ (by decide) (![⟨696737, by decide⟩,⟨696771, by decide⟩,⟨696788, by decide⟩,⟨696792, by decide⟩]) unmarked_context_12_91689_696793 node_context_12_91689_696793
  intro a
  fin_cases a
  · exact context_13_366756_696737
  · exact context_13_366757_696771
  · exact context_13_366758_696788
  · exact context_13_366759_696792

theorem selected_cut_27571 : selected 9 ⟨445248, by decide⟩
    (prefixPartial 12 91690) = some ⟨12, 1, 0, 445248, 91690, 1, 65536⟩ := by
  decide +kernel

theorem context_12_91690_445248 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91690 ⟨445248, by decide⟩ :=
  accepted_of_selected 12 91690 ⟨445248, by decide⟩ ⟨12, 1, 0, 445248, 91690, 1, 65536⟩
    (by decide) selected_cut_27571

theorem selected_cut_27572 : selected 8 ⟨696803, by decide⟩
    (prefixPartial 13 366764) = some ⟨13, 2, 0, 696803, 366764, 729, 16384⟩ := by
  decide +kernel

theorem context_13_366764_696803 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366764 ⟨696803, by decide⟩ :=
  accepted_of_selected 13 366764 ⟨696803, by decide⟩ ⟨13, 2, 0, 696803, 366764, 729, 16384⟩
    (by decide) selected_cut_27572

theorem selected_cut_27573 : selected 8 ⟨696832, by decide⟩
    (prefixPartial 13 366765) = some ⟨13, 2, 0, 696832, 366765, 1729, 16384⟩ := by
  decide +kernel

theorem context_13_366765_696832 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366765 ⟨696832, by decide⟩ :=
  accepted_of_selected 13 366765 ⟨696832, by decide⟩ ⟨13, 2, 0, 696832, 366765, 1729, 16384⟩
    (by decide) selected_cut_27573

theorem selected_cut_27574 : selected 8 ⟨696847, by decide⟩
    (prefixPartial 13 366766) = some ⟨13, 2, 0, 696847, 366766, 1241, 16384⟩ := by
  decide +kernel

theorem context_13_366766_696847 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366766 ⟨696847, by decide⟩ :=
  accepted_of_selected 13 366766 ⟨696847, by decide⟩ ⟨13, 2, 0, 696847, 366766, 1241, 16384⟩
    (by decide) selected_cut_27574

theorem selected_cut_27575 : selected 8 ⟨696852, by decide⟩
    (prefixPartial 13 366767) = some ⟨13, 2, 0, 696852, 366767, 701, 16384⟩ := by
  decide +kernel

theorem context_13_366767_696852 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366767 ⟨696852, by decide⟩ :=
  accepted_of_selected 13 366767 ⟨696852, by decide⟩ ⟨13, 2, 0, 696852, 366767, 701, 16384⟩
    (by decide) selected_cut_27575

theorem unmarked_context_12_91691_696853 : frontier 9 ⟨696853, by decide⟩
    (prefixCache 12 91691) (prefixPartial 12 91691) = false := by
  decide +kernel

theorem node_context_12_91691_696853 : EJMOriginalGlobalDAGData.nodes 9 ⟨696853, by decide⟩ =
    .split (coordinate 12) (![⟨696803, by decide⟩,⟨696832, by decide⟩,⟨696847, by decide⟩,⟨696852, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91691_696853 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91691 ⟨696853, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91691
    ⟨696853, by decide⟩ (by decide) (![⟨696803, by decide⟩,⟨696832, by decide⟩,⟨696847, by decide⟩,⟨696852, by decide⟩]) unmarked_context_12_91691_696853 node_context_12_91691_696853
  intro a
  fin_cases a
  · exact context_13_366764_696803
  · exact context_13_366765_696832
  · exact context_13_366766_696847
  · exact context_13_366767_696852

theorem unmarked_context_11_22922_696854 : frontier 10 ⟨696854, by decide⟩
    (prefixCache 11 22922) (prefixPartial 11 22922) = false := by
  decide +kernel

theorem node_context_11_22922_696854 : EJMOriginalGlobalDAGData.nodes 10 ⟨696854, by decide⟩ =
    .split (coordinate 11) (![⟨696727, by decide⟩,⟨696793, by decide⟩,⟨445248, by decide⟩,⟨696853, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22922_696854 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22922 ⟨696854, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22922
    ⟨696854, by decide⟩ (by decide) (![⟨696727, by decide⟩,⟨696793, by decide⟩,⟨445248, by decide⟩,⟨696853, by decide⟩]) unmarked_context_11_22922_696854 node_context_11_22922_696854
  intro a
  fin_cases a
  · exact context_12_91688_696727
  · exact context_12_91689_696793
  · exact context_12_91690_445248
  · exact context_12_91691_696853

theorem selected_cut_27576 : selected 8 ⟨696862, by decide⟩
    (prefixPartial 13 366768) = some ⟨13, 2, 0, 696862, 366768, 665, 16384⟩ := by
  decide +kernel

theorem context_13_366768_696862 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366768 ⟨696862, by decide⟩ :=
  accepted_of_selected 13 366768 ⟨696862, by decide⟩ ⟨13, 2, 0, 696862, 366768, 665, 16384⟩
    (by decide) selected_cut_27576

theorem selected_cut_27577 : selected 8 ⟨696885, by decide⟩
    (prefixPartial 13 366769) = some ⟨13, 2, 0, 696885, 366769, 1645, 16384⟩ := by
  decide +kernel

theorem context_13_366769_696885 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366769 ⟨696885, by decide⟩ :=
  accepted_of_selected 13 366769 ⟨696885, by decide⟩ ⟨13, 2, 0, 696885, 366769, 1645, 16384⟩
    (by decide) selected_cut_27577

theorem selected_cut_27578 : selected 8 ⟨696902, by decide⟩
    (prefixPartial 13 366770) = some ⟨13, 2, 0, 696902, 366770, 1229, 16384⟩ := by
  decide +kernel

theorem context_13_366770_696902 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366770 ⟨696902, by decide⟩ :=
  accepted_of_selected 13 366770 ⟨696902, by decide⟩ ⟨13, 2, 0, 696902, 366770, 1229, 16384⟩
    (by decide) selected_cut_27578

theorem selected_cut_27579 : selected 8 ⟨696909, by decide⟩
    (prefixPartial 13 366771) = some ⟨13, 2, 0, 696909, 366771, 809, 16384⟩ := by
  decide +kernel

theorem context_13_366771_696909 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366771 ⟨696909, by decide⟩ :=
  accepted_of_selected 13 366771 ⟨696909, by decide⟩ ⟨13, 2, 0, 696909, 366771, 809, 16384⟩
    (by decide) selected_cut_27579

theorem unmarked_context_12_91692_696910 : frontier 9 ⟨696910, by decide⟩
    (prefixCache 12 91692) (prefixPartial 12 91692) = false := by
  decide +kernel

theorem node_context_12_91692_696910 : EJMOriginalGlobalDAGData.nodes 9 ⟨696910, by decide⟩ =
    .split (coordinate 12) (![⟨696862, by decide⟩,⟨696885, by decide⟩,⟨696902, by decide⟩,⟨696909, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91692_696910 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91692 ⟨696910, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91692
    ⟨696910, by decide⟩ (by decide) (![⟨696862, by decide⟩,⟨696885, by decide⟩,⟨696902, by decide⟩,⟨696909, by decide⟩]) unmarked_context_12_91692_696910 node_context_12_91692_696910
  intro a
  fin_cases a
  · exact context_13_366768_696862
  · exact context_13_366769_696885
  · exact context_13_366770_696902
  · exact context_13_366771_696909

theorem selected_cut_27580 : selected 8 ⟨696921, by decide⟩
    (prefixPartial 13 366772) = some ⟨13, 2, 0, 696921, 366772, 833, 16384⟩ := by
  decide +kernel

theorem context_13_366772_696921 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366772 ⟨696921, by decide⟩ :=
  accepted_of_selected 13 366772 ⟨696921, by decide⟩ ⟨13, 2, 0, 696921, 366772, 833, 16384⟩
    (by decide) selected_cut_27580

theorem selected_cut_27581 : selected 8 ⟨696951, by decide⟩
    (prefixPartial 13 366773) = some ⟨13, 2, 0, 696951, 366773, 1905, 16384⟩ := by
  decide +kernel

theorem context_13_366773_696951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366773 ⟨696951, by decide⟩ :=
  accepted_of_selected 13 366773 ⟨696951, by decide⟩ ⟨13, 2, 0, 696951, 366773, 1905, 16384⟩
    (by decide) selected_cut_27581

theorem selected_cut_27582 : selected 8 ⟨696967, by decide⟩
    (prefixPartial 13 366774) = some ⟨13, 2, 0, 696967, 366774, 1277, 16384⟩ := by
  decide +kernel

theorem context_13_366774_696967 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366774 ⟨696967, by decide⟩ :=
  accepted_of_selected 13 366774 ⟨696967, by decide⟩ ⟨13, 2, 0, 696967, 366774, 1277, 16384⟩
    (by decide) selected_cut_27582

theorem selected_cut_27583 : selected 8 ⟨696972, by decide⟩
    (prefixPartial 13 366775) = some ⟨13, 2, 0, 696972, 366775, 813, 16384⟩ := by
  decide +kernel

theorem context_13_366775_696972 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366775 ⟨696972, by decide⟩ :=
  accepted_of_selected 13 366775 ⟨696972, by decide⟩ ⟨13, 2, 0, 696972, 366775, 813, 16384⟩
    (by decide) selected_cut_27583

theorem unmarked_context_12_91693_696973 : frontier 9 ⟨696973, by decide⟩
    (prefixCache 12 91693) (prefixPartial 12 91693) = false := by
  decide +kernel

theorem node_context_12_91693_696973 : EJMOriginalGlobalDAGData.nodes 9 ⟨696973, by decide⟩ =
    .split (coordinate 12) (![⟨696921, by decide⟩,⟨696951, by decide⟩,⟨696967, by decide⟩,⟨696972, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91693_696973 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91693 ⟨696973, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91693
    ⟨696973, by decide⟩ (by decide) (![⟨696921, by decide⟩,⟨696951, by decide⟩,⟨696967, by decide⟩,⟨696972, by decide⟩]) unmarked_context_12_91693_696973 node_context_12_91693_696973
  intro a
  fin_cases a
  · exact context_13_366772_696921
  · exact context_13_366773_696951
  · exact context_13_366774_696967
  · exact context_13_366775_696972

theorem selected_cut_27584 : selected 9 ⟨697023, by decide⟩
    (prefixPartial 12 91694) = some ⟨12, 2, 0, 697023, 91694, 3925, 65536⟩ := by
  decide +kernel

theorem context_12_91694_697023 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91694 ⟨697023, by decide⟩ :=
  accepted_of_selected 12 91694 ⟨697023, by decide⟩ ⟨12, 2, 0, 697023, 91694, 3925, 65536⟩
    (by decide) selected_cut_27584

theorem selected_cut_27585 : selected 8 ⟨697033, by decide⟩
    (prefixPartial 13 366780) = some ⟨13, 2, 0, 697033, 366780, 673, 16384⟩ := by
  decide +kernel

theorem context_13_366780_697033 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366780 ⟨697033, by decide⟩ :=
  accepted_of_selected 13 366780 ⟨697033, by decide⟩ ⟨13, 2, 0, 697033, 366780, 673, 16384⟩
    (by decide) selected_cut_27585

theorem selected_cut_27586 : selected 8 ⟨697060, by decide⟩
    (prefixPartial 13 366781) = some ⟨13, 2, 0, 697060, 366781, 1953, 16384⟩ := by
  decide +kernel

theorem context_13_366781_697060 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366781 ⟨697060, by decide⟩ :=
  accepted_of_selected 13 366781 ⟨697060, by decide⟩ ⟨13, 2, 0, 697060, 366781, 1953, 16384⟩
    (by decide) selected_cut_27586

theorem selected_cut_27587 : selected 8 ⟨697078, by decide⟩
    (prefixPartial 13 366782) = some ⟨13, 2, 0, 697078, 366782, 1409, 16384⟩ := by
  decide +kernel

theorem context_13_366782_697078 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366782 ⟨697078, by decide⟩ :=
  accepted_of_selected 13 366782 ⟨697078, by decide⟩ ⟨13, 2, 0, 697078, 366782, 1409, 16384⟩
    (by decide) selected_cut_27587

theorem selected_cut_27588 : selected 8 ⟨697083, by decide⟩
    (prefixPartial 13 366783) = some ⟨13, 2, 0, 697083, 366783, 745, 16384⟩ := by
  decide +kernel

theorem context_13_366783_697083 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366783 ⟨697083, by decide⟩ :=
  accepted_of_selected 13 366783 ⟨697083, by decide⟩ ⟨13, 2, 0, 697083, 366783, 745, 16384⟩
    (by decide) selected_cut_27588

theorem unmarked_context_12_91695_697084 : frontier 9 ⟨697084, by decide⟩
    (prefixCache 12 91695) (prefixPartial 12 91695) = false := by
  decide +kernel

theorem node_context_12_91695_697084 : EJMOriginalGlobalDAGData.nodes 9 ⟨697084, by decide⟩ =
    .split (coordinate 12) (![⟨697033, by decide⟩,⟨697060, by decide⟩,⟨697078, by decide⟩,⟨697083, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91695_697084 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91695 ⟨697084, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91695
    ⟨697084, by decide⟩ (by decide) (![⟨697033, by decide⟩,⟨697060, by decide⟩,⟨697078, by decide⟩,⟨697083, by decide⟩]) unmarked_context_12_91695_697084 node_context_12_91695_697084
  intro a
  fin_cases a
  · exact context_13_366780_697033
  · exact context_13_366781_697060
  · exact context_13_366782_697078
  · exact context_13_366783_697083

theorem unmarked_context_11_22923_697085 : frontier 10 ⟨697085, by decide⟩
    (prefixCache 11 22923) (prefixPartial 11 22923) = false := by
  decide +kernel

theorem node_context_11_22923_697085 : EJMOriginalGlobalDAGData.nodes 10 ⟨697085, by decide⟩ =
    .split (coordinate 11) (![⟨696910, by decide⟩,⟨696973, by decide⟩,⟨697023, by decide⟩,⟨697084, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22923_697085 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22923 ⟨697085, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22923
    ⟨697085, by decide⟩ (by decide) (![⟨696910, by decide⟩,⟨696973, by decide⟩,⟨697023, by decide⟩,⟨697084, by decide⟩]) unmarked_context_11_22923_697085 node_context_11_22923_697085
  intro a
  fin_cases a
  · exact context_12_91692_696910
  · exact context_12_91693_696973
  · exact context_12_91694_697023
  · exact context_12_91695_697084

theorem unmarked_context_10_5730_697086 : frontier 11 ⟨697086, by decide⟩
    (prefixCache 10 5730) (prefixPartial 10 5730) = false := by
  decide +kernel

theorem node_context_10_5730_697086 : EJMOriginalGlobalDAGData.nodes 11 ⟨697086, by decide⟩ =
    .split (coordinate 10) (![⟨696450, by decide⟩,⟨696674, by decide⟩,⟨696854, by decide⟩,⟨697085, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5730_697086 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5730 ⟨697086, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5730
    ⟨697086, by decide⟩ (by decide) (![⟨696450, by decide⟩,⟨696674, by decide⟩,⟨696854, by decide⟩,⟨697085, by decide⟩]) unmarked_context_10_5730_697086 node_context_10_5730_697086
  intro a
  fin_cases a
  · exact context_11_22920_696450
  · exact context_11_22921_696674
  · exact context_11_22922_696854
  · exact context_11_22923_697085

theorem selected_cut_27589 : selected 8 ⟨697096, by decide⟩
    (prefixPartial 13 366784) = some ⟨13, 2, 0, 697096, 366784, 825, 16384⟩ := by
  decide +kernel

theorem context_13_366784_697096 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366784 ⟨697096, by decide⟩ :=
  accepted_of_selected 13 366784 ⟨697096, by decide⟩ ⟨13, 2, 0, 697096, 366784, 825, 16384⟩
    (by decide) selected_cut_27589

theorem selected_cut_27590 : selected 8 ⟨697123, by decide⟩
    (prefixPartial 13 366785) = some ⟨13, 2, 0, 697123, 366785, 1669, 16384⟩ := by
  decide +kernel

theorem context_13_366785_697123 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366785 ⟨697123, by decide⟩ :=
  accepted_of_selected 13 366785 ⟨697123, by decide⟩ ⟨13, 2, 0, 697123, 366785, 1669, 16384⟩
    (by decide) selected_cut_27590

theorem selected_cut_27591 : selected 8 ⟨697138, by decide⟩
    (prefixPartial 13 366786) = some ⟨13, 2, 0, 697138, 366786, 1189, 16384⟩ := by
  decide +kernel

theorem context_13_366786_697138 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366786 ⟨697138, by decide⟩ :=
  accepted_of_selected 13 366786 ⟨697138, by decide⟩ ⟨13, 2, 0, 697138, 366786, 1189, 16384⟩
    (by decide) selected_cut_27591

theorem selected_cut_27592 : selected 8 ⟨697145, by decide⟩
    (prefixPartial 13 366787) = some ⟨13, 2, 0, 697145, 366787, 713, 16384⟩ := by
  decide +kernel

theorem context_13_366787_697145 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366787 ⟨697145, by decide⟩ :=
  accepted_of_selected 13 366787 ⟨697145, by decide⟩ ⟨13, 2, 0, 697145, 366787, 713, 16384⟩
    (by decide) selected_cut_27592

theorem unmarked_context_12_91696_697146 : frontier 9 ⟨697146, by decide⟩
    (prefixCache 12 91696) (prefixPartial 12 91696) = false := by
  decide +kernel

theorem node_context_12_91696_697146 : EJMOriginalGlobalDAGData.nodes 9 ⟨697146, by decide⟩ =
    .split (coordinate 12) (![⟨697096, by decide⟩,⟨697123, by decide⟩,⟨697138, by decide⟩,⟨697145, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91696_697146 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91696 ⟨697146, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91696
    ⟨697146, by decide⟩ (by decide) (![⟨697096, by decide⟩,⟨697123, by decide⟩,⟨697138, by decide⟩,⟨697145, by decide⟩]) unmarked_context_12_91696_697146 node_context_12_91696_697146
  intro a
  fin_cases a
  · exact context_13_366784_697096
  · exact context_13_366785_697123
  · exact context_13_366786_697138
  · exact context_13_366787_697145

theorem selected_cut_27593 : selected 8 ⟨697161, by decide⟩
    (prefixPartial 13 366788) = some ⟨13, 2, 0, 697161, 366788, 905, 16384⟩ := by
  decide +kernel

theorem context_13_366788_697161 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366788 ⟨697161, by decide⟩ :=
  accepted_of_selected 13 366788 ⟨697161, by decide⟩ ⟨13, 2, 0, 697161, 366788, 905, 16384⟩
    (by decide) selected_cut_27593

theorem selected_cut_27594 : selected 8 ⟨697187, by decide⟩
    (prefixPartial 13 366789) = some ⟨13, 2, 0, 697187, 366789, 1933, 16384⟩ := by
  decide +kernel

theorem context_13_366789_697187 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366789 ⟨697187, by decide⟩ :=
  accepted_of_selected 13 366789 ⟨697187, by decide⟩ ⟨13, 2, 0, 697187, 366789, 1933, 16384⟩
    (by decide) selected_cut_27594

theorem selected_cut_27595 : selected 8 ⟨697203, by decide⟩
    (prefixPartial 13 366790) = some ⟨13, 2, 0, 697203, 366790, 1345, 16384⟩ := by
  decide +kernel

theorem context_13_366790_697203 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366790 ⟨697203, by decide⟩ :=
  accepted_of_selected 13 366790 ⟨697203, by decide⟩ ⟨13, 2, 0, 697203, 366790, 1345, 16384⟩
    (by decide) selected_cut_27595

theorem selected_cut_27596 : selected 8 ⟨697207, by decide⟩
    (prefixPartial 13 366791) = some ⟨13, 2, 0, 697207, 366791, 777, 16384⟩ := by
  decide +kernel

theorem context_13_366791_697207 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366791 ⟨697207, by decide⟩ :=
  accepted_of_selected 13 366791 ⟨697207, by decide⟩ ⟨13, 2, 0, 697207, 366791, 777, 16384⟩
    (by decide) selected_cut_27596

theorem unmarked_context_12_91697_697208 : frontier 9 ⟨697208, by decide⟩
    (prefixCache 12 91697) (prefixPartial 12 91697) = false := by
  decide +kernel

theorem node_context_12_91697_697208 : EJMOriginalGlobalDAGData.nodes 9 ⟨697208, by decide⟩ =
    .split (coordinate 12) (![⟨697161, by decide⟩,⟨697187, by decide⟩,⟨697203, by decide⟩,⟨697207, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91697_697208 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91697 ⟨697208, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91697
    ⟨697208, by decide⟩ (by decide) (![⟨697161, by decide⟩,⟨697187, by decide⟩,⟨697203, by decide⟩,⟨697207, by decide⟩]) unmarked_context_12_91697_697208 node_context_12_91697_697208
  intro a
  fin_cases a
  · exact context_13_366788_697161
  · exact context_13_366789_697187
  · exact context_13_366790_697203
  · exact context_13_366791_697207

theorem selected_cut_27597 : selected 9 ⟨697258, by decide⟩
    (prefixPartial 12 91698) = some ⟨12, 2, 0, 697258, 91698, 3941, 65536⟩ := by
  decide +kernel

theorem context_12_91698_697258 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91698 ⟨697258, by decide⟩ :=
  accepted_of_selected 12 91698 ⟨697258, by decide⟩ ⟨12, 2, 0, 697258, 91698, 3941, 65536⟩
    (by decide) selected_cut_27597

theorem selected_cut_27598 : selected 8 ⟨697275, by decide⟩
    (prefixPartial 13 366796) = some ⟨13, 2, 0, 697275, 366796, 853, 16384⟩ := by
  decide +kernel

theorem context_13_366796_697275 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366796 ⟨697275, by decide⟩ :=
  accepted_of_selected 13 366796 ⟨697275, by decide⟩ ⟨13, 2, 0, 697275, 366796, 853, 16384⟩
    (by decide) selected_cut_27598

theorem selected_cut_27599 : selected 8 ⟨697319, by decide⟩
    (prefixPartial 13 366797) = some ⟨13, 2, 0, 697319, 366797, 2513, 16384⟩ := by
  decide +kernel

theorem context_13_366797_697319 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366797 ⟨697319, by decide⟩ :=
  accepted_of_selected 13 366797 ⟨697319, by decide⟩ ⟨13, 2, 0, 697319, 366797, 2513, 16384⟩
    (by decide) selected_cut_27599

theorem selected_cut_27600 : selected 8 ⟨697339, by decide⟩
    (prefixPartial 13 366798) = some ⟨13, 2, 0, 697339, 366798, 1521, 16384⟩ := by
  decide +kernel

theorem context_13_366798_697339 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366798 ⟨697339, by decide⟩ :=
  accepted_of_selected 13 366798 ⟨697339, by decide⟩ ⟨13, 2, 0, 697339, 366798, 1521, 16384⟩
    (by decide) selected_cut_27600

theorem selected_cut_27601 : selected 8 ⟨697344, by decide⟩
    (prefixPartial 13 366799) = some ⟨13, 2, 0, 697344, 366799, 873, 16384⟩ := by
  decide +kernel

theorem context_13_366799_697344 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366799 ⟨697344, by decide⟩ :=
  accepted_of_selected 13 366799 ⟨697344, by decide⟩ ⟨13, 2, 0, 697344, 366799, 873, 16384⟩
    (by decide) selected_cut_27601

theorem unmarked_context_12_91699_697345 : frontier 9 ⟨697345, by decide⟩
    (prefixCache 12 91699) (prefixPartial 12 91699) = false := by
  decide +kernel

theorem node_context_12_91699_697345 : EJMOriginalGlobalDAGData.nodes 9 ⟨697345, by decide⟩ =
    .split (coordinate 12) (![⟨697275, by decide⟩,⟨697319, by decide⟩,⟨697339, by decide⟩,⟨697344, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91699_697345 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91699 ⟨697345, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91699
    ⟨697345, by decide⟩ (by decide) (![⟨697275, by decide⟩,⟨697319, by decide⟩,⟨697339, by decide⟩,⟨697344, by decide⟩]) unmarked_context_12_91699_697345 node_context_12_91699_697345
  intro a
  fin_cases a
  · exact context_13_366796_697275
  · exact context_13_366797_697319
  · exact context_13_366798_697339
  · exact context_13_366799_697344

theorem unmarked_context_11_22924_697346 : frontier 10 ⟨697346, by decide⟩
    (prefixCache 11 22924) (prefixPartial 11 22924) = false := by
  decide +kernel

theorem node_context_11_22924_697346 : EJMOriginalGlobalDAGData.nodes 10 ⟨697346, by decide⟩ =
    .split (coordinate 11) (![⟨697146, by decide⟩,⟨697208, by decide⟩,⟨697258, by decide⟩,⟨697345, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22924_697346 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22924 ⟨697346, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22924
    ⟨697346, by decide⟩ (by decide) (![⟨697146, by decide⟩,⟨697208, by decide⟩,⟨697258, by decide⟩,⟨697345, by decide⟩]) unmarked_context_11_22924_697346 node_context_11_22924_697346
  intro a
  fin_cases a
  · exact context_12_91696_697146
  · exact context_12_91697_697208
  · exact context_12_91698_697258
  · exact context_12_91699_697345

theorem selected_cut_27602 : selected 8 ⟨697353, by decide⟩
    (prefixPartial 13 366800) = some ⟨13, 2, 0, 697353, 366800, 505, 16384⟩ := by
  decide +kernel

theorem context_13_366800_697353 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366800 ⟨697353, by decide⟩ :=
  accepted_of_selected 13 366800 ⟨697353, by decide⟩ ⟨13, 2, 0, 697353, 366800, 505, 16384⟩
    (by decide) selected_cut_27602

theorem selected_cut_27603 : selected 8 ⟨697389, by decide⟩
    (prefixPartial 13 366801) = some ⟨13, 2, 0, 697389, 366801, 1817, 16384⟩ := by
  decide +kernel

theorem context_13_366801_697389 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366801 ⟨697389, by decide⟩ :=
  accepted_of_selected 13 366801 ⟨697389, by decide⟩ ⟨13, 2, 0, 697389, 366801, 1817, 16384⟩
    (by decide) selected_cut_27603

theorem selected_cut_27604 : selected 8 ⟨697402, by decide⟩
    (prefixPartial 13 366802) = some ⟨13, 2, 0, 697402, 366802, 1045, 16384⟩ := by
  decide +kernel

theorem context_13_366802_697402 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366802 ⟨697402, by decide⟩ :=
  accepted_of_selected 13 366802 ⟨697402, by decide⟩ ⟨13, 2, 0, 697402, 366802, 1045, 16384⟩
    (by decide) selected_cut_27604

theorem selected_cut_27605 : selected 8 ⟨697407, by decide⟩
    (prefixPartial 13 366803) = some ⟨13, 2, 0, 697407, 366803, 745, 16384⟩ := by
  decide +kernel

theorem context_13_366803_697407 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366803 ⟨697407, by decide⟩ :=
  accepted_of_selected 13 366803 ⟨697407, by decide⟩ ⟨13, 2, 0, 697407, 366803, 745, 16384⟩
    (by decide) selected_cut_27605

theorem unmarked_context_12_91700_697408 : frontier 9 ⟨697408, by decide⟩
    (prefixCache 12 91700) (prefixPartial 12 91700) = false := by
  decide +kernel

theorem node_context_12_91700_697408 : EJMOriginalGlobalDAGData.nodes 9 ⟨697408, by decide⟩ =
    .split (coordinate 12) (![⟨697353, by decide⟩,⟨697389, by decide⟩,⟨697402, by decide⟩,⟨697407, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91700_697408 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91700 ⟨697408, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91700
    ⟨697408, by decide⟩ (by decide) (![⟨697353, by decide⟩,⟨697389, by decide⟩,⟨697402, by decide⟩,⟨697407, by decide⟩]) unmarked_context_12_91700_697408 node_context_12_91700_697408
  intro a
  fin_cases a
  · exact context_13_366800_697353
  · exact context_13_366801_697389
  · exact context_13_366802_697402
  · exact context_13_366803_697407

theorem selected_cut_27606 : selected 8 ⟨697418, by decide⟩
    (prefixPartial 13 366804) = some ⟨13, 2, 0, 697418, 366804, 569, 16384⟩ := by
  decide +kernel

theorem context_13_366804_697418 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366804 ⟨697418, by decide⟩ :=
  accepted_of_selected 13 366804 ⟨697418, by decide⟩ ⟨13, 2, 0, 697418, 366804, 569, 16384⟩
    (by decide) selected_cut_27606

theorem selected_cut_27607 : selected 8 ⟨697441, by decide⟩
    (prefixPartial 13 366805) = some ⟨13, 2, 0, 697441, 366805, 1717, 16384⟩ := by
  decide +kernel

theorem context_13_366805_697441 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366805 ⟨697441, by decide⟩ :=
  accepted_of_selected 13 366805 ⟨697441, by decide⟩ ⟨13, 2, 0, 697441, 366805, 1717, 16384⟩
    (by decide) selected_cut_27607

theorem selected_cut_27608 : selected 8 ⟨697454, by decide⟩
    (prefixPartial 13 366806) = some ⟨13, 2, 0, 697454, 366806, 1105, 16384⟩ := by
  decide +kernel

theorem context_13_366806_697454 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366806 ⟨697454, by decide⟩ :=
  accepted_of_selected 13 366806 ⟨697454, by decide⟩ ⟨13, 2, 0, 697454, 366806, 1105, 16384⟩
    (by decide) selected_cut_27608

theorem selected_cut_27609 : selected 8 ⟨697458, by decide⟩
    (prefixPartial 13 366807) = some ⟨13, 2, 0, 697458, 366807, 745, 16384⟩ := by
  decide +kernel

theorem context_13_366807_697458 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366807 ⟨697458, by decide⟩ :=
  accepted_of_selected 13 366807 ⟨697458, by decide⟩ ⟨13, 2, 0, 697458, 366807, 745, 16384⟩
    (by decide) selected_cut_27609

theorem unmarked_context_12_91701_697459 : frontier 9 ⟨697459, by decide⟩
    (prefixCache 12 91701) (prefixPartial 12 91701) = false := by
  decide +kernel

theorem node_context_12_91701_697459 : EJMOriginalGlobalDAGData.nodes 9 ⟨697459, by decide⟩ =
    .split (coordinate 12) (![⟨697418, by decide⟩,⟨697441, by decide⟩,⟨697454, by decide⟩,⟨697458, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91701_697459 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91701 ⟨697459, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91701
    ⟨697459, by decide⟩ (by decide) (![⟨697418, by decide⟩,⟨697441, by decide⟩,⟨697454, by decide⟩,⟨697458, by decide⟩]) unmarked_context_12_91701_697459 node_context_12_91701_697459
  intro a
  fin_cases a
  · exact context_13_366804_697418
  · exact context_13_366805_697441
  · exact context_13_366806_697454
  · exact context_13_366807_697458

theorem selected_cut_27610 : selected 9 ⟨697503, by decide⟩
    (prefixPartial 12 91702) = some ⟨12, 2, 0, 697503, 91702, 3621, 65536⟩ := by
  decide +kernel

theorem context_12_91702_697503 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91702 ⟨697503, by decide⟩ :=
  accepted_of_selected 12 91702 ⟨697503, by decide⟩ ⟨12, 2, 0, 697503, 91702, 3621, 65536⟩
    (by decide) selected_cut_27610

theorem selected_cut_27611 : selected 8 ⟨697515, by decide⟩
    (prefixPartial 13 366812) = some ⟨13, 2, 0, 697515, 366812, 549, 16384⟩ := by
  decide +kernel

theorem context_13_366812_697515 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366812 ⟨697515, by decide⟩ :=
  accepted_of_selected 13 366812 ⟨697515, by decide⟩ ⟨13, 2, 0, 697515, 366812, 549, 16384⟩
    (by decide) selected_cut_27611

theorem selected_cut_27612 : selected 8 ⟨697557, by decide⟩
    (prefixPartial 13 366813) = some ⟨13, 2, 0, 697557, 366813, 2237, 16384⟩ := by
  decide +kernel

theorem context_13_366813_697557 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366813 ⟨697557, by decide⟩ :=
  accepted_of_selected 13 366813 ⟨697557, by decide⟩ ⟨13, 2, 0, 697557, 366813, 2237, 16384⟩
    (by decide) selected_cut_27612

theorem selected_cut_27613 : selected 8 ⟨697577, by decide⟩
    (prefixPartial 13 366814) = some ⟨13, 2, 0, 697577, 366814, 1409, 16384⟩ := by
  decide +kernel

theorem context_13_366814_697577 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366814 ⟨697577, by decide⟩ :=
  accepted_of_selected 13 366814 ⟨697577, by decide⟩ ⟨13, 2, 0, 697577, 366814, 1409, 16384⟩
    (by decide) selected_cut_27613

theorem selected_cut_27614 : selected 8 ⟨697584, by decide⟩
    (prefixPartial 13 366815) = some ⟨13, 2, 0, 697584, 366815, 793, 16384⟩ := by
  decide +kernel

theorem context_13_366815_697584 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366815 ⟨697584, by decide⟩ :=
  accepted_of_selected 13 366815 ⟨697584, by decide⟩ ⟨13, 2, 0, 697584, 366815, 793, 16384⟩
    (by decide) selected_cut_27614

theorem unmarked_context_12_91703_697585 : frontier 9 ⟨697585, by decide⟩
    (prefixCache 12 91703) (prefixPartial 12 91703) = false := by
  decide +kernel

theorem node_context_12_91703_697585 : EJMOriginalGlobalDAGData.nodes 9 ⟨697585, by decide⟩ =
    .split (coordinate 12) (![⟨697515, by decide⟩,⟨697557, by decide⟩,⟨697577, by decide⟩,⟨697584, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91703_697585 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91703 ⟨697585, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91703
    ⟨697585, by decide⟩ (by decide) (![⟨697515, by decide⟩,⟨697557, by decide⟩,⟨697577, by decide⟩,⟨697584, by decide⟩]) unmarked_context_12_91703_697585 node_context_12_91703_697585
  intro a
  fin_cases a
  · exact context_13_366812_697515
  · exact context_13_366813_697557
  · exact context_13_366814_697577
  · exact context_13_366815_697584

theorem unmarked_context_11_22925_697586 : frontier 10 ⟨697586, by decide⟩
    (prefixCache 11 22925) (prefixPartial 11 22925) = false := by
  decide +kernel

theorem node_context_11_22925_697586 : EJMOriginalGlobalDAGData.nodes 10 ⟨697586, by decide⟩ =
    .split (coordinate 11) (![⟨697408, by decide⟩,⟨697459, by decide⟩,⟨697503, by decide⟩,⟨697585, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22925_697586 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22925 ⟨697586, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22925
    ⟨697586, by decide⟩ (by decide) (![⟨697408, by decide⟩,⟨697459, by decide⟩,⟨697503, by decide⟩,⟨697585, by decide⟩]) unmarked_context_11_22925_697586 node_context_11_22925_697586
  intro a
  fin_cases a
  · exact context_12_91700_697408
  · exact context_12_91701_697459
  · exact context_12_91702_697503
  · exact context_12_91703_697585

theorem selected_cut_27615 : selected 8 ⟨697593, by decide⟩
    (prefixPartial 13 366816) = some ⟨13, 2, 0, 697593, 366816, 345, 16384⟩ := by
  decide +kernel

theorem context_13_366816_697593 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366816 ⟨697593, by decide⟩ :=
  accepted_of_selected 13 366816 ⟨697593, by decide⟩ ⟨13, 2, 0, 697593, 366816, 345, 16384⟩
    (by decide) selected_cut_27615

theorem selected_cut_27616 : selected 8 ⟨697633, by decide⟩
    (prefixPartial 13 366817) = some ⟨13, 2, 0, 697633, 366817, 1965, 16384⟩ := by
  decide +kernel

theorem context_13_366817_697633 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366817 ⟨697633, by decide⟩ :=
  accepted_of_selected 13 366817 ⟨697633, by decide⟩ ⟨13, 2, 0, 697633, 366817, 1965, 16384⟩
    (by decide) selected_cut_27616

theorem selected_cut_27617 : selected 8 ⟨697648, by decide⟩
    (prefixPartial 13 366818) = some ⟨13, 2, 0, 697648, 366818, 1133, 16384⟩ := by
  decide +kernel

theorem context_13_366818_697648 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366818 ⟨697648, by decide⟩ :=
  accepted_of_selected 13 366818 ⟨697648, by decide⟩ ⟨13, 2, 0, 697648, 366818, 1133, 16384⟩
    (by decide) selected_cut_27617

theorem selected_cut_27618 : selected 8 ⟨697654, by decide⟩
    (prefixPartial 13 366819) = some ⟨13, 2, 0, 697654, 366819, 753, 16384⟩ := by
  decide +kernel

theorem context_13_366819_697654 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366819 ⟨697654, by decide⟩ :=
  accepted_of_selected 13 366819 ⟨697654, by decide⟩ ⟨13, 2, 0, 697654, 366819, 753, 16384⟩
    (by decide) selected_cut_27618

theorem unmarked_context_12_91704_697655 : frontier 9 ⟨697655, by decide⟩
    (prefixCache 12 91704) (prefixPartial 12 91704) = false := by
  decide +kernel

theorem node_context_12_91704_697655 : EJMOriginalGlobalDAGData.nodes 9 ⟨697655, by decide⟩ =
    .split (coordinate 12) (![⟨697593, by decide⟩,⟨697633, by decide⟩,⟨697648, by decide⟩,⟨697654, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91704_697655 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91704 ⟨697655, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91704
    ⟨697655, by decide⟩ (by decide) (![⟨697593, by decide⟩,⟨697633, by decide⟩,⟨697648, by decide⟩,⟨697654, by decide⟩]) unmarked_context_12_91704_697655 node_context_12_91704_697655
  intro a
  fin_cases a
  · exact context_13_366816_697593
  · exact context_13_366817_697633
  · exact context_13_366818_697648
  · exact context_13_366819_697654

theorem selected_cut_27619 : selected 8 ⟨697666, by decide⟩
    (prefixPartial 13 366820) = some ⟨13, 2, 0, 697666, 366820, 473, 16384⟩ := by
  decide +kernel

theorem context_13_366820_697666 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366820 ⟨697666, by decide⟩ :=
  accepted_of_selected 13 366820 ⟨697666, by decide⟩ ⟨13, 2, 0, 697666, 366820, 473, 16384⟩
    (by decide) selected_cut_27619

theorem selected_cut_27620 : selected 8 ⟨697700, by decide⟩
    (prefixPartial 13 366821) = some ⟨13, 2, 0, 697700, 366821, 2045, 16384⟩ := by
  decide +kernel

theorem context_13_366821_697700 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366821 ⟨697700, by decide⟩ :=
  accepted_of_selected 13 366821 ⟨697700, by decide⟩ ⟨13, 2, 0, 697700, 366821, 2045, 16384⟩
    (by decide) selected_cut_27620

theorem selected_cut_27621 : selected 8 ⟨697716, by decide⟩
    (prefixPartial 13 366822) = some ⟨13, 2, 0, 697716, 366822, 1293, 16384⟩ := by
  decide +kernel

theorem context_13_366822_697716 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366822 ⟨697716, by decide⟩ :=
  accepted_of_selected 13 366822 ⟨697716, by decide⟩ ⟨13, 2, 0, 697716, 366822, 1293, 16384⟩
    (by decide) selected_cut_27621

theorem selected_cut_27622 : selected 8 ⟨697721, by decide⟩
    (prefixPartial 13 366823) = some ⟨13, 2, 0, 697721, 366823, 825, 16384⟩ := by
  decide +kernel

theorem context_13_366823_697721 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366823 ⟨697721, by decide⟩ :=
  accepted_of_selected 13 366823 ⟨697721, by decide⟩ ⟨13, 2, 0, 697721, 366823, 825, 16384⟩
    (by decide) selected_cut_27622

theorem unmarked_context_12_91705_697722 : frontier 9 ⟨697722, by decide⟩
    (prefixCache 12 91705) (prefixPartial 12 91705) = false := by
  decide +kernel

theorem node_context_12_91705_697722 : EJMOriginalGlobalDAGData.nodes 9 ⟨697722, by decide⟩ =
    .split (coordinate 12) (![⟨697666, by decide⟩,⟨697700, by decide⟩,⟨697716, by decide⟩,⟨697721, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91705_697722 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91705 ⟨697722, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91705
    ⟨697722, by decide⟩ (by decide) (![⟨697666, by decide⟩,⟨697700, by decide⟩,⟨697716, by decide⟩,⟨697721, by decide⟩]) unmarked_context_12_91705_697722 node_context_12_91705_697722
  intro a
  fin_cases a
  · exact context_13_366820_697666
  · exact context_13_366821_697700
  · exact context_13_366822_697716
  · exact context_13_366823_697721

theorem selected_cut_27623 : selected 8 ⟨697733, by decide⟩
    (prefixPartial 13 366824) = some ⟨13, 2, 0, 697733, 366824, 485, 16384⟩ := by
  decide +kernel

theorem context_13_366824_697733 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366824 ⟨697733, by decide⟩ :=
  accepted_of_selected 13 366824 ⟨697733, by decide⟩ ⟨13, 2, 0, 697733, 366824, 485, 16384⟩
    (by decide) selected_cut_27623

theorem selected_cut_27624 : selected 8 ⟨697778, by decide⟩
    (prefixPartial 13 366825) = some ⟨13, 2, 0, 697778, 366825, 2977, 16384⟩ := by
  decide +kernel

theorem context_13_366825_697778 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366825 ⟨697778, by decide⟩ :=
  accepted_of_selected 13 366825 ⟨697778, by decide⟩ ⟨13, 2, 0, 697778, 366825, 2977, 16384⟩
    (by decide) selected_cut_27624

theorem selected_cut_27625 : selected 8 ⟨697795, by decide⟩
    (prefixPartial 13 366826) = some ⟨13, 2, 0, 697795, 366826, 1885, 16384⟩ := by
  decide +kernel

theorem context_13_366826_697795 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366826 ⟨697795, by decide⟩ :=
  accepted_of_selected 13 366826 ⟨697795, by decide⟩ ⟨13, 2, 0, 697795, 366826, 1885, 16384⟩
    (by decide) selected_cut_27625

theorem selected_cut_27626 : selected 8 ⟨697805, by decide⟩
    (prefixPartial 13 366827) = some ⟨13, 2, 0, 697805, 366827, 1197, 16384⟩ := by
  decide +kernel

theorem context_13_366827_697805 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366827 ⟨697805, by decide⟩ :=
  accepted_of_selected 13 366827 ⟨697805, by decide⟩ ⟨13, 2, 0, 697805, 366827, 1197, 16384⟩
    (by decide) selected_cut_27626

theorem unmarked_context_12_91706_697806 : frontier 9 ⟨697806, by decide⟩
    (prefixCache 12 91706) (prefixPartial 12 91706) = false := by
  decide +kernel

theorem node_context_12_91706_697806 : EJMOriginalGlobalDAGData.nodes 9 ⟨697806, by decide⟩ =
    .split (coordinate 12) (![⟨697733, by decide⟩,⟨697778, by decide⟩,⟨697795, by decide⟩,⟨697805, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91706_697806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91706 ⟨697806, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91706
    ⟨697806, by decide⟩ (by decide) (![⟨697733, by decide⟩,⟨697778, by decide⟩,⟨697795, by decide⟩,⟨697805, by decide⟩]) unmarked_context_12_91706_697806 node_context_12_91706_697806
  intro a
  fin_cases a
  · exact context_13_366824_697733
  · exact context_13_366825_697778
  · exact context_13_366826_697795
  · exact context_13_366827_697805

theorem selected_cut_27627 : selected 8 ⟨697813, by decide⟩
    (prefixPartial 13 366828) = some ⟨13, 2, 0, 697813, 366828, 277, 16384⟩ := by
  decide +kernel

theorem context_13_366828_697813 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366828 ⟨697813, by decide⟩ :=
  accepted_of_selected 13 366828 ⟨697813, by decide⟩ ⟨13, 2, 0, 697813, 366828, 277, 16384⟩
    (by decide) selected_cut_27627

theorem selected_cut_27628 : selected 8 ⟨697862, by decide⟩
    (prefixPartial 13 366829) = some ⟨13, 2, 0, 697862, 366829, 2597, 16384⟩ := by
  decide +kernel

theorem context_13_366829_697862 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366829 ⟨697862, by decide⟩ :=
  accepted_of_selected 13 366829 ⟨697862, by decide⟩ ⟨13, 2, 0, 697862, 366829, 2597, 16384⟩
    (by decide) selected_cut_27628

theorem selected_cut_27629 : selected 8 ⟨697880, by decide⟩
    (prefixPartial 13 366830) = some ⟨13, 2, 0, 697880, 366830, 1409, 16384⟩ := by
  decide +kernel

theorem context_13_366830_697880 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366830 ⟨697880, by decide⟩ :=
  accepted_of_selected 13 366830 ⟨697880, by decide⟩ ⟨13, 2, 0, 697880, 366830, 1409, 16384⟩
    (by decide) selected_cut_27629

theorem selected_cut_27630 : selected 8 ⟨697887, by decide⟩
    (prefixPartial 13 366831) = some ⟨13, 2, 0, 697887, 366831, 781, 16384⟩ := by
  decide +kernel

theorem context_13_366831_697887 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366831 ⟨697887, by decide⟩ :=
  accepted_of_selected 13 366831 ⟨697887, by decide⟩ ⟨13, 2, 0, 697887, 366831, 781, 16384⟩
    (by decide) selected_cut_27630

theorem unmarked_context_12_91707_697888 : frontier 9 ⟨697888, by decide⟩
    (prefixCache 12 91707) (prefixPartial 12 91707) = false := by
  decide +kernel

theorem node_context_12_91707_697888 : EJMOriginalGlobalDAGData.nodes 9 ⟨697888, by decide⟩ =
    .split (coordinate 12) (![⟨697813, by decide⟩,⟨697862, by decide⟩,⟨697880, by decide⟩,⟨697887, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91707_697888 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91707 ⟨697888, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91707
    ⟨697888, by decide⟩ (by decide) (![⟨697813, by decide⟩,⟨697862, by decide⟩,⟨697880, by decide⟩,⟨697887, by decide⟩]) unmarked_context_12_91707_697888 node_context_12_91707_697888
  intro a
  fin_cases a
  · exact context_13_366828_697813
  · exact context_13_366829_697862
  · exact context_13_366830_697880
  · exact context_13_366831_697887

theorem unmarked_context_11_22926_697889 : frontier 10 ⟨697889, by decide⟩
    (prefixCache 11 22926) (prefixPartial 11 22926) = false := by
  decide +kernel

theorem node_context_11_22926_697889 : EJMOriginalGlobalDAGData.nodes 10 ⟨697889, by decide⟩ =
    .split (coordinate 11) (![⟨697655, by decide⟩,⟨697722, by decide⟩,⟨697806, by decide⟩,⟨697888, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22926_697889 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22926 ⟨697889, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22926
    ⟨697889, by decide⟩ (by decide) (![⟨697655, by decide⟩,⟨697722, by decide⟩,⟨697806, by decide⟩,⟨697888, by decide⟩]) unmarked_context_11_22926_697889 node_context_11_22926_697889
  intro a
  fin_cases a
  · exact context_12_91704_697655
  · exact context_12_91705_697722
  · exact context_12_91706_697806
  · exact context_12_91707_697888

theorem selected_cut_27631 : selected 9 ⟨697944, by decide⟩
    (prefixPartial 12 91708) = some ⟨12, 2, 0, 697944, 91708, 3749, 65536⟩ := by
  decide +kernel

theorem context_12_91708_697944 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91708 ⟨697944, by decide⟩ :=
  accepted_of_selected 12 91708 ⟨697944, by decide⟩ ⟨12, 2, 0, 697944, 91708, 3749, 65536⟩
    (by decide) selected_cut_27631

theorem selected_cut_27632 : selected 9 ⟨698000, by decide⟩
    (prefixPartial 12 91709) = some ⟨12, 2, 0, 698000, 91709, 4053, 65536⟩ := by
  decide +kernel

theorem context_12_91709_698000 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91709 ⟨698000, by decide⟩ :=
  accepted_of_selected 12 91709 ⟨698000, by decide⟩ ⟨12, 2, 0, 698000, 91709, 4053, 65536⟩
    (by decide) selected_cut_27632

theorem selected_cut_27633 : selected 9 ⟨698041, by decide⟩
    (prefixPartial 12 91710) = some ⟨12, 2, 0, 698041, 91710, 3369, 65536⟩ := by
  decide +kernel

theorem context_12_91710_698041 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91710 ⟨698041, by decide⟩ :=
  accepted_of_selected 12 91710 ⟨698041, by decide⟩ ⟨12, 2, 0, 698041, 91710, 3369, 65536⟩
    (by decide) selected_cut_27633

theorem selected_cut_27634 : selected 8 ⟨698044, by decide⟩
    (prefixPartial 13 366844) = some ⟨13, 2, 0, 698044, 366844, 77, 16384⟩ := by
  decide +kernel

theorem context_13_366844_698044 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366844 ⟨698044, by decide⟩ :=
  accepted_of_selected 13 366844 ⟨698044, by decide⟩ ⟨13, 2, 0, 698044, 366844, 77, 16384⟩
    (by decide) selected_cut_27634

theorem selected_cut_27635 : selected 8 ⟨698091, by decide⟩
    (prefixPartial 13 366845) = some ⟨13, 2, 0, 698091, 366845, 2441, 16384⟩ := by
  decide +kernel

theorem context_13_366845_698091 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366845 ⟨698091, by decide⟩ :=
  accepted_of_selected 13 366845 ⟨698091, by decide⟩ ⟨13, 2, 0, 698091, 366845, 2441, 16384⟩
    (by decide) selected_cut_27635

theorem selected_cut_27636 : selected 8 ⟨698109, by decide⟩
    (prefixPartial 13 366846) = some ⟨13, 2, 0, 698109, 366846, 1453, 16384⟩ := by
  decide +kernel

theorem context_13_366846_698109 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366846 ⟨698109, by decide⟩ :=
  accepted_of_selected 13 366846 ⟨698109, by decide⟩ ⟨13, 2, 0, 698109, 366846, 1453, 16384⟩
    (by decide) selected_cut_27636

theorem selected_cut_27637 : selected 8 ⟨698114, by decide⟩
    (prefixPartial 13 366847) = some ⟨13, 2, 0, 698114, 366847, 793, 16384⟩ := by
  decide +kernel

theorem context_13_366847_698114 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366847 ⟨698114, by decide⟩ :=
  accepted_of_selected 13 366847 ⟨698114, by decide⟩ ⟨13, 2, 0, 698114, 366847, 793, 16384⟩
    (by decide) selected_cut_27637

theorem unmarked_context_12_91711_698115 : frontier 9 ⟨698115, by decide⟩
    (prefixCache 12 91711) (prefixPartial 12 91711) = false := by
  decide +kernel

theorem node_context_12_91711_698115 : EJMOriginalGlobalDAGData.nodes 9 ⟨698115, by decide⟩ =
    .split (coordinate 12) (![⟨698044, by decide⟩,⟨698091, by decide⟩,⟨698109, by decide⟩,⟨698114, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91711_698115 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91711 ⟨698115, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91711
    ⟨698115, by decide⟩ (by decide) (![⟨698044, by decide⟩,⟨698091, by decide⟩,⟨698109, by decide⟩,⟨698114, by decide⟩]) unmarked_context_12_91711_698115 node_context_12_91711_698115
  intro a
  fin_cases a
  · exact context_13_366844_698044
  · exact context_13_366845_698091
  · exact context_13_366846_698109
  · exact context_13_366847_698114

theorem unmarked_context_11_22927_698116 : frontier 10 ⟨698116, by decide⟩
    (prefixCache 11 22927) (prefixPartial 11 22927) = false := by
  decide +kernel

theorem node_context_11_22927_698116 : EJMOriginalGlobalDAGData.nodes 10 ⟨698116, by decide⟩ =
    .split (coordinate 11) (![⟨697944, by decide⟩,⟨698000, by decide⟩,⟨698041, by decide⟩,⟨698115, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22927_698116 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22927 ⟨698116, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22927
    ⟨698116, by decide⟩ (by decide) (![⟨697944, by decide⟩,⟨698000, by decide⟩,⟨698041, by decide⟩,⟨698115, by decide⟩]) unmarked_context_11_22927_698116 node_context_11_22927_698116
  intro a
  fin_cases a
  · exact context_12_91708_697944
  · exact context_12_91709_698000
  · exact context_12_91710_698041
  · exact context_12_91711_698115

theorem unmarked_context_10_5731_698117 : frontier 11 ⟨698117, by decide⟩
    (prefixCache 10 5731) (prefixPartial 10 5731) = false := by
  decide +kernel

theorem node_context_10_5731_698117 : EJMOriginalGlobalDAGData.nodes 11 ⟨698117, by decide⟩ =
    .split (coordinate 10) (![⟨697346, by decide⟩,⟨697586, by decide⟩,⟨697889, by decide⟩,⟨698116, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5731_698117 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5731 ⟨698117, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5731
    ⟨698117, by decide⟩ (by decide) (![⟨697346, by decide⟩,⟨697586, by decide⟩,⟨697889, by decide⟩,⟨698116, by decide⟩]) unmarked_context_10_5731_698117 node_context_10_5731_698117
  intro a
  fin_cases a
  · exact context_11_22924_697346
  · exact context_11_22925_697586
  · exact context_11_22926_697889
  · exact context_11_22927_698116

theorem unmarked_context_9_1432_698118 : frontier 12 ⟨698118, by decide⟩
    (prefixCache 9 1432) (prefixPartial 9 1432) = false := by
  decide +kernel

theorem node_context_9_1432_698118 : EJMOriginalGlobalDAGData.nodes 12 ⟨698118, by decide⟩ =
    .split (coordinate 9) (![⟨695037, by decide⟩,⟨696209, by decide⟩,⟨697086, by decide⟩,⟨698117, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1432_698118 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1432 ⟨698118, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1432
    ⟨698118, by decide⟩ (by decide) (![⟨695037, by decide⟩,⟨696209, by decide⟩,⟨697086, by decide⟩,⟨698117, by decide⟩]) unmarked_context_9_1432_698118 node_context_9_1432_698118
  intro a
  fin_cases a
  · exact context_10_5728_695037
  · exact context_10_5729_696209
  · exact context_10_5730_697086
  · exact context_10_5731_698117

theorem selected_cut_27638 : selected 9 ⟨698175, by decide⟩
    (prefixPartial 12 91712) = some ⟨12, 2, 0, 698175, 91712, 3781, 65536⟩ := by
  decide +kernel

theorem context_12_91712_698175 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91712 ⟨698175, by decide⟩ :=
  accepted_of_selected 12 91712 ⟨698175, by decide⟩ ⟨12, 2, 0, 698175, 91712, 3781, 65536⟩
    (by decide) selected_cut_27638

theorem selected_cut_27639 : selected 9 ⟨170504, by decide⟩
    (prefixPartial 12 91713) = some ⟨12, 1, 0, 170504, 91713, 1, 65536⟩ := by
  decide +kernel

theorem context_12_91713_170504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91713 ⟨170504, by decide⟩ :=
  accepted_of_selected 12 91713 ⟨170504, by decide⟩ ⟨12, 1, 0, 170504, 91713, 1, 65536⟩
    (by decide) selected_cut_27639

theorem selected_cut_27640 : selected 9 ⟨698228, by decide⟩
    (prefixPartial 12 91714) = some ⟨12, 2, 0, 698228, 91714, 3745, 65536⟩ := by
  decide +kernel

theorem context_12_91714_698228 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91714 ⟨698228, by decide⟩ :=
  accepted_of_selected 12 91714 ⟨698228, by decide⟩ ⟨12, 2, 0, 698228, 91714, 3745, 65536⟩
    (by decide) selected_cut_27640

theorem selected_cut_27641 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 366860) = some ⟨13, 1, 0, 3444, 366860, 1, 16384⟩ := by
  decide +kernel

theorem context_13_366860_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366860 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 366860 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 366860, 1, 16384⟩
    (by decide) selected_cut_27641

theorem selected_cut_27642 : selected 8 ⟨698270, by decide⟩
    (prefixPartial 13 366861) = some ⟨13, 2, 0, 698270, 366861, 2657, 16384⟩ := by
  decide +kernel

theorem context_13_366861_698270 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366861 ⟨698270, by decide⟩ :=
  accepted_of_selected 13 366861 ⟨698270, by decide⟩ ⟨13, 2, 0, 698270, 366861, 2657, 16384⟩
    (by decide) selected_cut_27642

theorem selected_cut_27643 : selected 8 ⟨698288, by decide⟩
    (prefixPartial 13 366862) = some ⟨13, 2, 0, 698288, 366862, 1265, 16384⟩ := by
  decide +kernel

theorem context_13_366862_698288 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366862 ⟨698288, by decide⟩ :=
  accepted_of_selected 13 366862 ⟨698288, by decide⟩ ⟨13, 2, 0, 698288, 366862, 1265, 16384⟩
    (by decide) selected_cut_27643

theorem selected_cut_27644 : selected 8 ⟨698292, by decide⟩
    (prefixPartial 13 366863) = some ⟨13, 2, 0, 698292, 366863, 577, 16384⟩ := by
  decide +kernel

theorem context_13_366863_698292 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366863 ⟨698292, by decide⟩ :=
  accepted_of_selected 13 366863 ⟨698292, by decide⟩ ⟨13, 2, 0, 698292, 366863, 577, 16384⟩
    (by decide) selected_cut_27644

theorem unmarked_context_12_91715_698293 : frontier 9 ⟨698293, by decide⟩
    (prefixCache 12 91715) (prefixPartial 12 91715) = false := by
  decide +kernel

theorem node_context_12_91715_698293 : EJMOriginalGlobalDAGData.nodes 9 ⟨698293, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨698270, by decide⟩,⟨698288, by decide⟩,⟨698292, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91715_698293 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91715 ⟨698293, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91715
    ⟨698293, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨698270, by decide⟩,⟨698288, by decide⟩,⟨698292, by decide⟩]) unmarked_context_12_91715_698293 node_context_12_91715_698293
  intro a
  fin_cases a
  · exact context_13_366860_3444
  · exact context_13_366861_698270
  · exact context_13_366862_698288
  · exact context_13_366863_698292

theorem unmarked_context_11_22928_698294 : frontier 10 ⟨698294, by decide⟩
    (prefixCache 11 22928) (prefixPartial 11 22928) = false := by
  decide +kernel

theorem node_context_11_22928_698294 : EJMOriginalGlobalDAGData.nodes 10 ⟨698294, by decide⟩ =
    .split (coordinate 11) (![⟨698175, by decide⟩,⟨170504, by decide⟩,⟨698228, by decide⟩,⟨698293, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22928_698294 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22928 ⟨698294, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22928
    ⟨698294, by decide⟩ (by decide) (![⟨698175, by decide⟩,⟨170504, by decide⟩,⟨698228, by decide⟩,⟨698293, by decide⟩]) unmarked_context_11_22928_698294 node_context_11_22928_698294
  intro a
  fin_cases a
  · exact context_12_91712_698175
  · exact context_12_91713_170504
  · exact context_12_91714_698228
  · exact context_12_91715_698293

theorem selected_cut_27645 : selected 9 ⟨698345, by decide⟩
    (prefixPartial 12 91716) = some ⟨12, 2, 0, 698345, 91716, 3413, 65536⟩ := by
  decide +kernel

theorem context_12_91716_698345 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91716 ⟨698345, by decide⟩ :=
  accepted_of_selected 12 91716 ⟨698345, by decide⟩ ⟨12, 2, 0, 698345, 91716, 3413, 65536⟩
    (by decide) selected_cut_27645

theorem selected_cut_27646 : selected 9 ⟨170504, by decide⟩
    (prefixPartial 12 91717) = some ⟨12, 1, 0, 170504, 91717, 1, 65536⟩ := by
  decide +kernel

theorem context_12_91717_170504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91717 ⟨170504, by decide⟩ :=
  accepted_of_selected 12 91717 ⟨170504, by decide⟩ ⟨12, 1, 0, 170504, 91717, 1, 65536⟩
    (by decide) selected_cut_27646

theorem selected_cut_27647 : selected 9 ⟨698393, by decide⟩
    (prefixPartial 12 91718) = some ⟨12, 2, 0, 698393, 91718, 3401, 65536⟩ := by
  decide +kernel

theorem context_12_91718_698393 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91718 ⟨698393, by decide⟩ :=
  accepted_of_selected 12 91718 ⟨698393, by decide⟩ ⟨12, 2, 0, 698393, 91718, 3401, 65536⟩
    (by decide) selected_cut_27647

theorem selected_cut_27648 : selected 9 ⟨698451, by decide⟩
    (prefixPartial 12 91719) = some ⟨12, 2, 0, 698451, 91719, 3761, 65536⟩ := by
  decide +kernel

theorem context_12_91719_698451 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91719 ⟨698451, by decide⟩ :=
  accepted_of_selected 12 91719 ⟨698451, by decide⟩ ⟨12, 2, 0, 698451, 91719, 3761, 65536⟩
    (by decide) selected_cut_27648

theorem unmarked_context_11_22929_698452 : frontier 10 ⟨698452, by decide⟩
    (prefixCache 11 22929) (prefixPartial 11 22929) = false := by
  decide +kernel

theorem node_context_11_22929_698452 : EJMOriginalGlobalDAGData.nodes 10 ⟨698452, by decide⟩ =
    .split (coordinate 11) (![⟨698345, by decide⟩,⟨170504, by decide⟩,⟨698393, by decide⟩,⟨698451, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22929_698452 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22929 ⟨698452, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22929
    ⟨698452, by decide⟩ (by decide) (![⟨698345, by decide⟩,⟨170504, by decide⟩,⟨698393, by decide⟩,⟨698451, by decide⟩]) unmarked_context_11_22929_698452 node_context_11_22929_698452
  intro a
  fin_cases a
  · exact context_12_91716_698345
  · exact context_12_91717_170504
  · exact context_12_91718_698393
  · exact context_12_91719_698451

theorem selected_cut_27649 : selected 9 ⟨698509, by decide⟩
    (prefixPartial 12 91720) = some ⟨12, 2, 0, 698509, 91720, 3541, 65536⟩ := by
  decide +kernel

theorem context_12_91720_698509 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91720 ⟨698509, by decide⟩ :=
  accepted_of_selected 12 91720 ⟨698509, by decide⟩ ⟨12, 2, 0, 698509, 91720, 3541, 65536⟩
    (by decide) selected_cut_27649

theorem selected_cut_27650 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 366884) = some ⟨13, 1, 0, 3444, 366884, 1, 16384⟩ := by
  decide +kernel

theorem context_13_366884_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366884 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 366884 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 366884, 1, 16384⟩
    (by decide) selected_cut_27650

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
