/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover143
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_13827 : selected 8 ⟨361548, by decide⟩
    (prefixPartial 13 107700) = some ⟨13, 2, 0, 361548, 107700, 645, 16384⟩ := by
  decide +kernel

theorem context_13_107700_361548 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107700 ⟨361548, by decide⟩ :=
  accepted_of_selected 13 107700 ⟨361548, by decide⟩ ⟨13, 2, 0, 361548, 107700, 645, 16384⟩
    (by decide) selected_cut_13827

theorem selected_cut_13828 : selected 8 ⟨361568, by decide⟩
    (prefixPartial 13 107701) = some ⟨13, 2, 0, 361568, 107701, 2077, 16384⟩ := by
  decide +kernel

theorem context_13_107701_361568 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107701 ⟨361568, by decide⟩ :=
  accepted_of_selected 13 107701 ⟨361568, by decide⟩ ⟨13, 2, 0, 361568, 107701, 2077, 16384⟩
    (by decide) selected_cut_13828

theorem selected_cut_13829 : selected 8 ⟨361586, by decide⟩
    (prefixPartial 13 107702) = some ⟨13, 2, 0, 361586, 107702, 1349, 16384⟩ := by
  decide +kernel

theorem context_13_107702_361586 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107702 ⟨361586, by decide⟩ :=
  accepted_of_selected 13 107702 ⟨361586, by decide⟩ ⟨13, 2, 0, 361586, 107702, 1349, 16384⟩
    (by decide) selected_cut_13829

theorem selected_cut_13830 : selected 8 ⟨361591, by decide⟩
    (prefixPartial 13 107703) = some ⟨13, 2, 0, 361591, 107703, 857, 16384⟩ := by
  decide +kernel

theorem context_13_107703_361591 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107703 ⟨361591, by decide⟩ :=
  accepted_of_selected 13 107703 ⟨361591, by decide⟩ ⟨13, 2, 0, 361591, 107703, 857, 16384⟩
    (by decide) selected_cut_13830

theorem unmarked_context_12_26925_361592 : frontier 9 ⟨361592, by decide⟩
    (prefixCache 12 26925) (prefixPartial 12 26925) = false := by
  decide +kernel

theorem node_context_12_26925_361592 : EJMOriginalGlobalDAGData.nodes 9 ⟨361592, by decide⟩ =
    .split (coordinate 12) (![⟨361548, by decide⟩,⟨361568, by decide⟩,⟨361586, by decide⟩,⟨361591, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26925_361592 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26925 ⟨361592, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26925
    ⟨361592, by decide⟩ (by decide) (![⟨361548, by decide⟩,⟨361568, by decide⟩,⟨361586, by decide⟩,⟨361591, by decide⟩]) unmarked_context_12_26925_361592 node_context_12_26925_361592
  intro a
  fin_cases a
  · exact context_13_107700_361548
  · exact context_13_107701_361568
  · exact context_13_107702_361586
  · exact context_13_107703_361591

theorem selected_cut_13831 : selected 8 ⟨361603, by decide⟩
    (prefixPartial 13 107704) = some ⟨13, 2, 0, 361603, 107704, 745, 16384⟩ := by
  decide +kernel

theorem context_13_107704_361603 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107704 ⟨361603, by decide⟩ :=
  accepted_of_selected 13 107704 ⟨361603, by decide⟩ ⟨13, 2, 0, 361603, 107704, 745, 16384⟩
    (by decide) selected_cut_13831

theorem selected_cut_13832 : selected 8 ⟨361627, by decide⟩
    (prefixPartial 13 107705) = some ⟨13, 2, 0, 361627, 107705, 2449, 16384⟩ := by
  decide +kernel

theorem context_13_107705_361627 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107705 ⟨361627, by decide⟩ :=
  accepted_of_selected 13 107705 ⟨361627, by decide⟩ ⟨13, 2, 0, 361627, 107705, 2449, 16384⟩
    (by decide) selected_cut_13832

theorem selected_cut_13833 : selected 8 ⟨361645, by decide⟩
    (prefixPartial 13 107706) = some ⟨13, 2, 0, 361645, 107706, 1309, 16384⟩ := by
  decide +kernel

theorem context_13_107706_361645 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107706 ⟨361645, by decide⟩ :=
  accepted_of_selected 13 107706 ⟨361645, by decide⟩ ⟨13, 2, 0, 361645, 107706, 1309, 16384⟩
    (by decide) selected_cut_13833

theorem selected_cut_13834 : selected 8 ⟨361650, by decide⟩
    (prefixPartial 13 107707) = some ⟨13, 2, 0, 361650, 107707, 933, 16384⟩ := by
  decide +kernel

theorem context_13_107707_361650 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107707 ⟨361650, by decide⟩ :=
  accepted_of_selected 13 107707 ⟨361650, by decide⟩ ⟨13, 2, 0, 361650, 107707, 933, 16384⟩
    (by decide) selected_cut_13834

theorem unmarked_context_12_26926_361651 : frontier 9 ⟨361651, by decide⟩
    (prefixCache 12 26926) (prefixPartial 12 26926) = false := by
  decide +kernel

theorem node_context_12_26926_361651 : EJMOriginalGlobalDAGData.nodes 9 ⟨361651, by decide⟩ =
    .split (coordinate 12) (![⟨361603, by decide⟩,⟨361627, by decide⟩,⟨361645, by decide⟩,⟨361650, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26926_361651 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26926 ⟨361651, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26926
    ⟨361651, by decide⟩ (by decide) (![⟨361603, by decide⟩,⟨361627, by decide⟩,⟨361645, by decide⟩,⟨361650, by decide⟩]) unmarked_context_12_26926_361651 node_context_12_26926_361651
  intro a
  fin_cases a
  · exact context_13_107704_361603
  · exact context_13_107705_361627
  · exact context_13_107706_361645
  · exact context_13_107707_361650

theorem selected_cut_13835 : selected 8 ⟨361662, by decide⟩
    (prefixPartial 13 107708) = some ⟨13, 2, 0, 361662, 107708, 781, 16384⟩ := by
  decide +kernel

theorem context_13_107708_361662 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107708 ⟨361662, by decide⟩ :=
  accepted_of_selected 13 107708 ⟨361662, by decide⟩ ⟨13, 2, 0, 361662, 107708, 781, 16384⟩
    (by decide) selected_cut_13835

theorem selected_cut_13836 : selected 8 ⟨361683, by decide⟩
    (prefixPartial 13 107709) = some ⟨13, 2, 0, 361683, 107709, 2485, 16384⟩ := by
  decide +kernel

theorem context_13_107709_361683 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107709 ⟨361683, by decide⟩ :=
  accepted_of_selected 13 107709 ⟨361683, by decide⟩ ⟨13, 2, 0, 361683, 107709, 2485, 16384⟩
    (by decide) selected_cut_13836

theorem selected_cut_13837 : selected 8 ⟨361701, by decide⟩
    (prefixPartial 13 107710) = some ⟨13, 2, 0, 361701, 107710, 1369, 16384⟩ := by
  decide +kernel

theorem context_13_107710_361701 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107710 ⟨361701, by decide⟩ :=
  accepted_of_selected 13 107710 ⟨361701, by decide⟩ ⟨13, 2, 0, 361701, 107710, 1369, 16384⟩
    (by decide) selected_cut_13837

theorem selected_cut_13838 : selected 8 ⟨361707, by decide⟩
    (prefixPartial 13 107711) = some ⟨13, 2, 0, 361707, 107711, 1005, 16384⟩ := by
  decide +kernel

theorem context_13_107711_361707 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107711 ⟨361707, by decide⟩ :=
  accepted_of_selected 13 107711 ⟨361707, by decide⟩ ⟨13, 2, 0, 361707, 107711, 1005, 16384⟩
    (by decide) selected_cut_13838

theorem unmarked_context_12_26927_361708 : frontier 9 ⟨361708, by decide⟩
    (prefixCache 12 26927) (prefixPartial 12 26927) = false := by
  decide +kernel

theorem node_context_12_26927_361708 : EJMOriginalGlobalDAGData.nodes 9 ⟨361708, by decide⟩ =
    .split (coordinate 12) (![⟨361662, by decide⟩,⟨361683, by decide⟩,⟨361701, by decide⟩,⟨361707, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26927_361708 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26927 ⟨361708, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26927
    ⟨361708, by decide⟩ (by decide) (![⟨361662, by decide⟩,⟨361683, by decide⟩,⟨361701, by decide⟩,⟨361707, by decide⟩]) unmarked_context_12_26927_361708 node_context_12_26927_361708
  intro a
  fin_cases a
  · exact context_13_107708_361662
  · exact context_13_107709_361683
  · exact context_13_107710_361701
  · exact context_13_107711_361707

theorem unmarked_context_11_6731_361709 : frontier 10 ⟨361709, by decide⟩
    (prefixCache 11 6731) (prefixPartial 11 6731) = false := by
  decide +kernel

theorem node_context_11_6731_361709 : EJMOriginalGlobalDAGData.nodes 10 ⟨361709, by decide⟩ =
    .split (coordinate 11) (![⟨361540, by decide⟩,⟨361592, by decide⟩,⟨361651, by decide⟩,⟨361708, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6731_361709 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6731 ⟨361709, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6731
    ⟨361709, by decide⟩ (by decide) (![⟨361540, by decide⟩,⟨361592, by decide⟩,⟨361651, by decide⟩,⟨361708, by decide⟩]) unmarked_context_11_6731_361709 node_context_11_6731_361709
  intro a
  fin_cases a
  · exact context_12_26924_361540
  · exact context_12_26925_361592
  · exact context_12_26926_361651
  · exact context_12_26927_361708

theorem unmarked_context_10_1682_361710 : frontier 11 ⟨361710, by decide⟩
    (prefixCache 10 1682) (prefixPartial 10 1682) = false := by
  decide +kernel

theorem node_context_10_1682_361710 : EJMOriginalGlobalDAGData.nodes 11 ⟨361710, by decide⟩ =
    .split (coordinate 10) (![⟨360782, by decide⟩,⟨361025, by decide⟩,⟨361475, by decide⟩,⟨361709, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1682_361710 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1682 ⟨361710, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1682
    ⟨361710, by decide⟩ (by decide) (![⟨360782, by decide⟩,⟨361025, by decide⟩,⟨361475, by decide⟩,⟨361709, by decide⟩]) unmarked_context_10_1682_361710 node_context_10_1682_361710
  intro a
  fin_cases a
  · exact context_11_6728_360782
  · exact context_11_6729_361025
  · exact context_11_6730_361475
  · exact context_11_6731_361709

theorem selected_cut_13839 : selected 8 ⟨361716, by decide⟩
    (prefixPartial 13 107712) = some ⟨13, 2, 0, 361716, 107712, 817, 16384⟩ := by
  decide +kernel

theorem context_13_107712_361716 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107712 ⟨361716, by decide⟩ :=
  accepted_of_selected 13 107712 ⟨361716, by decide⟩ ⟨13, 2, 0, 361716, 107712, 817, 16384⟩
    (by decide) selected_cut_13839

theorem selected_cut_13840 : selected 8 ⟨361737, by decide⟩
    (prefixPartial 13 107713) = some ⟨13, 2, 0, 361737, 107713, 2341, 16384⟩ := by
  decide +kernel

theorem context_13_107713_361737 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107713 ⟨361737, by decide⟩ :=
  accepted_of_selected 13 107713 ⟨361737, by decide⟩ ⟨13, 2, 0, 361737, 107713, 2341, 16384⟩
    (by decide) selected_cut_13840

theorem selected_cut_13841 : selected 8 ⟨361757, by decide⟩
    (prefixPartial 13 107714) = some ⟨13, 2, 0, 361757, 107714, 1525, 16384⟩ := by
  decide +kernel

theorem context_13_107714_361757 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107714 ⟨361757, by decide⟩ :=
  accepted_of_selected 13 107714 ⟨361757, by decide⟩ ⟨13, 2, 0, 361757, 107714, 1525, 16384⟩
    (by decide) selected_cut_13841

theorem selected_cut_13842 : selected 8 ⟨361763, by decide⟩
    (prefixPartial 13 107715) = some ⟨13, 2, 0, 361763, 107715, 885, 16384⟩ := by
  decide +kernel

theorem context_13_107715_361763 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107715 ⟨361763, by decide⟩ :=
  accepted_of_selected 13 107715 ⟨361763, by decide⟩ ⟨13, 2, 0, 361763, 107715, 885, 16384⟩
    (by decide) selected_cut_13842

theorem unmarked_context_12_26928_361764 : frontier 9 ⟨361764, by decide⟩
    (prefixCache 12 26928) (prefixPartial 12 26928) = false := by
  decide +kernel

theorem node_context_12_26928_361764 : EJMOriginalGlobalDAGData.nodes 9 ⟨361764, by decide⟩ =
    .split (coordinate 12) (![⟨361716, by decide⟩,⟨361737, by decide⟩,⟨361757, by decide⟩,⟨361763, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26928_361764 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26928 ⟨361764, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26928
    ⟨361764, by decide⟩ (by decide) (![⟨361716, by decide⟩,⟨361737, by decide⟩,⟨361757, by decide⟩,⟨361763, by decide⟩]) unmarked_context_12_26928_361764 node_context_12_26928_361764
  intro a
  fin_cases a
  · exact context_13_107712_361716
  · exact context_13_107713_361737
  · exact context_13_107714_361757
  · exact context_13_107715_361763

theorem selected_cut_13843 : selected 8 ⟨361772, by decide⟩
    (prefixPartial 13 107716) = some ⟨13, 2, 0, 361772, 107716, 741, 16384⟩ := by
  decide +kernel

theorem context_13_107716_361772 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107716 ⟨361772, by decide⟩ :=
  accepted_of_selected 13 107716 ⟨361772, by decide⟩ ⟨13, 2, 0, 361772, 107716, 741, 16384⟩
    (by decide) selected_cut_13843

theorem selected_cut_13844 : selected 8 ⟨361793, by decide⟩
    (prefixPartial 13 107717) = some ⟨13, 2, 0, 361793, 107717, 2021, 16384⟩ := by
  decide +kernel

theorem context_13_107717_361793 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107717 ⟨361793, by decide⟩ :=
  accepted_of_selected 13 107717 ⟨361793, by decide⟩ ⟨13, 2, 0, 361793, 107717, 2021, 16384⟩
    (by decide) selected_cut_13844

theorem selected_cut_13845 : selected 8 ⟨361811, by decide⟩
    (prefixPartial 13 107718) = some ⟨13, 2, 0, 361811, 107718, 1769, 16384⟩ := by
  decide +kernel

theorem context_13_107718_361811 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107718 ⟨361811, by decide⟩ :=
  accepted_of_selected 13 107718 ⟨361811, by decide⟩ ⟨13, 2, 0, 361811, 107718, 1769, 16384⟩
    (by decide) selected_cut_13845

theorem selected_cut_13846 : selected 8 ⟨361818, by decide⟩
    (prefixPartial 13 107719) = some ⟨13, 2, 0, 361818, 107719, 913, 16384⟩ := by
  decide +kernel

theorem context_13_107719_361818 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107719 ⟨361818, by decide⟩ :=
  accepted_of_selected 13 107719 ⟨361818, by decide⟩ ⟨13, 2, 0, 361818, 107719, 913, 16384⟩
    (by decide) selected_cut_13846

theorem unmarked_context_12_26929_361819 : frontier 9 ⟨361819, by decide⟩
    (prefixCache 12 26929) (prefixPartial 12 26929) = false := by
  decide +kernel

theorem node_context_12_26929_361819 : EJMOriginalGlobalDAGData.nodes 9 ⟨361819, by decide⟩ =
    .split (coordinate 12) (![⟨361772, by decide⟩,⟨361793, by decide⟩,⟨361811, by decide⟩,⟨361818, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26929_361819 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26929 ⟨361819, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26929
    ⟨361819, by decide⟩ (by decide) (![⟨361772, by decide⟩,⟨361793, by decide⟩,⟨361811, by decide⟩,⟨361818, by decide⟩]) unmarked_context_12_26929_361819 node_context_12_26929_361819
  intro a
  fin_cases a
  · exact context_13_107716_361772
  · exact context_13_107717_361793
  · exact context_13_107718_361811
  · exact context_13_107719_361818

theorem selected_cut_13847 : selected 8 ⟨361828, by decide⟩
    (prefixPartial 13 107720) = some ⟨13, 2, 0, 361828, 107720, 769, 16384⟩ := by
  decide +kernel

theorem context_13_107720_361828 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107720 ⟨361828, by decide⟩ :=
  accepted_of_selected 13 107720 ⟨361828, by decide⟩ ⟨13, 2, 0, 361828, 107720, 769, 16384⟩
    (by decide) selected_cut_13847

theorem selected_cut_13848 : selected 8 ⟨361853, by decide⟩
    (prefixPartial 13 107721) = some ⟨13, 2, 0, 361853, 107721, 2369, 16384⟩ := by
  decide +kernel

theorem context_13_107721_361853 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107721 ⟨361853, by decide⟩ :=
  accepted_of_selected 13 107721 ⟨361853, by decide⟩ ⟨13, 2, 0, 361853, 107721, 2369, 16384⟩
    (by decide) selected_cut_13848

theorem selected_cut_13849 : selected 8 ⟨361883, by decide⟩
    (prefixPartial 13 107722) = some ⟨13, 2, 0, 361883, 107722, 1997, 16384⟩ := by
  decide +kernel

theorem context_13_107722_361883 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107722 ⟨361883, by decide⟩ :=
  accepted_of_selected 13 107722 ⟨361883, by decide⟩ ⟨13, 2, 0, 361883, 107722, 1997, 16384⟩
    (by decide) selected_cut_13849

theorem selected_cut_13850 : selected 8 ⟨361890, by decide⟩
    (prefixPartial 13 107723) = some ⟨13, 2, 0, 361890, 107723, 997, 16384⟩ := by
  decide +kernel

theorem context_13_107723_361890 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107723 ⟨361890, by decide⟩ :=
  accepted_of_selected 13 107723 ⟨361890, by decide⟩ ⟨13, 2, 0, 361890, 107723, 997, 16384⟩
    (by decide) selected_cut_13850

theorem unmarked_context_12_26930_361891 : frontier 9 ⟨361891, by decide⟩
    (prefixCache 12 26930) (prefixPartial 12 26930) = false := by
  decide +kernel

theorem node_context_12_26930_361891 : EJMOriginalGlobalDAGData.nodes 9 ⟨361891, by decide⟩ =
    .split (coordinate 12) (![⟨361828, by decide⟩,⟨361853, by decide⟩,⟨361883, by decide⟩,⟨361890, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26930_361891 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26930 ⟨361891, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26930
    ⟨361891, by decide⟩ (by decide) (![⟨361828, by decide⟩,⟨361853, by decide⟩,⟨361883, by decide⟩,⟨361890, by decide⟩]) unmarked_context_12_26930_361891 node_context_12_26930_361891
  intro a
  fin_cases a
  · exact context_13_107720_361828
  · exact context_13_107721_361853
  · exact context_13_107722_361883
  · exact context_13_107723_361890

theorem selected_cut_13851 : selected 8 ⟨361905, by decide⟩
    (prefixPartial 13 107724) = some ⟨13, 2, 0, 361905, 107724, 917, 16384⟩ := by
  decide +kernel

theorem context_13_107724_361905 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107724 ⟨361905, by decide⟩ :=
  accepted_of_selected 13 107724 ⟨361905, by decide⟩ ⟨13, 2, 0, 361905, 107724, 917, 16384⟩
    (by decide) selected_cut_13851

theorem selected_cut_13852 : selected 8 ⟨361938, by decide⟩
    (prefixPartial 13 107725) = some ⟨13, 2, 0, 361938, 107725, 2609, 16384⟩ := by
  decide +kernel

theorem context_13_107725_361938 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107725 ⟨361938, by decide⟩ :=
  accepted_of_selected 13 107725 ⟨361938, by decide⟩ ⟨13, 2, 0, 361938, 107725, 2609, 16384⟩
    (by decide) selected_cut_13852

theorem selected_cut_13853 : selected 8 ⟨361968, by decide⟩
    (prefixPartial 13 107726) = some ⟨13, 2, 0, 361968, 107726, 2005, 16384⟩ := by
  decide +kernel

theorem context_13_107726_361968 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107726 ⟨361968, by decide⟩ :=
  accepted_of_selected 13 107726 ⟨361968, by decide⟩ ⟨13, 2, 0, 361968, 107726, 2005, 16384⟩
    (by decide) selected_cut_13853

theorem selected_cut_13854 : selected 8 ⟨361981, by decide⟩
    (prefixPartial 13 107727) = some ⟨13, 2, 0, 361981, 107727, 1033, 16384⟩ := by
  decide +kernel

theorem context_13_107727_361981 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107727 ⟨361981, by decide⟩ :=
  accepted_of_selected 13 107727 ⟨361981, by decide⟩ ⟨13, 2, 0, 361981, 107727, 1033, 16384⟩
    (by decide) selected_cut_13854

theorem unmarked_context_12_26931_361982 : frontier 9 ⟨361982, by decide⟩
    (prefixCache 12 26931) (prefixPartial 12 26931) = false := by
  decide +kernel

theorem node_context_12_26931_361982 : EJMOriginalGlobalDAGData.nodes 9 ⟨361982, by decide⟩ =
    .split (coordinate 12) (![⟨361905, by decide⟩,⟨361938, by decide⟩,⟨361968, by decide⟩,⟨361981, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26931_361982 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26931 ⟨361982, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26931
    ⟨361982, by decide⟩ (by decide) (![⟨361905, by decide⟩,⟨361938, by decide⟩,⟨361968, by decide⟩,⟨361981, by decide⟩]) unmarked_context_12_26931_361982 node_context_12_26931_361982
  intro a
  fin_cases a
  · exact context_13_107724_361905
  · exact context_13_107725_361938
  · exact context_13_107726_361968
  · exact context_13_107727_361981

theorem unmarked_context_11_6732_361983 : frontier 10 ⟨361983, by decide⟩
    (prefixCache 11 6732) (prefixPartial 11 6732) = false := by
  decide +kernel

theorem node_context_11_6732_361983 : EJMOriginalGlobalDAGData.nodes 10 ⟨361983, by decide⟩ =
    .split (coordinate 11) (![⟨361764, by decide⟩,⟨361819, by decide⟩,⟨361891, by decide⟩,⟨361982, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6732_361983 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6732 ⟨361983, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6732
    ⟨361983, by decide⟩ (by decide) (![⟨361764, by decide⟩,⟨361819, by decide⟩,⟨361891, by decide⟩,⟨361982, by decide⟩]) unmarked_context_11_6732_361983 node_context_11_6732_361983
  intro a
  fin_cases a
  · exact context_12_26928_361764
  · exact context_12_26929_361819
  · exact context_12_26930_361891
  · exact context_12_26931_361982

theorem selected_cut_13855 : selected 8 ⟨361989, by decide⟩
    (prefixPartial 13 107728) = some ⟨13, 2, 0, 361989, 107728, 549, 16384⟩ := by
  decide +kernel

theorem context_13_107728_361989 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107728 ⟨361989, by decide⟩ :=
  accepted_of_selected 13 107728 ⟨361989, by decide⟩ ⟨13, 2, 0, 361989, 107728, 549, 16384⟩
    (by decide) selected_cut_13855

theorem selected_cut_13856 : selected 8 ⟨362010, by decide⟩
    (prefixPartial 13 107729) = some ⟨13, 2, 0, 362010, 107729, 2049, 16384⟩ := by
  decide +kernel

theorem context_13_107729_362010 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107729 ⟨362010, by decide⟩ :=
  accepted_of_selected 13 107729 ⟨362010, by decide⟩ ⟨13, 2, 0, 362010, 107729, 2049, 16384⟩
    (by decide) selected_cut_13856

theorem selected_cut_13857 : selected 8 ⟨362026, by decide⟩
    (prefixPartial 13 107730) = some ⟨13, 2, 0, 362026, 107730, 1489, 16384⟩ := by
  decide +kernel

theorem context_13_107730_362026 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107730 ⟨362026, by decide⟩ :=
  accepted_of_selected 13 107730 ⟨362026, by decide⟩ ⟨13, 2, 0, 362026, 107730, 1489, 16384⟩
    (by decide) selected_cut_13857

theorem selected_cut_13858 : selected 8 ⟨362031, by decide⟩
    (prefixPartial 13 107731) = some ⟨13, 2, 0, 362031, 107731, 889, 16384⟩ := by
  decide +kernel

theorem context_13_107731_362031 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107731 ⟨362031, by decide⟩ :=
  accepted_of_selected 13 107731 ⟨362031, by decide⟩ ⟨13, 2, 0, 362031, 107731, 889, 16384⟩
    (by decide) selected_cut_13858

theorem unmarked_context_12_26932_362032 : frontier 9 ⟨362032, by decide⟩
    (prefixCache 12 26932) (prefixPartial 12 26932) = false := by
  decide +kernel

theorem node_context_12_26932_362032 : EJMOriginalGlobalDAGData.nodes 9 ⟨362032, by decide⟩ =
    .split (coordinate 12) (![⟨361989, by decide⟩,⟨362010, by decide⟩,⟨362026, by decide⟩,⟨362031, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26932_362032 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26932 ⟨362032, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26932
    ⟨362032, by decide⟩ (by decide) (![⟨361989, by decide⟩,⟨362010, by decide⟩,⟨362026, by decide⟩,⟨362031, by decide⟩]) unmarked_context_12_26932_362032 node_context_12_26932_362032
  intro a
  fin_cases a
  · exact context_13_107728_361989
  · exact context_13_107729_362010
  · exact context_13_107730_362026
  · exact context_13_107731_362031

theorem selected_cut_13859 : selected 8 ⟨362044, by decide⟩
    (prefixPartial 13 107732) = some ⟨13, 2, 0, 362044, 107732, 857, 16384⟩ := by
  decide +kernel

theorem context_13_107732_362044 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107732 ⟨362044, by decide⟩ :=
  accepted_of_selected 13 107732 ⟨362044, by decide⟩ ⟨13, 2, 0, 362044, 107732, 857, 16384⟩
    (by decide) selected_cut_13859

theorem selected_cut_13860 : selected 8 ⟨362076, by decide⟩
    (prefixPartial 13 107733) = some ⟨13, 2, 0, 362076, 107733, 3069, 16384⟩ := by
  decide +kernel

theorem context_13_107733_362076 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107733 ⟨362076, by decide⟩ :=
  accepted_of_selected 13 107733 ⟨362076, by decide⟩ ⟨13, 2, 0, 362076, 107733, 3069, 16384⟩
    (by decide) selected_cut_13860

theorem selected_cut_13861 : selected 8 ⟨362110, by decide⟩
    (prefixPartial 13 107734) = some ⟨13, 2, 0, 362110, 107734, 2289, 16384⟩ := by
  decide +kernel

theorem context_13_107734_362110 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107734 ⟨362110, by decide⟩ :=
  accepted_of_selected 13 107734 ⟨362110, by decide⟩ ⟨13, 2, 0, 362110, 107734, 2289, 16384⟩
    (by decide) selected_cut_13861

theorem selected_cut_13862 : selected 8 ⟨362119, by decide⟩
    (prefixPartial 13 107735) = some ⟨13, 2, 0, 362119, 107735, 1149, 16384⟩ := by
  decide +kernel

theorem context_13_107735_362119 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107735 ⟨362119, by decide⟩ :=
  accepted_of_selected 13 107735 ⟨362119, by decide⟩ ⟨13, 2, 0, 362119, 107735, 1149, 16384⟩
    (by decide) selected_cut_13862

theorem unmarked_context_12_26933_362120 : frontier 9 ⟨362120, by decide⟩
    (prefixCache 12 26933) (prefixPartial 12 26933) = false := by
  decide +kernel

theorem node_context_12_26933_362120 : EJMOriginalGlobalDAGData.nodes 9 ⟨362120, by decide⟩ =
    .split (coordinate 12) (![⟨362044, by decide⟩,⟨362076, by decide⟩,⟨362110, by decide⟩,⟨362119, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26933_362120 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26933 ⟨362120, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26933
    ⟨362120, by decide⟩ (by decide) (![⟨362044, by decide⟩,⟨362076, by decide⟩,⟨362110, by decide⟩,⟨362119, by decide⟩]) unmarked_context_12_26933_362120 node_context_12_26933_362120
  intro a
  fin_cases a
  · exact context_13_107732_362044
  · exact context_13_107733_362076
  · exact context_13_107734_362110
  · exact context_13_107735_362119

theorem selected_cut_13863 : selected 8 ⟨362129, by decide⟩
    (prefixPartial 13 107736) = some ⟨13, 2, 0, 362129, 107736, 549, 16384⟩ := by
  decide +kernel

theorem context_13_107736_362129 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107736 ⟨362129, by decide⟩ :=
  accepted_of_selected 13 107736 ⟨362129, by decide⟩ ⟨13, 2, 0, 362129, 107736, 549, 16384⟩
    (by decide) selected_cut_13863

theorem selected_cut_13864 : selected 8 ⟨362150, by decide⟩
    (prefixPartial 13 107737) = some ⟨13, 2, 0, 362150, 107737, 2113, 16384⟩ := by
  decide +kernel

theorem context_13_107737_362150 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107737 ⟨362150, by decide⟩ :=
  accepted_of_selected 13 107737 ⟨362150, by decide⟩ ⟨13, 2, 0, 362150, 107737, 2113, 16384⟩
    (by decide) selected_cut_13864

theorem selected_cut_13865 : selected 8 ⟨362170, by decide⟩
    (prefixPartial 13 107738) = some ⟨13, 2, 0, 362170, 107738, 1685, 16384⟩ := by
  decide +kernel

theorem context_13_107738_362170 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107738 ⟨362170, by decide⟩ :=
  accepted_of_selected 13 107738 ⟨362170, by decide⟩ ⟨13, 2, 0, 362170, 107738, 1685, 16384⟩
    (by decide) selected_cut_13865

theorem selected_cut_13866 : selected 8 ⟨362176, by decide⟩
    (prefixPartial 13 107739) = some ⟨13, 2, 0, 362176, 107739, 913, 16384⟩ := by
  decide +kernel

theorem context_13_107739_362176 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107739 ⟨362176, by decide⟩ :=
  accepted_of_selected 13 107739 ⟨362176, by decide⟩ ⟨13, 2, 0, 362176, 107739, 913, 16384⟩
    (by decide) selected_cut_13866

theorem unmarked_context_12_26934_362177 : frontier 9 ⟨362177, by decide⟩
    (prefixCache 12 26934) (prefixPartial 12 26934) = false := by
  decide +kernel

theorem node_context_12_26934_362177 : EJMOriginalGlobalDAGData.nodes 9 ⟨362177, by decide⟩ =
    .split (coordinate 12) (![⟨362129, by decide⟩,⟨362150, by decide⟩,⟨362170, by decide⟩,⟨362176, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26934_362177 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26934 ⟨362177, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26934
    ⟨362177, by decide⟩ (by decide) (![⟨362129, by decide⟩,⟨362150, by decide⟩,⟨362170, by decide⟩,⟨362176, by decide⟩]) unmarked_context_12_26934_362177 node_context_12_26934_362177
  intro a
  fin_cases a
  · exact context_13_107736_362129
  · exact context_13_107737_362150
  · exact context_13_107738_362170
  · exact context_13_107739_362176

theorem selected_cut_13867 : selected 8 ⟨362186, by decide⟩
    (prefixPartial 13 107740) = some ⟨13, 2, 0, 362186, 107740, 537, 16384⟩ := by
  decide +kernel

theorem context_13_107740_362186 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107740 ⟨362186, by decide⟩ :=
  accepted_of_selected 13 107740 ⟨362186, by decide⟩ ⟨13, 2, 0, 362186, 107740, 537, 16384⟩
    (by decide) selected_cut_13867

theorem selected_cut_13868 : selected 8 ⟨362213, by decide⟩
    (prefixPartial 13 107741) = some ⟨13, 2, 0, 362213, 107741, 2361, 16384⟩ := by
  decide +kernel

theorem context_13_107741_362213 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107741 ⟨362213, by decide⟩ :=
  accepted_of_selected 13 107741 ⟨362213, by decide⟩ ⟨13, 2, 0, 362213, 107741, 2361, 16384⟩
    (by decide) selected_cut_13868

theorem selected_cut_13869 : selected 8 ⟨362234, by decide⟩
    (prefixPartial 13 107742) = some ⟨13, 2, 0, 362234, 107742, 1753, 16384⟩ := by
  decide +kernel

theorem context_13_107742_362234 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107742 ⟨362234, by decide⟩ :=
  accepted_of_selected 13 107742 ⟨362234, by decide⟩ ⟨13, 2, 0, 362234, 107742, 1753, 16384⟩
    (by decide) selected_cut_13869

theorem selected_cut_13870 : selected 8 ⟨362239, by decide⟩
    (prefixPartial 13 107743) = some ⟨13, 2, 0, 362239, 107743, 905, 16384⟩ := by
  decide +kernel

theorem context_13_107743_362239 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107743 ⟨362239, by decide⟩ :=
  accepted_of_selected 13 107743 ⟨362239, by decide⟩ ⟨13, 2, 0, 362239, 107743, 905, 16384⟩
    (by decide) selected_cut_13870

theorem unmarked_context_12_26935_362240 : frontier 9 ⟨362240, by decide⟩
    (prefixCache 12 26935) (prefixPartial 12 26935) = false := by
  decide +kernel

theorem node_context_12_26935_362240 : EJMOriginalGlobalDAGData.nodes 9 ⟨362240, by decide⟩ =
    .split (coordinate 12) (![⟨362186, by decide⟩,⟨362213, by decide⟩,⟨362234, by decide⟩,⟨362239, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26935_362240 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26935 ⟨362240, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26935
    ⟨362240, by decide⟩ (by decide) (![⟨362186, by decide⟩,⟨362213, by decide⟩,⟨362234, by decide⟩,⟨362239, by decide⟩]) unmarked_context_12_26935_362240 node_context_12_26935_362240
  intro a
  fin_cases a
  · exact context_13_107740_362186
  · exact context_13_107741_362213
  · exact context_13_107742_362234
  · exact context_13_107743_362239

theorem unmarked_context_11_6733_362241 : frontier 10 ⟨362241, by decide⟩
    (prefixCache 11 6733) (prefixPartial 11 6733) = false := by
  decide +kernel

theorem node_context_11_6733_362241 : EJMOriginalGlobalDAGData.nodes 10 ⟨362241, by decide⟩ =
    .split (coordinate 11) (![⟨362032, by decide⟩,⟨362120, by decide⟩,⟨362177, by decide⟩,⟨362240, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6733_362241 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6733 ⟨362241, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6733
    ⟨362241, by decide⟩ (by decide) (![⟨362032, by decide⟩,⟨362120, by decide⟩,⟨362177, by decide⟩,⟨362240, by decide⟩]) unmarked_context_11_6733_362241 node_context_11_6733_362241
  intro a
  fin_cases a
  · exact context_12_26932_362032
  · exact context_12_26933_362120
  · exact context_12_26934_362177
  · exact context_12_26935_362240

theorem selected_cut_13871 : selected 8 ⟨362247, by decide⟩
    (prefixPartial 13 107744) = some ⟨13, 2, 0, 362247, 107744, 381, 16384⟩ := by
  decide +kernel

theorem context_13_107744_362247 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107744 ⟨362247, by decide⟩ :=
  accepted_of_selected 13 107744 ⟨362247, by decide⟩ ⟨13, 2, 0, 362247, 107744, 381, 16384⟩
    (by decide) selected_cut_13871

theorem selected_cut_13872 : selected 8 ⟨362278, by decide⟩
    (prefixPartial 13 107745) = some ⟨13, 2, 0, 362278, 107745, 2517, 16384⟩ := by
  decide +kernel

theorem context_13_107745_362278 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107745 ⟨362278, by decide⟩ :=
  accepted_of_selected 13 107745 ⟨362278, by decide⟩ ⟨13, 2, 0, 362278, 107745, 2517, 16384⟩
    (by decide) selected_cut_13872

theorem selected_cut_13873 : selected 8 ⟨362294, by decide⟩
    (prefixPartial 13 107746) = some ⟨13, 2, 0, 362294, 107746, 1773, 16384⟩ := by
  decide +kernel

theorem context_13_107746_362294 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107746 ⟨362294, by decide⟩ :=
  accepted_of_selected 13 107746 ⟨362294, by decide⟩ ⟨13, 2, 0, 362294, 107746, 1773, 16384⟩
    (by decide) selected_cut_13873

theorem selected_cut_13874 : selected 8 ⟨362301, by decide⟩
    (prefixPartial 13 107747) = some ⟨13, 2, 0, 362301, 107747, 993, 16384⟩ := by
  decide +kernel

theorem context_13_107747_362301 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107747 ⟨362301, by decide⟩ :=
  accepted_of_selected 13 107747 ⟨362301, by decide⟩ ⟨13, 2, 0, 362301, 107747, 993, 16384⟩
    (by decide) selected_cut_13874

theorem unmarked_context_12_26936_362302 : frontier 9 ⟨362302, by decide⟩
    (prefixCache 12 26936) (prefixPartial 12 26936) = false := by
  decide +kernel

theorem node_context_12_26936_362302 : EJMOriginalGlobalDAGData.nodes 9 ⟨362302, by decide⟩ =
    .split (coordinate 12) (![⟨362247, by decide⟩,⟨362278, by decide⟩,⟨362294, by decide⟩,⟨362301, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26936_362302 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26936 ⟨362302, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26936
    ⟨362302, by decide⟩ (by decide) (![⟨362247, by decide⟩,⟨362278, by decide⟩,⟨362294, by decide⟩,⟨362301, by decide⟩]) unmarked_context_12_26936_362302 node_context_12_26936_362302
  intro a
  fin_cases a
  · exact context_13_107744_362247
  · exact context_13_107745_362278
  · exact context_13_107746_362294
  · exact context_13_107747_362301

theorem selected_cut_13875 : selected 8 ⟨362309, by decide⟩
    (prefixPartial 13 107748) = some ⟨13, 2, 0, 362309, 107748, 373, 16384⟩ := by
  decide +kernel

theorem context_13_107748_362309 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107748 ⟨362309, by decide⟩ :=
  accepted_of_selected 13 107748 ⟨362309, by decide⟩ ⟨13, 2, 0, 362309, 107748, 373, 16384⟩
    (by decide) selected_cut_13875

theorem selected_cut_13876 : selected 8 ⟨362332, by decide⟩
    (prefixPartial 13 107749) = some ⟨13, 2, 0, 362332, 107749, 1873, 16384⟩ := by
  decide +kernel

theorem context_13_107749_362332 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107749 ⟨362332, by decide⟩ :=
  accepted_of_selected 13 107749 ⟨362332, by decide⟩ ⟨13, 2, 0, 362332, 107749, 1873, 16384⟩
    (by decide) selected_cut_13876

theorem selected_cut_13877 : selected 8 ⟨362349, by decide⟩
    (prefixPartial 13 107750) = some ⟨13, 2, 0, 362349, 107750, 1681, 16384⟩ := by
  decide +kernel

theorem context_13_107750_362349 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107750 ⟨362349, by decide⟩ :=
  accepted_of_selected 13 107750 ⟨362349, by decide⟩ ⟨13, 2, 0, 362349, 107750, 1681, 16384⟩
    (by decide) selected_cut_13877

theorem selected_cut_13878 : selected 8 ⟨362355, by decide⟩
    (prefixPartial 13 107751) = some ⟨13, 2, 0, 362355, 107751, 965, 16384⟩ := by
  decide +kernel

theorem context_13_107751_362355 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107751 ⟨362355, by decide⟩ :=
  accepted_of_selected 13 107751 ⟨362355, by decide⟩ ⟨13, 2, 0, 362355, 107751, 965, 16384⟩
    (by decide) selected_cut_13878

theorem unmarked_context_12_26937_362356 : frontier 9 ⟨362356, by decide⟩
    (prefixCache 12 26937) (prefixPartial 12 26937) = false := by
  decide +kernel

theorem node_context_12_26937_362356 : EJMOriginalGlobalDAGData.nodes 9 ⟨362356, by decide⟩ =
    .split (coordinate 12) (![⟨362309, by decide⟩,⟨362332, by decide⟩,⟨362349, by decide⟩,⟨362355, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26937_362356 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26937 ⟨362356, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26937
    ⟨362356, by decide⟩ (by decide) (![⟨362309, by decide⟩,⟨362332, by decide⟩,⟨362349, by decide⟩,⟨362355, by decide⟩]) unmarked_context_12_26937_362356 node_context_12_26937_362356
  intro a
  fin_cases a
  · exact context_13_107748_362309
  · exact context_13_107749_362332
  · exact context_13_107750_362349
  · exact context_13_107751_362355

theorem selected_cut_13879 : selected 8 ⟨362363, by decide⟩
    (prefixPartial 13 107752) = some ⟨13, 2, 0, 362363, 107752, 313, 16384⟩ := by
  decide +kernel

theorem context_13_107752_362363 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107752 ⟨362363, by decide⟩ :=
  accepted_of_selected 13 107752 ⟨362363, by decide⟩ ⟨13, 2, 0, 362363, 107752, 313, 16384⟩
    (by decide) selected_cut_13879

theorem selected_cut_13880 : selected 8 ⟨362390, by decide⟩
    (prefixPartial 13 107753) = some ⟨13, 2, 0, 362390, 107753, 2481, 16384⟩ := by
  decide +kernel

theorem context_13_107753_362390 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107753 ⟨362390, by decide⟩ :=
  accepted_of_selected 13 107753 ⟨362390, by decide⟩ ⟨13, 2, 0, 362390, 107753, 2481, 16384⟩
    (by decide) selected_cut_13880

theorem selected_cut_13881 : selected 8 ⟨362408, by decide⟩
    (prefixPartial 13 107754) = some ⟨13, 2, 0, 362408, 107754, 1889, 16384⟩ := by
  decide +kernel

theorem context_13_107754_362408 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107754 ⟨362408, by decide⟩ :=
  accepted_of_selected 13 107754 ⟨362408, by decide⟩ ⟨13, 2, 0, 362408, 107754, 1889, 16384⟩
    (by decide) selected_cut_13881

theorem selected_cut_13882 : selected 8 ⟨362416, by decide⟩
    (prefixPartial 13 107755) = some ⟨13, 2, 0, 362416, 107755, 997, 16384⟩ := by
  decide +kernel

theorem context_13_107755_362416 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107755 ⟨362416, by decide⟩ :=
  accepted_of_selected 13 107755 ⟨362416, by decide⟩ ⟨13, 2, 0, 362416, 107755, 997, 16384⟩
    (by decide) selected_cut_13882

theorem unmarked_context_12_26938_362417 : frontier 9 ⟨362417, by decide⟩
    (prefixCache 12 26938) (prefixPartial 12 26938) = false := by
  decide +kernel

theorem node_context_12_26938_362417 : EJMOriginalGlobalDAGData.nodes 9 ⟨362417, by decide⟩ =
    .split (coordinate 12) (![⟨362363, by decide⟩,⟨362390, by decide⟩,⟨362408, by decide⟩,⟨362416, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26938_362417 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26938 ⟨362417, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26938
    ⟨362417, by decide⟩ (by decide) (![⟨362363, by decide⟩,⟨362390, by decide⟩,⟨362408, by decide⟩,⟨362416, by decide⟩]) unmarked_context_12_26938_362417 node_context_12_26938_362417
  intro a
  fin_cases a
  · exact context_13_107752_362363
  · exact context_13_107753_362390
  · exact context_13_107754_362408
  · exact context_13_107755_362416

theorem selected_cut_13883 : selected 8 ⟨362425, by decide⟩
    (prefixPartial 13 107756) = some ⟨13, 2, 0, 362425, 107756, 341, 16384⟩ := by
  decide +kernel

theorem context_13_107756_362425 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107756 ⟨362425, by decide⟩ :=
  accepted_of_selected 13 107756 ⟨362425, by decide⟩ ⟨13, 2, 0, 362425, 107756, 341, 16384⟩
    (by decide) selected_cut_13883

theorem selected_cut_13884 : selected 8 ⟨362464, by decide⟩
    (prefixPartial 13 107757) = some ⟨13, 2, 0, 362464, 107757, 2913, 16384⟩ := by
  decide +kernel

theorem context_13_107757_362464 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107757 ⟨362464, by decide⟩ :=
  accepted_of_selected 13 107757 ⟨362464, by decide⟩ ⟨13, 2, 0, 362464, 107757, 2913, 16384⟩
    (by decide) selected_cut_13884

theorem selected_cut_13885 : selected 8 ⟨362487, by decide⟩
    (prefixPartial 13 107758) = some ⟨13, 2, 0, 362487, 107758, 1813, 16384⟩ := by
  decide +kernel

theorem context_13_107758_362487 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107758 ⟨362487, by decide⟩ :=
  accepted_of_selected 13 107758 ⟨362487, by decide⟩ ⟨13, 2, 0, 362487, 107758, 1813, 16384⟩
    (by decide) selected_cut_13885

theorem selected_cut_13886 : selected 8 ⟨362498, by decide⟩
    (prefixPartial 13 107759) = some ⟨13, 2, 0, 362498, 107759, 1005, 16384⟩ := by
  decide +kernel

theorem context_13_107759_362498 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107759 ⟨362498, by decide⟩ :=
  accepted_of_selected 13 107759 ⟨362498, by decide⟩ ⟨13, 2, 0, 362498, 107759, 1005, 16384⟩
    (by decide) selected_cut_13886

theorem unmarked_context_12_26939_362499 : frontier 9 ⟨362499, by decide⟩
    (prefixCache 12 26939) (prefixPartial 12 26939) = false := by
  decide +kernel

theorem node_context_12_26939_362499 : EJMOriginalGlobalDAGData.nodes 9 ⟨362499, by decide⟩ =
    .split (coordinate 12) (![⟨362425, by decide⟩,⟨362464, by decide⟩,⟨362487, by decide⟩,⟨362498, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26939_362499 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26939 ⟨362499, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26939
    ⟨362499, by decide⟩ (by decide) (![⟨362425, by decide⟩,⟨362464, by decide⟩,⟨362487, by decide⟩,⟨362498, by decide⟩]) unmarked_context_12_26939_362499 node_context_12_26939_362499
  intro a
  fin_cases a
  · exact context_13_107756_362425
  · exact context_13_107757_362464
  · exact context_13_107758_362487
  · exact context_13_107759_362498

theorem unmarked_context_11_6734_362500 : frontier 10 ⟨362500, by decide⟩
    (prefixCache 11 6734) (prefixPartial 11 6734) = false := by
  decide +kernel

theorem node_context_11_6734_362500 : EJMOriginalGlobalDAGData.nodes 10 ⟨362500, by decide⟩ =
    .split (coordinate 11) (![⟨362302, by decide⟩,⟨362356, by decide⟩,⟨362417, by decide⟩,⟨362499, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6734_362500 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6734 ⟨362500, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6734
    ⟨362500, by decide⟩ (by decide) (![⟨362302, by decide⟩,⟨362356, by decide⟩,⟨362417, by decide⟩,⟨362499, by decide⟩]) unmarked_context_11_6734_362500 node_context_11_6734_362500
  intro a
  fin_cases a
  · exact context_12_26936_362302
  · exact context_12_26937_362356
  · exact context_12_26938_362417
  · exact context_12_26939_362499

theorem selected_cut_13887 : selected 8 ⟨362503, by decide⟩
    (prefixPartial 13 107760) = some ⟨13, 2, 0, 362503, 107760, 129, 16384⟩ := by
  decide +kernel

theorem context_13_107760_362503 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107760 ⟨362503, by decide⟩ :=
  accepted_of_selected 13 107760 ⟨362503, by decide⟩ ⟨13, 2, 0, 362503, 107760, 129, 16384⟩
    (by decide) selected_cut_13887

theorem selected_cut_13888 : selected 8 ⟨362528, by decide⟩
    (prefixPartial 13 107761) = some ⟨13, 2, 0, 362528, 107761, 2377, 16384⟩ := by
  decide +kernel

theorem context_13_107761_362528 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107761 ⟨362528, by decide⟩ :=
  accepted_of_selected 13 107761 ⟨362528, by decide⟩ ⟨13, 2, 0, 362528, 107761, 2377, 16384⟩
    (by decide) selected_cut_13888

theorem selected_cut_13889 : selected 8 ⟨362545, by decide⟩
    (prefixPartial 13 107762) = some ⟨13, 2, 0, 362545, 107762, 1601, 16384⟩ := by
  decide +kernel

theorem context_13_107762_362545 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107762 ⟨362545, by decide⟩ :=
  accepted_of_selected 13 107762 ⟨362545, by decide⟩ ⟨13, 2, 0, 362545, 107762, 1601, 16384⟩
    (by decide) selected_cut_13889

theorem selected_cut_13890 : selected 8 ⟨362549, by decide⟩
    (prefixPartial 13 107763) = some ⟨13, 2, 0, 362549, 107763, 1017, 16384⟩ := by
  decide +kernel

theorem context_13_107763_362549 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107763 ⟨362549, by decide⟩ :=
  accepted_of_selected 13 107763 ⟨362549, by decide⟩ ⟨13, 2, 0, 362549, 107763, 1017, 16384⟩
    (by decide) selected_cut_13890

theorem unmarked_context_12_26940_362550 : frontier 9 ⟨362550, by decide⟩
    (prefixCache 12 26940) (prefixPartial 12 26940) = false := by
  decide +kernel

theorem node_context_12_26940_362550 : EJMOriginalGlobalDAGData.nodes 9 ⟨362550, by decide⟩ =
    .split (coordinate 12) (![⟨362503, by decide⟩,⟨362528, by decide⟩,⟨362545, by decide⟩,⟨362549, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26940_362550 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26940 ⟨362550, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26940
    ⟨362550, by decide⟩ (by decide) (![⟨362503, by decide⟩,⟨362528, by decide⟩,⟨362545, by decide⟩,⟨362549, by decide⟩]) unmarked_context_12_26940_362550 node_context_12_26940_362550
  intro a
  fin_cases a
  · exact context_13_107760_362503
  · exact context_13_107761_362528
  · exact context_13_107762_362545
  · exact context_13_107763_362549

theorem selected_cut_13891 : selected 8 ⟨362553, by decide⟩
    (prefixPartial 13 107764) = some ⟨13, 2, 0, 362553, 107764, 133, 16384⟩ := by
  decide +kernel

theorem context_13_107764_362553 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107764 ⟨362553, by decide⟩ :=
  accepted_of_selected 13 107764 ⟨362553, by decide⟩ ⟨13, 2, 0, 362553, 107764, 133, 16384⟩
    (by decide) selected_cut_13891

theorem selected_cut_13892 : selected 8 ⟨362575, by decide⟩
    (prefixPartial 13 107765) = some ⟨13, 2, 0, 362575, 107765, 2029, 16384⟩ := by
  decide +kernel

theorem context_13_107765_362575 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107765 ⟨362575, by decide⟩ :=
  accepted_of_selected 13 107765 ⟨362575, by decide⟩ ⟨13, 2, 0, 362575, 107765, 2029, 16384⟩
    (by decide) selected_cut_13892

theorem selected_cut_13893 : selected 8 ⟨362593, by decide⟩
    (prefixPartial 13 107766) = some ⟨13, 2, 0, 362593, 107766, 1533, 16384⟩ := by
  decide +kernel

theorem context_13_107766_362593 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107766 ⟨362593, by decide⟩ :=
  accepted_of_selected 13 107766 ⟨362593, by decide⟩ ⟨13, 2, 0, 362593, 107766, 1533, 16384⟩
    (by decide) selected_cut_13893

theorem selected_cut_13894 : selected 8 ⟨362598, by decide⟩
    (prefixPartial 13 107767) = some ⟨13, 2, 0, 362598, 107767, 885, 16384⟩ := by
  decide +kernel

theorem context_13_107767_362598 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107767 ⟨362598, by decide⟩ :=
  accepted_of_selected 13 107767 ⟨362598, by decide⟩ ⟨13, 2, 0, 362598, 107767, 885, 16384⟩
    (by decide) selected_cut_13894

theorem unmarked_context_12_26941_362599 : frontier 9 ⟨362599, by decide⟩
    (prefixCache 12 26941) (prefixPartial 12 26941) = false := by
  decide +kernel

theorem node_context_12_26941_362599 : EJMOriginalGlobalDAGData.nodes 9 ⟨362599, by decide⟩ =
    .split (coordinate 12) (![⟨362553, by decide⟩,⟨362575, by decide⟩,⟨362593, by decide⟩,⟨362598, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26941_362599 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26941 ⟨362599, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26941
    ⟨362599, by decide⟩ (by decide) (![⟨362553, by decide⟩,⟨362575, by decide⟩,⟨362593, by decide⟩,⟨362598, by decide⟩]) unmarked_context_12_26941_362599 node_context_12_26941_362599
  intro a
  fin_cases a
  · exact context_13_107764_362553
  · exact context_13_107765_362575
  · exact context_13_107766_362593
  · exact context_13_107767_362598

theorem selected_cut_13895 : selected 8 ⟨362603, by decide⟩
    (prefixPartial 13 107768) = some ⟨13, 2, 0, 362603, 107768, 85, 16384⟩ := by
  decide +kernel

theorem context_13_107768_362603 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107768 ⟨362603, by decide⟩ :=
  accepted_of_selected 13 107768 ⟨362603, by decide⟩ ⟨13, 2, 0, 362603, 107768, 85, 16384⟩
    (by decide) selected_cut_13895

theorem selected_cut_13896 : selected 8 ⟨362627, by decide⟩
    (prefixPartial 13 107769) = some ⟨13, 2, 0, 362627, 107769, 2469, 16384⟩ := by
  decide +kernel

theorem context_13_107769_362627 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107769 ⟨362627, by decide⟩ :=
  accepted_of_selected 13 107769 ⟨362627, by decide⟩ ⟨13, 2, 0, 362627, 107769, 2469, 16384⟩
    (by decide) selected_cut_13896

theorem selected_cut_13897 : selected 8 ⟨362648, by decide⟩
    (prefixPartial 13 107770) = some ⟨13, 2, 0, 362648, 107770, 1629, 16384⟩ := by
  decide +kernel

theorem context_13_107770_362648 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107770 ⟨362648, by decide⟩ :=
  accepted_of_selected 13 107770 ⟨362648, by decide⟩ ⟨13, 2, 0, 362648, 107770, 1629, 16384⟩
    (by decide) selected_cut_13897

theorem selected_cut_13898 : selected 8 ⟨362656, by decide⟩
    (prefixPartial 13 107771) = some ⟨13, 2, 0, 362656, 107771, 957, 16384⟩ := by
  decide +kernel

theorem context_13_107771_362656 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107771 ⟨362656, by decide⟩ :=
  accepted_of_selected 13 107771 ⟨362656, by decide⟩ ⟨13, 2, 0, 362656, 107771, 957, 16384⟩
    (by decide) selected_cut_13898

theorem unmarked_context_12_26942_362657 : frontier 9 ⟨362657, by decide⟩
    (prefixCache 12 26942) (prefixPartial 12 26942) = false := by
  decide +kernel

theorem node_context_12_26942_362657 : EJMOriginalGlobalDAGData.nodes 9 ⟨362657, by decide⟩ =
    .split (coordinate 12) (![⟨362603, by decide⟩,⟨362627, by decide⟩,⟨362648, by decide⟩,⟨362656, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26942_362657 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26942 ⟨362657, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26942
    ⟨362657, by decide⟩ (by decide) (![⟨362603, by decide⟩,⟨362627, by decide⟩,⟨362648, by decide⟩,⟨362656, by decide⟩]) unmarked_context_12_26942_362657 node_context_12_26942_362657
  intro a
  fin_cases a
  · exact context_13_107768_362603
  · exact context_13_107769_362627
  · exact context_13_107770_362648
  · exact context_13_107771_362656

theorem selected_cut_13899 : selected 8 ⟨362661, by decide⟩
    (prefixPartial 13 107772) = some ⟨13, 2, 0, 362661, 107772, 77, 16384⟩ := by
  decide +kernel

theorem context_13_107772_362661 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107772 ⟨362661, by decide⟩ :=
  accepted_of_selected 13 107772 ⟨362661, by decide⟩ ⟨13, 2, 0, 362661, 107772, 77, 16384⟩
    (by decide) selected_cut_13899

theorem selected_cut_13900 : selected 8 ⟨362684, by decide⟩
    (prefixPartial 13 107773) = some ⟨13, 2, 0, 362684, 107773, 2565, 16384⟩ := by
  decide +kernel

theorem context_13_107773_362684 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107773 ⟨362684, by decide⟩ :=
  accepted_of_selected 13 107773 ⟨362684, by decide⟩ ⟨13, 2, 0, 362684, 107773, 2565, 16384⟩
    (by decide) selected_cut_13900

theorem selected_cut_13901 : selected 8 ⟨362705, by decide⟩
    (prefixPartial 13 107774) = some ⟨13, 2, 0, 362705, 107774, 1653, 16384⟩ := by
  decide +kernel

theorem context_13_107774_362705 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107774 ⟨362705, by decide⟩ :=
  accepted_of_selected 13 107774 ⟨362705, by decide⟩ ⟨13, 2, 0, 362705, 107774, 1653, 16384⟩
    (by decide) selected_cut_13901

theorem selected_cut_13902 : selected 8 ⟨362714, by decide⟩
    (prefixPartial 13 107775) = some ⟨13, 2, 0, 362714, 107775, 1013, 16384⟩ := by
  decide +kernel

theorem context_13_107775_362714 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107775 ⟨362714, by decide⟩ :=
  accepted_of_selected 13 107775 ⟨362714, by decide⟩ ⟨13, 2, 0, 362714, 107775, 1013, 16384⟩
    (by decide) selected_cut_13902

theorem unmarked_context_12_26943_362715 : frontier 9 ⟨362715, by decide⟩
    (prefixCache 12 26943) (prefixPartial 12 26943) = false := by
  decide +kernel

theorem node_context_12_26943_362715 : EJMOriginalGlobalDAGData.nodes 9 ⟨362715, by decide⟩ =
    .split (coordinate 12) (![⟨362661, by decide⟩,⟨362684, by decide⟩,⟨362705, by decide⟩,⟨362714, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26943_362715 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26943 ⟨362715, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26943
    ⟨362715, by decide⟩ (by decide) (![⟨362661, by decide⟩,⟨362684, by decide⟩,⟨362705, by decide⟩,⟨362714, by decide⟩]) unmarked_context_12_26943_362715 node_context_12_26943_362715
  intro a
  fin_cases a
  · exact context_13_107772_362661
  · exact context_13_107773_362684
  · exact context_13_107774_362705
  · exact context_13_107775_362714

theorem unmarked_context_11_6735_362716 : frontier 10 ⟨362716, by decide⟩
    (prefixCache 11 6735) (prefixPartial 11 6735) = false := by
  decide +kernel

theorem node_context_11_6735_362716 : EJMOriginalGlobalDAGData.nodes 10 ⟨362716, by decide⟩ =
    .split (coordinate 11) (![⟨362550, by decide⟩,⟨362599, by decide⟩,⟨362657, by decide⟩,⟨362715, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6735_362716 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6735 ⟨362716, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6735
    ⟨362716, by decide⟩ (by decide) (![⟨362550, by decide⟩,⟨362599, by decide⟩,⟨362657, by decide⟩,⟨362715, by decide⟩]) unmarked_context_11_6735_362716 node_context_11_6735_362716
  intro a
  fin_cases a
  · exact context_12_26940_362550
  · exact context_12_26941_362599
  · exact context_12_26942_362657
  · exact context_12_26943_362715

theorem unmarked_context_10_1683_362717 : frontier 11 ⟨362717, by decide⟩
    (prefixCache 10 1683) (prefixPartial 10 1683) = false := by
  decide +kernel

theorem node_context_10_1683_362717 : EJMOriginalGlobalDAGData.nodes 11 ⟨362717, by decide⟩ =
    .split (coordinate 10) (![⟨361983, by decide⟩,⟨362241, by decide⟩,⟨362500, by decide⟩,⟨362716, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1683_362717 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1683 ⟨362717, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1683
    ⟨362717, by decide⟩ (by decide) (![⟨361983, by decide⟩,⟨362241, by decide⟩,⟨362500, by decide⟩,⟨362716, by decide⟩]) unmarked_context_10_1683_362717 node_context_10_1683_362717
  intro a
  fin_cases a
  · exact context_11_6732_361983
  · exact context_11_6733_362241
  · exact context_11_6734_362500
  · exact context_11_6735_362716

theorem unmarked_context_9_420_362718 : frontier 12 ⟨362718, by decide⟩
    (prefixCache 9 420) (prefixPartial 9 420) = false := by
  decide +kernel

theorem node_context_9_420_362718 : EJMOriginalGlobalDAGData.nodes 12 ⟨362718, by decide⟩ =
    .split (coordinate 9) (![⟨359425, by decide⟩,⟨360510, by decide⟩,⟨361710, by decide⟩,⟨362717, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_420_362718 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 420 ⟨362718, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 420
    ⟨362718, by decide⟩ (by decide) (![⟨359425, by decide⟩,⟨360510, by decide⟩,⟨361710, by decide⟩,⟨362717, by decide⟩]) unmarked_context_9_420_362718 node_context_9_420_362718
  intro a
  fin_cases a
  · exact context_10_1680_359425
  · exact context_10_1681_360510
  · exact context_10_1682_361710
  · exact context_10_1683_362717

theorem selected_cut_13903 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 107776) = some ⟨13, 1, 0, 3444, 107776, 1, 16384⟩ := by
  decide +kernel

theorem context_13_107776_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107776 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 107776 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 107776, 1, 16384⟩
    (by decide) selected_cut_13903

theorem selected_cut_13904 : selected 8 ⟨362742, by decide⟩
    (prefixPartial 13 107777) = some ⟨13, 2, 0, 362742, 107777, 2653, 16384⟩ := by
  decide +kernel

theorem context_13_107777_362742 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107777 ⟨362742, by decide⟩ :=
  accepted_of_selected 13 107777 ⟨362742, by decide⟩ ⟨13, 2, 0, 362742, 107777, 2653, 16384⟩
    (by decide) selected_cut_13904

theorem selected_cut_13905 : selected 8 ⟨362762, by decide⟩
    (prefixPartial 13 107778) = some ⟨13, 2, 0, 362762, 107778, 1733, 16384⟩ := by
  decide +kernel

theorem context_13_107778_362762 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107778 ⟨362762, by decide⟩ :=
  accepted_of_selected 13 107778 ⟨362762, by decide⟩ ⟨13, 2, 0, 362762, 107778, 1733, 16384⟩
    (by decide) selected_cut_13905

theorem selected_cut_13906 : selected 8 ⟨362769, by decide⟩
    (prefixPartial 13 107779) = some ⟨13, 2, 0, 362769, 107779, 941, 16384⟩ := by
  decide +kernel

theorem context_13_107779_362769 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107779 ⟨362769, by decide⟩ :=
  accepted_of_selected 13 107779 ⟨362769, by decide⟩ ⟨13, 2, 0, 362769, 107779, 941, 16384⟩
    (by decide) selected_cut_13906

theorem unmarked_context_12_26944_362770 : frontier 9 ⟨362770, by decide⟩
    (prefixCache 12 26944) (prefixPartial 12 26944) = false := by
  decide +kernel

theorem node_context_12_26944_362770 : EJMOriginalGlobalDAGData.nodes 9 ⟨362770, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨362742, by decide⟩,⟨362762, by decide⟩,⟨362769, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26944_362770 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26944 ⟨362770, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26944
    ⟨362770, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨362742, by decide⟩,⟨362762, by decide⟩,⟨362769, by decide⟩]) unmarked_context_12_26944_362770 node_context_12_26944_362770
  intro a
  fin_cases a
  · exact context_13_107776_3444
  · exact context_13_107777_362742
  · exact context_13_107778_362762
  · exact context_13_107779_362769

theorem selected_cut_13907 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 107780) = some ⟨13, 1, 0, 3444, 107780, 1, 16384⟩ := by
  decide +kernel

theorem context_13_107780_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107780 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 107780 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 107780, 1, 16384⟩
    (by decide) selected_cut_13907

theorem selected_cut_13908 : selected 8 ⟨362801, by decide⟩
    (prefixPartial 13 107781) = some ⟨13, 2, 0, 362801, 107781, 3041, 16384⟩ := by
  decide +kernel

theorem context_13_107781_362801 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107781 ⟨362801, by decide⟩ :=
  accepted_of_selected 13 107781 ⟨362801, by decide⟩ ⟨13, 2, 0, 362801, 107781, 3041, 16384⟩
    (by decide) selected_cut_13908

theorem selected_cut_13909 : selected 8 ⟨362823, by decide⟩
    (prefixPartial 13 107782) = some ⟨13, 2, 0, 362823, 107782, 2325, 16384⟩ := by
  decide +kernel

theorem context_13_107782_362823 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107782 ⟨362823, by decide⟩ :=
  accepted_of_selected 13 107782 ⟨362823, by decide⟩ ⟨13, 2, 0, 362823, 107782, 2325, 16384⟩
    (by decide) selected_cut_13909

theorem selected_cut_13910 : selected 8 ⟨362832, by decide⟩
    (prefixPartial 13 107783) = some ⟨13, 2, 0, 362832, 107783, 1225, 16384⟩ := by
  decide +kernel

theorem context_13_107783_362832 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107783 ⟨362832, by decide⟩ :=
  accepted_of_selected 13 107783 ⟨362832, by decide⟩ ⟨13, 2, 0, 362832, 107783, 1225, 16384⟩
    (by decide) selected_cut_13910

theorem unmarked_context_12_26945_362833 : frontier 9 ⟨362833, by decide⟩
    (prefixCache 12 26945) (prefixPartial 12 26945) = false := by
  decide +kernel

theorem node_context_12_26945_362833 : EJMOriginalGlobalDAGData.nodes 9 ⟨362833, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨362801, by decide⟩,⟨362823, by decide⟩,⟨362832, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26945_362833 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26945 ⟨362833, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26945
    ⟨362833, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨362801, by decide⟩,⟨362823, by decide⟩,⟨362832, by decide⟩]) unmarked_context_12_26945_362833 node_context_12_26945_362833
  intro a
  fin_cases a
  · exact context_13_107780_3444
  · exact context_13_107781_362801
  · exact context_13_107782_362823
  · exact context_13_107783_362832

theorem selected_cut_13911 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 107784) = some ⟨13, 1, 0, 3444, 107784, 1, 16384⟩ := by
  decide +kernel

theorem context_13_107784_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107784 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 107784 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 107784, 1, 16384⟩
    (by decide) selected_cut_13911

theorem selected_cut_13912 : selected 8 ⟨362859, by decide⟩
    (prefixPartial 13 107785) = some ⟨13, 2, 0, 362859, 107785, 2625, 16384⟩ := by
  decide +kernel

theorem context_13_107785_362859 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107785 ⟨362859, by decide⟩ :=
  accepted_of_selected 13 107785 ⟨362859, by decide⟩ ⟨13, 2, 0, 362859, 107785, 2625, 16384⟩
    (by decide) selected_cut_13912

theorem selected_cut_13913 : selected 8 ⟨362877, by decide⟩
    (prefixPartial 13 107786) = some ⟨13, 2, 0, 362877, 107786, 2093, 16384⟩ := by
  decide +kernel

theorem context_13_107786_362877 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107786 ⟨362877, by decide⟩ :=
  accepted_of_selected 13 107786 ⟨362877, by decide⟩ ⟨13, 2, 0, 362877, 107786, 2093, 16384⟩
    (by decide) selected_cut_13913

theorem selected_cut_13914 : selected 8 ⟨362884, by decide⟩
    (prefixPartial 13 107787) = some ⟨13, 2, 0, 362884, 107787, 1077, 16384⟩ := by
  decide +kernel

theorem context_13_107787_362884 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107787 ⟨362884, by decide⟩ :=
  accepted_of_selected 13 107787 ⟨362884, by decide⟩ ⟨13, 2, 0, 362884, 107787, 1077, 16384⟩
    (by decide) selected_cut_13914

theorem unmarked_context_12_26946_362885 : frontier 9 ⟨362885, by decide⟩
    (prefixCache 12 26946) (prefixPartial 12 26946) = false := by
  decide +kernel

theorem node_context_12_26946_362885 : EJMOriginalGlobalDAGData.nodes 9 ⟨362885, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨362859, by decide⟩,⟨362877, by decide⟩,⟨362884, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26946_362885 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26946 ⟨362885, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26946
    ⟨362885, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨362859, by decide⟩,⟨362877, by decide⟩,⟨362884, by decide⟩]) unmarked_context_12_26946_362885 node_context_12_26946_362885
  intro a
  fin_cases a
  · exact context_13_107784_3444
  · exact context_13_107785_362859
  · exact context_13_107786_362877
  · exact context_13_107787_362884

theorem selected_cut_13915 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 107788) = some ⟨13, 1, 0, 3444, 107788, 1, 16384⟩ := by
  decide +kernel

theorem context_13_107788_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107788 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 107788 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 107788, 1, 16384⟩
    (by decide) selected_cut_13915

theorem selected_cut_13916 : selected 8 ⟨362911, by decide⟩
    (prefixPartial 13 107789) = some ⟨13, 2, 0, 362911, 107789, 2713, 16384⟩ := by
  decide +kernel

theorem context_13_107789_362911 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107789 ⟨362911, by decide⟩ :=
  accepted_of_selected 13 107789 ⟨362911, by decide⟩ ⟨13, 2, 0, 362911, 107789, 2713, 16384⟩
    (by decide) selected_cut_13916

theorem selected_cut_13917 : selected 8 ⟨362930, by decide⟩
    (prefixPartial 13 107790) = some ⟨13, 2, 0, 362930, 107790, 2213, 16384⟩ := by
  decide +kernel

theorem context_13_107790_362930 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107790 ⟨362930, by decide⟩ :=
  accepted_of_selected 13 107790 ⟨362930, by decide⟩ ⟨13, 2, 0, 362930, 107790, 2213, 16384⟩
    (by decide) selected_cut_13917

theorem selected_cut_13918 : selected 8 ⟨362939, by decide⟩
    (prefixPartial 13 107791) = some ⟨13, 2, 0, 362939, 107791, 1025, 16384⟩ := by
  decide +kernel

theorem context_13_107791_362939 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107791 ⟨362939, by decide⟩ :=
  accepted_of_selected 13 107791 ⟨362939, by decide⟩ ⟨13, 2, 0, 362939, 107791, 1025, 16384⟩
    (by decide) selected_cut_13918

theorem unmarked_context_12_26947_362940 : frontier 9 ⟨362940, by decide⟩
    (prefixCache 12 26947) (prefixPartial 12 26947) = false := by
  decide +kernel

theorem node_context_12_26947_362940 : EJMOriginalGlobalDAGData.nodes 9 ⟨362940, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨362911, by decide⟩,⟨362930, by decide⟩,⟨362939, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26947_362940 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26947 ⟨362940, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26947
    ⟨362940, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨362911, by decide⟩,⟨362930, by decide⟩,⟨362939, by decide⟩]) unmarked_context_12_26947_362940 node_context_12_26947_362940
  intro a
  fin_cases a
  · exact context_13_107788_3444
  · exact context_13_107789_362911
  · exact context_13_107790_362930
  · exact context_13_107791_362939

theorem unmarked_context_11_6736_362941 : frontier 10 ⟨362941, by decide⟩
    (prefixCache 11 6736) (prefixPartial 11 6736) = false := by
  decide +kernel

theorem node_context_11_6736_362941 : EJMOriginalGlobalDAGData.nodes 10 ⟨362941, by decide⟩ =
    .split (coordinate 11) (![⟨362770, by decide⟩,⟨362833, by decide⟩,⟨362885, by decide⟩,⟨362940, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6736_362941 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6736 ⟨362941, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6736
    ⟨362941, by decide⟩ (by decide) (![⟨362770, by decide⟩,⟨362833, by decide⟩,⟨362885, by decide⟩,⟨362940, by decide⟩]) unmarked_context_11_6736_362941 node_context_11_6736_362941
  intro a
  fin_cases a
  · exact context_12_26944_362770
  · exact context_12_26945_362833
  · exact context_12_26946_362885
  · exact context_12_26947_362940

theorem selected_cut_13919 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 107792) = some ⟨13, 1, 0, 3444, 107792, 1, 16384⟩ := by
  decide +kernel

theorem context_13_107792_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107792 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 107792 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 107792, 1, 16384⟩
    (by decide) selected_cut_13919

theorem selected_cut_13920 : selected 8 ⟨362966, by decide⟩
    (prefixPartial 13 107793) = some ⟨13, 2, 0, 362966, 107793, 2169, 16384⟩ := by
  decide +kernel

theorem context_13_107793_362966 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107793 ⟨362966, by decide⟩ :=
  accepted_of_selected 13 107793 ⟨362966, by decide⟩ ⟨13, 2, 0, 362966, 107793, 2169, 16384⟩
    (by decide) selected_cut_13920

theorem selected_cut_13921 : selected 8 ⟨362984, by decide⟩
    (prefixPartial 13 107794) = some ⟨13, 2, 0, 362984, 107794, 1569, 16384⟩ := by
  decide +kernel

theorem context_13_107794_362984 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107794 ⟨362984, by decide⟩ :=
  accepted_of_selected 13 107794 ⟨362984, by decide⟩ ⟨13, 2, 0, 362984, 107794, 1569, 16384⟩
    (by decide) selected_cut_13921

theorem selected_cut_13922 : selected 8 ⟨362988, by decide⟩
    (prefixPartial 13 107795) = some ⟨13, 2, 0, 362988, 107795, 929, 16384⟩ := by
  decide +kernel

theorem context_13_107795_362988 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107795 ⟨362988, by decide⟩ :=
  accepted_of_selected 13 107795 ⟨362988, by decide⟩ ⟨13, 2, 0, 362988, 107795, 929, 16384⟩
    (by decide) selected_cut_13922

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
