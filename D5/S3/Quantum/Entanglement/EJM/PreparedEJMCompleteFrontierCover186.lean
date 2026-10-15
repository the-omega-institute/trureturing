/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover185
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_17858 : selected 8 ⟨456066, by decide⟩
    (prefixPartial 13 283736) = some ⟨13, 2, 0, 456066, 283736, 3905, 16384⟩ := by
  decide +kernel

theorem context_13_283736_456066 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 283736 ⟨456066, by decide⟩ :=
  accepted_of_selected 13 283736 ⟨456066, by decide⟩ ⟨13, 2, 0, 456066, 283736, 3905, 16384⟩
    (by decide) selected_cut_17858

theorem selected_cut_17859 : selected 8 ⟨456130, by decide⟩
    (prefixPartial 13 283737) = some ⟨13, 2, 0, 456130, 283737, 3089, 16384⟩ := by
  decide +kernel

theorem context_13_283737_456130 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 283737 ⟨456130, by decide⟩ :=
  accepted_of_selected 13 283737 ⟨456130, by decide⟩ ⟨13, 2, 0, 456130, 283737, 3089, 16384⟩
    (by decide) selected_cut_17859

theorem selected_cut_17860 : selected 8 ⟨456192, by decide⟩
    (prefixPartial 13 283738) = some ⟨13, 2, 0, 456192, 283738, 2545, 16384⟩ := by
  decide +kernel

theorem context_13_283738_456192 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 283738 ⟨456192, by decide⟩ :=
  accepted_of_selected 13 283738 ⟨456192, by decide⟩ ⟨13, 2, 0, 456192, 283738, 2545, 16384⟩
    (by decide) selected_cut_17860

theorem selected_cut_17861 : selected 8 ⟨456259, by decide⟩
    (prefixPartial 13 283739) = some ⟨13, 2, 0, 456259, 283739, 1529, 16384⟩ := by
  decide +kernel

theorem context_13_283739_456259 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 283739 ⟨456259, by decide⟩ :=
  accepted_of_selected 13 283739 ⟨456259, by decide⟩ ⟨13, 2, 0, 456259, 283739, 1529, 16384⟩
    (by decide) selected_cut_17861

theorem unmarked_context_12_70934_456260 : frontier 9 ⟨456260, by decide⟩
    (prefixCache 12 70934) (prefixPartial 12 70934) = false := by
  decide +kernel

theorem node_context_12_70934_456260 : EJMOriginalGlobalDAGData.nodes 9 ⟨456260, by decide⟩ =
    .split (coordinate 12) (![⟨456066, by decide⟩,⟨456130, by decide⟩,⟨456192, by decide⟩,⟨456259, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_70934_456260 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70934 ⟨456260, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 70934
    ⟨456260, by decide⟩ (by decide) (![⟨456066, by decide⟩,⟨456130, by decide⟩,⟨456192, by decide⟩,⟨456259, by decide⟩]) unmarked_context_12_70934_456260 node_context_12_70934_456260
  intro a
  fin_cases a
  · exact context_13_283736_456066
  · exact context_13_283737_456130
  · exact context_13_283738_456192
  · exact context_13_283739_456259

theorem selected_cut_17862 : selected 9 ⟨893, by decide⟩
    (prefixPartial 12 70935) = some ⟨12, 1, 0, 893, 70935, 1, 65536⟩ := by
  decide +kernel

theorem context_12_70935_893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70935 ⟨893, by decide⟩ :=
  accepted_of_selected 12 70935 ⟨893, by decide⟩ ⟨12, 1, 0, 893, 70935, 1, 65536⟩
    (by decide) selected_cut_17862

theorem unmarked_context_11_17733_456261 : frontier 10 ⟨456261, by decide⟩
    (prefixCache 11 17733) (prefixPartial 11 17733) = false := by
  decide +kernel

theorem node_context_11_17733_456261 : EJMOriginalGlobalDAGData.nodes 10 ⟨456261, by decide⟩ =
    .split (coordinate 11) (![⟨455938, by decide⟩,⟨455939, by decide⟩,⟨456260, by decide⟩,⟨893, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17733_456261 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17733 ⟨456261, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17733
    ⟨456261, by decide⟩ (by decide) (![⟨455938, by decide⟩,⟨455939, by decide⟩,⟨456260, by decide⟩,⟨893, by decide⟩]) unmarked_context_11_17733_456261 node_context_11_17733_456261
  intro a
  fin_cases a
  · exact context_12_70932_455938
  · exact context_12_70933_455939
  · exact context_12_70934_456260
  · exact context_12_70935_893

theorem selected_cut_17863 : selected 8 ⟨456326, by decide⟩
    (prefixPartial 13 283744) = some ⟨13, 2, 0, 456326, 283744, 2765, 16384⟩ := by
  decide +kernel

theorem context_13_283744_456326 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 283744 ⟨456326, by decide⟩ :=
  accepted_of_selected 13 283744 ⟨456326, by decide⟩ ⟨13, 2, 0, 456326, 283744, 2765, 16384⟩
    (by decide) selected_cut_17863

theorem selected_cut_17864 : selected 8 ⟨456385, by decide⟩
    (prefixPartial 13 283745) = some ⟨13, 2, 0, 456385, 283745, 3269, 16384⟩ := by
  decide +kernel

theorem context_13_283745_456385 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 283745 ⟨456385, by decide⟩ :=
  accepted_of_selected 13 283745 ⟨456385, by decide⟩ ⟨13, 2, 0, 456385, 283745, 3269, 16384⟩
    (by decide) selected_cut_17864

theorem selected_cut_17865 : selected 8 ⟨456466, by decide⟩
    (prefixPartial 13 283746) = some ⟨13, 2, 0, 456466, 283746, 2689, 16384⟩ := by
  decide +kernel

theorem context_13_283746_456466 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 283746 ⟨456466, by decide⟩ :=
  accepted_of_selected 13 283746 ⟨456466, by decide⟩ ⟨13, 2, 0, 456466, 283746, 2689, 16384⟩
    (by decide) selected_cut_17865

theorem selected_cut_17866 : selected 8 ⟨456520, by decide⟩
    (prefixPartial 13 283747) = some ⟨13, 2, 0, 456520, 283747, 1429, 16384⟩ := by
  decide +kernel

theorem context_13_283747_456520 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 283747 ⟨456520, by decide⟩ :=
  accepted_of_selected 13 283747 ⟨456520, by decide⟩ ⟨13, 2, 0, 456520, 283747, 1429, 16384⟩
    (by decide) selected_cut_17866

theorem unmarked_context_12_70936_456521 : frontier 9 ⟨456521, by decide⟩
    (prefixCache 12 70936) (prefixPartial 12 70936) = false := by
  decide +kernel

theorem node_context_12_70936_456521 : EJMOriginalGlobalDAGData.nodes 9 ⟨456521, by decide⟩ =
    .split (coordinate 12) (![⟨456326, by decide⟩,⟨456385, by decide⟩,⟨456466, by decide⟩,⟨456520, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_70936_456521 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70936 ⟨456521, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 70936
    ⟨456521, by decide⟩ (by decide) (![⟨456326, by decide⟩,⟨456385, by decide⟩,⟨456466, by decide⟩,⟨456520, by decide⟩]) unmarked_context_12_70936_456521 node_context_12_70936_456521
  intro a
  fin_cases a
  · exact context_13_283744_456326
  · exact context_13_283745_456385
  · exact context_13_283746_456466
  · exact context_13_283747_456520

theorem selected_cut_17867 : selected 8 ⟨456560, by decide⟩
    (prefixPartial 13 283748) = some ⟨13, 2, 0, 456560, 283748, 1701, 16384⟩ := by
  decide +kernel

theorem context_13_283748_456560 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 283748 ⟨456560, by decide⟩ :=
  accepted_of_selected 13 283748 ⟨456560, by decide⟩ ⟨13, 2, 0, 456560, 283748, 1701, 16384⟩
    (by decide) selected_cut_17867

theorem selected_cut_17868 : selected 8 ⟨456583, by decide⟩
    (prefixPartial 13 283749) = some ⟨13, 2, 0, 456583, 283749, 1793, 16384⟩ := by
  decide +kernel

theorem context_13_283749_456583 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 283749 ⟨456583, by decide⟩ :=
  accepted_of_selected 13 283749 ⟨456583, by decide⟩ ⟨13, 2, 0, 456583, 283749, 1793, 16384⟩
    (by decide) selected_cut_17868

theorem selected_cut_17869 : selected 8 ⟨456612, by decide⟩
    (prefixPartial 13 283750) = some ⟨13, 2, 0, 456612, 283750, 1773, 16384⟩ := by
  decide +kernel

theorem context_13_283750_456612 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 283750 ⟨456612, by decide⟩ :=
  accepted_of_selected 13 283750 ⟨456612, by decide⟩ ⟨13, 2, 0, 456612, 283750, 1773, 16384⟩
    (by decide) selected_cut_17869

theorem selected_cut_17870 : selected 8 ⟨456622, by decide⟩
    (prefixPartial 13 283751) = some ⟨13, 2, 0, 456622, 283751, 1021, 16384⟩ := by
  decide +kernel

theorem context_13_283751_456622 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 283751 ⟨456622, by decide⟩ :=
  accepted_of_selected 13 283751 ⟨456622, by decide⟩ ⟨13, 2, 0, 456622, 283751, 1021, 16384⟩
    (by decide) selected_cut_17870

theorem unmarked_context_12_70937_456623 : frontier 9 ⟨456623, by decide⟩
    (prefixCache 12 70937) (prefixPartial 12 70937) = false := by
  decide +kernel

theorem node_context_12_70937_456623 : EJMOriginalGlobalDAGData.nodes 9 ⟨456623, by decide⟩ =
    .split (coordinate 12) (![⟨456560, by decide⟩,⟨456583, by decide⟩,⟨456612, by decide⟩,⟨456622, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_70937_456623 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70937 ⟨456623, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 70937
    ⟨456623, by decide⟩ (by decide) (![⟨456560, by decide⟩,⟨456583, by decide⟩,⟨456612, by decide⟩,⟨456622, by decide⟩]) unmarked_context_12_70937_456623 node_context_12_70937_456623
  intro a
  fin_cases a
  · exact context_13_283748_456560
  · exact context_13_283749_456583
  · exact context_13_283750_456612
  · exact context_13_283751_456622

theorem selected_cut_17871 : selected 8 ⟨456675, by decide⟩
    (prefixPartial 13 283752) = some ⟨13, 2, 0, 456675, 283752, 2269, 16384⟩ := by
  decide +kernel

theorem context_13_283752_456675 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 283752 ⟨456675, by decide⟩ :=
  accepted_of_selected 13 283752 ⟨456675, by decide⟩ ⟨13, 2, 0, 456675, 283752, 2269, 16384⟩
    (by decide) selected_cut_17871

theorem selected_cut_17872 : selected 8 ⟨456706, by decide⟩
    (prefixPartial 13 283753) = some ⟨13, 2, 0, 456706, 283753, 2577, 16384⟩ := by
  decide +kernel

theorem context_13_283753_456706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 283753 ⟨456706, by decide⟩ :=
  accepted_of_selected 13 283753 ⟨456706, by decide⟩ ⟨13, 2, 0, 456706, 283753, 2577, 16384⟩
    (by decide) selected_cut_17872

theorem selected_cut_17873 : selected 8 ⟨456732, by decide⟩
    (prefixPartial 13 283754) = some ⟨13, 2, 0, 456732, 283754, 2061, 16384⟩ := by
  decide +kernel

theorem context_13_283754_456732 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 283754 ⟨456732, by decide⟩ :=
  accepted_of_selected 13 283754 ⟨456732, by decide⟩ ⟨13, 2, 0, 456732, 283754, 2061, 16384⟩
    (by decide) selected_cut_17873

theorem selected_cut_17874 : selected 8 ⟨456756, by decide⟩
    (prefixPartial 13 283755) = some ⟨13, 2, 0, 456756, 283755, 1201, 16384⟩ := by
  decide +kernel

theorem context_13_283755_456756 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 283755 ⟨456756, by decide⟩ :=
  accepted_of_selected 13 283755 ⟨456756, by decide⟩ ⟨13, 2, 0, 456756, 283755, 1201, 16384⟩
    (by decide) selected_cut_17874

theorem unmarked_context_12_70938_456757 : frontier 9 ⟨456757, by decide⟩
    (prefixCache 12 70938) (prefixPartial 12 70938) = false := by
  decide +kernel

theorem node_context_12_70938_456757 : EJMOriginalGlobalDAGData.nodes 9 ⟨456757, by decide⟩ =
    .split (coordinate 12) (![⟨456675, by decide⟩,⟨456706, by decide⟩,⟨456732, by decide⟩,⟨456756, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_70938_456757 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70938 ⟨456757, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 70938
    ⟨456757, by decide⟩ (by decide) (![⟨456675, by decide⟩,⟨456706, by decide⟩,⟨456732, by decide⟩,⟨456756, by decide⟩]) unmarked_context_12_70938_456757 node_context_12_70938_456757
  intro a
  fin_cases a
  · exact context_13_283752_456675
  · exact context_13_283753_456706
  · exact context_13_283754_456732
  · exact context_13_283755_456756

theorem selected_cut_17875 : selected 8 ⟨456811, by decide⟩
    (prefixPartial 13 283756) = some ⟨13, 2, 0, 456811, 283756, 2129, 16384⟩ := by
  decide +kernel

theorem context_13_283756_456811 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 283756 ⟨456811, by decide⟩ :=
  accepted_of_selected 13 283756 ⟨456811, by decide⟩ ⟨13, 2, 0, 456811, 283756, 2129, 16384⟩
    (by decide) selected_cut_17875

theorem selected_cut_17876 : selected 8 ⟨456846, by decide⟩
    (prefixPartial 13 283757) = some ⟨13, 2, 0, 456846, 283757, 2637, 16384⟩ := by
  decide +kernel

theorem context_13_283757_456846 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 283757 ⟨456846, by decide⟩ :=
  accepted_of_selected 13 283757 ⟨456846, by decide⟩ ⟨13, 2, 0, 456846, 283757, 2637, 16384⟩
    (by decide) selected_cut_17876

theorem selected_cut_17877 : selected 8 ⟨456893, by decide⟩
    (prefixPartial 13 283758) = some ⟨13, 2, 0, 456893, 283758, 2149, 16384⟩ := by
  decide +kernel

theorem context_13_283758_456893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 283758 ⟨456893, by decide⟩ :=
  accepted_of_selected 13 283758 ⟨456893, by decide⟩ ⟨13, 2, 0, 456893, 283758, 2149, 16384⟩
    (by decide) selected_cut_17877

theorem selected_cut_17878 : selected 8 ⟨456923, by decide⟩
    (prefixPartial 13 283759) = some ⟨13, 2, 0, 456923, 283759, 1053, 16384⟩ := by
  decide +kernel

theorem context_13_283759_456923 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 283759 ⟨456923, by decide⟩ :=
  accepted_of_selected 13 283759 ⟨456923, by decide⟩ ⟨13, 2, 0, 456923, 283759, 1053, 16384⟩
    (by decide) selected_cut_17878

theorem unmarked_context_12_70939_456924 : frontier 9 ⟨456924, by decide⟩
    (prefixCache 12 70939) (prefixPartial 12 70939) = false := by
  decide +kernel

theorem node_context_12_70939_456924 : EJMOriginalGlobalDAGData.nodes 9 ⟨456924, by decide⟩ =
    .split (coordinate 12) (![⟨456811, by decide⟩,⟨456846, by decide⟩,⟨456893, by decide⟩,⟨456923, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_70939_456924 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70939 ⟨456924, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 70939
    ⟨456924, by decide⟩ (by decide) (![⟨456811, by decide⟩,⟨456846, by decide⟩,⟨456893, by decide⟩,⟨456923, by decide⟩]) unmarked_context_12_70939_456924 node_context_12_70939_456924
  intro a
  fin_cases a
  · exact context_13_283756_456811
  · exact context_13_283757_456846
  · exact context_13_283758_456893
  · exact context_13_283759_456923

theorem unmarked_context_11_17734_456925 : frontier 10 ⟨456925, by decide⟩
    (prefixCache 11 17734) (prefixPartial 11 17734) = false := by
  decide +kernel

theorem node_context_11_17734_456925 : EJMOriginalGlobalDAGData.nodes 10 ⟨456925, by decide⟩ =
    .split (coordinate 11) (![⟨456521, by decide⟩,⟨456623, by decide⟩,⟨456757, by decide⟩,⟨456924, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17734_456925 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17734 ⟨456925, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17734
    ⟨456925, by decide⟩ (by decide) (![⟨456521, by decide⟩,⟨456623, by decide⟩,⟨456757, by decide⟩,⟨456924, by decide⟩]) unmarked_context_11_17734_456925 node_context_11_17734_456925
  intro a
  fin_cases a
  · exact context_12_70936_456521
  · exact context_12_70937_456623
  · exact context_12_70938_456757
  · exact context_12_70939_456924

theorem selected_cut_17879 : selected 10 ⟨1736, by decide⟩
    (prefixPartial 11 17735) = some ⟨11, 1, 0, 1736, 17735, 1, 262144⟩ := by
  decide +kernel

theorem context_11_17735_1736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17735 ⟨1736, by decide⟩ :=
  accepted_of_selected 11 17735 ⟨1736, by decide⟩ ⟨11, 1, 0, 1736, 17735, 1, 262144⟩
    (by decide) selected_cut_17879

theorem unmarked_context_10_4433_456926 : frontier 11 ⟨456926, by decide⟩
    (prefixCache 10 4433) (prefixPartial 10 4433) = false := by
  decide +kernel

theorem node_context_10_4433_456926 : EJMOriginalGlobalDAGData.nodes 11 ⟨456926, by decide⟩ =
    .split (coordinate 10) (![⟨455736, by decide⟩,⟨456261, by decide⟩,⟨456925, by decide⟩,⟨1736, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4433_456926 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4433 ⟨456926, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4433
    ⟨456926, by decide⟩ (by decide) (![⟨455736, by decide⟩,⟨456261, by decide⟩,⟨456925, by decide⟩,⟨1736, by decide⟩]) unmarked_context_10_4433_456926 node_context_10_4433_456926
  intro a
  fin_cases a
  · exact context_11_17732_455736
  · exact context_11_17733_456261
  · exact context_11_17734_456925
  · exact context_11_17735_1736

theorem selected_cut_17880 : selected 9 ⟨435790, by decide⟩
    (prefixPartial 12 70944) = some ⟨12, 1, 0, 435790, 70944, 1, 65536⟩ := by
  decide +kernel

theorem context_12_70944_435790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70944 ⟨435790, by decide⟩ :=
  accepted_of_selected 12 70944 ⟨435790, by decide⟩ ⟨12, 1, 0, 435790, 70944, 1, 65536⟩
    (by decide) selected_cut_17880

theorem selected_cut_17881 : selected 8 ⟨456968, by decide⟩
    (prefixPartial 13 283780) = some ⟨13, 2, 0, 456968, 283780, 1505, 16384⟩ := by
  decide +kernel

theorem context_13_283780_456968 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 283780 ⟨456968, by decide⟩ :=
  accepted_of_selected 13 283780 ⟨456968, by decide⟩ ⟨13, 2, 0, 456968, 283780, 1505, 16384⟩
    (by decide) selected_cut_17881

theorem selected_cut_17882 : selected 8 ⟨457015, by decide⟩
    (prefixPartial 13 283781) = some ⟨13, 2, 0, 457015, 283781, 2081, 16384⟩ := by
  decide +kernel

theorem context_13_283781_457015 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 283781 ⟨457015, by decide⟩ :=
  accepted_of_selected 13 283781 ⟨457015, by decide⟩ ⟨13, 2, 0, 457015, 283781, 2081, 16384⟩
    (by decide) selected_cut_17882

theorem selected_cut_17883 : selected 8 ⟨457050, by decide⟩
    (prefixPartial 13 283782) = some ⟨13, 2, 0, 457050, 283782, 1645, 16384⟩ := by
  decide +kernel

theorem context_13_283782_457050 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 283782 ⟨457050, by decide⟩ :=
  accepted_of_selected 13 283782 ⟨457050, by decide⟩ ⟨13, 2, 0, 457050, 283782, 1645, 16384⟩
    (by decide) selected_cut_17883

theorem selected_cut_17884 : selected 8 ⟨457066, by decide⟩
    (prefixPartial 13 283783) = some ⟨13, 2, 0, 457066, 283783, 861, 16384⟩ := by
  decide +kernel

theorem context_13_283783_457066 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 283783 ⟨457066, by decide⟩ :=
  accepted_of_selected 13 283783 ⟨457066, by decide⟩ ⟨13, 2, 0, 457066, 283783, 861, 16384⟩
    (by decide) selected_cut_17884

theorem unmarked_context_12_70945_457067 : frontier 9 ⟨457067, by decide⟩
    (prefixCache 12 70945) (prefixPartial 12 70945) = false := by
  decide +kernel

theorem node_context_12_70945_457067 : EJMOriginalGlobalDAGData.nodes 9 ⟨457067, by decide⟩ =
    .split (coordinate 12) (![⟨456968, by decide⟩,⟨457015, by decide⟩,⟨457050, by decide⟩,⟨457066, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_70945_457067 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70945 ⟨457067, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 70945
    ⟨457067, by decide⟩ (by decide) (![⟨456968, by decide⟩,⟨457015, by decide⟩,⟨457050, by decide⟩,⟨457066, by decide⟩]) unmarked_context_12_70945_457067 node_context_12_70945_457067
  intro a
  fin_cases a
  · exact context_13_283780_456968
  · exact context_13_283781_457015
  · exact context_13_283782_457050
  · exact context_13_283783_457066

theorem selected_cut_17885 : selected 8 ⟨457112, by decide⟩
    (prefixPartial 13 283784) = some ⟨13, 2, 0, 457112, 283784, 1821, 16384⟩ := by
  decide +kernel

theorem context_13_283784_457112 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 283784 ⟨457112, by decide⟩ :=
  accepted_of_selected 13 283784 ⟨457112, by decide⟩ ⟨13, 2, 0, 457112, 283784, 1821, 16384⟩
    (by decide) selected_cut_17885

theorem selected_cut_17886 : selected 8 ⟨457175, by decide⟩
    (prefixPartial 13 283785) = some ⟨13, 2, 0, 457175, 283785, 2597, 16384⟩ := by
  decide +kernel

theorem context_13_283785_457175 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 283785 ⟨457175, by decide⟩ :=
  accepted_of_selected 13 283785 ⟨457175, by decide⟩ ⟨13, 2, 0, 457175, 283785, 2597, 16384⟩
    (by decide) selected_cut_17886

theorem selected_cut_17887 : selected 8 ⟨457214, by decide⟩
    (prefixPartial 13 283786) = some ⟨13, 2, 0, 457214, 283786, 1857, 16384⟩ := by
  decide +kernel

theorem context_13_283786_457214 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 283786 ⟨457214, by decide⟩ :=
  accepted_of_selected 13 283786 ⟨457214, by decide⟩ ⟨13, 2, 0, 457214, 283786, 1857, 16384⟩
    (by decide) selected_cut_17887

theorem selected_cut_17888 : selected 8 ⟨457241, by decide⟩
    (prefixPartial 13 283787) = some ⟨13, 2, 0, 457241, 283787, 1033, 16384⟩ := by
  decide +kernel

theorem context_13_283787_457241 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 283787 ⟨457241, by decide⟩ :=
  accepted_of_selected 13 283787 ⟨457241, by decide⟩ ⟨13, 2, 0, 457241, 283787, 1033, 16384⟩
    (by decide) selected_cut_17888

theorem unmarked_context_12_70946_457242 : frontier 9 ⟨457242, by decide⟩
    (prefixCache 12 70946) (prefixPartial 12 70946) = false := by
  decide +kernel

theorem node_context_12_70946_457242 : EJMOriginalGlobalDAGData.nodes 9 ⟨457242, by decide⟩ =
    .split (coordinate 12) (![⟨457112, by decide⟩,⟨457175, by decide⟩,⟨457214, by decide⟩,⟨457241, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_70946_457242 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70946 ⟨457242, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 70946
    ⟨457242, by decide⟩ (by decide) (![⟨457112, by decide⟩,⟨457175, by decide⟩,⟨457214, by decide⟩,⟨457241, by decide⟩]) unmarked_context_12_70946_457242 node_context_12_70946_457242
  intro a
  fin_cases a
  · exact context_13_283784_457112
  · exact context_13_283785_457175
  · exact context_13_283786_457214
  · exact context_13_283787_457241

theorem selected_cut_17889 : selected 8 ⟨457281, by decide⟩
    (prefixPartial 13 283788) = some ⟨13, 2, 0, 457281, 283788, 1769, 16384⟩ := by
  decide +kernel

theorem context_13_283788_457281 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 283788 ⟨457281, by decide⟩ :=
  accepted_of_selected 13 283788 ⟨457281, by decide⟩ ⟨13, 2, 0, 457281, 283788, 1769, 16384⟩
    (by decide) selected_cut_17889

theorem selected_cut_17890 : selected 8 ⟨457323, by decide⟩
    (prefixPartial 13 283789) = some ⟨13, 2, 0, 457323, 283789, 2445, 16384⟩ := by
  decide +kernel

theorem context_13_283789_457323 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 283789 ⟨457323, by decide⟩ :=
  accepted_of_selected 13 283789 ⟨457323, by decide⟩ ⟨13, 2, 0, 457323, 283789, 2445, 16384⟩
    (by decide) selected_cut_17890

theorem selected_cut_17891 : selected 8 ⟨457369, by decide⟩
    (prefixPartial 13 283790) = some ⟨13, 2, 0, 457369, 283790, 2077, 16384⟩ := by
  decide +kernel

theorem context_13_283790_457369 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 283790 ⟨457369, by decide⟩ :=
  accepted_of_selected 13 283790 ⟨457369, by decide⟩ ⟨13, 2, 0, 457369, 283790, 2077, 16384⟩
    (by decide) selected_cut_17891

theorem selected_cut_17892 : selected 8 ⟨457387, by decide⟩
    (prefixPartial 13 283791) = some ⟨13, 2, 0, 457387, 283791, 981, 16384⟩ := by
  decide +kernel

theorem context_13_283791_457387 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 283791 ⟨457387, by decide⟩ :=
  accepted_of_selected 13 283791 ⟨457387, by decide⟩ ⟨13, 2, 0, 457387, 283791, 981, 16384⟩
    (by decide) selected_cut_17892

theorem unmarked_context_12_70947_457388 : frontier 9 ⟨457388, by decide⟩
    (prefixCache 12 70947) (prefixPartial 12 70947) = false := by
  decide +kernel

theorem node_context_12_70947_457388 : EJMOriginalGlobalDAGData.nodes 9 ⟨457388, by decide⟩ =
    .split (coordinate 12) (![⟨457281, by decide⟩,⟨457323, by decide⟩,⟨457369, by decide⟩,⟨457387, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_70947_457388 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70947 ⟨457388, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 70947
    ⟨457388, by decide⟩ (by decide) (![⟨457281, by decide⟩,⟨457323, by decide⟩,⟨457369, by decide⟩,⟨457387, by decide⟩]) unmarked_context_12_70947_457388 node_context_12_70947_457388
  intro a
  fin_cases a
  · exact context_13_283788_457281
  · exact context_13_283789_457323
  · exact context_13_283790_457369
  · exact context_13_283791_457387

theorem unmarked_context_11_17736_457389 : frontier 10 ⟨457389, by decide⟩
    (prefixCache 11 17736) (prefixPartial 11 17736) = false := by
  decide +kernel

theorem node_context_11_17736_457389 : EJMOriginalGlobalDAGData.nodes 10 ⟨457389, by decide⟩ =
    .split (coordinate 11) (![⟨435790, by decide⟩,⟨457067, by decide⟩,⟨457242, by decide⟩,⟨457388, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17736_457389 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17736 ⟨457389, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17736
    ⟨457389, by decide⟩ (by decide) (![⟨435790, by decide⟩,⟨457067, by decide⟩,⟨457242, by decide⟩,⟨457388, by decide⟩]) unmarked_context_11_17736_457389 node_context_11_17736_457389
  intro a
  fin_cases a
  · exact context_12_70944_435790
  · exact context_12_70945_457067
  · exact context_12_70946_457242
  · exact context_12_70947_457388

theorem selected_cut_17893 : selected 9 ⟨455939, by decide⟩
    (prefixPartial 12 70948) = some ⟨12, 1, 0, 455939, 70948, 1, 65536⟩ := by
  decide +kernel

theorem context_12_70948_455939 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70948 ⟨455939, by decide⟩ :=
  accepted_of_selected 12 70948 ⟨455939, by decide⟩ ⟨12, 1, 0, 455939, 70948, 1, 65536⟩
    (by decide) selected_cut_17893

theorem selected_cut_17894 : selected 9 ⟨455939, by decide⟩
    (prefixPartial 12 70949) = some ⟨12, 1, 0, 455939, 70949, 1, 65536⟩ := by
  decide +kernel

theorem context_12_70949_455939 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70949 ⟨455939, by decide⟩ :=
  accepted_of_selected 12 70949 ⟨455939, by decide⟩ ⟨12, 1, 0, 455939, 70949, 1, 65536⟩
    (by decide) selected_cut_17894

theorem selected_cut_17895 : selected 8 ⟨457461, by decide⟩
    (prefixPartial 13 283800) = some ⟨13, 2, 0, 457461, 283800, 1469, 16384⟩ := by
  decide +kernel

theorem context_13_283800_457461 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 283800 ⟨457461, by decide⟩ :=
  accepted_of_selected 13 283800 ⟨457461, by decide⟩ ⟨13, 2, 0, 457461, 283800, 1469, 16384⟩
    (by decide) selected_cut_17895

theorem selected_cut_17896 : selected 8 ⟨457534, by decide⟩
    (prefixPartial 13 283801) = some ⟨13, 2, 0, 457534, 283801, 1681, 16384⟩ := by
  decide +kernel

theorem context_13_283801_457534 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 283801 ⟨457534, by decide⟩ :=
  accepted_of_selected 13 283801 ⟨457534, by decide⟩ ⟨13, 2, 0, 457534, 283801, 1681, 16384⟩
    (by decide) selected_cut_17896

theorem selected_cut_17897 : selected 8 ⟨457579, by decide⟩
    (prefixPartial 13 283802) = some ⟨13, 2, 0, 457579, 283802, 761, 16384⟩ := by
  decide +kernel

theorem context_13_283802_457579 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 283802 ⟨457579, by decide⟩ :=
  accepted_of_selected 13 283802 ⟨457579, by decide⟩ ⟨13, 2, 0, 457579, 283802, 761, 16384⟩
    (by decide) selected_cut_17897

theorem selected_cut_17898 : selected 8 ⟨457606, by decide⟩
    (prefixPartial 13 283803) = some ⟨13, 2, 0, 457606, 283803, 241, 16384⟩ := by
  decide +kernel

theorem context_13_283803_457606 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 283803 ⟨457606, by decide⟩ :=
  accepted_of_selected 13 283803 ⟨457606, by decide⟩ ⟨13, 2, 0, 457606, 283803, 241, 16384⟩
    (by decide) selected_cut_17898

theorem unmarked_context_12_70950_457607 : frontier 9 ⟨457607, by decide⟩
    (prefixCache 12 70950) (prefixPartial 12 70950) = false := by
  decide +kernel

theorem node_context_12_70950_457607 : EJMOriginalGlobalDAGData.nodes 9 ⟨457607, by decide⟩ =
    .split (coordinate 12) (![⟨457461, by decide⟩,⟨457534, by decide⟩,⟨457579, by decide⟩,⟨457606, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_70950_457607 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70950 ⟨457607, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 70950
    ⟨457607, by decide⟩ (by decide) (![⟨457461, by decide⟩,⟨457534, by decide⟩,⟨457579, by decide⟩,⟨457606, by decide⟩]) unmarked_context_12_70950_457607 node_context_12_70950_457607
  intro a
  fin_cases a
  · exact context_13_283800_457461
  · exact context_13_283801_457534
  · exact context_13_283802_457579
  · exact context_13_283803_457606

theorem selected_cut_17899 : selected 8 ⟨457674, by decide⟩
    (prefixPartial 13 283804) = some ⟨13, 2, 0, 457674, 283804, 1489, 16384⟩ := by
  decide +kernel

theorem context_13_283804_457674 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 283804 ⟨457674, by decide⟩ :=
  accepted_of_selected 13 283804 ⟨457674, by decide⟩ ⟨13, 2, 0, 457674, 283804, 1489, 16384⟩
    (by decide) selected_cut_17899

theorem selected_cut_17900 : selected 8 ⟨457745, by decide⟩
    (prefixPartial 13 283805) = some ⟨13, 2, 0, 457745, 283805, 1693, 16384⟩ := by
  decide +kernel

theorem context_13_283805_457745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 283805 ⟨457745, by decide⟩ :=
  accepted_of_selected 13 283805 ⟨457745, by decide⟩ ⟨13, 2, 0, 457745, 283805, 1693, 16384⟩
    (by decide) selected_cut_17900

theorem selected_cut_17901 : selected 8 ⟨457801, by decide⟩
    (prefixPartial 13 283806) = some ⟨13, 2, 0, 457801, 283806, 857, 16384⟩ := by
  decide +kernel

theorem context_13_283806_457801 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 283806 ⟨457801, by decide⟩ :=
  accepted_of_selected 13 283806 ⟨457801, by decide⟩ ⟨13, 2, 0, 457801, 283806, 857, 16384⟩
    (by decide) selected_cut_17901

theorem selected_cut_17902 : selected 8 ⟨457827, by decide⟩
    (prefixPartial 13 283807) = some ⟨13, 2, 0, 457827, 283807, 181, 16384⟩ := by
  decide +kernel

theorem context_13_283807_457827 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 283807 ⟨457827, by decide⟩ :=
  accepted_of_selected 13 283807 ⟨457827, by decide⟩ ⟨13, 2, 0, 457827, 283807, 181, 16384⟩
    (by decide) selected_cut_17902

theorem unmarked_context_12_70951_457828 : frontier 9 ⟨457828, by decide⟩
    (prefixCache 12 70951) (prefixPartial 12 70951) = false := by
  decide +kernel

theorem node_context_12_70951_457828 : EJMOriginalGlobalDAGData.nodes 9 ⟨457828, by decide⟩ =
    .split (coordinate 12) (![⟨457674, by decide⟩,⟨457745, by decide⟩,⟨457801, by decide⟩,⟨457827, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_70951_457828 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70951 ⟨457828, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 70951
    ⟨457828, by decide⟩ (by decide) (![⟨457674, by decide⟩,⟨457745, by decide⟩,⟨457801, by decide⟩,⟨457827, by decide⟩]) unmarked_context_12_70951_457828 node_context_12_70951_457828
  intro a
  fin_cases a
  · exact context_13_283804_457674
  · exact context_13_283805_457745
  · exact context_13_283806_457801
  · exact context_13_283807_457827

theorem unmarked_context_11_17737_457829 : frontier 10 ⟨457829, by decide⟩
    (prefixCache 11 17737) (prefixPartial 11 17737) = false := by
  decide +kernel

theorem node_context_11_17737_457829 : EJMOriginalGlobalDAGData.nodes 10 ⟨457829, by decide⟩ =
    .split (coordinate 11) (![⟨455939, by decide⟩,⟨455939, by decide⟩,⟨457607, by decide⟩,⟨457828, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17737_457829 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17737 ⟨457829, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17737
    ⟨457829, by decide⟩ (by decide) (![⟨455939, by decide⟩,⟨455939, by decide⟩,⟨457607, by decide⟩,⟨457828, by decide⟩]) unmarked_context_11_17737_457829 node_context_11_17737_457829
  intro a
  fin_cases a
  · exact context_12_70948_455939
  · exact context_12_70949_455939
  · exact context_12_70950_457607
  · exact context_12_70951_457828

theorem selected_cut_17903 : selected 8 ⟨457874, by decide⟩
    (prefixPartial 13 283808) = some ⟨13, 2, 0, 457874, 283808, 1377, 16384⟩ := by
  decide +kernel

theorem context_13_283808_457874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 283808 ⟨457874, by decide⟩ :=
  accepted_of_selected 13 283808 ⟨457874, by decide⟩ ⟨13, 2, 0, 457874, 283808, 1377, 16384⟩
    (by decide) selected_cut_17903

theorem selected_cut_17904 : selected 8 ⟨457952, by decide⟩
    (prefixPartial 13 283809) = some ⟨13, 2, 0, 457952, 283809, 3117, 16384⟩ := by
  decide +kernel

theorem context_13_283809_457952 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 283809 ⟨457952, by decide⟩ :=
  accepted_of_selected 13 283809 ⟨457952, by decide⟩ ⟨13, 2, 0, 457952, 283809, 3117, 16384⟩
    (by decide) selected_cut_17904

theorem selected_cut_17905 : selected 8 ⟨458035, by decide⟩
    (prefixPartial 13 283810) = some ⟨13, 2, 0, 458035, 283810, 2557, 16384⟩ := by
  decide +kernel

theorem context_13_283810_458035 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 283810 ⟨458035, by decide⟩ :=
  accepted_of_selected 13 283810 ⟨458035, by decide⟩ ⟨13, 2, 0, 458035, 283810, 2557, 16384⟩
    (by decide) selected_cut_17905

theorem selected_cut_17906 : selected 8 ⟨458093, by decide⟩
    (prefixPartial 13 283811) = some ⟨13, 2, 0, 458093, 283811, 1437, 16384⟩ := by
  decide +kernel

theorem context_13_283811_458093 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 283811 ⟨458093, by decide⟩ :=
  accepted_of_selected 13 283811 ⟨458093, by decide⟩ ⟨13, 2, 0, 458093, 283811, 1437, 16384⟩
    (by decide) selected_cut_17906

theorem unmarked_context_12_70952_458094 : frontier 9 ⟨458094, by decide⟩
    (prefixCache 12 70952) (prefixPartial 12 70952) = false := by
  decide +kernel

theorem node_context_12_70952_458094 : EJMOriginalGlobalDAGData.nodes 9 ⟨458094, by decide⟩ =
    .split (coordinate 12) (![⟨457874, by decide⟩,⟨457952, by decide⟩,⟨458035, by decide⟩,⟨458093, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_70952_458094 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70952 ⟨458094, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 70952
    ⟨458094, by decide⟩ (by decide) (![⟨457874, by decide⟩,⟨457952, by decide⟩,⟨458035, by decide⟩,⟨458093, by decide⟩]) unmarked_context_12_70952_458094 node_context_12_70952_458094
  intro a
  fin_cases a
  · exact context_13_283808_457874
  · exact context_13_283809_457952
  · exact context_13_283810_458035
  · exact context_13_283811_458093

theorem selected_cut_17907 : selected 8 ⟨458122, by decide⟩
    (prefixPartial 13 283812) = some ⟨13, 2, 0, 458122, 283812, 841, 16384⟩ := by
  decide +kernel

theorem context_13_283812_458122 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 283812 ⟨458122, by decide⟩ :=
  accepted_of_selected 13 283812 ⟨458122, by decide⟩ ⟨13, 2, 0, 458122, 283812, 841, 16384⟩
    (by decide) selected_cut_17907

theorem selected_cut_17908 : selected 8 ⟨458153, by decide⟩
    (prefixPartial 13 283813) = some ⟨13, 2, 0, 458153, 283813, 1889, 16384⟩ := by
  decide +kernel

theorem context_13_283813_458153 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 283813 ⟨458153, by decide⟩ :=
  accepted_of_selected 13 283813 ⟨458153, by decide⟩ ⟨13, 2, 0, 458153, 283813, 1889, 16384⟩
    (by decide) selected_cut_17908

theorem selected_cut_17909 : selected 8 ⟨458185, by decide⟩
    (prefixPartial 13 283814) = some ⟨13, 2, 0, 458185, 283814, 1625, 16384⟩ := by
  decide +kernel

theorem context_13_283814_458185 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 283814 ⟨458185, by decide⟩ :=
  accepted_of_selected 13 283814 ⟨458185, by decide⟩ ⟨13, 2, 0, 458185, 283814, 1625, 16384⟩
    (by decide) selected_cut_17909

theorem selected_cut_17910 : selected 8 ⟨458206, by decide⟩
    (prefixPartial 13 283815) = some ⟨13, 2, 0, 458206, 283815, 969, 16384⟩ := by
  decide +kernel

theorem context_13_283815_458206 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 283815 ⟨458206, by decide⟩ :=
  accepted_of_selected 13 283815 ⟨458206, by decide⟩ ⟨13, 2, 0, 458206, 283815, 969, 16384⟩
    (by decide) selected_cut_17910

theorem unmarked_context_12_70953_458207 : frontier 9 ⟨458207, by decide⟩
    (prefixCache 12 70953) (prefixPartial 12 70953) = false := by
  decide +kernel

theorem node_context_12_70953_458207 : EJMOriginalGlobalDAGData.nodes 9 ⟨458207, by decide⟩ =
    .split (coordinate 12) (![⟨458122, by decide⟩,⟨458153, by decide⟩,⟨458185, by decide⟩,⟨458206, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_70953_458207 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70953 ⟨458207, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 70953
    ⟨458207, by decide⟩ (by decide) (![⟨458122, by decide⟩,⟨458153, by decide⟩,⟨458185, by decide⟩,⟨458206, by decide⟩]) unmarked_context_12_70953_458207 node_context_12_70953_458207
  intro a
  fin_cases a
  · exact context_13_283812_458122
  · exact context_13_283813_458153
  · exact context_13_283814_458185
  · exact context_13_283815_458206

theorem selected_cut_17911 : selected 8 ⟨458238, by decide⟩
    (prefixPartial 13 283816) = some ⟨13, 2, 0, 458238, 283816, 901, 16384⟩ := by
  decide +kernel

theorem context_13_283816_458238 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 283816 ⟨458238, by decide⟩ :=
  accepted_of_selected 13 283816 ⟨458238, by decide⟩ ⟨13, 2, 0, 458238, 283816, 901, 16384⟩
    (by decide) selected_cut_17911

theorem selected_cut_17912 : selected 8 ⟨458281, by decide⟩
    (prefixPartial 13 283817) = some ⟨13, 2, 0, 458281, 283817, 2397, 16384⟩ := by
  decide +kernel

theorem context_13_283817_458281 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 283817 ⟨458281, by decide⟩ :=
  accepted_of_selected 13 283817 ⟨458281, by decide⟩ ⟨13, 2, 0, 458281, 283817, 2397, 16384⟩
    (by decide) selected_cut_17912

theorem selected_cut_17913 : selected 8 ⟨458306, by decide⟩
    (prefixPartial 13 283818) = some ⟨13, 2, 0, 458306, 283818, 1577, 16384⟩ := by
  decide +kernel

theorem context_13_283818_458306 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 283818 ⟨458306, by decide⟩ :=
  accepted_of_selected 13 283818 ⟨458306, by decide⟩ ⟨13, 2, 0, 458306, 283818, 1577, 16384⟩
    (by decide) selected_cut_17913

theorem selected_cut_17914 : selected 8 ⟨458331, by decide⟩
    (prefixPartial 13 283819) = some ⟨13, 2, 0, 458331, 283819, 1073, 16384⟩ := by
  decide +kernel

theorem context_13_283819_458331 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 283819 ⟨458331, by decide⟩ :=
  accepted_of_selected 13 283819 ⟨458331, by decide⟩ ⟨13, 2, 0, 458331, 283819, 1073, 16384⟩
    (by decide) selected_cut_17914

theorem unmarked_context_12_70954_458332 : frontier 9 ⟨458332, by decide⟩
    (prefixCache 12 70954) (prefixPartial 12 70954) = false := by
  decide +kernel

theorem node_context_12_70954_458332 : EJMOriginalGlobalDAGData.nodes 9 ⟨458332, by decide⟩ =
    .split (coordinate 12) (![⟨458238, by decide⟩,⟨458281, by decide⟩,⟨458306, by decide⟩,⟨458331, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_70954_458332 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70954 ⟨458332, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 70954
    ⟨458332, by decide⟩ (by decide) (![⟨458238, by decide⟩,⟨458281, by decide⟩,⟨458306, by decide⟩,⟨458331, by decide⟩]) unmarked_context_12_70954_458332 node_context_12_70954_458332
  intro a
  fin_cases a
  · exact context_13_283816_458238
  · exact context_13_283817_458281
  · exact context_13_283818_458306
  · exact context_13_283819_458331

theorem selected_cut_17915 : selected 8 ⟨458354, by decide⟩
    (prefixPartial 13 283820) = some ⟨13, 2, 0, 458354, 283820, 805, 16384⟩ := by
  decide +kernel

theorem context_13_283820_458354 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 283820 ⟨458354, by decide⟩ :=
  accepted_of_selected 13 283820 ⟨458354, by decide⟩ ⟨13, 2, 0, 458354, 283820, 805, 16384⟩
    (by decide) selected_cut_17915

theorem selected_cut_17916 : selected 8 ⟨458397, by decide⟩
    (prefixPartial 13 283821) = some ⟨13, 2, 0, 458397, 283821, 2285, 16384⟩ := by
  decide +kernel

theorem context_13_283821_458397 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 283821 ⟨458397, by decide⟩ :=
  accepted_of_selected 13 283821 ⟨458397, by decide⟩ ⟨13, 2, 0, 458397, 283821, 2285, 16384⟩
    (by decide) selected_cut_17916

theorem selected_cut_17917 : selected 8 ⟨458428, by decide⟩
    (prefixPartial 13 283822) = some ⟨13, 2, 0, 458428, 283822, 1785, 16384⟩ := by
  decide +kernel

theorem context_13_283822_458428 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 283822 ⟨458428, by decide⟩ :=
  accepted_of_selected 13 283822 ⟨458428, by decide⟩ ⟨13, 2, 0, 458428, 283822, 1785, 16384⟩
    (by decide) selected_cut_17917

theorem selected_cut_17918 : selected 8 ⟨458449, by decide⟩
    (prefixPartial 13 283823) = some ⟨13, 2, 0, 458449, 283823, 993, 16384⟩ := by
  decide +kernel

theorem context_13_283823_458449 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 283823 ⟨458449, by decide⟩ :=
  accepted_of_selected 13 283823 ⟨458449, by decide⟩ ⟨13, 2, 0, 458449, 283823, 993, 16384⟩
    (by decide) selected_cut_17918

theorem unmarked_context_12_70955_458450 : frontier 9 ⟨458450, by decide⟩
    (prefixCache 12 70955) (prefixPartial 12 70955) = false := by
  decide +kernel

theorem node_context_12_70955_458450 : EJMOriginalGlobalDAGData.nodes 9 ⟨458450, by decide⟩ =
    .split (coordinate 12) (![⟨458354, by decide⟩,⟨458397, by decide⟩,⟨458428, by decide⟩,⟨458449, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_70955_458450 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70955 ⟨458450, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 70955
    ⟨458450, by decide⟩ (by decide) (![⟨458354, by decide⟩,⟨458397, by decide⟩,⟨458428, by decide⟩,⟨458449, by decide⟩]) unmarked_context_12_70955_458450 node_context_12_70955_458450
  intro a
  fin_cases a
  · exact context_13_283820_458354
  · exact context_13_283821_458397
  · exact context_13_283822_458428
  · exact context_13_283823_458449

theorem unmarked_context_11_17738_458451 : frontier 10 ⟨458451, by decide⟩
    (prefixCache 11 17738) (prefixPartial 11 17738) = false := by
  decide +kernel

theorem node_context_11_17738_458451 : EJMOriginalGlobalDAGData.nodes 10 ⟨458451, by decide⟩ =
    .split (coordinate 11) (![⟨458094, by decide⟩,⟨458207, by decide⟩,⟨458332, by decide⟩,⟨458450, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17738_458451 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17738 ⟨458451, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17738
    ⟨458451, by decide⟩ (by decide) (![⟨458094, by decide⟩,⟨458207, by decide⟩,⟨458332, by decide⟩,⟨458450, by decide⟩]) unmarked_context_11_17738_458451 node_context_11_17738_458451
  intro a
  fin_cases a
  · exact context_12_70952_458094
  · exact context_12_70953_458207
  · exact context_12_70954_458332
  · exact context_12_70955_458450

theorem selected_cut_17919 : selected 8 ⟨458484, by decide⟩
    (prefixPartial 13 283824) = some ⟨13, 2, 0, 458484, 283824, 737, 16384⟩ := by
  decide +kernel

theorem context_13_283824_458484 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 283824 ⟨458484, by decide⟩ :=
  accepted_of_selected 13 283824 ⟨458484, by decide⟩ ⟨13, 2, 0, 458484, 283824, 737, 16384⟩
    (by decide) selected_cut_17919

theorem selected_cut_17920 : selected 8 ⟨458580, by decide⟩
    (prefixPartial 13 283825) = some ⟨13, 2, 0, 458580, 283825, 3317, 16384⟩ := by
  decide +kernel

theorem context_13_283825_458580 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 283825 ⟨458580, by decide⟩ :=
  accepted_of_selected 13 283825 ⟨458580, by decide⟩ ⟨13, 2, 0, 458580, 283825, 3317, 16384⟩
    (by decide) selected_cut_17920

theorem selected_cut_17921 : selected 8 ⟨458689, by decide⟩
    (prefixPartial 13 283826) = some ⟨13, 2, 0, 458689, 283826, 2677, 16384⟩ := by
  decide +kernel

theorem context_13_283826_458689 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 283826 ⟨458689, by decide⟩ :=
  accepted_of_selected 13 283826 ⟨458689, by decide⟩ ⟨13, 2, 0, 458689, 283826, 2677, 16384⟩
    (by decide) selected_cut_17921

theorem selected_cut_17922 : selected 8 ⟨458736, by decide⟩
    (prefixPartial 13 283827) = some ⟨13, 2, 0, 458736, 283827, 1177, 16384⟩ := by
  decide +kernel

theorem context_13_283827_458736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 283827 ⟨458736, by decide⟩ :=
  accepted_of_selected 13 283827 ⟨458736, by decide⟩ ⟨13, 2, 0, 458736, 283827, 1177, 16384⟩
    (by decide) selected_cut_17922

theorem unmarked_context_12_70956_458737 : frontier 9 ⟨458737, by decide⟩
    (prefixCache 12 70956) (prefixPartial 12 70956) = false := by
  decide +kernel

theorem node_context_12_70956_458737 : EJMOriginalGlobalDAGData.nodes 9 ⟨458737, by decide⟩ =
    .split (coordinate 12) (![⟨458484, by decide⟩,⟨458580, by decide⟩,⟨458689, by decide⟩,⟨458736, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_70956_458737 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70956 ⟨458737, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 70956
    ⟨458737, by decide⟩ (by decide) (![⟨458484, by decide⟩,⟨458580, by decide⟩,⟨458689, by decide⟩,⟨458736, by decide⟩]) unmarked_context_12_70956_458737 node_context_12_70956_458737
  intro a
  fin_cases a
  · exact context_13_283824_458484
  · exact context_13_283825_458580
  · exact context_13_283826_458689
  · exact context_13_283827_458736

theorem selected_cut_17923 : selected 8 ⟨458755, by decide⟩
    (prefixPartial 13 283828) = some ⟨13, 2, 0, 458755, 283828, 369, 16384⟩ := by
  decide +kernel

theorem context_13_283828_458755 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 283828 ⟨458755, by decide⟩ :=
  accepted_of_selected 13 283828 ⟨458755, by decide⟩ ⟨13, 2, 0, 458755, 283828, 369, 16384⟩
    (by decide) selected_cut_17923

theorem selected_cut_17924 : selected 8 ⟨458792, by decide⟩
    (prefixPartial 13 283829) = some ⟨13, 2, 0, 458792, 283829, 1985, 16384⟩ := by
  decide +kernel

theorem context_13_283829_458792 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 283829 ⟨458792, by decide⟩ :=
  accepted_of_selected 13 283829 ⟨458792, by decide⟩ ⟨13, 2, 0, 458792, 283829, 1985, 16384⟩
    (by decide) selected_cut_17924

theorem selected_cut_17925 : selected 8 ⟨458842, by decide⟩
    (prefixPartial 13 283830) = some ⟨13, 2, 0, 458842, 283830, 1813, 16384⟩ := by
  decide +kernel

theorem context_13_283830_458842 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 283830 ⟨458842, by decide⟩ :=
  accepted_of_selected 13 283830 ⟨458842, by decide⟩ ⟨13, 2, 0, 458842, 283830, 1813, 16384⟩
    (by decide) selected_cut_17925

theorem selected_cut_17926 : selected 8 ⟨458862, by decide⟩
    (prefixPartial 13 283831) = some ⟨13, 2, 0, 458862, 283831, 801, 16384⟩ := by
  decide +kernel

theorem context_13_283831_458862 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 283831 ⟨458862, by decide⟩ :=
  accepted_of_selected 13 283831 ⟨458862, by decide⟩ ⟨13, 2, 0, 458862, 283831, 801, 16384⟩
    (by decide) selected_cut_17926

theorem unmarked_context_12_70957_458863 : frontier 9 ⟨458863, by decide⟩
    (prefixCache 12 70957) (prefixPartial 12 70957) = false := by
  decide +kernel

theorem node_context_12_70957_458863 : EJMOriginalGlobalDAGData.nodes 9 ⟨458863, by decide⟩ =
    .split (coordinate 12) (![⟨458755, by decide⟩,⟨458792, by decide⟩,⟨458842, by decide⟩,⟨458862, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_70957_458863 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70957 ⟨458863, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 70957
    ⟨458863, by decide⟩ (by decide) (![⟨458755, by decide⟩,⟨458792, by decide⟩,⟨458842, by decide⟩,⟨458862, by decide⟩]) unmarked_context_12_70957_458863 node_context_12_70957_458863
  intro a
  fin_cases a
  · exact context_13_283828_458755
  · exact context_13_283829_458792
  · exact context_13_283830_458842
  · exact context_13_283831_458862

theorem selected_cut_17927 : selected 8 ⟨458873, by decide⟩
    (prefixPartial 13 283832) = some ⟨13, 2, 0, 458873, 283832, 317, 16384⟩ := by
  decide +kernel

theorem context_13_283832_458873 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 283832 ⟨458873, by decide⟩ :=
  accepted_of_selected 13 283832 ⟨458873, by decide⟩ ⟨13, 2, 0, 458873, 283832, 317, 16384⟩
    (by decide) selected_cut_17927

theorem selected_cut_17928 : selected 8 ⟨458917, by decide⟩
    (prefixPartial 13 283833) = some ⟨13, 2, 0, 458917, 283833, 2553, 16384⟩ := by
  decide +kernel

theorem context_13_283833_458917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 283833 ⟨458917, by decide⟩ :=
  accepted_of_selected 13 283833 ⟨458917, by decide⟩ ⟨13, 2, 0, 458917, 283833, 2553, 16384⟩
    (by decide) selected_cut_17928

theorem selected_cut_17929 : selected 8 ⟨458963, by decide⟩
    (prefixPartial 13 283834) = some ⟨13, 2, 0, 458963, 283834, 1761, 16384⟩ := by
  decide +kernel

theorem context_13_283834_458963 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 283834 ⟨458963, by decide⟩ :=
  accepted_of_selected 13 283834 ⟨458963, by decide⟩ ⟨13, 2, 0, 458963, 283834, 1761, 16384⟩
    (by decide) selected_cut_17929

theorem selected_cut_17930 : selected 8 ⟨458979, by decide⟩
    (prefixPartial 13 283835) = some ⟨13, 2, 0, 458979, 283835, 885, 16384⟩ := by
  decide +kernel

theorem context_13_283835_458979 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 283835 ⟨458979, by decide⟩ :=
  accepted_of_selected 13 283835 ⟨458979, by decide⟩ ⟨13, 2, 0, 458979, 283835, 885, 16384⟩
    (by decide) selected_cut_17930

theorem unmarked_context_12_70958_458980 : frontier 9 ⟨458980, by decide⟩
    (prefixCache 12 70958) (prefixPartial 12 70958) = false := by
  decide +kernel

theorem node_context_12_70958_458980 : EJMOriginalGlobalDAGData.nodes 9 ⟨458980, by decide⟩ =
    .split (coordinate 12) (![⟨458873, by decide⟩,⟨458917, by decide⟩,⟨458963, by decide⟩,⟨458979, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_70958_458980 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70958 ⟨458980, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 70958
    ⟨458980, by decide⟩ (by decide) (![⟨458873, by decide⟩,⟨458917, by decide⟩,⟨458963, by decide⟩,⟨458979, by decide⟩]) unmarked_context_12_70958_458980 node_context_12_70958_458980
  intro a
  fin_cases a
  · exact context_13_283832_458873
  · exact context_13_283833_458917
  · exact context_13_283834_458963
  · exact context_13_283835_458979

theorem selected_cut_17931 : selected 8 ⟨458989, by decide⟩
    (prefixPartial 13 283836) = some ⟨13, 2, 0, 458989, 283836, 165, 16384⟩ := by
  decide +kernel

theorem context_13_283836_458989 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 283836 ⟨458989, by decide⟩ :=
  accepted_of_selected 13 283836 ⟨458989, by decide⟩ ⟨13, 2, 0, 458989, 283836, 165, 16384⟩
    (by decide) selected_cut_17931

theorem selected_cut_17932 : selected 8 ⟨459041, by decide⟩
    (prefixPartial 13 283837) = some ⟨13, 2, 0, 459041, 283837, 2513, 16384⟩ := by
  decide +kernel

theorem context_13_283837_459041 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 283837 ⟨459041, by decide⟩ :=
  accepted_of_selected 13 283837 ⟨459041, by decide⟩ ⟨13, 2, 0, 459041, 283837, 2513, 16384⟩
    (by decide) selected_cut_17932

theorem selected_cut_17933 : selected 8 ⟨459089, by decide⟩
    (prefixPartial 13 283838) = some ⟨13, 2, 0, 459089, 283838, 1909, 16384⟩ := by
  decide +kernel

theorem context_13_283838_459089 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 283838 ⟨459089, by decide⟩ :=
  accepted_of_selected 13 283838 ⟨459089, by decide⟩ ⟨13, 2, 0, 459089, 283838, 1909, 16384⟩
    (by decide) selected_cut_17933

theorem selected_cut_17934 : selected 8 ⟨459102, by decide⟩
    (prefixPartial 13 283839) = some ⟨13, 2, 0, 459102, 283839, 825, 16384⟩ := by
  decide +kernel

theorem context_13_283839_459102 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 283839 ⟨459102, by decide⟩ :=
  accepted_of_selected 13 283839 ⟨459102, by decide⟩ ⟨13, 2, 0, 459102, 283839, 825, 16384⟩
    (by decide) selected_cut_17934

theorem unmarked_context_12_70959_459103 : frontier 9 ⟨459103, by decide⟩
    (prefixCache 12 70959) (prefixPartial 12 70959) = false := by
  decide +kernel

theorem node_context_12_70959_459103 : EJMOriginalGlobalDAGData.nodes 9 ⟨459103, by decide⟩ =
    .split (coordinate 12) (![⟨458989, by decide⟩,⟨459041, by decide⟩,⟨459089, by decide⟩,⟨459102, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_70959_459103 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70959 ⟨459103, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 70959
    ⟨459103, by decide⟩ (by decide) (![⟨458989, by decide⟩,⟨459041, by decide⟩,⟨459089, by decide⟩,⟨459102, by decide⟩]) unmarked_context_12_70959_459103 node_context_12_70959_459103
  intro a
  fin_cases a
  · exact context_13_283836_458989
  · exact context_13_283837_459041
  · exact context_13_283838_459089
  · exact context_13_283839_459102

theorem unmarked_context_11_17739_459104 : frontier 10 ⟨459104, by decide⟩
    (prefixCache 11 17739) (prefixPartial 11 17739) = false := by
  decide +kernel

theorem node_context_11_17739_459104 : EJMOriginalGlobalDAGData.nodes 10 ⟨459104, by decide⟩ =
    .split (coordinate 11) (![⟨458737, by decide⟩,⟨458863, by decide⟩,⟨458980, by decide⟩,⟨459103, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17739_459104 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17739 ⟨459104, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17739
    ⟨459104, by decide⟩ (by decide) (![⟨458737, by decide⟩,⟨458863, by decide⟩,⟨458980, by decide⟩,⟨459103, by decide⟩]) unmarked_context_11_17739_459104 node_context_11_17739_459104
  intro a
  fin_cases a
  · exact context_12_70956_458737
  · exact context_12_70957_458863
  · exact context_12_70958_458980
  · exact context_12_70959_459103

theorem unmarked_context_10_4434_459105 : frontier 11 ⟨459105, by decide⟩
    (prefixCache 10 4434) (prefixPartial 10 4434) = false := by
  decide +kernel

theorem node_context_10_4434_459105 : EJMOriginalGlobalDAGData.nodes 11 ⟨459105, by decide⟩ =
    .split (coordinate 10) (![⟨457389, by decide⟩,⟨457829, by decide⟩,⟨458451, by decide⟩,⟨459104, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4434_459105 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4434 ⟨459105, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4434
    ⟨459105, by decide⟩ (by decide) (![⟨457389, by decide⟩,⟨457829, by decide⟩,⟨458451, by decide⟩,⟨459104, by decide⟩]) unmarked_context_10_4434_459105 node_context_10_4434_459105
  intro a
  fin_cases a
  · exact context_11_17736_457389
  · exact context_11_17737_457829
  · exact context_11_17738_458451
  · exact context_11_17739_459104

theorem selected_cut_17935 : selected 11 ⟨3440, by decide⟩
    (prefixPartial 10 4435) = some ⟨10, 1, 0, 3440, 4435, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_4435_3440 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4435 ⟨3440, by decide⟩ :=
  accepted_of_selected 10 4435 ⟨3440, by decide⟩ ⟨10, 1, 0, 3440, 4435, 1, 1048576⟩
    (by decide) selected_cut_17935

theorem unmarked_context_9_1108_459106 : frontier 12 ⟨459106, by decide⟩
    (prefixCache 9 1108) (prefixPartial 9 1108) = false := by
  decide +kernel

theorem node_context_9_1108_459106 : EJMOriginalGlobalDAGData.nodes 12 ⟨459106, by decide⟩ =
    .split (coordinate 9) (![⟨455493, by decide⟩,⟨456926, by decide⟩,⟨459105, by decide⟩,⟨3440, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1108_459106 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1108 ⟨459106, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1108
    ⟨459106, by decide⟩ (by decide) (![⟨455493, by decide⟩,⟨456926, by decide⟩,⟨459105, by decide⟩,⟨3440, by decide⟩]) unmarked_context_9_1108_459106 node_context_9_1108_459106
  intro a
  fin_cases a
  · exact context_10_4432_455493
  · exact context_10_4433_456926
  · exact context_10_4434_459105
  · exact context_10_4435_3440

theorem selected_cut_17936 : selected 9 ⟨459206, by decide⟩
    (prefixPartial 12 70976) = some ⟨12, 2, 0, 459206, 70976, 1841, 65536⟩ := by
  decide +kernel

theorem context_12_70976_459206 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70976 ⟨459206, by decide⟩ :=
  accepted_of_selected 12 70976 ⟨459206, by decide⟩ ⟨12, 2, 0, 459206, 70976, 1841, 65536⟩
    (by decide) selected_cut_17936

theorem selected_cut_17937 : selected 9 ⟨459280, by decide⟩
    (prefixPartial 12 70977) = some ⟨12, 2, 0, 459280, 70977, 1269, 65536⟩ := by
  decide +kernel

theorem context_12_70977_459280 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70977 ⟨459280, by decide⟩ :=
  accepted_of_selected 12 70977 ⟨459280, by decide⟩ ⟨12, 2, 0, 459280, 70977, 1269, 65536⟩
    (by decide) selected_cut_17937

theorem selected_cut_17938 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 283912) = some ⟨13, 1, 0, 3444, 283912, 1, 16384⟩ := by
  decide +kernel

theorem context_13_283912_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 283912 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 283912 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 283912, 1, 16384⟩
    (by decide) selected_cut_17938

theorem selected_cut_17939 : selected 8 ⟨459330, by decide⟩
    (prefixPartial 13 283913) = some ⟨13, 2, 0, 459330, 283913, 1937, 16384⟩ := by
  decide +kernel

theorem context_13_283913_459330 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 283913 ⟨459330, by decide⟩ :=
  accepted_of_selected 13 283913 ⟨459330, by decide⟩ ⟨13, 2, 0, 459330, 283913, 1937, 16384⟩
    (by decide) selected_cut_17939

theorem selected_cut_17940 : selected 8 ⟨459382, by decide⟩
    (prefixPartial 13 283914) = some ⟨13, 2, 0, 459382, 283914, 1601, 16384⟩ := by
  decide +kernel

theorem context_13_283914_459382 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 283914 ⟨459382, by decide⟩ :=
  accepted_of_selected 13 283914 ⟨459382, by decide⟩ ⟨13, 2, 0, 459382, 283914, 1601, 16384⟩
    (by decide) selected_cut_17940

theorem selected_cut_17941 : selected 8 ⟨459413, by decide⟩
    (prefixPartial 13 283915) = some ⟨13, 2, 0, 459413, 283915, 909, 16384⟩ := by
  decide +kernel

theorem context_13_283915_459413 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 283915 ⟨459413, by decide⟩ :=
  accepted_of_selected 13 283915 ⟨459413, by decide⟩ ⟨13, 2, 0, 459413, 283915, 909, 16384⟩
    (by decide) selected_cut_17941

theorem unmarked_context_12_70978_459414 : frontier 9 ⟨459414, by decide⟩
    (prefixCache 12 70978) (prefixPartial 12 70978) = false := by
  decide +kernel

theorem node_context_12_70978_459414 : EJMOriginalGlobalDAGData.nodes 9 ⟨459414, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨459330, by decide⟩,⟨459382, by decide⟩,⟨459413, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_70978_459414 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70978 ⟨459414, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 70978
    ⟨459414, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨459330, by decide⟩,⟨459382, by decide⟩,⟨459413, by decide⟩]) unmarked_context_12_70978_459414 node_context_12_70978_459414
  intro a
  fin_cases a
  · exact context_13_283912_3444
  · exact context_13_283913_459330
  · exact context_13_283914_459382
  · exact context_13_283915_459413

theorem selected_cut_17942 : selected 9 ⟨893, by decide⟩
    (prefixPartial 12 70979) = some ⟨12, 1, 0, 893, 70979, 1, 65536⟩ := by
  decide +kernel

theorem context_12_70979_893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70979 ⟨893, by decide⟩ :=
  accepted_of_selected 12 70979 ⟨893, by decide⟩ ⟨12, 1, 0, 893, 70979, 1, 65536⟩
    (by decide) selected_cut_17942

theorem unmarked_context_11_17744_459415 : frontier 10 ⟨459415, by decide⟩
    (prefixCache 11 17744) (prefixPartial 11 17744) = false := by
  decide +kernel

theorem node_context_11_17744_459415 : EJMOriginalGlobalDAGData.nodes 10 ⟨459415, by decide⟩ =
    .split (coordinate 11) (![⟨459206, by decide⟩,⟨459280, by decide⟩,⟨459414, by decide⟩,⟨893, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17744_459415 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17744 ⟨459415, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17744
    ⟨459415, by decide⟩ (by decide) (![⟨459206, by decide⟩,⟨459280, by decide⟩,⟨459414, by decide⟩,⟨893, by decide⟩]) unmarked_context_11_17744_459415 node_context_11_17744_459415
  intro a
  fin_cases a
  · exact context_12_70976_459206
  · exact context_12_70977_459280
  · exact context_12_70978_459414
  · exact context_12_70979_893

theorem selected_cut_17943 : selected 10 ⟨459416, by decide⟩
    (prefixPartial 11 17745) = some ⟨11, 1, 0, 459416, 17745, 1, 262144⟩ := by
  decide +kernel

theorem context_11_17745_459416 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17745 ⟨459416, by decide⟩ :=
  accepted_of_selected 11 17745 ⟨459416, by decide⟩ ⟨11, 1, 0, 459416, 17745, 1, 262144⟩
    (by decide) selected_cut_17943

theorem selected_cut_17944 : selected 9 ⟨459531, by decide⟩
    (prefixPartial 12 70984) = some ⟨12, 2, 0, 459531, 70984, 3949, 65536⟩ := by
  decide +kernel

theorem context_12_70984_459531 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70984 ⟨459531, by decide⟩ :=
  accepted_of_selected 12 70984 ⟨459531, by decide⟩ ⟨12, 2, 0, 459531, 70984, 3949, 65536⟩
    (by decide) selected_cut_17944

theorem selected_cut_17945 : selected 9 ⟨459620, by decide⟩
    (prefixPartial 12 70985) = some ⟨12, 2, 0, 459620, 70985, 3561, 65536⟩ := by
  decide +kernel

theorem context_12_70985_459620 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70985 ⟨459620, by decide⟩ :=
  accepted_of_selected 12 70985 ⟨459620, by decide⟩ ⟨12, 2, 0, 459620, 70985, 3561, 65536⟩
    (by decide) selected_cut_17945

theorem selected_cut_17946 : selected 9 ⟨459696, by decide⟩
    (prefixPartial 12 70986) = some ⟨12, 2, 0, 459696, 70986, 4061, 65536⟩ := by
  decide +kernel

theorem context_12_70986_459696 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70986 ⟨459696, by decide⟩ :=
  accepted_of_selected 12 70986 ⟨459696, by decide⟩ ⟨12, 2, 0, 459696, 70986, 4061, 65536⟩
    (by decide) selected_cut_17946

theorem selected_cut_17947 : selected 9 ⟨459764, by decide⟩
    (prefixPartial 12 70987) = some ⟨12, 2, 0, 459764, 70987, 3989, 65536⟩ := by
  decide +kernel

theorem context_12_70987_459764 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70987 ⟨459764, by decide⟩ :=
  accepted_of_selected 12 70987 ⟨459764, by decide⟩ ⟨12, 2, 0, 459764, 70987, 3989, 65536⟩
    (by decide) selected_cut_17947

theorem unmarked_context_11_17746_459765 : frontier 10 ⟨459765, by decide⟩
    (prefixCache 11 17746) (prefixPartial 11 17746) = false := by
  decide +kernel

theorem node_context_11_17746_459765 : EJMOriginalGlobalDAGData.nodes 10 ⟨459765, by decide⟩ =
    .split (coordinate 11) (![⟨459531, by decide⟩,⟨459620, by decide⟩,⟨459696, by decide⟩,⟨459764, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17746_459765 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17746 ⟨459765, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17746
    ⟨459765, by decide⟩ (by decide) (![⟨459531, by decide⟩,⟨459620, by decide⟩,⟨459696, by decide⟩,⟨459764, by decide⟩]) unmarked_context_11_17746_459765 node_context_11_17746_459765
  intro a
  fin_cases a
  · exact context_12_70984_459531
  · exact context_12_70985_459620
  · exact context_12_70986_459696
  · exact context_12_70987_459764

theorem selected_cut_17948 : selected 10 ⟨1736, by decide⟩
    (prefixPartial 11 17747) = some ⟨11, 1, 0, 1736, 17747, 1, 262144⟩ := by
  decide +kernel

theorem context_11_17747_1736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17747 ⟨1736, by decide⟩ :=
  accepted_of_selected 11 17747 ⟨1736, by decide⟩ ⟨11, 1, 0, 1736, 17747, 1, 262144⟩
    (by decide) selected_cut_17948

theorem unmarked_context_10_4436_459766 : frontier 11 ⟨459766, by decide⟩
    (prefixCache 10 4436) (prefixPartial 10 4436) = false := by
  decide +kernel

theorem node_context_10_4436_459766 : EJMOriginalGlobalDAGData.nodes 11 ⟨459766, by decide⟩ =
    .split (coordinate 10) (![⟨459415, by decide⟩,⟨459416, by decide⟩,⟨459765, by decide⟩,⟨1736, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4436_459766 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4436 ⟨459766, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4436
    ⟨459766, by decide⟩ (by decide) (![⟨459415, by decide⟩,⟨459416, by decide⟩,⟨459765, by decide⟩,⟨1736, by decide⟩]) unmarked_context_10_4436_459766 node_context_10_4436_459766
  intro a
  fin_cases a
  · exact context_11_17744_459415
  · exact context_11_17745_459416
  · exact context_11_17746_459765
  · exact context_11_17747_1736

theorem selected_cut_17949 : selected 9 ⟨459814, by decide⟩
    (prefixPartial 12 70992) = some ⟨12, 2, 0, 459814, 70992, 1137, 65536⟩ := by
  decide +kernel

theorem context_12_70992_459814 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70992 ⟨459814, by decide⟩ :=
  accepted_of_selected 12 70992 ⟨459814, by decide⟩ ⟨12, 2, 0, 459814, 70992, 1137, 65536⟩
    (by decide) selected_cut_17949

theorem selected_cut_17950 : selected 9 ⟨455939, by decide⟩
    (prefixPartial 12 70993) = some ⟨12, 1, 0, 455939, 70993, 1, 65536⟩ := by
  decide +kernel

theorem context_12_70993_455939 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70993 ⟨455939, by decide⟩ :=
  accepted_of_selected 12 70993 ⟨455939, by decide⟩ ⟨12, 1, 0, 455939, 70993, 1, 65536⟩
    (by decide) selected_cut_17950

theorem selected_cut_17951 : selected 9 ⟨459881, by decide⟩
    (prefixPartial 12 70994) = some ⟨12, 2, 0, 459881, 70994, 3669, 65536⟩ := by
  decide +kernel

theorem context_12_70994_459881 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70994 ⟨459881, by decide⟩ :=
  accepted_of_selected 12 70994 ⟨459881, by decide⟩ ⟨12, 2, 0, 459881, 70994, 3669, 65536⟩
    (by decide) selected_cut_17951

theorem selected_cut_17952 : selected 9 ⟨893, by decide⟩
    (prefixPartial 12 70995) = some ⟨12, 1, 0, 893, 70995, 1, 65536⟩ := by
  decide +kernel

theorem context_12_70995_893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70995 ⟨893, by decide⟩ :=
  accepted_of_selected 12 70995 ⟨893, by decide⟩ ⟨12, 1, 0, 893, 70995, 1, 65536⟩
    (by decide) selected_cut_17952

theorem unmarked_context_11_17748_459882 : frontier 10 ⟨459882, by decide⟩
    (prefixCache 11 17748) (prefixPartial 11 17748) = false := by
  decide +kernel

theorem node_context_11_17748_459882 : EJMOriginalGlobalDAGData.nodes 10 ⟨459882, by decide⟩ =
    .split (coordinate 11) (![⟨459814, by decide⟩,⟨455939, by decide⟩,⟨459881, by decide⟩,⟨893, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17748_459882 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17748 ⟨459882, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17748
    ⟨459882, by decide⟩ (by decide) (![⟨459814, by decide⟩,⟨455939, by decide⟩,⟨459881, by decide⟩,⟨893, by decide⟩]) unmarked_context_11_17748_459882 node_context_11_17748_459882
  intro a
  fin_cases a
  · exact context_12_70992_459814
  · exact context_12_70993_455939
  · exact context_12_70994_459881
  · exact context_12_70995_893

theorem selected_cut_17953 : selected 10 ⟨459416, by decide⟩
    (prefixPartial 11 17749) = some ⟨11, 1, 0, 459416, 17749, 1, 262144⟩ := by
  decide +kernel

theorem context_11_17749_459416 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17749 ⟨459416, by decide⟩ :=
  accepted_of_selected 11 17749 ⟨459416, by decide⟩ ⟨11, 1, 0, 459416, 17749, 1, 262144⟩
    (by decide) selected_cut_17953

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
