/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover192
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_18531 : selected 8 ⟨474609, by decide⟩
    (prefixPartial 13 286908) = some ⟨13, 2, 0, 474609, 286908, 629, 16384⟩ := by
  decide +kernel

theorem context_13_286908_474609 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286908 ⟨474609, by decide⟩ :=
  accepted_of_selected 13 286908 ⟨474609, by decide⟩ ⟨13, 2, 0, 474609, 286908, 629, 16384⟩
    (by decide) selected_cut_18531

theorem selected_cut_18532 : selected 8 ⟨474649, by decide⟩
    (prefixPartial 13 286909) = some ⟨13, 2, 0, 474649, 286909, 2745, 16384⟩ := by
  decide +kernel

theorem context_13_286909_474649 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286909 ⟨474649, by decide⟩ :=
  accepted_of_selected 13 286909 ⟨474649, by decide⟩ ⟨13, 2, 0, 474649, 286909, 2745, 16384⟩
    (by decide) selected_cut_18532

theorem selected_cut_18533 : selected 8 ⟨474670, by decide⟩
    (prefixPartial 13 286910) = some ⟨13, 2, 0, 474670, 286910, 1573, 16384⟩ := by
  decide +kernel

theorem context_13_286910_474670 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286910 ⟨474670, by decide⟩ :=
  accepted_of_selected 13 286910 ⟨474670, by decide⟩ ⟨13, 2, 0, 474670, 286910, 1573, 16384⟩
    (by decide) selected_cut_18533

theorem selected_cut_18534 : selected 8 ⟨474676, by decide⟩
    (prefixPartial 13 286911) = some ⟨13, 2, 0, 474676, 286911, 693, 16384⟩ := by
  decide +kernel

theorem context_13_286911_474676 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286911 ⟨474676, by decide⟩ :=
  accepted_of_selected 13 286911 ⟨474676, by decide⟩ ⟨13, 2, 0, 474676, 286911, 693, 16384⟩
    (by decide) selected_cut_18534

theorem unmarked_context_12_71727_474677 : frontier 9 ⟨474677, by decide⟩
    (prefixCache 12 71727) (prefixPartial 12 71727) = false := by
  decide +kernel

theorem node_context_12_71727_474677 : EJMOriginalGlobalDAGData.nodes 9 ⟨474677, by decide⟩ =
    .split (coordinate 12) (![⟨474609, by decide⟩,⟨474649, by decide⟩,⟨474670, by decide⟩,⟨474676, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71727_474677 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71727 ⟨474677, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71727
    ⟨474677, by decide⟩ (by decide) (![⟨474609, by decide⟩,⟨474649, by decide⟩,⟨474670, by decide⟩,⟨474676, by decide⟩]) unmarked_context_12_71727_474677 node_context_12_71727_474677
  intro a
  fin_cases a
  · exact context_13_286908_474609
  · exact context_13_286909_474649
  · exact context_13_286910_474670
  · exact context_13_286911_474676

theorem unmarked_context_11_17931_474678 : frontier 10 ⟨474678, by decide⟩
    (prefixCache 11 17931) (prefixPartial 11 17931) = false := by
  decide +kernel

theorem node_context_11_17931_474678 : EJMOriginalGlobalDAGData.nodes 10 ⟨474678, by decide⟩ =
    .split (coordinate 11) (![⟨474439, by decide⟩,⟨474511, by decide⟩,⟨474593, by decide⟩,⟨474677, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17931_474678 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17931 ⟨474678, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17931
    ⟨474678, by decide⟩ (by decide) (![⟨474439, by decide⟩,⟨474511, by decide⟩,⟨474593, by decide⟩,⟨474677, by decide⟩]) unmarked_context_11_17931_474678 node_context_11_17931_474678
  intro a
  fin_cases a
  · exact context_12_71724_474439
  · exact context_12_71725_474511
  · exact context_12_71726_474593
  · exact context_12_71727_474677

theorem unmarked_context_10_4482_474679 : frontier 11 ⟨474679, by decide⟩
    (prefixCache 10 4482) (prefixPartial 10 4482) = false := by
  decide +kernel

theorem node_context_10_4482_474679 : EJMOriginalGlobalDAGData.nodes 11 ⟨474679, by decide⟩ =
    .split (coordinate 10) (![⟨473731, by decide⟩,⟨474110, by decide⟩,⟨474320, by decide⟩,⟨474678, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4482_474679 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4482 ⟨474679, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4482
    ⟨474679, by decide⟩ (by decide) (![⟨473731, by decide⟩,⟨474110, by decide⟩,⟨474320, by decide⟩,⟨474678, by decide⟩]) unmarked_context_10_4482_474679 node_context_10_4482_474679
  intro a
  fin_cases a
  · exact context_11_17928_473731
  · exact context_11_17929_474110
  · exact context_11_17930_474320
  · exact context_11_17931_474678

theorem selected_cut_18535 : selected 9 ⟨445562, by decide⟩
    (prefixPartial 12 71728) = some ⟨12, 1, 0, 445562, 71728, 1, 65536⟩ := by
  decide +kernel

theorem context_12_71728_445562 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71728 ⟨445562, by decide⟩ :=
  accepted_of_selected 12 71728 ⟨445562, by decide⟩ ⟨12, 1, 0, 445562, 71728, 1, 65536⟩
    (by decide) selected_cut_18535

theorem selected_cut_18536 : selected 8 ⟨474691, by decide⟩
    (prefixPartial 13 286916) = some ⟨13, 2, 0, 474691, 286916, 521, 16384⟩ := by
  decide +kernel

theorem context_13_286916_474691 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286916 ⟨474691, by decide⟩ :=
  accepted_of_selected 13 286916 ⟨474691, by decide⟩ ⟨13, 2, 0, 474691, 286916, 521, 16384⟩
    (by decide) selected_cut_18536

theorem selected_cut_18537 : selected 8 ⟨474718, by decide⟩
    (prefixPartial 13 286917) = some ⟨13, 2, 0, 474718, 286917, 2009, 16384⟩ := by
  decide +kernel

theorem context_13_286917_474718 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286917 ⟨474718, by decide⟩ :=
  accepted_of_selected 13 286917 ⟨474718, by decide⟩ ⟨13, 2, 0, 474718, 286917, 2009, 16384⟩
    (by decide) selected_cut_18537

theorem selected_cut_18538 : selected 8 ⟨474737, by decide⟩
    (prefixPartial 13 286918) = some ⟨13, 2, 0, 474737, 286918, 1193, 16384⟩ := by
  decide +kernel

theorem context_13_286918_474737 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286918 ⟨474737, by decide⟩ :=
  accepted_of_selected 13 286918 ⟨474737, by decide⟩ ⟨13, 2, 0, 474737, 286918, 1193, 16384⟩
    (by decide) selected_cut_18538

theorem selected_cut_18539 : selected 8 ⟨474743, by decide⟩
    (prefixPartial 13 286919) = some ⟨13, 2, 0, 474743, 286919, 785, 16384⟩ := by
  decide +kernel

theorem context_13_286919_474743 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286919 ⟨474743, by decide⟩ :=
  accepted_of_selected 13 286919 ⟨474743, by decide⟩ ⟨13, 2, 0, 474743, 286919, 785, 16384⟩
    (by decide) selected_cut_18539

theorem unmarked_context_12_71729_474744 : frontier 9 ⟨474744, by decide⟩
    (prefixCache 12 71729) (prefixPartial 12 71729) = false := by
  decide +kernel

theorem node_context_12_71729_474744 : EJMOriginalGlobalDAGData.nodes 9 ⟨474744, by decide⟩ =
    .split (coordinate 12) (![⟨474691, by decide⟩,⟨474718, by decide⟩,⟨474737, by decide⟩,⟨474743, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71729_474744 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71729 ⟨474744, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71729
    ⟨474744, by decide⟩ (by decide) (![⟨474691, by decide⟩,⟨474718, by decide⟩,⟨474737, by decide⟩,⟨474743, by decide⟩]) unmarked_context_12_71729_474744 node_context_12_71729_474744
  intro a
  fin_cases a
  · exact context_13_286916_474691
  · exact context_13_286917_474718
  · exact context_13_286918_474737
  · exact context_13_286919_474743

theorem selected_cut_18540 : selected 8 ⟨474751, by decide⟩
    (prefixPartial 13 286920) = some ⟨13, 2, 0, 474751, 286920, 485, 16384⟩ := by
  decide +kernel

theorem context_13_286920_474751 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286920 ⟨474751, by decide⟩ :=
  accepted_of_selected 13 286920 ⟨474751, by decide⟩ ⟨13, 2, 0, 474751, 286920, 485, 16384⟩
    (by decide) selected_cut_18540

theorem selected_cut_18541 : selected 8 ⟨474785, by decide⟩
    (prefixPartial 13 286921) = some ⟨13, 2, 0, 474785, 286921, 2137, 16384⟩ := by
  decide +kernel

theorem context_13_286921_474785 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286921 ⟨474785, by decide⟩ :=
  accepted_of_selected 13 286921 ⟨474785, by decide⟩ ⟨13, 2, 0, 474785, 286921, 2137, 16384⟩
    (by decide) selected_cut_18541

theorem selected_cut_18542 : selected 8 ⟨474800, by decide⟩
    (prefixPartial 13 286922) = some ⟨13, 2, 0, 474800, 286922, 1409, 16384⟩ := by
  decide +kernel

theorem context_13_286922_474800 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286922 ⟨474800, by decide⟩ :=
  accepted_of_selected 13 286922 ⟨474800, by decide⟩ ⟨13, 2, 0, 474800, 286922, 1409, 16384⟩
    (by decide) selected_cut_18542

theorem selected_cut_18543 : selected 8 ⟨474805, by decide⟩
    (prefixPartial 13 286923) = some ⟨13, 2, 0, 474805, 286923, 777, 16384⟩ := by
  decide +kernel

theorem context_13_286923_474805 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286923 ⟨474805, by decide⟩ :=
  accepted_of_selected 13 286923 ⟨474805, by decide⟩ ⟨13, 2, 0, 474805, 286923, 777, 16384⟩
    (by decide) selected_cut_18543

theorem unmarked_context_12_71730_474806 : frontier 9 ⟨474806, by decide⟩
    (prefixCache 12 71730) (prefixPartial 12 71730) = false := by
  decide +kernel

theorem node_context_12_71730_474806 : EJMOriginalGlobalDAGData.nodes 9 ⟨474806, by decide⟩ =
    .split (coordinate 12) (![⟨474751, by decide⟩,⟨474785, by decide⟩,⟨474800, by decide⟩,⟨474805, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71730_474806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71730 ⟨474806, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71730
    ⟨474806, by decide⟩ (by decide) (![⟨474751, by decide⟩,⟨474785, by decide⟩,⟨474800, by decide⟩,⟨474805, by decide⟩]) unmarked_context_12_71730_474806 node_context_12_71730_474806
  intro a
  fin_cases a
  · exact context_13_286920_474751
  · exact context_13_286921_474785
  · exact context_13_286922_474800
  · exact context_13_286923_474805

theorem selected_cut_18544 : selected 8 ⟨474817, by decide⟩
    (prefixPartial 13 286924) = some ⟨13, 2, 0, 474817, 286924, 441, 16384⟩ := by
  decide +kernel

theorem context_13_286924_474817 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286924 ⟨474817, by decide⟩ :=
  accepted_of_selected 13 286924 ⟨474817, by decide⟩ ⟨13, 2, 0, 474817, 286924, 441, 16384⟩
    (by decide) selected_cut_18544

theorem selected_cut_18545 : selected 8 ⟨474852, by decide⟩
    (prefixPartial 13 286925) = some ⟨13, 2, 0, 474852, 286925, 2217, 16384⟩ := by
  decide +kernel

theorem context_13_286925_474852 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286925 ⟨474852, by decide⟩ :=
  accepted_of_selected 13 286925 ⟨474852, by decide⟩ ⟨13, 2, 0, 474852, 286925, 2217, 16384⟩
    (by decide) selected_cut_18545

theorem selected_cut_18546 : selected 8 ⟨474870, by decide⟩
    (prefixPartial 13 286926) = some ⟨13, 2, 0, 474870, 286926, 1429, 16384⟩ := by
  decide +kernel

theorem context_13_286926_474870 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286926 ⟨474870, by decide⟩ :=
  accepted_of_selected 13 286926 ⟨474870, by decide⟩ ⟨13, 2, 0, 474870, 286926, 1429, 16384⟩
    (by decide) selected_cut_18546

theorem selected_cut_18547 : selected 8 ⟨474875, by decide⟩
    (prefixPartial 13 286927) = some ⟨13, 2, 0, 474875, 286927, 629, 16384⟩ := by
  decide +kernel

theorem context_13_286927_474875 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286927 ⟨474875, by decide⟩ :=
  accepted_of_selected 13 286927 ⟨474875, by decide⟩ ⟨13, 2, 0, 474875, 286927, 629, 16384⟩
    (by decide) selected_cut_18547

theorem unmarked_context_12_71731_474876 : frontier 9 ⟨474876, by decide⟩
    (prefixCache 12 71731) (prefixPartial 12 71731) = false := by
  decide +kernel

theorem node_context_12_71731_474876 : EJMOriginalGlobalDAGData.nodes 9 ⟨474876, by decide⟩ =
    .split (coordinate 12) (![⟨474817, by decide⟩,⟨474852, by decide⟩,⟨474870, by decide⟩,⟨474875, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71731_474876 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71731 ⟨474876, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71731
    ⟨474876, by decide⟩ (by decide) (![⟨474817, by decide⟩,⟨474852, by decide⟩,⟨474870, by decide⟩,⟨474875, by decide⟩]) unmarked_context_12_71731_474876 node_context_12_71731_474876
  intro a
  fin_cases a
  · exact context_13_286924_474817
  · exact context_13_286925_474852
  · exact context_13_286926_474870
  · exact context_13_286927_474875

theorem unmarked_context_11_17932_474877 : frontier 10 ⟨474877, by decide⟩
    (prefixCache 11 17932) (prefixPartial 11 17932) = false := by
  decide +kernel

theorem node_context_11_17932_474877 : EJMOriginalGlobalDAGData.nodes 10 ⟨474877, by decide⟩ =
    .split (coordinate 11) (![⟨445562, by decide⟩,⟨474744, by decide⟩,⟨474806, by decide⟩,⟨474876, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17932_474877 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17932 ⟨474877, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17932
    ⟨474877, by decide⟩ (by decide) (![⟨445562, by decide⟩,⟨474744, by decide⟩,⟨474806, by decide⟩,⟨474876, by decide⟩]) unmarked_context_11_17932_474877 node_context_11_17932_474877
  intro a
  fin_cases a
  · exact context_12_71728_445562
  · exact context_12_71729_474744
  · exact context_12_71730_474806
  · exact context_12_71731_474876

theorem selected_cut_18548 : selected 8 ⟨474892, by decide⟩
    (prefixPartial 13 286928) = some ⟨13, 2, 0, 474892, 286928, 525, 16384⟩ := by
  decide +kernel

theorem context_13_286928_474892 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286928 ⟨474892, by decide⟩ :=
  accepted_of_selected 13 286928 ⟨474892, by decide⟩ ⟨13, 2, 0, 474892, 286928, 525, 16384⟩
    (by decide) selected_cut_18548

theorem selected_cut_18549 : selected 8 ⟨474943, by decide⟩
    (prefixPartial 13 286929) = some ⟨13, 2, 0, 474943, 286929, 3033, 16384⟩ := by
  decide +kernel

theorem context_13_286929_474943 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286929 ⟨474943, by decide⟩ :=
  accepted_of_selected 13 286929 ⟨474943, by decide⟩ ⟨13, 2, 0, 474943, 286929, 3033, 16384⟩
    (by decide) selected_cut_18549

theorem selected_cut_18550 : selected 8 ⟨474978, by decide⟩
    (prefixPartial 13 286930) = some ⟨13, 2, 0, 474978, 286930, 2121, 16384⟩ := by
  decide +kernel

theorem context_13_286930_474978 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286930 ⟨474978, by decide⟩ :=
  accepted_of_selected 13 286930 ⟨474978, by decide⟩ ⟨13, 2, 0, 474978, 286930, 2121, 16384⟩
    (by decide) selected_cut_18550

theorem selected_cut_18551 : selected 8 ⟨474997, by decide⟩
    (prefixPartial 13 286931) = some ⟨13, 2, 0, 474997, 286931, 1045, 16384⟩ := by
  decide +kernel

theorem context_13_286931_474997 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286931 ⟨474997, by decide⟩ :=
  accepted_of_selected 13 286931 ⟨474997, by decide⟩ ⟨13, 2, 0, 474997, 286931, 1045, 16384⟩
    (by decide) selected_cut_18551

theorem unmarked_context_12_71732_474998 : frontier 9 ⟨474998, by decide⟩
    (prefixCache 12 71732) (prefixPartial 12 71732) = false := by
  decide +kernel

theorem node_context_12_71732_474998 : EJMOriginalGlobalDAGData.nodes 9 ⟨474998, by decide⟩ =
    .split (coordinate 12) (![⟨474892, by decide⟩,⟨474943, by decide⟩,⟨474978, by decide⟩,⟨474997, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71732_474998 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71732 ⟨474998, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71732
    ⟨474998, by decide⟩ (by decide) (![⟨474892, by decide⟩,⟨474943, by decide⟩,⟨474978, by decide⟩,⟨474997, by decide⟩]) unmarked_context_12_71732_474998 node_context_12_71732_474998
  intro a
  fin_cases a
  · exact context_13_286928_474892
  · exact context_13_286929_474943
  · exact context_13_286930_474978
  · exact context_13_286931_474997

theorem selected_cut_18552 : selected 8 ⟨475006, by decide⟩
    (prefixPartial 13 286932) = some ⟨13, 2, 0, 475006, 286932, 389, 16384⟩ := by
  decide +kernel

theorem context_13_286932_475006 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286932 ⟨475006, by decide⟩ :=
  accepted_of_selected 13 286932 ⟨475006, by decide⟩ ⟨13, 2, 0, 475006, 286932, 389, 16384⟩
    (by decide) selected_cut_18552

theorem selected_cut_18553 : selected 8 ⟨475033, by decide⟩
    (prefixPartial 13 286933) = some ⟨13, 2, 0, 475033, 286933, 2189, 16384⟩ := by
  decide +kernel

theorem context_13_286933_475033 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286933 ⟨475033, by decide⟩ :=
  accepted_of_selected 13 286933 ⟨475033, by decide⟩ ⟨13, 2, 0, 475033, 286933, 2189, 16384⟩
    (by decide) selected_cut_18553

theorem selected_cut_18554 : selected 8 ⟨475054, by decide⟩
    (prefixPartial 13 286934) = some ⟨13, 2, 0, 475054, 286934, 1357, 16384⟩ := by
  decide +kernel

theorem context_13_286934_475054 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286934 ⟨475054, by decide⟩ :=
  accepted_of_selected 13 286934 ⟨475054, by decide⟩ ⟨13, 2, 0, 475054, 286934, 1357, 16384⟩
    (by decide) selected_cut_18554

theorem selected_cut_18555 : selected 8 ⟨475062, by decide⟩
    (prefixPartial 13 286935) = some ⟨13, 2, 0, 475062, 286935, 853, 16384⟩ := by
  decide +kernel

theorem context_13_286935_475062 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286935 ⟨475062, by decide⟩ :=
  accepted_of_selected 13 286935 ⟨475062, by decide⟩ ⟨13, 2, 0, 475062, 286935, 853, 16384⟩
    (by decide) selected_cut_18555

theorem unmarked_context_12_71733_475063 : frontier 9 ⟨475063, by decide⟩
    (prefixCache 12 71733) (prefixPartial 12 71733) = false := by
  decide +kernel

theorem node_context_12_71733_475063 : EJMOriginalGlobalDAGData.nodes 9 ⟨475063, by decide⟩ =
    .split (coordinate 12) (![⟨475006, by decide⟩,⟨475033, by decide⟩,⟨475054, by decide⟩,⟨475062, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71733_475063 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71733 ⟨475063, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71733
    ⟨475063, by decide⟩ (by decide) (![⟨475006, by decide⟩,⟨475033, by decide⟩,⟨475054, by decide⟩,⟨475062, by decide⟩]) unmarked_context_12_71733_475063 node_context_12_71733_475063
  intro a
  fin_cases a
  · exact context_13_286932_475006
  · exact context_13_286933_475033
  · exact context_13_286934_475054
  · exact context_13_286935_475062

theorem selected_cut_18556 : selected 8 ⟨475073, by decide⟩
    (prefixPartial 13 286936) = some ⟨13, 2, 0, 475073, 286936, 441, 16384⟩ := by
  decide +kernel

theorem context_13_286936_475073 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286936 ⟨475073, by decide⟩ :=
  accepted_of_selected 13 286936 ⟨475073, by decide⟩ ⟨13, 2, 0, 475073, 286936, 441, 16384⟩
    (by decide) selected_cut_18556

theorem selected_cut_18557 : selected 8 ⟨475105, by decide⟩
    (prefixPartial 13 286937) = some ⟨13, 2, 0, 475105, 286937, 2673, 16384⟩ := by
  decide +kernel

theorem context_13_286937_475105 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286937 ⟨475105, by decide⟩ :=
  accepted_of_selected 13 286937 ⟨475105, by decide⟩ ⟨13, 2, 0, 475105, 286937, 2673, 16384⟩
    (by decide) selected_cut_18557

theorem selected_cut_18558 : selected 8 ⟨475128, by decide⟩
    (prefixPartial 13 286938) = some ⟨13, 2, 0, 475128, 286938, 1641, 16384⟩ := by
  decide +kernel

theorem context_13_286938_475128 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286938 ⟨475128, by decide⟩ :=
  accepted_of_selected 13 286938 ⟨475128, by decide⟩ ⟨13, 2, 0, 475128, 286938, 1641, 16384⟩
    (by decide) selected_cut_18558

theorem selected_cut_18559 : selected 8 ⟨475133, by decide⟩
    (prefixPartial 13 286939) = some ⟨13, 2, 0, 475133, 286939, 849, 16384⟩ := by
  decide +kernel

theorem context_13_286939_475133 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286939 ⟨475133, by decide⟩ :=
  accepted_of_selected 13 286939 ⟨475133, by decide⟩ ⟨13, 2, 0, 475133, 286939, 849, 16384⟩
    (by decide) selected_cut_18559

theorem unmarked_context_12_71734_475134 : frontier 9 ⟨475134, by decide⟩
    (prefixCache 12 71734) (prefixPartial 12 71734) = false := by
  decide +kernel

theorem node_context_12_71734_475134 : EJMOriginalGlobalDAGData.nodes 9 ⟨475134, by decide⟩ =
    .split (coordinate 12) (![⟨475073, by decide⟩,⟨475105, by decide⟩,⟨475128, by decide⟩,⟨475133, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71734_475134 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71734 ⟨475134, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71734
    ⟨475134, by decide⟩ (by decide) (![⟨475073, by decide⟩,⟨475105, by decide⟩,⟨475128, by decide⟩,⟨475133, by decide⟩]) unmarked_context_12_71734_475134 node_context_12_71734_475134
  intro a
  fin_cases a
  · exact context_13_286936_475073
  · exact context_13_286937_475105
  · exact context_13_286938_475128
  · exact context_13_286939_475133

theorem selected_cut_18560 : selected 8 ⟨475140, by decide⟩
    (prefixPartial 13 286940) = some ⟨13, 2, 0, 475140, 286940, 389, 16384⟩ := by
  decide +kernel

theorem context_13_286940_475140 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286940 ⟨475140, by decide⟩ :=
  accepted_of_selected 13 286940 ⟨475140, by decide⟩ ⟨13, 2, 0, 475140, 286940, 389, 16384⟩
    (by decide) selected_cut_18560

theorem selected_cut_18561 : selected 8 ⟨475191, by decide⟩
    (prefixPartial 13 286941) = some ⟨13, 2, 0, 475191, 286941, 2833, 16384⟩ := by
  decide +kernel

theorem context_13_286941_475191 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286941 ⟨475191, by decide⟩ :=
  accepted_of_selected 13 286941 ⟨475191, by decide⟩ ⟨13, 2, 0, 475191, 286941, 2833, 16384⟩
    (by decide) selected_cut_18561

theorem selected_cut_18562 : selected 8 ⟨475213, by decide⟩
    (prefixPartial 13 286942) = some ⟨13, 2, 0, 475213, 286942, 1673, 16384⟩ := by
  decide +kernel

theorem context_13_286942_475213 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286942 ⟨475213, by decide⟩ :=
  accepted_of_selected 13 286942 ⟨475213, by decide⟩ ⟨13, 2, 0, 475213, 286942, 1673, 16384⟩
    (by decide) selected_cut_18562

theorem selected_cut_18563 : selected 8 ⟨475217, by decide⟩
    (prefixPartial 13 286943) = some ⟨13, 2, 0, 475217, 286943, 757, 16384⟩ := by
  decide +kernel

theorem context_13_286943_475217 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286943 ⟨475217, by decide⟩ :=
  accepted_of_selected 13 286943 ⟨475217, by decide⟩ ⟨13, 2, 0, 475217, 286943, 757, 16384⟩
    (by decide) selected_cut_18563

theorem unmarked_context_12_71735_475218 : frontier 9 ⟨475218, by decide⟩
    (prefixCache 12 71735) (prefixPartial 12 71735) = false := by
  decide +kernel

theorem node_context_12_71735_475218 : EJMOriginalGlobalDAGData.nodes 9 ⟨475218, by decide⟩ =
    .split (coordinate 12) (![⟨475140, by decide⟩,⟨475191, by decide⟩,⟨475213, by decide⟩,⟨475217, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71735_475218 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71735 ⟨475218, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71735
    ⟨475218, by decide⟩ (by decide) (![⟨475140, by decide⟩,⟨475191, by decide⟩,⟨475213, by decide⟩,⟨475217, by decide⟩]) unmarked_context_12_71735_475218 node_context_12_71735_475218
  intro a
  fin_cases a
  · exact context_13_286940_475140
  · exact context_13_286941_475191
  · exact context_13_286942_475213
  · exact context_13_286943_475217

theorem unmarked_context_11_17933_475219 : frontier 10 ⟨475219, by decide⟩
    (prefixCache 11 17933) (prefixPartial 11 17933) = false := by
  decide +kernel

theorem node_context_11_17933_475219 : EJMOriginalGlobalDAGData.nodes 10 ⟨475219, by decide⟩ =
    .split (coordinate 11) (![⟨474998, by decide⟩,⟨475063, by decide⟩,⟨475134, by decide⟩,⟨475218, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17933_475219 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17933 ⟨475219, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17933
    ⟨475219, by decide⟩ (by decide) (![⟨474998, by decide⟩,⟨475063, by decide⟩,⟨475134, by decide⟩,⟨475218, by decide⟩]) unmarked_context_11_17933_475219 node_context_11_17933_475219
  intro a
  fin_cases a
  · exact context_12_71732_474998
  · exact context_12_71733_475063
  · exact context_12_71734_475134
  · exact context_12_71735_475218

theorem selected_cut_18564 : selected 8 ⟨475228, by decide⟩
    (prefixPartial 13 286944) = some ⟨13, 2, 0, 475228, 286944, 345, 16384⟩ := by
  decide +kernel

theorem context_13_286944_475228 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286944 ⟨475228, by decide⟩ :=
  accepted_of_selected 13 286944 ⟨475228, by decide⟩ ⟨13, 2, 0, 475228, 286944, 345, 16384⟩
    (by decide) selected_cut_18564

theorem selected_cut_18565 : selected 8 ⟨475275, by decide⟩
    (prefixPartial 13 286945) = some ⟨13, 2, 0, 475275, 286945, 3005, 16384⟩ := by
  decide +kernel

theorem context_13_286945_475275 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286945 ⟨475275, by decide⟩ :=
  accepted_of_selected 13 286945 ⟨475275, by decide⟩ ⟨13, 2, 0, 475275, 286945, 3005, 16384⟩
    (by decide) selected_cut_18565

theorem selected_cut_18566 : selected 8 ⟨475317, by decide⟩
    (prefixPartial 13 286946) = some ⟨13, 2, 0, 475317, 286946, 2101, 16384⟩ := by
  decide +kernel

theorem context_13_286946_475317 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286946 ⟨475317, by decide⟩ :=
  accepted_of_selected 13 286946 ⟨475317, by decide⟩ ⟨13, 2, 0, 475317, 286946, 2101, 16384⟩
    (by decide) selected_cut_18566

theorem selected_cut_18567 : selected 8 ⟨475325, by decide⟩
    (prefixPartial 13 286947) = some ⟨13, 2, 0, 475325, 286947, 1037, 16384⟩ := by
  decide +kernel

theorem context_13_286947_475325 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286947 ⟨475325, by decide⟩ :=
  accepted_of_selected 13 286947 ⟨475325, by decide⟩ ⟨13, 2, 0, 475325, 286947, 1037, 16384⟩
    (by decide) selected_cut_18567

theorem unmarked_context_12_71736_475326 : frontier 9 ⟨475326, by decide⟩
    (prefixCache 12 71736) (prefixPartial 12 71736) = false := by
  decide +kernel

theorem node_context_12_71736_475326 : EJMOriginalGlobalDAGData.nodes 9 ⟨475326, by decide⟩ =
    .split (coordinate 12) (![⟨475228, by decide⟩,⟨475275, by decide⟩,⟨475317, by decide⟩,⟨475325, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71736_475326 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71736 ⟨475326, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71736
    ⟨475326, by decide⟩ (by decide) (![⟨475228, by decide⟩,⟨475275, by decide⟩,⟨475317, by decide⟩,⟨475325, by decide⟩]) unmarked_context_12_71736_475326 node_context_12_71736_475326
  intro a
  fin_cases a
  · exact context_13_286944_475228
  · exact context_13_286945_475275
  · exact context_13_286946_475317
  · exact context_13_286947_475325

theorem selected_cut_18568 : selected 8 ⟨475334, by decide⟩
    (prefixPartial 13 286948) = some ⟨13, 2, 0, 475334, 286948, 221, 16384⟩ := by
  decide +kernel

theorem context_13_286948_475334 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286948 ⟨475334, by decide⟩ :=
  accepted_of_selected 13 286948 ⟨475334, by decide⟩ ⟨13, 2, 0, 475334, 286948, 221, 16384⟩
    (by decide) selected_cut_18568

theorem selected_cut_18569 : selected 8 ⟨475368, by decide⟩
    (prefixPartial 13 286949) = some ⟨13, 2, 0, 475368, 286949, 2417, 16384⟩ := by
  decide +kernel

theorem context_13_286949_475368 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286949 ⟨475368, by decide⟩ :=
  accepted_of_selected 13 286949 ⟨475368, by decide⟩ ⟨13, 2, 0, 475368, 286949, 2417, 16384⟩
    (by decide) selected_cut_18569

theorem selected_cut_18570 : selected 8 ⟨475386, by decide⟩
    (prefixPartial 13 286950) = some ⟨13, 2, 0, 475386, 286950, 1545, 16384⟩ := by
  decide +kernel

theorem context_13_286950_475386 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286950 ⟨475386, by decide⟩ :=
  accepted_of_selected 13 286950 ⟨475386, by decide⟩ ⟨13, 2, 0, 475386, 286950, 1545, 16384⟩
    (by decide) selected_cut_18570

theorem selected_cut_18571 : selected 8 ⟨475390, by decide⟩
    (prefixPartial 13 286951) = some ⟨13, 2, 0, 475390, 286951, 925, 16384⟩ := by
  decide +kernel

theorem context_13_286951_475390 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286951 ⟨475390, by decide⟩ :=
  accepted_of_selected 13 286951 ⟨475390, by decide⟩ ⟨13, 2, 0, 475390, 286951, 925, 16384⟩
    (by decide) selected_cut_18571

theorem unmarked_context_12_71737_475391 : frontier 9 ⟨475391, by decide⟩
    (prefixCache 12 71737) (prefixPartial 12 71737) = false := by
  decide +kernel

theorem node_context_12_71737_475391 : EJMOriginalGlobalDAGData.nodes 9 ⟨475391, by decide⟩ =
    .split (coordinate 12) (![⟨475334, by decide⟩,⟨475368, by decide⟩,⟨475386, by decide⟩,⟨475390, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71737_475391 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71737 ⟨475391, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71737
    ⟨475391, by decide⟩ (by decide) (![⟨475334, by decide⟩,⟨475368, by decide⟩,⟨475386, by decide⟩,⟨475390, by decide⟩]) unmarked_context_12_71737_475391 node_context_12_71737_475391
  intro a
  fin_cases a
  · exact context_13_286948_475334
  · exact context_13_286949_475368
  · exact context_13_286950_475386
  · exact context_13_286951_475390

theorem selected_cut_18572 : selected 8 ⟨475395, by decide⟩
    (prefixPartial 13 286952) = some ⟨13, 2, 0, 475395, 286952, 161, 16384⟩ := by
  decide +kernel

theorem context_13_286952_475395 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286952 ⟨475395, by decide⟩ :=
  accepted_of_selected 13 286952 ⟨475395, by decide⟩ ⟨13, 2, 0, 475395, 286952, 161, 16384⟩
    (by decide) selected_cut_18572

theorem selected_cut_18573 : selected 8 ⟨475430, by decide⟩
    (prefixPartial 13 286953) = some ⟨13, 2, 0, 475430, 286953, 2457, 16384⟩ := by
  decide +kernel

theorem context_13_286953_475430 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286953 ⟨475430, by decide⟩ :=
  accepted_of_selected 13 286953 ⟨475430, by decide⟩ ⟨13, 2, 0, 475430, 286953, 2457, 16384⟩
    (by decide) selected_cut_18573

theorem selected_cut_18574 : selected 8 ⟨475448, by decide⟩
    (prefixPartial 13 286954) = some ⟨13, 2, 0, 475448, 286954, 1541, 16384⟩ := by
  decide +kernel

theorem context_13_286954_475448 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286954 ⟨475448, by decide⟩ :=
  accepted_of_selected 13 286954 ⟨475448, by decide⟩ ⟨13, 2, 0, 475448, 286954, 1541, 16384⟩
    (by decide) selected_cut_18574

theorem selected_cut_18575 : selected 8 ⟨475454, by decide⟩
    (prefixPartial 13 286955) = some ⟨13, 2, 0, 475454, 286955, 877, 16384⟩ := by
  decide +kernel

theorem context_13_286955_475454 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286955 ⟨475454, by decide⟩ :=
  accepted_of_selected 13 286955 ⟨475454, by decide⟩ ⟨13, 2, 0, 475454, 286955, 877, 16384⟩
    (by decide) selected_cut_18575

theorem unmarked_context_12_71738_475455 : frontier 9 ⟨475455, by decide⟩
    (prefixCache 12 71738) (prefixPartial 12 71738) = false := by
  decide +kernel

theorem node_context_12_71738_475455 : EJMOriginalGlobalDAGData.nodes 9 ⟨475455, by decide⟩ =
    .split (coordinate 12) (![⟨475395, by decide⟩,⟨475430, by decide⟩,⟨475448, by decide⟩,⟨475454, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71738_475455 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71738 ⟨475455, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71738
    ⟨475455, by decide⟩ (by decide) (![⟨475395, by decide⟩,⟨475430, by decide⟩,⟨475448, by decide⟩,⟨475454, by decide⟩]) unmarked_context_12_71738_475455 node_context_12_71738_475455
  intro a
  fin_cases a
  · exact context_13_286952_475395
  · exact context_13_286953_475430
  · exact context_13_286954_475448
  · exact context_13_286955_475454

theorem selected_cut_18576 : selected 8 ⟨475460, by decide⟩
    (prefixPartial 13 286956) = some ⟨13, 2, 0, 475460, 286956, 181, 16384⟩ := by
  decide +kernel

theorem context_13_286956_475460 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286956 ⟨475460, by decide⟩ :=
  accepted_of_selected 13 286956 ⟨475460, by decide⟩ ⟨13, 2, 0, 475460, 286956, 181, 16384⟩
    (by decide) selected_cut_18576

theorem selected_cut_18577 : selected 8 ⟨475501, by decide⟩
    (prefixPartial 13 286957) = some ⟨13, 2, 0, 475501, 286957, 2813, 16384⟩ := by
  decide +kernel

theorem context_13_286957_475501 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286957 ⟨475501, by decide⟩ :=
  accepted_of_selected 13 286957 ⟨475501, by decide⟩ ⟨13, 2, 0, 475501, 286957, 2813, 16384⟩
    (by decide) selected_cut_18577

theorem selected_cut_18578 : selected 8 ⟨475523, by decide⟩
    (prefixPartial 13 286958) = some ⟨13, 2, 0, 475523, 286958, 1617, 16384⟩ := by
  decide +kernel

theorem context_13_286958_475523 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286958 ⟨475523, by decide⟩ :=
  accepted_of_selected 13 286958 ⟨475523, by decide⟩ ⟨13, 2, 0, 475523, 286958, 1617, 16384⟩
    (by decide) selected_cut_18578

theorem selected_cut_18579 : selected 8 ⟨475530, by decide⟩
    (prefixPartial 13 286959) = some ⟨13, 2, 0, 475530, 286959, 801, 16384⟩ := by
  decide +kernel

theorem context_13_286959_475530 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286959 ⟨475530, by decide⟩ :=
  accepted_of_selected 13 286959 ⟨475530, by decide⟩ ⟨13, 2, 0, 475530, 286959, 801, 16384⟩
    (by decide) selected_cut_18579

theorem unmarked_context_12_71739_475531 : frontier 9 ⟨475531, by decide⟩
    (prefixCache 12 71739) (prefixPartial 12 71739) = false := by
  decide +kernel

theorem node_context_12_71739_475531 : EJMOriginalGlobalDAGData.nodes 9 ⟨475531, by decide⟩ =
    .split (coordinate 12) (![⟨475460, by decide⟩,⟨475501, by decide⟩,⟨475523, by decide⟩,⟨475530, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71739_475531 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71739 ⟨475531, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71739
    ⟨475531, by decide⟩ (by decide) (![⟨475460, by decide⟩,⟨475501, by decide⟩,⟨475523, by decide⟩,⟨475530, by decide⟩]) unmarked_context_12_71739_475531 node_context_12_71739_475531
  intro a
  fin_cases a
  · exact context_13_286956_475460
  · exact context_13_286957_475501
  · exact context_13_286958_475523
  · exact context_13_286959_475530

theorem unmarked_context_11_17934_475532 : frontier 10 ⟨475532, by decide⟩
    (prefixCache 11 17934) (prefixPartial 11 17934) = false := by
  decide +kernel

theorem node_context_11_17934_475532 : EJMOriginalGlobalDAGData.nodes 10 ⟨475532, by decide⟩ =
    .split (coordinate 11) (![⟨475326, by decide⟩,⟨475391, by decide⟩,⟨475455, by decide⟩,⟨475531, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17934_475532 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17934 ⟨475532, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17934
    ⟨475532, by decide⟩ (by decide) (![⟨475326, by decide⟩,⟨475391, by decide⟩,⟨475455, by decide⟩,⟨475531, by decide⟩]) unmarked_context_11_17934_475532 node_context_11_17934_475532
  intro a
  fin_cases a
  · exact context_12_71736_475326
  · exact context_12_71737_475391
  · exact context_12_71738_475455
  · exact context_12_71739_475531

theorem selected_cut_18580 : selected 9 ⟨475533, by decide⟩
    (prefixPartial 12 71740) = some ⟨12, 1, 0, 475533, 71740, 1, 65536⟩ := by
  decide +kernel

theorem context_12_71740_475533 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71740 ⟨475533, by decide⟩ :=
  accepted_of_selected 12 71740 ⟨475533, by decide⟩ ⟨12, 1, 0, 475533, 71740, 1, 65536⟩
    (by decide) selected_cut_18580

theorem selected_cut_18581 : selected 8 ⟨475537, by decide⟩
    (prefixPartial 13 286964) = some ⟨13, 2, 0, 475537, 286964, 125, 16384⟩ := by
  decide +kernel

theorem context_13_286964_475537 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286964 ⟨475537, by decide⟩ :=
  accepted_of_selected 13 286964 ⟨475537, by decide⟩ ⟨13, 2, 0, 475537, 286964, 125, 16384⟩
    (by decide) selected_cut_18581

theorem selected_cut_18582 : selected 8 ⟨475567, by decide⟩
    (prefixPartial 13 286965) = some ⟨13, 2, 0, 475567, 286965, 2505, 16384⟩ := by
  decide +kernel

theorem context_13_286965_475567 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286965 ⟨475567, by decide⟩ :=
  accepted_of_selected 13 286965 ⟨475567, by decide⟩ ⟨13, 2, 0, 475567, 286965, 2505, 16384⟩
    (by decide) selected_cut_18582

theorem selected_cut_18583 : selected 8 ⟨475589, by decide⟩
    (prefixPartial 13 286966) = some ⟨13, 2, 0, 475589, 286966, 1669, 16384⟩ := by
  decide +kernel

theorem context_13_286966_475589 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286966 ⟨475589, by decide⟩ :=
  accepted_of_selected 13 286966 ⟨475589, by decide⟩ ⟨13, 2, 0, 475589, 286966, 1669, 16384⟩
    (by decide) selected_cut_18583

theorem selected_cut_18584 : selected 8 ⟨475594, by decide⟩
    (prefixPartial 13 286967) = some ⟨13, 2, 0, 475594, 286967, 933, 16384⟩ := by
  decide +kernel

theorem context_13_286967_475594 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286967 ⟨475594, by decide⟩ :=
  accepted_of_selected 13 286967 ⟨475594, by decide⟩ ⟨13, 2, 0, 475594, 286967, 933, 16384⟩
    (by decide) selected_cut_18584

theorem unmarked_context_12_71741_475595 : frontier 9 ⟨475595, by decide⟩
    (prefixCache 12 71741) (prefixPartial 12 71741) = false := by
  decide +kernel

theorem node_context_12_71741_475595 : EJMOriginalGlobalDAGData.nodes 9 ⟨475595, by decide⟩ =
    .split (coordinate 12) (![⟨475537, by decide⟩,⟨475567, by decide⟩,⟨475589, by decide⟩,⟨475594, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71741_475595 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71741 ⟨475595, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71741
    ⟨475595, by decide⟩ (by decide) (![⟨475537, by decide⟩,⟨475567, by decide⟩,⟨475589, by decide⟩,⟨475594, by decide⟩]) unmarked_context_12_71741_475595 node_context_12_71741_475595
  intro a
  fin_cases a
  · exact context_13_286964_475537
  · exact context_13_286965_475567
  · exact context_13_286966_475589
  · exact context_13_286967_475594

theorem selected_cut_18585 : selected 8 ⟨475600, by decide⟩
    (prefixPartial 13 286968) = some ⟨13, 2, 0, 475600, 286968, 109, 16384⟩ := by
  decide +kernel

theorem context_13_286968_475600 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286968 ⟨475600, by decide⟩ :=
  accepted_of_selected 13 286968 ⟨475600, by decide⟩ ⟨13, 2, 0, 475600, 286968, 109, 16384⟩
    (by decide) selected_cut_18585

theorem selected_cut_18586 : selected 8 ⟨475629, by decide⟩
    (prefixPartial 13 286969) = some ⟨13, 2, 0, 475629, 286969, 2817, 16384⟩ := by
  decide +kernel

theorem context_13_286969_475629 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286969 ⟨475629, by decide⟩ :=
  accepted_of_selected 13 286969 ⟨475629, by decide⟩ ⟨13, 2, 0, 475629, 286969, 2817, 16384⟩
    (by decide) selected_cut_18586

theorem selected_cut_18587 : selected 8 ⟨475649, by decide⟩
    (prefixPartial 13 286970) = some ⟨13, 2, 0, 475649, 286970, 1821, 16384⟩ := by
  decide +kernel

theorem context_13_286970_475649 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286970 ⟨475649, by decide⟩ :=
  accepted_of_selected 13 286970 ⟨475649, by decide⟩ ⟨13, 2, 0, 475649, 286970, 1821, 16384⟩
    (by decide) selected_cut_18587

theorem selected_cut_18588 : selected 8 ⟨475655, by decide⟩
    (prefixPartial 13 286971) = some ⟨13, 2, 0, 475655, 286971, 857, 16384⟩ := by
  decide +kernel

theorem context_13_286971_475655 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286971 ⟨475655, by decide⟩ :=
  accepted_of_selected 13 286971 ⟨475655, by decide⟩ ⟨13, 2, 0, 475655, 286971, 857, 16384⟩
    (by decide) selected_cut_18588

theorem unmarked_context_12_71742_475656 : frontier 9 ⟨475656, by decide⟩
    (prefixCache 12 71742) (prefixPartial 12 71742) = false := by
  decide +kernel

theorem node_context_12_71742_475656 : EJMOriginalGlobalDAGData.nodes 9 ⟨475656, by decide⟩ =
    .split (coordinate 12) (![⟨475600, by decide⟩,⟨475629, by decide⟩,⟨475649, by decide⟩,⟨475655, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71742_475656 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71742 ⟨475656, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71742
    ⟨475656, by decide⟩ (by decide) (![⟨475600, by decide⟩,⟨475629, by decide⟩,⟨475649, by decide⟩,⟨475655, by decide⟩]) unmarked_context_12_71742_475656 node_context_12_71742_475656
  intro a
  fin_cases a
  · exact context_13_286968_475600
  · exact context_13_286969_475629
  · exact context_13_286970_475649
  · exact context_13_286971_475655

theorem selected_cut_18589 : selected 8 ⟨475660, by decide⟩
    (prefixPartial 13 286972) = some ⟨13, 2, 0, 475660, 286972, 49, 16384⟩ := by
  decide +kernel

theorem context_13_286972_475660 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286972 ⟨475660, by decide⟩ :=
  accepted_of_selected 13 286972 ⟨475660, by decide⟩ ⟨13, 2, 0, 475660, 286972, 49, 16384⟩
    (by decide) selected_cut_18589

theorem selected_cut_18590 : selected 8 ⟨475696, by decide⟩
    (prefixPartial 13 286973) = some ⟨13, 2, 0, 475696, 286973, 2725, 16384⟩ := by
  decide +kernel

theorem context_13_286973_475696 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286973 ⟨475696, by decide⟩ :=
  accepted_of_selected 13 286973 ⟨475696, by decide⟩ ⟨13, 2, 0, 475696, 286973, 2725, 16384⟩
    (by decide) selected_cut_18590

theorem selected_cut_18591 : selected 8 ⟨475714, by decide⟩
    (prefixPartial 13 286974) = some ⟨13, 2, 0, 475714, 286974, 1685, 16384⟩ := by
  decide +kernel

theorem context_13_286974_475714 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286974 ⟨475714, by decide⟩ :=
  accepted_of_selected 13 286974 ⟨475714, by decide⟩ ⟨13, 2, 0, 475714, 286974, 1685, 16384⟩
    (by decide) selected_cut_18591

theorem selected_cut_18592 : selected 8 ⟨475719, by decide⟩
    (prefixPartial 13 286975) = some ⟨13, 2, 0, 475719, 286975, 741, 16384⟩ := by
  decide +kernel

theorem context_13_286975_475719 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286975 ⟨475719, by decide⟩ :=
  accepted_of_selected 13 286975 ⟨475719, by decide⟩ ⟨13, 2, 0, 475719, 286975, 741, 16384⟩
    (by decide) selected_cut_18592

theorem unmarked_context_12_71743_475720 : frontier 9 ⟨475720, by decide⟩
    (prefixCache 12 71743) (prefixPartial 12 71743) = false := by
  decide +kernel

theorem node_context_12_71743_475720 : EJMOriginalGlobalDAGData.nodes 9 ⟨475720, by decide⟩ =
    .split (coordinate 12) (![⟨475660, by decide⟩,⟨475696, by decide⟩,⟨475714, by decide⟩,⟨475719, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71743_475720 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71743 ⟨475720, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71743
    ⟨475720, by decide⟩ (by decide) (![⟨475660, by decide⟩,⟨475696, by decide⟩,⟨475714, by decide⟩,⟨475719, by decide⟩]) unmarked_context_12_71743_475720 node_context_12_71743_475720
  intro a
  fin_cases a
  · exact context_13_286972_475660
  · exact context_13_286973_475696
  · exact context_13_286974_475714
  · exact context_13_286975_475719

theorem unmarked_context_11_17935_475721 : frontier 10 ⟨475721, by decide⟩
    (prefixCache 11 17935) (prefixPartial 11 17935) = false := by
  decide +kernel

theorem node_context_11_17935_475721 : EJMOriginalGlobalDAGData.nodes 10 ⟨475721, by decide⟩ =
    .split (coordinate 11) (![⟨475533, by decide⟩,⟨475595, by decide⟩,⟨475656, by decide⟩,⟨475720, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17935_475721 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17935 ⟨475721, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17935
    ⟨475721, by decide⟩ (by decide) (![⟨475533, by decide⟩,⟨475595, by decide⟩,⟨475656, by decide⟩,⟨475720, by decide⟩]) unmarked_context_11_17935_475721 node_context_11_17935_475721
  intro a
  fin_cases a
  · exact context_12_71740_475533
  · exact context_12_71741_475595
  · exact context_12_71742_475656
  · exact context_12_71743_475720

theorem unmarked_context_10_4483_475722 : frontier 11 ⟨475722, by decide⟩
    (prefixCache 10 4483) (prefixPartial 10 4483) = false := by
  decide +kernel

theorem node_context_10_4483_475722 : EJMOriginalGlobalDAGData.nodes 11 ⟨475722, by decide⟩ =
    .split (coordinate 10) (![⟨474877, by decide⟩,⟨475219, by decide⟩,⟨475532, by decide⟩,⟨475721, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4483_475722 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4483 ⟨475722, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4483
    ⟨475722, by decide⟩ (by decide) (![⟨474877, by decide⟩,⟨475219, by decide⟩,⟨475532, by decide⟩,⟨475721, by decide⟩]) unmarked_context_10_4483_475722 node_context_10_4483_475722
  intro a
  fin_cases a
  · exact context_11_17932_474877
  · exact context_11_17933_475219
  · exact context_11_17934_475532
  · exact context_11_17935_475721

theorem unmarked_context_9_1120_475723 : frontier 12 ⟨475723, by decide⟩
    (prefixCache 9 1120) (prefixPartial 9 1120) = false := by
  decide +kernel

theorem node_context_9_1120_475723 : EJMOriginalGlobalDAGData.nodes 12 ⟨475723, by decide⟩ =
    .split (coordinate 9) (![⟨471875, by decide⟩,⟨473506, by decide⟩,⟨474679, by decide⟩,⟨475722, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1120_475723 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1120 ⟨475723, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1120
    ⟨475723, by decide⟩ (by decide) (![⟨471875, by decide⟩,⟨473506, by decide⟩,⟨474679, by decide⟩,⟨475722, by decide⟩]) unmarked_context_9_1120_475723 node_context_9_1120_475723
  intro a
  fin_cases a
  · exact context_10_4480_471875
  · exact context_10_4481_473506
  · exact context_10_4482_474679
  · exact context_10_4483_475722

theorem selected_cut_18593 : selected 9 ⟨450982, by decide⟩
    (prefixPartial 12 71744) = some ⟨12, 1, 0, 450982, 71744, 1, 65536⟩ := by
  decide +kernel

theorem context_12_71744_450982 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71744 ⟨450982, by decide⟩ :=
  accepted_of_selected 12 71744 ⟨450982, by decide⟩ ⟨12, 1, 0, 450982, 71744, 1, 65536⟩
    (by decide) selected_cut_18593

theorem selected_cut_18594 : selected 9 ⟨475768, by decide⟩
    (prefixPartial 12 71745) = some ⟨12, 2, 0, 475768, 71745, 3117, 65536⟩ := by
  decide +kernel

theorem context_12_71745_475768 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71745 ⟨475768, by decide⟩ :=
  accepted_of_selected 12 71745 ⟨475768, by decide⟩ ⟨12, 2, 0, 475768, 71745, 3117, 65536⟩
    (by decide) selected_cut_18594

theorem selected_cut_18595 : selected 9 ⟨475821, by decide⟩
    (prefixPartial 12 71746) = some ⟨12, 2, 0, 475821, 71746, 3753, 65536⟩ := by
  decide +kernel

theorem context_12_71746_475821 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71746 ⟨475821, by decide⟩ :=
  accepted_of_selected 12 71746 ⟨475821, by decide⟩ ⟨12, 2, 0, 475821, 71746, 3753, 65536⟩
    (by decide) selected_cut_18595

theorem selected_cut_18596 : selected 9 ⟨475873, by decide⟩
    (prefixPartial 12 71747) = some ⟨12, 2, 0, 475873, 71747, 3801, 65536⟩ := by
  decide +kernel

theorem context_12_71747_475873 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71747 ⟨475873, by decide⟩ :=
  accepted_of_selected 12 71747 ⟨475873, by decide⟩ ⟨12, 2, 0, 475873, 71747, 3801, 65536⟩
    (by decide) selected_cut_18596

theorem unmarked_context_11_17936_475874 : frontier 10 ⟨475874, by decide⟩
    (prefixCache 11 17936) (prefixPartial 11 17936) = false := by
  decide +kernel

theorem node_context_11_17936_475874 : EJMOriginalGlobalDAGData.nodes 10 ⟨475874, by decide⟩ =
    .split (coordinate 11) (![⟨450982, by decide⟩,⟨475768, by decide⟩,⟨475821, by decide⟩,⟨475873, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17936_475874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17936 ⟨475874, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17936
    ⟨475874, by decide⟩ (by decide) (![⟨450982, by decide⟩,⟨475768, by decide⟩,⟨475821, by decide⟩,⟨475873, by decide⟩]) unmarked_context_11_17936_475874 node_context_11_17936_475874
  intro a
  fin_cases a
  · exact context_12_71744_450982
  · exact context_12_71745_475768
  · exact context_12_71746_475821
  · exact context_12_71747_475873

theorem selected_cut_18597 : selected 9 ⟨475926, by decide⟩
    (prefixPartial 12 71748) = some ⟨12, 2, 0, 475926, 71748, 3389, 65536⟩ := by
  decide +kernel

theorem context_12_71748_475926 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71748 ⟨475926, by decide⟩ :=
  accepted_of_selected 12 71748 ⟨475926, by decide⟩ ⟨12, 2, 0, 475926, 71748, 3389, 65536⟩
    (by decide) selected_cut_18597

theorem selected_cut_18598 : selected 9 ⟨475972, by decide⟩
    (prefixPartial 12 71749) = some ⟨12, 2, 0, 475972, 71749, 3353, 65536⟩ := by
  decide +kernel

theorem context_12_71749_475972 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71749 ⟨475972, by decide⟩ :=
  accepted_of_selected 12 71749 ⟨475972, by decide⟩ ⟨12, 2, 0, 475972, 71749, 3353, 65536⟩
    (by decide) selected_cut_18598

theorem selected_cut_18599 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 287000) = some ⟨13, 1, 0, 3444, 287000, 1, 16384⟩ := by
  decide +kernel

theorem context_13_287000_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287000 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 287000 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 287000, 1, 16384⟩
    (by decide) selected_cut_18599

theorem selected_cut_18600 : selected 8 ⟨476003, by decide⟩
    (prefixPartial 13 287001) = some ⟨13, 2, 0, 476003, 287001, 2101, 16384⟩ := by
  decide +kernel

theorem context_13_287001_476003 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287001 ⟨476003, by decide⟩ :=
  accepted_of_selected 13 287001 ⟨476003, by decide⟩ ⟨13, 2, 0, 476003, 287001, 2101, 16384⟩
    (by decide) selected_cut_18600

theorem selected_cut_18601 : selected 8 ⟨476024, by decide⟩
    (prefixPartial 13 287002) = some ⟨13, 2, 0, 476024, 287002, 1353, 16384⟩ := by
  decide +kernel

theorem context_13_287002_476024 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287002 ⟨476024, by decide⟩ :=
  accepted_of_selected 13 287002 ⟨476024, by decide⟩ ⟨13, 2, 0, 476024, 287002, 1353, 16384⟩
    (by decide) selected_cut_18601

theorem selected_cut_18602 : selected 8 ⟨476031, by decide⟩
    (prefixPartial 13 287003) = some ⟨13, 2, 0, 476031, 287003, 777, 16384⟩ := by
  decide +kernel

theorem context_13_287003_476031 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287003 ⟨476031, by decide⟩ :=
  accepted_of_selected 13 287003 ⟨476031, by decide⟩ ⟨13, 2, 0, 476031, 287003, 777, 16384⟩
    (by decide) selected_cut_18602

theorem unmarked_context_12_71750_476032 : frontier 9 ⟨476032, by decide⟩
    (prefixCache 12 71750) (prefixPartial 12 71750) = false := by
  decide +kernel

theorem node_context_12_71750_476032 : EJMOriginalGlobalDAGData.nodes 9 ⟨476032, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨476003, by decide⟩,⟨476024, by decide⟩,⟨476031, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71750_476032 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71750 ⟨476032, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71750
    ⟨476032, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨476003, by decide⟩,⟨476024, by decide⟩,⟨476031, by decide⟩]) unmarked_context_12_71750_476032 node_context_12_71750_476032
  intro a
  fin_cases a
  · exact context_13_287000_3444
  · exact context_13_287001_476003
  · exact context_13_287002_476024
  · exact context_13_287003_476031

theorem selected_cut_18603 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 287004) = some ⟨13, 1, 0, 3444, 287004, 1, 16384⟩ := by
  decide +kernel

theorem context_13_287004_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287004 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 287004 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 287004, 1, 16384⟩
    (by decide) selected_cut_18603

theorem selected_cut_18604 : selected 8 ⟨476068, by decide⟩
    (prefixPartial 13 287005) = some ⟨13, 2, 0, 476068, 287005, 2165, 16384⟩ := by
  decide +kernel

theorem context_13_287005_476068 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287005 ⟨476068, by decide⟩ :=
  accepted_of_selected 13 287005 ⟨476068, by decide⟩ ⟨13, 2, 0, 476068, 287005, 2165, 16384⟩
    (by decide) selected_cut_18604

theorem selected_cut_18605 : selected 8 ⟨476092, by decide⟩
    (prefixPartial 13 287006) = some ⟨13, 2, 0, 476092, 287006, 1413, 16384⟩ := by
  decide +kernel

theorem context_13_287006_476092 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287006 ⟨476092, by decide⟩ :=
  accepted_of_selected 13 287006 ⟨476092, by decide⟩ ⟨13, 2, 0, 476092, 287006, 1413, 16384⟩
    (by decide) selected_cut_18605

theorem selected_cut_18606 : selected 8 ⟨476098, by decide⟩
    (prefixPartial 13 287007) = some ⟨13, 2, 0, 476098, 287007, 737, 16384⟩ := by
  decide +kernel

theorem context_13_287007_476098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287007 ⟨476098, by decide⟩ :=
  accepted_of_selected 13 287007 ⟨476098, by decide⟩ ⟨13, 2, 0, 476098, 287007, 737, 16384⟩
    (by decide) selected_cut_18606

theorem unmarked_context_12_71751_476099 : frontier 9 ⟨476099, by decide⟩
    (prefixCache 12 71751) (prefixPartial 12 71751) = false := by
  decide +kernel

theorem node_context_12_71751_476099 : EJMOriginalGlobalDAGData.nodes 9 ⟨476099, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨476068, by decide⟩,⟨476092, by decide⟩,⟨476098, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71751_476099 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71751 ⟨476099, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71751
    ⟨476099, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨476068, by decide⟩,⟨476092, by decide⟩,⟨476098, by decide⟩]) unmarked_context_12_71751_476099 node_context_12_71751_476099
  intro a
  fin_cases a
  · exact context_13_287004_3444
  · exact context_13_287005_476068
  · exact context_13_287006_476092
  · exact context_13_287007_476098

theorem unmarked_context_11_17937_476100 : frontier 10 ⟨476100, by decide⟩
    (prefixCache 11 17937) (prefixPartial 11 17937) = false := by
  decide +kernel

theorem node_context_11_17937_476100 : EJMOriginalGlobalDAGData.nodes 10 ⟨476100, by decide⟩ =
    .split (coordinate 11) (![⟨475926, by decide⟩,⟨475972, by decide⟩,⟨476032, by decide⟩,⟨476099, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17937_476100 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17937 ⟨476100, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17937
    ⟨476100, by decide⟩ (by decide) (![⟨475926, by decide⟩,⟨475972, by decide⟩,⟨476032, by decide⟩,⟨476099, by decide⟩]) unmarked_context_11_17937_476100 node_context_11_17937_476100
  intro a
  fin_cases a
  · exact context_12_71748_475926
  · exact context_12_71749_475972
  · exact context_12_71750_476032
  · exact context_12_71751_476099

theorem selected_cut_18607 : selected 9 ⟨476143, by decide⟩
    (prefixPartial 12 71752) = some ⟨12, 2, 0, 476143, 71752, 3089, 65536⟩ := by
  decide +kernel

theorem context_12_71752_476143 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71752 ⟨476143, by decide⟩ :=
  accepted_of_selected 12 71752 ⟨476143, by decide⟩ ⟨12, 2, 0, 476143, 71752, 3089, 65536⟩
    (by decide) selected_cut_18607

theorem selected_cut_18608 : selected 9 ⟨476193, by decide⟩
    (prefixPartial 12 71753) = some ⟨12, 2, 0, 476193, 71753, 3365, 65536⟩ := by
  decide +kernel

theorem context_12_71753_476193 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71753 ⟨476193, by decide⟩ :=
  accepted_of_selected 12 71753 ⟨476193, by decide⟩ ⟨12, 2, 0, 476193, 71753, 3365, 65536⟩
    (by decide) selected_cut_18608

theorem selected_cut_18609 : selected 9 ⟨476246, by decide⟩
    (prefixPartial 12 71754) = some ⟨12, 2, 0, 476246, 71754, 3681, 65536⟩ := by
  decide +kernel

theorem context_12_71754_476246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71754 ⟨476246, by decide⟩ :=
  accepted_of_selected 12 71754 ⟨476246, by decide⟩ ⟨12, 2, 0, 476246, 71754, 3681, 65536⟩
    (by decide) selected_cut_18609

theorem selected_cut_18610 : selected 9 ⟨476296, by decide⟩
    (prefixPartial 12 71755) = some ⟨12, 2, 0, 476296, 71755, 3941, 65536⟩ := by
  decide +kernel

theorem context_12_71755_476296 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71755 ⟨476296, by decide⟩ :=
  accepted_of_selected 12 71755 ⟨476296, by decide⟩ ⟨12, 2, 0, 476296, 71755, 3941, 65536⟩
    (by decide) selected_cut_18610

theorem unmarked_context_11_17938_476297 : frontier 10 ⟨476297, by decide⟩
    (prefixCache 11 17938) (prefixPartial 11 17938) = false := by
  decide +kernel

theorem node_context_11_17938_476297 : EJMOriginalGlobalDAGData.nodes 10 ⟨476297, by decide⟩ =
    .split (coordinate 11) (![⟨476143, by decide⟩,⟨476193, by decide⟩,⟨476246, by decide⟩,⟨476296, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17938_476297 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17938 ⟨476297, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17938
    ⟨476297, by decide⟩ (by decide) (![⟨476143, by decide⟩,⟨476193, by decide⟩,⟨476246, by decide⟩,⟨476296, by decide⟩]) unmarked_context_11_17938_476297 node_context_11_17938_476297
  intro a
  fin_cases a
  · exact context_12_71752_476143
  · exact context_12_71753_476193
  · exact context_12_71754_476246
  · exact context_12_71755_476296

theorem selected_cut_18611 : selected 9 ⟨476341, by decide⟩
    (prefixPartial 12 71756) = some ⟨12, 2, 0, 476341, 71756, 3305, 65536⟩ := by
  decide +kernel

theorem context_12_71756_476341 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71756 ⟨476341, by decide⟩ :=
  accepted_of_selected 12 71756 ⟨476341, by decide⟩ ⟨12, 2, 0, 476341, 71756, 3305, 65536⟩
    (by decide) selected_cut_18611

theorem selected_cut_18612 : selected 9 ⟨476383, by decide⟩
    (prefixPartial 12 71757) = some ⟨12, 2, 0, 476383, 71757, 3693, 65536⟩ := by
  decide +kernel

theorem context_12_71757_476383 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71757 ⟨476383, by decide⟩ :=
  accepted_of_selected 12 71757 ⟨476383, by decide⟩ ⟨12, 2, 0, 476383, 71757, 3693, 65536⟩
    (by decide) selected_cut_18612

theorem selected_cut_18613 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 287032) = some ⟨13, 1, 0, 3444, 287032, 1, 16384⟩ := by
  decide +kernel

theorem context_13_287032_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287032 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 287032 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 287032, 1, 16384⟩
    (by decide) selected_cut_18613

theorem selected_cut_18614 : selected 8 ⟨476409, by decide⟩
    (prefixPartial 13 287033) = some ⟨13, 2, 0, 476409, 287033, 1917, 16384⟩ := by
  decide +kernel

theorem context_13_287033_476409 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287033 ⟨476409, by decide⟩ :=
  accepted_of_selected 13 287033 ⟨476409, by decide⟩ ⟨13, 2, 0, 476409, 287033, 1917, 16384⟩
    (by decide) selected_cut_18614

theorem selected_cut_18615 : selected 8 ⟨476427, by decide⟩
    (prefixPartial 13 287034) = some ⟨13, 2, 0, 476427, 287034, 1369, 16384⟩ := by
  decide +kernel

theorem context_13_287034_476427 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287034 ⟨476427, by decide⟩ :=
  accepted_of_selected 13 287034 ⟨476427, by decide⟩ ⟨13, 2, 0, 476427, 287034, 1369, 16384⟩
    (by decide) selected_cut_18615

theorem selected_cut_18616 : selected 8 ⟨476433, by decide⟩
    (prefixPartial 13 287035) = some ⟨13, 2, 0, 476433, 287035, 821, 16384⟩ := by
  decide +kernel

theorem context_13_287035_476433 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287035 ⟨476433, by decide⟩ :=
  accepted_of_selected 13 287035 ⟨476433, by decide⟩ ⟨13, 2, 0, 476433, 287035, 821, 16384⟩
    (by decide) selected_cut_18616

theorem unmarked_context_12_71758_476434 : frontier 9 ⟨476434, by decide⟩
    (prefixCache 12 71758) (prefixPartial 12 71758) = false := by
  decide +kernel

theorem node_context_12_71758_476434 : EJMOriginalGlobalDAGData.nodes 9 ⟨476434, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨476409, by decide⟩,⟨476427, by decide⟩,⟨476433, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71758_476434 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71758 ⟨476434, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71758
    ⟨476434, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨476409, by decide⟩,⟨476427, by decide⟩,⟨476433, by decide⟩]) unmarked_context_12_71758_476434 node_context_12_71758_476434
  intro a
  fin_cases a
  · exact context_13_287032_3444
  · exact context_13_287033_476409
  · exact context_13_287034_476427
  · exact context_13_287035_476433

theorem selected_cut_18617 : selected 9 ⟨476483, by decide⟩
    (prefixPartial 12 71759) = some ⟨12, 2, 0, 476483, 71759, 4045, 65536⟩ := by
  decide +kernel

theorem context_12_71759_476483 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71759 ⟨476483, by decide⟩ :=
  accepted_of_selected 12 71759 ⟨476483, by decide⟩ ⟨12, 2, 0, 476483, 71759, 4045, 65536⟩
    (by decide) selected_cut_18617

theorem unmarked_context_11_17939_476484 : frontier 10 ⟨476484, by decide⟩
    (prefixCache 11 17939) (prefixPartial 11 17939) = false := by
  decide +kernel

theorem node_context_11_17939_476484 : EJMOriginalGlobalDAGData.nodes 10 ⟨476484, by decide⟩ =
    .split (coordinate 11) (![⟨476341, by decide⟩,⟨476383, by decide⟩,⟨476434, by decide⟩,⟨476483, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17939_476484 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17939 ⟨476484, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17939
    ⟨476484, by decide⟩ (by decide) (![⟨476341, by decide⟩,⟨476383, by decide⟩,⟨476434, by decide⟩,⟨476483, by decide⟩]) unmarked_context_11_17939_476484 node_context_11_17939_476484
  intro a
  fin_cases a
  · exact context_12_71756_476341
  · exact context_12_71757_476383
  · exact context_12_71758_476434
  · exact context_12_71759_476483

theorem unmarked_context_10_4484_476485 : frontier 11 ⟨476485, by decide⟩
    (prefixCache 10 4484) (prefixPartial 10 4484) = false := by
  decide +kernel

theorem node_context_10_4484_476485 : EJMOriginalGlobalDAGData.nodes 11 ⟨476485, by decide⟩ =
    .split (coordinate 10) (![⟨475874, by decide⟩,⟨476100, by decide⟩,⟨476297, by decide⟩,⟨476484, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4484_476485 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4484 ⟨476485, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4484
    ⟨476485, by decide⟩ (by decide) (![⟨475874, by decide⟩,⟨476100, by decide⟩,⟨476297, by decide⟩,⟨476484, by decide⟩]) unmarked_context_10_4484_476485 node_context_10_4484_476485
  intro a
  fin_cases a
  · exact context_11_17936_475874
  · exact context_11_17937_476100
  · exact context_11_17938_476297
  · exact context_11_17939_476484

theorem selected_cut_18618 : selected 9 ⟨476560, by decide⟩
    (prefixPartial 12 71760) = some ⟨12, 2, 0, 476560, 71760, 2817, 65536⟩ := by
  decide +kernel

theorem context_12_71760_476560 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71760 ⟨476560, by decide⟩ :=
  accepted_of_selected 12 71760 ⟨476560, by decide⟩ ⟨12, 2, 0, 476560, 71760, 2817, 65536⟩
    (by decide) selected_cut_18618

theorem selected_cut_18619 : selected 9 ⟨476609, by decide⟩
    (prefixPartial 12 71761) = some ⟨12, 2, 0, 476609, 71761, 3893, 65536⟩ := by
  decide +kernel

theorem context_12_71761_476609 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71761 ⟨476609, by decide⟩ :=
  accepted_of_selected 12 71761 ⟨476609, by decide⟩ ⟨12, 2, 0, 476609, 71761, 3893, 65536⟩
    (by decide) selected_cut_18619

theorem selected_cut_18620 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 287048) = some ⟨13, 1, 0, 3444, 287048, 1, 16384⟩ := by
  decide +kernel

theorem context_13_287048_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287048 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 287048 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 287048, 1, 16384⟩
    (by decide) selected_cut_18620

theorem selected_cut_18621 : selected 8 ⟨476633, by decide⟩
    (prefixPartial 13 287049) = some ⟨13, 2, 0, 476633, 287049, 1933, 16384⟩ := by
  decide +kernel

theorem context_13_287049_476633 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287049 ⟨476633, by decide⟩ :=
  accepted_of_selected 13 287049 ⟨476633, by decide⟩ ⟨13, 2, 0, 476633, 287049, 1933, 16384⟩
    (by decide) selected_cut_18621

theorem selected_cut_18622 : selected 8 ⟨476651, by decide⟩
    (prefixPartial 13 287050) = some ⟨13, 2, 0, 476651, 287050, 1525, 16384⟩ := by
  decide +kernel

theorem context_13_287050_476651 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287050 ⟨476651, by decide⟩ :=
  accepted_of_selected 13 287050 ⟨476651, by decide⟩ ⟨13, 2, 0, 476651, 287050, 1525, 16384⟩
    (by decide) selected_cut_18622

theorem selected_cut_18623 : selected 8 ⟨476656, by decide⟩
    (prefixPartial 13 287051) = some ⟨13, 2, 0, 476656, 287051, 977, 16384⟩ := by
  decide +kernel

theorem context_13_287051_476656 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287051 ⟨476656, by decide⟩ :=
  accepted_of_selected 13 287051 ⟨476656, by decide⟩ ⟨13, 2, 0, 476656, 287051, 977, 16384⟩
    (by decide) selected_cut_18623

theorem unmarked_context_12_71762_476657 : frontier 9 ⟨476657, by decide⟩
    (prefixCache 12 71762) (prefixPartial 12 71762) = false := by
  decide +kernel

theorem node_context_12_71762_476657 : EJMOriginalGlobalDAGData.nodes 9 ⟨476657, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨476633, by decide⟩,⟨476651, by decide⟩,⟨476656, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71762_476657 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71762 ⟨476657, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71762
    ⟨476657, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨476633, by decide⟩,⟨476651, by decide⟩,⟨476656, by decide⟩]) unmarked_context_12_71762_476657 node_context_12_71762_476657
  intro a
  fin_cases a
  · exact context_13_287048_3444
  · exact context_13_287049_476633
  · exact context_13_287050_476651
  · exact context_13_287051_476656

theorem selected_cut_18624 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 287052) = some ⟨13, 1, 0, 3444, 287052, 1, 16384⟩ := by
  decide +kernel

theorem context_13_287052_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287052 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 287052 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 287052, 1, 16384⟩
    (by decide) selected_cut_18624

theorem selected_cut_18625 : selected 8 ⟨476682, by decide⟩
    (prefixPartial 13 287053) = some ⟨13, 2, 0, 476682, 287053, 1897, 16384⟩ := by
  decide +kernel

theorem context_13_287053_476682 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287053 ⟨476682, by decide⟩ :=
  accepted_of_selected 13 287053 ⟨476682, by decide⟩ ⟨13, 2, 0, 476682, 287053, 1897, 16384⟩
    (by decide) selected_cut_18625

theorem selected_cut_18626 : selected 8 ⟨476698, by decide⟩
    (prefixPartial 13 287054) = some ⟨13, 2, 0, 476698, 287054, 1641, 16384⟩ := by
  decide +kernel

theorem context_13_287054_476698 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287054 ⟨476698, by decide⟩ :=
  accepted_of_selected 13 287054 ⟨476698, by decide⟩ ⟨13, 2, 0, 476698, 287054, 1641, 16384⟩
    (by decide) selected_cut_18626

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
