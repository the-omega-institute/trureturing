/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover352
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_33891 : selected 8 ⟨873043, by decide⟩
    (prefixPartial 13 450693) = some ⟨13, 2, 0, 873043, 450693, 1941, 16384⟩ := by
  decide +kernel

theorem context_13_450693_873043 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 450693 ⟨873043, by decide⟩ :=
  accepted_of_selected 13 450693 ⟨873043, by decide⟩ ⟨13, 2, 0, 873043, 450693, 1941, 16384⟩
    (by decide) selected_cut_33891

theorem selected_cut_33892 : selected 8 ⟨873088, by decide⟩
    (prefixPartial 13 450694) = some ⟨13, 2, 0, 873088, 450694, 853, 16384⟩ := by
  decide +kernel

theorem context_13_450694_873088 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 450694 ⟨873088, by decide⟩ :=
  accepted_of_selected 13 450694 ⟨873088, by decide⟩ ⟨13, 2, 0, 873088, 450694, 853, 16384⟩
    (by decide) selected_cut_33892

theorem selected_cut_33893 : selected 8 ⟨873104, by decide⟩
    (prefixPartial 13 450695) = some ⟨13, 2, 0, 873104, 450695, 621, 16384⟩ := by
  decide +kernel

theorem context_13_450695_873104 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 450695 ⟨873104, by decide⟩ :=
  accepted_of_selected 13 450695 ⟨873104, by decide⟩ ⟨13, 2, 0, 873104, 450695, 621, 16384⟩
    (by decide) selected_cut_33893

theorem unmarked_context_12_112673_873105 : frontier 9 ⟨873105, by decide⟩
    (prefixCache 12 112673) (prefixPartial 12 112673) = false := by
  decide +kernel

theorem node_context_12_112673_873105 : EJMOriginalGlobalDAGData.nodes 9 ⟨873105, by decide⟩ =
    .split (coordinate 12) (![⟨872967, by decide⟩,⟨873043, by decide⟩,⟨873088, by decide⟩,⟨873104, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_112673_873105 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112673 ⟨873105, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 112673
    ⟨873105, by decide⟩ (by decide) (![⟨872967, by decide⟩,⟨873043, by decide⟩,⟨873088, by decide⟩,⟨873104, by decide⟩]) unmarked_context_12_112673_873105 node_context_12_112673_873105
  intro a
  fin_cases a
  · exact context_13_450692_872967
  · exact context_13_450693_873043
  · exact context_13_450694_873088
  · exact context_13_450695_873104

theorem selected_cut_33894 : selected 9 ⟨873238, by decide⟩
    (prefixPartial 12 112674) = some ⟨12, 2, 0, 873238, 112674, 3905, 65536⟩ := by
  decide +kernel

theorem context_12_112674_873238 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112674 ⟨873238, by decide⟩ :=
  accepted_of_selected 12 112674 ⟨873238, by decide⟩ ⟨12, 2, 0, 873238, 112674, 3905, 65536⟩
    (by decide) selected_cut_33894

theorem selected_cut_33895 : selected 9 ⟨873351, by decide⟩
    (prefixPartial 12 112675) = some ⟨12, 2, 0, 873351, 112675, 4041, 65536⟩ := by
  decide +kernel

theorem context_12_112675_873351 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112675 ⟨873351, by decide⟩ :=
  accepted_of_selected 12 112675 ⟨873351, by decide⟩ ⟨12, 2, 0, 873351, 112675, 4041, 65536⟩
    (by decide) selected_cut_33895

theorem unmarked_context_11_28168_873352 : frontier 10 ⟨873352, by decide⟩
    (prefixCache 11 28168) (prefixPartial 11 28168) = false := by
  decide +kernel

theorem node_context_11_28168_873352 : EJMOriginalGlobalDAGData.nodes 10 ⟨873352, by decide⟩ =
    .split (coordinate 11) (![⟨765706, by decide⟩,⟨873105, by decide⟩,⟨873238, by decide⟩,⟨873351, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_28168_873352 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 28168 ⟨873352, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 28168
    ⟨873352, by decide⟩ (by decide) (![⟨765706, by decide⟩,⟨873105, by decide⟩,⟨873238, by decide⟩,⟨873351, by decide⟩]) unmarked_context_11_28168_873352 node_context_11_28168_873352
  intro a
  fin_cases a
  · exact context_12_112672_765706
  · exact context_12_112673_873105
  · exact context_12_112674_873238
  · exact context_12_112675_873351

theorem selected_cut_33896 : selected 9 ⟨873479, by decide⟩
    (prefixPartial 12 112676) = some ⟨12, 2, 0, 873479, 112676, 3861, 65536⟩ := by
  decide +kernel

theorem context_12_112676_873479 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112676 ⟨873479, by decide⟩ :=
  accepted_of_selected 12 112676 ⟨873479, by decide⟩ ⟨12, 2, 0, 873479, 112676, 3861, 65536⟩
    (by decide) selected_cut_33896

theorem selected_cut_33897 : selected 8 ⟨873512, by decide⟩
    (prefixPartial 13 450708) = some ⟨13, 2, 0, 873512, 450708, 1033, 16384⟩ := by
  decide +kernel

theorem context_13_450708_873512 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 450708 ⟨873512, by decide⟩ :=
  accepted_of_selected 13 450708 ⟨873512, by decide⟩ ⟨13, 2, 0, 873512, 450708, 1033, 16384⟩
    (by decide) selected_cut_33897

theorem selected_cut_33898 : selected 8 ⟨873560, by decide⟩
    (prefixPartial 13 450709) = some ⟨13, 2, 0, 873560, 450709, 1925, 16384⟩ := by
  decide +kernel

theorem context_13_450709_873560 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 450709 ⟨873560, by decide⟩ :=
  accepted_of_selected 13 450709 ⟨873560, by decide⟩ ⟨13, 2, 0, 873560, 450709, 1925, 16384⟩
    (by decide) selected_cut_33898

theorem selected_cut_33899 : selected 8 ⟨873593, by decide⟩
    (prefixPartial 13 450710) = some ⟨13, 2, 0, 873593, 450710, 953, 16384⟩ := by
  decide +kernel

theorem context_13_450710_873593 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 450710 ⟨873593, by decide⟩ :=
  accepted_of_selected 13 450710 ⟨873593, by decide⟩ ⟨13, 2, 0, 873593, 450710, 953, 16384⟩
    (by decide) selected_cut_33899

theorem selected_cut_33900 : selected 8 ⟨873601, by decide⟩
    (prefixPartial 13 450711) = some ⟨13, 2, 0, 873601, 450711, 693, 16384⟩ := by
  decide +kernel

theorem context_13_450711_873601 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 450711 ⟨873601, by decide⟩ :=
  accepted_of_selected 13 450711 ⟨873601, by decide⟩ ⟨13, 2, 0, 873601, 450711, 693, 16384⟩
    (by decide) selected_cut_33900

theorem unmarked_context_12_112677_873602 : frontier 9 ⟨873602, by decide⟩
    (prefixCache 12 112677) (prefixPartial 12 112677) = false := by
  decide +kernel

theorem node_context_12_112677_873602 : EJMOriginalGlobalDAGData.nodes 9 ⟨873602, by decide⟩ =
    .split (coordinate 12) (![⟨873512, by decide⟩,⟨873560, by decide⟩,⟨873593, by decide⟩,⟨873601, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_112677_873602 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112677 ⟨873602, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 112677
    ⟨873602, by decide⟩ (by decide) (![⟨873512, by decide⟩,⟨873560, by decide⟩,⟨873593, by decide⟩,⟨873601, by decide⟩]) unmarked_context_12_112677_873602 node_context_12_112677_873602
  intro a
  fin_cases a
  · exact context_13_450708_873512
  · exact context_13_450709_873560
  · exact context_13_450710_873593
  · exact context_13_450711_873601

theorem selected_cut_33901 : selected 8 ⟨873627, by decide⟩
    (prefixPartial 13 450712) = some ⟨13, 2, 0, 873627, 450712, 973, 16384⟩ := by
  decide +kernel

theorem context_13_450712_873627 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 450712 ⟨873627, by decide⟩ :=
  accepted_of_selected 13 450712 ⟨873627, by decide⟩ ⟨13, 2, 0, 873627, 450712, 973, 16384⟩
    (by decide) selected_cut_33901

theorem selected_cut_33902 : selected 8 ⟨873670, by decide⟩
    (prefixPartial 13 450713) = some ⟨13, 2, 0, 873670, 450713, 1933, 16384⟩ := by
  decide +kernel

theorem context_13_450713_873670 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 450713 ⟨873670, by decide⟩ :=
  accepted_of_selected 13 450713 ⟨873670, by decide⟩ ⟨13, 2, 0, 873670, 450713, 1933, 16384⟩
    (by decide) selected_cut_33902

theorem selected_cut_33903 : selected 8 ⟨873696, by decide⟩
    (prefixPartial 13 450714) = some ⟨13, 2, 0, 873696, 450714, 805, 16384⟩ := by
  decide +kernel

theorem context_13_450714_873696 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 450714 ⟨873696, by decide⟩ :=
  accepted_of_selected 13 450714 ⟨873696, by decide⟩ ⟨13, 2, 0, 873696, 450714, 805, 16384⟩
    (by decide) selected_cut_33903

theorem selected_cut_33904 : selected 8 ⟨873699, by decide⟩
    (prefixPartial 13 450715) = some ⟨13, 2, 0, 873699, 450715, 613, 16384⟩ := by
  decide +kernel

theorem context_13_450715_873699 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 450715 ⟨873699, by decide⟩ :=
  accepted_of_selected 13 450715 ⟨873699, by decide⟩ ⟨13, 2, 0, 873699, 450715, 613, 16384⟩
    (by decide) selected_cut_33904

theorem unmarked_context_12_112678_873700 : frontier 9 ⟨873700, by decide⟩
    (prefixCache 12 112678) (prefixPartial 12 112678) = false := by
  decide +kernel

theorem node_context_12_112678_873700 : EJMOriginalGlobalDAGData.nodes 9 ⟨873700, by decide⟩ =
    .split (coordinate 12) (![⟨873627, by decide⟩,⟨873670, by decide⟩,⟨873696, by decide⟩,⟨873699, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_112678_873700 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112678 ⟨873700, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 112678
    ⟨873700, by decide⟩ (by decide) (![⟨873627, by decide⟩,⟨873670, by decide⟩,⟨873696, by decide⟩,⟨873699, by decide⟩]) unmarked_context_12_112678_873700 node_context_12_112678_873700
  intro a
  fin_cases a
  · exact context_13_450712_873627
  · exact context_13_450713_873670
  · exact context_13_450714_873696
  · exact context_13_450715_873699

theorem selected_cut_33905 : selected 8 ⟨873722, by decide⟩
    (prefixPartial 13 450716) = some ⟨13, 2, 0, 873722, 450716, 929, 16384⟩ := by
  decide +kernel

theorem context_13_450716_873722 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 450716 ⟨873722, by decide⟩ :=
  accepted_of_selected 13 450716 ⟨873722, by decide⟩ ⟨13, 2, 0, 873722, 450716, 929, 16384⟩
    (by decide) selected_cut_33905

theorem selected_cut_33906 : selected 8 ⟨873777, by decide⟩
    (prefixPartial 13 450717) = some ⟨13, 2, 0, 873777, 450717, 2201, 16384⟩ := by
  decide +kernel

theorem context_13_450717_873777 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 450717 ⟨873777, by decide⟩ :=
  accepted_of_selected 13 450717 ⟨873777, by decide⟩ ⟨13, 2, 0, 873777, 450717, 2201, 16384⟩
    (by decide) selected_cut_33906

theorem selected_cut_33907 : selected 8 ⟨873798, by decide⟩
    (prefixPartial 13 450718) = some ⟨13, 2, 0, 873798, 450718, 773, 16384⟩ := by
  decide +kernel

theorem context_13_450718_873798 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 450718 ⟨873798, by decide⟩ :=
  accepted_of_selected 13 450718 ⟨873798, by decide⟩ ⟨13, 2, 0, 873798, 450718, 773, 16384⟩
    (by decide) selected_cut_33907

theorem selected_cut_33908 : selected 8 ⟨873802, by decide⟩
    (prefixPartial 13 450719) = some ⟨13, 2, 0, 873802, 450719, 597, 16384⟩ := by
  decide +kernel

theorem context_13_450719_873802 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 450719 ⟨873802, by decide⟩ :=
  accepted_of_selected 13 450719 ⟨873802, by decide⟩ ⟨13, 2, 0, 873802, 450719, 597, 16384⟩
    (by decide) selected_cut_33908

theorem unmarked_context_12_112679_873803 : frontier 9 ⟨873803, by decide⟩
    (prefixCache 12 112679) (prefixPartial 12 112679) = false := by
  decide +kernel

theorem node_context_12_112679_873803 : EJMOriginalGlobalDAGData.nodes 9 ⟨873803, by decide⟩ =
    .split (coordinate 12) (![⟨873722, by decide⟩,⟨873777, by decide⟩,⟨873798, by decide⟩,⟨873802, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_112679_873803 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112679 ⟨873803, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 112679
    ⟨873803, by decide⟩ (by decide) (![⟨873722, by decide⟩,⟨873777, by decide⟩,⟨873798, by decide⟩,⟨873802, by decide⟩]) unmarked_context_12_112679_873803 node_context_12_112679_873803
  intro a
  fin_cases a
  · exact context_13_450716_873722
  · exact context_13_450717_873777
  · exact context_13_450718_873798
  · exact context_13_450719_873802

theorem unmarked_context_11_28169_873804 : frontier 10 ⟨873804, by decide⟩
    (prefixCache 11 28169) (prefixPartial 11 28169) = false := by
  decide +kernel

theorem node_context_11_28169_873804 : EJMOriginalGlobalDAGData.nodes 10 ⟨873804, by decide⟩ =
    .split (coordinate 11) (![⟨873479, by decide⟩,⟨873602, by decide⟩,⟨873700, by decide⟩,⟨873803, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_28169_873804 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 28169 ⟨873804, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 28169
    ⟨873804, by decide⟩ (by decide) (![⟨873479, by decide⟩,⟨873602, by decide⟩,⟨873700, by decide⟩,⟨873803, by decide⟩]) unmarked_context_11_28169_873804 node_context_11_28169_873804
  intro a
  fin_cases a
  · exact context_12_112676_873479
  · exact context_12_112677_873602
  · exact context_12_112678_873700
  · exact context_12_112679_873803

theorem selected_cut_33909 : selected 10 ⟨766338, by decide⟩
    (prefixPartial 11 28170) = some ⟨11, 1, 0, 766338, 28170, 1, 262144⟩ := by
  decide +kernel

theorem context_11_28170_766338 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 28170 ⟨766338, by decide⟩ :=
  accepted_of_selected 11 28170 ⟨766338, by decide⟩ ⟨11, 1, 0, 766338, 28170, 1, 262144⟩
    (by decide) selected_cut_33909

theorem selected_cut_33910 : selected 8 ⟨873820, by decide⟩
    (prefixPartial 13 450736) = some ⟨13, 2, 0, 873820, 450736, 577, 16384⟩ := by
  decide +kernel

theorem context_13_450736_873820 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 450736 ⟨873820, by decide⟩ :=
  accepted_of_selected 13 450736 ⟨873820, by decide⟩ ⟨13, 2, 0, 873820, 450736, 577, 16384⟩
    (by decide) selected_cut_33910

theorem selected_cut_33911 : selected 8 ⟨873877, by decide⟩
    (prefixPartial 13 450737) = some ⟨13, 2, 0, 873877, 450737, 2293, 16384⟩ := by
  decide +kernel

theorem context_13_450737_873877 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 450737 ⟨873877, by decide⟩ :=
  accepted_of_selected 13 450737 ⟨873877, by decide⟩ ⟨13, 2, 0, 873877, 450737, 2293, 16384⟩
    (by decide) selected_cut_33911

theorem selected_cut_33912 : selected 8 ⟨873919, by decide⟩
    (prefixPartial 13 450738) = some ⟨13, 2, 0, 873919, 450738, 829, 16384⟩ := by
  decide +kernel

theorem context_13_450738_873919 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 450738 ⟨873919, by decide⟩ :=
  accepted_of_selected 13 450738 ⟨873919, by decide⟩ ⟨13, 2, 0, 873919, 450738, 829, 16384⟩
    (by decide) selected_cut_33912

theorem selected_cut_33913 : selected 8 ⟨873925, by decide⟩
    (prefixPartial 13 450739) = some ⟨13, 2, 0, 873925, 450739, 533, 16384⟩ := by
  decide +kernel

theorem context_13_450739_873925 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 450739 ⟨873925, by decide⟩ :=
  accepted_of_selected 13 450739 ⟨873925, by decide⟩ ⟨13, 2, 0, 873925, 450739, 533, 16384⟩
    (by decide) selected_cut_33913

theorem unmarked_context_12_112684_873926 : frontier 9 ⟨873926, by decide⟩
    (prefixCache 12 112684) (prefixPartial 12 112684) = false := by
  decide +kernel

theorem node_context_12_112684_873926 : EJMOriginalGlobalDAGData.nodes 9 ⟨873926, by decide⟩ =
    .split (coordinate 12) (![⟨873820, by decide⟩,⟨873877, by decide⟩,⟨873919, by decide⟩,⟨873925, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_112684_873926 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112684 ⟨873926, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 112684
    ⟨873926, by decide⟩ (by decide) (![⟨873820, by decide⟩,⟨873877, by decide⟩,⟨873919, by decide⟩,⟨873925, by decide⟩]) unmarked_context_12_112684_873926 node_context_12_112684_873926
  intro a
  fin_cases a
  · exact context_13_450736_873820
  · exact context_13_450737_873877
  · exact context_13_450738_873919
  · exact context_13_450739_873925

theorem selected_cut_33914 : selected 8 ⟨873961, by decide⟩
    (prefixPartial 13 450740) = some ⟨13, 2, 0, 873961, 450740, 941, 16384⟩ := by
  decide +kernel

theorem context_13_450740_873961 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 450740 ⟨873961, by decide⟩ :=
  accepted_of_selected 13 450740 ⟨873961, by decide⟩ ⟨13, 2, 0, 873961, 450740, 941, 16384⟩
    (by decide) selected_cut_33914

theorem selected_cut_33915 : selected 8 ⟨874026, by decide⟩
    (prefixPartial 13 450741) = some ⟨13, 2, 0, 874026, 450741, 2593, 16384⟩ := by
  decide +kernel

theorem context_13_450741_874026 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 450741 ⟨874026, by decide⟩ :=
  accepted_of_selected 13 450741 ⟨874026, by decide⟩ ⟨13, 2, 0, 874026, 450741, 2593, 16384⟩
    (by decide) selected_cut_33915

theorem selected_cut_33916 : selected 8 ⟨874074, by decide⟩
    (prefixPartial 13 450742) = some ⟨13, 2, 0, 874074, 450742, 1045, 16384⟩ := by
  decide +kernel

theorem context_13_450742_874074 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 450742 ⟨874074, by decide⟩ :=
  accepted_of_selected 13 450742 ⟨874074, by decide⟩ ⟨13, 2, 0, 874074, 450742, 1045, 16384⟩
    (by decide) selected_cut_33916

theorem selected_cut_33917 : selected 8 ⟨874088, by decide⟩
    (prefixPartial 13 450743) = some ⟨13, 2, 0, 874088, 450743, 689, 16384⟩ := by
  decide +kernel

theorem context_13_450743_874088 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 450743 ⟨874088, by decide⟩ :=
  accepted_of_selected 13 450743 ⟨874088, by decide⟩ ⟨13, 2, 0, 874088, 450743, 689, 16384⟩
    (by decide) selected_cut_33917

theorem unmarked_context_12_112685_874089 : frontier 9 ⟨874089, by decide⟩
    (prefixCache 12 112685) (prefixPartial 12 112685) = false := by
  decide +kernel

theorem node_context_12_112685_874089 : EJMOriginalGlobalDAGData.nodes 9 ⟨874089, by decide⟩ =
    .split (coordinate 12) (![⟨873961, by decide⟩,⟨874026, by decide⟩,⟨874074, by decide⟩,⟨874088, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_112685_874089 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112685 ⟨874089, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 112685
    ⟨874089, by decide⟩ (by decide) (![⟨873961, by decide⟩,⟨874026, by decide⟩,⟨874074, by decide⟩,⟨874088, by decide⟩]) unmarked_context_12_112685_874089 node_context_12_112685_874089
  intro a
  fin_cases a
  · exact context_13_450740_873961
  · exact context_13_450741_874026
  · exact context_13_450742_874074
  · exact context_13_450743_874088

theorem selected_cut_33918 : selected 8 ⟨874104, by decide⟩
    (prefixPartial 13 450744) = some ⟨13, 2, 0, 874104, 450744, 645, 16384⟩ := by
  decide +kernel

theorem context_13_450744_874104 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 450744 ⟨874104, by decide⟩ :=
  accepted_of_selected 13 450744 ⟨874104, by decide⟩ ⟨13, 2, 0, 874104, 450744, 645, 16384⟩
    (by decide) selected_cut_33918

theorem selected_cut_33919 : selected 8 ⟨874161, by decide⟩
    (prefixPartial 13 450745) = some ⟨13, 2, 0, 874161, 450745, 2389, 16384⟩ := by
  decide +kernel

theorem context_13_450745_874161 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 450745 ⟨874161, by decide⟩ :=
  accepted_of_selected 13 450745 ⟨874161, by decide⟩ ⟨13, 2, 0, 874161, 450745, 2389, 16384⟩
    (by decide) selected_cut_33919

theorem selected_cut_33920 : selected 8 ⟨874185, by decide⟩
    (prefixPartial 13 450746) = some ⟨13, 2, 0, 874185, 450746, 741, 16384⟩ := by
  decide +kernel

theorem context_13_450746_874185 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 450746 ⟨874185, by decide⟩ :=
  accepted_of_selected 13 450746 ⟨874185, by decide⟩ ⟨13, 2, 0, 874185, 450746, 741, 16384⟩
    (by decide) selected_cut_33920

theorem selected_cut_33921 : selected 8 ⟨874189, by decide⟩
    (prefixPartial 13 450747) = some ⟨13, 2, 0, 874189, 450747, 585, 16384⟩ := by
  decide +kernel

theorem context_13_450747_874189 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 450747 ⟨874189, by decide⟩ :=
  accepted_of_selected 13 450747 ⟨874189, by decide⟩ ⟨13, 2, 0, 874189, 450747, 585, 16384⟩
    (by decide) selected_cut_33921

theorem unmarked_context_12_112686_874190 : frontier 9 ⟨874190, by decide⟩
    (prefixCache 12 112686) (prefixPartial 12 112686) = false := by
  decide +kernel

theorem node_context_12_112686_874190 : EJMOriginalGlobalDAGData.nodes 9 ⟨874190, by decide⟩ =
    .split (coordinate 12) (![⟨874104, by decide⟩,⟨874161, by decide⟩,⟨874185, by decide⟩,⟨874189, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_112686_874190 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112686 ⟨874190, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 112686
    ⟨874190, by decide⟩ (by decide) (![⟨874104, by decide⟩,⟨874161, by decide⟩,⟨874185, by decide⟩,⟨874189, by decide⟩]) unmarked_context_12_112686_874190 node_context_12_112686_874190
  intro a
  fin_cases a
  · exact context_13_450744_874104
  · exact context_13_450745_874161
  · exact context_13_450746_874185
  · exact context_13_450747_874189

theorem selected_cut_33922 : selected 8 ⟨874204, by decide⟩
    (prefixPartial 13 450748) = some ⟨13, 2, 0, 874204, 450748, 501, 16384⟩ := by
  decide +kernel

theorem context_13_450748_874204 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 450748 ⟨874204, by decide⟩ :=
  accepted_of_selected 13 450748 ⟨874204, by decide⟩ ⟨13, 2, 0, 874204, 450748, 501, 16384⟩
    (by decide) selected_cut_33922

theorem selected_cut_33923 : selected 8 ⟨874259, by decide⟩
    (prefixPartial 13 450749) = some ⟨13, 2, 0, 874259, 450749, 2401, 16384⟩ := by
  decide +kernel

theorem context_13_450749_874259 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 450749 ⟨874259, by decide⟩ :=
  accepted_of_selected 13 450749 ⟨874259, by decide⟩ ⟨13, 2, 0, 874259, 450749, 2401, 16384⟩
    (by decide) selected_cut_33923

theorem selected_cut_33924 : selected 8 ⟨874281, by decide⟩
    (prefixPartial 13 450750) = some ⟨13, 2, 0, 874281, 450750, 729, 16384⟩ := by
  decide +kernel

theorem context_13_450750_874281 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 450750 ⟨874281, by decide⟩ :=
  accepted_of_selected 13 450750 ⟨874281, by decide⟩ ⟨13, 2, 0, 874281, 450750, 729, 16384⟩
    (by decide) selected_cut_33924

theorem selected_cut_33925 : selected 8 ⟨874285, by decide⟩
    (prefixPartial 13 450751) = some ⟨13, 2, 0, 874285, 450751, 605, 16384⟩ := by
  decide +kernel

theorem context_13_450751_874285 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 450751 ⟨874285, by decide⟩ :=
  accepted_of_selected 13 450751 ⟨874285, by decide⟩ ⟨13, 2, 0, 874285, 450751, 605, 16384⟩
    (by decide) selected_cut_33925

theorem unmarked_context_12_112687_874286 : frontier 9 ⟨874286, by decide⟩
    (prefixCache 12 112687) (prefixPartial 12 112687) = false := by
  decide +kernel

theorem node_context_12_112687_874286 : EJMOriginalGlobalDAGData.nodes 9 ⟨874286, by decide⟩ =
    .split (coordinate 12) (![⟨874204, by decide⟩,⟨874259, by decide⟩,⟨874281, by decide⟩,⟨874285, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_112687_874286 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112687 ⟨874286, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 112687
    ⟨874286, by decide⟩ (by decide) (![⟨874204, by decide⟩,⟨874259, by decide⟩,⟨874281, by decide⟩,⟨874285, by decide⟩]) unmarked_context_12_112687_874286 node_context_12_112687_874286
  intro a
  fin_cases a
  · exact context_13_450748_874204
  · exact context_13_450749_874259
  · exact context_13_450750_874281
  · exact context_13_450751_874285

theorem unmarked_context_11_28171_874287 : frontier 10 ⟨874287, by decide⟩
    (prefixCache 11 28171) (prefixPartial 11 28171) = false := by
  decide +kernel

theorem node_context_11_28171_874287 : EJMOriginalGlobalDAGData.nodes 10 ⟨874287, by decide⟩ =
    .split (coordinate 11) (![⟨873926, by decide⟩,⟨874089, by decide⟩,⟨874190, by decide⟩,⟨874286, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_28171_874287 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 28171 ⟨874287, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 28171
    ⟨874287, by decide⟩ (by decide) (![⟨873926, by decide⟩,⟨874089, by decide⟩,⟨874190, by decide⟩,⟨874286, by decide⟩]) unmarked_context_11_28171_874287 node_context_11_28171_874287
  intro a
  fin_cases a
  · exact context_12_112684_873926
  · exact context_12_112685_874089
  · exact context_12_112686_874190
  · exact context_12_112687_874286

theorem unmarked_context_10_7042_874288 : frontier 11 ⟨874288, by decide⟩
    (prefixCache 10 7042) (prefixPartial 10 7042) = false := by
  decide +kernel

theorem node_context_10_7042_874288 : EJMOriginalGlobalDAGData.nodes 11 ⟨874288, by decide⟩ =
    .split (coordinate 10) (![⟨873352, by decide⟩,⟨873804, by decide⟩,⟨766338, by decide⟩,⟨874287, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_7042_874288 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 7042 ⟨874288, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 7042
    ⟨874288, by decide⟩ (by decide) (![⟨873352, by decide⟩,⟨873804, by decide⟩,⟨766338, by decide⟩,⟨874287, by decide⟩]) unmarked_context_10_7042_874288 node_context_10_7042_874288
  intro a
  fin_cases a
  · exact context_11_28168_873352
  · exact context_11_28169_873804
  · exact context_11_28170_766338
  · exact context_11_28171_874287

theorem selected_cut_33926 : selected 9 ⟨766630, by decide⟩
    (prefixPartial 12 112688) = some ⟨12, 1, 0, 766630, 112688, 1, 65536⟩ := by
  decide +kernel

theorem context_12_112688_766630 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112688 ⟨766630, by decide⟩ :=
  accepted_of_selected 12 112688 ⟨766630, by decide⟩ ⟨12, 1, 0, 766630, 112688, 1, 65536⟩
    (by decide) selected_cut_33926

theorem selected_cut_33927 : selected 8 ⟨874316, by decide⟩
    (prefixPartial 13 450756) = some ⟨13, 2, 0, 874316, 450756, 777, 16384⟩ := by
  decide +kernel

theorem context_13_450756_874316 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 450756 ⟨874316, by decide⟩ :=
  accepted_of_selected 13 450756 ⟨874316, by decide⟩ ⟨13, 2, 0, 874316, 450756, 777, 16384⟩
    (by decide) selected_cut_33927

theorem selected_cut_33928 : selected 8 ⟨874392, by decide⟩
    (prefixPartial 13 450757) = some ⟨13, 2, 0, 874392, 450757, 2113, 16384⟩ := by
  decide +kernel

theorem context_13_450757_874392 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 450757 ⟨874392, by decide⟩ :=
  accepted_of_selected 13 450757 ⟨874392, by decide⟩ ⟨13, 2, 0, 874392, 450757, 2113, 16384⟩
    (by decide) selected_cut_33928

theorem selected_cut_33929 : selected 8 ⟨874416, by decide⟩
    (prefixPartial 13 450758) = some ⟨13, 2, 0, 874416, 450758, 773, 16384⟩ := by
  decide +kernel

theorem context_13_450758_874416 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 450758 ⟨874416, by decide⟩ :=
  accepted_of_selected 13 450758 ⟨874416, by decide⟩ ⟨13, 2, 0, 874416, 450758, 773, 16384⟩
    (by decide) selected_cut_33929

theorem selected_cut_33930 : selected 8 ⟨874428, by decide⟩
    (prefixPartial 13 450759) = some ⟨13, 2, 0, 874428, 450759, 673, 16384⟩ := by
  decide +kernel

theorem context_13_450759_874428 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 450759 ⟨874428, by decide⟩ :=
  accepted_of_selected 13 450759 ⟨874428, by decide⟩ ⟨13, 2, 0, 874428, 450759, 673, 16384⟩
    (by decide) selected_cut_33930

theorem unmarked_context_12_112689_874429 : frontier 9 ⟨874429, by decide⟩
    (prefixCache 12 112689) (prefixPartial 12 112689) = false := by
  decide +kernel

theorem node_context_12_112689_874429 : EJMOriginalGlobalDAGData.nodes 9 ⟨874429, by decide⟩ =
    .split (coordinate 12) (![⟨874316, by decide⟩,⟨874392, by decide⟩,⟨874416, by decide⟩,⟨874428, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_112689_874429 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112689 ⟨874429, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 112689
    ⟨874429, by decide⟩ (by decide) (![⟨874316, by decide⟩,⟨874392, by decide⟩,⟨874416, by decide⟩,⟨874428, by decide⟩]) unmarked_context_12_112689_874429 node_context_12_112689_874429
  intro a
  fin_cases a
  · exact context_13_450756_874316
  · exact context_13_450757_874392
  · exact context_13_450758_874416
  · exact context_13_450759_874428

theorem selected_cut_33931 : selected 9 ⟨874522, by decide⟩
    (prefixPartial 12 112690) = some ⟨12, 2, 0, 874522, 112690, 3489, 65536⟩ := by
  decide +kernel

theorem context_12_112690_874522 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112690 ⟨874522, by decide⟩ :=
  accepted_of_selected 12 112690 ⟨874522, by decide⟩ ⟨12, 2, 0, 874522, 112690, 3489, 65536⟩
    (by decide) selected_cut_33931

theorem selected_cut_33932 : selected 9 ⟨874607, by decide⟩
    (prefixPartial 12 112691) = some ⟨12, 2, 0, 874607, 112691, 3797, 65536⟩ := by
  decide +kernel

theorem context_12_112691_874607 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112691 ⟨874607, by decide⟩ :=
  accepted_of_selected 12 112691 ⟨874607, by decide⟩ ⟨12, 2, 0, 874607, 112691, 3797, 65536⟩
    (by decide) selected_cut_33932

theorem unmarked_context_11_28172_874608 : frontier 10 ⟨874608, by decide⟩
    (prefixCache 11 28172) (prefixPartial 11 28172) = false := by
  decide +kernel

theorem node_context_11_28172_874608 : EJMOriginalGlobalDAGData.nodes 10 ⟨874608, by decide⟩ =
    .split (coordinate 11) (![⟨766630, by decide⟩,⟨874429, by decide⟩,⟨874522, by decide⟩,⟨874607, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_28172_874608 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 28172 ⟨874608, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 28172
    ⟨874608, by decide⟩ (by decide) (![⟨766630, by decide⟩,⟨874429, by decide⟩,⟨874522, by decide⟩,⟨874607, by decide⟩]) unmarked_context_11_28172_874608 node_context_11_28172_874608
  intro a
  fin_cases a
  · exact context_12_112688_766630
  · exact context_12_112689_874429
  · exact context_12_112690_874522
  · exact context_12_112691_874607

theorem selected_cut_33933 : selected 9 ⟨874688, by decide⟩
    (prefixPartial 12 112692) = some ⟨12, 2, 0, 874688, 112692, 3377, 65536⟩ := by
  decide +kernel

theorem context_12_112692_874688 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112692 ⟨874688, by decide⟩ :=
  accepted_of_selected 12 112692 ⟨874688, by decide⟩ ⟨12, 2, 0, 874688, 112692, 3377, 65536⟩
    (by decide) selected_cut_33933

theorem selected_cut_33934 : selected 9 ⟨874784, by decide⟩
    (prefixPartial 12 112693) = some ⟨12, 2, 0, 874784, 112693, 4021, 65536⟩ := by
  decide +kernel

theorem context_12_112693_874784 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112693 ⟨874784, by decide⟩ :=
  accepted_of_selected 12 112693 ⟨874784, by decide⟩ ⟨12, 2, 0, 874784, 112693, 4021, 65536⟩
    (by decide) selected_cut_33934

theorem selected_cut_33935 : selected 9 ⟨874859, by decide⟩
    (prefixPartial 12 112694) = some ⟨12, 2, 0, 874859, 112694, 3569, 65536⟩ := by
  decide +kernel

theorem context_12_112694_874859 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112694 ⟨874859, by decide⟩ :=
  accepted_of_selected 12 112694 ⟨874859, by decide⟩ ⟨12, 2, 0, 874859, 112694, 3569, 65536⟩
    (by decide) selected_cut_33935

theorem selected_cut_33936 : selected 9 ⟨874952, by decide⟩
    (prefixPartial 12 112695) = some ⟨12, 2, 0, 874952, 112695, 3801, 65536⟩ := by
  decide +kernel

theorem context_12_112695_874952 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112695 ⟨874952, by decide⟩ :=
  accepted_of_selected 12 112695 ⟨874952, by decide⟩ ⟨12, 2, 0, 874952, 112695, 3801, 65536⟩
    (by decide) selected_cut_33936

theorem unmarked_context_11_28173_874953 : frontier 10 ⟨874953, by decide⟩
    (prefixCache 11 28173) (prefixPartial 11 28173) = false := by
  decide +kernel

theorem node_context_11_28173_874953 : EJMOriginalGlobalDAGData.nodes 10 ⟨874953, by decide⟩ =
    .split (coordinate 11) (![⟨874688, by decide⟩,⟨874784, by decide⟩,⟨874859, by decide⟩,⟨874952, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_28173_874953 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 28173 ⟨874953, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 28173
    ⟨874953, by decide⟩ (by decide) (![⟨874688, by decide⟩,⟨874784, by decide⟩,⟨874859, by decide⟩,⟨874952, by decide⟩]) unmarked_context_11_28173_874953 node_context_11_28173_874953
  intro a
  fin_cases a
  · exact context_12_112692_874688
  · exact context_12_112693_874784
  · exact context_12_112694_874859
  · exact context_12_112695_874952

theorem selected_cut_33937 : selected 9 ⟨875022, by decide⟩
    (prefixPartial 12 112696) = some ⟨12, 2, 0, 875022, 112696, 2881, 65536⟩ := by
  decide +kernel

theorem context_12_112696_875022 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112696 ⟨875022, by decide⟩ :=
  accepted_of_selected 12 112696 ⟨875022, by decide⟩ ⟨12, 2, 0, 875022, 112696, 2881, 65536⟩
    (by decide) selected_cut_33937

theorem selected_cut_33938 : selected 9 ⟨875105, by decide⟩
    (prefixPartial 12 112697) = some ⟨12, 2, 0, 875105, 112697, 3621, 65536⟩ := by
  decide +kernel

theorem context_12_112697_875105 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112697 ⟨875105, by decide⟩ :=
  accepted_of_selected 12 112697 ⟨875105, by decide⟩ ⟨12, 2, 0, 875105, 112697, 3621, 65536⟩
    (by decide) selected_cut_33938

theorem selected_cut_33939 : selected 9 ⟨875157, by decide⟩
    (prefixPartial 12 112698) = some ⟨12, 2, 0, 875157, 112698, 2877, 65536⟩ := by
  decide +kernel

theorem context_12_112698_875157 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112698 ⟨875157, by decide⟩ :=
  accepted_of_selected 12 112698 ⟨875157, by decide⟩ ⟨12, 2, 0, 875157, 112698, 2877, 65536⟩
    (by decide) selected_cut_33939

theorem selected_cut_33940 : selected 9 ⟨875227, by decide⟩
    (prefixPartial 12 112699) = some ⟨12, 2, 0, 875227, 112699, 3209, 65536⟩ := by
  decide +kernel

theorem context_12_112699_875227 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112699 ⟨875227, by decide⟩ :=
  accepted_of_selected 12 112699 ⟨875227, by decide⟩ ⟨12, 2, 0, 875227, 112699, 3209, 65536⟩
    (by decide) selected_cut_33940

theorem unmarked_context_11_28174_875228 : frontier 10 ⟨875228, by decide⟩
    (prefixCache 11 28174) (prefixPartial 11 28174) = false := by
  decide +kernel

theorem node_context_11_28174_875228 : EJMOriginalGlobalDAGData.nodes 10 ⟨875228, by decide⟩ =
    .split (coordinate 11) (![⟨875022, by decide⟩,⟨875105, by decide⟩,⟨875157, by decide⟩,⟨875227, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_28174_875228 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 28174 ⟨875228, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 28174
    ⟨875228, by decide⟩ (by decide) (![⟨875022, by decide⟩,⟨875105, by decide⟩,⟨875157, by decide⟩,⟨875227, by decide⟩]) unmarked_context_11_28174_875228 node_context_11_28174_875228
  intro a
  fin_cases a
  · exact context_12_112696_875022
  · exact context_12_112697_875105
  · exact context_12_112698_875157
  · exact context_12_112699_875227

theorem selected_cut_33941 : selected 9 ⟨875291, by decide⟩
    (prefixPartial 12 112700) = some ⟨12, 2, 0, 875291, 112700, 3121, 65536⟩ := by
  decide +kernel

theorem context_12_112700_875291 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112700 ⟨875291, by decide⟩ :=
  accepted_of_selected 12 112700 ⟨875291, by decide⟩ ⟨12, 2, 0, 875291, 112700, 3121, 65536⟩
    (by decide) selected_cut_33941

theorem selected_cut_33942 : selected 9 ⟨875364, by decide⟩
    (prefixPartial 12 112701) = some ⟨12, 2, 0, 875364, 112701, 3565, 65536⟩ := by
  decide +kernel

theorem context_12_112701_875364 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112701 ⟨875364, by decide⟩ :=
  accepted_of_selected 12 112701 ⟨875364, by decide⟩ ⟨12, 2, 0, 875364, 112701, 3565, 65536⟩
    (by decide) selected_cut_33942

theorem selected_cut_33943 : selected 9 ⟨875420, by decide⟩
    (prefixPartial 12 112702) = some ⟨12, 2, 0, 875420, 112702, 3005, 65536⟩ := by
  decide +kernel

theorem context_12_112702_875420 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112702 ⟨875420, by decide⟩ :=
  accepted_of_selected 12 112702 ⟨875420, by decide⟩ ⟨12, 2, 0, 875420, 112702, 3005, 65536⟩
    (by decide) selected_cut_33943

theorem selected_cut_33944 : selected 9 ⟨875474, by decide⟩
    (prefixPartial 12 112703) = some ⟨12, 2, 0, 875474, 112703, 3077, 65536⟩ := by
  decide +kernel

theorem context_12_112703_875474 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112703 ⟨875474, by decide⟩ :=
  accepted_of_selected 12 112703 ⟨875474, by decide⟩ ⟨12, 2, 0, 875474, 112703, 3077, 65536⟩
    (by decide) selected_cut_33944

theorem unmarked_context_11_28175_875475 : frontier 10 ⟨875475, by decide⟩
    (prefixCache 11 28175) (prefixPartial 11 28175) = false := by
  decide +kernel

theorem node_context_11_28175_875475 : EJMOriginalGlobalDAGData.nodes 10 ⟨875475, by decide⟩ =
    .split (coordinate 11) (![⟨875291, by decide⟩,⟨875364, by decide⟩,⟨875420, by decide⟩,⟨875474, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_28175_875475 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 28175 ⟨875475, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 28175
    ⟨875475, by decide⟩ (by decide) (![⟨875291, by decide⟩,⟨875364, by decide⟩,⟨875420, by decide⟩,⟨875474, by decide⟩]) unmarked_context_11_28175_875475 node_context_11_28175_875475
  intro a
  fin_cases a
  · exact context_12_112700_875291
  · exact context_12_112701_875364
  · exact context_12_112702_875420
  · exact context_12_112703_875474

theorem unmarked_context_10_7043_875476 : frontier 11 ⟨875476, by decide⟩
    (prefixCache 10 7043) (prefixPartial 10 7043) = false := by
  decide +kernel

theorem node_context_10_7043_875476 : EJMOriginalGlobalDAGData.nodes 11 ⟨875476, by decide⟩ =
    .split (coordinate 10) (![⟨874608, by decide⟩,⟨874953, by decide⟩,⟨875228, by decide⟩,⟨875475, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_7043_875476 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 7043 ⟨875476, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 7043
    ⟨875476, by decide⟩ (by decide) (![⟨874608, by decide⟩,⟨874953, by decide⟩,⟨875228, by decide⟩,⟨875475, by decide⟩]) unmarked_context_10_7043_875476 node_context_10_7043_875476
  intro a
  fin_cases a
  · exact context_11_28172_874608
  · exact context_11_28173_874953
  · exact context_11_28174_875228
  · exact context_11_28175_875475

theorem unmarked_context_9_1760_875477 : frontier 12 ⟨875477, by decide⟩
    (prefixCache 9 1760) (prefixPartial 9 1760) = false := by
  decide +kernel

theorem node_context_9_1760_875477 : EJMOriginalGlobalDAGData.nodes 12 ⟨875477, by decide⟩ =
    .split (coordinate 9) (![⟨871375, by decide⟩,⟨872927, by decide⟩,⟨874288, by decide⟩,⟨875476, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1760_875477 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1760 ⟨875477, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1760
    ⟨875477, by decide⟩ (by decide) (![⟨871375, by decide⟩,⟨872927, by decide⟩,⟨874288, by decide⟩,⟨875476, by decide⟩]) unmarked_context_9_1760_875477 node_context_9_1760_875477
  intro a
  fin_cases a
  · exact context_10_7040_871375
  · exact context_10_7041_872927
  · exact context_10_7042_874288
  · exact context_10_7043_875476

theorem selected_cut_33945 : selected 11 ⟨875478, by decide⟩
    (prefixPartial 10 7044) = some ⟨10, 1, 0, 875478, 7044, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_7044_875478 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 7044 ⟨875478, by decide⟩ :=
  accepted_of_selected 10 7044 ⟨875478, by decide⟩ ⟨10, 1, 0, 875478, 7044, 1, 1048576⟩
    (by decide) selected_cut_33945

theorem selected_cut_33946 : selected 9 ⟨307381, by decide⟩
    (prefixPartial 12 112720) = some ⟨12, 1, 0, 307381, 112720, 1, 65536⟩ := by
  decide +kernel

theorem context_12_112720_307381 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112720 ⟨307381, by decide⟩ :=
  accepted_of_selected 12 112720 ⟨307381, by decide⟩ ⟨12, 1, 0, 307381, 112720, 1, 65536⟩
    (by decide) selected_cut_33946

theorem selected_cut_33947 : selected 9 ⟨875633, by decide⟩
    (prefixPartial 12 112721) = some ⟨12, 2, 0, 875633, 112721, 3325, 65536⟩ := by
  decide +kernel

theorem context_12_112721_875633 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112721 ⟨875633, by decide⟩ :=
  accepted_of_selected 12 112721 ⟨875633, by decide⟩ ⟨12, 2, 0, 875633, 112721, 3325, 65536⟩
    (by decide) selected_cut_33947

theorem selected_cut_33948 : selected 9 ⟨875712, by decide⟩
    (prefixPartial 12 112722) = some ⟨12, 2, 0, 875712, 112722, 2861, 65536⟩ := by
  decide +kernel

theorem context_12_112722_875712 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112722 ⟨875712, by decide⟩ :=
  accepted_of_selected 12 112722 ⟨875712, by decide⟩ ⟨12, 2, 0, 875712, 112722, 2861, 65536⟩
    (by decide) selected_cut_33948

theorem selected_cut_33949 : selected 9 ⟨875775, by decide⟩
    (prefixPartial 12 112723) = some ⟨12, 2, 0, 875775, 112723, 2861, 65536⟩ := by
  decide +kernel

theorem context_12_112723_875775 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112723 ⟨875775, by decide⟩ :=
  accepted_of_selected 12 112723 ⟨875775, by decide⟩ ⟨12, 2, 0, 875775, 112723, 2861, 65536⟩
    (by decide) selected_cut_33949

theorem unmarked_context_11_28180_875776 : frontier 10 ⟨875776, by decide⟩
    (prefixCache 11 28180) (prefixPartial 11 28180) = false := by
  decide +kernel

theorem node_context_11_28180_875776 : EJMOriginalGlobalDAGData.nodes 10 ⟨875776, by decide⟩ =
    .split (coordinate 11) (![⟨307381, by decide⟩,⟨875633, by decide⟩,⟨875712, by decide⟩,⟨875775, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_28180_875776 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 28180 ⟨875776, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 28180
    ⟨875776, by decide⟩ (by decide) (![⟨307381, by decide⟩,⟨875633, by decide⟩,⟨875712, by decide⟩,⟨875775, by decide⟩]) unmarked_context_11_28180_875776 node_context_11_28180_875776
  intro a
  fin_cases a
  · exact context_12_112720_307381
  · exact context_12_112721_875633
  · exact context_12_112722_875712
  · exact context_12_112723_875775

theorem selected_cut_33950 : selected 9 ⟨875849, by decide⟩
    (prefixPartial 12 112724) = some ⟨12, 2, 0, 875849, 112724, 2517, 65536⟩ := by
  decide +kernel

theorem context_12_112724_875849 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112724 ⟨875849, by decide⟩ :=
  accepted_of_selected 12 112724 ⟨875849, by decide⟩ ⟨12, 2, 0, 875849, 112724, 2517, 65536⟩
    (by decide) selected_cut_33950

theorem selected_cut_33951 : selected 9 ⟨875958, by decide⟩
    (prefixPartial 12 112725) = some ⟨12, 2, 0, 875958, 112725, 2917, 65536⟩ := by
  decide +kernel

theorem context_12_112725_875958 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112725 ⟨875958, by decide⟩ :=
  accepted_of_selected 12 112725 ⟨875958, by decide⟩ ⟨12, 2, 0, 875958, 112725, 2917, 65536⟩
    (by decide) selected_cut_33951

theorem selected_cut_33952 : selected 9 ⟨876022, by decide⟩
    (prefixPartial 12 112726) = some ⟨12, 2, 0, 876022, 112726, 2489, 65536⟩ := by
  decide +kernel

theorem context_12_112726_876022 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112726 ⟨876022, by decide⟩ :=
  accepted_of_selected 12 112726 ⟨876022, by decide⟩ ⟨12, 2, 0, 876022, 112726, 2489, 65536⟩
    (by decide) selected_cut_33952

theorem selected_cut_33953 : selected 9 ⟨876097, by decide⟩
    (prefixPartial 12 112727) = some ⟨12, 2, 0, 876097, 112727, 2629, 65536⟩ := by
  decide +kernel

theorem context_12_112727_876097 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112727 ⟨876097, by decide⟩ :=
  accepted_of_selected 12 112727 ⟨876097, by decide⟩ ⟨12, 2, 0, 876097, 112727, 2629, 65536⟩
    (by decide) selected_cut_33953

theorem unmarked_context_11_28181_876098 : frontier 10 ⟨876098, by decide⟩
    (prefixCache 11 28181) (prefixPartial 11 28181) = false := by
  decide +kernel

theorem node_context_11_28181_876098 : EJMOriginalGlobalDAGData.nodes 10 ⟨876098, by decide⟩ =
    .split (coordinate 11) (![⟨875849, by decide⟩,⟨875958, by decide⟩,⟨876022, by decide⟩,⟨876097, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_28181_876098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 28181 ⟨876098, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 28181
    ⟨876098, by decide⟩ (by decide) (![⟨875849, by decide⟩,⟨875958, by decide⟩,⟨876022, by decide⟩,⟨876097, by decide⟩]) unmarked_context_11_28181_876098 node_context_11_28181_876098
  intro a
  fin_cases a
  · exact context_12_112724_875849
  · exact context_12_112725_875958
  · exact context_12_112726_876022
  · exact context_12_112727_876097

theorem selected_cut_33954 : selected 9 ⟨876148, by decide⟩
    (prefixPartial 12 112728) = some ⟨12, 2, 0, 876148, 112728, 2269, 65536⟩ := by
  decide +kernel

theorem context_12_112728_876148 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112728 ⟨876148, by decide⟩ :=
  accepted_of_selected 12 112728 ⟨876148, by decide⟩ ⟨12, 2, 0, 876148, 112728, 2269, 65536⟩
    (by decide) selected_cut_33954

theorem selected_cut_33955 : selected 9 ⟨876236, by decide⟩
    (prefixPartial 12 112729) = some ⟨12, 2, 0, 876236, 112729, 2713, 65536⟩ := by
  decide +kernel

theorem context_12_112729_876236 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112729 ⟨876236, by decide⟩ :=
  accepted_of_selected 12 112729 ⟨876236, by decide⟩ ⟨12, 2, 0, 876236, 112729, 2713, 65536⟩
    (by decide) selected_cut_33955

theorem selected_cut_33956 : selected 9 ⟨876276, by decide⟩
    (prefixPartial 12 112730) = some ⟨12, 2, 0, 876276, 112730, 2289, 65536⟩ := by
  decide +kernel

theorem context_12_112730_876276 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112730 ⟨876276, by decide⟩ :=
  accepted_of_selected 12 112730 ⟨876276, by decide⟩ ⟨12, 2, 0, 876276, 112730, 2289, 65536⟩
    (by decide) selected_cut_33956

theorem selected_cut_33957 : selected 9 ⟨876326, by decide⟩
    (prefixPartial 12 112731) = some ⟨12, 2, 0, 876326, 112731, 2397, 65536⟩ := by
  decide +kernel

theorem context_12_112731_876326 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112731 ⟨876326, by decide⟩ :=
  accepted_of_selected 12 112731 ⟨876326, by decide⟩ ⟨12, 2, 0, 876326, 112731, 2397, 65536⟩
    (by decide) selected_cut_33957

theorem unmarked_context_11_28182_876327 : frontier 10 ⟨876327, by decide⟩
    (prefixCache 11 28182) (prefixPartial 11 28182) = false := by
  decide +kernel

theorem node_context_11_28182_876327 : EJMOriginalGlobalDAGData.nodes 10 ⟨876327, by decide⟩ =
    .split (coordinate 11) (![⟨876148, by decide⟩,⟨876236, by decide⟩,⟨876276, by decide⟩,⟨876326, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_28182_876327 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 28182 ⟨876327, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 28182
    ⟨876327, by decide⟩ (by decide) (![⟨876148, by decide⟩,⟨876236, by decide⟩,⟨876276, by decide⟩,⟨876326, by decide⟩]) unmarked_context_11_28182_876327 node_context_11_28182_876327
  intro a
  fin_cases a
  · exact context_12_112728_876148
  · exact context_12_112729_876236
  · exact context_12_112730_876276
  · exact context_12_112731_876326

theorem selected_cut_33958 : selected 9 ⟨876403, by decide⟩
    (prefixPartial 12 112732) = some ⟨12, 2, 0, 876403, 112732, 2525, 65536⟩ := by
  decide +kernel

theorem context_12_112732_876403 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112732 ⟨876403, by decide⟩ :=
  accepted_of_selected 12 112732 ⟨876403, by decide⟩ ⟨12, 2, 0, 876403, 112732, 2525, 65536⟩
    (by decide) selected_cut_33958

theorem selected_cut_33959 : selected 9 ⟨876505, by decide⟩
    (prefixPartial 12 112733) = some ⟨12, 2, 0, 876505, 112733, 2889, 65536⟩ := by
  decide +kernel

theorem context_12_112733_876505 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112733 ⟨876505, by decide⟩ :=
  accepted_of_selected 12 112733 ⟨876505, by decide⟩ ⟨12, 2, 0, 876505, 112733, 2889, 65536⟩
    (by decide) selected_cut_33959

theorem selected_cut_33960 : selected 9 ⟨876564, by decide⟩
    (prefixPartial 12 112734) = some ⟨12, 2, 0, 876564, 112734, 2421, 65536⟩ := by
  decide +kernel

theorem context_12_112734_876564 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112734 ⟨876564, by decide⟩ :=
  accepted_of_selected 12 112734 ⟨876564, by decide⟩ ⟨12, 2, 0, 876564, 112734, 2421, 65536⟩
    (by decide) selected_cut_33960

theorem selected_cut_33961 : selected 9 ⟨876616, by decide⟩
    (prefixPartial 12 112735) = some ⟨12, 2, 0, 876616, 112735, 2365, 65536⟩ := by
  decide +kernel

theorem context_12_112735_876616 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112735 ⟨876616, by decide⟩ :=
  accepted_of_selected 12 112735 ⟨876616, by decide⟩ ⟨12, 2, 0, 876616, 112735, 2365, 65536⟩
    (by decide) selected_cut_33961

theorem unmarked_context_11_28183_876617 : frontier 10 ⟨876617, by decide⟩
    (prefixCache 11 28183) (prefixPartial 11 28183) = false := by
  decide +kernel

theorem node_context_11_28183_876617 : EJMOriginalGlobalDAGData.nodes 10 ⟨876617, by decide⟩ =
    .split (coordinate 11) (![⟨876403, by decide⟩,⟨876505, by decide⟩,⟨876564, by decide⟩,⟨876616, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_28183_876617 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 28183 ⟨876617, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 28183
    ⟨876617, by decide⟩ (by decide) (![⟨876403, by decide⟩,⟨876505, by decide⟩,⟨876564, by decide⟩,⟨876616, by decide⟩]) unmarked_context_11_28183_876617 node_context_11_28183_876617
  intro a
  fin_cases a
  · exact context_12_112732_876403
  · exact context_12_112733_876505
  · exact context_12_112734_876564
  · exact context_12_112735_876616

theorem unmarked_context_10_7045_876618 : frontier 11 ⟨876618, by decide⟩
    (prefixCache 10 7045) (prefixPartial 10 7045) = false := by
  decide +kernel

theorem node_context_10_7045_876618 : EJMOriginalGlobalDAGData.nodes 11 ⟨876618, by decide⟩ =
    .split (coordinate 10) (![⟨875776, by decide⟩,⟨876098, by decide⟩,⟨876327, by decide⟩,⟨876617, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_7045_876618 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 7045 ⟨876618, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 7045
    ⟨876618, by decide⟩ (by decide) (![⟨875776, by decide⟩,⟨876098, by decide⟩,⟨876327, by decide⟩,⟨876617, by decide⟩]) unmarked_context_10_7045_876618 node_context_10_7045_876618
  intro a
  fin_cases a
  · exact context_11_28180_875776
  · exact context_11_28181_876098
  · exact context_11_28182_876327
  · exact context_11_28183_876617

theorem selected_cut_33962 : selected 9 ⟨765706, by decide⟩
    (prefixPartial 12 112736) = some ⟨12, 1, 0, 765706, 112736, 1, 65536⟩ := by
  decide +kernel

theorem context_12_112736_765706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112736 ⟨765706, by decide⟩ :=
  accepted_of_selected 12 112736 ⟨765706, by decide⟩ ⟨12, 1, 0, 765706, 112736, 1, 65536⟩
    (by decide) selected_cut_33962

theorem selected_cut_33963 : selected 9 ⟨876724, by decide⟩
    (prefixPartial 12 112737) = some ⟨12, 2, 0, 876724, 112737, 2025, 65536⟩ := by
  decide +kernel

theorem context_12_112737_876724 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112737 ⟨876724, by decide⟩ :=
  accepted_of_selected 12 112737 ⟨876724, by decide⟩ ⟨12, 2, 0, 876724, 112737, 2025, 65536⟩
    (by decide) selected_cut_33963

theorem selected_cut_33964 : selected 9 ⟨876784, by decide⟩
    (prefixPartial 12 112738) = some ⟨12, 2, 0, 876784, 112738, 1845, 65536⟩ := by
  decide +kernel

theorem context_12_112738_876784 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112738 ⟨876784, by decide⟩ :=
  accepted_of_selected 12 112738 ⟨876784, by decide⟩ ⟨12, 2, 0, 876784, 112738, 1845, 65536⟩
    (by decide) selected_cut_33964

theorem selected_cut_33965 : selected 9 ⟨876834, by decide⟩
    (prefixPartial 12 112739) = some ⟨12, 2, 0, 876834, 112739, 1821, 65536⟩ := by
  decide +kernel

theorem context_12_112739_876834 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112739 ⟨876834, by decide⟩ :=
  accepted_of_selected 12 112739 ⟨876834, by decide⟩ ⟨12, 2, 0, 876834, 112739, 1821, 65536⟩
    (by decide) selected_cut_33965

theorem unmarked_context_11_28184_876835 : frontier 10 ⟨876835, by decide⟩
    (prefixCache 11 28184) (prefixPartial 11 28184) = false := by
  decide +kernel

theorem node_context_11_28184_876835 : EJMOriginalGlobalDAGData.nodes 10 ⟨876835, by decide⟩ =
    .split (coordinate 11) (![⟨765706, by decide⟩,⟨876724, by decide⟩,⟨876784, by decide⟩,⟨876834, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_28184_876835 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 28184 ⟨876835, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 28184
    ⟨876835, by decide⟩ (by decide) (![⟨765706, by decide⟩,⟨876724, by decide⟩,⟨876784, by decide⟩,⟨876834, by decide⟩]) unmarked_context_11_28184_876835 node_context_11_28184_876835
  intro a
  fin_cases a
  · exact context_12_112736_765706
  · exact context_12_112737_876724
  · exact context_12_112738_876784
  · exact context_12_112739_876834

theorem selected_cut_33966 : selected 9 ⟨876898, by decide⟩
    (prefixPartial 12 112740) = some ⟨12, 2, 0, 876898, 112740, 1865, 65536⟩ := by
  decide +kernel

theorem context_12_112740_876898 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112740 ⟨876898, by decide⟩ :=
  accepted_of_selected 12 112740 ⟨876898, by decide⟩ ⟨12, 2, 0, 876898, 112740, 1865, 65536⟩
    (by decide) selected_cut_33966

theorem selected_cut_33967 : selected 9 ⟨876944, by decide⟩
    (prefixPartial 12 112741) = some ⟨12, 2, 0, 876944, 112741, 1801, 65536⟩ := by
  decide +kernel

theorem context_12_112741_876944 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112741 ⟨876944, by decide⟩ :=
  accepted_of_selected 12 112741 ⟨876944, by decide⟩ ⟨12, 2, 0, 876944, 112741, 1801, 65536⟩
    (by decide) selected_cut_33967

theorem selected_cut_33968 : selected 9 ⟨876999, by decide⟩
    (prefixPartial 12 112742) = some ⟨12, 2, 0, 876999, 112742, 1801, 65536⟩ := by
  decide +kernel

theorem context_12_112742_876999 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112742 ⟨876999, by decide⟩ :=
  accepted_of_selected 12 112742 ⟨876999, by decide⟩ ⟨12, 2, 0, 876999, 112742, 1801, 65536⟩
    (by decide) selected_cut_33968

theorem selected_cut_33969 : selected 9 ⟨877050, by decide⟩
    (prefixPartial 12 112743) = some ⟨12, 2, 0, 877050, 112743, 1777, 65536⟩ := by
  decide +kernel

theorem context_12_112743_877050 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112743 ⟨877050, by decide⟩ :=
  accepted_of_selected 12 112743 ⟨877050, by decide⟩ ⟨12, 2, 0, 877050, 112743, 1777, 65536⟩
    (by decide) selected_cut_33969

theorem unmarked_context_11_28185_877051 : frontier 10 ⟨877051, by decide⟩
    (prefixCache 11 28185) (prefixPartial 11 28185) = false := by
  decide +kernel

theorem node_context_11_28185_877051 : EJMOriginalGlobalDAGData.nodes 10 ⟨877051, by decide⟩ =
    .split (coordinate 11) (![⟨876898, by decide⟩,⟨876944, by decide⟩,⟨876999, by decide⟩,⟨877050, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_28185_877051 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 28185 ⟨877051, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 28185
    ⟨877051, by decide⟩ (by decide) (![⟨876898, by decide⟩,⟨876944, by decide⟩,⟨876999, by decide⟩,⟨877050, by decide⟩]) unmarked_context_11_28185_877051 node_context_11_28185_877051
  intro a
  fin_cases a
  · exact context_12_112740_876898
  · exact context_12_112741_876944
  · exact context_12_112742_876999
  · exact context_12_112743_877050

theorem selected_cut_33970 : selected 10 ⟨877098, by decide⟩
    (prefixPartial 11 28186) = some ⟨11, 2, 0, 877098, 28186, 385, 262144⟩ := by
  decide +kernel

theorem context_11_28186_877098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 28186 ⟨877098, by decide⟩ :=
  accepted_of_selected 11 28186 ⟨877098, by decide⟩ ⟨11, 2, 0, 877098, 28186, 385, 262144⟩
    (by decide) selected_cut_33970

theorem selected_cut_33971 : selected 9 ⟨877155, by decide⟩
    (prefixPartial 12 112748) = some ⟨12, 2, 0, 877155, 112748, 1749, 65536⟩ := by
  decide +kernel

theorem context_12_112748_877155 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112748 ⟨877155, by decide⟩ :=
  accepted_of_selected 12 112748 ⟨877155, by decide⟩ ⟨12, 2, 0, 877155, 112748, 1749, 65536⟩
    (by decide) selected_cut_33971

theorem selected_cut_33972 : selected 9 ⟨877203, by decide⟩
    (prefixPartial 12 112749) = some ⟨12, 2, 0, 877203, 112749, 1725, 65536⟩ := by
  decide +kernel

theorem context_12_112749_877203 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112749 ⟨877203, by decide⟩ :=
  accepted_of_selected 12 112749 ⟨877203, by decide⟩ ⟨12, 2, 0, 877203, 112749, 1725, 65536⟩
    (by decide) selected_cut_33972

theorem selected_cut_33973 : selected 9 ⟨877241, by decide⟩
    (prefixPartial 12 112750) = some ⟨12, 2, 0, 877241, 112750, 1617, 65536⟩ := by
  decide +kernel

theorem context_12_112750_877241 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112750 ⟨877241, by decide⟩ :=
  accepted_of_selected 12 112750 ⟨877241, by decide⟩ ⟨12, 2, 0, 877241, 112750, 1617, 65536⟩
    (by decide) selected_cut_33973

theorem selected_cut_33974 : selected 9 ⟨877280, by decide⟩
    (prefixPartial 12 112751) = some ⟨12, 2, 0, 877280, 112751, 1497, 65536⟩ := by
  decide +kernel

theorem context_12_112751_877280 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112751 ⟨877280, by decide⟩ :=
  accepted_of_selected 12 112751 ⟨877280, by decide⟩ ⟨12, 2, 0, 877280, 112751, 1497, 65536⟩
    (by decide) selected_cut_33974

theorem unmarked_context_11_28187_877281 : frontier 10 ⟨877281, by decide⟩
    (prefixCache 11 28187) (prefixPartial 11 28187) = false := by
  decide +kernel

theorem node_context_11_28187_877281 : EJMOriginalGlobalDAGData.nodes 10 ⟨877281, by decide⟩ =
    .split (coordinate 11) (![⟨877155, by decide⟩,⟨877203, by decide⟩,⟨877241, by decide⟩,⟨877280, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_28187_877281 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 28187 ⟨877281, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 28187
    ⟨877281, by decide⟩ (by decide) (![⟨877155, by decide⟩,⟨877203, by decide⟩,⟨877241, by decide⟩,⟨877280, by decide⟩]) unmarked_context_11_28187_877281 node_context_11_28187_877281
  intro a
  fin_cases a
  · exact context_12_112748_877155
  · exact context_12_112749_877203
  · exact context_12_112750_877241
  · exact context_12_112751_877280

theorem unmarked_context_10_7046_877282 : frontier 11 ⟨877282, by decide⟩
    (prefixCache 10 7046) (prefixPartial 10 7046) = false := by
  decide +kernel

theorem node_context_10_7046_877282 : EJMOriginalGlobalDAGData.nodes 11 ⟨877282, by decide⟩ =
    .split (coordinate 10) (![⟨876835, by decide⟩,⟨877051, by decide⟩,⟨877098, by decide⟩,⟨877281, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_7046_877282 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 7046 ⟨877282, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 7046
    ⟨877282, by decide⟩ (by decide) (![⟨876835, by decide⟩,⟨877051, by decide⟩,⟨877098, by decide⟩,⟨877281, by decide⟩]) unmarked_context_10_7046_877282 node_context_10_7046_877282
  intro a
  fin_cases a
  · exact context_11_28184_876835
  · exact context_11_28185_877051
  · exact context_11_28186_877098
  · exact context_11_28187_877281

theorem selected_cut_33975 : selected 10 ⟨877444, by decide⟩
    (prefixPartial 11 28188) = some ⟨11, 2, 0, 877444, 28188, 3753, 262144⟩ := by
  decide +kernel

theorem context_11_28188_877444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 28188 ⟨877444, by decide⟩ :=
  accepted_of_selected 11 28188 ⟨877444, by decide⟩ ⟨11, 2, 0, 877444, 28188, 3753, 262144⟩
    (by decide) selected_cut_33975

theorem selected_cut_33976 : selected 10 ⟨877562, by decide⟩
    (prefixPartial 11 28189) = some ⟨11, 2, 0, 877562, 28189, 2681, 262144⟩ := by
  decide +kernel

theorem context_11_28189_877562 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 28189 ⟨877562, by decide⟩ :=
  accepted_of_selected 11 28189 ⟨877562, by decide⟩ ⟨11, 2, 0, 877562, 28189, 2681, 262144⟩
    (by decide) selected_cut_33976

theorem selected_cut_33977 : selected 10 ⟨877615, by decide⟩
    (prefixPartial 11 28190) = some ⟨11, 2, 0, 877615, 28190, 1437, 262144⟩ := by
  decide +kernel

theorem context_11_28190_877615 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 28190 ⟨877615, by decide⟩ :=
  accepted_of_selected 11 28190 ⟨877615, by decide⟩ ⟨11, 2, 0, 877615, 28190, 1437, 262144⟩
    (by decide) selected_cut_33977

theorem selected_cut_33978 : selected 10 ⟨877644, by decide⟩
    (prefixPartial 11 28191) = some ⟨11, 2, 0, 877644, 28191, 601, 262144⟩ := by
  decide +kernel

theorem context_11_28191_877644 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 28191 ⟨877644, by decide⟩ :=
  accepted_of_selected 11 28191 ⟨877644, by decide⟩ ⟨11, 2, 0, 877644, 28191, 601, 262144⟩
    (by decide) selected_cut_33978

theorem unmarked_context_10_7047_877645 : frontier 11 ⟨877645, by decide⟩
    (prefixCache 10 7047) (prefixPartial 10 7047) = false := by
  decide +kernel

theorem node_context_10_7047_877645 : EJMOriginalGlobalDAGData.nodes 11 ⟨877645, by decide⟩ =
    .split (coordinate 10) (![⟨877444, by decide⟩,⟨877562, by decide⟩,⟨877615, by decide⟩,⟨877644, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_7047_877645 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 7047 ⟨877645, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 7047
    ⟨877645, by decide⟩ (by decide) (![⟨877444, by decide⟩,⟨877562, by decide⟩,⟨877615, by decide⟩,⟨877644, by decide⟩]) unmarked_context_10_7047_877645 node_context_10_7047_877645
  intro a
  fin_cases a
  · exact context_11_28188_877444
  · exact context_11_28189_877562
  · exact context_11_28190_877615
  · exact context_11_28191_877644

theorem unmarked_context_9_1761_877646 : frontier 12 ⟨877646, by decide⟩
    (prefixCache 9 1761) (prefixPartial 9 1761) = false := by
  decide +kernel

theorem node_context_9_1761_877646 : EJMOriginalGlobalDAGData.nodes 12 ⟨877646, by decide⟩ =
    .split (coordinate 9) (![⟨875478, by decide⟩,⟨876618, by decide⟩,⟨877282, by decide⟩,⟨877645, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1761_877646 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1761 ⟨877646, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1761
    ⟨877646, by decide⟩ (by decide) (![⟨875478, by decide⟩,⟨876618, by decide⟩,⟨877282, by decide⟩,⟨877645, by decide⟩]) unmarked_context_9_1761_877646 node_context_9_1761_877646
  intro a
  fin_cases a
  · exact context_10_7044_875478
  · exact context_10_7045_876618
  · exact context_10_7046_877282
  · exact context_10_7047_877645

theorem selected_cut_33979 : selected 11 ⟨875478, by decide⟩
    (prefixPartial 10 7048) = some ⟨10, 1, 0, 875478, 7048, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_7048_875478 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 7048 ⟨875478, by decide⟩ :=
  accepted_of_selected 10 7048 ⟨875478, by decide⟩ ⟨10, 1, 0, 875478, 7048, 1, 1048576⟩
    (by decide) selected_cut_33979

theorem selected_cut_33980 : selected 10 ⟨877772, by decide⟩
    (prefixPartial 11 28196) = some ⟨11, 2, 0, 877772, 28196, 1985, 262144⟩ := by
  decide +kernel

theorem context_11_28196_877772 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 28196 ⟨877772, by decide⟩ :=
  accepted_of_selected 11 28196 ⟨877772, by decide⟩ ⟨11, 2, 0, 877772, 28196, 1985, 262144⟩
    (by decide) selected_cut_33980

theorem selected_cut_33981 : selected 10 ⟨877875, by decide⟩
    (prefixPartial 11 28197) = some ⟨11, 2, 0, 877875, 28197, 2377, 262144⟩ := by
  decide +kernel

theorem context_11_28197_877875 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 28197 ⟨877875, by decide⟩ :=
  accepted_of_selected 11 28197 ⟨877875, by decide⟩ ⟨11, 2, 0, 877875, 28197, 2377, 262144⟩
    (by decide) selected_cut_33981

theorem selected_cut_33982 : selected 10 ⟨877956, by decide⟩
    (prefixPartial 11 28198) = some ⟨11, 2, 0, 877956, 28198, 2129, 262144⟩ := by
  decide +kernel

theorem context_11_28198_877956 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 28198 ⟨877956, by decide⟩ :=
  accepted_of_selected 11 28198 ⟨877956, by decide⟩ ⟨11, 2, 0, 877956, 28198, 2129, 262144⟩
    (by decide) selected_cut_33982

theorem selected_cut_33983 : selected 10 ⟨878069, by decide⟩
    (prefixPartial 11 28199) = some ⟨11, 2, 0, 878069, 28199, 2037, 262144⟩ := by
  decide +kernel

theorem context_11_28199_878069 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 28199 ⟨878069, by decide⟩ :=
  accepted_of_selected 11 28199 ⟨878069, by decide⟩ ⟨11, 2, 0, 878069, 28199, 2037, 262144⟩
    (by decide) selected_cut_33983

theorem unmarked_context_10_7049_878070 : frontier 11 ⟨878070, by decide⟩
    (prefixCache 10 7049) (prefixPartial 10 7049) = false := by
  decide +kernel

theorem node_context_10_7049_878070 : EJMOriginalGlobalDAGData.nodes 11 ⟨878070, by decide⟩ =
    .split (coordinate 10) (![⟨877772, by decide⟩,⟨877875, by decide⟩,⟨877956, by decide⟩,⟨878069, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_7049_878070 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 7049 ⟨878070, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 7049
    ⟨878070, by decide⟩ (by decide) (![⟨877772, by decide⟩,⟨877875, by decide⟩,⟨877956, by decide⟩,⟨878069, by decide⟩]) unmarked_context_10_7049_878070 node_context_10_7049_878070
  intro a
  fin_cases a
  · exact context_11_28196_877772
  · exact context_11_28197_877875
  · exact context_11_28198_877956
  · exact context_11_28199_878069

theorem selected_cut_33984 : selected 11 ⟨878136, by decide⟩
    (prefixPartial 10 7050) = some ⟨10, 2, 0, 878136, 7050, 1341, 1048576⟩ := by
  decide +kernel

theorem context_10_7050_878136 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 7050 ⟨878136, by decide⟩ :=
  accepted_of_selected 10 7050 ⟨878136, by decide⟩ ⟨10, 2, 0, 878136, 7050, 1341, 1048576⟩
    (by decide) selected_cut_33984

theorem selected_cut_33985 : selected 11 ⟨875478, by decide⟩
    (prefixPartial 10 7051) = some ⟨10, 1, 0, 875478, 7051, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_7051_875478 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 7051 ⟨875478, by decide⟩ :=
  accepted_of_selected 10 7051 ⟨875478, by decide⟩ ⟨10, 1, 0, 875478, 7051, 1, 1048576⟩
    (by decide) selected_cut_33985

theorem unmarked_context_9_1762_878137 : frontier 12 ⟨878137, by decide⟩
    (prefixCache 9 1762) (prefixPartial 9 1762) = false := by
  decide +kernel

theorem node_context_9_1762_878137 : EJMOriginalGlobalDAGData.nodes 12 ⟨878137, by decide⟩ =
    .split (coordinate 9) (![⟨875478, by decide⟩,⟨878070, by decide⟩,⟨878136, by decide⟩,⟨875478, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1762_878137 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1762 ⟨878137, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1762
    ⟨878137, by decide⟩ (by decide) (![⟨875478, by decide⟩,⟨878070, by decide⟩,⟨878136, by decide⟩,⟨875478, by decide⟩]) unmarked_context_9_1762_878137 node_context_9_1762_878137
  intro a
  fin_cases a
  · exact context_10_7048_875478
  · exact context_10_7049_878070
  · exact context_10_7050_878136
  · exact context_10_7051_875478

theorem selected_cut_33986 : selected 12 ⟨878223, by decide⟩
    (prefixPartial 9 1763) = some ⟨9, 2, 0, 878223, 1763, 1069, 4194304⟩ := by
  decide +kernel

theorem context_9_1763_878223 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1763 ⟨878223, by decide⟩ :=
  accepted_of_selected 9 1763 ⟨878223, by decide⟩ ⟨9, 2, 0, 878223, 1763, 1069, 4194304⟩
    (by decide) selected_cut_33986

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
