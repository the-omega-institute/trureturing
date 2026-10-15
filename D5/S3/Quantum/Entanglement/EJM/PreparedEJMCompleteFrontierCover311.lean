/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover310
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_29860 : selected 9 ⟨753717, by decide⟩
    (prefixPartial 12 93835) = some ⟨12, 2, 0, 753717, 93835, 2221, 65536⟩ := by
  decide +kernel

theorem context_12_93835_753717 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93835 ⟨753717, by decide⟩ :=
  accepted_of_selected 12 93835 ⟨753717, by decide⟩ ⟨12, 2, 0, 753717, 93835, 2221, 65536⟩
    (by decide) selected_cut_29860

theorem unmarked_context_11_23458_753718 : frontier 10 ⟨753718, by decide⟩
    (prefixCache 11 23458) (prefixPartial 11 23458) = false := by
  decide +kernel

theorem node_context_11_23458_753718 : EJMOriginalGlobalDAGData.nodes 10 ⟨753718, by decide⟩ =
    .split (coordinate 11) (![⟨753663, by decide⟩,⟨753689, by decide⟩,⟨448662, by decide⟩,⟨753717, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23458_753718 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23458 ⟨753718, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23458
    ⟨753718, by decide⟩ (by decide) (![⟨753663, by decide⟩,⟨753689, by decide⟩,⟨448662, by decide⟩,⟨753717, by decide⟩]) unmarked_context_11_23458_753718 node_context_11_23458_753718
  intro a
  fin_cases a
  · exact context_12_93832_753663
  · exact context_12_93833_753689
  · exact context_12_93834_448662
  · exact context_12_93835_753717

theorem selected_cut_29861 : selected 9 ⟨753748, by decide⟩
    (prefixPartial 12 93836) = some ⟨12, 2, 0, 753748, 93836, 2149, 65536⟩ := by
  decide +kernel

theorem context_12_93836_753748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93836 ⟨753748, by decide⟩ :=
  accepted_of_selected 12 93836 ⟨753748, by decide⟩ ⟨12, 2, 0, 753748, 93836, 2149, 65536⟩
    (by decide) selected_cut_29861

theorem selected_cut_29862 : selected 9 ⟨753776, by decide⟩
    (prefixPartial 12 93837) = some ⟨12, 2, 0, 753776, 93837, 1949, 65536⟩ := by
  decide +kernel

theorem context_12_93837_753776 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93837 ⟨753776, by decide⟩ :=
  accepted_of_selected 12 93837 ⟨753776, by decide⟩ ⟨12, 2, 0, 753776, 93837, 1949, 65536⟩
    (by decide) selected_cut_29862

theorem selected_cut_29863 : selected 9 ⟨753804, by decide⟩
    (prefixPartial 12 93838) = some ⟨12, 2, 0, 753804, 93838, 2005, 65536⟩ := by
  decide +kernel

theorem context_12_93838_753804 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93838 ⟨753804, by decide⟩ :=
  accepted_of_selected 12 93838 ⟨753804, by decide⟩ ⟨12, 2, 0, 753804, 93838, 2005, 65536⟩
    (by decide) selected_cut_29863

theorem selected_cut_29864 : selected 9 ⟨753825, by decide⟩
    (prefixPartial 12 93839) = some ⟨12, 2, 0, 753825, 93839, 2341, 65536⟩ := by
  decide +kernel

theorem context_12_93839_753825 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93839 ⟨753825, by decide⟩ :=
  accepted_of_selected 12 93839 ⟨753825, by decide⟩ ⟨12, 2, 0, 753825, 93839, 2341, 65536⟩
    (by decide) selected_cut_29864

theorem unmarked_context_11_23459_753826 : frontier 10 ⟨753826, by decide⟩
    (prefixCache 11 23459) (prefixPartial 11 23459) = false := by
  decide +kernel

theorem node_context_11_23459_753826 : EJMOriginalGlobalDAGData.nodes 10 ⟨753826, by decide⟩ =
    .split (coordinate 11) (![⟨753748, by decide⟩,⟨753776, by decide⟩,⟨753804, by decide⟩,⟨753825, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23459_753826 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23459 ⟨753826, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23459
    ⟨753826, by decide⟩ (by decide) (![⟨753748, by decide⟩,⟨753776, by decide⟩,⟨753804, by decide⟩,⟨753825, by decide⟩]) unmarked_context_11_23459_753826 node_context_11_23459_753826
  intro a
  fin_cases a
  · exact context_12_93836_753748
  · exact context_12_93837_753776
  · exact context_12_93838_753804
  · exact context_12_93839_753825

theorem unmarked_context_10_5864_753827 : frontier 11 ⟨753827, by decide⟩
    (prefixCache 10 5864) (prefixPartial 10 5864) = false := by
  decide +kernel

theorem node_context_10_5864_753827 : EJMOriginalGlobalDAGData.nodes 11 ⟨753827, by decide⟩ =
    .split (coordinate 10) (![⟨753535, by decide⟩,⟨753637, by decide⟩,⟨753718, by decide⟩,⟨753826, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5864_753827 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5864 ⟨753827, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5864
    ⟨753827, by decide⟩ (by decide) (![⟨753535, by decide⟩,⟨753637, by decide⟩,⟨753718, by decide⟩,⟨753826, by decide⟩]) unmarked_context_10_5864_753827 node_context_10_5864_753827
  intro a
  fin_cases a
  · exact context_11_23456_753535
  · exact context_11_23457_753637
  · exact context_11_23458_753718
  · exact context_11_23459_753826

theorem selected_cut_29865 : selected 9 ⟨753849, by decide⟩
    (prefixPartial 12 93840) = some ⟨12, 2, 0, 753849, 93840, 2345, 65536⟩ := by
  decide +kernel

theorem context_12_93840_753849 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93840 ⟨753849, by decide⟩ :=
  accepted_of_selected 12 93840 ⟨753849, by decide⟩ ⟨12, 2, 0, 753849, 93840, 2345, 65536⟩
    (by decide) selected_cut_29865

theorem selected_cut_29866 : selected 9 ⟨753875, by decide⟩
    (prefixPartial 12 93841) = some ⟨12, 2, 0, 753875, 93841, 2441, 65536⟩ := by
  decide +kernel

theorem context_12_93841_753875 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93841 ⟨753875, by decide⟩ :=
  accepted_of_selected 12 93841 ⟨753875, by decide⟩ ⟨12, 2, 0, 753875, 93841, 2441, 65536⟩
    (by decide) selected_cut_29866

theorem selected_cut_29867 : selected 9 ⟨753901, by decide⟩
    (prefixPartial 12 93842) = some ⟨12, 2, 0, 753901, 93842, 2189, 65536⟩ := by
  decide +kernel

theorem context_12_93842_753901 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93842 ⟨753901, by decide⟩ :=
  accepted_of_selected 12 93842 ⟨753901, by decide⟩ ⟨12, 2, 0, 753901, 93842, 2189, 65536⟩
    (by decide) selected_cut_29867

theorem selected_cut_29868 : selected 9 ⟨753949, by decide⟩
    (prefixPartial 12 93843) = some ⟨12, 2, 0, 753949, 93843, 2613, 65536⟩ := by
  decide +kernel

theorem context_12_93843_753949 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93843 ⟨753949, by decide⟩ :=
  accepted_of_selected 12 93843 ⟨753949, by decide⟩ ⟨12, 2, 0, 753949, 93843, 2613, 65536⟩
    (by decide) selected_cut_29868

theorem unmarked_context_11_23460_753950 : frontier 10 ⟨753950, by decide⟩
    (prefixCache 11 23460) (prefixPartial 11 23460) = false := by
  decide +kernel

theorem node_context_11_23460_753950 : EJMOriginalGlobalDAGData.nodes 10 ⟨753950, by decide⟩ =
    .split (coordinate 11) (![⟨753849, by decide⟩,⟨753875, by decide⟩,⟨753901, by decide⟩,⟨753949, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23460_753950 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23460 ⟨753950, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23460
    ⟨753950, by decide⟩ (by decide) (![⟨753849, by decide⟩,⟨753875, by decide⟩,⟨753901, by decide⟩,⟨753949, by decide⟩]) unmarked_context_11_23460_753950 node_context_11_23460_753950
  intro a
  fin_cases a
  · exact context_12_93840_753849
  · exact context_12_93841_753875
  · exact context_12_93842_753901
  · exact context_12_93843_753949

theorem selected_cut_29869 : selected 9 ⟨753982, by decide⟩
    (prefixPartial 12 93844) = some ⟨12, 2, 0, 753982, 93844, 2265, 65536⟩ := by
  decide +kernel

theorem context_12_93844_753982 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93844 ⟨753982, by decide⟩ :=
  accepted_of_selected 12 93844 ⟨753982, by decide⟩ ⟨12, 2, 0, 753982, 93844, 2265, 65536⟩
    (by decide) selected_cut_29869

theorem selected_cut_29870 : selected 9 ⟨754007, by decide⟩
    (prefixPartial 12 93845) = some ⟨12, 2, 0, 754007, 93845, 2361, 65536⟩ := by
  decide +kernel

theorem context_12_93845_754007 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93845 ⟨754007, by decide⟩ :=
  accepted_of_selected 12 93845 ⟨754007, by decide⟩ ⟨12, 2, 0, 754007, 93845, 2361, 65536⟩
    (by decide) selected_cut_29870

theorem selected_cut_29871 : selected 9 ⟨754025, by decide⟩
    (prefixPartial 12 93846) = some ⟨12, 2, 0, 754025, 93846, 2085, 65536⟩ := by
  decide +kernel

theorem context_12_93846_754025 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93846 ⟨754025, by decide⟩ :=
  accepted_of_selected 12 93846 ⟨754025, by decide⟩ ⟨12, 2, 0, 754025, 93846, 2085, 65536⟩
    (by decide) selected_cut_29871

theorem selected_cut_29872 : selected 9 ⟨754064, by decide⟩
    (prefixPartial 12 93847) = some ⟨12, 2, 0, 754064, 93847, 2481, 65536⟩ := by
  decide +kernel

theorem context_12_93847_754064 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93847 ⟨754064, by decide⟩ :=
  accepted_of_selected 12 93847 ⟨754064, by decide⟩ ⟨12, 2, 0, 754064, 93847, 2481, 65536⟩
    (by decide) selected_cut_29872

theorem unmarked_context_11_23461_754065 : frontier 10 ⟨754065, by decide⟩
    (prefixCache 11 23461) (prefixPartial 11 23461) = false := by
  decide +kernel

theorem node_context_11_23461_754065 : EJMOriginalGlobalDAGData.nodes 10 ⟨754065, by decide⟩ =
    .split (coordinate 11) (![⟨753982, by decide⟩,⟨754007, by decide⟩,⟨754025, by decide⟩,⟨754064, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23461_754065 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23461 ⟨754065, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23461
    ⟨754065, by decide⟩ (by decide) (![⟨753982, by decide⟩,⟨754007, by decide⟩,⟨754025, by decide⟩,⟨754064, by decide⟩]) unmarked_context_11_23461_754065 node_context_11_23461_754065
  intro a
  fin_cases a
  · exact context_12_93844_753982
  · exact context_12_93845_754007
  · exact context_12_93846_754025
  · exact context_12_93847_754064

theorem selected_cut_29873 : selected 9 ⟨754091, by decide⟩
    (prefixPartial 12 93848) = some ⟨12, 2, 0, 754091, 93848, 2097, 65536⟩ := by
  decide +kernel

theorem context_12_93848_754091 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93848 ⟨754091, by decide⟩ :=
  accepted_of_selected 12 93848 ⟨754091, by decide⟩ ⟨12, 2, 0, 754091, 93848, 2097, 65536⟩
    (by decide) selected_cut_29873

theorem selected_cut_29874 : selected 9 ⟨754115, by decide⟩
    (prefixPartial 12 93849) = some ⟨12, 2, 0, 754115, 93849, 2249, 65536⟩ := by
  decide +kernel

theorem context_12_93849_754115 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93849 ⟨754115, by decide⟩ :=
  accepted_of_selected 12 93849 ⟨754115, by decide⟩ ⟨12, 2, 0, 754115, 93849, 2249, 65536⟩
    (by decide) selected_cut_29874

theorem selected_cut_29875 : selected 9 ⟨448662, by decide⟩
    (prefixPartial 12 93850) = some ⟨12, 1, 0, 448662, 93850, 1, 65536⟩ := by
  decide +kernel

theorem context_12_93850_448662 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93850 ⟨448662, by decide⟩ :=
  accepted_of_selected 12 93850 ⟨448662, by decide⟩ ⟨12, 1, 0, 448662, 93850, 1, 65536⟩
    (by decide) selected_cut_29875

theorem selected_cut_29876 : selected 9 ⟨754144, by decide⟩
    (prefixPartial 12 93851) = some ⟨12, 2, 0, 754144, 93851, 2125, 65536⟩ := by
  decide +kernel

theorem context_12_93851_754144 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93851 ⟨754144, by decide⟩ :=
  accepted_of_selected 12 93851 ⟨754144, by decide⟩ ⟨12, 2, 0, 754144, 93851, 2125, 65536⟩
    (by decide) selected_cut_29876

theorem unmarked_context_11_23462_754145 : frontier 10 ⟨754145, by decide⟩
    (prefixCache 11 23462) (prefixPartial 11 23462) = false := by
  decide +kernel

theorem node_context_11_23462_754145 : EJMOriginalGlobalDAGData.nodes 10 ⟨754145, by decide⟩ =
    .split (coordinate 11) (![⟨754091, by decide⟩,⟨754115, by decide⟩,⟨448662, by decide⟩,⟨754144, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23462_754145 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23462 ⟨754145, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23462
    ⟨754145, by decide⟩ (by decide) (![⟨754091, by decide⟩,⟨754115, by decide⟩,⟨448662, by decide⟩,⟨754144, by decide⟩]) unmarked_context_11_23462_754145 node_context_11_23462_754145
  intro a
  fin_cases a
  · exact context_12_93848_754091
  · exact context_12_93849_754115
  · exact context_12_93850_448662
  · exact context_12_93851_754144

theorem selected_cut_29877 : selected 9 ⟨754167, by decide⟩
    (prefixPartial 12 93852) = some ⟨12, 2, 0, 754167, 93852, 1957, 65536⟩ := by
  decide +kernel

theorem context_12_93852_754167 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93852 ⟨754167, by decide⟩ :=
  accepted_of_selected 12 93852 ⟨754167, by decide⟩ ⟨12, 2, 0, 754167, 93852, 1957, 65536⟩
    (by decide) selected_cut_29877

theorem selected_cut_29878 : selected 9 ⟨754188, by decide⟩
    (prefixPartial 12 93853) = some ⟨12, 2, 0, 754188, 93853, 2045, 65536⟩ := by
  decide +kernel

theorem context_12_93853_754188 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93853 ⟨754188, by decide⟩ :=
  accepted_of_selected 12 93853 ⟨754188, by decide⟩ ⟨12, 2, 0, 754188, 93853, 2045, 65536⟩
    (by decide) selected_cut_29878

theorem selected_cut_29879 : selected 9 ⟨754210, by decide⟩
    (prefixPartial 12 93854) = some ⟨12, 2, 0, 754210, 93854, 1809, 65536⟩ := by
  decide +kernel

theorem context_12_93854_754210 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93854 ⟨754210, by decide⟩ :=
  accepted_of_selected 12 93854 ⟨754210, by decide⟩ ⟨12, 2, 0, 754210, 93854, 1809, 65536⟩
    (by decide) selected_cut_29879

theorem selected_cut_29880 : selected 9 ⟨754234, by decide⟩
    (prefixPartial 12 93855) = some ⟨12, 2, 0, 754234, 93855, 2141, 65536⟩ := by
  decide +kernel

theorem context_12_93855_754234 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93855 ⟨754234, by decide⟩ :=
  accepted_of_selected 12 93855 ⟨754234, by decide⟩ ⟨12, 2, 0, 754234, 93855, 2141, 65536⟩
    (by decide) selected_cut_29880

theorem unmarked_context_11_23463_754235 : frontier 10 ⟨754235, by decide⟩
    (prefixCache 11 23463) (prefixPartial 11 23463) = false := by
  decide +kernel

theorem node_context_11_23463_754235 : EJMOriginalGlobalDAGData.nodes 10 ⟨754235, by decide⟩ =
    .split (coordinate 11) (![⟨754167, by decide⟩,⟨754188, by decide⟩,⟨754210, by decide⟩,⟨754234, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23463_754235 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23463 ⟨754235, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23463
    ⟨754235, by decide⟩ (by decide) (![⟨754167, by decide⟩,⟨754188, by decide⟩,⟨754210, by decide⟩,⟨754234, by decide⟩]) unmarked_context_11_23463_754235 node_context_11_23463_754235
  intro a
  fin_cases a
  · exact context_12_93852_754167
  · exact context_12_93853_754188
  · exact context_12_93854_754210
  · exact context_12_93855_754234

theorem unmarked_context_10_5865_754236 : frontier 11 ⟨754236, by decide⟩
    (prefixCache 10 5865) (prefixPartial 10 5865) = false := by
  decide +kernel

theorem node_context_10_5865_754236 : EJMOriginalGlobalDAGData.nodes 11 ⟨754236, by decide⟩ =
    .split (coordinate 10) (![⟨753950, by decide⟩,⟨754065, by decide⟩,⟨754145, by decide⟩,⟨754235, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5865_754236 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5865 ⟨754236, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5865
    ⟨754236, by decide⟩ (by decide) (![⟨753950, by decide⟩,⟨754065, by decide⟩,⟨754145, by decide⟩,⟨754235, by decide⟩]) unmarked_context_10_5865_754236 node_context_10_5865_754236
  intro a
  fin_cases a
  · exact context_11_23460_753950
  · exact context_11_23461_754065
  · exact context_11_23462_754145
  · exact context_11_23463_754235

theorem selected_cut_29881 : selected 9 ⟨754252, by decide⟩
    (prefixPartial 12 93856) = some ⟨12, 2, 0, 754252, 93856, 1497, 65536⟩ := by
  decide +kernel

theorem context_12_93856_754252 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93856 ⟨754252, by decide⟩ :=
  accepted_of_selected 12 93856 ⟨754252, by decide⟩ ⟨12, 2, 0, 754252, 93856, 1497, 65536⟩
    (by decide) selected_cut_29881

theorem selected_cut_29882 : selected 9 ⟨754272, by decide⟩
    (prefixPartial 12 93857) = some ⟨12, 2, 0, 754272, 93857, 1533, 65536⟩ := by
  decide +kernel

theorem context_12_93857_754272 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93857 ⟨754272, by decide⟩ :=
  accepted_of_selected 12 93857 ⟨754272, by decide⟩ ⟨12, 2, 0, 754272, 93857, 1533, 65536⟩
    (by decide) selected_cut_29882

theorem selected_cut_29883 : selected 9 ⟨754290, by decide⟩
    (prefixPartial 12 93858) = some ⟨12, 2, 0, 754290, 93858, 1349, 65536⟩ := by
  decide +kernel

theorem context_12_93858_754290 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93858 ⟨754290, by decide⟩ :=
  accepted_of_selected 12 93858 ⟨754290, by decide⟩ ⟨12, 2, 0, 754290, 93858, 1349, 65536⟩
    (by decide) selected_cut_29883

theorem selected_cut_29884 : selected 9 ⟨754314, by decide⟩
    (prefixPartial 12 93859) = some ⟨12, 2, 0, 754314, 93859, 1769, 65536⟩ := by
  decide +kernel

theorem context_12_93859_754314 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93859 ⟨754314, by decide⟩ :=
  accepted_of_selected 12 93859 ⟨754314, by decide⟩ ⟨12, 2, 0, 754314, 93859, 1769, 65536⟩
    (by decide) selected_cut_29884

theorem unmarked_context_11_23464_754315 : frontier 10 ⟨754315, by decide⟩
    (prefixCache 11 23464) (prefixPartial 11 23464) = false := by
  decide +kernel

theorem node_context_11_23464_754315 : EJMOriginalGlobalDAGData.nodes 10 ⟨754315, by decide⟩ =
    .split (coordinate 11) (![⟨754252, by decide⟩,⟨754272, by decide⟩,⟨754290, by decide⟩,⟨754314, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23464_754315 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23464 ⟨754315, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23464
    ⟨754315, by decide⟩ (by decide) (![⟨754252, by decide⟩,⟨754272, by decide⟩,⟨754290, by decide⟩,⟨754314, by decide⟩]) unmarked_context_11_23464_754315 node_context_11_23464_754315
  intro a
  fin_cases a
  · exact context_12_93856_754252
  · exact context_12_93857_754272
  · exact context_12_93858_754290
  · exact context_12_93859_754314

theorem selected_cut_29885 : selected 9 ⟨754331, by decide⟩
    (prefixPartial 12 93860) = some ⟨12, 2, 0, 754331, 93860, 1497, 65536⟩ := by
  decide +kernel

theorem context_12_93860_754331 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93860 ⟨754331, by decide⟩ :=
  accepted_of_selected 12 93860 ⟨754331, by decide⟩ ⟨12, 2, 0, 754331, 93860, 1497, 65536⟩
    (by decide) selected_cut_29885

theorem selected_cut_29886 : selected 9 ⟨754349, by decide⟩
    (prefixPartial 12 93861) = some ⟨12, 2, 0, 754349, 93861, 1481, 65536⟩ := by
  decide +kernel

theorem context_12_93861_754349 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93861 ⟨754349, by decide⟩ :=
  accepted_of_selected 12 93861 ⟨754349, by decide⟩ ⟨12, 2, 0, 754349, 93861, 1481, 65536⟩
    (by decide) selected_cut_29886

theorem selected_cut_29887 : selected 9 ⟨754366, by decide⟩
    (prefixPartial 12 93862) = some ⟨12, 2, 0, 754366, 93862, 1345, 65536⟩ := by
  decide +kernel

theorem context_12_93862_754366 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93862 ⟨754366, by decide⟩ :=
  accepted_of_selected 12 93862 ⟨754366, by decide⟩ ⟨12, 2, 0, 754366, 93862, 1345, 65536⟩
    (by decide) selected_cut_29887

theorem selected_cut_29888 : selected 9 ⟨754392, by decide⟩
    (prefixPartial 12 93863) = some ⟨12, 2, 0, 754392, 93863, 1705, 65536⟩ := by
  decide +kernel

theorem context_12_93863_754392 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93863 ⟨754392, by decide⟩ :=
  accepted_of_selected 12 93863 ⟨754392, by decide⟩ ⟨12, 2, 0, 754392, 93863, 1705, 65536⟩
    (by decide) selected_cut_29888

theorem unmarked_context_11_23465_754393 : frontier 10 ⟨754393, by decide⟩
    (prefixCache 11 23465) (prefixPartial 11 23465) = false := by
  decide +kernel

theorem node_context_11_23465_754393 : EJMOriginalGlobalDAGData.nodes 10 ⟨754393, by decide⟩ =
    .split (coordinate 11) (![⟨754331, by decide⟩,⟨754349, by decide⟩,⟨754366, by decide⟩,⟨754392, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23465_754393 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23465 ⟨754393, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23465
    ⟨754393, by decide⟩ (by decide) (![⟨754331, by decide⟩,⟨754349, by decide⟩,⟨754366, by decide⟩,⟨754392, by decide⟩]) unmarked_context_11_23465_754393 node_context_11_23465_754393
  intro a
  fin_cases a
  · exact context_12_93860_754331
  · exact context_12_93861_754349
  · exact context_12_93862_754366
  · exact context_12_93863_754392

theorem selected_cut_29889 : selected 9 ⟨754412, by decide⟩
    (prefixPartial 12 93864) = some ⟨12, 2, 0, 754412, 93864, 1413, 65536⟩ := by
  decide +kernel

theorem context_12_93864_754412 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93864 ⟨754412, by decide⟩ :=
  accepted_of_selected 12 93864 ⟨754412, by decide⟩ ⟨12, 2, 0, 754412, 93864, 1413, 65536⟩
    (by decide) selected_cut_29889

theorem selected_cut_29890 : selected 9 ⟨754429, by decide⟩
    (prefixPartial 12 93865) = some ⟨12, 2, 0, 754429, 93865, 1461, 65536⟩ := by
  decide +kernel

theorem context_12_93865_754429 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93865 ⟨754429, by decide⟩ :=
  accepted_of_selected 12 93865 ⟨754429, by decide⟩ ⟨12, 2, 0, 754429, 93865, 1461, 65536⟩
    (by decide) selected_cut_29890

theorem selected_cut_29891 : selected 9 ⟨445248, by decide⟩
    (prefixPartial 12 93866) = some ⟨12, 1, 0, 445248, 93866, 1, 65536⟩ := by
  decide +kernel

theorem context_12_93866_445248 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93866 ⟨445248, by decide⟩ :=
  accepted_of_selected 12 93866 ⟨445248, by decide⟩ ⟨12, 1, 0, 445248, 93866, 1, 65536⟩
    (by decide) selected_cut_29891

theorem selected_cut_29892 : selected 9 ⟨754451, by decide⟩
    (prefixPartial 12 93867) = some ⟨12, 2, 0, 754451, 93867, 1457, 65536⟩ := by
  decide +kernel

theorem context_12_93867_754451 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93867 ⟨754451, by decide⟩ :=
  accepted_of_selected 12 93867 ⟨754451, by decide⟩ ⟨12, 2, 0, 754451, 93867, 1457, 65536⟩
    (by decide) selected_cut_29892

theorem unmarked_context_11_23466_754452 : frontier 10 ⟨754452, by decide⟩
    (prefixCache 11 23466) (prefixPartial 11 23466) = false := by
  decide +kernel

theorem node_context_11_23466_754452 : EJMOriginalGlobalDAGData.nodes 10 ⟨754452, by decide⟩ =
    .split (coordinate 11) (![⟨754412, by decide⟩,⟨754429, by decide⟩,⟨445248, by decide⟩,⟨754451, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23466_754452 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23466 ⟨754452, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23466
    ⟨754452, by decide⟩ (by decide) (![⟨754412, by decide⟩,⟨754429, by decide⟩,⟨445248, by decide⟩,⟨754451, by decide⟩]) unmarked_context_11_23466_754452 node_context_11_23466_754452
  intro a
  fin_cases a
  · exact context_12_93864_754412
  · exact context_12_93865_754429
  · exact context_12_93866_445248
  · exact context_12_93867_754451

theorem selected_cut_29893 : selected 9 ⟨754468, by decide⟩
    (prefixPartial 12 93868) = some ⟨12, 2, 0, 754468, 93868, 1441, 65536⟩ := by
  decide +kernel

theorem context_12_93868_754468 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93868 ⟨754468, by decide⟩ :=
  accepted_of_selected 12 93868 ⟨754468, by decide⟩ ⟨12, 2, 0, 754468, 93868, 1441, 65536⟩
    (by decide) selected_cut_29893

theorem selected_cut_29894 : selected 9 ⟨754483, by decide⟩
    (prefixPartial 12 93869) = some ⟨12, 2, 0, 754483, 93869, 1313, 65536⟩ := by
  decide +kernel

theorem context_12_93869_754483 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93869 ⟨754483, by decide⟩ :=
  accepted_of_selected 12 93869 ⟨754483, by decide⟩ ⟨12, 2, 0, 754483, 93869, 1313, 65536⟩
    (by decide) selected_cut_29894

theorem selected_cut_29895 : selected 9 ⟨754500, by decide⟩
    (prefixPartial 12 93870) = some ⟨12, 2, 0, 754500, 93870, 1209, 65536⟩ := by
  decide +kernel

theorem context_12_93870_754500 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93870 ⟨754500, by decide⟩ :=
  accepted_of_selected 12 93870 ⟨754500, by decide⟩ ⟨12, 2, 0, 754500, 93870, 1209, 65536⟩
    (by decide) selected_cut_29895

theorem selected_cut_29896 : selected 9 ⟨754514, by decide⟩
    (prefixPartial 12 93871) = some ⟨12, 2, 0, 754514, 93871, 1517, 65536⟩ := by
  decide +kernel

theorem context_12_93871_754514 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93871 ⟨754514, by decide⟩ :=
  accepted_of_selected 12 93871 ⟨754514, by decide⟩ ⟨12, 2, 0, 754514, 93871, 1517, 65536⟩
    (by decide) selected_cut_29896

theorem unmarked_context_11_23467_754515 : frontier 10 ⟨754515, by decide⟩
    (prefixCache 11 23467) (prefixPartial 11 23467) = false := by
  decide +kernel

theorem node_context_11_23467_754515 : EJMOriginalGlobalDAGData.nodes 10 ⟨754515, by decide⟩ =
    .split (coordinate 11) (![⟨754468, by decide⟩,⟨754483, by decide⟩,⟨754500, by decide⟩,⟨754514, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23467_754515 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23467 ⟨754515, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23467
    ⟨754515, by decide⟩ (by decide) (![⟨754468, by decide⟩,⟨754483, by decide⟩,⟨754500, by decide⟩,⟨754514, by decide⟩]) unmarked_context_11_23467_754515 node_context_11_23467_754515
  intro a
  fin_cases a
  · exact context_12_93868_754468
  · exact context_12_93869_754483
  · exact context_12_93870_754500
  · exact context_12_93871_754514

theorem unmarked_context_10_5866_754516 : frontier 11 ⟨754516, by decide⟩
    (prefixCache 10 5866) (prefixPartial 10 5866) = false := by
  decide +kernel

theorem node_context_10_5866_754516 : EJMOriginalGlobalDAGData.nodes 11 ⟨754516, by decide⟩ =
    .split (coordinate 10) (![⟨754315, by decide⟩,⟨754393, by decide⟩,⟨754452, by decide⟩,⟨754515, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5866_754516 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5866 ⟨754516, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5866
    ⟨754516, by decide⟩ (by decide) (![⟨754315, by decide⟩,⟨754393, by decide⟩,⟨754452, by decide⟩,⟨754515, by decide⟩]) unmarked_context_10_5866_754516 node_context_10_5866_754516
  intro a
  fin_cases a
  · exact context_11_23464_754315
  · exact context_11_23465_754393
  · exact context_11_23466_754452
  · exact context_11_23467_754515

theorem selected_cut_29897 : selected 9 ⟨754530, by decide⟩
    (prefixPartial 12 93872) = some ⟨12, 2, 0, 754530, 93872, 1217, 65536⟩ := by
  decide +kernel

theorem context_12_93872_754530 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93872 ⟨754530, by decide⟩ :=
  accepted_of_selected 12 93872 ⟨754530, by decide⟩ ⟨12, 2, 0, 754530, 93872, 1217, 65536⟩
    (by decide) selected_cut_29897

theorem selected_cut_29898 : selected 9 ⟨754542, by decide⟩
    (prefixPartial 12 93873) = some ⟨12, 2, 0, 754542, 93873, 1357, 65536⟩ := by
  decide +kernel

theorem context_12_93873_754542 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93873 ⟨754542, by decide⟩ :=
  accepted_of_selected 12 93873 ⟨754542, by decide⟩ ⟨12, 2, 0, 754542, 93873, 1357, 65536⟩
    (by decide) selected_cut_29898

theorem selected_cut_29899 : selected 9 ⟨754558, by decide⟩
    (prefixPartial 12 93874) = some ⟨12, 2, 0, 754558, 93874, 1165, 65536⟩ := by
  decide +kernel

theorem context_12_93874_754558 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93874 ⟨754558, by decide⟩ :=
  accepted_of_selected 12 93874 ⟨754558, by decide⟩ ⟨12, 2, 0, 754558, 93874, 1165, 65536⟩
    (by decide) selected_cut_29899

theorem selected_cut_29900 : selected 9 ⟨754577, by decide⟩
    (prefixPartial 12 93875) = some ⟨12, 2, 0, 754577, 93875, 1397, 65536⟩ := by
  decide +kernel

theorem context_12_93875_754577 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93875 ⟨754577, by decide⟩ :=
  accepted_of_selected 12 93875 ⟨754577, by decide⟩ ⟨12, 2, 0, 754577, 93875, 1397, 65536⟩
    (by decide) selected_cut_29900

theorem unmarked_context_11_23468_754578 : frontier 10 ⟨754578, by decide⟩
    (prefixCache 11 23468) (prefixPartial 11 23468) = false := by
  decide +kernel

theorem node_context_11_23468_754578 : EJMOriginalGlobalDAGData.nodes 10 ⟨754578, by decide⟩ =
    .split (coordinate 11) (![⟨754530, by decide⟩,⟨754542, by decide⟩,⟨754558, by decide⟩,⟨754577, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23468_754578 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23468 ⟨754578, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23468
    ⟨754578, by decide⟩ (by decide) (![⟨754530, by decide⟩,⟨754542, by decide⟩,⟨754558, by decide⟩,⟨754577, by decide⟩]) unmarked_context_11_23468_754578 node_context_11_23468_754578
  intro a
  fin_cases a
  · exact context_12_93872_754530
  · exact context_12_93873_754542
  · exact context_12_93874_754558
  · exact context_12_93875_754577

theorem selected_cut_29901 : selected 9 ⟨754588, by decide⟩
    (prefixPartial 12 93876) = some ⟨12, 2, 0, 754588, 93876, 1109, 65536⟩ := by
  decide +kernel

theorem context_12_93876_754588 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93876 ⟨754588, by decide⟩ :=
  accepted_of_selected 12 93876 ⟨754588, by decide⟩ ⟨12, 2, 0, 754588, 93876, 1109, 65536⟩
    (by decide) selected_cut_29901

theorem selected_cut_29902 : selected 9 ⟨754601, by decide⟩
    (prefixPartial 12 93877) = some ⟨12, 2, 0, 754601, 93877, 1161, 65536⟩ := by
  decide +kernel

theorem context_12_93877_754601 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93877 ⟨754601, by decide⟩ :=
  accepted_of_selected 12 93877 ⟨754601, by decide⟩ ⟨12, 2, 0, 754601, 93877, 1161, 65536⟩
    (by decide) selected_cut_29902

theorem selected_cut_29903 : selected 9 ⟨754614, by decide⟩
    (prefixPartial 12 93878) = some ⟨12, 2, 0, 754614, 93878, 1013, 65536⟩ := by
  decide +kernel

theorem context_12_93878_754614 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93878 ⟨754614, by decide⟩ :=
  accepted_of_selected 12 93878 ⟨754614, by decide⟩ ⟨12, 2, 0, 754614, 93878, 1013, 65536⟩
    (by decide) selected_cut_29903

theorem selected_cut_29904 : selected 9 ⟨754635, by decide⟩
    (prefixPartial 12 93879) = some ⟨12, 2, 0, 754635, 93879, 1257, 65536⟩ := by
  decide +kernel

theorem context_12_93879_754635 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93879 ⟨754635, by decide⟩ :=
  accepted_of_selected 12 93879 ⟨754635, by decide⟩ ⟨12, 2, 0, 754635, 93879, 1257, 65536⟩
    (by decide) selected_cut_29904

theorem unmarked_context_11_23469_754636 : frontier 10 ⟨754636, by decide⟩
    (prefixCache 11 23469) (prefixPartial 11 23469) = false := by
  decide +kernel

theorem node_context_11_23469_754636 : EJMOriginalGlobalDAGData.nodes 10 ⟨754636, by decide⟩ =
    .split (coordinate 11) (![⟨754588, by decide⟩,⟨754601, by decide⟩,⟨754614, by decide⟩,⟨754635, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23469_754636 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23469 ⟨754636, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23469
    ⟨754636, by decide⟩ (by decide) (![⟨754588, by decide⟩,⟨754601, by decide⟩,⟨754614, by decide⟩,⟨754635, by decide⟩]) unmarked_context_11_23469_754636 node_context_11_23469_754636
  intro a
  fin_cases a
  · exact context_12_93876_754588
  · exact context_12_93877_754601
  · exact context_12_93878_754614
  · exact context_12_93879_754635

theorem selected_cut_29905 : selected 10 ⟨754675, by decide⟩
    (prefixPartial 11 23470) = some ⟨11, 2, 0, 754675, 23470, 3337, 262144⟩ := by
  decide +kernel

theorem context_11_23470_754675 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23470 ⟨754675, by decide⟩ :=
  accepted_of_selected 11 23470 ⟨754675, by decide⟩ ⟨11, 2, 0, 754675, 23470, 3337, 262144⟩
    (by decide) selected_cut_29905

theorem selected_cut_29906 : selected 10 ⟨754701, by decide⟩
    (prefixPartial 11 23471) = some ⟨11, 2, 0, 754701, 23471, 2413, 262144⟩ := by
  decide +kernel

theorem context_11_23471_754701 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23471 ⟨754701, by decide⟩ :=
  accepted_of_selected 11 23471 ⟨754701, by decide⟩ ⟨11, 2, 0, 754701, 23471, 2413, 262144⟩
    (by decide) selected_cut_29906

theorem unmarked_context_10_5867_754702 : frontier 11 ⟨754702, by decide⟩
    (prefixCache 10 5867) (prefixPartial 10 5867) = false := by
  decide +kernel

theorem node_context_10_5867_754702 : EJMOriginalGlobalDAGData.nodes 11 ⟨754702, by decide⟩ =
    .split (coordinate 10) (![⟨754578, by decide⟩,⟨754636, by decide⟩,⟨754675, by decide⟩,⟨754701, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5867_754702 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5867 ⟨754702, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5867
    ⟨754702, by decide⟩ (by decide) (![⟨754578, by decide⟩,⟨754636, by decide⟩,⟨754675, by decide⟩,⟨754701, by decide⟩]) unmarked_context_10_5867_754702 node_context_10_5867_754702
  intro a
  fin_cases a
  · exact context_11_23468_754578
  · exact context_11_23469_754636
  · exact context_11_23470_754675
  · exact context_11_23471_754701

theorem unmarked_context_9_1466_754703 : frontier 12 ⟨754703, by decide⟩
    (prefixCache 9 1466) (prefixPartial 9 1466) = false := by
  decide +kernel

theorem node_context_9_1466_754703 : EJMOriginalGlobalDAGData.nodes 12 ⟨754703, by decide⟩ =
    .split (coordinate 9) (![⟨753827, by decide⟩,⟨754236, by decide⟩,⟨754516, by decide⟩,⟨754702, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1466_754703 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1466 ⟨754703, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1466
    ⟨754703, by decide⟩ (by decide) (![⟨753827, by decide⟩,⟨754236, by decide⟩,⟨754516, by decide⟩,⟨754702, by decide⟩]) unmarked_context_9_1466_754703 node_context_9_1466_754703
  intro a
  fin_cases a
  · exact context_10_5864_753827
  · exact context_10_5865_754236
  · exact context_10_5866_754516
  · exact context_10_5867_754702

theorem selected_cut_29907 : selected 10 ⟨754742, by decide⟩
    (prefixPartial 11 23472) = some ⟨11, 2, 0, 754742, 23472, 3925, 262144⟩ := by
  decide +kernel

theorem context_11_23472_754742 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23472 ⟨754742, by decide⟩ :=
  accepted_of_selected 11 23472 ⟨754742, by decide⟩ ⟨11, 2, 0, 754742, 23472, 3925, 262144⟩
    (by decide) selected_cut_29907

theorem selected_cut_29908 : selected 10 ⟨754775, by decide⟩
    (prefixPartial 11 23473) = some ⟨11, 2, 0, 754775, 23473, 3273, 262144⟩ := by
  decide +kernel

theorem context_11_23473_754775 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23473 ⟨754775, by decide⟩ :=
  accepted_of_selected 11 23473 ⟨754775, by decide⟩ ⟨11, 2, 0, 754775, 23473, 3273, 262144⟩
    (by decide) selected_cut_29908

theorem selected_cut_29909 : selected 10 ⟨754814, by decide⟩
    (prefixPartial 11 23474) = some ⟨11, 2, 0, 754814, 23474, 3529, 262144⟩ := by
  decide +kernel

theorem context_11_23474_754814 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23474 ⟨754814, by decide⟩ :=
  accepted_of_selected 11 23474 ⟨754814, by decide⟩ ⟨11, 2, 0, 754814, 23474, 3529, 262144⟩
    (by decide) selected_cut_29909

theorem selected_cut_29910 : selected 10 ⟨754852, by decide⟩
    (prefixPartial 11 23475) = some ⟨11, 2, 0, 754852, 23475, 3189, 262144⟩ := by
  decide +kernel

theorem context_11_23475_754852 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23475 ⟨754852, by decide⟩ :=
  accepted_of_selected 11 23475 ⟨754852, by decide⟩ ⟨11, 2, 0, 754852, 23475, 3189, 262144⟩
    (by decide) selected_cut_29910

theorem unmarked_context_10_5868_754853 : frontier 11 ⟨754853, by decide⟩
    (prefixCache 10 5868) (prefixPartial 10 5868) = false := by
  decide +kernel

theorem node_context_10_5868_754853 : EJMOriginalGlobalDAGData.nodes 11 ⟨754853, by decide⟩ =
    .split (coordinate 10) (![⟨754742, by decide⟩,⟨754775, by decide⟩,⟨754814, by decide⟩,⟨754852, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5868_754853 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5868 ⟨754853, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5868
    ⟨754853, by decide⟩ (by decide) (![⟨754742, by decide⟩,⟨754775, by decide⟩,⟨754814, by decide⟩,⟨754852, by decide⟩]) unmarked_context_10_5868_754853 node_context_10_5868_754853
  intro a
  fin_cases a
  · exact context_11_23472_754742
  · exact context_11_23473_754775
  · exact context_11_23474_754814
  · exact context_11_23475_754852

theorem selected_cut_29911 : selected 10 ⟨754872, by decide⟩
    (prefixPartial 11 23476) = some ⟨11, 2, 0, 754872, 23476, 2837, 262144⟩ := by
  decide +kernel

theorem context_11_23476_754872 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23476 ⟨754872, by decide⟩ :=
  accepted_of_selected 11 23476 ⟨754872, by decide⟩ ⟨11, 2, 0, 754872, 23476, 2837, 262144⟩
    (by decide) selected_cut_29911

theorem selected_cut_29912 : selected 10 ⟨754897, by decide⟩
    (prefixPartial 11 23477) = some ⟨11, 2, 0, 754897, 23477, 2321, 262144⟩ := by
  decide +kernel

theorem context_11_23477_754897 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23477 ⟨754897, by decide⟩ :=
  accepted_of_selected 11 23477 ⟨754897, by decide⟩ ⟨11, 2, 0, 754897, 23477, 2321, 262144⟩
    (by decide) selected_cut_29912

theorem selected_cut_29913 : selected 10 ⟨754919, by decide⟩
    (prefixPartial 11 23478) = some ⟨11, 2, 0, 754919, 23478, 2137, 262144⟩ := by
  decide +kernel

theorem context_11_23478_754919 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23478 ⟨754919, by decide⟩ :=
  accepted_of_selected 11 23478 ⟨754919, by decide⟩ ⟨11, 2, 0, 754919, 23478, 2137, 262144⟩
    (by decide) selected_cut_29913

theorem selected_cut_29914 : selected 10 ⟨754938, by decide⟩
    (prefixPartial 11 23479) = some ⟨11, 2, 0, 754938, 23479, 1801, 262144⟩ := by
  decide +kernel

theorem context_11_23479_754938 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23479 ⟨754938, by decide⟩ :=
  accepted_of_selected 11 23479 ⟨754938, by decide⟩ ⟨11, 2, 0, 754938, 23479, 1801, 262144⟩
    (by decide) selected_cut_29914

theorem unmarked_context_10_5869_754939 : frontier 11 ⟨754939, by decide⟩
    (prefixCache 10 5869) (prefixPartial 10 5869) = false := by
  decide +kernel

theorem node_context_10_5869_754939 : EJMOriginalGlobalDAGData.nodes 11 ⟨754939, by decide⟩ =
    .split (coordinate 10) (![⟨754872, by decide⟩,⟨754897, by decide⟩,⟨754919, by decide⟩,⟨754938, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5869_754939 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5869 ⟨754939, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5869
    ⟨754939, by decide⟩ (by decide) (![⟨754872, by decide⟩,⟨754897, by decide⟩,⟨754919, by decide⟩,⟨754938, by decide⟩]) unmarked_context_10_5869_754939 node_context_10_5869_754939
  intro a
  fin_cases a
  · exact context_11_23476_754872
  · exact context_11_23477_754897
  · exact context_11_23478_754919
  · exact context_11_23479_754938

theorem selected_cut_29915 : selected 11 ⟨754994, by decide⟩
    (prefixPartial 10 5870) = some ⟨10, 2, 0, 754994, 5870, 3997, 1048576⟩ := by
  decide +kernel

theorem context_10_5870_754994 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5870 ⟨754994, by decide⟩ :=
  accepted_of_selected 10 5870 ⟨754994, by decide⟩ ⟨10, 2, 0, 754994, 5870, 3997, 1048576⟩
    (by decide) selected_cut_29915

theorem selected_cut_29916 : selected 11 ⟨755030, by decide⟩
    (prefixPartial 10 5871) = some ⟨10, 2, 0, 755030, 5871, 1025, 1048576⟩ := by
  decide +kernel

theorem context_10_5871_755030 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5871 ⟨755030, by decide⟩ :=
  accepted_of_selected 10 5871 ⟨755030, by decide⟩ ⟨10, 2, 0, 755030, 5871, 1025, 1048576⟩
    (by decide) selected_cut_29916

theorem unmarked_context_9_1467_755031 : frontier 12 ⟨755031, by decide⟩
    (prefixCache 9 1467) (prefixPartial 9 1467) = false := by
  decide +kernel

theorem node_context_9_1467_755031 : EJMOriginalGlobalDAGData.nodes 12 ⟨755031, by decide⟩ =
    .split (coordinate 9) (![⟨754853, by decide⟩,⟨754939, by decide⟩,⟨754994, by decide⟩,⟨755030, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1467_755031 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1467 ⟨755031, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1467
    ⟨755031, by decide⟩ (by decide) (![⟨754853, by decide⟩,⟨754939, by decide⟩,⟨754994, by decide⟩,⟨755030, by decide⟩]) unmarked_context_9_1467_755031 node_context_9_1467_755031
  intro a
  fin_cases a
  · exact context_10_5868_754853
  · exact context_10_5869_754939
  · exact context_10_5870_754994
  · exact context_10_5871_755030

theorem unmarked_context_8_366_755032 : frontier 13 ⟨755032, by decide⟩
    (prefixCache 8 366) (prefixPartial 8 366) = false := by
  decide +kernel

theorem node_context_8_366_755032 : EJMOriginalGlobalDAGData.nodes 13 ⟨755032, by decide⟩ =
    .split (coordinate 8) (![⟨750984, by decide⟩,⟨753417, by decide⟩,⟨754703, by decide⟩,⟨755031, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_366_755032 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 366 ⟨755032, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 366
    ⟨755032, by decide⟩ (by decide) (![⟨750984, by decide⟩,⟨753417, by decide⟩,⟨754703, by decide⟩,⟨755031, by decide⟩]) unmarked_context_8_366_755032 node_context_8_366_755032
  intro a
  fin_cases a
  · exact context_9_1464_750984
  · exact context_9_1465_753417
  · exact context_9_1466_754703
  · exact context_9_1467_755031

theorem selected_cut_29917 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 23488) = some ⟨11, 1, 0, 434745, 23488, 1, 262144⟩ := by
  decide +kernel

theorem context_11_23488_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23488 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 23488 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 23488, 1, 262144⟩
    (by decide) selected_cut_29917

theorem selected_cut_29918 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 93956) = some ⟨12, 1, 0, 448748, 93956, 1, 65536⟩ := by
  decide +kernel

theorem context_12_93956_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93956 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 93956 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 93956, 1, 65536⟩
    (by decide) selected_cut_29918

theorem selected_cut_29919 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 93957) = some ⟨12, 1, 0, 34034, 93957, 1, 65536⟩ := by
  decide +kernel

theorem context_12_93957_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93957 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 93957 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 93957, 1, 65536⟩
    (by decide) selected_cut_29919

theorem selected_cut_29920 : selected 7 ⟨755084, by decide⟩
    (prefixPartial 14 1503328) = some ⟨14, 2, 0, 755084, 1503328, 693, 4096⟩ := by
  decide +kernel

theorem context_14_1503328_755084 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1503328 ⟨755084, by decide⟩ :=
  accepted_of_selected 14 1503328 ⟨755084, by decide⟩ ⟨14, 2, 0, 755084, 1503328, 693, 4096⟩
    (by decide) selected_cut_29920

theorem selected_cut_29921 : selected 7 ⟨755138, by decide⟩
    (prefixPartial 14 1503329) = some ⟨14, 2, 0, 755138, 1503329, 1545, 4096⟩ := by
  decide +kernel

theorem context_14_1503329_755138 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1503329 ⟨755138, by decide⟩ :=
  accepted_of_selected 14 1503329 ⟨755138, by decide⟩ ⟨14, 2, 0, 755138, 1503329, 1545, 4096⟩
    (by decide) selected_cut_29921

theorem selected_cut_29922 : selected 7 ⟨755166, by decide⟩
    (prefixPartial 14 1503330) = some ⟨14, 2, 0, 755166, 1503330, 1277, 4096⟩ := by
  decide +kernel

theorem context_14_1503330_755166 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1503330 ⟨755166, by decide⟩ :=
  accepted_of_selected 14 1503330 ⟨755166, by decide⟩ ⟨14, 2, 0, 755166, 1503330, 1277, 4096⟩
    (by decide) selected_cut_29922

theorem selected_cut_29923 : selected 7 ⟨755186, by decide⟩
    (prefixPartial 14 1503331) = some ⟨14, 2, 0, 755186, 1503331, 909, 4096⟩ := by
  decide +kernel

theorem context_14_1503331_755186 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1503331 ⟨755186, by decide⟩ :=
  accepted_of_selected 14 1503331 ⟨755186, by decide⟩ ⟨14, 2, 0, 755186, 1503331, 909, 4096⟩
    (by decide) selected_cut_29923

theorem unmarked_context_13_375832_755187 : frontier 8 ⟨755187, by decide⟩
    (prefixCache 13 375832) (prefixPartial 13 375832) = false := by
  decide +kernel

theorem node_context_13_375832_755187 : EJMOriginalGlobalDAGData.nodes 8 ⟨755187, by decide⟩ =
    .split (coordinate 13) (![⟨755084, by decide⟩,⟨755138, by decide⟩,⟨755166, by decide⟩,⟨755186, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_375832_755187 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375832 ⟨755187, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 375832
    ⟨755187, by decide⟩ (by decide) (![⟨755084, by decide⟩,⟨755138, by decide⟩,⟨755166, by decide⟩,⟨755186, by decide⟩]) unmarked_context_13_375832_755187 node_context_13_375832_755187
  intro a
  fin_cases a
  · exact context_14_1503328_755084
  · exact context_14_1503329_755138
  · exact context_14_1503330_755166
  · exact context_14_1503331_755186

theorem selected_cut_29924 : selected 8 ⟨755315, by decide⟩
    (prefixPartial 13 375833) = some ⟨13, 2, 0, 755315, 375833, 3053, 16384⟩ := by
  decide +kernel

theorem context_13_375833_755315 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375833 ⟨755315, by decide⟩ :=
  accepted_of_selected 13 375833 ⟨755315, by decide⟩ ⟨13, 2, 0, 755315, 375833, 3053, 16384⟩
    (by decide) selected_cut_29924

theorem selected_cut_29925 : selected 8 ⟨755384, by decide⟩
    (prefixPartial 13 375834) = some ⟨13, 2, 0, 755384, 375834, 2337, 16384⟩ := by
  decide +kernel

theorem context_13_375834_755384 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375834 ⟨755384, by decide⟩ :=
  accepted_of_selected 13 375834 ⟨755384, by decide⟩ ⟨13, 2, 0, 755384, 375834, 2337, 16384⟩
    (by decide) selected_cut_29925

theorem selected_cut_29926 : selected 8 ⟨755392, by decide⟩
    (prefixPartial 13 375835) = some ⟨13, 2, 0, 755392, 375835, 789, 16384⟩ := by
  decide +kernel

theorem context_13_375835_755392 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375835 ⟨755392, by decide⟩ :=
  accepted_of_selected 13 375835 ⟨755392, by decide⟩ ⟨13, 2, 0, 755392, 375835, 789, 16384⟩
    (by decide) selected_cut_29926

theorem unmarked_context_12_93958_755393 : frontier 9 ⟨755393, by decide⟩
    (prefixCache 12 93958) (prefixPartial 12 93958) = false := by
  decide +kernel

theorem node_context_12_93958_755393 : EJMOriginalGlobalDAGData.nodes 9 ⟨755393, by decide⟩ =
    .split (coordinate 12) (![⟨755187, by decide⟩,⟨755315, by decide⟩,⟨755384, by decide⟩,⟨755392, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93958_755393 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93958 ⟨755393, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93958
    ⟨755393, by decide⟩ (by decide) (![⟨755187, by decide⟩,⟨755315, by decide⟩,⟨755384, by decide⟩,⟨755392, by decide⟩]) unmarked_context_12_93958_755393 node_context_12_93958_755393
  intro a
  fin_cases a
  · exact context_13_375832_755187
  · exact context_13_375833_755315
  · exact context_13_375834_755384
  · exact context_13_375835_755392

theorem selected_cut_29927 : selected 8 ⟨755467, by decide⟩
    (prefixPartial 13 375836) = some ⟨13, 2, 0, 755467, 375836, 3829, 16384⟩ := by
  decide +kernel

theorem context_13_375836_755467 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375836 ⟨755467, by decide⟩ :=
  accepted_of_selected 13 375836 ⟨755467, by decide⟩ ⟨13, 2, 0, 755467, 375836, 3829, 16384⟩
    (by decide) selected_cut_29927

theorem selected_cut_29928 : selected 8 ⟨755536, by decide⟩
    (prefixPartial 13 375837) = some ⟨13, 2, 0, 755536, 375837, 2841, 16384⟩ := by
  decide +kernel

theorem context_13_375837_755536 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375837 ⟨755536, by decide⟩ :=
  accepted_of_selected 13 375837 ⟨755536, by decide⟩ ⟨13, 2, 0, 755536, 375837, 2841, 16384⟩
    (by decide) selected_cut_29928

theorem selected_cut_29929 : selected 8 ⟨755597, by decide⟩
    (prefixPartial 13 375838) = some ⟨13, 2, 0, 755597, 375838, 2417, 16384⟩ := by
  decide +kernel

theorem context_13_375838_755597 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375838 ⟨755597, by decide⟩ :=
  accepted_of_selected 13 375838 ⟨755597, by decide⟩ ⟨13, 2, 0, 755597, 375838, 2417, 16384⟩
    (by decide) selected_cut_29929

theorem selected_cut_29930 : selected 8 ⟨755608, by decide⟩
    (prefixPartial 13 375839) = some ⟨13, 2, 0, 755608, 375839, 813, 16384⟩ := by
  decide +kernel

theorem context_13_375839_755608 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375839 ⟨755608, by decide⟩ :=
  accepted_of_selected 13 375839 ⟨755608, by decide⟩ ⟨13, 2, 0, 755608, 375839, 813, 16384⟩
    (by decide) selected_cut_29930

theorem unmarked_context_12_93959_755609 : frontier 9 ⟨755609, by decide⟩
    (prefixCache 12 93959) (prefixPartial 12 93959) = false := by
  decide +kernel

theorem node_context_12_93959_755609 : EJMOriginalGlobalDAGData.nodes 9 ⟨755609, by decide⟩ =
    .split (coordinate 12) (![⟨755467, by decide⟩,⟨755536, by decide⟩,⟨755597, by decide⟩,⟨755608, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93959_755609 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93959 ⟨755609, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93959
    ⟨755609, by decide⟩ (by decide) (![⟨755467, by decide⟩,⟨755536, by decide⟩,⟨755597, by decide⟩,⟨755608, by decide⟩]) unmarked_context_12_93959_755609 node_context_12_93959_755609
  intro a
  fin_cases a
  · exact context_13_375836_755467
  · exact context_13_375837_755536
  · exact context_13_375838_755597
  · exact context_13_375839_755608

theorem unmarked_context_11_23489_755610 : frontier 10 ⟨755610, by decide⟩
    (prefixCache 11 23489) (prefixPartial 11 23489) = false := by
  decide +kernel

theorem node_context_11_23489_755610 : EJMOriginalGlobalDAGData.nodes 10 ⟨755610, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨34034, by decide⟩,⟨755393, by decide⟩,⟨755609, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23489_755610 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23489 ⟨755610, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23489
    ⟨755610, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨34034, by decide⟩,⟨755393, by decide⟩,⟨755609, by decide⟩]) unmarked_context_11_23489_755610 node_context_11_23489_755610
  intro a
  fin_cases a
  · exact context_12_93956_448748
  · exact context_12_93957_34034
  · exact context_12_93958_755393
  · exact context_12_93959_755609

theorem selected_cut_29931 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 93960) = some ⟨12, 1, 0, 448748, 93960, 1, 65536⟩ := by
  decide +kernel

theorem context_12_93960_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93960 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 93960 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 93960, 1, 65536⟩
    (by decide) selected_cut_29931

theorem selected_cut_29932 : selected 8 ⟨755696, by decide⟩
    (prefixPartial 13 375844) = some ⟨13, 2, 0, 755696, 375844, 3757, 16384⟩ := by
  decide +kernel

theorem context_13_375844_755696 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375844 ⟨755696, by decide⟩ :=
  accepted_of_selected 13 375844 ⟨755696, by decide⟩ ⟨13, 2, 0, 755696, 375844, 3757, 16384⟩
    (by decide) selected_cut_29932

theorem selected_cut_29933 : selected 8 ⟨755771, by decide⟩
    (prefixPartial 13 375845) = some ⟨13, 2, 0, 755771, 375845, 2849, 16384⟩ := by
  decide +kernel

theorem context_13_375845_755771 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375845 ⟨755771, by decide⟩ :=
  accepted_of_selected 13 375845 ⟨755771, by decide⟩ ⟨13, 2, 0, 755771, 375845, 2849, 16384⟩
    (by decide) selected_cut_29933

theorem selected_cut_29934 : selected 8 ⟨755863, by decide⟩
    (prefixPartial 13 375846) = some ⟨13, 2, 0, 755863, 375846, 2677, 16384⟩ := by
  decide +kernel

theorem context_13_375846_755863 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375846 ⟨755863, by decide⟩ :=
  accepted_of_selected 13 375846 ⟨755863, by decide⟩ ⟨13, 2, 0, 755863, 375846, 2677, 16384⟩
    (by decide) selected_cut_29934

theorem selected_cut_29935 : selected 8 ⟨755882, by decide⟩
    (prefixPartial 13 375847) = some ⟨13, 2, 0, 755882, 375847, 969, 16384⟩ := by
  decide +kernel

theorem context_13_375847_755882 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375847 ⟨755882, by decide⟩ :=
  accepted_of_selected 13 375847 ⟨755882, by decide⟩ ⟨13, 2, 0, 755882, 375847, 969, 16384⟩
    (by decide) selected_cut_29935

theorem unmarked_context_12_93961_755883 : frontier 9 ⟨755883, by decide⟩
    (prefixCache 12 93961) (prefixPartial 12 93961) = false := by
  decide +kernel

theorem node_context_12_93961_755883 : EJMOriginalGlobalDAGData.nodes 9 ⟨755883, by decide⟩ =
    .split (coordinate 12) (![⟨755696, by decide⟩,⟨755771, by decide⟩,⟨755863, by decide⟩,⟨755882, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93961_755883 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93961 ⟨755883, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93961
    ⟨755883, by decide⟩ (by decide) (![⟨755696, by decide⟩,⟨755771, by decide⟩,⟨755863, by decide⟩,⟨755882, by decide⟩]) unmarked_context_12_93961_755883 node_context_12_93961_755883
  intro a
  fin_cases a
  · exact context_13_375844_755696
  · exact context_13_375845_755771
  · exact context_13_375846_755863
  · exact context_13_375847_755882

theorem selected_cut_29936 : selected 8 ⟨755959, by decide⟩
    (prefixPartial 13 375848) = some ⟨13, 2, 0, 755959, 375848, 3689, 16384⟩ := by
  decide +kernel

theorem context_13_375848_755959 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375848 ⟨755959, by decide⟩ :=
  accepted_of_selected 13 375848 ⟨755959, by decide⟩ ⟨13, 2, 0, 755959, 375848, 3689, 16384⟩
    (by decide) selected_cut_29936

theorem selected_cut_29937 : selected 8 ⟨756041, by decide⟩
    (prefixPartial 13 375849) = some ⟨13, 2, 0, 756041, 375849, 3217, 16384⟩ := by
  decide +kernel

theorem context_13_375849_756041 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375849 ⟨756041, by decide⟩ :=
  accepted_of_selected 13 375849 ⟨756041, by decide⟩ ⟨13, 2, 0, 756041, 375849, 3217, 16384⟩
    (by decide) selected_cut_29937

theorem selected_cut_29938 : selected 8 ⟨756076, by decide⟩
    (prefixPartial 13 375850) = some ⟨13, 2, 0, 756076, 375850, 2425, 16384⟩ := by
  decide +kernel

theorem context_13_375850_756076 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375850 ⟨756076, by decide⟩ :=
  accepted_of_selected 13 375850 ⟨756076, by decide⟩ ⟨13, 2, 0, 756076, 375850, 2425, 16384⟩
    (by decide) selected_cut_29938

theorem selected_cut_29939 : selected 8 ⟨756085, by decide⟩
    (prefixPartial 13 375851) = some ⟨13, 2, 0, 756085, 375851, 909, 16384⟩ := by
  decide +kernel

theorem context_13_375851_756085 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375851 ⟨756085, by decide⟩ :=
  accepted_of_selected 13 375851 ⟨756085, by decide⟩ ⟨13, 2, 0, 756085, 375851, 909, 16384⟩
    (by decide) selected_cut_29939

theorem unmarked_context_12_93962_756086 : frontier 9 ⟨756086, by decide⟩
    (prefixCache 12 93962) (prefixPartial 12 93962) = false := by
  decide +kernel

theorem node_context_12_93962_756086 : EJMOriginalGlobalDAGData.nodes 9 ⟨756086, by decide⟩ =
    .split (coordinate 12) (![⟨755959, by decide⟩,⟨756041, by decide⟩,⟨756076, by decide⟩,⟨756085, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93962_756086 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93962 ⟨756086, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93962
    ⟨756086, by decide⟩ (by decide) (![⟨755959, by decide⟩,⟨756041, by decide⟩,⟨756076, by decide⟩,⟨756085, by decide⟩]) unmarked_context_12_93962_756086 node_context_12_93962_756086
  intro a
  fin_cases a
  · exact context_13_375848_755959
  · exact context_13_375849_756041
  · exact context_13_375850_756076
  · exact context_13_375851_756085

theorem selected_cut_29940 : selected 8 ⟨756158, by decide⟩
    (prefixPartial 13 375852) = some ⟨13, 2, 0, 756158, 375852, 3517, 16384⟩ := by
  decide +kernel

theorem context_13_375852_756158 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375852 ⟨756158, by decide⟩ :=
  accepted_of_selected 13 375852 ⟨756158, by decide⟩ ⟨13, 2, 0, 756158, 375852, 3517, 16384⟩
    (by decide) selected_cut_29940

theorem selected_cut_29941 : selected 8 ⟨756235, by decide⟩
    (prefixPartial 13 375853) = some ⟨13, 2, 0, 756235, 375853, 3189, 16384⟩ := by
  decide +kernel

theorem context_13_375853_756235 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375853 ⟨756235, by decide⟩ :=
  accepted_of_selected 13 375853 ⟨756235, by decide⟩ ⟨13, 2, 0, 756235, 375853, 3189, 16384⟩
    (by decide) selected_cut_29941

theorem selected_cut_29942 : selected 8 ⟨756283, by decide⟩
    (prefixPartial 13 375854) = some ⟨13, 2, 0, 756283, 375854, 2545, 16384⟩ := by
  decide +kernel

theorem context_13_375854_756283 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375854 ⟨756283, by decide⟩ :=
  accepted_of_selected 13 375854 ⟨756283, by decide⟩ ⟨13, 2, 0, 756283, 375854, 2545, 16384⟩
    (by decide) selected_cut_29942

theorem selected_cut_29943 : selected 8 ⟨756295, by decide⟩
    (prefixPartial 13 375855) = some ⟨13, 2, 0, 756295, 375855, 993, 16384⟩ := by
  decide +kernel

theorem context_13_375855_756295 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375855 ⟨756295, by decide⟩ :=
  accepted_of_selected 13 375855 ⟨756295, by decide⟩ ⟨13, 2, 0, 756295, 375855, 993, 16384⟩
    (by decide) selected_cut_29943

theorem unmarked_context_12_93963_756296 : frontier 9 ⟨756296, by decide⟩
    (prefixCache 12 93963) (prefixPartial 12 93963) = false := by
  decide +kernel

theorem node_context_12_93963_756296 : EJMOriginalGlobalDAGData.nodes 9 ⟨756296, by decide⟩ =
    .split (coordinate 12) (![⟨756158, by decide⟩,⟨756235, by decide⟩,⟨756283, by decide⟩,⟨756295, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93963_756296 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93963 ⟨756296, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93963
    ⟨756296, by decide⟩ (by decide) (![⟨756158, by decide⟩,⟨756235, by decide⟩,⟨756283, by decide⟩,⟨756295, by decide⟩]) unmarked_context_12_93963_756296 node_context_12_93963_756296
  intro a
  fin_cases a
  · exact context_13_375852_756158
  · exact context_13_375853_756235
  · exact context_13_375854_756283
  · exact context_13_375855_756295

theorem unmarked_context_11_23490_756297 : frontier 10 ⟨756297, by decide⟩
    (prefixCache 11 23490) (prefixPartial 11 23490) = false := by
  decide +kernel

theorem node_context_11_23490_756297 : EJMOriginalGlobalDAGData.nodes 10 ⟨756297, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨755883, by decide⟩,⟨756086, by decide⟩,⟨756296, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23490_756297 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23490 ⟨756297, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23490
    ⟨756297, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨755883, by decide⟩,⟨756086, by decide⟩,⟨756296, by decide⟩]) unmarked_context_11_23490_756297 node_context_11_23490_756297
  intro a
  fin_cases a
  · exact context_12_93960_448748
  · exact context_12_93961_755883
  · exact context_12_93962_756086
  · exact context_12_93963_756296

theorem selected_cut_29944 : selected 10 ⟨756298, by decide⟩
    (prefixPartial 11 23491) = some ⟨11, 2, 0, 756298, 23491, 5, 262144⟩ := by
  decide +kernel

theorem context_11_23491_756298 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23491 ⟨756298, by decide⟩ :=
  accepted_of_selected 11 23491 ⟨756298, by decide⟩ ⟨11, 2, 0, 756298, 23491, 5, 262144⟩
    (by decide) selected_cut_29944

theorem unmarked_context_10_5872_756299 : frontier 11 ⟨756299, by decide⟩
    (prefixCache 10 5872) (prefixPartial 10 5872) = false := by
  decide +kernel

theorem node_context_10_5872_756299 : EJMOriginalGlobalDAGData.nodes 11 ⟨756299, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨755610, by decide⟩,⟨756297, by decide⟩,⟨756298, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5872_756299 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5872 ⟨756299, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5872
    ⟨756299, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨755610, by decide⟩,⟨756297, by decide⟩,⟨756298, by decide⟩]) unmarked_context_10_5872_756299 node_context_10_5872_756299
  intro a
  fin_cases a
  · exact context_11_23488_434745
  · exact context_11_23489_755610
  · exact context_11_23490_756297
  · exact context_11_23491_756298

theorem selected_cut_29945 : selected 8 ⟨756345, by decide⟩
    (prefixPartial 13 375872) = some ⟨13, 2, 0, 756345, 375872, 2613, 16384⟩ := by
  decide +kernel

theorem context_13_375872_756345 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375872 ⟨756345, by decide⟩ :=
  accepted_of_selected 13 375872 ⟨756345, by decide⟩ ⟨13, 2, 0, 756345, 375872, 2613, 16384⟩
    (by decide) selected_cut_29945

theorem selected_cut_29946 : selected 8 ⟨756375, by decide⟩
    (prefixPartial 13 375873) = some ⟨13, 2, 0, 756375, 375873, 1709, 16384⟩ := by
  decide +kernel

theorem context_13_375873_756375 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375873 ⟨756375, by decide⟩ :=
  accepted_of_selected 13 375873 ⟨756375, by decide⟩ ⟨13, 2, 0, 756375, 375873, 1709, 16384⟩
    (by decide) selected_cut_29946

theorem selected_cut_29947 : selected 8 ⟨756396, by decide⟩
    (prefixPartial 13 375874) = some ⟨13, 2, 0, 756396, 375874, 1545, 16384⟩ := by
  decide +kernel

theorem context_13_375874_756396 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375874 ⟨756396, by decide⟩ :=
  accepted_of_selected 13 375874 ⟨756396, by decide⟩ ⟨13, 2, 0, 756396, 375874, 1545, 16384⟩
    (by decide) selected_cut_29947

theorem selected_cut_29948 : selected 8 ⟨756406, by decide⟩
    (prefixPartial 13 375875) = some ⟨13, 2, 0, 756406, 375875, 749, 16384⟩ := by
  decide +kernel

theorem context_13_375875_756406 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375875 ⟨756406, by decide⟩ :=
  accepted_of_selected 13 375875 ⟨756406, by decide⟩ ⟨13, 2, 0, 756406, 375875, 749, 16384⟩
    (by decide) selected_cut_29948

theorem unmarked_context_12_93968_756407 : frontier 9 ⟨756407, by decide⟩
    (prefixCache 12 93968) (prefixPartial 12 93968) = false := by
  decide +kernel

theorem node_context_12_93968_756407 : EJMOriginalGlobalDAGData.nodes 9 ⟨756407, by decide⟩ =
    .split (coordinate 12) (![⟨756345, by decide⟩,⟨756375, by decide⟩,⟨756396, by decide⟩,⟨756406, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93968_756407 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93968 ⟨756407, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93968
    ⟨756407, by decide⟩ (by decide) (![⟨756345, by decide⟩,⟨756375, by decide⟩,⟨756396, by decide⟩,⟨756406, by decide⟩]) unmarked_context_12_93968_756407 node_context_12_93968_756407
  intro a
  fin_cases a
  · exact context_13_375872_756345
  · exact context_13_375873_756375
  · exact context_13_375874_756396
  · exact context_13_375875_756406

theorem selected_cut_29949 : selected 8 ⟨756454, by decide⟩
    (prefixPartial 13 375876) = some ⟨13, 2, 0, 756454, 375876, 2741, 16384⟩ := by
  decide +kernel

theorem context_13_375876_756454 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375876 ⟨756454, by decide⟩ :=
  accepted_of_selected 13 375876 ⟨756454, by decide⟩ ⟨13, 2, 0, 756454, 375876, 2741, 16384⟩
    (by decide) selected_cut_29949

theorem selected_cut_29950 : selected 8 ⟨756486, by decide⟩
    (prefixPartial 13 375877) = some ⟨13, 2, 0, 756486, 375877, 1725, 16384⟩ := by
  decide +kernel

theorem context_13_375877_756486 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375877 ⟨756486, by decide⟩ :=
  accepted_of_selected 13 375877 ⟨756486, by decide⟩ ⟨13, 2, 0, 756486, 375877, 1725, 16384⟩
    (by decide) selected_cut_29950

theorem selected_cut_29951 : selected 8 ⟨756512, by decide⟩
    (prefixPartial 13 375878) = some ⟨13, 2, 0, 756512, 375878, 1909, 16384⟩ := by
  decide +kernel

theorem context_13_375878_756512 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375878 ⟨756512, by decide⟩ :=
  accepted_of_selected 13 375878 ⟨756512, by decide⟩ ⟨13, 2, 0, 756512, 375878, 1909, 16384⟩
    (by decide) selected_cut_29951

theorem selected_cut_29952 : selected 8 ⟨756521, by decide⟩
    (prefixPartial 13 375879) = some ⟨13, 2, 0, 756521, 375879, 633, 16384⟩ := by
  decide +kernel

theorem context_13_375879_756521 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375879 ⟨756521, by decide⟩ :=
  accepted_of_selected 13 375879 ⟨756521, by decide⟩ ⟨13, 2, 0, 756521, 375879, 633, 16384⟩
    (by decide) selected_cut_29952

theorem unmarked_context_12_93969_756522 : frontier 9 ⟨756522, by decide⟩
    (prefixCache 12 93969) (prefixPartial 12 93969) = false := by
  decide +kernel

theorem node_context_12_93969_756522 : EJMOriginalGlobalDAGData.nodes 9 ⟨756522, by decide⟩ =
    .split (coordinate 12) (![⟨756454, by decide⟩,⟨756486, by decide⟩,⟨756512, by decide⟩,⟨756521, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93969_756522 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93969 ⟨756522, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93969
    ⟨756522, by decide⟩ (by decide) (![⟨756454, by decide⟩,⟨756486, by decide⟩,⟨756512, by decide⟩,⟨756521, by decide⟩]) unmarked_context_12_93969_756522 node_context_12_93969_756522
  intro a
  fin_cases a
  · exact context_13_375876_756454
  · exact context_13_375877_756486
  · exact context_13_375878_756512
  · exact context_13_375879_756521

theorem selected_cut_29953 : selected 8 ⟨756568, by decide⟩
    (prefixPartial 13 375880) = some ⟨13, 2, 0, 756568, 375880, 2717, 16384⟩ := by
  decide +kernel

theorem context_13_375880_756568 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375880 ⟨756568, by decide⟩ :=
  accepted_of_selected 13 375880 ⟨756568, by decide⟩ ⟨13, 2, 0, 756568, 375880, 2717, 16384⟩
    (by decide) selected_cut_29953

theorem selected_cut_29954 : selected 8 ⟨756603, by decide⟩
    (prefixPartial 13 375881) = some ⟨13, 2, 0, 756603, 375881, 1825, 16384⟩ := by
  decide +kernel

theorem context_13_375881_756603 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375881 ⟨756603, by decide⟩ :=
  accepted_of_selected 13 375881 ⟨756603, by decide⟩ ⟨13, 2, 0, 756603, 375881, 1825, 16384⟩
    (by decide) selected_cut_29954

theorem selected_cut_29955 : selected 8 ⟨756635, by decide⟩
    (prefixPartial 13 375882) = some ⟨13, 2, 0, 756635, 375882, 1729, 16384⟩ := by
  decide +kernel

theorem context_13_375882_756635 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375882 ⟨756635, by decide⟩ :=
  accepted_of_selected 13 375882 ⟨756635, by decide⟩ ⟨13, 2, 0, 756635, 375882, 1729, 16384⟩
    (by decide) selected_cut_29955

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
