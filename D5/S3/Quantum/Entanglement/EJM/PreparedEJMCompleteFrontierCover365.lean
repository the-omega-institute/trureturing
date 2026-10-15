/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover364
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem unmarked_context_10_17708_916723 : frontier 11 ⟨916723, by decide⟩
    (prefixCache 10 17708) (prefixPartial 10 17708) = false := by
  decide +kernel

theorem node_context_10_17708_916723 : EJMOriginalGlobalDAGData.nodes 11 ⟨916723, by decide⟩ =
    .split (coordinate 10) (![⟨907917, by decide⟩,⟨916672, by decide⟩,⟨916692, by decide⟩,⟨916722, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17708_916723 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17708 ⟨916723, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17708
    ⟨916723, by decide⟩ (by decide) (![⟨907917, by decide⟩,⟨916672, by decide⟩,⟨916692, by decide⟩,⟨916722, by decide⟩]) unmarked_context_10_17708_916723 node_context_10_17708_916723
  intro a
  fin_cases a
  · exact context_11_70832_907917
  · exact context_11_70833_916672
  · exact context_11_70834_916692
  · exact context_11_70835_916722

theorem selected_cut_35043 : selected 10 ⟨916738, by decide⟩
    (prefixPartial 11 70836) = some ⟨11, 2, 0, 916738, 70836, 1697, 262144⟩ := by
  decide +kernel

theorem context_11_70836_916738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70836 ⟨916738, by decide⟩ :=
  accepted_of_selected 11 70836 ⟨916738, by decide⟩ ⟨11, 2, 0, 916738, 70836, 1697, 262144⟩
    (by decide) selected_cut_35043

theorem selected_cut_35044 : selected 10 ⟨916752, by decide⟩
    (prefixPartial 11 70837) = some ⟨11, 2, 0, 916752, 70837, 1473, 262144⟩ := by
  decide +kernel

theorem context_11_70837_916752 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70837 ⟨916752, by decide⟩ :=
  accepted_of_selected 11 70837 ⟨916752, by decide⟩ ⟨11, 2, 0, 916752, 70837, 1473, 262144⟩
    (by decide) selected_cut_35044

theorem selected_cut_35045 : selected 10 ⟨916762, by decide⟩
    (prefixPartial 11 70838) = some ⟨11, 2, 0, 916762, 70838, 1037, 262144⟩ := by
  decide +kernel

theorem context_11_70838_916762 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70838 ⟨916762, by decide⟩ :=
  accepted_of_selected 11 70838 ⟨916762, by decide⟩ ⟨11, 2, 0, 916762, 70838, 1037, 262144⟩
    (by decide) selected_cut_35045

theorem selected_cut_35046 : selected 10 ⟨916782, by decide⟩
    (prefixPartial 11 70839) = some ⟨11, 2, 0, 916782, 70839, 1449, 262144⟩ := by
  decide +kernel

theorem context_11_70839_916782 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70839 ⟨916782, by decide⟩ :=
  accepted_of_selected 11 70839 ⟨916782, by decide⟩ ⟨11, 2, 0, 916782, 70839, 1449, 262144⟩
    (by decide) selected_cut_35046

theorem unmarked_context_10_17709_916783 : frontier 11 ⟨916783, by decide⟩
    (prefixCache 10 17709) (prefixPartial 10 17709) = false := by
  decide +kernel

theorem node_context_10_17709_916783 : EJMOriginalGlobalDAGData.nodes 11 ⟨916783, by decide⟩ =
    .split (coordinate 10) (![⟨916738, by decide⟩,⟨916752, by decide⟩,⟨916762, by decide⟩,⟨916782, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17709_916783 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17709 ⟨916783, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17709
    ⟨916783, by decide⟩ (by decide) (![⟨916738, by decide⟩,⟨916752, by decide⟩,⟨916762, by decide⟩,⟨916782, by decide⟩]) unmarked_context_10_17709_916783 node_context_10_17709_916783
  intro a
  fin_cases a
  · exact context_11_70836_916738
  · exact context_11_70837_916752
  · exact context_11_70838_916762
  · exact context_11_70839_916782

theorem selected_cut_35047 : selected 11 ⟨916838, by decide⟩
    (prefixPartial 10 17710) = some ⟨10, 2, 0, 916838, 17710, 3413, 1048576⟩ := by
  decide +kernel

theorem context_10_17710_916838 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17710 ⟨916838, by decide⟩ :=
  accepted_of_selected 10 17710 ⟨916838, by decide⟩ ⟨10, 2, 0, 916838, 17710, 3413, 1048576⟩
    (by decide) selected_cut_35047

theorem selected_cut_35048 : selected 11 ⟨916888, by decide⟩
    (prefixPartial 10 17711) = some ⟨10, 2, 0, 916888, 17711, 1169, 1048576⟩ := by
  decide +kernel

theorem context_10_17711_916888 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17711 ⟨916888, by decide⟩ :=
  accepted_of_selected 10 17711 ⟨916888, by decide⟩ ⟨10, 2, 0, 916888, 17711, 1169, 1048576⟩
    (by decide) selected_cut_35048

theorem unmarked_context_9_4427_916889 : frontier 12 ⟨916889, by decide⟩
    (prefixCache 9 4427) (prefixPartial 9 4427) = false := by
  decide +kernel

theorem node_context_9_4427_916889 : EJMOriginalGlobalDAGData.nodes 12 ⟨916889, by decide⟩ =
    .split (coordinate 9) (![⟨916723, by decide⟩,⟨916783, by decide⟩,⟨916838, by decide⟩,⟨916888, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4427_916889 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4427 ⟨916889, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4427
    ⟨916889, by decide⟩ (by decide) (![⟨916723, by decide⟩,⟨916783, by decide⟩,⟨916838, by decide⟩,⟨916888, by decide⟩]) unmarked_context_9_4427_916889 node_context_9_4427_916889
  intro a
  fin_cases a
  · exact context_10_17708_916723
  · exact context_10_17709_916783
  · exact context_10_17710_916838
  · exact context_10_17711_916888

theorem unmarked_context_8_1106_916890 : frontier 13 ⟨916890, by decide⟩
    (prefixCache 8 1106) (prefixPartial 8 1106) = false := by
  decide +kernel

theorem node_context_8_1106_916890 : EJMOriginalGlobalDAGData.nodes 13 ⟨916890, by decide⟩ =
    .split (coordinate 8) (![⟨915076, by decide⟩,⟨915827, by decide⟩,⟨916644, by decide⟩,⟨916889, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1106_916890 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1106 ⟨916890, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1106
    ⟨916890, by decide⟩ (by decide) (![⟨915076, by decide⟩,⟨915827, by decide⟩,⟨916644, by decide⟩,⟨916889, by decide⟩]) unmarked_context_8_1106_916890 node_context_8_1106_916890
  intro a
  fin_cases a
  · exact context_9_4424_915076
  · exact context_9_4425_915827
  · exact context_9_4426_916644
  · exact context_9_4427_916889

theorem selected_cut_35049 : selected 13 ⟨14298, by decide⟩
    (prefixPartial 8 1107) = some ⟨8, 1, 0, 14298, 1107, 1, 16777216⟩ := by
  decide +kernel

theorem context_8_1107_14298 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1107 ⟨14298, by decide⟩ :=
  accepted_of_selected 8 1107 ⟨14298, by decide⟩ ⟨8, 1, 0, 14298, 1107, 1, 16777216⟩
    (by decide) selected_cut_35049

theorem unmarked_context_7_276_916891 : frontier 14 ⟨916891, by decide⟩
    (prefixCache 7 276) (prefixPartial 7 276) = false := by
  decide +kernel

theorem node_context_7_276_916891 : EJMOriginalGlobalDAGData.nodes 14 ⟨916891, by decide⟩ =
    .split (coordinate 7) (![⟨908884, by decide⟩,⟨911607, by decide⟩,⟨916890, by decide⟩,⟨14298, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_7_276_916891 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 276 ⟨916891, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 7 276
    ⟨916891, by decide⟩ (by decide) (![⟨908884, by decide⟩,⟨911607, by decide⟩,⟨916890, by decide⟩,⟨14298, by decide⟩]) unmarked_context_7_276_916891 node_context_7_276_916891
  intro a
  fin_cases a
  · exact context_8_1104_908884
  · exact context_8_1105_911607
  · exact context_8_1106_916890
  · exact context_8_1107_14298

theorem selected_cut_35050 : selected 13 ⟨14300, by decide⟩
    (prefixPartial 8 1108) = some ⟨8, 1, 0, 14300, 1108, 1, 16777216⟩ := by
  decide +kernel

theorem context_8_1108_14300 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1108 ⟨14300, by decide⟩ :=
  accepted_of_selected 8 1108 ⟨14300, by decide⟩ ⟨8, 1, 0, 14300, 1108, 1, 16777216⟩
    (by decide) selected_cut_35050

theorem selected_cut_35051 : selected 10 ⟨916993, by decide⟩
    (prefixPartial 11 70976) = some ⟨11, 2, 0, 916993, 70976, 4049, 262144⟩ := by
  decide +kernel

theorem context_11_70976_916993 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70976 ⟨916993, by decide⟩ :=
  accepted_of_selected 11 70976 ⟨916993, by decide⟩ ⟨11, 2, 0, 916993, 70976, 4049, 262144⟩
    (by decide) selected_cut_35051

theorem selected_cut_35052 : selected 9 ⟨917069, by decide⟩
    (prefixPartial 12 283908) = some ⟨12, 2, 0, 917069, 283908, 1541, 65536⟩ := by
  decide +kernel

theorem context_12_283908_917069 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283908 ⟨917069, by decide⟩ :=
  accepted_of_selected 12 283908 ⟨917069, by decide⟩ ⟨12, 2, 0, 917069, 283908, 1541, 65536⟩
    (by decide) selected_cut_35052

theorem selected_cut_35053 : selected 9 ⟨891951, by decide⟩
    (prefixPartial 12 283909) = some ⟨12, 1, 0, 891951, 283909, 1, 65536⟩ := by
  decide +kernel

theorem context_12_283909_891951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283909 ⟨891951, by decide⟩ :=
  accepted_of_selected 12 283909 ⟨891951, by decide⟩ ⟨12, 1, 0, 891951, 283909, 1, 65536⟩
    (by decide) selected_cut_35053

theorem selected_cut_35054 : selected 9 ⟨917126, by decide⟩
    (prefixPartial 12 283910) = some ⟨12, 2, 0, 917126, 283910, 2945, 65536⟩ := by
  decide +kernel

theorem context_12_283910_917126 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283910 ⟨917126, by decide⟩ :=
  accepted_of_selected 12 283910 ⟨917126, by decide⟩ ⟨12, 2, 0, 917126, 283910, 2945, 65536⟩
    (by decide) selected_cut_35054

theorem selected_cut_35055 : selected 9 ⟨893, by decide⟩
    (prefixPartial 12 283911) = some ⟨12, 1, 0, 893, 283911, 1, 65536⟩ := by
  decide +kernel

theorem context_12_283911_893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283911 ⟨893, by decide⟩ :=
  accepted_of_selected 12 283911 ⟨893, by decide⟩ ⟨12, 1, 0, 893, 283911, 1, 65536⟩
    (by decide) selected_cut_35055

theorem unmarked_context_11_70977_917127 : frontier 10 ⟨917127, by decide⟩
    (prefixCache 11 70977) (prefixPartial 11 70977) = false := by
  decide +kernel

theorem node_context_11_70977_917127 : EJMOriginalGlobalDAGData.nodes 10 ⟨917127, by decide⟩ =
    .split (coordinate 11) (![⟨917069, by decide⟩,⟨891951, by decide⟩,⟨917126, by decide⟩,⟨893, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_70977_917127 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70977 ⟨917127, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 70977
    ⟨917127, by decide⟩ (by decide) (![⟨917069, by decide⟩,⟨891951, by decide⟩,⟨917126, by decide⟩,⟨893, by decide⟩]) unmarked_context_11_70977_917127 node_context_11_70977_917127
  intro a
  fin_cases a
  · exact context_12_283908_917069
  · exact context_12_283909_891951
  · exact context_12_283910_917126
  · exact context_12_283911_893

theorem selected_cut_35056 : selected 9 ⟨917224, by decide⟩
    (prefixPartial 12 283912) = some ⟨12, 2, 0, 917224, 283912, 2593, 65536⟩ := by
  decide +kernel

theorem context_12_283912_917224 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283912 ⟨917224, by decide⟩ :=
  accepted_of_selected 12 283912 ⟨917224, by decide⟩ ⟨12, 2, 0, 917224, 283912, 2593, 65536⟩
    (by decide) selected_cut_35056

theorem selected_cut_35057 : selected 9 ⟨917255, by decide⟩
    (prefixPartial 12 283913) = some ⟨12, 2, 0, 917255, 283913, 2553, 65536⟩ := by
  decide +kernel

theorem context_12_283913_917255 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283913 ⟨917255, by decide⟩ :=
  accepted_of_selected 12 283913 ⟨917255, by decide⟩ ⟨12, 2, 0, 917255, 283913, 2553, 65536⟩
    (by decide) selected_cut_35057

theorem selected_cut_35058 : selected 9 ⟨917321, by decide⟩
    (prefixPartial 12 283914) = some ⟨12, 2, 0, 917321, 283914, 3149, 65536⟩ := by
  decide +kernel

theorem context_12_283914_917321 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283914 ⟨917321, by decide⟩ :=
  accepted_of_selected 12 283914 ⟨917321, by decide⟩ ⟨12, 2, 0, 917321, 283914, 3149, 65536⟩
    (by decide) selected_cut_35058

theorem selected_cut_35059 : selected 9 ⟨917379, by decide⟩
    (prefixPartial 12 283915) = some ⟨12, 2, 0, 917379, 283915, 2949, 65536⟩ := by
  decide +kernel

theorem context_12_283915_917379 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283915 ⟨917379, by decide⟩ :=
  accepted_of_selected 12 283915 ⟨917379, by decide⟩ ⟨12, 2, 0, 917379, 283915, 2949, 65536⟩
    (by decide) selected_cut_35059

theorem unmarked_context_11_70978_917380 : frontier 10 ⟨917380, by decide⟩
    (prefixCache 11 70978) (prefixPartial 11 70978) = false := by
  decide +kernel

theorem node_context_11_70978_917380 : EJMOriginalGlobalDAGData.nodes 10 ⟨917380, by decide⟩ =
    .split (coordinate 11) (![⟨917224, by decide⟩,⟨917255, by decide⟩,⟨917321, by decide⟩,⟨917379, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_70978_917380 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70978 ⟨917380, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 70978
    ⟨917380, by decide⟩ (by decide) (![⟨917224, by decide⟩,⟨917255, by decide⟩,⟨917321, by decide⟩,⟨917379, by decide⟩]) unmarked_context_11_70978_917380 node_context_11_70978_917380
  intro a
  fin_cases a
  · exact context_12_283912_917224
  · exact context_12_283913_917255
  · exact context_12_283914_917321
  · exact context_12_283915_917379

theorem selected_cut_35060 : selected 10 ⟨1736, by decide⟩
    (prefixPartial 11 70979) = some ⟨11, 1, 0, 1736, 70979, 1, 262144⟩ := by
  decide +kernel

theorem context_11_70979_1736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70979 ⟨1736, by decide⟩ :=
  accepted_of_selected 11 70979 ⟨1736, by decide⟩ ⟨11, 1, 0, 1736, 70979, 1, 262144⟩
    (by decide) selected_cut_35060

theorem unmarked_context_10_17744_917381 : frontier 11 ⟨917381, by decide⟩
    (prefixCache 10 17744) (prefixPartial 10 17744) = false := by
  decide +kernel

theorem node_context_10_17744_917381 : EJMOriginalGlobalDAGData.nodes 11 ⟨917381, by decide⟩ =
    .split (coordinate 10) (![⟨916993, by decide⟩,⟨917127, by decide⟩,⟨917380, by decide⟩,⟨1736, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17744_917381 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17744 ⟨917381, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17744
    ⟨917381, by decide⟩ (by decide) (![⟨916993, by decide⟩,⟨917127, by decide⟩,⟨917380, by decide⟩,⟨1736, by decide⟩]) unmarked_context_10_17744_917381 node_context_10_17744_917381
  intro a
  fin_cases a
  · exact context_11_70976_916993
  · exact context_11_70977_917127
  · exact context_11_70978_917380
  · exact context_11_70979_1736

theorem selected_cut_35061 : selected 10 ⟨917456, by decide⟩
    (prefixPartial 11 70980) = some ⟨11, 2, 0, 917456, 70980, 2829, 262144⟩ := by
  decide +kernel

theorem context_11_70980_917456 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70980 ⟨917456, by decide⟩ :=
  accepted_of_selected 11 70980 ⟨917456, by decide⟩ ⟨11, 2, 0, 917456, 70980, 2829, 262144⟩
    (by decide) selected_cut_35061

theorem selected_cut_35062 : selected 10 ⟨892405, by decide⟩
    (prefixPartial 11 70981) = some ⟨11, 1, 0, 892405, 70981, 1, 262144⟩ := by
  decide +kernel

theorem context_11_70981_892405 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70981 ⟨892405, by decide⟩ :=
  accepted_of_selected 11 70981 ⟨892405, by decide⟩ ⟨11, 1, 0, 892405, 70981, 1, 262144⟩
    (by decide) selected_cut_35062

theorem selected_cut_35063 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 283928) = some ⟨12, 1, 0, 1738, 283928, 1, 65536⟩ := by
  decide +kernel

theorem context_12_283928_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283928 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 283928 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 283928, 1, 65536⟩
    (by decide) selected_cut_35063

theorem selected_cut_35064 : selected 9 ⟨917486, by decide⟩
    (prefixPartial 12 283929) = some ⟨12, 2, 0, 917486, 283929, 1025, 65536⟩ := by
  decide +kernel

theorem context_12_283929_917486 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283929 ⟨917486, by decide⟩ :=
  accepted_of_selected 12 283929 ⟨917486, by decide⟩ ⟨12, 2, 0, 917486, 283929, 1025, 65536⟩
    (by decide) selected_cut_35064

theorem selected_cut_35065 : selected 9 ⟨917521, by decide⟩
    (prefixPartial 12 283930) = some ⟨12, 2, 0, 917521, 283930, 2341, 65536⟩ := by
  decide +kernel

theorem context_12_283930_917521 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283930 ⟨917521, by decide⟩ :=
  accepted_of_selected 12 283930 ⟨917521, by decide⟩ ⟨12, 2, 0, 917521, 283930, 2341, 65536⟩
    (by decide) selected_cut_35065

theorem selected_cut_35066 : selected 9 ⟨917549, by decide⟩
    (prefixPartial 12 283931) = some ⟨12, 2, 0, 917549, 283931, 2229, 65536⟩ := by
  decide +kernel

theorem context_12_283931_917549 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283931 ⟨917549, by decide⟩ :=
  accepted_of_selected 12 283931 ⟨917549, by decide⟩ ⟨12, 2, 0, 917549, 283931, 2229, 65536⟩
    (by decide) selected_cut_35066

theorem unmarked_context_11_70982_917550 : frontier 10 ⟨917550, by decide⟩
    (prefixCache 11 70982) (prefixPartial 11 70982) = false := by
  decide +kernel

theorem node_context_11_70982_917550 : EJMOriginalGlobalDAGData.nodes 10 ⟨917550, by decide⟩ =
    .split (coordinate 11) (![⟨1738, by decide⟩,⟨917486, by decide⟩,⟨917521, by decide⟩,⟨917549, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_70982_917550 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70982 ⟨917550, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 70982
    ⟨917550, by decide⟩ (by decide) (![⟨1738, by decide⟩,⟨917486, by decide⟩,⟨917521, by decide⟩,⟨917549, by decide⟩]) unmarked_context_11_70982_917550 node_context_11_70982_917550
  intro a
  fin_cases a
  · exact context_12_283928_1738
  · exact context_12_283929_917486
  · exact context_12_283930_917521
  · exact context_12_283931_917549

theorem selected_cut_35067 : selected 10 ⟨1736, by decide⟩
    (prefixPartial 11 70983) = some ⟨11, 1, 0, 1736, 70983, 1, 262144⟩ := by
  decide +kernel

theorem context_11_70983_1736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70983 ⟨1736, by decide⟩ :=
  accepted_of_selected 11 70983 ⟨1736, by decide⟩ ⟨11, 1, 0, 1736, 70983, 1, 262144⟩
    (by decide) selected_cut_35067

theorem unmarked_context_10_17745_917551 : frontier 11 ⟨917551, by decide⟩
    (prefixCache 10 17745) (prefixPartial 10 17745) = false := by
  decide +kernel

theorem node_context_10_17745_917551 : EJMOriginalGlobalDAGData.nodes 11 ⟨917551, by decide⟩ =
    .split (coordinate 10) (![⟨917456, by decide⟩,⟨892405, by decide⟩,⟨917550, by decide⟩,⟨1736, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17745_917551 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17745 ⟨917551, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17745
    ⟨917551, by decide⟩ (by decide) (![⟨917456, by decide⟩,⟨892405, by decide⟩,⟨917550, by decide⟩,⟨1736, by decide⟩]) unmarked_context_10_17745_917551 node_context_10_17745_917551
  intro a
  fin_cases a
  · exact context_11_70980_917456
  · exact context_11_70981_892405
  · exact context_11_70982_917550
  · exact context_11_70983_1736

theorem selected_cut_35068 : selected 10 ⟨917661, by decide⟩
    (prefixPartial 11 70984) = some ⟨11, 2, 0, 917661, 70984, 3673, 262144⟩ := by
  decide +kernel

theorem context_11_70984_917661 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70984 ⟨917661, by decide⟩ :=
  accepted_of_selected 11 70984 ⟨917661, by decide⟩ ⟨11, 2, 0, 917661, 70984, 3673, 262144⟩
    (by decide) selected_cut_35068

theorem selected_cut_35069 : selected 10 ⟨917734, by decide⟩
    (prefixPartial 11 70985) = some ⟨11, 2, 0, 917734, 70985, 3025, 262144⟩ := by
  decide +kernel

theorem context_11_70985_917734 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70985 ⟨917734, by decide⟩ :=
  accepted_of_selected 11 70985 ⟨917734, by decide⟩ ⟨11, 2, 0, 917734, 70985, 3025, 262144⟩
    (by decide) selected_cut_35069

theorem selected_cut_35070 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 283944) = some ⟨12, 1, 0, 1738, 283944, 1, 65536⟩ := by
  decide +kernel

theorem context_12_283944_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283944 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 283944 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 283944, 1, 65536⟩
    (by decide) selected_cut_35070

theorem selected_cut_35071 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 283945) = some ⟨12, 1, 0, 1738, 283945, 1, 65536⟩ := by
  decide +kernel

theorem context_12_283945_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283945 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 283945 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 283945, 1, 65536⟩
    (by decide) selected_cut_35071

theorem selected_cut_35072 : selected 9 ⟨917783, by decide⟩
    (prefixPartial 12 283946) = some ⟨12, 2, 0, 917783, 283946, 1961, 65536⟩ := by
  decide +kernel

theorem context_12_283946_917783 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283946 ⟨917783, by decide⟩ :=
  accepted_of_selected 12 283946 ⟨917783, by decide⟩ ⟨12, 2, 0, 917783, 283946, 1961, 65536⟩
    (by decide) selected_cut_35072

theorem selected_cut_35073 : selected 9 ⟨917832, by decide⟩
    (prefixPartial 12 283947) = some ⟨12, 2, 0, 917832, 283947, 2365, 65536⟩ := by
  decide +kernel

theorem context_12_283947_917832 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283947 ⟨917832, by decide⟩ :=
  accepted_of_selected 12 283947 ⟨917832, by decide⟩ ⟨12, 2, 0, 917832, 283947, 2365, 65536⟩
    (by decide) selected_cut_35073

theorem unmarked_context_11_70986_917833 : frontier 10 ⟨917833, by decide⟩
    (prefixCache 11 70986) (prefixPartial 11 70986) = false := by
  decide +kernel

theorem node_context_11_70986_917833 : EJMOriginalGlobalDAGData.nodes 10 ⟨917833, by decide⟩ =
    .split (coordinate 11) (![⟨1738, by decide⟩,⟨1738, by decide⟩,⟨917783, by decide⟩,⟨917832, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_70986_917833 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70986 ⟨917833, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 70986
    ⟨917833, by decide⟩ (by decide) (![⟨1738, by decide⟩,⟨1738, by decide⟩,⟨917783, by decide⟩,⟨917832, by decide⟩]) unmarked_context_11_70986_917833 node_context_11_70986_917833
  intro a
  fin_cases a
  · exact context_12_283944_1738
  · exact context_12_283945_1738
  · exact context_12_283946_917783
  · exact context_12_283947_917832

theorem selected_cut_35074 : selected 10 ⟨917889, by decide⟩
    (prefixPartial 11 70987) = some ⟨11, 2, 0, 917889, 70987, 1825, 262144⟩ := by
  decide +kernel

theorem context_11_70987_917889 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70987 ⟨917889, by decide⟩ :=
  accepted_of_selected 11 70987 ⟨917889, by decide⟩ ⟨11, 2, 0, 917889, 70987, 1825, 262144⟩
    (by decide) selected_cut_35074

theorem unmarked_context_10_17746_917890 : frontier 11 ⟨917890, by decide⟩
    (prefixCache 10 17746) (prefixPartial 10 17746) = false := by
  decide +kernel

theorem node_context_10_17746_917890 : EJMOriginalGlobalDAGData.nodes 11 ⟨917890, by decide⟩ =
    .split (coordinate 10) (![⟨917661, by decide⟩,⟨917734, by decide⟩,⟨917833, by decide⟩,⟨917889, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17746_917890 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17746 ⟨917890, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17746
    ⟨917890, by decide⟩ (by decide) (![⟨917661, by decide⟩,⟨917734, by decide⟩,⟨917833, by decide⟩,⟨917889, by decide⟩]) unmarked_context_10_17746_917890 node_context_10_17746_917890
  intro a
  fin_cases a
  · exact context_11_70984_917661
  · exact context_11_70985_917734
  · exact context_11_70986_917833
  · exact context_11_70987_917889

theorem selected_cut_35075 : selected 11 ⟨3440, by decide⟩
    (prefixPartial 10 17747) = some ⟨10, 1, 0, 3440, 17747, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_17747_3440 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17747 ⟨3440, by decide⟩ :=
  accepted_of_selected 10 17747 ⟨3440, by decide⟩ ⟨10, 1, 0, 3440, 17747, 1, 1048576⟩
    (by decide) selected_cut_35075

theorem unmarked_context_9_4436_917891 : frontier 12 ⟨917891, by decide⟩
    (prefixCache 9 4436) (prefixPartial 9 4436) = false := by
  decide +kernel

theorem node_context_9_4436_917891 : EJMOriginalGlobalDAGData.nodes 12 ⟨917891, by decide⟩ =
    .split (coordinate 9) (![⟨917381, by decide⟩,⟨917551, by decide⟩,⟨917890, by decide⟩,⟨3440, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4436_917891 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4436 ⟨917891, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4436
    ⟨917891, by decide⟩ (by decide) (![⟨917381, by decide⟩,⟨917551, by decide⟩,⟨917890, by decide⟩,⟨3440, by decide⟩]) unmarked_context_9_4436_917891 node_context_9_4436_917891
  intro a
  fin_cases a
  · exact context_10_17744_917381
  · exact context_10_17745_917551
  · exact context_10_17746_917890
  · exact context_10_17747_3440

theorem selected_cut_35076 : selected 10 ⟨918026, by decide⟩
    (prefixPartial 11 70992) = some ⟨11, 2, 0, 918026, 70992, 3033, 262144⟩ := by
  decide +kernel

theorem context_11_70992_918026 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70992 ⟨918026, by decide⟩ :=
  accepted_of_selected 11 70992 ⟨918026, by decide⟩ ⟨11, 2, 0, 918026, 70992, 3033, 262144⟩
    (by decide) selected_cut_35076

theorem selected_cut_35077 : selected 10 ⟨918115, by decide⟩
    (prefixPartial 11 70993) = some ⟨11, 2, 0, 918115, 70993, 2813, 262144⟩ := by
  decide +kernel

theorem context_11_70993_918115 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70993 ⟨918115, by decide⟩ :=
  accepted_of_selected 11 70993 ⟨918115, by decide⟩ ⟨11, 2, 0, 918115, 70993, 2813, 262144⟩
    (by decide) selected_cut_35077

theorem selected_cut_35078 : selected 9 ⟨918177, by decide⟩
    (prefixPartial 12 283976) = some ⟨12, 2, 0, 918177, 283976, 1877, 65536⟩ := by
  decide +kernel

theorem context_12_283976_918177 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283976 ⟨918177, by decide⟩ :=
  accepted_of_selected 12 283976 ⟨918177, by decide⟩ ⟨12, 2, 0, 918177, 283976, 1877, 65536⟩
    (by decide) selected_cut_35078

theorem selected_cut_35079 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 283977) = some ⟨12, 1, 0, 896706, 283977, 1, 65536⟩ := by
  decide +kernel

theorem context_12_283977_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283977 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 283977 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 283977, 1, 65536⟩
    (by decide) selected_cut_35079

theorem selected_cut_35080 : selected 9 ⟨918220, by decide⟩
    (prefixPartial 12 283978) = some ⟨12, 2, 0, 918220, 283978, 1993, 65536⟩ := by
  decide +kernel

theorem context_12_283978_918220 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283978 ⟨918220, by decide⟩ :=
  accepted_of_selected 12 283978 ⟨918220, by decide⟩ ⟨12, 2, 0, 918220, 283978, 1993, 65536⟩
    (by decide) selected_cut_35080

theorem selected_cut_35081 : selected 9 ⟨918259, by decide⟩
    (prefixPartial 12 283979) = some ⟨12, 2, 0, 918259, 283979, 1861, 65536⟩ := by
  decide +kernel

theorem context_12_283979_918259 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283979 ⟨918259, by decide⟩ :=
  accepted_of_selected 12 283979 ⟨918259, by decide⟩ ⟨12, 2, 0, 918259, 283979, 1861, 65536⟩
    (by decide) selected_cut_35081

theorem unmarked_context_11_70994_918260 : frontier 10 ⟨918260, by decide⟩
    (prefixCache 11 70994) (prefixPartial 11 70994) = false := by
  decide +kernel

theorem node_context_11_70994_918260 : EJMOriginalGlobalDAGData.nodes 10 ⟨918260, by decide⟩ =
    .split (coordinate 11) (![⟨918177, by decide⟩,⟨896706, by decide⟩,⟨918220, by decide⟩,⟨918259, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_70994_918260 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70994 ⟨918260, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 70994
    ⟨918260, by decide⟩ (by decide) (![⟨918177, by decide⟩,⟨896706, by decide⟩,⟨918220, by decide⟩,⟨918259, by decide⟩]) unmarked_context_11_70994_918260 node_context_11_70994_918260
  intro a
  fin_cases a
  · exact context_12_283976_918177
  · exact context_12_283977_896706
  · exact context_12_283978_918220
  · exact context_12_283979_918259

theorem selected_cut_35082 : selected 10 ⟨1736, by decide⟩
    (prefixPartial 11 70995) = some ⟨11, 1, 0, 1736, 70995, 1, 262144⟩ := by
  decide +kernel

theorem context_11_70995_1736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70995 ⟨1736, by decide⟩ :=
  accepted_of_selected 11 70995 ⟨1736, by decide⟩ ⟨11, 1, 0, 1736, 70995, 1, 262144⟩
    (by decide) selected_cut_35082

theorem unmarked_context_10_17748_918261 : frontier 11 ⟨918261, by decide⟩
    (prefixCache 10 17748) (prefixPartial 10 17748) = false := by
  decide +kernel

theorem node_context_10_17748_918261 : EJMOriginalGlobalDAGData.nodes 11 ⟨918261, by decide⟩ =
    .split (coordinate 10) (![⟨918026, by decide⟩,⟨918115, by decide⟩,⟨918260, by decide⟩,⟨1736, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17748_918261 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17748 ⟨918261, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17748
    ⟨918261, by decide⟩ (by decide) (![⟨918026, by decide⟩,⟨918115, by decide⟩,⟨918260, by decide⟩,⟨1736, by decide⟩]) unmarked_context_10_17748_918261 node_context_10_17748_918261
  intro a
  fin_cases a
  · exact context_11_70992_918026
  · exact context_11_70993_918115
  · exact context_11_70994_918260
  · exact context_11_70995_1736

theorem selected_cut_35083 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 17749) = some ⟨10, 1, 0, 893098, 17749, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_17749_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17749 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 17749 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 17749, 1, 1048576⟩
    (by decide) selected_cut_35083

theorem selected_cut_35084 : selected 10 ⟨918328, by decide⟩
    (prefixPartial 11 71000) = some ⟨11, 2, 0, 918328, 71000, 2381, 262144⟩ := by
  decide +kernel

theorem context_11_71000_918328 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71000 ⟨918328, by decide⟩ :=
  accepted_of_selected 11 71000 ⟨918328, by decide⟩ ⟨11, 2, 0, 918328, 71000, 2381, 262144⟩
    (by decide) selected_cut_35084

theorem selected_cut_35085 : selected 10 ⟨918375, by decide⟩
    (prefixPartial 11 71001) = some ⟨11, 2, 0, 918375, 71001, 1741, 262144⟩ := by
  decide +kernel

theorem context_11_71001_918375 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71001 ⟨918375, by decide⟩ :=
  accepted_of_selected 11 71001 ⟨918375, by decide⟩ ⟨11, 2, 0, 918375, 71001, 1741, 262144⟩
    (by decide) selected_cut_35085

theorem selected_cut_35086 : selected 10 ⟨918463, by decide⟩
    (prefixPartial 11 71002) = some ⟨11, 2, 0, 918463, 71002, 2289, 262144⟩ := by
  decide +kernel

theorem context_11_71002_918463 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71002 ⟨918463, by decide⟩ :=
  accepted_of_selected 11 71002 ⟨918463, by decide⟩ ⟨11, 2, 0, 918463, 71002, 2289, 262144⟩
    (by decide) selected_cut_35086

theorem selected_cut_35087 : selected 10 ⟨918504, by decide⟩
    (prefixPartial 11 71003) = some ⟨11, 2, 0, 918504, 71003, 1225, 262144⟩ := by
  decide +kernel

theorem context_11_71003_918504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71003 ⟨918504, by decide⟩ :=
  accepted_of_selected 11 71003 ⟨918504, by decide⟩ ⟨11, 2, 0, 918504, 71003, 1225, 262144⟩
    (by decide) selected_cut_35087

theorem unmarked_context_10_17750_918505 : frontier 11 ⟨918505, by decide⟩
    (prefixCache 10 17750) (prefixPartial 10 17750) = false := by
  decide +kernel

theorem node_context_10_17750_918505 : EJMOriginalGlobalDAGData.nodes 11 ⟨918505, by decide⟩ =
    .split (coordinate 10) (![⟨918328, by decide⟩,⟨918375, by decide⟩,⟨918463, by decide⟩,⟨918504, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17750_918505 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17750 ⟨918505, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17750
    ⟨918505, by decide⟩ (by decide) (![⟨918328, by decide⟩,⟨918375, by decide⟩,⟨918463, by decide⟩,⟨918504, by decide⟩]) unmarked_context_10_17750_918505 node_context_10_17750_918505
  intro a
  fin_cases a
  · exact context_11_71000_918328
  · exact context_11_71001_918375
  · exact context_11_71002_918463
  · exact context_11_71003_918504

theorem selected_cut_35088 : selected 11 ⟨3440, by decide⟩
    (prefixPartial 10 17751) = some ⟨10, 1, 0, 3440, 17751, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_17751_3440 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17751 ⟨3440, by decide⟩ :=
  accepted_of_selected 10 17751 ⟨3440, by decide⟩ ⟨10, 1, 0, 3440, 17751, 1, 1048576⟩
    (by decide) selected_cut_35088

theorem unmarked_context_9_4437_918506 : frontier 12 ⟨918506, by decide⟩
    (prefixCache 9 4437) (prefixPartial 9 4437) = false := by
  decide +kernel

theorem node_context_9_4437_918506 : EJMOriginalGlobalDAGData.nodes 12 ⟨918506, by decide⟩ =
    .split (coordinate 9) (![⟨918261, by decide⟩,⟨893098, by decide⟩,⟨918505, by decide⟩,⟨3440, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4437_918506 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4437 ⟨918506, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4437
    ⟨918506, by decide⟩ (by decide) (![⟨918261, by decide⟩,⟨893098, by decide⟩,⟨918505, by decide⟩,⟨3440, by decide⟩]) unmarked_context_9_4437_918506 node_context_9_4437_918506
  intro a
  fin_cases a
  · exact context_10_17748_918261
  · exact context_10_17749_893098
  · exact context_10_17750_918505
  · exact context_10_17751_3440

theorem selected_cut_35089 : selected 9 ⟨918545, by decide⟩
    (prefixPartial 12 284032) = some ⟨12, 2, 0, 918545, 284032, 1461, 65536⟩ := by
  decide +kernel

theorem context_12_284032_918545 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284032 ⟨918545, by decide⟩ :=
  accepted_of_selected 12 284032 ⟨918545, by decide⟩ ⟨12, 2, 0, 918545, 284032, 1461, 65536⟩
    (by decide) selected_cut_35089

theorem selected_cut_35090 : selected 9 ⟨918573, by decide⟩
    (prefixPartial 12 284033) = some ⟨12, 2, 0, 918573, 284033, 1329, 65536⟩ := by
  decide +kernel

theorem context_12_284033_918573 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284033 ⟨918573, by decide⟩ :=
  accepted_of_selected 12 284033 ⟨918573, by decide⟩ ⟨12, 2, 0, 918573, 284033, 1329, 65536⟩
    (by decide) selected_cut_35090

theorem selected_cut_35091 : selected 9 ⟨918596, by decide⟩
    (prefixPartial 12 284034) = some ⟨12, 2, 0, 918596, 284034, 1345, 65536⟩ := by
  decide +kernel

theorem context_12_284034_918596 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284034 ⟨918596, by decide⟩ :=
  accepted_of_selected 12 284034 ⟨918596, by decide⟩ ⟨12, 2, 0, 918596, 284034, 1345, 65536⟩
    (by decide) selected_cut_35091

theorem selected_cut_35092 : selected 9 ⟨918624, by decide⟩
    (prefixPartial 12 284035) = some ⟨12, 2, 0, 918624, 284035, 1405, 65536⟩ := by
  decide +kernel

theorem context_12_284035_918624 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284035 ⟨918624, by decide⟩ :=
  accepted_of_selected 12 284035 ⟨918624, by decide⟩ ⟨12, 2, 0, 918624, 284035, 1405, 65536⟩
    (by decide) selected_cut_35092

theorem unmarked_context_11_71008_918625 : frontier 10 ⟨918625, by decide⟩
    (prefixCache 11 71008) (prefixPartial 11 71008) = false := by
  decide +kernel

theorem node_context_11_71008_918625 : EJMOriginalGlobalDAGData.nodes 10 ⟨918625, by decide⟩ =
    .split (coordinate 11) (![⟨918545, by decide⟩,⟨918573, by decide⟩,⟨918596, by decide⟩,⟨918624, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71008_918625 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71008 ⟨918625, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71008
    ⟨918625, by decide⟩ (by decide) (![⟨918545, by decide⟩,⟨918573, by decide⟩,⟨918596, by decide⟩,⟨918624, by decide⟩]) unmarked_context_11_71008_918625 node_context_11_71008_918625
  intro a
  fin_cases a
  · exact context_12_284032_918545
  · exact context_12_284033_918573
  · exact context_12_284034_918596
  · exact context_12_284035_918624

theorem selected_cut_35093 : selected 10 ⟨918732, by decide⟩
    (prefixPartial 11 71009) = some ⟨11, 2, 0, 918732, 71009, 3541, 262144⟩ := by
  decide +kernel

theorem context_11_71009_918732 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71009 ⟨918732, by decide⟩ :=
  accepted_of_selected 11 71009 ⟨918732, by decide⟩ ⟨11, 2, 0, 918732, 71009, 3541, 262144⟩
    (by decide) selected_cut_35093

theorem selected_cut_35094 : selected 9 ⟨918773, by decide⟩
    (prefixPartial 12 284040) = some ⟨12, 2, 0, 918773, 284040, 1065, 65536⟩ := by
  decide +kernel

theorem context_12_284040_918773 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284040 ⟨918773, by decide⟩ :=
  accepted_of_selected 12 284040 ⟨918773, by decide⟩ ⟨12, 2, 0, 918773, 284040, 1065, 65536⟩
    (by decide) selected_cut_35094

theorem selected_cut_35095 : selected 9 ⟨918801, by decide⟩
    (prefixPartial 12 284041) = some ⟨12, 2, 0, 918801, 284041, 981, 65536⟩ := by
  decide +kernel

theorem context_12_284041_918801 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284041 ⟨918801, by decide⟩ :=
  accepted_of_selected 12 284041 ⟨918801, by decide⟩ ⟨12, 2, 0, 918801, 284041, 981, 65536⟩
    (by decide) selected_cut_35095

theorem selected_cut_35096 : selected 9 ⟨918823, by decide⟩
    (prefixPartial 12 284042) = some ⟨12, 2, 0, 918823, 284042, 1045, 65536⟩ := by
  decide +kernel

theorem context_12_284042_918823 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284042 ⟨918823, by decide⟩ :=
  accepted_of_selected 12 284042 ⟨918823, by decide⟩ ⟨12, 2, 0, 918823, 284042, 1045, 65536⟩
    (by decide) selected_cut_35096

theorem selected_cut_35097 : selected 9 ⟨918849, by decide⟩
    (prefixPartial 12 284043) = some ⟨12, 2, 0, 918849, 284043, 1049, 65536⟩ := by
  decide +kernel

theorem context_12_284043_918849 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284043 ⟨918849, by decide⟩ :=
  accepted_of_selected 12 284043 ⟨918849, by decide⟩ ⟨12, 2, 0, 918849, 284043, 1049, 65536⟩
    (by decide) selected_cut_35097

theorem unmarked_context_11_71010_918850 : frontier 10 ⟨918850, by decide⟩
    (prefixCache 11 71010) (prefixPartial 11 71010) = false := by
  decide +kernel

theorem node_context_11_71010_918850 : EJMOriginalGlobalDAGData.nodes 10 ⟨918850, by decide⟩ =
    .split (coordinate 11) (![⟨918773, by decide⟩,⟨918801, by decide⟩,⟨918823, by decide⟩,⟨918849, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71010_918850 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71010 ⟨918850, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71010
    ⟨918850, by decide⟩ (by decide) (![⟨918773, by decide⟩,⟨918801, by decide⟩,⟨918823, by decide⟩,⟨918849, by decide⟩]) unmarked_context_11_71010_918850 node_context_11_71010_918850
  intro a
  fin_cases a
  · exact context_12_284040_918773
  · exact context_12_284041_918801
  · exact context_12_284042_918823
  · exact context_12_284043_918849

theorem selected_cut_35098 : selected 10 ⟨918941, by decide⟩
    (prefixPartial 11 71011) = some ⟨11, 2, 0, 918941, 71011, 3161, 262144⟩ := by
  decide +kernel

theorem context_11_71011_918941 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71011 ⟨918941, by decide⟩ :=
  accepted_of_selected 11 71011 ⟨918941, by decide⟩ ⟨11, 2, 0, 918941, 71011, 3161, 262144⟩
    (by decide) selected_cut_35098

theorem unmarked_context_10_17752_918942 : frontier 11 ⟨918942, by decide⟩
    (prefixCache 10 17752) (prefixPartial 10 17752) = false := by
  decide +kernel

theorem node_context_10_17752_918942 : EJMOriginalGlobalDAGData.nodes 11 ⟨918942, by decide⟩ =
    .split (coordinate 10) (![⟨918625, by decide⟩,⟨918732, by decide⟩,⟨918850, by decide⟩,⟨918941, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17752_918942 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17752 ⟨918942, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17752
    ⟨918942, by decide⟩ (by decide) (![⟨918625, by decide⟩,⟨918732, by decide⟩,⟨918850, by decide⟩,⟨918941, by decide⟩]) unmarked_context_10_17752_918942 node_context_10_17752_918942
  intro a
  fin_cases a
  · exact context_11_71008_918625
  · exact context_11_71009_918732
  · exact context_11_71010_918850
  · exact context_11_71011_918941

theorem selected_cut_35099 : selected 11 ⟨919090, by decide⟩
    (prefixPartial 10 17753) = some ⟨10, 2, 0, 919090, 17753, 3905, 1048576⟩ := by
  decide +kernel

theorem context_10_17753_919090 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17753 ⟨919090, by decide⟩ :=
  accepted_of_selected 10 17753 ⟨919090, by decide⟩ ⟨10, 2, 0, 919090, 17753, 3905, 1048576⟩
    (by decide) selected_cut_35099

theorem selected_cut_35100 : selected 11 ⟨919158, by decide⟩
    (prefixPartial 10 17754) = some ⟨10, 2, 0, 919158, 17754, 1633, 1048576⟩ := by
  decide +kernel

theorem context_10_17754_919158 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17754 ⟨919158, by decide⟩ :=
  accepted_of_selected 10 17754 ⟨919158, by decide⟩ ⟨10, 2, 0, 919158, 17754, 1633, 1048576⟩
    (by decide) selected_cut_35100

theorem selected_cut_35101 : selected 11 ⟨919183, by decide⟩
    (prefixPartial 10 17755) = some ⟨10, 2, 0, 919183, 17755, 417, 1048576⟩ := by
  decide +kernel

theorem context_10_17755_919183 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17755 ⟨919183, by decide⟩ :=
  accepted_of_selected 10 17755 ⟨919183, by decide⟩ ⟨10, 2, 0, 919183, 17755, 417, 1048576⟩
    (by decide) selected_cut_35101

theorem unmarked_context_9_4438_919184 : frontier 12 ⟨919184, by decide⟩
    (prefixCache 9 4438) (prefixPartial 9 4438) = false := by
  decide +kernel

theorem node_context_9_4438_919184 : EJMOriginalGlobalDAGData.nodes 12 ⟨919184, by decide⟩ =
    .split (coordinate 9) (![⟨918942, by decide⟩,⟨919090, by decide⟩,⟨919158, by decide⟩,⟨919183, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4438_919184 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4438 ⟨919184, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4438
    ⟨919184, by decide⟩ (by decide) (![⟨918942, by decide⟩,⟨919090, by decide⟩,⟨919158, by decide⟩,⟨919183, by decide⟩]) unmarked_context_9_4438_919184 node_context_9_4438_919184
  intro a
  fin_cases a
  · exact context_10_17752_918942
  · exact context_10_17753_919090
  · exact context_10_17754_919158
  · exact context_10_17755_919183

theorem selected_cut_35102 : selected 12 ⟨4601, by decide⟩
    (prefixPartial 9 4439) = some ⟨9, 1, 0, 4601, 4439, 1, 4194304⟩ := by
  decide +kernel

theorem context_9_4439_4601 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4439 ⟨4601, by decide⟩ :=
  accepted_of_selected 9 4439 ⟨4601, by decide⟩ ⟨9, 1, 0, 4601, 4439, 1, 4194304⟩
    (by decide) selected_cut_35102

theorem unmarked_context_8_1109_919185 : frontier 13 ⟨919185, by decide⟩
    (prefixCache 8 1109) (prefixPartial 8 1109) = false := by
  decide +kernel

theorem node_context_8_1109_919185 : EJMOriginalGlobalDAGData.nodes 13 ⟨919185, by decide⟩ =
    .split (coordinate 8) (![⟨917891, by decide⟩,⟨918506, by decide⟩,⟨919184, by decide⟩,⟨4601, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1109_919185 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1109 ⟨919185, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1109
    ⟨919185, by decide⟩ (by decide) (![⟨917891, by decide⟩,⟨918506, by decide⟩,⟨919184, by decide⟩,⟨4601, by decide⟩]) unmarked_context_8_1109_919185 node_context_8_1109_919185
  intro a
  fin_cases a
  · exact context_9_4436_917891
  · exact context_9_4437_918506
  · exact context_9_4438_919184
  · exact context_9_4439_4601

theorem selected_cut_35103 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 284160) = some ⟨12, 1, 0, 34034, 284160, 1, 65536⟩ := by
  decide +kernel

theorem context_12_284160_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284160 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 284160 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 284160, 1, 65536⟩
    (by decide) selected_cut_35103

theorem selected_cut_35104 : selected 9 ⟨919249, by decide⟩
    (prefixPartial 12 284161) = some ⟨12, 2, 0, 919249, 284161, 1789, 65536⟩ := by
  decide +kernel

theorem context_12_284161_919249 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284161 ⟨919249, by decide⟩ :=
  accepted_of_selected 12 284161 ⟨919249, by decide⟩ ⟨12, 2, 0, 919249, 284161, 1789, 65536⟩
    (by decide) selected_cut_35104

theorem selected_cut_35105 : selected 9 ⟨919310, by decide⟩
    (prefixPartial 12 284162) = some ⟨12, 2, 0, 919310, 284162, 3257, 65536⟩ := by
  decide +kernel

theorem context_12_284162_919310 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284162 ⟨919310, by decide⟩ :=
  accepted_of_selected 12 284162 ⟨919310, by decide⟩ ⟨12, 2, 0, 919310, 284162, 3257, 65536⟩
    (by decide) selected_cut_35105

theorem selected_cut_35106 : selected 9 ⟨919366, by decide⟩
    (prefixPartial 12 284163) = some ⟨12, 2, 0, 919366, 284163, 3425, 65536⟩ := by
  decide +kernel

theorem context_12_284163_919366 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284163 ⟨919366, by decide⟩ :=
  accepted_of_selected 12 284163 ⟨919366, by decide⟩ ⟨12, 2, 0, 919366, 284163, 3425, 65536⟩
    (by decide) selected_cut_35106

theorem unmarked_context_11_71040_919367 : frontier 10 ⟨919367, by decide⟩
    (prefixCache 11 71040) (prefixPartial 11 71040) = false := by
  decide +kernel

theorem node_context_11_71040_919367 : EJMOriginalGlobalDAGData.nodes 10 ⟨919367, by decide⟩ =
    .split (coordinate 11) (![⟨34034, by decide⟩,⟨919249, by decide⟩,⟨919310, by decide⟩,⟨919366, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71040_919367 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71040 ⟨919367, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71040
    ⟨919367, by decide⟩ (by decide) (![⟨34034, by decide⟩,⟨919249, by decide⟩,⟨919310, by decide⟩,⟨919366, by decide⟩]) unmarked_context_11_71040_919367 node_context_11_71040_919367
  intro a
  fin_cases a
  · exact context_12_284160_34034
  · exact context_12_284161_919249
  · exact context_12_284162_919310
  · exact context_12_284163_919366

theorem selected_cut_35107 : selected 9 ⟨919451, by decide⟩
    (prefixPartial 12 284164) = some ⟨12, 2, 0, 919451, 284164, 3521, 65536⟩ := by
  decide +kernel

theorem context_12_284164_919451 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284164 ⟨919451, by decide⟩ :=
  accepted_of_selected 12 284164 ⟨919451, by decide⟩ ⟨12, 2, 0, 919451, 284164, 3521, 65536⟩
    (by decide) selected_cut_35107

theorem selected_cut_35108 : selected 9 ⟨919497, by decide⟩
    (prefixPartial 12 284165) = some ⟨12, 2, 0, 919497, 284165, 2577, 65536⟩ := by
  decide +kernel

theorem context_12_284165_919497 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284165 ⟨919497, by decide⟩ :=
  accepted_of_selected 12 284165 ⟨919497, by decide⟩ ⟨12, 2, 0, 919497, 284165, 2577, 65536⟩
    (by decide) selected_cut_35108

theorem selected_cut_35109 : selected 9 ⟨919549, by decide⟩
    (prefixPartial 12 284166) = some ⟨12, 2, 0, 919549, 284166, 2965, 65536⟩ := by
  decide +kernel

theorem context_12_284166_919549 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284166 ⟨919549, by decide⟩ :=
  accepted_of_selected 12 284166 ⟨919549, by decide⟩ ⟨12, 2, 0, 919549, 284166, 2965, 65536⟩
    (by decide) selected_cut_35109

theorem selected_cut_35110 : selected 9 ⟨919605, by decide⟩
    (prefixPartial 12 284167) = some ⟨12, 2, 0, 919605, 284167, 3013, 65536⟩ := by
  decide +kernel

theorem context_12_284167_919605 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284167 ⟨919605, by decide⟩ :=
  accepted_of_selected 12 284167 ⟨919605, by decide⟩ ⟨12, 2, 0, 919605, 284167, 3013, 65536⟩
    (by decide) selected_cut_35110

theorem unmarked_context_11_71041_919606 : frontier 10 ⟨919606, by decide⟩
    (prefixCache 11 71041) (prefixPartial 11 71041) = false := by
  decide +kernel

theorem node_context_11_71041_919606 : EJMOriginalGlobalDAGData.nodes 10 ⟨919606, by decide⟩ =
    .split (coordinate 11) (![⟨919451, by decide⟩,⟨919497, by decide⟩,⟨919549, by decide⟩,⟨919605, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71041_919606 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71041 ⟨919606, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71041
    ⟨919606, by decide⟩ (by decide) (![⟨919451, by decide⟩,⟨919497, by decide⟩,⟨919549, by decide⟩,⟨919605, by decide⟩]) unmarked_context_11_71041_919606 node_context_11_71041_919606
  intro a
  fin_cases a
  · exact context_12_284164_919451
  · exact context_12_284165_919497
  · exact context_12_284166_919549
  · exact context_12_284167_919605

theorem selected_cut_35111 : selected 9 ⟨919682, by decide⟩
    (prefixPartial 12 284168) = some ⟨12, 2, 0, 919682, 284168, 3601, 65536⟩ := by
  decide +kernel

theorem context_12_284168_919682 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284168 ⟨919682, by decide⟩ :=
  accepted_of_selected 12 284168 ⟨919682, by decide⟩ ⟨12, 2, 0, 919682, 284168, 3601, 65536⟩
    (by decide) selected_cut_35111

theorem selected_cut_35112 : selected 9 ⟨919716, by decide⟩
    (prefixPartial 12 284169) = some ⟨12, 2, 0, 919716, 284169, 2769, 65536⟩ := by
  decide +kernel

theorem context_12_284169_919716 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284169 ⟨919716, by decide⟩ :=
  accepted_of_selected 12 284169 ⟨919716, by decide⟩ ⟨12, 2, 0, 919716, 284169, 2769, 65536⟩
    (by decide) selected_cut_35112

theorem selected_cut_35113 : selected 9 ⟨893903, by decide⟩
    (prefixPartial 12 284170) = some ⟨12, 1, 0, 893903, 284170, 1, 65536⟩ := by
  decide +kernel

theorem context_12_284170_893903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284170 ⟨893903, by decide⟩ :=
  accepted_of_selected 12 284170 ⟨893903, by decide⟩ ⟨12, 1, 0, 893903, 284170, 1, 65536⟩
    (by decide) selected_cut_35113

theorem selected_cut_35114 : selected 9 ⟨919779, by decide⟩
    (prefixPartial 12 284171) = some ⟨12, 2, 0, 919779, 284171, 3501, 65536⟩ := by
  decide +kernel

theorem context_12_284171_919779 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284171 ⟨919779, by decide⟩ :=
  accepted_of_selected 12 284171 ⟨919779, by decide⟩ ⟨12, 2, 0, 919779, 284171, 3501, 65536⟩
    (by decide) selected_cut_35114

theorem unmarked_context_11_71042_919780 : frontier 10 ⟨919780, by decide⟩
    (prefixCache 11 71042) (prefixPartial 11 71042) = false := by
  decide +kernel

theorem node_context_11_71042_919780 : EJMOriginalGlobalDAGData.nodes 10 ⟨919780, by decide⟩ =
    .split (coordinate 11) (![⟨919682, by decide⟩,⟨919716, by decide⟩,⟨893903, by decide⟩,⟨919779, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71042_919780 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71042 ⟨919780, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71042
    ⟨919780, by decide⟩ (by decide) (![⟨919682, by decide⟩,⟨919716, by decide⟩,⟨893903, by decide⟩,⟨919779, by decide⟩]) unmarked_context_11_71042_919780 node_context_11_71042_919780
  intro a
  fin_cases a
  · exact context_12_284168_919682
  · exact context_12_284169_919716
  · exact context_12_284170_893903
  · exact context_12_284171_919779

theorem selected_cut_35115 : selected 9 ⟨919865, by decide⟩
    (prefixPartial 12 284172) = some ⟨12, 2, 0, 919865, 284172, 3885, 65536⟩ := by
  decide +kernel

theorem context_12_284172_919865 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284172 ⟨919865, by decide⟩ :=
  accepted_of_selected 12 284172 ⟨919865, by decide⟩ ⟨12, 2, 0, 919865, 284172, 3885, 65536⟩
    (by decide) selected_cut_35115

theorem selected_cut_35116 : selected 9 ⟨919912, by decide⟩
    (prefixPartial 12 284173) = some ⟨12, 2, 0, 919912, 284173, 2857, 65536⟩ := by
  decide +kernel

theorem context_12_284173_919912 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284173 ⟨919912, by decide⟩ :=
  accepted_of_selected 12 284173 ⟨919912, by decide⟩ ⟨12, 2, 0, 919912, 284173, 2857, 65536⟩
    (by decide) selected_cut_35116

theorem selected_cut_35117 : selected 9 ⟨919985, by decide⟩
    (prefixPartial 12 284174) = some ⟨12, 2, 0, 919985, 284174, 3521, 65536⟩ := by
  decide +kernel

theorem context_12_284174_919985 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284174 ⟨919985, by decide⟩ :=
  accepted_of_selected 12 284174 ⟨919985, by decide⟩ ⟨12, 2, 0, 919985, 284174, 3521, 65536⟩
    (by decide) selected_cut_35117

theorem selected_cut_35118 : selected 9 ⟨920049, by decide⟩
    (prefixPartial 12 284175) = some ⟨12, 2, 0, 920049, 284175, 3365, 65536⟩ := by
  decide +kernel

theorem context_12_284175_920049 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284175 ⟨920049, by decide⟩ :=
  accepted_of_selected 12 284175 ⟨920049, by decide⟩ ⟨12, 2, 0, 920049, 284175, 3365, 65536⟩
    (by decide) selected_cut_35118

theorem unmarked_context_11_71043_920050 : frontier 10 ⟨920050, by decide⟩
    (prefixCache 11 71043) (prefixPartial 11 71043) = false := by
  decide +kernel

theorem node_context_11_71043_920050 : EJMOriginalGlobalDAGData.nodes 10 ⟨920050, by decide⟩ =
    .split (coordinate 11) (![⟨919865, by decide⟩,⟨919912, by decide⟩,⟨919985, by decide⟩,⟨920049, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71043_920050 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71043 ⟨920050, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71043
    ⟨920050, by decide⟩ (by decide) (![⟨919865, by decide⟩,⟨919912, by decide⟩,⟨919985, by decide⟩,⟨920049, by decide⟩]) unmarked_context_11_71043_920050 node_context_11_71043_920050
  intro a
  fin_cases a
  · exact context_12_284172_919865
  · exact context_12_284173_919912
  · exact context_12_284174_919985
  · exact context_12_284175_920049

theorem unmarked_context_10_17760_920051 : frontier 11 ⟨920051, by decide⟩
    (prefixCache 10 17760) (prefixPartial 10 17760) = false := by
  decide +kernel

theorem node_context_10_17760_920051 : EJMOriginalGlobalDAGData.nodes 11 ⟨920051, by decide⟩ =
    .split (coordinate 10) (![⟨919367, by decide⟩,⟨919606, by decide⟩,⟨919780, by decide⟩,⟨920050, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17760_920051 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17760 ⟨920051, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17760
    ⟨920051, by decide⟩ (by decide) (![⟨919367, by decide⟩,⟨919606, by decide⟩,⟨919780, by decide⟩,⟨920050, by decide⟩]) unmarked_context_10_17760_920051 node_context_10_17760_920051
  intro a
  fin_cases a
  · exact context_11_71040_919367
  · exact context_11_71041_919606
  · exact context_11_71042_919780
  · exact context_11_71043_920050

theorem selected_cut_35119 : selected 9 ⟨920100, by decide⟩
    (prefixPartial 12 284176) = some ⟨12, 2, 0, 920100, 284176, 2897, 65536⟩ := by
  decide +kernel

theorem context_12_284176_920100 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284176 ⟨920100, by decide⟩ :=
  accepted_of_selected 12 284176 ⟨920100, by decide⟩ ⟨12, 2, 0, 920100, 284176, 2897, 65536⟩
    (by decide) selected_cut_35119

theorem selected_cut_35120 : selected 9 ⟨920149, by decide⟩
    (prefixPartial 12 284177) = some ⟨12, 2, 0, 920149, 284177, 2277, 65536⟩ := by
  decide +kernel

theorem context_12_284177_920149 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284177 ⟨920149, by decide⟩ :=
  accepted_of_selected 12 284177 ⟨920149, by decide⟩ ⟨12, 2, 0, 920149, 284177, 2277, 65536⟩
    (by decide) selected_cut_35120

theorem selected_cut_35121 : selected 9 ⟨920193, by decide⟩
    (prefixPartial 12 284178) = some ⟨12, 2, 0, 920193, 284178, 2701, 65536⟩ := by
  decide +kernel

theorem context_12_284178_920193 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284178 ⟨920193, by decide⟩ :=
  accepted_of_selected 12 284178 ⟨920193, by decide⟩ ⟨12, 2, 0, 920193, 284178, 2701, 65536⟩
    (by decide) selected_cut_35121

theorem selected_cut_35122 : selected 9 ⟨920244, by decide⟩
    (prefixPartial 12 284179) = some ⟨12, 2, 0, 920244, 284179, 3073, 65536⟩ := by
  decide +kernel

theorem context_12_284179_920244 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284179 ⟨920244, by decide⟩ :=
  accepted_of_selected 12 284179 ⟨920244, by decide⟩ ⟨12, 2, 0, 920244, 284179, 3073, 65536⟩
    (by decide) selected_cut_35122

theorem unmarked_context_11_71044_920245 : frontier 10 ⟨920245, by decide⟩
    (prefixCache 11 71044) (prefixPartial 11 71044) = false := by
  decide +kernel

theorem node_context_11_71044_920245 : EJMOriginalGlobalDAGData.nodes 10 ⟨920245, by decide⟩ =
    .split (coordinate 11) (![⟨920100, by decide⟩,⟨920149, by decide⟩,⟨920193, by decide⟩,⟨920244, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71044_920245 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71044 ⟨920245, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71044
    ⟨920245, by decide⟩ (by decide) (![⟨920100, by decide⟩,⟨920149, by decide⟩,⟨920193, by decide⟩,⟨920244, by decide⟩]) unmarked_context_11_71044_920245 node_context_11_71044_920245
  intro a
  fin_cases a
  · exact context_12_284176_920100
  · exact context_12_284177_920149
  · exact context_12_284178_920193
  · exact context_12_284179_920244

theorem selected_cut_35123 : selected 10 ⟨892405, by decide⟩
    (prefixPartial 11 71045) = some ⟨11, 1, 0, 892405, 71045, 1, 262144⟩ := by
  decide +kernel

theorem context_11_71045_892405 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71045 ⟨892405, by decide⟩ :=
  accepted_of_selected 11 71045 ⟨892405, by decide⟩ ⟨11, 1, 0, 892405, 71045, 1, 262144⟩
    (by decide) selected_cut_35123

theorem selected_cut_35124 : selected 9 ⟨920283, by decide⟩
    (prefixPartial 12 284184) = some ⟨12, 2, 0, 920283, 284184, 2977, 65536⟩ := by
  decide +kernel

theorem context_12_284184_920283 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284184 ⟨920283, by decide⟩ :=
  accepted_of_selected 12 284184 ⟨920283, by decide⟩ ⟨12, 2, 0, 920283, 284184, 2977, 65536⟩
    (by decide) selected_cut_35124

theorem selected_cut_35125 : selected 9 ⟨920320, by decide⟩
    (prefixPartial 12 284185) = some ⟨12, 2, 0, 920320, 284185, 2345, 65536⟩ := by
  decide +kernel

theorem context_12_284185_920320 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284185 ⟨920320, by decide⟩ :=
  accepted_of_selected 12 284185 ⟨920320, by decide⟩ ⟨12, 2, 0, 920320, 284185, 2345, 65536⟩
    (by decide) selected_cut_35125

theorem selected_cut_35126 : selected 9 ⟨893903, by decide⟩
    (prefixPartial 12 284186) = some ⟨12, 1, 0, 893903, 284186, 1, 65536⟩ := by
  decide +kernel

theorem context_12_284186_893903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284186 ⟨893903, by decide⟩ :=
  accepted_of_selected 12 284186 ⟨893903, by decide⟩ ⟨12, 1, 0, 893903, 284186, 1, 65536⟩
    (by decide) selected_cut_35126

theorem selected_cut_35127 : selected 9 ⟨920373, by decide⟩
    (prefixPartial 12 284187) = some ⟨12, 2, 0, 920373, 284187, 3161, 65536⟩ := by
  decide +kernel

theorem context_12_284187_920373 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284187 ⟨920373, by decide⟩ :=
  accepted_of_selected 12 284187 ⟨920373, by decide⟩ ⟨12, 2, 0, 920373, 284187, 3161, 65536⟩
    (by decide) selected_cut_35127

theorem unmarked_context_11_71046_920374 : frontier 10 ⟨920374, by decide⟩
    (prefixCache 11 71046) (prefixPartial 11 71046) = false := by
  decide +kernel

theorem node_context_11_71046_920374 : EJMOriginalGlobalDAGData.nodes 10 ⟨920374, by decide⟩ =
    .split (coordinate 11) (![⟨920283, by decide⟩,⟨920320, by decide⟩,⟨893903, by decide⟩,⟨920373, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71046_920374 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71046 ⟨920374, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71046
    ⟨920374, by decide⟩ (by decide) (![⟨920283, by decide⟩,⟨920320, by decide⟩,⟨893903, by decide⟩,⟨920373, by decide⟩]) unmarked_context_11_71046_920374 node_context_11_71046_920374
  intro a
  fin_cases a
  · exact context_12_284184_920283
  · exact context_12_284185_920320
  · exact context_12_284186_893903
  · exact context_12_284187_920373

theorem selected_cut_35128 : selected 9 ⟨920424, by decide⟩
    (prefixPartial 12 284188) = some ⟨12, 2, 0, 920424, 284188, 3201, 65536⟩ := by
  decide +kernel

theorem context_12_284188_920424 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284188 ⟨920424, by decide⟩ :=
  accepted_of_selected 12 284188 ⟨920424, by decide⟩ ⟨12, 2, 0, 920424, 284188, 3201, 65536⟩
    (by decide) selected_cut_35128

theorem selected_cut_35129 : selected 9 ⟨920460, by decide⟩
    (prefixPartial 12 284189) = some ⟨12, 2, 0, 920460, 284189, 2393, 65536⟩ := by
  decide +kernel

theorem context_12_284189_920460 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284189 ⟨920460, by decide⟩ :=
  accepted_of_selected 12 284189 ⟨920460, by decide⟩ ⟨12, 2, 0, 920460, 284189, 2393, 65536⟩
    (by decide) selected_cut_35129

theorem selected_cut_35130 : selected 9 ⟨920503, by decide⟩
    (prefixPartial 12 284190) = some ⟨12, 2, 0, 920503, 284190, 2941, 65536⟩ := by
  decide +kernel

theorem context_12_284190_920503 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284190 ⟨920503, by decide⟩ :=
  accepted_of_selected 12 284190 ⟨920503, by decide⟩ ⟨12, 2, 0, 920503, 284190, 2941, 65536⟩
    (by decide) selected_cut_35130

theorem selected_cut_35131 : selected 9 ⟨920556, by decide⟩
    (prefixPartial 12 284191) = some ⟨12, 2, 0, 920556, 284191, 3021, 65536⟩ := by
  decide +kernel

theorem context_12_284191_920556 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284191 ⟨920556, by decide⟩ :=
  accepted_of_selected 12 284191 ⟨920556, by decide⟩ ⟨12, 2, 0, 920556, 284191, 3021, 65536⟩
    (by decide) selected_cut_35131

theorem unmarked_context_11_71047_920557 : frontier 10 ⟨920557, by decide⟩
    (prefixCache 11 71047) (prefixPartial 11 71047) = false := by
  decide +kernel

theorem node_context_11_71047_920557 : EJMOriginalGlobalDAGData.nodes 10 ⟨920557, by decide⟩ =
    .split (coordinate 11) (![⟨920424, by decide⟩,⟨920460, by decide⟩,⟨920503, by decide⟩,⟨920556, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71047_920557 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71047 ⟨920557, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71047
    ⟨920557, by decide⟩ (by decide) (![⟨920424, by decide⟩,⟨920460, by decide⟩,⟨920503, by decide⟩,⟨920556, by decide⟩]) unmarked_context_11_71047_920557 node_context_11_71047_920557
  intro a
  fin_cases a
  · exact context_12_284188_920424
  · exact context_12_284189_920460
  · exact context_12_284190_920503
  · exact context_12_284191_920556

theorem unmarked_context_10_17761_920558 : frontier 11 ⟨920558, by decide⟩
    (prefixCache 10 17761) (prefixPartial 10 17761) = false := by
  decide +kernel

theorem node_context_10_17761_920558 : EJMOriginalGlobalDAGData.nodes 11 ⟨920558, by decide⟩ =
    .split (coordinate 10) (![⟨920245, by decide⟩,⟨892405, by decide⟩,⟨920374, by decide⟩,⟨920557, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17761_920558 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17761 ⟨920558, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17761
    ⟨920558, by decide⟩ (by decide) (![⟨920245, by decide⟩,⟨892405, by decide⟩,⟨920374, by decide⟩,⟨920557, by decide⟩]) unmarked_context_10_17761_920558 node_context_10_17761_920558
  intro a
  fin_cases a
  · exact context_11_71044_920245
  · exact context_11_71045_892405
  · exact context_11_71046_920374
  · exact context_11_71047_920557

theorem selected_cut_35132 : selected 9 ⟨920602, by decide⟩
    (prefixPartial 12 284192) = some ⟨12, 2, 0, 920602, 284192, 2841, 65536⟩ := by
  decide +kernel

theorem context_12_284192_920602 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284192 ⟨920602, by decide⟩ :=
  accepted_of_selected 12 284192 ⟨920602, by decide⟩ ⟨12, 2, 0, 920602, 284192, 2841, 65536⟩
    (by decide) selected_cut_35132

theorem selected_cut_35133 : selected 9 ⟨920636, by decide⟩
    (prefixPartial 12 284193) = some ⟨12, 2, 0, 920636, 284193, 2533, 65536⟩ := by
  decide +kernel

theorem context_12_284193_920636 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284193 ⟨920636, by decide⟩ :=
  accepted_of_selected 12 284193 ⟨920636, by decide⟩ ⟨12, 2, 0, 920636, 284193, 2533, 65536⟩
    (by decide) selected_cut_35133

theorem selected_cut_35134 : selected 9 ⟨920698, by decide⟩
    (prefixPartial 12 284194) = some ⟨12, 2, 0, 920698, 284194, 3073, 65536⟩ := by
  decide +kernel

theorem context_12_284194_920698 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284194 ⟨920698, by decide⟩ :=
  accepted_of_selected 12 284194 ⟨920698, by decide⟩ ⟨12, 2, 0, 920698, 284194, 3073, 65536⟩
    (by decide) selected_cut_35134

theorem selected_cut_35135 : selected 9 ⟨920755, by decide⟩
    (prefixPartial 12 284195) = some ⟨12, 2, 0, 920755, 284195, 3013, 65536⟩ := by
  decide +kernel

theorem context_12_284195_920755 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284195 ⟨920755, by decide⟩ :=
  accepted_of_selected 12 284195 ⟨920755, by decide⟩ ⟨12, 2, 0, 920755, 284195, 3013, 65536⟩
    (by decide) selected_cut_35135

theorem unmarked_context_11_71048_920756 : frontier 10 ⟨920756, by decide⟩
    (prefixCache 11 71048) (prefixPartial 11 71048) = false := by
  decide +kernel

theorem node_context_11_71048_920756 : EJMOriginalGlobalDAGData.nodes 10 ⟨920756, by decide⟩ =
    .split (coordinate 11) (![⟨920602, by decide⟩,⟨920636, by decide⟩,⟨920698, by decide⟩,⟨920755, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71048_920756 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71048 ⟨920756, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71048
    ⟨920756, by decide⟩ (by decide) (![⟨920602, by decide⟩,⟨920636, by decide⟩,⟨920698, by decide⟩,⟨920755, by decide⟩]) unmarked_context_11_71048_920756 node_context_11_71048_920756
  intro a
  fin_cases a
  · exact context_12_284192_920602
  · exact context_12_284193_920636
  · exact context_12_284194_920698
  · exact context_12_284195_920755

theorem selected_cut_35136 : selected 9 ⟨920797, by decide⟩
    (prefixPartial 12 284196) = some ⟨12, 2, 0, 920797, 284196, 2661, 65536⟩ := by
  decide +kernel

theorem context_12_284196_920797 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284196 ⟨920797, by decide⟩ :=
  accepted_of_selected 12 284196 ⟨920797, by decide⟩ ⟨12, 2, 0, 920797, 284196, 2661, 65536⟩
    (by decide) selected_cut_35136

theorem selected_cut_35137 : selected 9 ⟨920829, by decide⟩
    (prefixPartial 12 284197) = some ⟨12, 2, 0, 920829, 284197, 2173, 65536⟩ := by
  decide +kernel

theorem context_12_284197_920829 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284197 ⟨920829, by decide⟩ :=
  accepted_of_selected 12 284197 ⟨920829, by decide⟩ ⟨12, 2, 0, 920829, 284197, 2173, 65536⟩
    (by decide) selected_cut_35137

theorem selected_cut_35138 : selected 9 ⟨920874, by decide⟩
    (prefixPartial 12 284198) = some ⟨12, 2, 0, 920874, 284198, 2657, 65536⟩ := by
  decide +kernel

theorem context_12_284198_920874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284198 ⟨920874, by decide⟩ :=
  accepted_of_selected 12 284198 ⟨920874, by decide⟩ ⟨12, 2, 0, 920874, 284198, 2657, 65536⟩
    (by decide) selected_cut_35138

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
