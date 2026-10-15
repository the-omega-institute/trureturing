/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover363
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_34947 : selected 9 ⟨914333, by decide⟩
    (prefixPartial 12 283182) = some ⟨12, 2, 0, 914333, 283182, 3865, 65536⟩ := by
  decide +kernel

theorem context_12_283182_914333 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283182 ⟨914333, by decide⟩ :=
  accepted_of_selected 12 283182 ⟨914333, by decide⟩ ⟨12, 2, 0, 914333, 283182, 3865, 65536⟩
    (by decide) selected_cut_34947

theorem selected_cut_34948 : selected 9 ⟨914392, by decide⟩
    (prefixPartial 12 283183) = some ⟨12, 2, 0, 914392, 283183, 3345, 65536⟩ := by
  decide +kernel

theorem context_12_283183_914392 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283183 ⟨914392, by decide⟩ :=
  accepted_of_selected 12 283183 ⟨914392, by decide⟩ ⟨12, 2, 0, 914392, 283183, 3345, 65536⟩
    (by decide) selected_cut_34948

theorem unmarked_context_11_70795_914393 : frontier 10 ⟨914393, by decide⟩
    (prefixCache 11 70795) (prefixPartial 11 70795) = false := by
  decide +kernel

theorem node_context_11_70795_914393 : EJMOriginalGlobalDAGData.nodes 10 ⟨914393, by decide⟩ =
    .split (coordinate 11) (![⟨914189, by decide⟩,⟨914255, by decide⟩,⟨914333, by decide⟩,⟨914392, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_70795_914393 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70795 ⟨914393, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 70795
    ⟨914393, by decide⟩ (by decide) (![⟨914189, by decide⟩,⟨914255, by decide⟩,⟨914333, by decide⟩,⟨914392, by decide⟩]) unmarked_context_11_70795_914393 node_context_11_70795_914393
  intro a
  fin_cases a
  · exact context_12_283180_914189
  · exact context_12_283181_914255
  · exact context_12_283182_914333
  · exact context_12_283183_914392

theorem unmarked_context_10_17698_914394 : frontier 11 ⟨914394, by decide⟩
    (prefixCache 10 17698) (prefixPartial 10 17698) = false := by
  decide +kernel

theorem node_context_10_17698_914394 : EJMOriginalGlobalDAGData.nodes 11 ⟨914394, by decide⟩ =
    .split (coordinate 10) (![⟨913704, by decide⟩,⟨913908, by decide⟩,⟨914115, by decide⟩,⟨914393, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17698_914394 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17698 ⟨914394, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17698
    ⟨914394, by decide⟩ (by decide) (![⟨913704, by decide⟩,⟨913908, by decide⟩,⟨914115, by decide⟩,⟨914393, by decide⟩]) unmarked_context_10_17698_914394 node_context_10_17698_914394
  intro a
  fin_cases a
  · exact context_11_70792_913704
  · exact context_11_70793_913908
  · exact context_11_70794_914115
  · exact context_11_70795_914393

theorem selected_cut_34949 : selected 9 ⟨914438, by decide⟩
    (prefixPartial 12 283184) = some ⟨12, 2, 0, 914438, 283184, 2465, 65536⟩ := by
  decide +kernel

theorem context_12_283184_914438 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283184 ⟨914438, by decide⟩ :=
  accepted_of_selected 12 283184 ⟨914438, by decide⟩ ⟨12, 2, 0, 914438, 283184, 2465, 65536⟩
    (by decide) selected_cut_34949

theorem selected_cut_34950 : selected 9 ⟨914476, by decide⟩
    (prefixPartial 12 283185) = some ⟨12, 2, 0, 914476, 283185, 2433, 65536⟩ := by
  decide +kernel

theorem context_12_283185_914476 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283185 ⟨914476, by decide⟩ :=
  accepted_of_selected 12 283185 ⟨914476, by decide⟩ ⟨12, 2, 0, 914476, 283185, 2433, 65536⟩
    (by decide) selected_cut_34950

theorem selected_cut_34951 : selected 9 ⟨914515, by decide⟩
    (prefixPartial 12 283186) = some ⟨12, 2, 0, 914515, 283186, 2249, 65536⟩ := by
  decide +kernel

theorem context_12_283186_914515 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283186 ⟨914515, by decide⟩ :=
  accepted_of_selected 12 283186 ⟨914515, by decide⟩ ⟨12, 2, 0, 914515, 283186, 2249, 65536⟩
    (by decide) selected_cut_34951

theorem selected_cut_34952 : selected 9 ⟨914570, by decide⟩
    (prefixPartial 12 283187) = some ⟨12, 2, 0, 914570, 283187, 2701, 65536⟩ := by
  decide +kernel

theorem context_12_283187_914570 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283187 ⟨914570, by decide⟩ :=
  accepted_of_selected 12 283187 ⟨914570, by decide⟩ ⟨12, 2, 0, 914570, 283187, 2701, 65536⟩
    (by decide) selected_cut_34952

theorem unmarked_context_11_70796_914571 : frontier 10 ⟨914571, by decide⟩
    (prefixCache 11 70796) (prefixPartial 11 70796) = false := by
  decide +kernel

theorem node_context_11_70796_914571 : EJMOriginalGlobalDAGData.nodes 10 ⟨914571, by decide⟩ =
    .split (coordinate 11) (![⟨914438, by decide⟩,⟨914476, by decide⟩,⟨914515, by decide⟩,⟨914570, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_70796_914571 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70796 ⟨914571, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 70796
    ⟨914571, by decide⟩ (by decide) (![⟨914438, by decide⟩,⟨914476, by decide⟩,⟨914515, by decide⟩,⟨914570, by decide⟩]) unmarked_context_11_70796_914571 node_context_11_70796_914571
  intro a
  fin_cases a
  · exact context_12_283184_914438
  · exact context_12_283185_914476
  · exact context_12_283186_914515
  · exact context_12_283187_914570

theorem selected_cut_34953 : selected 9 ⟨914608, by decide⟩
    (prefixPartial 12 283188) = some ⟨12, 2, 0, 914608, 283188, 2413, 65536⟩ := by
  decide +kernel

theorem context_12_283188_914608 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283188 ⟨914608, by decide⟩ :=
  accepted_of_selected 12 283188 ⟨914608, by decide⟩ ⟨12, 2, 0, 914608, 283188, 2413, 65536⟩
    (by decide) selected_cut_34953

theorem selected_cut_34954 : selected 9 ⟨914645, by decide⟩
    (prefixPartial 12 283189) = some ⟨12, 2, 0, 914645, 283189, 2225, 65536⟩ := by
  decide +kernel

theorem context_12_283189_914645 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283189 ⟨914645, by decide⟩ :=
  accepted_of_selected 12 283189 ⟨914645, by decide⟩ ⟨12, 2, 0, 914645, 283189, 2225, 65536⟩
    (by decide) selected_cut_34954

theorem selected_cut_34955 : selected 9 ⟨914677, by decide⟩
    (prefixPartial 12 283190) = some ⟨12, 2, 0, 914677, 283190, 2121, 65536⟩ := by
  decide +kernel

theorem context_12_283190_914677 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283190 ⟨914677, by decide⟩ :=
  accepted_of_selected 12 283190 ⟨914677, by decide⟩ ⟨12, 2, 0, 914677, 283190, 2121, 65536⟩
    (by decide) selected_cut_34955

theorem selected_cut_34956 : selected 9 ⟨914719, by decide⟩
    (prefixPartial 12 283191) = some ⟨12, 2, 0, 914719, 283191, 2549, 65536⟩ := by
  decide +kernel

theorem context_12_283191_914719 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283191 ⟨914719, by decide⟩ :=
  accepted_of_selected 12 283191 ⟨914719, by decide⟩ ⟨12, 2, 0, 914719, 283191, 2549, 65536⟩
    (by decide) selected_cut_34956

theorem unmarked_context_11_70797_914720 : frontier 10 ⟨914720, by decide⟩
    (prefixCache 11 70797) (prefixPartial 11 70797) = false := by
  decide +kernel

theorem node_context_11_70797_914720 : EJMOriginalGlobalDAGData.nodes 10 ⟨914720, by decide⟩ =
    .split (coordinate 11) (![⟨914608, by decide⟩,⟨914645, by decide⟩,⟨914677, by decide⟩,⟨914719, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_70797_914720 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70797 ⟨914720, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 70797
    ⟨914720, by decide⟩ (by decide) (![⟨914608, by decide⟩,⟨914645, by decide⟩,⟨914677, by decide⟩,⟨914719, by decide⟩]) unmarked_context_11_70797_914720 node_context_11_70797_914720
  intro a
  fin_cases a
  · exact context_12_283188_914608
  · exact context_12_283189_914645
  · exact context_12_283190_914677
  · exact context_12_283191_914719

theorem selected_cut_34957 : selected 9 ⟨914766, by decide⟩
    (prefixPartial 12 283192) = some ⟨12, 2, 0, 914766, 283192, 2765, 65536⟩ := by
  decide +kernel

theorem context_12_283192_914766 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283192 ⟨914766, by decide⟩ :=
  accepted_of_selected 12 283192 ⟨914766, by decide⟩ ⟨12, 2, 0, 914766, 283192, 2765, 65536⟩
    (by decide) selected_cut_34957

theorem selected_cut_34958 : selected 9 ⟨914820, by decide⟩
    (prefixPartial 12 283193) = some ⟨12, 2, 0, 914820, 283193, 2861, 65536⟩ := by
  decide +kernel

theorem context_12_283193_914820 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283193 ⟨914820, by decide⟩ :=
  accepted_of_selected 12 283193 ⟨914820, by decide⟩ ⟨12, 2, 0, 914820, 283193, 2861, 65536⟩
    (by decide) selected_cut_34958

theorem selected_cut_34959 : selected 9 ⟨893903, by decide⟩
    (prefixPartial 12 283194) = some ⟨12, 1, 0, 893903, 283194, 1, 65536⟩ := by
  decide +kernel

theorem context_12_283194_893903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283194 ⟨893903, by decide⟩ :=
  accepted_of_selected 12 283194 ⟨893903, by decide⟩ ⟨12, 1, 0, 893903, 283194, 1, 65536⟩
    (by decide) selected_cut_34959

theorem selected_cut_34960 : selected 9 ⟨914881, by decide⟩
    (prefixPartial 12 283195) = some ⟨12, 2, 0, 914881, 283195, 3141, 65536⟩ := by
  decide +kernel

theorem context_12_283195_914881 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283195 ⟨914881, by decide⟩ :=
  accepted_of_selected 12 283195 ⟨914881, by decide⟩ ⟨12, 2, 0, 914881, 283195, 3141, 65536⟩
    (by decide) selected_cut_34960

theorem unmarked_context_11_70798_914882 : frontier 10 ⟨914882, by decide⟩
    (prefixCache 11 70798) (prefixPartial 11 70798) = false := by
  decide +kernel

theorem node_context_11_70798_914882 : EJMOriginalGlobalDAGData.nodes 10 ⟨914882, by decide⟩ =
    .split (coordinate 11) (![⟨914766, by decide⟩,⟨914820, by decide⟩,⟨893903, by decide⟩,⟨914881, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_70798_914882 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70798 ⟨914882, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 70798
    ⟨914882, by decide⟩ (by decide) (![⟨914766, by decide⟩,⟨914820, by decide⟩,⟨893903, by decide⟩,⟨914881, by decide⟩]) unmarked_context_11_70798_914882 node_context_11_70798_914882
  intro a
  fin_cases a
  · exact context_12_283192_914766
  · exact context_12_283193_914820
  · exact context_12_283194_893903
  · exact context_12_283195_914881

theorem selected_cut_34961 : selected 9 ⟨914929, by decide⟩
    (prefixPartial 12 283196) = some ⟨12, 2, 0, 914929, 283196, 2641, 65536⟩ := by
  decide +kernel

theorem context_12_283196_914929 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283196 ⟨914929, by decide⟩ :=
  accepted_of_selected 12 283196 ⟨914929, by decide⟩ ⟨12, 2, 0, 914929, 283196, 2641, 65536⟩
    (by decide) selected_cut_34961

theorem selected_cut_34962 : selected 9 ⟨914981, by decide⟩
    (prefixPartial 12 283197) = some ⟨12, 2, 0, 914981, 283197, 2633, 65536⟩ := by
  decide +kernel

theorem context_12_283197_914981 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283197 ⟨914981, by decide⟩ :=
  accepted_of_selected 12 283197 ⟨914981, by decide⟩ ⟨12, 2, 0, 914981, 283197, 2633, 65536⟩
    (by decide) selected_cut_34962

theorem selected_cut_34963 : selected 9 ⟨915025, by decide⟩
    (prefixPartial 12 283198) = some ⟨12, 2, 0, 915025, 283198, 2549, 65536⟩ := by
  decide +kernel

theorem context_12_283198_915025 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283198 ⟨915025, by decide⟩ :=
  accepted_of_selected 12 283198 ⟨915025, by decide⟩ ⟨12, 2, 0, 915025, 283198, 2549, 65536⟩
    (by decide) selected_cut_34963

theorem selected_cut_34964 : selected 9 ⟨915073, by decide⟩
    (prefixPartial 12 283199) = some ⟨12, 2, 0, 915073, 283199, 2641, 65536⟩ := by
  decide +kernel

theorem context_12_283199_915073 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283199 ⟨915073, by decide⟩ :=
  accepted_of_selected 12 283199 ⟨915073, by decide⟩ ⟨12, 2, 0, 915073, 283199, 2641, 65536⟩
    (by decide) selected_cut_34964

theorem unmarked_context_11_70799_915074 : frontier 10 ⟨915074, by decide⟩
    (prefixCache 11 70799) (prefixPartial 11 70799) = false := by
  decide +kernel

theorem node_context_11_70799_915074 : EJMOriginalGlobalDAGData.nodes 10 ⟨915074, by decide⟩ =
    .split (coordinate 11) (![⟨914929, by decide⟩,⟨914981, by decide⟩,⟨915025, by decide⟩,⟨915073, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_70799_915074 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70799 ⟨915074, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 70799
    ⟨915074, by decide⟩ (by decide) (![⟨914929, by decide⟩,⟨914981, by decide⟩,⟨915025, by decide⟩,⟨915073, by decide⟩]) unmarked_context_11_70799_915074 node_context_11_70799_915074
  intro a
  fin_cases a
  · exact context_12_283196_914929
  · exact context_12_283197_914981
  · exact context_12_283198_915025
  · exact context_12_283199_915073

theorem unmarked_context_10_17699_915075 : frontier 11 ⟨915075, by decide⟩
    (prefixCache 10 17699) (prefixPartial 10 17699) = false := by
  decide +kernel

theorem node_context_10_17699_915075 : EJMOriginalGlobalDAGData.nodes 11 ⟨915075, by decide⟩ =
    .split (coordinate 10) (![⟨914571, by decide⟩,⟨914720, by decide⟩,⟨914882, by decide⟩,⟨915074, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17699_915075 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17699 ⟨915075, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17699
    ⟨915075, by decide⟩ (by decide) (![⟨914571, by decide⟩,⟨914720, by decide⟩,⟨914882, by decide⟩,⟨915074, by decide⟩]) unmarked_context_10_17699_915075 node_context_10_17699_915075
  intro a
  fin_cases a
  · exact context_11_70796_914571
  · exact context_11_70797_914720
  · exact context_11_70798_914882
  · exact context_11_70799_915074

theorem unmarked_context_9_4424_915076 : frontier 12 ⟨915076, by decide⟩
    (prefixCache 9 4424) (prefixPartial 9 4424) = false := by
  decide +kernel

theorem node_context_9_4424_915076 : EJMOriginalGlobalDAGData.nodes 12 ⟨915076, by decide⟩ =
    .split (coordinate 9) (![⟨912531, by decide⟩,⟨913473, by decide⟩,⟨914394, by decide⟩,⟨915075, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4424_915076 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4424 ⟨915076, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4424
    ⟨915076, by decide⟩ (by decide) (![⟨912531, by decide⟩,⟨913473, by decide⟩,⟨914394, by decide⟩,⟨915075, by decide⟩]) unmarked_context_9_4424_915076 node_context_9_4424_915076
  intro a
  fin_cases a
  · exact context_10_17696_912531
  · exact context_10_17697_913473
  · exact context_10_17698_914394
  · exact context_10_17699_915075

theorem selected_cut_34965 : selected 10 ⟨907917, by decide⟩
    (prefixPartial 11 70800) = some ⟨11, 1, 0, 907917, 70800, 1, 262144⟩ := by
  decide +kernel

theorem context_11_70800_907917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70800 ⟨907917, by decide⟩ :=
  accepted_of_selected 11 70800 ⟨907917, by decide⟩ ⟨11, 1, 0, 907917, 70800, 1, 262144⟩
    (by decide) selected_cut_34965

theorem selected_cut_34966 : selected 9 ⟨915098, by decide⟩
    (prefixPartial 12 283204) = some ⟨12, 2, 0, 915098, 283204, 1833, 65536⟩ := by
  decide +kernel

theorem context_12_283204_915098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283204 ⟨915098, by decide⟩ :=
  accepted_of_selected 12 283204 ⟨915098, by decide⟩ ⟨12, 2, 0, 915098, 283204, 1833, 65536⟩
    (by decide) selected_cut_34966

theorem selected_cut_34967 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 283205) = some ⟨12, 1, 0, 896706, 283205, 1, 65536⟩ := by
  decide +kernel

theorem context_12_283205_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283205 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 283205 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 283205, 1, 65536⟩
    (by decide) selected_cut_34967

theorem selected_cut_34968 : selected 9 ⟨915124, by decide⟩
    (prefixPartial 12 283206) = some ⟨12, 2, 0, 915124, 283206, 1609, 65536⟩ := by
  decide +kernel

theorem context_12_283206_915124 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283206 ⟨915124, by decide⟩ :=
  accepted_of_selected 12 283206 ⟨915124, by decide⟩ ⟨12, 2, 0, 915124, 283206, 1609, 65536⟩
    (by decide) selected_cut_34968

theorem selected_cut_34969 : selected 9 ⟨915148, by decide⟩
    (prefixPartial 12 283207) = some ⟨12, 2, 0, 915148, 283207, 1665, 65536⟩ := by
  decide +kernel

theorem context_12_283207_915148 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283207 ⟨915148, by decide⟩ :=
  accepted_of_selected 12 283207 ⟨915148, by decide⟩ ⟨12, 2, 0, 915148, 283207, 1665, 65536⟩
    (by decide) selected_cut_34969

theorem unmarked_context_11_70801_915149 : frontier 10 ⟨915149, by decide⟩
    (prefixCache 11 70801) (prefixPartial 11 70801) = false := by
  decide +kernel

theorem node_context_11_70801_915149 : EJMOriginalGlobalDAGData.nodes 10 ⟨915149, by decide⟩ =
    .split (coordinate 11) (![⟨915098, by decide⟩,⟨896706, by decide⟩,⟨915124, by decide⟩,⟨915148, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_70801_915149 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70801 ⟨915149, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 70801
    ⟨915149, by decide⟩ (by decide) (![⟨915098, by decide⟩,⟨896706, by decide⟩,⟨915124, by decide⟩,⟨915148, by decide⟩]) unmarked_context_11_70801_915149 node_context_11_70801_915149
  intro a
  fin_cases a
  · exact context_12_283204_915098
  · exact context_12_283205_896706
  · exact context_12_283206_915124
  · exact context_12_283207_915148

theorem selected_cut_34970 : selected 9 ⟨915178, by decide⟩
    (prefixPartial 12 283208) = some ⟨12, 2, 0, 915178, 283208, 2073, 65536⟩ := by
  decide +kernel

theorem context_12_283208_915178 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283208 ⟨915178, by decide⟩ :=
  accepted_of_selected 12 283208 ⟨915178, by decide⟩ ⟨12, 2, 0, 915178, 283208, 2073, 65536⟩
    (by decide) selected_cut_34970

theorem selected_cut_34971 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 283209) = some ⟨12, 1, 0, 896706, 283209, 1, 65536⟩ := by
  decide +kernel

theorem context_12_283209_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283209 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 283209 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 283209, 1, 65536⟩
    (by decide) selected_cut_34971

theorem selected_cut_34972 : selected 9 ⟨893903, by decide⟩
    (prefixPartial 12 283210) = some ⟨12, 1, 0, 893903, 283210, 1, 65536⟩ := by
  decide +kernel

theorem context_12_283210_893903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283210 ⟨893903, by decide⟩ :=
  accepted_of_selected 12 283210 ⟨893903, by decide⟩ ⟨12, 1, 0, 893903, 283210, 1, 65536⟩
    (by decide) selected_cut_34972

theorem selected_cut_34973 : selected 9 ⟨915211, by decide⟩
    (prefixPartial 12 283211) = some ⟨12, 2, 0, 915211, 283211, 2101, 65536⟩ := by
  decide +kernel

theorem context_12_283211_915211 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283211 ⟨915211, by decide⟩ :=
  accepted_of_selected 12 283211 ⟨915211, by decide⟩ ⟨12, 2, 0, 915211, 283211, 2101, 65536⟩
    (by decide) selected_cut_34973

theorem unmarked_context_11_70802_915212 : frontier 10 ⟨915212, by decide⟩
    (prefixCache 11 70802) (prefixPartial 11 70802) = false := by
  decide +kernel

theorem node_context_11_70802_915212 : EJMOriginalGlobalDAGData.nodes 10 ⟨915212, by decide⟩ =
    .split (coordinate 11) (![⟨915178, by decide⟩,⟨896706, by decide⟩,⟨893903, by decide⟩,⟨915211, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_70802_915212 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70802 ⟨915212, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 70802
    ⟨915212, by decide⟩ (by decide) (![⟨915178, by decide⟩,⟨896706, by decide⟩,⟨893903, by decide⟩,⟨915211, by decide⟩]) unmarked_context_11_70802_915212 node_context_11_70802_915212
  intro a
  fin_cases a
  · exact context_12_283208_915178
  · exact context_12_283209_896706
  · exact context_12_283210_893903
  · exact context_12_283211_915211

theorem selected_cut_34974 : selected 9 ⟨915249, by decide⟩
    (prefixPartial 12 283212) = some ⟨12, 2, 0, 915249, 283212, 2185, 65536⟩ := by
  decide +kernel

theorem context_12_283212_915249 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283212 ⟨915249, by decide⟩ :=
  accepted_of_selected 12 283212 ⟨915249, by decide⟩ ⟨12, 2, 0, 915249, 283212, 2185, 65536⟩
    (by decide) selected_cut_34974

theorem selected_cut_34975 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 283213) = some ⟨12, 1, 0, 896706, 283213, 1, 65536⟩ := by
  decide +kernel

theorem context_12_283213_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283213 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 283213 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 283213, 1, 65536⟩
    (by decide) selected_cut_34975

theorem selected_cut_34976 : selected 9 ⟨915282, by decide⟩
    (prefixPartial 12 283214) = some ⟨12, 2, 0, 915282, 283214, 2073, 65536⟩ := by
  decide +kernel

theorem context_12_283214_915282 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283214 ⟨915282, by decide⟩ :=
  accepted_of_selected 12 283214 ⟨915282, by decide⟩ ⟨12, 2, 0, 915282, 283214, 2073, 65536⟩
    (by decide) selected_cut_34976

theorem selected_cut_34977 : selected 9 ⟨915310, by decide⟩
    (prefixPartial 12 283215) = some ⟨12, 2, 0, 915310, 283215, 1957, 65536⟩ := by
  decide +kernel

theorem context_12_283215_915310 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283215 ⟨915310, by decide⟩ :=
  accepted_of_selected 12 283215 ⟨915310, by decide⟩ ⟨12, 2, 0, 915310, 283215, 1957, 65536⟩
    (by decide) selected_cut_34977

theorem unmarked_context_11_70803_915311 : frontier 10 ⟨915311, by decide⟩
    (prefixCache 11 70803) (prefixPartial 11 70803) = false := by
  decide +kernel

theorem node_context_11_70803_915311 : EJMOriginalGlobalDAGData.nodes 10 ⟨915311, by decide⟩ =
    .split (coordinate 11) (![⟨915249, by decide⟩,⟨896706, by decide⟩,⟨915282, by decide⟩,⟨915310, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_70803_915311 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70803 ⟨915311, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 70803
    ⟨915311, by decide⟩ (by decide) (![⟨915249, by decide⟩,⟨896706, by decide⟩,⟨915282, by decide⟩,⟨915310, by decide⟩]) unmarked_context_11_70803_915311 node_context_11_70803_915311
  intro a
  fin_cases a
  · exact context_12_283212_915249
  · exact context_12_283213_896706
  · exact context_12_283214_915282
  · exact context_12_283215_915310

theorem unmarked_context_10_17700_915312 : frontier 11 ⟨915312, by decide⟩
    (prefixCache 10 17700) (prefixPartial 10 17700) = false := by
  decide +kernel

theorem node_context_10_17700_915312 : EJMOriginalGlobalDAGData.nodes 11 ⟨915312, by decide⟩ =
    .split (coordinate 10) (![⟨907917, by decide⟩,⟨915149, by decide⟩,⟨915212, by decide⟩,⟨915311, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17700_915312 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17700 ⟨915312, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17700
    ⟨915312, by decide⟩ (by decide) (![⟨907917, by decide⟩,⟨915149, by decide⟩,⟨915212, by decide⟩,⟨915311, by decide⟩]) unmarked_context_10_17700_915312 node_context_10_17700_915312
  intro a
  fin_cases a
  · exact context_11_70800_907917
  · exact context_11_70801_915149
  · exact context_11_70802_915212
  · exact context_11_70803_915311

theorem selected_cut_34978 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 17701) = some ⟨10, 1, 0, 893098, 17701, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_17701_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17701 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 17701 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 17701, 1, 1048576⟩
    (by decide) selected_cut_34978

theorem selected_cut_34979 : selected 9 ⟨915335, by decide⟩
    (prefixPartial 12 283232) = some ⟨12, 2, 0, 915335, 283232, 1617, 65536⟩ := by
  decide +kernel

theorem context_12_283232_915335 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283232 ⟨915335, by decide⟩ :=
  accepted_of_selected 12 283232 ⟨915335, by decide⟩ ⟨12, 2, 0, 915335, 283232, 1617, 65536⟩
    (by decide) selected_cut_34979

theorem selected_cut_34980 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 283233) = some ⟨12, 1, 0, 896706, 283233, 1, 65536⟩ := by
  decide +kernel

theorem context_12_283233_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283233 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 283233 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 283233, 1, 65536⟩
    (by decide) selected_cut_34980

theorem selected_cut_34981 : selected 9 ⟨915361, by decide⟩
    (prefixPartial 12 283234) = some ⟨12, 2, 0, 915361, 283234, 1757, 65536⟩ := by
  decide +kernel

theorem context_12_283234_915361 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283234 ⟨915361, by decide⟩ :=
  accepted_of_selected 12 283234 ⟨915361, by decide⟩ ⟨12, 2, 0, 915361, 283234, 1757, 65536⟩
    (by decide) selected_cut_34981

theorem selected_cut_34982 : selected 9 ⟨915390, by decide⟩
    (prefixPartial 12 283235) = some ⟨12, 2, 0, 915390, 283235, 1773, 65536⟩ := by
  decide +kernel

theorem context_12_283235_915390 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283235 ⟨915390, by decide⟩ :=
  accepted_of_selected 12 283235 ⟨915390, by decide⟩ ⟨12, 2, 0, 915390, 283235, 1773, 65536⟩
    (by decide) selected_cut_34982

theorem unmarked_context_11_70808_915391 : frontier 10 ⟨915391, by decide⟩
    (prefixCache 11 70808) (prefixPartial 11 70808) = false := by
  decide +kernel

theorem node_context_11_70808_915391 : EJMOriginalGlobalDAGData.nodes 10 ⟨915391, by decide⟩ =
    .split (coordinate 11) (![⟨915335, by decide⟩,⟨896706, by decide⟩,⟨915361, by decide⟩,⟨915390, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_70808_915391 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70808 ⟨915391, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 70808
    ⟨915391, by decide⟩ (by decide) (![⟨915335, by decide⟩,⟨896706, by decide⟩,⟨915361, by decide⟩,⟨915390, by decide⟩]) unmarked_context_11_70808_915391 node_context_11_70808_915391
  intro a
  fin_cases a
  · exact context_12_283232_915335
  · exact context_12_283233_896706
  · exact context_12_283234_915361
  · exact context_12_283235_915390

theorem selected_cut_34983 : selected 9 ⟨915408, by decide⟩
    (prefixPartial 12 283236) = some ⟨12, 2, 0, 915408, 283236, 1493, 65536⟩ := by
  decide +kernel

theorem context_12_283236_915408 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283236 ⟨915408, by decide⟩ :=
  accepted_of_selected 12 283236 ⟨915408, by decide⟩ ⟨12, 2, 0, 915408, 283236, 1493, 65536⟩
    (by decide) selected_cut_34983

theorem selected_cut_34984 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 283237) = some ⟨12, 1, 0, 896706, 283237, 1, 65536⟩ := by
  decide +kernel

theorem context_12_283237_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283237 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 283237 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 283237, 1, 65536⟩
    (by decide) selected_cut_34984

theorem selected_cut_34985 : selected 9 ⟨915431, by decide⟩
    (prefixPartial 12 283238) = some ⟨12, 2, 0, 915431, 283238, 1573, 65536⟩ := by
  decide +kernel

theorem context_12_283238_915431 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283238 ⟨915431, by decide⟩ :=
  accepted_of_selected 12 283238 ⟨915431, by decide⟩ ⟨12, 2, 0, 915431, 283238, 1573, 65536⟩
    (by decide) selected_cut_34985

theorem selected_cut_34986 : selected 9 ⟨915451, by decide⟩
    (prefixPartial 12 283239) = some ⟨12, 2, 0, 915451, 283239, 1521, 65536⟩ := by
  decide +kernel

theorem context_12_283239_915451 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283239 ⟨915451, by decide⟩ :=
  accepted_of_selected 12 283239 ⟨915451, by decide⟩ ⟨12, 2, 0, 915451, 283239, 1521, 65536⟩
    (by decide) selected_cut_34986

theorem unmarked_context_11_70809_915452 : frontier 10 ⟨915452, by decide⟩
    (prefixCache 11 70809) (prefixPartial 11 70809) = false := by
  decide +kernel

theorem node_context_11_70809_915452 : EJMOriginalGlobalDAGData.nodes 10 ⟨915452, by decide⟩ =
    .split (coordinate 11) (![⟨915408, by decide⟩,⟨896706, by decide⟩,⟨915431, by decide⟩,⟨915451, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_70809_915452 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70809 ⟨915452, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 70809
    ⟨915452, by decide⟩ (by decide) (![⟨915408, by decide⟩,⟨896706, by decide⟩,⟨915431, by decide⟩,⟨915451, by decide⟩]) unmarked_context_11_70809_915452 node_context_11_70809_915452
  intro a
  fin_cases a
  · exact context_12_283236_915408
  · exact context_12_283237_896706
  · exact context_12_283238_915431
  · exact context_12_283239_915451

theorem selected_cut_34987 : selected 10 ⟨915512, by decide⟩
    (prefixPartial 11 70810) = some ⟨11, 2, 0, 915512, 70810, 3649, 262144⟩ := by
  decide +kernel

theorem context_11_70810_915512 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70810 ⟨915512, by decide⟩ :=
  accepted_of_selected 11 70810 ⟨915512, by decide⟩ ⟨11, 2, 0, 915512, 70810, 3649, 262144⟩
    (by decide) selected_cut_34987

theorem selected_cut_34988 : selected 9 ⟨915534, by decide⟩
    (prefixPartial 12 283244) = some ⟨12, 2, 0, 915534, 283244, 1781, 65536⟩ := by
  decide +kernel

theorem context_12_283244_915534 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283244 ⟨915534, by decide⟩ :=
  accepted_of_selected 12 283244 ⟨915534, by decide⟩ ⟨12, 2, 0, 915534, 283244, 1781, 65536⟩
    (by decide) selected_cut_34988

theorem selected_cut_34989 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 283245) = some ⟨12, 1, 0, 896706, 283245, 1, 65536⟩ := by
  decide +kernel

theorem context_12_283245_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283245 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 283245 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 283245, 1, 65536⟩
    (by decide) selected_cut_34989

theorem selected_cut_34990 : selected 9 ⟨915570, by decide⟩
    (prefixPartial 12 283246) = some ⟨12, 2, 0, 915570, 283246, 2041, 65536⟩ := by
  decide +kernel

theorem context_12_283246_915570 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283246 ⟨915570, by decide⟩ :=
  accepted_of_selected 12 283246 ⟨915570, by decide⟩ ⟨12, 2, 0, 915570, 283246, 2041, 65536⟩
    (by decide) selected_cut_34990

theorem selected_cut_34991 : selected 9 ⟨915595, by decide⟩
    (prefixPartial 12 283247) = some ⟨12, 2, 0, 915595, 283247, 1785, 65536⟩ := by
  decide +kernel

theorem context_12_283247_915595 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283247 ⟨915595, by decide⟩ :=
  accepted_of_selected 12 283247 ⟨915595, by decide⟩ ⟨12, 2, 0, 915595, 283247, 1785, 65536⟩
    (by decide) selected_cut_34991

theorem unmarked_context_11_70811_915596 : frontier 10 ⟨915596, by decide⟩
    (prefixCache 11 70811) (prefixPartial 11 70811) = false := by
  decide +kernel

theorem node_context_11_70811_915596 : EJMOriginalGlobalDAGData.nodes 10 ⟨915596, by decide⟩ =
    .split (coordinate 11) (![⟨915534, by decide⟩,⟨896706, by decide⟩,⟨915570, by decide⟩,⟨915595, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_70811_915596 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70811 ⟨915596, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 70811
    ⟨915596, by decide⟩ (by decide) (![⟨915534, by decide⟩,⟨896706, by decide⟩,⟨915570, by decide⟩,⟨915595, by decide⟩]) unmarked_context_11_70811_915596 node_context_11_70811_915596
  intro a
  fin_cases a
  · exact context_12_283244_915534
  · exact context_12_283245_896706
  · exact context_12_283246_915570
  · exact context_12_283247_915595

theorem unmarked_context_10_17702_915597 : frontier 11 ⟨915597, by decide⟩
    (prefixCache 10 17702) (prefixPartial 10 17702) = false := by
  decide +kernel

theorem node_context_10_17702_915597 : EJMOriginalGlobalDAGData.nodes 11 ⟨915597, by decide⟩ =
    .split (coordinate 10) (![⟨915391, by decide⟩,⟨915452, by decide⟩,⟨915512, by decide⟩,⟨915596, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17702_915597 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17702 ⟨915597, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17702
    ⟨915597, by decide⟩ (by decide) (![⟨915391, by decide⟩,⟨915452, by decide⟩,⟨915512, by decide⟩,⟨915596, by decide⟩]) unmarked_context_10_17702_915597 node_context_10_17702_915597
  intro a
  fin_cases a
  · exact context_11_70808_915391
  · exact context_11_70809_915452
  · exact context_11_70810_915512
  · exact context_11_70811_915596

theorem selected_cut_34992 : selected 9 ⟨915615, by decide⟩
    (prefixPartial 12 283248) = some ⟨12, 2, 0, 915615, 283248, 1361, 65536⟩ := by
  decide +kernel

theorem context_12_283248_915615 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283248 ⟨915615, by decide⟩ :=
  accepted_of_selected 12 283248 ⟨915615, by decide⟩ ⟨12, 2, 0, 915615, 283248, 1361, 65536⟩
    (by decide) selected_cut_34992

theorem selected_cut_34993 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 283249) = some ⟨12, 1, 0, 896706, 283249, 1, 65536⟩ := by
  decide +kernel

theorem context_12_283249_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283249 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 283249 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 283249, 1, 65536⟩
    (by decide) selected_cut_34993

theorem selected_cut_34994 : selected 9 ⟨915630, by decide⟩
    (prefixPartial 12 283250) = some ⟨12, 2, 0, 915630, 283250, 1345, 65536⟩ := by
  decide +kernel

theorem context_12_283250_915630 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283250 ⟨915630, by decide⟩ :=
  accepted_of_selected 12 283250 ⟨915630, by decide⟩ ⟨12, 2, 0, 915630, 283250, 1345, 65536⟩
    (by decide) selected_cut_34994

theorem selected_cut_34995 : selected 9 ⟨915655, by decide⟩
    (prefixPartial 12 283251) = some ⟨12, 2, 0, 915655, 283251, 1633, 65536⟩ := by
  decide +kernel

theorem context_12_283251_915655 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283251 ⟨915655, by decide⟩ :=
  accepted_of_selected 12 283251 ⟨915655, by decide⟩ ⟨12, 2, 0, 915655, 283251, 1633, 65536⟩
    (by decide) selected_cut_34995

theorem unmarked_context_11_70812_915656 : frontier 10 ⟨915656, by decide⟩
    (prefixCache 11 70812) (prefixPartial 11 70812) = false := by
  decide +kernel

theorem node_context_11_70812_915656 : EJMOriginalGlobalDAGData.nodes 10 ⟨915656, by decide⟩ =
    .split (coordinate 11) (![⟨915615, by decide⟩,⟨896706, by decide⟩,⟨915630, by decide⟩,⟨915655, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_70812_915656 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70812 ⟨915656, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 70812
    ⟨915656, by decide⟩ (by decide) (![⟨915615, by decide⟩,⟨896706, by decide⟩,⟨915630, by decide⟩,⟨915655, by decide⟩]) unmarked_context_11_70812_915656 node_context_11_70812_915656
  intro a
  fin_cases a
  · exact context_12_283248_915615
  · exact context_12_283249_896706
  · exact context_12_283250_915630
  · exact context_12_283251_915655

theorem selected_cut_34996 : selected 10 ⟨915705, by decide⟩
    (prefixPartial 11 70813) = some ⟨11, 2, 0, 915705, 70813, 3993, 262144⟩ := by
  decide +kernel

theorem context_11_70813_915705 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70813 ⟨915705, by decide⟩ :=
  accepted_of_selected 11 70813 ⟨915705, by decide⟩ ⟨11, 2, 0, 915705, 70813, 3993, 262144⟩
    (by decide) selected_cut_34996

theorem selected_cut_34997 : selected 10 ⟨915764, by decide⟩
    (prefixPartial 11 70814) = some ⟨11, 2, 0, 915764, 70814, 3489, 262144⟩ := by
  decide +kernel

theorem context_11_70814_915764 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70814 ⟨915764, by decide⟩ :=
  accepted_of_selected 11 70814 ⟨915764, by decide⟩ ⟨11, 2, 0, 915764, 70814, 3489, 262144⟩
    (by decide) selected_cut_34997

theorem selected_cut_34998 : selected 9 ⟨915779, by decide⟩
    (prefixPartial 12 283260) = some ⟨12, 2, 0, 915779, 283260, 1397, 65536⟩ := by
  decide +kernel

theorem context_12_283260_915779 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283260 ⟨915779, by decide⟩ :=
  accepted_of_selected 12 283260 ⟨915779, by decide⟩ ⟨12, 2, 0, 915779, 283260, 1397, 65536⟩
    (by decide) selected_cut_34998

theorem selected_cut_34999 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 283261) = some ⟨12, 1, 0, 896706, 283261, 1, 65536⟩ := by
  decide +kernel

theorem context_12_283261_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283261 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 283261 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 283261, 1, 65536⟩
    (by decide) selected_cut_34999

theorem selected_cut_35000 : selected 9 ⟨915799, by decide⟩
    (prefixPartial 12 283262) = some ⟨12, 2, 0, 915799, 283262, 1461, 65536⟩ := by
  decide +kernel

theorem context_12_283262_915799 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283262 ⟨915799, by decide⟩ :=
  accepted_of_selected 12 283262 ⟨915799, by decide⟩ ⟨12, 2, 0, 915799, 283262, 1461, 65536⟩
    (by decide) selected_cut_35000

theorem selected_cut_35001 : selected 9 ⟨915824, by decide⟩
    (prefixPartial 12 283263) = some ⟨12, 2, 0, 915824, 283263, 1545, 65536⟩ := by
  decide +kernel

theorem context_12_283263_915824 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283263 ⟨915824, by decide⟩ :=
  accepted_of_selected 12 283263 ⟨915824, by decide⟩ ⟨12, 2, 0, 915824, 283263, 1545, 65536⟩
    (by decide) selected_cut_35001

theorem unmarked_context_11_70815_915825 : frontier 10 ⟨915825, by decide⟩
    (prefixCache 11 70815) (prefixPartial 11 70815) = false := by
  decide +kernel

theorem node_context_11_70815_915825 : EJMOriginalGlobalDAGData.nodes 10 ⟨915825, by decide⟩ =
    .split (coordinate 11) (![⟨915779, by decide⟩,⟨896706, by decide⟩,⟨915799, by decide⟩,⟨915824, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_70815_915825 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70815 ⟨915825, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 70815
    ⟨915825, by decide⟩ (by decide) (![⟨915779, by decide⟩,⟨896706, by decide⟩,⟨915799, by decide⟩,⟨915824, by decide⟩]) unmarked_context_11_70815_915825 node_context_11_70815_915825
  intro a
  fin_cases a
  · exact context_12_283260_915779
  · exact context_12_283261_896706
  · exact context_12_283262_915799
  · exact context_12_283263_915824

theorem unmarked_context_10_17703_915826 : frontier 11 ⟨915826, by decide⟩
    (prefixCache 10 17703) (prefixPartial 10 17703) = false := by
  decide +kernel

theorem node_context_10_17703_915826 : EJMOriginalGlobalDAGData.nodes 11 ⟨915826, by decide⟩ =
    .split (coordinate 10) (![⟨915656, by decide⟩,⟨915705, by decide⟩,⟨915764, by decide⟩,⟨915825, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17703_915826 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17703 ⟨915826, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17703
    ⟨915826, by decide⟩ (by decide) (![⟨915656, by decide⟩,⟨915705, by decide⟩,⟨915764, by decide⟩,⟨915825, by decide⟩]) unmarked_context_10_17703_915826 node_context_10_17703_915826
  intro a
  fin_cases a
  · exact context_11_70812_915656
  · exact context_11_70813_915705
  · exact context_11_70814_915764
  · exact context_11_70815_915825

theorem unmarked_context_9_4425_915827 : frontier 12 ⟨915827, by decide⟩
    (prefixCache 9 4425) (prefixPartial 9 4425) = false := by
  decide +kernel

theorem node_context_9_4425_915827 : EJMOriginalGlobalDAGData.nodes 12 ⟨915827, by decide⟩ =
    .split (coordinate 9) (![⟨915312, by decide⟩,⟨893098, by decide⟩,⟨915597, by decide⟩,⟨915826, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4425_915827 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4425 ⟨915827, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4425
    ⟨915827, by decide⟩ (by decide) (![⟨915312, by decide⟩,⟨893098, by decide⟩,⟨915597, by decide⟩,⟨915826, by decide⟩]) unmarked_context_9_4425_915827 node_context_9_4425_915827
  intro a
  fin_cases a
  · exact context_10_17700_915312
  · exact context_10_17701_893098
  · exact context_10_17702_915597
  · exact context_10_17703_915826

theorem selected_cut_35002 : selected 10 ⟨907917, by decide⟩
    (prefixPartial 11 70816) = some ⟨11, 1, 0, 907917, 70816, 1, 262144⟩ := by
  decide +kernel

theorem context_11_70816_907917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70816 ⟨907917, by decide⟩ :=
  accepted_of_selected 11 70816 ⟨907917, by decide⟩ ⟨11, 1, 0, 907917, 70816, 1, 262144⟩
    (by decide) selected_cut_35002

theorem selected_cut_35003 : selected 9 ⟨915851, by decide⟩
    (prefixPartial 12 283268) = some ⟨12, 2, 0, 915851, 283268, 1493, 65536⟩ := by
  decide +kernel

theorem context_12_283268_915851 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283268 ⟨915851, by decide⟩ :=
  accepted_of_selected 12 283268 ⟨915851, by decide⟩ ⟨12, 2, 0, 915851, 283268, 1493, 65536⟩
    (by decide) selected_cut_35003

theorem selected_cut_35004 : selected 9 ⟨915870, by decide⟩
    (prefixPartial 12 283269) = some ⟨12, 2, 0, 915870, 283269, 1317, 65536⟩ := by
  decide +kernel

theorem context_12_283269_915870 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283269 ⟨915870, by decide⟩ :=
  accepted_of_selected 12 283269 ⟨915870, by decide⟩ ⟨12, 2, 0, 915870, 283269, 1317, 65536⟩
    (by decide) selected_cut_35004

theorem selected_cut_35005 : selected 9 ⟨915887, by decide⟩
    (prefixPartial 12 283270) = some ⟨12, 2, 0, 915887, 283270, 1285, 65536⟩ := by
  decide +kernel

theorem context_12_283270_915887 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283270 ⟨915887, by decide⟩ :=
  accepted_of_selected 12 283270 ⟨915887, by decide⟩ ⟨12, 2, 0, 915887, 283270, 1285, 65536⟩
    (by decide) selected_cut_35005

theorem selected_cut_35006 : selected 9 ⟨915906, by decide⟩
    (prefixPartial 12 283271) = some ⟨12, 2, 0, 915906, 283271, 1353, 65536⟩ := by
  decide +kernel

theorem context_12_283271_915906 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283271 ⟨915906, by decide⟩ :=
  accepted_of_selected 12 283271 ⟨915906, by decide⟩ ⟨12, 2, 0, 915906, 283271, 1353, 65536⟩
    (by decide) selected_cut_35006

theorem unmarked_context_11_70817_915907 : frontier 10 ⟨915907, by decide⟩
    (prefixCache 11 70817) (prefixPartial 11 70817) = false := by
  decide +kernel

theorem node_context_11_70817_915907 : EJMOriginalGlobalDAGData.nodes 10 ⟨915907, by decide⟩ =
    .split (coordinate 11) (![⟨915851, by decide⟩,⟨915870, by decide⟩,⟨915887, by decide⟩,⟨915906, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_70817_915907 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70817 ⟨915907, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 70817
    ⟨915907, by decide⟩ (by decide) (![⟨915851, by decide⟩,⟨915870, by decide⟩,⟨915887, by decide⟩,⟨915906, by decide⟩]) unmarked_context_11_70817_915907 node_context_11_70817_915907
  intro a
  fin_cases a
  · exact context_12_283268_915851
  · exact context_12_283269_915870
  · exact context_12_283270_915887
  · exact context_12_283271_915906

theorem selected_cut_35007 : selected 9 ⟨915940, by decide⟩
    (prefixPartial 12 283272) = some ⟨12, 2, 0, 915940, 283272, 1757, 65536⟩ := by
  decide +kernel

theorem context_12_283272_915940 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283272 ⟨915940, by decide⟩ :=
  accepted_of_selected 12 283272 ⟨915940, by decide⟩ ⟨12, 2, 0, 915940, 283272, 1757, 65536⟩
    (by decide) selected_cut_35007

theorem selected_cut_35008 : selected 9 ⟨915970, by decide⟩
    (prefixPartial 12 283273) = some ⟨12, 2, 0, 915970, 283273, 1613, 65536⟩ := by
  decide +kernel

theorem context_12_283273_915970 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283273 ⟨915970, by decide⟩ :=
  accepted_of_selected 12 283273 ⟨915970, by decide⟩ ⟨12, 2, 0, 915970, 283273, 1613, 65536⟩
    (by decide) selected_cut_35008

theorem selected_cut_35009 : selected 9 ⟨893903, by decide⟩
    (prefixPartial 12 283274) = some ⟨12, 1, 0, 893903, 283274, 1, 65536⟩ := by
  decide +kernel

theorem context_12_283274_893903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283274 ⟨893903, by decide⟩ :=
  accepted_of_selected 12 283274 ⟨893903, by decide⟩ ⟨12, 1, 0, 893903, 283274, 1, 65536⟩
    (by decide) selected_cut_35009

theorem selected_cut_35010 : selected 9 ⟨915994, by decide⟩
    (prefixPartial 12 283275) = some ⟨12, 2, 0, 915994, 283275, 1669, 65536⟩ := by
  decide +kernel

theorem context_12_283275_915994 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283275 ⟨915994, by decide⟩ :=
  accepted_of_selected 12 283275 ⟨915994, by decide⟩ ⟨12, 2, 0, 915994, 283275, 1669, 65536⟩
    (by decide) selected_cut_35010

theorem unmarked_context_11_70818_915995 : frontier 10 ⟨915995, by decide⟩
    (prefixCache 11 70818) (prefixPartial 11 70818) = false := by
  decide +kernel

theorem node_context_11_70818_915995 : EJMOriginalGlobalDAGData.nodes 10 ⟨915995, by decide⟩ =
    .split (coordinate 11) (![⟨915940, by decide⟩,⟨915970, by decide⟩,⟨893903, by decide⟩,⟨915994, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_70818_915995 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70818 ⟨915995, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 70818
    ⟨915995, by decide⟩ (by decide) (![⟨915940, by decide⟩,⟨915970, by decide⟩,⟨893903, by decide⟩,⟨915994, by decide⟩]) unmarked_context_11_70818_915995 node_context_11_70818_915995
  intro a
  fin_cases a
  · exact context_12_283272_915940
  · exact context_12_283273_915970
  · exact context_12_283274_893903
  · exact context_12_283275_915994

theorem selected_cut_35011 : selected 9 ⟨916019, by decide⟩
    (prefixPartial 12 283276) = some ⟨12, 2, 0, 916019, 283276, 1589, 65536⟩ := by
  decide +kernel

theorem context_12_283276_916019 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283276 ⟨916019, by decide⟩ :=
  accepted_of_selected 12 283276 ⟨916019, by decide⟩ ⟨12, 2, 0, 916019, 283276, 1589, 65536⟩
    (by decide) selected_cut_35011

theorem selected_cut_35012 : selected 9 ⟨916039, by decide⟩
    (prefixPartial 12 283277) = some ⟨12, 2, 0, 916039, 283277, 1429, 65536⟩ := by
  decide +kernel

theorem context_12_283277_916039 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283277 ⟨916039, by decide⟩ :=
  accepted_of_selected 12 283277 ⟨916039, by decide⟩ ⟨12, 2, 0, 916039, 283277, 1429, 65536⟩
    (by decide) selected_cut_35012

theorem selected_cut_35013 : selected 9 ⟨916057, by decide⟩
    (prefixPartial 12 283278) = some ⟨12, 2, 0, 916057, 283278, 1313, 65536⟩ := by
  decide +kernel

theorem context_12_283278_916057 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283278 ⟨916057, by decide⟩ :=
  accepted_of_selected 12 283278 ⟨916057, by decide⟩ ⟨12, 2, 0, 916057, 283278, 1313, 65536⟩
    (by decide) selected_cut_35013

theorem selected_cut_35014 : selected 9 ⟨916075, by decide⟩
    (prefixPartial 12 283279) = some ⟨12, 2, 0, 916075, 283279, 1457, 65536⟩ := by
  decide +kernel

theorem context_12_283279_916075 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283279 ⟨916075, by decide⟩ :=
  accepted_of_selected 12 283279 ⟨916075, by decide⟩ ⟨12, 2, 0, 916075, 283279, 1457, 65536⟩
    (by decide) selected_cut_35014

theorem unmarked_context_11_70819_916076 : frontier 10 ⟨916076, by decide⟩
    (prefixCache 11 70819) (prefixPartial 11 70819) = false := by
  decide +kernel

theorem node_context_11_70819_916076 : EJMOriginalGlobalDAGData.nodes 10 ⟨916076, by decide⟩ =
    .split (coordinate 11) (![⟨916019, by decide⟩,⟨916039, by decide⟩,⟨916057, by decide⟩,⟨916075, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_70819_916076 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70819 ⟨916076, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 70819
    ⟨916076, by decide⟩ (by decide) (![⟨916019, by decide⟩,⟨916039, by decide⟩,⟨916057, by decide⟩,⟨916075, by decide⟩]) unmarked_context_11_70819_916076 node_context_11_70819_916076
  intro a
  fin_cases a
  · exact context_12_283276_916019
  · exact context_12_283277_916039
  · exact context_12_283278_916057
  · exact context_12_283279_916075

theorem unmarked_context_10_17704_916077 : frontier 11 ⟨916077, by decide⟩
    (prefixCache 10 17704) (prefixPartial 10 17704) = false := by
  decide +kernel

theorem node_context_10_17704_916077 : EJMOriginalGlobalDAGData.nodes 11 ⟨916077, by decide⟩ =
    .split (coordinate 10) (![⟨907917, by decide⟩,⟨915907, by decide⟩,⟨915995, by decide⟩,⟨916076, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17704_916077 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17704 ⟨916077, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17704
    ⟨916077, by decide⟩ (by decide) (![⟨907917, by decide⟩,⟨915907, by decide⟩,⟨915995, by decide⟩,⟨916076, by decide⟩]) unmarked_context_10_17704_916077 node_context_10_17704_916077
  intro a
  fin_cases a
  · exact context_11_70816_907917
  · exact context_11_70817_915907
  · exact context_11_70818_915995
  · exact context_11_70819_916076

theorem selected_cut_35015 : selected 9 ⟨916095, by decide⟩
    (prefixPartial 12 283280) = some ⟨12, 2, 0, 916095, 283280, 1221, 65536⟩ := by
  decide +kernel

theorem context_12_283280_916095 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283280 ⟨916095, by decide⟩ :=
  accepted_of_selected 12 283280 ⟨916095, by decide⟩ ⟨12, 2, 0, 916095, 283280, 1221, 65536⟩
    (by decide) selected_cut_35015

theorem selected_cut_35016 : selected 9 ⟨916114, by decide⟩
    (prefixPartial 12 283281) = some ⟨12, 2, 0, 916114, 283281, 1257, 65536⟩ := by
  decide +kernel

theorem context_12_283281_916114 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283281 ⟨916114, by decide⟩ :=
  accepted_of_selected 12 283281 ⟨916114, by decide⟩ ⟨12, 2, 0, 916114, 283281, 1257, 65536⟩
    (by decide) selected_cut_35016

theorem selected_cut_35017 : selected 9 ⟨916128, by decide⟩
    (prefixPartial 12 283282) = some ⟨12, 2, 0, 916128, 283282, 1129, 65536⟩ := by
  decide +kernel

theorem context_12_283282_916128 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283282 ⟨916128, by decide⟩ :=
  accepted_of_selected 12 283282 ⟨916128, by decide⟩ ⟨12, 2, 0, 916128, 283282, 1129, 65536⟩
    (by decide) selected_cut_35017

theorem selected_cut_35018 : selected 9 ⟨916145, by decide⟩
    (prefixPartial 12 283283) = some ⟨12, 2, 0, 916145, 283283, 1365, 65536⟩ := by
  decide +kernel

theorem context_12_283283_916145 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283283 ⟨916145, by decide⟩ :=
  accepted_of_selected 12 283283 ⟨916145, by decide⟩ ⟨12, 2, 0, 916145, 283283, 1365, 65536⟩
    (by decide) selected_cut_35018

theorem unmarked_context_11_70820_916146 : frontier 10 ⟨916146, by decide⟩
    (prefixCache 11 70820) (prefixPartial 11 70820) = false := by
  decide +kernel

theorem node_context_11_70820_916146 : EJMOriginalGlobalDAGData.nodes 10 ⟨916146, by decide⟩ =
    .split (coordinate 11) (![⟨916095, by decide⟩,⟨916114, by decide⟩,⟨916128, by decide⟩,⟨916145, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_70820_916146 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70820 ⟨916146, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 70820
    ⟨916146, by decide⟩ (by decide) (![⟨916095, by decide⟩,⟨916114, by decide⟩,⟨916128, by decide⟩,⟨916145, by decide⟩]) unmarked_context_11_70820_916146 node_context_11_70820_916146
  intro a
  fin_cases a
  · exact context_12_283280_916095
  · exact context_12_283281_916114
  · exact context_12_283282_916128
  · exact context_12_283283_916145

theorem selected_cut_35019 : selected 9 ⟨916159, by decide⟩
    (prefixPartial 12 283284) = some ⟨12, 2, 0, 916159, 283284, 1085, 65536⟩ := by
  decide +kernel

theorem context_12_283284_916159 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283284 ⟨916159, by decide⟩ :=
  accepted_of_selected 12 283284 ⟨916159, by decide⟩ ⟨12, 2, 0, 916159, 283284, 1085, 65536⟩
    (by decide) selected_cut_35019

theorem selected_cut_35020 : selected 9 ⟨916174, by decide⟩
    (prefixPartial 12 283285) = some ⟨12, 2, 0, 916174, 283285, 1057, 65536⟩ := by
  decide +kernel

theorem context_12_283285_916174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283285 ⟨916174, by decide⟩ :=
  accepted_of_selected 12 283285 ⟨916174, by decide⟩ ⟨12, 2, 0, 916174, 283285, 1057, 65536⟩
    (by decide) selected_cut_35020

theorem selected_cut_35021 : selected 9 ⟨916189, by decide⟩
    (prefixPartial 12 283286) = some ⟨12, 2, 0, 916189, 283286, 1033, 65536⟩ := by
  decide +kernel

theorem context_12_283286_916189 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283286 ⟨916189, by decide⟩ :=
  accepted_of_selected 12 283286 ⟨916189, by decide⟩ ⟨12, 2, 0, 916189, 283286, 1033, 65536⟩
    (by decide) selected_cut_35021

theorem selected_cut_35022 : selected 9 ⟨916205, by decide⟩
    (prefixPartial 12 283287) = some ⟨12, 2, 0, 916205, 283287, 1129, 65536⟩ := by
  decide +kernel

theorem context_12_283287_916205 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283287 ⟨916205, by decide⟩ :=
  accepted_of_selected 12 283287 ⟨916205, by decide⟩ ⟨12, 2, 0, 916205, 283287, 1129, 65536⟩
    (by decide) selected_cut_35022

theorem unmarked_context_11_70821_916206 : frontier 10 ⟨916206, by decide⟩
    (prefixCache 11 70821) (prefixPartial 11 70821) = false := by
  decide +kernel

theorem node_context_11_70821_916206 : EJMOriginalGlobalDAGData.nodes 10 ⟨916206, by decide⟩ =
    .split (coordinate 11) (![⟨916159, by decide⟩,⟨916174, by decide⟩,⟨916189, by decide⟩,⟨916205, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_70821_916206 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70821 ⟨916206, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 70821
    ⟨916206, by decide⟩ (by decide) (![⟨916159, by decide⟩,⟨916174, by decide⟩,⟨916189, by decide⟩,⟨916205, by decide⟩]) unmarked_context_11_70821_916206 node_context_11_70821_916206
  intro a
  fin_cases a
  · exact context_12_283284_916159
  · exact context_12_283285_916174
  · exact context_12_283286_916189
  · exact context_12_283287_916205

theorem selected_cut_35023 : selected 9 ⟨916223, by decide⟩
    (prefixPartial 12 283288) = some ⟨12, 2, 0, 916223, 283288, 1305, 65536⟩ := by
  decide +kernel

theorem context_12_283288_916223 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283288 ⟨916223, by decide⟩ :=
  accepted_of_selected 12 283288 ⟨916223, by decide⟩ ⟨12, 2, 0, 916223, 283288, 1305, 65536⟩
    (by decide) selected_cut_35023

theorem selected_cut_35024 : selected 9 ⟨916247, by decide⟩
    (prefixPartial 12 283289) = some ⟨12, 2, 0, 916247, 283289, 1429, 65536⟩ := by
  decide +kernel

theorem context_12_283289_916247 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283289 ⟨916247, by decide⟩ :=
  accepted_of_selected 12 283289 ⟨916247, by decide⟩ ⟨12, 2, 0, 916247, 283289, 1429, 65536⟩
    (by decide) selected_cut_35024

theorem selected_cut_35025 : selected 9 ⟨893903, by decide⟩
    (prefixPartial 12 283290) = some ⟨12, 1, 0, 893903, 283290, 1, 65536⟩ := by
  decide +kernel

theorem context_12_283290_893903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283290 ⟨893903, by decide⟩ :=
  accepted_of_selected 12 283290 ⟨893903, by decide⟩ ⟨12, 1, 0, 893903, 283290, 1, 65536⟩
    (by decide) selected_cut_35025

theorem selected_cut_35026 : selected 9 ⟨916270, by decide⟩
    (prefixPartial 12 283291) = some ⟨12, 2, 0, 916270, 283291, 1509, 65536⟩ := by
  decide +kernel

theorem context_12_283291_916270 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283291 ⟨916270, by decide⟩ :=
  accepted_of_selected 12 283291 ⟨916270, by decide⟩ ⟨12, 2, 0, 916270, 283291, 1509, 65536⟩
    (by decide) selected_cut_35026

theorem unmarked_context_11_70822_916271 : frontier 10 ⟨916271, by decide⟩
    (prefixCache 11 70822) (prefixPartial 11 70822) = false := by
  decide +kernel

theorem node_context_11_70822_916271 : EJMOriginalGlobalDAGData.nodes 10 ⟨916271, by decide⟩ =
    .split (coordinate 11) (![⟨916223, by decide⟩,⟨916247, by decide⟩,⟨893903, by decide⟩,⟨916270, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_70822_916271 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70822 ⟨916271, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 70822
    ⟨916271, by decide⟩ (by decide) (![⟨916223, by decide⟩,⟨916247, by decide⟩,⟨893903, by decide⟩,⟨916270, by decide⟩]) unmarked_context_11_70822_916271 node_context_11_70822_916271
  intro a
  fin_cases a
  · exact context_12_283288_916223
  · exact context_12_283289_916247
  · exact context_12_283290_893903
  · exact context_12_283291_916270

theorem selected_cut_35027 : selected 9 ⟨916291, by decide⟩
    (prefixPartial 12 283292) = some ⟨12, 2, 0, 916291, 283292, 1265, 65536⟩ := by
  decide +kernel

theorem context_12_283292_916291 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283292 ⟨916291, by decide⟩ :=
  accepted_of_selected 12 283292 ⟨916291, by decide⟩ ⟨12, 2, 0, 916291, 283292, 1265, 65536⟩
    (by decide) selected_cut_35027

theorem selected_cut_35028 : selected 9 ⟨916309, by decide⟩
    (prefixPartial 12 283293) = some ⟨12, 2, 0, 916309, 283293, 1281, 65536⟩ := by
  decide +kernel

theorem context_12_283293_916309 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283293 ⟨916309, by decide⟩ :=
  accepted_of_selected 12 283293 ⟨916309, by decide⟩ ⟨12, 2, 0, 916309, 283293, 1281, 65536⟩
    (by decide) selected_cut_35028

theorem selected_cut_35029 : selected 9 ⟨916326, by decide⟩
    (prefixPartial 12 283294) = some ⟨12, 2, 0, 916326, 283294, 1225, 65536⟩ := by
  decide +kernel

theorem context_12_283294_916326 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283294 ⟨916326, by decide⟩ :=
  accepted_of_selected 12 283294 ⟨916326, by decide⟩ ⟨12, 2, 0, 916326, 283294, 1225, 65536⟩
    (by decide) selected_cut_35029

theorem selected_cut_35030 : selected 9 ⟨916344, by decide⟩
    (prefixPartial 12 283295) = some ⟨12, 2, 0, 916344, 283295, 1229, 65536⟩ := by
  decide +kernel

theorem context_12_283295_916344 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283295 ⟨916344, by decide⟩ :=
  accepted_of_selected 12 283295 ⟨916344, by decide⟩ ⟨12, 2, 0, 916344, 283295, 1229, 65536⟩
    (by decide) selected_cut_35030

theorem unmarked_context_11_70823_916345 : frontier 10 ⟨916345, by decide⟩
    (prefixCache 11 70823) (prefixPartial 11 70823) = false := by
  decide +kernel

theorem node_context_11_70823_916345 : EJMOriginalGlobalDAGData.nodes 10 ⟨916345, by decide⟩ =
    .split (coordinate 11) (![⟨916291, by decide⟩,⟨916309, by decide⟩,⟨916326, by decide⟩,⟨916344, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_70823_916345 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70823 ⟨916345, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 70823
    ⟨916345, by decide⟩ (by decide) (![⟨916291, by decide⟩,⟨916309, by decide⟩,⟨916326, by decide⟩,⟨916344, by decide⟩]) unmarked_context_11_70823_916345 node_context_11_70823_916345
  intro a
  fin_cases a
  · exact context_12_283292_916291
  · exact context_12_283293_916309
  · exact context_12_283294_916326
  · exact context_12_283295_916344

theorem unmarked_context_10_17705_916346 : frontier 11 ⟨916346, by decide⟩
    (prefixCache 10 17705) (prefixPartial 10 17705) = false := by
  decide +kernel

theorem node_context_10_17705_916346 : EJMOriginalGlobalDAGData.nodes 11 ⟨916346, by decide⟩ =
    .split (coordinate 10) (![⟨916146, by decide⟩,⟨916206, by decide⟩,⟨916271, by decide⟩,⟨916345, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17705_916346 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17705 ⟨916346, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17705
    ⟨916346, by decide⟩ (by decide) (![⟨916146, by decide⟩,⟨916206, by decide⟩,⟨916271, by decide⟩,⟨916345, by decide⟩]) unmarked_context_10_17705_916346 node_context_10_17705_916346
  intro a
  fin_cases a
  · exact context_11_70820_916146
  · exact context_11_70821_916206
  · exact context_11_70822_916271
  · exact context_11_70823_916345

theorem selected_cut_35031 : selected 10 ⟨916393, by decide⟩
    (prefixPartial 11 70824) = some ⟨11, 2, 0, 916393, 70824, 3869, 262144⟩ := by
  decide +kernel

theorem context_11_70824_916393 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70824 ⟨916393, by decide⟩ :=
  accepted_of_selected 11 70824 ⟨916393, by decide⟩ ⟨11, 2, 0, 916393, 70824, 3869, 262144⟩
    (by decide) selected_cut_35031

theorem selected_cut_35032 : selected 10 ⟨916436, by decide⟩
    (prefixPartial 11 70825) = some ⟨11, 2, 0, 916436, 70825, 2853, 262144⟩ := by
  decide +kernel

theorem context_11_70825_916436 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70825 ⟨916436, by decide⟩ :=
  accepted_of_selected 11 70825 ⟨916436, by decide⟩ ⟨11, 2, 0, 916436, 70825, 2853, 262144⟩
    (by decide) selected_cut_35032

theorem selected_cut_35033 : selected 10 ⟨916474, by decide⟩
    (prefixPartial 11 70826) = some ⟨11, 2, 0, 916474, 70826, 2869, 262144⟩ := by
  decide +kernel

theorem context_11_70826_916474 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70826 ⟨916474, by decide⟩ :=
  accepted_of_selected 11 70826 ⟨916474, by decide⟩ ⟨11, 2, 0, 916474, 70826, 2869, 262144⟩
    (by decide) selected_cut_35033

theorem selected_cut_35034 : selected 10 ⟨916523, by decide⟩
    (prefixPartial 11 70827) = some ⟨11, 2, 0, 916523, 70827, 3745, 262144⟩ := by
  decide +kernel

theorem context_11_70827_916523 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70827 ⟨916523, by decide⟩ :=
  accepted_of_selected 11 70827 ⟨916523, by decide⟩ ⟨11, 2, 0, 916523, 70827, 3745, 262144⟩
    (by decide) selected_cut_35034

theorem unmarked_context_10_17706_916524 : frontier 11 ⟨916524, by decide⟩
    (prefixCache 10 17706) (prefixPartial 10 17706) = false := by
  decide +kernel

theorem node_context_10_17706_916524 : EJMOriginalGlobalDAGData.nodes 11 ⟨916524, by decide⟩ =
    .split (coordinate 10) (![⟨916393, by decide⟩,⟨916436, by decide⟩,⟨916474, by decide⟩,⟨916523, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17706_916524 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17706 ⟨916524, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17706
    ⟨916524, by decide⟩ (by decide) (![⟨916393, by decide⟩,⟨916436, by decide⟩,⟨916474, by decide⟩,⟨916523, by decide⟩]) unmarked_context_10_17706_916524 node_context_10_17706_916524
  intro a
  fin_cases a
  · exact context_11_70824_916393
  · exact context_11_70825_916436
  · exact context_11_70826_916474
  · exact context_11_70827_916523

theorem selected_cut_35035 : selected 10 ⟨916550, by decide⟩
    (prefixPartial 11 70828) = some ⟨11, 2, 0, 916550, 70828, 2893, 262144⟩ := by
  decide +kernel

theorem context_11_70828_916550 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70828 ⟨916550, by decide⟩ :=
  accepted_of_selected 11 70828 ⟨916550, by decide⟩ ⟨11, 2, 0, 916550, 70828, 2893, 262144⟩
    (by decide) selected_cut_35035

theorem selected_cut_35036 : selected 10 ⟨916579, by decide⟩
    (prefixPartial 11 70829) = some ⟨11, 2, 0, 916579, 70829, 2761, 262144⟩ := by
  decide +kernel

theorem context_11_70829_916579 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70829 ⟨916579, by decide⟩ :=
  accepted_of_selected 11 70829 ⟨916579, by decide⟩ ⟨11, 2, 0, 916579, 70829, 2761, 262144⟩
    (by decide) selected_cut_35036

theorem selected_cut_35037 : selected 10 ⟨916608, by decide⟩
    (prefixPartial 11 70830) = some ⟨11, 2, 0, 916608, 70830, 2233, 262144⟩ := by
  decide +kernel

theorem context_11_70830_916608 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70830 ⟨916608, by decide⟩ :=
  accepted_of_selected 11 70830 ⟨916608, by decide⟩ ⟨11, 2, 0, 916608, 70830, 2233, 262144⟩
    (by decide) selected_cut_35037

theorem selected_cut_35038 : selected 10 ⟨916642, by decide⟩
    (prefixPartial 11 70831) = some ⟨11, 2, 0, 916642, 70831, 2645, 262144⟩ := by
  decide +kernel

theorem context_11_70831_916642 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70831 ⟨916642, by decide⟩ :=
  accepted_of_selected 11 70831 ⟨916642, by decide⟩ ⟨11, 2, 0, 916642, 70831, 2645, 262144⟩
    (by decide) selected_cut_35038

theorem unmarked_context_10_17707_916643 : frontier 11 ⟨916643, by decide⟩
    (prefixCache 10 17707) (prefixPartial 10 17707) = false := by
  decide +kernel

theorem node_context_10_17707_916643 : EJMOriginalGlobalDAGData.nodes 11 ⟨916643, by decide⟩ =
    .split (coordinate 10) (![⟨916550, by decide⟩,⟨916579, by decide⟩,⟨916608, by decide⟩,⟨916642, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17707_916643 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17707 ⟨916643, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17707
    ⟨916643, by decide⟩ (by decide) (![⟨916550, by decide⟩,⟨916579, by decide⟩,⟨916608, by decide⟩,⟨916642, by decide⟩]) unmarked_context_10_17707_916643 node_context_10_17707_916643
  intro a
  fin_cases a
  · exact context_11_70828_916550
  · exact context_11_70829_916579
  · exact context_11_70830_916608
  · exact context_11_70831_916642

theorem unmarked_context_9_4426_916644 : frontier 12 ⟨916644, by decide⟩
    (prefixCache 9 4426) (prefixPartial 9 4426) = false := by
  decide +kernel

theorem node_context_9_4426_916644 : EJMOriginalGlobalDAGData.nodes 12 ⟨916644, by decide⟩ =
    .split (coordinate 9) (![⟨916077, by decide⟩,⟨916346, by decide⟩,⟨916524, by decide⟩,⟨916643, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4426_916644 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4426 ⟨916644, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4426
    ⟨916644, by decide⟩ (by decide) (![⟨916077, by decide⟩,⟨916346, by decide⟩,⟨916524, by decide⟩,⟨916643, by decide⟩]) unmarked_context_9_4426_916644 node_context_9_4426_916644
  intro a
  fin_cases a
  · exact context_10_17704_916077
  · exact context_10_17705_916346
  · exact context_10_17706_916524
  · exact context_10_17707_916643

theorem selected_cut_35039 : selected 10 ⟨907917, by decide⟩
    (prefixPartial 11 70832) = some ⟨11, 1, 0, 907917, 70832, 1, 262144⟩ := by
  decide +kernel

theorem context_11_70832_907917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70832 ⟨907917, by decide⟩ :=
  accepted_of_selected 11 70832 ⟨907917, by decide⟩ ⟨11, 1, 0, 907917, 70832, 1, 262144⟩
    (by decide) selected_cut_35039

theorem selected_cut_35040 : selected 10 ⟨916672, by decide⟩
    (prefixPartial 11 70833) = some ⟨11, 2, 0, 916672, 70833, 2337, 262144⟩ := by
  decide +kernel

theorem context_11_70833_916672 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70833 ⟨916672, by decide⟩ :=
  accepted_of_selected 11 70833 ⟨916672, by decide⟩ ⟨11, 2, 0, 916672, 70833, 2337, 262144⟩
    (by decide) selected_cut_35040

theorem selected_cut_35041 : selected 10 ⟨916692, by decide⟩
    (prefixPartial 11 70834) = some ⟨11, 2, 0, 916692, 70834, 1781, 262144⟩ := by
  decide +kernel

theorem context_11_70834_916692 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70834 ⟨916692, by decide⟩ :=
  accepted_of_selected 11 70834 ⟨916692, by decide⟩ ⟨11, 2, 0, 916692, 70834, 1781, 262144⟩
    (by decide) selected_cut_35041

theorem selected_cut_35042 : selected 10 ⟨916722, by decide⟩
    (prefixPartial 11 70835) = some ⟨11, 2, 0, 916722, 70835, 2445, 262144⟩ := by
  decide +kernel

theorem context_11_70835_916722 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70835 ⟨916722, by decide⟩ :=
  accepted_of_selected 11 70835 ⟨916722, by decide⟩ ⟨11, 2, 0, 916722, 70835, 2445, 262144⟩
    (by decide) selected_cut_35042

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
