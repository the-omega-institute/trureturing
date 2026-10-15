/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover290
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_27940 : selected 8 ⟨705657, by decide⟩
    (prefixPartial 13 367819) = some ⟨13, 2, 0, 705657, 367819, 825, 16384⟩ := by
  decide +kernel

theorem context_13_367819_705657 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367819 ⟨705657, by decide⟩ :=
  accepted_of_selected 13 367819 ⟨705657, by decide⟩ ⟨13, 2, 0, 705657, 367819, 825, 16384⟩
    (by decide) selected_cut_27940

theorem unmarked_context_12_91954_705658 : frontier 9 ⟨705658, by decide⟩
    (prefixCache 12 91954) (prefixPartial 12 91954) = false := by
  decide +kernel

theorem node_context_12_91954_705658 : EJMOriginalGlobalDAGData.nodes 9 ⟨705658, by decide⟩ =
    .split (coordinate 12) (![⟨705605, by decide⟩,⟨705630, by decide⟩,⟨705646, by decide⟩,⟨705657, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91954_705658 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91954 ⟨705658, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91954
    ⟨705658, by decide⟩ (by decide) (![⟨705605, by decide⟩,⟨705630, by decide⟩,⟨705646, by decide⟩,⟨705657, by decide⟩]) unmarked_context_12_91954_705658 node_context_12_91954_705658
  intro a
  fin_cases a
  · exact context_13_367816_705605
  · exact context_13_367817_705630
  · exact context_13_367818_705646
  · exact context_13_367819_705657

theorem selected_cut_27941 : selected 8 ⟨705665, by decide⟩
    (prefixPartial 13 367820) = some ⟨13, 2, 0, 705665, 367820, 469, 16384⟩ := by
  decide +kernel

theorem context_13_367820_705665 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367820 ⟨705665, by decide⟩ :=
  accepted_of_selected 13 367820 ⟨705665, by decide⟩ ⟨13, 2, 0, 705665, 367820, 469, 16384⟩
    (by decide) selected_cut_27941

theorem selected_cut_27942 : selected 8 ⟨705692, by decide⟩
    (prefixPartial 13 367821) = some ⟨13, 2, 0, 705692, 367821, 2181, 16384⟩ := by
  decide +kernel

theorem context_13_367821_705692 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367821 ⟨705692, by decide⟩ :=
  accepted_of_selected 13 367821 ⟨705692, by decide⟩ ⟨13, 2, 0, 705692, 367821, 2181, 16384⟩
    (by decide) selected_cut_27942

theorem selected_cut_27943 : selected 8 ⟨705709, by decide⟩
    (prefixPartial 13 367822) = some ⟨13, 2, 0, 705709, 367822, 1585, 16384⟩ := by
  decide +kernel

theorem context_13_367822_705709 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367822 ⟨705709, by decide⟩ :=
  accepted_of_selected 13 367822 ⟨705709, by decide⟩ ⟨13, 2, 0, 705709, 367822, 1585, 16384⟩
    (by decide) selected_cut_27943

theorem selected_cut_27944 : selected 8 ⟨705716, by decide⟩
    (prefixPartial 13 367823) = some ⟨13, 2, 0, 705716, 367823, 753, 16384⟩ := by
  decide +kernel

theorem context_13_367823_705716 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367823 ⟨705716, by decide⟩ :=
  accepted_of_selected 13 367823 ⟨705716, by decide⟩ ⟨13, 2, 0, 705716, 367823, 753, 16384⟩
    (by decide) selected_cut_27944

theorem unmarked_context_12_91955_705717 : frontier 9 ⟨705717, by decide⟩
    (prefixCache 12 91955) (prefixPartial 12 91955) = false := by
  decide +kernel

theorem node_context_12_91955_705717 : EJMOriginalGlobalDAGData.nodes 9 ⟨705717, by decide⟩ =
    .split (coordinate 12) (![⟨705665, by decide⟩,⟨705692, by decide⟩,⟨705709, by decide⟩,⟨705716, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91955_705717 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91955 ⟨705717, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91955
    ⟨705717, by decide⟩ (by decide) (![⟨705665, by decide⟩,⟨705692, by decide⟩,⟨705709, by decide⟩,⟨705716, by decide⟩]) unmarked_context_12_91955_705717 node_context_12_91955_705717
  intro a
  fin_cases a
  · exact context_13_367820_705665
  · exact context_13_367821_705692
  · exact context_13_367822_705709
  · exact context_13_367823_705716

theorem unmarked_context_11_22988_705718 : frontier 10 ⟨705718, by decide⟩
    (prefixCache 11 22988) (prefixPartial 11 22988) = false := by
  decide +kernel

theorem node_context_11_22988_705718 : EJMOriginalGlobalDAGData.nodes 10 ⟨705718, by decide⟩ =
    .split (coordinate 11) (![⟨705525, by decide⟩,⟨705598, by decide⟩,⟨705658, by decide⟩,⟨705717, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22988_705718 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22988 ⟨705718, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22988
    ⟨705718, by decide⟩ (by decide) (![⟨705525, by decide⟩,⟨705598, by decide⟩,⟨705658, by decide⟩,⟨705717, by decide⟩]) unmarked_context_11_22988_705718 node_context_11_22988_705718
  intro a
  fin_cases a
  · exact context_12_91952_705525
  · exact context_12_91953_705598
  · exact context_12_91954_705658
  · exact context_12_91955_705717

theorem selected_cut_27945 : selected 8 ⟨705723, by decide⟩
    (prefixPartial 13 367824) = some ⟨13, 2, 0, 705723, 367824, 317, 16384⟩ := by
  decide +kernel

theorem context_13_367824_705723 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367824 ⟨705723, by decide⟩ :=
  accepted_of_selected 13 367824 ⟨705723, by decide⟩ ⟨13, 2, 0, 705723, 367824, 317, 16384⟩
    (by decide) selected_cut_27945

theorem selected_cut_27946 : selected 8 ⟨705756, by decide⟩
    (prefixPartial 13 367825) = some ⟨13, 2, 0, 705756, 367825, 1937, 16384⟩ := by
  decide +kernel

theorem context_13_367825_705756 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367825 ⟨705756, by decide⟩ :=
  accepted_of_selected 13 367825 ⟨705756, by decide⟩ ⟨13, 2, 0, 705756, 367825, 1937, 16384⟩
    (by decide) selected_cut_27946

theorem selected_cut_27947 : selected 8 ⟨705770, by decide⟩
    (prefixPartial 13 367826) = some ⟨13, 2, 0, 705770, 367826, 1369, 16384⟩ := by
  decide +kernel

theorem context_13_367826_705770 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367826 ⟨705770, by decide⟩ :=
  accepted_of_selected 13 367826 ⟨705770, by decide⟩ ⟨13, 2, 0, 705770, 367826, 1369, 16384⟩
    (by decide) selected_cut_27947

theorem selected_cut_27948 : selected 8 ⟨705776, by decide⟩
    (prefixPartial 13 367827) = some ⟨13, 2, 0, 705776, 367827, 837, 16384⟩ := by
  decide +kernel

theorem context_13_367827_705776 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367827 ⟨705776, by decide⟩ :=
  accepted_of_selected 13 367827 ⟨705776, by decide⟩ ⟨13, 2, 0, 705776, 367827, 837, 16384⟩
    (by decide) selected_cut_27948

theorem unmarked_context_12_91956_705777 : frontier 9 ⟨705777, by decide⟩
    (prefixCache 12 91956) (prefixPartial 12 91956) = false := by
  decide +kernel

theorem node_context_12_91956_705777 : EJMOriginalGlobalDAGData.nodes 9 ⟨705777, by decide⟩ =
    .split (coordinate 12) (![⟨705723, by decide⟩,⟨705756, by decide⟩,⟨705770, by decide⟩,⟨705776, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91956_705777 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91956 ⟨705777, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91956
    ⟨705777, by decide⟩ (by decide) (![⟨705723, by decide⟩,⟨705756, by decide⟩,⟨705770, by decide⟩,⟨705776, by decide⟩]) unmarked_context_12_91956_705777 node_context_12_91956_705777
  intro a
  fin_cases a
  · exact context_13_367824_705723
  · exact context_13_367825_705756
  · exact context_13_367826_705770
  · exact context_13_367827_705776

theorem selected_cut_27949 : selected 8 ⟨705782, by decide⟩
    (prefixPartial 13 367828) = some ⟨13, 2, 0, 705782, 367828, 325, 16384⟩ := by
  decide +kernel

theorem context_13_367828_705782 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367828 ⟨705782, by decide⟩ :=
  accepted_of_selected 13 367828 ⟨705782, by decide⟩ ⟨13, 2, 0, 705782, 367828, 325, 16384⟩
    (by decide) selected_cut_27949

theorem selected_cut_27950 : selected 8 ⟨705810, by decide⟩
    (prefixPartial 13 367829) = some ⟨13, 2, 0, 705810, 367829, 1877, 16384⟩ := by
  decide +kernel

theorem context_13_367829_705810 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367829 ⟨705810, by decide⟩ :=
  accepted_of_selected 13 367829 ⟨705810, by decide⟩ ⟨13, 2, 0, 705810, 367829, 1877, 16384⟩
    (by decide) selected_cut_27950

theorem selected_cut_27951 : selected 8 ⟨705827, by decide⟩
    (prefixPartial 13 367830) = some ⟨13, 2, 0, 705827, 367830, 1377, 16384⟩ := by
  decide +kernel

theorem context_13_367830_705827 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367830 ⟨705827, by decide⟩ :=
  accepted_of_selected 13 367830 ⟨705827, by decide⟩ ⟨13, 2, 0, 705827, 367830, 1377, 16384⟩
    (by decide) selected_cut_27951

theorem selected_cut_27952 : selected 8 ⟨705833, by decide⟩
    (prefixPartial 13 367831) = some ⟨13, 2, 0, 705833, 367831, 677, 16384⟩ := by
  decide +kernel

theorem context_13_367831_705833 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367831 ⟨705833, by decide⟩ :=
  accepted_of_selected 13 367831 ⟨705833, by decide⟩ ⟨13, 2, 0, 705833, 367831, 677, 16384⟩
    (by decide) selected_cut_27952

theorem unmarked_context_12_91957_705834 : frontier 9 ⟨705834, by decide⟩
    (prefixCache 12 91957) (prefixPartial 12 91957) = false := by
  decide +kernel

theorem node_context_12_91957_705834 : EJMOriginalGlobalDAGData.nodes 9 ⟨705834, by decide⟩ =
    .split (coordinate 12) (![⟨705782, by decide⟩,⟨705810, by decide⟩,⟨705827, by decide⟩,⟨705833, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91957_705834 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91957 ⟨705834, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91957
    ⟨705834, by decide⟩ (by decide) (![⟨705782, by decide⟩,⟨705810, by decide⟩,⟨705827, by decide⟩,⟨705833, by decide⟩]) unmarked_context_12_91957_705834 node_context_12_91957_705834
  intro a
  fin_cases a
  · exact context_13_367828_705782
  · exact context_13_367829_705810
  · exact context_13_367830_705827
  · exact context_13_367831_705833

theorem selected_cut_27953 : selected 8 ⟨705840, by decide⟩
    (prefixPartial 13 367832) = some ⟨13, 2, 0, 705840, 367832, 321, 16384⟩ := by
  decide +kernel

theorem context_13_367832_705840 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367832 ⟨705840, by decide⟩ :=
  accepted_of_selected 13 367832 ⟨705840, by decide⟩ ⟨13, 2, 0, 705840, 367832, 321, 16384⟩
    (by decide) selected_cut_27953

theorem selected_cut_27954 : selected 8 ⟨705870, by decide⟩
    (prefixPartial 13 367833) = some ⟨13, 2, 0, 705870, 367833, 1865, 16384⟩ := by
  decide +kernel

theorem context_13_367833_705870 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367833 ⟨705870, by decide⟩ :=
  accepted_of_selected 13 367833 ⟨705870, by decide⟩ ⟨13, 2, 0, 705870, 367833, 1865, 16384⟩
    (by decide) selected_cut_27954

theorem selected_cut_27955 : selected 8 ⟨705885, by decide⟩
    (prefixPartial 13 367834) = some ⟨13, 2, 0, 705885, 367834, 1161, 16384⟩ := by
  decide +kernel

theorem context_13_367834_705885 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367834 ⟨705885, by decide⟩ :=
  accepted_of_selected 13 367834 ⟨705885, by decide⟩ ⟨13, 2, 0, 705885, 367834, 1161, 16384⟩
    (by decide) selected_cut_27955

theorem selected_cut_27956 : selected 8 ⟨705893, by decide⟩
    (prefixPartial 13 367835) = some ⟨13, 2, 0, 705893, 367835, 833, 16384⟩ := by
  decide +kernel

theorem context_13_367835_705893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367835 ⟨705893, by decide⟩ :=
  accepted_of_selected 13 367835 ⟨705893, by decide⟩ ⟨13, 2, 0, 705893, 367835, 833, 16384⟩
    (by decide) selected_cut_27956

theorem unmarked_context_12_91958_705894 : frontier 9 ⟨705894, by decide⟩
    (prefixCache 12 91958) (prefixPartial 12 91958) = false := by
  decide +kernel

theorem node_context_12_91958_705894 : EJMOriginalGlobalDAGData.nodes 9 ⟨705894, by decide⟩ =
    .split (coordinate 12) (![⟨705840, by decide⟩,⟨705870, by decide⟩,⟨705885, by decide⟩,⟨705893, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91958_705894 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91958 ⟨705894, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91958
    ⟨705894, by decide⟩ (by decide) (![⟨705840, by decide⟩,⟨705870, by decide⟩,⟨705885, by decide⟩,⟨705893, by decide⟩]) unmarked_context_12_91958_705894 node_context_12_91958_705894
  intro a
  fin_cases a
  · exact context_13_367832_705840
  · exact context_13_367833_705870
  · exact context_13_367834_705885
  · exact context_13_367835_705893

theorem selected_cut_27957 : selected 8 ⟨705899, by decide⟩
    (prefixPartial 13 367836) = some ⟨13, 2, 0, 705899, 367836, 241, 16384⟩ := by
  decide +kernel

theorem context_13_367836_705899 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367836 ⟨705899, by decide⟩ :=
  accepted_of_selected 13 367836 ⟨705899, by decide⟩ ⟨13, 2, 0, 705899, 367836, 241, 16384⟩
    (by decide) selected_cut_27957

theorem selected_cut_27958 : selected 8 ⟨705923, by decide⟩
    (prefixPartial 13 367837) = some ⟨13, 2, 0, 705923, 367837, 1953, 16384⟩ := by
  decide +kernel

theorem context_13_367837_705923 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367837 ⟨705923, by decide⟩ :=
  accepted_of_selected 13 367837 ⟨705923, by decide⟩ ⟨13, 2, 0, 705923, 367837, 1953, 16384⟩
    (by decide) selected_cut_27958

theorem selected_cut_27959 : selected 8 ⟨705942, by decide⟩
    (prefixPartial 13 367838) = some ⟨13, 2, 0, 705942, 367838, 1405, 16384⟩ := by
  decide +kernel

theorem context_13_367838_705942 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367838 ⟨705942, by decide⟩ :=
  accepted_of_selected 13 367838 ⟨705942, by decide⟩ ⟨13, 2, 0, 705942, 367838, 1405, 16384⟩
    (by decide) selected_cut_27959

theorem selected_cut_27960 : selected 8 ⟨705947, by decide⟩
    (prefixPartial 13 367839) = some ⟨13, 2, 0, 705947, 367839, 745, 16384⟩ := by
  decide +kernel

theorem context_13_367839_705947 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367839 ⟨705947, by decide⟩ :=
  accepted_of_selected 13 367839 ⟨705947, by decide⟩ ⟨13, 2, 0, 705947, 367839, 745, 16384⟩
    (by decide) selected_cut_27960

theorem unmarked_context_12_91959_705948 : frontier 9 ⟨705948, by decide⟩
    (prefixCache 12 91959) (prefixPartial 12 91959) = false := by
  decide +kernel

theorem node_context_12_91959_705948 : EJMOriginalGlobalDAGData.nodes 9 ⟨705948, by decide⟩ =
    .split (coordinate 12) (![⟨705899, by decide⟩,⟨705923, by decide⟩,⟨705942, by decide⟩,⟨705947, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91959_705948 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91959 ⟨705948, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91959
    ⟨705948, by decide⟩ (by decide) (![⟨705899, by decide⟩,⟨705923, by decide⟩,⟨705942, by decide⟩,⟨705947, by decide⟩]) unmarked_context_12_91959_705948 node_context_12_91959_705948
  intro a
  fin_cases a
  · exact context_13_367836_705899
  · exact context_13_367837_705923
  · exact context_13_367838_705942
  · exact context_13_367839_705947

theorem unmarked_context_11_22989_705949 : frontier 10 ⟨705949, by decide⟩
    (prefixCache 11 22989) (prefixPartial 11 22989) = false := by
  decide +kernel

theorem node_context_11_22989_705949 : EJMOriginalGlobalDAGData.nodes 10 ⟨705949, by decide⟩ =
    .split (coordinate 11) (![⟨705777, by decide⟩,⟨705834, by decide⟩,⟨705894, by decide⟩,⟨705948, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22989_705949 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22989 ⟨705949, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22989
    ⟨705949, by decide⟩ (by decide) (![⟨705777, by decide⟩,⟨705834, by decide⟩,⟨705894, by decide⟩,⟨705948, by decide⟩]) unmarked_context_11_22989_705949 node_context_11_22989_705949
  intro a
  fin_cases a
  · exact context_12_91956_705777
  · exact context_12_91957_705834
  · exact context_12_91958_705894
  · exact context_12_91959_705948

theorem selected_cut_27961 : selected 8 ⟨705954, by decide⟩
    (prefixPartial 13 367840) = some ⟨13, 2, 0, 705954, 367840, 257, 16384⟩ := by
  decide +kernel

theorem context_13_367840_705954 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367840 ⟨705954, by decide⟩ :=
  accepted_of_selected 13 367840 ⟨705954, by decide⟩ ⟨13, 2, 0, 705954, 367840, 257, 16384⟩
    (by decide) selected_cut_27961

theorem selected_cut_27962 : selected 8 ⟨705986, by decide⟩
    (prefixPartial 13 367841) = some ⟨13, 2, 0, 705986, 367841, 2249, 16384⟩ := by
  decide +kernel

theorem context_13_367841_705986 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367841 ⟨705986, by decide⟩ :=
  accepted_of_selected 13 367841 ⟨705986, by decide⟩ ⟨13, 2, 0, 705986, 367841, 2249, 16384⟩
    (by decide) selected_cut_27962

theorem selected_cut_27963 : selected 8 ⟨706005, by decide⟩
    (prefixPartial 13 367842) = some ⟨13, 2, 0, 706005, 367842, 1585, 16384⟩ := by
  decide +kernel

theorem context_13_367842_706005 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367842 ⟨706005, by decide⟩ :=
  accepted_of_selected 13 367842 ⟨706005, by decide⟩ ⟨13, 2, 0, 706005, 367842, 1585, 16384⟩
    (by decide) selected_cut_27963

theorem selected_cut_27964 : selected 8 ⟨706014, by decide⟩
    (prefixPartial 13 367843) = some ⟨13, 2, 0, 706014, 367843, 933, 16384⟩ := by
  decide +kernel

theorem context_13_367843_706014 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367843 ⟨706014, by decide⟩ :=
  accepted_of_selected 13 367843 ⟨706014, by decide⟩ ⟨13, 2, 0, 706014, 367843, 933, 16384⟩
    (by decide) selected_cut_27964

theorem unmarked_context_12_91960_706015 : frontier 9 ⟨706015, by decide⟩
    (prefixCache 12 91960) (prefixPartial 12 91960) = false := by
  decide +kernel

theorem node_context_12_91960_706015 : EJMOriginalGlobalDAGData.nodes 9 ⟨706015, by decide⟩ =
    .split (coordinate 12) (![⟨705954, by decide⟩,⟨705986, by decide⟩,⟨706005, by decide⟩,⟨706014, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91960_706015 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91960 ⟨706015, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91960
    ⟨706015, by decide⟩ (by decide) (![⟨705954, by decide⟩,⟨705986, by decide⟩,⟨706005, by decide⟩,⟨706014, by decide⟩]) unmarked_context_12_91960_706015 node_context_12_91960_706015
  intro a
  fin_cases a
  · exact context_13_367840_705954
  · exact context_13_367841_705986
  · exact context_13_367842_706005
  · exact context_13_367843_706014

theorem selected_cut_27965 : selected 8 ⟨706020, by decide⟩
    (prefixPartial 13 367844) = some ⟨13, 2, 0, 706020, 367844, 293, 16384⟩ := by
  decide +kernel

theorem context_13_367844_706020 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367844 ⟨706020, by decide⟩ :=
  accepted_of_selected 13 367844 ⟨706020, by decide⟩ ⟨13, 2, 0, 706020, 367844, 293, 16384⟩
    (by decide) selected_cut_27965

theorem selected_cut_27966 : selected 8 ⟨706059, by decide⟩
    (prefixPartial 13 367845) = some ⟨13, 2, 0, 706059, 367845, 2293, 16384⟩ := by
  decide +kernel

theorem context_13_367845_706059 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367845 ⟨706059, by decide⟩ :=
  accepted_of_selected 13 367845 ⟨706059, by decide⟩ ⟨13, 2, 0, 706059, 367845, 2293, 16384⟩
    (by decide) selected_cut_27966

theorem selected_cut_27967 : selected 8 ⟨706085, by decide⟩
    (prefixPartial 13 367846) = some ⟨13, 2, 0, 706085, 367846, 1657, 16384⟩ := by
  decide +kernel

theorem context_13_367846_706085 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367846 ⟨706085, by decide⟩ :=
  accepted_of_selected 13 367846 ⟨706085, by decide⟩ ⟨13, 2, 0, 706085, 367846, 1657, 16384⟩
    (by decide) selected_cut_27967

theorem selected_cut_27968 : selected 8 ⟨706092, by decide⟩
    (prefixPartial 13 367847) = some ⟨13, 2, 0, 706092, 367847, 821, 16384⟩ := by
  decide +kernel

theorem context_13_367847_706092 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367847 ⟨706092, by decide⟩ :=
  accepted_of_selected 13 367847 ⟨706092, by decide⟩ ⟨13, 2, 0, 706092, 367847, 821, 16384⟩
    (by decide) selected_cut_27968

theorem unmarked_context_12_91961_706093 : frontier 9 ⟨706093, by decide⟩
    (prefixCache 12 91961) (prefixPartial 12 91961) = false := by
  decide +kernel

theorem node_context_12_91961_706093 : EJMOriginalGlobalDAGData.nodes 9 ⟨706093, by decide⟩ =
    .split (coordinate 12) (![⟨706020, by decide⟩,⟨706059, by decide⟩,⟨706085, by decide⟩,⟨706092, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91961_706093 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91961 ⟨706093, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91961
    ⟨706093, by decide⟩ (by decide) (![⟨706020, by decide⟩,⟨706059, by decide⟩,⟨706085, by decide⟩,⟨706092, by decide⟩]) unmarked_context_12_91961_706093 node_context_12_91961_706093
  intro a
  fin_cases a
  · exact context_13_367844_706020
  · exact context_13_367845_706059
  · exact context_13_367846_706085
  · exact context_13_367847_706092

theorem selected_cut_27969 : selected 8 ⟨706097, by decide⟩
    (prefixPartial 13 367848) = some ⟨13, 2, 0, 706097, 367848, 197, 16384⟩ := by
  decide +kernel

theorem context_13_367848_706097 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367848 ⟨706097, by decide⟩ :=
  accepted_of_selected 13 367848 ⟨706097, by decide⟩ ⟨13, 2, 0, 706097, 367848, 197, 16384⟩
    (by decide) selected_cut_27969

theorem selected_cut_27970 : selected 8 ⟨706130, by decide⟩
    (prefixPartial 13 367849) = some ⟨13, 2, 0, 706130, 367849, 2221, 16384⟩ := by
  decide +kernel

theorem context_13_367849_706130 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367849 ⟨706130, by decide⟩ :=
  accepted_of_selected 13 367849 ⟨706130, by decide⟩ ⟨13, 2, 0, 706130, 367849, 2221, 16384⟩
    (by decide) selected_cut_27970

theorem selected_cut_27971 : selected 8 ⟨706149, by decide⟩
    (prefixPartial 13 367850) = some ⟨13, 2, 0, 706149, 367850, 1377, 16384⟩ := by
  decide +kernel

theorem context_13_367850_706149 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367850 ⟨706149, by decide⟩ :=
  accepted_of_selected 13 367850 ⟨706149, by decide⟩ ⟨13, 2, 0, 706149, 367850, 1377, 16384⟩
    (by decide) selected_cut_27971

theorem selected_cut_27972 : selected 8 ⟨706162, by decide⟩
    (prefixPartial 13 367851) = some ⟨13, 2, 0, 706162, 367851, 865, 16384⟩ := by
  decide +kernel

theorem context_13_367851_706162 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367851 ⟨706162, by decide⟩ :=
  accepted_of_selected 13 367851 ⟨706162, by decide⟩ ⟨13, 2, 0, 706162, 367851, 865, 16384⟩
    (by decide) selected_cut_27972

theorem unmarked_context_12_91962_706163 : frontier 9 ⟨706163, by decide⟩
    (prefixCache 12 91962) (prefixPartial 12 91962) = false := by
  decide +kernel

theorem node_context_12_91962_706163 : EJMOriginalGlobalDAGData.nodes 9 ⟨706163, by decide⟩ =
    .split (coordinate 12) (![⟨706097, by decide⟩,⟨706130, by decide⟩,⟨706149, by decide⟩,⟨706162, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91962_706163 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91962 ⟨706163, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91962
    ⟨706163, by decide⟩ (by decide) (![⟨706097, by decide⟩,⟨706130, by decide⟩,⟨706149, by decide⟩,⟨706162, by decide⟩]) unmarked_context_12_91962_706163 node_context_12_91962_706163
  intro a
  fin_cases a
  · exact context_13_367848_706097
  · exact context_13_367849_706130
  · exact context_13_367850_706149
  · exact context_13_367851_706162

theorem selected_cut_27973 : selected 8 ⟨706167, by decide⟩
    (prefixPartial 13 367852) = some ⟨13, 2, 0, 706167, 367852, 153, 16384⟩ := by
  decide +kernel

theorem context_13_367852_706167 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367852 ⟨706167, by decide⟩ :=
  accepted_of_selected 13 367852 ⟨706167, by decide⟩ ⟨13, 2, 0, 706167, 367852, 153, 16384⟩
    (by decide) selected_cut_27973

theorem selected_cut_27974 : selected 8 ⟨706208, by decide⟩
    (prefixPartial 13 367853) = some ⟨13, 2, 0, 706208, 367853, 2405, 16384⟩ := by
  decide +kernel

theorem context_13_367853_706208 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367853 ⟨706208, by decide⟩ :=
  accepted_of_selected 13 367853 ⟨706208, by decide⟩ ⟨13, 2, 0, 706208, 367853, 2405, 16384⟩
    (by decide) selected_cut_27974

theorem selected_cut_27975 : selected 8 ⟨706225, by decide⟩
    (prefixPartial 13 367854) = some ⟨13, 2, 0, 706225, 367854, 1589, 16384⟩ := by
  decide +kernel

theorem context_13_367854_706225 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367854 ⟨706225, by decide⟩ :=
  accepted_of_selected 13 367854 ⟨706225, by decide⟩ ⟨13, 2, 0, 706225, 367854, 1589, 16384⟩
    (by decide) selected_cut_27975

theorem selected_cut_27976 : selected 8 ⟨706233, by decide⟩
    (prefixPartial 13 367855) = some ⟨13, 2, 0, 706233, 367855, 813, 16384⟩ := by
  decide +kernel

theorem context_13_367855_706233 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367855 ⟨706233, by decide⟩ :=
  accepted_of_selected 13 367855 ⟨706233, by decide⟩ ⟨13, 2, 0, 706233, 367855, 813, 16384⟩
    (by decide) selected_cut_27976

theorem unmarked_context_12_91963_706234 : frontier 9 ⟨706234, by decide⟩
    (prefixCache 12 91963) (prefixPartial 12 91963) = false := by
  decide +kernel

theorem node_context_12_91963_706234 : EJMOriginalGlobalDAGData.nodes 9 ⟨706234, by decide⟩ =
    .split (coordinate 12) (![⟨706167, by decide⟩,⟨706208, by decide⟩,⟨706225, by decide⟩,⟨706233, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91963_706234 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91963 ⟨706234, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91963
    ⟨706234, by decide⟩ (by decide) (![⟨706167, by decide⟩,⟨706208, by decide⟩,⟨706225, by decide⟩,⟨706233, by decide⟩]) unmarked_context_12_91963_706234 node_context_12_91963_706234
  intro a
  fin_cases a
  · exact context_13_367852_706167
  · exact context_13_367853_706208
  · exact context_13_367854_706225
  · exact context_13_367855_706233

theorem unmarked_context_11_22990_706235 : frontier 10 ⟨706235, by decide⟩
    (prefixCache 11 22990) (prefixPartial 11 22990) = false := by
  decide +kernel

theorem node_context_11_22990_706235 : EJMOriginalGlobalDAGData.nodes 10 ⟨706235, by decide⟩ =
    .split (coordinate 11) (![⟨706015, by decide⟩,⟨706093, by decide⟩,⟨706163, by decide⟩,⟨706234, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22990_706235 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22990 ⟨706235, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22990
    ⟨706235, by decide⟩ (by decide) (![⟨706015, by decide⟩,⟨706093, by decide⟩,⟨706163, by decide⟩,⟨706234, by decide⟩]) unmarked_context_11_22990_706235 node_context_11_22990_706235
  intro a
  fin_cases a
  · exact context_12_91960_706015
  · exact context_12_91961_706093
  · exact context_12_91962_706163
  · exact context_12_91963_706234

theorem selected_cut_27977 : selected 9 ⟨706284, by decide⟩
    (prefixPartial 12 91964) = some ⟨12, 2, 0, 706284, 91964, 3829, 65536⟩ := by
  decide +kernel

theorem context_12_91964_706284 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91964 ⟨706284, by decide⟩ :=
  accepted_of_selected 12 91964 ⟨706284, by decide⟩ ⟨12, 2, 0, 706284, 91964, 3829, 65536⟩
    (by decide) selected_cut_27977

theorem selected_cut_27978 : selected 9 ⟨706341, by decide⟩
    (prefixPartial 12 91965) = some ⟨12, 2, 0, 706341, 91965, 4001, 65536⟩ := by
  decide +kernel

theorem context_12_91965_706341 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91965 ⟨706341, by decide⟩ :=
  accepted_of_selected 12 91965 ⟨706341, by decide⟩ ⟨12, 2, 0, 706341, 91965, 4001, 65536⟩
    (by decide) selected_cut_27978

theorem selected_cut_27979 : selected 9 ⟨706392, by decide⟩
    (prefixPartial 12 91966) = some ⟨12, 2, 0, 706392, 91966, 3693, 65536⟩ := by
  decide +kernel

theorem context_12_91966_706392 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91966 ⟨706392, by decide⟩ :=
  accepted_of_selected 12 91966 ⟨706392, by decide⟩ ⟨12, 2, 0, 706392, 91966, 3693, 65536⟩
    (by decide) selected_cut_27979

theorem selected_cut_27980 : selected 9 ⟨512556, by decide⟩
    (prefixPartial 12 91967) = some ⟨12, 1, 0, 512556, 91967, 1, 65536⟩ := by
  decide +kernel

theorem context_12_91967_512556 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91967 ⟨512556, by decide⟩ :=
  accepted_of_selected 12 91967 ⟨512556, by decide⟩ ⟨12, 1, 0, 512556, 91967, 1, 65536⟩
    (by decide) selected_cut_27980

theorem unmarked_context_11_22991_706393 : frontier 10 ⟨706393, by decide⟩
    (prefixCache 11 22991) (prefixPartial 11 22991) = false := by
  decide +kernel

theorem node_context_11_22991_706393 : EJMOriginalGlobalDAGData.nodes 10 ⟨706393, by decide⟩ =
    .split (coordinate 11) (![⟨706284, by decide⟩,⟨706341, by decide⟩,⟨706392, by decide⟩,⟨512556, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22991_706393 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22991 ⟨706393, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22991
    ⟨706393, by decide⟩ (by decide) (![⟨706284, by decide⟩,⟨706341, by decide⟩,⟨706392, by decide⟩,⟨512556, by decide⟩]) unmarked_context_11_22991_706393 node_context_11_22991_706393
  intro a
  fin_cases a
  · exact context_12_91964_706284
  · exact context_12_91965_706341
  · exact context_12_91966_706392
  · exact context_12_91967_512556

theorem unmarked_context_10_5747_706394 : frontier 11 ⟨706394, by decide⟩
    (prefixCache 10 5747) (prefixPartial 10 5747) = false := by
  decide +kernel

theorem node_context_10_5747_706394 : EJMOriginalGlobalDAGData.nodes 11 ⟨706394, by decide⟩ =
    .split (coordinate 10) (![⟨705718, by decide⟩,⟨705949, by decide⟩,⟨706235, by decide⟩,⟨706393, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5747_706394 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5747 ⟨706394, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5747
    ⟨706394, by decide⟩ (by decide) (![⟨705718, by decide⟩,⟨705949, by decide⟩,⟨706235, by decide⟩,⟨706393, by decide⟩]) unmarked_context_10_5747_706394 node_context_10_5747_706394
  intro a
  fin_cases a
  · exact context_11_22988_705718
  · exact context_11_22989_705949
  · exact context_11_22990_706235
  · exact context_11_22991_706393

theorem unmarked_context_9_1436_706395 : frontier 12 ⟨706395, by decide⟩
    (prefixCache 9 1436) (prefixPartial 9 1436) = false := by
  decide +kernel

theorem node_context_9_1436_706395 : EJMOriginalGlobalDAGData.nodes 12 ⟨706395, by decide⟩ =
    .split (coordinate 9) (![⟨703139, by decide⟩,⟨704335, by decide⟩,⟨705467, by decide⟩,⟨706394, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1436_706395 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1436 ⟨706395, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1436
    ⟨706395, by decide⟩ (by decide) (![⟨703139, by decide⟩,⟨704335, by decide⟩,⟨705467, by decide⟩,⟨706394, by decide⟩]) unmarked_context_9_1436_706395 node_context_9_1436_706395
  intro a
  fin_cases a
  · exact context_10_5744_703139
  · exact context_10_5745_704335
  · exact context_10_5746_705467
  · exact context_10_5747_706394

theorem selected_cut_27981 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 367872) = some ⟨13, 1, 0, 3444, 367872, 1, 16384⟩ := by
  decide +kernel

theorem context_13_367872_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367872 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 367872 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 367872, 1, 16384⟩
    (by decide) selected_cut_27981

theorem selected_cut_27982 : selected 8 ⟨706437, by decide⟩
    (prefixPartial 13 367873) = some ⟨13, 2, 0, 706437, 367873, 2321, 16384⟩ := by
  decide +kernel

theorem context_13_367873_706437 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367873 ⟨706437, by decide⟩ :=
  accepted_of_selected 13 367873 ⟨706437, by decide⟩ ⟨13, 2, 0, 706437, 367873, 2321, 16384⟩
    (by decide) selected_cut_27982

theorem selected_cut_27983 : selected 8 ⟨706453, by decide⟩
    (prefixPartial 13 367874) = some ⟨13, 2, 0, 706453, 367874, 1209, 16384⟩ := by
  decide +kernel

theorem context_13_367874_706453 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367874 ⟨706453, by decide⟩ :=
  accepted_of_selected 13 367874 ⟨706453, by decide⟩ ⟨13, 2, 0, 706453, 367874, 1209, 16384⟩
    (by decide) selected_cut_27983

theorem selected_cut_27984 : selected 8 ⟨706458, by decide⟩
    (prefixPartial 13 367875) = some ⟨13, 2, 0, 706458, 367875, 573, 16384⟩ := by
  decide +kernel

theorem context_13_367875_706458 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367875 ⟨706458, by decide⟩ :=
  accepted_of_selected 13 367875 ⟨706458, by decide⟩ ⟨13, 2, 0, 706458, 367875, 573, 16384⟩
    (by decide) selected_cut_27984

theorem unmarked_context_12_91968_706459 : frontier 9 ⟨706459, by decide⟩
    (prefixCache 12 91968) (prefixPartial 12 91968) = false := by
  decide +kernel

theorem node_context_12_91968_706459 : EJMOriginalGlobalDAGData.nodes 9 ⟨706459, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨706437, by decide⟩,⟨706453, by decide⟩,⟨706458, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91968_706459 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91968 ⟨706459, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91968
    ⟨706459, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨706437, by decide⟩,⟨706453, by decide⟩,⟨706458, by decide⟩]) unmarked_context_12_91968_706459 node_context_12_91968_706459
  intro a
  fin_cases a
  · exact context_13_367872_3444
  · exact context_13_367873_706437
  · exact context_13_367874_706453
  · exact context_13_367875_706458

theorem selected_cut_27985 : selected 9 ⟨170504, by decide⟩
    (prefixPartial 12 91969) = some ⟨12, 1, 0, 170504, 91969, 1, 65536⟩ := by
  decide +kernel

theorem context_12_91969_170504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91969 ⟨170504, by decide⟩ :=
  accepted_of_selected 12 91969 ⟨170504, by decide⟩ ⟨12, 1, 0, 170504, 91969, 1, 65536⟩
    (by decide) selected_cut_27985

theorem selected_cut_27986 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 367880) = some ⟨13, 1, 0, 3444, 367880, 1, 16384⟩ := by
  decide +kernel

theorem context_13_367880_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367880 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 367880 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 367880, 1, 16384⟩
    (by decide) selected_cut_27986

theorem selected_cut_27987 : selected 8 ⟨706514, by decide⟩
    (prefixPartial 13 367881) = some ⟨13, 2, 0, 706514, 367881, 2501, 16384⟩ := by
  decide +kernel

theorem context_13_367881_706514 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367881 ⟨706514, by decide⟩ :=
  accepted_of_selected 13 367881 ⟨706514, by decide⟩ ⟨13, 2, 0, 706514, 367881, 2501, 16384⟩
    (by decide) selected_cut_27987

theorem selected_cut_27988 : selected 8 ⟨706535, by decide⟩
    (prefixPartial 13 367882) = some ⟨13, 2, 0, 706535, 367882, 1421, 16384⟩ := by
  decide +kernel

theorem context_13_367882_706535 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367882 ⟨706535, by decide⟩ :=
  accepted_of_selected 13 367882 ⟨706535, by decide⟩ ⟨13, 2, 0, 706535, 367882, 1421, 16384⟩
    (by decide) selected_cut_27988

theorem selected_cut_27989 : selected 8 ⟨706539, by decide⟩
    (prefixPartial 13 367883) = some ⟨13, 2, 0, 706539, 367883, 537, 16384⟩ := by
  decide +kernel

theorem context_13_367883_706539 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367883 ⟨706539, by decide⟩ :=
  accepted_of_selected 13 367883 ⟨706539, by decide⟩ ⟨13, 2, 0, 706539, 367883, 537, 16384⟩
    (by decide) selected_cut_27989

theorem unmarked_context_12_91970_706540 : frontier 9 ⟨706540, by decide⟩
    (prefixCache 12 91970) (prefixPartial 12 91970) = false := by
  decide +kernel

theorem node_context_12_91970_706540 : EJMOriginalGlobalDAGData.nodes 9 ⟨706540, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨706514, by decide⟩,⟨706535, by decide⟩,⟨706539, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91970_706540 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91970 ⟨706540, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91970
    ⟨706540, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨706514, by decide⟩,⟨706535, by decide⟩,⟨706539, by decide⟩]) unmarked_context_12_91970_706540 node_context_12_91970_706540
  intro a
  fin_cases a
  · exact context_13_367880_3444
  · exact context_13_367881_706514
  · exact context_13_367882_706535
  · exact context_13_367883_706539

theorem selected_cut_27990 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 367884) = some ⟨13, 1, 0, 3444, 367884, 1, 16384⟩ := by
  decide +kernel

theorem context_13_367884_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367884 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 367884 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 367884, 1, 16384⟩
    (by decide) selected_cut_27990

theorem selected_cut_27991 : selected 8 ⟨706586, by decide⟩
    (prefixPartial 13 367885) = some ⟨13, 2, 0, 706586, 367885, 2397, 16384⟩ := by
  decide +kernel

theorem context_13_367885_706586 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367885 ⟨706586, by decide⟩ :=
  accepted_of_selected 13 367885 ⟨706586, by decide⟩ ⟨13, 2, 0, 706586, 367885, 2397, 16384⟩
    (by decide) selected_cut_27991

theorem selected_cut_27992 : selected 8 ⟨706603, by decide⟩
    (prefixPartial 13 367886) = some ⟨13, 2, 0, 706603, 367886, 1309, 16384⟩ := by
  decide +kernel

theorem context_13_367886_706603 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367886 ⟨706603, by decide⟩ :=
  accepted_of_selected 13 367886 ⟨706603, by decide⟩ ⟨13, 2, 0, 706603, 367886, 1309, 16384⟩
    (by decide) selected_cut_27992

theorem selected_cut_27993 : selected 8 ⟨706610, by decide⟩
    (prefixPartial 13 367887) = some ⟨13, 2, 0, 706610, 367887, 473, 16384⟩ := by
  decide +kernel

theorem context_13_367887_706610 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367887 ⟨706610, by decide⟩ :=
  accepted_of_selected 13 367887 ⟨706610, by decide⟩ ⟨13, 2, 0, 706610, 367887, 473, 16384⟩
    (by decide) selected_cut_27993

theorem unmarked_context_12_91971_706611 : frontier 9 ⟨706611, by decide⟩
    (prefixCache 12 91971) (prefixPartial 12 91971) = false := by
  decide +kernel

theorem node_context_12_91971_706611 : EJMOriginalGlobalDAGData.nodes 9 ⟨706611, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨706586, by decide⟩,⟨706603, by decide⟩,⟨706610, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91971_706611 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91971 ⟨706611, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91971
    ⟨706611, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨706586, by decide⟩,⟨706603, by decide⟩,⟨706610, by decide⟩]) unmarked_context_12_91971_706611 node_context_12_91971_706611
  intro a
  fin_cases a
  · exact context_13_367884_3444
  · exact context_13_367885_706586
  · exact context_13_367886_706603
  · exact context_13_367887_706610

theorem unmarked_context_11_22992_706612 : frontier 10 ⟨706612, by decide⟩
    (prefixCache 11 22992) (prefixPartial 11 22992) = false := by
  decide +kernel

theorem node_context_11_22992_706612 : EJMOriginalGlobalDAGData.nodes 10 ⟨706612, by decide⟩ =
    .split (coordinate 11) (![⟨706459, by decide⟩,⟨170504, by decide⟩,⟨706540, by decide⟩,⟨706611, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22992_706612 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22992 ⟨706612, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22992
    ⟨706612, by decide⟩ (by decide) (![⟨706459, by decide⟩,⟨170504, by decide⟩,⟨706540, by decide⟩,⟨706611, by decide⟩]) unmarked_context_11_22992_706612 node_context_11_22992_706612
  intro a
  fin_cases a
  · exact context_12_91968_706459
  · exact context_12_91969_170504
  · exact context_12_91970_706540
  · exact context_12_91971_706611

theorem selected_cut_27994 : selected 9 ⟨706666, by decide⟩
    (prefixPartial 12 91972) = some ⟨12, 2, 0, 706666, 91972, 3657, 65536⟩ := by
  decide +kernel

theorem context_12_91972_706666 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91972 ⟨706666, by decide⟩ :=
  accepted_of_selected 12 91972 ⟨706666, by decide⟩ ⟨12, 2, 0, 706666, 91972, 3657, 65536⟩
    (by decide) selected_cut_27994

theorem selected_cut_27995 : selected 9 ⟨170504, by decide⟩
    (prefixPartial 12 91973) = some ⟨12, 1, 0, 170504, 91973, 1, 65536⟩ := by
  decide +kernel

theorem context_12_91973_170504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91973 ⟨170504, by decide⟩ :=
  accepted_of_selected 12 91973 ⟨170504, by decide⟩ ⟨12, 1, 0, 170504, 91973, 1, 65536⟩
    (by decide) selected_cut_27995

theorem selected_cut_27996 : selected 9 ⟨706729, by decide⟩
    (prefixPartial 12 91974) = some ⟨12, 2, 0, 706729, 91974, 3677, 65536⟩ := by
  decide +kernel

theorem context_12_91974_706729 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91974 ⟨706729, by decide⟩ :=
  accepted_of_selected 12 91974 ⟨706729, by decide⟩ ⟨12, 2, 0, 706729, 91974, 3677, 65536⟩
    (by decide) selected_cut_27996

theorem selected_cut_27997 : selected 9 ⟨706790, by decide⟩
    (prefixPartial 12 91975) = some ⟨12, 2, 0, 706790, 91975, 3653, 65536⟩ := by
  decide +kernel

theorem context_12_91975_706790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91975 ⟨706790, by decide⟩ :=
  accepted_of_selected 12 91975 ⟨706790, by decide⟩ ⟨12, 2, 0, 706790, 91975, 3653, 65536⟩
    (by decide) selected_cut_27997

theorem unmarked_context_11_22993_706791 : frontier 10 ⟨706791, by decide⟩
    (prefixCache 11 22993) (prefixPartial 11 22993) = false := by
  decide +kernel

theorem node_context_11_22993_706791 : EJMOriginalGlobalDAGData.nodes 10 ⟨706791, by decide⟩ =
    .split (coordinate 11) (![⟨706666, by decide⟩,⟨170504, by decide⟩,⟨706729, by decide⟩,⟨706790, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22993_706791 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22993 ⟨706791, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22993
    ⟨706791, by decide⟩ (by decide) (![⟨706666, by decide⟩,⟨170504, by decide⟩,⟨706729, by decide⟩,⟨706790, by decide⟩]) unmarked_context_11_22993_706791 node_context_11_22993_706791
  intro a
  fin_cases a
  · exact context_12_91972_706666
  · exact context_12_91973_170504
  · exact context_12_91974_706729
  · exact context_12_91975_706790

theorem selected_cut_27998 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 367904) = some ⟨13, 1, 0, 3444, 367904, 1, 16384⟩ := by
  decide +kernel

theorem context_13_367904_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367904 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 367904 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 367904, 1, 16384⟩
    (by decide) selected_cut_27998

theorem selected_cut_27999 : selected 8 ⟨706827, by decide⟩
    (prefixPartial 13 367905) = some ⟨13, 2, 0, 706827, 367905, 2021, 16384⟩ := by
  decide +kernel

theorem context_13_367905_706827 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367905 ⟨706827, by decide⟩ :=
  accepted_of_selected 13 367905 ⟨706827, by decide⟩ ⟨13, 2, 0, 706827, 367905, 2021, 16384⟩
    (by decide) selected_cut_27999

theorem selected_cut_28000 : selected 8 ⟨706846, by decide⟩
    (prefixPartial 13 367906) = some ⟨13, 2, 0, 706846, 367906, 1365, 16384⟩ := by
  decide +kernel

theorem context_13_367906_706846 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367906 ⟨706846, by decide⟩ :=
  accepted_of_selected 13 367906 ⟨706846, by decide⟩ ⟨13, 2, 0, 706846, 367906, 1365, 16384⟩
    (by decide) selected_cut_28000

theorem selected_cut_28001 : selected 8 ⟨706852, by decide⟩
    (prefixPartial 13 367907) = some ⟨13, 2, 0, 706852, 367907, 717, 16384⟩ := by
  decide +kernel

theorem context_13_367907_706852 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367907 ⟨706852, by decide⟩ :=
  accepted_of_selected 13 367907 ⟨706852, by decide⟩ ⟨13, 2, 0, 706852, 367907, 717, 16384⟩
    (by decide) selected_cut_28001

theorem unmarked_context_12_91976_706853 : frontier 9 ⟨706853, by decide⟩
    (prefixCache 12 91976) (prefixPartial 12 91976) = false := by
  decide +kernel

theorem node_context_12_91976_706853 : EJMOriginalGlobalDAGData.nodes 9 ⟨706853, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨706827, by decide⟩,⟨706846, by decide⟩,⟨706852, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91976_706853 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91976 ⟨706853, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91976
    ⟨706853, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨706827, by decide⟩,⟨706846, by decide⟩,⟨706852, by decide⟩]) unmarked_context_12_91976_706853 node_context_12_91976_706853
  intro a
  fin_cases a
  · exact context_13_367904_3444
  · exact context_13_367905_706827
  · exact context_13_367906_706846
  · exact context_13_367907_706852

theorem selected_cut_28002 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 367908) = some ⟨13, 1, 0, 3444, 367908, 1, 16384⟩ := by
  decide +kernel

theorem context_13_367908_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367908 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 367908 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 367908, 1, 16384⟩
    (by decide) selected_cut_28002

theorem selected_cut_28003 : selected 8 ⟨706920, by decide⟩
    (prefixPartial 13 367909) = some ⟨13, 2, 0, 706920, 367909, 2993, 16384⟩ := by
  decide +kernel

theorem context_13_367909_706920 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367909 ⟨706920, by decide⟩ :=
  accepted_of_selected 13 367909 ⟨706920, by decide⟩ ⟨13, 2, 0, 706920, 367909, 2993, 16384⟩
    (by decide) selected_cut_28003

theorem selected_cut_28004 : selected 8 ⟨706959, by decide⟩
    (prefixPartial 13 367910) = some ⟨13, 2, 0, 706959, 367910, 2289, 16384⟩ := by
  decide +kernel

theorem context_13_367910_706959 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367910 ⟨706959, by decide⟩ :=
  accepted_of_selected 13 367910 ⟨706959, by decide⟩ ⟨13, 2, 0, 706959, 367910, 2289, 16384⟩
    (by decide) selected_cut_28004

theorem selected_cut_28005 : selected 8 ⟨706971, by decide⟩
    (prefixPartial 13 367911) = some ⟨13, 2, 0, 706971, 367911, 961, 16384⟩ := by
  decide +kernel

theorem context_13_367911_706971 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367911 ⟨706971, by decide⟩ :=
  accepted_of_selected 13 367911 ⟨706971, by decide⟩ ⟨13, 2, 0, 706971, 367911, 961, 16384⟩
    (by decide) selected_cut_28005

theorem unmarked_context_12_91977_706972 : frontier 9 ⟨706972, by decide⟩
    (prefixCache 12 91977) (prefixPartial 12 91977) = false := by
  decide +kernel

theorem node_context_12_91977_706972 : EJMOriginalGlobalDAGData.nodes 9 ⟨706972, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨706920, by decide⟩,⟨706959, by decide⟩,⟨706971, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91977_706972 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91977 ⟨706972, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91977
    ⟨706972, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨706920, by decide⟩,⟨706959, by decide⟩,⟨706971, by decide⟩]) unmarked_context_12_91977_706972 node_context_12_91977_706972
  intro a
  fin_cases a
  · exact context_13_367908_3444
  · exact context_13_367909_706920
  · exact context_13_367910_706959
  · exact context_13_367911_706971

theorem selected_cut_28006 : selected 9 ⟨707030, by decide⟩
    (prefixPartial 12 91978) = some ⟨12, 2, 0, 707030, 91978, 3929, 65536⟩ := by
  decide +kernel

theorem context_12_91978_707030 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91978 ⟨707030, by decide⟩ :=
  accepted_of_selected 12 91978 ⟨707030, by decide⟩ ⟨12, 2, 0, 707030, 91978, 3929, 65536⟩
    (by decide) selected_cut_28006

theorem selected_cut_28007 : selected 9 ⟨707095, by decide⟩
    (prefixPartial 12 91979) = some ⟨12, 2, 0, 707095, 91979, 3925, 65536⟩ := by
  decide +kernel

theorem context_12_91979_707095 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91979 ⟨707095, by decide⟩ :=
  accepted_of_selected 12 91979 ⟨707095, by decide⟩ ⟨12, 2, 0, 707095, 91979, 3925, 65536⟩
    (by decide) selected_cut_28007

theorem unmarked_context_11_22994_707096 : frontier 10 ⟨707096, by decide⟩
    (prefixCache 11 22994) (prefixPartial 11 22994) = false := by
  decide +kernel

theorem node_context_11_22994_707096 : EJMOriginalGlobalDAGData.nodes 10 ⟨707096, by decide⟩ =
    .split (coordinate 11) (![⟨706853, by decide⟩,⟨706972, by decide⟩,⟨707030, by decide⟩,⟨707095, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22994_707096 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22994 ⟨707096, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22994
    ⟨707096, by decide⟩ (by decide) (![⟨706853, by decide⟩,⟨706972, by decide⟩,⟨707030, by decide⟩,⟨707095, by decide⟩]) unmarked_context_11_22994_707096 node_context_11_22994_707096
  intro a
  fin_cases a
  · exact context_12_91976_706853
  · exact context_12_91977_706972
  · exact context_12_91978_707030
  · exact context_12_91979_707095

theorem selected_cut_28008 : selected 9 ⟨707140, by decide⟩
    (prefixPartial 12 91980) = some ⟨12, 2, 0, 707140, 91980, 3217, 65536⟩ := by
  decide +kernel

theorem context_12_91980_707140 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91980 ⟨707140, by decide⟩ :=
  accepted_of_selected 12 91980 ⟨707140, by decide⟩ ⟨12, 2, 0, 707140, 91980, 3217, 65536⟩
    (by decide) selected_cut_28008

theorem selected_cut_28009 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 367924) = some ⟨13, 1, 0, 3444, 367924, 1, 16384⟩ := by
  decide +kernel

theorem context_13_367924_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367924 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 367924 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 367924, 1, 16384⟩
    (by decide) selected_cut_28009

theorem selected_cut_28010 : selected 8 ⟨707195, by decide⟩
    (prefixPartial 13 367925) = some ⟨13, 2, 0, 707195, 367925, 2281, 16384⟩ := by
  decide +kernel

theorem context_13_367925_707195 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367925 ⟨707195, by decide⟩ :=
  accepted_of_selected 13 367925 ⟨707195, by decide⟩ ⟨13, 2, 0, 707195, 367925, 2281, 16384⟩
    (by decide) selected_cut_28010

theorem selected_cut_28011 : selected 8 ⟨707228, by decide⟩
    (prefixPartial 13 367926) = some ⟨13, 2, 0, 707228, 367926, 1893, 16384⟩ := by
  decide +kernel

theorem context_13_367926_707228 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367926 ⟨707228, by decide⟩ :=
  accepted_of_selected 13 367926 ⟨707228, by decide⟩ ⟨13, 2, 0, 707228, 367926, 1893, 16384⟩
    (by decide) selected_cut_28011

theorem selected_cut_28012 : selected 8 ⟨707238, by decide⟩
    (prefixPartial 13 367927) = some ⟨13, 2, 0, 707238, 367927, 753, 16384⟩ := by
  decide +kernel

theorem context_13_367927_707238 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367927 ⟨707238, by decide⟩ :=
  accepted_of_selected 13 367927 ⟨707238, by decide⟩ ⟨13, 2, 0, 707238, 367927, 753, 16384⟩
    (by decide) selected_cut_28012

theorem unmarked_context_12_91981_707239 : frontier 9 ⟨707239, by decide⟩
    (prefixCache 12 91981) (prefixPartial 12 91981) = false := by
  decide +kernel

theorem node_context_12_91981_707239 : EJMOriginalGlobalDAGData.nodes 9 ⟨707239, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨707195, by decide⟩,⟨707228, by decide⟩,⟨707238, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91981_707239 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91981 ⟨707239, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91981
    ⟨707239, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨707195, by decide⟩,⟨707228, by decide⟩,⟨707238, by decide⟩]) unmarked_context_12_91981_707239 node_context_12_91981_707239
  intro a
  fin_cases a
  · exact context_13_367924_3444
  · exact context_13_367925_707195
  · exact context_13_367926_707228
  · exact context_13_367927_707238

theorem selected_cut_28013 : selected 9 ⟨707286, by decide⟩
    (prefixPartial 12 91982) = some ⟨12, 2, 0, 707286, 91982, 3109, 65536⟩ := by
  decide +kernel

theorem context_12_91982_707286 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91982 ⟨707286, by decide⟩ :=
  accepted_of_selected 12 91982 ⟨707286, by decide⟩ ⟨12, 2, 0, 707286, 91982, 3109, 65536⟩
    (by decide) selected_cut_28013

theorem selected_cut_28014 : selected 9 ⟨347191, by decide⟩
    (prefixPartial 12 91983) = some ⟨12, 1, 0, 347191, 91983, 1, 65536⟩ := by
  decide +kernel

theorem context_12_91983_347191 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91983 ⟨347191, by decide⟩ :=
  accepted_of_selected 12 91983 ⟨347191, by decide⟩ ⟨12, 1, 0, 347191, 91983, 1, 65536⟩
    (by decide) selected_cut_28014

theorem unmarked_context_11_22995_707287 : frontier 10 ⟨707287, by decide⟩
    (prefixCache 11 22995) (prefixPartial 11 22995) = false := by
  decide +kernel

theorem node_context_11_22995_707287 : EJMOriginalGlobalDAGData.nodes 10 ⟨707287, by decide⟩ =
    .split (coordinate 11) (![⟨707140, by decide⟩,⟨707239, by decide⟩,⟨707286, by decide⟩,⟨347191, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22995_707287 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22995 ⟨707287, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22995
    ⟨707287, by decide⟩ (by decide) (![⟨707140, by decide⟩,⟨707239, by decide⟩,⟨707286, by decide⟩,⟨347191, by decide⟩]) unmarked_context_11_22995_707287 node_context_11_22995_707287
  intro a
  fin_cases a
  · exact context_12_91980_707140
  · exact context_12_91981_707239
  · exact context_12_91982_707286
  · exact context_12_91983_347191

theorem unmarked_context_10_5748_707288 : frontier 11 ⟨707288, by decide⟩
    (prefixCache 10 5748) (prefixPartial 10 5748) = false := by
  decide +kernel

theorem node_context_10_5748_707288 : EJMOriginalGlobalDAGData.nodes 11 ⟨707288, by decide⟩ =
    .split (coordinate 10) (![⟨706612, by decide⟩,⟨706791, by decide⟩,⟨707096, by decide⟩,⟨707287, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5748_707288 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5748 ⟨707288, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5748
    ⟨707288, by decide⟩ (by decide) (![⟨706612, by decide⟩,⟨706791, by decide⟩,⟨707096, by decide⟩,⟨707287, by decide⟩]) unmarked_context_10_5748_707288 node_context_10_5748_707288
  intro a
  fin_cases a
  · exact context_11_22992_706612
  · exact context_11_22993_706791
  · exact context_11_22994_707096
  · exact context_11_22995_707287

theorem selected_cut_28015 : selected 9 ⟨707334, by decide⟩
    (prefixPartial 12 91984) = some ⟨12, 2, 0, 707334, 91984, 3377, 65536⟩ := by
  decide +kernel

theorem context_12_91984_707334 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91984 ⟨707334, by decide⟩ :=
  accepted_of_selected 12 91984 ⟨707334, by decide⟩ ⟨12, 2, 0, 707334, 91984, 3377, 65536⟩
    (by decide) selected_cut_28015

theorem selected_cut_28016 : selected 9 ⟨642341, by decide⟩
    (prefixPartial 12 91985) = some ⟨12, 1, 0, 642341, 91985, 1, 65536⟩ := by
  decide +kernel

theorem context_12_91985_642341 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91985 ⟨642341, by decide⟩ :=
  accepted_of_selected 12 91985 ⟨642341, by decide⟩ ⟨12, 1, 0, 642341, 91985, 1, 65536⟩
    (by decide) selected_cut_28016

theorem selected_cut_28017 : selected 9 ⟨707385, by decide⟩
    (prefixPartial 12 91986) = some ⟨12, 2, 0, 707385, 91986, 3841, 65536⟩ := by
  decide +kernel

theorem context_12_91986_707385 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91986 ⟨707385, by decide⟩ :=
  accepted_of_selected 12 91986 ⟨707385, by decide⟩ ⟨12, 2, 0, 707385, 91986, 3841, 65536⟩
    (by decide) selected_cut_28017

theorem selected_cut_28018 : selected 9 ⟨707428, by decide⟩
    (prefixPartial 12 91987) = some ⟨12, 2, 0, 707428, 91987, 3421, 65536⟩ := by
  decide +kernel

theorem context_12_91987_707428 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91987 ⟨707428, by decide⟩ :=
  accepted_of_selected 12 91987 ⟨707428, by decide⟩ ⟨12, 2, 0, 707428, 91987, 3421, 65536⟩
    (by decide) selected_cut_28018

theorem unmarked_context_11_22996_707429 : frontier 10 ⟨707429, by decide⟩
    (prefixCache 11 22996) (prefixPartial 11 22996) = false := by
  decide +kernel

theorem node_context_11_22996_707429 : EJMOriginalGlobalDAGData.nodes 10 ⟨707429, by decide⟩ =
    .split (coordinate 11) (![⟨707334, by decide⟩,⟨642341, by decide⟩,⟨707385, by decide⟩,⟨707428, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22996_707429 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22996 ⟨707429, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22996
    ⟨707429, by decide⟩ (by decide) (![⟨707334, by decide⟩,⟨642341, by decide⟩,⟨707385, by decide⟩,⟨707428, by decide⟩]) unmarked_context_11_22996_707429 node_context_11_22996_707429
  intro a
  fin_cases a
  · exact context_12_91984_707334
  · exact context_12_91985_642341
  · exact context_12_91986_707385
  · exact context_12_91987_707428

theorem selected_cut_28019 : selected 10 ⟨451541, by decide⟩
    (prefixPartial 11 22997) = some ⟨11, 1, 0, 451541, 22997, 1, 262144⟩ := by
  decide +kernel

theorem context_11_22997_451541 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22997 ⟨451541, by decide⟩ :=
  accepted_of_selected 11 22997 ⟨451541, by decide⟩ ⟨11, 1, 0, 451541, 22997, 1, 262144⟩
    (by decide) selected_cut_28019

theorem selected_cut_28020 : selected 9 ⟨707475, by decide⟩
    (prefixPartial 12 91992) = some ⟨12, 2, 0, 707475, 91992, 3365, 65536⟩ := by
  decide +kernel

theorem context_12_91992_707475 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91992 ⟨707475, by decide⟩ :=
  accepted_of_selected 12 91992 ⟨707475, by decide⟩ ⟨12, 2, 0, 707475, 91992, 3365, 65536⟩
    (by decide) selected_cut_28020

theorem selected_cut_28021 : selected 9 ⟨642341, by decide⟩
    (prefixPartial 12 91993) = some ⟨12, 1, 0, 642341, 91993, 1, 65536⟩ := by
  decide +kernel

theorem context_12_91993_642341 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91993 ⟨642341, by decide⟩ :=
  accepted_of_selected 12 91993 ⟨642341, by decide⟩ ⟨12, 1, 0, 642341, 91993, 1, 65536⟩
    (by decide) selected_cut_28021

theorem selected_cut_28022 : selected 9 ⟨707522, by decide⟩
    (prefixPartial 12 91994) = some ⟨12, 2, 0, 707522, 91994, 3349, 65536⟩ := by
  decide +kernel

theorem context_12_91994_707522 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91994 ⟨707522, by decide⟩ :=
  accepted_of_selected 12 91994 ⟨707522, by decide⟩ ⟨12, 2, 0, 707522, 91994, 3349, 65536⟩
    (by decide) selected_cut_28022

theorem selected_cut_28023 : selected 9 ⟨707566, by decide⟩
    (prefixPartial 12 91995) = some ⟨12, 2, 0, 707566, 91995, 3217, 65536⟩ := by
  decide +kernel

theorem context_12_91995_707566 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91995 ⟨707566, by decide⟩ :=
  accepted_of_selected 12 91995 ⟨707566, by decide⟩ ⟨12, 2, 0, 707566, 91995, 3217, 65536⟩
    (by decide) selected_cut_28023

theorem unmarked_context_11_22998_707567 : frontier 10 ⟨707567, by decide⟩
    (prefixCache 11 22998) (prefixPartial 11 22998) = false := by
  decide +kernel

theorem node_context_11_22998_707567 : EJMOriginalGlobalDAGData.nodes 10 ⟨707567, by decide⟩ =
    .split (coordinate 11) (![⟨707475, by decide⟩,⟨642341, by decide⟩,⟨707522, by decide⟩,⟨707566, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22998_707567 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22998 ⟨707567, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22998
    ⟨707567, by decide⟩ (by decide) (![⟨707475, by decide⟩,⟨642341, by decide⟩,⟨707522, by decide⟩,⟨707566, by decide⟩]) unmarked_context_11_22998_707567 node_context_11_22998_707567
  intro a
  fin_cases a
  · exact context_12_91992_707475
  · exact context_12_91993_642341
  · exact context_12_91994_707522
  · exact context_12_91995_707566

theorem selected_cut_28024 : selected 9 ⟨707605, by decide⟩
    (prefixPartial 12 91996) = some ⟨12, 2, 0, 707605, 91996, 2769, 65536⟩ := by
  decide +kernel

theorem context_12_91996_707605 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91996 ⟨707605, by decide⟩ :=
  accepted_of_selected 12 91996 ⟨707605, by decide⟩ ⟨12, 2, 0, 707605, 91996, 2769, 65536⟩
    (by decide) selected_cut_28024

theorem selected_cut_28025 : selected 9 ⟨642341, by decide⟩
    (prefixPartial 12 91997) = some ⟨12, 1, 0, 642341, 91997, 1, 65536⟩ := by
  decide +kernel

theorem context_12_91997_642341 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91997 ⟨642341, by decide⟩ :=
  accepted_of_selected 12 91997 ⟨642341, by decide⟩ ⟨12, 1, 0, 642341, 91997, 1, 65536⟩
    (by decide) selected_cut_28025

theorem selected_cut_28026 : selected 9 ⟨707639, by decide⟩
    (prefixPartial 12 91998) = some ⟨12, 2, 0, 707639, 91998, 2777, 65536⟩ := by
  decide +kernel

theorem context_12_91998_707639 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91998 ⟨707639, by decide⟩ :=
  accepted_of_selected 12 91998 ⟨707639, by decide⟩ ⟨12, 2, 0, 707639, 91998, 2777, 65536⟩
    (by decide) selected_cut_28026

theorem selected_cut_28027 : selected 9 ⟨345284, by decide⟩
    (prefixPartial 12 91999) = some ⟨12, 1, 0, 345284, 91999, 1, 65536⟩ := by
  decide +kernel

theorem context_12_91999_345284 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91999 ⟨345284, by decide⟩ :=
  accepted_of_selected 12 91999 ⟨345284, by decide⟩ ⟨12, 1, 0, 345284, 91999, 1, 65536⟩
    (by decide) selected_cut_28027

theorem unmarked_context_11_22999_707640 : frontier 10 ⟨707640, by decide⟩
    (prefixCache 11 22999) (prefixPartial 11 22999) = false := by
  decide +kernel

theorem node_context_11_22999_707640 : EJMOriginalGlobalDAGData.nodes 10 ⟨707640, by decide⟩ =
    .split (coordinate 11) (![⟨707605, by decide⟩,⟨642341, by decide⟩,⟨707639, by decide⟩,⟨345284, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22999_707640 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22999 ⟨707640, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22999
    ⟨707640, by decide⟩ (by decide) (![⟨707605, by decide⟩,⟨642341, by decide⟩,⟨707639, by decide⟩,⟨345284, by decide⟩]) unmarked_context_11_22999_707640 node_context_11_22999_707640
  intro a
  fin_cases a
  · exact context_12_91996_707605
  · exact context_12_91997_642341
  · exact context_12_91998_707639
  · exact context_12_91999_345284

theorem unmarked_context_10_5749_707641 : frontier 11 ⟨707641, by decide⟩
    (prefixCache 10 5749) (prefixPartial 10 5749) = false := by
  decide +kernel

theorem node_context_10_5749_707641 : EJMOriginalGlobalDAGData.nodes 11 ⟨707641, by decide⟩ =
    .split (coordinate 10) (![⟨707429, by decide⟩,⟨451541, by decide⟩,⟨707567, by decide⟩,⟨707640, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5749_707641 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5749 ⟨707641, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5749
    ⟨707641, by decide⟩ (by decide) (![⟨707429, by decide⟩,⟨451541, by decide⟩,⟨707567, by decide⟩,⟨707640, by decide⟩]) unmarked_context_10_5749_707641 node_context_10_5749_707641
  intro a
  fin_cases a
  · exact context_11_22996_707429
  · exact context_11_22997_451541
  · exact context_11_22998_707567
  · exact context_11_22999_707640

theorem selected_cut_28028 : selected 9 ⟨707691, by decide⟩
    (prefixPartial 12 92000) = some ⟨12, 2, 0, 707691, 92000, 3257, 65536⟩ := by
  decide +kernel

theorem context_12_92000_707691 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92000 ⟨707691, by decide⟩ :=
  accepted_of_selected 12 92000 ⟨707691, by decide⟩ ⟨12, 2, 0, 707691, 92000, 3257, 65536⟩
    (by decide) selected_cut_28028

theorem selected_cut_28029 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 368004) = some ⟨13, 1, 0, 3444, 368004, 1, 16384⟩ := by
  decide +kernel

theorem context_13_368004_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 368004 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 368004 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 368004, 1, 16384⟩
    (by decide) selected_cut_28029

theorem selected_cut_28030 : selected 8 ⟨707735, by decide⟩
    (prefixPartial 13 368005) = some ⟨13, 2, 0, 707735, 368005, 1737, 16384⟩ := by
  decide +kernel

theorem context_13_368005_707735 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 368005 ⟨707735, by decide⟩ :=
  accepted_of_selected 13 368005 ⟨707735, by decide⟩ ⟨13, 2, 0, 707735, 368005, 1737, 16384⟩
    (by decide) selected_cut_28030

theorem selected_cut_28031 : selected 8 ⟨707763, by decide⟩
    (prefixPartial 13 368006) = some ⟨13, 2, 0, 707763, 368006, 2225, 16384⟩ := by
  decide +kernel

theorem context_13_368006_707763 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 368006 ⟨707763, by decide⟩ :=
  accepted_of_selected 13 368006 ⟨707763, by decide⟩ ⟨13, 2, 0, 707763, 368006, 2225, 16384⟩
    (by decide) selected_cut_28031

theorem selected_cut_28032 : selected 8 ⟨707775, by decide⟩
    (prefixPartial 13 368007) = some ⟨13, 2, 0, 707775, 368007, 897, 16384⟩ := by
  decide +kernel

theorem context_13_368007_707775 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 368007 ⟨707775, by decide⟩ :=
  accepted_of_selected 13 368007 ⟨707775, by decide⟩ ⟨13, 2, 0, 707775, 368007, 897, 16384⟩
    (by decide) selected_cut_28032

theorem unmarked_context_12_92001_707776 : frontier 9 ⟨707776, by decide⟩
    (prefixCache 12 92001) (prefixPartial 12 92001) = false := by
  decide +kernel

theorem node_context_12_92001_707776 : EJMOriginalGlobalDAGData.nodes 9 ⟨707776, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨707735, by decide⟩,⟨707763, by decide⟩,⟨707775, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_92001_707776 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92001 ⟨707776, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 92001
    ⟨707776, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨707735, by decide⟩,⟨707763, by decide⟩,⟨707775, by decide⟩]) unmarked_context_12_92001_707776 node_context_12_92001_707776
  intro a
  fin_cases a
  · exact context_13_368004_3444
  · exact context_13_368005_707735
  · exact context_13_368006_707763
  · exact context_13_368007_707775

theorem selected_cut_28033 : selected 9 ⟨707821, by decide⟩
    (prefixPartial 12 92002) = some ⟨12, 2, 0, 707821, 92002, 3337, 65536⟩ := by
  decide +kernel

theorem context_12_92002_707821 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92002 ⟨707821, by decide⟩ :=
  accepted_of_selected 12 92002 ⟨707821, by decide⟩ ⟨12, 2, 0, 707821, 92002, 3337, 65536⟩
    (by decide) selected_cut_28033

theorem selected_cut_28034 : selected 9 ⟨707859, by decide⟩
    (prefixPartial 12 92003) = some ⟨12, 2, 0, 707859, 92003, 2845, 65536⟩ := by
  decide +kernel

theorem context_12_92003_707859 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92003 ⟨707859, by decide⟩ :=
  accepted_of_selected 12 92003 ⟨707859, by decide⟩ ⟨12, 2, 0, 707859, 92003, 2845, 65536⟩
    (by decide) selected_cut_28034

theorem unmarked_context_11_23000_707860 : frontier 10 ⟨707860, by decide⟩
    (prefixCache 11 23000) (prefixPartial 11 23000) = false := by
  decide +kernel

theorem node_context_11_23000_707860 : EJMOriginalGlobalDAGData.nodes 10 ⟨707860, by decide⟩ =
    .split (coordinate 11) (![⟨707691, by decide⟩,⟨707776, by decide⟩,⟨707821, by decide⟩,⟨707859, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23000_707860 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23000 ⟨707860, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23000
    ⟨707860, by decide⟩ (by decide) (![⟨707691, by decide⟩,⟨707776, by decide⟩,⟨707821, by decide⟩,⟨707859, by decide⟩]) unmarked_context_11_23000_707860 node_context_11_23000_707860
  intro a
  fin_cases a
  · exact context_12_92000_707691
  · exact context_12_92001_707776
  · exact context_12_92002_707821
  · exact context_12_92003_707859

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
