/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover362
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_34850 : selected 10 ⟨1736, by decide⟩
    (prefixPartial 11 70739) = some ⟨11, 1, 0, 1736, 70739, 1, 262144⟩ := by
  decide +kernel

theorem context_11_70739_1736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70739 ⟨1736, by decide⟩ :=
  accepted_of_selected 11 70739 ⟨1736, by decide⟩ ⟨11, 1, 0, 1736, 70739, 1, 262144⟩
    (by decide) selected_cut_34850

theorem unmarked_context_10_17684_910666 : frontier 11 ⟨910666, by decide⟩
    (prefixCache 10 17684) (prefixPartial 10 17684) = false := by
  decide +kernel

theorem node_context_10_17684_910666 : EJMOriginalGlobalDAGData.nodes 11 ⟨910666, by decide⟩ =
    .split (coordinate 10) (![⟨907917, by decide⟩,⟨910569, by decide⟩,⟨910665, by decide⟩,⟨1736, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17684_910666 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17684 ⟨910666, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17684
    ⟨910666, by decide⟩ (by decide) (![⟨907917, by decide⟩,⟨910569, by decide⟩,⟨910665, by decide⟩,⟨1736, by decide⟩]) unmarked_context_10_17684_910666 node_context_10_17684_910666
  intro a
  fin_cases a
  · exact context_11_70736_907917
  · exact context_11_70737_910569
  · exact context_11_70738_910665
  · exact context_11_70739_1736

theorem selected_cut_34851 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 17685) = some ⟨10, 1, 0, 893098, 17685, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_17685_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17685 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 17685 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 17685, 1, 1048576⟩
    (by decide) selected_cut_34851

theorem selected_cut_34852 : selected 9 ⟨910686, by decide⟩
    (prefixPartial 12 282976) = some ⟨12, 2, 0, 910686, 282976, 1569, 65536⟩ := by
  decide +kernel

theorem context_12_282976_910686 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 282976 ⟨910686, by decide⟩ :=
  accepted_of_selected 12 282976 ⟨910686, by decide⟩ ⟨12, 2, 0, 910686, 282976, 1569, 65536⟩
    (by decide) selected_cut_34852

theorem selected_cut_34853 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 282977) = some ⟨12, 1, 0, 896706, 282977, 1, 65536⟩ := by
  decide +kernel

theorem context_12_282977_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 282977 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 282977 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 282977, 1, 65536⟩
    (by decide) selected_cut_34853

theorem selected_cut_34854 : selected 9 ⟨910714, by decide⟩
    (prefixPartial 12 282978) = some ⟨12, 2, 0, 910714, 282978, 1833, 65536⟩ := by
  decide +kernel

theorem context_12_282978_910714 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 282978 ⟨910714, by decide⟩ :=
  accepted_of_selected 12 282978 ⟨910714, by decide⟩ ⟨12, 2, 0, 910714, 282978, 1833, 65536⟩
    (by decide) selected_cut_34854

theorem selected_cut_34855 : selected 9 ⟨910734, by decide⟩
    (prefixPartial 12 282979) = some ⟨12, 2, 0, 910734, 282979, 1541, 65536⟩ := by
  decide +kernel

theorem context_12_282979_910734 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 282979 ⟨910734, by decide⟩ :=
  accepted_of_selected 12 282979 ⟨910734, by decide⟩ ⟨12, 2, 0, 910734, 282979, 1541, 65536⟩
    (by decide) selected_cut_34855

theorem unmarked_context_11_70744_910735 : frontier 10 ⟨910735, by decide⟩
    (prefixCache 11 70744) (prefixPartial 11 70744) = false := by
  decide +kernel

theorem node_context_11_70744_910735 : EJMOriginalGlobalDAGData.nodes 10 ⟨910735, by decide⟩ =
    .split (coordinate 11) (![⟨910686, by decide⟩,⟨896706, by decide⟩,⟨910714, by decide⟩,⟨910734, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_70744_910735 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70744 ⟨910735, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 70744
    ⟨910735, by decide⟩ (by decide) (![⟨910686, by decide⟩,⟨896706, by decide⟩,⟨910714, by decide⟩,⟨910734, by decide⟩]) unmarked_context_11_70744_910735 node_context_11_70744_910735
  intro a
  fin_cases a
  · exact context_12_282976_910686
  · exact context_12_282977_896706
  · exact context_12_282978_910714
  · exact context_12_282979_910734

theorem selected_cut_34856 : selected 9 ⟨910757, by decide⟩
    (prefixPartial 12 282980) = some ⟨12, 2, 0, 910757, 282980, 1421, 65536⟩ := by
  decide +kernel

theorem context_12_282980_910757 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 282980 ⟨910757, by decide⟩ :=
  accepted_of_selected 12 282980 ⟨910757, by decide⟩ ⟨12, 2, 0, 910757, 282980, 1421, 65536⟩
    (by decide) selected_cut_34856

theorem selected_cut_34857 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 282981) = some ⟨12, 1, 0, 896706, 282981, 1, 65536⟩ := by
  decide +kernel

theorem context_12_282981_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 282981 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 282981 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 282981, 1, 65536⟩
    (by decide) selected_cut_34857

theorem selected_cut_34858 : selected 9 ⟨910785, by decide⟩
    (prefixPartial 12 282982) = some ⟨12, 2, 0, 910785, 282982, 1509, 65536⟩ := by
  decide +kernel

theorem context_12_282982_910785 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 282982 ⟨910785, by decide⟩ :=
  accepted_of_selected 12 282982 ⟨910785, by decide⟩ ⟨12, 2, 0, 910785, 282982, 1509, 65536⟩
    (by decide) selected_cut_34858

theorem selected_cut_34859 : selected 9 ⟨910808, by decide⟩
    (prefixPartial 12 282983) = some ⟨12, 2, 0, 910808, 282983, 1313, 65536⟩ := by
  decide +kernel

theorem context_12_282983_910808 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 282983 ⟨910808, by decide⟩ :=
  accepted_of_selected 12 282983 ⟨910808, by decide⟩ ⟨12, 2, 0, 910808, 282983, 1313, 65536⟩
    (by decide) selected_cut_34859

theorem unmarked_context_11_70745_910809 : frontier 10 ⟨910809, by decide⟩
    (prefixCache 11 70745) (prefixPartial 11 70745) = false := by
  decide +kernel

theorem node_context_11_70745_910809 : EJMOriginalGlobalDAGData.nodes 10 ⟨910809, by decide⟩ =
    .split (coordinate 11) (![⟨910757, by decide⟩,⟨896706, by decide⟩,⟨910785, by decide⟩,⟨910808, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_70745_910809 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70745 ⟨910809, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 70745
    ⟨910809, by decide⟩ (by decide) (![⟨910757, by decide⟩,⟨896706, by decide⟩,⟨910785, by decide⟩,⟨910808, by decide⟩]) unmarked_context_11_70745_910809 node_context_11_70745_910809
  intro a
  fin_cases a
  · exact context_12_282980_910757
  · exact context_12_282981_896706
  · exact context_12_282982_910785
  · exact context_12_282983_910808

theorem selected_cut_34860 : selected 9 ⟨910829, by decide⟩
    (prefixPartial 12 282984) = some ⟨12, 2, 0, 910829, 282984, 1529, 65536⟩ := by
  decide +kernel

theorem context_12_282984_910829 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 282984 ⟨910829, by decide⟩ :=
  accepted_of_selected 12 282984 ⟨910829, by decide⟩ ⟨12, 2, 0, 910829, 282984, 1529, 65536⟩
    (by decide) selected_cut_34860

theorem selected_cut_34861 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 282985) = some ⟨12, 1, 0, 896706, 282985, 1, 65536⟩ := by
  decide +kernel

theorem context_12_282985_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 282985 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 282985 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 282985, 1, 65536⟩
    (by decide) selected_cut_34861

theorem selected_cut_34862 : selected 9 ⟨910862, by decide⟩
    (prefixPartial 12 282986) = some ⟨12, 2, 0, 910862, 282986, 1825, 65536⟩ := by
  decide +kernel

theorem context_12_282986_910862 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 282986 ⟨910862, by decide⟩ :=
  accepted_of_selected 12 282986 ⟨910862, by decide⟩ ⟨12, 2, 0, 910862, 282986, 1825, 65536⟩
    (by decide) selected_cut_34862

theorem selected_cut_34863 : selected 9 ⟨910892, by decide⟩
    (prefixPartial 12 282987) = some ⟨12, 2, 0, 910892, 282987, 1545, 65536⟩ := by
  decide +kernel

theorem context_12_282987_910892 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 282987 ⟨910892, by decide⟩ :=
  accepted_of_selected 12 282987 ⟨910892, by decide⟩ ⟨12, 2, 0, 910892, 282987, 1545, 65536⟩
    (by decide) selected_cut_34863

theorem unmarked_context_11_70746_910893 : frontier 10 ⟨910893, by decide⟩
    (prefixCache 11 70746) (prefixPartial 11 70746) = false := by
  decide +kernel

theorem node_context_11_70746_910893 : EJMOriginalGlobalDAGData.nodes 10 ⟨910893, by decide⟩ =
    .split (coordinate 11) (![⟨910829, by decide⟩,⟨896706, by decide⟩,⟨910862, by decide⟩,⟨910892, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_70746_910893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70746 ⟨910893, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 70746
    ⟨910893, by decide⟩ (by decide) (![⟨910829, by decide⟩,⟨896706, by decide⟩,⟨910862, by decide⟩,⟨910892, by decide⟩]) unmarked_context_11_70746_910893 node_context_11_70746_910893
  intro a
  fin_cases a
  · exact context_12_282984_910829
  · exact context_12_282985_896706
  · exact context_12_282986_910862
  · exact context_12_282987_910892

theorem selected_cut_34864 : selected 9 ⟨910911, by decide⟩
    (prefixPartial 12 282988) = some ⟨12, 2, 0, 910911, 282988, 1485, 65536⟩ := by
  decide +kernel

theorem context_12_282988_910911 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 282988 ⟨910911, by decide⟩ :=
  accepted_of_selected 12 282988 ⟨910911, by decide⟩ ⟨12, 2, 0, 910911, 282988, 1485, 65536⟩
    (by decide) selected_cut_34864

theorem selected_cut_34865 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 282989) = some ⟨12, 1, 0, 896706, 282989, 1, 65536⟩ := by
  decide +kernel

theorem context_12_282989_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 282989 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 282989 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 282989, 1, 65536⟩
    (by decide) selected_cut_34865

theorem selected_cut_34866 : selected 9 ⟨910944, by decide⟩
    (prefixPartial 12 282990) = some ⟨12, 2, 0, 910944, 282990, 1789, 65536⟩ := by
  decide +kernel

theorem context_12_282990_910944 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 282990 ⟨910944, by decide⟩ :=
  accepted_of_selected 12 282990 ⟨910944, by decide⟩ ⟨12, 2, 0, 910944, 282990, 1789, 65536⟩
    (by decide) selected_cut_34866

theorem selected_cut_34867 : selected 9 ⟨910966, by decide⟩
    (prefixPartial 12 282991) = some ⟨12, 2, 0, 910966, 282991, 1549, 65536⟩ := by
  decide +kernel

theorem context_12_282991_910966 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 282991 ⟨910966, by decide⟩ :=
  accepted_of_selected 12 282991 ⟨910966, by decide⟩ ⟨12, 2, 0, 910966, 282991, 1549, 65536⟩
    (by decide) selected_cut_34867

theorem unmarked_context_11_70747_910967 : frontier 10 ⟨910967, by decide⟩
    (prefixCache 11 70747) (prefixPartial 11 70747) = false := by
  decide +kernel

theorem node_context_11_70747_910967 : EJMOriginalGlobalDAGData.nodes 10 ⟨910967, by decide⟩ =
    .split (coordinate 11) (![⟨910911, by decide⟩,⟨896706, by decide⟩,⟨910944, by decide⟩,⟨910966, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_70747_910967 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70747 ⟨910967, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 70747
    ⟨910967, by decide⟩ (by decide) (![⟨910911, by decide⟩,⟨896706, by decide⟩,⟨910944, by decide⟩,⟨910966, by decide⟩]) unmarked_context_11_70747_910967 node_context_11_70747_910967
  intro a
  fin_cases a
  · exact context_12_282988_910911
  · exact context_12_282989_896706
  · exact context_12_282990_910944
  · exact context_12_282991_910966

theorem unmarked_context_10_17686_910968 : frontier 11 ⟨910968, by decide⟩
    (prefixCache 10 17686) (prefixPartial 10 17686) = false := by
  decide +kernel

theorem node_context_10_17686_910968 : EJMOriginalGlobalDAGData.nodes 11 ⟨910968, by decide⟩ =
    .split (coordinate 10) (![⟨910735, by decide⟩,⟨910809, by decide⟩,⟨910893, by decide⟩,⟨910967, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17686_910968 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17686 ⟨910968, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17686
    ⟨910968, by decide⟩ (by decide) (![⟨910735, by decide⟩,⟨910809, by decide⟩,⟨910893, by decide⟩,⟨910967, by decide⟩]) unmarked_context_10_17686_910968 node_context_10_17686_910968
  intro a
  fin_cases a
  · exact context_11_70744_910735
  · exact context_11_70745_910809
  · exact context_11_70746_910893
  · exact context_11_70747_910967

theorem selected_cut_34868 : selected 11 ⟨3440, by decide⟩
    (prefixPartial 10 17687) = some ⟨10, 1, 0, 3440, 17687, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_17687_3440 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17687 ⟨3440, by decide⟩ :=
  accepted_of_selected 10 17687 ⟨3440, by decide⟩ ⟨10, 1, 0, 3440, 17687, 1, 1048576⟩
    (by decide) selected_cut_34868

theorem unmarked_context_9_4421_910969 : frontier 12 ⟨910969, by decide⟩
    (prefixCache 9 4421) (prefixPartial 9 4421) = false := by
  decide +kernel

theorem node_context_9_4421_910969 : EJMOriginalGlobalDAGData.nodes 12 ⟨910969, by decide⟩ =
    .split (coordinate 9) (![⟨910666, by decide⟩,⟨893098, by decide⟩,⟨910968, by decide⟩,⟨3440, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4421_910969 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4421 ⟨910969, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4421
    ⟨910969, by decide⟩ (by decide) (![⟨910666, by decide⟩,⟨893098, by decide⟩,⟨910968, by decide⟩,⟨3440, by decide⟩]) unmarked_context_9_4421_910969 node_context_9_4421_910969
  intro a
  fin_cases a
  · exact context_10_17684_910666
  · exact context_10_17685_893098
  · exact context_10_17686_910968
  · exact context_10_17687_3440

theorem selected_cut_34869 : selected 10 ⟨907917, by decide⟩
    (prefixPartial 11 70752) = some ⟨11, 1, 0, 907917, 70752, 1, 262144⟩ := by
  decide +kernel

theorem context_11_70752_907917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70752 ⟨907917, by decide⟩ :=
  accepted_of_selected 11 70752 ⟨907917, by decide⟩ ⟨11, 1, 0, 907917, 70752, 1, 262144⟩
    (by decide) selected_cut_34869

theorem selected_cut_34870 : selected 9 ⟨911001, by decide⟩
    (prefixPartial 12 283012) = some ⟨12, 2, 0, 911001, 283012, 1585, 65536⟩ := by
  decide +kernel

theorem context_12_283012_911001 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283012 ⟨911001, by decide⟩ :=
  accepted_of_selected 12 283012 ⟨911001, by decide⟩ ⟨12, 2, 0, 911001, 283012, 1585, 65536⟩
    (by decide) selected_cut_34870

theorem selected_cut_34871 : selected 9 ⟨891951, by decide⟩
    (prefixPartial 12 283013) = some ⟨12, 1, 0, 891951, 283013, 1, 65536⟩ := by
  decide +kernel

theorem context_12_283013_891951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283013 ⟨891951, by decide⟩ :=
  accepted_of_selected 12 283013 ⟨891951, by decide⟩ ⟨12, 1, 0, 891951, 283013, 1, 65536⟩
    (by decide) selected_cut_34871

theorem selected_cut_34872 : selected 9 ⟨911022, by decide⟩
    (prefixPartial 12 283014) = some ⟨12, 2, 0, 911022, 283014, 1281, 65536⟩ := by
  decide +kernel

theorem context_12_283014_911022 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283014 ⟨911022, by decide⟩ :=
  accepted_of_selected 12 283014 ⟨911022, by decide⟩ ⟨12, 2, 0, 911022, 283014, 1281, 65536⟩
    (by decide) selected_cut_34872

theorem selected_cut_34873 : selected 9 ⟨911043, by decide⟩
    (prefixPartial 12 283015) = some ⟨12, 2, 0, 911043, 283015, 1277, 65536⟩ := by
  decide +kernel

theorem context_12_283015_911043 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283015 ⟨911043, by decide⟩ :=
  accepted_of_selected 12 283015 ⟨911043, by decide⟩ ⟨12, 2, 0, 911043, 283015, 1277, 65536⟩
    (by decide) selected_cut_34873

theorem unmarked_context_11_70753_911044 : frontier 10 ⟨911044, by decide⟩
    (prefixCache 11 70753) (prefixPartial 11 70753) = false := by
  decide +kernel

theorem node_context_11_70753_911044 : EJMOriginalGlobalDAGData.nodes 10 ⟨911044, by decide⟩ =
    .split (coordinate 11) (![⟨911001, by decide⟩,⟨891951, by decide⟩,⟨911022, by decide⟩,⟨911043, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_70753_911044 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70753 ⟨911044, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 70753
    ⟨911044, by decide⟩ (by decide) (![⟨911001, by decide⟩,⟨891951, by decide⟩,⟨911022, by decide⟩,⟨911043, by decide⟩]) unmarked_context_11_70753_911044 node_context_11_70753_911044
  intro a
  fin_cases a
  · exact context_12_283012_911001
  · exact context_12_283013_891951
  · exact context_12_283014_911022
  · exact context_12_283015_911043

theorem selected_cut_34874 : selected 9 ⟨911074, by decide⟩
    (prefixPartial 12 283016) = some ⟨12, 2, 0, 911074, 283016, 1597, 65536⟩ := by
  decide +kernel

theorem context_12_283016_911074 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283016 ⟨911074, by decide⟩ :=
  accepted_of_selected 12 283016 ⟨911074, by decide⟩ ⟨12, 2, 0, 911074, 283016, 1597, 65536⟩
    (by decide) selected_cut_34874

theorem selected_cut_34875 : selected 9 ⟨911096, by decide⟩
    (prefixPartial 12 283017) = some ⟨12, 2, 0, 911096, 283017, 1465, 65536⟩ := by
  decide +kernel

theorem context_12_283017_911096 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283017 ⟨911096, by decide⟩ :=
  accepted_of_selected 12 283017 ⟨911096, by decide⟩ ⟨12, 2, 0, 911096, 283017, 1465, 65536⟩
    (by decide) selected_cut_34875

theorem selected_cut_34876 : selected 9 ⟨911116, by decide⟩
    (prefixPartial 12 283018) = some ⟨12, 2, 0, 911116, 283018, 1373, 65536⟩ := by
  decide +kernel

theorem context_12_283018_911116 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283018 ⟨911116, by decide⟩ :=
  accepted_of_selected 12 283018 ⟨911116, by decide⟩ ⟨12, 2, 0, 911116, 283018, 1373, 65536⟩
    (by decide) selected_cut_34876

theorem selected_cut_34877 : selected 9 ⟨911134, by decide⟩
    (prefixPartial 12 283019) = some ⟨12, 2, 0, 911134, 283019, 1345, 65536⟩ := by
  decide +kernel

theorem context_12_283019_911134 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283019 ⟨911134, by decide⟩ :=
  accepted_of_selected 12 283019 ⟨911134, by decide⟩ ⟨12, 2, 0, 911134, 283019, 1345, 65536⟩
    (by decide) selected_cut_34877

theorem unmarked_context_11_70754_911135 : frontier 10 ⟨911135, by decide⟩
    (prefixCache 11 70754) (prefixPartial 11 70754) = false := by
  decide +kernel

theorem node_context_11_70754_911135 : EJMOriginalGlobalDAGData.nodes 10 ⟨911135, by decide⟩ =
    .split (coordinate 11) (![⟨911074, by decide⟩,⟨911096, by decide⟩,⟨911116, by decide⟩,⟨911134, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_70754_911135 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70754 ⟨911135, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 70754
    ⟨911135, by decide⟩ (by decide) (![⟨911074, by decide⟩,⟨911096, by decide⟩,⟨911116, by decide⟩,⟨911134, by decide⟩]) unmarked_context_11_70754_911135 node_context_11_70754_911135
  intro a
  fin_cases a
  · exact context_12_283016_911074
  · exact context_12_283017_911096
  · exact context_12_283018_911116
  · exact context_12_283019_911134

theorem selected_cut_34878 : selected 9 ⟨911158, by decide⟩
    (prefixPartial 12 283020) = some ⟨12, 2, 0, 911158, 283020, 1309, 65536⟩ := by
  decide +kernel

theorem context_12_283020_911158 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283020 ⟨911158, by decide⟩ :=
  accepted_of_selected 12 283020 ⟨911158, by decide⟩ ⟨12, 2, 0, 911158, 283020, 1309, 65536⟩
    (by decide) selected_cut_34878

theorem selected_cut_34879 : selected 9 ⟨911177, by decide⟩
    (prefixPartial 12 283021) = some ⟨12, 2, 0, 911177, 283021, 1205, 65536⟩ := by
  decide +kernel

theorem context_12_283021_911177 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283021 ⟨911177, by decide⟩ :=
  accepted_of_selected 12 283021 ⟨911177, by decide⟩ ⟨12, 2, 0, 911177, 283021, 1205, 65536⟩
    (by decide) selected_cut_34879

theorem selected_cut_34880 : selected 9 ⟨911194, by decide⟩
    (prefixPartial 12 283022) = some ⟨12, 2, 0, 911194, 283022, 1117, 65536⟩ := by
  decide +kernel

theorem context_12_283022_911194 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283022 ⟨911194, by decide⟩ :=
  accepted_of_selected 12 283022 ⟨911194, by decide⟩ ⟨12, 2, 0, 911194, 283022, 1117, 65536⟩
    (by decide) selected_cut_34880

theorem selected_cut_34881 : selected 9 ⟨911206, by decide⟩
    (prefixPartial 12 283023) = some ⟨12, 2, 0, 911206, 283023, 1137, 65536⟩ := by
  decide +kernel

theorem context_12_283023_911206 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283023 ⟨911206, by decide⟩ :=
  accepted_of_selected 12 283023 ⟨911206, by decide⟩ ⟨12, 2, 0, 911206, 283023, 1137, 65536⟩
    (by decide) selected_cut_34881

theorem unmarked_context_11_70755_911207 : frontier 10 ⟨911207, by decide⟩
    (prefixCache 11 70755) (prefixPartial 11 70755) = false := by
  decide +kernel

theorem node_context_11_70755_911207 : EJMOriginalGlobalDAGData.nodes 10 ⟨911207, by decide⟩ =
    .split (coordinate 11) (![⟨911158, by decide⟩,⟨911177, by decide⟩,⟨911194, by decide⟩,⟨911206, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_70755_911207 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70755 ⟨911207, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 70755
    ⟨911207, by decide⟩ (by decide) (![⟨911158, by decide⟩,⟨911177, by decide⟩,⟨911194, by decide⟩,⟨911206, by decide⟩]) unmarked_context_11_70755_911207 node_context_11_70755_911207
  intro a
  fin_cases a
  · exact context_12_283020_911158
  · exact context_12_283021_911177
  · exact context_12_283022_911194
  · exact context_12_283023_911206

theorem unmarked_context_10_17688_911208 : frontier 11 ⟨911208, by decide⟩
    (prefixCache 10 17688) (prefixPartial 10 17688) = false := by
  decide +kernel

theorem node_context_10_17688_911208 : EJMOriginalGlobalDAGData.nodes 11 ⟨911208, by decide⟩ =
    .split (coordinate 10) (![⟨907917, by decide⟩,⟨911044, by decide⟩,⟨911135, by decide⟩,⟨911207, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17688_911208 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17688 ⟨911208, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17688
    ⟨911208, by decide⟩ (by decide) (![⟨907917, by decide⟩,⟨911044, by decide⟩,⟨911135, by decide⟩,⟨911207, by decide⟩]) unmarked_context_10_17688_911208 node_context_10_17688_911208
  intro a
  fin_cases a
  · exact context_11_70752_907917
  · exact context_11_70753_911044
  · exact context_11_70754_911135
  · exact context_11_70755_911207

theorem selected_cut_34882 : selected 10 ⟨911267, by decide⟩
    (prefixPartial 11 70756) = some ⟨11, 2, 0, 911267, 70756, 3689, 262144⟩ := by
  decide +kernel

theorem context_11_70756_911267 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70756 ⟨911267, by decide⟩ :=
  accepted_of_selected 11 70756 ⟨911267, by decide⟩ ⟨11, 2, 0, 911267, 70756, 3689, 262144⟩
    (by decide) selected_cut_34882

theorem selected_cut_34883 : selected 10 ⟨911314, by decide⟩
    (prefixPartial 11 70757) = some ⟨11, 2, 0, 911314, 70757, 2377, 262144⟩ := by
  decide +kernel

theorem context_11_70757_911314 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70757 ⟨911314, by decide⟩ :=
  accepted_of_selected 11 70757 ⟨911314, by decide⟩ ⟨11, 2, 0, 911314, 70757, 2377, 262144⟩
    (by decide) selected_cut_34883

theorem selected_cut_34884 : selected 10 ⟨911355, by decide⟩
    (prefixPartial 11 70758) = some ⟨11, 2, 0, 911355, 70758, 3261, 262144⟩ := by
  decide +kernel

theorem context_11_70758_911355 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70758 ⟨911355, by decide⟩ :=
  accepted_of_selected 11 70758 ⟨911355, by decide⟩ ⟨11, 2, 0, 911355, 70758, 3261, 262144⟩
    (by decide) selected_cut_34884

theorem selected_cut_34885 : selected 10 ⟨911396, by decide⟩
    (prefixPartial 11 70759) = some ⟨11, 2, 0, 911396, 70759, 2833, 262144⟩ := by
  decide +kernel

theorem context_11_70759_911396 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70759 ⟨911396, by decide⟩ :=
  accepted_of_selected 11 70759 ⟨911396, by decide⟩ ⟨11, 2, 0, 911396, 70759, 2833, 262144⟩
    (by decide) selected_cut_34885

theorem unmarked_context_10_17689_911397 : frontier 11 ⟨911397, by decide⟩
    (prefixCache 10 17689) (prefixPartial 10 17689) = false := by
  decide +kernel

theorem node_context_10_17689_911397 : EJMOriginalGlobalDAGData.nodes 11 ⟨911397, by decide⟩ =
    .split (coordinate 10) (![⟨911267, by decide⟩,⟨911314, by decide⟩,⟨911355, by decide⟩,⟨911396, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17689_911397 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17689 ⟨911397, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17689
    ⟨911397, by decide⟩ (by decide) (![⟨911267, by decide⟩,⟨911314, by decide⟩,⟨911355, by decide⟩,⟨911396, by decide⟩]) unmarked_context_10_17689_911397 node_context_10_17689_911397
  intro a
  fin_cases a
  · exact context_11_70756_911267
  · exact context_11_70757_911314
  · exact context_11_70758_911355
  · exact context_11_70759_911396

theorem selected_cut_34886 : selected 10 ⟨911440, by decide⟩
    (prefixPartial 11 70760) = some ⟨11, 2, 0, 911440, 70760, 2641, 262144⟩ := by
  decide +kernel

theorem context_11_70760_911440 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70760 ⟨911440, by decide⟩ :=
  accepted_of_selected 11 70760 ⟨911440, by decide⟩ ⟨11, 2, 0, 911440, 70760, 2641, 262144⟩
    (by decide) selected_cut_34886

theorem selected_cut_34887 : selected 10 ⟨911466, by decide⟩
    (prefixPartial 11 70761) = some ⟨11, 2, 0, 911466, 70761, 1641, 262144⟩ := by
  decide +kernel

theorem context_11_70761_911466 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70761 ⟨911466, by decide⟩ :=
  accepted_of_selected 11 70761 ⟨911466, by decide⟩ ⟨11, 2, 0, 911466, 70761, 1641, 262144⟩
    (by decide) selected_cut_34887

theorem selected_cut_34888 : selected 10 ⟨911489, by decide⟩
    (prefixPartial 11 70762) = some ⟨11, 2, 0, 911489, 70762, 1561, 262144⟩ := by
  decide +kernel

theorem context_11_70762_911489 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70762 ⟨911489, by decide⟩ :=
  accepted_of_selected 11 70762 ⟨911489, by decide⟩ ⟨11, 2, 0, 911489, 70762, 1561, 262144⟩
    (by decide) selected_cut_34888

theorem selected_cut_34889 : selected 10 ⟨911517, by decide⟩
    (prefixPartial 11 70763) = some ⟨11, 2, 0, 911517, 70763, 1805, 262144⟩ := by
  decide +kernel

theorem context_11_70763_911517 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70763 ⟨911517, by decide⟩ :=
  accepted_of_selected 11 70763 ⟨911517, by decide⟩ ⟨11, 2, 0, 911517, 70763, 1805, 262144⟩
    (by decide) selected_cut_34889

theorem unmarked_context_10_17690_911518 : frontier 11 ⟨911518, by decide⟩
    (prefixCache 10 17690) (prefixPartial 10 17690) = false := by
  decide +kernel

theorem node_context_10_17690_911518 : EJMOriginalGlobalDAGData.nodes 11 ⟨911518, by decide⟩ =
    .split (coordinate 10) (![⟨911440, by decide⟩,⟨911466, by decide⟩,⟨911489, by decide⟩,⟨911517, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17690_911518 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17690 ⟨911518, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17690
    ⟨911518, by decide⟩ (by decide) (![⟨911440, by decide⟩,⟨911466, by decide⟩,⟨911489, by decide⟩,⟨911517, by decide⟩]) unmarked_context_10_17690_911518 node_context_10_17690_911518
  intro a
  fin_cases a
  · exact context_11_70760_911440
  · exact context_11_70761_911466
  · exact context_11_70762_911489
  · exact context_11_70763_911517

theorem selected_cut_34890 : selected 11 ⟨911605, by decide⟩
    (prefixPartial 10 17691) = some ⟨10, 2, 0, 911605, 17691, 3149, 1048576⟩ := by
  decide +kernel

theorem context_10_17691_911605 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17691 ⟨911605, by decide⟩ :=
  accepted_of_selected 10 17691 ⟨911605, by decide⟩ ⟨10, 2, 0, 911605, 17691, 3149, 1048576⟩
    (by decide) selected_cut_34890

theorem unmarked_context_9_4422_911606 : frontier 12 ⟨911606, by decide⟩
    (prefixCache 9 4422) (prefixPartial 9 4422) = false := by
  decide +kernel

theorem node_context_9_4422_911606 : EJMOriginalGlobalDAGData.nodes 12 ⟨911606, by decide⟩ =
    .split (coordinate 9) (![⟨911208, by decide⟩,⟨911397, by decide⟩,⟨911518, by decide⟩,⟨911605, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4422_911606 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4422 ⟨911606, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4422
    ⟨911606, by decide⟩ (by decide) (![⟨911208, by decide⟩,⟨911397, by decide⟩,⟨911518, by decide⟩,⟨911605, by decide⟩]) unmarked_context_9_4422_911606 node_context_9_4422_911606
  intro a
  fin_cases a
  · exact context_10_17688_911208
  · exact context_10_17689_911397
  · exact context_10_17690_911518
  · exact context_10_17691_911605

theorem selected_cut_34891 : selected 12 ⟨4601, by decide⟩
    (prefixPartial 9 4423) = some ⟨9, 1, 0, 4601, 4423, 1, 4194304⟩ := by
  decide +kernel

theorem context_9_4423_4601 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4423 ⟨4601, by decide⟩ :=
  accepted_of_selected 9 4423 ⟨4601, by decide⟩ ⟨9, 1, 0, 4601, 4423, 1, 4194304⟩
    (by decide) selected_cut_34891

theorem unmarked_context_8_1105_911607 : frontier 13 ⟨911607, by decide⟩
    (prefixCache 8 1105) (prefixPartial 8 1105) = false := by
  decide +kernel

theorem node_context_8_1105_911607 : EJMOriginalGlobalDAGData.nodes 13 ⟨911607, by decide⟩ =
    .split (coordinate 8) (![⟨910517, by decide⟩,⟨910969, by decide⟩,⟨911606, by decide⟩,⟨4601, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1105_911607 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1105 ⟨911607, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1105
    ⟨911607, by decide⟩ (by decide) (![⟨910517, by decide⟩,⟨910969, by decide⟩,⟨911606, by decide⟩,⟨4601, by decide⟩]) unmarked_context_8_1105_911607 node_context_8_1105_911607
  intro a
  fin_cases a
  · exact context_9_4420_910517
  · exact context_9_4421_910969
  · exact context_9_4422_911606
  · exact context_9_4423_4601

theorem selected_cut_34892 : selected 10 ⟨167448, by decide⟩
    (prefixPartial 11 70784) = some ⟨11, 1, 0, 167448, 70784, 1, 262144⟩ := by
  decide +kernel

theorem context_11_70784_167448 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70784 ⟨167448, by decide⟩ :=
  accepted_of_selected 11 70784 ⟨167448, by decide⟩ ⟨11, 1, 0, 167448, 70784, 1, 262144⟩
    (by decide) selected_cut_34892

theorem selected_cut_34893 : selected 8 ⟨911665, by decide⟩
    (prefixPartial 13 1132560) = some ⟨13, 2, 0, 911665, 1132560, 1825, 16384⟩ := by
  decide +kernel

theorem context_13_1132560_911665 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1132560 ⟨911665, by decide⟩ :=
  accepted_of_selected 13 1132560 ⟨911665, by decide⟩ ⟨13, 2, 0, 911665, 1132560, 1825, 16384⟩
    (by decide) selected_cut_34893

theorem selected_cut_34894 : selected 8 ⟨911680, by decide⟩
    (prefixPartial 13 1132561) = some ⟨13, 2, 0, 911680, 1132561, 585, 16384⟩ := by
  decide +kernel

theorem context_13_1132561_911680 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1132561 ⟨911680, by decide⟩ :=
  accepted_of_selected 13 1132561 ⟨911680, by decide⟩ ⟨13, 2, 0, 911680, 1132561, 585, 16384⟩
    (by decide) selected_cut_34894

theorem selected_cut_34895 : selected 8 ⟨911712, by decide⟩
    (prefixPartial 13 1132562) = some ⟨13, 2, 0, 911712, 1132562, 1113, 16384⟩ := by
  decide +kernel

theorem context_13_1132562_911712 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1132562 ⟨911712, by decide⟩ :=
  accepted_of_selected 13 1132562 ⟨911712, by decide⟩ ⟨13, 2, 0, 911712, 1132562, 1113, 16384⟩
    (by decide) selected_cut_34895

theorem selected_cut_34896 : selected 8 ⟨911722, by decide⟩
    (prefixPartial 13 1132563) = some ⟨13, 2, 0, 911722, 1132563, 597, 16384⟩ := by
  decide +kernel

theorem context_13_1132563_911722 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1132563 ⟨911722, by decide⟩ :=
  accepted_of_selected 13 1132563 ⟨911722, by decide⟩ ⟨13, 2, 0, 911722, 1132563, 597, 16384⟩
    (by decide) selected_cut_34896

theorem unmarked_context_12_283140_911723 : frontier 9 ⟨911723, by decide⟩
    (prefixCache 12 283140) (prefixPartial 12 283140) = false := by
  decide +kernel

theorem node_context_12_283140_911723 : EJMOriginalGlobalDAGData.nodes 9 ⟨911723, by decide⟩ =
    .split (coordinate 12) (![⟨911665, by decide⟩,⟨911680, by decide⟩,⟨911712, by decide⟩,⟨911722, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_283140_911723 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283140 ⟨911723, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 283140
    ⟨911723, by decide⟩ (by decide) (![⟨911665, by decide⟩,⟨911680, by decide⟩,⟨911712, by decide⟩,⟨911722, by decide⟩]) unmarked_context_12_283140_911723 node_context_12_283140_911723
  intro a
  fin_cases a
  · exact context_13_1132560_911665
  · exact context_13_1132561_911680
  · exact context_13_1132562_911712
  · exact context_13_1132563_911722

theorem selected_cut_34897 : selected 9 ⟨911781, by decide⟩
    (prefixPartial 12 283141) = some ⟨12, 2, 0, 911781, 283141, 3045, 65536⟩ := by
  decide +kernel

theorem context_12_283141_911781 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283141 ⟨911781, by decide⟩ :=
  accepted_of_selected 12 283141 ⟨911781, by decide⟩ ⟨12, 2, 0, 911781, 283141, 3045, 65536⟩
    (by decide) selected_cut_34897

theorem selected_cut_34898 : selected 9 ⟨911846, by decide⟩
    (prefixPartial 12 283142) = some ⟨12, 2, 0, 911846, 283142, 3201, 65536⟩ := by
  decide +kernel

theorem context_12_283142_911846 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283142 ⟨911846, by decide⟩ :=
  accepted_of_selected 12 283142 ⟨911846, by decide⟩ ⟨12, 2, 0, 911846, 283142, 3201, 65536⟩
    (by decide) selected_cut_34898

theorem selected_cut_34899 : selected 9 ⟨911911, by decide⟩
    (prefixPartial 12 283143) = some ⟨12, 2, 0, 911911, 283143, 3289, 65536⟩ := by
  decide +kernel

theorem context_12_283143_911911 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283143 ⟨911911, by decide⟩ :=
  accepted_of_selected 12 283143 ⟨911911, by decide⟩ ⟨12, 2, 0, 911911, 283143, 3289, 65536⟩
    (by decide) selected_cut_34899

theorem unmarked_context_11_70785_911912 : frontier 10 ⟨911912, by decide⟩
    (prefixCache 11 70785) (prefixPartial 11 70785) = false := by
  decide +kernel

theorem node_context_11_70785_911912 : EJMOriginalGlobalDAGData.nodes 10 ⟨911912, by decide⟩ =
    .split (coordinate 11) (![⟨911723, by decide⟩,⟨911781, by decide⟩,⟨911846, by decide⟩,⟨911911, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_70785_911912 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70785 ⟨911912, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 70785
    ⟨911912, by decide⟩ (by decide) (![⟨911723, by decide⟩,⟨911781, by decide⟩,⟨911846, by decide⟩,⟨911911, by decide⟩]) unmarked_context_11_70785_911912 node_context_11_70785_911912
  intro a
  fin_cases a
  · exact context_12_283140_911723
  · exact context_12_283141_911781
  · exact context_12_283142_911846
  · exact context_12_283143_911911

theorem selected_cut_34900 : selected 8 ⟨911959, by decide⟩
    (prefixPartial 13 1132576) = some ⟨13, 2, 0, 911959, 1132576, 2025, 16384⟩ := by
  decide +kernel

theorem context_13_1132576_911959 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1132576 ⟨911959, by decide⟩ :=
  accepted_of_selected 13 1132576 ⟨911959, by decide⟩ ⟨13, 2, 0, 911959, 1132576, 2025, 16384⟩
    (by decide) selected_cut_34900

theorem selected_cut_34901 : selected 8 ⟨911980, by decide⟩
    (prefixPartial 13 1132577) = some ⟨13, 2, 0, 911980, 1132577, 781, 16384⟩ := by
  decide +kernel

theorem context_13_1132577_911980 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1132577 ⟨911980, by decide⟩ :=
  accepted_of_selected 13 1132577 ⟨911980, by decide⟩ ⟨13, 2, 0, 911980, 1132577, 781, 16384⟩
    (by decide) selected_cut_34901

theorem selected_cut_34902 : selected 8 ⟨912008, by decide⟩
    (prefixPartial 13 1132578) = some ⟨13, 2, 0, 912008, 1132578, 1305, 16384⟩ := by
  decide +kernel

theorem context_13_1132578_912008 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1132578 ⟨912008, by decide⟩ :=
  accepted_of_selected 13 1132578 ⟨912008, by decide⟩ ⟨13, 2, 0, 912008, 1132578, 1305, 16384⟩
    (by decide) selected_cut_34902

theorem selected_cut_34903 : selected 8 ⟨912016, by decide⟩
    (prefixPartial 13 1132579) = some ⟨13, 2, 0, 912016, 1132579, 629, 16384⟩ := by
  decide +kernel

theorem context_13_1132579_912016 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1132579 ⟨912016, by decide⟩ :=
  accepted_of_selected 13 1132579 ⟨912016, by decide⟩ ⟨13, 2, 0, 912016, 1132579, 629, 16384⟩
    (by decide) selected_cut_34903

theorem unmarked_context_12_283144_912017 : frontier 9 ⟨912017, by decide⟩
    (prefixCache 12 283144) (prefixPartial 12 283144) = false := by
  decide +kernel

theorem node_context_12_283144_912017 : EJMOriginalGlobalDAGData.nodes 9 ⟨912017, by decide⟩ =
    .split (coordinate 12) (![⟨911959, by decide⟩,⟨911980, by decide⟩,⟨912008, by decide⟩,⟨912016, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_283144_912017 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283144 ⟨912017, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 283144
    ⟨912017, by decide⟩ (by decide) (![⟨911959, by decide⟩,⟨911980, by decide⟩,⟨912008, by decide⟩,⟨912016, by decide⟩]) unmarked_context_12_283144_912017 node_context_12_283144_912017
  intro a
  fin_cases a
  · exact context_13_1132576_911959
  · exact context_13_1132577_911980
  · exact context_13_1132578_912008
  · exact context_13_1132579_912016

theorem selected_cut_34904 : selected 9 ⟨912092, by decide⟩
    (prefixPartial 12 283145) = some ⟨12, 2, 0, 912092, 283145, 3765, 65536⟩ := by
  decide +kernel

theorem context_12_283145_912092 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283145 ⟨912092, by decide⟩ :=
  accepted_of_selected 12 283145 ⟨912092, by decide⟩ ⟨12, 2, 0, 912092, 283145, 3765, 65536⟩
    (by decide) selected_cut_34904

theorem selected_cut_34905 : selected 9 ⟨893903, by decide⟩
    (prefixPartial 12 283146) = some ⟨12, 1, 0, 893903, 283146, 1, 65536⟩ := by
  decide +kernel

theorem context_12_283146_893903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283146 ⟨893903, by decide⟩ :=
  accepted_of_selected 12 283146 ⟨893903, by decide⟩ ⟨12, 1, 0, 893903, 283146, 1, 65536⟩
    (by decide) selected_cut_34905

theorem selected_cut_34906 : selected 9 ⟨912175, by decide⟩
    (prefixPartial 12 283147) = some ⟨12, 2, 0, 912175, 283147, 4057, 65536⟩ := by
  decide +kernel

theorem context_12_283147_912175 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283147 ⟨912175, by decide⟩ :=
  accepted_of_selected 12 283147 ⟨912175, by decide⟩ ⟨12, 2, 0, 912175, 283147, 4057, 65536⟩
    (by decide) selected_cut_34906

theorem unmarked_context_11_70786_912176 : frontier 10 ⟨912176, by decide⟩
    (prefixCache 11 70786) (prefixPartial 11 70786) = false := by
  decide +kernel

theorem node_context_11_70786_912176 : EJMOriginalGlobalDAGData.nodes 10 ⟨912176, by decide⟩ =
    .split (coordinate 11) (![⟨912017, by decide⟩,⟨912092, by decide⟩,⟨893903, by decide⟩,⟨912175, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_70786_912176 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70786 ⟨912176, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 70786
    ⟨912176, by decide⟩ (by decide) (![⟨912017, by decide⟩,⟨912092, by decide⟩,⟨893903, by decide⟩,⟨912175, by decide⟩]) unmarked_context_11_70786_912176 node_context_11_70786_912176
  intro a
  fin_cases a
  · exact context_12_283144_912017
  · exact context_12_283145_912092
  · exact context_12_283146_893903
  · exact context_12_283147_912175

theorem selected_cut_34907 : selected 8 ⟨912226, by decide⟩
    (prefixPartial 13 1132592) = some ⟨13, 2, 0, 912226, 1132592, 2029, 16384⟩ := by
  decide +kernel

theorem context_13_1132592_912226 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1132592 ⟨912226, by decide⟩ :=
  accepted_of_selected 13 1132592 ⟨912226, by decide⟩ ⟨13, 2, 0, 912226, 1132592, 2029, 16384⟩
    (by decide) selected_cut_34907

theorem selected_cut_34908 : selected 8 ⟨912249, by decide⟩
    (prefixPartial 13 1132593) = some ⟨13, 2, 0, 912249, 1132593, 861, 16384⟩ := by
  decide +kernel

theorem context_13_1132593_912249 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1132593 ⟨912249, by decide⟩ :=
  accepted_of_selected 13 1132593 ⟨912249, by decide⟩ ⟨13, 2, 0, 912249, 1132593, 861, 16384⟩
    (by decide) selected_cut_34908

theorem selected_cut_34909 : selected 8 ⟨912283, by decide⟩
    (prefixPartial 13 1132594) = some ⟨13, 2, 0, 912283, 1132594, 1365, 16384⟩ := by
  decide +kernel

theorem context_13_1132594_912283 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1132594 ⟨912283, by decide⟩ :=
  accepted_of_selected 13 1132594 ⟨912283, by decide⟩ ⟨13, 2, 0, 912283, 1132594, 1365, 16384⟩
    (by decide) selected_cut_34909

theorem selected_cut_34910 : selected 8 ⟨912293, by decide⟩
    (prefixPartial 13 1132595) = some ⟨13, 2, 0, 912293, 1132595, 685, 16384⟩ := by
  decide +kernel

theorem context_13_1132595_912293 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1132595 ⟨912293, by decide⟩ :=
  accepted_of_selected 13 1132595 ⟨912293, by decide⟩ ⟨13, 2, 0, 912293, 1132595, 685, 16384⟩
    (by decide) selected_cut_34910

theorem unmarked_context_12_283148_912294 : frontier 9 ⟨912294, by decide⟩
    (prefixCache 12 283148) (prefixPartial 12 283148) = false := by
  decide +kernel

theorem node_context_12_283148_912294 : EJMOriginalGlobalDAGData.nodes 9 ⟨912294, by decide⟩ =
    .split (coordinate 12) (![⟨912226, by decide⟩,⟨912249, by decide⟩,⟨912283, by decide⟩,⟨912293, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_283148_912294 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283148 ⟨912294, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 283148
    ⟨912294, by decide⟩ (by decide) (![⟨912226, by decide⟩,⟨912249, by decide⟩,⟨912283, by decide⟩,⟨912293, by decide⟩]) unmarked_context_12_283148_912294 node_context_12_283148_912294
  intro a
  fin_cases a
  · exact context_13_1132592_912226
  · exact context_13_1132593_912249
  · exact context_13_1132594_912283
  · exact context_13_1132595_912293

theorem selected_cut_34911 : selected 9 ⟨912371, by decide⟩
    (prefixPartial 12 283149) = some ⟨12, 2, 0, 912371, 283149, 3881, 65536⟩ := by
  decide +kernel

theorem context_12_283149_912371 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283149 ⟨912371, by decide⟩ :=
  accepted_of_selected 12 283149 ⟨912371, by decide⟩ ⟨12, 2, 0, 912371, 283149, 3881, 65536⟩
    (by decide) selected_cut_34911

theorem selected_cut_34912 : selected 9 ⟨912442, by decide⟩
    (prefixPartial 12 283150) = some ⟨12, 2, 0, 912442, 283150, 3953, 65536⟩ := by
  decide +kernel

theorem context_12_283150_912442 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283150 ⟨912442, by decide⟩ :=
  accepted_of_selected 12 283150 ⟨912442, by decide⟩ ⟨12, 2, 0, 912442, 283150, 3953, 65536⟩
    (by decide) selected_cut_34912

theorem selected_cut_34913 : selected 9 ⟨912529, by decide⟩
    (prefixPartial 12 283151) = some ⟨12, 2, 0, 912529, 283151, 3869, 65536⟩ := by
  decide +kernel

theorem context_12_283151_912529 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283151 ⟨912529, by decide⟩ :=
  accepted_of_selected 12 283151 ⟨912529, by decide⟩ ⟨12, 2, 0, 912529, 283151, 3869, 65536⟩
    (by decide) selected_cut_34913

theorem unmarked_context_11_70787_912530 : frontier 10 ⟨912530, by decide⟩
    (prefixCache 11 70787) (prefixPartial 11 70787) = false := by
  decide +kernel

theorem node_context_11_70787_912530 : EJMOriginalGlobalDAGData.nodes 10 ⟨912530, by decide⟩ =
    .split (coordinate 11) (![⟨912294, by decide⟩,⟨912371, by decide⟩,⟨912442, by decide⟩,⟨912529, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_70787_912530 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70787 ⟨912530, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 70787
    ⟨912530, by decide⟩ (by decide) (![⟨912294, by decide⟩,⟨912371, by decide⟩,⟨912442, by decide⟩,⟨912529, by decide⟩]) unmarked_context_11_70787_912530 node_context_11_70787_912530
  intro a
  fin_cases a
  · exact context_12_283148_912294
  · exact context_12_283149_912371
  · exact context_12_283150_912442
  · exact context_12_283151_912529

theorem unmarked_context_10_17696_912531 : frontier 11 ⟨912531, by decide⟩
    (prefixCache 10 17696) (prefixPartial 10 17696) = false := by
  decide +kernel

theorem node_context_10_17696_912531 : EJMOriginalGlobalDAGData.nodes 11 ⟨912531, by decide⟩ =
    .split (coordinate 10) (![⟨167448, by decide⟩,⟨911912, by decide⟩,⟨912176, by decide⟩,⟨912530, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17696_912531 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17696 ⟨912531, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17696
    ⟨912531, by decide⟩ (by decide) (![⟨167448, by decide⟩,⟨911912, by decide⟩,⟨912176, by decide⟩,⟨912530, by decide⟩]) unmarked_context_10_17696_912531 node_context_10_17696_912531
  intro a
  fin_cases a
  · exact context_11_70784_167448
  · exact context_11_70785_911912
  · exact context_11_70786_912176
  · exact context_11_70787_912530

theorem selected_cut_34914 : selected 9 ⟨912593, by decide⟩
    (prefixPartial 12 283152) = some ⟨12, 2, 0, 912593, 283152, 3253, 65536⟩ := by
  decide +kernel

theorem context_12_283152_912593 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283152 ⟨912593, by decide⟩ :=
  accepted_of_selected 12 283152 ⟨912593, by decide⟩ ⟨12, 2, 0, 912593, 283152, 3253, 65536⟩
    (by decide) selected_cut_34914

theorem selected_cut_34915 : selected 9 ⟨912637, by decide⟩
    (prefixPartial 12 283153) = some ⟨12, 2, 0, 912637, 283153, 2833, 65536⟩ := by
  decide +kernel

theorem context_12_283153_912637 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283153 ⟨912637, by decide⟩ :=
  accepted_of_selected 12 283153 ⟨912637, by decide⟩ ⟨12, 2, 0, 912637, 283153, 2833, 65536⟩
    (by decide) selected_cut_34915

theorem selected_cut_34916 : selected 9 ⟨912684, by decide⟩
    (prefixPartial 12 283154) = some ⟨12, 2, 0, 912684, 283154, 2901, 65536⟩ := by
  decide +kernel

theorem context_12_283154_912684 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283154 ⟨912684, by decide⟩ :=
  accepted_of_selected 12 283154 ⟨912684, by decide⟩ ⟨12, 2, 0, 912684, 283154, 2901, 65536⟩
    (by decide) selected_cut_34916

theorem selected_cut_34917 : selected 9 ⟨912742, by decide⟩
    (prefixPartial 12 283155) = some ⟨12, 2, 0, 912742, 283155, 3289, 65536⟩ := by
  decide +kernel

theorem context_12_283155_912742 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283155 ⟨912742, by decide⟩ :=
  accepted_of_selected 12 283155 ⟨912742, by decide⟩ ⟨12, 2, 0, 912742, 283155, 3289, 65536⟩
    (by decide) selected_cut_34917

theorem unmarked_context_11_70788_912743 : frontier 10 ⟨912743, by decide⟩
    (prefixCache 11 70788) (prefixPartial 11 70788) = false := by
  decide +kernel

theorem node_context_11_70788_912743 : EJMOriginalGlobalDAGData.nodes 10 ⟨912743, by decide⟩ =
    .split (coordinate 11) (![⟨912593, by decide⟩,⟨912637, by decide⟩,⟨912684, by decide⟩,⟨912742, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_70788_912743 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70788 ⟨912743, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 70788
    ⟨912743, by decide⟩ (by decide) (![⟨912593, by decide⟩,⟨912637, by decide⟩,⟨912684, by decide⟩,⟨912742, by decide⟩]) unmarked_context_11_70788_912743 node_context_11_70788_912743
  intro a
  fin_cases a
  · exact context_12_283152_912593
  · exact context_12_283153_912637
  · exact context_12_283154_912684
  · exact context_12_283155_912742

theorem selected_cut_34918 : selected 9 ⟨912806, by decide⟩
    (prefixPartial 12 283156) = some ⟨12, 2, 0, 912806, 283156, 3337, 65536⟩ := by
  decide +kernel

theorem context_12_283156_912806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283156 ⟨912806, by decide⟩ :=
  accepted_of_selected 12 283156 ⟨912806, by decide⟩ ⟨12, 2, 0, 912806, 283156, 3337, 65536⟩
    (by decide) selected_cut_34918

theorem selected_cut_34919 : selected 9 ⟨912854, by decide⟩
    (prefixPartial 12 283157) = some ⟨12, 2, 0, 912854, 283157, 2621, 65536⟩ := by
  decide +kernel

theorem context_12_283157_912854 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283157 ⟨912854, by decide⟩ :=
  accepted_of_selected 12 283157 ⟨912854, by decide⟩ ⟨12, 2, 0, 912854, 283157, 2621, 65536⟩
    (by decide) selected_cut_34919

theorem selected_cut_34920 : selected 9 ⟨912895, by decide⟩
    (prefixPartial 12 283158) = some ⟨12, 2, 0, 912895, 283158, 2769, 65536⟩ := by
  decide +kernel

theorem context_12_283158_912895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283158 ⟨912895, by decide⟩ :=
  accepted_of_selected 12 283158 ⟨912895, by decide⟩ ⟨12, 2, 0, 912895, 283158, 2769, 65536⟩
    (by decide) selected_cut_34920

theorem selected_cut_34921 : selected 9 ⟨912946, by decide⟩
    (prefixPartial 12 283159) = some ⟨12, 2, 0, 912946, 283159, 3073, 65536⟩ := by
  decide +kernel

theorem context_12_283159_912946 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283159 ⟨912946, by decide⟩ :=
  accepted_of_selected 12 283159 ⟨912946, by decide⟩ ⟨12, 2, 0, 912946, 283159, 3073, 65536⟩
    (by decide) selected_cut_34921

theorem unmarked_context_11_70789_912947 : frontier 10 ⟨912947, by decide⟩
    (prefixCache 11 70789) (prefixPartial 11 70789) = false := by
  decide +kernel

theorem node_context_11_70789_912947 : EJMOriginalGlobalDAGData.nodes 10 ⟨912947, by decide⟩ =
    .split (coordinate 11) (![⟨912806, by decide⟩,⟨912854, by decide⟩,⟨912895, by decide⟩,⟨912946, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_70789_912947 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70789 ⟨912947, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 70789
    ⟨912947, by decide⟩ (by decide) (![⟨912806, by decide⟩,⟨912854, by decide⟩,⟨912895, by decide⟩,⟨912946, by decide⟩]) unmarked_context_11_70789_912947 node_context_11_70789_912947
  intro a
  fin_cases a
  · exact context_12_283156_912806
  · exact context_12_283157_912854
  · exact context_12_283158_912895
  · exact context_12_283159_912946

theorem selected_cut_34922 : selected 9 ⟨913028, by decide⟩
    (prefixPartial 12 283160) = some ⟨12, 2, 0, 913028, 283160, 3957, 65536⟩ := by
  decide +kernel

theorem context_12_283160_913028 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283160 ⟨913028, by decide⟩ :=
  accepted_of_selected 12 283160 ⟨913028, by decide⟩ ⟨12, 2, 0, 913028, 283160, 3957, 65536⟩
    (by decide) selected_cut_34922

theorem selected_cut_34923 : selected 9 ⟨913095, by decide⟩
    (prefixPartial 12 283161) = some ⟨12, 2, 0, 913095, 283161, 3473, 65536⟩ := by
  decide +kernel

theorem context_12_283161_913095 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283161 ⟨913095, by decide⟩ :=
  accepted_of_selected 12 283161 ⟨913095, by decide⟩ ⟨12, 2, 0, 913095, 283161, 3473, 65536⟩
    (by decide) selected_cut_34923

theorem selected_cut_34924 : selected 9 ⟨893903, by decide⟩
    (prefixPartial 12 283162) = some ⟨12, 1, 0, 893903, 283162, 1, 65536⟩ := by
  decide +kernel

theorem context_12_283162_893903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283162 ⟨893903, by decide⟩ :=
  accepted_of_selected 12 283162 ⟨893903, by decide⟩ ⟨12, 1, 0, 893903, 283162, 1, 65536⟩
    (by decide) selected_cut_34924

theorem selected_cut_34925 : selected 9 ⟨913170, by decide⟩
    (prefixPartial 12 283163) = some ⟨12, 2, 0, 913170, 283163, 3941, 65536⟩ := by
  decide +kernel

theorem context_12_283163_913170 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283163 ⟨913170, by decide⟩ :=
  accepted_of_selected 12 283163 ⟨913170, by decide⟩ ⟨12, 2, 0, 913170, 283163, 3941, 65536⟩
    (by decide) selected_cut_34925

theorem unmarked_context_11_70790_913171 : frontier 10 ⟨913171, by decide⟩
    (prefixCache 11 70790) (prefixPartial 11 70790) = false := by
  decide +kernel

theorem node_context_11_70790_913171 : EJMOriginalGlobalDAGData.nodes 10 ⟨913171, by decide⟩ =
    .split (coordinate 11) (![⟨913028, by decide⟩,⟨913095, by decide⟩,⟨893903, by decide⟩,⟨913170, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_70790_913171 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70790 ⟨913171, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 70790
    ⟨913171, by decide⟩ (by decide) (![⟨913028, by decide⟩,⟨913095, by decide⟩,⟨893903, by decide⟩,⟨913170, by decide⟩]) unmarked_context_11_70790_913171 node_context_11_70790_913171
  intro a
  fin_cases a
  · exact context_12_283160_913028
  · exact context_12_283161_913095
  · exact context_12_283162_893903
  · exact context_12_283163_913170

theorem selected_cut_34926 : selected 8 ⟨913210, by decide⟩
    (prefixPartial 13 1132656) = some ⟨13, 2, 0, 913210, 1132656, 1813, 16384⟩ := by
  decide +kernel

theorem context_13_1132656_913210 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1132656 ⟨913210, by decide⟩ :=
  accepted_of_selected 13 1132656 ⟨913210, by decide⟩ ⟨13, 2, 0, 913210, 1132656, 1813, 16384⟩
    (by decide) selected_cut_34926

theorem selected_cut_34927 : selected 8 ⟨913223, by decide⟩
    (prefixPartial 13 1132657) = some ⟨13, 2, 0, 913223, 1132657, 677, 16384⟩ := by
  decide +kernel

theorem context_13_1132657_913223 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1132657 ⟨913223, by decide⟩ :=
  accepted_of_selected 13 1132657 ⟨913223, by decide⟩ ⟨13, 2, 0, 913223, 1132657, 677, 16384⟩
    (by decide) selected_cut_34927

theorem selected_cut_34928 : selected 8 ⟨913243, by decide⟩
    (prefixPartial 13 1132658) = some ⟨13, 2, 0, 913243, 1132658, 1241, 16384⟩ := by
  decide +kernel

theorem context_13_1132658_913243 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1132658 ⟨913243, by decide⟩ :=
  accepted_of_selected 13 1132658 ⟨913243, by decide⟩ ⟨13, 2, 0, 913243, 1132658, 1241, 16384⟩
    (by decide) selected_cut_34928

theorem selected_cut_34929 : selected 8 ⟨913250, by decide⟩
    (prefixPartial 13 1132659) = some ⟨13, 2, 0, 913250, 1132659, 573, 16384⟩ := by
  decide +kernel

theorem context_13_1132659_913250 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1132659 ⟨913250, by decide⟩ :=
  accepted_of_selected 13 1132659 ⟨913250, by decide⟩ ⟨13, 2, 0, 913250, 1132659, 573, 16384⟩
    (by decide) selected_cut_34929

theorem unmarked_context_12_283164_913251 : frontier 9 ⟨913251, by decide⟩
    (prefixCache 12 283164) (prefixPartial 12 283164) = false := by
  decide +kernel

theorem node_context_12_283164_913251 : EJMOriginalGlobalDAGData.nodes 9 ⟨913251, by decide⟩ =
    .split (coordinate 12) (![⟨913210, by decide⟩,⟨913223, by decide⟩,⟨913243, by decide⟩,⟨913250, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_283164_913251 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283164 ⟨913251, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 283164
    ⟨913251, by decide⟩ (by decide) (![⟨913210, by decide⟩,⟨913223, by decide⟩,⟨913243, by decide⟩,⟨913250, by decide⟩]) unmarked_context_12_283164_913251 node_context_12_283164_913251
  intro a
  fin_cases a
  · exact context_13_1132656_913210
  · exact context_13_1132657_913223
  · exact context_13_1132658_913243
  · exact context_13_1132659_913250

theorem selected_cut_34930 : selected 9 ⟨913322, by decide⟩
    (prefixPartial 12 283165) = some ⟨12, 2, 0, 913322, 283165, 3529, 65536⟩ := by
  decide +kernel

theorem context_12_283165_913322 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283165 ⟨913322, by decide⟩ :=
  accepted_of_selected 12 283165 ⟨913322, by decide⟩ ⟨12, 2, 0, 913322, 283165, 3529, 65536⟩
    (by decide) selected_cut_34930

theorem selected_cut_34931 : selected 9 ⟨913396, by decide⟩
    (prefixPartial 12 283166) = some ⟨12, 2, 0, 913396, 283166, 3965, 65536⟩ := by
  decide +kernel

theorem context_12_283166_913396 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283166 ⟨913396, by decide⟩ :=
  accepted_of_selected 12 283166 ⟨913396, by decide⟩ ⟨12, 2, 0, 913396, 283166, 3965, 65536⟩
    (by decide) selected_cut_34931

theorem selected_cut_34932 : selected 9 ⟨913471, by decide⟩
    (prefixPartial 12 283167) = some ⟨12, 2, 0, 913471, 283167, 3769, 65536⟩ := by
  decide +kernel

theorem context_12_283167_913471 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283167 ⟨913471, by decide⟩ :=
  accepted_of_selected 12 283167 ⟨913471, by decide⟩ ⟨12, 2, 0, 913471, 283167, 3769, 65536⟩
    (by decide) selected_cut_34932

theorem unmarked_context_11_70791_913472 : frontier 10 ⟨913472, by decide⟩
    (prefixCache 11 70791) (prefixPartial 11 70791) = false := by
  decide +kernel

theorem node_context_11_70791_913472 : EJMOriginalGlobalDAGData.nodes 10 ⟨913472, by decide⟩ =
    .split (coordinate 11) (![⟨913251, by decide⟩,⟨913322, by decide⟩,⟨913396, by decide⟩,⟨913471, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_70791_913472 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70791 ⟨913472, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 70791
    ⟨913472, by decide⟩ (by decide) (![⟨913251, by decide⟩,⟨913322, by decide⟩,⟨913396, by decide⟩,⟨913471, by decide⟩]) unmarked_context_11_70791_913472 node_context_11_70791_913472
  intro a
  fin_cases a
  · exact context_12_283164_913251
  · exact context_12_283165_913322
  · exact context_12_283166_913396
  · exact context_12_283167_913471

theorem unmarked_context_10_17697_913473 : frontier 11 ⟨913473, by decide⟩
    (prefixCache 10 17697) (prefixPartial 10 17697) = false := by
  decide +kernel

theorem node_context_10_17697_913473 : EJMOriginalGlobalDAGData.nodes 11 ⟨913473, by decide⟩ =
    .split (coordinate 10) (![⟨912743, by decide⟩,⟨912947, by decide⟩,⟨913171, by decide⟩,⟨913472, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17697_913473 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17697 ⟨913473, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17697
    ⟨913473, by decide⟩ (by decide) (![⟨912743, by decide⟩,⟨912947, by decide⟩,⟨913171, by decide⟩,⟨913472, by decide⟩]) unmarked_context_10_17697_913473 node_context_10_17697_913473
  intro a
  fin_cases a
  · exact context_11_70788_912743
  · exact context_11_70789_912947
  · exact context_11_70790_913171
  · exact context_11_70791_913472

theorem selected_cut_34933 : selected 9 ⟨913533, by decide⟩
    (prefixPartial 12 283168) = some ⟨12, 2, 0, 913533, 283168, 3241, 65536⟩ := by
  decide +kernel

theorem context_12_283168_913533 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283168 ⟨913533, by decide⟩ :=
  accepted_of_selected 12 283168 ⟨913533, by decide⟩ ⟨12, 2, 0, 913533, 283168, 3241, 65536⟩
    (by decide) selected_cut_34933

theorem selected_cut_34934 : selected 9 ⟨913584, by decide⟩
    (prefixPartial 12 283169) = some ⟨12, 2, 0, 913584, 283169, 2981, 65536⟩ := by
  decide +kernel

theorem context_12_283169_913584 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283169 ⟨913584, by decide⟩ :=
  accepted_of_selected 12 283169 ⟨913584, by decide⟩ ⟨12, 2, 0, 913584, 283169, 2981, 65536⟩
    (by decide) selected_cut_34934

theorem selected_cut_34935 : selected 9 ⟨913646, by decide⟩
    (prefixPartial 12 283170) = some ⟨12, 2, 0, 913646, 283170, 3133, 65536⟩ := by
  decide +kernel

theorem context_12_283170_913646 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283170 ⟨913646, by decide⟩ :=
  accepted_of_selected 12 283170 ⟨913646, by decide⟩ ⟨12, 2, 0, 913646, 283170, 3133, 65536⟩
    (by decide) selected_cut_34935

theorem selected_cut_34936 : selected 9 ⟨913703, by decide⟩
    (prefixPartial 12 283171) = some ⟨12, 2, 0, 913703, 283171, 3105, 65536⟩ := by
  decide +kernel

theorem context_12_283171_913703 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283171 ⟨913703, by decide⟩ :=
  accepted_of_selected 12 283171 ⟨913703, by decide⟩ ⟨12, 2, 0, 913703, 283171, 3105, 65536⟩
    (by decide) selected_cut_34936

theorem unmarked_context_11_70792_913704 : frontier 10 ⟨913704, by decide⟩
    (prefixCache 11 70792) (prefixPartial 11 70792) = false := by
  decide +kernel

theorem node_context_11_70792_913704 : EJMOriginalGlobalDAGData.nodes 10 ⟨913704, by decide⟩ =
    .split (coordinate 11) (![⟨913533, by decide⟩,⟨913584, by decide⟩,⟨913646, by decide⟩,⟨913703, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_70792_913704 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70792 ⟨913704, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 70792
    ⟨913704, by decide⟩ (by decide) (![⟨913533, by decide⟩,⟨913584, by decide⟩,⟨913646, by decide⟩,⟨913703, by decide⟩]) unmarked_context_11_70792_913704 node_context_11_70792_913704
  intro a
  fin_cases a
  · exact context_12_283168_913533
  · exact context_12_283169_913584
  · exact context_12_283170_913646
  · exact context_12_283171_913703

theorem selected_cut_34937 : selected 9 ⟨913760, by decide⟩
    (prefixPartial 12 283172) = some ⟨12, 2, 0, 913760, 283172, 3101, 65536⟩ := by
  decide +kernel

theorem context_12_283172_913760 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283172 ⟨913760, by decide⟩ :=
  accepted_of_selected 12 283172 ⟨913760, by decide⟩ ⟨12, 2, 0, 913760, 283172, 3101, 65536⟩
    (by decide) selected_cut_34937

theorem selected_cut_34938 : selected 9 ⟨913806, by decide⟩
    (prefixPartial 12 283173) = some ⟨12, 2, 0, 913806, 283173, 2821, 65536⟩ := by
  decide +kernel

theorem context_12_283173_913806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283173 ⟨913806, by decide⟩ :=
  accepted_of_selected 12 283173 ⟨913806, by decide⟩ ⟨12, 2, 0, 913806, 283173, 2821, 65536⟩
    (by decide) selected_cut_34938

theorem selected_cut_34939 : selected 9 ⟨913854, by decide⟩
    (prefixPartial 12 283174) = some ⟨12, 2, 0, 913854, 283174, 2825, 65536⟩ := by
  decide +kernel

theorem context_12_283174_913854 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283174 ⟨913854, by decide⟩ :=
  accepted_of_selected 12 283174 ⟨913854, by decide⟩ ⟨12, 2, 0, 913854, 283174, 2825, 65536⟩
    (by decide) selected_cut_34939

theorem selected_cut_34940 : selected 9 ⟨913907, by decide⟩
    (prefixPartial 12 283175) = some ⟨12, 2, 0, 913907, 283175, 2833, 65536⟩ := by
  decide +kernel

theorem context_12_283175_913907 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283175 ⟨913907, by decide⟩ :=
  accepted_of_selected 12 283175 ⟨913907, by decide⟩ ⟨12, 2, 0, 913907, 283175, 2833, 65536⟩
    (by decide) selected_cut_34940

theorem unmarked_context_11_70793_913908 : frontier 10 ⟨913908, by decide⟩
    (prefixCache 11 70793) (prefixPartial 11 70793) = false := by
  decide +kernel

theorem node_context_11_70793_913908 : EJMOriginalGlobalDAGData.nodes 10 ⟨913908, by decide⟩ =
    .split (coordinate 11) (![⟨913760, by decide⟩,⟨913806, by decide⟩,⟨913854, by decide⟩,⟨913907, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_70793_913908 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70793 ⟨913908, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 70793
    ⟨913908, by decide⟩ (by decide) (![⟨913760, by decide⟩,⟨913806, by decide⟩,⟨913854, by decide⟩,⟨913907, by decide⟩]) unmarked_context_11_70793_913908 node_context_11_70793_913908
  intro a
  fin_cases a
  · exact context_12_283172_913760
  · exact context_12_283173_913806
  · exact context_12_283174_913854
  · exact context_12_283175_913907

theorem selected_cut_34941 : selected 9 ⟨913972, by decide⟩
    (prefixPartial 12 283176) = some ⟨12, 2, 0, 913972, 283176, 3549, 65536⟩ := by
  decide +kernel

theorem context_12_283176_913972 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283176 ⟨913972, by decide⟩ :=
  accepted_of_selected 12 283176 ⟨913972, by decide⟩ ⟨12, 2, 0, 913972, 283176, 3549, 65536⟩
    (by decide) selected_cut_34941

theorem selected_cut_34942 : selected 9 ⟨914044, by decide⟩
    (prefixPartial 12 283177) = some ⟨12, 2, 0, 914044, 283177, 3573, 65536⟩ := by
  decide +kernel

theorem context_12_283177_914044 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283177 ⟨914044, by decide⟩ :=
  accepted_of_selected 12 283177 ⟨914044, by decide⟩ ⟨12, 2, 0, 914044, 283177, 3573, 65536⟩
    (by decide) selected_cut_34942

theorem selected_cut_34943 : selected 9 ⟨242157, by decide⟩
    (prefixPartial 12 283178) = some ⟨12, 1, 0, 242157, 283178, 1, 65536⟩ := by
  decide +kernel

theorem context_12_283178_242157 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283178 ⟨242157, by decide⟩ :=
  accepted_of_selected 12 283178 ⟨242157, by decide⟩ ⟨12, 1, 0, 242157, 283178, 1, 65536⟩
    (by decide) selected_cut_34943

theorem selected_cut_34944 : selected 9 ⟨914114, by decide⟩
    (prefixPartial 12 283179) = some ⟨12, 2, 0, 914114, 283179, 3441, 65536⟩ := by
  decide +kernel

theorem context_12_283179_914114 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283179 ⟨914114, by decide⟩ :=
  accepted_of_selected 12 283179 ⟨914114, by decide⟩ ⟨12, 2, 0, 914114, 283179, 3441, 65536⟩
    (by decide) selected_cut_34944

theorem unmarked_context_11_70794_914115 : frontier 10 ⟨914115, by decide⟩
    (prefixCache 11 70794) (prefixPartial 11 70794) = false := by
  decide +kernel

theorem node_context_11_70794_914115 : EJMOriginalGlobalDAGData.nodes 10 ⟨914115, by decide⟩ =
    .split (coordinate 11) (![⟨913972, by decide⟩,⟨914044, by decide⟩,⟨242157, by decide⟩,⟨914114, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_70794_914115 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70794 ⟨914115, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 70794
    ⟨914115, by decide⟩ (by decide) (![⟨913972, by decide⟩,⟨914044, by decide⟩,⟨242157, by decide⟩,⟨914114, by decide⟩]) unmarked_context_11_70794_914115 node_context_11_70794_914115
  intro a
  fin_cases a
  · exact context_12_283176_913972
  · exact context_12_283177_914044
  · exact context_12_283178_242157
  · exact context_12_283179_914114

theorem selected_cut_34945 : selected 9 ⟨914189, by decide⟩
    (prefixPartial 12 283180) = some ⟨12, 2, 0, 914189, 283180, 3841, 65536⟩ := by
  decide +kernel

theorem context_12_283180_914189 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283180 ⟨914189, by decide⟩ :=
  accepted_of_selected 12 283180 ⟨914189, by decide⟩ ⟨12, 2, 0, 914189, 283180, 3841, 65536⟩
    (by decide) selected_cut_34945

theorem selected_cut_34946 : selected 9 ⟨914255, by decide⟩
    (prefixPartial 12 283181) = some ⟨12, 2, 0, 914255, 283181, 3729, 65536⟩ := by
  decide +kernel

theorem context_12_283181_914255 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 283181 ⟨914255, by decide⟩ :=
  accepted_of_selected 12 283181 ⟨914255, by decide⟩ ⟨12, 2, 0, 914255, 283181, 3729, 65536⟩
    (by decide) selected_cut_34946

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
