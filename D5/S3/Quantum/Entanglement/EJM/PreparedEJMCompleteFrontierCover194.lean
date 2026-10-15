/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover193
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_18627 : selected 8 ⟨476704, by decide⟩
    (prefixPartial 13 287055) = some ⟨13, 2, 0, 476704, 287055, 789, 16384⟩ := by
  decide +kernel

theorem context_13_287055_476704 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287055 ⟨476704, by decide⟩ :=
  accepted_of_selected 13 287055 ⟨476704, by decide⟩ ⟨13, 2, 0, 476704, 287055, 789, 16384⟩
    (by decide) selected_cut_18627

theorem unmarked_context_12_71763_476705 : frontier 9 ⟨476705, by decide⟩
    (prefixCache 12 71763) (prefixPartial 12 71763) = false := by
  decide +kernel

theorem node_context_12_71763_476705 : EJMOriginalGlobalDAGData.nodes 9 ⟨476705, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨476682, by decide⟩,⟨476698, by decide⟩,⟨476704, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71763_476705 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71763 ⟨476705, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71763
    ⟨476705, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨476682, by decide⟩,⟨476698, by decide⟩,⟨476704, by decide⟩]) unmarked_context_12_71763_476705 node_context_12_71763_476705
  intro a
  fin_cases a
  · exact context_13_287052_3444
  · exact context_13_287053_476682
  · exact context_13_287054_476698
  · exact context_13_287055_476704

theorem unmarked_context_11_17940_476706 : frontier 10 ⟨476706, by decide⟩
    (prefixCache 11 17940) (prefixPartial 11 17940) = false := by
  decide +kernel

theorem node_context_11_17940_476706 : EJMOriginalGlobalDAGData.nodes 10 ⟨476706, by decide⟩ =
    .split (coordinate 11) (![⟨476560, by decide⟩,⟨476609, by decide⟩,⟨476657, by decide⟩,⟨476705, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17940_476706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17940 ⟨476706, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17940
    ⟨476706, by decide⟩ (by decide) (![⟨476560, by decide⟩,⟨476609, by decide⟩,⟨476657, by decide⟩,⟨476705, by decide⟩]) unmarked_context_11_17940_476706 node_context_11_17940_476706
  intro a
  fin_cases a
  · exact context_12_71760_476560
  · exact context_12_71761_476609
  · exact context_12_71762_476657
  · exact context_12_71763_476705

theorem selected_cut_18628 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 287056) = some ⟨13, 1, 0, 3444, 287056, 1, 16384⟩ := by
  decide +kernel

theorem context_13_287056_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287056 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 287056 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 287056, 1, 16384⟩
    (by decide) selected_cut_18628

theorem selected_cut_18629 : selected 8 ⟨476724, by decide⟩
    (prefixPartial 13 287057) = some ⟨13, 2, 0, 476724, 287057, 1729, 16384⟩ := by
  decide +kernel

theorem context_13_287057_476724 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287057 ⟨476724, by decide⟩ :=
  accepted_of_selected 13 287057 ⟨476724, by decide⟩ ⟨13, 2, 0, 476724, 287057, 1729, 16384⟩
    (by decide) selected_cut_18629

theorem selected_cut_18630 : selected 8 ⟨476746, by decide⟩
    (prefixPartial 13 287058) = some ⟨13, 2, 0, 476746, 287058, 1693, 16384⟩ := by
  decide +kernel

theorem context_13_287058_476746 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287058 ⟨476746, by decide⟩ :=
  accepted_of_selected 13 287058 ⟨476746, by decide⟩ ⟨13, 2, 0, 476746, 287058, 1693, 16384⟩
    (by decide) selected_cut_18630

theorem selected_cut_18631 : selected 8 ⟨476756, by decide⟩
    (prefixPartial 13 287059) = some ⟨13, 2, 0, 476756, 287059, 1001, 16384⟩ := by
  decide +kernel

theorem context_13_287059_476756 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287059 ⟨476756, by decide⟩ :=
  accepted_of_selected 13 287059 ⟨476756, by decide⟩ ⟨13, 2, 0, 476756, 287059, 1001, 16384⟩
    (by decide) selected_cut_18631

theorem unmarked_context_12_71764_476757 : frontier 9 ⟨476757, by decide⟩
    (prefixCache 12 71764) (prefixPartial 12 71764) = false := by
  decide +kernel

theorem node_context_12_71764_476757 : EJMOriginalGlobalDAGData.nodes 9 ⟨476757, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨476724, by decide⟩,⟨476746, by decide⟩,⟨476756, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71764_476757 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71764 ⟨476757, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71764
    ⟨476757, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨476724, by decide⟩,⟨476746, by decide⟩,⟨476756, by decide⟩]) unmarked_context_12_71764_476757 node_context_12_71764_476757
  intro a
  fin_cases a
  · exact context_13_287056_3444
  · exact context_13_287057_476724
  · exact context_13_287058_476746
  · exact context_13_287059_476756

theorem selected_cut_18632 : selected 9 ⟨476811, by decide⟩
    (prefixPartial 12 71765) = some ⟨12, 2, 0, 476811, 71765, 4081, 65536⟩ := by
  decide +kernel

theorem context_12_71765_476811 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71765 ⟨476811, by decide⟩ :=
  accepted_of_selected 12 71765 ⟨476811, by decide⟩ ⟨12, 2, 0, 476811, 71765, 4081, 65536⟩
    (by decide) selected_cut_18632

theorem selected_cut_18633 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 287064) = some ⟨13, 1, 0, 3444, 287064, 1, 16384⟩ := by
  decide +kernel

theorem context_13_287064_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287064 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 287064 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 287064, 1, 16384⟩
    (by decide) selected_cut_18633

theorem selected_cut_18634 : selected 8 ⟨476843, by decide⟩
    (prefixPartial 13 287065) = some ⟨13, 2, 0, 476843, 287065, 2021, 16384⟩ := by
  decide +kernel

theorem context_13_287065_476843 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287065 ⟨476843, by decide⟩ :=
  accepted_of_selected 13 287065 ⟨476843, by decide⟩ ⟨13, 2, 0, 476843, 287065, 2021, 16384⟩
    (by decide) selected_cut_18634

theorem selected_cut_18635 : selected 8 ⟨476874, by decide⟩
    (prefixPartial 13 287066) = some ⟨13, 2, 0, 476874, 287066, 1861, 16384⟩ := by
  decide +kernel

theorem context_13_287066_476874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287066 ⟨476874, by decide⟩ :=
  accepted_of_selected 13 287066 ⟨476874, by decide⟩ ⟨13, 2, 0, 476874, 287066, 1861, 16384⟩
    (by decide) selected_cut_18635

theorem selected_cut_18636 : selected 8 ⟨476883, by decide⟩
    (prefixPartial 13 287067) = some ⟨13, 2, 0, 476883, 287067, 1041, 16384⟩ := by
  decide +kernel

theorem context_13_287067_476883 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287067 ⟨476883, by decide⟩ :=
  accepted_of_selected 13 287067 ⟨476883, by decide⟩ ⟨13, 2, 0, 476883, 287067, 1041, 16384⟩
    (by decide) selected_cut_18636

theorem unmarked_context_12_71766_476884 : frontier 9 ⟨476884, by decide⟩
    (prefixCache 12 71766) (prefixPartial 12 71766) = false := by
  decide +kernel

theorem node_context_12_71766_476884 : EJMOriginalGlobalDAGData.nodes 9 ⟨476884, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨476843, by decide⟩,⟨476874, by decide⟩,⟨476883, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71766_476884 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71766 ⟨476884, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71766
    ⟨476884, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨476843, by decide⟩,⟨476874, by decide⟩,⟨476883, by decide⟩]) unmarked_context_12_71766_476884 node_context_12_71766_476884
  intro a
  fin_cases a
  · exact context_13_287064_3444
  · exact context_13_287065_476843
  · exact context_13_287066_476874
  · exact context_13_287067_476883

theorem selected_cut_18637 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 287068) = some ⟨13, 1, 0, 3444, 287068, 1, 16384⟩ := by
  decide +kernel

theorem context_13_287068_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287068 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 287068 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 287068, 1, 16384⟩
    (by decide) selected_cut_18637

theorem selected_cut_18638 : selected 8 ⟨476923, by decide⟩
    (prefixPartial 13 287069) = some ⟨13, 2, 0, 476923, 287069, 2001, 16384⟩ := by
  decide +kernel

theorem context_13_287069_476923 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287069 ⟨476923, by decide⟩ :=
  accepted_of_selected 13 287069 ⟨476923, by decide⟩ ⟨13, 2, 0, 476923, 287069, 2001, 16384⟩
    (by decide) selected_cut_18638

theorem selected_cut_18639 : selected 8 ⟨476961, by decide⟩
    (prefixPartial 13 287070) = some ⟨13, 2, 0, 476961, 287070, 2077, 16384⟩ := by
  decide +kernel

theorem context_13_287070_476961 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287070 ⟨476961, by decide⟩ :=
  accepted_of_selected 13 287070 ⟨476961, by decide⟩ ⟨13, 2, 0, 476961, 287070, 2077, 16384⟩
    (by decide) selected_cut_18639

theorem selected_cut_18640 : selected 8 ⟨476969, by decide⟩
    (prefixPartial 13 287071) = some ⟨13, 2, 0, 476969, 287071, 921, 16384⟩ := by
  decide +kernel

theorem context_13_287071_476969 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287071 ⟨476969, by decide⟩ :=
  accepted_of_selected 13 287071 ⟨476969, by decide⟩ ⟨13, 2, 0, 476969, 287071, 921, 16384⟩
    (by decide) selected_cut_18640

theorem unmarked_context_12_71767_476970 : frontier 9 ⟨476970, by decide⟩
    (prefixCache 12 71767) (prefixPartial 12 71767) = false := by
  decide +kernel

theorem node_context_12_71767_476970 : EJMOriginalGlobalDAGData.nodes 9 ⟨476970, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨476923, by decide⟩,⟨476961, by decide⟩,⟨476969, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71767_476970 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71767 ⟨476970, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71767
    ⟨476970, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨476923, by decide⟩,⟨476961, by decide⟩,⟨476969, by decide⟩]) unmarked_context_12_71767_476970 node_context_12_71767_476970
  intro a
  fin_cases a
  · exact context_13_287068_3444
  · exact context_13_287069_476923
  · exact context_13_287070_476961
  · exact context_13_287071_476969

theorem unmarked_context_11_17941_476971 : frontier 10 ⟨476971, by decide⟩
    (prefixCache 11 17941) (prefixPartial 11 17941) = false := by
  decide +kernel

theorem node_context_11_17941_476971 : EJMOriginalGlobalDAGData.nodes 10 ⟨476971, by decide⟩ =
    .split (coordinate 11) (![⟨476757, by decide⟩,⟨476811, by decide⟩,⟨476884, by decide⟩,⟨476970, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17941_476971 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17941 ⟨476971, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17941
    ⟨476971, by decide⟩ (by decide) (![⟨476757, by decide⟩,⟨476811, by decide⟩,⟨476884, by decide⟩,⟨476970, by decide⟩]) unmarked_context_11_17941_476971 node_context_11_17941_476971
  intro a
  fin_cases a
  · exact context_12_71764_476757
  · exact context_12_71765_476811
  · exact context_12_71766_476884
  · exact context_12_71767_476970

theorem selected_cut_18641 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 287072) = some ⟨13, 1, 0, 3444, 287072, 1, 16384⟩ := by
  decide +kernel

theorem context_13_287072_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287072 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 287072 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 287072, 1, 16384⟩
    (by decide) selected_cut_18641

theorem selected_cut_18642 : selected 8 ⟨476986, by decide⟩
    (prefixPartial 13 287073) = some ⟨13, 2, 0, 476986, 287073, 1561, 16384⟩ := by
  decide +kernel

theorem context_13_287073_476986 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287073 ⟨476986, by decide⟩ :=
  accepted_of_selected 13 287073 ⟨476986, by decide⟩ ⟨13, 2, 0, 476986, 287073, 1561, 16384⟩
    (by decide) selected_cut_18642

theorem selected_cut_18643 : selected 8 ⟨477010, by decide⟩
    (prefixPartial 13 287074) = some ⟨13, 2, 0, 477010, 287074, 1617, 16384⟩ := by
  decide +kernel

theorem context_13_287074_477010 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287074 ⟨477010, by decide⟩ :=
  accepted_of_selected 13 287074 ⟨477010, by decide⟩ ⟨13, 2, 0, 477010, 287074, 1617, 16384⟩
    (by decide) selected_cut_18643

theorem selected_cut_18644 : selected 8 ⟨477019, by decide⟩
    (prefixPartial 13 287075) = some ⟨13, 2, 0, 477019, 287075, 993, 16384⟩ := by
  decide +kernel

theorem context_13_287075_477019 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287075 ⟨477019, by decide⟩ :=
  accepted_of_selected 13 287075 ⟨477019, by decide⟩ ⟨13, 2, 0, 477019, 287075, 993, 16384⟩
    (by decide) selected_cut_18644

theorem unmarked_context_12_71768_477020 : frontier 9 ⟨477020, by decide⟩
    (prefixCache 12 71768) (prefixPartial 12 71768) = false := by
  decide +kernel

theorem node_context_12_71768_477020 : EJMOriginalGlobalDAGData.nodes 9 ⟨477020, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨476986, by decide⟩,⟨477010, by decide⟩,⟨477019, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71768_477020 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71768 ⟨477020, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71768
    ⟨477020, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨476986, by decide⟩,⟨477010, by decide⟩,⟨477019, by decide⟩]) unmarked_context_12_71768_477020 node_context_12_71768_477020
  intro a
  fin_cases a
  · exact context_13_287072_3444
  · exact context_13_287073_476986
  · exact context_13_287074_477010
  · exact context_13_287075_477019

theorem selected_cut_18645 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 287076) = some ⟨13, 1, 0, 3444, 287076, 1, 16384⟩ := by
  decide +kernel

theorem context_13_287076_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287076 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 287076 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 287076, 1, 16384⟩
    (by decide) selected_cut_18645

theorem selected_cut_18646 : selected 8 ⟨477041, by decide⟩
    (prefixPartial 13 287077) = some ⟨13, 2, 0, 477041, 287077, 1465, 16384⟩ := by
  decide +kernel

theorem context_13_287077_477041 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287077 ⟨477041, by decide⟩ :=
  accepted_of_selected 13 287077 ⟨477041, by decide⟩ ⟨13, 2, 0, 477041, 287077, 1465, 16384⟩
    (by decide) selected_cut_18646

theorem selected_cut_18647 : selected 8 ⟨477072, by decide⟩
    (prefixPartial 13 287078) = some ⟨13, 2, 0, 477072, 287078, 1661, 16384⟩ := by
  decide +kernel

theorem context_13_287078_477072 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287078 ⟨477072, by decide⟩ :=
  accepted_of_selected 13 287078 ⟨477072, by decide⟩ ⟨13, 2, 0, 477072, 287078, 1661, 16384⟩
    (by decide) selected_cut_18647

theorem selected_cut_18648 : selected 8 ⟨477085, by decide⟩
    (prefixPartial 13 287079) = some ⟨13, 2, 0, 477085, 287079, 1105, 16384⟩ := by
  decide +kernel

theorem context_13_287079_477085 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287079 ⟨477085, by decide⟩ :=
  accepted_of_selected 13 287079 ⟨477085, by decide⟩ ⟨13, 2, 0, 477085, 287079, 1105, 16384⟩
    (by decide) selected_cut_18648

theorem unmarked_context_12_71769_477086 : frontier 9 ⟨477086, by decide⟩
    (prefixCache 12 71769) (prefixPartial 12 71769) = false := by
  decide +kernel

theorem node_context_12_71769_477086 : EJMOriginalGlobalDAGData.nodes 9 ⟨477086, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨477041, by decide⟩,⟨477072, by decide⟩,⟨477085, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71769_477086 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71769 ⟨477086, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71769
    ⟨477086, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨477041, by decide⟩,⟨477072, by decide⟩,⟨477085, by decide⟩]) unmarked_context_12_71769_477086 node_context_12_71769_477086
  intro a
  fin_cases a
  · exact context_13_287076_3444
  · exact context_13_287077_477041
  · exact context_13_287078_477072
  · exact context_13_287079_477085

theorem selected_cut_18649 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 287080) = some ⟨13, 1, 0, 3444, 287080, 1, 16384⟩ := by
  decide +kernel

theorem context_13_287080_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287080 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 287080 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 287080, 1, 16384⟩
    (by decide) selected_cut_18649

theorem selected_cut_18650 : selected 8 ⟨477104, by decide⟩
    (prefixPartial 13 287081) = some ⟨13, 2, 0, 477104, 287081, 1645, 16384⟩ := by
  decide +kernel

theorem context_13_287081_477104 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287081 ⟨477104, by decide⟩ :=
  accepted_of_selected 13 287081 ⟨477104, by decide⟩ ⟨13, 2, 0, 477104, 287081, 1645, 16384⟩
    (by decide) selected_cut_18650

theorem selected_cut_18651 : selected 8 ⟨477127, by decide⟩
    (prefixPartial 13 287082) = some ⟨13, 2, 0, 477127, 287082, 1725, 16384⟩ := by
  decide +kernel

theorem context_13_287082_477127 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287082 ⟨477127, by decide⟩ :=
  accepted_of_selected 13 287082 ⟨477127, by decide⟩ ⟨13, 2, 0, 477127, 287082, 1725, 16384⟩
    (by decide) selected_cut_18651

theorem selected_cut_18652 : selected 8 ⟨477137, by decide⟩
    (prefixPartial 13 287083) = some ⟨13, 2, 0, 477137, 287083, 1029, 16384⟩ := by
  decide +kernel

theorem context_13_287083_477137 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287083 ⟨477137, by decide⟩ :=
  accepted_of_selected 13 287083 ⟨477137, by decide⟩ ⟨13, 2, 0, 477137, 287083, 1029, 16384⟩
    (by decide) selected_cut_18652

theorem unmarked_context_12_71770_477138 : frontier 9 ⟨477138, by decide⟩
    (prefixCache 12 71770) (prefixPartial 12 71770) = false := by
  decide +kernel

theorem node_context_12_71770_477138 : EJMOriginalGlobalDAGData.nodes 9 ⟨477138, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨477104, by decide⟩,⟨477127, by decide⟩,⟨477137, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71770_477138 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71770 ⟨477138, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71770
    ⟨477138, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨477104, by decide⟩,⟨477127, by decide⟩,⟨477137, by decide⟩]) unmarked_context_12_71770_477138 node_context_12_71770_477138
  intro a
  fin_cases a
  · exact context_13_287080_3444
  · exact context_13_287081_477104
  · exact context_13_287082_477127
  · exact context_13_287083_477137

theorem selected_cut_18653 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 287084) = some ⟨13, 1, 0, 3444, 287084, 1, 16384⟩ := by
  decide +kernel

theorem context_13_287084_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287084 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 287084 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 287084, 1, 16384⟩
    (by decide) selected_cut_18653

theorem selected_cut_18654 : selected 8 ⟨477160, by decide⟩
    (prefixPartial 13 287085) = some ⟨13, 2, 0, 477160, 287085, 1669, 16384⟩ := by
  decide +kernel

theorem context_13_287085_477160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287085 ⟨477160, by decide⟩ :=
  accepted_of_selected 13 287085 ⟨477160, by decide⟩ ⟨13, 2, 0, 477160, 287085, 1669, 16384⟩
    (by decide) selected_cut_18654

theorem selected_cut_18655 : selected 8 ⟨477182, by decide⟩
    (prefixPartial 13 287086) = some ⟨13, 2, 0, 477182, 287086, 1941, 16384⟩ := by
  decide +kernel

theorem context_13_287086_477182 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287086 ⟨477182, by decide⟩ :=
  accepted_of_selected 13 287086 ⟨477182, by decide⟩ ⟨13, 2, 0, 477182, 287086, 1941, 16384⟩
    (by decide) selected_cut_18655

theorem selected_cut_18656 : selected 8 ⟨477189, by decide⟩
    (prefixPartial 13 287087) = some ⟨13, 2, 0, 477189, 287087, 989, 16384⟩ := by
  decide +kernel

theorem context_13_287087_477189 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287087 ⟨477189, by decide⟩ :=
  accepted_of_selected 13 287087 ⟨477189, by decide⟩ ⟨13, 2, 0, 477189, 287087, 989, 16384⟩
    (by decide) selected_cut_18656

theorem unmarked_context_12_71771_477190 : frontier 9 ⟨477190, by decide⟩
    (prefixCache 12 71771) (prefixPartial 12 71771) = false := by
  decide +kernel

theorem node_context_12_71771_477190 : EJMOriginalGlobalDAGData.nodes 9 ⟨477190, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨477160, by decide⟩,⟨477182, by decide⟩,⟨477189, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71771_477190 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71771 ⟨477190, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71771
    ⟨477190, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨477160, by decide⟩,⟨477182, by decide⟩,⟨477189, by decide⟩]) unmarked_context_12_71771_477190 node_context_12_71771_477190
  intro a
  fin_cases a
  · exact context_13_287084_3444
  · exact context_13_287085_477160
  · exact context_13_287086_477182
  · exact context_13_287087_477189

theorem unmarked_context_11_17942_477191 : frontier 10 ⟨477191, by decide⟩
    (prefixCache 11 17942) (prefixPartial 11 17942) = false := by
  decide +kernel

theorem node_context_11_17942_477191 : EJMOriginalGlobalDAGData.nodes 10 ⟨477191, by decide⟩ =
    .split (coordinate 11) (![⟨477020, by decide⟩,⟨477086, by decide⟩,⟨477138, by decide⟩,⟨477190, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17942_477191 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17942 ⟨477191, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17942
    ⟨477191, by decide⟩ (by decide) (![⟨477020, by decide⟩,⟨477086, by decide⟩,⟨477138, by decide⟩,⟨477190, by decide⟩]) unmarked_context_11_17942_477191 node_context_11_17942_477191
  intro a
  fin_cases a
  · exact context_12_71768_477020
  · exact context_12_71769_477086
  · exact context_12_71770_477138
  · exact context_12_71771_477190

theorem selected_cut_18657 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 287088) = some ⟨13, 1, 0, 3444, 287088, 1, 16384⟩ := by
  decide +kernel

theorem context_13_287088_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287088 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 287088 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 287088, 1, 16384⟩
    (by decide) selected_cut_18657

theorem selected_cut_18658 : selected 8 ⟨477204, by decide⟩
    (prefixPartial 13 287089) = some ⟨13, 2, 0, 477204, 287089, 1561, 16384⟩ := by
  decide +kernel

theorem context_13_287089_477204 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287089 ⟨477204, by decide⟩ :=
  accepted_of_selected 13 287089 ⟨477204, by decide⟩ ⟨13, 2, 0, 477204, 287089, 1561, 16384⟩
    (by decide) selected_cut_18658

theorem selected_cut_18659 : selected 8 ⟨477223, by decide⟩
    (prefixPartial 13 287090) = some ⟨13, 2, 0, 477223, 287090, 1737, 16384⟩ := by
  decide +kernel

theorem context_13_287090_477223 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287090 ⟨477223, by decide⟩ :=
  accepted_of_selected 13 287090 ⟨477223, by decide⟩ ⟨13, 2, 0, 477223, 287090, 1737, 16384⟩
    (by decide) selected_cut_18659

theorem selected_cut_18660 : selected 8 ⟨477230, by decide⟩
    (prefixPartial 13 287091) = some ⟨13, 2, 0, 477230, 287091, 985, 16384⟩ := by
  decide +kernel

theorem context_13_287091_477230 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287091 ⟨477230, by decide⟩ :=
  accepted_of_selected 13 287091 ⟨477230, by decide⟩ ⟨13, 2, 0, 477230, 287091, 985, 16384⟩
    (by decide) selected_cut_18660

theorem unmarked_context_12_71772_477231 : frontier 9 ⟨477231, by decide⟩
    (prefixCache 12 71772) (prefixPartial 12 71772) = false := by
  decide +kernel

theorem node_context_12_71772_477231 : EJMOriginalGlobalDAGData.nodes 9 ⟨477231, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨477204, by decide⟩,⟨477223, by decide⟩,⟨477230, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71772_477231 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71772 ⟨477231, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71772
    ⟨477231, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨477204, by decide⟩,⟨477223, by decide⟩,⟨477230, by decide⟩]) unmarked_context_12_71772_477231 node_context_12_71772_477231
  intro a
  fin_cases a
  · exact context_13_287088_3444
  · exact context_13_287089_477204
  · exact context_13_287090_477223
  · exact context_13_287091_477230

theorem selected_cut_18661 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 287092) = some ⟨13, 1, 0, 3444, 287092, 1, 16384⟩ := by
  decide +kernel

theorem context_13_287092_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287092 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 287092 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 287092, 1, 16384⟩
    (by decide) selected_cut_18661

theorem selected_cut_18662 : selected 8 ⟨477247, by decide⟩
    (prefixPartial 13 287093) = some ⟨13, 2, 0, 477247, 287093, 1413, 16384⟩ := by
  decide +kernel

theorem context_13_287093_477247 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287093 ⟨477247, by decide⟩ :=
  accepted_of_selected 13 287093 ⟨477247, by decide⟩ ⟨13, 2, 0, 477247, 287093, 1413, 16384⟩
    (by decide) selected_cut_18662

theorem selected_cut_18663 : selected 8 ⟨477268, by decide⟩
    (prefixPartial 13 287094) = some ⟨13, 2, 0, 477268, 287094, 1801, 16384⟩ := by
  decide +kernel

theorem context_13_287094_477268 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287094 ⟨477268, by decide⟩ :=
  accepted_of_selected 13 287094 ⟨477268, by decide⟩ ⟨13, 2, 0, 477268, 287094, 1801, 16384⟩
    (by decide) selected_cut_18663

theorem selected_cut_18664 : selected 8 ⟨477276, by decide⟩
    (prefixPartial 13 287095) = some ⟨13, 2, 0, 477276, 287095, 1089, 16384⟩ := by
  decide +kernel

theorem context_13_287095_477276 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287095 ⟨477276, by decide⟩ :=
  accepted_of_selected 13 287095 ⟨477276, by decide⟩ ⟨13, 2, 0, 477276, 287095, 1089, 16384⟩
    (by decide) selected_cut_18664

theorem unmarked_context_12_71773_477277 : frontier 9 ⟨477277, by decide⟩
    (prefixCache 12 71773) (prefixPartial 12 71773) = false := by
  decide +kernel

theorem node_context_12_71773_477277 : EJMOriginalGlobalDAGData.nodes 9 ⟨477277, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨477247, by decide⟩,⟨477268, by decide⟩,⟨477276, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71773_477277 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71773 ⟨477277, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71773
    ⟨477277, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨477247, by decide⟩,⟨477268, by decide⟩,⟨477276, by decide⟩]) unmarked_context_12_71773_477277 node_context_12_71773_477277
  intro a
  fin_cases a
  · exact context_13_287092_3444
  · exact context_13_287093_477247
  · exact context_13_287094_477268
  · exact context_13_287095_477276

theorem selected_cut_18665 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 287096) = some ⟨13, 1, 0, 3444, 287096, 1, 16384⟩ := by
  decide +kernel

theorem context_13_287096_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287096 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 287096 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 287096, 1, 16384⟩
    (by decide) selected_cut_18665

theorem selected_cut_18666 : selected 8 ⟨477300, by decide⟩
    (prefixPartial 13 287097) = some ⟨13, 2, 0, 477300, 287097, 1637, 16384⟩ := by
  decide +kernel

theorem context_13_287097_477300 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287097 ⟨477300, by decide⟩ :=
  accepted_of_selected 13 287097 ⟨477300, by decide⟩ ⟨13, 2, 0, 477300, 287097, 1637, 16384⟩
    (by decide) selected_cut_18666

theorem selected_cut_18667 : selected 8 ⟨477323, by decide⟩
    (prefixPartial 13 287098) = some ⟨13, 2, 0, 477323, 287098, 1965, 16384⟩ := by
  decide +kernel

theorem context_13_287098_477323 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287098 ⟨477323, by decide⟩ :=
  accepted_of_selected 13 287098 ⟨477323, by decide⟩ ⟨13, 2, 0, 477323, 287098, 1965, 16384⟩
    (by decide) selected_cut_18667

theorem selected_cut_18668 : selected 8 ⟨477329, by decide⟩
    (prefixPartial 13 287099) = some ⟨13, 2, 0, 477329, 287099, 1061, 16384⟩ := by
  decide +kernel

theorem context_13_287099_477329 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287099 ⟨477329, by decide⟩ :=
  accepted_of_selected 13 287099 ⟨477329, by decide⟩ ⟨13, 2, 0, 477329, 287099, 1061, 16384⟩
    (by decide) selected_cut_18668

theorem unmarked_context_12_71774_477330 : frontier 9 ⟨477330, by decide⟩
    (prefixCache 12 71774) (prefixPartial 12 71774) = false := by
  decide +kernel

theorem node_context_12_71774_477330 : EJMOriginalGlobalDAGData.nodes 9 ⟨477330, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨477300, by decide⟩,⟨477323, by decide⟩,⟨477329, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71774_477330 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71774 ⟨477330, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71774
    ⟨477330, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨477300, by decide⟩,⟨477323, by decide⟩,⟨477329, by decide⟩]) unmarked_context_12_71774_477330 node_context_12_71774_477330
  intro a
  fin_cases a
  · exact context_13_287096_3444
  · exact context_13_287097_477300
  · exact context_13_287098_477323
  · exact context_13_287099_477329

theorem selected_cut_18669 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 287100) = some ⟨13, 1, 0, 3444, 287100, 1, 16384⟩ := by
  decide +kernel

theorem context_13_287100_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287100 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 287100 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 287100, 1, 16384⟩
    (by decide) selected_cut_18669

theorem selected_cut_18670 : selected 8 ⟨477347, by decide⟩
    (prefixPartial 13 287101) = some ⟨13, 2, 0, 477347, 287101, 1521, 16384⟩ := by
  decide +kernel

theorem context_13_287101_477347 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287101 ⟨477347, by decide⟩ :=
  accepted_of_selected 13 287101 ⟨477347, by decide⟩ ⟨13, 2, 0, 477347, 287101, 1521, 16384⟩
    (by decide) selected_cut_18670

theorem selected_cut_18671 : selected 8 ⟨477364, by decide⟩
    (prefixPartial 13 287102) = some ⟨13, 2, 0, 477364, 287102, 1925, 16384⟩ := by
  decide +kernel

theorem context_13_287102_477364 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287102 ⟨477364, by decide⟩ :=
  accepted_of_selected 13 287102 ⟨477364, by decide⟩ ⟨13, 2, 0, 477364, 287102, 1925, 16384⟩
    (by decide) selected_cut_18671

theorem selected_cut_18672 : selected 8 ⟨477373, by decide⟩
    (prefixPartial 13 287103) = some ⟨13, 2, 0, 477373, 287103, 893, 16384⟩ := by
  decide +kernel

theorem context_13_287103_477373 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287103 ⟨477373, by decide⟩ :=
  accepted_of_selected 13 287103 ⟨477373, by decide⟩ ⟨13, 2, 0, 477373, 287103, 893, 16384⟩
    (by decide) selected_cut_18672

theorem unmarked_context_12_71775_477374 : frontier 9 ⟨477374, by decide⟩
    (prefixCache 12 71775) (prefixPartial 12 71775) = false := by
  decide +kernel

theorem node_context_12_71775_477374 : EJMOriginalGlobalDAGData.nodes 9 ⟨477374, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨477347, by decide⟩,⟨477364, by decide⟩,⟨477373, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71775_477374 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71775 ⟨477374, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71775
    ⟨477374, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨477347, by decide⟩,⟨477364, by decide⟩,⟨477373, by decide⟩]) unmarked_context_12_71775_477374 node_context_12_71775_477374
  intro a
  fin_cases a
  · exact context_13_287100_3444
  · exact context_13_287101_477347
  · exact context_13_287102_477364
  · exact context_13_287103_477373

theorem unmarked_context_11_17943_477375 : frontier 10 ⟨477375, by decide⟩
    (prefixCache 11 17943) (prefixPartial 11 17943) = false := by
  decide +kernel

theorem node_context_11_17943_477375 : EJMOriginalGlobalDAGData.nodes 10 ⟨477375, by decide⟩ =
    .split (coordinate 11) (![⟨477231, by decide⟩,⟨477277, by decide⟩,⟨477330, by decide⟩,⟨477374, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17943_477375 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17943 ⟨477375, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17943
    ⟨477375, by decide⟩ (by decide) (![⟨477231, by decide⟩,⟨477277, by decide⟩,⟨477330, by decide⟩,⟨477374, by decide⟩]) unmarked_context_11_17943_477375 node_context_11_17943_477375
  intro a
  fin_cases a
  · exact context_12_71772_477231
  · exact context_12_71773_477277
  · exact context_12_71774_477330
  · exact context_12_71775_477374

theorem unmarked_context_10_4485_477376 : frontier 11 ⟨477376, by decide⟩
    (prefixCache 10 4485) (prefixPartial 10 4485) = false := by
  decide +kernel

theorem node_context_10_4485_477376 : EJMOriginalGlobalDAGData.nodes 11 ⟨477376, by decide⟩ =
    .split (coordinate 10) (![⟨476706, by decide⟩,⟨476971, by decide⟩,⟨477191, by decide⟩,⟨477375, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4485_477376 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4485 ⟨477376, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4485
    ⟨477376, by decide⟩ (by decide) (![⟨476706, by decide⟩,⟨476971, by decide⟩,⟨477191, by decide⟩,⟨477375, by decide⟩]) unmarked_context_10_4485_477376 node_context_10_4485_477376
  intro a
  fin_cases a
  · exact context_11_17940_476706
  · exact context_11_17941_476971
  · exact context_11_17942_477191
  · exact context_11_17943_477375

theorem selected_cut_18673 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 287104) = some ⟨13, 1, 0, 3444, 287104, 1, 16384⟩ := by
  decide +kernel

theorem context_13_287104_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287104 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 287104 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 287104, 1, 16384⟩
    (by decide) selected_cut_18673

theorem selected_cut_18674 : selected 8 ⟨477415, by decide⟩
    (prefixPartial 13 287105) = some ⟨13, 2, 0, 477415, 287105, 1889, 16384⟩ := by
  decide +kernel

theorem context_13_287105_477415 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287105 ⟨477415, by decide⟩ :=
  accepted_of_selected 13 287105 ⟨477415, by decide⟩ ⟨13, 2, 0, 477415, 287105, 1889, 16384⟩
    (by decide) selected_cut_18674

theorem selected_cut_18675 : selected 8 ⟨477461, by decide⟩
    (prefixPartial 13 287106) = some ⟨13, 2, 0, 477461, 287106, 2193, 16384⟩ := by
  decide +kernel

theorem context_13_287106_477461 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287106 ⟨477461, by decide⟩ :=
  accepted_of_selected 13 287106 ⟨477461, by decide⟩ ⟨13, 2, 0, 477461, 287106, 2193, 16384⟩
    (by decide) selected_cut_18675

theorem selected_cut_18676 : selected 8 ⟨477471, by decide⟩
    (prefixPartial 13 287107) = some ⟨13, 2, 0, 477471, 287107, 1097, 16384⟩ := by
  decide +kernel

theorem context_13_287107_477471 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287107 ⟨477471, by decide⟩ :=
  accepted_of_selected 13 287107 ⟨477471, by decide⟩ ⟨13, 2, 0, 477471, 287107, 1097, 16384⟩
    (by decide) selected_cut_18676

theorem unmarked_context_12_71776_477472 : frontier 9 ⟨477472, by decide⟩
    (prefixCache 12 71776) (prefixPartial 12 71776) = false := by
  decide +kernel

theorem node_context_12_71776_477472 : EJMOriginalGlobalDAGData.nodes 9 ⟨477472, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨477415, by decide⟩,⟨477461, by decide⟩,⟨477471, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71776_477472 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71776 ⟨477472, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71776
    ⟨477472, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨477415, by decide⟩,⟨477461, by decide⟩,⟨477471, by decide⟩]) unmarked_context_12_71776_477472 node_context_12_71776_477472
  intro a
  fin_cases a
  · exact context_13_287104_3444
  · exact context_13_287105_477415
  · exact context_13_287106_477461
  · exact context_13_287107_477471

theorem selected_cut_18677 : selected 9 ⟨477507, by decide⟩
    (prefixPartial 12 71777) = some ⟨12, 2, 0, 477507, 71777, 3349, 65536⟩ := by
  decide +kernel

theorem context_12_71777_477507 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71777 ⟨477507, by decide⟩ :=
  accepted_of_selected 12 71777 ⟨477507, by decide⟩ ⟨12, 2, 0, 477507, 71777, 3349, 65536⟩
    (by decide) selected_cut_18677

theorem selected_cut_18678 : selected 9 ⟨477556, by decide⟩
    (prefixPartial 12 71778) = some ⟨12, 2, 0, 477556, 71778, 3749, 65536⟩ := by
  decide +kernel

theorem context_12_71778_477556 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71778 ⟨477556, by decide⟩ :=
  accepted_of_selected 12 71778 ⟨477556, by decide⟩ ⟨12, 2, 0, 477556, 71778, 3749, 65536⟩
    (by decide) selected_cut_18678

theorem selected_cut_18679 : selected 9 ⟨477590, by decide⟩
    (prefixPartial 12 71779) = some ⟨12, 2, 0, 477590, 71779, 3729, 65536⟩ := by
  decide +kernel

theorem context_12_71779_477590 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71779 ⟨477590, by decide⟩ :=
  accepted_of_selected 12 71779 ⟨477590, by decide⟩ ⟨12, 2, 0, 477590, 71779, 3729, 65536⟩
    (by decide) selected_cut_18679

theorem unmarked_context_11_17944_477591 : frontier 10 ⟨477591, by decide⟩
    (prefixCache 11 17944) (prefixPartial 11 17944) = false := by
  decide +kernel

theorem node_context_11_17944_477591 : EJMOriginalGlobalDAGData.nodes 10 ⟨477591, by decide⟩ =
    .split (coordinate 11) (![⟨477472, by decide⟩,⟨477507, by decide⟩,⟨477556, by decide⟩,⟨477590, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17944_477591 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17944 ⟨477591, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17944
    ⟨477591, by decide⟩ (by decide) (![⟨477472, by decide⟩,⟨477507, by decide⟩,⟨477556, by decide⟩,⟨477590, by decide⟩]) unmarked_context_11_17944_477591 node_context_11_17944_477591
  intro a
  fin_cases a
  · exact context_12_71776_477472
  · exact context_12_71777_477507
  · exact context_12_71778_477556
  · exact context_12_71779_477590

theorem selected_cut_18680 : selected 9 ⟨477637, by decide⟩
    (prefixPartial 12 71780) = some ⟨12, 2, 0, 477637, 71780, 3505, 65536⟩ := by
  decide +kernel

theorem context_12_71780_477637 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71780 ⟨477637, by decide⟩ :=
  accepted_of_selected 12 71780 ⟨477637, by decide⟩ ⟨12, 2, 0, 477637, 71780, 3505, 65536⟩
    (by decide) selected_cut_18680

theorem selected_cut_18681 : selected 9 ⟨477677, by decide⟩
    (prefixPartial 12 71781) = some ⟨12, 2, 0, 477677, 71781, 3173, 65536⟩ := by
  decide +kernel

theorem context_12_71781_477677 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71781 ⟨477677, by decide⟩ :=
  accepted_of_selected 12 71781 ⟨477677, by decide⟩ ⟨12, 2, 0, 477677, 71781, 3173, 65536⟩
    (by decide) selected_cut_18681

theorem selected_cut_18682 : selected 9 ⟨477732, by decide⟩
    (prefixPartial 12 71782) = some ⟨12, 2, 0, 477732, 71782, 3765, 65536⟩ := by
  decide +kernel

theorem context_12_71782_477732 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71782 ⟨477732, by decide⟩ :=
  accepted_of_selected 12 71782 ⟨477732, by decide⟩ ⟨12, 2, 0, 477732, 71782, 3765, 65536⟩
    (by decide) selected_cut_18682

theorem selected_cut_18683 : selected 9 ⟨477780, by decide⟩
    (prefixPartial 12 71783) = some ⟨12, 2, 0, 477780, 71783, 3829, 65536⟩ := by
  decide +kernel

theorem context_12_71783_477780 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71783 ⟨477780, by decide⟩ :=
  accepted_of_selected 12 71783 ⟨477780, by decide⟩ ⟨12, 2, 0, 477780, 71783, 3829, 65536⟩
    (by decide) selected_cut_18683

theorem unmarked_context_11_17945_477781 : frontier 10 ⟨477781, by decide⟩
    (prefixCache 11 17945) (prefixPartial 11 17945) = false := by
  decide +kernel

theorem node_context_11_17945_477781 : EJMOriginalGlobalDAGData.nodes 10 ⟨477781, by decide⟩ =
    .split (coordinate 11) (![⟨477637, by decide⟩,⟨477677, by decide⟩,⟨477732, by decide⟩,⟨477780, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17945_477781 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17945 ⟨477781, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17945
    ⟨477781, by decide⟩ (by decide) (![⟨477637, by decide⟩,⟨477677, by decide⟩,⟨477732, by decide⟩,⟨477780, by decide⟩]) unmarked_context_11_17945_477781 node_context_11_17945_477781
  intro a
  fin_cases a
  · exact context_12_71780_477637
  · exact context_12_71781_477677
  · exact context_12_71782_477732
  · exact context_12_71783_477780

theorem selected_cut_18684 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 287136) = some ⟨13, 1, 0, 3444, 287136, 1, 16384⟩ := by
  decide +kernel

theorem context_13_287136_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287136 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 287136 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 287136, 1, 16384⟩
    (by decide) selected_cut_18684

theorem selected_cut_18685 : selected 8 ⟨477801, by decide⟩
    (prefixPartial 13 287137) = some ⟨13, 2, 0, 477801, 287137, 1277, 16384⟩ := by
  decide +kernel

theorem context_13_287137_477801 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287137 ⟨477801, by decide⟩ :=
  accepted_of_selected 13 287137 ⟨477801, by decide⟩ ⟨13, 2, 0, 477801, 287137, 1277, 16384⟩
    (by decide) selected_cut_18685

theorem selected_cut_18686 : selected 8 ⟨477824, by decide⟩
    (prefixPartial 13 287138) = some ⟨13, 2, 0, 477824, 287138, 1933, 16384⟩ := by
  decide +kernel

theorem context_13_287138_477824 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287138 ⟨477824, by decide⟩ :=
  accepted_of_selected 13 287138 ⟨477824, by decide⟩ ⟨13, 2, 0, 477824, 287138, 1933, 16384⟩
    (by decide) selected_cut_18686

theorem selected_cut_18687 : selected 8 ⟨477830, by decide⟩
    (prefixPartial 13 287139) = some ⟨13, 2, 0, 477830, 287139, 1069, 16384⟩ := by
  decide +kernel

theorem context_13_287139_477830 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287139 ⟨477830, by decide⟩ :=
  accepted_of_selected 13 287139 ⟨477830, by decide⟩ ⟨13, 2, 0, 477830, 287139, 1069, 16384⟩
    (by decide) selected_cut_18687

theorem unmarked_context_12_71784_477831 : frontier 9 ⟨477831, by decide⟩
    (prefixCache 12 71784) (prefixPartial 12 71784) = false := by
  decide +kernel

theorem node_context_12_71784_477831 : EJMOriginalGlobalDAGData.nodes 9 ⟨477831, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨477801, by decide⟩,⟨477824, by decide⟩,⟨477830, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71784_477831 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71784 ⟨477831, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71784
    ⟨477831, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨477801, by decide⟩,⟨477824, by decide⟩,⟨477830, by decide⟩]) unmarked_context_12_71784_477831 node_context_12_71784_477831
  intro a
  fin_cases a
  · exact context_13_287136_3444
  · exact context_13_287137_477801
  · exact context_13_287138_477824
  · exact context_13_287139_477830

theorem selected_cut_18688 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 287140) = some ⟨13, 1, 0, 3444, 287140, 1, 16384⟩ := by
  decide +kernel

theorem context_13_287140_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287140 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 287140 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 287140, 1, 16384⟩
    (by decide) selected_cut_18688

theorem selected_cut_18689 : selected 8 ⟨477848, by decide⟩
    (prefixPartial 13 287141) = some ⟨13, 2, 0, 477848, 287141, 1157, 16384⟩ := by
  decide +kernel

theorem context_13_287141_477848 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287141 ⟨477848, by decide⟩ :=
  accepted_of_selected 13 287141 ⟨477848, by decide⟩ ⟨13, 2, 0, 477848, 287141, 1157, 16384⟩
    (by decide) selected_cut_18689

theorem selected_cut_18690 : selected 8 ⟨477878, by decide⟩
    (prefixPartial 13 287142) = some ⟨13, 2, 0, 477878, 287142, 1973, 16384⟩ := by
  decide +kernel

theorem context_13_287142_477878 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287142 ⟨477878, by decide⟩ :=
  accepted_of_selected 13 287142 ⟨477878, by decide⟩ ⟨13, 2, 0, 477878, 287142, 1973, 16384⟩
    (by decide) selected_cut_18690

theorem selected_cut_18691 : selected 8 ⟨477892, by decide⟩
    (prefixPartial 13 287143) = some ⟨13, 2, 0, 477892, 287143, 1181, 16384⟩ := by
  decide +kernel

theorem context_13_287143_477892 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287143 ⟨477892, by decide⟩ :=
  accepted_of_selected 13 287143 ⟨477892, by decide⟩ ⟨13, 2, 0, 477892, 287143, 1181, 16384⟩
    (by decide) selected_cut_18691

theorem unmarked_context_12_71785_477893 : frontier 9 ⟨477893, by decide⟩
    (prefixCache 12 71785) (prefixPartial 12 71785) = false := by
  decide +kernel

theorem node_context_12_71785_477893 : EJMOriginalGlobalDAGData.nodes 9 ⟨477893, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨477848, by decide⟩,⟨477878, by decide⟩,⟨477892, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71785_477893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71785 ⟨477893, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71785
    ⟨477893, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨477848, by decide⟩,⟨477878, by decide⟩,⟨477892, by decide⟩]) unmarked_context_12_71785_477893 node_context_12_71785_477893
  intro a
  fin_cases a
  · exact context_13_287140_3444
  · exact context_13_287141_477848
  · exact context_13_287142_477878
  · exact context_13_287143_477892

theorem selected_cut_18692 : selected 9 ⟨474208, by decide⟩
    (prefixPartial 12 71786) = some ⟨12, 1, 0, 474208, 71786, 1, 65536⟩ := by
  decide +kernel

theorem context_12_71786_474208 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71786 ⟨474208, by decide⟩ :=
  accepted_of_selected 12 71786 ⟨474208, by decide⟩ ⟨12, 1, 0, 474208, 71786, 1, 65536⟩
    (by decide) selected_cut_18692

theorem selected_cut_18693 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 287148) = some ⟨13, 1, 0, 3444, 287148, 1, 16384⟩ := by
  decide +kernel

theorem context_13_287148_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287148 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 287148 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 287148, 1, 16384⟩
    (by decide) selected_cut_18693

theorem selected_cut_18694 : selected 8 ⟨477922, by decide⟩
    (prefixPartial 13 287149) = some ⟨13, 2, 0, 477922, 287149, 1313, 16384⟩ := by
  decide +kernel

theorem context_13_287149_477922 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287149 ⟨477922, by decide⟩ :=
  accepted_of_selected 13 287149 ⟨477922, by decide⟩ ⟨13, 2, 0, 477922, 287149, 1313, 16384⟩
    (by decide) selected_cut_18694

theorem selected_cut_18695 : selected 8 ⟨477951, by decide⟩
    (prefixPartial 13 287150) = some ⟨13, 2, 0, 477951, 287150, 2161, 16384⟩ := by
  decide +kernel

theorem context_13_287150_477951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287150 ⟨477951, by decide⟩ :=
  accepted_of_selected 13 287150 ⟨477951, by decide⟩ ⟨13, 2, 0, 477951, 287150, 2161, 16384⟩
    (by decide) selected_cut_18695

theorem selected_cut_18696 : selected 8 ⟨477965, by decide⟩
    (prefixPartial 13 287151) = some ⟨13, 2, 0, 477965, 287151, 1153, 16384⟩ := by
  decide +kernel

theorem context_13_287151_477965 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287151 ⟨477965, by decide⟩ :=
  accepted_of_selected 13 287151 ⟨477965, by decide⟩ ⟨13, 2, 0, 477965, 287151, 1153, 16384⟩
    (by decide) selected_cut_18696

theorem unmarked_context_12_71787_477966 : frontier 9 ⟨477966, by decide⟩
    (prefixCache 12 71787) (prefixPartial 12 71787) = false := by
  decide +kernel

theorem node_context_12_71787_477966 : EJMOriginalGlobalDAGData.nodes 9 ⟨477966, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨477922, by decide⟩,⟨477951, by decide⟩,⟨477965, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71787_477966 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71787 ⟨477966, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71787
    ⟨477966, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨477922, by decide⟩,⟨477951, by decide⟩,⟨477965, by decide⟩]) unmarked_context_12_71787_477966 node_context_12_71787_477966
  intro a
  fin_cases a
  · exact context_13_287148_3444
  · exact context_13_287149_477922
  · exact context_13_287150_477951
  · exact context_13_287151_477965

theorem unmarked_context_11_17946_477967 : frontier 10 ⟨477967, by decide⟩
    (prefixCache 11 17946) (prefixPartial 11 17946) = false := by
  decide +kernel

theorem node_context_11_17946_477967 : EJMOriginalGlobalDAGData.nodes 10 ⟨477967, by decide⟩ =
    .split (coordinate 11) (![⟨477831, by decide⟩,⟨477893, by decide⟩,⟨474208, by decide⟩,⟨477966, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17946_477967 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17946 ⟨477967, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17946
    ⟨477967, by decide⟩ (by decide) (![⟨477831, by decide⟩,⟨477893, by decide⟩,⟨474208, by decide⟩,⟨477966, by decide⟩]) unmarked_context_11_17946_477967 node_context_11_17946_477967
  intro a
  fin_cases a
  · exact context_12_71784_477831
  · exact context_12_71785_477893
  · exact context_12_71786_474208
  · exact context_12_71787_477966

theorem selected_cut_18697 : selected 9 ⟨478001, by decide⟩
    (prefixPartial 12 71788) = some ⟨12, 2, 0, 478001, 71788, 3429, 65536⟩ := by
  decide +kernel

theorem context_12_71788_478001 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71788 ⟨478001, by decide⟩ :=
  accepted_of_selected 12 71788 ⟨478001, by decide⟩ ⟨12, 2, 0, 478001, 71788, 3429, 65536⟩
    (by decide) selected_cut_18697

theorem selected_cut_18698 : selected 9 ⟨478036, by decide⟩
    (prefixPartial 12 71789) = some ⟨12, 2, 0, 478036, 71789, 3449, 65536⟩ := by
  decide +kernel

theorem context_12_71789_478036 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71789 ⟨478036, by decide⟩ :=
  accepted_of_selected 12 71789 ⟨478036, by decide⟩ ⟨12, 2, 0, 478036, 71789, 3449, 65536⟩
    (by decide) selected_cut_18698

theorem selected_cut_18699 : selected 9 ⟨478087, by decide⟩
    (prefixPartial 12 71790) = some ⟨12, 2, 0, 478087, 71790, 3665, 65536⟩ := by
  decide +kernel

theorem context_12_71790_478087 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71790 ⟨478087, by decide⟩ :=
  accepted_of_selected 12 71790 ⟨478087, by decide⟩ ⟨12, 2, 0, 478087, 71790, 3665, 65536⟩
    (by decide) selected_cut_18699

theorem selected_cut_18700 : selected 9 ⟨478125, by decide⟩
    (prefixPartial 12 71791) = some ⟨12, 2, 0, 478125, 71791, 3457, 65536⟩ := by
  decide +kernel

theorem context_12_71791_478125 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71791 ⟨478125, by decide⟩ :=
  accepted_of_selected 12 71791 ⟨478125, by decide⟩ ⟨12, 2, 0, 478125, 71791, 3457, 65536⟩
    (by decide) selected_cut_18700

theorem unmarked_context_11_17947_478126 : frontier 10 ⟨478126, by decide⟩
    (prefixCache 11 17947) (prefixPartial 11 17947) = false := by
  decide +kernel

theorem node_context_11_17947_478126 : EJMOriginalGlobalDAGData.nodes 10 ⟨478126, by decide⟩ =
    .split (coordinate 11) (![⟨478001, by decide⟩,⟨478036, by decide⟩,⟨478087, by decide⟩,⟨478125, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17947_478126 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17947 ⟨478126, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17947
    ⟨478126, by decide⟩ (by decide) (![⟨478001, by decide⟩,⟨478036, by decide⟩,⟨478087, by decide⟩,⟨478125, by decide⟩]) unmarked_context_11_17947_478126 node_context_11_17947_478126
  intro a
  fin_cases a
  · exact context_12_71788_478001
  · exact context_12_71789_478036
  · exact context_12_71790_478087
  · exact context_12_71791_478125

theorem unmarked_context_10_4486_478127 : frontier 11 ⟨478127, by decide⟩
    (prefixCache 10 4486) (prefixPartial 10 4486) = false := by
  decide +kernel

theorem node_context_10_4486_478127 : EJMOriginalGlobalDAGData.nodes 11 ⟨478127, by decide⟩ =
    .split (coordinate 10) (![⟨477591, by decide⟩,⟨477781, by decide⟩,⟨477967, by decide⟩,⟨478126, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4486_478127 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4486 ⟨478127, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4486
    ⟨478127, by decide⟩ (by decide) (![⟨477591, by decide⟩,⟨477781, by decide⟩,⟨477967, by decide⟩,⟨478126, by decide⟩]) unmarked_context_10_4486_478127 node_context_10_4486_478127
  intro a
  fin_cases a
  · exact context_11_17944_477591
  · exact context_11_17945_477781
  · exact context_11_17946_477967
  · exact context_11_17947_478126

theorem selected_cut_18701 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 287168) = some ⟨13, 1, 0, 3444, 287168, 1, 16384⟩ := by
  decide +kernel

theorem context_13_287168_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287168 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 287168 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 287168, 1, 16384⟩
    (by decide) selected_cut_18701

theorem selected_cut_18702 : selected 8 ⟨478148, by decide⟩
    (prefixPartial 13 287169) = some ⟨13, 2, 0, 478148, 287169, 865, 16384⟩ := by
  decide +kernel

theorem context_13_287169_478148 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287169 ⟨478148, by decide⟩ :=
  accepted_of_selected 13 287169 ⟨478148, by decide⟩ ⟨13, 2, 0, 478148, 287169, 865, 16384⟩
    (by decide) selected_cut_18702

theorem selected_cut_18703 : selected 8 ⟨478183, by decide⟩
    (prefixPartial 13 287170) = some ⟨13, 2, 0, 478183, 287170, 2085, 16384⟩ := by
  decide +kernel

theorem context_13_287170_478183 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287170 ⟨478183, by decide⟩ :=
  accepted_of_selected 13 287170 ⟨478183, by decide⟩ ⟨13, 2, 0, 478183, 287170, 2085, 16384⟩
    (by decide) selected_cut_18703

theorem selected_cut_18704 : selected 8 ⟨478213, by decide⟩
    (prefixPartial 13 287171) = some ⟨13, 2, 0, 478213, 287171, 1225, 16384⟩ := by
  decide +kernel

theorem context_13_287171_478213 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287171 ⟨478213, by decide⟩ :=
  accepted_of_selected 13 287171 ⟨478213, by decide⟩ ⟨13, 2, 0, 478213, 287171, 1225, 16384⟩
    (by decide) selected_cut_18704

theorem unmarked_context_12_71792_478214 : frontier 9 ⟨478214, by decide⟩
    (prefixCache 12 71792) (prefixPartial 12 71792) = false := by
  decide +kernel

theorem node_context_12_71792_478214 : EJMOriginalGlobalDAGData.nodes 9 ⟨478214, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨478148, by decide⟩,⟨478183, by decide⟩,⟨478213, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71792_478214 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71792 ⟨478214, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71792
    ⟨478214, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨478148, by decide⟩,⟨478183, by decide⟩,⟨478213, by decide⟩]) unmarked_context_12_71792_478214 node_context_12_71792_478214
  intro a
  fin_cases a
  · exact context_13_287168_3444
  · exact context_13_287169_478148
  · exact context_13_287170_478183
  · exact context_13_287171_478213

theorem selected_cut_18705 : selected 9 ⟨478242, by decide⟩
    (prefixPartial 12 71793) = some ⟨12, 2, 0, 478242, 71793, 2861, 65536⟩ := by
  decide +kernel

theorem context_12_71793_478242 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71793 ⟨478242, by decide⟩ :=
  accepted_of_selected 12 71793 ⟨478242, by decide⟩ ⟨12, 2, 0, 478242, 71793, 2861, 65536⟩
    (by decide) selected_cut_18705

theorem selected_cut_18706 : selected 9 ⟨478269, by decide⟩
    (prefixPartial 12 71794) = some ⟨12, 2, 0, 478269, 71794, 3185, 65536⟩ := by
  decide +kernel

theorem context_12_71794_478269 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71794 ⟨478269, by decide⟩ :=
  accepted_of_selected 12 71794 ⟨478269, by decide⟩ ⟨12, 2, 0, 478269, 71794, 3185, 65536⟩
    (by decide) selected_cut_18706

theorem selected_cut_18707 : selected 9 ⟨478305, by decide⟩
    (prefixPartial 12 71795) = some ⟨12, 2, 0, 478305, 71795, 3121, 65536⟩ := by
  decide +kernel

theorem context_12_71795_478305 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71795 ⟨478305, by decide⟩ :=
  accepted_of_selected 12 71795 ⟨478305, by decide⟩ ⟨12, 2, 0, 478305, 71795, 3121, 65536⟩
    (by decide) selected_cut_18707

theorem unmarked_context_11_17948_478306 : frontier 10 ⟨478306, by decide⟩
    (prefixCache 11 17948) (prefixPartial 11 17948) = false := by
  decide +kernel

theorem node_context_11_17948_478306 : EJMOriginalGlobalDAGData.nodes 10 ⟨478306, by decide⟩ =
    .split (coordinate 11) (![⟨478214, by decide⟩,⟨478242, by decide⟩,⟨478269, by decide⟩,⟨478305, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17948_478306 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17948 ⟨478306, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17948
    ⟨478306, by decide⟩ (by decide) (![⟨478214, by decide⟩,⟨478242, by decide⟩,⟨478269, by decide⟩,⟨478305, by decide⟩]) unmarked_context_11_17948_478306 node_context_11_17948_478306
  intro a
  fin_cases a
  · exact context_12_71792_478214
  · exact context_12_71793_478242
  · exact context_12_71794_478269
  · exact context_12_71795_478305

theorem selected_cut_18708 : selected 9 ⟨478344, by decide⟩
    (prefixPartial 12 71796) = some ⟨12, 2, 0, 478344, 71796, 3109, 65536⟩ := by
  decide +kernel

theorem context_12_71796_478344 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71796 ⟨478344, by decide⟩ :=
  accepted_of_selected 12 71796 ⟨478344, by decide⟩ ⟨12, 2, 0, 478344, 71796, 3109, 65536⟩
    (by decide) selected_cut_18708

theorem selected_cut_18709 : selected 9 ⟨478384, by decide⟩
    (prefixPartial 12 71797) = some ⟨12, 2, 0, 478384, 71797, 2861, 65536⟩ := by
  decide +kernel

theorem context_12_71797_478384 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71797 ⟨478384, by decide⟩ :=
  accepted_of_selected 12 71797 ⟨478384, by decide⟩ ⟨12, 2, 0, 478384, 71797, 2861, 65536⟩
    (by decide) selected_cut_18709

theorem selected_cut_18710 : selected 9 ⟨478430, by decide⟩
    (prefixPartial 12 71798) = some ⟨12, 2, 0, 478430, 71798, 3297, 65536⟩ := by
  decide +kernel

theorem context_12_71798_478430 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71798 ⟨478430, by decide⟩ :=
  accepted_of_selected 12 71798 ⟨478430, by decide⟩ ⟨12, 2, 0, 478430, 71798, 3297, 65536⟩
    (by decide) selected_cut_18710

theorem selected_cut_18711 : selected 9 ⟨478477, by decide⟩
    (prefixPartial 12 71799) = some ⟨12, 2, 0, 478477, 71799, 3365, 65536⟩ := by
  decide +kernel

theorem context_12_71799_478477 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71799 ⟨478477, by decide⟩ :=
  accepted_of_selected 12 71799 ⟨478477, by decide⟩ ⟨12, 2, 0, 478477, 71799, 3365, 65536⟩
    (by decide) selected_cut_18711

theorem unmarked_context_11_17949_478478 : frontier 10 ⟨478478, by decide⟩
    (prefixCache 11 17949) (prefixPartial 11 17949) = false := by
  decide +kernel

theorem node_context_11_17949_478478 : EJMOriginalGlobalDAGData.nodes 10 ⟨478478, by decide⟩ =
    .split (coordinate 11) (![⟨478344, by decide⟩,⟨478384, by decide⟩,⟨478430, by decide⟩,⟨478477, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17949_478478 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17949 ⟨478478, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17949
    ⟨478478, by decide⟩ (by decide) (![⟨478344, by decide⟩,⟨478384, by decide⟩,⟨478430, by decide⟩,⟨478477, by decide⟩]) unmarked_context_11_17949_478478 node_context_11_17949_478478
  intro a
  fin_cases a
  · exact context_12_71796_478344
  · exact context_12_71797_478384
  · exact context_12_71798_478430
  · exact context_12_71799_478477

theorem selected_cut_18712 : selected 9 ⟨478511, by decide⟩
    (prefixPartial 12 71800) = some ⟨12, 2, 0, 478511, 71800, 3025, 65536⟩ := by
  decide +kernel

theorem context_12_71800_478511 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71800 ⟨478511, by decide⟩ :=
  accepted_of_selected 12 71800 ⟨478511, by decide⟩ ⟨12, 2, 0, 478511, 71800, 3025, 65536⟩
    (by decide) selected_cut_18712

theorem selected_cut_18713 : selected 9 ⟨478548, by decide⟩
    (prefixPartial 12 71801) = some ⟨12, 2, 0, 478548, 71801, 3045, 65536⟩ := by
  decide +kernel

theorem context_12_71801_478548 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71801 ⟨478548, by decide⟩ :=
  accepted_of_selected 12 71801 ⟨478548, by decide⟩ ⟨12, 2, 0, 478548, 71801, 3045, 65536⟩
    (by decide) selected_cut_18713

theorem selected_cut_18714 : selected 9 ⟨478580, by decide⟩
    (prefixPartial 12 71802) = some ⟨12, 2, 0, 478580, 71802, 3085, 65536⟩ := by
  decide +kernel

theorem context_12_71802_478580 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71802 ⟨478580, by decide⟩ :=
  accepted_of_selected 12 71802 ⟨478580, by decide⟩ ⟨12, 2, 0, 478580, 71802, 3085, 65536⟩
    (by decide) selected_cut_18714

theorem selected_cut_18715 : selected 9 ⟨478621, by decide⟩
    (prefixPartial 12 71803) = some ⟨12, 2, 0, 478621, 71803, 3133, 65536⟩ := by
  decide +kernel

theorem context_12_71803_478621 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71803 ⟨478621, by decide⟩ :=
  accepted_of_selected 12 71803 ⟨478621, by decide⟩ ⟨12, 2, 0, 478621, 71803, 3133, 65536⟩
    (by decide) selected_cut_18715

theorem unmarked_context_11_17950_478622 : frontier 10 ⟨478622, by decide⟩
    (prefixCache 11 17950) (prefixPartial 11 17950) = false := by
  decide +kernel

theorem node_context_11_17950_478622 : EJMOriginalGlobalDAGData.nodes 10 ⟨478622, by decide⟩ =
    .split (coordinate 11) (![⟨478511, by decide⟩,⟨478548, by decide⟩,⟨478580, by decide⟩,⟨478621, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17950_478622 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17950 ⟨478622, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17950
    ⟨478622, by decide⟩ (by decide) (![⟨478511, by decide⟩,⟨478548, by decide⟩,⟨478580, by decide⟩,⟨478621, by decide⟩]) unmarked_context_11_17950_478622 node_context_11_17950_478622
  intro a
  fin_cases a
  · exact context_12_71800_478511
  · exact context_12_71801_478548
  · exact context_12_71802_478580
  · exact context_12_71803_478621

theorem selected_cut_18716 : selected 9 ⟨478649, by decide⟩
    (prefixPartial 12 71804) = some ⟨12, 2, 0, 478649, 71804, 2773, 65536⟩ := by
  decide +kernel

theorem context_12_71804_478649 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71804 ⟨478649, by decide⟩ :=
  accepted_of_selected 12 71804 ⟨478649, by decide⟩ ⟨12, 2, 0, 478649, 71804, 2773, 65536⟩
    (by decide) selected_cut_18716

theorem selected_cut_18717 : selected 9 ⟨478686, by decide⟩
    (prefixPartial 12 71805) = some ⟨12, 2, 0, 478686, 71805, 2757, 65536⟩ := by
  decide +kernel

theorem context_12_71805_478686 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71805 ⟨478686, by decide⟩ :=
  accepted_of_selected 12 71805 ⟨478686, by decide⟩ ⟨12, 2, 0, 478686, 71805, 2757, 65536⟩
    (by decide) selected_cut_18717

theorem selected_cut_18718 : selected 9 ⟨478717, by decide⟩
    (prefixPartial 12 71806) = some ⟨12, 2, 0, 478717, 71806, 2965, 65536⟩ := by
  decide +kernel

theorem context_12_71806_478717 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71806 ⟨478717, by decide⟩ :=
  accepted_of_selected 12 71806 ⟨478717, by decide⟩ ⟨12, 2, 0, 478717, 71806, 2965, 65536⟩
    (by decide) selected_cut_18718

theorem selected_cut_18719 : selected 9 ⟨478749, by decide⟩
    (prefixPartial 12 71807) = some ⟨12, 2, 0, 478749, 71807, 2753, 65536⟩ := by
  decide +kernel

theorem context_12_71807_478749 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71807 ⟨478749, by decide⟩ :=
  accepted_of_selected 12 71807 ⟨478749, by decide⟩ ⟨12, 2, 0, 478749, 71807, 2753, 65536⟩
    (by decide) selected_cut_18719

theorem unmarked_context_11_17951_478750 : frontier 10 ⟨478750, by decide⟩
    (prefixCache 11 17951) (prefixPartial 11 17951) = false := by
  decide +kernel

theorem node_context_11_17951_478750 : EJMOriginalGlobalDAGData.nodes 10 ⟨478750, by decide⟩ =
    .split (coordinate 11) (![⟨478649, by decide⟩,⟨478686, by decide⟩,⟨478717, by decide⟩,⟨478749, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17951_478750 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17951 ⟨478750, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17951
    ⟨478750, by decide⟩ (by decide) (![⟨478649, by decide⟩,⟨478686, by decide⟩,⟨478717, by decide⟩,⟨478749, by decide⟩]) unmarked_context_11_17951_478750 node_context_11_17951_478750
  intro a
  fin_cases a
  · exact context_12_71804_478649
  · exact context_12_71805_478686
  · exact context_12_71806_478717
  · exact context_12_71807_478749

theorem unmarked_context_10_4487_478751 : frontier 11 ⟨478751, by decide⟩
    (prefixCache 10 4487) (prefixPartial 10 4487) = false := by
  decide +kernel

theorem node_context_10_4487_478751 : EJMOriginalGlobalDAGData.nodes 11 ⟨478751, by decide⟩ =
    .split (coordinate 10) (![⟨478306, by decide⟩,⟨478478, by decide⟩,⟨478622, by decide⟩,⟨478750, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4487_478751 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4487 ⟨478751, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4487
    ⟨478751, by decide⟩ (by decide) (![⟨478306, by decide⟩,⟨478478, by decide⟩,⟨478622, by decide⟩,⟨478750, by decide⟩]) unmarked_context_10_4487_478751 node_context_10_4487_478751
  intro a
  fin_cases a
  · exact context_11_17948_478306
  · exact context_11_17949_478478
  · exact context_11_17950_478622
  · exact context_11_17951_478750

theorem unmarked_context_9_1121_478752 : frontier 12 ⟨478752, by decide⟩
    (prefixCache 9 1121) (prefixPartial 9 1121) = false := by
  decide +kernel

theorem node_context_9_1121_478752 : EJMOriginalGlobalDAGData.nodes 12 ⟨478752, by decide⟩ =
    .split (coordinate 9) (![⟨476485, by decide⟩,⟨477376, by decide⟩,⟨478127, by decide⟩,⟨478751, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1121_478752 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1121 ⟨478752, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1121
    ⟨478752, by decide⟩ (by decide) (![⟨476485, by decide⟩,⟨477376, by decide⟩,⟨478127, by decide⟩,⟨478751, by decide⟩]) unmarked_context_9_1121_478752 node_context_9_1121_478752
  intro a
  fin_cases a
  · exact context_10_4484_476485
  · exact context_10_4485_477376
  · exact context_10_4486_478127
  · exact context_10_4487_478751

theorem selected_cut_18720 : selected 9 ⟨450982, by decide⟩
    (prefixPartial 12 71808) = some ⟨12, 1, 0, 450982, 71808, 1, 65536⟩ := by
  decide +kernel

theorem context_12_71808_450982 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71808 ⟨450982, by decide⟩ :=
  accepted_of_selected 12 71808 ⟨450982, by decide⟩ ⟨12, 1, 0, 450982, 71808, 1, 65536⟩
    (by decide) selected_cut_18720

theorem selected_cut_18721 : selected 9 ⟨478780, by decide⟩
    (prefixPartial 12 71809) = some ⟨12, 2, 0, 478780, 71809, 2089, 65536⟩ := by
  decide +kernel

theorem context_12_71809_478780 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71809 ⟨478780, by decide⟩ :=
  accepted_of_selected 12 71809 ⟨478780, by decide⟩ ⟨12, 2, 0, 478780, 71809, 2089, 65536⟩
    (by decide) selected_cut_18721

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
