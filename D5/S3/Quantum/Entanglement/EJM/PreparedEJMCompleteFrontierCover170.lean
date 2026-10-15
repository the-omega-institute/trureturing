/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover169
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_16324 : selected 8 ⟨415737, by decide⟩
    (prefixPartial 13 112846) = some ⟨13, 2, 0, 415737, 112846, 1729, 16384⟩ := by
  decide +kernel

theorem context_13_112846_415737 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112846 ⟨415737, by decide⟩ :=
  accepted_of_selected 13 112846 ⟨415737, by decide⟩ ⟨13, 2, 0, 415737, 112846, 1729, 16384⟩
    (by decide) selected_cut_16324

theorem selected_cut_16325 : selected 8 ⟨415743, by decide⟩
    (prefixPartial 13 112847) = some ⟨13, 2, 0, 415743, 112847, 873, 16384⟩ := by
  decide +kernel

theorem context_13_112847_415743 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112847 ⟨415743, by decide⟩ :=
  accepted_of_selected 13 112847 ⟨415743, by decide⟩ ⟨13, 2, 0, 415743, 112847, 873, 16384⟩
    (by decide) selected_cut_16325

theorem unmarked_context_12_28211_415744 : frontier 9 ⟨415744, by decide⟩
    (prefixCache 12 28211) (prefixPartial 12 28211) = false := by
  decide +kernel

theorem node_context_12_28211_415744 : EJMOriginalGlobalDAGData.nodes 9 ⟨415744, by decide⟩ =
    .split (coordinate 12) (![⟨415664, by decide⟩,⟨415713, by decide⟩,⟨415737, by decide⟩,⟨415743, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28211_415744 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28211 ⟨415744, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28211
    ⟨415744, by decide⟩ (by decide) (![⟨415664, by decide⟩,⟨415713, by decide⟩,⟨415737, by decide⟩,⟨415743, by decide⟩]) unmarked_context_12_28211_415744 node_context_12_28211_415744
  intro a
  fin_cases a
  · exact context_13_112844_415664
  · exact context_13_112845_415713
  · exact context_13_112846_415737
  · exact context_13_112847_415743

theorem unmarked_context_11_7052_415745 : frontier 10 ⟨415745, by decide⟩
    (prefixCache 11 7052) (prefixPartial 11 7052) = false := by
  decide +kernel

theorem node_context_11_7052_415745 : EJMOriginalGlobalDAGData.nodes 10 ⟨415745, by decide⟩ =
    .split (coordinate 11) (![⟨415533, by decide⟩,⟨415599, by decide⟩,⟨415653, by decide⟩,⟨415744, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_7052_415745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7052 ⟨415745, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 7052
    ⟨415745, by decide⟩ (by decide) (![⟨415533, by decide⟩,⟨415599, by decide⟩,⟨415653, by decide⟩,⟨415744, by decide⟩]) unmarked_context_11_7052_415745 node_context_11_7052_415745
  intro a
  fin_cases a
  · exact context_12_28208_415533
  · exact context_12_28209_415599
  · exact context_12_28210_415653
  · exact context_12_28211_415744

theorem selected_cut_16326 : selected 8 ⟨415752, by decide⟩
    (prefixPartial 13 112848) = some ⟨13, 2, 0, 415752, 112848, 545, 16384⟩ := by
  decide +kernel

theorem context_13_112848_415752 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112848 ⟨415752, by decide⟩ :=
  accepted_of_selected 13 112848 ⟨415752, by decide⟩ ⟨13, 2, 0, 415752, 112848, 545, 16384⟩
    (by decide) selected_cut_16326

theorem selected_cut_16327 : selected 8 ⟨415781, by decide⟩
    (prefixPartial 13 112849) = some ⟨13, 2, 0, 415781, 112849, 2333, 16384⟩ := by
  decide +kernel

theorem context_13_112849_415781 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112849 ⟨415781, by decide⟩ :=
  accepted_of_selected 13 112849 ⟨415781, by decide⟩ ⟨13, 2, 0, 415781, 112849, 2333, 16384⟩
    (by decide) selected_cut_16327

theorem selected_cut_16328 : selected 8 ⟨415798, by decide⟩
    (prefixPartial 13 112850) = some ⟨13, 2, 0, 415798, 112850, 1261, 16384⟩ := by
  decide +kernel

theorem context_13_112850_415798 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112850 ⟨415798, by decide⟩ :=
  accepted_of_selected 13 112850 ⟨415798, by decide⟩ ⟨13, 2, 0, 415798, 112850, 1261, 16384⟩
    (by decide) selected_cut_16328

theorem selected_cut_16329 : selected 8 ⟨415804, by decide⟩
    (prefixPartial 13 112851) = some ⟨13, 2, 0, 415804, 112851, 729, 16384⟩ := by
  decide +kernel

theorem context_13_112851_415804 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112851 ⟨415804, by decide⟩ :=
  accepted_of_selected 13 112851 ⟨415804, by decide⟩ ⟨13, 2, 0, 415804, 112851, 729, 16384⟩
    (by decide) selected_cut_16329

theorem unmarked_context_12_28212_415805 : frontier 9 ⟨415805, by decide⟩
    (prefixCache 12 28212) (prefixPartial 12 28212) = false := by
  decide +kernel

theorem node_context_12_28212_415805 : EJMOriginalGlobalDAGData.nodes 9 ⟨415805, by decide⟩ =
    .split (coordinate 12) (![⟨415752, by decide⟩,⟨415781, by decide⟩,⟨415798, by decide⟩,⟨415804, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28212_415805 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28212 ⟨415805, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28212
    ⟨415805, by decide⟩ (by decide) (![⟨415752, by decide⟩,⟨415781, by decide⟩,⟨415798, by decide⟩,⟨415804, by decide⟩]) unmarked_context_12_28212_415805 node_context_12_28212_415805
  intro a
  fin_cases a
  · exact context_13_112848_415752
  · exact context_13_112849_415781
  · exact context_13_112850_415798
  · exact context_13_112851_415804

theorem selected_cut_16330 : selected 8 ⟨415812, by decide⟩
    (prefixPartial 13 112852) = some ⟨13, 2, 0, 415812, 112852, 541, 16384⟩ := by
  decide +kernel

theorem context_13_112852_415812 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112852 ⟨415812, by decide⟩ :=
  accepted_of_selected 13 112852 ⟨415812, by decide⟩ ⟨13, 2, 0, 415812, 112852, 541, 16384⟩
    (by decide) selected_cut_16330

theorem selected_cut_16331 : selected 8 ⟨415839, by decide⟩
    (prefixPartial 13 112853) = some ⟨13, 2, 0, 415839, 112853, 2049, 16384⟩ := by
  decide +kernel

theorem context_13_112853_415839 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112853 ⟨415839, by decide⟩ :=
  accepted_of_selected 13 112853 ⟨415839, by decide⟩ ⟨13, 2, 0, 415839, 112853, 2049, 16384⟩
    (by decide) selected_cut_16331

theorem selected_cut_16332 : selected 8 ⟨415857, by decide⟩
    (prefixPartial 13 112854) = some ⟨13, 2, 0, 415857, 112854, 1381, 16384⟩ := by
  decide +kernel

theorem context_13_112854_415857 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112854 ⟨415857, by decide⟩ :=
  accepted_of_selected 13 112854 ⟨415857, by decide⟩ ⟨13, 2, 0, 415857, 112854, 1381, 16384⟩
    (by decide) selected_cut_16332

theorem selected_cut_16333 : selected 8 ⟨415864, by decide⟩
    (prefixPartial 13 112855) = some ⟨13, 2, 0, 415864, 112855, 873, 16384⟩ := by
  decide +kernel

theorem context_13_112855_415864 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112855 ⟨415864, by decide⟩ :=
  accepted_of_selected 13 112855 ⟨415864, by decide⟩ ⟨13, 2, 0, 415864, 112855, 873, 16384⟩
    (by decide) selected_cut_16333

theorem unmarked_context_12_28213_415865 : frontier 9 ⟨415865, by decide⟩
    (prefixCache 12 28213) (prefixPartial 12 28213) = false := by
  decide +kernel

theorem node_context_12_28213_415865 : EJMOriginalGlobalDAGData.nodes 9 ⟨415865, by decide⟩ =
    .split (coordinate 12) (![⟨415812, by decide⟩,⟨415839, by decide⟩,⟨415857, by decide⟩,⟨415864, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28213_415865 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28213 ⟨415865, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28213
    ⟨415865, by decide⟩ (by decide) (![⟨415812, by decide⟩,⟨415839, by decide⟩,⟨415857, by decide⟩,⟨415864, by decide⟩]) unmarked_context_12_28213_415865 node_context_12_28213_415865
  intro a
  fin_cases a
  · exact context_13_112852_415812
  · exact context_13_112853_415839
  · exact context_13_112854_415857
  · exact context_13_112855_415864

theorem selected_cut_16334 : selected 8 ⟨415870, by decide⟩
    (prefixPartial 13 112856) = some ⟨13, 2, 0, 415870, 112856, 469, 16384⟩ := by
  decide +kernel

theorem context_13_112856_415870 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112856 ⟨415870, by decide⟩ :=
  accepted_of_selected 13 112856 ⟨415870, by decide⟩ ⟨13, 2, 0, 415870, 112856, 469, 16384⟩
    (by decide) selected_cut_16334

theorem selected_cut_16335 : selected 8 ⟨415891, by decide⟩
    (prefixPartial 13 112857) = some ⟨13, 2, 0, 415891, 112857, 1925, 16384⟩ := by
  decide +kernel

theorem context_13_112857_415891 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112857 ⟨415891, by decide⟩ :=
  accepted_of_selected 13 112857 ⟨415891, by decide⟩ ⟨13, 2, 0, 415891, 112857, 1925, 16384⟩
    (by decide) selected_cut_16335

theorem selected_cut_16336 : selected 8 ⟨415907, by decide⟩
    (prefixPartial 13 112858) = some ⟨13, 2, 0, 415907, 112858, 1225, 16384⟩ := by
  decide +kernel

theorem context_13_112858_415907 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112858 ⟨415907, by decide⟩ :=
  accepted_of_selected 13 112858 ⟨415907, by decide⟩ ⟨13, 2, 0, 415907, 112858, 1225, 16384⟩
    (by decide) selected_cut_16336

theorem selected_cut_16337 : selected 8 ⟨415912, by decide⟩
    (prefixPartial 13 112859) = some ⟨13, 2, 0, 415912, 112859, 865, 16384⟩ := by
  decide +kernel

theorem context_13_112859_415912 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112859 ⟨415912, by decide⟩ :=
  accepted_of_selected 13 112859 ⟨415912, by decide⟩ ⟨13, 2, 0, 415912, 112859, 865, 16384⟩
    (by decide) selected_cut_16337

theorem unmarked_context_12_28214_415913 : frontier 9 ⟨415913, by decide⟩
    (prefixCache 12 28214) (prefixPartial 12 28214) = false := by
  decide +kernel

theorem node_context_12_28214_415913 : EJMOriginalGlobalDAGData.nodes 9 ⟨415913, by decide⟩ =
    .split (coordinate 12) (![⟨415870, by decide⟩,⟨415891, by decide⟩,⟨415907, by decide⟩,⟨415912, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28214_415913 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28214 ⟨415913, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28214
    ⟨415913, by decide⟩ (by decide) (![⟨415870, by decide⟩,⟨415891, by decide⟩,⟨415907, by decide⟩,⟨415912, by decide⟩]) unmarked_context_12_28214_415913 node_context_12_28214_415913
  intro a
  fin_cases a
  · exact context_13_112856_415870
  · exact context_13_112857_415891
  · exact context_13_112858_415907
  · exact context_13_112859_415912

theorem selected_cut_16338 : selected 8 ⟨415920, by decide⟩
    (prefixPartial 13 112860) = some ⟨13, 2, 0, 415920, 112860, 485, 16384⟩ := by
  decide +kernel

theorem context_13_112860_415920 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112860 ⟨415920, by decide⟩ :=
  accepted_of_selected 13 112860 ⟨415920, by decide⟩ ⟨13, 2, 0, 415920, 112860, 485, 16384⟩
    (by decide) selected_cut_16338

theorem selected_cut_16339 : selected 8 ⟨415948, by decide⟩
    (prefixPartial 13 112861) = some ⟨13, 2, 0, 415948, 112861, 2381, 16384⟩ := by
  decide +kernel

theorem context_13_112861_415948 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112861 ⟨415948, by decide⟩ :=
  accepted_of_selected 13 112861 ⟨415948, by decide⟩ ⟨13, 2, 0, 415948, 112861, 2381, 16384⟩
    (by decide) selected_cut_16339

theorem selected_cut_16340 : selected 8 ⟨415966, by decide⟩
    (prefixPartial 13 112862) = some ⟨13, 2, 0, 415966, 112862, 1577, 16384⟩ := by
  decide +kernel

theorem context_13_112862_415966 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112862 ⟨415966, by decide⟩ :=
  accepted_of_selected 13 112862 ⟨415966, by decide⟩ ⟨13, 2, 0, 415966, 112862, 1577, 16384⟩
    (by decide) selected_cut_16340

theorem selected_cut_16341 : selected 8 ⟨415972, by decide⟩
    (prefixPartial 13 112863) = some ⟨13, 2, 0, 415972, 112863, 997, 16384⟩ := by
  decide +kernel

theorem context_13_112863_415972 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112863 ⟨415972, by decide⟩ :=
  accepted_of_selected 13 112863 ⟨415972, by decide⟩ ⟨13, 2, 0, 415972, 112863, 997, 16384⟩
    (by decide) selected_cut_16341

theorem unmarked_context_12_28215_415973 : frontier 9 ⟨415973, by decide⟩
    (prefixCache 12 28215) (prefixPartial 12 28215) = false := by
  decide +kernel

theorem node_context_12_28215_415973 : EJMOriginalGlobalDAGData.nodes 9 ⟨415973, by decide⟩ =
    .split (coordinate 12) (![⟨415920, by decide⟩,⟨415948, by decide⟩,⟨415966, by decide⟩,⟨415972, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28215_415973 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28215 ⟨415973, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28215
    ⟨415973, by decide⟩ (by decide) (![⟨415920, by decide⟩,⟨415948, by decide⟩,⟨415966, by decide⟩,⟨415972, by decide⟩]) unmarked_context_12_28215_415973 node_context_12_28215_415973
  intro a
  fin_cases a
  · exact context_13_112860_415920
  · exact context_13_112861_415948
  · exact context_13_112862_415966
  · exact context_13_112863_415972

theorem unmarked_context_11_7053_415974 : frontier 10 ⟨415974, by decide⟩
    (prefixCache 11 7053) (prefixPartial 11 7053) = false := by
  decide +kernel

theorem node_context_11_7053_415974 : EJMOriginalGlobalDAGData.nodes 10 ⟨415974, by decide⟩ =
    .split (coordinate 11) (![⟨415805, by decide⟩,⟨415865, by decide⟩,⟨415913, by decide⟩,⟨415973, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_7053_415974 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7053 ⟨415974, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 7053
    ⟨415974, by decide⟩ (by decide) (![⟨415805, by decide⟩,⟨415865, by decide⟩,⟨415913, by decide⟩,⟨415973, by decide⟩]) unmarked_context_11_7053_415974 node_context_11_7053_415974
  intro a
  fin_cases a
  · exact context_12_28212_415805
  · exact context_12_28213_415865
  · exact context_12_28214_415913
  · exact context_12_28215_415973

theorem selected_cut_16342 : selected 8 ⟨415979, by decide⟩
    (prefixPartial 13 112864) = some ⟨13, 2, 0, 415979, 112864, 313, 16384⟩ := by
  decide +kernel

theorem context_13_112864_415979 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112864 ⟨415979, by decide⟩ :=
  accepted_of_selected 13 112864 ⟨415979, by decide⟩ ⟨13, 2, 0, 415979, 112864, 313, 16384⟩
    (by decide) selected_cut_16342

theorem selected_cut_16343 : selected 8 ⟨416013, by decide⟩
    (prefixPartial 13 112865) = some ⟨13, 2, 0, 416013, 112865, 2341, 16384⟩ := by
  decide +kernel

theorem context_13_112865_416013 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112865 ⟨416013, by decide⟩ :=
  accepted_of_selected 13 112865 ⟨416013, by decide⟩ ⟨13, 2, 0, 416013, 112865, 2341, 16384⟩
    (by decide) selected_cut_16343

theorem selected_cut_16344 : selected 8 ⟨416029, by decide⟩
    (prefixPartial 13 112866) = some ⟨13, 2, 0, 416029, 112866, 1149, 16384⟩ := by
  decide +kernel

theorem context_13_112866_416029 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112866 ⟨416029, by decide⟩ :=
  accepted_of_selected 13 112866 ⟨416029, by decide⟩ ⟨13, 2, 0, 416029, 112866, 1149, 16384⟩
    (by decide) selected_cut_16344

theorem selected_cut_16345 : selected 8 ⟨416036, by decide⟩
    (prefixPartial 13 112867) = some ⟨13, 2, 0, 416036, 112867, 681, 16384⟩ := by
  decide +kernel

theorem context_13_112867_416036 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112867 ⟨416036, by decide⟩ :=
  accepted_of_selected 13 112867 ⟨416036, by decide⟩ ⟨13, 2, 0, 416036, 112867, 681, 16384⟩
    (by decide) selected_cut_16345

theorem unmarked_context_12_28216_416037 : frontier 9 ⟨416037, by decide⟩
    (prefixCache 12 28216) (prefixPartial 12 28216) = false := by
  decide +kernel

theorem node_context_12_28216_416037 : EJMOriginalGlobalDAGData.nodes 9 ⟨416037, by decide⟩ =
    .split (coordinate 12) (![⟨415979, by decide⟩,⟨416013, by decide⟩,⟨416029, by decide⟩,⟨416036, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28216_416037 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28216 ⟨416037, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28216
    ⟨416037, by decide⟩ (by decide) (![⟨415979, by decide⟩,⟨416013, by decide⟩,⟨416029, by decide⟩,⟨416036, by decide⟩]) unmarked_context_12_28216_416037 node_context_12_28216_416037
  intro a
  fin_cases a
  · exact context_13_112864_415979
  · exact context_13_112865_416013
  · exact context_13_112866_416029
  · exact context_13_112867_416036

theorem selected_cut_16346 : selected 8 ⟨416044, by decide⟩
    (prefixPartial 13 112868) = some ⟨13, 2, 0, 416044, 112868, 337, 16384⟩ := by
  decide +kernel

theorem context_13_112868_416044 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112868 ⟨416044, by decide⟩ :=
  accepted_of_selected 13 112868 ⟨416044, by decide⟩ ⟨13, 2, 0, 416044, 112868, 337, 16384⟩
    (by decide) selected_cut_16346

theorem selected_cut_16347 : selected 8 ⟨416077, by decide⟩
    (prefixPartial 13 112869) = some ⟨13, 2, 0, 416077, 112869, 2293, 16384⟩ := by
  decide +kernel

theorem context_13_112869_416077 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112869 ⟨416077, by decide⟩ :=
  accepted_of_selected 13 112869 ⟨416077, by decide⟩ ⟨13, 2, 0, 416077, 112869, 2293, 16384⟩
    (by decide) selected_cut_16347

theorem selected_cut_16348 : selected 8 ⟨416096, by decide⟩
    (prefixPartial 13 112870) = some ⟨13, 2, 0, 416096, 112870, 1353, 16384⟩ := by
  decide +kernel

theorem context_13_112870_416096 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112870 ⟨416096, by decide⟩ :=
  accepted_of_selected 13 112870 ⟨416096, by decide⟩ ⟨13, 2, 0, 416096, 112870, 1353, 16384⟩
    (by decide) selected_cut_16348

theorem selected_cut_16349 : selected 8 ⟨416105, by decide⟩
    (prefixPartial 13 112871) = some ⟨13, 2, 0, 416105, 112871, 849, 16384⟩ := by
  decide +kernel

theorem context_13_112871_416105 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112871 ⟨416105, by decide⟩ :=
  accepted_of_selected 13 112871 ⟨416105, by decide⟩ ⟨13, 2, 0, 416105, 112871, 849, 16384⟩
    (by decide) selected_cut_16349

theorem unmarked_context_12_28217_416106 : frontier 9 ⟨416106, by decide⟩
    (prefixCache 12 28217) (prefixPartial 12 28217) = false := by
  decide +kernel

theorem node_context_12_28217_416106 : EJMOriginalGlobalDAGData.nodes 9 ⟨416106, by decide⟩ =
    .split (coordinate 12) (![⟨416044, by decide⟩,⟨416077, by decide⟩,⟨416096, by decide⟩,⟨416105, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28217_416106 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28217 ⟨416106, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28217
    ⟨416106, by decide⟩ (by decide) (![⟨416044, by decide⟩,⟨416077, by decide⟩,⟨416096, by decide⟩,⟨416105, by decide⟩]) unmarked_context_12_28217_416106 node_context_12_28217_416106
  intro a
  fin_cases a
  · exact context_13_112868_416044
  · exact context_13_112869_416077
  · exact context_13_112870_416096
  · exact context_13_112871_416105

theorem selected_cut_16350 : selected 8 ⟨416118, by decide⟩
    (prefixPartial 13 112872) = some ⟨13, 2, 0, 416118, 112872, 441, 16384⟩ := by
  decide +kernel

theorem context_13_112872_416118 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112872 ⟨416118, by decide⟩ :=
  accepted_of_selected 13 112872 ⟨416118, by decide⟩ ⟨13, 2, 0, 416118, 112872, 441, 16384⟩
    (by decide) selected_cut_16350

theorem selected_cut_16351 : selected 8 ⟨416183, by decide⟩
    (prefixPartial 13 112873) = some ⟨13, 2, 0, 416183, 112873, 3537, 16384⟩ := by
  decide +kernel

theorem context_13_112873_416183 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112873 ⟨416183, by decide⟩ :=
  accepted_of_selected 13 112873 ⟨416183, by decide⟩ ⟨13, 2, 0, 416183, 112873, 3537, 16384⟩
    (by decide) selected_cut_16351

theorem selected_cut_16352 : selected 8 ⟨416202, by decide⟩
    (prefixPartial 13 112874) = some ⟨13, 2, 0, 416202, 112874, 1957, 16384⟩ := by
  decide +kernel

theorem context_13_112874_416202 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112874 ⟨416202, by decide⟩ :=
  accepted_of_selected 13 112874 ⟨416202, by decide⟩ ⟨13, 2, 0, 416202, 112874, 1957, 16384⟩
    (by decide) selected_cut_16352

theorem selected_cut_16353 : selected 8 ⟨416209, by decide⟩
    (prefixPartial 13 112875) = some ⟨13, 2, 0, 416209, 112875, 1081, 16384⟩ := by
  decide +kernel

theorem context_13_112875_416209 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112875 ⟨416209, by decide⟩ :=
  accepted_of_selected 13 112875 ⟨416209, by decide⟩ ⟨13, 2, 0, 416209, 112875, 1081, 16384⟩
    (by decide) selected_cut_16353

theorem unmarked_context_12_28218_416210 : frontier 9 ⟨416210, by decide⟩
    (prefixCache 12 28218) (prefixPartial 12 28218) = false := by
  decide +kernel

theorem node_context_12_28218_416210 : EJMOriginalGlobalDAGData.nodes 9 ⟨416210, by decide⟩ =
    .split (coordinate 12) (![⟨416118, by decide⟩,⟨416183, by decide⟩,⟨416202, by decide⟩,⟨416209, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28218_416210 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28218 ⟨416210, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28218
    ⟨416210, by decide⟩ (by decide) (![⟨416118, by decide⟩,⟨416183, by decide⟩,⟨416202, by decide⟩,⟨416209, by decide⟩]) unmarked_context_12_28218_416210 node_context_12_28218_416210
  intro a
  fin_cases a
  · exact context_13_112872_416118
  · exact context_13_112873_416183
  · exact context_13_112874_416202
  · exact context_13_112875_416209

theorem selected_cut_16354 : selected 8 ⟨416219, by decide⟩
    (prefixPartial 13 112876) = some ⟨13, 2, 0, 416219, 112876, 269, 16384⟩ := by
  decide +kernel

theorem context_13_112876_416219 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112876 ⟨416219, by decide⟩ :=
  accepted_of_selected 13 112876 ⟨416219, by decide⟩ ⟨13, 2, 0, 416219, 112876, 269, 16384⟩
    (by decide) selected_cut_16354

theorem selected_cut_16355 : selected 8 ⟨416263, by decide⟩
    (prefixPartial 13 112877) = some ⟨13, 2, 0, 416263, 112877, 2777, 16384⟩ := by
  decide +kernel

theorem context_13_112877_416263 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112877 ⟨416263, by decide⟩ :=
  accepted_of_selected 13 112877 ⟨416263, by decide⟩ ⟨13, 2, 0, 416263, 112877, 2777, 16384⟩
    (by decide) selected_cut_16355

theorem selected_cut_16356 : selected 8 ⟨416279, by decide⟩
    (prefixPartial 13 112878) = some ⟨13, 2, 0, 416279, 112878, 1445, 16384⟩ := by
  decide +kernel

theorem context_13_112878_416279 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112878 ⟨416279, by decide⟩ :=
  accepted_of_selected 13 112878 ⟨416279, by decide⟩ ⟨13, 2, 0, 416279, 112878, 1445, 16384⟩
    (by decide) selected_cut_16356

theorem selected_cut_16357 : selected 8 ⟨416286, by decide⟩
    (prefixPartial 13 112879) = some ⟨13, 2, 0, 416286, 112879, 865, 16384⟩ := by
  decide +kernel

theorem context_13_112879_416286 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112879 ⟨416286, by decide⟩ :=
  accepted_of_selected 13 112879 ⟨416286, by decide⟩ ⟨13, 2, 0, 416286, 112879, 865, 16384⟩
    (by decide) selected_cut_16357

theorem unmarked_context_12_28219_416287 : frontier 9 ⟨416287, by decide⟩
    (prefixCache 12 28219) (prefixPartial 12 28219) = false := by
  decide +kernel

theorem node_context_12_28219_416287 : EJMOriginalGlobalDAGData.nodes 9 ⟨416287, by decide⟩ =
    .split (coordinate 12) (![⟨416219, by decide⟩,⟨416263, by decide⟩,⟨416279, by decide⟩,⟨416286, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28219_416287 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28219 ⟨416287, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28219
    ⟨416287, by decide⟩ (by decide) (![⟨416219, by decide⟩,⟨416263, by decide⟩,⟨416279, by decide⟩,⟨416286, by decide⟩]) unmarked_context_12_28219_416287 node_context_12_28219_416287
  intro a
  fin_cases a
  · exact context_13_112876_416219
  · exact context_13_112877_416263
  · exact context_13_112878_416279
  · exact context_13_112879_416286

theorem unmarked_context_11_7054_416288 : frontier 10 ⟨416288, by decide⟩
    (prefixCache 11 7054) (prefixPartial 11 7054) = false := by
  decide +kernel

theorem node_context_11_7054_416288 : EJMOriginalGlobalDAGData.nodes 10 ⟨416288, by decide⟩ =
    .split (coordinate 11) (![⟨416037, by decide⟩,⟨416106, by decide⟩,⟨416210, by decide⟩,⟨416287, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_7054_416288 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7054 ⟨416288, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 7054
    ⟨416288, by decide⟩ (by decide) (![⟨416037, by decide⟩,⟨416106, by decide⟩,⟨416210, by decide⟩,⟨416287, by decide⟩]) unmarked_context_11_7054_416288 node_context_11_7054_416288
  intro a
  fin_cases a
  · exact context_12_28216_416037
  · exact context_12_28217_416106
  · exact context_12_28218_416210
  · exact context_12_28219_416287

theorem selected_cut_16358 : selected 8 ⟨416291, by decide⟩
    (prefixPartial 13 112880) = some ⟨13, 2, 0, 416291, 112880, 193, 16384⟩ := by
  decide +kernel

theorem context_13_112880_416291 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112880 ⟨416291, by decide⟩ :=
  accepted_of_selected 13 112880 ⟨416291, by decide⟩ ⟨13, 2, 0, 416291, 112880, 193, 16384⟩
    (by decide) selected_cut_16358

theorem selected_cut_16359 : selected 8 ⟨416354, by decide⟩
    (prefixPartial 13 112881) = some ⟨13, 2, 0, 416354, 112881, 3149, 16384⟩ := by
  decide +kernel

theorem context_13_112881_416354 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112881 ⟨416354, by decide⟩ :=
  accepted_of_selected 13 112881 ⟨416354, by decide⟩ ⟨13, 2, 0, 416354, 112881, 3149, 16384⟩
    (by decide) selected_cut_16359

theorem selected_cut_16360 : selected 8 ⟨416373, by decide⟩
    (prefixPartial 13 112882) = some ⟨13, 2, 0, 416373, 112882, 1565, 16384⟩ := by
  decide +kernel

theorem context_13_112882_416373 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112882 ⟨416373, by decide⟩ :=
  accepted_of_selected 13 112882 ⟨416373, by decide⟩ ⟨13, 2, 0, 416373, 112882, 1565, 16384⟩
    (by decide) selected_cut_16360

theorem selected_cut_16361 : selected 8 ⟨416383, by decide⟩
    (prefixPartial 13 112883) = some ⟨13, 2, 0, 416383, 112883, 921, 16384⟩ := by
  decide +kernel

theorem context_13_112883_416383 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112883 ⟨416383, by decide⟩ :=
  accepted_of_selected 13 112883 ⟨416383, by decide⟩ ⟨13, 2, 0, 416383, 112883, 921, 16384⟩
    (by decide) selected_cut_16361

theorem unmarked_context_12_28220_416384 : frontier 9 ⟨416384, by decide⟩
    (prefixCache 12 28220) (prefixPartial 12 28220) = false := by
  decide +kernel

theorem node_context_12_28220_416384 : EJMOriginalGlobalDAGData.nodes 9 ⟨416384, by decide⟩ =
    .split (coordinate 12) (![⟨416291, by decide⟩,⟨416354, by decide⟩,⟨416373, by decide⟩,⟨416383, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28220_416384 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28220 ⟨416384, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28220
    ⟨416384, by decide⟩ (by decide) (![⟨416291, by decide⟩,⟨416354, by decide⟩,⟨416373, by decide⟩,⟨416383, by decide⟩]) unmarked_context_12_28220_416384 node_context_12_28220_416384
  intro a
  fin_cases a
  · exact context_13_112880_416291
  · exact context_13_112881_416354
  · exact context_13_112882_416373
  · exact context_13_112883_416383

theorem selected_cut_16362 : selected 8 ⟨416387, by decide⟩
    (prefixPartial 13 112884) = some ⟨13, 2, 0, 416387, 112884, 153, 16384⟩ := by
  decide +kernel

theorem context_13_112884_416387 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112884 ⟨416387, by decide⟩ :=
  accepted_of_selected 13 112884 ⟨416387, by decide⟩ ⟨13, 2, 0, 416387, 112884, 153, 16384⟩
    (by decide) selected_cut_16362

theorem selected_cut_16363 : selected 8 ⟨416453, by decide⟩
    (prefixPartial 13 112885) = some ⟨13, 2, 0, 416453, 112885, 3337, 16384⟩ := by
  decide +kernel

theorem context_13_112885_416453 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112885 ⟨416453, by decide⟩ :=
  accepted_of_selected 13 112885 ⟨416453, by decide⟩ ⟨13, 2, 0, 416453, 112885, 3337, 16384⟩
    (by decide) selected_cut_16363

theorem selected_cut_16364 : selected 8 ⟨416479, by decide⟩
    (prefixPartial 13 112886) = some ⟨13, 2, 0, 416479, 112886, 1861, 16384⟩ := by
  decide +kernel

theorem context_13_112886_416479 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112886 ⟨416479, by decide⟩ :=
  accepted_of_selected 13 112886 ⟨416479, by decide⟩ ⟨13, 2, 0, 416479, 112886, 1861, 16384⟩
    (by decide) selected_cut_16364

theorem selected_cut_16365 : selected 8 ⟨416487, by decide⟩
    (prefixPartial 13 112887) = some ⟨13, 2, 0, 416487, 112887, 1073, 16384⟩ := by
  decide +kernel

theorem context_13_112887_416487 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112887 ⟨416487, by decide⟩ :=
  accepted_of_selected 13 112887 ⟨416487, by decide⟩ ⟨13, 2, 0, 416487, 112887, 1073, 16384⟩
    (by decide) selected_cut_16365

theorem unmarked_context_12_28221_416488 : frontier 9 ⟨416488, by decide⟩
    (prefixCache 12 28221) (prefixPartial 12 28221) = false := by
  decide +kernel

theorem node_context_12_28221_416488 : EJMOriginalGlobalDAGData.nodes 9 ⟨416488, by decide⟩ =
    .split (coordinate 12) (![⟨416387, by decide⟩,⟨416453, by decide⟩,⟨416479, by decide⟩,⟨416487, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28221_416488 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28221 ⟨416488, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28221
    ⟨416488, by decide⟩ (by decide) (![⟨416387, by decide⟩,⟨416453, by decide⟩,⟨416479, by decide⟩,⟨416487, by decide⟩]) unmarked_context_12_28221_416488 node_context_12_28221_416488
  intro a
  fin_cases a
  · exact context_13_112884_416387
  · exact context_13_112885_416453
  · exact context_13_112886_416479
  · exact context_13_112887_416487

theorem selected_cut_16366 : selected 8 ⟨416491, by decide⟩
    (prefixPartial 13 112888) = some ⟨13, 2, 0, 416491, 112888, 65, 16384⟩ := by
  decide +kernel

theorem context_13_112888_416491 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112888 ⟨416491, by decide⟩ :=
  accepted_of_selected 13 112888 ⟨416491, by decide⟩ ⟨13, 2, 0, 416491, 112888, 65, 16384⟩
    (by decide) selected_cut_16366

theorem selected_cut_16367 : selected 8 ⟨416551, by decide⟩
    (prefixPartial 13 112889) = some ⟨13, 2, 0, 416551, 112889, 2965, 16384⟩ := by
  decide +kernel

theorem context_13_112889_416551 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112889 ⟨416551, by decide⟩ :=
  accepted_of_selected 13 112889 ⟨416551, by decide⟩ ⟨13, 2, 0, 416551, 112889, 2965, 16384⟩
    (by decide) selected_cut_16367

theorem selected_cut_16368 : selected 8 ⟨416568, by decide⟩
    (prefixPartial 13 112890) = some ⟨13, 2, 0, 416568, 112890, 1513, 16384⟩ := by
  decide +kernel

theorem context_13_112890_416568 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112890 ⟨416568, by decide⟩ :=
  accepted_of_selected 13 112890 ⟨416568, by decide⟩ ⟨13, 2, 0, 416568, 112890, 1513, 16384⟩
    (by decide) selected_cut_16368

theorem selected_cut_16369 : selected 8 ⟨416572, by decide⟩
    (prefixPartial 13 112891) = some ⟨13, 2, 0, 416572, 112891, 1013, 16384⟩ := by
  decide +kernel

theorem context_13_112891_416572 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112891 ⟨416572, by decide⟩ :=
  accepted_of_selected 13 112891 ⟨416572, by decide⟩ ⟨13, 2, 0, 416572, 112891, 1013, 16384⟩
    (by decide) selected_cut_16369

theorem unmarked_context_12_28222_416573 : frontier 9 ⟨416573, by decide⟩
    (prefixCache 12 28222) (prefixPartial 12 28222) = false := by
  decide +kernel

theorem node_context_12_28222_416573 : EJMOriginalGlobalDAGData.nodes 9 ⟨416573, by decide⟩ =
    .split (coordinate 12) (![⟨416491, by decide⟩,⟨416551, by decide⟩,⟨416568, by decide⟩,⟨416572, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28222_416573 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28222 ⟨416573, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28222
    ⟨416573, by decide⟩ (by decide) (![⟨416491, by decide⟩,⟨416551, by decide⟩,⟨416568, by decide⟩,⟨416572, by decide⟩]) unmarked_context_12_28222_416573 node_context_12_28222_416573
  intro a
  fin_cases a
  · exact context_13_112888_416491
  · exact context_13_112889_416551
  · exact context_13_112890_416568
  · exact context_13_112891_416572

theorem selected_cut_16370 : selected 9 ⟨416574, by decide⟩
    (prefixPartial 12 28223) = some ⟨12, 1, 0, 416574, 28223, 1, 65536⟩ := by
  decide +kernel

theorem context_12_28223_416574 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28223 ⟨416574, by decide⟩ :=
  accepted_of_selected 12 28223 ⟨416574, by decide⟩ ⟨12, 1, 0, 416574, 28223, 1, 65536⟩
    (by decide) selected_cut_16370

theorem unmarked_context_11_7055_416575 : frontier 10 ⟨416575, by decide⟩
    (prefixCache 11 7055) (prefixPartial 11 7055) = false := by
  decide +kernel

theorem node_context_11_7055_416575 : EJMOriginalGlobalDAGData.nodes 10 ⟨416575, by decide⟩ =
    .split (coordinate 11) (![⟨416384, by decide⟩,⟨416488, by decide⟩,⟨416573, by decide⟩,⟨416574, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_7055_416575 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7055 ⟨416575, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 7055
    ⟨416575, by decide⟩ (by decide) (![⟨416384, by decide⟩,⟨416488, by decide⟩,⟨416573, by decide⟩,⟨416574, by decide⟩]) unmarked_context_11_7055_416575 node_context_11_7055_416575
  intro a
  fin_cases a
  · exact context_12_28220_416384
  · exact context_12_28221_416488
  · exact context_12_28222_416573
  · exact context_12_28223_416574

theorem unmarked_context_10_1763_416576 : frontier 11 ⟨416576, by decide⟩
    (prefixCache 10 1763) (prefixPartial 10 1763) = false := by
  decide +kernel

theorem node_context_10_1763_416576 : EJMOriginalGlobalDAGData.nodes 11 ⟨416576, by decide⟩ =
    .split (coordinate 10) (![⟨415745, by decide⟩,⟨415974, by decide⟩,⟨416288, by decide⟩,⟨416575, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1763_416576 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1763 ⟨416576, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1763
    ⟨416576, by decide⟩ (by decide) (![⟨415745, by decide⟩,⟨415974, by decide⟩,⟨416288, by decide⟩,⟨416575, by decide⟩]) unmarked_context_10_1763_416576 node_context_10_1763_416576
  intro a
  fin_cases a
  · exact context_11_7052_415745
  · exact context_11_7053_415974
  · exact context_11_7054_416288
  · exact context_11_7055_416575

theorem unmarked_context_9_440_416577 : frontier 12 ⟨416577, by decide⟩
    (prefixCache 9 440) (prefixPartial 9 440) = false := by
  decide +kernel

theorem node_context_9_440_416577 : EJMOriginalGlobalDAGData.nodes 12 ⟨416577, by decide⟩ =
    .split (coordinate 9) (![⟨412821, by decide⟩,⟨414221, by decide⟩,⟨415480, by decide⟩,⟨416576, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_440_416577 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 440 ⟨416577, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 440
    ⟨416577, by decide⟩ (by decide) (![⟨412821, by decide⟩,⟨414221, by decide⟩,⟨415480, by decide⟩,⟨416576, by decide⟩]) unmarked_context_9_440_416577 node_context_9_440_416577
  intro a
  fin_cases a
  · exact context_10_1760_412821
  · exact context_10_1761_414221
  · exact context_10_1762_415480
  · exact context_10_1763_416576

theorem selected_cut_16371 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 112896) = some ⟨13, 1, 0, 3444, 112896, 1, 16384⟩ := by
  decide +kernel

theorem context_13_112896_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112896 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 112896 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 112896, 1, 16384⟩
    (by decide) selected_cut_16371

theorem selected_cut_16372 : selected 8 ⟨416623, by decide⟩
    (prefixPartial 13 112897) = some ⟨13, 2, 0, 416623, 112897, 2985, 16384⟩ := by
  decide +kernel

theorem context_13_112897_416623 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112897 ⟨416623, by decide⟩ :=
  accepted_of_selected 13 112897 ⟨416623, by decide⟩ ⟨13, 2, 0, 416623, 112897, 2985, 16384⟩
    (by decide) selected_cut_16372

theorem selected_cut_16373 : selected 8 ⟨416636, by decide⟩
    (prefixPartial 13 112898) = some ⟨13, 2, 0, 416636, 112898, 1417, 16384⟩ := by
  decide +kernel

theorem context_13_112898_416636 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112898 ⟨416636, by decide⟩ :=
  accepted_of_selected 13 112898 ⟨416636, by decide⟩ ⟨13, 2, 0, 416636, 112898, 1417, 16384⟩
    (by decide) selected_cut_16373

theorem selected_cut_16374 : selected 8 ⟨416648, by decide⟩
    (prefixPartial 13 112899) = some ⟨13, 2, 0, 416648, 112899, 725, 16384⟩ := by
  decide +kernel

theorem context_13_112899_416648 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112899 ⟨416648, by decide⟩ :=
  accepted_of_selected 13 112899 ⟨416648, by decide⟩ ⟨13, 2, 0, 416648, 112899, 725, 16384⟩
    (by decide) selected_cut_16374

theorem unmarked_context_12_28224_416649 : frontier 9 ⟨416649, by decide⟩
    (prefixCache 12 28224) (prefixPartial 12 28224) = false := by
  decide +kernel

theorem node_context_12_28224_416649 : EJMOriginalGlobalDAGData.nodes 9 ⟨416649, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨416623, by decide⟩,⟨416636, by decide⟩,⟨416648, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28224_416649 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28224 ⟨416649, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28224
    ⟨416649, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨416623, by decide⟩,⟨416636, by decide⟩,⟨416648, by decide⟩]) unmarked_context_12_28224_416649 node_context_12_28224_416649
  intro a
  fin_cases a
  · exact context_13_112896_3444
  · exact context_13_112897_416623
  · exact context_13_112898_416636
  · exact context_13_112899_416648

theorem selected_cut_16375 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 112900) = some ⟨13, 1, 0, 3444, 112900, 1, 16384⟩ := by
  decide +kernel

theorem context_13_112900_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112900 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 112900 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 112900, 1, 16384⟩
    (by decide) selected_cut_16375

theorem selected_cut_16376 : selected 7 ⟨416681, by decide⟩
    (prefixPartial 14 451604) = some ⟨14, 2, 0, 416681, 451604, 1081, 4096⟩ := by
  decide +kernel

theorem context_14_451604_416681 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 451604 ⟨416681, by decide⟩ :=
  accepted_of_selected 14 451604 ⟨416681, by decide⟩ ⟨14, 2, 0, 416681, 451604, 1081, 4096⟩
    (by decide) selected_cut_16376

theorem selected_cut_16377 : selected 7 ⟨416705, by decide⟩
    (prefixPartial 14 451605) = some ⟨14, 2, 0, 416705, 451605, 901, 4096⟩ := by
  decide +kernel

theorem context_14_451605_416705 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 451605 ⟨416705, by decide⟩ :=
  accepted_of_selected 14 451605 ⟨416705, by decide⟩ ⟨14, 2, 0, 416705, 451605, 901, 4096⟩
    (by decide) selected_cut_16377

theorem selected_cut_16378 : selected 7 ⟨416744, by decide⟩
    (prefixPartial 14 451606) = some ⟨14, 2, 0, 416744, 451606, 1225, 4096⟩ := by
  decide +kernel

theorem context_14_451606_416744 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 451606 ⟨416744, by decide⟩ :=
  accepted_of_selected 14 451606 ⟨416744, by decide⟩ ⟨14, 2, 0, 416744, 451606, 1225, 4096⟩
    (by decide) selected_cut_16378

theorem selected_cut_16379 : selected 7 ⟨416783, by decide⟩
    (prefixPartial 14 451607) = some ⟨14, 2, 0, 416783, 451607, 1213, 4096⟩ := by
  decide +kernel

theorem context_14_451607_416783 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 451607 ⟨416783, by decide⟩ :=
  accepted_of_selected 14 451607 ⟨416783, by decide⟩ ⟨14, 2, 0, 416783, 451607, 1213, 4096⟩
    (by decide) selected_cut_16379

theorem unmarked_context_13_112901_416784 : frontier 8 ⟨416784, by decide⟩
    (prefixCache 13 112901) (prefixPartial 13 112901) = false := by
  decide +kernel

theorem node_context_13_112901_416784 : EJMOriginalGlobalDAGData.nodes 8 ⟨416784, by decide⟩ =
    .split (coordinate 13) (![⟨416681, by decide⟩,⟨416705, by decide⟩,⟨416744, by decide⟩,⟨416783, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_112901_416784 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112901 ⟨416784, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 112901
    ⟨416784, by decide⟩ (by decide) (![⟨416681, by decide⟩,⟨416705, by decide⟩,⟨416744, by decide⟩,⟨416783, by decide⟩]) unmarked_context_13_112901_416784 node_context_13_112901_416784
  intro a
  fin_cases a
  · exact context_14_451604_416681
  · exact context_14_451605_416705
  · exact context_14_451606_416744
  · exact context_14_451607_416783

theorem selected_cut_16380 : selected 8 ⟨416822, by decide⟩
    (prefixPartial 13 112902) = some ⟨13, 2, 0, 416822, 112902, 2245, 16384⟩ := by
  decide +kernel

theorem context_13_112902_416822 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112902 ⟨416822, by decide⟩ :=
  accepted_of_selected 13 112902 ⟨416822, by decide⟩ ⟨13, 2, 0, 416822, 112902, 2245, 16384⟩
    (by decide) selected_cut_16380

theorem selected_cut_16381 : selected 8 ⟨416854, by decide⟩
    (prefixPartial 13 112903) = some ⟨13, 2, 0, 416854, 112903, 1137, 16384⟩ := by
  decide +kernel

theorem context_13_112903_416854 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112903 ⟨416854, by decide⟩ :=
  accepted_of_selected 13 112903 ⟨416854, by decide⟩ ⟨13, 2, 0, 416854, 112903, 1137, 16384⟩
    (by decide) selected_cut_16381

theorem unmarked_context_12_28225_416855 : frontier 9 ⟨416855, by decide⟩
    (prefixCache 12 28225) (prefixPartial 12 28225) = false := by
  decide +kernel

theorem node_context_12_28225_416855 : EJMOriginalGlobalDAGData.nodes 9 ⟨416855, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨416784, by decide⟩,⟨416822, by decide⟩,⟨416854, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28225_416855 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28225 ⟨416855, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28225
    ⟨416855, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨416784, by decide⟩,⟨416822, by decide⟩,⟨416854, by decide⟩]) unmarked_context_12_28225_416855 node_context_12_28225_416855
  intro a
  fin_cases a
  · exact context_13_112900_3444
  · exact context_13_112901_416784
  · exact context_13_112902_416822
  · exact context_13_112903_416854

theorem selected_cut_16382 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 112904) = some ⟨13, 1, 0, 3444, 112904, 1, 16384⟩ := by
  decide +kernel

theorem context_13_112904_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112904 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 112904 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 112904, 1, 16384⟩
    (by decide) selected_cut_16382

theorem selected_cut_16383 : selected 8 ⟨416891, by decide⟩
    (prefixPartial 13 112905) = some ⟨13, 2, 0, 416891, 112905, 2769, 16384⟩ := by
  decide +kernel

theorem context_13_112905_416891 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112905 ⟨416891, by decide⟩ :=
  accepted_of_selected 13 112905 ⟨416891, by decide⟩ ⟨13, 2, 0, 416891, 112905, 2769, 16384⟩
    (by decide) selected_cut_16383

theorem selected_cut_16384 : selected 8 ⟨416912, by decide⟩
    (prefixPartial 13 112906) = some ⟨13, 2, 0, 416912, 112906, 1333, 16384⟩ := by
  decide +kernel

theorem context_13_112906_416912 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112906 ⟨416912, by decide⟩ :=
  accepted_of_selected 13 112906 ⟨416912, by decide⟩ ⟨13, 2, 0, 416912, 112906, 1333, 16384⟩
    (by decide) selected_cut_16384

theorem selected_cut_16385 : selected 8 ⟨416924, by decide⟩
    (prefixPartial 13 112907) = some ⟨13, 2, 0, 416924, 112907, 777, 16384⟩ := by
  decide +kernel

theorem context_13_112907_416924 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112907 ⟨416924, by decide⟩ :=
  accepted_of_selected 13 112907 ⟨416924, by decide⟩ ⟨13, 2, 0, 416924, 112907, 777, 16384⟩
    (by decide) selected_cut_16385

theorem unmarked_context_12_28226_416925 : frontier 9 ⟨416925, by decide⟩
    (prefixCache 12 28226) (prefixPartial 12 28226) = false := by
  decide +kernel

theorem node_context_12_28226_416925 : EJMOriginalGlobalDAGData.nodes 9 ⟨416925, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨416891, by decide⟩,⟨416912, by decide⟩,⟨416924, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28226_416925 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28226 ⟨416925, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28226
    ⟨416925, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨416891, by decide⟩,⟨416912, by decide⟩,⟨416924, by decide⟩]) unmarked_context_12_28226_416925 node_context_12_28226_416925
  intro a
  fin_cases a
  · exact context_13_112904_3444
  · exact context_13_112905_416891
  · exact context_13_112906_416912
  · exact context_13_112907_416924

theorem selected_cut_16386 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 112908) = some ⟨13, 1, 0, 3444, 112908, 1, 16384⟩ := by
  decide +kernel

theorem context_13_112908_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112908 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 112908 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 112908, 1, 16384⟩
    (by decide) selected_cut_16386

theorem selected_cut_16387 : selected 8 ⟨416988, by decide⟩
    (prefixPartial 13 112909) = some ⟨13, 2, 0, 416988, 112909, 3301, 16384⟩ := by
  decide +kernel

theorem context_13_112909_416988 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112909 ⟨416988, by decide⟩ :=
  accepted_of_selected 13 112909 ⟨416988, by decide⟩ ⟨13, 2, 0, 416988, 112909, 3301, 16384⟩
    (by decide) selected_cut_16387

theorem selected_cut_16388 : selected 8 ⟨417009, by decide⟩
    (prefixPartial 13 112910) = some ⟨13, 2, 0, 417009, 112910, 1693, 16384⟩ := by
  decide +kernel

theorem context_13_112910_417009 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112910 ⟨417009, by decide⟩ :=
  accepted_of_selected 13 112910 ⟨417009, by decide⟩ ⟨13, 2, 0, 417009, 112910, 1693, 16384⟩
    (by decide) selected_cut_16388

theorem selected_cut_16389 : selected 8 ⟨417018, by decide⟩
    (prefixPartial 13 112911) = some ⟨13, 2, 0, 417018, 112911, 937, 16384⟩ := by
  decide +kernel

theorem context_13_112911_417018 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112911 ⟨417018, by decide⟩ :=
  accepted_of_selected 13 112911 ⟨417018, by decide⟩ ⟨13, 2, 0, 417018, 112911, 937, 16384⟩
    (by decide) selected_cut_16389

theorem unmarked_context_12_28227_417019 : frontier 9 ⟨417019, by decide⟩
    (prefixCache 12 28227) (prefixPartial 12 28227) = false := by
  decide +kernel

theorem node_context_12_28227_417019 : EJMOriginalGlobalDAGData.nodes 9 ⟨417019, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨416988, by decide⟩,⟨417009, by decide⟩,⟨417018, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28227_417019 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28227 ⟨417019, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28227
    ⟨417019, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨416988, by decide⟩,⟨417009, by decide⟩,⟨417018, by decide⟩]) unmarked_context_12_28227_417019 node_context_12_28227_417019
  intro a
  fin_cases a
  · exact context_13_112908_3444
  · exact context_13_112909_416988
  · exact context_13_112910_417009
  · exact context_13_112911_417018

theorem unmarked_context_11_7056_417020 : frontier 10 ⟨417020, by decide⟩
    (prefixCache 11 7056) (prefixPartial 11 7056) = false := by
  decide +kernel

theorem node_context_11_7056_417020 : EJMOriginalGlobalDAGData.nodes 10 ⟨417020, by decide⟩ =
    .split (coordinate 11) (![⟨416649, by decide⟩,⟨416855, by decide⟩,⟨416925, by decide⟩,⟨417019, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_7056_417020 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7056 ⟨417020, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 7056
    ⟨417020, by decide⟩ (by decide) (![⟨416649, by decide⟩,⟨416855, by decide⟩,⟨416925, by decide⟩,⟨417019, by decide⟩]) unmarked_context_11_7056_417020 node_context_11_7056_417020
  intro a
  fin_cases a
  · exact context_12_28224_416649
  · exact context_12_28225_416855
  · exact context_12_28226_416925
  · exact context_12_28227_417019

theorem selected_cut_16390 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 112912) = some ⟨13, 1, 0, 3444, 112912, 1, 16384⟩ := by
  decide +kernel

theorem context_13_112912_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112912 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 112912 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 112912, 1, 16384⟩
    (by decide) selected_cut_16390

theorem selected_cut_16391 : selected 8 ⟨417084, by decide⟩
    (prefixPartial 13 112913) = some ⟨13, 2, 0, 417084, 112913, 3033, 16384⟩ := by
  decide +kernel

theorem context_13_112913_417084 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112913 ⟨417084, by decide⟩ :=
  accepted_of_selected 13 112913 ⟨417084, by decide⟩ ⟨13, 2, 0, 417084, 112913, 3033, 16384⟩
    (by decide) selected_cut_16391

theorem selected_cut_16392 : selected 8 ⟨417101, by decide⟩
    (prefixPartial 13 112914) = some ⟨13, 2, 0, 417101, 112914, 1629, 16384⟩ := by
  decide +kernel

theorem context_13_112914_417101 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112914 ⟨417101, by decide⟩ :=
  accepted_of_selected 13 112914 ⟨417101, by decide⟩ ⟨13, 2, 0, 417101, 112914, 1629, 16384⟩
    (by decide) selected_cut_16392

theorem selected_cut_16393 : selected 8 ⟨417107, by decide⟩
    (prefixPartial 13 112915) = some ⟨13, 2, 0, 417107, 112915, 709, 16384⟩ := by
  decide +kernel

theorem context_13_112915_417107 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112915 ⟨417107, by decide⟩ :=
  accepted_of_selected 13 112915 ⟨417107, by decide⟩ ⟨13, 2, 0, 417107, 112915, 709, 16384⟩
    (by decide) selected_cut_16393

theorem unmarked_context_12_28228_417108 : frontier 9 ⟨417108, by decide⟩
    (prefixCache 12 28228) (prefixPartial 12 28228) = false := by
  decide +kernel

theorem node_context_12_28228_417108 : EJMOriginalGlobalDAGData.nodes 9 ⟨417108, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨417084, by decide⟩,⟨417101, by decide⟩,⟨417107, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28228_417108 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28228 ⟨417108, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28228
    ⟨417108, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨417084, by decide⟩,⟨417101, by decide⟩,⟨417107, by decide⟩]) unmarked_context_12_28228_417108 node_context_12_28228_417108
  intro a
  fin_cases a
  · exact context_13_112912_3444
  · exact context_13_112913_417084
  · exact context_13_112914_417101
  · exact context_13_112915_417107

theorem selected_cut_16394 : selected 9 ⟨417109, by decide⟩
    (prefixPartial 12 28229) = some ⟨12, 1, 0, 417109, 28229, 1, 65536⟩ := by
  decide +kernel

theorem context_12_28229_417109 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28229 ⟨417109, by decide⟩ :=
  accepted_of_selected 12 28229 ⟨417109, by decide⟩ ⟨12, 1, 0, 417109, 28229, 1, 65536⟩
    (by decide) selected_cut_16394

theorem selected_cut_16395 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 112920) = some ⟨13, 1, 0, 3444, 112920, 1, 16384⟩ := by
  decide +kernel

theorem context_13_112920_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112920 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 112920 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 112920, 1, 16384⟩
    (by decide) selected_cut_16395

theorem selected_cut_16396 : selected 8 ⟨417149, by decide⟩
    (prefixPartial 13 112921) = some ⟨13, 2, 0, 417149, 112921, 2553, 16384⟩ := by
  decide +kernel

theorem context_13_112921_417149 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112921 ⟨417149, by decide⟩ :=
  accepted_of_selected 13 112921 ⟨417149, by decide⟩ ⟨13, 2, 0, 417149, 112921, 2553, 16384⟩
    (by decide) selected_cut_16396

theorem selected_cut_16397 : selected 8 ⟨417168, by decide⟩
    (prefixPartial 13 112922) = some ⟨13, 2, 0, 417168, 112922, 1605, 16384⟩ := by
  decide +kernel

theorem context_13_112922_417168 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112922 ⟨417168, by decide⟩ :=
  accepted_of_selected 13 112922 ⟨417168, by decide⟩ ⟨13, 2, 0, 417168, 112922, 1605, 16384⟩
    (by decide) selected_cut_16397

theorem selected_cut_16398 : selected 8 ⟨417175, by decide⟩
    (prefixPartial 13 112923) = some ⟨13, 2, 0, 417175, 112923, 793, 16384⟩ := by
  decide +kernel

theorem context_13_112923_417175 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112923 ⟨417175, by decide⟩ :=
  accepted_of_selected 13 112923 ⟨417175, by decide⟩ ⟨13, 2, 0, 417175, 112923, 793, 16384⟩
    (by decide) selected_cut_16398

theorem unmarked_context_12_28230_417176 : frontier 9 ⟨417176, by decide⟩
    (prefixCache 12 28230) (prefixPartial 12 28230) = false := by
  decide +kernel

theorem node_context_12_28230_417176 : EJMOriginalGlobalDAGData.nodes 9 ⟨417176, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨417149, by decide⟩,⟨417168, by decide⟩,⟨417175, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28230_417176 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28230 ⟨417176, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28230
    ⟨417176, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨417149, by decide⟩,⟨417168, by decide⟩,⟨417175, by decide⟩]) unmarked_context_12_28230_417176 node_context_12_28230_417176
  intro a
  fin_cases a
  · exact context_13_112920_3444
  · exact context_13_112921_417149
  · exact context_13_112922_417168
  · exact context_13_112923_417175

theorem selected_cut_16399 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 112924) = some ⟨13, 1, 0, 3444, 112924, 1, 16384⟩ := by
  decide +kernel

theorem context_13_112924_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112924 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 112924 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 112924, 1, 16384⟩
    (by decide) selected_cut_16399

theorem selected_cut_16400 : selected 8 ⟨417234, by decide⟩
    (prefixPartial 13 112925) = some ⟨13, 2, 0, 417234, 112925, 2929, 16384⟩ := by
  decide +kernel

theorem context_13_112925_417234 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112925 ⟨417234, by decide⟩ :=
  accepted_of_selected 13 112925 ⟨417234, by decide⟩ ⟨13, 2, 0, 417234, 112925, 2929, 16384⟩
    (by decide) selected_cut_16400

theorem selected_cut_16401 : selected 8 ⟨417253, by decide⟩
    (prefixPartial 13 112926) = some ⟨13, 2, 0, 417253, 112926, 1849, 16384⟩ := by
  decide +kernel

theorem context_13_112926_417253 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112926 ⟨417253, by decide⟩ :=
  accepted_of_selected 13 112926 ⟨417253, by decide⟩ ⟨13, 2, 0, 417253, 112926, 1849, 16384⟩
    (by decide) selected_cut_16401

theorem selected_cut_16402 : selected 8 ⟨417261, by decide⟩
    (prefixPartial 13 112927) = some ⟨13, 2, 0, 417261, 112927, 953, 16384⟩ := by
  decide +kernel

theorem context_13_112927_417261 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112927 ⟨417261, by decide⟩ :=
  accepted_of_selected 13 112927 ⟨417261, by decide⟩ ⟨13, 2, 0, 417261, 112927, 953, 16384⟩
    (by decide) selected_cut_16402

theorem unmarked_context_12_28231_417262 : frontier 9 ⟨417262, by decide⟩
    (prefixCache 12 28231) (prefixPartial 12 28231) = false := by
  decide +kernel

theorem node_context_12_28231_417262 : EJMOriginalGlobalDAGData.nodes 9 ⟨417262, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨417234, by decide⟩,⟨417253, by decide⟩,⟨417261, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28231_417262 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28231 ⟨417262, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28231
    ⟨417262, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨417234, by decide⟩,⟨417253, by decide⟩,⟨417261, by decide⟩]) unmarked_context_12_28231_417262 node_context_12_28231_417262
  intro a
  fin_cases a
  · exact context_13_112924_3444
  · exact context_13_112925_417234
  · exact context_13_112926_417253
  · exact context_13_112927_417261

theorem unmarked_context_11_7057_417263 : frontier 10 ⟨417263, by decide⟩
    (prefixCache 11 7057) (prefixPartial 11 7057) = false := by
  decide +kernel

theorem node_context_11_7057_417263 : EJMOriginalGlobalDAGData.nodes 10 ⟨417263, by decide⟩ =
    .split (coordinate 11) (![⟨417108, by decide⟩,⟨417109, by decide⟩,⟨417176, by decide⟩,⟨417262, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_7057_417263 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7057 ⟨417263, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 7057
    ⟨417263, by decide⟩ (by decide) (![⟨417108, by decide⟩,⟨417109, by decide⟩,⟨417176, by decide⟩,⟨417262, by decide⟩]) unmarked_context_11_7057_417263 node_context_11_7057_417263
  intro a
  fin_cases a
  · exact context_12_28228_417108
  · exact context_12_28229_417109
  · exact context_12_28230_417176
  · exact context_12_28231_417262

theorem selected_cut_16403 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 112928) = some ⟨13, 1, 0, 3444, 112928, 1, 16384⟩ := by
  decide +kernel

theorem context_13_112928_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112928 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 112928 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 112928, 1, 16384⟩
    (by decide) selected_cut_16403

theorem selected_cut_16404 : selected 8 ⟨417300, by decide⟩
    (prefixPartial 13 112929) = some ⟨13, 2, 0, 417300, 112929, 2189, 16384⟩ := by
  decide +kernel

theorem context_13_112929_417300 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112929 ⟨417300, by decide⟩ :=
  accepted_of_selected 13 112929 ⟨417300, by decide⟩ ⟨13, 2, 0, 417300, 112929, 2189, 16384⟩
    (by decide) selected_cut_16404

theorem selected_cut_16405 : selected 8 ⟨417321, by decide⟩
    (prefixPartial 13 112930) = some ⟨13, 2, 0, 417321, 112930, 1369, 16384⟩ := by
  decide +kernel

theorem context_13_112930_417321 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112930 ⟨417321, by decide⟩ :=
  accepted_of_selected 13 112930 ⟨417321, by decide⟩ ⟨13, 2, 0, 417321, 112930, 1369, 16384⟩
    (by decide) selected_cut_16405

theorem selected_cut_16406 : selected 8 ⟨417327, by decide⟩
    (prefixPartial 13 112931) = some ⟨13, 2, 0, 417327, 112931, 741, 16384⟩ := by
  decide +kernel

theorem context_13_112931_417327 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112931 ⟨417327, by decide⟩ :=
  accepted_of_selected 13 112931 ⟨417327, by decide⟩ ⟨13, 2, 0, 417327, 112931, 741, 16384⟩
    (by decide) selected_cut_16406

theorem unmarked_context_12_28232_417328 : frontier 9 ⟨417328, by decide⟩
    (prefixCache 12 28232) (prefixPartial 12 28232) = false := by
  decide +kernel

theorem node_context_12_28232_417328 : EJMOriginalGlobalDAGData.nodes 9 ⟨417328, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨417300, by decide⟩,⟨417321, by decide⟩,⟨417327, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28232_417328 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28232 ⟨417328, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28232
    ⟨417328, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨417300, by decide⟩,⟨417321, by decide⟩,⟨417327, by decide⟩]) unmarked_context_12_28232_417328 node_context_12_28232_417328
  intro a
  fin_cases a
  · exact context_13_112928_3444
  · exact context_13_112929_417300
  · exact context_13_112930_417321
  · exact context_13_112931_417327

theorem selected_cut_16407 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 112932) = some ⟨13, 1, 0, 3444, 112932, 1, 16384⟩ := by
  decide +kernel

theorem context_13_112932_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112932 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 112932 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 112932, 1, 16384⟩
    (by decide) selected_cut_16407

theorem selected_cut_16408 : selected 8 ⟨417394, by decide⟩
    (prefixPartial 13 112933) = some ⟨13, 2, 0, 417394, 112933, 3061, 16384⟩ := by
  decide +kernel

theorem context_13_112933_417394 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112933 ⟨417394, by decide⟩ :=
  accepted_of_selected 13 112933 ⟨417394, by decide⟩ ⟨13, 2, 0, 417394, 112933, 3061, 16384⟩
    (by decide) selected_cut_16408

theorem selected_cut_16409 : selected 8 ⟨417422, by decide⟩
    (prefixPartial 13 112934) = some ⟨13, 2, 0, 417422, 112934, 2149, 16384⟩ := by
  decide +kernel

theorem context_13_112934_417422 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112934 ⟨417422, by decide⟩ :=
  accepted_of_selected 13 112934 ⟨417422, by decide⟩ ⟨13, 2, 0, 417422, 112934, 2149, 16384⟩
    (by decide) selected_cut_16409

theorem selected_cut_16410 : selected 8 ⟨417430, by decide⟩
    (prefixPartial 13 112935) = some ⟨13, 2, 0, 417430, 112935, 1157, 16384⟩ := by
  decide +kernel

theorem context_13_112935_417430 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112935 ⟨417430, by decide⟩ :=
  accepted_of_selected 13 112935 ⟨417430, by decide⟩ ⟨13, 2, 0, 417430, 112935, 1157, 16384⟩
    (by decide) selected_cut_16410

theorem unmarked_context_12_28233_417431 : frontier 9 ⟨417431, by decide⟩
    (prefixCache 12 28233) (prefixPartial 12 28233) = false := by
  decide +kernel

theorem node_context_12_28233_417431 : EJMOriginalGlobalDAGData.nodes 9 ⟨417431, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨417394, by decide⟩,⟨417422, by decide⟩,⟨417430, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28233_417431 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28233 ⟨417431, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28233
    ⟨417431, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨417394, by decide⟩,⟨417422, by decide⟩,⟨417430, by decide⟩]) unmarked_context_12_28233_417431 node_context_12_28233_417431
  intro a
  fin_cases a
  · exact context_13_112932_3444
  · exact context_13_112933_417394
  · exact context_13_112934_417422
  · exact context_13_112935_417430

theorem selected_cut_16411 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 112936) = some ⟨13, 1, 0, 3444, 112936, 1, 16384⟩ := by
  decide +kernel

theorem context_13_112936_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112936 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 112936 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 112936, 1, 16384⟩
    (by decide) selected_cut_16411

theorem selected_cut_16412 : selected 8 ⟨417517, by decide⟩
    (prefixPartial 13 112937) = some ⟨13, 2, 0, 417517, 112937, 3337, 16384⟩ := by
  decide +kernel

theorem context_13_112937_417517 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112937 ⟨417517, by decide⟩ :=
  accepted_of_selected 13 112937 ⟨417517, by decide⟩ ⟨13, 2, 0, 417517, 112937, 3337, 16384⟩
    (by decide) selected_cut_16412

theorem selected_cut_16413 : selected 8 ⟨417554, by decide⟩
    (prefixPartial 13 112938) = some ⟨13, 2, 0, 417554, 112938, 2409, 16384⟩ := by
  decide +kernel

theorem context_13_112938_417554 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112938 ⟨417554, by decide⟩ :=
  accepted_of_selected 13 112938 ⟨417554, by decide⟩ ⟨13, 2, 0, 417554, 112938, 2409, 16384⟩
    (by decide) selected_cut_16413

theorem selected_cut_16414 : selected 8 ⟨417564, by decide⟩
    (prefixPartial 13 112939) = some ⟨13, 2, 0, 417564, 112939, 1205, 16384⟩ := by
  decide +kernel

theorem context_13_112939_417564 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112939 ⟨417564, by decide⟩ :=
  accepted_of_selected 13 112939 ⟨417564, by decide⟩ ⟨13, 2, 0, 417564, 112939, 1205, 16384⟩
    (by decide) selected_cut_16414

theorem unmarked_context_12_28234_417565 : frontier 9 ⟨417565, by decide⟩
    (prefixCache 12 28234) (prefixPartial 12 28234) = false := by
  decide +kernel

theorem node_context_12_28234_417565 : EJMOriginalGlobalDAGData.nodes 9 ⟨417565, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨417517, by decide⟩,⟨417554, by decide⟩,⟨417564, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28234_417565 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28234 ⟨417565, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28234
    ⟨417565, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨417517, by decide⟩,⟨417554, by decide⟩,⟨417564, by decide⟩]) unmarked_context_12_28234_417565 node_context_12_28234_417565
  intro a
  fin_cases a
  · exact context_13_112936_3444
  · exact context_13_112937_417517
  · exact context_13_112938_417554
  · exact context_13_112939_417564

theorem selected_cut_16415 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 112940) = some ⟨13, 1, 0, 3444, 112940, 1, 16384⟩ := by
  decide +kernel

theorem context_13_112940_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112940 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 112940 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 112940, 1, 16384⟩
    (by decide) selected_cut_16415

theorem selected_cut_16416 : selected 8 ⟨417600, by decide⟩
    (prefixPartial 13 112941) = some ⟨13, 2, 0, 417600, 112941, 2401, 16384⟩ := by
  decide +kernel

theorem context_13_112941_417600 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112941 ⟨417600, by decide⟩ :=
  accepted_of_selected 13 112941 ⟨417600, by decide⟩ ⟨13, 2, 0, 417600, 112941, 2401, 16384⟩
    (by decide) selected_cut_16416

theorem selected_cut_16417 : selected 8 ⟨417621, by decide⟩
    (prefixPartial 13 112942) = some ⟨13, 2, 0, 417621, 112942, 1557, 16384⟩ := by
  decide +kernel

theorem context_13_112942_417621 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112942 ⟨417621, by decide⟩ :=
  accepted_of_selected 13 112942 ⟨417621, by decide⟩ ⟨13, 2, 0, 417621, 112942, 1557, 16384⟩
    (by decide) selected_cut_16417

theorem selected_cut_16418 : selected 8 ⟨417633, by decide⟩
    (prefixPartial 13 112943) = some ⟨13, 2, 0, 417633, 112943, 957, 16384⟩ := by
  decide +kernel

theorem context_13_112943_417633 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112943 ⟨417633, by decide⟩ :=
  accepted_of_selected 13 112943 ⟨417633, by decide⟩ ⟨13, 2, 0, 417633, 112943, 957, 16384⟩
    (by decide) selected_cut_16418

theorem unmarked_context_12_28235_417634 : frontier 9 ⟨417634, by decide⟩
    (prefixCache 12 28235) (prefixPartial 12 28235) = false := by
  decide +kernel

theorem node_context_12_28235_417634 : EJMOriginalGlobalDAGData.nodes 9 ⟨417634, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨417600, by decide⟩,⟨417621, by decide⟩,⟨417633, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28235_417634 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28235 ⟨417634, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28235
    ⟨417634, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨417600, by decide⟩,⟨417621, by decide⟩,⟨417633, by decide⟩]) unmarked_context_12_28235_417634 node_context_12_28235_417634
  intro a
  fin_cases a
  · exact context_13_112940_3444
  · exact context_13_112941_417600
  · exact context_13_112942_417621
  · exact context_13_112943_417633

theorem unmarked_context_11_7058_417635 : frontier 10 ⟨417635, by decide⟩
    (prefixCache 11 7058) (prefixPartial 11 7058) = false := by
  decide +kernel

theorem node_context_11_7058_417635 : EJMOriginalGlobalDAGData.nodes 10 ⟨417635, by decide⟩ =
    .split (coordinate 11) (![⟨417328, by decide⟩,⟨417431, by decide⟩,⟨417565, by decide⟩,⟨417634, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_7058_417635 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7058 ⟨417635, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 7058
    ⟨417635, by decide⟩ (by decide) (![⟨417328, by decide⟩,⟨417431, by decide⟩,⟨417565, by decide⟩,⟨417634, by decide⟩]) unmarked_context_11_7058_417635 node_context_11_7058_417635
  intro a
  fin_cases a
  · exact context_12_28232_417328
  · exact context_12_28233_417431
  · exact context_12_28234_417565
  · exact context_12_28235_417634

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
