/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover115
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_11139 : selected 9 ⟨298732, by decide⟩
    (prefixPartial 12 25446) = some ⟨12, 2, 0, 298732, 25446, 3661, 65536⟩ := by
  decide +kernel

theorem context_12_25446_298732 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25446 ⟨298732, by decide⟩ :=
  accepted_of_selected 12 25446 ⟨298732, by decide⟩ ⟨12, 2, 0, 298732, 25446, 3661, 65536⟩
    (by decide) selected_cut_11139

theorem selected_cut_11140 : selected 9 ⟨298778, by decide⟩
    (prefixPartial 12 25447) = some ⟨12, 2, 0, 298778, 25447, 3673, 65536⟩ := by
  decide +kernel

theorem context_12_25447_298778 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25447 ⟨298778, by decide⟩ :=
  accepted_of_selected 12 25447 ⟨298778, by decide⟩ ⟨12, 2, 0, 298778, 25447, 3673, 65536⟩
    (by decide) selected_cut_11140

theorem unmarked_context_11_6361_298779 : frontier 10 ⟨298779, by decide⟩
    (prefixCache 11 6361) (prefixPartial 11 6361) = false := by
  decide +kernel

theorem node_context_11_6361_298779 : EJMOriginalGlobalDAGData.nodes 10 ⟨298779, by decide⟩ =
    .split (coordinate 11) (![⟨298619, by decide⟩,⟨298689, by decide⟩,⟨298732, by decide⟩,⟨298778, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6361_298779 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6361 ⟨298779, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6361
    ⟨298779, by decide⟩ (by decide) (![⟨298619, by decide⟩,⟨298689, by decide⟩,⟨298732, by decide⟩,⟨298778, by decide⟩]) unmarked_context_11_6361_298779 node_context_11_6361_298779
  intro a
  fin_cases a
  · exact context_12_25444_298619
  · exact context_12_25445_298689
  · exact context_12_25446_298732
  · exact context_12_25447_298778

theorem selected_cut_11141 : selected 9 ⟨298813, by decide⟩
    (prefixPartial 12 25448) = some ⟨12, 2, 0, 298813, 25448, 2885, 65536⟩ := by
  decide +kernel

theorem context_12_25448_298813 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25448 ⟨298813, by decide⟩ :=
  accepted_of_selected 12 25448 ⟨298813, by decide⟩ ⟨12, 2, 0, 298813, 25448, 2885, 65536⟩
    (by decide) selected_cut_11141

theorem selected_cut_11142 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 101796) = some ⟨13, 1, 0, 3444, 101796, 1, 16384⟩ := by
  decide +kernel

theorem context_13_101796_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101796 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 101796 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 101796, 1, 16384⟩
    (by decide) selected_cut_11142

theorem selected_cut_11143 : selected 8 ⟨298832, by decide⟩
    (prefixPartial 13 101797) = some ⟨13, 2, 0, 298832, 101797, 1193, 16384⟩ := by
  decide +kernel

theorem context_13_101797_298832 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101797 ⟨298832, by decide⟩ :=
  accepted_of_selected 13 101797 ⟨298832, by decide⟩ ⟨13, 2, 0, 298832, 101797, 1193, 16384⟩
    (by decide) selected_cut_11143

theorem selected_cut_11144 : selected 8 ⟨298863, by decide⟩
    (prefixPartial 13 101798) = some ⟨13, 2, 0, 298863, 101798, 2221, 16384⟩ := by
  decide +kernel

theorem context_13_101798_298863 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101798 ⟨298863, by decide⟩ :=
  accepted_of_selected 13 101798 ⟨298863, by decide⟩ ⟨13, 2, 0, 298863, 101798, 2221, 16384⟩
    (by decide) selected_cut_11144

theorem selected_cut_11145 : selected 8 ⟨298874, by decide⟩
    (prefixPartial 13 101799) = some ⟨13, 2, 0, 298874, 101799, 1017, 16384⟩ := by
  decide +kernel

theorem context_13_101799_298874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101799 ⟨298874, by decide⟩ :=
  accepted_of_selected 13 101799 ⟨298874, by decide⟩ ⟨13, 2, 0, 298874, 101799, 1017, 16384⟩
    (by decide) selected_cut_11145

theorem unmarked_context_12_25449_298875 : frontier 9 ⟨298875, by decide⟩
    (prefixCache 12 25449) (prefixPartial 12 25449) = false := by
  decide +kernel

theorem node_context_12_25449_298875 : EJMOriginalGlobalDAGData.nodes 9 ⟨298875, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨298832, by decide⟩,⟨298863, by decide⟩,⟨298874, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25449_298875 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25449 ⟨298875, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25449
    ⟨298875, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨298832, by decide⟩,⟨298863, by decide⟩,⟨298874, by decide⟩]) unmarked_context_12_25449_298875 node_context_12_25449_298875
  intro a
  fin_cases a
  · exact context_13_101796_3444
  · exact context_13_101797_298832
  · exact context_13_101798_298863
  · exact context_13_101799_298874

theorem selected_cut_11146 : selected 9 ⟨298913, by decide⟩
    (prefixPartial 12 25450) = some ⟨12, 2, 0, 298913, 25450, 3233, 65536⟩ := by
  decide +kernel

theorem context_12_25450_298913 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25450 ⟨298913, by decide⟩ :=
  accepted_of_selected 12 25450 ⟨298913, by decide⟩ ⟨12, 2, 0, 298913, 25450, 3233, 65536⟩
    (by decide) selected_cut_11146

theorem selected_cut_11147 : selected 9 ⟨298948, by decide⟩
    (prefixPartial 12 25451) = some ⟨12, 2, 0, 298948, 25451, 3241, 65536⟩ := by
  decide +kernel

theorem context_12_25451_298948 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25451 ⟨298948, by decide⟩ :=
  accepted_of_selected 12 25451 ⟨298948, by decide⟩ ⟨12, 2, 0, 298948, 25451, 3241, 65536⟩
    (by decide) selected_cut_11147

theorem unmarked_context_11_6362_298949 : frontier 10 ⟨298949, by decide⟩
    (prefixCache 11 6362) (prefixPartial 11 6362) = false := by
  decide +kernel

theorem node_context_11_6362_298949 : EJMOriginalGlobalDAGData.nodes 10 ⟨298949, by decide⟩ =
    .split (coordinate 11) (![⟨298813, by decide⟩,⟨298875, by decide⟩,⟨298913, by decide⟩,⟨298948, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6362_298949 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6362 ⟨298949, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6362
    ⟨298949, by decide⟩ (by decide) (![⟨298813, by decide⟩,⟨298875, by decide⟩,⟨298913, by decide⟩,⟨298948, by decide⟩]) unmarked_context_11_6362_298949 node_context_11_6362_298949
  intro a
  fin_cases a
  · exact context_12_25448_298813
  · exact context_12_25449_298875
  · exact context_12_25450_298913
  · exact context_12_25451_298948

theorem selected_cut_11148 : selected 9 ⟨298973, by decide⟩
    (prefixPartial 12 25452) = some ⟨12, 2, 0, 298973, 25452, 2369, 65536⟩ := by
  decide +kernel

theorem context_12_25452_298973 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25452 ⟨298973, by decide⟩ :=
  accepted_of_selected 12 25452 ⟨298973, by decide⟩ ⟨12, 2, 0, 298973, 25452, 2369, 65536⟩
    (by decide) selected_cut_11148

theorem selected_cut_11149 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 101812) = some ⟨13, 1, 0, 3444, 101812, 1, 16384⟩ := by
  decide +kernel

theorem context_13_101812_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101812 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 101812 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 101812, 1, 16384⟩
    (by decide) selected_cut_11149

theorem selected_cut_11150 : selected 8 ⟨298988, by decide⟩
    (prefixPartial 13 101813) = some ⟨13, 2, 0, 298988, 101813, 977, 16384⟩ := by
  decide +kernel

theorem context_13_101813_298988 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101813 ⟨298988, by decide⟩ :=
  accepted_of_selected 13 101813 ⟨298988, by decide⟩ ⟨13, 2, 0, 298988, 101813, 977, 16384⟩
    (by decide) selected_cut_11150

theorem selected_cut_11151 : selected 8 ⟨299008, by decide⟩
    (prefixPartial 13 101814) = some ⟨13, 2, 0, 299008, 101814, 2189, 16384⟩ := by
  decide +kernel

theorem context_13_101814_299008 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101814 ⟨299008, by decide⟩ :=
  accepted_of_selected 13 101814 ⟨299008, by decide⟩ ⟨13, 2, 0, 299008, 101814, 2189, 16384⟩
    (by decide) selected_cut_11151

theorem selected_cut_11152 : selected 8 ⟨299024, by decide⟩
    (prefixPartial 13 101815) = some ⟨13, 2, 0, 299024, 101815, 1053, 16384⟩ := by
  decide +kernel

theorem context_13_101815_299024 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101815 ⟨299024, by decide⟩ :=
  accepted_of_selected 13 101815 ⟨299024, by decide⟩ ⟨13, 2, 0, 299024, 101815, 1053, 16384⟩
    (by decide) selected_cut_11152

theorem unmarked_context_12_25453_299025 : frontier 9 ⟨299025, by decide⟩
    (prefixCache 12 25453) (prefixPartial 12 25453) = false := by
  decide +kernel

theorem node_context_12_25453_299025 : EJMOriginalGlobalDAGData.nodes 9 ⟨299025, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨298988, by decide⟩,⟨299008, by decide⟩,⟨299024, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25453_299025 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25453 ⟨299025, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25453
    ⟨299025, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨298988, by decide⟩,⟨299008, by decide⟩,⟨299024, by decide⟩]) unmarked_context_12_25453_299025 node_context_12_25453_299025
  intro a
  fin_cases a
  · exact context_13_101812_3444
  · exact context_13_101813_298988
  · exact context_13_101814_299008
  · exact context_13_101815_299024

theorem selected_cut_11153 : selected 9 ⟨299062, by decide⟩
    (prefixPartial 12 25454) = some ⟨12, 2, 0, 299062, 25454, 2881, 65536⟩ := by
  decide +kernel

theorem context_12_25454_299062 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25454 ⟨299062, by decide⟩ :=
  accepted_of_selected 12 25454 ⟨299062, by decide⟩ ⟨12, 2, 0, 299062, 25454, 2881, 65536⟩
    (by decide) selected_cut_11153

theorem selected_cut_11154 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 101820) = some ⟨13, 1, 0, 3444, 101820, 1, 16384⟩ := by
  decide +kernel

theorem context_13_101820_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101820 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 101820 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 101820, 1, 16384⟩
    (by decide) selected_cut_11154

theorem selected_cut_11155 : selected 8 ⟨299084, by decide⟩
    (prefixPartial 13 101821) = some ⟨13, 2, 0, 299084, 101821, 1165, 16384⟩ := by
  decide +kernel

theorem context_13_101821_299084 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101821 ⟨299084, by decide⟩ :=
  accepted_of_selected 13 101821 ⟨299084, by decide⟩ ⟨13, 2, 0, 299084, 101821, 1165, 16384⟩
    (by decide) selected_cut_11155

theorem selected_cut_11156 : selected 8 ⟨299115, by decide⟩
    (prefixPartial 13 101822) = some ⟨13, 2, 0, 299115, 101822, 2489, 16384⟩ := by
  decide +kernel

theorem context_13_101822_299115 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101822 ⟨299115, by decide⟩ :=
  accepted_of_selected 13 101822 ⟨299115, by decide⟩ ⟨13, 2, 0, 299115, 101822, 2489, 16384⟩
    (by decide) selected_cut_11156

theorem selected_cut_11157 : selected 8 ⟨299142, by decide⟩
    (prefixPartial 13 101823) = some ⟨13, 2, 0, 299142, 101823, 1381, 16384⟩ := by
  decide +kernel

theorem context_13_101823_299142 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101823 ⟨299142, by decide⟩ :=
  accepted_of_selected 13 101823 ⟨299142, by decide⟩ ⟨13, 2, 0, 299142, 101823, 1381, 16384⟩
    (by decide) selected_cut_11157

theorem unmarked_context_12_25455_299143 : frontier 9 ⟨299143, by decide⟩
    (prefixCache 12 25455) (prefixPartial 12 25455) = false := by
  decide +kernel

theorem node_context_12_25455_299143 : EJMOriginalGlobalDAGData.nodes 9 ⟨299143, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨299084, by decide⟩,⟨299115, by decide⟩,⟨299142, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25455_299143 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25455 ⟨299143, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25455
    ⟨299143, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨299084, by decide⟩,⟨299115, by decide⟩,⟨299142, by decide⟩]) unmarked_context_12_25455_299143 node_context_12_25455_299143
  intro a
  fin_cases a
  · exact context_13_101820_3444
  · exact context_13_101821_299084
  · exact context_13_101822_299115
  · exact context_13_101823_299142

theorem unmarked_context_11_6363_299144 : frontier 10 ⟨299144, by decide⟩
    (prefixCache 11 6363) (prefixPartial 11 6363) = false := by
  decide +kernel

theorem node_context_11_6363_299144 : EJMOriginalGlobalDAGData.nodes 10 ⟨299144, by decide⟩ =
    .split (coordinate 11) (![⟨298973, by decide⟩,⟨299025, by decide⟩,⟨299062, by decide⟩,⟨299143, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6363_299144 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6363 ⟨299144, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6363
    ⟨299144, by decide⟩ (by decide) (![⟨298973, by decide⟩,⟨299025, by decide⟩,⟨299062, by decide⟩,⟨299143, by decide⟩]) unmarked_context_11_6363_299144 node_context_11_6363_299144
  intro a
  fin_cases a
  · exact context_12_25452_298973
  · exact context_12_25453_299025
  · exact context_12_25454_299062
  · exact context_12_25455_299143

theorem unmarked_context_10_1590_299145 : frontier 11 ⟨299145, by decide⟩
    (prefixCache 10 1590) (prefixPartial 10 1590) = false := by
  decide +kernel

theorem node_context_10_1590_299145 : EJMOriginalGlobalDAGData.nodes 11 ⟨299145, by decide⟩ =
    .split (coordinate 10) (![⟨298585, by decide⟩,⟨298779, by decide⟩,⟨298949, by decide⟩,⟨299144, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1590_299145 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1590 ⟨299145, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1590
    ⟨299145, by decide⟩ (by decide) (![⟨298585, by decide⟩,⟨298779, by decide⟩,⟨298949, by decide⟩,⟨299144, by decide⟩]) unmarked_context_10_1590_299145 node_context_10_1590_299145
  intro a
  fin_cases a
  · exact context_11_6360_298585
  · exact context_11_6361_298779
  · exact context_11_6362_298949
  · exact context_11_6363_299144

theorem selected_cut_11158 : selected 9 ⟨299176, by decide⟩
    (prefixPartial 12 25456) = some ⟨12, 2, 0, 299176, 25456, 2541, 65536⟩ := by
  decide +kernel

theorem context_12_25456_299176 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25456 ⟨299176, by decide⟩ :=
  accepted_of_selected 12 25456 ⟨299176, by decide⟩ ⟨12, 2, 0, 299176, 25456, 2541, 65536⟩
    (by decide) selected_cut_11158

theorem selected_cut_11159 : selected 9 ⟨299247, by decide⟩
    (prefixPartial 12 25457) = some ⟨12, 2, 0, 299247, 25457, 3957, 65536⟩ := by
  decide +kernel

theorem context_12_25457_299247 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25457 ⟨299247, by decide⟩ :=
  accepted_of_selected 12 25457 ⟨299247, by decide⟩ ⟨12, 2, 0, 299247, 25457, 3957, 65536⟩
    (by decide) selected_cut_11159

theorem selected_cut_11160 : selected 9 ⟨299278, by decide⟩
    (prefixPartial 12 25458) = some ⟨12, 2, 0, 299278, 25458, 2821, 65536⟩ := by
  decide +kernel

theorem context_12_25458_299278 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25458 ⟨299278, by decide⟩ :=
  accepted_of_selected 12 25458 ⟨299278, by decide⟩ ⟨12, 2, 0, 299278, 25458, 2821, 65536⟩
    (by decide) selected_cut_11160

theorem selected_cut_11161 : selected 9 ⟨299313, by decide⟩
    (prefixPartial 12 25459) = some ⟨12, 2, 0, 299313, 25459, 2945, 65536⟩ := by
  decide +kernel

theorem context_12_25459_299313 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25459 ⟨299313, by decide⟩ :=
  accepted_of_selected 12 25459 ⟨299313, by decide⟩ ⟨12, 2, 0, 299313, 25459, 2945, 65536⟩
    (by decide) selected_cut_11161

theorem unmarked_context_11_6364_299314 : frontier 10 ⟨299314, by decide⟩
    (prefixCache 11 6364) (prefixPartial 11 6364) = false := by
  decide +kernel

theorem node_context_11_6364_299314 : EJMOriginalGlobalDAGData.nodes 10 ⟨299314, by decide⟩ =
    .split (coordinate 11) (![⟨299176, by decide⟩,⟨299247, by decide⟩,⟨299278, by decide⟩,⟨299313, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6364_299314 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6364 ⟨299314, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6364
    ⟨299314, by decide⟩ (by decide) (![⟨299176, by decide⟩,⟨299247, by decide⟩,⟨299278, by decide⟩,⟨299313, by decide⟩]) unmarked_context_11_6364_299314 node_context_11_6364_299314
  intro a
  fin_cases a
  · exact context_12_25456_299176
  · exact context_12_25457_299247
  · exact context_12_25458_299278
  · exact context_12_25459_299313

theorem selected_cut_11162 : selected 9 ⟨299349, by decide⟩
    (prefixPartial 12 25460) = some ⟨12, 2, 0, 299349, 25460, 2705, 65536⟩ := by
  decide +kernel

theorem context_12_25460_299349 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25460 ⟨299349, by decide⟩ :=
  accepted_of_selected 12 25460 ⟨299349, by decide⟩ ⟨12, 2, 0, 299349, 25460, 2705, 65536⟩
    (by decide) selected_cut_11162

theorem selected_cut_11163 : selected 9 ⟨299350, by decide⟩
    (prefixPartial 12 25461) = some ⟨12, 1, 0, 299350, 25461, 1, 65536⟩ := by
  decide +kernel

theorem context_12_25461_299350 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25461 ⟨299350, by decide⟩ :=
  accepted_of_selected 12 25461 ⟨299350, by decide⟩ ⟨12, 1, 0, 299350, 25461, 1, 65536⟩
    (by decide) selected_cut_11163

theorem selected_cut_11164 : selected 9 ⟨299385, by decide⟩
    (prefixPartial 12 25462) = some ⟨12, 2, 0, 299385, 25462, 3045, 65536⟩ := by
  decide +kernel

theorem context_12_25462_299385 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25462 ⟨299385, by decide⟩ :=
  accepted_of_selected 12 25462 ⟨299385, by decide⟩ ⟨12, 2, 0, 299385, 25462, 3045, 65536⟩
    (by decide) selected_cut_11164

theorem selected_cut_11165 : selected 9 ⟨299422, by decide⟩
    (prefixPartial 12 25463) = some ⟨12, 2, 0, 299422, 25463, 3189, 65536⟩ := by
  decide +kernel

theorem context_12_25463_299422 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25463 ⟨299422, by decide⟩ :=
  accepted_of_selected 12 25463 ⟨299422, by decide⟩ ⟨12, 2, 0, 299422, 25463, 3189, 65536⟩
    (by decide) selected_cut_11165

theorem unmarked_context_11_6365_299423 : frontier 10 ⟨299423, by decide⟩
    (prefixCache 11 6365) (prefixPartial 11 6365) = false := by
  decide +kernel

theorem node_context_11_6365_299423 : EJMOriginalGlobalDAGData.nodes 10 ⟨299423, by decide⟩ =
    .split (coordinate 11) (![⟨299349, by decide⟩,⟨299350, by decide⟩,⟨299385, by decide⟩,⟨299422, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6365_299423 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6365 ⟨299423, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6365
    ⟨299423, by decide⟩ (by decide) (![⟨299349, by decide⟩,⟨299350, by decide⟩,⟨299385, by decide⟩,⟨299422, by decide⟩]) unmarked_context_11_6365_299423 node_context_11_6365_299423
  intro a
  fin_cases a
  · exact context_12_25460_299349
  · exact context_12_25461_299350
  · exact context_12_25462_299385
  · exact context_12_25463_299422

theorem selected_cut_11166 : selected 9 ⟨299464, by decide⟩
    (prefixPartial 12 25464) = some ⟨12, 2, 0, 299464, 25464, 2873, 65536⟩ := by
  decide +kernel

theorem context_12_25464_299464 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25464 ⟨299464, by decide⟩ :=
  accepted_of_selected 12 25464 ⟨299464, by decide⟩ ⟨12, 2, 0, 299464, 25464, 2873, 65536⟩
    (by decide) selected_cut_11166

theorem selected_cut_11167 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 101860) = some ⟨13, 1, 0, 3444, 101860, 1, 16384⟩ := by
  decide +kernel

theorem context_13_101860_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101860 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 101860 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 101860, 1, 16384⟩
    (by decide) selected_cut_11167

theorem selected_cut_11168 : selected 8 ⟨299471, by decide⟩
    (prefixPartial 13 101861) = some ⟨13, 2, 0, 299471, 101861, 369, 16384⟩ := by
  decide +kernel

theorem context_13_101861_299471 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101861 ⟨299471, by decide⟩ :=
  accepted_of_selected 13 101861 ⟨299471, by decide⟩ ⟨13, 2, 0, 299471, 101861, 369, 16384⟩
    (by decide) selected_cut_11168

theorem selected_cut_11169 : selected 8 ⟨299533, by decide⟩
    (prefixPartial 13 101862) = some ⟨13, 2, 0, 299533, 101862, 2745, 16384⟩ := by
  decide +kernel

theorem context_13_101862_299533 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101862 ⟨299533, by decide⟩ :=
  accepted_of_selected 13 101862 ⟨299533, by decide⟩ ⟨13, 2, 0, 299533, 101862, 2745, 16384⟩
    (by decide) selected_cut_11169

theorem selected_cut_11170 : selected 8 ⟨299555, by decide⟩
    (prefixPartial 13 101863) = some ⟨13, 2, 0, 299555, 101863, 1193, 16384⟩ := by
  decide +kernel

theorem context_13_101863_299555 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101863 ⟨299555, by decide⟩ :=
  accepted_of_selected 13 101863 ⟨299555, by decide⟩ ⟨13, 2, 0, 299555, 101863, 1193, 16384⟩
    (by decide) selected_cut_11170

theorem unmarked_context_12_25465_299556 : frontier 9 ⟨299556, by decide⟩
    (prefixCache 12 25465) (prefixPartial 12 25465) = false := by
  decide +kernel

theorem node_context_12_25465_299556 : EJMOriginalGlobalDAGData.nodes 9 ⟨299556, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨299471, by decide⟩,⟨299533, by decide⟩,⟨299555, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25465_299556 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25465 ⟨299556, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25465
    ⟨299556, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨299471, by decide⟩,⟨299533, by decide⟩,⟨299555, by decide⟩]) unmarked_context_12_25465_299556 node_context_12_25465_299556
  intro a
  fin_cases a
  · exact context_13_101860_3444
  · exact context_13_101861_299471
  · exact context_13_101862_299533
  · exact context_13_101863_299555

theorem selected_cut_11171 : selected 9 ⟨299593, by decide⟩
    (prefixPartial 12 25466) = some ⟨12, 2, 0, 299593, 25466, 2885, 65536⟩ := by
  decide +kernel

theorem context_12_25466_299593 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25466 ⟨299593, by decide⟩ :=
  accepted_of_selected 12 25466 ⟨299593, by decide⟩ ⟨12, 2, 0, 299593, 25466, 2885, 65536⟩
    (by decide) selected_cut_11171

theorem selected_cut_11172 : selected 9 ⟨299628, by decide⟩
    (prefixPartial 12 25467) = some ⟨12, 2, 0, 299628, 25467, 2965, 65536⟩ := by
  decide +kernel

theorem context_12_25467_299628 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25467 ⟨299628, by decide⟩ :=
  accepted_of_selected 12 25467 ⟨299628, by decide⟩ ⟨12, 2, 0, 299628, 25467, 2965, 65536⟩
    (by decide) selected_cut_11172

theorem unmarked_context_11_6366_299629 : frontier 10 ⟨299629, by decide⟩
    (prefixCache 11 6366) (prefixPartial 11 6366) = false := by
  decide +kernel

theorem node_context_11_6366_299629 : EJMOriginalGlobalDAGData.nodes 10 ⟨299629, by decide⟩ =
    .split (coordinate 11) (![⟨299464, by decide⟩,⟨299556, by decide⟩,⟨299593, by decide⟩,⟨299628, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6366_299629 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6366 ⟨299629, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6366
    ⟨299629, by decide⟩ (by decide) (![⟨299464, by decide⟩,⟨299556, by decide⟩,⟨299593, by decide⟩,⟨299628, by decide⟩]) unmarked_context_11_6366_299629 node_context_11_6366_299629
  intro a
  fin_cases a
  · exact context_12_25464_299464
  · exact context_12_25465_299556
  · exact context_12_25466_299593
  · exact context_12_25467_299628

theorem selected_cut_11173 : selected 9 ⟨299661, by decide⟩
    (prefixPartial 12 25468) = some ⟨12, 2, 0, 299661, 25468, 2269, 65536⟩ := by
  decide +kernel

theorem context_12_25468_299661 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25468 ⟨299661, by decide⟩ :=
  accepted_of_selected 12 25468 ⟨299661, by decide⟩ ⟨12, 2, 0, 299661, 25468, 2269, 65536⟩
    (by decide) selected_cut_11173

theorem selected_cut_11174 : selected 9 ⟨299712, by decide⟩
    (prefixPartial 12 25469) = some ⟨12, 2, 0, 299712, 25469, 3549, 65536⟩ := by
  decide +kernel

theorem context_12_25469_299712 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25469 ⟨299712, by decide⟩ :=
  accepted_of_selected 12 25469 ⟨299712, by decide⟩ ⟨12, 2, 0, 299712, 25469, 3549, 65536⟩
    (by decide) selected_cut_11174

theorem selected_cut_11175 : selected 9 ⟨299741, by decide⟩
    (prefixPartial 12 25470) = some ⟨12, 2, 0, 299741, 25470, 2305, 65536⟩ := by
  decide +kernel

theorem context_12_25470_299741 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25470 ⟨299741, by decide⟩ :=
  accepted_of_selected 12 25470 ⟨299741, by decide⟩ ⟨12, 2, 0, 299741, 25470, 2305, 65536⟩
    (by decide) selected_cut_11175

theorem selected_cut_11176 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 101884) = some ⟨13, 1, 0, 3444, 101884, 1, 16384⟩ := by
  decide +kernel

theorem context_13_101884_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101884 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 101884 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 101884, 1, 16384⟩
    (by decide) selected_cut_11176

theorem selected_cut_11177 : selected 8 ⟨299747, by decide⟩
    (prefixPartial 13 101885) = some ⟨13, 2, 0, 299747, 101885, 101, 16384⟩ := by
  decide +kernel

theorem context_13_101885_299747 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101885 ⟨299747, by decide⟩ :=
  accepted_of_selected 13 101885 ⟨299747, by decide⟩ ⟨13, 2, 0, 299747, 101885, 101, 16384⟩
    (by decide) selected_cut_11177

theorem selected_cut_11178 : selected 8 ⟨299790, by decide⟩
    (prefixPartial 13 101886) = some ⟨13, 2, 0, 299790, 101886, 2561, 16384⟩ := by
  decide +kernel

theorem context_13_101886_299790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101886 ⟨299790, by decide⟩ :=
  accepted_of_selected 13 101886 ⟨299790, by decide⟩ ⟨13, 2, 0, 299790, 101886, 2561, 16384⟩
    (by decide) selected_cut_11178

theorem selected_cut_11179 : selected 8 ⟨299834, by decide⟩
    (prefixPartial 13 101887) = some ⟨13, 2, 0, 299834, 101887, 1477, 16384⟩ := by
  decide +kernel

theorem context_13_101887_299834 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101887 ⟨299834, by decide⟩ :=
  accepted_of_selected 13 101887 ⟨299834, by decide⟩ ⟨13, 2, 0, 299834, 101887, 1477, 16384⟩
    (by decide) selected_cut_11179

theorem unmarked_context_12_25471_299835 : frontier 9 ⟨299835, by decide⟩
    (prefixCache 12 25471) (prefixPartial 12 25471) = false := by
  decide +kernel

theorem node_context_12_25471_299835 : EJMOriginalGlobalDAGData.nodes 9 ⟨299835, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨299747, by decide⟩,⟨299790, by decide⟩,⟨299834, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25471_299835 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25471 ⟨299835, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25471
    ⟨299835, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨299747, by decide⟩,⟨299790, by decide⟩,⟨299834, by decide⟩]) unmarked_context_12_25471_299835 node_context_12_25471_299835
  intro a
  fin_cases a
  · exact context_13_101884_3444
  · exact context_13_101885_299747
  · exact context_13_101886_299790
  · exact context_13_101887_299834

theorem unmarked_context_11_6367_299836 : frontier 10 ⟨299836, by decide⟩
    (prefixCache 11 6367) (prefixPartial 11 6367) = false := by
  decide +kernel

theorem node_context_11_6367_299836 : EJMOriginalGlobalDAGData.nodes 10 ⟨299836, by decide⟩ =
    .split (coordinate 11) (![⟨299661, by decide⟩,⟨299712, by decide⟩,⟨299741, by decide⟩,⟨299835, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6367_299836 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6367 ⟨299836, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6367
    ⟨299836, by decide⟩ (by decide) (![⟨299661, by decide⟩,⟨299712, by decide⟩,⟨299741, by decide⟩,⟨299835, by decide⟩]) unmarked_context_11_6367_299836 node_context_11_6367_299836
  intro a
  fin_cases a
  · exact context_12_25468_299661
  · exact context_12_25469_299712
  · exact context_12_25470_299741
  · exact context_12_25471_299835

theorem unmarked_context_10_1591_299837 : frontier 11 ⟨299837, by decide⟩
    (prefixCache 10 1591) (prefixPartial 10 1591) = false := by
  decide +kernel

theorem node_context_10_1591_299837 : EJMOriginalGlobalDAGData.nodes 11 ⟨299837, by decide⟩ =
    .split (coordinate 10) (![⟨299314, by decide⟩,⟨299423, by decide⟩,⟨299629, by decide⟩,⟨299836, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1591_299837 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1591 ⟨299837, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1591
    ⟨299837, by decide⟩ (by decide) (![⟨299314, by decide⟩,⟨299423, by decide⟩,⟨299629, by decide⟩,⟨299836, by decide⟩]) unmarked_context_10_1591_299837 node_context_10_1591_299837
  intro a
  fin_cases a
  · exact context_11_6364_299314
  · exact context_11_6365_299423
  · exact context_11_6366_299629
  · exact context_11_6367_299836

theorem unmarked_context_9_397_299838 : frontier 12 ⟨299838, by decide⟩
    (prefixCache 9 397) (prefixPartial 9 397) = false := by
  decide +kernel

theorem node_context_9_397_299838 : EJMOriginalGlobalDAGData.nodes 12 ⟨299838, by decide⟩ =
    .split (coordinate 9) (![⟨297661, by decide⟩,⟨298412, by decide⟩,⟨299145, by decide⟩,⟨299837, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_397_299838 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 397 ⟨299838, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 397
    ⟨299838, by decide⟩ (by decide) (![⟨297661, by decide⟩,⟨298412, by decide⟩,⟨299145, by decide⟩,⟨299837, by decide⟩]) unmarked_context_9_397_299838 node_context_9_397_299838
  intro a
  fin_cases a
  · exact context_10_1588_297661
  · exact context_10_1589_298412
  · exact context_10_1590_299145
  · exact context_10_1591_299837

theorem selected_cut_11180 : selected 9 ⟨299948, by decide⟩
    (prefixPartial 12 25472) = some ⟨12, 2, 0, 299948, 25472, 1125, 65536⟩ := by
  decide +kernel

theorem context_12_25472_299948 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25472 ⟨299948, by decide⟩ :=
  accepted_of_selected 12 25472 ⟨299948, by decide⟩ ⟨12, 2, 0, 299948, 25472, 1125, 65536⟩
    (by decide) selected_cut_11180

theorem selected_cut_11181 : selected 9 ⟨299999, by decide⟩
    (prefixPartial 12 25473) = some ⟨12, 2, 0, 299999, 25473, 3309, 65536⟩ := by
  decide +kernel

theorem context_12_25473_299999 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25473 ⟨299999, by decide⟩ :=
  accepted_of_selected 12 25473 ⟨299999, by decide⟩ ⟨12, 2, 0, 299999, 25473, 3309, 65536⟩
    (by decide) selected_cut_11181

theorem selected_cut_11182 : selected 9 ⟨300045, by decide⟩
    (prefixPartial 12 25474) = some ⟨12, 2, 0, 300045, 25474, 3265, 65536⟩ := by
  decide +kernel

theorem context_12_25474_300045 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25474 ⟨300045, by decide⟩ :=
  accepted_of_selected 12 25474 ⟨300045, by decide⟩ ⟨12, 2, 0, 300045, 25474, 3265, 65536⟩
    (by decide) selected_cut_11182

theorem selected_cut_11183 : selected 9 ⟨300083, by decide⟩
    (prefixPartial 12 25475) = some ⟨12, 2, 0, 300083, 25475, 3365, 65536⟩ := by
  decide +kernel

theorem context_12_25475_300083 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25475 ⟨300083, by decide⟩ :=
  accepted_of_selected 12 25475 ⟨300083, by decide⟩ ⟨12, 2, 0, 300083, 25475, 3365, 65536⟩
    (by decide) selected_cut_11183

theorem unmarked_context_11_6368_300084 : frontier 10 ⟨300084, by decide⟩
    (prefixCache 11 6368) (prefixPartial 11 6368) = false := by
  decide +kernel

theorem node_context_11_6368_300084 : EJMOriginalGlobalDAGData.nodes 10 ⟨300084, by decide⟩ =
    .split (coordinate 11) (![⟨299948, by decide⟩,⟨299999, by decide⟩,⟨300045, by decide⟩,⟨300083, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6368_300084 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6368 ⟨300084, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6368
    ⟨300084, by decide⟩ (by decide) (![⟨299948, by decide⟩,⟨299999, by decide⟩,⟨300045, by decide⟩,⟨300083, by decide⟩]) unmarked_context_11_6368_300084 node_context_11_6368_300084
  intro a
  fin_cases a
  · exact context_12_25472_299948
  · exact context_12_25473_299999
  · exact context_12_25474_300045
  · exact context_12_25475_300083

theorem selected_cut_11184 : selected 9 ⟨300104, by decide⟩
    (prefixPartial 12 25476) = some ⟨12, 2, 0, 300104, 25476, 2365, 65536⟩ := by
  decide +kernel

theorem context_12_25476_300104 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25476 ⟨300104, by decide⟩ :=
  accepted_of_selected 12 25476 ⟨300104, by decide⟩ ⟨12, 2, 0, 300104, 25476, 2365, 65536⟩
    (by decide) selected_cut_11184

theorem selected_cut_11185 : selected 9 ⟨300131, by decide⟩
    (prefixPartial 12 25477) = some ⟨12, 2, 0, 300131, 25477, 2437, 65536⟩ := by
  decide +kernel

theorem context_12_25477_300131 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25477 ⟨300131, by decide⟩ :=
  accepted_of_selected 12 25477 ⟨300131, by decide⟩ ⟨12, 2, 0, 300131, 25477, 2437, 65536⟩
    (by decide) selected_cut_11185

theorem selected_cut_11186 : selected 9 ⟨300160, by decide⟩
    (prefixPartial 12 25478) = some ⟨12, 2, 0, 300160, 25478, 2649, 65536⟩ := by
  decide +kernel

theorem context_12_25478_300160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25478 ⟨300160, by decide⟩ :=
  accepted_of_selected 12 25478 ⟨300160, by decide⟩ ⟨12, 2, 0, 300160, 25478, 2649, 65536⟩
    (by decide) selected_cut_11186

theorem selected_cut_11187 : selected 9 ⟨300185, by decide⟩
    (prefixPartial 12 25479) = some ⟨12, 2, 0, 300185, 25479, 2753, 65536⟩ := by
  decide +kernel

theorem context_12_25479_300185 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25479 ⟨300185, by decide⟩ :=
  accepted_of_selected 12 25479 ⟨300185, by decide⟩ ⟨12, 2, 0, 300185, 25479, 2753, 65536⟩
    (by decide) selected_cut_11187

theorem unmarked_context_11_6369_300186 : frontier 10 ⟨300186, by decide⟩
    (prefixCache 11 6369) (prefixPartial 11 6369) = false := by
  decide +kernel

theorem node_context_11_6369_300186 : EJMOriginalGlobalDAGData.nodes 10 ⟨300186, by decide⟩ =
    .split (coordinate 11) (![⟨300104, by decide⟩,⟨300131, by decide⟩,⟨300160, by decide⟩,⟨300185, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6369_300186 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6369 ⟨300186, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6369
    ⟨300186, by decide⟩ (by decide) (![⟨300104, by decide⟩,⟨300131, by decide⟩,⟨300160, by decide⟩,⟨300185, by decide⟩]) unmarked_context_11_6369_300186 node_context_11_6369_300186
  intro a
  fin_cases a
  · exact context_12_25476_300104
  · exact context_12_25477_300131
  · exact context_12_25478_300160
  · exact context_12_25479_300185

theorem selected_cut_11188 : selected 9 ⟨300214, by decide⟩
    (prefixPartial 12 25480) = some ⟨12, 2, 0, 300214, 25480, 2373, 65536⟩ := by
  decide +kernel

theorem context_12_25480_300214 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25480 ⟨300214, by decide⟩ :=
  accepted_of_selected 12 25480 ⟨300214, by decide⟩ ⟨12, 2, 0, 300214, 25480, 2373, 65536⟩
    (by decide) selected_cut_11188

theorem selected_cut_11189 : selected 9 ⟨300252, by decide⟩
    (prefixPartial 12 25481) = some ⟨12, 2, 0, 300252, 25481, 2589, 65536⟩ := by
  decide +kernel

theorem context_12_25481_300252 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25481 ⟨300252, by decide⟩ :=
  accepted_of_selected 12 25481 ⟨300252, by decide⟩ ⟨12, 2, 0, 300252, 25481, 2589, 65536⟩
    (by decide) selected_cut_11189

theorem selected_cut_11190 : selected 9 ⟨300280, by decide⟩
    (prefixPartial 12 25482) = some ⟨12, 2, 0, 300280, 25482, 2501, 65536⟩ := by
  decide +kernel

theorem context_12_25482_300280 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25482 ⟨300280, by decide⟩ :=
  accepted_of_selected 12 25482 ⟨300280, by decide⟩ ⟨12, 2, 0, 300280, 25482, 2501, 65536⟩
    (by decide) selected_cut_11190

theorem selected_cut_11191 : selected 9 ⟨300303, by decide⟩
    (prefixPartial 12 25483) = some ⟨12, 2, 0, 300303, 25483, 2425, 65536⟩ := by
  decide +kernel

theorem context_12_25483_300303 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25483 ⟨300303, by decide⟩ :=
  accepted_of_selected 12 25483 ⟨300303, by decide⟩ ⟨12, 2, 0, 300303, 25483, 2425, 65536⟩
    (by decide) selected_cut_11191

theorem unmarked_context_11_6370_300304 : frontier 10 ⟨300304, by decide⟩
    (prefixCache 11 6370) (prefixPartial 11 6370) = false := by
  decide +kernel

theorem node_context_11_6370_300304 : EJMOriginalGlobalDAGData.nodes 10 ⟨300304, by decide⟩ =
    .split (coordinate 11) (![⟨300214, by decide⟩,⟨300252, by decide⟩,⟨300280, by decide⟩,⟨300303, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6370_300304 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6370 ⟨300304, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6370
    ⟨300304, by decide⟩ (by decide) (![⟨300214, by decide⟩,⟨300252, by decide⟩,⟨300280, by decide⟩,⟨300303, by decide⟩]) unmarked_context_11_6370_300304 node_context_11_6370_300304
  intro a
  fin_cases a
  · exact context_12_25480_300214
  · exact context_12_25481_300252
  · exact context_12_25482_300280
  · exact context_12_25483_300303

theorem selected_cut_11192 : selected 9 ⟨300324, by decide⟩
    (prefixPartial 12 25484) = some ⟨12, 2, 0, 300324, 25484, 1877, 65536⟩ := by
  decide +kernel

theorem context_12_25484_300324 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25484 ⟨300324, by decide⟩ :=
  accepted_of_selected 12 25484 ⟨300324, by decide⟩ ⟨12, 2, 0, 300324, 25484, 1877, 65536⟩
    (by decide) selected_cut_11192

theorem selected_cut_11193 : selected 9 ⟨300352, by decide⟩
    (prefixPartial 12 25485) = some ⟨12, 2, 0, 300352, 25485, 2089, 65536⟩ := by
  decide +kernel

theorem context_12_25485_300352 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25485 ⟨300352, by decide⟩ :=
  accepted_of_selected 12 25485 ⟨300352, by decide⟩ ⟨12, 2, 0, 300352, 25485, 2089, 65536⟩
    (by decide) selected_cut_11193

theorem selected_cut_11194 : selected 9 ⟨300376, by decide⟩
    (prefixPartial 12 25486) = some ⟨12, 2, 0, 300376, 25486, 2025, 65536⟩ := by
  decide +kernel

theorem context_12_25486_300376 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25486 ⟨300376, by decide⟩ :=
  accepted_of_selected 12 25486 ⟨300376, by decide⟩ ⟨12, 2, 0, 300376, 25486, 2025, 65536⟩
    (by decide) selected_cut_11194

theorem selected_cut_11195 : selected 9 ⟨300436, by decide⟩
    (prefixPartial 12 25487) = some ⟨12, 2, 0, 300436, 25487, 3309, 65536⟩ := by
  decide +kernel

theorem context_12_25487_300436 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25487 ⟨300436, by decide⟩ :=
  accepted_of_selected 12 25487 ⟨300436, by decide⟩ ⟨12, 2, 0, 300436, 25487, 3309, 65536⟩
    (by decide) selected_cut_11195

theorem unmarked_context_11_6371_300437 : frontier 10 ⟨300437, by decide⟩
    (prefixCache 11 6371) (prefixPartial 11 6371) = false := by
  decide +kernel

theorem node_context_11_6371_300437 : EJMOriginalGlobalDAGData.nodes 10 ⟨300437, by decide⟩ =
    .split (coordinate 11) (![⟨300324, by decide⟩,⟨300352, by decide⟩,⟨300376, by decide⟩,⟨300436, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6371_300437 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6371 ⟨300437, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6371
    ⟨300437, by decide⟩ (by decide) (![⟨300324, by decide⟩,⟨300352, by decide⟩,⟨300376, by decide⟩,⟨300436, by decide⟩]) unmarked_context_11_6371_300437 node_context_11_6371_300437
  intro a
  fin_cases a
  · exact context_12_25484_300324
  · exact context_12_25485_300352
  · exact context_12_25486_300376
  · exact context_12_25487_300436

theorem unmarked_context_10_1592_300438 : frontier 11 ⟨300438, by decide⟩
    (prefixCache 10 1592) (prefixPartial 10 1592) = false := by
  decide +kernel

theorem node_context_10_1592_300438 : EJMOriginalGlobalDAGData.nodes 11 ⟨300438, by decide⟩ =
    .split (coordinate 10) (![⟨300084, by decide⟩,⟨300186, by decide⟩,⟨300304, by decide⟩,⟨300437, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1592_300438 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1592 ⟨300438, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1592
    ⟨300438, by decide⟩ (by decide) (![⟨300084, by decide⟩,⟨300186, by decide⟩,⟨300304, by decide⟩,⟨300437, by decide⟩]) unmarked_context_10_1592_300438 node_context_10_1592_300438
  intro a
  fin_cases a
  · exact context_11_6368_300084
  · exact context_11_6369_300186
  · exact context_11_6370_300304
  · exact context_11_6371_300437

theorem selected_cut_11196 : selected 9 ⟨300456, by decide⟩
    (prefixPartial 12 25488) = some ⟨12, 2, 0, 300456, 25488, 1753, 65536⟩ := by
  decide +kernel

theorem context_12_25488_300456 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25488 ⟨300456, by decide⟩ :=
  accepted_of_selected 12 25488 ⟨300456, by decide⟩ ⟨12, 2, 0, 300456, 25488, 1753, 65536⟩
    (by decide) selected_cut_11196

theorem selected_cut_11197 : selected 9 ⟨300481, by decide⟩
    (prefixPartial 12 25489) = some ⟨12, 2, 0, 300481, 25489, 1953, 65536⟩ := by
  decide +kernel

theorem context_12_25489_300481 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25489 ⟨300481, by decide⟩ :=
  accepted_of_selected 12 25489 ⟨300481, by decide⟩ ⟨12, 2, 0, 300481, 25489, 1953, 65536⟩
    (by decide) selected_cut_11197

theorem selected_cut_11198 : selected 9 ⟨300505, by decide⟩
    (prefixPartial 12 25490) = some ⟨12, 2, 0, 300505, 25490, 1937, 65536⟩ := by
  decide +kernel

theorem context_12_25490_300505 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25490 ⟨300505, by decide⟩ :=
  accepted_of_selected 12 25490 ⟨300505, by decide⟩ ⟨12, 2, 0, 300505, 25490, 1937, 65536⟩
    (by decide) selected_cut_11198

theorem selected_cut_11199 : selected 9 ⟨300531, by decide⟩
    (prefixPartial 12 25491) = some ⟨12, 2, 0, 300531, 25491, 1957, 65536⟩ := by
  decide +kernel

theorem context_12_25491_300531 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25491 ⟨300531, by decide⟩ :=
  accepted_of_selected 12 25491 ⟨300531, by decide⟩ ⟨12, 2, 0, 300531, 25491, 1957, 65536⟩
    (by decide) selected_cut_11199

theorem unmarked_context_11_6372_300532 : frontier 10 ⟨300532, by decide⟩
    (prefixCache 11 6372) (prefixPartial 11 6372) = false := by
  decide +kernel

theorem node_context_11_6372_300532 : EJMOriginalGlobalDAGData.nodes 10 ⟨300532, by decide⟩ =
    .split (coordinate 11) (![⟨300456, by decide⟩,⟨300481, by decide⟩,⟨300505, by decide⟩,⟨300531, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6372_300532 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6372 ⟨300532, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6372
    ⟨300532, by decide⟩ (by decide) (![⟨300456, by decide⟩,⟨300481, by decide⟩,⟨300505, by decide⟩,⟨300531, by decide⟩]) unmarked_context_11_6372_300532 node_context_11_6372_300532
  intro a
  fin_cases a
  · exact context_12_25488_300456
  · exact context_12_25489_300481
  · exact context_12_25490_300505
  · exact context_12_25491_300531

theorem selected_cut_11200 : selected 9 ⟨300550, by decide⟩
    (prefixPartial 12 25492) = some ⟨12, 2, 0, 300550, 25492, 1857, 65536⟩ := by
  decide +kernel

theorem context_12_25492_300550 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25492 ⟨300550, by decide⟩ :=
  accepted_of_selected 12 25492 ⟨300550, by decide⟩ ⟨12, 2, 0, 300550, 25492, 1857, 65536⟩
    (by decide) selected_cut_11200

theorem selected_cut_11201 : selected 9 ⟨300571, by decide⟩
    (prefixPartial 12 25493) = some ⟨12, 2, 0, 300571, 25493, 2089, 65536⟩ := by
  decide +kernel

theorem context_12_25493_300571 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25493 ⟨300571, by decide⟩ :=
  accepted_of_selected 12 25493 ⟨300571, by decide⟩ ⟨12, 2, 0, 300571, 25493, 2089, 65536⟩
    (by decide) selected_cut_11201

theorem selected_cut_11202 : selected 9 ⟨300595, by decide⟩
    (prefixPartial 12 25494) = some ⟨12, 2, 0, 300595, 25494, 2205, 65536⟩ := by
  decide +kernel

theorem context_12_25494_300595 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25494 ⟨300595, by decide⟩ :=
  accepted_of_selected 12 25494 ⟨300595, by decide⟩ ⟨12, 2, 0, 300595, 25494, 2205, 65536⟩
    (by decide) selected_cut_11202

theorem selected_cut_11203 : selected 9 ⟨300617, by decide⟩
    (prefixPartial 12 25495) = some ⟨12, 2, 0, 300617, 25495, 2285, 65536⟩ := by
  decide +kernel

theorem context_12_25495_300617 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25495 ⟨300617, by decide⟩ :=
  accepted_of_selected 12 25495 ⟨300617, by decide⟩ ⟨12, 2, 0, 300617, 25495, 2285, 65536⟩
    (by decide) selected_cut_11203

theorem unmarked_context_11_6373_300618 : frontier 10 ⟨300618, by decide⟩
    (prefixCache 11 6373) (prefixPartial 11 6373) = false := by
  decide +kernel

theorem node_context_11_6373_300618 : EJMOriginalGlobalDAGData.nodes 10 ⟨300618, by decide⟩ =
    .split (coordinate 11) (![⟨300550, by decide⟩,⟨300571, by decide⟩,⟨300595, by decide⟩,⟨300617, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6373_300618 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6373 ⟨300618, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6373
    ⟨300618, by decide⟩ (by decide) (![⟨300550, by decide⟩,⟨300571, by decide⟩,⟨300595, by decide⟩,⟨300617, by decide⟩]) unmarked_context_11_6373_300618 node_context_11_6373_300618
  intro a
  fin_cases a
  · exact context_12_25492_300550
  · exact context_12_25493_300571
  · exact context_12_25494_300595
  · exact context_12_25495_300617

theorem selected_cut_11204 : selected 9 ⟨300640, by decide⟩
    (prefixPartial 12 25496) = some ⟨12, 2, 0, 300640, 25496, 1805, 65536⟩ := by
  decide +kernel

theorem context_12_25496_300640 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25496 ⟨300640, by decide⟩ :=
  accepted_of_selected 12 25496 ⟨300640, by decide⟩ ⟨12, 2, 0, 300640, 25496, 1805, 65536⟩
    (by decide) selected_cut_11204

theorem selected_cut_11205 : selected 9 ⟨300668, by decide⟩
    (prefixPartial 12 25497) = some ⟨12, 2, 0, 300668, 25497, 2141, 65536⟩ := by
  decide +kernel

theorem context_12_25497_300668 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25497 ⟨300668, by decide⟩ :=
  accepted_of_selected 12 25497 ⟨300668, by decide⟩ ⟨12, 2, 0, 300668, 25497, 2141, 65536⟩
    (by decide) selected_cut_11205

theorem selected_cut_11206 : selected 9 ⟨300703, by decide⟩
    (prefixPartial 12 25498) = some ⟨12, 2, 0, 300703, 25498, 1941, 65536⟩ := by
  decide +kernel

theorem context_12_25498_300703 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25498 ⟨300703, by decide⟩ :=
  accepted_of_selected 12 25498 ⟨300703, by decide⟩ ⟨12, 2, 0, 300703, 25498, 1941, 65536⟩
    (by decide) selected_cut_11206

theorem selected_cut_11207 : selected 9 ⟨300732, by decide⟩
    (prefixPartial 12 25499) = some ⟨12, 2, 0, 300732, 25499, 1877, 65536⟩ := by
  decide +kernel

theorem context_12_25499_300732 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25499 ⟨300732, by decide⟩ :=
  accepted_of_selected 12 25499 ⟨300732, by decide⟩ ⟨12, 2, 0, 300732, 25499, 1877, 65536⟩
    (by decide) selected_cut_11207

theorem unmarked_context_11_6374_300733 : frontier 10 ⟨300733, by decide⟩
    (prefixCache 11 6374) (prefixPartial 11 6374) = false := by
  decide +kernel

theorem node_context_11_6374_300733 : EJMOriginalGlobalDAGData.nodes 10 ⟨300733, by decide⟩ =
    .split (coordinate 11) (![⟨300640, by decide⟩,⟨300668, by decide⟩,⟨300703, by decide⟩,⟨300732, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6374_300733 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6374 ⟨300733, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6374
    ⟨300733, by decide⟩ (by decide) (![⟨300640, by decide⟩,⟨300668, by decide⟩,⟨300703, by decide⟩,⟨300732, by decide⟩]) unmarked_context_11_6374_300733 node_context_11_6374_300733
  intro a
  fin_cases a
  · exact context_12_25496_300640
  · exact context_12_25497_300668
  · exact context_12_25498_300703
  · exact context_12_25499_300732

theorem selected_cut_11208 : selected 9 ⟨300750, by decide⟩
    (prefixPartial 12 25500) = some ⟨12, 2, 0, 300750, 25500, 1425, 65536⟩ := by
  decide +kernel

theorem context_12_25500_300750 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25500 ⟨300750, by decide⟩ :=
  accepted_of_selected 12 25500 ⟨300750, by decide⟩ ⟨12, 2, 0, 300750, 25500, 1425, 65536⟩
    (by decide) selected_cut_11208

theorem selected_cut_11209 : selected 9 ⟨300772, by decide⟩
    (prefixPartial 12 25501) = some ⟨12, 2, 0, 300772, 25501, 1641, 65536⟩ := by
  decide +kernel

theorem context_12_25501_300772 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25501 ⟨300772, by decide⟩ :=
  accepted_of_selected 12 25501 ⟨300772, by decide⟩ ⟨12, 2, 0, 300772, 25501, 1641, 65536⟩
    (by decide) selected_cut_11209

theorem selected_cut_11210 : selected 9 ⟨300789, by decide⟩
    (prefixPartial 12 25502) = some ⟨12, 2, 0, 300789, 25502, 1529, 65536⟩ := by
  decide +kernel

theorem context_12_25502_300789 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25502 ⟨300789, by decide⟩ :=
  accepted_of_selected 12 25502 ⟨300789, by decide⟩ ⟨12, 2, 0, 300789, 25502, 1529, 65536⟩
    (by decide) selected_cut_11210

theorem selected_cut_11211 : selected 9 ⟨300824, by decide⟩
    (prefixPartial 12 25503) = some ⟨12, 2, 0, 300824, 25503, 2541, 65536⟩ := by
  decide +kernel

theorem context_12_25503_300824 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25503 ⟨300824, by decide⟩ :=
  accepted_of_selected 12 25503 ⟨300824, by decide⟩ ⟨12, 2, 0, 300824, 25503, 2541, 65536⟩
    (by decide) selected_cut_11211

theorem unmarked_context_11_6375_300825 : frontier 10 ⟨300825, by decide⟩
    (prefixCache 11 6375) (prefixPartial 11 6375) = false := by
  decide +kernel

theorem node_context_11_6375_300825 : EJMOriginalGlobalDAGData.nodes 10 ⟨300825, by decide⟩ =
    .split (coordinate 11) (![⟨300750, by decide⟩,⟨300772, by decide⟩,⟨300789, by decide⟩,⟨300824, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6375_300825 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6375 ⟨300825, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6375
    ⟨300825, by decide⟩ (by decide) (![⟨300750, by decide⟩,⟨300772, by decide⟩,⟨300789, by decide⟩,⟨300824, by decide⟩]) unmarked_context_11_6375_300825 node_context_11_6375_300825
  intro a
  fin_cases a
  · exact context_12_25500_300750
  · exact context_12_25501_300772
  · exact context_12_25502_300789
  · exact context_12_25503_300824

theorem unmarked_context_10_1593_300826 : frontier 11 ⟨300826, by decide⟩
    (prefixCache 10 1593) (prefixPartial 10 1593) = false := by
  decide +kernel

theorem node_context_10_1593_300826 : EJMOriginalGlobalDAGData.nodes 11 ⟨300826, by decide⟩ =
    .split (coordinate 10) (![⟨300532, by decide⟩,⟨300618, by decide⟩,⟨300733, by decide⟩,⟨300825, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1593_300826 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1593 ⟨300826, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1593
    ⟨300826, by decide⟩ (by decide) (![⟨300532, by decide⟩,⟨300618, by decide⟩,⟨300733, by decide⟩,⟨300825, by decide⟩]) unmarked_context_10_1593_300826 node_context_10_1593_300826
  intro a
  fin_cases a
  · exact context_11_6372_300532
  · exact context_11_6373_300618
  · exact context_11_6374_300733
  · exact context_11_6375_300825

theorem selected_cut_11212 : selected 9 ⟨300835, by decide⟩
    (prefixPartial 12 25504) = some ⟨12, 2, 0, 300835, 25504, 1213, 65536⟩ := by
  decide +kernel

theorem context_12_25504_300835 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25504 ⟨300835, by decide⟩ :=
  accepted_of_selected 12 25504 ⟨300835, by decide⟩ ⟨12, 2, 0, 300835, 25504, 1213, 65536⟩
    (by decide) selected_cut_11212

theorem selected_cut_11213 : selected 9 ⟨300850, by decide⟩
    (prefixPartial 12 25505) = some ⟨12, 2, 0, 300850, 25505, 1301, 65536⟩ := by
  decide +kernel

theorem context_12_25505_300850 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25505 ⟨300850, by decide⟩ :=
  accepted_of_selected 12 25505 ⟨300850, by decide⟩ ⟨12, 2, 0, 300850, 25505, 1301, 65536⟩
    (by decide) selected_cut_11213

theorem selected_cut_11214 : selected 9 ⟨300861, by decide⟩
    (prefixPartial 12 25506) = some ⟨12, 2, 0, 300861, 25506, 1233, 65536⟩ := by
  decide +kernel

theorem context_12_25506_300861 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25506 ⟨300861, by decide⟩ :=
  accepted_of_selected 12 25506 ⟨300861, by decide⟩ ⟨12, 2, 0, 300861, 25506, 1233, 65536⟩
    (by decide) selected_cut_11214

theorem selected_cut_11215 : selected 9 ⟨300873, by decide⟩
    (prefixPartial 12 25507) = some ⟨12, 2, 0, 300873, 25507, 1217, 65536⟩ := by
  decide +kernel

theorem context_12_25507_300873 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25507 ⟨300873, by decide⟩ :=
  accepted_of_selected 12 25507 ⟨300873, by decide⟩ ⟨12, 2, 0, 300873, 25507, 1217, 65536⟩
    (by decide) selected_cut_11215

theorem unmarked_context_11_6376_300874 : frontier 10 ⟨300874, by decide⟩
    (prefixCache 11 6376) (prefixPartial 11 6376) = false := by
  decide +kernel

theorem node_context_11_6376_300874 : EJMOriginalGlobalDAGData.nodes 10 ⟨300874, by decide⟩ =
    .split (coordinate 11) (![⟨300835, by decide⟩,⟨300850, by decide⟩,⟨300861, by decide⟩,⟨300873, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6376_300874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6376 ⟨300874, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6376
    ⟨300874, by decide⟩ (by decide) (![⟨300835, by decide⟩,⟨300850, by decide⟩,⟨300861, by decide⟩,⟨300873, by decide⟩]) unmarked_context_11_6376_300874 node_context_11_6376_300874
  intro a
  fin_cases a
  · exact context_12_25504_300835
  · exact context_12_25505_300850
  · exact context_12_25506_300861
  · exact context_12_25507_300873

theorem selected_cut_11216 : selected 9 ⟨300885, by decide⟩
    (prefixPartial 12 25508) = some ⟨12, 2, 0, 300885, 25508, 1325, 65536⟩ := by
  decide +kernel

theorem context_12_25508_300885 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25508 ⟨300885, by decide⟩ :=
  accepted_of_selected 12 25508 ⟨300885, by decide⟩ ⟨12, 2, 0, 300885, 25508, 1325, 65536⟩
    (by decide) selected_cut_11216

theorem selected_cut_11217 : selected 9 ⟨300903, by decide⟩
    (prefixPartial 12 25509) = some ⟨12, 2, 0, 300903, 25509, 1389, 65536⟩ := by
  decide +kernel

theorem context_12_25509_300903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25509 ⟨300903, by decide⟩ :=
  accepted_of_selected 12 25509 ⟨300903, by decide⟩ ⟨12, 2, 0, 300903, 25509, 1389, 65536⟩
    (by decide) selected_cut_11217

theorem selected_cut_11218 : selected 9 ⟨300920, by decide⟩
    (prefixPartial 12 25510) = some ⟨12, 2, 0, 300920, 25510, 1469, 65536⟩ := by
  decide +kernel

theorem context_12_25510_300920 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25510 ⟨300920, by decide⟩ :=
  accepted_of_selected 12 25510 ⟨300920, by decide⟩ ⟨12, 2, 0, 300920, 25510, 1469, 65536⟩
    (by decide) selected_cut_11218

theorem selected_cut_11219 : selected 9 ⟨300936, by decide⟩
    (prefixPartial 12 25511) = some ⟨12, 2, 0, 300936, 25511, 1441, 65536⟩ := by
  decide +kernel

theorem context_12_25511_300936 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25511 ⟨300936, by decide⟩ :=
  accepted_of_selected 12 25511 ⟨300936, by decide⟩ ⟨12, 2, 0, 300936, 25511, 1441, 65536⟩
    (by decide) selected_cut_11219

theorem unmarked_context_11_6377_300937 : frontier 10 ⟨300937, by decide⟩
    (prefixCache 11 6377) (prefixPartial 11 6377) = false := by
  decide +kernel

theorem node_context_11_6377_300937 : EJMOriginalGlobalDAGData.nodes 10 ⟨300937, by decide⟩ =
    .split (coordinate 11) (![⟨300885, by decide⟩,⟨300903, by decide⟩,⟨300920, by decide⟩,⟨300936, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6377_300937 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6377 ⟨300937, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6377
    ⟨300937, by decide⟩ (by decide) (![⟨300885, by decide⟩,⟨300903, by decide⟩,⟨300920, by decide⟩,⟨300936, by decide⟩]) unmarked_context_11_6377_300937 node_context_11_6377_300937
  intro a
  fin_cases a
  · exact context_12_25508_300885
  · exact context_12_25509_300903
  · exact context_12_25510_300920
  · exact context_12_25511_300936

theorem selected_cut_11220 : selected 9 ⟨300950, by decide⟩
    (prefixPartial 12 25512) = some ⟨12, 2, 0, 300950, 25512, 1261, 65536⟩ := by
  decide +kernel

theorem context_12_25512_300950 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25512 ⟨300950, by decide⟩ :=
  accepted_of_selected 12 25512 ⟨300950, by decide⟩ ⟨12, 2, 0, 300950, 25512, 1261, 65536⟩
    (by decide) selected_cut_11220

theorem selected_cut_11221 : selected 9 ⟨300968, by decide⟩
    (prefixPartial 12 25513) = some ⟨12, 2, 0, 300968, 25513, 1365, 65536⟩ := by
  decide +kernel

theorem context_12_25513_300968 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25513 ⟨300968, by decide⟩ :=
  accepted_of_selected 12 25513 ⟨300968, by decide⟩ ⟨12, 2, 0, 300968, 25513, 1365, 65536⟩
    (by decide) selected_cut_11221

theorem selected_cut_11222 : selected 9 ⟨300982, by decide⟩
    (prefixPartial 12 25514) = some ⟨12, 2, 0, 300982, 25514, 1225, 65536⟩ := by
  decide +kernel

theorem context_12_25514_300982 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25514 ⟨300982, by decide⟩ :=
  accepted_of_selected 12 25514 ⟨300982, by decide⟩ ⟨12, 2, 0, 300982, 25514, 1225, 65536⟩
    (by decide) selected_cut_11222

theorem selected_cut_11223 : selected 9 ⟨300994, by decide⟩
    (prefixPartial 12 25515) = some ⟨12, 2, 0, 300994, 25515, 1121, 65536⟩ := by
  decide +kernel

theorem context_12_25515_300994 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25515 ⟨300994, by decide⟩ :=
  accepted_of_selected 12 25515 ⟨300994, by decide⟩ ⟨12, 2, 0, 300994, 25515, 1121, 65536⟩
    (by decide) selected_cut_11223

theorem unmarked_context_11_6378_300995 : frontier 10 ⟨300995, by decide⟩
    (prefixCache 11 6378) (prefixPartial 11 6378) = false := by
  decide +kernel

theorem node_context_11_6378_300995 : EJMOriginalGlobalDAGData.nodes 10 ⟨300995, by decide⟩ =
    .split (coordinate 11) (![⟨300950, by decide⟩,⟨300968, by decide⟩,⟨300982, by decide⟩,⟨300994, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6378_300995 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6378 ⟨300995, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6378
    ⟨300995, by decide⟩ (by decide) (![⟨300950, by decide⟩,⟨300968, by decide⟩,⟨300982, by decide⟩,⟨300994, by decide⟩]) unmarked_context_11_6378_300995 node_context_11_6378_300995
  intro a
  fin_cases a
  · exact context_12_25512_300950
  · exact context_12_25513_300968
  · exact context_12_25514_300982
  · exact context_12_25515_300994

theorem selected_cut_11224 : selected 9 ⟨301007, by decide⟩
    (prefixPartial 12 25516) = some ⟨12, 2, 0, 301007, 25516, 1149, 65536⟩ := by
  decide +kernel

theorem context_12_25516_301007 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25516 ⟨301007, by decide⟩ :=
  accepted_of_selected 12 25516 ⟨301007, by decide⟩ ⟨12, 2, 0, 301007, 25516, 1149, 65536⟩
    (by decide) selected_cut_11224

theorem selected_cut_11225 : selected 9 ⟨301022, by decide⟩
    (prefixPartial 12 25517) = some ⟨12, 2, 0, 301022, 25517, 1273, 65536⟩ := by
  decide +kernel

theorem context_12_25517_301022 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25517 ⟨301022, by decide⟩ :=
  accepted_of_selected 12 25517 ⟨301022, by decide⟩ ⟨12, 2, 0, 301022, 25517, 1273, 65536⟩
    (by decide) selected_cut_11225

theorem selected_cut_11226 : selected 9 ⟨301033, by decide⟩
    (prefixPartial 12 25518) = some ⟨12, 2, 0, 301033, 25518, 1193, 65536⟩ := by
  decide +kernel

theorem context_12_25518_301033 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25518 ⟨301033, by decide⟩ :=
  accepted_of_selected 12 25518 ⟨301033, by decide⟩ ⟨12, 2, 0, 301033, 25518, 1193, 65536⟩
    (by decide) selected_cut_11226

theorem selected_cut_11227 : selected 9 ⟨301071, by decide⟩
    (prefixPartial 12 25519) = some ⟨12, 2, 0, 301071, 25519, 1917, 65536⟩ := by
  decide +kernel

theorem context_12_25519_301071 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25519 ⟨301071, by decide⟩ :=
  accepted_of_selected 12 25519 ⟨301071, by decide⟩ ⟨12, 2, 0, 301071, 25519, 1917, 65536⟩
    (by decide) selected_cut_11227

theorem unmarked_context_11_6379_301072 : frontier 10 ⟨301072, by decide⟩
    (prefixCache 11 6379) (prefixPartial 11 6379) = false := by
  decide +kernel

theorem node_context_11_6379_301072 : EJMOriginalGlobalDAGData.nodes 10 ⟨301072, by decide⟩ =
    .split (coordinate 11) (![⟨301007, by decide⟩,⟨301022, by decide⟩,⟨301033, by decide⟩,⟨301071, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6379_301072 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6379 ⟨301072, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6379
    ⟨301072, by decide⟩ (by decide) (![⟨301007, by decide⟩,⟨301022, by decide⟩,⟨301033, by decide⟩,⟨301071, by decide⟩]) unmarked_context_11_6379_301072 node_context_11_6379_301072
  intro a
  fin_cases a
  · exact context_12_25516_301007
  · exact context_12_25517_301022
  · exact context_12_25518_301033
  · exact context_12_25519_301071

theorem unmarked_context_10_1594_301073 : frontier 11 ⟨301073, by decide⟩
    (prefixCache 10 1594) (prefixPartial 10 1594) = false := by
  decide +kernel

theorem node_context_10_1594_301073 : EJMOriginalGlobalDAGData.nodes 11 ⟨301073, by decide⟩ =
    .split (coordinate 10) (![⟨300874, by decide⟩,⟨300937, by decide⟩,⟨300995, by decide⟩,⟨301072, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1594_301073 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1594 ⟨301073, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1594
    ⟨301073, by decide⟩ (by decide) (![⟨300874, by decide⟩,⟨300937, by decide⟩,⟨300995, by decide⟩,⟨301072, by decide⟩]) unmarked_context_10_1594_301073 node_context_10_1594_301073
  intro a
  fin_cases a
  · exact context_11_6376_300874
  · exact context_11_6377_300937
  · exact context_11_6378_300995
  · exact context_11_6379_301072

theorem selected_cut_11228 : selected 9 ⟨301089, by decide⟩
    (prefixPartial 12 25520) = some ⟨12, 2, 0, 301089, 25520, 1185, 65536⟩ := by
  decide +kernel

theorem context_12_25520_301089 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25520 ⟨301089, by decide⟩ :=
  accepted_of_selected 12 25520 ⟨301089, by decide⟩ ⟨12, 2, 0, 301089, 25520, 1185, 65536⟩
    (by decide) selected_cut_11228

theorem selected_cut_11229 : selected 9 ⟨301105, by decide⟩
    (prefixPartial 12 25521) = some ⟨12, 2, 0, 301105, 25521, 1161, 65536⟩ := by
  decide +kernel

theorem context_12_25521_301105 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25521 ⟨301105, by decide⟩ :=
  accepted_of_selected 12 25521 ⟨301105, by decide⟩ ⟨12, 2, 0, 301105, 25521, 1161, 65536⟩
    (by decide) selected_cut_11229

theorem selected_cut_11230 : selected 9 ⟨301120, by decide⟩
    (prefixPartial 12 25522) = some ⟨12, 2, 0, 301120, 25522, 1109, 65536⟩ := by
  decide +kernel

theorem context_12_25522_301120 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25522 ⟨301120, by decide⟩ :=
  accepted_of_selected 12 25522 ⟨301120, by decide⟩ ⟨12, 2, 0, 301120, 25522, 1109, 65536⟩
    (by decide) selected_cut_11230

theorem selected_cut_11231 : selected 9 ⟨301137, by decide⟩
    (prefixPartial 12 25523) = some ⟨12, 2, 0, 301137, 25523, 1145, 65536⟩ := by
  decide +kernel

theorem context_12_25523_301137 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25523 ⟨301137, by decide⟩ :=
  accepted_of_selected 12 25523 ⟨301137, by decide⟩ ⟨12, 2, 0, 301137, 25523, 1145, 65536⟩
    (by decide) selected_cut_11231

theorem unmarked_context_11_6380_301138 : frontier 10 ⟨301138, by decide⟩
    (prefixCache 11 6380) (prefixPartial 11 6380) = false := by
  decide +kernel

theorem node_context_11_6380_301138 : EJMOriginalGlobalDAGData.nodes 10 ⟨301138, by decide⟩ =
    .split (coordinate 11) (![⟨301089, by decide⟩,⟨301105, by decide⟩,⟨301120, by decide⟩,⟨301137, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6380_301138 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6380 ⟨301138, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6380
    ⟨301138, by decide⟩ (by decide) (![⟨301089, by decide⟩,⟨301105, by decide⟩,⟨301120, by decide⟩,⟨301137, by decide⟩]) unmarked_context_11_6380_301138 node_context_11_6380_301138
  intro a
  fin_cases a
  · exact context_12_25520_301089
  · exact context_12_25521_301105
  · exact context_12_25522_301120
  · exact context_12_25523_301137

theorem selected_cut_11232 : selected 9 ⟨301155, by decide⟩
    (prefixPartial 12 25524) = some ⟨12, 2, 0, 301155, 25524, 1337, 65536⟩ := by
  decide +kernel

theorem context_12_25524_301155 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25524 ⟨301155, by decide⟩ :=
  accepted_of_selected 12 25524 ⟨301155, by decide⟩ ⟨12, 2, 0, 301155, 25524, 1337, 65536⟩
    (by decide) selected_cut_11232

theorem selected_cut_11233 : selected 9 ⟨301173, by decide⟩
    (prefixPartial 12 25525) = some ⟨12, 2, 0, 301173, 25525, 1301, 65536⟩ := by
  decide +kernel

theorem context_12_25525_301173 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25525 ⟨301173, by decide⟩ :=
  accepted_of_selected 12 25525 ⟨301173, by decide⟩ ⟨12, 2, 0, 301173, 25525, 1301, 65536⟩
    (by decide) selected_cut_11233

theorem selected_cut_11234 : selected 9 ⟨301184, by decide⟩
    (prefixPartial 12 25526) = some ⟨12, 2, 0, 301184, 25526, 1377, 65536⟩ := by
  decide +kernel

theorem context_12_25526_301184 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25526 ⟨301184, by decide⟩ :=
  accepted_of_selected 12 25526 ⟨301184, by decide⟩ ⟨12, 2, 0, 301184, 25526, 1377, 65536⟩
    (by decide) selected_cut_11234

theorem selected_cut_11235 : selected 9 ⟨301193, by decide⟩
    (prefixPartial 12 25527) = some ⟨12, 2, 0, 301193, 25527, 1389, 65536⟩ := by
  decide +kernel

theorem context_12_25527_301193 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25527 ⟨301193, by decide⟩ :=
  accepted_of_selected 12 25527 ⟨301193, by decide⟩ ⟨12, 2, 0, 301193, 25527, 1389, 65536⟩
    (by decide) selected_cut_11235

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
