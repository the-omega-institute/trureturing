/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover485
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_46660 : selected 9 ⟨1301895, by decide⟩
    (prefixPartial 12 371239) = some ⟨12, 2, 0, 1301895, 371239, 2673, 65536⟩ := by
  decide +kernel

theorem context_12_371239_1301895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371239 ⟨1301895, by decide⟩ :=
  accepted_of_selected 12 371239 ⟨1301895, by decide⟩ ⟨12, 2, 0, 1301895, 371239, 2673, 65536⟩
    (by decide) selected_cut_46660

theorem unmarked_context_11_92809_1301896 : frontier 10 ⟨1301896, by decide⟩
    (prefixCache 11 92809) (prefixPartial 11 92809) = false := by
  decide +kernel

theorem node_context_11_92809_1301896 : EJMOriginalGlobalDAGData.nodes 10 ⟨1301896, by decide⟩ =
    .split (coordinate 11) (![⟨450498, by decide⟩,⟨688903, by decide⟩,⟨1301830, by decide⟩,⟨1301895, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92809_1301896 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92809 ⟨1301896, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92809
    ⟨1301896, by decide⟩ (by decide) (![⟨450498, by decide⟩,⟨688903, by decide⟩,⟨1301830, by decide⟩,⟨1301895, by decide⟩]) unmarked_context_11_92809_1301896 node_context_11_92809_1301896
  intro a
  fin_cases a
  · exact context_12_371236_450498
  · exact context_12_371237_688903
  · exact context_12_371238_1301830
  · exact context_12_371239_1301895

theorem selected_cut_46661 : selected 10 ⟨900587, by decide⟩
    (prefixPartial 11 92810) = some ⟨11, 1, 0, 900587, 92810, 1, 262144⟩ := by
  decide +kernel

theorem context_11_92810_900587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92810 ⟨900587, by decide⟩ :=
  accepted_of_selected 11 92810 ⟨900587, by decide⟩ ⟨11, 1, 0, 900587, 92810, 1, 262144⟩
    (by decide) selected_cut_46661

theorem selected_cut_46662 : selected 9 ⟨1301938, by decide⟩
    (prefixPartial 12 371244) = some ⟨12, 2, 0, 1301938, 371244, 2149, 65536⟩ := by
  decide +kernel

theorem context_12_371244_1301938 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371244 ⟨1301938, by decide⟩ :=
  accepted_of_selected 12 371244 ⟨1301938, by decide⟩ ⟨12, 2, 0, 1301938, 371244, 2149, 65536⟩
    (by decide) selected_cut_46662

theorem selected_cut_46663 : selected 9 ⟨1301981, by decide⟩
    (prefixPartial 12 371245) = some ⟨12, 2, 0, 1301981, 371245, 2061, 65536⟩ := by
  decide +kernel

theorem context_12_371245_1301981 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371245 ⟨1301981, by decide⟩ :=
  accepted_of_selected 12 371245 ⟨1301981, by decide⟩ ⟨12, 2, 0, 1301981, 371245, 2061, 65536⟩
    (by decide) selected_cut_46663

theorem selected_cut_46664 : selected 9 ⟨1302005, by decide⟩
    (prefixPartial 12 371246) = some ⟨12, 2, 0, 1302005, 371246, 1689, 65536⟩ := by
  decide +kernel

theorem context_12_371246_1302005 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371246 ⟨1302005, by decide⟩ :=
  accepted_of_selected 12 371246 ⟨1302005, by decide⟩ ⟨12, 2, 0, 1302005, 371246, 1689, 65536⟩
    (by decide) selected_cut_46664

theorem selected_cut_46665 : selected 9 ⟨758968, by decide⟩
    (prefixPartial 12 371247) = some ⟨12, 1, 0, 758968, 371247, 1, 65536⟩ := by
  decide +kernel

theorem context_12_371247_758968 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371247 ⟨758968, by decide⟩ :=
  accepted_of_selected 12 371247 ⟨758968, by decide⟩ ⟨12, 1, 0, 758968, 371247, 1, 65536⟩
    (by decide) selected_cut_46665

theorem unmarked_context_11_92811_1302006 : frontier 10 ⟨1302006, by decide⟩
    (prefixCache 11 92811) (prefixPartial 11 92811) = false := by
  decide +kernel

theorem node_context_11_92811_1302006 : EJMOriginalGlobalDAGData.nodes 10 ⟨1302006, by decide⟩ =
    .split (coordinate 11) (![⟨1301938, by decide⟩,⟨1301981, by decide⟩,⟨1302005, by decide⟩,⟨758968, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92811_1302006 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92811 ⟨1302006, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92811
    ⟨1302006, by decide⟩ (by decide) (![⟨1301938, by decide⟩,⟨1301981, by decide⟩,⟨1302005, by decide⟩,⟨758968, by decide⟩]) unmarked_context_11_92811_1302006 node_context_11_92811_1302006
  intro a
  fin_cases a
  · exact context_12_371244_1301938
  · exact context_12_371245_1301981
  · exact context_12_371246_1302005
  · exact context_12_371247_758968

theorem unmarked_context_10_23202_1302007 : frontier 11 ⟨1302007, by decide⟩
    (prefixCache 10 23202) (prefixPartial 10 23202) = false := by
  decide +kernel

theorem node_context_10_23202_1302007 : EJMOriginalGlobalDAGData.nodes 11 ⟨1302007, by decide⟩ =
    .split (coordinate 10) (![⟨1301795, by decide⟩,⟨1301896, by decide⟩,⟨900587, by decide⟩,⟨1302006, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23202_1302007 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23202 ⟨1302007, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23202
    ⟨1302007, by decide⟩ (by decide) (![⟨1301795, by decide⟩,⟨1301896, by decide⟩,⟨900587, by decide⟩,⟨1302006, by decide⟩]) unmarked_context_10_23202_1302007 node_context_10_23202_1302007
  intro a
  fin_cases a
  · exact context_11_92808_1301795
  · exact context_11_92809_1301896
  · exact context_11_92810_900587
  · exact context_11_92811_1302006

theorem selected_cut_46666 : selected 9 ⟨1255011, by decide⟩
    (prefixPartial 12 371248) = some ⟨12, 1, 0, 1255011, 371248, 1, 65536⟩ := by
  decide +kernel

theorem context_12_371248_1255011 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371248 ⟨1255011, by decide⟩ :=
  accepted_of_selected 12 371248 ⟨1255011, by decide⟩ ⟨12, 1, 0, 1255011, 371248, 1, 65536⟩
    (by decide) selected_cut_46666

theorem selected_cut_46667 : selected 9 ⟨1302048, by decide⟩
    (prefixPartial 12 371249) = some ⟨12, 2, 0, 1302048, 371249, 2185, 65536⟩ := by
  decide +kernel

theorem context_12_371249_1302048 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371249 ⟨1302048, by decide⟩ :=
  accepted_of_selected 12 371249 ⟨1302048, by decide⟩ ⟨12, 2, 0, 1302048, 371249, 2185, 65536⟩
    (by decide) selected_cut_46667

theorem selected_cut_46668 : selected 9 ⟨1302082, by decide⟩
    (prefixPartial 12 371250) = some ⟨12, 2, 0, 1302082, 371250, 2013, 65536⟩ := by
  decide +kernel

theorem context_12_371250_1302082 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371250 ⟨1302082, by decide⟩ :=
  accepted_of_selected 12 371250 ⟨1302082, by decide⟩ ⟨12, 2, 0, 1302082, 371250, 2013, 65536⟩
    (by decide) selected_cut_46668

theorem selected_cut_46669 : selected 9 ⟨1302132, by decide⟩
    (prefixPartial 12 371251) = some ⟨12, 2, 0, 1302132, 371251, 2509, 65536⟩ := by
  decide +kernel

theorem context_12_371251_1302132 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371251 ⟨1302132, by decide⟩ :=
  accepted_of_selected 12 371251 ⟨1302132, by decide⟩ ⟨12, 2, 0, 1302132, 371251, 2509, 65536⟩
    (by decide) selected_cut_46669

theorem unmarked_context_11_92812_1302133 : frontier 10 ⟨1302133, by decide⟩
    (prefixCache 11 92812) (prefixPartial 11 92812) = false := by
  decide +kernel

theorem node_context_11_92812_1302133 : EJMOriginalGlobalDAGData.nodes 10 ⟨1302133, by decide⟩ =
    .split (coordinate 11) (![⟨1255011, by decide⟩,⟨1302048, by decide⟩,⟨1302082, by decide⟩,⟨1302132, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92812_1302133 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92812 ⟨1302133, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92812
    ⟨1302133, by decide⟩ (by decide) (![⟨1255011, by decide⟩,⟨1302048, by decide⟩,⟨1302082, by decide⟩,⟨1302132, by decide⟩]) unmarked_context_11_92812_1302133 node_context_11_92812_1302133
  intro a
  fin_cases a
  · exact context_12_371248_1255011
  · exact context_12_371249_1302048
  · exact context_12_371250_1302082
  · exact context_12_371251_1302132

theorem selected_cut_46670 : selected 9 ⟨1302192, by decide⟩
    (prefixPartial 12 371252) = some ⟨12, 2, 0, 1302192, 371252, 2525, 65536⟩ := by
  decide +kernel

theorem context_12_371252_1302192 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371252 ⟨1302192, by decide⟩ :=
  accepted_of_selected 12 371252 ⟨1302192, by decide⟩ ⟨12, 2, 0, 1302192, 371252, 2525, 65536⟩
    (by decide) selected_cut_46670

theorem selected_cut_46671 : selected 9 ⟨1302241, by decide⟩
    (prefixPartial 12 371253) = some ⟨12, 2, 0, 1302241, 371253, 2433, 65536⟩ := by
  decide +kernel

theorem context_12_371253_1302241 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371253 ⟨1302241, by decide⟩ :=
  accepted_of_selected 12 371253 ⟨1302241, by decide⟩ ⟨12, 2, 0, 1302241, 371253, 2433, 65536⟩
    (by decide) selected_cut_46671

theorem selected_cut_46672 : selected 9 ⟨1302281, by decide⟩
    (prefixPartial 12 371254) = some ⟨12, 2, 0, 1302281, 371254, 1945, 65536⟩ := by
  decide +kernel

theorem context_12_371254_1302281 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371254 ⟨1302281, by decide⟩ :=
  accepted_of_selected 12 371254 ⟨1302281, by decide⟩ ⟨12, 2, 0, 1302281, 371254, 1945, 65536⟩
    (by decide) selected_cut_46672

theorem selected_cut_46673 : selected 9 ⟨1302348, by decide⟩
    (prefixPartial 12 371255) = some ⟨12, 2, 0, 1302348, 371255, 2697, 65536⟩ := by
  decide +kernel

theorem context_12_371255_1302348 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371255 ⟨1302348, by decide⟩ :=
  accepted_of_selected 12 371255 ⟨1302348, by decide⟩ ⟨12, 2, 0, 1302348, 371255, 2697, 65536⟩
    (by decide) selected_cut_46673

theorem unmarked_context_11_92813_1302349 : frontier 10 ⟨1302349, by decide⟩
    (prefixCache 11 92813) (prefixPartial 11 92813) = false := by
  decide +kernel

theorem node_context_11_92813_1302349 : EJMOriginalGlobalDAGData.nodes 10 ⟨1302349, by decide⟩ =
    .split (coordinate 11) (![⟨1302192, by decide⟩,⟨1302241, by decide⟩,⟨1302281, by decide⟩,⟨1302348, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92813_1302349 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92813 ⟨1302349, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92813
    ⟨1302349, by decide⟩ (by decide) (![⟨1302192, by decide⟩,⟨1302241, by decide⟩,⟨1302281, by decide⟩,⟨1302348, by decide⟩]) unmarked_context_11_92813_1302349 node_context_11_92813_1302349
  intro a
  fin_cases a
  · exact context_12_371252_1302192
  · exact context_12_371253_1302241
  · exact context_12_371254_1302281
  · exact context_12_371255_1302348

theorem selected_cut_46674 : selected 9 ⟨994572, by decide⟩
    (prefixPartial 12 371256) = some ⟨12, 1, 0, 994572, 371256, 1, 65536⟩ := by
  decide +kernel

theorem context_12_371256_994572 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371256 ⟨994572, by decide⟩ :=
  accepted_of_selected 12 371256 ⟨994572, by decide⟩ ⟨12, 1, 0, 994572, 371256, 1, 65536⟩
    (by decide) selected_cut_46674

theorem selected_cut_46675 : selected 9 ⟨1302388, by decide⟩
    (prefixPartial 12 371257) = some ⟨12, 2, 0, 1302388, 371257, 2001, 65536⟩ := by
  decide +kernel

theorem context_12_371257_1302388 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371257 ⟨1302388, by decide⟩ :=
  accepted_of_selected 12 371257 ⟨1302388, by decide⟩ ⟨12, 2, 0, 1302388, 371257, 2001, 65536⟩
    (by decide) selected_cut_46675

theorem selected_cut_46676 : selected 9 ⟨893903, by decide⟩
    (prefixPartial 12 371258) = some ⟨12, 1, 0, 893903, 371258, 1, 65536⟩ := by
  decide +kernel

theorem context_12_371258_893903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371258 ⟨893903, by decide⟩ :=
  accepted_of_selected 12 371258 ⟨893903, by decide⟩ ⟨12, 1, 0, 893903, 371258, 1, 65536⟩
    (by decide) selected_cut_46676

theorem selected_cut_46677 : selected 9 ⟨1302433, by decide⟩
    (prefixPartial 12 371259) = some ⟨12, 2, 0, 1302433, 371259, 2181, 65536⟩ := by
  decide +kernel

theorem context_12_371259_1302433 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371259 ⟨1302433, by decide⟩ :=
  accepted_of_selected 12 371259 ⟨1302433, by decide⟩ ⟨12, 2, 0, 1302433, 371259, 2181, 65536⟩
    (by decide) selected_cut_46677

theorem unmarked_context_11_92814_1302434 : frontier 10 ⟨1302434, by decide⟩
    (prefixCache 11 92814) (prefixPartial 11 92814) = false := by
  decide +kernel

theorem node_context_11_92814_1302434 : EJMOriginalGlobalDAGData.nodes 10 ⟨1302434, by decide⟩ =
    .split (coordinate 11) (![⟨994572, by decide⟩,⟨1302388, by decide⟩,⟨893903, by decide⟩,⟨1302433, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92814_1302434 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92814 ⟨1302434, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92814
    ⟨1302434, by decide⟩ (by decide) (![⟨994572, by decide⟩,⟨1302388, by decide⟩,⟨893903, by decide⟩,⟨1302433, by decide⟩]) unmarked_context_11_92814_1302434 node_context_11_92814_1302434
  intro a
  fin_cases a
  · exact context_12_371256_994572
  · exact context_12_371257_1302388
  · exact context_12_371258_893903
  · exact context_12_371259_1302433

theorem selected_cut_46678 : selected 10 ⟨1302511, by decide⟩
    (prefixPartial 11 92815) = some ⟨11, 2, 0, 1302511, 92815, 3761, 262144⟩ := by
  decide +kernel

theorem context_11_92815_1302511 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92815 ⟨1302511, by decide⟩ :=
  accepted_of_selected 11 92815 ⟨1302511, by decide⟩ ⟨11, 2, 0, 1302511, 92815, 3761, 262144⟩
    (by decide) selected_cut_46678

theorem unmarked_context_10_23203_1302512 : frontier 11 ⟨1302512, by decide⟩
    (prefixCache 10 23203) (prefixPartial 10 23203) = false := by
  decide +kernel

theorem node_context_10_23203_1302512 : EJMOriginalGlobalDAGData.nodes 11 ⟨1302512, by decide⟩ =
    .split (coordinate 10) (![⟨1302133, by decide⟩,⟨1302349, by decide⟩,⟨1302434, by decide⟩,⟨1302511, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23203_1302512 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23203 ⟨1302512, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23203
    ⟨1302512, by decide⟩ (by decide) (![⟨1302133, by decide⟩,⟨1302349, by decide⟩,⟨1302434, by decide⟩,⟨1302511, by decide⟩]) unmarked_context_10_23203_1302512 node_context_10_23203_1302512
  intro a
  fin_cases a
  · exact context_11_92812_1302133
  · exact context_11_92813_1302349
  · exact context_11_92814_1302434
  · exact context_11_92815_1302511

theorem unmarked_context_9_5800_1302513 : frontier 12 ⟨1302513, by decide⟩
    (prefixCache 9 5800) (prefixPartial 9 5800) = false := by
  decide +kernel

theorem node_context_9_5800_1302513 : EJMOriginalGlobalDAGData.nodes 12 ⟨1302513, by decide⟩ =
    .split (coordinate 9) (![⟨1301046, by decide⟩,⟨1301667, by decide⟩,⟨1302007, by decide⟩,⟨1302512, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5800_1302513 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5800 ⟨1302513, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5800
    ⟨1302513, by decide⟩ (by decide) (![⟨1301046, by decide⟩,⟨1301667, by decide⟩,⟨1302007, by decide⟩,⟨1302512, by decide⟩]) unmarked_context_9_5800_1302513 node_context_9_5800_1302513
  intro a
  fin_cases a
  · exact context_10_23200_1301046
  · exact context_10_23201_1301667
  · exact context_10_23202_1302007
  · exact context_10_23203_1302512

theorem selected_cut_46679 : selected 10 ⟨1302580, by decide⟩
    (prefixPartial 11 92816) = some ⟨11, 2, 0, 1302580, 92816, 3317, 262144⟩ := by
  decide +kernel

theorem context_11_92816_1302580 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92816 ⟨1302580, by decide⟩ :=
  accepted_of_selected 11 92816 ⟨1302580, by decide⟩ ⟨11, 2, 0, 1302580, 92816, 3317, 262144⟩
    (by decide) selected_cut_46679

theorem selected_cut_46680 : selected 9 ⟨1302618, by decide⟩
    (prefixPartial 12 371268) = some ⟨12, 2, 0, 1302618, 371268, 1913, 65536⟩ := by
  decide +kernel

theorem context_12_371268_1302618 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371268 ⟨1302618, by decide⟩ :=
  accepted_of_selected 12 371268 ⟨1302618, by decide⟩ ⟨12, 2, 0, 1302618, 371268, 1913, 65536⟩
    (by decide) selected_cut_46680

theorem selected_cut_46681 : selected 9 ⟨1257136, by decide⟩
    (prefixPartial 12 371269) = some ⟨12, 1, 0, 1257136, 371269, 1, 65536⟩ := by
  decide +kernel

theorem context_12_371269_1257136 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371269 ⟨1257136, by decide⟩ :=
  accepted_of_selected 12 371269 ⟨1257136, by decide⟩ ⟨12, 1, 0, 1257136, 371269, 1, 65536⟩
    (by decide) selected_cut_46681

theorem selected_cut_46682 : selected 9 ⟨1302645, by decide⟩
    (prefixPartial 12 371270) = some ⟨12, 2, 0, 1302645, 371270, 1413, 65536⟩ := by
  decide +kernel

theorem context_12_371270_1302645 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371270 ⟨1302645, by decide⟩ :=
  accepted_of_selected 12 371270 ⟨1302645, by decide⟩ ⟨12, 2, 0, 1302645, 371270, 1413, 65536⟩
    (by decide) selected_cut_46682

theorem selected_cut_46683 : selected 9 ⟨1302683, by decide⟩
    (prefixPartial 12 371271) = some ⟨12, 2, 0, 1302683, 371271, 1917, 65536⟩ := by
  decide +kernel

theorem context_12_371271_1302683 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371271 ⟨1302683, by decide⟩ :=
  accepted_of_selected 12 371271 ⟨1302683, by decide⟩ ⟨12, 2, 0, 1302683, 371271, 1917, 65536⟩
    (by decide) selected_cut_46683

theorem unmarked_context_11_92817_1302684 : frontier 10 ⟨1302684, by decide⟩
    (prefixCache 11 92817) (prefixPartial 11 92817) = false := by
  decide +kernel

theorem node_context_11_92817_1302684 : EJMOriginalGlobalDAGData.nodes 10 ⟨1302684, by decide⟩ =
    .split (coordinate 11) (![⟨1302618, by decide⟩,⟨1257136, by decide⟩,⟨1302645, by decide⟩,⟨1302683, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92817_1302684 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92817 ⟨1302684, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92817
    ⟨1302684, by decide⟩ (by decide) (![⟨1302618, by decide⟩,⟨1257136, by decide⟩,⟨1302645, by decide⟩,⟨1302683, by decide⟩]) unmarked_context_11_92817_1302684 node_context_11_92817_1302684
  intro a
  fin_cases a
  · exact context_12_371268_1302618
  · exact context_12_371269_1257136
  · exact context_12_371270_1302645
  · exact context_12_371271_1302683

theorem selected_cut_46684 : selected 10 ⟨1302747, by decide⟩
    (prefixPartial 11 92818) = some ⟨11, 2, 0, 1302747, 92818, 3253, 262144⟩ := by
  decide +kernel

theorem context_11_92818_1302747 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92818 ⟨1302747, by decide⟩ :=
  accepted_of_selected 11 92818 ⟨1302747, by decide⟩ ⟨11, 2, 0, 1302747, 92818, 3253, 262144⟩
    (by decide) selected_cut_46684

theorem selected_cut_46685 : selected 9 ⟨1302775, by decide⟩
    (prefixPartial 12 371276) = some ⟨12, 2, 0, 1302775, 371276, 1513, 65536⟩ := by
  decide +kernel

theorem context_12_371276_1302775 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371276 ⟨1302775, by decide⟩ :=
  accepted_of_selected 12 371276 ⟨1302775, by decide⟩ ⟨12, 2, 0, 1302775, 371276, 1513, 65536⟩
    (by decide) selected_cut_46685

theorem selected_cut_46686 : selected 9 ⟨1302798, by decide⟩
    (prefixPartial 12 371277) = some ⟨12, 2, 0, 1302798, 371277, 1405, 65536⟩ := by
  decide +kernel

theorem context_12_371277_1302798 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371277 ⟨1302798, by decide⟩ :=
  accepted_of_selected 12 371277 ⟨1302798, by decide⟩ ⟨12, 2, 0, 1302798, 371277, 1405, 65536⟩
    (by decide) selected_cut_46686

theorem selected_cut_46687 : selected 9 ⟨1302819, by decide⟩
    (prefixPartial 12 371278) = some ⟨12, 2, 0, 1302819, 371278, 1257, 65536⟩ := by
  decide +kernel

theorem context_12_371278_1302819 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371278 ⟨1302819, by decide⟩ :=
  accepted_of_selected 12 371278 ⟨1302819, by decide⟩ ⟨12, 2, 0, 1302819, 371278, 1257, 65536⟩
    (by decide) selected_cut_46687

theorem selected_cut_46688 : selected 9 ⟨1302841, by decide⟩
    (prefixPartial 12 371279) = some ⟨12, 2, 0, 1302841, 371279, 1381, 65536⟩ := by
  decide +kernel

theorem context_12_371279_1302841 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371279 ⟨1302841, by decide⟩ :=
  accepted_of_selected 12 371279 ⟨1302841, by decide⟩ ⟨12, 2, 0, 1302841, 371279, 1381, 65536⟩
    (by decide) selected_cut_46688

theorem unmarked_context_11_92819_1302842 : frontier 10 ⟨1302842, by decide⟩
    (prefixCache 11 92819) (prefixPartial 11 92819) = false := by
  decide +kernel

theorem node_context_11_92819_1302842 : EJMOriginalGlobalDAGData.nodes 10 ⟨1302842, by decide⟩ =
    .split (coordinate 11) (![⟨1302775, by decide⟩,⟨1302798, by decide⟩,⟨1302819, by decide⟩,⟨1302841, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92819_1302842 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92819 ⟨1302842, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92819
    ⟨1302842, by decide⟩ (by decide) (![⟨1302775, by decide⟩,⟨1302798, by decide⟩,⟨1302819, by decide⟩,⟨1302841, by decide⟩]) unmarked_context_11_92819_1302842 node_context_11_92819_1302842
  intro a
  fin_cases a
  · exact context_12_371276_1302775
  · exact context_12_371277_1302798
  · exact context_12_371278_1302819
  · exact context_12_371279_1302841

theorem unmarked_context_10_23204_1302843 : frontier 11 ⟨1302843, by decide⟩
    (prefixCache 10 23204) (prefixPartial 10 23204) = false := by
  decide +kernel

theorem node_context_10_23204_1302843 : EJMOriginalGlobalDAGData.nodes 11 ⟨1302843, by decide⟩ =
    .split (coordinate 10) (![⟨1302580, by decide⟩,⟨1302684, by decide⟩,⟨1302747, by decide⟩,⟨1302842, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23204_1302843 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23204 ⟨1302843, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23204
    ⟨1302843, by decide⟩ (by decide) (![⟨1302580, by decide⟩,⟨1302684, by decide⟩,⟨1302747, by decide⟩,⟨1302842, by decide⟩]) unmarked_context_10_23204_1302843 node_context_10_23204_1302843
  intro a
  fin_cases a
  · exact context_11_92816_1302580
  · exact context_11_92817_1302684
  · exact context_11_92818_1302747
  · exact context_11_92819_1302842

theorem selected_cut_46689 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 23205) = some ⟨10, 1, 0, 893098, 23205, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_23205_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23205 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 23205 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 23205, 1, 1048576⟩
    (by decide) selected_cut_46689

theorem selected_cut_46690 : selected 10 ⟨1302882, by decide⟩
    (prefixPartial 11 92824) = some ⟨11, 2, 0, 1302882, 92824, 2117, 262144⟩ := by
  decide +kernel

theorem context_11_92824_1302882 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92824 ⟨1302882, by decide⟩ :=
  accepted_of_selected 11 92824 ⟨1302882, by decide⟩ ⟨11, 2, 0, 1302882, 92824, 2117, 262144⟩
    (by decide) selected_cut_46690

theorem selected_cut_46691 : selected 10 ⟨1302937, by decide⟩
    (prefixPartial 11 92825) = some ⟨11, 2, 0, 1302937, 92825, 3273, 262144⟩ := by
  decide +kernel

theorem context_11_92825_1302937 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92825 ⟨1302937, by decide⟩ :=
  accepted_of_selected 11 92825 ⟨1302937, by decide⟩ ⟨11, 2, 0, 1302937, 92825, 3273, 262144⟩
    (by decide) selected_cut_46691

theorem selected_cut_46692 : selected 10 ⟨900587, by decide⟩
    (prefixPartial 11 92826) = some ⟨11, 1, 0, 900587, 92826, 1, 262144⟩ := by
  decide +kernel

theorem context_11_92826_900587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92826 ⟨900587, by decide⟩ :=
  accepted_of_selected 11 92826 ⟨900587, by decide⟩ ⟨11, 1, 0, 900587, 92826, 1, 262144⟩
    (by decide) selected_cut_46692

theorem selected_cut_46693 : selected 10 ⟨1302971, by decide⟩
    (prefixPartial 11 92827) = some ⟨11, 2, 0, 1302971, 92827, 1921, 262144⟩ := by
  decide +kernel

theorem context_11_92827_1302971 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92827 ⟨1302971, by decide⟩ :=
  accepted_of_selected 11 92827 ⟨1302971, by decide⟩ ⟨11, 2, 0, 1302971, 92827, 1921, 262144⟩
    (by decide) selected_cut_46693

theorem unmarked_context_10_23206_1302972 : frontier 11 ⟨1302972, by decide⟩
    (prefixCache 10 23206) (prefixPartial 10 23206) = false := by
  decide +kernel

theorem node_context_10_23206_1302972 : EJMOriginalGlobalDAGData.nodes 11 ⟨1302972, by decide⟩ =
    .split (coordinate 10) (![⟨1302882, by decide⟩,⟨1302937, by decide⟩,⟨900587, by decide⟩,⟨1302971, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23206_1302972 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23206 ⟨1302972, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23206
    ⟨1302972, by decide⟩ (by decide) (![⟨1302882, by decide⟩,⟨1302937, by decide⟩,⟨900587, by decide⟩,⟨1302971, by decide⟩]) unmarked_context_10_23206_1302972 node_context_10_23206_1302972
  intro a
  fin_cases a
  · exact context_11_92824_1302882
  · exact context_11_92825_1302937
  · exact context_11_92826_900587
  · exact context_11_92827_1302971

theorem selected_cut_46694 : selected 9 ⟨1302990, by decide⟩
    (prefixPartial 12 371312) = some ⟨12, 2, 0, 1302990, 371312, 1153, 65536⟩ := by
  decide +kernel

theorem context_12_371312_1302990 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371312 ⟨1302990, by decide⟩ :=
  accepted_of_selected 12 371312 ⟨1302990, by decide⟩ ⟨12, 2, 0, 1302990, 371312, 1153, 65536⟩
    (by decide) selected_cut_46694

theorem selected_cut_46695 : selected 9 ⟨1303007, by decide⟩
    (prefixPartial 12 371313) = some ⟨12, 2, 0, 1303007, 371313, 1061, 65536⟩ := by
  decide +kernel

theorem context_12_371313_1303007 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371313 ⟨1303007, by decide⟩ :=
  accepted_of_selected 12 371313 ⟨1303007, by decide⟩ ⟨12, 2, 0, 1303007, 371313, 1061, 65536⟩
    (by decide) selected_cut_46695

theorem selected_cut_46696 : selected 9 ⟨1303024, by decide⟩
    (prefixPartial 12 371314) = some ⟨12, 2, 0, 1303024, 371314, 965, 65536⟩ := by
  decide +kernel

theorem context_12_371314_1303024 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371314 ⟨1303024, by decide⟩ :=
  accepted_of_selected 12 371314 ⟨1303024, by decide⟩ ⟨12, 2, 0, 1303024, 371314, 965, 65536⟩
    (by decide) selected_cut_46696

theorem selected_cut_46697 : selected 9 ⟨1303048, by decide⟩
    (prefixPartial 12 371315) = some ⟨12, 2, 0, 1303048, 371315, 1153, 65536⟩ := by
  decide +kernel

theorem context_12_371315_1303048 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371315 ⟨1303048, by decide⟩ :=
  accepted_of_selected 12 371315 ⟨1303048, by decide⟩ ⟨12, 2, 0, 1303048, 371315, 1153, 65536⟩
    (by decide) selected_cut_46697

theorem unmarked_context_11_92828_1303049 : frontier 10 ⟨1303049, by decide⟩
    (prefixCache 11 92828) (prefixPartial 11 92828) = false := by
  decide +kernel

theorem node_context_11_92828_1303049 : EJMOriginalGlobalDAGData.nodes 10 ⟨1303049, by decide⟩ =
    .split (coordinate 11) (![⟨1302990, by decide⟩,⟨1303007, by decide⟩,⟨1303024, by decide⟩,⟨1303048, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92828_1303049 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92828 ⟨1303049, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92828
    ⟨1303049, by decide⟩ (by decide) (![⟨1302990, by decide⟩,⟨1303007, by decide⟩,⟨1303024, by decide⟩,⟨1303048, by decide⟩]) unmarked_context_11_92828_1303049 node_context_11_92828_1303049
  intro a
  fin_cases a
  · exact context_12_371312_1302990
  · exact context_12_371313_1303007
  · exact context_12_371314_1303024
  · exact context_12_371315_1303048

theorem selected_cut_46698 : selected 10 ⟨1303106, by decide⟩
    (prefixPartial 11 92829) = some ⟨11, 2, 0, 1303106, 92829, 3065, 262144⟩ := by
  decide +kernel

theorem context_11_92829_1303106 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92829 ⟨1303106, by decide⟩ :=
  accepted_of_selected 11 92829 ⟨1303106, by decide⟩ ⟨11, 2, 0, 1303106, 92829, 3065, 262144⟩
    (by decide) selected_cut_46698

theorem selected_cut_46699 : selected 10 ⟨1303130, by decide⟩
    (prefixPartial 11 92830) = some ⟨11, 2, 0, 1303130, 92830, 1745, 262144⟩ := by
  decide +kernel

theorem context_11_92830_1303130 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92830 ⟨1303130, by decide⟩ :=
  accepted_of_selected 11 92830 ⟨1303130, by decide⟩ ⟨11, 2, 0, 1303130, 92830, 1745, 262144⟩
    (by decide) selected_cut_46699

theorem selected_cut_46700 : selected 10 ⟨1303150, by decide⟩
    (prefixPartial 11 92831) = some ⟨11, 2, 0, 1303150, 92831, 1593, 262144⟩ := by
  decide +kernel

theorem context_11_92831_1303150 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92831 ⟨1303150, by decide⟩ :=
  accepted_of_selected 11 92831 ⟨1303150, by decide⟩ ⟨11, 2, 0, 1303150, 92831, 1593, 262144⟩
    (by decide) selected_cut_46700

theorem unmarked_context_10_23207_1303151 : frontier 11 ⟨1303151, by decide⟩
    (prefixCache 10 23207) (prefixPartial 10 23207) = false := by
  decide +kernel

theorem node_context_10_23207_1303151 : EJMOriginalGlobalDAGData.nodes 11 ⟨1303151, by decide⟩ =
    .split (coordinate 10) (![⟨1303049, by decide⟩,⟨1303106, by decide⟩,⟨1303130, by decide⟩,⟨1303150, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23207_1303151 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23207 ⟨1303151, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23207
    ⟨1303151, by decide⟩ (by decide) (![⟨1303049, by decide⟩,⟨1303106, by decide⟩,⟨1303130, by decide⟩,⟨1303150, by decide⟩]) unmarked_context_10_23207_1303151 node_context_10_23207_1303151
  intro a
  fin_cases a
  · exact context_11_92828_1303049
  · exact context_11_92829_1303106
  · exact context_11_92830_1303130
  · exact context_11_92831_1303150

theorem unmarked_context_9_5801_1303152 : frontier 12 ⟨1303152, by decide⟩
    (prefixCache 9 5801) (prefixPartial 9 5801) = false := by
  decide +kernel

theorem node_context_9_5801_1303152 : EJMOriginalGlobalDAGData.nodes 12 ⟨1303152, by decide⟩ =
    .split (coordinate 9) (![⟨1302843, by decide⟩,⟨893098, by decide⟩,⟨1302972, by decide⟩,⟨1303151, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5801_1303152 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5801 ⟨1303152, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5801
    ⟨1303152, by decide⟩ (by decide) (![⟨1302843, by decide⟩,⟨893098, by decide⟩,⟨1302972, by decide⟩,⟨1303151, by decide⟩]) unmarked_context_9_5801_1303152 node_context_9_5801_1303152
  intro a
  fin_cases a
  · exact context_10_23204_1302843
  · exact context_10_23205_893098
  · exact context_10_23206_1302972
  · exact context_10_23207_1303151

theorem selected_cut_46701 : selected 10 ⟨1303167, by decide⟩
    (prefixPartial 11 92832) = some ⟨11, 2, 0, 1303167, 92832, 869, 262144⟩ := by
  decide +kernel

theorem context_11_92832_1303167 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92832 ⟨1303167, by decide⟩ :=
  accepted_of_selected 11 92832 ⟨1303167, by decide⟩ ⟨11, 2, 0, 1303167, 92832, 869, 262144⟩
    (by decide) selected_cut_46701

theorem selected_cut_46702 : selected 10 ⟨1303203, by decide⟩
    (prefixPartial 11 92833) = some ⟨11, 2, 0, 1303203, 92833, 1965, 262144⟩ := by
  decide +kernel

theorem context_11_92833_1303203 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92833 ⟨1303203, by decide⟩ :=
  accepted_of_selected 11 92833 ⟨1303203, by decide⟩ ⟨11, 2, 0, 1303203, 92833, 1965, 262144⟩
    (by decide) selected_cut_46702

theorem selected_cut_46703 : selected 10 ⟨1303244, by decide⟩
    (prefixPartial 11 92834) = some ⟨11, 2, 0, 1303244, 92834, 2413, 262144⟩ := by
  decide +kernel

theorem context_11_92834_1303244 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92834 ⟨1303244, by decide⟩ :=
  accepted_of_selected 11 92834 ⟨1303244, by decide⟩ ⟨11, 2, 0, 1303244, 92834, 2413, 262144⟩
    (by decide) selected_cut_46703

theorem selected_cut_46704 : selected 10 ⟨1303275, by decide⟩
    (prefixPartial 11 92835) = some ⟨11, 2, 0, 1303275, 92835, 1709, 262144⟩ := by
  decide +kernel

theorem context_11_92835_1303275 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92835 ⟨1303275, by decide⟩ :=
  accepted_of_selected 11 92835 ⟨1303275, by decide⟩ ⟨11, 2, 0, 1303275, 92835, 1709, 262144⟩
    (by decide) selected_cut_46704

theorem unmarked_context_10_23208_1303276 : frontier 11 ⟨1303276, by decide⟩
    (prefixCache 10 23208) (prefixPartial 10 23208) = false := by
  decide +kernel

theorem node_context_10_23208_1303276 : EJMOriginalGlobalDAGData.nodes 11 ⟨1303276, by decide⟩ =
    .split (coordinate 10) (![⟨1303167, by decide⟩,⟨1303203, by decide⟩,⟨1303244, by decide⟩,⟨1303275, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23208_1303276 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23208 ⟨1303276, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23208
    ⟨1303276, by decide⟩ (by decide) (![⟨1303167, by decide⟩,⟨1303203, by decide⟩,⟨1303244, by decide⟩,⟨1303275, by decide⟩]) unmarked_context_10_23208_1303276 node_context_10_23208_1303276
  intro a
  fin_cases a
  · exact context_11_92832_1303167
  · exact context_11_92833_1303203
  · exact context_11_92834_1303244
  · exact context_11_92835_1303275

theorem selected_cut_46705 : selected 10 ⟨1303300, by decide⟩
    (prefixPartial 11 92836) = some ⟨11, 2, 0, 1303300, 92836, 1441, 262144⟩ := by
  decide +kernel

theorem context_11_92836_1303300 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92836 ⟨1303300, by decide⟩ :=
  accepted_of_selected 11 92836 ⟨1303300, by decide⟩ ⟨11, 2, 0, 1303300, 92836, 1441, 262144⟩
    (by decide) selected_cut_46705

theorem selected_cut_46706 : selected 10 ⟨1192826, by decide⟩
    (prefixPartial 11 92837) = some ⟨11, 1, 0, 1192826, 92837, 1, 262144⟩ := by
  decide +kernel

theorem context_11_92837_1192826 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92837 ⟨1192826, by decide⟩ :=
  accepted_of_selected 11 92837 ⟨1192826, by decide⟩ ⟨11, 1, 0, 1192826, 92837, 1, 262144⟩
    (by decide) selected_cut_46706

theorem selected_cut_46707 : selected 10 ⟨1303332, by decide⟩
    (prefixPartial 11 92838) = some ⟨11, 2, 0, 1303332, 92838, 1801, 262144⟩ := by
  decide +kernel

theorem context_11_92838_1303332 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92838 ⟨1303332, by decide⟩ :=
  accepted_of_selected 11 92838 ⟨1303332, by decide⟩ ⟨11, 2, 0, 1303332, 92838, 1801, 262144⟩
    (by decide) selected_cut_46707

theorem selected_cut_46708 : selected 10 ⟨1303360, by decide⟩
    (prefixPartial 11 92839) = some ⟨11, 2, 0, 1303360, 92839, 1309, 262144⟩ := by
  decide +kernel

theorem context_11_92839_1303360 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92839 ⟨1303360, by decide⟩ :=
  accepted_of_selected 11 92839 ⟨1303360, by decide⟩ ⟨11, 2, 0, 1303360, 92839, 1309, 262144⟩
    (by decide) selected_cut_46708

theorem unmarked_context_10_23209_1303361 : frontier 11 ⟨1303361, by decide⟩
    (prefixCache 10 23209) (prefixPartial 10 23209) = false := by
  decide +kernel

theorem node_context_10_23209_1303361 : EJMOriginalGlobalDAGData.nodes 11 ⟨1303361, by decide⟩ =
    .split (coordinate 10) (![⟨1303300, by decide⟩,⟨1192826, by decide⟩,⟨1303332, by decide⟩,⟨1303360, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23209_1303361 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23209 ⟨1303361, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23209
    ⟨1303361, by decide⟩ (by decide) (![⟨1303300, by decide⟩,⟨1192826, by decide⟩,⟨1303332, by decide⟩,⟨1303360, by decide⟩]) unmarked_context_10_23209_1303361 node_context_10_23209_1303361
  intro a
  fin_cases a
  · exact context_11_92836_1303300
  · exact context_11_92837_1192826
  · exact context_11_92838_1303332
  · exact context_11_92839_1303360

theorem selected_cut_46709 : selected 11 ⟨1303385, by decide⟩
    (prefixPartial 10 23210) = some ⟨10, 2, 0, 1303385, 23210, 1181, 1048576⟩ := by
  decide +kernel

theorem context_10_23210_1303385 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23210 ⟨1303385, by decide⟩ :=
  accepted_of_selected 10 23210 ⟨1303385, by decide⟩ ⟨10, 2, 0, 1303385, 23210, 1181, 1048576⟩
    (by decide) selected_cut_46709

theorem selected_cut_46710 : selected 11 ⟨1303460, by decide⟩
    (prefixPartial 10 23211) = some ⟨10, 2, 0, 1303460, 23211, 3909, 1048576⟩ := by
  decide +kernel

theorem context_10_23211_1303460 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23211 ⟨1303460, by decide⟩ :=
  accepted_of_selected 10 23211 ⟨1303460, by decide⟩ ⟨10, 2, 0, 1303460, 23211, 3909, 1048576⟩
    (by decide) selected_cut_46710

theorem unmarked_context_9_5802_1303461 : frontier 12 ⟨1303461, by decide⟩
    (prefixCache 9 5802) (prefixPartial 9 5802) = false := by
  decide +kernel

theorem node_context_9_5802_1303461 : EJMOriginalGlobalDAGData.nodes 12 ⟨1303461, by decide⟩ =
    .split (coordinate 9) (![⟨1303276, by decide⟩,⟨1303361, by decide⟩,⟨1303385, by decide⟩,⟨1303460, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5802_1303461 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5802 ⟨1303461, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5802
    ⟨1303461, by decide⟩ (by decide) (![⟨1303276, by decide⟩,⟨1303361, by decide⟩,⟨1303385, by decide⟩,⟨1303460, by decide⟩]) unmarked_context_9_5802_1303461 node_context_9_5802_1303461
  intro a
  fin_cases a
  · exact context_10_23208_1303276
  · exact context_10_23209_1303361
  · exact context_10_23210_1303385
  · exact context_10_23211_1303460

theorem selected_cut_46711 : selected 10 ⟨1303485, by decide⟩
    (prefixPartial 11 92848) = some ⟨11, 2, 0, 1303485, 92848, 1065, 262144⟩ := by
  decide +kernel

theorem context_11_92848_1303485 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92848 ⟨1303485, by decide⟩ :=
  accepted_of_selected 11 92848 ⟨1303485, by decide⟩ ⟨11, 2, 0, 1303485, 92848, 1065, 262144⟩
    (by decide) selected_cut_46711

theorem selected_cut_46712 : selected 10 ⟨1303532, by decide⟩
    (prefixPartial 11 92849) = some ⟨11, 2, 0, 1303532, 92849, 2237, 262144⟩ := by
  decide +kernel

theorem context_11_92849_1303532 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92849 ⟨1303532, by decide⟩ :=
  accepted_of_selected 11 92849 ⟨1303532, by decide⟩ ⟨11, 2, 0, 1303532, 92849, 2237, 262144⟩
    (by decide) selected_cut_46712

theorem selected_cut_46713 : selected 10 ⟨1303549, by decide⟩
    (prefixPartial 11 92850) = some ⟨11, 2, 0, 1303549, 92850, 873, 262144⟩ := by
  decide +kernel

theorem context_11_92850_1303549 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92850 ⟨1303549, by decide⟩ :=
  accepted_of_selected 11 92850 ⟨1303549, by decide⟩ ⟨11, 2, 0, 1303549, 92850, 873, 262144⟩
    (by decide) selected_cut_46713

theorem selected_cut_46714 : selected 10 ⟨1303571, by decide⟩
    (prefixPartial 11 92851) = some ⟨11, 2, 0, 1303571, 92851, 1301, 262144⟩ := by
  decide +kernel

theorem context_11_92851_1303571 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92851 ⟨1303571, by decide⟩ :=
  accepted_of_selected 11 92851 ⟨1303571, by decide⟩ ⟨11, 2, 0, 1303571, 92851, 1301, 262144⟩
    (by decide) selected_cut_46714

theorem unmarked_context_10_23212_1303572 : frontier 11 ⟨1303572, by decide⟩
    (prefixCache 10 23212) (prefixPartial 10 23212) = false := by
  decide +kernel

theorem node_context_10_23212_1303572 : EJMOriginalGlobalDAGData.nodes 11 ⟨1303572, by decide⟩ =
    .split (coordinate 10) (![⟨1303485, by decide⟩,⟨1303532, by decide⟩,⟨1303549, by decide⟩,⟨1303571, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23212_1303572 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23212 ⟨1303572, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23212
    ⟨1303572, by decide⟩ (by decide) (![⟨1303485, by decide⟩,⟨1303532, by decide⟩,⟨1303549, by decide⟩,⟨1303571, by decide⟩]) unmarked_context_10_23212_1303572 node_context_10_23212_1303572
  intro a
  fin_cases a
  · exact context_11_92848_1303485
  · exact context_11_92849_1303532
  · exact context_11_92850_1303549
  · exact context_11_92851_1303571

theorem selected_cut_46715 : selected 11 ⟨1303626, by decide⟩
    (prefixPartial 10 23213) = some ⟨10, 2, 0, 1303626, 23213, 2837, 1048576⟩ := by
  decide +kernel

theorem context_10_23213_1303626 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23213 ⟨1303626, by decide⟩ :=
  accepted_of_selected 10 23213 ⟨1303626, by decide⟩ ⟨10, 2, 0, 1303626, 23213, 2837, 1048576⟩
    (by decide) selected_cut_46715

theorem selected_cut_46716 : selected 11 ⟨1303652, by decide⟩
    (prefixPartial 10 23214) = some ⟨10, 2, 0, 1303652, 23214, 989, 1048576⟩ := by
  decide +kernel

theorem context_10_23214_1303652 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23214 ⟨1303652, by decide⟩ :=
  accepted_of_selected 10 23214 ⟨1303652, by decide⟩ ⟨10, 2, 0, 1303652, 23214, 989, 1048576⟩
    (by decide) selected_cut_46716

theorem selected_cut_46717 : selected 11 ⟨1303666, by decide⟩
    (prefixPartial 10 23215) = some ⟨10, 2, 0, 1303666, 23215, 281, 1048576⟩ := by
  decide +kernel

theorem context_10_23215_1303666 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23215 ⟨1303666, by decide⟩ :=
  accepted_of_selected 10 23215 ⟨1303666, by decide⟩ ⟨10, 2, 0, 1303666, 23215, 281, 1048576⟩
    (by decide) selected_cut_46717

theorem unmarked_context_9_5803_1303667 : frontier 12 ⟨1303667, by decide⟩
    (prefixCache 9 5803) (prefixPartial 9 5803) = false := by
  decide +kernel

theorem node_context_9_5803_1303667 : EJMOriginalGlobalDAGData.nodes 12 ⟨1303667, by decide⟩ =
    .split (coordinate 9) (![⟨1303572, by decide⟩,⟨1303626, by decide⟩,⟨1303652, by decide⟩,⟨1303666, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5803_1303667 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5803 ⟨1303667, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5803
    ⟨1303667, by decide⟩ (by decide) (![⟨1303572, by decide⟩,⟨1303626, by decide⟩,⟨1303652, by decide⟩,⟨1303666, by decide⟩]) unmarked_context_9_5803_1303667 node_context_9_5803_1303667
  intro a
  fin_cases a
  · exact context_10_23212_1303572
  · exact context_10_23213_1303626
  · exact context_10_23214_1303652
  · exact context_10_23215_1303666

theorem unmarked_context_8_1450_1303668 : frontier 13 ⟨1303668, by decide⟩
    (prefixCache 8 1450) (prefixPartial 8 1450) = false := by
  decide +kernel

theorem node_context_8_1450_1303668 : EJMOriginalGlobalDAGData.nodes 13 ⟨1303668, by decide⟩ =
    .split (coordinate 8) (![⟨1302513, by decide⟩,⟨1303152, by decide⟩,⟨1303461, by decide⟩,⟨1303667, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1450_1303668 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1450 ⟨1303668, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1450
    ⟨1303668, by decide⟩ (by decide) (![⟨1302513, by decide⟩,⟨1303152, by decide⟩,⟨1303461, by decide⟩,⟨1303667, by decide⟩]) unmarked_context_8_1450_1303668 node_context_8_1450_1303668
  intro a
  fin_cases a
  · exact context_9_5800_1302513
  · exact context_9_5801_1303152
  · exact context_9_5802_1303461
  · exact context_9_5803_1303667

theorem selected_cut_46718 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 92864) = some ⟨11, 1, 0, 434745, 92864, 1, 262144⟩ := by
  decide +kernel

theorem context_11_92864_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92864 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 92864 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 92864, 1, 262144⟩
    (by decide) selected_cut_46718

theorem selected_cut_46719 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 371460) = some ⟨12, 1, 0, 448748, 371460, 1, 65536⟩ := by
  decide +kernel

theorem context_12_371460_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371460 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 371460 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 371460, 1, 65536⟩
    (by decide) selected_cut_46719

theorem selected_cut_46720 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 371461) = some ⟨12, 1, 0, 34034, 371461, 1, 65536⟩ := by
  decide +kernel

theorem context_12_371461_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371461 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 371461 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 371461, 1, 65536⟩
    (by decide) selected_cut_46720

theorem selected_cut_46721 : selected 9 ⟨1303733, by decide⟩
    (prefixPartial 12 371462) = some ⟨12, 2, 0, 1303733, 371462, 1937, 65536⟩ := by
  decide +kernel

theorem context_12_371462_1303733 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371462 ⟨1303733, by decide⟩ :=
  accepted_of_selected 12 371462 ⟨1303733, by decide⟩ ⟨12, 2, 0, 1303733, 371462, 1937, 65536⟩
    (by decide) selected_cut_46721

theorem selected_cut_46722 : selected 9 ⟨1303797, by decide⟩
    (prefixPartial 12 371463) = some ⟨12, 2, 0, 1303797, 371463, 3717, 65536⟩ := by
  decide +kernel

theorem context_12_371463_1303797 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371463 ⟨1303797, by decide⟩ :=
  accepted_of_selected 12 371463 ⟨1303797, by decide⟩ ⟨12, 2, 0, 1303797, 371463, 3717, 65536⟩
    (by decide) selected_cut_46722

theorem unmarked_context_11_92865_1303798 : frontier 10 ⟨1303798, by decide⟩
    (prefixCache 11 92865) (prefixPartial 11 92865) = false := by
  decide +kernel

theorem node_context_11_92865_1303798 : EJMOriginalGlobalDAGData.nodes 10 ⟨1303798, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨34034, by decide⟩,⟨1303733, by decide⟩,⟨1303797, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92865_1303798 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92865 ⟨1303798, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92865
    ⟨1303798, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨34034, by decide⟩,⟨1303733, by decide⟩,⟨1303797, by decide⟩]) unmarked_context_11_92865_1303798 node_context_11_92865_1303798
  intro a
  fin_cases a
  · exact context_12_371460_448748
  · exact context_12_371461_34034
  · exact context_12_371462_1303733
  · exact context_12_371463_1303797

theorem selected_cut_46723 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 371464) = some ⟨12, 1, 0, 448748, 371464, 1, 65536⟩ := by
  decide +kernel

theorem context_12_371464_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371464 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 371464 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 371464, 1, 65536⟩
    (by decide) selected_cut_46723

theorem selected_cut_46724 : selected 9 ⟨1303881, by decide⟩
    (prefixPartial 12 371465) = some ⟨12, 2, 0, 1303881, 371465, 3741, 65536⟩ := by
  decide +kernel

theorem context_12_371465_1303881 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371465 ⟨1303881, by decide⟩ :=
  accepted_of_selected 12 371465 ⟨1303881, by decide⟩ ⟨12, 2, 0, 1303881, 371465, 3741, 65536⟩
    (by decide) selected_cut_46724

theorem selected_cut_46725 : selected 9 ⟨1303933, by decide⟩
    (prefixPartial 12 371466) = some ⟨12, 2, 0, 1303933, 371466, 2901, 65536⟩ := by
  decide +kernel

theorem context_12_371466_1303933 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371466 ⟨1303933, by decide⟩ :=
  accepted_of_selected 12 371466 ⟨1303933, by decide⟩ ⟨12, 2, 0, 1303933, 371466, 2901, 65536⟩
    (by decide) selected_cut_46725

theorem selected_cut_46726 : selected 9 ⟨1303995, by decide⟩
    (prefixPartial 12 371467) = some ⟨12, 2, 0, 1303995, 371467, 3501, 65536⟩ := by
  decide +kernel

theorem context_12_371467_1303995 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371467 ⟨1303995, by decide⟩ :=
  accepted_of_selected 12 371467 ⟨1303995, by decide⟩ ⟨12, 2, 0, 1303995, 371467, 3501, 65536⟩
    (by decide) selected_cut_46726

theorem unmarked_context_11_92866_1303996 : frontier 10 ⟨1303996, by decide⟩
    (prefixCache 11 92866) (prefixPartial 11 92866) = false := by
  decide +kernel

theorem node_context_11_92866_1303996 : EJMOriginalGlobalDAGData.nodes 10 ⟨1303996, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨1303881, by decide⟩,⟨1303933, by decide⟩,⟨1303995, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92866_1303996 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92866 ⟨1303996, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92866
    ⟨1303996, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨1303881, by decide⟩,⟨1303933, by decide⟩,⟨1303995, by decide⟩]) unmarked_context_11_92866_1303996 node_context_11_92866_1303996
  intro a
  fin_cases a
  · exact context_12_371464_448748
  · exact context_12_371465_1303881
  · exact context_12_371466_1303933
  · exact context_12_371467_1303995

theorem selected_cut_46727 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 371468) = some ⟨12, 1, 0, 448748, 371468, 1, 65536⟩ := by
  decide +kernel

theorem context_12_371468_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371468 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 371468 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 371468, 1, 65536⟩
    (by decide) selected_cut_46727

theorem selected_cut_46728 : selected 9 ⟨1304044, by decide⟩
    (prefixPartial 12 371469) = some ⟨12, 2, 0, 1304044, 371469, 3249, 65536⟩ := by
  decide +kernel

theorem context_12_371469_1304044 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371469 ⟨1304044, by decide⟩ :=
  accepted_of_selected 12 371469 ⟨1304044, by decide⟩ ⟨12, 2, 0, 1304044, 371469, 3249, 65536⟩
    (by decide) selected_cut_46728

theorem selected_cut_46729 : selected 9 ⟨1304092, by decide⟩
    (prefixPartial 12 371470) = some ⟨12, 2, 0, 1304092, 371470, 2929, 65536⟩ := by
  decide +kernel

theorem context_12_371470_1304092 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371470 ⟨1304092, by decide⟩ :=
  accepted_of_selected 12 371470 ⟨1304092, by decide⟩ ⟨12, 2, 0, 1304092, 371470, 2929, 65536⟩
    (by decide) selected_cut_46729

theorem selected_cut_46730 : selected 9 ⟨903806, by decide⟩
    (prefixPartial 12 371471) = some ⟨12, 1, 0, 903806, 371471, 1, 65536⟩ := by
  decide +kernel

theorem context_12_371471_903806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371471 ⟨903806, by decide⟩ :=
  accepted_of_selected 12 371471 ⟨903806, by decide⟩ ⟨12, 1, 0, 903806, 371471, 1, 65536⟩
    (by decide) selected_cut_46730

theorem unmarked_context_11_92867_1304093 : frontier 10 ⟨1304093, by decide⟩
    (prefixCache 11 92867) (prefixPartial 11 92867) = false := by
  decide +kernel

theorem node_context_11_92867_1304093 : EJMOriginalGlobalDAGData.nodes 10 ⟨1304093, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨1304044, by decide⟩,⟨1304092, by decide⟩,⟨903806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92867_1304093 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92867 ⟨1304093, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92867
    ⟨1304093, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨1304044, by decide⟩,⟨1304092, by decide⟩,⟨903806, by decide⟩]) unmarked_context_11_92867_1304093 node_context_11_92867_1304093
  intro a
  fin_cases a
  · exact context_12_371468_448748
  · exact context_12_371469_1304044
  · exact context_12_371470_1304092
  · exact context_12_371471_903806

theorem unmarked_context_10_23216_1304094 : frontier 11 ⟨1304094, by decide⟩
    (prefixCache 10 23216) (prefixPartial 10 23216) = false := by
  decide +kernel

theorem node_context_10_23216_1304094 : EJMOriginalGlobalDAGData.nodes 11 ⟨1304094, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨1303798, by decide⟩,⟨1303996, by decide⟩,⟨1304093, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23216_1304094 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23216 ⟨1304094, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23216
    ⟨1304094, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨1303798, by decide⟩,⟨1303996, by decide⟩,⟨1304093, by decide⟩]) unmarked_context_10_23216_1304094 node_context_10_23216_1304094
  intro a
  fin_cases a
  · exact context_11_92864_434745
  · exact context_11_92865_1303798
  · exact context_11_92866_1303996
  · exact context_11_92867_1304093

theorem selected_cut_46731 : selected 9 ⟨1255011, by decide⟩
    (prefixPartial 12 371472) = some ⟨12, 1, 0, 1255011, 371472, 1, 65536⟩ := by
  decide +kernel

theorem context_12_371472_1255011 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371472 ⟨1255011, by decide⟩ :=
  accepted_of_selected 12 371472 ⟨1255011, by decide⟩ ⟨12, 1, 0, 1255011, 371472, 1, 65536⟩
    (by decide) selected_cut_46731

theorem selected_cut_46732 : selected 9 ⟨1304148, by decide⟩
    (prefixPartial 12 371473) = some ⟨12, 2, 0, 1304148, 371473, 3409, 65536⟩ := by
  decide +kernel

theorem context_12_371473_1304148 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371473 ⟨1304148, by decide⟩ :=
  accepted_of_selected 12 371473 ⟨1304148, by decide⟩ ⟨12, 2, 0, 1304148, 371473, 3409, 65536⟩
    (by decide) selected_cut_46732

theorem selected_cut_46733 : selected 9 ⟨1304195, by decide⟩
    (prefixPartial 12 371474) = some ⟨12, 2, 0, 1304195, 371474, 2793, 65536⟩ := by
  decide +kernel

theorem context_12_371474_1304195 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371474 ⟨1304195, by decide⟩ :=
  accepted_of_selected 12 371474 ⟨1304195, by decide⟩ ⟨12, 2, 0, 1304195, 371474, 2793, 65536⟩
    (by decide) selected_cut_46733

theorem selected_cut_46734 : selected 9 ⟨1304250, by decide⟩
    (prefixPartial 12 371475) = some ⟨12, 2, 0, 1304250, 371475, 3301, 65536⟩ := by
  decide +kernel

theorem context_12_371475_1304250 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371475 ⟨1304250, by decide⟩ :=
  accepted_of_selected 12 371475 ⟨1304250, by decide⟩ ⟨12, 2, 0, 1304250, 371475, 3301, 65536⟩
    (by decide) selected_cut_46734

theorem unmarked_context_11_92868_1304251 : frontier 10 ⟨1304251, by decide⟩
    (prefixCache 11 92868) (prefixPartial 11 92868) = false := by
  decide +kernel

theorem node_context_11_92868_1304251 : EJMOriginalGlobalDAGData.nodes 10 ⟨1304251, by decide⟩ =
    .split (coordinate 11) (![⟨1255011, by decide⟩,⟨1304148, by decide⟩,⟨1304195, by decide⟩,⟨1304250, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92868_1304251 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92868 ⟨1304251, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92868
    ⟨1304251, by decide⟩ (by decide) (![⟨1255011, by decide⟩,⟨1304148, by decide⟩,⟨1304195, by decide⟩,⟨1304250, by decide⟩]) unmarked_context_11_92868_1304251 node_context_11_92868_1304251
  intro a
  fin_cases a
  · exact context_12_371472_1255011
  · exact context_12_371473_1304148
  · exact context_12_371474_1304195
  · exact context_12_371475_1304250

theorem selected_cut_46735 : selected 9 ⟨1304306, by decide⟩
    (prefixPartial 12 371476) = some ⟨12, 2, 0, 1304306, 371476, 3253, 65536⟩ := by
  decide +kernel

theorem context_12_371476_1304306 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371476 ⟨1304306, by decide⟩ :=
  accepted_of_selected 12 371476 ⟨1304306, by decide⟩ ⟨12, 2, 0, 1304306, 371476, 3253, 65536⟩
    (by decide) selected_cut_46735

theorem selected_cut_46736 : selected 9 ⟨1118965, by decide⟩
    (prefixPartial 12 371477) = some ⟨12, 1, 0, 1118965, 371477, 1, 65536⟩ := by
  decide +kernel

theorem context_12_371477_1118965 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371477 ⟨1118965, by decide⟩ :=
  accepted_of_selected 12 371477 ⟨1118965, by decide⟩ ⟨12, 1, 0, 1118965, 371477, 1, 65536⟩
    (by decide) selected_cut_46736

theorem selected_cut_46737 : selected 9 ⟨1304350, by decide⟩
    (prefixPartial 12 371478) = some ⟨12, 2, 0, 1304350, 371478, 2837, 65536⟩ := by
  decide +kernel

theorem context_12_371478_1304350 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371478 ⟨1304350, by decide⟩ :=
  accepted_of_selected 12 371478 ⟨1304350, by decide⟩ ⟨12, 2, 0, 1304350, 371478, 2837, 65536⟩
    (by decide) selected_cut_46737

theorem selected_cut_46738 : selected 9 ⟨1304412, by decide⟩
    (prefixPartial 12 371479) = some ⟨12, 2, 0, 1304412, 371479, 3609, 65536⟩ := by
  decide +kernel

theorem context_12_371479_1304412 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371479 ⟨1304412, by decide⟩ :=
  accepted_of_selected 12 371479 ⟨1304412, by decide⟩ ⟨12, 2, 0, 1304412, 371479, 3609, 65536⟩
    (by decide) selected_cut_46738

theorem unmarked_context_11_92869_1304413 : frontier 10 ⟨1304413, by decide⟩
    (prefixCache 11 92869) (prefixPartial 11 92869) = false := by
  decide +kernel

theorem node_context_11_92869_1304413 : EJMOriginalGlobalDAGData.nodes 10 ⟨1304413, by decide⟩ =
    .split (coordinate 11) (![⟨1304306, by decide⟩,⟨1118965, by decide⟩,⟨1304350, by decide⟩,⟨1304412, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92869_1304413 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92869 ⟨1304413, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92869
    ⟨1304413, by decide⟩ (by decide) (![⟨1304306, by decide⟩,⟨1118965, by decide⟩,⟨1304350, by decide⟩,⟨1304412, by decide⟩]) unmarked_context_11_92869_1304413 node_context_11_92869_1304413
  intro a
  fin_cases a
  · exact context_12_371476_1304306
  · exact context_12_371477_1118965
  · exact context_12_371478_1304350
  · exact context_12_371479_1304412

theorem selected_cut_46739 : selected 9 ⟨1304464, by decide⟩
    (prefixPartial 12 371480) = some ⟨12, 2, 0, 1304464, 371480, 2777, 65536⟩ := by
  decide +kernel

theorem context_12_371480_1304464 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371480 ⟨1304464, by decide⟩ :=
  accepted_of_selected 12 371480 ⟨1304464, by decide⟩ ⟨12, 2, 0, 1304464, 371480, 2777, 65536⟩
    (by decide) selected_cut_46739

theorem selected_cut_46740 : selected 9 ⟨1304512, by decide⟩
    (prefixPartial 12 371481) = some ⟨12, 2, 0, 1304512, 371481, 3137, 65536⟩ := by
  decide +kernel

theorem context_12_371481_1304512 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371481 ⟨1304512, by decide⟩ :=
  accepted_of_selected 12 371481 ⟨1304512, by decide⟩ ⟨12, 2, 0, 1304512, 371481, 3137, 65536⟩
    (by decide) selected_cut_46740

theorem selected_cut_46741 : selected 9 ⟨1304552, by decide⟩
    (prefixPartial 12 371482) = some ⟨12, 2, 0, 1304552, 371482, 2521, 65536⟩ := by
  decide +kernel

theorem context_12_371482_1304552 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371482 ⟨1304552, by decide⟩ :=
  accepted_of_selected 12 371482 ⟨1304552, by decide⟩ ⟨12, 2, 0, 1304552, 371482, 2521, 65536⟩
    (by decide) selected_cut_46741

theorem selected_cut_46742 : selected 9 ⟨1304596, by decide⟩
    (prefixPartial 12 371483) = some ⟨12, 2, 0, 1304596, 371483, 3005, 65536⟩ := by
  decide +kernel

theorem context_12_371483_1304596 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371483 ⟨1304596, by decide⟩ :=
  accepted_of_selected 12 371483 ⟨1304596, by decide⟩ ⟨12, 2, 0, 1304596, 371483, 3005, 65536⟩
    (by decide) selected_cut_46742

theorem unmarked_context_11_92870_1304597 : frontier 10 ⟨1304597, by decide⟩
    (prefixCache 11 92870) (prefixPartial 11 92870) = false := by
  decide +kernel

theorem node_context_11_92870_1304597 : EJMOriginalGlobalDAGData.nodes 10 ⟨1304597, by decide⟩ =
    .split (coordinate 11) (![⟨1304464, by decide⟩,⟨1304512, by decide⟩,⟨1304552, by decide⟩,⟨1304596, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92870_1304597 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92870 ⟨1304597, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92870
    ⟨1304597, by decide⟩ (by decide) (![⟨1304464, by decide⟩,⟨1304512, by decide⟩,⟨1304552, by decide⟩,⟨1304596, by decide⟩]) unmarked_context_11_92870_1304597 node_context_11_92870_1304597
  intro a
  fin_cases a
  · exact context_12_371480_1304464
  · exact context_12_371481_1304512
  · exact context_12_371482_1304552
  · exact context_12_371483_1304596

theorem selected_cut_46743 : selected 9 ⟨1304642, by decide⟩
    (prefixPartial 12 371484) = some ⟨12, 2, 0, 1304642, 371484, 2709, 65536⟩ := by
  decide +kernel

theorem context_12_371484_1304642 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371484 ⟨1304642, by decide⟩ :=
  accepted_of_selected 12 371484 ⟨1304642, by decide⟩ ⟨12, 2, 0, 1304642, 371484, 2709, 65536⟩
    (by decide) selected_cut_46743

theorem selected_cut_46744 : selected 9 ⟨1304682, by decide⟩
    (prefixPartial 12 371485) = some ⟨12, 2, 0, 1304682, 371485, 2765, 65536⟩ := by
  decide +kernel

theorem context_12_371485_1304682 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371485 ⟨1304682, by decide⟩ :=
  accepted_of_selected 12 371485 ⟨1304682, by decide⟩ ⟨12, 2, 0, 1304682, 371485, 2765, 65536⟩
    (by decide) selected_cut_46744

theorem selected_cut_46745 : selected 9 ⟨1304721, by decide⟩
    (prefixPartial 12 371486) = some ⟨12, 2, 0, 1304721, 371486, 2537, 65536⟩ := by
  decide +kernel

theorem context_12_371486_1304721 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371486 ⟨1304721, by decide⟩ :=
  accepted_of_selected 12 371486 ⟨1304721, by decide⟩ ⟨12, 2, 0, 1304721, 371486, 2537, 65536⟩
    (by decide) selected_cut_46745

theorem selected_cut_46746 : selected 9 ⟨903806, by decide⟩
    (prefixPartial 12 371487) = some ⟨12, 1, 0, 903806, 371487, 1, 65536⟩ := by
  decide +kernel

theorem context_12_371487_903806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371487 ⟨903806, by decide⟩ :=
  accepted_of_selected 12 371487 ⟨903806, by decide⟩ ⟨12, 1, 0, 903806, 371487, 1, 65536⟩
    (by decide) selected_cut_46746

theorem unmarked_context_11_92871_1304722 : frontier 10 ⟨1304722, by decide⟩
    (prefixCache 11 92871) (prefixPartial 11 92871) = false := by
  decide +kernel

theorem node_context_11_92871_1304722 : EJMOriginalGlobalDAGData.nodes 10 ⟨1304722, by decide⟩ =
    .split (coordinate 11) (![⟨1304642, by decide⟩,⟨1304682, by decide⟩,⟨1304721, by decide⟩,⟨903806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92871_1304722 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92871 ⟨1304722, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92871
    ⟨1304722, by decide⟩ (by decide) (![⟨1304642, by decide⟩,⟨1304682, by decide⟩,⟨1304721, by decide⟩,⟨903806, by decide⟩]) unmarked_context_11_92871_1304722 node_context_11_92871_1304722
  intro a
  fin_cases a
  · exact context_12_371484_1304642
  · exact context_12_371485_1304682
  · exact context_12_371486_1304721
  · exact context_12_371487_903806

theorem unmarked_context_10_23217_1304723 : frontier 11 ⟨1304723, by decide⟩
    (prefixCache 10 23217) (prefixPartial 10 23217) = false := by
  decide +kernel

theorem node_context_10_23217_1304723 : EJMOriginalGlobalDAGData.nodes 11 ⟨1304723, by decide⟩ =
    .split (coordinate 10) (![⟨1304251, by decide⟩,⟨1304413, by decide⟩,⟨1304597, by decide⟩,⟨1304722, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23217_1304723 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23217 ⟨1304723, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23217
    ⟨1304723, by decide⟩ (by decide) (![⟨1304251, by decide⟩,⟨1304413, by decide⟩,⟨1304597, by decide⟩,⟨1304722, by decide⟩]) unmarked_context_10_23217_1304723 node_context_10_23217_1304723
  intro a
  fin_cases a
  · exact context_11_92868_1304251
  · exact context_11_92869_1304413
  · exact context_11_92870_1304597
  · exact context_11_92871_1304722

theorem selected_cut_46747 : selected 9 ⟨435790, by decide⟩
    (prefixPartial 12 371488) = some ⟨12, 1, 0, 435790, 371488, 1, 65536⟩ := by
  decide +kernel

theorem context_12_371488_435790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371488 ⟨435790, by decide⟩ :=
  accepted_of_selected 12 371488 ⟨435790, by decide⟩ ⟨12, 1, 0, 435790, 371488, 1, 65536⟩
    (by decide) selected_cut_46747

theorem selected_cut_46748 : selected 9 ⟨1304761, by decide⟩
    (prefixPartial 12 371489) = some ⟨12, 2, 0, 1304761, 371489, 2689, 65536⟩ := by
  decide +kernel

theorem context_12_371489_1304761 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371489 ⟨1304761, by decide⟩ :=
  accepted_of_selected 12 371489 ⟨1304761, by decide⟩ ⟨12, 2, 0, 1304761, 371489, 2689, 65536⟩
    (by decide) selected_cut_46748

theorem selected_cut_46749 : selected 9 ⟨1304789, by decide⟩
    (prefixPartial 12 371490) = some ⟨12, 2, 0, 1304789, 371490, 2265, 65536⟩ := by
  decide +kernel

theorem context_12_371490_1304789 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371490 ⟨1304789, by decide⟩ :=
  accepted_of_selected 12 371490 ⟨1304789, by decide⟩ ⟨12, 2, 0, 1304789, 371490, 2265, 65536⟩
    (by decide) selected_cut_46749

theorem selected_cut_46750 : selected 9 ⟨1304833, by decide⟩
    (prefixPartial 12 371491) = some ⟨12, 2, 0, 1304833, 371491, 2493, 65536⟩ := by
  decide +kernel

theorem context_12_371491_1304833 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371491 ⟨1304833, by decide⟩ :=
  accepted_of_selected 12 371491 ⟨1304833, by decide⟩ ⟨12, 2, 0, 1304833, 371491, 2493, 65536⟩
    (by decide) selected_cut_46750

theorem unmarked_context_11_92872_1304834 : frontier 10 ⟨1304834, by decide⟩
    (prefixCache 11 92872) (prefixPartial 11 92872) = false := by
  decide +kernel

theorem node_context_11_92872_1304834 : EJMOriginalGlobalDAGData.nodes 10 ⟨1304834, by decide⟩ =
    .split (coordinate 11) (![⟨435790, by decide⟩,⟨1304761, by decide⟩,⟨1304789, by decide⟩,⟨1304833, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92872_1304834 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92872 ⟨1304834, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92872
    ⟨1304834, by decide⟩ (by decide) (![⟨435790, by decide⟩,⟨1304761, by decide⟩,⟨1304789, by decide⟩,⟨1304833, by decide⟩]) unmarked_context_11_92872_1304834 node_context_11_92872_1304834
  intro a
  fin_cases a
  · exact context_12_371488_435790
  · exact context_12_371489_1304761
  · exact context_12_371490_1304789
  · exact context_12_371491_1304833

theorem selected_cut_46751 : selected 9 ⟨1304886, by decide⟩
    (prefixPartial 12 371492) = some ⟨12, 2, 0, 1304886, 371492, 3277, 65536⟩ := by
  decide +kernel

theorem context_12_371492_1304886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371492 ⟨1304886, by decide⟩ :=
  accepted_of_selected 12 371492 ⟨1304886, by decide⟩ ⟨12, 2, 0, 1304886, 371492, 3277, 65536⟩
    (by decide) selected_cut_46751

theorem selected_cut_46752 : selected 9 ⟨1304938, by decide⟩
    (prefixPartial 12 371493) = some ⟨12, 2, 0, 1304938, 371493, 3069, 65536⟩ := by
  decide +kernel

theorem context_12_371493_1304938 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371493 ⟨1304938, by decide⟩ :=
  accepted_of_selected 12 371493 ⟨1304938, by decide⟩ ⟨12, 2, 0, 1304938, 371493, 3069, 65536⟩
    (by decide) selected_cut_46752

theorem selected_cut_46753 : selected 9 ⟨1304976, by decide⟩
    (prefixPartial 12 371494) = some ⟨12, 2, 0, 1304976, 371494, 2425, 65536⟩ := by
  decide +kernel

theorem context_12_371494_1304976 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371494 ⟨1304976, by decide⟩ :=
  accepted_of_selected 12 371494 ⟨1304976, by decide⟩ ⟨12, 2, 0, 1304976, 371494, 2425, 65536⟩
    (by decide) selected_cut_46753

theorem selected_cut_46754 : selected 9 ⟨1305024, by decide⟩
    (prefixPartial 12 371495) = some ⟨12, 2, 0, 1305024, 371495, 2921, 65536⟩ := by
  decide +kernel

theorem context_12_371495_1305024 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371495 ⟨1305024, by decide⟩ :=
  accepted_of_selected 12 371495 ⟨1305024, by decide⟩ ⟨12, 2, 0, 1305024, 371495, 2921, 65536⟩
    (by decide) selected_cut_46754

theorem unmarked_context_11_92873_1305025 : frontier 10 ⟨1305025, by decide⟩
    (prefixCache 11 92873) (prefixPartial 11 92873) = false := by
  decide +kernel

theorem node_context_11_92873_1305025 : EJMOriginalGlobalDAGData.nodes 10 ⟨1305025, by decide⟩ =
    .split (coordinate 11) (![⟨1304886, by decide⟩,⟨1304938, by decide⟩,⟨1304976, by decide⟩,⟨1305024, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92873_1305025 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92873 ⟨1305025, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92873
    ⟨1305025, by decide⟩ (by decide) (![⟨1304886, by decide⟩,⟨1304938, by decide⟩,⟨1304976, by decide⟩,⟨1305024, by decide⟩]) unmarked_context_11_92873_1305025 node_context_11_92873_1305025
  intro a
  fin_cases a
  · exact context_12_371492_1304886
  · exact context_12_371493_1304938
  · exact context_12_371494_1304976
  · exact context_12_371495_1305024

theorem selected_cut_46755 : selected 10 ⟨900587, by decide⟩
    (prefixPartial 11 92874) = some ⟨11, 1, 0, 900587, 92874, 1, 262144⟩ := by
  decide +kernel

theorem context_11_92874_900587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92874 ⟨900587, by decide⟩ :=
  accepted_of_selected 11 92874 ⟨900587, by decide⟩ ⟨11, 1, 0, 900587, 92874, 1, 262144⟩
    (by decide) selected_cut_46755

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
