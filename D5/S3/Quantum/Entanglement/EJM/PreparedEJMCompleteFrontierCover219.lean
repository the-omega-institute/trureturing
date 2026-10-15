/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover218
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_21027 : selected 8 ⟨539380, by decide⟩
    (prefixPartial 13 299127) = some ⟨13, 2, 0, 539380, 299127, 705, 16384⟩ := by
  decide +kernel

theorem context_13_299127_539380 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299127 ⟨539380, by decide⟩ :=
  accepted_of_selected 13 299127 ⟨539380, by decide⟩ ⟨13, 2, 0, 539380, 299127, 705, 16384⟩
    (by decide) selected_cut_21027

theorem unmarked_context_12_74781_539381 : frontier 9 ⟨539381, by decide⟩
    (prefixCache 12 74781) (prefixPartial 12 74781) = false := by
  decide +kernel

theorem node_context_12_74781_539381 : EJMOriginalGlobalDAGData.nodes 9 ⟨539381, by decide⟩ =
    .split (coordinate 12) (![⟨539322, by decide⟩,⟨539353, by decide⟩,⟨539375, by decide⟩,⟨539380, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74781_539381 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74781 ⟨539381, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74781
    ⟨539381, by decide⟩ (by decide) (![⟨539322, by decide⟩,⟨539353, by decide⟩,⟨539375, by decide⟩,⟨539380, by decide⟩]) unmarked_context_12_74781_539381 node_context_12_74781_539381
  intro a
  fin_cases a
  · exact context_13_299124_539322
  · exact context_13_299125_539353
  · exact context_13_299126_539375
  · exact context_13_299127_539380

theorem selected_cut_21028 : selected 8 ⟨539409, by decide⟩
    (prefixPartial 13 299128) = some ⟨13, 2, 0, 539409, 299128, 1113, 16384⟩ := by
  decide +kernel

theorem context_13_299128_539409 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299128 ⟨539409, by decide⟩ :=
  accepted_of_selected 13 299128 ⟨539409, by decide⟩ ⟨13, 2, 0, 539409, 299128, 1113, 16384⟩
    (by decide) selected_cut_21028

theorem selected_cut_21029 : selected 8 ⟨539435, by decide⟩
    (prefixPartial 13 299129) = some ⟨13, 2, 0, 539435, 299129, 2477, 16384⟩ := by
  decide +kernel

theorem context_13_299129_539435 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299129 ⟨539435, by decide⟩ :=
  accepted_of_selected 13 299129 ⟨539435, by decide⟩ ⟨13, 2, 0, 539435, 299129, 2477, 16384⟩
    (by decide) selected_cut_21029

theorem selected_cut_21030 : selected 8 ⟨539456, by decide⟩
    (prefixPartial 13 299130) = some ⟨13, 2, 0, 539456, 299130, 1513, 16384⟩ := by
  decide +kernel

theorem context_13_299130_539456 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299130 ⟨539456, by decide⟩ :=
  accepted_of_selected 13 299130 ⟨539456, by decide⟩ ⟨13, 2, 0, 539456, 299130, 1513, 16384⟩
    (by decide) selected_cut_21030

theorem selected_cut_21031 : selected 8 ⟨539462, by decide⟩
    (prefixPartial 13 299131) = some ⟨13, 2, 0, 539462, 299131, 833, 16384⟩ := by
  decide +kernel

theorem context_13_299131_539462 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299131 ⟨539462, by decide⟩ :=
  accepted_of_selected 13 299131 ⟨539462, by decide⟩ ⟨13, 2, 0, 539462, 299131, 833, 16384⟩
    (by decide) selected_cut_21031

theorem unmarked_context_12_74782_539463 : frontier 9 ⟨539463, by decide⟩
    (prefixCache 12 74782) (prefixPartial 12 74782) = false := by
  decide +kernel

theorem node_context_12_74782_539463 : EJMOriginalGlobalDAGData.nodes 9 ⟨539463, by decide⟩ =
    .split (coordinate 12) (![⟨539409, by decide⟩,⟨539435, by decide⟩,⟨539456, by decide⟩,⟨539462, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74782_539463 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74782 ⟨539463, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74782
    ⟨539463, by decide⟩ (by decide) (![⟨539409, by decide⟩,⟨539435, by decide⟩,⟨539456, by decide⟩,⟨539462, by decide⟩]) unmarked_context_12_74782_539463 node_context_12_74782_539463
  intro a
  fin_cases a
  · exact context_13_299128_539409
  · exact context_13_299129_539435
  · exact context_13_299130_539456
  · exact context_13_299131_539462

theorem selected_cut_21032 : selected 8 ⟨539489, by decide⟩
    (prefixPartial 13 299132) = some ⟨13, 2, 0, 539489, 299132, 1021, 16384⟩ := by
  decide +kernel

theorem context_13_299132_539489 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299132 ⟨539489, by decide⟩ :=
  accepted_of_selected 13 299132 ⟨539489, by decide⟩ ⟨13, 2, 0, 539489, 299132, 1021, 16384⟩
    (by decide) selected_cut_21032

theorem selected_cut_21033 : selected 8 ⟨539519, by decide⟩
    (prefixPartial 13 299133) = some ⟨13, 2, 0, 539519, 299133, 2565, 16384⟩ := by
  decide +kernel

theorem context_13_299133_539519 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299133 ⟨539519, by decide⟩ :=
  accepted_of_selected 13 299133 ⟨539519, by decide⟩ ⟨13, 2, 0, 539519, 299133, 2565, 16384⟩
    (by decide) selected_cut_21033

theorem selected_cut_21034 : selected 8 ⟨539539, by decide⟩
    (prefixPartial 13 299134) = some ⟨13, 2, 0, 539539, 299134, 1765, 16384⟩ := by
  decide +kernel

theorem context_13_299134_539539 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299134 ⟨539539, by decide⟩ :=
  accepted_of_selected 13 299134 ⟨539539, by decide⟩ ⟨13, 2, 0, 539539, 299134, 1765, 16384⟩
    (by decide) selected_cut_21034

theorem selected_cut_21035 : selected 8 ⟨539545, by decide⟩
    (prefixPartial 13 299135) = some ⟨13, 2, 0, 539545, 299135, 709, 16384⟩ := by
  decide +kernel

theorem context_13_299135_539545 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299135 ⟨539545, by decide⟩ :=
  accepted_of_selected 13 299135 ⟨539545, by decide⟩ ⟨13, 2, 0, 539545, 299135, 709, 16384⟩
    (by decide) selected_cut_21035

theorem unmarked_context_12_74783_539546 : frontier 9 ⟨539546, by decide⟩
    (prefixCache 12 74783) (prefixPartial 12 74783) = false := by
  decide +kernel

theorem node_context_12_74783_539546 : EJMOriginalGlobalDAGData.nodes 9 ⟨539546, by decide⟩ =
    .split (coordinate 12) (![⟨539489, by decide⟩,⟨539519, by decide⟩,⟨539539, by decide⟩,⟨539545, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74783_539546 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74783 ⟨539546, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74783
    ⟨539546, by decide⟩ (by decide) (![⟨539489, by decide⟩,⟨539519, by decide⟩,⟨539539, by decide⟩,⟨539545, by decide⟩]) unmarked_context_12_74783_539546 node_context_12_74783_539546
  intro a
  fin_cases a
  · exact context_13_299132_539489
  · exact context_13_299133_539519
  · exact context_13_299134_539539
  · exact context_13_299135_539545

theorem unmarked_context_11_18695_539547 : frontier 10 ⟨539547, by decide⟩
    (prefixCache 11 18695) (prefixPartial 11 18695) = false := by
  decide +kernel

theorem node_context_11_18695_539547 : EJMOriginalGlobalDAGData.nodes 10 ⟨539547, by decide⟩ =
    .split (coordinate 11) (![⟨539296, by decide⟩,⟨539381, by decide⟩,⟨539463, by decide⟩,⟨539546, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18695_539547 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18695 ⟨539547, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18695
    ⟨539547, by decide⟩ (by decide) (![⟨539296, by decide⟩,⟨539381, by decide⟩,⟨539463, by decide⟩,⟨539546, by decide⟩]) unmarked_context_11_18695_539547 node_context_11_18695_539547
  intro a
  fin_cases a
  · exact context_12_74780_539296
  · exact context_12_74781_539381
  · exact context_12_74782_539463
  · exact context_12_74783_539546

theorem unmarked_context_10_4673_539548 : frontier 11 ⟨539548, by decide⟩
    (prefixCache 10 4673) (prefixPartial 10 4673) = false := by
  decide +kernel

theorem node_context_10_4673_539548 : EJMOriginalGlobalDAGData.nodes 11 ⟨539548, by decide⟩ =
    .split (coordinate 10) (![⟨538766, by decide⟩,⟨539046, by decide⟩,⟨539295, by decide⟩,⟨539547, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4673_539548 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4673 ⟨539548, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4673
    ⟨539548, by decide⟩ (by decide) (![⟨538766, by decide⟩,⟨539046, by decide⟩,⟨539295, by decide⟩,⟨539547, by decide⟩]) unmarked_context_10_4673_539548 node_context_10_4673_539548
  intro a
  fin_cases a
  · exact context_11_18692_538766
  · exact context_11_18693_539046
  · exact context_11_18694_539295
  · exact context_11_18695_539547

theorem selected_cut_21036 : selected 9 ⟨435790, by decide⟩
    (prefixPartial 12 74784) = some ⟨12, 1, 0, 435790, 74784, 1, 65536⟩ := by
  decide +kernel

theorem context_12_74784_435790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74784 ⟨435790, by decide⟩ :=
  accepted_of_selected 12 74784 ⟨435790, by decide⟩ ⟨12, 1, 0, 435790, 74784, 1, 65536⟩
    (by decide) selected_cut_21036

theorem selected_cut_21037 : selected 8 ⟨539567, by decide⟩
    (prefixPartial 13 299140) = some ⟨13, 2, 0, 539567, 299140, 849, 16384⟩ := by
  decide +kernel

theorem context_13_299140_539567 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299140 ⟨539567, by decide⟩ :=
  accepted_of_selected 13 299140 ⟨539567, by decide⟩ ⟨13, 2, 0, 539567, 299140, 849, 16384⟩
    (by decide) selected_cut_21037

theorem selected_cut_21038 : selected 8 ⟨539588, by decide⟩
    (prefixPartial 13 299141) = some ⟨13, 2, 0, 539588, 299141, 1709, 16384⟩ := by
  decide +kernel

theorem context_13_299141_539588 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299141 ⟨539588, by decide⟩ :=
  accepted_of_selected 13 299141 ⟨539588, by decide⟩ ⟨13, 2, 0, 539588, 299141, 1709, 16384⟩
    (by decide) selected_cut_21038

theorem selected_cut_21039 : selected 8 ⟨539603, by decide⟩
    (prefixPartial 13 299142) = some ⟨13, 2, 0, 539603, 299142, 1085, 16384⟩ := by
  decide +kernel

theorem context_13_299142_539603 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299142 ⟨539603, by decide⟩ :=
  accepted_of_selected 13 299142 ⟨539603, by decide⟩ ⟨13, 2, 0, 539603, 299142, 1085, 16384⟩
    (by decide) selected_cut_21039

theorem selected_cut_21040 : selected 8 ⟨539608, by decide⟩
    (prefixPartial 13 299143) = some ⟨13, 2, 0, 539608, 299143, 709, 16384⟩ := by
  decide +kernel

theorem context_13_299143_539608 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299143 ⟨539608, by decide⟩ :=
  accepted_of_selected 13 299143 ⟨539608, by decide⟩ ⟨13, 2, 0, 539608, 299143, 709, 16384⟩
    (by decide) selected_cut_21040

theorem unmarked_context_12_74785_539609 : frontier 9 ⟨539609, by decide⟩
    (prefixCache 12 74785) (prefixPartial 12 74785) = false := by
  decide +kernel

theorem node_context_12_74785_539609 : EJMOriginalGlobalDAGData.nodes 9 ⟨539609, by decide⟩ =
    .split (coordinate 12) (![⟨539567, by decide⟩,⟨539588, by decide⟩,⟨539603, by decide⟩,⟨539608, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74785_539609 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74785 ⟨539609, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74785
    ⟨539609, by decide⟩ (by decide) (![⟨539567, by decide⟩,⟨539588, by decide⟩,⟨539603, by decide⟩,⟨539608, by decide⟩]) unmarked_context_12_74785_539609 node_context_12_74785_539609
  intro a
  fin_cases a
  · exact context_13_299140_539567
  · exact context_13_299141_539588
  · exact context_13_299142_539603
  · exact context_13_299143_539608

theorem selected_cut_21041 : selected 8 ⟨539627, by decide⟩
    (prefixPartial 13 299144) = some ⟨13, 2, 0, 539627, 299144, 913, 16384⟩ := by
  decide +kernel

theorem context_13_299144_539627 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299144 ⟨539627, by decide⟩ :=
  accepted_of_selected 13 299144 ⟨539627, by decide⟩ ⟨13, 2, 0, 539627, 299144, 913, 16384⟩
    (by decide) selected_cut_21041

theorem selected_cut_21042 : selected 8 ⟨539650, by decide⟩
    (prefixPartial 13 299145) = some ⟨13, 2, 0, 539650, 299145, 1645, 16384⟩ := by
  decide +kernel

theorem context_13_299145_539650 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299145 ⟨539650, by decide⟩ :=
  accepted_of_selected 13 299145 ⟨539650, by decide⟩ ⟨13, 2, 0, 539650, 299145, 1645, 16384⟩
    (by decide) selected_cut_21042

theorem selected_cut_21043 : selected 8 ⟨539664, by decide⟩
    (prefixPartial 13 299146) = some ⟨13, 2, 0, 539664, 299146, 1073, 16384⟩ := by
  decide +kernel

theorem context_13_299146_539664 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299146 ⟨539664, by decide⟩ :=
  accepted_of_selected 13 299146 ⟨539664, by decide⟩ ⟨13, 2, 0, 539664, 299146, 1073, 16384⟩
    (by decide) selected_cut_21043

theorem selected_cut_21044 : selected 8 ⟨539671, by decide⟩
    (prefixPartial 13 299147) = some ⟨13, 2, 0, 539671, 299147, 697, 16384⟩ := by
  decide +kernel

theorem context_13_299147_539671 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299147 ⟨539671, by decide⟩ :=
  accepted_of_selected 13 299147 ⟨539671, by decide⟩ ⟨13, 2, 0, 539671, 299147, 697, 16384⟩
    (by decide) selected_cut_21044

theorem unmarked_context_12_74786_539672 : frontier 9 ⟨539672, by decide⟩
    (prefixCache 12 74786) (prefixPartial 12 74786) = false := by
  decide +kernel

theorem node_context_12_74786_539672 : EJMOriginalGlobalDAGData.nodes 9 ⟨539672, by decide⟩ =
    .split (coordinate 12) (![⟨539627, by decide⟩,⟨539650, by decide⟩,⟨539664, by decide⟩,⟨539671, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74786_539672 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74786 ⟨539672, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74786
    ⟨539672, by decide⟩ (by decide) (![⟨539627, by decide⟩,⟨539650, by decide⟩,⟨539664, by decide⟩,⟨539671, by decide⟩]) unmarked_context_12_74786_539672 node_context_12_74786_539672
  intro a
  fin_cases a
  · exact context_13_299144_539627
  · exact context_13_299145_539650
  · exact context_13_299146_539664
  · exact context_13_299147_539671

theorem selected_cut_21045 : selected 8 ⟨539693, by decide⟩
    (prefixPartial 13 299148) = some ⟨13, 2, 0, 539693, 299148, 933, 16384⟩ := by
  decide +kernel

theorem context_13_299148_539693 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299148 ⟨539693, by decide⟩ :=
  accepted_of_selected 13 299148 ⟨539693, by decide⟩ ⟨13, 2, 0, 539693, 299148, 933, 16384⟩
    (by decide) selected_cut_21045

theorem selected_cut_21046 : selected 8 ⟨539716, by decide⟩
    (prefixPartial 13 299149) = some ⟨13, 2, 0, 539716, 299149, 1937, 16384⟩ := by
  decide +kernel

theorem context_13_299149_539716 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299149 ⟨539716, by decide⟩ :=
  accepted_of_selected 13 299149 ⟨539716, by decide⟩ ⟨13, 2, 0, 539716, 299149, 1937, 16384⟩
    (by decide) selected_cut_21046

theorem selected_cut_21047 : selected 8 ⟨539735, by decide⟩
    (prefixPartial 13 299150) = some ⟨13, 2, 0, 539735, 299150, 1245, 16384⟩ := by
  decide +kernel

theorem context_13_299150_539735 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299150 ⟨539735, by decide⟩ :=
  accepted_of_selected 13 299150 ⟨539735, by decide⟩ ⟨13, 2, 0, 539735, 299150, 1245, 16384⟩
    (by decide) selected_cut_21047

theorem selected_cut_21048 : selected 8 ⟨539740, by decide⟩
    (prefixPartial 13 299151) = some ⟨13, 2, 0, 539740, 299151, 661, 16384⟩ := by
  decide +kernel

theorem context_13_299151_539740 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299151 ⟨539740, by decide⟩ :=
  accepted_of_selected 13 299151 ⟨539740, by decide⟩ ⟨13, 2, 0, 539740, 299151, 661, 16384⟩
    (by decide) selected_cut_21048

theorem unmarked_context_12_74787_539741 : frontier 9 ⟨539741, by decide⟩
    (prefixCache 12 74787) (prefixPartial 12 74787) = false := by
  decide +kernel

theorem node_context_12_74787_539741 : EJMOriginalGlobalDAGData.nodes 9 ⟨539741, by decide⟩ =
    .split (coordinate 12) (![⟨539693, by decide⟩,⟨539716, by decide⟩,⟨539735, by decide⟩,⟨539740, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74787_539741 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74787 ⟨539741, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74787
    ⟨539741, by decide⟩ (by decide) (![⟨539693, by decide⟩,⟨539716, by decide⟩,⟨539735, by decide⟩,⟨539740, by decide⟩]) unmarked_context_12_74787_539741 node_context_12_74787_539741
  intro a
  fin_cases a
  · exact context_13_299148_539693
  · exact context_13_299149_539716
  · exact context_13_299150_539735
  · exact context_13_299151_539740

theorem unmarked_context_11_18696_539742 : frontier 10 ⟨539742, by decide⟩
    (prefixCache 11 18696) (prefixPartial 11 18696) = false := by
  decide +kernel

theorem node_context_11_18696_539742 : EJMOriginalGlobalDAGData.nodes 10 ⟨539742, by decide⟩ =
    .split (coordinate 11) (![⟨435790, by decide⟩,⟨539609, by decide⟩,⟨539672, by decide⟩,⟨539741, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18696_539742 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18696 ⟨539742, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18696
    ⟨539742, by decide⟩ (by decide) (![⟨435790, by decide⟩,⟨539609, by decide⟩,⟨539672, by decide⟩,⟨539741, by decide⟩]) unmarked_context_11_18696_539742 node_context_11_18696_539742
  intro a
  fin_cases a
  · exact context_12_74784_435790
  · exact context_12_74785_539609
  · exact context_12_74786_539672
  · exact context_12_74787_539741

theorem selected_cut_21049 : selected 9 ⟨450498, by decide⟩
    (prefixPartial 12 74788) = some ⟨12, 1, 0, 450498, 74788, 1, 65536⟩ := by
  decide +kernel

theorem context_12_74788_450498 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74788 ⟨450498, by decide⟩ :=
  accepted_of_selected 12 74788 ⟨450498, by decide⟩ ⟨12, 1, 0, 450498, 74788, 1, 65536⟩
    (by decide) selected_cut_21049

theorem selected_cut_21050 : selected 8 ⟨539758, by decide⟩
    (prefixPartial 13 299156) = some ⟨13, 2, 0, 539758, 299156, 793, 16384⟩ := by
  decide +kernel

theorem context_13_299156_539758 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299156 ⟨539758, by decide⟩ :=
  accepted_of_selected 13 299156 ⟨539758, by decide⟩ ⟨13, 2, 0, 539758, 299156, 793, 16384⟩
    (by decide) selected_cut_21050

theorem selected_cut_21051 : selected 8 ⟨539780, by decide⟩
    (prefixPartial 13 299157) = some ⟨13, 2, 0, 539780, 299157, 1893, 16384⟩ := by
  decide +kernel

theorem context_13_299157_539780 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299157 ⟨539780, by decide⟩ :=
  accepted_of_selected 13 299157 ⟨539780, by decide⟩ ⟨13, 2, 0, 539780, 299157, 1893, 16384⟩
    (by decide) selected_cut_21051

theorem selected_cut_21052 : selected 8 ⟨539797, by decide⟩
    (prefixPartial 13 299158) = some ⟨13, 2, 0, 539797, 299158, 1273, 16384⟩ := by
  decide +kernel

theorem context_13_299158_539797 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299158 ⟨539797, by decide⟩ :=
  accepted_of_selected 13 299158 ⟨539797, by decide⟩ ⟨13, 2, 0, 539797, 299158, 1273, 16384⟩
    (by decide) selected_cut_21052

theorem selected_cut_21053 : selected 8 ⟨539801, by decide⟩
    (prefixPartial 13 299159) = some ⟨13, 2, 0, 539801, 299159, 785, 16384⟩ := by
  decide +kernel

theorem context_13_299159_539801 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299159 ⟨539801, by decide⟩ :=
  accepted_of_selected 13 299159 ⟨539801, by decide⟩ ⟨13, 2, 0, 539801, 299159, 785, 16384⟩
    (by decide) selected_cut_21053

theorem unmarked_context_12_74789_539802 : frontier 9 ⟨539802, by decide⟩
    (prefixCache 12 74789) (prefixPartial 12 74789) = false := by
  decide +kernel

theorem node_context_12_74789_539802 : EJMOriginalGlobalDAGData.nodes 9 ⟨539802, by decide⟩ =
    .split (coordinate 12) (![⟨539758, by decide⟩,⟨539780, by decide⟩,⟨539797, by decide⟩,⟨539801, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74789_539802 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74789 ⟨539802, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74789
    ⟨539802, by decide⟩ (by decide) (![⟨539758, by decide⟩,⟨539780, by decide⟩,⟨539797, by decide⟩,⟨539801, by decide⟩]) unmarked_context_12_74789_539802 node_context_12_74789_539802
  intro a
  fin_cases a
  · exact context_13_299156_539758
  · exact context_13_299157_539780
  · exact context_13_299158_539797
  · exact context_13_299159_539801

theorem selected_cut_21054 : selected 8 ⟨539822, by decide⟩
    (prefixPartial 13 299160) = some ⟨13, 2, 0, 539822, 299160, 953, 16384⟩ := by
  decide +kernel

theorem context_13_299160_539822 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299160 ⟨539822, by decide⟩ :=
  accepted_of_selected 13 299160 ⟨539822, by decide⟩ ⟨13, 2, 0, 539822, 299160, 953, 16384⟩
    (by decide) selected_cut_21054

theorem selected_cut_21055 : selected 8 ⟨539853, by decide⟩
    (prefixPartial 13 299161) = some ⟨13, 2, 0, 539853, 299161, 2033, 16384⟩ := by
  decide +kernel

theorem context_13_299161_539853 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299161 ⟨539853, by decide⟩ :=
  accepted_of_selected 13 299161 ⟨539853, by decide⟩ ⟨13, 2, 0, 539853, 299161, 2033, 16384⟩
    (by decide) selected_cut_21055

theorem selected_cut_21056 : selected 8 ⟨539871, by decide⟩
    (prefixPartial 13 299162) = some ⟨13, 2, 0, 539871, 299162, 1385, 16384⟩ := by
  decide +kernel

theorem context_13_299162_539871 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299162 ⟨539871, by decide⟩ :=
  accepted_of_selected 13 299162 ⟨539871, by decide⟩ ⟨13, 2, 0, 539871, 299162, 1385, 16384⟩
    (by decide) selected_cut_21056

theorem selected_cut_21057 : selected 8 ⟨539879, by decide⟩
    (prefixPartial 13 299163) = some ⟨13, 2, 0, 539879, 299163, 869, 16384⟩ := by
  decide +kernel

theorem context_13_299163_539879 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299163 ⟨539879, by decide⟩ :=
  accepted_of_selected 13 299163 ⟨539879, by decide⟩ ⟨13, 2, 0, 539879, 299163, 869, 16384⟩
    (by decide) selected_cut_21057

theorem unmarked_context_12_74790_539880 : frontier 9 ⟨539880, by decide⟩
    (prefixCache 12 74790) (prefixPartial 12 74790) = false := by
  decide +kernel

theorem node_context_12_74790_539880 : EJMOriginalGlobalDAGData.nodes 9 ⟨539880, by decide⟩ =
    .split (coordinate 12) (![⟨539822, by decide⟩,⟨539853, by decide⟩,⟨539871, by decide⟩,⟨539879, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74790_539880 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74790 ⟨539880, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74790
    ⟨539880, by decide⟩ (by decide) (![⟨539822, by decide⟩,⟨539853, by decide⟩,⟨539871, by decide⟩,⟨539879, by decide⟩]) unmarked_context_12_74790_539880 node_context_12_74790_539880
  intro a
  fin_cases a
  · exact context_13_299160_539822
  · exact context_13_299161_539853
  · exact context_13_299162_539871
  · exact context_13_299163_539879

theorem selected_cut_21058 : selected 8 ⟨539904, by decide⟩
    (prefixPartial 13 299164) = some ⟨13, 2, 0, 539904, 299164, 1009, 16384⟩ := by
  decide +kernel

theorem context_13_299164_539904 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299164 ⟨539904, by decide⟩ :=
  accepted_of_selected 13 299164 ⟨539904, by decide⟩ ⟨13, 2, 0, 539904, 299164, 1009, 16384⟩
    (by decide) selected_cut_21058

theorem selected_cut_21059 : selected 8 ⟨539934, by decide⟩
    (prefixPartial 13 299165) = some ⟨13, 2, 0, 539934, 299165, 2305, 16384⟩ := by
  decide +kernel

theorem context_13_299165_539934 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299165 ⟨539934, by decide⟩ :=
  accepted_of_selected 13 299165 ⟨539934, by decide⟩ ⟨13, 2, 0, 539934, 299165, 2305, 16384⟩
    (by decide) selected_cut_21059

theorem selected_cut_21060 : selected 8 ⟨539958, by decide⟩
    (prefixPartial 13 299166) = some ⟨13, 2, 0, 539958, 299166, 1669, 16384⟩ := by
  decide +kernel

theorem context_13_299166_539958 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299166 ⟨539958, by decide⟩ :=
  accepted_of_selected 13 299166 ⟨539958, by decide⟩ ⟨13, 2, 0, 539958, 299166, 1669, 16384⟩
    (by decide) selected_cut_21060

theorem selected_cut_21061 : selected 8 ⟨539965, by decide⟩
    (prefixPartial 13 299167) = some ⟨13, 2, 0, 539965, 299167, 869, 16384⟩ := by
  decide +kernel

theorem context_13_299167_539965 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299167 ⟨539965, by decide⟩ :=
  accepted_of_selected 13 299167 ⟨539965, by decide⟩ ⟨13, 2, 0, 539965, 299167, 869, 16384⟩
    (by decide) selected_cut_21061

theorem unmarked_context_12_74791_539966 : frontier 9 ⟨539966, by decide⟩
    (prefixCache 12 74791) (prefixPartial 12 74791) = false := by
  decide +kernel

theorem node_context_12_74791_539966 : EJMOriginalGlobalDAGData.nodes 9 ⟨539966, by decide⟩ =
    .split (coordinate 12) (![⟨539904, by decide⟩,⟨539934, by decide⟩,⟨539958, by decide⟩,⟨539965, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74791_539966 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74791 ⟨539966, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74791
    ⟨539966, by decide⟩ (by decide) (![⟨539904, by decide⟩,⟨539934, by decide⟩,⟨539958, by decide⟩,⟨539965, by decide⟩]) unmarked_context_12_74791_539966 node_context_12_74791_539966
  intro a
  fin_cases a
  · exact context_13_299164_539904
  · exact context_13_299165_539934
  · exact context_13_299166_539958
  · exact context_13_299167_539965

theorem unmarked_context_11_18697_539967 : frontier 10 ⟨539967, by decide⟩
    (prefixCache 11 18697) (prefixPartial 11 18697) = false := by
  decide +kernel

theorem node_context_11_18697_539967 : EJMOriginalGlobalDAGData.nodes 10 ⟨539967, by decide⟩ =
    .split (coordinate 11) (![⟨450498, by decide⟩,⟨539802, by decide⟩,⟨539880, by decide⟩,⟨539966, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18697_539967 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18697 ⟨539967, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18697
    ⟨539967, by decide⟩ (by decide) (![⟨450498, by decide⟩,⟨539802, by decide⟩,⟨539880, by decide⟩,⟨539966, by decide⟩]) unmarked_context_11_18697_539967 node_context_11_18697_539967
  intro a
  fin_cases a
  · exact context_12_74788_450498
  · exact context_12_74789_539802
  · exact context_12_74790_539880
  · exact context_12_74791_539966

theorem selected_cut_21062 : selected 9 ⟨435790, by decide⟩
    (prefixPartial 12 74792) = some ⟨12, 1, 0, 435790, 74792, 1, 65536⟩ := by
  decide +kernel

theorem context_12_74792_435790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74792 ⟨435790, by decide⟩ :=
  accepted_of_selected 12 74792 ⟨435790, by decide⟩ ⟨12, 1, 0, 435790, 74792, 1, 65536⟩
    (by decide) selected_cut_21062

theorem selected_cut_21063 : selected 8 ⟨539982, by decide⟩
    (prefixPartial 13 299172) = some ⟨13, 2, 0, 539982, 299172, 761, 16384⟩ := by
  decide +kernel

theorem context_13_299172_539982 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299172 ⟨539982, by decide⟩ :=
  accepted_of_selected 13 299172 ⟨539982, by decide⟩ ⟨13, 2, 0, 539982, 299172, 761, 16384⟩
    (by decide) selected_cut_21063

theorem selected_cut_21064 : selected 8 ⟨540010, by decide⟩
    (prefixPartial 13 299173) = some ⟨13, 2, 0, 540010, 299173, 2225, 16384⟩ := by
  decide +kernel

theorem context_13_299173_540010 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299173 ⟨540010, by decide⟩ :=
  accepted_of_selected 13 299173 ⟨540010, by decide⟩ ⟨13, 2, 0, 540010, 299173, 2225, 16384⟩
    (by decide) selected_cut_21064

theorem selected_cut_21065 : selected 8 ⟨540029, by decide⟩
    (prefixPartial 13 299174) = some ⟨13, 2, 0, 540029, 299174, 1453, 16384⟩ := by
  decide +kernel

theorem context_13_299174_540029 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299174 ⟨540029, by decide⟩ :=
  accepted_of_selected 13 299174 ⟨540029, by decide⟩ ⟨13, 2, 0, 540029, 299174, 1453, 16384⟩
    (by decide) selected_cut_21065

theorem selected_cut_21066 : selected 8 ⟨540034, by decide⟩
    (prefixPartial 13 299175) = some ⟨13, 2, 0, 540034, 299175, 857, 16384⟩ := by
  decide +kernel

theorem context_13_299175_540034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299175 ⟨540034, by decide⟩ :=
  accepted_of_selected 13 299175 ⟨540034, by decide⟩ ⟨13, 2, 0, 540034, 299175, 857, 16384⟩
    (by decide) selected_cut_21066

theorem unmarked_context_12_74793_540035 : frontier 9 ⟨540035, by decide⟩
    (prefixCache 12 74793) (prefixPartial 12 74793) = false := by
  decide +kernel

theorem node_context_12_74793_540035 : EJMOriginalGlobalDAGData.nodes 9 ⟨540035, by decide⟩ =
    .split (coordinate 12) (![⟨539982, by decide⟩,⟨540010, by decide⟩,⟨540029, by decide⟩,⟨540034, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74793_540035 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74793 ⟨540035, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74793
    ⟨540035, by decide⟩ (by decide) (![⟨539982, by decide⟩,⟨540010, by decide⟩,⟨540029, by decide⟩,⟨540034, by decide⟩]) unmarked_context_12_74793_540035 node_context_12_74793_540035
  intro a
  fin_cases a
  · exact context_13_299172_539982
  · exact context_13_299173_540010
  · exact context_13_299174_540029
  · exact context_13_299175_540034

theorem selected_cut_21067 : selected 8 ⟨540049, by decide⟩
    (prefixPartial 13 299176) = some ⟨13, 2, 0, 540049, 299176, 677, 16384⟩ := by
  decide +kernel

theorem context_13_299176_540049 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299176 ⟨540049, by decide⟩ :=
  accepted_of_selected 13 299176 ⟨540049, by decide⟩ ⟨13, 2, 0, 540049, 299176, 677, 16384⟩
    (by decide) selected_cut_21067

theorem selected_cut_21068 : selected 8 ⟨540079, by decide⟩
    (prefixPartial 13 299177) = some ⟨13, 2, 0, 540079, 299177, 2073, 16384⟩ := by
  decide +kernel

theorem context_13_299177_540079 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299177 ⟨540079, by decide⟩ :=
  accepted_of_selected 13 299177 ⟨540079, by decide⟩ ⟨13, 2, 0, 540079, 299177, 2073, 16384⟩
    (by decide) selected_cut_21068

theorem selected_cut_21069 : selected 8 ⟨540097, by decide⟩
    (prefixPartial 13 299178) = some ⟨13, 2, 0, 540097, 299178, 1325, 16384⟩ := by
  decide +kernel

theorem context_13_299178_540097 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299178 ⟨540097, by decide⟩ :=
  accepted_of_selected 13 299178 ⟨540097, by decide⟩ ⟨13, 2, 0, 540097, 299178, 1325, 16384⟩
    (by decide) selected_cut_21069

theorem selected_cut_21070 : selected 8 ⟨540103, by decide⟩
    (prefixPartial 13 299179) = some ⟨13, 2, 0, 540103, 299179, 813, 16384⟩ := by
  decide +kernel

theorem context_13_299179_540103 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299179 ⟨540103, by decide⟩ :=
  accepted_of_selected 13 299179 ⟨540103, by decide⟩ ⟨13, 2, 0, 540103, 299179, 813, 16384⟩
    (by decide) selected_cut_21070

theorem unmarked_context_12_74794_540104 : frontier 9 ⟨540104, by decide⟩
    (prefixCache 12 74794) (prefixPartial 12 74794) = false := by
  decide +kernel

theorem node_context_12_74794_540104 : EJMOriginalGlobalDAGData.nodes 9 ⟨540104, by decide⟩ =
    .split (coordinate 12) (![⟨540049, by decide⟩,⟨540079, by decide⟩,⟨540097, by decide⟩,⟨540103, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74794_540104 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74794 ⟨540104, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74794
    ⟨540104, by decide⟩ (by decide) (![⟨540049, by decide⟩,⟨540079, by decide⟩,⟨540097, by decide⟩,⟨540103, by decide⟩]) unmarked_context_12_74794_540104 node_context_12_74794_540104
  intro a
  fin_cases a
  · exact context_13_299176_540049
  · exact context_13_299177_540079
  · exact context_13_299178_540097
  · exact context_13_299179_540103

theorem selected_cut_21071 : selected 8 ⟨540126, by decide⟩
    (prefixPartial 13 299180) = some ⟨13, 2, 0, 540126, 299180, 761, 16384⟩ := by
  decide +kernel

theorem context_13_299180_540126 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299180 ⟨540126, by decide⟩ :=
  accepted_of_selected 13 299180 ⟨540126, by decide⟩ ⟨13, 2, 0, 540126, 299180, 761, 16384⟩
    (by decide) selected_cut_21071

theorem selected_cut_21072 : selected 8 ⟨540159, by decide⟩
    (prefixPartial 13 299181) = some ⟨13, 2, 0, 540159, 299181, 2589, 16384⟩ := by
  decide +kernel

theorem context_13_299181_540159 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299181 ⟨540159, by decide⟩ :=
  accepted_of_selected 13 299181 ⟨540159, by decide⟩ ⟨13, 2, 0, 540159, 299181, 2589, 16384⟩
    (by decide) selected_cut_21072

theorem selected_cut_21073 : selected 8 ⟨540178, by decide⟩
    (prefixPartial 13 299182) = some ⟨13, 2, 0, 540178, 299182, 1529, 16384⟩ := by
  decide +kernel

theorem context_13_299182_540178 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299182 ⟨540178, by decide⟩ :=
  accepted_of_selected 13 299182 ⟨540178, by decide⟩ ⟨13, 2, 0, 540178, 299182, 1529, 16384⟩
    (by decide) selected_cut_21073

theorem selected_cut_21074 : selected 8 ⟨540186, by decide⟩
    (prefixPartial 13 299183) = some ⟨13, 2, 0, 540186, 299183, 797, 16384⟩ := by
  decide +kernel

theorem context_13_299183_540186 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299183 ⟨540186, by decide⟩ :=
  accepted_of_selected 13 299183 ⟨540186, by decide⟩ ⟨13, 2, 0, 540186, 299183, 797, 16384⟩
    (by decide) selected_cut_21074

theorem unmarked_context_12_74795_540187 : frontier 9 ⟨540187, by decide⟩
    (prefixCache 12 74795) (prefixPartial 12 74795) = false := by
  decide +kernel

theorem node_context_12_74795_540187 : EJMOriginalGlobalDAGData.nodes 9 ⟨540187, by decide⟩ =
    .split (coordinate 12) (![⟨540126, by decide⟩,⟨540159, by decide⟩,⟨540178, by decide⟩,⟨540186, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74795_540187 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74795 ⟨540187, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74795
    ⟨540187, by decide⟩ (by decide) (![⟨540126, by decide⟩,⟨540159, by decide⟩,⟨540178, by decide⟩,⟨540186, by decide⟩]) unmarked_context_12_74795_540187 node_context_12_74795_540187
  intro a
  fin_cases a
  · exact context_13_299180_540126
  · exact context_13_299181_540159
  · exact context_13_299182_540178
  · exact context_13_299183_540186

theorem unmarked_context_11_18698_540188 : frontier 10 ⟨540188, by decide⟩
    (prefixCache 11 18698) (prefixPartial 11 18698) = false := by
  decide +kernel

theorem node_context_11_18698_540188 : EJMOriginalGlobalDAGData.nodes 10 ⟨540188, by decide⟩ =
    .split (coordinate 11) (![⟨435790, by decide⟩,⟨540035, by decide⟩,⟨540104, by decide⟩,⟨540187, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18698_540188 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18698 ⟨540188, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18698
    ⟨540188, by decide⟩ (by decide) (![⟨435790, by decide⟩,⟨540035, by decide⟩,⟨540104, by decide⟩,⟨540187, by decide⟩]) unmarked_context_11_18698_540188 node_context_11_18698_540188
  intro a
  fin_cases a
  · exact context_12_74792_435790
  · exact context_12_74793_540035
  · exact context_12_74794_540104
  · exact context_12_74795_540187

theorem selected_cut_21075 : selected 9 ⟨540189, by decide⟩
    (prefixPartial 12 74796) = some ⟨12, 1, 0, 540189, 74796, 1, 65536⟩ := by
  decide +kernel

theorem context_12_74796_540189 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74796 ⟨540189, by decide⟩ :=
  accepted_of_selected 12 74796 ⟨540189, by decide⟩ ⟨12, 1, 0, 540189, 74796, 1, 65536⟩
    (by decide) selected_cut_21075

theorem selected_cut_21076 : selected 8 ⟨540202, by decide⟩
    (prefixPartial 13 299188) = some ⟨13, 2, 0, 540202, 299188, 597, 16384⟩ := by
  decide +kernel

theorem context_13_299188_540202 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299188 ⟨540202, by decide⟩ :=
  accepted_of_selected 13 299188 ⟨540202, by decide⟩ ⟨13, 2, 0, 540202, 299188, 597, 16384⟩
    (by decide) selected_cut_21076

theorem selected_cut_21077 : selected 8 ⟨540237, by decide⟩
    (prefixPartial 13 299189) = some ⟨13, 2, 0, 540237, 299189, 2705, 16384⟩ := by
  decide +kernel

theorem context_13_299189_540237 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299189 ⟨540237, by decide⟩ :=
  accepted_of_selected 13 299189 ⟨540237, by decide⟩ ⟨13, 2, 0, 540237, 299189, 2705, 16384⟩
    (by decide) selected_cut_21077

theorem selected_cut_21078 : selected 8 ⟨540254, by decide⟩
    (prefixPartial 13 299190) = some ⟨13, 2, 0, 540254, 299190, 1405, 16384⟩ := by
  decide +kernel

theorem context_13_299190_540254 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299190 ⟨540254, by decide⟩ :=
  accepted_of_selected 13 299190 ⟨540254, by decide⟩ ⟨13, 2, 0, 540254, 299190, 1405, 16384⟩
    (by decide) selected_cut_21078

theorem selected_cut_21079 : selected 8 ⟨540259, by decide⟩
    (prefixPartial 13 299191) = some ⟨13, 2, 0, 540259, 299191, 781, 16384⟩ := by
  decide +kernel

theorem context_13_299191_540259 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299191 ⟨540259, by decide⟩ :=
  accepted_of_selected 13 299191 ⟨540259, by decide⟩ ⟨13, 2, 0, 540259, 299191, 781, 16384⟩
    (by decide) selected_cut_21079

theorem unmarked_context_12_74797_540260 : frontier 9 ⟨540260, by decide⟩
    (prefixCache 12 74797) (prefixPartial 12 74797) = false := by
  decide +kernel

theorem node_context_12_74797_540260 : EJMOriginalGlobalDAGData.nodes 9 ⟨540260, by decide⟩ =
    .split (coordinate 12) (![⟨540202, by decide⟩,⟨540237, by decide⟩,⟨540254, by decide⟩,⟨540259, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74797_540260 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74797 ⟨540260, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74797
    ⟨540260, by decide⟩ (by decide) (![⟨540202, by decide⟩,⟨540237, by decide⟩,⟨540254, by decide⟩,⟨540259, by decide⟩]) unmarked_context_12_74797_540260 node_context_12_74797_540260
  intro a
  fin_cases a
  · exact context_13_299188_540202
  · exact context_13_299189_540237
  · exact context_13_299190_540254
  · exact context_13_299191_540259

theorem selected_cut_21080 : selected 8 ⟨540274, by decide⟩
    (prefixPartial 13 299192) = some ⟨13, 2, 0, 540274, 299192, 609, 16384⟩ := by
  decide +kernel

theorem context_13_299192_540274 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299192 ⟨540274, by decide⟩ :=
  accepted_of_selected 13 299192 ⟨540274, by decide⟩ ⟨13, 2, 0, 540274, 299192, 609, 16384⟩
    (by decide) selected_cut_21080

theorem selected_cut_21081 : selected 8 ⟨540311, by decide⟩
    (prefixPartial 13 299193) = some ⟨13, 2, 0, 540311, 299193, 2777, 16384⟩ := by
  decide +kernel

theorem context_13_299193_540311 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299193 ⟨540311, by decide⟩ :=
  accepted_of_selected 13 299193 ⟨540311, by decide⟩ ⟨13, 2, 0, 540311, 299193, 2777, 16384⟩
    (by decide) selected_cut_21081

theorem selected_cut_21082 : selected 8 ⟨540328, by decide⟩
    (prefixPartial 13 299194) = some ⟨13, 2, 0, 540328, 299194, 1441, 16384⟩ := by
  decide +kernel

theorem context_13_299194_540328 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299194 ⟨540328, by decide⟩ :=
  accepted_of_selected 13 299194 ⟨540328, by decide⟩ ⟨13, 2, 0, 540328, 299194, 1441, 16384⟩
    (by decide) selected_cut_21082

theorem selected_cut_21083 : selected 8 ⟨540334, by decide⟩
    (prefixPartial 13 299195) = some ⟨13, 2, 0, 540334, 299195, 825, 16384⟩ := by
  decide +kernel

theorem context_13_299195_540334 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299195 ⟨540334, by decide⟩ :=
  accepted_of_selected 13 299195 ⟨540334, by decide⟩ ⟨13, 2, 0, 540334, 299195, 825, 16384⟩
    (by decide) selected_cut_21083

theorem unmarked_context_12_74798_540335 : frontier 9 ⟨540335, by decide⟩
    (prefixCache 12 74798) (prefixPartial 12 74798) = false := by
  decide +kernel

theorem node_context_12_74798_540335 : EJMOriginalGlobalDAGData.nodes 9 ⟨540335, by decide⟩ =
    .split (coordinate 12) (![⟨540274, by decide⟩,⟨540311, by decide⟩,⟨540328, by decide⟩,⟨540334, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74798_540335 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74798 ⟨540335, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74798
    ⟨540335, by decide⟩ (by decide) (![⟨540274, by decide⟩,⟨540311, by decide⟩,⟨540328, by decide⟩,⟨540334, by decide⟩]) unmarked_context_12_74798_540335 node_context_12_74798_540335
  intro a
  fin_cases a
  · exact context_13_299192_540274
  · exact context_13_299193_540311
  · exact context_13_299194_540328
  · exact context_13_299195_540334

theorem selected_cut_21084 : selected 8 ⟨540350, by decide⟩
    (prefixPartial 13 299196) = some ⟨13, 2, 0, 540350, 299196, 525, 16384⟩ := by
  decide +kernel

theorem context_13_299196_540350 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299196 ⟨540350, by decide⟩ :=
  accepted_of_selected 13 299196 ⟨540350, by decide⟩ ⟨13, 2, 0, 540350, 299196, 525, 16384⟩
    (by decide) selected_cut_21084

theorem selected_cut_21085 : selected 8 ⟨540381, by decide⟩
    (prefixPartial 13 299197) = some ⟨13, 2, 0, 540381, 299197, 2837, 16384⟩ := by
  decide +kernel

theorem context_13_299197_540381 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299197 ⟨540381, by decide⟩ :=
  accepted_of_selected 13 299197 ⟨540381, by decide⟩ ⟨13, 2, 0, 540381, 299197, 2837, 16384⟩
    (by decide) selected_cut_21085

theorem selected_cut_21086 : selected 8 ⟨540400, by decide⟩
    (prefixPartial 13 299198) = some ⟨13, 2, 0, 540400, 299198, 1589, 16384⟩ := by
  decide +kernel

theorem context_13_299198_540400 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299198 ⟨540400, by decide⟩ :=
  accepted_of_selected 13 299198 ⟨540400, by decide⟩ ⟨13, 2, 0, 540400, 299198, 1589, 16384⟩
    (by decide) selected_cut_21086

theorem selected_cut_21087 : selected 8 ⟨540407, by decide⟩
    (prefixPartial 13 299199) = some ⟨13, 2, 0, 540407, 299199, 745, 16384⟩ := by
  decide +kernel

theorem context_13_299199_540407 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299199 ⟨540407, by decide⟩ :=
  accepted_of_selected 13 299199 ⟨540407, by decide⟩ ⟨13, 2, 0, 540407, 299199, 745, 16384⟩
    (by decide) selected_cut_21087

theorem unmarked_context_12_74799_540408 : frontier 9 ⟨540408, by decide⟩
    (prefixCache 12 74799) (prefixPartial 12 74799) = false := by
  decide +kernel

theorem node_context_12_74799_540408 : EJMOriginalGlobalDAGData.nodes 9 ⟨540408, by decide⟩ =
    .split (coordinate 12) (![⟨540350, by decide⟩,⟨540381, by decide⟩,⟨540400, by decide⟩,⟨540407, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74799_540408 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74799 ⟨540408, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74799
    ⟨540408, by decide⟩ (by decide) (![⟨540350, by decide⟩,⟨540381, by decide⟩,⟨540400, by decide⟩,⟨540407, by decide⟩]) unmarked_context_12_74799_540408 node_context_12_74799_540408
  intro a
  fin_cases a
  · exact context_13_299196_540350
  · exact context_13_299197_540381
  · exact context_13_299198_540400
  · exact context_13_299199_540407

theorem unmarked_context_11_18699_540409 : frontier 10 ⟨540409, by decide⟩
    (prefixCache 11 18699) (prefixPartial 11 18699) = false := by
  decide +kernel

theorem node_context_11_18699_540409 : EJMOriginalGlobalDAGData.nodes 10 ⟨540409, by decide⟩ =
    .split (coordinate 11) (![⟨540189, by decide⟩,⟨540260, by decide⟩,⟨540335, by decide⟩,⟨540408, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18699_540409 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18699 ⟨540409, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18699
    ⟨540409, by decide⟩ (by decide) (![⟨540189, by decide⟩,⟨540260, by decide⟩,⟨540335, by decide⟩,⟨540408, by decide⟩]) unmarked_context_11_18699_540409 node_context_11_18699_540409
  intro a
  fin_cases a
  · exact context_12_74796_540189
  · exact context_12_74797_540260
  · exact context_12_74798_540335
  · exact context_12_74799_540408

theorem unmarked_context_10_4674_540410 : frontier 11 ⟨540410, by decide⟩
    (prefixCache 10 4674) (prefixPartial 10 4674) = false := by
  decide +kernel

theorem node_context_10_4674_540410 : EJMOriginalGlobalDAGData.nodes 11 ⟨540410, by decide⟩ =
    .split (coordinate 10) (![⟨539742, by decide⟩,⟨539967, by decide⟩,⟨540188, by decide⟩,⟨540409, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4674_540410 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4674 ⟨540410, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4674
    ⟨540410, by decide⟩ (by decide) (![⟨539742, by decide⟩,⟨539967, by decide⟩,⟨540188, by decide⟩,⟨540409, by decide⟩]) unmarked_context_10_4674_540410 node_context_10_4674_540410
  intro a
  fin_cases a
  · exact context_11_18696_539742
  · exact context_11_18697_539967
  · exact context_11_18698_540188
  · exact context_11_18699_540409

theorem selected_cut_21088 : selected 9 ⟨445562, by decide⟩
    (prefixPartial 12 74800) = some ⟨12, 1, 0, 445562, 74800, 1, 65536⟩ := by
  decide +kernel

theorem context_12_74800_445562 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74800 ⟨445562, by decide⟩ :=
  accepted_of_selected 12 74800 ⟨445562, by decide⟩ ⟨12, 1, 0, 445562, 74800, 1, 65536⟩
    (by decide) selected_cut_21088

theorem selected_cut_21089 : selected 8 ⟨540417, by decide⟩
    (prefixPartial 13 299204) = some ⟨13, 2, 0, 540417, 299204, 405, 16384⟩ := by
  decide +kernel

theorem context_13_299204_540417 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299204 ⟨540417, by decide⟩ :=
  accepted_of_selected 13 299204 ⟨540417, by decide⟩ ⟨13, 2, 0, 540417, 299204, 405, 16384⟩
    (by decide) selected_cut_21089

theorem selected_cut_21090 : selected 8 ⟨540442, by decide⟩
    (prefixPartial 13 299205) = some ⟨13, 2, 0, 540442, 299205, 1881, 16384⟩ := by
  decide +kernel

theorem context_13_299205_540442 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299205 ⟨540442, by decide⟩ :=
  accepted_of_selected 13 299205 ⟨540442, by decide⟩ ⟨13, 2, 0, 540442, 299205, 1881, 16384⟩
    (by decide) selected_cut_21090

theorem selected_cut_21091 : selected 8 ⟨540459, by decide⟩
    (prefixPartial 13 299206) = some ⟨13, 2, 0, 540459, 299206, 1249, 16384⟩ := by
  decide +kernel

theorem context_13_299206_540459 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299206 ⟨540459, by decide⟩ :=
  accepted_of_selected 13 299206 ⟨540459, by decide⟩ ⟨13, 2, 0, 540459, 299206, 1249, 16384⟩
    (by decide) selected_cut_21091

theorem selected_cut_21092 : selected 8 ⟨540464, by decide⟩
    (prefixPartial 13 299207) = some ⟨13, 2, 0, 540464, 299207, 645, 16384⟩ := by
  decide +kernel

theorem context_13_299207_540464 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299207 ⟨540464, by decide⟩ :=
  accepted_of_selected 13 299207 ⟨540464, by decide⟩ ⟨13, 2, 0, 540464, 299207, 645, 16384⟩
    (by decide) selected_cut_21092

theorem unmarked_context_12_74801_540465 : frontier 9 ⟨540465, by decide⟩
    (prefixCache 12 74801) (prefixPartial 12 74801) = false := by
  decide +kernel

theorem node_context_12_74801_540465 : EJMOriginalGlobalDAGData.nodes 9 ⟨540465, by decide⟩ =
    .split (coordinate 12) (![⟨540417, by decide⟩,⟨540442, by decide⟩,⟨540459, by decide⟩,⟨540464, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74801_540465 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74801 ⟨540465, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74801
    ⟨540465, by decide⟩ (by decide) (![⟨540417, by decide⟩,⟨540442, by decide⟩,⟨540459, by decide⟩,⟨540464, by decide⟩]) unmarked_context_12_74801_540465 node_context_12_74801_540465
  intro a
  fin_cases a
  · exact context_13_299204_540417
  · exact context_13_299205_540442
  · exact context_13_299206_540459
  · exact context_13_299207_540464

theorem selected_cut_21093 : selected 8 ⟨540472, by decide⟩
    (prefixPartial 13 299208) = some ⟨13, 2, 0, 540472, 299208, 437, 16384⟩ := by
  decide +kernel

theorem context_13_299208_540472 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299208 ⟨540472, by decide⟩ :=
  accepted_of_selected 13 299208 ⟨540472, by decide⟩ ⟨13, 2, 0, 540472, 299208, 437, 16384⟩
    (by decide) selected_cut_21093

theorem selected_cut_21094 : selected 8 ⟨540493, by decide⟩
    (prefixPartial 13 299209) = some ⟨13, 2, 0, 540493, 299209, 1909, 16384⟩ := by
  decide +kernel

theorem context_13_299209_540493 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299209 ⟨540493, by decide⟩ :=
  accepted_of_selected 13 299209 ⟨540493, by decide⟩ ⟨13, 2, 0, 540493, 299209, 1909, 16384⟩
    (by decide) selected_cut_21094

theorem selected_cut_21095 : selected 8 ⟨540509, by decide⟩
    (prefixPartial 13 299210) = some ⟨13, 2, 0, 540509, 299210, 1193, 16384⟩ := by
  decide +kernel

theorem context_13_299210_540509 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299210 ⟨540509, by decide⟩ :=
  accepted_of_selected 13 299210 ⟨540509, by decide⟩ ⟨13, 2, 0, 540509, 299210, 1193, 16384⟩
    (by decide) selected_cut_21095

theorem selected_cut_21096 : selected 8 ⟨540514, by decide⟩
    (prefixPartial 13 299211) = some ⟨13, 2, 0, 540514, 299211, 701, 16384⟩ := by
  decide +kernel

theorem context_13_299211_540514 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299211 ⟨540514, by decide⟩ :=
  accepted_of_selected 13 299211 ⟨540514, by decide⟩ ⟨13, 2, 0, 540514, 299211, 701, 16384⟩
    (by decide) selected_cut_21096

theorem unmarked_context_12_74802_540515 : frontier 9 ⟨540515, by decide⟩
    (prefixCache 12 74802) (prefixPartial 12 74802) = false := by
  decide +kernel

theorem node_context_12_74802_540515 : EJMOriginalGlobalDAGData.nodes 9 ⟨540515, by decide⟩ =
    .split (coordinate 12) (![⟨540472, by decide⟩,⟨540493, by decide⟩,⟨540509, by decide⟩,⟨540514, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74802_540515 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74802 ⟨540515, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74802
    ⟨540515, by decide⟩ (by decide) (![⟨540472, by decide⟩,⟨540493, by decide⟩,⟨540509, by decide⟩,⟨540514, by decide⟩]) unmarked_context_12_74802_540515 node_context_12_74802_540515
  intro a
  fin_cases a
  · exact context_13_299208_540472
  · exact context_13_299209_540493
  · exact context_13_299210_540509
  · exact context_13_299211_540514

theorem selected_cut_21097 : selected 8 ⟨540524, by decide⟩
    (prefixPartial 13 299212) = some ⟨13, 2, 0, 540524, 299212, 453, 16384⟩ := by
  decide +kernel

theorem context_13_299212_540524 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299212 ⟨540524, by decide⟩ :=
  accepted_of_selected 13 299212 ⟨540524, by decide⟩ ⟨13, 2, 0, 540524, 299212, 453, 16384⟩
    (by decide) selected_cut_21097

theorem selected_cut_21098 : selected 8 ⟨540552, by decide⟩
    (prefixPartial 13 299213) = some ⟨13, 2, 0, 540552, 299213, 2033, 16384⟩ := by
  decide +kernel

theorem context_13_299213_540552 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299213 ⟨540552, by decide⟩ :=
  accepted_of_selected 13 299213 ⟨540552, by decide⟩ ⟨13, 2, 0, 540552, 299213, 2033, 16384⟩
    (by decide) selected_cut_21098

theorem selected_cut_21099 : selected 8 ⟨540571, by decide⟩
    (prefixPartial 13 299214) = some ⟨13, 2, 0, 540571, 299214, 1369, 16384⟩ := by
  decide +kernel

theorem context_13_299214_540571 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299214 ⟨540571, by decide⟩ :=
  accepted_of_selected 13 299214 ⟨540571, by decide⟩ ⟨13, 2, 0, 540571, 299214, 1369, 16384⟩
    (by decide) selected_cut_21099

theorem selected_cut_21100 : selected 8 ⟨540575, by decide⟩
    (prefixPartial 13 299215) = some ⟨13, 2, 0, 540575, 299215, 661, 16384⟩ := by
  decide +kernel

theorem context_13_299215_540575 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299215 ⟨540575, by decide⟩ :=
  accepted_of_selected 13 299215 ⟨540575, by decide⟩ ⟨13, 2, 0, 540575, 299215, 661, 16384⟩
    (by decide) selected_cut_21100

theorem unmarked_context_12_74803_540576 : frontier 9 ⟨540576, by decide⟩
    (prefixCache 12 74803) (prefixPartial 12 74803) = false := by
  decide +kernel

theorem node_context_12_74803_540576 : EJMOriginalGlobalDAGData.nodes 9 ⟨540576, by decide⟩ =
    .split (coordinate 12) (![⟨540524, by decide⟩,⟨540552, by decide⟩,⟨540571, by decide⟩,⟨540575, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74803_540576 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74803 ⟨540576, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74803
    ⟨540576, by decide⟩ (by decide) (![⟨540524, by decide⟩,⟨540552, by decide⟩,⟨540571, by decide⟩,⟨540575, by decide⟩]) unmarked_context_12_74803_540576 node_context_12_74803_540576
  intro a
  fin_cases a
  · exact context_13_299212_540524
  · exact context_13_299213_540552
  · exact context_13_299214_540571
  · exact context_13_299215_540575

theorem unmarked_context_11_18700_540577 : frontier 10 ⟨540577, by decide⟩
    (prefixCache 11 18700) (prefixPartial 11 18700) = false := by
  decide +kernel

theorem node_context_11_18700_540577 : EJMOriginalGlobalDAGData.nodes 10 ⟨540577, by decide⟩ =
    .split (coordinate 11) (![⟨445562, by decide⟩,⟨540465, by decide⟩,⟨540515, by decide⟩,⟨540576, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18700_540577 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18700 ⟨540577, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18700
    ⟨540577, by decide⟩ (by decide) (![⟨445562, by decide⟩,⟨540465, by decide⟩,⟨540515, by decide⟩,⟨540576, by decide⟩]) unmarked_context_11_18700_540577 node_context_11_18700_540577
  intro a
  fin_cases a
  · exact context_12_74800_445562
  · exact context_12_74801_540465
  · exact context_12_74802_540515
  · exact context_12_74803_540576

theorem selected_cut_21101 : selected 9 ⟨475533, by decide⟩
    (prefixPartial 12 74804) = some ⟨12, 1, 0, 475533, 74804, 1, 65536⟩ := by
  decide +kernel

theorem context_12_74804_475533 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74804 ⟨475533, by decide⟩ :=
  accepted_of_selected 12 74804 ⟨475533, by decide⟩ ⟨12, 1, 0, 475533, 74804, 1, 65536⟩
    (by decide) selected_cut_21101

theorem selected_cut_21102 : selected 8 ⟨540583, by decide⟩
    (prefixPartial 13 299220) = some ⟨13, 2, 0, 540583, 299220, 301, 16384⟩ := by
  decide +kernel

theorem context_13_299220_540583 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299220 ⟨540583, by decide⟩ :=
  accepted_of_selected 13 299220 ⟨540583, by decide⟩ ⟨13, 2, 0, 540583, 299220, 301, 16384⟩
    (by decide) selected_cut_21102

theorem selected_cut_21103 : selected 8 ⟨540608, by decide⟩
    (prefixPartial 13 299221) = some ⟨13, 2, 0, 540608, 299221, 2049, 16384⟩ := by
  decide +kernel

theorem context_13_299221_540608 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299221 ⟨540608, by decide⟩ :=
  accepted_of_selected 13 299221 ⟨540608, by decide⟩ ⟨13, 2, 0, 540608, 299221, 2049, 16384⟩
    (by decide) selected_cut_21103

theorem selected_cut_21104 : selected 8 ⟨540628, by decide⟩
    (prefixPartial 13 299222) = some ⟨13, 2, 0, 540628, 299222, 1489, 16384⟩ := by
  decide +kernel

theorem context_13_299222_540628 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299222 ⟨540628, by decide⟩ :=
  accepted_of_selected 13 299222 ⟨540628, by decide⟩ ⟨13, 2, 0, 540628, 299222, 1489, 16384⟩
    (by decide) selected_cut_21104

theorem selected_cut_21105 : selected 8 ⟨540636, by decide⟩
    (prefixPartial 13 299223) = some ⟨13, 2, 0, 540636, 299223, 741, 16384⟩ := by
  decide +kernel

theorem context_13_299223_540636 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299223 ⟨540636, by decide⟩ :=
  accepted_of_selected 13 299223 ⟨540636, by decide⟩ ⟨13, 2, 0, 540636, 299223, 741, 16384⟩
    (by decide) selected_cut_21105

theorem unmarked_context_12_74805_540637 : frontier 9 ⟨540637, by decide⟩
    (prefixCache 12 74805) (prefixPartial 12 74805) = false := by
  decide +kernel

theorem node_context_12_74805_540637 : EJMOriginalGlobalDAGData.nodes 9 ⟨540637, by decide⟩ =
    .split (coordinate 12) (![⟨540583, by decide⟩,⟨540608, by decide⟩,⟨540628, by decide⟩,⟨540636, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74805_540637 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74805 ⟨540637, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74805
    ⟨540637, by decide⟩ (by decide) (![⟨540583, by decide⟩,⟨540608, by decide⟩,⟨540628, by decide⟩,⟨540636, by decide⟩]) unmarked_context_12_74805_540637 node_context_12_74805_540637
  intro a
  fin_cases a
  · exact context_13_299220_540583
  · exact context_13_299221_540608
  · exact context_13_299222_540628
  · exact context_13_299223_540636

theorem selected_cut_21106 : selected 8 ⟨540644, by decide⟩
    (prefixPartial 13 299224) = some ⟨13, 2, 0, 540644, 299224, 381, 16384⟩ := by
  decide +kernel

theorem context_13_299224_540644 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299224 ⟨540644, by decide⟩ :=
  accepted_of_selected 13 299224 ⟨540644, by decide⟩ ⟨13, 2, 0, 540644, 299224, 381, 16384⟩
    (by decide) selected_cut_21106

theorem selected_cut_21107 : selected 8 ⟨540674, by decide⟩
    (prefixPartial 13 299225) = some ⟨13, 2, 0, 540674, 299225, 2309, 16384⟩ := by
  decide +kernel

theorem context_13_299225_540674 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299225 ⟨540674, by decide⟩ :=
  accepted_of_selected 13 299225 ⟨540674, by decide⟩ ⟨13, 2, 0, 540674, 299225, 2309, 16384⟩
    (by decide) selected_cut_21107

theorem selected_cut_21108 : selected 8 ⟨540693, by decide⟩
    (prefixPartial 13 299226) = some ⟨13, 2, 0, 540693, 299226, 1505, 16384⟩ := by
  decide +kernel

theorem context_13_299226_540693 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299226 ⟨540693, by decide⟩ :=
  accepted_of_selected 13 299226 ⟨540693, by decide⟩ ⟨13, 2, 0, 540693, 299226, 1505, 16384⟩
    (by decide) selected_cut_21108

theorem selected_cut_21109 : selected 8 ⟨540700, by decide⟩
    (prefixPartial 13 299227) = some ⟨13, 2, 0, 540700, 299227, 853, 16384⟩ := by
  decide +kernel

theorem context_13_299227_540700 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299227 ⟨540700, by decide⟩ :=
  accepted_of_selected 13 299227 ⟨540700, by decide⟩ ⟨13, 2, 0, 540700, 299227, 853, 16384⟩
    (by decide) selected_cut_21109

theorem unmarked_context_12_74806_540701 : frontier 9 ⟨540701, by decide⟩
    (prefixCache 12 74806) (prefixPartial 12 74806) = false := by
  decide +kernel

theorem node_context_12_74806_540701 : EJMOriginalGlobalDAGData.nodes 9 ⟨540701, by decide⟩ =
    .split (coordinate 12) (![⟨540644, by decide⟩,⟨540674, by decide⟩,⟨540693, by decide⟩,⟨540700, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74806_540701 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74806 ⟨540701, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74806
    ⟨540701, by decide⟩ (by decide) (![⟨540644, by decide⟩,⟨540674, by decide⟩,⟨540693, by decide⟩,⟨540700, by decide⟩]) unmarked_context_12_74806_540701 node_context_12_74806_540701
  intro a
  fin_cases a
  · exact context_13_299224_540644
  · exact context_13_299225_540674
  · exact context_13_299226_540693
  · exact context_13_299227_540700

theorem selected_cut_21110 : selected 8 ⟨540709, by decide⟩
    (prefixPartial 13 299228) = some ⟨13, 2, 0, 540709, 299228, 405, 16384⟩ := by
  decide +kernel

theorem context_13_299228_540709 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299228 ⟨540709, by decide⟩ :=
  accepted_of_selected 13 299228 ⟨540709, by decide⟩ ⟨13, 2, 0, 540709, 299228, 405, 16384⟩
    (by decide) selected_cut_21110

theorem selected_cut_21111 : selected 8 ⟨540742, by decide⟩
    (prefixPartial 13 299229) = some ⟨13, 2, 0, 540742, 299229, 2457, 16384⟩ := by
  decide +kernel

theorem context_13_299229_540742 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299229 ⟨540742, by decide⟩ :=
  accepted_of_selected 13 299229 ⟨540742, by decide⟩ ⟨13, 2, 0, 540742, 299229, 2457, 16384⟩
    (by decide) selected_cut_21111

theorem selected_cut_21112 : selected 8 ⟨540767, by decide⟩
    (prefixPartial 13 299230) = some ⟨13, 2, 0, 540767, 299230, 1849, 16384⟩ := by
  decide +kernel

theorem context_13_299230_540767 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299230 ⟨540767, by decide⟩ :=
  accepted_of_selected 13 299230 ⟨540767, by decide⟩ ⟨13, 2, 0, 540767, 299230, 1849, 16384⟩
    (by decide) selected_cut_21112

theorem selected_cut_21113 : selected 8 ⟨540777, by decide⟩
    (prefixPartial 13 299231) = some ⟨13, 2, 0, 540777, 299231, 889, 16384⟩ := by
  decide +kernel

theorem context_13_299231_540777 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299231 ⟨540777, by decide⟩ :=
  accepted_of_selected 13 299231 ⟨540777, by decide⟩ ⟨13, 2, 0, 540777, 299231, 889, 16384⟩
    (by decide) selected_cut_21113

theorem unmarked_context_12_74807_540778 : frontier 9 ⟨540778, by decide⟩
    (prefixCache 12 74807) (prefixPartial 12 74807) = false := by
  decide +kernel

theorem node_context_12_74807_540778 : EJMOriginalGlobalDAGData.nodes 9 ⟨540778, by decide⟩ =
    .split (coordinate 12) (![⟨540709, by decide⟩,⟨540742, by decide⟩,⟨540767, by decide⟩,⟨540777, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74807_540778 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74807 ⟨540778, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74807
    ⟨540778, by decide⟩ (by decide) (![⟨540709, by decide⟩,⟨540742, by decide⟩,⟨540767, by decide⟩,⟨540777, by decide⟩]) unmarked_context_12_74807_540778 node_context_12_74807_540778
  intro a
  fin_cases a
  · exact context_13_299228_540709
  · exact context_13_299229_540742
  · exact context_13_299230_540767
  · exact context_13_299231_540777

theorem unmarked_context_11_18701_540779 : frontier 10 ⟨540779, by decide⟩
    (prefixCache 11 18701) (prefixPartial 11 18701) = false := by
  decide +kernel

theorem node_context_11_18701_540779 : EJMOriginalGlobalDAGData.nodes 10 ⟨540779, by decide⟩ =
    .split (coordinate 11) (![⟨475533, by decide⟩,⟨540637, by decide⟩,⟨540701, by decide⟩,⟨540778, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18701_540779 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18701 ⟨540779, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18701
    ⟨540779, by decide⟩ (by decide) (![⟨475533, by decide⟩,⟨540637, by decide⟩,⟨540701, by decide⟩,⟨540778, by decide⟩]) unmarked_context_11_18701_540779 node_context_11_18701_540779
  intro a
  fin_cases a
  · exact context_12_74804_475533
  · exact context_12_74805_540637
  · exact context_12_74806_540701
  · exact context_12_74807_540778

theorem selected_cut_21114 : selected 9 ⟨540780, by decide⟩
    (prefixPartial 12 74808) = some ⟨12, 1, 0, 540780, 74808, 1, 65536⟩ := by
  decide +kernel

theorem context_12_74808_540780 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74808 ⟨540780, by decide⟩ :=
  accepted_of_selected 12 74808 ⟨540780, by decide⟩ ⟨12, 1, 0, 540780, 74808, 1, 65536⟩
    (by decide) selected_cut_21114

theorem selected_cut_21115 : selected 8 ⟨540788, by decide⟩
    (prefixPartial 13 299236) = some ⟨13, 2, 0, 540788, 299236, 285, 16384⟩ := by
  decide +kernel

theorem context_13_299236_540788 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299236 ⟨540788, by decide⟩ :=
  accepted_of_selected 13 299236 ⟨540788, by decide⟩ ⟨13, 2, 0, 540788, 299236, 285, 16384⟩
    (by decide) selected_cut_21115

theorem selected_cut_21116 : selected 8 ⟨540819, by decide⟩
    (prefixPartial 13 299237) = some ⟨13, 2, 0, 540819, 299237, 2485, 16384⟩ := by
  decide +kernel

theorem context_13_299237_540819 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299237 ⟨540819, by decide⟩ :=
  accepted_of_selected 13 299237 ⟨540819, by decide⟩ ⟨13, 2, 0, 540819, 299237, 2485, 16384⟩
    (by decide) selected_cut_21116

theorem selected_cut_21117 : selected 8 ⟨540844, by decide⟩
    (prefixPartial 13 299238) = some ⟨13, 2, 0, 540844, 299238, 1677, 16384⟩ := by
  decide +kernel

theorem context_13_299238_540844 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299238 ⟨540844, by decide⟩ :=
  accepted_of_selected 13 299238 ⟨540844, by decide⟩ ⟨13, 2, 0, 540844, 299238, 1677, 16384⟩
    (by decide) selected_cut_21117

theorem selected_cut_21118 : selected 8 ⟨540851, by decide⟩
    (prefixPartial 13 299239) = some ⟨13, 2, 0, 540851, 299239, 837, 16384⟩ := by
  decide +kernel

theorem context_13_299239_540851 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299239 ⟨540851, by decide⟩ :=
  accepted_of_selected 13 299239 ⟨540851, by decide⟩ ⟨13, 2, 0, 540851, 299239, 837, 16384⟩
    (by decide) selected_cut_21118

theorem unmarked_context_12_74809_540852 : frontier 9 ⟨540852, by decide⟩
    (prefixCache 12 74809) (prefixPartial 12 74809) = false := by
  decide +kernel

theorem node_context_12_74809_540852 : EJMOriginalGlobalDAGData.nodes 9 ⟨540852, by decide⟩ =
    .split (coordinate 12) (![⟨540788, by decide⟩,⟨540819, by decide⟩,⟨540844, by decide⟩,⟨540851, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74809_540852 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74809 ⟨540852, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74809
    ⟨540852, by decide⟩ (by decide) (![⟨540788, by decide⟩,⟨540819, by decide⟩,⟨540844, by decide⟩,⟨540851, by decide⟩]) unmarked_context_12_74809_540852 node_context_12_74809_540852
  intro a
  fin_cases a
  · exact context_13_299236_540788
  · exact context_13_299237_540819
  · exact context_13_299238_540844
  · exact context_13_299239_540851

theorem selected_cut_21119 : selected 8 ⟨540858, by decide⟩
    (prefixPartial 13 299240) = some ⟨13, 2, 0, 540858, 299240, 237, 16384⟩ := by
  decide +kernel

theorem context_13_299240_540858 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299240 ⟨540858, by decide⟩ :=
  accepted_of_selected 13 299240 ⟨540858, by decide⟩ ⟨13, 2, 0, 540858, 299240, 237, 16384⟩
    (by decide) selected_cut_21119

theorem selected_cut_21120 : selected 8 ⟨540882, by decide⟩
    (prefixPartial 13 299241) = some ⟨13, 2, 0, 540882, 299241, 2425, 16384⟩ := by
  decide +kernel

theorem context_13_299241_540882 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299241 ⟨540882, by decide⟩ :=
  accepted_of_selected 13 299241 ⟨540882, by decide⟩ ⟨13, 2, 0, 540882, 299241, 2425, 16384⟩
    (by decide) selected_cut_21120

theorem selected_cut_21121 : selected 8 ⟨540898, by decide⟩
    (prefixPartial 13 299242) = some ⟨13, 2, 0, 540898, 299242, 1481, 16384⟩ := by
  decide +kernel

theorem context_13_299242_540898 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299242 ⟨540898, by decide⟩ :=
  accepted_of_selected 13 299242 ⟨540898, by decide⟩ ⟨13, 2, 0, 540898, 299242, 1481, 16384⟩
    (by decide) selected_cut_21121

theorem selected_cut_21122 : selected 8 ⟨540905, by decide⟩
    (prefixPartial 13 299243) = some ⟨13, 2, 0, 540905, 299243, 901, 16384⟩ := by
  decide +kernel

theorem context_13_299243_540905 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299243 ⟨540905, by decide⟩ :=
  accepted_of_selected 13 299243 ⟨540905, by decide⟩ ⟨13, 2, 0, 540905, 299243, 901, 16384⟩
    (by decide) selected_cut_21122

theorem unmarked_context_12_74810_540906 : frontier 9 ⟨540906, by decide⟩
    (prefixCache 12 74810) (prefixPartial 12 74810) = false := by
  decide +kernel

theorem node_context_12_74810_540906 : EJMOriginalGlobalDAGData.nodes 9 ⟨540906, by decide⟩ =
    .split (coordinate 12) (![⟨540858, by decide⟩,⟨540882, by decide⟩,⟨540898, by decide⟩,⟨540905, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74810_540906 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74810 ⟨540906, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74810
    ⟨540906, by decide⟩ (by decide) (![⟨540858, by decide⟩,⟨540882, by decide⟩,⟨540898, by decide⟩,⟨540905, by decide⟩]) unmarked_context_12_74810_540906 node_context_12_74810_540906
  intro a
  fin_cases a
  · exact context_13_299240_540858
  · exact context_13_299241_540882
  · exact context_13_299242_540898
  · exact context_13_299243_540905

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
