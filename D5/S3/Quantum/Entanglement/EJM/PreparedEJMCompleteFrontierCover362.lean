/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover361
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_34754 : selected 9 ⟨907253, by decide⟩
    (prefixPartial 12 282635) = some ⟨12, 2, 0, 907253, 282635, 2973, 65536⟩ := by
  decide +kernel

theorem context_12_282635_907253 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 282635 ⟨907253, by decide⟩ :=
  accepted_of_selected 12 282635 ⟨907253, by decide⟩ ⟨12, 2, 0, 907253, 282635, 2973, 65536⟩
    (by decide) selected_cut_34754

theorem unmarked_context_11_70658_907254 : frontier 10 ⟨907254, by decide⟩
    (prefixCache 11 70658) (prefixPartial 11 70658) = false := by
  decide +kernel

theorem node_context_11_70658_907254 : EJMOriginalGlobalDAGData.nodes 10 ⟨907254, by decide⟩ =
    .split (coordinate 11) (![⟨907055, by decide⟩,⟨907123, by decide⟩,⟨907186, by decide⟩,⟨907253, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_70658_907254 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70658 ⟨907254, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 70658
    ⟨907254, by decide⟩ (by decide) (![⟨907055, by decide⟩,⟨907123, by decide⟩,⟨907186, by decide⟩,⟨907253, by decide⟩]) unmarked_context_11_70658_907254 node_context_11_70658_907254
  intro a
  fin_cases a
  · exact context_12_282632_907055
  · exact context_12_282633_907123
  · exact context_12_282634_907186
  · exact context_12_282635_907253

theorem selected_cut_34755 : selected 10 ⟨1736, by decide⟩
    (prefixPartial 11 70659) = some ⟨11, 1, 0, 1736, 70659, 1, 262144⟩ := by
  decide +kernel

theorem context_11_70659_1736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70659 ⟨1736, by decide⟩ :=
  accepted_of_selected 11 70659 ⟨1736, by decide⟩ ⟨11, 1, 0, 1736, 70659, 1, 262144⟩
    (by decide) selected_cut_34755

theorem unmarked_context_10_17664_907255 : frontier 11 ⟨907255, by decide⟩
    (prefixCache 10 17664) (prefixPartial 10 17664) = false := by
  decide +kernel

theorem node_context_10_17664_907255 : EJMOriginalGlobalDAGData.nodes 11 ⟨907255, by decide⟩ =
    .split (coordinate 10) (![⟨167448, by decide⟩,⟨906965, by decide⟩,⟨907254, by decide⟩,⟨1736, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17664_907255 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17664 ⟨907255, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17664
    ⟨907255, by decide⟩ (by decide) (![⟨167448, by decide⟩,⟨906965, by decide⟩,⟨907254, by decide⟩,⟨1736, by decide⟩]) unmarked_context_10_17664_907255 node_context_10_17664_907255
  intro a
  fin_cases a
  · exact context_11_70656_167448
  · exact context_11_70657_906965
  · exact context_11_70658_907254
  · exact context_11_70659_1736

theorem selected_cut_34756 : selected 10 ⟨907316, by decide⟩
    (prefixPartial 11 70660) = some ⟨11, 2, 0, 907316, 70660, 2657, 262144⟩ := by
  decide +kernel

theorem context_11_70660_907316 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70660 ⟨907316, by decide⟩ :=
  accepted_of_selected 11 70660 ⟨907316, by decide⟩ ⟨11, 2, 0, 907316, 70660, 2657, 262144⟩
    (by decide) selected_cut_34756

theorem selected_cut_34757 : selected 10 ⟨907388, by decide⟩
    (prefixPartial 11 70661) = some ⟨11, 2, 0, 907388, 70661, 2665, 262144⟩ := by
  decide +kernel

theorem context_11_70661_907388 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70661 ⟨907388, by decide⟩ :=
  accepted_of_selected 11 70661 ⟨907388, by decide⟩ ⟨11, 2, 0, 907388, 70661, 2665, 262144⟩
    (by decide) selected_cut_34757

theorem selected_cut_34758 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 282648) = some ⟨12, 1, 0, 1738, 282648, 1, 65536⟩ := by
  decide +kernel

theorem context_12_282648_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 282648 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 282648 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 282648, 1, 65536⟩
    (by decide) selected_cut_34758

theorem selected_cut_34759 : selected 9 ⟨907440, by decide⟩
    (prefixPartial 12 282649) = some ⟨12, 2, 0, 907440, 282649, 1793, 65536⟩ := by
  decide +kernel

theorem context_12_282649_907440 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 282649 ⟨907440, by decide⟩ :=
  accepted_of_selected 12 282649 ⟨907440, by decide⟩ ⟨12, 2, 0, 907440, 282649, 1793, 65536⟩
    (by decide) selected_cut_34759

theorem selected_cut_34760 : selected 9 ⟨907497, by decide⟩
    (prefixPartial 12 282650) = some ⟨12, 2, 0, 907497, 282650, 2649, 65536⟩ := by
  decide +kernel

theorem context_12_282650_907497 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 282650 ⟨907497, by decide⟩ :=
  accepted_of_selected 12 282650 ⟨907497, by decide⟩ ⟨12, 2, 0, 907497, 282650, 2649, 65536⟩
    (by decide) selected_cut_34760

theorem selected_cut_34761 : selected 9 ⟨907557, by decide⟩
    (prefixPartial 12 282651) = some ⟨12, 2, 0, 907557, 282651, 2885, 65536⟩ := by
  decide +kernel

theorem context_12_282651_907557 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 282651 ⟨907557, by decide⟩ :=
  accepted_of_selected 12 282651 ⟨907557, by decide⟩ ⟨12, 2, 0, 907557, 282651, 2885, 65536⟩
    (by decide) selected_cut_34761

theorem unmarked_context_11_70662_907558 : frontier 10 ⟨907558, by decide⟩
    (prefixCache 11 70662) (prefixPartial 11 70662) = false := by
  decide +kernel

theorem node_context_11_70662_907558 : EJMOriginalGlobalDAGData.nodes 10 ⟨907558, by decide⟩ =
    .split (coordinate 11) (![⟨1738, by decide⟩,⟨907440, by decide⟩,⟨907497, by decide⟩,⟨907557, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_70662_907558 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70662 ⟨907558, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 70662
    ⟨907558, by decide⟩ (by decide) (![⟨1738, by decide⟩,⟨907440, by decide⟩,⟨907497, by decide⟩,⟨907557, by decide⟩]) unmarked_context_11_70662_907558 node_context_11_70662_907558
  intro a
  fin_cases a
  · exact context_12_282648_1738
  · exact context_12_282649_907440
  · exact context_12_282650_907497
  · exact context_12_282651_907557

theorem selected_cut_34762 : selected 10 ⟨1736, by decide⟩
    (prefixPartial 11 70663) = some ⟨11, 1, 0, 1736, 70663, 1, 262144⟩ := by
  decide +kernel

theorem context_11_70663_1736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70663 ⟨1736, by decide⟩ :=
  accepted_of_selected 11 70663 ⟨1736, by decide⟩ ⟨11, 1, 0, 1736, 70663, 1, 262144⟩
    (by decide) selected_cut_34762

theorem unmarked_context_10_17665_907559 : frontier 11 ⟨907559, by decide⟩
    (prefixCache 10 17665) (prefixPartial 10 17665) = false := by
  decide +kernel

theorem node_context_10_17665_907559 : EJMOriginalGlobalDAGData.nodes 11 ⟨907559, by decide⟩ =
    .split (coordinate 10) (![⟨907316, by decide⟩,⟨907388, by decide⟩,⟨907558, by decide⟩,⟨1736, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17665_907559 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17665 ⟨907559, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17665
    ⟨907559, by decide⟩ (by decide) (![⟨907316, by decide⟩,⟨907388, by decide⟩,⟨907558, by decide⟩,⟨1736, by decide⟩]) unmarked_context_10_17665_907559 node_context_10_17665_907559
  intro a
  fin_cases a
  · exact context_11_70660_907316
  · exact context_11_70661_907388
  · exact context_11_70662_907558
  · exact context_11_70663_1736

theorem selected_cut_34763 : selected 10 ⟨907640, by decide⟩
    (prefixPartial 11 70664) = some ⟨11, 2, 0, 907640, 70664, 2649, 262144⟩ := by
  decide +kernel

theorem context_11_70664_907640 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70664 ⟨907640, by decide⟩ :=
  accepted_of_selected 11 70664 ⟨907640, by decide⟩ ⟨11, 2, 0, 907640, 70664, 2649, 262144⟩
    (by decide) selected_cut_34763

theorem selected_cut_34764 : selected 10 ⟨907729, by decide⟩
    (prefixPartial 11 70665) = some ⟨11, 2, 0, 907729, 70665, 3009, 262144⟩ := by
  decide +kernel

theorem context_11_70665_907729 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70665 ⟨907729, by decide⟩ :=
  accepted_of_selected 11 70665 ⟨907729, by decide⟩ ⟨11, 2, 0, 907729, 70665, 3009, 262144⟩
    (by decide) selected_cut_34764

theorem selected_cut_34765 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 282664) = some ⟨12, 1, 0, 1738, 282664, 1, 65536⟩ := by
  decide +kernel

theorem context_12_282664_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 282664 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 282664 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 282664, 1, 65536⟩
    (by decide) selected_cut_34765

theorem selected_cut_34766 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 282665) = some ⟨12, 1, 0, 1738, 282665, 1, 65536⟩ := by
  decide +kernel

theorem context_12_282665_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 282665 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 282665 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 282665, 1, 65536⟩
    (by decide) selected_cut_34766

theorem selected_cut_34767 : selected 9 ⟨907793, by decide⟩
    (prefixPartial 12 282666) = some ⟨12, 2, 0, 907793, 282666, 2001, 65536⟩ := by
  decide +kernel

theorem context_12_282666_907793 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 282666 ⟨907793, by decide⟩ :=
  accepted_of_selected 12 282666 ⟨907793, by decide⟩ ⟨12, 2, 0, 907793, 282666, 2001, 65536⟩
    (by decide) selected_cut_34767

theorem selected_cut_34768 : selected 9 ⟨907852, by decide⟩
    (prefixPartial 12 282667) = some ⟨12, 2, 0, 907852, 282667, 2453, 65536⟩ := by
  decide +kernel

theorem context_12_282667_907852 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 282667 ⟨907852, by decide⟩ :=
  accepted_of_selected 12 282667 ⟨907852, by decide⟩ ⟨12, 2, 0, 907852, 282667, 2453, 65536⟩
    (by decide) selected_cut_34768

theorem unmarked_context_11_70666_907853 : frontier 10 ⟨907853, by decide⟩
    (prefixCache 11 70666) (prefixPartial 11 70666) = false := by
  decide +kernel

theorem node_context_11_70666_907853 : EJMOriginalGlobalDAGData.nodes 10 ⟨907853, by decide⟩ =
    .split (coordinate 11) (![⟨1738, by decide⟩,⟨1738, by decide⟩,⟨907793, by decide⟩,⟨907852, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_70666_907853 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70666 ⟨907853, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 70666
    ⟨907853, by decide⟩ (by decide) (![⟨1738, by decide⟩,⟨1738, by decide⟩,⟨907793, by decide⟩,⟨907852, by decide⟩]) unmarked_context_11_70666_907853 node_context_11_70666_907853
  intro a
  fin_cases a
  · exact context_12_282664_1738
  · exact context_12_282665_1738
  · exact context_12_282666_907793
  · exact context_12_282667_907852

theorem selected_cut_34769 : selected 10 ⟨907914, by decide⟩
    (prefixPartial 11 70667) = some ⟨11, 2, 0, 907914, 70667, 2029, 262144⟩ := by
  decide +kernel

theorem context_11_70667_907914 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70667 ⟨907914, by decide⟩ :=
  accepted_of_selected 11 70667 ⟨907914, by decide⟩ ⟨11, 2, 0, 907914, 70667, 2029, 262144⟩
    (by decide) selected_cut_34769

theorem unmarked_context_10_17666_907915 : frontier 11 ⟨907915, by decide⟩
    (prefixCache 10 17666) (prefixPartial 10 17666) = false := by
  decide +kernel

theorem node_context_10_17666_907915 : EJMOriginalGlobalDAGData.nodes 11 ⟨907915, by decide⟩ =
    .split (coordinate 10) (![⟨907640, by decide⟩,⟨907729, by decide⟩,⟨907853, by decide⟩,⟨907914, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17666_907915 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17666 ⟨907915, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17666
    ⟨907915, by decide⟩ (by decide) (![⟨907640, by decide⟩,⟨907729, by decide⟩,⟨907853, by decide⟩,⟨907914, by decide⟩]) unmarked_context_10_17666_907915 node_context_10_17666_907915
  intro a
  fin_cases a
  · exact context_11_70664_907640
  · exact context_11_70665_907729
  · exact context_11_70666_907853
  · exact context_11_70667_907914

theorem selected_cut_34770 : selected 11 ⟨3440, by decide⟩
    (prefixPartial 10 17667) = some ⟨10, 1, 0, 3440, 17667, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_17667_3440 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17667 ⟨3440, by decide⟩ :=
  accepted_of_selected 10 17667 ⟨3440, by decide⟩ ⟨10, 1, 0, 3440, 17667, 1, 1048576⟩
    (by decide) selected_cut_34770

theorem unmarked_context_9_4416_907916 : frontier 12 ⟨907916, by decide⟩
    (prefixCache 9 4416) (prefixPartial 9 4416) = false := by
  decide +kernel

theorem node_context_9_4416_907916 : EJMOriginalGlobalDAGData.nodes 12 ⟨907916, by decide⟩ =
    .split (coordinate 9) (![⟨907255, by decide⟩,⟨907559, by decide⟩,⟨907915, by decide⟩,⟨3440, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4416_907916 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4416 ⟨907916, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4416
    ⟨907916, by decide⟩ (by decide) (![⟨907255, by decide⟩,⟨907559, by decide⟩,⟨907915, by decide⟩,⟨3440, by decide⟩]) unmarked_context_9_4416_907916 node_context_9_4416_907916
  intro a
  fin_cases a
  · exact context_10_17664_907255
  · exact context_10_17665_907559
  · exact context_10_17666_907915
  · exact context_10_17667_3440

theorem selected_cut_34771 : selected 10 ⟨907917, by decide⟩
    (prefixPartial 11 70672) = some ⟨11, 1, 0, 907917, 70672, 1, 262144⟩ := by
  decide +kernel

theorem context_11_70672_907917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70672 ⟨907917, by decide⟩ :=
  accepted_of_selected 11 70672 ⟨907917, by decide⟩ ⟨11, 1, 0, 907917, 70672, 1, 262144⟩
    (by decide) selected_cut_34771

theorem selected_cut_34772 : selected 10 ⟨907962, by decide⟩
    (prefixPartial 11 70673) = some ⟨11, 2, 0, 907962, 70673, 2041, 262144⟩ := by
  decide +kernel

theorem context_11_70673_907962 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70673 ⟨907962, by decide⟩ :=
  accepted_of_selected 11 70673 ⟨907962, by decide⟩ ⟨11, 2, 0, 907962, 70673, 2041, 262144⟩
    (by decide) selected_cut_34772

theorem selected_cut_34773 : selected 9 ⟨907986, by decide⟩
    (prefixPartial 12 282696) = some ⟨12, 2, 0, 907986, 282696, 1161, 65536⟩ := by
  decide +kernel

theorem context_12_282696_907986 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 282696 ⟨907986, by decide⟩ :=
  accepted_of_selected 12 282696 ⟨907986, by decide⟩ ⟨12, 2, 0, 907986, 282696, 1161, 65536⟩
    (by decide) selected_cut_34773

theorem selected_cut_34774 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 282697) = some ⟨12, 1, 0, 896706, 282697, 1, 65536⟩ := by
  decide +kernel

theorem context_12_282697_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 282697 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 282697 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 282697, 1, 65536⟩
    (by decide) selected_cut_34774

theorem selected_cut_34775 : selected 9 ⟨908017, by decide⟩
    (prefixPartial 12 282698) = some ⟨12, 2, 0, 908017, 282698, 1797, 65536⟩ := by
  decide +kernel

theorem context_12_282698_908017 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 282698 ⟨908017, by decide⟩ :=
  accepted_of_selected 12 282698 ⟨908017, by decide⟩ ⟨12, 2, 0, 908017, 282698, 1797, 65536⟩
    (by decide) selected_cut_34775

theorem selected_cut_34776 : selected 9 ⟨908055, by decide⟩
    (prefixPartial 12 282699) = some ⟨12, 2, 0, 908055, 282699, 1889, 65536⟩ := by
  decide +kernel

theorem context_12_282699_908055 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 282699 ⟨908055, by decide⟩ :=
  accepted_of_selected 12 282699 ⟨908055, by decide⟩ ⟨12, 2, 0, 908055, 282699, 1889, 65536⟩
    (by decide) selected_cut_34776

theorem unmarked_context_11_70674_908056 : frontier 10 ⟨908056, by decide⟩
    (prefixCache 11 70674) (prefixPartial 11 70674) = false := by
  decide +kernel

theorem node_context_11_70674_908056 : EJMOriginalGlobalDAGData.nodes 10 ⟨908056, by decide⟩ =
    .split (coordinate 11) (![⟨907986, by decide⟩,⟨896706, by decide⟩,⟨908017, by decide⟩,⟨908055, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_70674_908056 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70674 ⟨908056, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 70674
    ⟨908056, by decide⟩ (by decide) (![⟨907986, by decide⟩,⟨896706, by decide⟩,⟨908017, by decide⟩,⟨908055, by decide⟩]) unmarked_context_11_70674_908056 node_context_11_70674_908056
  intro a
  fin_cases a
  · exact context_12_282696_907986
  · exact context_12_282697_896706
  · exact context_12_282698_908017
  · exact context_12_282699_908055

theorem selected_cut_34777 : selected 10 ⟨1736, by decide⟩
    (prefixPartial 11 70675) = some ⟨11, 1, 0, 1736, 70675, 1, 262144⟩ := by
  decide +kernel

theorem context_11_70675_1736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70675 ⟨1736, by decide⟩ :=
  accepted_of_selected 11 70675 ⟨1736, by decide⟩ ⟨11, 1, 0, 1736, 70675, 1, 262144⟩
    (by decide) selected_cut_34777

theorem unmarked_context_10_17668_908057 : frontier 11 ⟨908057, by decide⟩
    (prefixCache 10 17668) (prefixPartial 10 17668) = false := by
  decide +kernel

theorem node_context_10_17668_908057 : EJMOriginalGlobalDAGData.nodes 11 ⟨908057, by decide⟩ =
    .split (coordinate 10) (![⟨907917, by decide⟩,⟨907962, by decide⟩,⟨908056, by decide⟩,⟨1736, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17668_908057 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17668 ⟨908057, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17668
    ⟨908057, by decide⟩ (by decide) (![⟨907917, by decide⟩,⟨907962, by decide⟩,⟨908056, by decide⟩,⟨1736, by decide⟩]) unmarked_context_10_17668_908057 node_context_10_17668_908057
  intro a
  fin_cases a
  · exact context_11_70672_907917
  · exact context_11_70673_907962
  · exact context_11_70674_908056
  · exact context_11_70675_1736

theorem selected_cut_34778 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 17669) = some ⟨10, 1, 0, 893098, 17669, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_17669_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17669 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 17669 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 17669, 1, 1048576⟩
    (by decide) selected_cut_34778

theorem selected_cut_34779 : selected 10 ⟨908101, by decide⟩
    (prefixPartial 11 70680) = some ⟨11, 2, 0, 908101, 70680, 1989, 262144⟩ := by
  decide +kernel

theorem context_11_70680_908101 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70680 ⟨908101, by decide⟩ :=
  accepted_of_selected 11 70680 ⟨908101, by decide⟩ ⟨11, 2, 0, 908101, 70680, 1989, 262144⟩
    (by decide) selected_cut_34779

theorem selected_cut_34780 : selected 10 ⟨908135, by decide⟩
    (prefixPartial 11 70681) = some ⟨11, 2, 0, 908135, 70681, 1881, 262144⟩ := by
  decide +kernel

theorem context_11_70681_908135 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70681 ⟨908135, by decide⟩ :=
  accepted_of_selected 11 70681 ⟨908135, by decide⟩ ⟨11, 2, 0, 908135, 70681, 1881, 262144⟩
    (by decide) selected_cut_34780

theorem selected_cut_34781 : selected 10 ⟨908208, by decide⟩
    (prefixPartial 11 70682) = some ⟨11, 2, 0, 908208, 70682, 3069, 262144⟩ := by
  decide +kernel

theorem context_11_70682_908208 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70682 ⟨908208, by decide⟩ :=
  accepted_of_selected 11 70682 ⟨908208, by decide⟩ ⟨11, 2, 0, 908208, 70682, 3069, 262144⟩
    (by decide) selected_cut_34781

theorem selected_cut_34782 : selected 10 ⟨908255, by decide⟩
    (prefixPartial 11 70683) = some ⟨11, 2, 0, 908255, 70683, 1441, 262144⟩ := by
  decide +kernel

theorem context_11_70683_908255 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70683 ⟨908255, by decide⟩ :=
  accepted_of_selected 11 70683 ⟨908255, by decide⟩ ⟨11, 2, 0, 908255, 70683, 1441, 262144⟩
    (by decide) selected_cut_34782

theorem unmarked_context_10_17670_908256 : frontier 11 ⟨908256, by decide⟩
    (prefixCache 10 17670) (prefixPartial 10 17670) = false := by
  decide +kernel

theorem node_context_10_17670_908256 : EJMOriginalGlobalDAGData.nodes 11 ⟨908256, by decide⟩ =
    .split (coordinate 10) (![⟨908101, by decide⟩,⟨908135, by decide⟩,⟨908208, by decide⟩,⟨908255, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17670_908256 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17670 ⟨908256, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17670
    ⟨908256, by decide⟩ (by decide) (![⟨908101, by decide⟩,⟨908135, by decide⟩,⟨908208, by decide⟩,⟨908255, by decide⟩]) unmarked_context_10_17670_908256 node_context_10_17670_908256
  intro a
  fin_cases a
  · exact context_11_70680_908101
  · exact context_11_70681_908135
  · exact context_11_70682_908208
  · exact context_11_70683_908255

theorem selected_cut_34783 : selected 11 ⟨3440, by decide⟩
    (prefixPartial 10 17671) = some ⟨10, 1, 0, 3440, 17671, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_17671_3440 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17671 ⟨3440, by decide⟩ :=
  accepted_of_selected 10 17671 ⟨3440, by decide⟩ ⟨10, 1, 0, 3440, 17671, 1, 1048576⟩
    (by decide) selected_cut_34783

theorem unmarked_context_9_4417_908257 : frontier 12 ⟨908257, by decide⟩
    (prefixCache 9 4417) (prefixPartial 9 4417) = false := by
  decide +kernel

theorem node_context_9_4417_908257 : EJMOriginalGlobalDAGData.nodes 12 ⟨908257, by decide⟩ =
    .split (coordinate 9) (![⟨908057, by decide⟩,⟨893098, by decide⟩,⟨908256, by decide⟩,⟨3440, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4417_908257 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4417 ⟨908257, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4417
    ⟨908257, by decide⟩ (by decide) (![⟨908057, by decide⟩,⟨893098, by decide⟩,⟨908256, by decide⟩,⟨3440, by decide⟩]) unmarked_context_9_4417_908257 node_context_9_4417_908257
  intro a
  fin_cases a
  · exact context_10_17668_908057
  · exact context_10_17669_893098
  · exact context_10_17670_908256
  · exact context_10_17671_3440

theorem selected_cut_34784 : selected 10 ⟨907917, by decide⟩
    (prefixPartial 11 70688) = some ⟨11, 1, 0, 907917, 70688, 1, 262144⟩ := by
  decide +kernel

theorem context_11_70688_907917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70688 ⟨907917, by decide⟩ :=
  accepted_of_selected 11 70688 ⟨907917, by decide⟩ ⟨11, 1, 0, 907917, 70688, 1, 262144⟩
    (by decide) selected_cut_34784

theorem selected_cut_34785 : selected 9 ⟨908279, by decide⟩
    (prefixPartial 12 282756) = some ⟨12, 2, 0, 908279, 282756, 861, 65536⟩ := by
  decide +kernel

theorem context_12_282756_908279 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 282756 ⟨908279, by decide⟩ :=
  accepted_of_selected 12 282756 ⟨908279, by decide⟩ ⟨12, 2, 0, 908279, 282756, 861, 65536⟩
    (by decide) selected_cut_34785

theorem selected_cut_34786 : selected 9 ⟨908302, by decide⟩
    (prefixPartial 12 282757) = some ⟨12, 2, 0, 908302, 282757, 1265, 65536⟩ := by
  decide +kernel

theorem context_12_282757_908302 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 282757 ⟨908302, by decide⟩ :=
  accepted_of_selected 12 282757 ⟨908302, by decide⟩ ⟨12, 2, 0, 908302, 282757, 1265, 65536⟩
    (by decide) selected_cut_34786

theorem selected_cut_34787 : selected 9 ⟨908329, by decide⟩
    (prefixPartial 12 282758) = some ⟨12, 2, 0, 908329, 282758, 1257, 65536⟩ := by
  decide +kernel

theorem context_12_282758_908329 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 282758 ⟨908329, by decide⟩ :=
  accepted_of_selected 12 282758 ⟨908329, by decide⟩ ⟨12, 2, 0, 908329, 282758, 1257, 65536⟩
    (by decide) selected_cut_34787

theorem selected_cut_34788 : selected 9 ⟨908353, by decide⟩
    (prefixPartial 12 282759) = some ⟨12, 2, 0, 908353, 282759, 1285, 65536⟩ := by
  decide +kernel

theorem context_12_282759_908353 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 282759 ⟨908353, by decide⟩ :=
  accepted_of_selected 12 282759 ⟨908353, by decide⟩ ⟨12, 2, 0, 908353, 282759, 1285, 65536⟩
    (by decide) selected_cut_34788

theorem unmarked_context_11_70689_908354 : frontier 10 ⟨908354, by decide⟩
    (prefixCache 11 70689) (prefixPartial 11 70689) = false := by
  decide +kernel

theorem node_context_11_70689_908354 : EJMOriginalGlobalDAGData.nodes 10 ⟨908354, by decide⟩ =
    .split (coordinate 11) (![⟨908279, by decide⟩,⟨908302, by decide⟩,⟨908329, by decide⟩,⟨908353, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_70689_908354 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70689 ⟨908354, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 70689
    ⟨908354, by decide⟩ (by decide) (![⟨908279, by decide⟩,⟨908302, by decide⟩,⟨908329, by decide⟩,⟨908353, by decide⟩]) unmarked_context_11_70689_908354 node_context_11_70689_908354
  intro a
  fin_cases a
  · exact context_12_282756_908279
  · exact context_12_282757_908302
  · exact context_12_282758_908329
  · exact context_12_282759_908353

theorem selected_cut_34789 : selected 9 ⟨908377, by decide⟩
    (prefixPartial 12 282760) = some ⟨12, 2, 0, 908377, 282760, 981, 65536⟩ := by
  decide +kernel

theorem context_12_282760_908377 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 282760 ⟨908377, by decide⟩ :=
  accepted_of_selected 12 282760 ⟨908377, by decide⟩ ⟨12, 2, 0, 908377, 282760, 981, 65536⟩
    (by decide) selected_cut_34789

theorem selected_cut_34790 : selected 9 ⟨908411, by decide⟩
    (prefixPartial 12 282761) = some ⟨12, 2, 0, 908411, 282761, 1561, 65536⟩ := by
  decide +kernel

theorem context_12_282761_908411 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 282761 ⟨908411, by decide⟩ :=
  accepted_of_selected 12 282761 ⟨908411, by decide⟩ ⟨12, 2, 0, 908411, 282761, 1561, 65536⟩
    (by decide) selected_cut_34790

theorem selected_cut_34791 : selected 9 ⟨908438, by decide⟩
    (prefixPartial 12 282762) = some ⟨12, 2, 0, 908438, 282762, 1389, 65536⟩ := by
  decide +kernel

theorem context_12_282762_908438 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 282762 ⟨908438, by decide⟩ :=
  accepted_of_selected 12 282762 ⟨908438, by decide⟩ ⟨12, 2, 0, 908438, 282762, 1389, 65536⟩
    (by decide) selected_cut_34791

theorem selected_cut_34792 : selected 9 ⟨908467, by decide⟩
    (prefixPartial 12 282763) = some ⟨12, 2, 0, 908467, 282763, 1629, 65536⟩ := by
  decide +kernel

theorem context_12_282763_908467 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 282763 ⟨908467, by decide⟩ :=
  accepted_of_selected 12 282763 ⟨908467, by decide⟩ ⟨12, 2, 0, 908467, 282763, 1629, 65536⟩
    (by decide) selected_cut_34792

theorem unmarked_context_11_70690_908468 : frontier 10 ⟨908468, by decide⟩
    (prefixCache 11 70690) (prefixPartial 11 70690) = false := by
  decide +kernel

theorem node_context_11_70690_908468 : EJMOriginalGlobalDAGData.nodes 10 ⟨908468, by decide⟩ =
    .split (coordinate 11) (![⟨908377, by decide⟩,⟨908411, by decide⟩,⟨908438, by decide⟩,⟨908467, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_70690_908468 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70690 ⟨908468, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 70690
    ⟨908468, by decide⟩ (by decide) (![⟨908377, by decide⟩,⟨908411, by decide⟩,⟨908438, by decide⟩,⟨908467, by decide⟩]) unmarked_context_11_70690_908468 node_context_11_70690_908468
  intro a
  fin_cases a
  · exact context_12_282760_908377
  · exact context_12_282761_908411
  · exact context_12_282762_908438
  · exact context_12_282763_908467

theorem selected_cut_34793 : selected 9 ⟨908485, by decide⟩
    (prefixPartial 12 282764) = some ⟨12, 2, 0, 908485, 282764, 753, 65536⟩ := by
  decide +kernel

theorem context_12_282764_908485 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 282764 ⟨908485, by decide⟩ :=
  accepted_of_selected 12 282764 ⟨908485, by decide⟩ ⟨12, 2, 0, 908485, 282764, 753, 65536⟩
    (by decide) selected_cut_34793

theorem selected_cut_34794 : selected 9 ⟨908509, by decide⟩
    (prefixPartial 12 282765) = some ⟨12, 2, 0, 908509, 282765, 1169, 65536⟩ := by
  decide +kernel

theorem context_12_282765_908509 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 282765 ⟨908509, by decide⟩ :=
  accepted_of_selected 12 282765 ⟨908509, by decide⟩ ⟨12, 2, 0, 908509, 282765, 1169, 65536⟩
    (by decide) selected_cut_34794

theorem selected_cut_34795 : selected 9 ⟨908528, by decide⟩
    (prefixPartial 12 282766) = some ⟨12, 2, 0, 908528, 282766, 1097, 65536⟩ := by
  decide +kernel

theorem context_12_282766_908528 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 282766 ⟨908528, by decide⟩ :=
  accepted_of_selected 12 282766 ⟨908528, by decide⟩ ⟨12, 2, 0, 908528, 282766, 1097, 65536⟩
    (by decide) selected_cut_34795

theorem selected_cut_34796 : selected 9 ⟨908549, by decide⟩
    (prefixPartial 12 282767) = some ⟨12, 2, 0, 908549, 282767, 1121, 65536⟩ := by
  decide +kernel

theorem context_12_282767_908549 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 282767 ⟨908549, by decide⟩ :=
  accepted_of_selected 12 282767 ⟨908549, by decide⟩ ⟨12, 2, 0, 908549, 282767, 1121, 65536⟩
    (by decide) selected_cut_34796

theorem unmarked_context_11_70691_908550 : frontier 10 ⟨908550, by decide⟩
    (prefixCache 11 70691) (prefixPartial 11 70691) = false := by
  decide +kernel

theorem node_context_11_70691_908550 : EJMOriginalGlobalDAGData.nodes 10 ⟨908550, by decide⟩ =
    .split (coordinate 11) (![⟨908485, by decide⟩,⟨908509, by decide⟩,⟨908528, by decide⟩,⟨908549, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_70691_908550 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70691 ⟨908550, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 70691
    ⟨908550, by decide⟩ (by decide) (![⟨908485, by decide⟩,⟨908509, by decide⟩,⟨908528, by decide⟩,⟨908549, by decide⟩]) unmarked_context_11_70691_908550 node_context_11_70691_908550
  intro a
  fin_cases a
  · exact context_12_282764_908485
  · exact context_12_282765_908509
  · exact context_12_282766_908528
  · exact context_12_282767_908549

theorem unmarked_context_10_17672_908551 : frontier 11 ⟨908551, by decide⟩
    (prefixCache 10 17672) (prefixPartial 10 17672) = false := by
  decide +kernel

theorem node_context_10_17672_908551 : EJMOriginalGlobalDAGData.nodes 11 ⟨908551, by decide⟩ =
    .split (coordinate 10) (![⟨907917, by decide⟩,⟨908354, by decide⟩,⟨908468, by decide⟩,⟨908550, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17672_908551 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17672 ⟨908551, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17672
    ⟨908551, by decide⟩ (by decide) (![⟨907917, by decide⟩,⟨908354, by decide⟩,⟨908468, by decide⟩,⟨908550, by decide⟩]) unmarked_context_10_17672_908551 node_context_10_17672_908551
  intro a
  fin_cases a
  · exact context_11_70688_907917
  · exact context_11_70689_908354
  · exact context_11_70690_908468
  · exact context_11_70691_908550

theorem selected_cut_34797 : selected 10 ⟨908615, by decide⟩
    (prefixPartial 11 70692) = some ⟨11, 2, 0, 908615, 70692, 2461, 262144⟩ := by
  decide +kernel

theorem context_11_70692_908615 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70692 ⟨908615, by decide⟩ :=
  accepted_of_selected 11 70692 ⟨908615, by decide⟩ ⟨11, 2, 0, 908615, 70692, 2461, 262144⟩
    (by decide) selected_cut_34797

theorem selected_cut_34798 : selected 10 ⟨908663, by decide⟩
    (prefixPartial 11 70693) = some ⟨11, 2, 0, 908663, 70693, 1965, 262144⟩ := by
  decide +kernel

theorem context_11_70693_908663 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70693 ⟨908663, by decide⟩ :=
  accepted_of_selected 11 70693 ⟨908663, by decide⟩ ⟨11, 2, 0, 908663, 70693, 1965, 262144⟩
    (by decide) selected_cut_34798

theorem selected_cut_34799 : selected 10 ⟨908727, by decide⟩
    (prefixPartial 11 70694) = some ⟨11, 2, 0, 908727, 70694, 2273, 262144⟩ := by
  decide +kernel

theorem context_11_70694_908727 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70694 ⟨908727, by decide⟩ :=
  accepted_of_selected 11 70694 ⟨908727, by decide⟩ ⟨11, 2, 0, 908727, 70694, 2273, 262144⟩
    (by decide) selected_cut_34799

theorem selected_cut_34800 : selected 10 ⟨908773, by decide⟩
    (prefixPartial 11 70695) = some ⟨11, 2, 0, 908773, 70695, 1601, 262144⟩ := by
  decide +kernel

theorem context_11_70695_908773 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70695 ⟨908773, by decide⟩ :=
  accepted_of_selected 11 70695 ⟨908773, by decide⟩ ⟨11, 2, 0, 908773, 70695, 1601, 262144⟩
    (by decide) selected_cut_34800

theorem unmarked_context_10_17673_908774 : frontier 11 ⟨908774, by decide⟩
    (prefixCache 10 17673) (prefixPartial 10 17673) = false := by
  decide +kernel

theorem node_context_10_17673_908774 : EJMOriginalGlobalDAGData.nodes 11 ⟨908774, by decide⟩ =
    .split (coordinate 10) (![⟨908615, by decide⟩,⟨908663, by decide⟩,⟨908727, by decide⟩,⟨908773, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17673_908774 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17673 ⟨908774, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17673
    ⟨908774, by decide⟩ (by decide) (![⟨908615, by decide⟩,⟨908663, by decide⟩,⟨908727, by decide⟩,⟨908773, by decide⟩]) unmarked_context_10_17673_908774 node_context_10_17673_908774
  intro a
  fin_cases a
  · exact context_11_70692_908615
  · exact context_11_70693_908663
  · exact context_11_70694_908727
  · exact context_11_70695_908773

theorem selected_cut_34801 : selected 11 ⟨908861, by decide⟩
    (prefixPartial 10 17674) = some ⟨10, 2, 0, 908861, 17674, 2257, 1048576⟩ := by
  decide +kernel

theorem context_10_17674_908861 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17674 ⟨908861, by decide⟩ :=
  accepted_of_selected 10 17674 ⟨908861, by decide⟩ ⟨10, 2, 0, 908861, 17674, 2257, 1048576⟩
    (by decide) selected_cut_34801

theorem selected_cut_34802 : selected 11 ⟨908882, by decide⟩
    (prefixPartial 10 17675) = some ⟨10, 2, 0, 908882, 17675, 429, 1048576⟩ := by
  decide +kernel

theorem context_10_17675_908882 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17675 ⟨908882, by decide⟩ :=
  accepted_of_selected 10 17675 ⟨908882, by decide⟩ ⟨10, 2, 0, 908882, 17675, 429, 1048576⟩
    (by decide) selected_cut_34802

theorem unmarked_context_9_4418_908883 : frontier 12 ⟨908883, by decide⟩
    (prefixCache 9 4418) (prefixPartial 9 4418) = false := by
  decide +kernel

theorem node_context_9_4418_908883 : EJMOriginalGlobalDAGData.nodes 12 ⟨908883, by decide⟩ =
    .split (coordinate 9) (![⟨908551, by decide⟩,⟨908774, by decide⟩,⟨908861, by decide⟩,⟨908882, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4418_908883 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4418 ⟨908883, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4418
    ⟨908883, by decide⟩ (by decide) (![⟨908551, by decide⟩,⟨908774, by decide⟩,⟨908861, by decide⟩,⟨908882, by decide⟩]) unmarked_context_9_4418_908883 node_context_9_4418_908883
  intro a
  fin_cases a
  · exact context_10_17672_908551
  · exact context_10_17673_908774
  · exact context_10_17674_908861
  · exact context_10_17675_908882

theorem selected_cut_34803 : selected 12 ⟨4601, by decide⟩
    (prefixPartial 9 4419) = some ⟨9, 1, 0, 4601, 4419, 1, 4194304⟩ := by
  decide +kernel

theorem context_9_4419_4601 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4419 ⟨4601, by decide⟩ :=
  accepted_of_selected 9 4419 ⟨4601, by decide⟩ ⟨9, 1, 0, 4601, 4419, 1, 4194304⟩
    (by decide) selected_cut_34803

theorem unmarked_context_8_1104_908884 : frontier 13 ⟨908884, by decide⟩
    (prefixCache 8 1104) (prefixPartial 8 1104) = false := by
  decide +kernel

theorem node_context_8_1104_908884 : EJMOriginalGlobalDAGData.nodes 13 ⟨908884, by decide⟩ =
    .split (coordinate 8) (![⟨907916, by decide⟩,⟨908257, by decide⟩,⟨908883, by decide⟩,⟨4601, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1104_908884 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1104 ⟨908884, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1104
    ⟨908884, by decide⟩ (by decide) (![⟨907916, by decide⟩,⟨908257, by decide⟩,⟨908883, by decide⟩,⟨4601, by decide⟩]) unmarked_context_8_1104_908884 node_context_8_1104_908884
  intro a
  fin_cases a
  · exact context_9_4416_907916
  · exact context_9_4417_908257
  · exact context_9_4418_908883
  · exact context_9_4419_4601

theorem selected_cut_34804 : selected 10 ⟨167448, by decide⟩
    (prefixPartial 11 70720) = some ⟨11, 1, 0, 167448, 70720, 1, 262144⟩ := by
  decide +kernel

theorem context_11_70720_167448 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70720 ⟨167448, by decide⟩ :=
  accepted_of_selected 11 70720 ⟨167448, by decide⟩ ⟨11, 1, 0, 167448, 70720, 1, 262144⟩
    (by decide) selected_cut_34804

theorem selected_cut_34805 : selected 9 ⟨908947, by decide⟩
    (prefixPartial 12 282884) = some ⟨12, 2, 0, 908947, 282884, 2141, 65536⟩ := by
  decide +kernel

theorem context_12_282884_908947 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 282884 ⟨908947, by decide⟩ :=
  accepted_of_selected 12 282884 ⟨908947, by decide⟩ ⟨12, 2, 0, 908947, 282884, 2141, 65536⟩
    (by decide) selected_cut_34805

theorem selected_cut_34806 : selected 9 ⟨891951, by decide⟩
    (prefixPartial 12 282885) = some ⟨12, 1, 0, 891951, 282885, 1, 65536⟩ := by
  decide +kernel

theorem context_12_282885_891951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 282885 ⟨891951, by decide⟩ :=
  accepted_of_selected 12 282885 ⟨891951, by decide⟩ ⟨12, 1, 0, 891951, 282885, 1, 65536⟩
    (by decide) selected_cut_34806

theorem selected_cut_34807 : selected 9 ⟨909004, by decide⟩
    (prefixPartial 12 282886) = some ⟨12, 2, 0, 909004, 282886, 2885, 65536⟩ := by
  decide +kernel

theorem context_12_282886_909004 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 282886 ⟨909004, by decide⟩ :=
  accepted_of_selected 12 282886 ⟨909004, by decide⟩ ⟨12, 2, 0, 909004, 282886, 2885, 65536⟩
    (by decide) selected_cut_34807

theorem selected_cut_34808 : selected 9 ⟨893, by decide⟩
    (prefixPartial 12 282887) = some ⟨12, 1, 0, 893, 282887, 1, 65536⟩ := by
  decide +kernel

theorem context_12_282887_893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 282887 ⟨893, by decide⟩ :=
  accepted_of_selected 12 282887 ⟨893, by decide⟩ ⟨12, 1, 0, 893, 282887, 1, 65536⟩
    (by decide) selected_cut_34808

theorem unmarked_context_11_70721_909005 : frontier 10 ⟨909005, by decide⟩
    (prefixCache 11 70721) (prefixPartial 11 70721) = false := by
  decide +kernel

theorem node_context_11_70721_909005 : EJMOriginalGlobalDAGData.nodes 10 ⟨909005, by decide⟩ =
    .split (coordinate 11) (![⟨908947, by decide⟩,⟨891951, by decide⟩,⟨909004, by decide⟩,⟨893, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_70721_909005 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70721 ⟨909005, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 70721
    ⟨909005, by decide⟩ (by decide) (![⟨908947, by decide⟩,⟨891951, by decide⟩,⟨909004, by decide⟩,⟨893, by decide⟩]) unmarked_context_11_70721_909005 node_context_11_70721_909005
  intro a
  fin_cases a
  · exact context_12_282884_908947
  · exact context_12_282885_891951
  · exact context_12_282886_909004
  · exact context_12_282887_893

theorem selected_cut_34809 : selected 8 ⟨909046, by decide⟩
    (prefixPartial 13 1131552) = some ⟨13, 2, 0, 909046, 1131552, 1613, 16384⟩ := by
  decide +kernel

theorem context_13_1131552_909046 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1131552 ⟨909046, by decide⟩ :=
  accepted_of_selected 13 1131552 ⟨909046, by decide⟩ ⟨13, 2, 0, 909046, 1131552, 1613, 16384⟩
    (by decide) selected_cut_34809

theorem selected_cut_34810 : selected 8 ⟨909077, by decide⟩
    (prefixPartial 13 1131553) = some ⟨13, 2, 0, 909077, 1131553, 993, 16384⟩ := by
  decide +kernel

theorem context_13_1131553_909077 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1131553 ⟨909077, by decide⟩ :=
  accepted_of_selected 13 1131553 ⟨909077, by decide⟩ ⟨13, 2, 0, 909077, 1131553, 993, 16384⟩
    (by decide) selected_cut_34810

theorem selected_cut_34811 : selected 8 ⟨909110, by decide⟩
    (prefixPartial 13 1131554) = some ⟨13, 2, 0, 909110, 1131554, 1053, 16384⟩ := by
  decide +kernel

theorem context_13_1131554_909110 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1131554 ⟨909110, by decide⟩ :=
  accepted_of_selected 13 1131554 ⟨909110, by decide⟩ ⟨13, 2, 0, 909110, 1131554, 1053, 16384⟩
    (by decide) selected_cut_34811

theorem selected_cut_34812 : selected 8 ⟨909118, by decide⟩
    (prefixPartial 13 1131555) = some ⟨13, 2, 0, 909118, 1131555, 569, 16384⟩ := by
  decide +kernel

theorem context_13_1131555_909118 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1131555 ⟨909118, by decide⟩ :=
  accepted_of_selected 13 1131555 ⟨909118, by decide⟩ ⟨13, 2, 0, 909118, 1131555, 569, 16384⟩
    (by decide) selected_cut_34812

theorem unmarked_context_12_282888_909119 : frontier 9 ⟨909119, by decide⟩
    (prefixCache 12 282888) (prefixPartial 12 282888) = false := by
  decide +kernel

theorem node_context_12_282888_909119 : EJMOriginalGlobalDAGData.nodes 9 ⟨909119, by decide⟩ =
    .split (coordinate 12) (![⟨909046, by decide⟩,⟨909077, by decide⟩,⟨909110, by decide⟩,⟨909118, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_282888_909119 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 282888 ⟨909119, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 282888
    ⟨909119, by decide⟩ (by decide) (![⟨909046, by decide⟩,⟨909077, by decide⟩,⟨909110, by decide⟩,⟨909118, by decide⟩]) unmarked_context_12_282888_909119 node_context_12_282888_909119
  intro a
  fin_cases a
  · exact context_13_1131552_909046
  · exact context_13_1131553_909077
  · exact context_13_1131554_909110
  · exact context_13_1131555_909118

theorem selected_cut_34813 : selected 9 ⟨909180, by decide⟩
    (prefixPartial 12 282889) = some ⟨12, 2, 0, 909180, 282889, 3141, 65536⟩ := by
  decide +kernel

theorem context_12_282889_909180 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 282889 ⟨909180, by decide⟩ :=
  accepted_of_selected 12 282889 ⟨909180, by decide⟩ ⟨12, 2, 0, 909180, 282889, 3141, 65536⟩
    (by decide) selected_cut_34813

theorem selected_cut_34814 : selected 9 ⟨909260, by decide⟩
    (prefixPartial 12 282890) = some ⟨12, 2, 0, 909260, 282890, 3437, 65536⟩ := by
  decide +kernel

theorem context_12_282890_909260 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 282890 ⟨909260, by decide⟩ :=
  accepted_of_selected 12 282890 ⟨909260, by decide⟩ ⟨12, 2, 0, 909260, 282890, 3437, 65536⟩
    (by decide) selected_cut_34814

theorem selected_cut_34815 : selected 9 ⟨909331, by decide⟩
    (prefixPartial 12 282891) = some ⟨12, 2, 0, 909331, 282891, 3381, 65536⟩ := by
  decide +kernel

theorem context_12_282891_909331 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 282891 ⟨909331, by decide⟩ :=
  accepted_of_selected 12 282891 ⟨909331, by decide⟩ ⟨12, 2, 0, 909331, 282891, 3381, 65536⟩
    (by decide) selected_cut_34815

theorem unmarked_context_11_70722_909332 : frontier 10 ⟨909332, by decide⟩
    (prefixCache 11 70722) (prefixPartial 11 70722) = false := by
  decide +kernel

theorem node_context_11_70722_909332 : EJMOriginalGlobalDAGData.nodes 10 ⟨909332, by decide⟩ =
    .split (coordinate 11) (![⟨909119, by decide⟩,⟨909180, by decide⟩,⟨909260, by decide⟩,⟨909331, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_70722_909332 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70722 ⟨909332, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 70722
    ⟨909332, by decide⟩ (by decide) (![⟨909119, by decide⟩,⟨909180, by decide⟩,⟨909260, by decide⟩,⟨909331, by decide⟩]) unmarked_context_11_70722_909332 node_context_11_70722_909332
  intro a
  fin_cases a
  · exact context_12_282888_909119
  · exact context_12_282889_909180
  · exact context_12_282890_909260
  · exact context_12_282891_909331

theorem selected_cut_34816 : selected 10 ⟨1736, by decide⟩
    (prefixPartial 11 70723) = some ⟨11, 1, 0, 1736, 70723, 1, 262144⟩ := by
  decide +kernel

theorem context_11_70723_1736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70723 ⟨1736, by decide⟩ :=
  accepted_of_selected 11 70723 ⟨1736, by decide⟩ ⟨11, 1, 0, 1736, 70723, 1, 262144⟩
    (by decide) selected_cut_34816

theorem unmarked_context_10_17680_909333 : frontier 11 ⟨909333, by decide⟩
    (prefixCache 10 17680) (prefixPartial 10 17680) = false := by
  decide +kernel

theorem node_context_10_17680_909333 : EJMOriginalGlobalDAGData.nodes 11 ⟨909333, by decide⟩ =
    .split (coordinate 10) (![⟨167448, by decide⟩,⟨909005, by decide⟩,⟨909332, by decide⟩,⟨1736, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17680_909333 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17680 ⟨909333, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17680
    ⟨909333, by decide⟩ (by decide) (![⟨167448, by decide⟩,⟨909005, by decide⟩,⟨909332, by decide⟩,⟨1736, by decide⟩]) unmarked_context_10_17680_909333 node_context_10_17680_909333
  intro a
  fin_cases a
  · exact context_11_70720_167448
  · exact context_11_70721_909005
  · exact context_11_70722_909332
  · exact context_11_70723_1736

theorem selected_cut_34817 : selected 9 ⟨909371, by decide⟩
    (prefixPartial 12 282896) = some ⟨12, 2, 0, 909371, 282896, 921, 65536⟩ := by
  decide +kernel

theorem context_12_282896_909371 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 282896 ⟨909371, by decide⟩ :=
  accepted_of_selected 12 282896 ⟨909371, by decide⟩ ⟨12, 2, 0, 909371, 282896, 921, 65536⟩
    (by decide) selected_cut_34817

theorem selected_cut_34818 : selected 9 ⟨909399, by decide⟩
    (prefixPartial 12 282897) = some ⟨12, 2, 0, 909399, 282897, 973, 65536⟩ := by
  decide +kernel

theorem context_12_282897_909399 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 282897 ⟨909399, by decide⟩ :=
  accepted_of_selected 12 282897 ⟨909399, by decide⟩ ⟨12, 2, 0, 909399, 282897, 973, 65536⟩
    (by decide) selected_cut_34818

theorem selected_cut_34819 : selected 9 ⟨909444, by decide⟩
    (prefixPartial 12 282898) = some ⟨12, 2, 0, 909444, 282898, 2269, 65536⟩ := by
  decide +kernel

theorem context_12_282898_909444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 282898 ⟨909444, by decide⟩ :=
  accepted_of_selected 12 282898 ⟨909444, by decide⟩ ⟨12, 2, 0, 909444, 282898, 2269, 65536⟩
    (by decide) selected_cut_34819

theorem selected_cut_34820 : selected 9 ⟨893, by decide⟩
    (prefixPartial 12 282899) = some ⟨12, 1, 0, 893, 282899, 1, 65536⟩ := by
  decide +kernel

theorem context_12_282899_893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 282899 ⟨893, by decide⟩ :=
  accepted_of_selected 12 282899 ⟨893, by decide⟩ ⟨12, 1, 0, 893, 282899, 1, 65536⟩
    (by decide) selected_cut_34820

theorem unmarked_context_11_70724_909445 : frontier 10 ⟨909445, by decide⟩
    (prefixCache 11 70724) (prefixPartial 11 70724) = false := by
  decide +kernel

theorem node_context_11_70724_909445 : EJMOriginalGlobalDAGData.nodes 10 ⟨909445, by decide⟩ =
    .split (coordinate 11) (![⟨909371, by decide⟩,⟨909399, by decide⟩,⟨909444, by decide⟩,⟨893, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_70724_909445 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70724 ⟨909445, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 70724
    ⟨909445, by decide⟩ (by decide) (![⟨909371, by decide⟩,⟨909399, by decide⟩,⟨909444, by decide⟩,⟨893, by decide⟩]) unmarked_context_11_70724_909445 node_context_11_70724_909445
  intro a
  fin_cases a
  · exact context_12_282896_909371
  · exact context_12_282897_909399
  · exact context_12_282898_909444
  · exact context_12_282899_893

theorem selected_cut_34821 : selected 10 ⟨909528, by decide⟩
    (prefixPartial 11 70725) = some ⟨11, 2, 0, 909528, 70725, 3437, 262144⟩ := by
  decide +kernel

theorem context_11_70725_909528 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70725 ⟨909528, by decide⟩ :=
  accepted_of_selected 11 70725 ⟨909528, by decide⟩ ⟨11, 2, 0, 909528, 70725, 3437, 262144⟩
    (by decide) selected_cut_34821

theorem selected_cut_34822 : selected 9 ⟨909588, by decide⟩
    (prefixPartial 12 282904) = some ⟨12, 2, 0, 909588, 282904, 2949, 65536⟩ := by
  decide +kernel

theorem context_12_282904_909588 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 282904 ⟨909588, by decide⟩ :=
  accepted_of_selected 12 282904 ⟨909588, by decide⟩ ⟨12, 2, 0, 909588, 282904, 2949, 65536⟩
    (by decide) selected_cut_34822

theorem selected_cut_34823 : selected 9 ⟨909639, by decide⟩
    (prefixPartial 12 282905) = some ⟨12, 2, 0, 909639, 282905, 2409, 65536⟩ := by
  decide +kernel

theorem context_12_282905_909639 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 282905 ⟨909639, by decide⟩ :=
  accepted_of_selected 12 282905 ⟨909639, by decide⟩ ⟨12, 2, 0, 909639, 282905, 2409, 65536⟩
    (by decide) selected_cut_34823

theorem selected_cut_34824 : selected 9 ⟨909691, by decide⟩
    (prefixPartial 12 282906) = some ⟨12, 2, 0, 909691, 282906, 2881, 65536⟩ := by
  decide +kernel

theorem context_12_282906_909691 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 282906 ⟨909691, by decide⟩ :=
  accepted_of_selected 12 282906 ⟨909691, by decide⟩ ⟨12, 2, 0, 909691, 282906, 2881, 65536⟩
    (by decide) selected_cut_34824

theorem selected_cut_34825 : selected 9 ⟨909743, by decide⟩
    (prefixPartial 12 282907) = some ⟨12, 2, 0, 909743, 282907, 2877, 65536⟩ := by
  decide +kernel

theorem context_12_282907_909743 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 282907 ⟨909743, by decide⟩ :=
  accepted_of_selected 12 282907 ⟨909743, by decide⟩ ⟨12, 2, 0, 909743, 282907, 2877, 65536⟩
    (by decide) selected_cut_34825

theorem unmarked_context_11_70726_909744 : frontier 10 ⟨909744, by decide⟩
    (prefixCache 11 70726) (prefixPartial 11 70726) = false := by
  decide +kernel

theorem node_context_11_70726_909744 : EJMOriginalGlobalDAGData.nodes 10 ⟨909744, by decide⟩ =
    .split (coordinate 11) (![⟨909588, by decide⟩,⟨909639, by decide⟩,⟨909691, by decide⟩,⟨909743, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_70726_909744 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70726 ⟨909744, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 70726
    ⟨909744, by decide⟩ (by decide) (![⟨909588, by decide⟩,⟨909639, by decide⟩,⟨909691, by decide⟩,⟨909743, by decide⟩]) unmarked_context_11_70726_909744 node_context_11_70726_909744
  intro a
  fin_cases a
  · exact context_12_282904_909588
  · exact context_12_282905_909639
  · exact context_12_282906_909691
  · exact context_12_282907_909743

theorem selected_cut_34826 : selected 10 ⟨1736, by decide⟩
    (prefixPartial 11 70727) = some ⟨11, 1, 0, 1736, 70727, 1, 262144⟩ := by
  decide +kernel

theorem context_11_70727_1736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70727 ⟨1736, by decide⟩ :=
  accepted_of_selected 11 70727 ⟨1736, by decide⟩ ⟨11, 1, 0, 1736, 70727, 1, 262144⟩
    (by decide) selected_cut_34826

theorem unmarked_context_10_17681_909745 : frontier 11 ⟨909745, by decide⟩
    (prefixCache 10 17681) (prefixPartial 10 17681) = false := by
  decide +kernel

theorem node_context_10_17681_909745 : EJMOriginalGlobalDAGData.nodes 11 ⟨909745, by decide⟩ =
    .split (coordinate 10) (![⟨909445, by decide⟩,⟨909528, by decide⟩,⟨909744, by decide⟩,⟨1736, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17681_909745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17681 ⟨909745, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17681
    ⟨909745, by decide⟩ (by decide) (![⟨909445, by decide⟩,⟨909528, by decide⟩,⟨909744, by decide⟩,⟨1736, by decide⟩]) unmarked_context_10_17681_909745 node_context_10_17681_909745
  intro a
  fin_cases a
  · exact context_11_70724_909445
  · exact context_11_70725_909528
  · exact context_11_70726_909744
  · exact context_11_70727_1736

theorem selected_cut_34827 : selected 9 ⟨909811, by decide⟩
    (prefixPartial 12 282912) = some ⟨12, 2, 0, 909811, 282912, 3077, 65536⟩ := by
  decide +kernel

theorem context_12_282912_909811 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 282912 ⟨909811, by decide⟩ :=
  accepted_of_selected 12 282912 ⟨909811, by decide⟩ ⟨12, 2, 0, 909811, 282912, 3077, 65536⟩
    (by decide) selected_cut_34827

theorem selected_cut_34828 : selected 9 ⟨909863, by decide⟩
    (prefixPartial 12 282913) = some ⟨12, 2, 0, 909863, 282913, 2565, 65536⟩ := by
  decide +kernel

theorem context_12_282913_909863 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 282913 ⟨909863, by decide⟩ :=
  accepted_of_selected 12 282913 ⟨909863, by decide⟩ ⟨12, 2, 0, 909863, 282913, 2565, 65536⟩
    (by decide) selected_cut_34828

theorem selected_cut_34829 : selected 9 ⟨909924, by decide⟩
    (prefixPartial 12 282914) = some ⟨12, 2, 0, 909924, 282914, 2889, 65536⟩ := by
  decide +kernel

theorem context_12_282914_909924 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 282914 ⟨909924, by decide⟩ :=
  accepted_of_selected 12 282914 ⟨909924, by decide⟩ ⟨12, 2, 0, 909924, 282914, 2889, 65536⟩
    (by decide) selected_cut_34829

theorem selected_cut_34830 : selected 9 ⟨909970, by decide⟩
    (prefixPartial 12 282915) = some ⟨12, 2, 0, 909970, 282915, 2525, 65536⟩ := by
  decide +kernel

theorem context_12_282915_909970 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 282915 ⟨909970, by decide⟩ :=
  accepted_of_selected 12 282915 ⟨909970, by decide⟩ ⟨12, 2, 0, 909970, 282915, 2525, 65536⟩
    (by decide) selected_cut_34830

theorem unmarked_context_11_70728_909971 : frontier 10 ⟨909971, by decide⟩
    (prefixCache 11 70728) (prefixPartial 11 70728) = false := by
  decide +kernel

theorem node_context_11_70728_909971 : EJMOriginalGlobalDAGData.nodes 10 ⟨909971, by decide⟩ =
    .split (coordinate 11) (![⟨909811, by decide⟩,⟨909863, by decide⟩,⟨909924, by decide⟩,⟨909970, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_70728_909971 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70728 ⟨909971, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 70728
    ⟨909971, by decide⟩ (by decide) (![⟨909811, by decide⟩,⟨909863, by decide⟩,⟨909924, by decide⟩,⟨909970, by decide⟩]) unmarked_context_11_70728_909971 node_context_11_70728_909971
  intro a
  fin_cases a
  · exact context_12_282912_909811
  · exact context_12_282913_909863
  · exact context_12_282914_909924
  · exact context_12_282915_909970

theorem selected_cut_34831 : selected 9 ⟨910029, by decide⟩
    (prefixPartial 12 282916) = some ⟨12, 2, 0, 910029, 282916, 2849, 65536⟩ := by
  decide +kernel

theorem context_12_282916_910029 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 282916 ⟨910029, by decide⟩ :=
  accepted_of_selected 12 282916 ⟨910029, by decide⟩ ⟨12, 2, 0, 910029, 282916, 2849, 65536⟩
    (by decide) selected_cut_34831

theorem selected_cut_34832 : selected 9 ⟨891951, by decide⟩
    (prefixPartial 12 282917) = some ⟨12, 1, 0, 891951, 282917, 1, 65536⟩ := by
  decide +kernel

theorem context_12_282917_891951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 282917 ⟨891951, by decide⟩ :=
  accepted_of_selected 12 282917 ⟨891951, by decide⟩ ⟨12, 1, 0, 891951, 282917, 1, 65536⟩
    (by decide) selected_cut_34832

theorem selected_cut_34833 : selected 9 ⟨910073, by decide⟩
    (prefixPartial 12 282918) = some ⟨12, 2, 0, 910073, 282918, 2713, 65536⟩ := by
  decide +kernel

theorem context_12_282918_910073 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 282918 ⟨910073, by decide⟩ :=
  accepted_of_selected 12 282918 ⟨910073, by decide⟩ ⟨12, 2, 0, 910073, 282918, 2713, 65536⟩
    (by decide) selected_cut_34833

theorem selected_cut_34834 : selected 9 ⟨910116, by decide⟩
    (prefixPartial 12 282919) = some ⟨12, 2, 0, 910116, 282919, 2489, 65536⟩ := by
  decide +kernel

theorem context_12_282919_910116 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 282919 ⟨910116, by decide⟩ :=
  accepted_of_selected 12 282919 ⟨910116, by decide⟩ ⟨12, 2, 0, 910116, 282919, 2489, 65536⟩
    (by decide) selected_cut_34834

theorem unmarked_context_11_70729_910117 : frontier 10 ⟨910117, by decide⟩
    (prefixCache 11 70729) (prefixPartial 11 70729) = false := by
  decide +kernel

theorem node_context_11_70729_910117 : EJMOriginalGlobalDAGData.nodes 10 ⟨910117, by decide⟩ =
    .split (coordinate 11) (![⟨910029, by decide⟩,⟨891951, by decide⟩,⟨910073, by decide⟩,⟨910116, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_70729_910117 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70729 ⟨910117, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 70729
    ⟨910117, by decide⟩ (by decide) (![⟨910029, by decide⟩,⟨891951, by decide⟩,⟨910073, by decide⟩,⟨910116, by decide⟩]) unmarked_context_11_70729_910117 node_context_11_70729_910117
  intro a
  fin_cases a
  · exact context_12_282916_910029
  · exact context_12_282917_891951
  · exact context_12_282918_910073
  · exact context_12_282919_910116

theorem selected_cut_34835 : selected 9 ⟨910172, by decide⟩
    (prefixPartial 12 282920) = some ⟨12, 2, 0, 910172, 282920, 2941, 65536⟩ := by
  decide +kernel

theorem context_12_282920_910172 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 282920 ⟨910172, by decide⟩ :=
  accepted_of_selected 12 282920 ⟨910172, by decide⟩ ⟨12, 2, 0, 910172, 282920, 2941, 65536⟩
    (by decide) selected_cut_34835

theorem selected_cut_34836 : selected 9 ⟨910215, by decide⟩
    (prefixPartial 12 282921) = some ⟨12, 2, 0, 910215, 282921, 2637, 65536⟩ := by
  decide +kernel

theorem context_12_282921_910215 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 282921 ⟨910215, by decide⟩ :=
  accepted_of_selected 12 282921 ⟨910215, by decide⟩ ⟨12, 2, 0, 910215, 282921, 2637, 65536⟩
    (by decide) selected_cut_34836

theorem selected_cut_34837 : selected 9 ⟨910281, by decide⟩
    (prefixPartial 12 282922) = some ⟨12, 2, 0, 910281, 282922, 2993, 65536⟩ := by
  decide +kernel

theorem context_12_282922_910281 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 282922 ⟨910281, by decide⟩ :=
  accepted_of_selected 12 282922 ⟨910281, by decide⟩ ⟨12, 2, 0, 910281, 282922, 2993, 65536⟩
    (by decide) selected_cut_34837

theorem selected_cut_34838 : selected 9 ⟨910325, by decide⟩
    (prefixPartial 12 282923) = some ⟨12, 2, 0, 910325, 282923, 2657, 65536⟩ := by
  decide +kernel

theorem context_12_282923_910325 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 282923 ⟨910325, by decide⟩ :=
  accepted_of_selected 12 282923 ⟨910325, by decide⟩ ⟨12, 2, 0, 910325, 282923, 2657, 65536⟩
    (by decide) selected_cut_34838

theorem unmarked_context_11_70730_910326 : frontier 10 ⟨910326, by decide⟩
    (prefixCache 11 70730) (prefixPartial 11 70730) = false := by
  decide +kernel

theorem node_context_11_70730_910326 : EJMOriginalGlobalDAGData.nodes 10 ⟨910326, by decide⟩ =
    .split (coordinate 11) (![⟨910172, by decide⟩,⟨910215, by decide⟩,⟨910281, by decide⟩,⟨910325, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_70730_910326 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70730 ⟨910326, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 70730
    ⟨910326, by decide⟩ (by decide) (![⟨910172, by decide⟩,⟨910215, by decide⟩,⟨910281, by decide⟩,⟨910325, by decide⟩]) unmarked_context_11_70730_910326 node_context_11_70730_910326
  intro a
  fin_cases a
  · exact context_12_282920_910172
  · exact context_12_282921_910215
  · exact context_12_282922_910281
  · exact context_12_282923_910325

theorem selected_cut_34839 : selected 9 ⟨910376, by decide⟩
    (prefixPartial 12 282924) = some ⟨12, 2, 0, 910376, 282924, 2649, 65536⟩ := by
  decide +kernel

theorem context_12_282924_910376 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 282924 ⟨910376, by decide⟩ :=
  accepted_of_selected 12 282924 ⟨910376, by decide⟩ ⟨12, 2, 0, 910376, 282924, 2649, 65536⟩
    (by decide) selected_cut_34839

theorem selected_cut_34840 : selected 9 ⟨910415, by decide⟩
    (prefixPartial 12 282925) = some ⟨12, 2, 0, 910415, 282925, 2405, 65536⟩ := by
  decide +kernel

theorem context_12_282925_910415 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 282925 ⟨910415, by decide⟩ :=
  accepted_of_selected 12 282925 ⟨910415, by decide⟩ ⟨12, 2, 0, 910415, 282925, 2405, 65536⟩
    (by decide) selected_cut_34840

theorem selected_cut_34841 : selected 9 ⟨910469, by decide⟩
    (prefixPartial 12 282926) = some ⟨12, 2, 0, 910469, 282926, 2713, 65536⟩ := by
  decide +kernel

theorem context_12_282926_910469 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 282926 ⟨910469, by decide⟩ :=
  accepted_of_selected 12 282926 ⟨910469, by decide⟩ ⟨12, 2, 0, 910469, 282926, 2713, 65536⟩
    (by decide) selected_cut_34841

theorem selected_cut_34842 : selected 9 ⟨910514, by decide⟩
    (prefixPartial 12 282927) = some ⟨12, 2, 0, 910514, 282927, 2397, 65536⟩ := by
  decide +kernel

theorem context_12_282927_910514 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 282927 ⟨910514, by decide⟩ :=
  accepted_of_selected 12 282927 ⟨910514, by decide⟩ ⟨12, 2, 0, 910514, 282927, 2397, 65536⟩
    (by decide) selected_cut_34842

theorem unmarked_context_11_70731_910515 : frontier 10 ⟨910515, by decide⟩
    (prefixCache 11 70731) (prefixPartial 11 70731) = false := by
  decide +kernel

theorem node_context_11_70731_910515 : EJMOriginalGlobalDAGData.nodes 10 ⟨910515, by decide⟩ =
    .split (coordinate 11) (![⟨910376, by decide⟩,⟨910415, by decide⟩,⟨910469, by decide⟩,⟨910514, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_70731_910515 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70731 ⟨910515, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 70731
    ⟨910515, by decide⟩ (by decide) (![⟨910376, by decide⟩,⟨910415, by decide⟩,⟨910469, by decide⟩,⟨910514, by decide⟩]) unmarked_context_11_70731_910515 node_context_11_70731_910515
  intro a
  fin_cases a
  · exact context_12_282924_910376
  · exact context_12_282925_910415
  · exact context_12_282926_910469
  · exact context_12_282927_910514

theorem unmarked_context_10_17682_910516 : frontier 11 ⟨910516, by decide⟩
    (prefixCache 10 17682) (prefixPartial 10 17682) = false := by
  decide +kernel

theorem node_context_10_17682_910516 : EJMOriginalGlobalDAGData.nodes 11 ⟨910516, by decide⟩ =
    .split (coordinate 10) (![⟨909971, by decide⟩,⟨910117, by decide⟩,⟨910326, by decide⟩,⟨910515, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17682_910516 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17682 ⟨910516, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17682
    ⟨910516, by decide⟩ (by decide) (![⟨909971, by decide⟩,⟨910117, by decide⟩,⟨910326, by decide⟩,⟨910515, by decide⟩]) unmarked_context_10_17682_910516 node_context_10_17682_910516
  intro a
  fin_cases a
  · exact context_11_70728_909971
  · exact context_11_70729_910117
  · exact context_11_70730_910326
  · exact context_11_70731_910515

theorem selected_cut_34843 : selected 11 ⟨3440, by decide⟩
    (prefixPartial 10 17683) = some ⟨10, 1, 0, 3440, 17683, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_17683_3440 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17683 ⟨3440, by decide⟩ :=
  accepted_of_selected 10 17683 ⟨3440, by decide⟩ ⟨10, 1, 0, 3440, 17683, 1, 1048576⟩
    (by decide) selected_cut_34843

theorem unmarked_context_9_4420_910517 : frontier 12 ⟨910517, by decide⟩
    (prefixCache 9 4420) (prefixPartial 9 4420) = false := by
  decide +kernel

theorem node_context_9_4420_910517 : EJMOriginalGlobalDAGData.nodes 12 ⟨910517, by decide⟩ =
    .split (coordinate 9) (![⟨909333, by decide⟩,⟨909745, by decide⟩,⟨910516, by decide⟩,⟨3440, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4420_910517 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4420 ⟨910517, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4420
    ⟨910517, by decide⟩ (by decide) (![⟨909333, by decide⟩,⟨909745, by decide⟩,⟨910516, by decide⟩,⟨3440, by decide⟩]) unmarked_context_9_4420_910517 node_context_9_4420_910517
  intro a
  fin_cases a
  · exact context_10_17680_909333
  · exact context_10_17681_909745
  · exact context_10_17682_910516
  · exact context_10_17683_3440

theorem selected_cut_34844 : selected 10 ⟨907917, by decide⟩
    (prefixPartial 11 70736) = some ⟨11, 1, 0, 907917, 70736, 1, 262144⟩ := by
  decide +kernel

theorem context_11_70736_907917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70736 ⟨907917, by decide⟩ :=
  accepted_of_selected 11 70736 ⟨907917, by decide⟩ ⟨11, 1, 0, 907917, 70736, 1, 262144⟩
    (by decide) selected_cut_34844

theorem selected_cut_34845 : selected 10 ⟨910569, by decide⟩
    (prefixPartial 11 70737) = some ⟨11, 2, 0, 910569, 70737, 2405, 262144⟩ := by
  decide +kernel

theorem context_11_70737_910569 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70737 ⟨910569, by decide⟩ :=
  accepted_of_selected 11 70737 ⟨910569, by decide⟩ ⟨11, 2, 0, 910569, 70737, 2405, 262144⟩
    (by decide) selected_cut_34845

theorem selected_cut_34846 : selected 9 ⟨910601, by decide⟩
    (prefixPartial 12 282952) = some ⟨12, 2, 0, 910601, 282952, 1985, 65536⟩ := by
  decide +kernel

theorem context_12_282952_910601 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 282952 ⟨910601, by decide⟩ :=
  accepted_of_selected 12 282952 ⟨910601, by decide⟩ ⟨12, 2, 0, 910601, 282952, 1985, 65536⟩
    (by decide) selected_cut_34846

theorem selected_cut_34847 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 282953) = some ⟨12, 1, 0, 896706, 282953, 1, 65536⟩ := by
  decide +kernel

theorem context_12_282953_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 282953 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 282953 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 282953, 1, 65536⟩
    (by decide) selected_cut_34847

theorem selected_cut_34848 : selected 9 ⟨910631, by decide⟩
    (prefixPartial 12 282954) = some ⟨12, 2, 0, 910631, 282954, 1937, 65536⟩ := by
  decide +kernel

theorem context_12_282954_910631 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 282954 ⟨910631, by decide⟩ :=
  accepted_of_selected 12 282954 ⟨910631, by decide⟩ ⟨12, 2, 0, 910631, 282954, 1937, 65536⟩
    (by decide) selected_cut_34848

theorem selected_cut_34849 : selected 9 ⟨910664, by decide⟩
    (prefixPartial 12 282955) = some ⟨12, 2, 0, 910664, 282955, 1825, 65536⟩ := by
  decide +kernel

theorem context_12_282955_910664 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 282955 ⟨910664, by decide⟩ :=
  accepted_of_selected 12 282955 ⟨910664, by decide⟩ ⟨12, 2, 0, 910664, 282955, 1825, 65536⟩
    (by decide) selected_cut_34849

theorem unmarked_context_11_70738_910665 : frontier 10 ⟨910665, by decide⟩
    (prefixCache 11 70738) (prefixPartial 11 70738) = false := by
  decide +kernel

theorem node_context_11_70738_910665 : EJMOriginalGlobalDAGData.nodes 10 ⟨910665, by decide⟩ =
    .split (coordinate 11) (![⟨910601, by decide⟩,⟨896706, by decide⟩,⟨910631, by decide⟩,⟨910664, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_70738_910665 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70738 ⟨910665, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 70738
    ⟨910665, by decide⟩ (by decide) (![⟨910601, by decide⟩,⟨896706, by decide⟩,⟨910631, by decide⟩,⟨910664, by decide⟩]) unmarked_context_11_70738_910665 node_context_11_70738_910665
  intro a
  fin_cases a
  · exact context_12_282952_910601
  · exact context_12_282953_896706
  · exact context_12_282954_910631
  · exact context_12_282955_910664

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
