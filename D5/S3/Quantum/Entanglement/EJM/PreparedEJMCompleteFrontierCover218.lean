/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover217
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_20931 : selected 9 ⟨536672, by decide⟩
    (prefixPartial 12 74610) = some ⟨12, 2, 0, 536672, 74610, 2073, 65536⟩ := by
  decide +kernel

theorem context_12_74610_536672 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74610 ⟨536672, by decide⟩ :=
  accepted_of_selected 12 74610 ⟨536672, by decide⟩ ⟨12, 2, 0, 536672, 74610, 2073, 65536⟩
    (by decide) selected_cut_20931

theorem selected_cut_20932 : selected 9 ⟨536696, by decide⟩
    (prefixPartial 12 74611) = some ⟨12, 2, 0, 536696, 74611, 1725, 65536⟩ := by
  decide +kernel

theorem context_12_74611_536696 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74611 ⟨536696, by decide⟩ :=
  accepted_of_selected 12 74611 ⟨536696, by decide⟩ ⟨12, 2, 0, 536696, 74611, 1725, 65536⟩
    (by decide) selected_cut_20932

theorem unmarked_context_11_18652_536697 : frontier 10 ⟨536697, by decide⟩
    (prefixCache 11 18652) (prefixPartial 11 18652) = false := by
  decide +kernel

theorem node_context_11_18652_536697 : EJMOriginalGlobalDAGData.nodes 10 ⟨536697, by decide⟩ =
    .split (coordinate 11) (![⟨536607, by decide⟩,⟨536637, by decide⟩,⟨536672, by decide⟩,⟨536696, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18652_536697 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18652 ⟨536697, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18652
    ⟨536697, by decide⟩ (by decide) (![⟨536607, by decide⟩,⟨536637, by decide⟩,⟨536672, by decide⟩,⟨536696, by decide⟩]) unmarked_context_11_18652_536697 node_context_11_18652_536697
  intro a
  fin_cases a
  · exact context_12_74608_536607
  · exact context_12_74609_536637
  · exact context_12_74610_536672
  · exact context_12_74611_536696

theorem selected_cut_20933 : selected 9 ⟨536747, by decide⟩
    (prefixPartial 12 74612) = some ⟨12, 2, 0, 536747, 74612, 1769, 65536⟩ := by
  decide +kernel

theorem context_12_74612_536747 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74612 ⟨536747, by decide⟩ :=
  accepted_of_selected 12 74612 ⟨536747, by decide⟩ ⟨12, 2, 0, 536747, 74612, 1769, 65536⟩
    (by decide) selected_cut_20933

theorem selected_cut_20934 : selected 9 ⟨536773, by decide⟩
    (prefixPartial 12 74613) = some ⟨12, 2, 0, 536773, 74613, 1917, 65536⟩ := by
  decide +kernel

theorem context_12_74613_536773 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74613 ⟨536773, by decide⟩ :=
  accepted_of_selected 12 74613 ⟨536773, by decide⟩ ⟨12, 2, 0, 536773, 74613, 1917, 65536⟩
    (by decide) selected_cut_20934

theorem selected_cut_20935 : selected 9 ⟨536821, by decide⟩
    (prefixPartial 12 74614) = some ⟨12, 2, 0, 536821, 74614, 1917, 65536⟩ := by
  decide +kernel

theorem context_12_74614_536821 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74614 ⟨536821, by decide⟩ :=
  accepted_of_selected 12 74614 ⟨536821, by decide⟩ ⟨12, 2, 0, 536821, 74614, 1917, 65536⟩
    (by decide) selected_cut_20935

theorem selected_cut_20936 : selected 9 ⟨536853, by decide⟩
    (prefixPartial 12 74615) = some ⟨12, 2, 0, 536853, 74615, 1673, 65536⟩ := by
  decide +kernel

theorem context_12_74615_536853 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74615 ⟨536853, by decide⟩ :=
  accepted_of_selected 12 74615 ⟨536853, by decide⟩ ⟨12, 2, 0, 536853, 74615, 1673, 65536⟩
    (by decide) selected_cut_20936

theorem unmarked_context_11_18653_536854 : frontier 10 ⟨536854, by decide⟩
    (prefixCache 11 18653) (prefixPartial 11 18653) = false := by
  decide +kernel

theorem node_context_11_18653_536854 : EJMOriginalGlobalDAGData.nodes 10 ⟨536854, by decide⟩ =
    .split (coordinate 11) (![⟨536747, by decide⟩,⟨536773, by decide⟩,⟨536821, by decide⟩,⟨536853, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18653_536854 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18653 ⟨536854, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18653
    ⟨536854, by decide⟩ (by decide) (![⟨536747, by decide⟩,⟨536773, by decide⟩,⟨536821, by decide⟩,⟨536853, by decide⟩]) unmarked_context_11_18653_536854 node_context_11_18653_536854
  intro a
  fin_cases a
  · exact context_12_74612_536747
  · exact context_12_74613_536773
  · exact context_12_74614_536821
  · exact context_12_74615_536853

theorem selected_cut_20937 : selected 9 ⟨536905, by decide⟩
    (prefixPartial 12 74616) = some ⟨12, 2, 0, 536905, 74616, 1737, 65536⟩ := by
  decide +kernel

theorem context_12_74616_536905 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74616 ⟨536905, by decide⟩ :=
  accepted_of_selected 12 74616 ⟨536905, by decide⟩ ⟨12, 2, 0, 536905, 74616, 1737, 65536⟩
    (by decide) selected_cut_20937

theorem selected_cut_20938 : selected 9 ⟨536980, by decide⟩
    (prefixPartial 12 74617) = some ⟨12, 2, 0, 536980, 74617, 2121, 65536⟩ := by
  decide +kernel

theorem context_12_74617_536980 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74617 ⟨536980, by decide⟩ :=
  accepted_of_selected 12 74617 ⟨536980, by decide⟩ ⟨12, 2, 0, 536980, 74617, 2121, 65536⟩
    (by decide) selected_cut_20938

theorem selected_cut_20939 : selected 9 ⟨537019, by decide⟩
    (prefixPartial 12 74618) = some ⟨12, 2, 0, 537019, 74618, 1861, 65536⟩ := by
  decide +kernel

theorem context_12_74618_537019 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74618 ⟨537019, by decide⟩ :=
  accepted_of_selected 12 74618 ⟨537019, by decide⟩ ⟨12, 2, 0, 537019, 74618, 1861, 65536⟩
    (by decide) selected_cut_20939

theorem selected_cut_20940 : selected 9 ⟨537043, by decide⟩
    (prefixPartial 12 74619) = some ⟨12, 2, 0, 537043, 74619, 1601, 65536⟩ := by
  decide +kernel

theorem context_12_74619_537043 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74619 ⟨537043, by decide⟩ :=
  accepted_of_selected 12 74619 ⟨537043, by decide⟩ ⟨12, 2, 0, 537043, 74619, 1601, 65536⟩
    (by decide) selected_cut_20940

theorem unmarked_context_11_18654_537044 : frontier 10 ⟨537044, by decide⟩
    (prefixCache 11 18654) (prefixPartial 11 18654) = false := by
  decide +kernel

theorem node_context_11_18654_537044 : EJMOriginalGlobalDAGData.nodes 10 ⟨537044, by decide⟩ =
    .split (coordinate 11) (![⟨536905, by decide⟩,⟨536980, by decide⟩,⟨537019, by decide⟩,⟨537043, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18654_537044 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18654 ⟨537044, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18654
    ⟨537044, by decide⟩ (by decide) (![⟨536905, by decide⟩,⟨536980, by decide⟩,⟨537019, by decide⟩,⟨537043, by decide⟩]) unmarked_context_11_18654_537044 node_context_11_18654_537044
  intro a
  fin_cases a
  · exact context_12_74616_536905
  · exact context_12_74617_536980
  · exact context_12_74618_537019
  · exact context_12_74619_537043

theorem selected_cut_20941 : selected 9 ⟨537080, by decide⟩
    (prefixPartial 12 74620) = some ⟨12, 2, 0, 537080, 74620, 1461, 65536⟩ := by
  decide +kernel

theorem context_12_74620_537080 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74620 ⟨537080, by decide⟩ :=
  accepted_of_selected 12 74620 ⟨537080, by decide⟩ ⟨12, 2, 0, 537080, 74620, 1461, 65536⟩
    (by decide) selected_cut_20941

theorem selected_cut_20942 : selected 9 ⟨537115, by decide⟩
    (prefixPartial 12 74621) = some ⟨12, 2, 0, 537115, 74621, 1613, 65536⟩ := by
  decide +kernel

theorem context_12_74621_537115 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74621 ⟨537115, by decide⟩ :=
  accepted_of_selected 12 74621 ⟨537115, by decide⟩ ⟨12, 2, 0, 537115, 74621, 1613, 65536⟩
    (by decide) selected_cut_20942

theorem selected_cut_20943 : selected 9 ⟨537138, by decide⟩
    (prefixPartial 12 74622) = some ⟨12, 2, 0, 537138, 74622, 1473, 65536⟩ := by
  decide +kernel

theorem context_12_74622_537138 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74622 ⟨537138, by decide⟩ :=
  accepted_of_selected 12 74622 ⟨537138, by decide⟩ ⟨12, 2, 0, 537138, 74622, 1473, 65536⟩
    (by decide) selected_cut_20943

theorem selected_cut_20944 : selected 9 ⟨512556, by decide⟩
    (prefixPartial 12 74623) = some ⟨12, 1, 0, 512556, 74623, 1, 65536⟩ := by
  decide +kernel

theorem context_12_74623_512556 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74623 ⟨512556, by decide⟩ :=
  accepted_of_selected 12 74623 ⟨512556, by decide⟩ ⟨12, 1, 0, 512556, 74623, 1, 65536⟩
    (by decide) selected_cut_20944

theorem unmarked_context_11_18655_537139 : frontier 10 ⟨537139, by decide⟩
    (prefixCache 11 18655) (prefixPartial 11 18655) = false := by
  decide +kernel

theorem node_context_11_18655_537139 : EJMOriginalGlobalDAGData.nodes 10 ⟨537139, by decide⟩ =
    .split (coordinate 11) (![⟨537080, by decide⟩,⟨537115, by decide⟩,⟨537138, by decide⟩,⟨512556, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18655_537139 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18655 ⟨537139, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18655
    ⟨537139, by decide⟩ (by decide) (![⟨537080, by decide⟩,⟨537115, by decide⟩,⟨537138, by decide⟩,⟨512556, by decide⟩]) unmarked_context_11_18655_537139 node_context_11_18655_537139
  intro a
  fin_cases a
  · exact context_12_74620_537080
  · exact context_12_74621_537115
  · exact context_12_74622_537138
  · exact context_12_74623_512556

theorem unmarked_context_10_4663_537140 : frontier 11 ⟨537140, by decide⟩
    (prefixCache 10 4663) (prefixPartial 10 4663) = false := by
  decide +kernel

theorem node_context_10_4663_537140 : EJMOriginalGlobalDAGData.nodes 11 ⟨537140, by decide⟩ =
    .split (coordinate 10) (![⟨536697, by decide⟩,⟨536854, by decide⟩,⟨537044, by decide⟩,⟨537139, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4663_537140 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4663 ⟨537140, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4663
    ⟨537140, by decide⟩ (by decide) (![⟨536697, by decide⟩,⟨536854, by decide⟩,⟨537044, by decide⟩,⟨537139, by decide⟩]) unmarked_context_10_4663_537140 node_context_10_4663_537140
  intro a
  fin_cases a
  · exact context_11_18652_536697
  · exact context_11_18653_536854
  · exact context_11_18654_537044
  · exact context_11_18655_537139

theorem unmarked_context_9_1165_537141 : frontier 12 ⟨537141, by decide⟩
    (prefixCache 9 1165) (prefixPartial 9 1165) = false := by
  decide +kernel

theorem node_context_9_1165_537141 : EJMOriginalGlobalDAGData.nodes 12 ⟨537141, by decide⟩ =
    .split (coordinate 9) (![⟨145424, by decide⟩,⟨536150, by decide⟩,⟨536573, by decide⟩,⟨537140, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1165_537141 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1165 ⟨537141, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1165
    ⟨537141, by decide⟩ (by decide) (![⟨145424, by decide⟩,⟨536150, by decide⟩,⟨536573, by decide⟩,⟨537140, by decide⟩]) unmarked_context_9_1165_537141 node_context_9_1165_537141
  intro a
  fin_cases a
  · exact context_10_4660_145424
  · exact context_10_4661_536150
  · exact context_10_4662_536573
  · exact context_10_4663_537140

theorem selected_cut_20945 : selected 11 ⟨145424, by decide⟩
    (prefixPartial 10 4664) = some ⟨10, 1, 0, 145424, 4664, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_4664_145424 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4664 ⟨145424, by decide⟩ :=
  accepted_of_selected 10 4664 ⟨145424, by decide⟩ ⟨10, 1, 0, 145424, 4664, 1, 1048576⟩
    (by decide) selected_cut_20945

theorem selected_cut_20946 : selected 10 ⟨537213, by decide⟩
    (prefixPartial 11 18660) = some ⟨11, 2, 0, 537213, 18660, 3793, 262144⟩ := by
  decide +kernel

theorem context_11_18660_537213 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18660 ⟨537213, by decide⟩ :=
  accepted_of_selected 11 18660 ⟨537213, by decide⟩ ⟨11, 2, 0, 537213, 18660, 3793, 262144⟩
    (by decide) selected_cut_20946

theorem selected_cut_20947 : selected 10 ⟨537291, by decide⟩
    (prefixPartial 11 18661) = some ⟨11, 2, 0, 537291, 18661, 2777, 262144⟩ := by
  decide +kernel

theorem context_11_18661_537291 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18661 ⟨537291, by decide⟩ :=
  accepted_of_selected 11 18661 ⟨537291, by decide⟩ ⟨11, 2, 0, 537291, 18661, 2777, 262144⟩
    (by decide) selected_cut_20947

theorem selected_cut_20948 : selected 10 ⟨537332, by decide⟩
    (prefixPartial 11 18662) = some ⟨11, 2, 0, 537332, 18662, 1553, 262144⟩ := by
  decide +kernel

theorem context_11_18662_537332 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18662 ⟨537332, by decide⟩ :=
  accepted_of_selected 11 18662 ⟨537332, by decide⟩ ⟨11, 2, 0, 537332, 18662, 1553, 262144⟩
    (by decide) selected_cut_20948

theorem selected_cut_20949 : selected 10 ⟨537349, by decide⟩
    (prefixPartial 11 18663) = some ⟨11, 2, 0, 537349, 18663, 605, 262144⟩ := by
  decide +kernel

theorem context_11_18663_537349 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18663 ⟨537349, by decide⟩ :=
  accepted_of_selected 11 18663 ⟨537349, by decide⟩ ⟨11, 2, 0, 537349, 18663, 605, 262144⟩
    (by decide) selected_cut_20949

theorem unmarked_context_10_4665_537350 : frontier 11 ⟨537350, by decide⟩
    (prefixCache 10 4665) (prefixPartial 10 4665) = false := by
  decide +kernel

theorem node_context_10_4665_537350 : EJMOriginalGlobalDAGData.nodes 11 ⟨537350, by decide⟩ =
    .split (coordinate 10) (![⟨537213, by decide⟩,⟨537291, by decide⟩,⟨537332, by decide⟩,⟨537349, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4665_537350 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4665 ⟨537350, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4665
    ⟨537350, by decide⟩ (by decide) (![⟨537213, by decide⟩,⟨537291, by decide⟩,⟨537332, by decide⟩,⟨537349, by decide⟩]) unmarked_context_10_4665_537350 node_context_10_4665_537350
  intro a
  fin_cases a
  · exact context_11_18660_537213
  · exact context_11_18661_537291
  · exact context_11_18662_537332
  · exact context_11_18663_537349

theorem selected_cut_20950 : selected 11 ⟨145424, by decide⟩
    (prefixPartial 10 4666) = some ⟨10, 1, 0, 145424, 4666, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_4666_145424 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4666 ⟨145424, by decide⟩ :=
  accepted_of_selected 10 4666 ⟨145424, by decide⟩ ⟨10, 1, 0, 145424, 4666, 1, 1048576⟩
    (by decide) selected_cut_20950

theorem selected_cut_20951 : selected 10 ⟨537417, by decide⟩
    (prefixPartial 11 18668) = some ⟨11, 2, 0, 537417, 18668, 2737, 262144⟩ := by
  decide +kernel

theorem context_11_18668_537417 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18668 ⟨537417, by decide⟩ :=
  accepted_of_selected 11 18668 ⟨537417, by decide⟩ ⟨11, 2, 0, 537417, 18668, 2737, 262144⟩
    (by decide) selected_cut_20951

theorem selected_cut_20952 : selected 10 ⟨537470, by decide⟩
    (prefixPartial 11 18669) = some ⟨11, 2, 0, 537470, 18669, 2413, 262144⟩ := by
  decide +kernel

theorem context_11_18669_537470 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18669 ⟨537470, by decide⟩ :=
  accepted_of_selected 11 18669 ⟨537470, by decide⟩ ⟨11, 2, 0, 537470, 18669, 2413, 262144⟩
    (by decide) selected_cut_20952

theorem selected_cut_20953 : selected 10 ⟨537536, by decide⟩
    (prefixPartial 11 18670) = some ⟨11, 2, 0, 537536, 18670, 1785, 262144⟩ := by
  decide +kernel

theorem context_11_18670_537536 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18670 ⟨537536, by decide⟩ :=
  accepted_of_selected 11 18670 ⟨537536, by decide⟩ ⟨11, 2, 0, 537536, 18670, 1785, 262144⟩
    (by decide) selected_cut_20953

theorem selected_cut_20954 : selected 10 ⟨537556, by decide⟩
    (prefixPartial 11 18671) = some ⟨11, 2, 0, 537556, 18671, 873, 262144⟩ := by
  decide +kernel

theorem context_11_18671_537556 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18671 ⟨537556, by decide⟩ :=
  accepted_of_selected 11 18671 ⟨537556, by decide⟩ ⟨11, 2, 0, 537556, 18671, 873, 262144⟩
    (by decide) selected_cut_20954

theorem unmarked_context_10_4667_537557 : frontier 11 ⟨537557, by decide⟩
    (prefixCache 10 4667) (prefixPartial 10 4667) = false := by
  decide +kernel

theorem node_context_10_4667_537557 : EJMOriginalGlobalDAGData.nodes 11 ⟨537557, by decide⟩ =
    .split (coordinate 10) (![⟨537417, by decide⟩,⟨537470, by decide⟩,⟨537536, by decide⟩,⟨537556, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4667_537557 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4667 ⟨537557, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4667
    ⟨537557, by decide⟩ (by decide) (![⟨537417, by decide⟩,⟨537470, by decide⟩,⟨537536, by decide⟩,⟨537556, by decide⟩]) unmarked_context_10_4667_537557 node_context_10_4667_537557
  intro a
  fin_cases a
  · exact context_11_18668_537417
  · exact context_11_18669_537470
  · exact context_11_18670_537536
  · exact context_11_18671_537556

theorem unmarked_context_9_1166_537558 : frontier 12 ⟨537558, by decide⟩
    (prefixCache 9 1166) (prefixPartial 9 1166) = false := by
  decide +kernel

theorem node_context_9_1166_537558 : EJMOriginalGlobalDAGData.nodes 12 ⟨537558, by decide⟩ =
    .split (coordinate 9) (![⟨145424, by decide⟩,⟨537350, by decide⟩,⟨145424, by decide⟩,⟨537557, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1166_537558 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1166 ⟨537558, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1166
    ⟨537558, by decide⟩ (by decide) (![⟨145424, by decide⟩,⟨537350, by decide⟩,⟨145424, by decide⟩,⟨537557, by decide⟩]) unmarked_context_9_1166_537558 node_context_9_1166_537558
  intro a
  fin_cases a
  · exact context_10_4664_145424
  · exact context_10_4665_537350
  · exact context_10_4666_145424
  · exact context_10_4667_537557

theorem selected_cut_20955 : selected 12 ⟨537596, by decide⟩
    (prefixPartial 9 1167) = some ⟨9, 2, 0, 537596, 1167, 813, 4194304⟩ := by
  decide +kernel

theorem context_9_1167_537596 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1167 ⟨537596, by decide⟩ :=
  accepted_of_selected 9 1167 ⟨537596, by decide⟩ ⟨9, 2, 0, 537596, 1167, 813, 4194304⟩
    (by decide) selected_cut_20955

theorem unmarked_context_8_291_537597 : frontier 13 ⟨537597, by decide⟩
    (prefixCache 8 291) (prefixPartial 8 291) = false := by
  decide +kernel

theorem node_context_8_291_537597 : EJMOriginalGlobalDAGData.nodes 13 ⟨537597, by decide⟩ =
    .split (coordinate 8) (![⟨535068, by decide⟩,⟨537141, by decide⟩,⟨537558, by decide⟩,⟨537596, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_291_537597 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 291 ⟨537597, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 291
    ⟨537597, by decide⟩ (by decide) (![⟨535068, by decide⟩,⟨537141, by decide⟩,⟨537558, by decide⟩,⟨537596, by decide⟩]) unmarked_context_8_291_537597 node_context_8_291_537597
  intro a
  fin_cases a
  · exact context_9_1164_535068
  · exact context_9_1165_537141
  · exact context_9_1166_537558
  · exact context_9_1167_537596

theorem unmarked_context_7_72_537598 : frontier 14 ⟨537598, by decide⟩
    (prefixCache 7 72) (prefixPartial 7 72) = false := by
  decide +kernel

theorem node_context_7_72_537598 : EJMOriginalGlobalDAGData.nodes 14 ⟨537598, by decide⟩ =
    .split (coordinate 7) (![⟨523865, by decide⟩,⟨531553, by decide⟩,⟨158379, by decide⟩,⟨537597, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_7_72_537598 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 72 ⟨537598, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 7 72
    ⟨537598, by decide⟩ (by decide) (![⟨523865, by decide⟩,⟨531553, by decide⟩,⟨158379, by decide⟩,⟨537597, by decide⟩]) unmarked_context_7_72_537598 node_context_7_72_537598
  intro a
  fin_cases a
  · exact context_8_288_523865
  · exact context_8_289_531553
  · exact context_8_290_158379
  · exact context_8_291_537597

theorem selected_cut_20956 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 18688) = some ⟨11, 1, 0, 434745, 18688, 1, 262144⟩ := by
  decide +kernel

theorem context_11_18688_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18688 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 18688 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 18688, 1, 262144⟩
    (by decide) selected_cut_20956

theorem selected_cut_20957 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 74756) = some ⟨12, 1, 0, 448748, 74756, 1, 65536⟩ := by
  decide +kernel

theorem context_12_74756_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74756 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 74756 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 74756, 1, 65536⟩
    (by decide) selected_cut_20957

theorem selected_cut_20958 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 74757) = some ⟨12, 1, 0, 34034, 74757, 1, 65536⟩ := by
  decide +kernel

theorem context_12_74757_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74757 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 74757 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 74757, 1, 65536⟩
    (by decide) selected_cut_20958

theorem selected_cut_20959 : selected 8 ⟨537658, by decide⟩
    (prefixPartial 13 299032) = some ⟨13, 2, 0, 537658, 299032, 2253, 16384⟩ := by
  decide +kernel

theorem context_13_299032_537658 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299032 ⟨537658, by decide⟩ :=
  accepted_of_selected 13 299032 ⟨537658, by decide⟩ ⟨13, 2, 0, 537658, 299032, 2253, 16384⟩
    (by decide) selected_cut_20959

theorem selected_cut_20960 : selected 8 ⟨537700, by decide⟩
    (prefixPartial 13 299033) = some ⟨13, 2, 0, 537700, 299033, 2573, 16384⟩ := by
  decide +kernel

theorem context_13_299033_537700 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299033 ⟨537700, by decide⟩ :=
  accepted_of_selected 13 299033 ⟨537700, by decide⟩ ⟨13, 2, 0, 537700, 299033, 2573, 16384⟩
    (by decide) selected_cut_20960

theorem selected_cut_20961 : selected 8 ⟨537728, by decide⟩
    (prefixPartial 13 299034) = some ⟨13, 2, 0, 537728, 299034, 1821, 16384⟩ := by
  decide +kernel

theorem context_13_299034_537728 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299034 ⟨537728, by decide⟩ :=
  accepted_of_selected 13 299034 ⟨537728, by decide⟩ ⟨13, 2, 0, 537728, 299034, 1821, 16384⟩
    (by decide) selected_cut_20961

theorem selected_cut_20962 : selected 8 ⟨537760, by decide⟩
    (prefixPartial 13 299035) = some ⟨13, 2, 0, 537760, 299035, 1081, 16384⟩ := by
  decide +kernel

theorem context_13_299035_537760 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299035 ⟨537760, by decide⟩ :=
  accepted_of_selected 13 299035 ⟨537760, by decide⟩ ⟨13, 2, 0, 537760, 299035, 1081, 16384⟩
    (by decide) selected_cut_20962

theorem unmarked_context_12_74758_537761 : frontier 9 ⟨537761, by decide⟩
    (prefixCache 12 74758) (prefixPartial 12 74758) = false := by
  decide +kernel

theorem node_context_12_74758_537761 : EJMOriginalGlobalDAGData.nodes 9 ⟨537761, by decide⟩ =
    .split (coordinate 12) (![⟨537658, by decide⟩,⟨537700, by decide⟩,⟨537728, by decide⟩,⟨537760, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74758_537761 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74758 ⟨537761, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74758
    ⟨537761, by decide⟩ (by decide) (![⟨537658, by decide⟩,⟨537700, by decide⟩,⟨537728, by decide⟩,⟨537760, by decide⟩]) unmarked_context_12_74758_537761 node_context_12_74758_537761
  intro a
  fin_cases a
  · exact context_13_299032_537658
  · exact context_13_299033_537700
  · exact context_13_299034_537728
  · exact context_13_299035_537760

theorem selected_cut_20963 : selected 8 ⟨537817, by decide⟩
    (prefixPartial 13 299036) = some ⟨13, 2, 0, 537817, 299036, 2245, 16384⟩ := by
  decide +kernel

theorem context_13_299036_537817 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299036 ⟨537817, by decide⟩ :=
  accepted_of_selected 13 299036 ⟨537817, by decide⟩ ⟨13, 2, 0, 537817, 299036, 2245, 16384⟩
    (by decide) selected_cut_20963

theorem selected_cut_20964 : selected 8 ⟨537858, by decide⟩
    (prefixPartial 13 299037) = some ⟨13, 2, 0, 537858, 299037, 2765, 16384⟩ := by
  decide +kernel

theorem context_13_299037_537858 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299037 ⟨537858, by decide⟩ :=
  accepted_of_selected 13 299037 ⟨537858, by decide⟩ ⟨13, 2, 0, 537858, 299037, 2765, 16384⟩
    (by decide) selected_cut_20964

theorem selected_cut_20965 : selected 8 ⟨537897, by decide⟩
    (prefixPartial 13 299038) = some ⟨13, 2, 0, 537897, 299038, 2241, 16384⟩ := by
  decide +kernel

theorem context_13_299038_537897 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299038 ⟨537897, by decide⟩ :=
  accepted_of_selected 13 299038 ⟨537897, by decide⟩ ⟨13, 2, 0, 537897, 299038, 2241, 16384⟩
    (by decide) selected_cut_20965

theorem selected_cut_20966 : selected 8 ⟨537917, by decide⟩
    (prefixPartial 13 299039) = some ⟨13, 2, 0, 537917, 299039, 993, 16384⟩ := by
  decide +kernel

theorem context_13_299039_537917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299039 ⟨537917, by decide⟩ :=
  accepted_of_selected 13 299039 ⟨537917, by decide⟩ ⟨13, 2, 0, 537917, 299039, 993, 16384⟩
    (by decide) selected_cut_20966

theorem unmarked_context_12_74759_537918 : frontier 9 ⟨537918, by decide⟩
    (prefixCache 12 74759) (prefixPartial 12 74759) = false := by
  decide +kernel

theorem node_context_12_74759_537918 : EJMOriginalGlobalDAGData.nodes 9 ⟨537918, by decide⟩ =
    .split (coordinate 12) (![⟨537817, by decide⟩,⟨537858, by decide⟩,⟨537897, by decide⟩,⟨537917, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74759_537918 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74759 ⟨537918, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74759
    ⟨537918, by decide⟩ (by decide) (![⟨537817, by decide⟩,⟨537858, by decide⟩,⟨537897, by decide⟩,⟨537917, by decide⟩]) unmarked_context_12_74759_537918 node_context_12_74759_537918
  intro a
  fin_cases a
  · exact context_13_299036_537817
  · exact context_13_299037_537858
  · exact context_13_299038_537897
  · exact context_13_299039_537917

theorem unmarked_context_11_18689_537919 : frontier 10 ⟨537919, by decide⟩
    (prefixCache 11 18689) (prefixPartial 11 18689) = false := by
  decide +kernel

theorem node_context_11_18689_537919 : EJMOriginalGlobalDAGData.nodes 10 ⟨537919, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨34034, by decide⟩,⟨537761, by decide⟩,⟨537918, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18689_537919 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18689 ⟨537919, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18689
    ⟨537919, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨34034, by decide⟩,⟨537761, by decide⟩,⟨537918, by decide⟩]) unmarked_context_11_18689_537919 node_context_11_18689_537919
  intro a
  fin_cases a
  · exact context_12_74756_448748
  · exact context_12_74757_34034
  · exact context_12_74758_537761
  · exact context_12_74759_537918

theorem selected_cut_20967 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 74760) = some ⟨12, 1, 0, 448748, 74760, 1, 65536⟩ := by
  decide +kernel

theorem context_12_74760_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74760 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 74760 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 74760, 1, 65536⟩
    (by decide) selected_cut_20967

theorem selected_cut_20968 : selected 8 ⟨537990, by decide⟩
    (prefixPartial 13 299044) = some ⟨13, 2, 0, 537990, 299044, 2393, 16384⟩ := by
  decide +kernel

theorem context_13_299044_537990 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299044 ⟨537990, by decide⟩ :=
  accepted_of_selected 13 299044 ⟨537990, by decide⟩ ⟨13, 2, 0, 537990, 299044, 2393, 16384⟩
    (by decide) selected_cut_20968

theorem selected_cut_20969 : selected 8 ⟨538056, by decide⟩
    (prefixPartial 13 299045) = some ⟨13, 2, 0, 538056, 299045, 2945, 16384⟩ := by
  decide +kernel

theorem context_13_299045_538056 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299045 ⟨538056, by decide⟩ :=
  accepted_of_selected 13 299045 ⟨538056, by decide⟩ ⟨13, 2, 0, 538056, 299045, 2945, 16384⟩
    (by decide) selected_cut_20969

theorem selected_cut_20970 : selected 8 ⟨538102, by decide⟩
    (prefixPartial 13 299046) = some ⟨13, 2, 0, 538102, 299046, 2153, 16384⟩ := by
  decide +kernel

theorem context_13_299046_538102 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299046 ⟨538102, by decide⟩ :=
  accepted_of_selected 13 299046 ⟨538102, by decide⟩ ⟨13, 2, 0, 538102, 299046, 2153, 16384⟩
    (by decide) selected_cut_20970

theorem selected_cut_20971 : selected 8 ⟨538128, by decide⟩
    (prefixPartial 13 299047) = some ⟨13, 2, 0, 538128, 299047, 1021, 16384⟩ := by
  decide +kernel

theorem context_13_299047_538128 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299047 ⟨538128, by decide⟩ :=
  accepted_of_selected 13 299047 ⟨538128, by decide⟩ ⟨13, 2, 0, 538128, 299047, 1021, 16384⟩
    (by decide) selected_cut_20971

theorem unmarked_context_12_74761_538129 : frontier 9 ⟨538129, by decide⟩
    (prefixCache 12 74761) (prefixPartial 12 74761) = false := by
  decide +kernel

theorem node_context_12_74761_538129 : EJMOriginalGlobalDAGData.nodes 9 ⟨538129, by decide⟩ =
    .split (coordinate 12) (![⟨537990, by decide⟩,⟨538056, by decide⟩,⟨538102, by decide⟩,⟨538128, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74761_538129 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74761 ⟨538129, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74761
    ⟨538129, by decide⟩ (by decide) (![⟨537990, by decide⟩,⟨538056, by decide⟩,⟨538102, by decide⟩,⟨538128, by decide⟩]) unmarked_context_12_74761_538129 node_context_12_74761_538129
  intro a
  fin_cases a
  · exact context_13_299044_537990
  · exact context_13_299045_538056
  · exact context_13_299046_538102
  · exact context_13_299047_538128

theorem selected_cut_20972 : selected 9 ⟨524302, by decide⟩
    (prefixPartial 12 74762) = some ⟨12, 1, 0, 524302, 74762, 1, 65536⟩ := by
  decide +kernel

theorem context_12_74762_524302 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74762 ⟨524302, by decide⟩ :=
  accepted_of_selected 12 74762 ⟨524302, by decide⟩ ⟨12, 1, 0, 524302, 74762, 1, 65536⟩
    (by decide) selected_cut_20972

theorem selected_cut_20973 : selected 8 ⟨538192, by decide⟩
    (prefixPartial 13 299052) = some ⟨13, 2, 0, 538192, 299052, 2593, 16384⟩ := by
  decide +kernel

theorem context_13_299052_538192 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299052 ⟨538192, by decide⟩ :=
  accepted_of_selected 13 299052 ⟨538192, by decide⟩ ⟨13, 2, 0, 538192, 299052, 2593, 16384⟩
    (by decide) selected_cut_20973

theorem selected_cut_20974 : selected 8 ⟨538243, by decide⟩
    (prefixPartial 13 299053) = some ⟨13, 2, 0, 538243, 299053, 3149, 16384⟩ := by
  decide +kernel

theorem context_13_299053_538243 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299053 ⟨538243, by decide⟩ :=
  accepted_of_selected 13 299053 ⟨538243, by decide⟩ ⟨13, 2, 0, 538243, 299053, 3149, 16384⟩
    (by decide) selected_cut_20974

theorem selected_cut_20975 : selected 8 ⟨538278, by decide⟩
    (prefixPartial 13 299054) = some ⟨13, 2, 0, 538278, 299054, 2317, 16384⟩ := by
  decide +kernel

theorem context_13_299054_538278 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299054 ⟨538278, by decide⟩ :=
  accepted_of_selected 13 299054 ⟨538278, by decide⟩ ⟨13, 2, 0, 538278, 299054, 2317, 16384⟩
    (by decide) selected_cut_20975

theorem selected_cut_20976 : selected 8 ⟨538293, by decide⟩
    (prefixPartial 13 299055) = some ⟨13, 2, 0, 538293, 299055, 1005, 16384⟩ := by
  decide +kernel

theorem context_13_299055_538293 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299055 ⟨538293, by decide⟩ :=
  accepted_of_selected 13 299055 ⟨538293, by decide⟩ ⟨13, 2, 0, 538293, 299055, 1005, 16384⟩
    (by decide) selected_cut_20976

theorem unmarked_context_12_74763_538294 : frontier 9 ⟨538294, by decide⟩
    (prefixCache 12 74763) (prefixPartial 12 74763) = false := by
  decide +kernel

theorem node_context_12_74763_538294 : EJMOriginalGlobalDAGData.nodes 9 ⟨538294, by decide⟩ =
    .split (coordinate 12) (![⟨538192, by decide⟩,⟨538243, by decide⟩,⟨538278, by decide⟩,⟨538293, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74763_538294 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74763 ⟨538294, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74763
    ⟨538294, by decide⟩ (by decide) (![⟨538192, by decide⟩,⟨538243, by decide⟩,⟨538278, by decide⟩,⟨538293, by decide⟩]) unmarked_context_12_74763_538294 node_context_12_74763_538294
  intro a
  fin_cases a
  · exact context_13_299052_538192
  · exact context_13_299053_538243
  · exact context_13_299054_538278
  · exact context_13_299055_538293

theorem unmarked_context_11_18690_538295 : frontier 10 ⟨538295, by decide⟩
    (prefixCache 11 18690) (prefixPartial 11 18690) = false := by
  decide +kernel

theorem node_context_11_18690_538295 : EJMOriginalGlobalDAGData.nodes 10 ⟨538295, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨538129, by decide⟩,⟨524302, by decide⟩,⟨538294, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18690_538295 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18690 ⟨538295, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18690
    ⟨538295, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨538129, by decide⟩,⟨524302, by decide⟩,⟨538294, by decide⟩]) unmarked_context_11_18690_538295 node_context_11_18690_538295
  intro a
  fin_cases a
  · exact context_12_74760_448748
  · exact context_12_74761_538129
  · exact context_12_74762_524302
  · exact context_12_74763_538294

theorem selected_cut_20977 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 74764) = some ⟨12, 1, 0, 448748, 74764, 1, 65536⟩ := by
  decide +kernel

theorem context_12_74764_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74764 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 74764 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 74764, 1, 65536⟩
    (by decide) selected_cut_20977

theorem selected_cut_20978 : selected 8 ⟨538323, by decide⟩
    (prefixPartial 13 299060) = some ⟨13, 2, 0, 538323, 299060, 917, 16384⟩ := by
  decide +kernel

theorem context_13_299060_538323 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299060 ⟨538323, by decide⟩ :=
  accepted_of_selected 13 299060 ⟨538323, by decide⟩ ⟨13, 2, 0, 538323, 299060, 917, 16384⟩
    (by decide) selected_cut_20978

theorem selected_cut_20979 : selected 8 ⟨538378, by decide⟩
    (prefixPartial 13 299061) = some ⟨13, 2, 0, 538378, 299061, 1649, 16384⟩ := by
  decide +kernel

theorem context_13_299061_538378 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299061 ⟨538378, by decide⟩ :=
  accepted_of_selected 13 299061 ⟨538378, by decide⟩ ⟨13, 2, 0, 538378, 299061, 1649, 16384⟩
    (by decide) selected_cut_20979

theorem selected_cut_20980 : selected 8 ⟨538424, by decide⟩
    (prefixPartial 13 299062) = some ⟨13, 2, 0, 538424, 299062, 1625, 16384⟩ := by
  decide +kernel

theorem context_13_299062_538424 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299062 ⟨538424, by decide⟩ :=
  accepted_of_selected 13 299062 ⟨538424, by decide⟩ ⟨13, 2, 0, 538424, 299062, 1625, 16384⟩
    (by decide) selected_cut_20980

theorem selected_cut_20981 : selected 8 ⟨265883, by decide⟩
    (prefixPartial 13 299063) = some ⟨13, 1, 0, 265883, 299063, 1, 16384⟩ := by
  decide +kernel

theorem context_13_299063_265883 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299063 ⟨265883, by decide⟩ :=
  accepted_of_selected 13 299063 ⟨265883, by decide⟩ ⟨13, 1, 0, 265883, 299063, 1, 16384⟩
    (by decide) selected_cut_20981

theorem unmarked_context_12_74765_538425 : frontier 9 ⟨538425, by decide⟩
    (prefixCache 12 74765) (prefixPartial 12 74765) = false := by
  decide +kernel

theorem node_context_12_74765_538425 : EJMOriginalGlobalDAGData.nodes 9 ⟨538425, by decide⟩ =
    .split (coordinate 12) (![⟨538323, by decide⟩,⟨538378, by decide⟩,⟨538424, by decide⟩,⟨265883, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74765_538425 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74765 ⟨538425, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74765
    ⟨538425, by decide⟩ (by decide) (![⟨538323, by decide⟩,⟨538378, by decide⟩,⟨538424, by decide⟩,⟨265883, by decide⟩]) unmarked_context_12_74765_538425 node_context_12_74765_538425
  intro a
  fin_cases a
  · exact context_13_299060_538323
  · exact context_13_299061_538378
  · exact context_13_299062_538424
  · exact context_13_299063_265883

theorem selected_cut_20982 : selected 8 ⟨538468, by decide⟩
    (prefixPartial 13 299064) = some ⟨13, 2, 0, 538468, 299064, 1981, 16384⟩ := by
  decide +kernel

theorem context_13_299064_538468 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299064 ⟨538468, by decide⟩ :=
  accepted_of_selected 13 299064 ⟨538468, by decide⟩ ⟨13, 2, 0, 538468, 299064, 1981, 16384⟩
    (by decide) selected_cut_20982

theorem selected_cut_20983 : selected 8 ⟨538520, by decide⟩
    (prefixPartial 13 299065) = some ⟨13, 2, 0, 538520, 299065, 3077, 16384⟩ := by
  decide +kernel

theorem context_13_299065_538520 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299065 ⟨538520, by decide⟩ :=
  accepted_of_selected 13 299065 ⟨538520, by decide⟩ ⟨13, 2, 0, 538520, 299065, 3077, 16384⟩
    (by decide) selected_cut_20983

theorem selected_cut_20984 : selected 8 ⟨538539, by decide⟩
    (prefixPartial 13 299066) = some ⟨13, 2, 0, 538539, 299066, 1845, 16384⟩ := by
  decide +kernel

theorem context_13_299066_538539 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299066 ⟨538539, by decide⟩ :=
  accepted_of_selected 13 299066 ⟨538539, by decide⟩ ⟨13, 2, 0, 538539, 299066, 1845, 16384⟩
    (by decide) selected_cut_20984

theorem selected_cut_20985 : selected 8 ⟨538557, by decide⟩
    (prefixPartial 13 299067) = some ⟨13, 2, 0, 538557, 299067, 1093, 16384⟩ := by
  decide +kernel

theorem context_13_299067_538557 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299067 ⟨538557, by decide⟩ :=
  accepted_of_selected 13 299067 ⟨538557, by decide⟩ ⟨13, 2, 0, 538557, 299067, 1093, 16384⟩
    (by decide) selected_cut_20985

theorem unmarked_context_12_74766_538558 : frontier 9 ⟨538558, by decide⟩
    (prefixCache 12 74766) (prefixPartial 12 74766) = false := by
  decide +kernel

theorem node_context_12_74766_538558 : EJMOriginalGlobalDAGData.nodes 9 ⟨538558, by decide⟩ =
    .split (coordinate 12) (![⟨538468, by decide⟩,⟨538520, by decide⟩,⟨538539, by decide⟩,⟨538557, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74766_538558 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74766 ⟨538558, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74766
    ⟨538558, by decide⟩ (by decide) (![⟨538468, by decide⟩,⟨538520, by decide⟩,⟨538539, by decide⟩,⟨538557, by decide⟩]) unmarked_context_12_74766_538558 node_context_12_74766_538558
  intro a
  fin_cases a
  · exact context_13_299064_538468
  · exact context_13_299065_538520
  · exact context_13_299066_538539
  · exact context_13_299067_538557

theorem selected_cut_20986 : selected 9 ⟨518278, by decide⟩
    (prefixPartial 12 74767) = some ⟨12, 1, 0, 518278, 74767, 1, 65536⟩ := by
  decide +kernel

theorem context_12_74767_518278 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74767 ⟨518278, by decide⟩ :=
  accepted_of_selected 12 74767 ⟨518278, by decide⟩ ⟨12, 1, 0, 518278, 74767, 1, 65536⟩
    (by decide) selected_cut_20986

theorem unmarked_context_11_18691_538559 : frontier 10 ⟨538559, by decide⟩
    (prefixCache 11 18691) (prefixPartial 11 18691) = false := by
  decide +kernel

theorem node_context_11_18691_538559 : EJMOriginalGlobalDAGData.nodes 10 ⟨538559, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨538425, by decide⟩,⟨538558, by decide⟩,⟨518278, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18691_538559 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18691 ⟨538559, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18691
    ⟨538559, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨538425, by decide⟩,⟨538558, by decide⟩,⟨518278, by decide⟩]) unmarked_context_11_18691_538559 node_context_11_18691_538559
  intro a
  fin_cases a
  · exact context_12_74764_448748
  · exact context_12_74765_538425
  · exact context_12_74766_538558
  · exact context_12_74767_518278

theorem unmarked_context_10_4672_538560 : frontier 11 ⟨538560, by decide⟩
    (prefixCache 10 4672) (prefixPartial 10 4672) = false := by
  decide +kernel

theorem node_context_10_4672_538560 : EJMOriginalGlobalDAGData.nodes 11 ⟨538560, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨537919, by decide⟩,⟨538295, by decide⟩,⟨538559, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4672_538560 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4672 ⟨538560, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4672
    ⟨538560, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨537919, by decide⟩,⟨538295, by decide⟩,⟨538559, by decide⟩]) unmarked_context_10_4672_538560 node_context_10_4672_538560
  intro a
  fin_cases a
  · exact context_11_18688_434745
  · exact context_11_18689_537919
  · exact context_11_18690_538295
  · exact context_11_18691_538559

theorem selected_cut_20987 : selected 9 ⟨435160, by decide⟩
    (prefixPartial 12 74768) = some ⟨12, 1, 0, 435160, 74768, 1, 65536⟩ := by
  decide +kernel

theorem context_12_74768_435160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74768 ⟨435160, by decide⟩ :=
  accepted_of_selected 12 74768 ⟨435160, by decide⟩ ⟨12, 1, 0, 435160, 74768, 1, 65536⟩
    (by decide) selected_cut_20987

theorem selected_cut_20988 : selected 8 ⟨538581, by decide⟩
    (prefixPartial 13 299076) = some ⟨13, 2, 0, 538581, 299076, 965, 16384⟩ := by
  decide +kernel

theorem context_13_299076_538581 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299076 ⟨538581, by decide⟩ :=
  accepted_of_selected 13 299076 ⟨538581, by decide⟩ ⟨13, 2, 0, 538581, 299076, 965, 16384⟩
    (by decide) selected_cut_20988

theorem selected_cut_20989 : selected 8 ⟨538601, by decide⟩
    (prefixPartial 13 299077) = some ⟨13, 2, 0, 538601, 299077, 1545, 16384⟩ := by
  decide +kernel

theorem context_13_299077_538601 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299077 ⟨538601, by decide⟩ :=
  accepted_of_selected 13 299077 ⟨538601, by decide⟩ ⟨13, 2, 0, 538601, 299077, 1545, 16384⟩
    (by decide) selected_cut_20989

theorem selected_cut_20990 : selected 8 ⟨538618, by decide⟩
    (prefixPartial 13 299078) = some ⟨13, 2, 0, 538618, 299078, 1121, 16384⟩ := by
  decide +kernel

theorem context_13_299078_538618 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299078 ⟨538618, by decide⟩ :=
  accepted_of_selected 13 299078 ⟨538618, by decide⟩ ⟨13, 2, 0, 538618, 299078, 1121, 16384⟩
    (by decide) selected_cut_20990

theorem selected_cut_20991 : selected 8 ⟨538625, by decide⟩
    (prefixPartial 13 299079) = some ⟨13, 2, 0, 538625, 299079, 625, 16384⟩ := by
  decide +kernel

theorem context_13_299079_538625 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299079 ⟨538625, by decide⟩ :=
  accepted_of_selected 13 299079 ⟨538625, by decide⟩ ⟨13, 2, 0, 538625, 299079, 625, 16384⟩
    (by decide) selected_cut_20991

theorem unmarked_context_12_74769_538626 : frontier 9 ⟨538626, by decide⟩
    (prefixCache 12 74769) (prefixPartial 12 74769) = false := by
  decide +kernel

theorem node_context_12_74769_538626 : EJMOriginalGlobalDAGData.nodes 9 ⟨538626, by decide⟩ =
    .split (coordinate 12) (![⟨538581, by decide⟩,⟨538601, by decide⟩,⟨538618, by decide⟩,⟨538625, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74769_538626 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74769 ⟨538626, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74769
    ⟨538626, by decide⟩ (by decide) (![⟨538581, by decide⟩,⟨538601, by decide⟩,⟨538618, by decide⟩,⟨538625, by decide⟩]) unmarked_context_12_74769_538626 node_context_12_74769_538626
  intro a
  fin_cases a
  · exact context_13_299076_538581
  · exact context_13_299077_538601
  · exact context_13_299078_538618
  · exact context_13_299079_538625

theorem selected_cut_20992 : selected 8 ⟨538651, by decide⟩
    (prefixPartial 13 299080) = some ⟨13, 2, 0, 538651, 299080, 1029, 16384⟩ := by
  decide +kernel

theorem context_13_299080_538651 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299080 ⟨538651, by decide⟩ :=
  accepted_of_selected 13 299080 ⟨538651, by decide⟩ ⟨13, 2, 0, 538651, 299080, 1029, 16384⟩
    (by decide) selected_cut_20992

theorem selected_cut_20993 : selected 8 ⟨538669, by decide⟩
    (prefixPartial 13 299081) = some ⟨13, 2, 0, 538669, 299081, 1629, 16384⟩ := by
  decide +kernel

theorem context_13_299081_538669 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299081 ⟨538669, by decide⟩ :=
  accepted_of_selected 13 299081 ⟨538669, by decide⟩ ⟨13, 2, 0, 538669, 299081, 1629, 16384⟩
    (by decide) selected_cut_20993

theorem selected_cut_20994 : selected 8 ⟨538683, by decide⟩
    (prefixPartial 13 299082) = some ⟨13, 2, 0, 538683, 299082, 1093, 16384⟩ := by
  decide +kernel

theorem context_13_299082_538683 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299082 ⟨538683, by decide⟩ :=
  accepted_of_selected 13 299082 ⟨538683, by decide⟩ ⟨13, 2, 0, 538683, 299082, 1093, 16384⟩
    (by decide) selected_cut_20994

theorem selected_cut_20995 : selected 8 ⟨538690, by decide⟩
    (prefixPartial 13 299083) = some ⟨13, 2, 0, 538690, 299083, 669, 16384⟩ := by
  decide +kernel

theorem context_13_299083_538690 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299083 ⟨538690, by decide⟩ :=
  accepted_of_selected 13 299083 ⟨538690, by decide⟩ ⟨13, 2, 0, 538690, 299083, 669, 16384⟩
    (by decide) selected_cut_20995

theorem unmarked_context_12_74770_538691 : frontier 9 ⟨538691, by decide⟩
    (prefixCache 12 74770) (prefixPartial 12 74770) = false := by
  decide +kernel

theorem node_context_12_74770_538691 : EJMOriginalGlobalDAGData.nodes 9 ⟨538691, by decide⟩ =
    .split (coordinate 12) (![⟨538651, by decide⟩,⟨538669, by decide⟩,⟨538683, by decide⟩,⟨538690, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74770_538691 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74770 ⟨538691, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74770
    ⟨538691, by decide⟩ (by decide) (![⟨538651, by decide⟩,⟨538669, by decide⟩,⟨538683, by decide⟩,⟨538690, by decide⟩]) unmarked_context_12_74770_538691 node_context_12_74770_538691
  intro a
  fin_cases a
  · exact context_13_299080_538651
  · exact context_13_299081_538669
  · exact context_13_299082_538683
  · exact context_13_299083_538690

theorem selected_cut_20996 : selected 8 ⟨538716, by decide⟩
    (prefixPartial 13 299084) = some ⟨13, 2, 0, 538716, 299084, 1041, 16384⟩ := by
  decide +kernel

theorem context_13_299084_538716 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299084 ⟨538716, by decide⟩ :=
  accepted_of_selected 13 299084 ⟨538716, by decide⟩ ⟨13, 2, 0, 538716, 299084, 1041, 16384⟩
    (by decide) selected_cut_20996

theorem selected_cut_20997 : selected 8 ⟨538738, by decide⟩
    (prefixPartial 13 299085) = some ⟨13, 2, 0, 538738, 299085, 1889, 16384⟩ := by
  decide +kernel

theorem context_13_299085_538738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299085 ⟨538738, by decide⟩ :=
  accepted_of_selected 13 299085 ⟨538738, by decide⟩ ⟨13, 2, 0, 538738, 299085, 1889, 16384⟩
    (by decide) selected_cut_20997

theorem selected_cut_20998 : selected 8 ⟨538759, by decide⟩
    (prefixPartial 13 299086) = some ⟨13, 2, 0, 538759, 299086, 1369, 16384⟩ := by
  decide +kernel

theorem context_13_299086_538759 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299086 ⟨538759, by decide⟩ :=
  accepted_of_selected 13 299086 ⟨538759, by decide⟩ ⟨13, 2, 0, 538759, 299086, 1369, 16384⟩
    (by decide) selected_cut_20998

theorem selected_cut_20999 : selected 8 ⟨538764, by decide⟩
    (prefixPartial 13 299087) = some ⟨13, 2, 0, 538764, 299087, 613, 16384⟩ := by
  decide +kernel

theorem context_13_299087_538764 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299087 ⟨538764, by decide⟩ :=
  accepted_of_selected 13 299087 ⟨538764, by decide⟩ ⟨13, 2, 0, 538764, 299087, 613, 16384⟩
    (by decide) selected_cut_20999

theorem unmarked_context_12_74771_538765 : frontier 9 ⟨538765, by decide⟩
    (prefixCache 12 74771) (prefixPartial 12 74771) = false := by
  decide +kernel

theorem node_context_12_74771_538765 : EJMOriginalGlobalDAGData.nodes 9 ⟨538765, by decide⟩ =
    .split (coordinate 12) (![⟨538716, by decide⟩,⟨538738, by decide⟩,⟨538759, by decide⟩,⟨538764, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74771_538765 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74771 ⟨538765, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74771
    ⟨538765, by decide⟩ (by decide) (![⟨538716, by decide⟩,⟨538738, by decide⟩,⟨538759, by decide⟩,⟨538764, by decide⟩]) unmarked_context_12_74771_538765 node_context_12_74771_538765
  intro a
  fin_cases a
  · exact context_13_299084_538716
  · exact context_13_299085_538738
  · exact context_13_299086_538759
  · exact context_13_299087_538764

theorem unmarked_context_11_18692_538766 : frontier 10 ⟨538766, by decide⟩
    (prefixCache 11 18692) (prefixPartial 11 18692) = false := by
  decide +kernel

theorem node_context_11_18692_538766 : EJMOriginalGlobalDAGData.nodes 10 ⟨538766, by decide⟩ =
    .split (coordinate 11) (![⟨435160, by decide⟩,⟨538626, by decide⟩,⟨538691, by decide⟩,⟨538765, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18692_538766 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18692 ⟨538766, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18692
    ⟨538766, by decide⟩ (by decide) (![⟨435160, by decide⟩,⟨538626, by decide⟩,⟨538691, by decide⟩,⟨538765, by decide⟩]) unmarked_context_11_18692_538766 node_context_11_18692_538766
  intro a
  fin_cases a
  · exact context_12_74768_435160
  · exact context_12_74769_538626
  · exact context_12_74770_538691
  · exact context_12_74771_538765

theorem selected_cut_21000 : selected 9 ⟨435160, by decide⟩
    (prefixPartial 12 74772) = some ⟨12, 1, 0, 435160, 74772, 1, 65536⟩ := by
  decide +kernel

theorem context_12_74772_435160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74772 ⟨435160, by decide⟩ :=
  accepted_of_selected 12 74772 ⟨435160, by decide⟩ ⟨12, 1, 0, 435160, 74772, 1, 65536⟩
    (by decide) selected_cut_21000

theorem selected_cut_21001 : selected 9 ⟨449506, by decide⟩
    (prefixPartial 12 74773) = some ⟨12, 1, 0, 449506, 74773, 1, 65536⟩ := by
  decide +kernel

theorem context_12_74773_449506 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74773 ⟨449506, by decide⟩ :=
  accepted_of_selected 12 74773 ⟨449506, by decide⟩ ⟨12, 1, 0, 449506, 74773, 1, 65536⟩
    (by decide) selected_cut_21001

theorem selected_cut_21002 : selected 8 ⟨538809, by decide⟩
    (prefixPartial 13 299096) = some ⟨13, 2, 0, 538809, 299096, 2061, 16384⟩ := by
  decide +kernel

theorem context_13_299096_538809 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299096 ⟨538809, by decide⟩ :=
  accepted_of_selected 13 299096 ⟨538809, by decide⟩ ⟨13, 2, 0, 538809, 299096, 2061, 16384⟩
    (by decide) selected_cut_21002

theorem selected_cut_21003 : selected 8 ⟨538848, by decide⟩
    (prefixPartial 13 299097) = some ⟨13, 2, 0, 538848, 299097, 2629, 16384⟩ := by
  decide +kernel

theorem context_13_299097_538848 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299097 ⟨538848, by decide⟩ :=
  accepted_of_selected 13 299097 ⟨538848, by decide⟩ ⟨13, 2, 0, 538848, 299097, 2629, 16384⟩
    (by decide) selected_cut_21003

theorem selected_cut_21004 : selected 8 ⟨538876, by decide⟩
    (prefixPartial 13 299098) = some ⟨13, 2, 0, 538876, 299098, 1937, 16384⟩ := by
  decide +kernel

theorem context_13_299098_538876 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299098 ⟨538876, by decide⟩ :=
  accepted_of_selected 13 299098 ⟨538876, by decide⟩ ⟨13, 2, 0, 538876, 299098, 1937, 16384⟩
    (by decide) selected_cut_21004

theorem selected_cut_21005 : selected 8 ⟨538890, by decide⟩
    (prefixPartial 13 299099) = some ⟨13, 2, 0, 538890, 299099, 1069, 16384⟩ := by
  decide +kernel

theorem context_13_299099_538890 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299099 ⟨538890, by decide⟩ :=
  accepted_of_selected 13 299099 ⟨538890, by decide⟩ ⟨13, 2, 0, 538890, 299099, 1069, 16384⟩
    (by decide) selected_cut_21005

theorem unmarked_context_12_74774_538891 : frontier 9 ⟨538891, by decide⟩
    (prefixCache 12 74774) (prefixPartial 12 74774) = false := by
  decide +kernel

theorem node_context_12_74774_538891 : EJMOriginalGlobalDAGData.nodes 9 ⟨538891, by decide⟩ =
    .split (coordinate 12) (![⟨538809, by decide⟩,⟨538848, by decide⟩,⟨538876, by decide⟩,⟨538890, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74774_538891 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74774 ⟨538891, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74774
    ⟨538891, by decide⟩ (by decide) (![⟨538809, by decide⟩,⟨538848, by decide⟩,⟨538876, by decide⟩,⟨538890, by decide⟩]) unmarked_context_12_74774_538891 node_context_12_74774_538891
  intro a
  fin_cases a
  · exact context_13_299096_538809
  · exact context_13_299097_538848
  · exact context_13_299098_538876
  · exact context_13_299099_538890

theorem selected_cut_21006 : selected 8 ⟨538935, by decide⟩
    (prefixPartial 13 299100) = some ⟨13, 2, 0, 538935, 299100, 2153, 16384⟩ := by
  decide +kernel

theorem context_13_299100_538935 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299100 ⟨538935, by decide⟩ :=
  accepted_of_selected 13 299100 ⟨538935, by decide⟩ ⟨13, 2, 0, 538935, 299100, 2153, 16384⟩
    (by decide) selected_cut_21006

theorem selected_cut_21007 : selected 8 ⟨538987, by decide⟩
    (prefixPartial 13 299101) = some ⟨13, 2, 0, 538987, 299101, 2965, 16384⟩ := by
  decide +kernel

theorem context_13_299101_538987 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299101 ⟨538987, by decide⟩ :=
  accepted_of_selected 13 299101 ⟨538987, by decide⟩ ⟨13, 2, 0, 538987, 299101, 2965, 16384⟩
    (by decide) selected_cut_21007

theorem selected_cut_21008 : selected 8 ⟨539032, by decide⟩
    (prefixPartial 13 299102) = some ⟨13, 2, 0, 539032, 299102, 2457, 16384⟩ := by
  decide +kernel

theorem context_13_299102_539032 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299102 ⟨539032, by decide⟩ :=
  accepted_of_selected 13 299102 ⟨539032, by decide⟩ ⟨13, 2, 0, 539032, 299102, 2457, 16384⟩
    (by decide) selected_cut_21008

theorem selected_cut_21009 : selected 8 ⟨539044, by decide⟩
    (prefixPartial 13 299103) = some ⟨13, 2, 0, 539044, 299103, 993, 16384⟩ := by
  decide +kernel

theorem context_13_299103_539044 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299103 ⟨539044, by decide⟩ :=
  accepted_of_selected 13 299103 ⟨539044, by decide⟩ ⟨13, 2, 0, 539044, 299103, 993, 16384⟩
    (by decide) selected_cut_21009

theorem unmarked_context_12_74775_539045 : frontier 9 ⟨539045, by decide⟩
    (prefixCache 12 74775) (prefixPartial 12 74775) = false := by
  decide +kernel

theorem node_context_12_74775_539045 : EJMOriginalGlobalDAGData.nodes 9 ⟨539045, by decide⟩ =
    .split (coordinate 12) (![⟨538935, by decide⟩,⟨538987, by decide⟩,⟨539032, by decide⟩,⟨539044, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74775_539045 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74775 ⟨539045, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74775
    ⟨539045, by decide⟩ (by decide) (![⟨538935, by decide⟩,⟨538987, by decide⟩,⟨539032, by decide⟩,⟨539044, by decide⟩]) unmarked_context_12_74775_539045 node_context_12_74775_539045
  intro a
  fin_cases a
  · exact context_13_299100_538935
  · exact context_13_299101_538987
  · exact context_13_299102_539032
  · exact context_13_299103_539044

theorem unmarked_context_11_18693_539046 : frontier 10 ⟨539046, by decide⟩
    (prefixCache 11 18693) (prefixPartial 11 18693) = false := by
  decide +kernel

theorem node_context_11_18693_539046 : EJMOriginalGlobalDAGData.nodes 10 ⟨539046, by decide⟩ =
    .split (coordinate 11) (![⟨435160, by decide⟩,⟨449506, by decide⟩,⟨538891, by decide⟩,⟨539045, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18693_539046 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18693 ⟨539046, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18693
    ⟨539046, by decide⟩ (by decide) (![⟨435160, by decide⟩,⟨449506, by decide⟩,⟨538891, by decide⟩,⟨539045, by decide⟩]) unmarked_context_11_18693_539046 node_context_11_18693_539046
  intro a
  fin_cases a
  · exact context_12_74772_435160
  · exact context_12_74773_449506
  · exact context_12_74774_538891
  · exact context_12_74775_539045

theorem selected_cut_21010 : selected 9 ⟨449505, by decide⟩
    (prefixPartial 12 74776) = some ⟨12, 1, 0, 449505, 74776, 1, 65536⟩ := by
  decide +kernel

theorem context_12_74776_449505 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74776 ⟨449505, by decide⟩ :=
  accepted_of_selected 12 74776 ⟨449505, by decide⟩ ⟨12, 1, 0, 449505, 74776, 1, 65536⟩
    (by decide) selected_cut_21010

theorem selected_cut_21011 : selected 8 ⟨539075, by decide⟩
    (prefixPartial 13 299108) = some ⟨13, 2, 0, 539075, 299108, 1269, 16384⟩ := by
  decide +kernel

theorem context_13_299108_539075 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299108 ⟨539075, by decide⟩ :=
  accepted_of_selected 13 299108 ⟨539075, by decide⟩ ⟨13, 2, 0, 539075, 299108, 1269, 16384⟩
    (by decide) selected_cut_21011

theorem selected_cut_21012 : selected 8 ⟨539098, by decide⟩
    (prefixPartial 13 299109) = some ⟨13, 2, 0, 539098, 299109, 1961, 16384⟩ := by
  decide +kernel

theorem context_13_299109_539098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299109 ⟨539098, by decide⟩ :=
  accepted_of_selected 13 299109 ⟨539098, by decide⟩ ⟨13, 2, 0, 539098, 299109, 1961, 16384⟩
    (by decide) selected_cut_21012

theorem selected_cut_21013 : selected 8 ⟨539122, by decide⟩
    (prefixPartial 13 299110) = some ⟨13, 2, 0, 539122, 299110, 1613, 16384⟩ := by
  decide +kernel

theorem context_13_299110_539122 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299110 ⟨539122, by decide⟩ :=
  accepted_of_selected 13 299110 ⟨539122, by decide⟩ ⟨13, 2, 0, 539122, 299110, 1613, 16384⟩
    (by decide) selected_cut_21013

theorem selected_cut_21014 : selected 8 ⟨539128, by decide⟩
    (prefixPartial 13 299111) = some ⟨13, 2, 0, 539128, 299111, 801, 16384⟩ := by
  decide +kernel

theorem context_13_299111_539128 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299111 ⟨539128, by decide⟩ :=
  accepted_of_selected 13 299111 ⟨539128, by decide⟩ ⟨13, 2, 0, 539128, 299111, 801, 16384⟩
    (by decide) selected_cut_21014

theorem unmarked_context_12_74777_539129 : frontier 9 ⟨539129, by decide⟩
    (prefixCache 12 74777) (prefixPartial 12 74777) = false := by
  decide +kernel

theorem node_context_12_74777_539129 : EJMOriginalGlobalDAGData.nodes 9 ⟨539129, by decide⟩ =
    .split (coordinate 12) (![⟨539075, by decide⟩,⟨539098, by decide⟩,⟨539122, by decide⟩,⟨539128, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74777_539129 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74777 ⟨539129, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74777
    ⟨539129, by decide⟩ (by decide) (![⟨539075, by decide⟩,⟨539098, by decide⟩,⟨539122, by decide⟩,⟨539128, by decide⟩]) unmarked_context_12_74777_539129 node_context_12_74777_539129
  intro a
  fin_cases a
  · exact context_13_299108_539075
  · exact context_13_299109_539098
  · exact context_13_299110_539122
  · exact context_13_299111_539128

theorem selected_cut_21015 : selected 8 ⟨539153, by decide⟩
    (prefixPartial 13 299112) = some ⟨13, 2, 0, 539153, 299112, 1053, 16384⟩ := by
  decide +kernel

theorem context_13_299112_539153 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299112 ⟨539153, by decide⟩ :=
  accepted_of_selected 13 299112 ⟨539153, by decide⟩ ⟨13, 2, 0, 539153, 299112, 1053, 16384⟩
    (by decide) selected_cut_21015

theorem selected_cut_21016 : selected 8 ⟨539176, by decide⟩
    (prefixPartial 13 299113) = some ⟨13, 2, 0, 539176, 299113, 1957, 16384⟩ := by
  decide +kernel

theorem context_13_299113_539176 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299113 ⟨539176, by decide⟩ :=
  accepted_of_selected 13 299113 ⟨539176, by decide⟩ ⟨13, 2, 0, 539176, 299113, 1957, 16384⟩
    (by decide) selected_cut_21016

theorem selected_cut_21017 : selected 8 ⟨539194, by decide⟩
    (prefixPartial 13 299114) = some ⟨13, 2, 0, 539194, 299114, 1441, 16384⟩ := by
  decide +kernel

theorem context_13_299114_539194 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299114 ⟨539194, by decide⟩ :=
  accepted_of_selected 13 299114 ⟨539194, by decide⟩ ⟨13, 2, 0, 539194, 299114, 1441, 16384⟩
    (by decide) selected_cut_21017

theorem selected_cut_21018 : selected 8 ⟨539201, by decide⟩
    (prefixPartial 13 299115) = some ⟨13, 2, 0, 539201, 299115, 857, 16384⟩ := by
  decide +kernel

theorem context_13_299115_539201 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299115 ⟨539201, by decide⟩ :=
  accepted_of_selected 13 299115 ⟨539201, by decide⟩ ⟨13, 2, 0, 539201, 299115, 857, 16384⟩
    (by decide) selected_cut_21018

theorem unmarked_context_12_74778_539202 : frontier 9 ⟨539202, by decide⟩
    (prefixCache 12 74778) (prefixPartial 12 74778) = false := by
  decide +kernel

theorem node_context_12_74778_539202 : EJMOriginalGlobalDAGData.nodes 9 ⟨539202, by decide⟩ =
    .split (coordinate 12) (![⟨539153, by decide⟩,⟨539176, by decide⟩,⟨539194, by decide⟩,⟨539201, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74778_539202 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74778 ⟨539202, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74778
    ⟨539202, by decide⟩ (by decide) (![⟨539153, by decide⟩,⟨539176, by decide⟩,⟨539194, by decide⟩,⟨539201, by decide⟩]) unmarked_context_12_74778_539202 node_context_12_74778_539202
  intro a
  fin_cases a
  · exact context_13_299112_539153
  · exact context_13_299113_539176
  · exact context_13_299114_539194
  · exact context_13_299115_539201

theorem selected_cut_21019 : selected 8 ⟨539236, by decide⟩
    (prefixPartial 13 299116) = some ⟨13, 2, 0, 539236, 299116, 1385, 16384⟩ := by
  decide +kernel

theorem context_13_299116_539236 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299116 ⟨539236, by decide⟩ :=
  accepted_of_selected 13 299116 ⟨539236, by decide⟩ ⟨13, 2, 0, 539236, 299116, 1385, 16384⟩
    (by decide) selected_cut_21019

theorem selected_cut_21020 : selected 8 ⟨539263, by decide⟩
    (prefixPartial 13 299117) = some ⟨13, 2, 0, 539263, 299117, 2433, 16384⟩ := by
  decide +kernel

theorem context_13_299117_539263 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299117 ⟨539263, by decide⟩ :=
  accepted_of_selected 13 299117 ⟨539263, by decide⟩ ⟨13, 2, 0, 539263, 299117, 2433, 16384⟩
    (by decide) selected_cut_21020

theorem selected_cut_21021 : selected 8 ⟨539284, by decide⟩
    (prefixPartial 13 299118) = some ⟨13, 2, 0, 539284, 299118, 1861, 16384⟩ := by
  decide +kernel

theorem context_13_299118_539284 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299118 ⟨539284, by decide⟩ :=
  accepted_of_selected 13 299118 ⟨539284, by decide⟩ ⟨13, 2, 0, 539284, 299118, 1861, 16384⟩
    (by decide) selected_cut_21021

theorem selected_cut_21022 : selected 8 ⟨539293, by decide⟩
    (prefixPartial 13 299119) = some ⟨13, 2, 0, 539293, 299119, 809, 16384⟩ := by
  decide +kernel

theorem context_13_299119_539293 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299119 ⟨539293, by decide⟩ :=
  accepted_of_selected 13 299119 ⟨539293, by decide⟩ ⟨13, 2, 0, 539293, 299119, 809, 16384⟩
    (by decide) selected_cut_21022

theorem unmarked_context_12_74779_539294 : frontier 9 ⟨539294, by decide⟩
    (prefixCache 12 74779) (prefixPartial 12 74779) = false := by
  decide +kernel

theorem node_context_12_74779_539294 : EJMOriginalGlobalDAGData.nodes 9 ⟨539294, by decide⟩ =
    .split (coordinate 12) (![⟨539236, by decide⟩,⟨539263, by decide⟩,⟨539284, by decide⟩,⟨539293, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74779_539294 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74779 ⟨539294, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74779
    ⟨539294, by decide⟩ (by decide) (![⟨539236, by decide⟩,⟨539263, by decide⟩,⟨539284, by decide⟩,⟨539293, by decide⟩]) unmarked_context_12_74779_539294 node_context_12_74779_539294
  intro a
  fin_cases a
  · exact context_13_299116_539236
  · exact context_13_299117_539263
  · exact context_13_299118_539284
  · exact context_13_299119_539293

theorem unmarked_context_11_18694_539295 : frontier 10 ⟨539295, by decide⟩
    (prefixCache 11 18694) (prefixPartial 11 18694) = false := by
  decide +kernel

theorem node_context_11_18694_539295 : EJMOriginalGlobalDAGData.nodes 10 ⟨539295, by decide⟩ =
    .split (coordinate 11) (![⟨449505, by decide⟩,⟨539129, by decide⟩,⟨539202, by decide⟩,⟨539294, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18694_539295 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18694 ⟨539295, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18694
    ⟨539295, by decide⟩ (by decide) (![⟨449505, by decide⟩,⟨539129, by decide⟩,⟨539202, by decide⟩,⟨539294, by decide⟩]) unmarked_context_11_18694_539295 node_context_11_18694_539295
  intro a
  fin_cases a
  · exact context_12_74776_449505
  · exact context_12_74777_539129
  · exact context_12_74778_539202
  · exact context_12_74779_539294

theorem selected_cut_21023 : selected 9 ⟨539296, by decide⟩
    (prefixPartial 12 74780) = some ⟨12, 1, 0, 539296, 74780, 1, 65536⟩ := by
  decide +kernel

theorem context_12_74780_539296 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74780 ⟨539296, by decide⟩ :=
  accepted_of_selected 12 74780 ⟨539296, by decide⟩ ⟨12, 1, 0, 539296, 74780, 1, 65536⟩
    (by decide) selected_cut_21023

theorem selected_cut_21024 : selected 8 ⟨539322, by decide⟩
    (prefixPartial 13 299124) = some ⟨13, 2, 0, 539322, 299124, 1025, 16384⟩ := by
  decide +kernel

theorem context_13_299124_539322 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299124 ⟨539322, by decide⟩ :=
  accepted_of_selected 13 299124 ⟨539322, by decide⟩ ⟨13, 2, 0, 539322, 299124, 1025, 16384⟩
    (by decide) selected_cut_21024

theorem selected_cut_21025 : selected 8 ⟨539353, by decide⟩
    (prefixPartial 13 299125) = some ⟨13, 2, 0, 539353, 299125, 2361, 16384⟩ := by
  decide +kernel

theorem context_13_299125_539353 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299125 ⟨539353, by decide⟩ :=
  accepted_of_selected 13 299125 ⟨539353, by decide⟩ ⟨13, 2, 0, 539353, 299125, 2361, 16384⟩
    (by decide) selected_cut_21025

theorem selected_cut_21026 : selected 8 ⟨539375, by decide⟩
    (prefixPartial 13 299126) = some ⟨13, 2, 0, 539375, 299126, 1485, 16384⟩ := by
  decide +kernel

theorem context_13_299126_539375 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299126 ⟨539375, by decide⟩ :=
  accepted_of_selected 13 299126 ⟨539375, by decide⟩ ⟨13, 2, 0, 539375, 299126, 1485, 16384⟩
    (by decide) selected_cut_21026

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
