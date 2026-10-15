/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover126
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_12195 : selected 9 ⟨323628, by decide⟩
    (prefixPartial 12 26028) = some ⟨12, 2, 0, 323628, 26028, 1617, 65536⟩ := by
  decide +kernel

theorem context_12_26028_323628 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26028 ⟨323628, by decide⟩ :=
  accepted_of_selected 12 26028 ⟨323628, by decide⟩ ⟨12, 2, 0, 323628, 26028, 1617, 65536⟩
    (by decide) selected_cut_12195

theorem selected_cut_12196 : selected 9 ⟨323646, by decide⟩
    (prefixPartial 12 26029) = some ⟨12, 2, 0, 323646, 26029, 1485, 65536⟩ := by
  decide +kernel

theorem context_12_26029_323646 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26029 ⟨323646, by decide⟩ :=
  accepted_of_selected 12 26029 ⟨323646, by decide⟩ ⟨12, 2, 0, 323646, 26029, 1485, 65536⟩
    (by decide) selected_cut_12196

theorem selected_cut_12197 : selected 9 ⟨323665, by decide⟩
    (prefixPartial 12 26030) = some ⟨12, 2, 0, 323665, 26030, 1409, 65536⟩ := by
  decide +kernel

theorem context_12_26030_323665 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26030 ⟨323665, by decide⟩ :=
  accepted_of_selected 12 26030 ⟨323665, by decide⟩ ⟨12, 2, 0, 323665, 26030, 1409, 65536⟩
    (by decide) selected_cut_12197

theorem selected_cut_12198 : selected 9 ⟨323681, by decide⟩
    (prefixPartial 12 26031) = some ⟨12, 2, 0, 323681, 26031, 1525, 65536⟩ := by
  decide +kernel

theorem context_12_26031_323681 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26031 ⟨323681, by decide⟩ :=
  accepted_of_selected 12 26031 ⟨323681, by decide⟩ ⟨12, 2, 0, 323681, 26031, 1525, 65536⟩
    (by decide) selected_cut_12198

theorem unmarked_context_11_6507_323682 : frontier 10 ⟨323682, by decide⟩
    (prefixCache 11 6507) (prefixPartial 11 6507) = false := by
  decide +kernel

theorem node_context_11_6507_323682 : EJMOriginalGlobalDAGData.nodes 10 ⟨323682, by decide⟩ =
    .split (coordinate 11) (![⟨323628, by decide⟩,⟨323646, by decide⟩,⟨323665, by decide⟩,⟨323681, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6507_323682 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6507 ⟨323682, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6507
    ⟨323682, by decide⟩ (by decide) (![⟨323628, by decide⟩,⟨323646, by decide⟩,⟨323665, by decide⟩,⟨323681, by decide⟩]) unmarked_context_11_6507_323682 node_context_11_6507_323682
  intro a
  fin_cases a
  · exact context_12_26028_323628
  · exact context_12_26029_323646
  · exact context_12_26030_323665
  · exact context_12_26031_323681

theorem unmarked_context_10_1626_323683 : frontier 11 ⟨323683, by decide⟩
    (prefixCache 10 1626) (prefixPartial 10 1626) = false := by
  decide +kernel

theorem node_context_10_1626_323683 : EJMOriginalGlobalDAGData.nodes 11 ⟨323683, by decide⟩ =
    .split (coordinate 10) (![⟨323470, by decide⟩,⟨323540, by decide⟩,⟨323611, by decide⟩,⟨323682, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1626_323683 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1626 ⟨323683, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1626
    ⟨323683, by decide⟩ (by decide) (![⟨323470, by decide⟩,⟨323540, by decide⟩,⟨323611, by decide⟩,⟨323682, by decide⟩]) unmarked_context_10_1626_323683 node_context_10_1626_323683
  intro a
  fin_cases a
  · exact context_11_6504_323470
  · exact context_11_6505_323540
  · exact context_11_6506_323611
  · exact context_11_6507_323682

theorem selected_cut_12199 : selected 9 ⟨323697, by decide⟩
    (prefixPartial 12 26032) = some ⟨12, 2, 0, 323697, 26032, 1461, 65536⟩ := by
  decide +kernel

theorem context_12_26032_323697 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26032 ⟨323697, by decide⟩ :=
  accepted_of_selected 12 26032 ⟨323697, by decide⟩ ⟨12, 2, 0, 323697, 26032, 1461, 65536⟩
    (by decide) selected_cut_12199

theorem selected_cut_12200 : selected 9 ⟨323714, by decide⟩
    (prefixPartial 12 26033) = some ⟨12, 2, 0, 323714, 26033, 1485, 65536⟩ := by
  decide +kernel

theorem context_12_26033_323714 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26033 ⟨323714, by decide⟩ :=
  accepted_of_selected 12 26033 ⟨323714, by decide⟩ ⟨12, 2, 0, 323714, 26033, 1485, 65536⟩
    (by decide) selected_cut_12200

theorem selected_cut_12201 : selected 9 ⟨323742, by decide⟩
    (prefixPartial 12 26034) = some ⟨12, 2, 0, 323742, 26034, 1637, 65536⟩ := by
  decide +kernel

theorem context_12_26034_323742 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26034 ⟨323742, by decide⟩ :=
  accepted_of_selected 12 26034 ⟨323742, by decide⟩ ⟨12, 2, 0, 323742, 26034, 1637, 65536⟩
    (by decide) selected_cut_12201

theorem selected_cut_12202 : selected 9 ⟨323763, by decide⟩
    (prefixPartial 12 26035) = some ⟨12, 2, 0, 323763, 26035, 1589, 65536⟩ := by
  decide +kernel

theorem context_12_26035_323763 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26035 ⟨323763, by decide⟩ :=
  accepted_of_selected 12 26035 ⟨323763, by decide⟩ ⟨12, 2, 0, 323763, 26035, 1589, 65536⟩
    (by decide) selected_cut_12202

theorem unmarked_context_11_6508_323764 : frontier 10 ⟨323764, by decide⟩
    (prefixCache 11 6508) (prefixPartial 11 6508) = false := by
  decide +kernel

theorem node_context_11_6508_323764 : EJMOriginalGlobalDAGData.nodes 10 ⟨323764, by decide⟩ =
    .split (coordinate 11) (![⟨323697, by decide⟩,⟨323714, by decide⟩,⟨323742, by decide⟩,⟨323763, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6508_323764 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6508 ⟨323764, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6508
    ⟨323764, by decide⟩ (by decide) (![⟨323697, by decide⟩,⟨323714, by decide⟩,⟨323742, by decide⟩,⟨323763, by decide⟩]) unmarked_context_11_6508_323764 node_context_11_6508_323764
  intro a
  fin_cases a
  · exact context_12_26032_323697
  · exact context_12_26033_323714
  · exact context_12_26034_323742
  · exact context_12_26035_323763

theorem selected_cut_12203 : selected 9 ⟨323775, by decide⟩
    (prefixPartial 12 26036) = some ⟨12, 2, 0, 323775, 26036, 1229, 65536⟩ := by
  decide +kernel

theorem context_12_26036_323775 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26036 ⟨323775, by decide⟩ :=
  accepted_of_selected 12 26036 ⟨323775, by decide⟩ ⟨12, 2, 0, 323775, 26036, 1229, 65536⟩
    (by decide) selected_cut_12203

theorem selected_cut_12204 : selected 9 ⟨323797, by decide⟩
    (prefixPartial 12 26037) = some ⟨12, 2, 0, 323797, 26037, 1721, 65536⟩ := by
  decide +kernel

theorem context_12_26037_323797 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26037 ⟨323797, by decide⟩ :=
  accepted_of_selected 12 26037 ⟨323797, by decide⟩ ⟨12, 2, 0, 323797, 26037, 1721, 65536⟩
    (by decide) selected_cut_12204

theorem selected_cut_12205 : selected 9 ⟨323810, by decide⟩
    (prefixPartial 12 26038) = some ⟨12, 2, 0, 323810, 26038, 1233, 65536⟩ := by
  decide +kernel

theorem context_12_26038_323810 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26038 ⟨323810, by decide⟩ :=
  accepted_of_selected 12 26038 ⟨323810, by decide⟩ ⟨12, 2, 0, 323810, 26038, 1233, 65536⟩
    (by decide) selected_cut_12205

theorem selected_cut_12206 : selected 9 ⟨323825, by decide⟩
    (prefixPartial 12 26039) = some ⟨12, 2, 0, 323825, 26039, 1321, 65536⟩ := by
  decide +kernel

theorem context_12_26039_323825 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26039 ⟨323825, by decide⟩ :=
  accepted_of_selected 12 26039 ⟨323825, by decide⟩ ⟨12, 2, 0, 323825, 26039, 1321, 65536⟩
    (by decide) selected_cut_12206

theorem unmarked_context_11_6509_323826 : frontier 10 ⟨323826, by decide⟩
    (prefixCache 11 6509) (prefixPartial 11 6509) = false := by
  decide +kernel

theorem node_context_11_6509_323826 : EJMOriginalGlobalDAGData.nodes 10 ⟨323826, by decide⟩ =
    .split (coordinate 11) (![⟨323775, by decide⟩,⟨323797, by decide⟩,⟨323810, by decide⟩,⟨323825, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6509_323826 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6509 ⟨323826, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6509
    ⟨323826, by decide⟩ (by decide) (![⟨323775, by decide⟩,⟨323797, by decide⟩,⟨323810, by decide⟩,⟨323825, by decide⟩]) unmarked_context_11_6509_323826 node_context_11_6509_323826
  intro a
  fin_cases a
  · exact context_12_26036_323775
  · exact context_12_26037_323797
  · exact context_12_26038_323810
  · exact context_12_26039_323825

theorem selected_cut_12207 : selected 9 ⟨323842, by decide⟩
    (prefixPartial 12 26040) = some ⟨12, 2, 0, 323842, 26040, 1261, 65536⟩ := by
  decide +kernel

theorem context_12_26040_323842 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26040 ⟨323842, by decide⟩ :=
  accepted_of_selected 12 26040 ⟨323842, by decide⟩ ⟨12, 2, 0, 323842, 26040, 1261, 65536⟩
    (by decide) selected_cut_12207

theorem selected_cut_12208 : selected 9 ⟨323853, by decide⟩
    (prefixPartial 12 26041) = some ⟨12, 2, 0, 323853, 26041, 1229, 65536⟩ := by
  decide +kernel

theorem context_12_26041_323853 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26041 ⟨323853, by decide⟩ :=
  accepted_of_selected 12 26041 ⟨323853, by decide⟩ ⟨12, 2, 0, 323853, 26041, 1229, 65536⟩
    (by decide) selected_cut_12208

theorem selected_cut_12209 : selected 9 ⟨323867, by decide⟩
    (prefixPartial 12 26042) = some ⟨12, 2, 0, 323867, 26042, 1197, 65536⟩ := by
  decide +kernel

theorem context_12_26042_323867 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26042 ⟨323867, by decide⟩ :=
  accepted_of_selected 12 26042 ⟨323867, by decide⟩ ⟨12, 2, 0, 323867, 26042, 1197, 65536⟩
    (by decide) selected_cut_12209

theorem selected_cut_12210 : selected 9 ⟨323884, by decide⟩
    (prefixPartial 12 26043) = some ⟨12, 2, 0, 323884, 26043, 1277, 65536⟩ := by
  decide +kernel

theorem context_12_26043_323884 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26043 ⟨323884, by decide⟩ :=
  accepted_of_selected 12 26043 ⟨323884, by decide⟩ ⟨12, 2, 0, 323884, 26043, 1277, 65536⟩
    (by decide) selected_cut_12210

theorem unmarked_context_11_6510_323885 : frontier 10 ⟨323885, by decide⟩
    (prefixCache 11 6510) (prefixPartial 11 6510) = false := by
  decide +kernel

theorem node_context_11_6510_323885 : EJMOriginalGlobalDAGData.nodes 10 ⟨323885, by decide⟩ =
    .split (coordinate 11) (![⟨323842, by decide⟩,⟨323853, by decide⟩,⟨323867, by decide⟩,⟨323884, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6510_323885 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6510 ⟨323885, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6510
    ⟨323885, by decide⟩ (by decide) (![⟨323842, by decide⟩,⟨323853, by decide⟩,⟨323867, by decide⟩,⟨323884, by decide⟩]) unmarked_context_11_6510_323885 node_context_11_6510_323885
  intro a
  fin_cases a
  · exact context_12_26040_323842
  · exact context_12_26041_323853
  · exact context_12_26042_323867
  · exact context_12_26043_323884

theorem selected_cut_12211 : selected 9 ⟨323895, by decide⟩
    (prefixPartial 12 26044) = some ⟨12, 2, 0, 323895, 26044, 1269, 65536⟩ := by
  decide +kernel

theorem context_12_26044_323895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26044 ⟨323895, by decide⟩ :=
  accepted_of_selected 12 26044 ⟨323895, by decide⟩ ⟨12, 2, 0, 323895, 26044, 1269, 65536⟩
    (by decide) selected_cut_12211

theorem selected_cut_12212 : selected 9 ⟨323907, by decide⟩
    (prefixPartial 12 26045) = some ⟨12, 2, 0, 323907, 26045, 1065, 65536⟩ := by
  decide +kernel

theorem context_12_26045_323907 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26045 ⟨323907, by decide⟩ :=
  accepted_of_selected 12 26045 ⟨323907, by decide⟩ ⟨12, 2, 0, 323907, 26045, 1065, 65536⟩
    (by decide) selected_cut_12212

theorem selected_cut_12213 : selected 9 ⟨323924, by decide⟩
    (prefixPartial 12 26046) = some ⟨12, 2, 0, 323924, 26046, 1117, 65536⟩ := by
  decide +kernel

theorem context_12_26046_323924 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26046 ⟨323924, by decide⟩ :=
  accepted_of_selected 12 26046 ⟨323924, by decide⟩ ⟨12, 2, 0, 323924, 26046, 1117, 65536⟩
    (by decide) selected_cut_12213

theorem selected_cut_12214 : selected 9 ⟨323932, by decide⟩
    (prefixPartial 12 26047) = some ⟨12, 2, 0, 323932, 26047, 1221, 65536⟩ := by
  decide +kernel

theorem context_12_26047_323932 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26047 ⟨323932, by decide⟩ :=
  accepted_of_selected 12 26047 ⟨323932, by decide⟩ ⟨12, 2, 0, 323932, 26047, 1221, 65536⟩
    (by decide) selected_cut_12214

theorem unmarked_context_11_6511_323933 : frontier 10 ⟨323933, by decide⟩
    (prefixCache 11 6511) (prefixPartial 11 6511) = false := by
  decide +kernel

theorem node_context_11_6511_323933 : EJMOriginalGlobalDAGData.nodes 10 ⟨323933, by decide⟩ =
    .split (coordinate 11) (![⟨323895, by decide⟩,⟨323907, by decide⟩,⟨323924, by decide⟩,⟨323932, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6511_323933 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6511 ⟨323933, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6511
    ⟨323933, by decide⟩ (by decide) (![⟨323895, by decide⟩,⟨323907, by decide⟩,⟨323924, by decide⟩,⟨323932, by decide⟩]) unmarked_context_11_6511_323933 node_context_11_6511_323933
  intro a
  fin_cases a
  · exact context_12_26044_323895
  · exact context_12_26045_323907
  · exact context_12_26046_323924
  · exact context_12_26047_323932

theorem unmarked_context_10_1627_323934 : frontier 11 ⟨323934, by decide⟩
    (prefixCache 10 1627) (prefixPartial 10 1627) = false := by
  decide +kernel

theorem node_context_10_1627_323934 : EJMOriginalGlobalDAGData.nodes 11 ⟨323934, by decide⟩ =
    .split (coordinate 10) (![⟨323764, by decide⟩,⟨323826, by decide⟩,⟨323885, by decide⟩,⟨323933, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1627_323934 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1627 ⟨323934, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1627
    ⟨323934, by decide⟩ (by decide) (![⟨323764, by decide⟩,⟨323826, by decide⟩,⟨323885, by decide⟩,⟨323933, by decide⟩]) unmarked_context_10_1627_323934 node_context_10_1627_323934
  intro a
  fin_cases a
  · exact context_11_6508_323764
  · exact context_11_6509_323826
  · exact context_11_6510_323885
  · exact context_11_6511_323933

theorem unmarked_context_9_406_323935 : frontier 12 ⟨323935, by decide⟩
    (prefixCache 9 406) (prefixPartial 9 406) = false := by
  decide +kernel

theorem node_context_9_406_323935 : EJMOriginalGlobalDAGData.nodes 12 ⟨323935, by decide⟩ =
    .split (coordinate 9) (![⟨323027, by decide⟩,⟨323385, by decide⟩,⟨323683, by decide⟩,⟨323934, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_406_323935 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 406 ⟨323935, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 406
    ⟨323935, by decide⟩ (by decide) (![⟨323027, by decide⟩,⟨323385, by decide⟩,⟨323683, by decide⟩,⟨323934, by decide⟩]) unmarked_context_9_406_323935 node_context_9_406_323935
  intro a
  fin_cases a
  · exact context_10_1624_323027
  · exact context_10_1625_323385
  · exact context_10_1626_323683
  · exact context_10_1627_323934

theorem selected_cut_12215 : selected 9 ⟨323947, by decide⟩
    (prefixPartial 12 26048) = some ⟨12, 2, 0, 323947, 26048, 1197, 65536⟩ := by
  decide +kernel

theorem context_12_26048_323947 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26048 ⟨323947, by decide⟩ :=
  accepted_of_selected 12 26048 ⟨323947, by decide⟩ ⟨12, 2, 0, 323947, 26048, 1197, 65536⟩
    (by decide) selected_cut_12215

theorem selected_cut_12216 : selected 9 ⟨323957, by decide⟩
    (prefixPartial 12 26049) = some ⟨12, 2, 0, 323957, 26049, 1157, 65536⟩ := by
  decide +kernel

theorem context_12_26049_323957 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26049 ⟨323957, by decide⟩ :=
  accepted_of_selected 12 26049 ⟨323957, by decide⟩ ⟨12, 2, 0, 323957, 26049, 1157, 65536⟩
    (by decide) selected_cut_12216

theorem selected_cut_12217 : selected 9 ⟨323972, by decide⟩
    (prefixPartial 12 26050) = some ⟨12, 2, 0, 323972, 26050, 1173, 65536⟩ := by
  decide +kernel

theorem context_12_26050_323972 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26050 ⟨323972, by decide⟩ :=
  accepted_of_selected 12 26050 ⟨323972, by decide⟩ ⟨12, 2, 0, 323972, 26050, 1173, 65536⟩
    (by decide) selected_cut_12217

theorem selected_cut_12218 : selected 9 ⟨323981, by decide⟩
    (prefixPartial 12 26051) = some ⟨12, 2, 0, 323981, 26051, 1077, 65536⟩ := by
  decide +kernel

theorem context_12_26051_323981 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26051 ⟨323981, by decide⟩ :=
  accepted_of_selected 12 26051 ⟨323981, by decide⟩ ⟨12, 2, 0, 323981, 26051, 1077, 65536⟩
    (by decide) selected_cut_12218

theorem unmarked_context_11_6512_323982 : frontier 10 ⟨323982, by decide⟩
    (prefixCache 11 6512) (prefixPartial 11 6512) = false := by
  decide +kernel

theorem node_context_11_6512_323982 : EJMOriginalGlobalDAGData.nodes 10 ⟨323982, by decide⟩ =
    .split (coordinate 11) (![⟨323947, by decide⟩,⟨323957, by decide⟩,⟨323972, by decide⟩,⟨323981, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6512_323982 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6512 ⟨323982, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6512
    ⟨323982, by decide⟩ (by decide) (![⟨323947, by decide⟩,⟨323957, by decide⟩,⟨323972, by decide⟩,⟨323981, by decide⟩]) unmarked_context_11_6512_323982 node_context_11_6512_323982
  intro a
  fin_cases a
  · exact context_12_26048_323947
  · exact context_12_26049_323957
  · exact context_12_26050_323972
  · exact context_12_26051_323981

theorem selected_cut_12219 : selected 10 ⟨324021, by decide⟩
    (prefixPartial 11 6513) = some ⟨11, 2, 0, 324021, 6513, 3845, 262144⟩ := by
  decide +kernel

theorem context_11_6513_324021 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6513 ⟨324021, by decide⟩ :=
  accepted_of_selected 11 6513 ⟨324021, by decide⟩ ⟨11, 2, 0, 324021, 6513, 3845, 262144⟩
    (by decide) selected_cut_12219

theorem selected_cut_12220 : selected 10 ⟨324059, by decide⟩
    (prefixPartial 11 6514) = some ⟨11, 2, 0, 324059, 6514, 3545, 262144⟩ := by
  decide +kernel

theorem context_11_6514_324059 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6514 ⟨324059, by decide⟩ :=
  accepted_of_selected 11 6514 ⟨324059, by decide⟩ ⟨11, 2, 0, 324059, 6514, 3545, 262144⟩
    (by decide) selected_cut_12220

theorem selected_cut_12221 : selected 10 ⟨324097, by decide⟩
    (prefixPartial 11 6515) = some ⟨11, 2, 0, 324097, 6515, 3317, 262144⟩ := by
  decide +kernel

theorem context_11_6515_324097 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6515 ⟨324097, by decide⟩ :=
  accepted_of_selected 11 6515 ⟨324097, by decide⟩ ⟨11, 2, 0, 324097, 6515, 3317, 262144⟩
    (by decide) selected_cut_12221

theorem unmarked_context_10_1628_324098 : frontier 11 ⟨324098, by decide⟩
    (prefixCache 10 1628) (prefixPartial 10 1628) = false := by
  decide +kernel

theorem node_context_10_1628_324098 : EJMOriginalGlobalDAGData.nodes 11 ⟨324098, by decide⟩ =
    .split (coordinate 10) (![⟨323982, by decide⟩,⟨324021, by decide⟩,⟨324059, by decide⟩,⟨324097, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1628_324098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1628 ⟨324098, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1628
    ⟨324098, by decide⟩ (by decide) (![⟨323982, by decide⟩,⟨324021, by decide⟩,⟨324059, by decide⟩,⟨324097, by decide⟩]) unmarked_context_10_1628_324098 node_context_10_1628_324098
  intro a
  fin_cases a
  · exact context_11_6512_323982
  · exact context_11_6513_324021
  · exact context_11_6514_324059
  · exact context_11_6515_324097

theorem selected_cut_12222 : selected 10 ⟨324121, by decide⟩
    (prefixPartial 11 6516) = some ⟨11, 2, 0, 324121, 6516, 2589, 262144⟩ := by
  decide +kernel

theorem context_11_6516_324121 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6516 ⟨324121, by decide⟩ :=
  accepted_of_selected 11 6516 ⟨324121, by decide⟩ ⟨11, 2, 0, 324121, 6516, 2589, 262144⟩
    (by decide) selected_cut_12222

theorem selected_cut_12223 : selected 10 ⟨324142, by decide⟩
    (prefixPartial 11 6517) = some ⟨11, 2, 0, 324142, 6517, 1993, 262144⟩ := by
  decide +kernel

theorem context_11_6517_324142 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6517 ⟨324142, by decide⟩ :=
  accepted_of_selected 11 6517 ⟨324142, by decide⟩ ⟨11, 2, 0, 324142, 6517, 1993, 262144⟩
    (by decide) selected_cut_12223

theorem selected_cut_12224 : selected 10 ⟨324159, by decide⟩
    (prefixPartial 11 6518) = some ⟨11, 2, 0, 324159, 6518, 2089, 262144⟩ := by
  decide +kernel

theorem context_11_6518_324159 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6518 ⟨324159, by decide⟩ :=
  accepted_of_selected 11 6518 ⟨324159, by decide⟩ ⟨11, 2, 0, 324159, 6518, 2089, 262144⟩
    (by decide) selected_cut_12224

theorem selected_cut_12225 : selected 10 ⟨324178, by decide⟩
    (prefixPartial 11 6519) = some ⟨11, 2, 0, 324178, 6519, 1929, 262144⟩ := by
  decide +kernel

theorem context_11_6519_324178 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6519 ⟨324178, by decide⟩ :=
  accepted_of_selected 11 6519 ⟨324178, by decide⟩ ⟨11, 2, 0, 324178, 6519, 1929, 262144⟩
    (by decide) selected_cut_12225

theorem unmarked_context_10_1629_324179 : frontier 11 ⟨324179, by decide⟩
    (prefixCache 10 1629) (prefixPartial 10 1629) = false := by
  decide +kernel

theorem node_context_10_1629_324179 : EJMOriginalGlobalDAGData.nodes 11 ⟨324179, by decide⟩ =
    .split (coordinate 10) (![⟨324121, by decide⟩,⟨324142, by decide⟩,⟨324159, by decide⟩,⟨324178, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1629_324179 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1629 ⟨324179, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1629
    ⟨324179, by decide⟩ (by decide) (![⟨324121, by decide⟩,⟨324142, by decide⟩,⟨324159, by decide⟩,⟨324178, by decide⟩]) unmarked_context_10_1629_324179 node_context_10_1629_324179
  intro a
  fin_cases a
  · exact context_11_6516_324121
  · exact context_11_6517_324142
  · exact context_11_6518_324159
  · exact context_11_6519_324178

theorem selected_cut_12226 : selected 10 ⟨324194, by decide⟩
    (prefixPartial 11 6520) = some ⟨11, 2, 0, 324194, 6520, 1845, 262144⟩ := by
  decide +kernel

theorem context_11_6520_324194 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6520 ⟨324194, by decide⟩ :=
  accepted_of_selected 11 6520 ⟨324194, by decide⟩ ⟨11, 2, 0, 324194, 6520, 1845, 262144⟩
    (by decide) selected_cut_12226

theorem selected_cut_12227 : selected 10 ⟨324209, by decide⟩
    (prefixPartial 11 6521) = some ⟨11, 2, 0, 324209, 6521, 1397, 262144⟩ := by
  decide +kernel

theorem context_11_6521_324209 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6521 ⟨324209, by decide⟩ :=
  accepted_of_selected 11 6521 ⟨324209, by decide⟩ ⟨11, 2, 0, 324209, 6521, 1397, 262144⟩
    (by decide) selected_cut_12227

theorem selected_cut_12228 : selected 10 ⟨324226, by decide⟩
    (prefixPartial 11 6522) = some ⟨11, 2, 0, 324226, 6522, 1197, 262144⟩ := by
  decide +kernel

theorem context_11_6522_324226 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6522 ⟨324226, by decide⟩ :=
  accepted_of_selected 11 6522 ⟨324226, by decide⟩ ⟨11, 2, 0, 324226, 6522, 1197, 262144⟩
    (by decide) selected_cut_12228

theorem selected_cut_12229 : selected 10 ⟨324242, by decide⟩
    (prefixPartial 11 6523) = some ⟨11, 2, 0, 324242, 6523, 945, 262144⟩ := by
  decide +kernel

theorem context_11_6523_324242 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6523 ⟨324242, by decide⟩ :=
  accepted_of_selected 11 6523 ⟨324242, by decide⟩ ⟨11, 2, 0, 324242, 6523, 945, 262144⟩
    (by decide) selected_cut_12229

theorem unmarked_context_10_1630_324243 : frontier 11 ⟨324243, by decide⟩
    (prefixCache 10 1630) (prefixPartial 10 1630) = false := by
  decide +kernel

theorem node_context_10_1630_324243 : EJMOriginalGlobalDAGData.nodes 11 ⟨324243, by decide⟩ =
    .split (coordinate 10) (![⟨324194, by decide⟩,⟨324209, by decide⟩,⟨324226, by decide⟩,⟨324242, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1630_324243 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1630 ⟨324243, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1630
    ⟨324243, by decide⟩ (by decide) (![⟨324194, by decide⟩,⟨324209, by decide⟩,⟨324226, by decide⟩,⟨324242, by decide⟩]) unmarked_context_10_1630_324243 node_context_10_1630_324243
  intro a
  fin_cases a
  · exact context_11_6520_324194
  · exact context_11_6521_324209
  · exact context_11_6522_324226
  · exact context_11_6523_324242

theorem selected_cut_12230 : selected 11 ⟨324277, by decide⟩
    (prefixPartial 10 1631) = some ⟨10, 2, 0, 324277, 1631, 1961, 1048576⟩ := by
  decide +kernel

theorem context_10_1631_324277 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1631 ⟨324277, by decide⟩ :=
  accepted_of_selected 10 1631 ⟨324277, by decide⟩ ⟨10, 2, 0, 324277, 1631, 1961, 1048576⟩
    (by decide) selected_cut_12230

theorem unmarked_context_9_407_324278 : frontier 12 ⟨324278, by decide⟩
    (prefixCache 9 407) (prefixPartial 9 407) = false := by
  decide +kernel

theorem node_context_9_407_324278 : EJMOriginalGlobalDAGData.nodes 12 ⟨324278, by decide⟩ =
    .split (coordinate 9) (![⟨324098, by decide⟩,⟨324179, by decide⟩,⟨324243, by decide⟩,⟨324277, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_407_324278 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 407 ⟨324278, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 407
    ⟨324278, by decide⟩ (by decide) (![⟨324098, by decide⟩,⟨324179, by decide⟩,⟨324243, by decide⟩,⟨324277, by decide⟩]) unmarked_context_9_407_324278 node_context_9_407_324278
  intro a
  fin_cases a
  · exact context_10_1628_324098
  · exact context_10_1629_324179
  · exact context_10_1630_324243
  · exact context_10_1631_324277

theorem unmarked_context_8_101_324279 : frontier 13 ⟨324279, by decide⟩
    (prefixCache 8 101) (prefixPartial 8 101) = false := by
  decide +kernel

theorem node_context_8_101_324279 : EJMOriginalGlobalDAGData.nodes 13 ⟨324279, by decide⟩ =
    .split (coordinate 8) (![⟨319535, by decide⟩,⟨322476, by decide⟩,⟨323935, by decide⟩,⟨324278, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_101_324279 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 101 ⟨324279, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 101
    ⟨324279, by decide⟩ (by decide) (![⟨319535, by decide⟩,⟨322476, by decide⟩,⟨323935, by decide⟩,⟨324278, by decide⟩]) unmarked_context_8_101_324279 node_context_8_101_324279
  intro a
  fin_cases a
  · exact context_9_404_319535
  · exact context_9_405_322476
  · exact context_9_406_323935
  · exact context_9_407_324278

theorem selected_cut_12231 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 26112) = some ⟨12, 1, 0, 34034, 26112, 1, 65536⟩ := by
  decide +kernel

theorem context_12_26112_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26112 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 26112 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 26112, 1, 65536⟩
    (by decide) selected_cut_12231

theorem selected_cut_12232 : selected 9 ⟨301653, by decide⟩
    (prefixPartial 12 26113) = some ⟨12, 1, 0, 301653, 26113, 1, 65536⟩ := by
  decide +kernel

theorem context_12_26113_301653 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26113 ⟨301653, by decide⟩ :=
  accepted_of_selected 12 26113 ⟨301653, by decide⟩ ⟨12, 1, 0, 301653, 26113, 1, 65536⟩
    (by decide) selected_cut_12232

theorem selected_cut_12233 : selected 8 ⟨324340, by decide⟩
    (prefixPartial 13 104456) = some ⟨13, 2, 0, 324340, 104456, 2893, 16384⟩ := by
  decide +kernel

theorem context_13_104456_324340 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104456 ⟨324340, by decide⟩ :=
  accepted_of_selected 13 104456 ⟨324340, by decide⟩ ⟨13, 2, 0, 324340, 104456, 2893, 16384⟩
    (by decide) selected_cut_12233

theorem selected_cut_12234 : selected 8 ⟨324377, by decide⟩
    (prefixPartial 13 104457) = some ⟨13, 2, 0, 324377, 104457, 1613, 16384⟩ := by
  decide +kernel

theorem context_13_104457_324377 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104457 ⟨324377, by decide⟩ :=
  accepted_of_selected 13 104457 ⟨324377, by decide⟩ ⟨13, 2, 0, 324377, 104457, 1613, 16384⟩
    (by decide) selected_cut_12234

theorem selected_cut_12235 : selected 8 ⟨324390, by decide⟩
    (prefixPartial 13 104458) = some ⟨13, 2, 0, 324390, 104458, 533, 16384⟩ := by
  decide +kernel

theorem context_13_104458_324390 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104458 ⟨324390, by decide⟩ :=
  accepted_of_selected 13 104458 ⟨324390, by decide⟩ ⟨13, 2, 0, 324390, 104458, 533, 16384⟩
    (by decide) selected_cut_12235

theorem selected_cut_12236 : selected 8 ⟨324393, by decide⟩
    (prefixPartial 13 104459) = some ⟨13, 2, 0, 324393, 104459, 137, 16384⟩ := by
  decide +kernel

theorem context_13_104459_324393 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104459 ⟨324393, by decide⟩ :=
  accepted_of_selected 13 104459 ⟨324393, by decide⟩ ⟨13, 2, 0, 324393, 104459, 137, 16384⟩
    (by decide) selected_cut_12236

theorem unmarked_context_12_26114_324394 : frontier 9 ⟨324394, by decide⟩
    (prefixCache 12 26114) (prefixPartial 12 26114) = false := by
  decide +kernel

theorem node_context_12_26114_324394 : EJMOriginalGlobalDAGData.nodes 9 ⟨324394, by decide⟩ =
    .split (coordinate 12) (![⟨324340, by decide⟩,⟨324377, by decide⟩,⟨324390, by decide⟩,⟨324393, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26114_324394 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26114 ⟨324394, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26114
    ⟨324394, by decide⟩ (by decide) (![⟨324340, by decide⟩,⟨324377, by decide⟩,⟨324390, by decide⟩,⟨324393, by decide⟩]) unmarked_context_12_26114_324394 node_context_12_26114_324394
  intro a
  fin_cases a
  · exact context_13_104456_324340
  · exact context_13_104457_324377
  · exact context_13_104458_324390
  · exact context_13_104459_324393

theorem selected_cut_12237 : selected 7 ⟨324430, by decide⟩
    (prefixPartial 14 417840) = some ⟨14, 2, 0, 324430, 417840, 1245, 4096⟩ := by
  decide +kernel

theorem context_14_417840_324430 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 417840 ⟨324430, by decide⟩ :=
  accepted_of_selected 14 417840 ⟨324430, by decide⟩ ⟨14, 2, 0, 324430, 417840, 1245, 4096⟩
    (by decide) selected_cut_12237

theorem selected_cut_12238 : selected 7 ⟨324445, by decide⟩
    (prefixPartial 14 417841) = some ⟨14, 2, 0, 324445, 417841, 1113, 4096⟩ := by
  decide +kernel

theorem context_14_417841_324445 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 417841 ⟨324445, by decide⟩ :=
  accepted_of_selected 14 417841 ⟨324445, by decide⟩ ⟨14, 2, 0, 324445, 417841, 1113, 4096⟩
    (by decide) selected_cut_12238

theorem selected_cut_12239 : selected 7 ⟨324454, by decide⟩
    (prefixPartial 14 417842) = some ⟨14, 2, 0, 324454, 417842, 885, 4096⟩ := by
  decide +kernel

theorem context_14_417842_324454 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 417842 ⟨324454, by decide⟩ :=
  accepted_of_selected 14 417842 ⟨324454, by decide⟩ ⟨14, 2, 0, 324454, 417842, 885, 4096⟩
    (by decide) selected_cut_12239

theorem selected_cut_12240 : selected 7 ⟨324469, by decide⟩
    (prefixPartial 14 417843) = some ⟨14, 2, 0, 324469, 417843, 1021, 4096⟩ := by
  decide +kernel

theorem context_14_417843_324469 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 417843 ⟨324469, by decide⟩ :=
  accepted_of_selected 14 417843 ⟨324469, by decide⟩ ⟨14, 2, 0, 324469, 417843, 1021, 4096⟩
    (by decide) selected_cut_12240

theorem unmarked_context_13_104460_324470 : frontier 8 ⟨324470, by decide⟩
    (prefixCache 13 104460) (prefixPartial 13 104460) = false := by
  decide +kernel

theorem node_context_13_104460_324470 : EJMOriginalGlobalDAGData.nodes 8 ⟨324470, by decide⟩ =
    .split (coordinate 13) (![⟨324430, by decide⟩,⟨324445, by decide⟩,⟨324454, by decide⟩,⟨324469, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_104460_324470 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104460 ⟨324470, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 104460
    ⟨324470, by decide⟩ (by decide) (![⟨324430, by decide⟩,⟨324445, by decide⟩,⟨324454, by decide⟩,⟨324469, by decide⟩]) unmarked_context_13_104460_324470 node_context_13_104460_324470
  intro a
  fin_cases a
  · exact context_14_417840_324430
  · exact context_14_417841_324445
  · exact context_14_417842_324454
  · exact context_14_417843_324469

theorem selected_cut_12241 : selected 8 ⟨324546, by decide⟩
    (prefixPartial 13 104461) = some ⟨13, 2, 0, 324546, 104461, 3841, 16384⟩ := by
  decide +kernel

theorem context_13_104461_324546 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104461 ⟨324546, by decide⟩ :=
  accepted_of_selected 13 104461 ⟨324546, by decide⟩ ⟨13, 2, 0, 324546, 104461, 3841, 16384⟩
    (by decide) selected_cut_12241

theorem selected_cut_12242 : selected 8 ⟨324582, by decide⟩
    (prefixPartial 13 104462) = some ⟨13, 2, 0, 324582, 104462, 2217, 16384⟩ := by
  decide +kernel

theorem context_13_104462_324582 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104462 ⟨324582, by decide⟩ :=
  accepted_of_selected 13 104462 ⟨324582, by decide⟩ ⟨13, 2, 0, 324582, 104462, 2217, 16384⟩
    (by decide) selected_cut_12242

theorem selected_cut_12243 : selected 8 ⟨324595, by decide⟩
    (prefixPartial 13 104463) = some ⟨13, 2, 0, 324595, 104463, 1161, 16384⟩ := by
  decide +kernel

theorem context_13_104463_324595 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104463 ⟨324595, by decide⟩ :=
  accepted_of_selected 13 104463 ⟨324595, by decide⟩ ⟨13, 2, 0, 324595, 104463, 1161, 16384⟩
    (by decide) selected_cut_12243

theorem unmarked_context_12_26115_324596 : frontier 9 ⟨324596, by decide⟩
    (prefixCache 12 26115) (prefixPartial 12 26115) = false := by
  decide +kernel

theorem node_context_12_26115_324596 : EJMOriginalGlobalDAGData.nodes 9 ⟨324596, by decide⟩ =
    .split (coordinate 12) (![⟨324470, by decide⟩,⟨324546, by decide⟩,⟨324582, by decide⟩,⟨324595, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26115_324596 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26115 ⟨324596, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26115
    ⟨324596, by decide⟩ (by decide) (![⟨324470, by decide⟩,⟨324546, by decide⟩,⟨324582, by decide⟩,⟨324595, by decide⟩]) unmarked_context_12_26115_324596 node_context_12_26115_324596
  intro a
  fin_cases a
  · exact context_13_104460_324470
  · exact context_13_104461_324546
  · exact context_13_104462_324582
  · exact context_13_104463_324595

theorem unmarked_context_11_6528_324597 : frontier 10 ⟨324597, by decide⟩
    (prefixCache 11 6528) (prefixPartial 11 6528) = false := by
  decide +kernel

theorem node_context_11_6528_324597 : EJMOriginalGlobalDAGData.nodes 10 ⟨324597, by decide⟩ =
    .split (coordinate 11) (![⟨34034, by decide⟩,⟨301653, by decide⟩,⟨324394, by decide⟩,⟨324596, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6528_324597 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6528 ⟨324597, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6528
    ⟨324597, by decide⟩ (by decide) (![⟨34034, by decide⟩,⟨301653, by decide⟩,⟨324394, by decide⟩,⟨324596, by decide⟩]) unmarked_context_11_6528_324597 node_context_11_6528_324597
  intro a
  fin_cases a
  · exact context_12_26112_34034
  · exact context_12_26113_301653
  · exact context_12_26114_324394
  · exact context_12_26115_324596

theorem selected_cut_12244 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 26116) = some ⟨12, 1, 0, 34034, 26116, 1, 65536⟩ := by
  decide +kernel

theorem context_12_26116_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26116 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 26116 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 26116, 1, 65536⟩
    (by decide) selected_cut_12244

theorem selected_cut_12245 : selected 8 ⟨324642, by decide⟩
    (prefixPartial 13 104468) = some ⟨13, 2, 0, 324642, 104468, 3717, 16384⟩ := by
  decide +kernel

theorem context_13_104468_324642 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104468 ⟨324642, by decide⟩ :=
  accepted_of_selected 13 104468 ⟨324642, by decide⟩ ⟨13, 2, 0, 324642, 104468, 3717, 16384⟩
    (by decide) selected_cut_12245

theorem selected_cut_12246 : selected 8 ⟨324692, by decide⟩
    (prefixPartial 13 104469) = some ⟨13, 2, 0, 324692, 104469, 3269, 16384⟩ := by
  decide +kernel

theorem context_13_104469_324692 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104469 ⟨324692, by decide⟩ :=
  accepted_of_selected 13 104469 ⟨324692, by decide⟩ ⟨13, 2, 0, 324692, 104469, 3269, 16384⟩
    (by decide) selected_cut_12246

theorem selected_cut_12247 : selected 8 ⟨324718, by decide⟩
    (prefixPartial 13 104470) = some ⟨13, 2, 0, 324718, 104470, 1945, 16384⟩ := by
  decide +kernel

theorem context_13_104470_324718 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104470 ⟨324718, by decide⟩ :=
  accepted_of_selected 13 104470 ⟨324718, by decide⟩ ⟨13, 2, 0, 324718, 104470, 1945, 16384⟩
    (by decide) selected_cut_12247

theorem selected_cut_12248 : selected 8 ⟨324731, by decide⟩
    (prefixPartial 13 104471) = some ⟨13, 2, 0, 324731, 104471, 1153, 16384⟩ := by
  decide +kernel

theorem context_13_104471_324731 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104471 ⟨324731, by decide⟩ :=
  accepted_of_selected 13 104471 ⟨324731, by decide⟩ ⟨13, 2, 0, 324731, 104471, 1153, 16384⟩
    (by decide) selected_cut_12248

theorem unmarked_context_12_26117_324732 : frontier 9 ⟨324732, by decide⟩
    (prefixCache 12 26117) (prefixPartial 12 26117) = false := by
  decide +kernel

theorem node_context_12_26117_324732 : EJMOriginalGlobalDAGData.nodes 9 ⟨324732, by decide⟩ =
    .split (coordinate 12) (![⟨324642, by decide⟩,⟨324692, by decide⟩,⟨324718, by decide⟩,⟨324731, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26117_324732 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26117 ⟨324732, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26117
    ⟨324732, by decide⟩ (by decide) (![⟨324642, by decide⟩,⟨324692, by decide⟩,⟨324718, by decide⟩,⟨324731, by decide⟩]) unmarked_context_12_26117_324732 node_context_12_26117_324732
  intro a
  fin_cases a
  · exact context_13_104468_324642
  · exact context_13_104469_324692
  · exact context_13_104470_324718
  · exact context_13_104471_324731

theorem selected_cut_12249 : selected 8 ⟨324768, by decide⟩
    (prefixPartial 13 104472) = some ⟨13, 2, 0, 324768, 104472, 2781, 16384⟩ := by
  decide +kernel

theorem context_13_104472_324768 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104472 ⟨324768, by decide⟩ :=
  accepted_of_selected 13 104472 ⟨324768, by decide⟩ ⟨13, 2, 0, 324768, 104472, 2781, 16384⟩
    (by decide) selected_cut_12249

theorem selected_cut_12250 : selected 8 ⟨324799, by decide⟩
    (prefixPartial 13 104473) = some ⟨13, 2, 0, 324799, 104473, 3029, 16384⟩ := by
  decide +kernel

theorem context_13_104473_324799 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104473 ⟨324799, by decide⟩ :=
  accepted_of_selected 13 104473 ⟨324799, by decide⟩ ⟨13, 2, 0, 324799, 104473, 3029, 16384⟩
    (by decide) selected_cut_12250

theorem selected_cut_12251 : selected 8 ⟨324816, by decide⟩
    (prefixPartial 13 104474) = some ⟨13, 2, 0, 324816, 104474, 1721, 16384⟩ := by
  decide +kernel

theorem context_13_104474_324816 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104474 ⟨324816, by decide⟩ :=
  accepted_of_selected 13 104474 ⟨324816, by decide⟩ ⟨13, 2, 0, 324816, 104474, 1721, 16384⟩
    (by decide) selected_cut_12251

theorem selected_cut_12252 : selected 8 ⟨324827, by decide⟩
    (prefixPartial 13 104475) = some ⟨13, 2, 0, 324827, 104475, 1185, 16384⟩ := by
  decide +kernel

theorem context_13_104475_324827 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104475 ⟨324827, by decide⟩ :=
  accepted_of_selected 13 104475 ⟨324827, by decide⟩ ⟨13, 2, 0, 324827, 104475, 1185, 16384⟩
    (by decide) selected_cut_12252

theorem unmarked_context_12_26118_324828 : frontier 9 ⟨324828, by decide⟩
    (prefixCache 12 26118) (prefixPartial 12 26118) = false := by
  decide +kernel

theorem node_context_12_26118_324828 : EJMOriginalGlobalDAGData.nodes 9 ⟨324828, by decide⟩ =
    .split (coordinate 12) (![⟨324768, by decide⟩,⟨324799, by decide⟩,⟨324816, by decide⟩,⟨324827, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26118_324828 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26118 ⟨324828, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26118
    ⟨324828, by decide⟩ (by decide) (![⟨324768, by decide⟩,⟨324799, by decide⟩,⟨324816, by decide⟩,⟨324827, by decide⟩]) unmarked_context_12_26118_324828 node_context_12_26118_324828
  intro a
  fin_cases a
  · exact context_13_104472_324768
  · exact context_13_104473_324799
  · exact context_13_104474_324816
  · exact context_13_104475_324827

theorem selected_cut_12253 : selected 8 ⟨324879, by decide⟩
    (prefixPartial 13 104476) = some ⟨13, 2, 0, 324879, 104476, 3653, 16384⟩ := by
  decide +kernel

theorem context_13_104476_324879 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104476 ⟨324879, by decide⟩ :=
  accepted_of_selected 13 104476 ⟨324879, by decide⟩ ⟨13, 2, 0, 324879, 104476, 3653, 16384⟩
    (by decide) selected_cut_12253

theorem selected_cut_12254 : selected 8 ⟨324939, by decide⟩
    (prefixPartial 13 104477) = some ⟨13, 2, 0, 324939, 104477, 3909, 16384⟩ := by
  decide +kernel

theorem context_13_104477_324939 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104477 ⟨324939, by decide⟩ :=
  accepted_of_selected 13 104477 ⟨324939, by decide⟩ ⟨13, 2, 0, 324939, 104477, 3909, 16384⟩
    (by decide) selected_cut_12254

theorem selected_cut_12255 : selected 8 ⟨324974, by decide⟩
    (prefixPartial 13 104478) = some ⟨13, 2, 0, 324974, 104478, 2205, 16384⟩ := by
  decide +kernel

theorem context_13_104478_324974 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104478 ⟨324974, by decide⟩ :=
  accepted_of_selected 13 104478 ⟨324974, by decide⟩ ⟨13, 2, 0, 324974, 104478, 2205, 16384⟩
    (by decide) selected_cut_12255

theorem selected_cut_12256 : selected 8 ⟨324980, by decide⟩
    (prefixPartial 13 104479) = some ⟨13, 2, 0, 324980, 104479, 1193, 16384⟩ := by
  decide +kernel

theorem context_13_104479_324980 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104479 ⟨324980, by decide⟩ :=
  accepted_of_selected 13 104479 ⟨324980, by decide⟩ ⟨13, 2, 0, 324980, 104479, 1193, 16384⟩
    (by decide) selected_cut_12256

theorem unmarked_context_12_26119_324981 : frontier 9 ⟨324981, by decide⟩
    (prefixCache 12 26119) (prefixPartial 12 26119) = false := by
  decide +kernel

theorem node_context_12_26119_324981 : EJMOriginalGlobalDAGData.nodes 9 ⟨324981, by decide⟩ =
    .split (coordinate 12) (![⟨324879, by decide⟩,⟨324939, by decide⟩,⟨324974, by decide⟩,⟨324980, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26119_324981 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26119 ⟨324981, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26119
    ⟨324981, by decide⟩ (by decide) (![⟨324879, by decide⟩,⟨324939, by decide⟩,⟨324974, by decide⟩,⟨324980, by decide⟩]) unmarked_context_12_26119_324981 node_context_12_26119_324981
  intro a
  fin_cases a
  · exact context_13_104476_324879
  · exact context_13_104477_324939
  · exact context_13_104478_324974
  · exact context_13_104479_324980

theorem unmarked_context_11_6529_324982 : frontier 10 ⟨324982, by decide⟩
    (prefixCache 11 6529) (prefixPartial 11 6529) = false := by
  decide +kernel

theorem node_context_11_6529_324982 : EJMOriginalGlobalDAGData.nodes 10 ⟨324982, by decide⟩ =
    .split (coordinate 11) (![⟨34034, by decide⟩,⟨324732, by decide⟩,⟨324828, by decide⟩,⟨324981, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6529_324982 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6529 ⟨324982, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6529
    ⟨324982, by decide⟩ (by decide) (![⟨34034, by decide⟩,⟨324732, by decide⟩,⟨324828, by decide⟩,⟨324981, by decide⟩]) unmarked_context_11_6529_324982 node_context_11_6529_324982
  intro a
  fin_cases a
  · exact context_12_26116_34034
  · exact context_12_26117_324732
  · exact context_12_26118_324828
  · exact context_12_26119_324981

theorem selected_cut_12257 : selected 8 ⟨325030, by decide⟩
    (prefixPartial 13 104480) = some ⟨13, 2, 0, 325030, 104480, 2477, 16384⟩ := by
  decide +kernel

theorem context_13_104480_325030 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104480 ⟨325030, by decide⟩ :=
  accepted_of_selected 13 104480 ⟨325030, by decide⟩ ⟨13, 2, 0, 325030, 104480, 2477, 16384⟩
    (by decide) selected_cut_12257

theorem selected_cut_12258 : selected 8 ⟨325089, by decide⟩
    (prefixPartial 13 104481) = some ⟨13, 2, 0, 325089, 104481, 3029, 16384⟩ := by
  decide +kernel

theorem context_13_104481_325089 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104481 ⟨325089, by decide⟩ :=
  accepted_of_selected 13 104481 ⟨325089, by decide⟩ ⟨13, 2, 0, 325089, 104481, 3029, 16384⟩
    (by decide) selected_cut_12258

theorem selected_cut_12259 : selected 8 ⟨325111, by decide⟩
    (prefixPartial 13 104482) = some ⟨13, 2, 0, 325111, 104482, 1685, 16384⟩ := by
  decide +kernel

theorem context_13_104482_325111 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104482 ⟨325111, by decide⟩ :=
  accepted_of_selected 13 104482 ⟨325111, by decide⟩ ⟨13, 2, 0, 325111, 104482, 1685, 16384⟩
    (by decide) selected_cut_12259

theorem selected_cut_12260 : selected 8 ⟨325127, by decide⟩
    (prefixPartial 13 104483) = some ⟨13, 2, 0, 325127, 104483, 1125, 16384⟩ := by
  decide +kernel

theorem context_13_104483_325127 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104483 ⟨325127, by decide⟩ :=
  accepted_of_selected 13 104483 ⟨325127, by decide⟩ ⟨13, 2, 0, 325127, 104483, 1125, 16384⟩
    (by decide) selected_cut_12260

theorem unmarked_context_12_26120_325128 : frontier 9 ⟨325128, by decide⟩
    (prefixCache 12 26120) (prefixPartial 12 26120) = false := by
  decide +kernel

theorem node_context_12_26120_325128 : EJMOriginalGlobalDAGData.nodes 9 ⟨325128, by decide⟩ =
    .split (coordinate 12) (![⟨325030, by decide⟩,⟨325089, by decide⟩,⟨325111, by decide⟩,⟨325127, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26120_325128 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26120 ⟨325128, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26120
    ⟨325128, by decide⟩ (by decide) (![⟨325030, by decide⟩,⟨325089, by decide⟩,⟨325111, by decide⟩,⟨325127, by decide⟩]) unmarked_context_12_26120_325128 node_context_12_26120_325128
  intro a
  fin_cases a
  · exact context_13_104480_325030
  · exact context_13_104481_325089
  · exact context_13_104482_325111
  · exact context_13_104483_325127

theorem selected_cut_12261 : selected 8 ⟨325182, by decide⟩
    (prefixPartial 13 104484) = some ⟨13, 2, 0, 325182, 104484, 3525, 16384⟩ := by
  decide +kernel

theorem context_13_104484_325182 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104484 ⟨325182, by decide⟩ :=
  accepted_of_selected 13 104484 ⟨325182, by decide⟩ ⟨13, 2, 0, 325182, 104484, 3525, 16384⟩
    (by decide) selected_cut_12261

theorem selected_cut_12262 : selected 8 ⟨325245, by decide⟩
    (prefixPartial 13 104485) = some ⟨13, 2, 0, 325245, 104485, 3333, 16384⟩ := by
  decide +kernel

theorem context_13_104485_325245 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104485 ⟨325245, by decide⟩ :=
  accepted_of_selected 13 104485 ⟨325245, by decide⟩ ⟨13, 2, 0, 325245, 104485, 3333, 16384⟩
    (by decide) selected_cut_12262

theorem selected_cut_12263 : selected 8 ⟨325263, by decide⟩
    (prefixPartial 13 104486) = some ⟨13, 2, 0, 325263, 104486, 1997, 16384⟩ := by
  decide +kernel

theorem context_13_104486_325263 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104486 ⟨325263, by decide⟩ :=
  accepted_of_selected 13 104486 ⟨325263, by decide⟩ ⟨13, 2, 0, 325263, 104486, 1997, 16384⟩
    (by decide) selected_cut_12263

theorem selected_cut_12264 : selected 8 ⟨325274, by decide⟩
    (prefixPartial 13 104487) = some ⟨13, 2, 0, 325274, 104487, 1197, 16384⟩ := by
  decide +kernel

theorem context_13_104487_325274 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104487 ⟨325274, by decide⟩ :=
  accepted_of_selected 13 104487 ⟨325274, by decide⟩ ⟨13, 2, 0, 325274, 104487, 1197, 16384⟩
    (by decide) selected_cut_12264

theorem unmarked_context_12_26121_325275 : frontier 9 ⟨325275, by decide⟩
    (prefixCache 12 26121) (prefixPartial 12 26121) = false := by
  decide +kernel

theorem node_context_12_26121_325275 : EJMOriginalGlobalDAGData.nodes 9 ⟨325275, by decide⟩ =
    .split (coordinate 12) (![⟨325182, by decide⟩,⟨325245, by decide⟩,⟨325263, by decide⟩,⟨325274, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26121_325275 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26121 ⟨325275, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26121
    ⟨325275, by decide⟩ (by decide) (![⟨325182, by decide⟩,⟨325245, by decide⟩,⟨325263, by decide⟩,⟨325274, by decide⟩]) unmarked_context_12_26121_325275 node_context_12_26121_325275
  intro a
  fin_cases a
  · exact context_13_104484_325182
  · exact context_13_104485_325245
  · exact context_13_104486_325263
  · exact context_13_104487_325274

theorem selected_cut_12265 : selected 7 ⟨325297, by decide⟩
    (prefixPartial 14 417952) = some ⟨14, 2, 0, 325297, 417952, 1145, 4096⟩ := by
  decide +kernel

theorem context_14_417952_325297 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 417952 ⟨325297, by decide⟩ :=
  accepted_of_selected 14 417952 ⟨325297, by decide⟩ ⟨14, 2, 0, 325297, 417952, 1145, 4096⟩
    (by decide) selected_cut_12265

theorem selected_cut_12266 : selected 7 ⟨325314, by decide⟩
    (prefixPartial 14 417953) = some ⟨14, 2, 0, 325314, 417953, 1241, 4096⟩ := by
  decide +kernel

theorem context_14_417953_325314 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 417953 ⟨325314, by decide⟩ :=
  accepted_of_selected 14 417953 ⟨325314, by decide⟩ ⟨14, 2, 0, 325314, 417953, 1241, 4096⟩
    (by decide) selected_cut_12266

theorem selected_cut_12267 : selected 7 ⟨325328, by decide⟩
    (prefixPartial 14 417954) = some ⟨14, 2, 0, 325328, 417954, 1021, 4096⟩ := by
  decide +kernel

theorem context_14_417954_325328 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 417954 ⟨325328, by decide⟩ :=
  accepted_of_selected 14 417954 ⟨325328, by decide⟩ ⟨14, 2, 0, 325328, 417954, 1021, 4096⟩
    (by decide) selected_cut_12267

theorem selected_cut_12268 : selected 7 ⟨325355, by decide⟩
    (prefixPartial 14 417955) = some ⟨14, 2, 0, 325355, 417955, 1221, 4096⟩ := by
  decide +kernel

theorem context_14_417955_325355 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 417955 ⟨325355, by decide⟩ :=
  accepted_of_selected 14 417955 ⟨325355, by decide⟩ ⟨14, 2, 0, 325355, 417955, 1221, 4096⟩
    (by decide) selected_cut_12268

theorem unmarked_context_13_104488_325356 : frontier 8 ⟨325356, by decide⟩
    (prefixCache 13 104488) (prefixPartial 13 104488) = false := by
  decide +kernel

theorem node_context_13_104488_325356 : EJMOriginalGlobalDAGData.nodes 8 ⟨325356, by decide⟩ =
    .split (coordinate 13) (![⟨325297, by decide⟩,⟨325314, by decide⟩,⟨325328, by decide⟩,⟨325355, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_104488_325356 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104488 ⟨325356, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 104488
    ⟨325356, by decide⟩ (by decide) (![⟨325297, by decide⟩,⟨325314, by decide⟩,⟨325328, by decide⟩,⟨325355, by decide⟩]) unmarked_context_13_104488_325356 node_context_13_104488_325356
  intro a
  fin_cases a
  · exact context_14_417952_325297
  · exact context_14_417953_325314
  · exact context_14_417954_325328
  · exact context_14_417955_325355

theorem selected_cut_12269 : selected 7 ⟨325390, by decide⟩
    (prefixPartial 14 417956) = some ⟨14, 2, 0, 325390, 417956, 1633, 4096⟩ := by
  decide +kernel

theorem context_14_417956_325390 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 417956 ⟨325390, by decide⟩ :=
  accepted_of_selected 14 417956 ⟨325390, by decide⟩ ⟨14, 2, 0, 325390, 417956, 1633, 4096⟩
    (by decide) selected_cut_12269

theorem selected_cut_12270 : selected 7 ⟨325412, by decide⟩
    (prefixPartial 14 417957) = some ⟨14, 2, 0, 325412, 417957, 1157, 4096⟩ := by
  decide +kernel

theorem context_14_417957_325412 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 417957 ⟨325412, by decide⟩ :=
  accepted_of_selected 14 417957 ⟨325412, by decide⟩ ⟨14, 2, 0, 325412, 417957, 1157, 4096⟩
    (by decide) selected_cut_12270

theorem selected_cut_12271 : selected 7 ⟨325432, by decide⟩
    (prefixPartial 14 417958) = some ⟨14, 2, 0, 325432, 417958, 1101, 4096⟩ := by
  decide +kernel

theorem context_14_417958_325432 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 417958 ⟨325432, by decide⟩ :=
  accepted_of_selected 14 417958 ⟨325432, by decide⟩ ⟨14, 2, 0, 325432, 417958, 1101, 4096⟩
    (by decide) selected_cut_12271

theorem selected_cut_12272 : selected 7 ⟨325447, by decide⟩
    (prefixPartial 14 417959) = some ⟨14, 2, 0, 325447, 417959, 1153, 4096⟩ := by
  decide +kernel

theorem context_14_417959_325447 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 417959 ⟨325447, by decide⟩ :=
  accepted_of_selected 14 417959 ⟨325447, by decide⟩ ⟨14, 2, 0, 325447, 417959, 1153, 4096⟩
    (by decide) selected_cut_12272

theorem unmarked_context_13_104489_325448 : frontier 8 ⟨325448, by decide⟩
    (prefixCache 13 104489) (prefixPartial 13 104489) = false := by
  decide +kernel

theorem node_context_13_104489_325448 : EJMOriginalGlobalDAGData.nodes 8 ⟨325448, by decide⟩ =
    .split (coordinate 13) (![⟨325390, by decide⟩,⟨325412, by decide⟩,⟨325432, by decide⟩,⟨325447, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_104489_325448 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104489 ⟨325448, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 104489
    ⟨325448, by decide⟩ (by decide) (![⟨325390, by decide⟩,⟨325412, by decide⟩,⟨325432, by decide⟩,⟨325447, by decide⟩]) unmarked_context_13_104489_325448 node_context_13_104489_325448
  intro a
  fin_cases a
  · exact context_14_417956_325390
  · exact context_14_417957_325412
  · exact context_14_417958_325432
  · exact context_14_417959_325447

theorem selected_cut_12273 : selected 8 ⟨325481, by decide⟩
    (prefixPartial 13 104490) = some ⟨13, 2, 0, 325481, 104490, 2665, 16384⟩ := by
  decide +kernel

theorem context_13_104490_325481 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104490 ⟨325481, by decide⟩ :=
  accepted_of_selected 13 104490 ⟨325481, by decide⟩ ⟨13, 2, 0, 325481, 104490, 2665, 16384⟩
    (by decide) selected_cut_12273

theorem selected_cut_12274 : selected 8 ⟨325506, by decide⟩
    (prefixPartial 13 104491) = some ⟨13, 2, 0, 325506, 104491, 1653, 16384⟩ := by
  decide +kernel

theorem context_13_104491_325506 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104491 ⟨325506, by decide⟩ :=
  accepted_of_selected 13 104491 ⟨325506, by decide⟩ ⟨13, 2, 0, 325506, 104491, 1653, 16384⟩
    (by decide) selected_cut_12274

theorem unmarked_context_12_26122_325507 : frontier 9 ⟨325507, by decide⟩
    (prefixCache 12 26122) (prefixPartial 12 26122) = false := by
  decide +kernel

theorem node_context_12_26122_325507 : EJMOriginalGlobalDAGData.nodes 9 ⟨325507, by decide⟩ =
    .split (coordinate 12) (![⟨325356, by decide⟩,⟨325448, by decide⟩,⟨325481, by decide⟩,⟨325506, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26122_325507 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26122 ⟨325507, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26122
    ⟨325507, by decide⟩ (by decide) (![⟨325356, by decide⟩,⟨325448, by decide⟩,⟨325481, by decide⟩,⟨325506, by decide⟩]) unmarked_context_12_26122_325507 node_context_12_26122_325507
  intro a
  fin_cases a
  · exact context_13_104488_325356
  · exact context_13_104489_325448
  · exact context_13_104490_325481
  · exact context_13_104491_325506

theorem selected_cut_12275 : selected 8 ⟨325560, by decide⟩
    (prefixPartial 13 104492) = some ⟨13, 2, 0, 325560, 104492, 3201, 16384⟩ := by
  decide +kernel

theorem context_13_104492_325560 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104492 ⟨325560, by decide⟩ :=
  accepted_of_selected 13 104492 ⟨325560, by decide⟩ ⟨13, 2, 0, 325560, 104492, 3201, 16384⟩
    (by decide) selected_cut_12275

theorem selected_cut_12276 : selected 7 ⟨325590, by decide⟩
    (prefixPartial 14 417972) = some ⟨14, 2, 0, 325590, 417972, 1437, 4096⟩ := by
  decide +kernel

theorem context_14_417972_325590 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 417972 ⟨325590, by decide⟩ :=
  accepted_of_selected 14 417972 ⟨325590, by decide⟩ ⟨14, 2, 0, 325590, 417972, 1437, 4096⟩
    (by decide) selected_cut_12276

theorem selected_cut_12277 : selected 7 ⟨325609, by decide⟩
    (prefixPartial 14 417973) = some ⟨14, 2, 0, 325609, 417973, 929, 4096⟩ := by
  decide +kernel

theorem context_14_417973_325609 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 417973 ⟨325609, by decide⟩ :=
  accepted_of_selected 14 417973 ⟨325609, by decide⟩ ⟨14, 2, 0, 325609, 417973, 929, 4096⟩
    (by decide) selected_cut_12277

theorem selected_cut_12278 : selected 7 ⟨325624, by decide⟩
    (prefixPartial 14 417974) = some ⟨14, 2, 0, 325624, 417974, 909, 4096⟩ := by
  decide +kernel

theorem context_14_417974_325624 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 417974 ⟨325624, by decide⟩ :=
  accepted_of_selected 14 417974 ⟨325624, by decide⟩ ⟨14, 2, 0, 325624, 417974, 909, 4096⟩
    (by decide) selected_cut_12278

theorem selected_cut_12279 : selected 7 ⟨325635, by decide⟩
    (prefixPartial 14 417975) = some ⟨14, 2, 0, 325635, 417975, 869, 4096⟩ := by
  decide +kernel

theorem context_14_417975_325635 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 417975 ⟨325635, by decide⟩ :=
  accepted_of_selected 14 417975 ⟨325635, by decide⟩ ⟨14, 2, 0, 325635, 417975, 869, 4096⟩
    (by decide) selected_cut_12279

theorem unmarked_context_13_104493_325636 : frontier 8 ⟨325636, by decide⟩
    (prefixCache 13 104493) (prefixPartial 13 104493) = false := by
  decide +kernel

theorem node_context_13_104493_325636 : EJMOriginalGlobalDAGData.nodes 8 ⟨325636, by decide⟩ =
    .split (coordinate 13) (![⟨325590, by decide⟩,⟨325609, by decide⟩,⟨325624, by decide⟩,⟨325635, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_104493_325636 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104493 ⟨325636, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 104493
    ⟨325636, by decide⟩ (by decide) (![⟨325590, by decide⟩,⟨325609, by decide⟩,⟨325624, by decide⟩,⟨325635, by decide⟩]) unmarked_context_13_104493_325636 node_context_13_104493_325636
  intro a
  fin_cases a
  · exact context_14_417972_325590
  · exact context_14_417973_325609
  · exact context_14_417974_325624
  · exact context_14_417975_325635

theorem selected_cut_12280 : selected 8 ⟨325660, by decide⟩
    (prefixPartial 13 104494) = some ⟨13, 2, 0, 325660, 104494, 2001, 16384⟩ := by
  decide +kernel

theorem context_13_104494_325660 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104494 ⟨325660, by decide⟩ :=
  accepted_of_selected 13 104494 ⟨325660, by decide⟩ ⟨13, 2, 0, 325660, 104494, 2001, 16384⟩
    (by decide) selected_cut_12280

theorem selected_cut_12281 : selected 8 ⟨325668, by decide⟩
    (prefixPartial 13 104495) = some ⟨13, 2, 0, 325668, 104495, 1153, 16384⟩ := by
  decide +kernel

theorem context_13_104495_325668 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104495 ⟨325668, by decide⟩ :=
  accepted_of_selected 13 104495 ⟨325668, by decide⟩ ⟨13, 2, 0, 325668, 104495, 1153, 16384⟩
    (by decide) selected_cut_12281

theorem unmarked_context_12_26123_325669 : frontier 9 ⟨325669, by decide⟩
    (prefixCache 12 26123) (prefixPartial 12 26123) = false := by
  decide +kernel

theorem node_context_12_26123_325669 : EJMOriginalGlobalDAGData.nodes 9 ⟨325669, by decide⟩ =
    .split (coordinate 12) (![⟨325560, by decide⟩,⟨325636, by decide⟩,⟨325660, by decide⟩,⟨325668, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26123_325669 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26123 ⟨325669, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26123
    ⟨325669, by decide⟩ (by decide) (![⟨325560, by decide⟩,⟨325636, by decide⟩,⟨325660, by decide⟩,⟨325668, by decide⟩]) unmarked_context_12_26123_325669 node_context_12_26123_325669
  intro a
  fin_cases a
  · exact context_13_104492_325560
  · exact context_13_104493_325636
  · exact context_13_104494_325660
  · exact context_13_104495_325668

theorem unmarked_context_11_6530_325670 : frontier 10 ⟨325670, by decide⟩
    (prefixCache 11 6530) (prefixPartial 11 6530) = false := by
  decide +kernel

theorem node_context_11_6530_325670 : EJMOriginalGlobalDAGData.nodes 10 ⟨325670, by decide⟩ =
    .split (coordinate 11) (![⟨325128, by decide⟩,⟨325275, by decide⟩,⟨325507, by decide⟩,⟨325669, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6530_325670 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6530 ⟨325670, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6530
    ⟨325670, by decide⟩ (by decide) (![⟨325128, by decide⟩,⟨325275, by decide⟩,⟨325507, by decide⟩,⟨325669, by decide⟩]) unmarked_context_11_6530_325670 node_context_11_6530_325670
  intro a
  fin_cases a
  · exact context_12_26120_325128
  · exact context_12_26121_325275
  · exact context_12_26122_325507
  · exact context_12_26123_325669

theorem selected_cut_12282 : selected 8 ⟨325701, by decide⟩
    (prefixPartial 13 104496) = some ⟨13, 2, 0, 325701, 104496, 2229, 16384⟩ := by
  decide +kernel

theorem context_13_104496_325701 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104496 ⟨325701, by decide⟩ :=
  accepted_of_selected 13 104496 ⟨325701, by decide⟩ ⟨13, 2, 0, 325701, 104496, 2229, 16384⟩
    (by decide) selected_cut_12282

theorem selected_cut_12283 : selected 8 ⟨325750, by decide⟩
    (prefixPartial 13 104497) = some ⟨13, 2, 0, 325750, 104497, 3013, 16384⟩ := by
  decide +kernel

theorem context_13_104497_325750 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104497 ⟨325750, by decide⟩ :=
  accepted_of_selected 13 104497 ⟨325750, by decide⟩ ⟨13, 2, 0, 325750, 104497, 3013, 16384⟩
    (by decide) selected_cut_12283

theorem selected_cut_12284 : selected 8 ⟨325776, by decide⟩
    (prefixPartial 13 104498) = some ⟨13, 2, 0, 325776, 104498, 1869, 16384⟩ := by
  decide +kernel

theorem context_13_104498_325776 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104498 ⟨325776, by decide⟩ :=
  accepted_of_selected 13 104498 ⟨325776, by decide⟩ ⟨13, 2, 0, 325776, 104498, 1869, 16384⟩
    (by decide) selected_cut_12284

theorem selected_cut_12285 : selected 8 ⟨325786, by decide⟩
    (prefixPartial 13 104499) = some ⟨13, 2, 0, 325786, 104499, 1057, 16384⟩ := by
  decide +kernel

theorem context_13_104499_325786 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104499 ⟨325786, by decide⟩ :=
  accepted_of_selected 13 104499 ⟨325786, by decide⟩ ⟨13, 2, 0, 325786, 104499, 1057, 16384⟩
    (by decide) selected_cut_12285

theorem unmarked_context_12_26124_325787 : frontier 9 ⟨325787, by decide⟩
    (prefixCache 12 26124) (prefixPartial 12 26124) = false := by
  decide +kernel

theorem node_context_12_26124_325787 : EJMOriginalGlobalDAGData.nodes 9 ⟨325787, by decide⟩ =
    .split (coordinate 12) (![⟨325701, by decide⟩,⟨325750, by decide⟩,⟨325776, by decide⟩,⟨325786, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26124_325787 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26124 ⟨325787, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26124
    ⟨325787, by decide⟩ (by decide) (![⟨325701, by decide⟩,⟨325750, by decide⟩,⟨325776, by decide⟩,⟨325786, by decide⟩]) unmarked_context_12_26124_325787 node_context_12_26124_325787
  intro a
  fin_cases a
  · exact context_13_104496_325701
  · exact context_13_104497_325750
  · exact context_13_104498_325776
  · exact context_13_104499_325786

theorem selected_cut_12286 : selected 8 ⟨325836, by decide⟩
    (prefixPartial 13 104500) = some ⟨13, 2, 0, 325836, 104500, 3345, 16384⟩ := by
  decide +kernel

theorem context_13_104500_325836 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104500 ⟨325836, by decide⟩ :=
  accepted_of_selected 13 104500 ⟨325836, by decide⟩ ⟨13, 2, 0, 325836, 104500, 3345, 16384⟩
    (by decide) selected_cut_12286

theorem selected_cut_12287 : selected 8 ⟨325907, by decide⟩
    (prefixPartial 13 104501) = some ⟨13, 2, 0, 325907, 104501, 3437, 16384⟩ := by
  decide +kernel

theorem context_13_104501_325907 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104501 ⟨325907, by decide⟩ :=
  accepted_of_selected 13 104501 ⟨325907, by decide⟩ ⟨13, 2, 0, 325907, 104501, 3437, 16384⟩
    (by decide) selected_cut_12287

theorem selected_cut_12288 : selected 8 ⟨325933, by decide⟩
    (prefixPartial 13 104502) = some ⟨13, 2, 0, 325933, 104502, 1957, 16384⟩ := by
  decide +kernel

theorem context_13_104502_325933 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104502 ⟨325933, by decide⟩ :=
  accepted_of_selected 13 104502 ⟨325933, by decide⟩ ⟨13, 2, 0, 325933, 104502, 1957, 16384⟩
    (by decide) selected_cut_12288

theorem selected_cut_12289 : selected 8 ⟨325943, by decide⟩
    (prefixPartial 13 104503) = some ⟨13, 2, 0, 325943, 104503, 1021, 16384⟩ := by
  decide +kernel

theorem context_13_104503_325943 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104503 ⟨325943, by decide⟩ :=
  accepted_of_selected 13 104503 ⟨325943, by decide⟩ ⟨13, 2, 0, 325943, 104503, 1021, 16384⟩
    (by decide) selected_cut_12289

theorem unmarked_context_12_26125_325944 : frontier 9 ⟨325944, by decide⟩
    (prefixCache 12 26125) (prefixPartial 12 26125) = false := by
  decide +kernel

theorem node_context_12_26125_325944 : EJMOriginalGlobalDAGData.nodes 9 ⟨325944, by decide⟩ =
    .split (coordinate 12) (![⟨325836, by decide⟩,⟨325907, by decide⟩,⟨325933, by decide⟩,⟨325943, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26125_325944 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26125 ⟨325944, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26125
    ⟨325944, by decide⟩ (by decide) (![⟨325836, by decide⟩,⟨325907, by decide⟩,⟨325933, by decide⟩,⟨325943, by decide⟩]) unmarked_context_12_26125_325944 node_context_12_26125_325944
  intro a
  fin_cases a
  · exact context_13_104500_325836
  · exact context_13_104501_325907
  · exact context_13_104502_325933
  · exact context_13_104503_325943

theorem selected_cut_12290 : selected 8 ⟨325976, by decide⟩
    (prefixPartial 13 104504) = some ⟨13, 2, 0, 325976, 104504, 2437, 16384⟩ := by
  decide +kernel

theorem context_13_104504_325976 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104504 ⟨325976, by decide⟩ :=
  accepted_of_selected 13 104504 ⟨325976, by decide⟩ ⟨13, 2, 0, 325976, 104504, 2437, 16384⟩
    (by decide) selected_cut_12290

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
