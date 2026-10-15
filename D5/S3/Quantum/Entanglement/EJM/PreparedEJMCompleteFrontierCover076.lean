/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover075
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_07299 : selected 9 ⟨212305, by decide⟩
    (prefixPartial 12 22200) = some ⟨12, 2, 0, 212305, 22200, 1049, 65536⟩ := by
  decide +kernel

theorem context_12_22200_212305 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22200 ⟨212305, by decide⟩ :=
  accepted_of_selected 12 22200 ⟨212305, by decide⟩ ⟨12, 2, 0, 212305, 22200, 1049, 65536⟩
    (by decide) selected_cut_07299

theorem selected_cut_07300 : selected 9 ⟨212319, by decide⟩
    (prefixPartial 12 22201) = some ⟨12, 2, 0, 212319, 22201, 1097, 65536⟩ := by
  decide +kernel

theorem context_12_22201_212319 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22201 ⟨212319, by decide⟩ :=
  accepted_of_selected 12 22201 ⟨212319, by decide⟩ ⟨12, 2, 0, 212319, 22201, 1097, 65536⟩
    (by decide) selected_cut_07300

theorem selected_cut_07301 : selected 9 ⟨212331, by decide⟩
    (prefixPartial 12 22202) = some ⟨12, 2, 0, 212331, 22202, 1385, 65536⟩ := by
  decide +kernel

theorem context_12_22202_212331 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22202 ⟨212331, by decide⟩ :=
  accepted_of_selected 12 22202 ⟨212331, by decide⟩ ⟨12, 2, 0, 212331, 22202, 1385, 65536⟩
    (by decide) selected_cut_07301

theorem selected_cut_07302 : selected 9 ⟨212344, by decide⟩
    (prefixPartial 12 22203) = some ⟨12, 2, 0, 212344, 22203, 933, 65536⟩ := by
  decide +kernel

theorem context_12_22203_212344 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22203 ⟨212344, by decide⟩ :=
  accepted_of_selected 12 22203 ⟨212344, by decide⟩ ⟨12, 2, 0, 212344, 22203, 933, 65536⟩
    (by decide) selected_cut_07302

theorem unmarked_context_11_5550_212345 : frontier 10 ⟨212345, by decide⟩
    (prefixCache 11 5550) (prefixPartial 11 5550) = false := by
  decide +kernel

theorem node_context_11_5550_212345 : EJMOriginalGlobalDAGData.nodes 10 ⟨212345, by decide⟩ =
    .split (coordinate 11) (![⟨212305, by decide⟩,⟨212319, by decide⟩,⟨212331, by decide⟩,⟨212344, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5550_212345 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5550 ⟨212345, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5550
    ⟨212345, by decide⟩ (by decide) (![⟨212305, by decide⟩,⟨212319, by decide⟩,⟨212331, by decide⟩,⟨212344, by decide⟩]) unmarked_context_11_5550_212345 node_context_11_5550_212345
  intro a
  fin_cases a
  · exact context_12_22200_212305
  · exact context_12_22201_212319
  · exact context_12_22202_212331
  · exact context_12_22203_212344

theorem selected_cut_07303 : selected 10 ⟨212396, by decide⟩
    (prefixPartial 11 5551) = some ⟨11, 2, 0, 212396, 5551, 4029, 262144⟩ := by
  decide +kernel

theorem context_11_5551_212396 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5551 ⟨212396, by decide⟩ :=
  accepted_of_selected 11 5551 ⟨212396, by decide⟩ ⟨11, 2, 0, 212396, 5551, 4029, 262144⟩
    (by decide) selected_cut_07303

theorem unmarked_context_10_1387_212397 : frontier 11 ⟨212397, by decide⟩
    (prefixCache 10 1387) (prefixPartial 10 1387) = false := by
  decide +kernel

theorem node_context_10_1387_212397 : EJMOriginalGlobalDAGData.nodes 11 ⟨212397, by decide⟩ =
    .split (coordinate 10) (![⟨212242, by decide⟩,⟨212295, by decide⟩,⟨212345, by decide⟩,⟨212396, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1387_212397 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1387 ⟨212397, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1387
    ⟨212397, by decide⟩ (by decide) (![⟨212242, by decide⟩,⟨212295, by decide⟩,⟨212345, by decide⟩,⟨212396, by decide⟩]) unmarked_context_10_1387_212397 node_context_10_1387_212397
  intro a
  fin_cases a
  · exact context_11_5548_212242
  · exact context_11_5549_212295
  · exact context_11_5550_212345
  · exact context_11_5551_212396

theorem unmarked_context_9_346_212398 : frontier 12 ⟨212398, by decide⟩
    (prefixCache 9 346) (prefixPartial 9 346) = false := by
  decide +kernel

theorem node_context_9_346_212398 : EJMOriginalGlobalDAGData.nodes 12 ⟨212398, by decide⟩ =
    .split (coordinate 9) (![⟨211456, by decide⟩,⟨211948, by decide⟩,⟨212192, by decide⟩,⟨212397, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_346_212398 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 346 ⟨212398, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 346
    ⟨212398, by decide⟩ (by decide) (![⟨211456, by decide⟩,⟨211948, by decide⟩,⟨212192, by decide⟩,⟨212397, by decide⟩]) unmarked_context_9_346_212398 node_context_9_346_212398
  intro a
  fin_cases a
  · exact context_10_1384_211456
  · exact context_10_1385_211948
  · exact context_10_1386_212192
  · exact context_10_1387_212397

theorem selected_cut_07304 : selected 9 ⟨212408, by decide⟩
    (prefixPartial 12 22208) = some ⟨12, 2, 0, 212408, 22208, 1085, 65536⟩ := by
  decide +kernel

theorem context_12_22208_212408 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22208 ⟨212408, by decide⟩ :=
  accepted_of_selected 12 22208 ⟨212408, by decide⟩ ⟨12, 2, 0, 212408, 22208, 1085, 65536⟩
    (by decide) selected_cut_07304

theorem selected_cut_07305 : selected 9 ⟨212419, by decide⟩
    (prefixPartial 12 22209) = some ⟨12, 2, 0, 212419, 22209, 1181, 65536⟩ := by
  decide +kernel

theorem context_12_22209_212419 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22209 ⟨212419, by decide⟩ :=
  accepted_of_selected 12 22209 ⟨212419, by decide⟩ ⟨12, 2, 0, 212419, 22209, 1181, 65536⟩
    (by decide) selected_cut_07305

theorem selected_cut_07306 : selected 9 ⟨212433, by decide⟩
    (prefixPartial 12 22210) = some ⟨12, 2, 0, 212433, 22210, 1241, 65536⟩ := by
  decide +kernel

theorem context_12_22210_212433 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22210 ⟨212433, by decide⟩ :=
  accepted_of_selected 12 22210 ⟨212433, by decide⟩ ⟨12, 2, 0, 212433, 22210, 1241, 65536⟩
    (by decide) selected_cut_07306

theorem selected_cut_07307 : selected 9 ⟨212443, by decide⟩
    (prefixPartial 12 22211) = some ⟨12, 2, 0, 212443, 22211, 1017, 65536⟩ := by
  decide +kernel

theorem context_12_22211_212443 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22211 ⟨212443, by decide⟩ :=
  accepted_of_selected 12 22211 ⟨212443, by decide⟩ ⟨12, 2, 0, 212443, 22211, 1017, 65536⟩
    (by decide) selected_cut_07307

theorem unmarked_context_11_5552_212444 : frontier 10 ⟨212444, by decide⟩
    (prefixCache 11 5552) (prefixPartial 11 5552) = false := by
  decide +kernel

theorem node_context_11_5552_212444 : EJMOriginalGlobalDAGData.nodes 10 ⟨212444, by decide⟩ =
    .split (coordinate 11) (![⟨212408, by decide⟩,⟨212419, by decide⟩,⟨212433, by decide⟩,⟨212443, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5552_212444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5552 ⟨212444, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5552
    ⟨212444, by decide⟩ (by decide) (![⟨212408, by decide⟩,⟨212419, by decide⟩,⟨212433, by decide⟩,⟨212443, by decide⟩]) unmarked_context_11_5552_212444 node_context_11_5552_212444
  intro a
  fin_cases a
  · exact context_12_22208_212408
  · exact context_12_22209_212419
  · exact context_12_22210_212433
  · exact context_12_22211_212443

theorem selected_cut_07308 : selected 10 ⟨212502, by decide⟩
    (prefixPartial 11 5553) = some ⟨11, 2, 0, 212502, 5553, 3941, 262144⟩ := by
  decide +kernel

theorem context_11_5553_212502 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5553 ⟨212502, by decide⟩ :=
  accepted_of_selected 11 5553 ⟨212502, by decide⟩ ⟨11, 2, 0, 212502, 5553, 3941, 262144⟩
    (by decide) selected_cut_07308

theorem selected_cut_07309 : selected 10 ⟨212546, by decide⟩
    (prefixPartial 11 5554) = some ⟨11, 2, 0, 212546, 5554, 3617, 262144⟩ := by
  decide +kernel

theorem context_11_5554_212546 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5554 ⟨212546, by decide⟩ :=
  accepted_of_selected 11 5554 ⟨212546, by decide⟩ ⟨11, 2, 0, 212546, 5554, 3617, 262144⟩
    (by decide) selected_cut_07309

theorem selected_cut_07310 : selected 10 ⟨212583, by decide⟩
    (prefixPartial 11 5555) = some ⟨11, 2, 0, 212583, 5555, 3369, 262144⟩ := by
  decide +kernel

theorem context_11_5555_212583 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5555 ⟨212583, by decide⟩ :=
  accepted_of_selected 11 5555 ⟨212583, by decide⟩ ⟨11, 2, 0, 212583, 5555, 3369, 262144⟩
    (by decide) selected_cut_07310

theorem unmarked_context_10_1388_212584 : frontier 11 ⟨212584, by decide⟩
    (prefixCache 10 1388) (prefixPartial 10 1388) = false := by
  decide +kernel

theorem node_context_10_1388_212584 : EJMOriginalGlobalDAGData.nodes 11 ⟨212584, by decide⟩ =
    .split (coordinate 10) (![⟨212444, by decide⟩,⟨212502, by decide⟩,⟨212546, by decide⟩,⟨212583, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1388_212584 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1388 ⟨212584, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1388
    ⟨212584, by decide⟩ (by decide) (![⟨212444, by decide⟩,⟨212502, by decide⟩,⟨212546, by decide⟩,⟨212583, by decide⟩]) unmarked_context_10_1388_212584 node_context_10_1388_212584
  intro a
  fin_cases a
  · exact context_11_5552_212444
  · exact context_11_5553_212502
  · exact context_11_5554_212546
  · exact context_11_5555_212583

theorem selected_cut_07311 : selected 10 ⟨212612, by decide⟩
    (prefixPartial 11 5556) = some ⟨11, 2, 0, 212612, 5556, 2917, 262144⟩ := by
  decide +kernel

theorem context_11_5556_212612 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5556 ⟨212612, by decide⟩ :=
  accepted_of_selected 11 5556 ⟨212612, by decide⟩ ⟨11, 2, 0, 212612, 5556, 2917, 262144⟩
    (by decide) selected_cut_07311

theorem selected_cut_07312 : selected 10 ⟨212647, by decide⟩
    (prefixPartial 11 5557) = some ⟨11, 2, 0, 212647, 5557, 2801, 262144⟩ := by
  decide +kernel

theorem context_11_5557_212647 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5557 ⟨212647, by decide⟩ :=
  accepted_of_selected 11 5557 ⟨212647, by decide⟩ ⟨11, 2, 0, 212647, 5557, 2801, 262144⟩
    (by decide) selected_cut_07312

theorem selected_cut_07313 : selected 10 ⟨212671, by decide⟩
    (prefixPartial 11 5558) = some ⟨11, 2, 0, 212671, 5558, 2073, 262144⟩ := by
  decide +kernel

theorem context_11_5558_212671 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5558 ⟨212671, by decide⟩ :=
  accepted_of_selected 11 5558 ⟨212671, by decide⟩ ⟨11, 2, 0, 212671, 5558, 2073, 262144⟩
    (by decide) selected_cut_07313

theorem selected_cut_07314 : selected 10 ⟨212691, by decide⟩
    (prefixPartial 11 5559) = some ⟨11, 2, 0, 212691, 5559, 1805, 262144⟩ := by
  decide +kernel

theorem context_11_5559_212691 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5559 ⟨212691, by decide⟩ :=
  accepted_of_selected 11 5559 ⟨212691, by decide⟩ ⟨11, 2, 0, 212691, 5559, 1805, 262144⟩
    (by decide) selected_cut_07314

theorem unmarked_context_10_1389_212692 : frontier 11 ⟨212692, by decide⟩
    (prefixCache 10 1389) (prefixPartial 10 1389) = false := by
  decide +kernel

theorem node_context_10_1389_212692 : EJMOriginalGlobalDAGData.nodes 11 ⟨212692, by decide⟩ =
    .split (coordinate 10) (![⟨212612, by decide⟩,⟨212647, by decide⟩,⟨212671, by decide⟩,⟨212691, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1389_212692 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1389 ⟨212692, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1389
    ⟨212692, by decide⟩ (by decide) (![⟨212612, by decide⟩,⟨212647, by decide⟩,⟨212671, by decide⟩,⟨212691, by decide⟩]) unmarked_context_10_1389_212692 node_context_10_1389_212692
  intro a
  fin_cases a
  · exact context_11_5556_212612
  · exact context_11_5557_212647
  · exact context_11_5558_212671
  · exact context_11_5559_212691

theorem selected_cut_07315 : selected 10 ⟨212708, by decide⟩
    (prefixPartial 11 5560) = some ⟨11, 2, 0, 212708, 5560, 1493, 262144⟩ := by
  decide +kernel

theorem context_11_5560_212708 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5560 ⟨212708, by decide⟩ :=
  accepted_of_selected 11 5560 ⟨212708, by decide⟩ ⟨11, 2, 0, 212708, 5560, 1493, 262144⟩
    (by decide) selected_cut_07315

theorem selected_cut_07316 : selected 10 ⟨212722, by decide⟩
    (prefixPartial 11 5561) = some ⟨11, 2, 0, 212722, 5561, 1145, 262144⟩ := by
  decide +kernel

theorem context_11_5561_212722 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5561 ⟨212722, by decide⟩ :=
  accepted_of_selected 11 5561 ⟨212722, by decide⟩ ⟨11, 2, 0, 212722, 5561, 1145, 262144⟩
    (by decide) selected_cut_07316

theorem selected_cut_07317 : selected 10 ⟨212737, by decide⟩
    (prefixPartial 11 5562) = some ⟨11, 2, 0, 212737, 5562, 1045, 262144⟩ := by
  decide +kernel

theorem context_11_5562_212737 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5562 ⟨212737, by decide⟩ :=
  accepted_of_selected 11 5562 ⟨212737, by decide⟩ ⟨11, 2, 0, 212737, 5562, 1045, 262144⟩
    (by decide) selected_cut_07317

theorem selected_cut_07318 : selected 10 ⟨212752, by decide⟩
    (prefixPartial 11 5563) = some ⟨11, 2, 0, 212752, 5563, 817, 262144⟩ := by
  decide +kernel

theorem context_11_5563_212752 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5563 ⟨212752, by decide⟩ :=
  accepted_of_selected 11 5563 ⟨212752, by decide⟩ ⟨11, 2, 0, 212752, 5563, 817, 262144⟩
    (by decide) selected_cut_07318

theorem unmarked_context_10_1390_212753 : frontier 11 ⟨212753, by decide⟩
    (prefixCache 10 1390) (prefixPartial 10 1390) = false := by
  decide +kernel

theorem node_context_10_1390_212753 : EJMOriginalGlobalDAGData.nodes 11 ⟨212753, by decide⟩ =
    .split (coordinate 10) (![⟨212708, by decide⟩,⟨212722, by decide⟩,⟨212737, by decide⟩,⟨212752, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1390_212753 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1390 ⟨212753, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1390
    ⟨212753, by decide⟩ (by decide) (![⟨212708, by decide⟩,⟨212722, by decide⟩,⟨212737, by decide⟩,⟨212752, by decide⟩]) unmarked_context_10_1390_212753 node_context_10_1390_212753
  intro a
  fin_cases a
  · exact context_11_5560_212708
  · exact context_11_5561_212722
  · exact context_11_5562_212737
  · exact context_11_5563_212752

theorem selected_cut_07319 : selected 11 ⟨212788, by decide⟩
    (prefixPartial 10 1391) = some ⟨10, 2, 0, 212788, 1391, 1685, 1048576⟩ := by
  decide +kernel

theorem context_10_1391_212788 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1391 ⟨212788, by decide⟩ :=
  accepted_of_selected 10 1391 ⟨212788, by decide⟩ ⟨10, 2, 0, 212788, 1391, 1685, 1048576⟩
    (by decide) selected_cut_07319

theorem unmarked_context_9_347_212789 : frontier 12 ⟨212789, by decide⟩
    (prefixCache 9 347) (prefixPartial 9 347) = false := by
  decide +kernel

theorem node_context_9_347_212789 : EJMOriginalGlobalDAGData.nodes 12 ⟨212789, by decide⟩ =
    .split (coordinate 9) (![⟨212584, by decide⟩,⟨212692, by decide⟩,⟨212753, by decide⟩,⟨212788, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_347_212789 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 347 ⟨212789, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 347
    ⟨212789, by decide⟩ (by decide) (![⟨212584, by decide⟩,⟨212692, by decide⟩,⟨212753, by decide⟩,⟨212788, by decide⟩]) unmarked_context_9_347_212789 node_context_9_347_212789
  intro a
  fin_cases a
  · exact context_10_1388_212584
  · exact context_10_1389_212692
  · exact context_10_1390_212753
  · exact context_10_1391_212788

theorem unmarked_context_8_86_212790 : frontier 13 ⟨212790, by decide⟩
    (prefixCache 8 86) (prefixPartial 8 86) = false := by
  decide +kernel

theorem node_context_8_86_212790 : EJMOriginalGlobalDAGData.nodes 13 ⟨212790, by decide⟩ =
    .split (coordinate 8) (![⟨207398, by decide⟩,⟨210994, by decide⟩,⟨212398, by decide⟩,⟨212789, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_86_212790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 86 ⟨212790, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 86
    ⟨212790, by decide⟩ (by decide) (![⟨207398, by decide⟩,⟨210994, by decide⟩,⟨212398, by decide⟩,⟨212789, by decide⟩]) unmarked_context_8_86_212790 node_context_8_86_212790
  intro a
  fin_cases a
  · exact context_9_344_207398
  · exact context_9_345_210994
  · exact context_9_346_212398
  · exact context_9_347_212789

theorem selected_cut_07320 : selected 13 ⟨14298, by decide⟩
    (prefixPartial 8 87) = some ⟨8, 1, 0, 14298, 87, 1, 16777216⟩ := by
  decide +kernel

theorem context_8_87_14298 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 87 ⟨14298, by decide⟩ :=
  accepted_of_selected 8 87 ⟨14298, by decide⟩ ⟨8, 1, 0, 14298, 87, 1, 16777216⟩
    (by decide) selected_cut_07320

theorem unmarked_context_7_21_212791 : frontier 14 ⟨212791, by decide⟩
    (prefixCache 7 21) (prefixPartial 7 21) = false := by
  decide +kernel

theorem node_context_7_21_212791 : EJMOriginalGlobalDAGData.nodes 14 ⟨212791, by decide⟩ =
    .split (coordinate 7) (![⟨195565, by decide⟩,⟨201358, by decide⟩,⟨212790, by decide⟩,⟨14298, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_7_21_212791 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 21 ⟨212791, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 7 21
    ⟨212791, by decide⟩ (by decide) (![⟨195565, by decide⟩,⟨201358, by decide⟩,⟨212790, by decide⟩,⟨14298, by decide⟩]) unmarked_context_7_21_212791 node_context_7_21_212791
  intro a
  fin_cases a
  · exact context_8_84_195565
  · exact context_8_85_201358
  · exact context_8_86_212790
  · exact context_8_87_14298

theorem selected_cut_07321 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 22528) = some ⟨12, 1, 0, 34034, 22528, 1, 65536⟩ := by
  decide +kernel

theorem context_12_22528_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22528 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 22528 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 22528, 1, 65536⟩
    (by decide) selected_cut_07321

theorem selected_cut_07322 : selected 8 ⟨212850, by decide⟩
    (prefixPartial 13 90116) = some ⟨13, 2, 0, 212850, 90116, 3161, 16384⟩ := by
  decide +kernel

theorem context_13_90116_212850 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90116 ⟨212850, by decide⟩ :=
  accepted_of_selected 13 90116 ⟨212850, by decide⟩ ⟨13, 2, 0, 212850, 90116, 3161, 16384⟩
    (by decide) selected_cut_07322

theorem selected_cut_07323 : selected 8 ⟨212892, by decide⟩
    (prefixPartial 13 90117) = some ⟨13, 2, 0, 212892, 90117, 3009, 16384⟩ := by
  decide +kernel

theorem context_13_90117_212892 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90117 ⟨212892, by decide⟩ :=
  accepted_of_selected 13 90117 ⟨212892, by decide⟩ ⟨13, 2, 0, 212892, 90117, 3009, 16384⟩
    (by decide) selected_cut_07323

theorem selected_cut_07324 : selected 8 ⟨212922, by decide⟩
    (prefixPartial 13 90118) = some ⟨13, 2, 0, 212922, 90118, 2033, 16384⟩ := by
  decide +kernel

theorem context_13_90118_212922 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90118 ⟨212922, by decide⟩ :=
  accepted_of_selected 13 90118 ⟨212922, by decide⟩ ⟨13, 2, 0, 212922, 90118, 2033, 16384⟩
    (by decide) selected_cut_07324

theorem selected_cut_07325 : selected 8 ⟨212933, by decide⟩
    (prefixPartial 13 90119) = some ⟨13, 2, 0, 212933, 90119, 1081, 16384⟩ := by
  decide +kernel

theorem context_13_90119_212933 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90119 ⟨212933, by decide⟩ :=
  accepted_of_selected 13 90119 ⟨212933, by decide⟩ ⟨13, 2, 0, 212933, 90119, 1081, 16384⟩
    (by decide) selected_cut_07325

theorem unmarked_context_12_22529_212934 : frontier 9 ⟨212934, by decide⟩
    (prefixCache 12 22529) (prefixPartial 12 22529) = false := by
  decide +kernel

theorem node_context_12_22529_212934 : EJMOriginalGlobalDAGData.nodes 9 ⟨212934, by decide⟩ =
    .split (coordinate 12) (![⟨212850, by decide⟩,⟨212892, by decide⟩,⟨212922, by decide⟩,⟨212933, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22529_212934 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22529 ⟨212934, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22529
    ⟨212934, by decide⟩ (by decide) (![⟨212850, by decide⟩,⟨212892, by decide⟩,⟨212922, by decide⟩,⟨212933, by decide⟩]) unmarked_context_12_22529_212934 node_context_12_22529_212934
  intro a
  fin_cases a
  · exact context_13_90116_212850
  · exact context_13_90117_212892
  · exact context_13_90118_212922
  · exact context_13_90119_212933

theorem selected_cut_07326 : selected 8 ⟨213012, by decide⟩
    (prefixPartial 13 90120) = some ⟨13, 2, 0, 213012, 90120, 3257, 16384⟩ := by
  decide +kernel

theorem context_13_90120_213012 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90120 ⟨213012, by decide⟩ :=
  accepted_of_selected 13 90120 ⟨213012, by decide⟩ ⟨13, 2, 0, 213012, 90120, 3257, 16384⟩
    (by decide) selected_cut_07326

theorem selected_cut_07327 : selected 8 ⟨213090, by decide⟩
    (prefixPartial 13 90121) = some ⟨13, 2, 0, 213090, 90121, 2097, 16384⟩ := by
  decide +kernel

theorem context_13_90121_213090 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90121 ⟨213090, by decide⟩ :=
  accepted_of_selected 13 90121 ⟨213090, by decide⟩ ⟨13, 2, 0, 213090, 90121, 2097, 16384⟩
    (by decide) selected_cut_07327

theorem selected_cut_07328 : selected 8 ⟨213123, by decide⟩
    (prefixPartial 13 90122) = some ⟨13, 2, 0, 213123, 90122, 805, 16384⟩ := by
  decide +kernel

theorem context_13_90122_213123 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90122 ⟨213123, by decide⟩ :=
  accepted_of_selected 13 90122 ⟨213123, by decide⟩ ⟨13, 2, 0, 213123, 90122, 805, 16384⟩
    (by decide) selected_cut_07328

theorem selected_cut_07329 : selected 8 ⟨213128, by decide⟩
    (prefixPartial 13 90123) = some ⟨13, 2, 0, 213128, 90123, 113, 16384⟩ := by
  decide +kernel

theorem context_13_90123_213128 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90123 ⟨213128, by decide⟩ :=
  accepted_of_selected 13 90123 ⟨213128, by decide⟩ ⟨13, 2, 0, 213128, 90123, 113, 16384⟩
    (by decide) selected_cut_07329

theorem unmarked_context_12_22530_213129 : frontier 9 ⟨213129, by decide⟩
    (prefixCache 12 22530) (prefixPartial 12 22530) = false := by
  decide +kernel

theorem node_context_12_22530_213129 : EJMOriginalGlobalDAGData.nodes 9 ⟨213129, by decide⟩ =
    .split (coordinate 12) (![⟨213012, by decide⟩,⟨213090, by decide⟩,⟨213123, by decide⟩,⟨213128, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22530_213129 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22530 ⟨213129, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22530
    ⟨213129, by decide⟩ (by decide) (![⟨213012, by decide⟩,⟨213090, by decide⟩,⟨213123, by decide⟩,⟨213128, by decide⟩]) unmarked_context_12_22530_213129 node_context_12_22530_213129
  intro a
  fin_cases a
  · exact context_13_90120_213012
  · exact context_13_90121_213090
  · exact context_13_90122_213123
  · exact context_13_90123_213128

theorem selected_cut_07330 : selected 8 ⟨213198, by decide⟩
    (prefixPartial 13 90124) = some ⟨13, 2, 0, 213198, 90124, 4069, 16384⟩ := by
  decide +kernel

theorem context_13_90124_213198 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90124 ⟨213198, by decide⟩ :=
  accepted_of_selected 13 90124 ⟨213198, by decide⟩ ⟨13, 2, 0, 213198, 90124, 4069, 16384⟩
    (by decide) selected_cut_07330

theorem selected_cut_07331 : selected 8 ⟨213262, by decide⟩
    (prefixPartial 13 90125) = some ⟨13, 2, 0, 213262, 90125, 3885, 16384⟩ := by
  decide +kernel

theorem context_13_90125_213262 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90125 ⟨213262, by decide⟩ :=
  accepted_of_selected 13 90125 ⟨213262, by decide⟩ ⟨13, 2, 0, 213262, 90125, 3885, 16384⟩
    (by decide) selected_cut_07331

theorem selected_cut_07332 : selected 8 ⟨213285, by decide⟩
    (prefixPartial 13 90126) = some ⟨13, 2, 0, 213285, 90126, 2045, 16384⟩ := by
  decide +kernel

theorem context_13_90126_213285 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90126 ⟨213285, by decide⟩ :=
  accepted_of_selected 13 90126 ⟨213285, by decide⟩ ⟨13, 2, 0, 213285, 90126, 2045, 16384⟩
    (by decide) selected_cut_07332

theorem selected_cut_07333 : selected 8 ⟨213297, by decide⟩
    (prefixPartial 13 90127) = some ⟨13, 2, 0, 213297, 90127, 1005, 16384⟩ := by
  decide +kernel

theorem context_13_90127_213297 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90127 ⟨213297, by decide⟩ :=
  accepted_of_selected 13 90127 ⟨213297, by decide⟩ ⟨13, 2, 0, 213297, 90127, 1005, 16384⟩
    (by decide) selected_cut_07333

theorem unmarked_context_12_22531_213298 : frontier 9 ⟨213298, by decide⟩
    (prefixCache 12 22531) (prefixPartial 12 22531) = false := by
  decide +kernel

theorem node_context_12_22531_213298 : EJMOriginalGlobalDAGData.nodes 9 ⟨213298, by decide⟩ =
    .split (coordinate 12) (![⟨213198, by decide⟩,⟨213262, by decide⟩,⟨213285, by decide⟩,⟨213297, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22531_213298 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22531 ⟨213298, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22531
    ⟨213298, by decide⟩ (by decide) (![⟨213198, by decide⟩,⟨213262, by decide⟩,⟨213285, by decide⟩,⟨213297, by decide⟩]) unmarked_context_12_22531_213298 node_context_12_22531_213298
  intro a
  fin_cases a
  · exact context_13_90124_213198
  · exact context_13_90125_213262
  · exact context_13_90126_213285
  · exact context_13_90127_213297

theorem unmarked_context_11_5632_213299 : frontier 10 ⟨213299, by decide⟩
    (prefixCache 11 5632) (prefixPartial 11 5632) = false := by
  decide +kernel

theorem node_context_11_5632_213299 : EJMOriginalGlobalDAGData.nodes 10 ⟨213299, by decide⟩ =
    .split (coordinate 11) (![⟨34034, by decide⟩,⟨212934, by decide⟩,⟨213129, by decide⟩,⟨213298, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5632_213299 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5632 ⟨213299, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5632
    ⟨213299, by decide⟩ (by decide) (![⟨34034, by decide⟩,⟨212934, by decide⟩,⟨213129, by decide⟩,⟨213298, by decide⟩]) unmarked_context_11_5632_213299 node_context_11_5632_213299
  intro a
  fin_cases a
  · exact context_12_22528_34034
  · exact context_12_22529_212934
  · exact context_12_22530_213129
  · exact context_12_22531_213298

theorem selected_cut_07334 : selected 8 ⟨213349, by decide⟩
    (prefixPartial 13 90128) = some ⟨13, 2, 0, 213349, 90128, 2745, 16384⟩ := by
  decide +kernel

theorem context_13_90128_213349 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90128 ⟨213349, by decide⟩ :=
  accepted_of_selected 13 90128 ⟨213349, by decide⟩ ⟨13, 2, 0, 213349, 90128, 2745, 16384⟩
    (by decide) selected_cut_07334

theorem selected_cut_07335 : selected 7 ⟨213388, by decide⟩
    (prefixPartial 14 360516) = some ⟨14, 2, 0, 213388, 360516, 1257, 4096⟩ := by
  decide +kernel

theorem context_14_360516_213388 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 360516 ⟨213388, by decide⟩ :=
  accepted_of_selected 14 360516 ⟨213388, by decide⟩ ⟨14, 2, 0, 213388, 360516, 1257, 4096⟩
    (by decide) selected_cut_07335

theorem selected_cut_07336 : selected 7 ⟨213409, by decide⟩
    (prefixPartial 14 360517) = some ⟨14, 2, 0, 213409, 360517, 1165, 4096⟩ := by
  decide +kernel

theorem context_14_360517_213409 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 360517 ⟨213409, by decide⟩ :=
  accepted_of_selected 14 360517 ⟨213409, by decide⟩ ⟨14, 2, 0, 213409, 360517, 1165, 4096⟩
    (by decide) selected_cut_07336

theorem selected_cut_07337 : selected 7 ⟨213432, by decide⟩
    (prefixPartial 14 360518) = some ⟨14, 2, 0, 213432, 360518, 1145, 4096⟩ := by
  decide +kernel

theorem context_14_360518_213432 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 360518 ⟨213432, by decide⟩ :=
  accepted_of_selected 14 360518 ⟨213432, by decide⟩ ⟨14, 2, 0, 213432, 360518, 1145, 4096⟩
    (by decide) selected_cut_07337

theorem selected_cut_07338 : selected 7 ⟨213443, by decide⟩
    (prefixPartial 14 360519) = some ⟨14, 2, 0, 213443, 360519, 857, 4096⟩ := by
  decide +kernel

theorem context_14_360519_213443 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 360519 ⟨213443, by decide⟩ :=
  accepted_of_selected 14 360519 ⟨213443, by decide⟩ ⟨14, 2, 0, 213443, 360519, 857, 4096⟩
    (by decide) selected_cut_07338

theorem unmarked_context_13_90129_213444 : frontier 8 ⟨213444, by decide⟩
    (prefixCache 13 90129) (prefixPartial 13 90129) = false := by
  decide +kernel

theorem node_context_13_90129_213444 : EJMOriginalGlobalDAGData.nodes 8 ⟨213444, by decide⟩ =
    .split (coordinate 13) (![⟨213388, by decide⟩,⟨213409, by decide⟩,⟨213432, by decide⟩,⟨213443, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_90129_213444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90129 ⟨213444, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 90129
    ⟨213444, by decide⟩ (by decide) (![⟨213388, by decide⟩,⟨213409, by decide⟩,⟨213432, by decide⟩,⟨213443, by decide⟩]) unmarked_context_13_90129_213444 node_context_13_90129_213444
  intro a
  fin_cases a
  · exact context_14_360516_213388
  · exact context_14_360517_213409
  · exact context_14_360518_213432
  · exact context_14_360519_213443

theorem selected_cut_07339 : selected 8 ⟨213468, by decide⟩
    (prefixPartial 13 90130) = some ⟨13, 2, 0, 213468, 90130, 1857, 16384⟩ := by
  decide +kernel

theorem context_13_90130_213468 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90130 ⟨213468, by decide⟩ :=
  accepted_of_selected 13 90130 ⟨213468, by decide⟩ ⟨13, 2, 0, 213468, 90130, 1857, 16384⟩
    (by decide) selected_cut_07339

theorem selected_cut_07340 : selected 8 ⟨213486, by decide⟩
    (prefixPartial 13 90131) = some ⟨13, 2, 0, 213486, 90131, 1177, 16384⟩ := by
  decide +kernel

theorem context_13_90131_213486 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90131 ⟨213486, by decide⟩ :=
  accepted_of_selected 13 90131 ⟨213486, by decide⟩ ⟨13, 2, 0, 213486, 90131, 1177, 16384⟩
    (by decide) selected_cut_07340

theorem unmarked_context_12_22532_213487 : frontier 9 ⟨213487, by decide⟩
    (prefixCache 12 22532) (prefixPartial 12 22532) = false := by
  decide +kernel

theorem node_context_12_22532_213487 : EJMOriginalGlobalDAGData.nodes 9 ⟨213487, by decide⟩ =
    .split (coordinate 12) (![⟨213349, by decide⟩,⟨213444, by decide⟩,⟨213468, by decide⟩,⟨213486, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22532_213487 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22532 ⟨213487, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22532
    ⟨213487, by decide⟩ (by decide) (![⟨213349, by decide⟩,⟨213444, by decide⟩,⟨213468, by decide⟩,⟨213486, by decide⟩]) unmarked_context_12_22532_213487 node_context_12_22532_213487
  intro a
  fin_cases a
  · exact context_13_90128_213349
  · exact context_13_90129_213444
  · exact context_13_90130_213468
  · exact context_13_90131_213486

theorem selected_cut_07341 : selected 8 ⟨213538, by decide⟩
    (prefixPartial 13 90132) = some ⟨13, 2, 0, 213538, 90132, 3081, 16384⟩ := by
  decide +kernel

theorem context_13_90132_213538 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90132 ⟨213538, by decide⟩ :=
  accepted_of_selected 13 90132 ⟨213538, by decide⟩ ⟨13, 2, 0, 213538, 90132, 3081, 16384⟩
    (by decide) selected_cut_07341

theorem selected_cut_07342 : selected 8 ⟨213598, by decide⟩
    (prefixPartial 13 90133) = some ⟨13, 2, 0, 213598, 90133, 3345, 16384⟩ := by
  decide +kernel

theorem context_13_90133_213598 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90133 ⟨213598, by decide⟩ :=
  accepted_of_selected 13 90133 ⟨213598, by decide⟩ ⟨13, 2, 0, 213598, 90133, 3345, 16384⟩
    (by decide) selected_cut_07342

theorem selected_cut_07343 : selected 8 ⟨213623, by decide⟩
    (prefixPartial 13 90134) = some ⟨13, 2, 0, 213623, 90134, 1917, 16384⟩ := by
  decide +kernel

theorem context_13_90134_213623 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90134 ⟨213623, by decide⟩ :=
  accepted_of_selected 13 90134 ⟨213623, by decide⟩ ⟨13, 2, 0, 213623, 90134, 1917, 16384⟩
    (by decide) selected_cut_07343

theorem selected_cut_07344 : selected 8 ⟨213635, by decide⟩
    (prefixPartial 13 90135) = some ⟨13, 2, 0, 213635, 90135, 1149, 16384⟩ := by
  decide +kernel

theorem context_13_90135_213635 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90135 ⟨213635, by decide⟩ :=
  accepted_of_selected 13 90135 ⟨213635, by decide⟩ ⟨13, 2, 0, 213635, 90135, 1149, 16384⟩
    (by decide) selected_cut_07344

theorem unmarked_context_12_22533_213636 : frontier 9 ⟨213636, by decide⟩
    (prefixCache 12 22533) (prefixPartial 12 22533) = false := by
  decide +kernel

theorem node_context_12_22533_213636 : EJMOriginalGlobalDAGData.nodes 9 ⟨213636, by decide⟩ =
    .split (coordinate 12) (![⟨213538, by decide⟩,⟨213598, by decide⟩,⟨213623, by decide⟩,⟨213635, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22533_213636 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22533 ⟨213636, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22533
    ⟨213636, by decide⟩ (by decide) (![⟨213538, by decide⟩,⟨213598, by decide⟩,⟨213623, by decide⟩,⟨213635, by decide⟩]) unmarked_context_12_22533_213636 node_context_12_22533_213636
  intro a
  fin_cases a
  · exact context_13_90132_213538
  · exact context_13_90133_213598
  · exact context_13_90134_213623
  · exact context_13_90135_213635

theorem selected_cut_07345 : selected 8 ⟨213695, by decide⟩
    (prefixPartial 13 90136) = some ⟨13, 2, 0, 213695, 90136, 3837, 16384⟩ := by
  decide +kernel

theorem context_13_90136_213695 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90136 ⟨213695, by decide⟩ :=
  accepted_of_selected 13 90136 ⟨213695, by decide⟩ ⟨13, 2, 0, 213695, 90136, 3837, 16384⟩
    (by decide) selected_cut_07345

theorem selected_cut_07346 : selected 7 ⟨213722, by decide⟩
    (prefixPartial 14 360548) = some ⟨14, 2, 0, 213722, 360548, 1169, 4096⟩ := by
  decide +kernel

theorem context_14_360548_213722 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 360548 ⟨213722, by decide⟩ :=
  accepted_of_selected 14 360548 ⟨213722, by decide⟩ ⟨14, 2, 0, 213722, 360548, 1169, 4096⟩
    (by decide) selected_cut_07346

theorem selected_cut_07347 : selected 7 ⟨213742, by decide⟩
    (prefixPartial 14 360549) = some ⟨14, 2, 0, 213742, 360549, 1069, 4096⟩ := by
  decide +kernel

theorem context_14_360549_213742 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 360549 ⟨213742, by decide⟩ :=
  accepted_of_selected 14 360549 ⟨213742, by decide⟩ ⟨14, 2, 0, 213742, 360549, 1069, 4096⟩
    (by decide) selected_cut_07347

theorem selected_cut_07348 : selected 7 ⟨213761, by decide⟩
    (prefixPartial 14 360550) = some ⟨14, 2, 0, 213761, 360550, 1189, 4096⟩ := by
  decide +kernel

theorem context_14_360550_213761 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 360550 ⟨213761, by decide⟩ :=
  accepted_of_selected 14 360550 ⟨213761, by decide⟩ ⟨14, 2, 0, 213761, 360550, 1189, 4096⟩
    (by decide) selected_cut_07348

theorem selected_cut_07349 : selected 7 ⟨213772, by decide⟩
    (prefixPartial 14 360551) = some ⟨14, 2, 0, 213772, 360551, 897, 4096⟩ := by
  decide +kernel

theorem context_14_360551_213772 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 360551 ⟨213772, by decide⟩ :=
  accepted_of_selected 14 360551 ⟨213772, by decide⟩ ⟨14, 2, 0, 213772, 360551, 897, 4096⟩
    (by decide) selected_cut_07349

theorem unmarked_context_13_90137_213773 : frontier 8 ⟨213773, by decide⟩
    (prefixCache 13 90137) (prefixPartial 13 90137) = false := by
  decide +kernel

theorem node_context_13_90137_213773 : EJMOriginalGlobalDAGData.nodes 8 ⟨213773, by decide⟩ =
    .split (coordinate 13) (![⟨213722, by decide⟩,⟨213742, by decide⟩,⟨213761, by decide⟩,⟨213772, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_90137_213773 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90137 ⟨213773, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 90137
    ⟨213773, by decide⟩ (by decide) (![⟨213722, by decide⟩,⟨213742, by decide⟩,⟨213761, by decide⟩,⟨213772, by decide⟩]) unmarked_context_13_90137_213773 node_context_13_90137_213773
  intro a
  fin_cases a
  · exact context_14_360548_213722
  · exact context_14_360549_213742
  · exact context_14_360550_213761
  · exact context_14_360551_213772

theorem selected_cut_07350 : selected 8 ⟨213807, by decide⟩
    (prefixPartial 13 90138) = some ⟨13, 2, 0, 213807, 90138, 2265, 16384⟩ := by
  decide +kernel

theorem context_13_90138_213807 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90138 ⟨213807, by decide⟩ :=
  accepted_of_selected 13 90138 ⟨213807, by decide⟩ ⟨13, 2, 0, 213807, 90138, 2265, 16384⟩
    (by decide) selected_cut_07350

theorem selected_cut_07351 : selected 8 ⟨213817, by decide⟩
    (prefixPartial 13 90139) = some ⟨13, 2, 0, 213817, 90139, 1145, 16384⟩ := by
  decide +kernel

theorem context_13_90139_213817 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90139 ⟨213817, by decide⟩ :=
  accepted_of_selected 13 90139 ⟨213817, by decide⟩ ⟨13, 2, 0, 213817, 90139, 1145, 16384⟩
    (by decide) selected_cut_07351

theorem unmarked_context_12_22534_213818 : frontier 9 ⟨213818, by decide⟩
    (prefixCache 12 22534) (prefixPartial 12 22534) = false := by
  decide +kernel

theorem node_context_12_22534_213818 : EJMOriginalGlobalDAGData.nodes 9 ⟨213818, by decide⟩ =
    .split (coordinate 12) (![⟨213695, by decide⟩,⟨213773, by decide⟩,⟨213807, by decide⟩,⟨213817, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22534_213818 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22534 ⟨213818, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22534
    ⟨213818, by decide⟩ (by decide) (![⟨213695, by decide⟩,⟨213773, by decide⟩,⟨213807, by decide⟩,⟨213817, by decide⟩]) unmarked_context_12_22534_213818 node_context_12_22534_213818
  intro a
  fin_cases a
  · exact context_13_90136_213695
  · exact context_13_90137_213773
  · exact context_13_90138_213807
  · exact context_13_90139_213817

theorem selected_cut_07352 : selected 8 ⟨213877, by decide⟩
    (prefixPartial 13 90140) = some ⟨13, 2, 0, 213877, 90140, 4057, 16384⟩ := by
  decide +kernel

theorem context_13_90140_213877 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90140 ⟨213877, by decide⟩ :=
  accepted_of_selected 13 90140 ⟨213877, by decide⟩ ⟨13, 2, 0, 213877, 90140, 4057, 16384⟩
    (by decide) selected_cut_07352

theorem selected_cut_07353 : selected 7 ⟨213905, by decide⟩
    (prefixPartial 14 360564) = some ⟨14, 2, 0, 213905, 360564, 1205, 4096⟩ := by
  decide +kernel

theorem context_14_360564_213905 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 360564 ⟨213905, by decide⟩ :=
  accepted_of_selected 14 360564 ⟨213905, by decide⟩ ⟨14, 2, 0, 213905, 360564, 1205, 4096⟩
    (by decide) selected_cut_07353

theorem selected_cut_07354 : selected 7 ⟨213928, by decide⟩
    (prefixPartial 14 360565) = some ⟨14, 2, 0, 213928, 360565, 1117, 4096⟩ := by
  decide +kernel

theorem context_14_360565_213928 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 360565 ⟨213928, by decide⟩ :=
  accepted_of_selected 14 360565 ⟨213928, by decide⟩ ⟨14, 2, 0, 213928, 360565, 1117, 4096⟩
    (by decide) selected_cut_07354

theorem selected_cut_07355 : selected 7 ⟨213942, by decide⟩
    (prefixPartial 14 360566) = some ⟨14, 2, 0, 213942, 360566, 1121, 4096⟩ := by
  decide +kernel

theorem context_14_360566_213942 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 360566 ⟨213942, by decide⟩ :=
  accepted_of_selected 14 360566 ⟨213942, by decide⟩ ⟨14, 2, 0, 213942, 360566, 1121, 4096⟩
    (by decide) selected_cut_07355

theorem selected_cut_07356 : selected 7 ⟨213952, by decide⟩
    (prefixPartial 14 360567) = some ⟨14, 2, 0, 213952, 360567, 917, 4096⟩ := by
  decide +kernel

theorem context_14_360567_213952 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 360567 ⟨213952, by decide⟩ :=
  accepted_of_selected 14 360567 ⟨213952, by decide⟩ ⟨14, 2, 0, 213952, 360567, 917, 4096⟩
    (by decide) selected_cut_07356

theorem unmarked_context_13_90141_213953 : frontier 8 ⟨213953, by decide⟩
    (prefixCache 13 90141) (prefixPartial 13 90141) = false := by
  decide +kernel

theorem node_context_13_90141_213953 : EJMOriginalGlobalDAGData.nodes 8 ⟨213953, by decide⟩ =
    .split (coordinate 13) (![⟨213905, by decide⟩,⟨213928, by decide⟩,⟨213942, by decide⟩,⟨213952, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_90141_213953 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90141 ⟨213953, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 90141
    ⟨213953, by decide⟩ (by decide) (![⟨213905, by decide⟩,⟨213928, by decide⟩,⟨213942, by decide⟩,⟨213952, by decide⟩]) unmarked_context_13_90141_213953 node_context_13_90141_213953
  intro a
  fin_cases a
  · exact context_14_360564_213905
  · exact context_14_360565_213928
  · exact context_14_360566_213942
  · exact context_14_360567_213952

theorem selected_cut_07357 : selected 8 ⟨213977, by decide⟩
    (prefixPartial 13 90142) = some ⟨13, 2, 0, 213977, 90142, 2049, 16384⟩ := by
  decide +kernel

theorem context_13_90142_213977 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90142 ⟨213977, by decide⟩ :=
  accepted_of_selected 13 90142 ⟨213977, by decide⟩ ⟨13, 2, 0, 213977, 90142, 2049, 16384⟩
    (by decide) selected_cut_07357

theorem selected_cut_07358 : selected 8 ⟨213991, by decide⟩
    (prefixPartial 13 90143) = some ⟨13, 2, 0, 213991, 90143, 1177, 16384⟩ := by
  decide +kernel

theorem context_13_90143_213991 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90143 ⟨213991, by decide⟩ :=
  accepted_of_selected 13 90143 ⟨213991, by decide⟩ ⟨13, 2, 0, 213991, 90143, 1177, 16384⟩
    (by decide) selected_cut_07358

theorem unmarked_context_12_22535_213992 : frontier 9 ⟨213992, by decide⟩
    (prefixCache 12 22535) (prefixPartial 12 22535) = false := by
  decide +kernel

theorem node_context_12_22535_213992 : EJMOriginalGlobalDAGData.nodes 9 ⟨213992, by decide⟩ =
    .split (coordinate 12) (![⟨213877, by decide⟩,⟨213953, by decide⟩,⟨213977, by decide⟩,⟨213991, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22535_213992 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22535 ⟨213992, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22535
    ⟨213992, by decide⟩ (by decide) (![⟨213877, by decide⟩,⟨213953, by decide⟩,⟨213977, by decide⟩,⟨213991, by decide⟩]) unmarked_context_12_22535_213992 node_context_12_22535_213992
  intro a
  fin_cases a
  · exact context_13_90140_213877
  · exact context_13_90141_213953
  · exact context_13_90142_213977
  · exact context_13_90143_213991

theorem unmarked_context_11_5633_213993 : frontier 10 ⟨213993, by decide⟩
    (prefixCache 11 5633) (prefixPartial 11 5633) = false := by
  decide +kernel

theorem node_context_11_5633_213993 : EJMOriginalGlobalDAGData.nodes 10 ⟨213993, by decide⟩ =
    .split (coordinate 11) (![⟨213487, by decide⟩,⟨213636, by decide⟩,⟨213818, by decide⟩,⟨213992, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5633_213993 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5633 ⟨213993, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5633
    ⟨213993, by decide⟩ (by decide) (![⟨213487, by decide⟩,⟨213636, by decide⟩,⟨213818, by decide⟩,⟨213992, by decide⟩]) unmarked_context_11_5633_213993 node_context_11_5633_213993
  intro a
  fin_cases a
  · exact context_12_22532_213487
  · exact context_12_22533_213636
  · exact context_12_22534_213818
  · exact context_12_22535_213992

theorem selected_cut_07359 : selected 8 ⟨214034, by decide⟩
    (prefixPartial 13 90144) = some ⟨13, 2, 0, 214034, 90144, 2341, 16384⟩ := by
  decide +kernel

theorem context_13_90144_214034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90144 ⟨214034, by decide⟩ :=
  accepted_of_selected 13 90144 ⟨214034, by decide⟩ ⟨13, 2, 0, 214034, 90144, 2341, 16384⟩
    (by decide) selected_cut_07359

theorem selected_cut_07360 : selected 7 ⟨214057, by decide⟩
    (prefixPartial 14 360580) = some ⟨14, 2, 0, 214057, 360580, 1153, 4096⟩ := by
  decide +kernel

theorem context_14_360580_214057 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 360580 ⟨214057, by decide⟩ :=
  accepted_of_selected 14 360580 ⟨214057, by decide⟩ ⟨14, 2, 0, 214057, 360580, 1153, 4096⟩
    (by decide) selected_cut_07360

theorem selected_cut_07361 : selected 7 ⟨214072, by decide⟩
    (prefixPartial 14 360581) = some ⟨14, 2, 0, 214072, 360581, 953, 4096⟩ := by
  decide +kernel

theorem context_14_360581_214072 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 360581 ⟨214072, by decide⟩ :=
  accepted_of_selected 14 360581 ⟨214072, by decide⟩ ⟨14, 2, 0, 214072, 360581, 953, 4096⟩
    (by decide) selected_cut_07361

theorem selected_cut_07362 : selected 7 ⟨214089, by decide⟩
    (prefixPartial 14 360582) = some ⟨14, 2, 0, 214089, 360582, 1133, 4096⟩ := by
  decide +kernel

theorem context_14_360582_214089 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 360582 ⟨214089, by decide⟩ :=
  accepted_of_selected 14 360582 ⟨214089, by decide⟩ ⟨14, 2, 0, 214089, 360582, 1133, 4096⟩
    (by decide) selected_cut_07362

theorem selected_cut_07363 : selected 7 ⟨214100, by decide⟩
    (prefixPartial 14 360583) = some ⟨14, 2, 0, 214100, 360583, 893, 4096⟩ := by
  decide +kernel

theorem context_14_360583_214100 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 360583 ⟨214100, by decide⟩ :=
  accepted_of_selected 14 360583 ⟨214100, by decide⟩ ⟨14, 2, 0, 214100, 360583, 893, 4096⟩
    (by decide) selected_cut_07363

theorem unmarked_context_13_90145_214101 : frontier 8 ⟨214101, by decide⟩
    (prefixCache 13 90145) (prefixPartial 13 90145) = false := by
  decide +kernel

theorem node_context_13_90145_214101 : EJMOriginalGlobalDAGData.nodes 8 ⟨214101, by decide⟩ =
    .split (coordinate 13) (![⟨214057, by decide⟩,⟨214072, by decide⟩,⟨214089, by decide⟩,⟨214100, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_90145_214101 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90145 ⟨214101, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 90145
    ⟨214101, by decide⟩ (by decide) (![⟨214057, by decide⟩,⟨214072, by decide⟩,⟨214089, by decide⟩,⟨214100, by decide⟩]) unmarked_context_13_90145_214101 node_context_13_90145_214101
  intro a
  fin_cases a
  · exact context_14_360580_214057
  · exact context_14_360581_214072
  · exact context_14_360582_214089
  · exact context_14_360583_214100

theorem selected_cut_07364 : selected 8 ⟨214122, by decide⟩
    (prefixPartial 13 90146) = some ⟨13, 2, 0, 214122, 90146, 2153, 16384⟩ := by
  decide +kernel

theorem context_13_90146_214122 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90146 ⟨214122, by decide⟩ :=
  accepted_of_selected 13 90146 ⟨214122, by decide⟩ ⟨13, 2, 0, 214122, 90146, 2153, 16384⟩
    (by decide) selected_cut_07364

theorem selected_cut_07365 : selected 8 ⟨214130, by decide⟩
    (prefixPartial 13 90147) = some ⟨13, 2, 0, 214130, 90147, 1173, 16384⟩ := by
  decide +kernel

theorem context_13_90147_214130 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90147 ⟨214130, by decide⟩ :=
  accepted_of_selected 13 90147 ⟨214130, by decide⟩ ⟨13, 2, 0, 214130, 90147, 1173, 16384⟩
    (by decide) selected_cut_07365

theorem unmarked_context_12_22536_214131 : frontier 9 ⟨214131, by decide⟩
    (prefixCache 12 22536) (prefixPartial 12 22536) = false := by
  decide +kernel

theorem node_context_12_22536_214131 : EJMOriginalGlobalDAGData.nodes 9 ⟨214131, by decide⟩ =
    .split (coordinate 12) (![⟨214034, by decide⟩,⟨214101, by decide⟩,⟨214122, by decide⟩,⟨214130, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22536_214131 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22536 ⟨214131, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22536
    ⟨214131, by decide⟩ (by decide) (![⟨214034, by decide⟩,⟨214101, by decide⟩,⟨214122, by decide⟩,⟨214130, by decide⟩]) unmarked_context_12_22536_214131 node_context_12_22536_214131
  intro a
  fin_cases a
  · exact context_13_90144_214034
  · exact context_13_90145_214101
  · exact context_13_90146_214122
  · exact context_13_90147_214130

theorem selected_cut_07366 : selected 8 ⟨214183, by decide⟩
    (prefixPartial 13 90148) = some ⟨13, 2, 0, 214183, 90148, 2877, 16384⟩ := by
  decide +kernel

theorem context_13_90148_214183 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90148 ⟨214183, by decide⟩ :=
  accepted_of_selected 13 90148 ⟨214183, by decide⟩ ⟨13, 2, 0, 214183, 90148, 2877, 16384⟩
    (by decide) selected_cut_07366

theorem selected_cut_07367 : selected 8 ⟨214241, by decide⟩
    (prefixPartial 13 90149) = some ⟨13, 2, 0, 214241, 90149, 3617, 16384⟩ := by
  decide +kernel

theorem context_13_90149_214241 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90149 ⟨214241, by decide⟩ :=
  accepted_of_selected 13 90149 ⟨214241, by decide⟩ ⟨13, 2, 0, 214241, 90149, 3617, 16384⟩
    (by decide) selected_cut_07367

theorem selected_cut_07368 : selected 8 ⟨214265, by decide⟩
    (prefixPartial 13 90150) = some ⟨13, 2, 0, 214265, 90150, 2197, 16384⟩ := by
  decide +kernel

theorem context_13_90150_214265 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90150 ⟨214265, by decide⟩ :=
  accepted_of_selected 13 90150 ⟨214265, by decide⟩ ⟨13, 2, 0, 214265, 90150, 2197, 16384⟩
    (by decide) selected_cut_07368

theorem selected_cut_07369 : selected 8 ⟨214276, by decide⟩
    (prefixPartial 13 90151) = some ⟨13, 2, 0, 214276, 90151, 1141, 16384⟩ := by
  decide +kernel

theorem context_13_90151_214276 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90151 ⟨214276, by decide⟩ :=
  accepted_of_selected 13 90151 ⟨214276, by decide⟩ ⟨13, 2, 0, 214276, 90151, 1141, 16384⟩
    (by decide) selected_cut_07369

theorem unmarked_context_12_22537_214277 : frontier 9 ⟨214277, by decide⟩
    (prefixCache 12 22537) (prefixPartial 12 22537) = false := by
  decide +kernel

theorem node_context_12_22537_214277 : EJMOriginalGlobalDAGData.nodes 9 ⟨214277, by decide⟩ =
    .split (coordinate 12) (![⟨214183, by decide⟩,⟨214241, by decide⟩,⟨214265, by decide⟩,⟨214276, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22537_214277 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22537 ⟨214277, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22537
    ⟨214277, by decide⟩ (by decide) (![⟨214183, by decide⟩,⟨214241, by decide⟩,⟨214265, by decide⟩,⟨214276, by decide⟩]) unmarked_context_12_22537_214277 node_context_12_22537_214277
  intro a
  fin_cases a
  · exact context_13_90148_214183
  · exact context_13_90149_214241
  · exact context_13_90150_214265
  · exact context_13_90151_214276

theorem selected_cut_07370 : selected 8 ⟨214334, by decide⟩
    (prefixPartial 13 90152) = some ⟨13, 2, 0, 214334, 90152, 3281, 16384⟩ := by
  decide +kernel

theorem context_13_90152_214334 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90152 ⟨214334, by decide⟩ :=
  accepted_of_selected 13 90152 ⟨214334, by decide⟩ ⟨13, 2, 0, 214334, 90152, 3281, 16384⟩
    (by decide) selected_cut_07370

theorem selected_cut_07371 : selected 7 ⟨214353, by decide⟩
    (prefixPartial 14 360612) = some ⟨14, 2, 0, 214353, 360612, 1049, 4096⟩ := by
  decide +kernel

theorem context_14_360612_214353 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 360612 ⟨214353, by decide⟩ :=
  accepted_of_selected 14 360612 ⟨214353, by decide⟩ ⟨14, 2, 0, 214353, 360612, 1049, 4096⟩
    (by decide) selected_cut_07371

theorem selected_cut_07372 : selected 7 ⟨214374, by decide⟩
    (prefixPartial 14 360613) = some ⟨14, 2, 0, 214374, 360613, 1077, 4096⟩ := by
  decide +kernel

theorem context_14_360613_214374 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 360613 ⟨214374, by decide⟩ :=
  accepted_of_selected 14 360613 ⟨214374, by decide⟩ ⟨14, 2, 0, 214374, 360613, 1077, 4096⟩
    (by decide) selected_cut_07372

theorem selected_cut_07373 : selected 7 ⟨214390, by decide⟩
    (prefixPartial 14 360614) = some ⟨14, 2, 0, 214390, 360614, 1185, 4096⟩ := by
  decide +kernel

theorem context_14_360614_214390 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 360614 ⟨214390, by decide⟩ :=
  accepted_of_selected 14 360614 ⟨214390, by decide⟩ ⟨14, 2, 0, 214390, 360614, 1185, 4096⟩
    (by decide) selected_cut_07373

theorem selected_cut_07374 : selected 7 ⟨214406, by decide⟩
    (prefixPartial 14 360615) = some ⟨14, 2, 0, 214406, 360615, 1065, 4096⟩ := by
  decide +kernel

theorem context_14_360615_214406 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 360615 ⟨214406, by decide⟩ :=
  accepted_of_selected 14 360615 ⟨214406, by decide⟩ ⟨14, 2, 0, 214406, 360615, 1065, 4096⟩
    (by decide) selected_cut_07374

theorem unmarked_context_13_90153_214407 : frontier 8 ⟨214407, by decide⟩
    (prefixCache 13 90153) (prefixPartial 13 90153) = false := by
  decide +kernel

theorem node_context_13_90153_214407 : EJMOriginalGlobalDAGData.nodes 8 ⟨214407, by decide⟩ =
    .split (coordinate 13) (![⟨214353, by decide⟩,⟨214374, by decide⟩,⟨214390, by decide⟩,⟨214406, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_90153_214407 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90153 ⟨214407, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 90153
    ⟨214407, by decide⟩ (by decide) (![⟨214353, by decide⟩,⟨214374, by decide⟩,⟨214390, by decide⟩,⟨214406, by decide⟩]) unmarked_context_13_90153_214407 node_context_13_90153_214407
  intro a
  fin_cases a
  · exact context_14_360612_214353
  · exact context_14_360613_214374
  · exact context_14_360614_214390
  · exact context_14_360615_214406

theorem selected_cut_07375 : selected 8 ⟨214435, by decide⟩
    (prefixPartial 13 90154) = some ⟨13, 2, 0, 214435, 90154, 2357, 16384⟩ := by
  decide +kernel

theorem context_13_90154_214435 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90154 ⟨214435, by decide⟩ :=
  accepted_of_selected 13 90154 ⟨214435, by decide⟩ ⟨13, 2, 0, 214435, 90154, 2357, 16384⟩
    (by decide) selected_cut_07375

theorem selected_cut_07376 : selected 8 ⟨214444, by decide⟩
    (prefixPartial 13 90155) = some ⟨13, 2, 0, 214444, 90155, 1141, 16384⟩ := by
  decide +kernel

theorem context_13_90155_214444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90155 ⟨214444, by decide⟩ :=
  accepted_of_selected 13 90155 ⟨214444, by decide⟩ ⟨13, 2, 0, 214444, 90155, 1141, 16384⟩
    (by decide) selected_cut_07376

theorem unmarked_context_12_22538_214445 : frontier 9 ⟨214445, by decide⟩
    (prefixCache 12 22538) (prefixPartial 12 22538) = false := by
  decide +kernel

theorem node_context_12_22538_214445 : EJMOriginalGlobalDAGData.nodes 9 ⟨214445, by decide⟩ =
    .split (coordinate 12) (![⟨214334, by decide⟩,⟨214407, by decide⟩,⟨214435, by decide⟩,⟨214444, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22538_214445 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22538 ⟨214445, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22538
    ⟨214445, by decide⟩ (by decide) (![⟨214334, by decide⟩,⟨214407, by decide⟩,⟨214435, by decide⟩,⟨214444, by decide⟩]) unmarked_context_12_22538_214445 node_context_12_22538_214445
  intro a
  fin_cases a
  · exact context_13_90152_214334
  · exact context_13_90153_214407
  · exact context_13_90154_214435
  · exact context_13_90155_214444

theorem selected_cut_07377 : selected 8 ⟨214501, by decide⟩
    (prefixPartial 13 90156) = some ⟨13, 2, 0, 214501, 90156, 3673, 16384⟩ := by
  decide +kernel

theorem context_13_90156_214501 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90156 ⟨214501, by decide⟩ :=
  accepted_of_selected 13 90156 ⟨214501, by decide⟩ ⟨13, 2, 0, 214501, 90156, 3673, 16384⟩
    (by decide) selected_cut_07377

theorem selected_cut_07378 : selected 7 ⟨214527, by decide⟩
    (prefixPartial 14 360628) = some ⟨14, 2, 0, 214527, 360628, 1249, 4096⟩ := by
  decide +kernel

theorem context_14_360628_214527 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 360628 ⟨214527, by decide⟩ :=
  accepted_of_selected 14 360628 ⟨214527, by decide⟩ ⟨14, 2, 0, 214527, 360628, 1249, 4096⟩
    (by decide) selected_cut_07378

theorem selected_cut_07379 : selected 7 ⟨214552, by decide⟩
    (prefixPartial 14 360629) = some ⟨14, 2, 0, 214552, 360629, 1161, 4096⟩ := by
  decide +kernel

theorem context_14_360629_214552 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 360629 ⟨214552, by decide⟩ :=
  accepted_of_selected 14 360629 ⟨214552, by decide⟩ ⟨14, 2, 0, 214552, 360629, 1161, 4096⟩
    (by decide) selected_cut_07379

theorem selected_cut_07380 : selected 7 ⟨214570, by decide⟩
    (prefixPartial 14 360630) = some ⟨14, 2, 0, 214570, 360630, 1181, 4096⟩ := by
  decide +kernel

theorem context_14_360630_214570 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 360630 ⟨214570, by decide⟩ :=
  accepted_of_selected 14 360630 ⟨214570, by decide⟩ ⟨14, 2, 0, 214570, 360630, 1181, 4096⟩
    (by decide) selected_cut_07380

theorem selected_cut_07381 : selected 7 ⟨214584, by decide⟩
    (prefixPartial 14 360631) = some ⟨14, 2, 0, 214584, 360631, 1009, 4096⟩ := by
  decide +kernel

theorem context_14_360631_214584 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 360631 ⟨214584, by decide⟩ :=
  accepted_of_selected 14 360631 ⟨214584, by decide⟩ ⟨14, 2, 0, 214584, 360631, 1009, 4096⟩
    (by decide) selected_cut_07381

theorem unmarked_context_13_90157_214585 : frontier 8 ⟨214585, by decide⟩
    (prefixCache 13 90157) (prefixPartial 13 90157) = false := by
  decide +kernel

theorem node_context_13_90157_214585 : EJMOriginalGlobalDAGData.nodes 8 ⟨214585, by decide⟩ =
    .split (coordinate 13) (![⟨214527, by decide⟩,⟨214552, by decide⟩,⟨214570, by decide⟩,⟨214584, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_90157_214585 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90157 ⟨214585, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 90157
    ⟨214585, by decide⟩ (by decide) (![⟨214527, by decide⟩,⟨214552, by decide⟩,⟨214570, by decide⟩,⟨214584, by decide⟩]) unmarked_context_13_90157_214585 node_context_13_90157_214585
  intro a
  fin_cases a
  · exact context_14_360628_214527
  · exact context_14_360629_214552
  · exact context_14_360630_214570
  · exact context_14_360631_214584

theorem selected_cut_07382 : selected 8 ⟨214610, by decide⟩
    (prefixPartial 13 90158) = some ⟨13, 2, 0, 214610, 90158, 2345, 16384⟩ := by
  decide +kernel

theorem context_13_90158_214610 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90158 ⟨214610, by decide⟩ :=
  accepted_of_selected 13 90158 ⟨214610, by decide⟩ ⟨13, 2, 0, 214610, 90158, 2345, 16384⟩
    (by decide) selected_cut_07382

theorem selected_cut_07383 : selected 8 ⟨214619, by decide⟩
    (prefixPartial 13 90159) = some ⟨13, 2, 0, 214619, 90159, 1197, 16384⟩ := by
  decide +kernel

theorem context_13_90159_214619 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90159 ⟨214619, by decide⟩ :=
  accepted_of_selected 13 90159 ⟨214619, by decide⟩ ⟨13, 2, 0, 214619, 90159, 1197, 16384⟩
    (by decide) selected_cut_07383

theorem unmarked_context_12_22539_214620 : frontier 9 ⟨214620, by decide⟩
    (prefixCache 12 22539) (prefixPartial 12 22539) = false := by
  decide +kernel

theorem node_context_12_22539_214620 : EJMOriginalGlobalDAGData.nodes 9 ⟨214620, by decide⟩ =
    .split (coordinate 12) (![⟨214501, by decide⟩,⟨214585, by decide⟩,⟨214610, by decide⟩,⟨214619, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22539_214620 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22539 ⟨214620, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22539
    ⟨214620, by decide⟩ (by decide) (![⟨214501, by decide⟩,⟨214585, by decide⟩,⟨214610, by decide⟩,⟨214619, by decide⟩]) unmarked_context_12_22539_214620 node_context_12_22539_214620
  intro a
  fin_cases a
  · exact context_13_90156_214501
  · exact context_13_90157_214585
  · exact context_13_90158_214610
  · exact context_13_90159_214619

theorem unmarked_context_11_5634_214621 : frontier 10 ⟨214621, by decide⟩
    (prefixCache 11 5634) (prefixPartial 11 5634) = false := by
  decide +kernel

theorem node_context_11_5634_214621 : EJMOriginalGlobalDAGData.nodes 10 ⟨214621, by decide⟩ =
    .split (coordinate 11) (![⟨214131, by decide⟩,⟨214277, by decide⟩,⟨214445, by decide⟩,⟨214620, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5634_214621 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5634 ⟨214621, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5634
    ⟨214621, by decide⟩ (by decide) (![⟨214131, by decide⟩,⟨214277, by decide⟩,⟨214445, by decide⟩,⟨214620, by decide⟩]) unmarked_context_11_5634_214621 node_context_11_5634_214621
  intro a
  fin_cases a
  · exact context_12_22536_214131
  · exact context_12_22537_214277
  · exact context_12_22538_214445
  · exact context_12_22539_214620

theorem selected_cut_07384 : selected 8 ⟨214665, by decide⟩
    (prefixPartial 13 90160) = some ⟨13, 2, 0, 214665, 90160, 2217, 16384⟩ := by
  decide +kernel

theorem context_13_90160_214665 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90160 ⟨214665, by decide⟩ :=
  accepted_of_selected 13 90160 ⟨214665, by decide⟩ ⟨13, 2, 0, 214665, 90160, 2217, 16384⟩
    (by decide) selected_cut_07384

theorem selected_cut_07385 : selected 7 ⟨214686, by decide⟩
    (prefixPartial 14 360644) = some ⟨14, 2, 0, 214686, 360644, 1137, 4096⟩ := by
  decide +kernel

theorem context_14_360644_214686 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 360644 ⟨214686, by decide⟩ :=
  accepted_of_selected 14 360644 ⟨214686, by decide⟩ ⟨14, 2, 0, 214686, 360644, 1137, 4096⟩
    (by decide) selected_cut_07385

theorem selected_cut_07386 : selected 7 ⟨214703, by decide⟩
    (prefixPartial 14 360645) = some ⟨14, 2, 0, 214703, 360645, 949, 4096⟩ := by
  decide +kernel

theorem context_14_360645_214703 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 360645 ⟨214703, by decide⟩ :=
  accepted_of_selected 14 360645 ⟨214703, by decide⟩ ⟨14, 2, 0, 214703, 360645, 949, 4096⟩
    (by decide) selected_cut_07386

theorem selected_cut_07387 : selected 7 ⟨214722, by decide⟩
    (prefixPartial 14 360646) = some ⟨14, 2, 0, 214722, 360646, 1157, 4096⟩ := by
  decide +kernel

theorem context_14_360646_214722 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 360646 ⟨214722, by decide⟩ :=
  accepted_of_selected 14 360646 ⟨214722, by decide⟩ ⟨14, 2, 0, 214722, 360646, 1157, 4096⟩
    (by decide) selected_cut_07387

theorem selected_cut_07388 : selected 7 ⟨214732, by decide⟩
    (prefixPartial 14 360647) = some ⟨14, 2, 0, 214732, 360647, 901, 4096⟩ := by
  decide +kernel

theorem context_14_360647_214732 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 360647 ⟨214732, by decide⟩ :=
  accepted_of_selected 14 360647 ⟨214732, by decide⟩ ⟨14, 2, 0, 214732, 360647, 901, 4096⟩
    (by decide) selected_cut_07388

theorem unmarked_context_13_90161_214733 : frontier 8 ⟨214733, by decide⟩
    (prefixCache 13 90161) (prefixPartial 13 90161) = false := by
  decide +kernel

theorem node_context_13_90161_214733 : EJMOriginalGlobalDAGData.nodes 8 ⟨214733, by decide⟩ =
    .split (coordinate 13) (![⟨214686, by decide⟩,⟨214703, by decide⟩,⟨214722, by decide⟩,⟨214732, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_90161_214733 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90161 ⟨214733, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 90161
    ⟨214733, by decide⟩ (by decide) (![⟨214686, by decide⟩,⟨214703, by decide⟩,⟨214722, by decide⟩,⟨214732, by decide⟩]) unmarked_context_13_90161_214733 node_context_13_90161_214733
  intro a
  fin_cases a
  · exact context_14_360644_214686
  · exact context_14_360645_214703
  · exact context_14_360646_214722
  · exact context_14_360647_214732

theorem selected_cut_07389 : selected 8 ⟨214752, by decide⟩
    (prefixPartial 13 90162) = some ⟨13, 2, 0, 214752, 90162, 1933, 16384⟩ := by
  decide +kernel

theorem context_13_90162_214752 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90162 ⟨214752, by decide⟩ :=
  accepted_of_selected 13 90162 ⟨214752, by decide⟩ ⟨13, 2, 0, 214752, 90162, 1933, 16384⟩
    (by decide) selected_cut_07389

theorem selected_cut_07390 : selected 8 ⟨214762, by decide⟩
    (prefixPartial 13 90163) = some ⟨13, 2, 0, 214762, 90163, 1117, 16384⟩ := by
  decide +kernel

theorem context_13_90163_214762 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90163 ⟨214762, by decide⟩ :=
  accepted_of_selected 13 90163 ⟨214762, by decide⟩ ⟨13, 2, 0, 214762, 90163, 1117, 16384⟩
    (by decide) selected_cut_07390

theorem unmarked_context_12_22540_214763 : frontier 9 ⟨214763, by decide⟩
    (prefixCache 12 22540) (prefixPartial 12 22540) = false := by
  decide +kernel

theorem node_context_12_22540_214763 : EJMOriginalGlobalDAGData.nodes 9 ⟨214763, by decide⟩ =
    .split (coordinate 12) (![⟨214665, by decide⟩,⟨214733, by decide⟩,⟨214752, by decide⟩,⟨214762, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22540_214763 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22540 ⟨214763, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22540
    ⟨214763, by decide⟩ (by decide) (![⟨214665, by decide⟩,⟨214733, by decide⟩,⟨214752, by decide⟩,⟨214762, by decide⟩]) unmarked_context_12_22540_214763 node_context_12_22540_214763
  intro a
  fin_cases a
  · exact context_13_90160_214665
  · exact context_13_90161_214733
  · exact context_13_90162_214752
  · exact context_13_90163_214762

theorem selected_cut_07391 : selected 8 ⟨214806, by decide⟩
    (prefixPartial 13 90164) = some ⟨13, 2, 0, 214806, 90164, 2729, 16384⟩ := by
  decide +kernel

theorem context_13_90164_214806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90164 ⟨214806, by decide⟩ :=
  accepted_of_selected 13 90164 ⟨214806, by decide⟩ ⟨13, 2, 0, 214806, 90164, 2729, 16384⟩
    (by decide) selected_cut_07391

theorem selected_cut_07392 : selected 8 ⟨214859, by decide⟩
    (prefixPartial 13 90165) = some ⟨13, 2, 0, 214859, 90165, 3657, 16384⟩ := by
  decide +kernel

theorem context_13_90165_214859 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90165 ⟨214859, by decide⟩ :=
  accepted_of_selected 13 90165 ⟨214859, by decide⟩ ⟨13, 2, 0, 214859, 90165, 3657, 16384⟩
    (by decide) selected_cut_07392

theorem selected_cut_07393 : selected 8 ⟨214882, by decide⟩
    (prefixPartial 13 90166) = some ⟨13, 2, 0, 214882, 90166, 2101, 16384⟩ := by
  decide +kernel

theorem context_13_90166_214882 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90166 ⟨214882, by decide⟩ :=
  accepted_of_selected 13 90166 ⟨214882, by decide⟩ ⟨13, 2, 0, 214882, 90166, 2101, 16384⟩
    (by decide) selected_cut_07393

theorem selected_cut_07394 : selected 8 ⟨214893, by decide⟩
    (prefixPartial 13 90167) = some ⟨13, 2, 0, 214893, 90167, 1077, 16384⟩ := by
  decide +kernel

theorem context_13_90167_214893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90167 ⟨214893, by decide⟩ :=
  accepted_of_selected 13 90167 ⟨214893, by decide⟩ ⟨13, 2, 0, 214893, 90167, 1077, 16384⟩
    (by decide) selected_cut_07394

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
