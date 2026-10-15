/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover128
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_12387 : selected 8 ⟨327871, by decide⟩
    (prefixPartial 13 104598) = some ⟨13, 2, 0, 327871, 104598, 1269, 16384⟩ := by
  decide +kernel

theorem context_13_104598_327871 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104598 ⟨327871, by decide⟩ :=
  accepted_of_selected 13 104598 ⟨327871, by decide⟩ ⟨13, 2, 0, 327871, 104598, 1269, 16384⟩
    (by decide) selected_cut_12387

theorem selected_cut_12388 : selected 8 ⟨327878, by decide⟩
    (prefixPartial 13 104599) = some ⟨13, 2, 0, 327878, 104599, 745, 16384⟩ := by
  decide +kernel

theorem context_13_104599_327878 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104599 ⟨327878, by decide⟩ :=
  accepted_of_selected 13 104599 ⟨327878, by decide⟩ ⟨13, 2, 0, 327878, 104599, 745, 16384⟩
    (by decide) selected_cut_12388

theorem unmarked_context_12_26149_327879 : frontier 9 ⟨327879, by decide⟩
    (prefixCache 12 26149) (prefixPartial 12 26149) = false := by
  decide +kernel

theorem node_context_12_26149_327879 : EJMOriginalGlobalDAGData.nodes 9 ⟨327879, by decide⟩ =
    .split (coordinate 12) (![⟨327832, by decide⟩,⟨327857, by decide⟩,⟨327871, by decide⟩,⟨327878, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26149_327879 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26149 ⟨327879, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26149
    ⟨327879, by decide⟩ (by decide) (![⟨327832, by decide⟩,⟨327857, by decide⟩,⟨327871, by decide⟩,⟨327878, by decide⟩]) unmarked_context_12_26149_327879 node_context_12_26149_327879
  intro a
  fin_cases a
  · exact context_13_104596_327832
  · exact context_13_104597_327857
  · exact context_13_104598_327871
  · exact context_13_104599_327878

theorem selected_cut_12389 : selected 8 ⟨327891, by decide⟩
    (prefixPartial 13 104600) = some ⟨13, 2, 0, 327891, 104600, 837, 16384⟩ := by
  decide +kernel

theorem context_13_104600_327891 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104600 ⟨327891, by decide⟩ :=
  accepted_of_selected 13 104600 ⟨327891, by decide⟩ ⟨13, 2, 0, 327891, 104600, 837, 16384⟩
    (by decide) selected_cut_12389

theorem selected_cut_12390 : selected 8 ⟨327915, by decide⟩
    (prefixPartial 13 104601) = some ⟨13, 2, 0, 327915, 104601, 1681, 16384⟩ := by
  decide +kernel

theorem context_13_104601_327915 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104601 ⟨327915, by decide⟩ :=
  accepted_of_selected 13 104601 ⟨327915, by decide⟩ ⟨13, 2, 0, 327915, 104601, 1681, 16384⟩
    (by decide) selected_cut_12390

theorem selected_cut_12391 : selected 8 ⟨327925, by decide⟩
    (prefixPartial 13 104602) = some ⟨13, 2, 0, 327925, 104602, 913, 16384⟩ := by
  decide +kernel

theorem context_13_104602_327925 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104602 ⟨327925, by decide⟩ :=
  accepted_of_selected 13 104602 ⟨327925, by decide⟩ ⟨13, 2, 0, 327925, 104602, 913, 16384⟩
    (by decide) selected_cut_12391

theorem selected_cut_12392 : selected 8 ⟨327929, by decide⟩
    (prefixPartial 13 104603) = some ⟨13, 2, 0, 327929, 104603, 733, 16384⟩ := by
  decide +kernel

theorem context_13_104603_327929 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104603 ⟨327929, by decide⟩ :=
  accepted_of_selected 13 104603 ⟨327929, by decide⟩ ⟨13, 2, 0, 327929, 104603, 733, 16384⟩
    (by decide) selected_cut_12392

theorem unmarked_context_12_26150_327930 : frontier 9 ⟨327930, by decide⟩
    (prefixCache 12 26150) (prefixPartial 12 26150) = false := by
  decide +kernel

theorem node_context_12_26150_327930 : EJMOriginalGlobalDAGData.nodes 9 ⟨327930, by decide⟩ =
    .split (coordinate 12) (![⟨327891, by decide⟩,⟨327915, by decide⟩,⟨327925, by decide⟩,⟨327929, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26150_327930 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26150 ⟨327930, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26150
    ⟨327930, by decide⟩ (by decide) (![⟨327891, by decide⟩,⟨327915, by decide⟩,⟨327925, by decide⟩,⟨327929, by decide⟩]) unmarked_context_12_26150_327930 node_context_12_26150_327930
  intro a
  fin_cases a
  · exact context_13_104600_327891
  · exact context_13_104601_327915
  · exact context_13_104602_327925
  · exact context_13_104603_327929

theorem selected_cut_12393 : selected 8 ⟨327941, by decide⟩
    (prefixPartial 13 104604) = some ⟨13, 2, 0, 327941, 104604, 949, 16384⟩ := by
  decide +kernel

theorem context_13_104604_327941 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104604 ⟨327941, by decide⟩ :=
  accepted_of_selected 13 104604 ⟨327941, by decide⟩ ⟨13, 2, 0, 327941, 104604, 949, 16384⟩
    (by decide) selected_cut_12393

theorem selected_cut_12394 : selected 8 ⟨327969, by decide⟩
    (prefixPartial 13 104605) = some ⟨13, 2, 0, 327969, 104605, 2361, 16384⟩ := by
  decide +kernel

theorem context_13_104605_327969 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104605 ⟨327969, by decide⟩ :=
  accepted_of_selected 13 104605 ⟨327969, by decide⟩ ⟨13, 2, 0, 327969, 104605, 2361, 16384⟩
    (by decide) selected_cut_12394

theorem selected_cut_12395 : selected 8 ⟨327985, by decide⟩
    (prefixPartial 13 104606) = some ⟨13, 2, 0, 327985, 104606, 1353, 16384⟩ := by
  decide +kernel

theorem context_13_104606_327985 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104606 ⟨327985, by decide⟩ :=
  accepted_of_selected 13 104606 ⟨327985, by decide⟩ ⟨13, 2, 0, 327985, 104606, 1353, 16384⟩
    (by decide) selected_cut_12395

theorem selected_cut_12396 : selected 8 ⟨327992, by decide⟩
    (prefixPartial 13 104607) = some ⟨13, 2, 0, 327992, 104607, 829, 16384⟩ := by
  decide +kernel

theorem context_13_104607_327992 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104607 ⟨327992, by decide⟩ :=
  accepted_of_selected 13 104607 ⟨327992, by decide⟩ ⟨13, 2, 0, 327992, 104607, 829, 16384⟩
    (by decide) selected_cut_12396

theorem unmarked_context_12_26151_327993 : frontier 9 ⟨327993, by decide⟩
    (prefixCache 12 26151) (prefixPartial 12 26151) = false := by
  decide +kernel

theorem node_context_12_26151_327993 : EJMOriginalGlobalDAGData.nodes 9 ⟨327993, by decide⟩ =
    .split (coordinate 12) (![⟨327941, by decide⟩,⟨327969, by decide⟩,⟨327985, by decide⟩,⟨327992, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26151_327993 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26151 ⟨327993, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26151
    ⟨327993, by decide⟩ (by decide) (![⟨327941, by decide⟩,⟨327969, by decide⟩,⟨327985, by decide⟩,⟨327992, by decide⟩]) unmarked_context_12_26151_327993 node_context_12_26151_327993
  intro a
  fin_cases a
  · exact context_13_104604_327941
  · exact context_13_104605_327969
  · exact context_13_104606_327985
  · exact context_13_104607_327992

theorem unmarked_context_11_6537_327994 : frontier 10 ⟨327994, by decide⟩
    (prefixCache 11 6537) (prefixPartial 11 6537) = false := by
  decide +kernel

theorem node_context_11_6537_327994 : EJMOriginalGlobalDAGData.nodes 10 ⟨327994, by decide⟩ =
    .split (coordinate 11) (![⟨327822, by decide⟩,⟨327879, by decide⟩,⟨327930, by decide⟩,⟨327993, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6537_327994 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6537 ⟨327994, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6537
    ⟨327994, by decide⟩ (by decide) (![⟨327822, by decide⟩,⟨327879, by decide⟩,⟨327930, by decide⟩,⟨327993, by decide⟩]) unmarked_context_11_6537_327994 node_context_11_6537_327994
  intro a
  fin_cases a
  · exact context_12_26148_327822
  · exact context_12_26149_327879
  · exact context_12_26150_327930
  · exact context_12_26151_327993

theorem selected_cut_12397 : selected 9 ⟨328048, by decide⟩
    (prefixPartial 12 26152) = some ⟨12, 2, 0, 328048, 26152, 3881, 65536⟩ := by
  decide +kernel

theorem context_12_26152_328048 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26152 ⟨328048, by decide⟩ :=
  accepted_of_selected 12 26152 ⟨328048, by decide⟩ ⟨12, 2, 0, 328048, 26152, 3881, 65536⟩
    (by decide) selected_cut_12397

theorem selected_cut_12398 : selected 8 ⟨328057, by decide⟩
    (prefixPartial 13 104612) = some ⟨13, 2, 0, 328057, 104612, 757, 16384⟩ := by
  decide +kernel

theorem context_13_104612_328057 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104612 ⟨328057, by decide⟩ :=
  accepted_of_selected 13 104612 ⟨328057, by decide⟩ ⟨13, 2, 0, 328057, 104612, 757, 16384⟩
    (by decide) selected_cut_12398

theorem selected_cut_12399 : selected 8 ⟨328081, by decide⟩
    (prefixPartial 13 104613) = some ⟨13, 2, 0, 328081, 104613, 1957, 16384⟩ := by
  decide +kernel

theorem context_13_104613_328081 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104613 ⟨328081, by decide⟩ :=
  accepted_of_selected 13 104613 ⟨328081, by decide⟩ ⟨13, 2, 0, 328081, 104613, 1957, 16384⟩
    (by decide) selected_cut_12399

theorem selected_cut_12400 : selected 8 ⟨328098, by decide⟩
    (prefixPartial 13 104614) = some ⟨13, 2, 0, 328098, 104614, 1329, 16384⟩ := by
  decide +kernel

theorem context_13_104614_328098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104614 ⟨328098, by decide⟩ :=
  accepted_of_selected 13 104614 ⟨328098, by decide⟩ ⟨13, 2, 0, 328098, 104614, 1329, 16384⟩
    (by decide) selected_cut_12400

theorem selected_cut_12401 : selected 8 ⟨328104, by decide⟩
    (prefixPartial 13 104615) = some ⟨13, 2, 0, 328104, 104615, 817, 16384⟩ := by
  decide +kernel

theorem context_13_104615_328104 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104615 ⟨328104, by decide⟩ :=
  accepted_of_selected 13 104615 ⟨328104, by decide⟩ ⟨13, 2, 0, 328104, 104615, 817, 16384⟩
    (by decide) selected_cut_12401

theorem unmarked_context_12_26153_328105 : frontier 9 ⟨328105, by decide⟩
    (prefixCache 12 26153) (prefixPartial 12 26153) = false := by
  decide +kernel

theorem node_context_12_26153_328105 : EJMOriginalGlobalDAGData.nodes 9 ⟨328105, by decide⟩ =
    .split (coordinate 12) (![⟨328057, by decide⟩,⟨328081, by decide⟩,⟨328098, by decide⟩,⟨328104, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26153_328105 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26153 ⟨328105, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26153
    ⟨328105, by decide⟩ (by decide) (![⟨328057, by decide⟩,⟨328081, by decide⟩,⟨328098, by decide⟩,⟨328104, by decide⟩]) unmarked_context_12_26153_328105 node_context_12_26153_328105
  intro a
  fin_cases a
  · exact context_13_104612_328057
  · exact context_13_104613_328081
  · exact context_13_104614_328098
  · exact context_13_104615_328104

theorem selected_cut_12402 : selected 9 ⟨328263, by decide⟩
    (prefixPartial 12 26154) = some ⟨12, 2, 0, 328263, 26154, 4029, 65536⟩ := by
  decide +kernel

theorem context_12_26154_328263 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26154 ⟨328263, by decide⟩ :=
  accepted_of_selected 12 26154 ⟨328263, by decide⟩ ⟨12, 2, 0, 328263, 26154, 4029, 65536⟩
    (by decide) selected_cut_12402

theorem selected_cut_12403 : selected 8 ⟨328277, by decide⟩
    (prefixPartial 13 104620) = some ⟨13, 2, 0, 328277, 104620, 669, 16384⟩ := by
  decide +kernel

theorem context_13_104620_328277 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104620 ⟨328277, by decide⟩ :=
  accepted_of_selected 13 104620 ⟨328277, by decide⟩ ⟨13, 2, 0, 328277, 104620, 669, 16384⟩
    (by decide) selected_cut_12403

theorem selected_cut_12404 : selected 8 ⟨328305, by decide⟩
    (prefixPartial 13 104621) = some ⟨13, 2, 0, 328305, 104621, 2225, 16384⟩ := by
  decide +kernel

theorem context_13_104621_328305 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104621 ⟨328305, by decide⟩ :=
  accepted_of_selected 13 104621 ⟨328305, by decide⟩ ⟨13, 2, 0, 328305, 104621, 2225, 16384⟩
    (by decide) selected_cut_12404

theorem selected_cut_12405 : selected 8 ⟨328321, by decide⟩
    (prefixPartial 13 104622) = some ⟨13, 2, 0, 328321, 104622, 1261, 16384⟩ := by
  decide +kernel

theorem context_13_104622_328321 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104622 ⟨328321, by decide⟩ :=
  accepted_of_selected 13 104622 ⟨328321, by decide⟩ ⟨13, 2, 0, 328321, 104622, 1261, 16384⟩
    (by decide) selected_cut_12405

theorem selected_cut_12406 : selected 8 ⟨328328, by decide⟩
    (prefixPartial 13 104623) = some ⟨13, 2, 0, 328328, 104623, 777, 16384⟩ := by
  decide +kernel

theorem context_13_104623_328328 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104623 ⟨328328, by decide⟩ :=
  accepted_of_selected 13 104623 ⟨328328, by decide⟩ ⟨13, 2, 0, 328328, 104623, 777, 16384⟩
    (by decide) selected_cut_12406

theorem unmarked_context_12_26155_328329 : frontier 9 ⟨328329, by decide⟩
    (prefixCache 12 26155) (prefixPartial 12 26155) = false := by
  decide +kernel

theorem node_context_12_26155_328329 : EJMOriginalGlobalDAGData.nodes 9 ⟨328329, by decide⟩ =
    .split (coordinate 12) (![⟨328277, by decide⟩,⟨328305, by decide⟩,⟨328321, by decide⟩,⟨328328, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26155_328329 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26155 ⟨328329, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26155
    ⟨328329, by decide⟩ (by decide) (![⟨328277, by decide⟩,⟨328305, by decide⟩,⟨328321, by decide⟩,⟨328328, by decide⟩]) unmarked_context_12_26155_328329 node_context_12_26155_328329
  intro a
  fin_cases a
  · exact context_13_104620_328277
  · exact context_13_104621_328305
  · exact context_13_104622_328321
  · exact context_13_104623_328328

theorem unmarked_context_11_6538_328330 : frontier 10 ⟨328330, by decide⟩
    (prefixCache 11 6538) (prefixPartial 11 6538) = false := by
  decide +kernel

theorem node_context_11_6538_328330 : EJMOriginalGlobalDAGData.nodes 10 ⟨328330, by decide⟩ =
    .split (coordinate 11) (![⟨328048, by decide⟩,⟨328105, by decide⟩,⟨328263, by decide⟩,⟨328329, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6538_328330 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6538 ⟨328330, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6538
    ⟨328330, by decide⟩ (by decide) (![⟨328048, by decide⟩,⟨328105, by decide⟩,⟨328263, by decide⟩,⟨328329, by decide⟩]) unmarked_context_11_6538_328330 node_context_11_6538_328330
  intro a
  fin_cases a
  · exact context_12_26152_328048
  · exact context_12_26153_328105
  · exact context_12_26154_328263
  · exact context_12_26155_328329

theorem selected_cut_12407 : selected 8 ⟨328338, by decide⟩
    (prefixPartial 13 104624) = some ⟨13, 2, 0, 328338, 104624, 549, 16384⟩ := by
  decide +kernel

theorem context_13_104624_328338 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104624 ⟨328338, by decide⟩ :=
  accepted_of_selected 13 104624 ⟨328338, by decide⟩ ⟨13, 2, 0, 328338, 104624, 549, 16384⟩
    (by decide) selected_cut_12407

theorem selected_cut_12408 : selected 8 ⟨328359, by decide⟩
    (prefixPartial 13 104625) = some ⟨13, 2, 0, 328359, 104625, 1689, 16384⟩ := by
  decide +kernel

theorem context_13_104625_328359 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104625 ⟨328359, by decide⟩ :=
  accepted_of_selected 13 104625 ⟨328359, by decide⟩ ⟨13, 2, 0, 328359, 104625, 1689, 16384⟩
    (by decide) selected_cut_12408

theorem selected_cut_12409 : selected 8 ⟨328374, by decide⟩
    (prefixPartial 13 104626) = some ⟨13, 2, 0, 328374, 104626, 1121, 16384⟩ := by
  decide +kernel

theorem context_13_104626_328374 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104626 ⟨328374, by decide⟩ :=
  accepted_of_selected 13 104626 ⟨328374, by decide⟩ ⟨13, 2, 0, 328374, 104626, 1121, 16384⟩
    (by decide) selected_cut_12409

theorem selected_cut_12410 : selected 8 ⟨328380, by decide⟩
    (prefixPartial 13 104627) = some ⟨13, 2, 0, 328380, 104627, 761, 16384⟩ := by
  decide +kernel

theorem context_13_104627_328380 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104627 ⟨328380, by decide⟩ :=
  accepted_of_selected 13 104627 ⟨328380, by decide⟩ ⟨13, 2, 0, 328380, 104627, 761, 16384⟩
    (by decide) selected_cut_12410

theorem unmarked_context_12_26156_328381 : frontier 9 ⟨328381, by decide⟩
    (prefixCache 12 26156) (prefixPartial 12 26156) = false := by
  decide +kernel

theorem node_context_12_26156_328381 : EJMOriginalGlobalDAGData.nodes 9 ⟨328381, by decide⟩ =
    .split (coordinate 12) (![⟨328338, by decide⟩,⟨328359, by decide⟩,⟨328374, by decide⟩,⟨328380, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26156_328381 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26156 ⟨328381, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26156
    ⟨328381, by decide⟩ (by decide) (![⟨328338, by decide⟩,⟨328359, by decide⟩,⟨328374, by decide⟩,⟨328380, by decide⟩]) unmarked_context_12_26156_328381 node_context_12_26156_328381
  intro a
  fin_cases a
  · exact context_13_104624_328338
  · exact context_13_104625_328359
  · exact context_13_104626_328374
  · exact context_13_104627_328380

theorem selected_cut_12411 : selected 8 ⟨328389, by decide⟩
    (prefixPartial 13 104628) = some ⟨13, 2, 0, 328389, 104628, 797, 16384⟩ := by
  decide +kernel

theorem context_13_104628_328389 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104628 ⟨328389, by decide⟩ :=
  accepted_of_selected 13 104628 ⟨328389, by decide⟩ ⟨13, 2, 0, 328389, 104628, 797, 16384⟩
    (by decide) selected_cut_12411

theorem selected_cut_12412 : selected 8 ⟨328416, by decide⟩
    (prefixPartial 13 104629) = some ⟨13, 2, 0, 328416, 104629, 2265, 16384⟩ := by
  decide +kernel

theorem context_13_104629_328416 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104629 ⟨328416, by decide⟩ :=
  accepted_of_selected 13 104629 ⟨328416, by decide⟩ ⟨13, 2, 0, 328416, 104629, 2265, 16384⟩
    (by decide) selected_cut_12412

theorem selected_cut_12413 : selected 8 ⟨328433, by decide⟩
    (prefixPartial 13 104630) = some ⟨13, 2, 0, 328433, 104630, 1285, 16384⟩ := by
  decide +kernel

theorem context_13_104630_328433 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104630 ⟨328433, by decide⟩ :=
  accepted_of_selected 13 104630 ⟨328433, by decide⟩ ⟨13, 2, 0, 328433, 104630, 1285, 16384⟩
    (by decide) selected_cut_12413

theorem selected_cut_12414 : selected 8 ⟨328439, by decide⟩
    (prefixPartial 13 104631) = some ⟨13, 2, 0, 328439, 104631, 773, 16384⟩ := by
  decide +kernel

theorem context_13_104631_328439 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104631 ⟨328439, by decide⟩ :=
  accepted_of_selected 13 104631 ⟨328439, by decide⟩ ⟨13, 2, 0, 328439, 104631, 773, 16384⟩
    (by decide) selected_cut_12414

theorem unmarked_context_12_26157_328440 : frontier 9 ⟨328440, by decide⟩
    (prefixCache 12 26157) (prefixPartial 12 26157) = false := by
  decide +kernel

theorem node_context_12_26157_328440 : EJMOriginalGlobalDAGData.nodes 9 ⟨328440, by decide⟩ =
    .split (coordinate 12) (![⟨328389, by decide⟩,⟨328416, by decide⟩,⟨328433, by decide⟩,⟨328439, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26157_328440 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26157 ⟨328440, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26157
    ⟨328440, by decide⟩ (by decide) (![⟨328389, by decide⟩,⟨328416, by decide⟩,⟨328433, by decide⟩,⟨328439, by decide⟩]) unmarked_context_12_26157_328440 node_context_12_26157_328440
  intro a
  fin_cases a
  · exact context_13_104628_328389
  · exact context_13_104629_328416
  · exact context_13_104630_328433
  · exact context_13_104631_328439

theorem selected_cut_12415 : selected 9 ⟨328493, by decide⟩
    (prefixPartial 12 26158) = some ⟨12, 2, 0, 328493, 26158, 3977, 65536⟩ := by
  decide +kernel

theorem context_12_26158_328493 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26158 ⟨328493, by decide⟩ :=
  accepted_of_selected 12 26158 ⟨328493, by decide⟩ ⟨12, 2, 0, 328493, 26158, 3977, 65536⟩
    (by decide) selected_cut_12415

theorem selected_cut_12416 : selected 8 ⟨328502, by decide⟩
    (prefixPartial 13 104636) = some ⟨13, 2, 0, 328502, 104636, 649, 16384⟩ := by
  decide +kernel

theorem context_13_104636_328502 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104636 ⟨328502, by decide⟩ :=
  accepted_of_selected 13 104636 ⟨328502, by decide⟩ ⟨13, 2, 0, 328502, 104636, 649, 16384⟩
    (by decide) selected_cut_12416

theorem selected_cut_12417 : selected 8 ⟨328526, by decide⟩
    (prefixPartial 13 104637) = some ⟨13, 2, 0, 328526, 104637, 2241, 16384⟩ := by
  decide +kernel

theorem context_13_104637_328526 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104637 ⟨328526, by decide⟩ :=
  accepted_of_selected 13 104637 ⟨328526, by decide⟩ ⟨13, 2, 0, 328526, 104637, 2241, 16384⟩
    (by decide) selected_cut_12417

theorem selected_cut_12418 : selected 8 ⟨328544, by decide⟩
    (prefixPartial 13 104638) = some ⟨13, 2, 0, 328544, 104638, 1337, 16384⟩ := by
  decide +kernel

theorem context_13_104638_328544 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104638 ⟨328544, by decide⟩ :=
  accepted_of_selected 13 104638 ⟨328544, by decide⟩ ⟨13, 2, 0, 328544, 104638, 1337, 16384⟩
    (by decide) selected_cut_12418

theorem selected_cut_12419 : selected 8 ⟨328553, by decide⟩
    (prefixPartial 13 104639) = some ⟨13, 2, 0, 328553, 104639, 805, 16384⟩ := by
  decide +kernel

theorem context_13_104639_328553 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104639 ⟨328553, by decide⟩ :=
  accepted_of_selected 13 104639 ⟨328553, by decide⟩ ⟨13, 2, 0, 328553, 104639, 805, 16384⟩
    (by decide) selected_cut_12419

theorem unmarked_context_12_26159_328554 : frontier 9 ⟨328554, by decide⟩
    (prefixCache 12 26159) (prefixPartial 12 26159) = false := by
  decide +kernel

theorem node_context_12_26159_328554 : EJMOriginalGlobalDAGData.nodes 9 ⟨328554, by decide⟩ =
    .split (coordinate 12) (![⟨328502, by decide⟩,⟨328526, by decide⟩,⟨328544, by decide⟩,⟨328553, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26159_328554 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26159 ⟨328554, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26159
    ⟨328554, by decide⟩ (by decide) (![⟨328502, by decide⟩,⟨328526, by decide⟩,⟨328544, by decide⟩,⟨328553, by decide⟩]) unmarked_context_12_26159_328554 node_context_12_26159_328554
  intro a
  fin_cases a
  · exact context_13_104636_328502
  · exact context_13_104637_328526
  · exact context_13_104638_328544
  · exact context_13_104639_328553

theorem unmarked_context_11_6539_328555 : frontier 10 ⟨328555, by decide⟩
    (prefixCache 11 6539) (prefixPartial 11 6539) = false := by
  decide +kernel

theorem node_context_11_6539_328555 : EJMOriginalGlobalDAGData.nodes 10 ⟨328555, by decide⟩ =
    .split (coordinate 11) (![⟨328381, by decide⟩,⟨328440, by decide⟩,⟨328493, by decide⟩,⟨328554, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6539_328555 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6539 ⟨328555, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6539
    ⟨328555, by decide⟩ (by decide) (![⟨328381, by decide⟩,⟨328440, by decide⟩,⟨328493, by decide⟩,⟨328554, by decide⟩]) unmarked_context_11_6539_328555 node_context_11_6539_328555
  intro a
  fin_cases a
  · exact context_12_26156_328381
  · exact context_12_26157_328440
  · exact context_12_26158_328493
  · exact context_12_26159_328554

theorem unmarked_context_10_1634_328556 : frontier 11 ⟨328556, by decide⟩
    (prefixCache 10 1634) (prefixPartial 10 1634) = false := by
  decide +kernel

theorem node_context_10_1634_328556 : EJMOriginalGlobalDAGData.nodes 11 ⟨328556, by decide⟩ =
    .split (coordinate 10) (![⟨327773, by decide⟩,⟨327994, by decide⟩,⟨328330, by decide⟩,⟨328555, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1634_328556 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1634 ⟨328556, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1634
    ⟨328556, by decide⟩ (by decide) (![⟨327773, by decide⟩,⟨327994, by decide⟩,⟨328330, by decide⟩,⟨328555, by decide⟩]) unmarked_context_10_1634_328556 node_context_10_1634_328556
  intro a
  fin_cases a
  · exact context_11_6536_327773
  · exact context_11_6537_327994
  · exact context_11_6538_328330
  · exact context_11_6539_328555

theorem selected_cut_12420 : selected 8 ⟨328563, by decide⟩
    (prefixPartial 13 104640) = some ⟨13, 2, 0, 328563, 104640, 661, 16384⟩ := by
  decide +kernel

theorem context_13_104640_328563 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104640 ⟨328563, by decide⟩ :=
  accepted_of_selected 13 104640 ⟨328563, by decide⟩ ⟨13, 2, 0, 328563, 104640, 661, 16384⟩
    (by decide) selected_cut_12420

theorem selected_cut_12421 : selected 8 ⟨328584, by decide⟩
    (prefixPartial 13 104641) = some ⟨13, 2, 0, 328584, 104641, 1817, 16384⟩ := by
  decide +kernel

theorem context_13_104641_328584 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104641 ⟨328584, by decide⟩ :=
  accepted_of_selected 13 104641 ⟨328584, by decide⟩ ⟨13, 2, 0, 328584, 104641, 1817, 16384⟩
    (by decide) selected_cut_12421

theorem selected_cut_12422 : selected 8 ⟨328599, by decide⟩
    (prefixPartial 13 104642) = some ⟨13, 2, 0, 328599, 104642, 1101, 16384⟩ := by
  decide +kernel

theorem context_13_104642_328599 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104642 ⟨328599, by decide⟩ :=
  accepted_of_selected 13 104642 ⟨328599, by decide⟩ ⟨13, 2, 0, 328599, 104642, 1101, 16384⟩
    (by decide) selected_cut_12422

theorem selected_cut_12423 : selected 8 ⟨328603, by decide⟩
    (prefixPartial 13 104643) = some ⟨13, 2, 0, 328603, 104643, 745, 16384⟩ := by
  decide +kernel

theorem context_13_104643_328603 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104643 ⟨328603, by decide⟩ :=
  accepted_of_selected 13 104643 ⟨328603, by decide⟩ ⟨13, 2, 0, 328603, 104643, 745, 16384⟩
    (by decide) selected_cut_12423

theorem unmarked_context_12_26160_328604 : frontier 9 ⟨328604, by decide⟩
    (prefixCache 12 26160) (prefixPartial 12 26160) = false := by
  decide +kernel

theorem node_context_12_26160_328604 : EJMOriginalGlobalDAGData.nodes 9 ⟨328604, by decide⟩ =
    .split (coordinate 12) (![⟨328563, by decide⟩,⟨328584, by decide⟩,⟨328599, by decide⟩,⟨328603, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26160_328604 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26160 ⟨328604, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26160
    ⟨328604, by decide⟩ (by decide) (![⟨328563, by decide⟩,⟨328584, by decide⟩,⟨328599, by decide⟩,⟨328603, by decide⟩]) unmarked_context_12_26160_328604 node_context_12_26160_328604
  intro a
  fin_cases a
  · exact context_13_104640_328563
  · exact context_13_104641_328584
  · exact context_13_104642_328599
  · exact context_13_104643_328603

theorem selected_cut_12424 : selected 8 ⟨328616, by decide⟩
    (prefixPartial 13 104644) = some ⟨13, 2, 0, 328616, 104644, 857, 16384⟩ := by
  decide +kernel

theorem context_13_104644_328616 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104644 ⟨328616, by decide⟩ :=
  accepted_of_selected 13 104644 ⟨328616, by decide⟩ ⟨13, 2, 0, 328616, 104644, 857, 16384⟩
    (by decide) selected_cut_12424

theorem selected_cut_12425 : selected 8 ⟨328652, by decide⟩
    (prefixPartial 13 104645) = some ⟨13, 2, 0, 328652, 104645, 2589, 16384⟩ := by
  decide +kernel

theorem context_13_104645_328652 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104645 ⟨328652, by decide⟩ :=
  accepted_of_selected 13 104645 ⟨328652, by decide⟩ ⟨13, 2, 0, 328652, 104645, 2589, 16384⟩
    (by decide) selected_cut_12425

theorem selected_cut_12426 : selected 8 ⟨328671, by decide⟩
    (prefixPartial 13 104646) = some ⟨13, 2, 0, 328671, 104646, 1373, 16384⟩ := by
  decide +kernel

theorem context_13_104646_328671 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104646 ⟨328671, by decide⟩ :=
  accepted_of_selected 13 104646 ⟨328671, by decide⟩ ⟨13, 2, 0, 328671, 104646, 1373, 16384⟩
    (by decide) selected_cut_12426

theorem selected_cut_12427 : selected 8 ⟨328678, by decide⟩
    (prefixPartial 13 104647) = some ⟨13, 2, 0, 328678, 104647, 821, 16384⟩ := by
  decide +kernel

theorem context_13_104647_328678 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104647 ⟨328678, by decide⟩ :=
  accepted_of_selected 13 104647 ⟨328678, by decide⟩ ⟨13, 2, 0, 328678, 104647, 821, 16384⟩
    (by decide) selected_cut_12427

theorem unmarked_context_12_26161_328679 : frontier 9 ⟨328679, by decide⟩
    (prefixCache 12 26161) (prefixPartial 12 26161) = false := by
  decide +kernel

theorem node_context_12_26161_328679 : EJMOriginalGlobalDAGData.nodes 9 ⟨328679, by decide⟩ =
    .split (coordinate 12) (![⟨328616, by decide⟩,⟨328652, by decide⟩,⟨328671, by decide⟩,⟨328678, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26161_328679 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26161 ⟨328679, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26161
    ⟨328679, by decide⟩ (by decide) (![⟨328616, by decide⟩,⟨328652, by decide⟩,⟨328671, by decide⟩,⟨328678, by decide⟩]) unmarked_context_12_26161_328679 node_context_12_26161_328679
  intro a
  fin_cases a
  · exact context_13_104644_328616
  · exact context_13_104645_328652
  · exact context_13_104646_328671
  · exact context_13_104647_328678

theorem selected_cut_12428 : selected 8 ⟨328692, by decide⟩
    (prefixPartial 13 104648) = some ⟨13, 2, 0, 328692, 104648, 721, 16384⟩ := by
  decide +kernel

theorem context_13_104648_328692 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104648 ⟨328692, by decide⟩ :=
  accepted_of_selected 13 104648 ⟨328692, by decide⟩ ⟨13, 2, 0, 328692, 104648, 721, 16384⟩
    (by decide) selected_cut_12428

theorem selected_cut_12429 : selected 8 ⟨328719, by decide⟩
    (prefixPartial 13 104649) = some ⟨13, 2, 0, 328719, 104649, 1961, 16384⟩ := by
  decide +kernel

theorem context_13_104649_328719 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104649 ⟨328719, by decide⟩ :=
  accepted_of_selected 13 104649 ⟨328719, by decide⟩ ⟨13, 2, 0, 328719, 104649, 1961, 16384⟩
    (by decide) selected_cut_12429

theorem selected_cut_12430 : selected 8 ⟨328734, by decide⟩
    (prefixPartial 13 104650) = some ⟨13, 2, 0, 328734, 104650, 1045, 16384⟩ := by
  decide +kernel

theorem context_13_104650_328734 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104650 ⟨328734, by decide⟩ :=
  accepted_of_selected 13 104650 ⟨328734, by decide⟩ ⟨13, 2, 0, 328734, 104650, 1045, 16384⟩
    (by decide) selected_cut_12430

theorem selected_cut_12431 : selected 8 ⟨328739, by decide⟩
    (prefixPartial 13 104651) = some ⟨13, 2, 0, 328739, 104651, 801, 16384⟩ := by
  decide +kernel

theorem context_13_104651_328739 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104651 ⟨328739, by decide⟩ :=
  accepted_of_selected 13 104651 ⟨328739, by decide⟩ ⟨13, 2, 0, 328739, 104651, 801, 16384⟩
    (by decide) selected_cut_12431

theorem unmarked_context_12_26162_328740 : frontier 9 ⟨328740, by decide⟩
    (prefixCache 12 26162) (prefixPartial 12 26162) = false := by
  decide +kernel

theorem node_context_12_26162_328740 : EJMOriginalGlobalDAGData.nodes 9 ⟨328740, by decide⟩ =
    .split (coordinate 12) (![⟨328692, by decide⟩,⟨328719, by decide⟩,⟨328734, by decide⟩,⟨328739, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26162_328740 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26162 ⟨328740, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26162
    ⟨328740, by decide⟩ (by decide) (![⟨328692, by decide⟩,⟨328719, by decide⟩,⟨328734, by decide⟩,⟨328739, by decide⟩]) unmarked_context_12_26162_328740 node_context_12_26162_328740
  intro a
  fin_cases a
  · exact context_13_104648_328692
  · exact context_13_104649_328719
  · exact context_13_104650_328734
  · exact context_13_104651_328739

theorem selected_cut_12432 : selected 8 ⟨328757, by decide⟩
    (prefixPartial 13 104652) = some ⟨13, 2, 0, 328757, 104652, 893, 16384⟩ := by
  decide +kernel

theorem context_13_104652_328757 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104652 ⟨328757, by decide⟩ :=
  accepted_of_selected 13 104652 ⟨328757, by decide⟩ ⟨13, 2, 0, 328757, 104652, 893, 16384⟩
    (by decide) selected_cut_12432

theorem selected_cut_12433 : selected 8 ⟨328802, by decide⟩
    (prefixPartial 13 104653) = some ⟨13, 2, 0, 328802, 104653, 3101, 16384⟩ := by
  decide +kernel

theorem context_13_104653_328802 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104653 ⟨328802, by decide⟩ :=
  accepted_of_selected 13 104653 ⟨328802, by decide⟩ ⟨13, 2, 0, 328802, 104653, 3101, 16384⟩
    (by decide) selected_cut_12433

theorem selected_cut_12434 : selected 8 ⟨328819, by decide⟩
    (prefixPartial 13 104654) = some ⟨13, 2, 0, 328819, 104654, 1485, 16384⟩ := by
  decide +kernel

theorem context_13_104654_328819 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104654 ⟨328819, by decide⟩ :=
  accepted_of_selected 13 104654 ⟨328819, by decide⟩ ⟨13, 2, 0, 328819, 104654, 1485, 16384⟩
    (by decide) selected_cut_12434

theorem selected_cut_12435 : selected 8 ⟨328824, by decide⟩
    (prefixPartial 13 104655) = some ⟨13, 2, 0, 328824, 104655, 921, 16384⟩ := by
  decide +kernel

theorem context_13_104655_328824 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104655 ⟨328824, by decide⟩ :=
  accepted_of_selected 13 104655 ⟨328824, by decide⟩ ⟨13, 2, 0, 328824, 104655, 921, 16384⟩
    (by decide) selected_cut_12435

theorem unmarked_context_12_26163_328825 : frontier 9 ⟨328825, by decide⟩
    (prefixCache 12 26163) (prefixPartial 12 26163) = false := by
  decide +kernel

theorem node_context_12_26163_328825 : EJMOriginalGlobalDAGData.nodes 9 ⟨328825, by decide⟩ =
    .split (coordinate 12) (![⟨328757, by decide⟩,⟨328802, by decide⟩,⟨328819, by decide⟩,⟨328824, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26163_328825 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26163 ⟨328825, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26163
    ⟨328825, by decide⟩ (by decide) (![⟨328757, by decide⟩,⟨328802, by decide⟩,⟨328819, by decide⟩,⟨328824, by decide⟩]) unmarked_context_12_26163_328825 node_context_12_26163_328825
  intro a
  fin_cases a
  · exact context_13_104652_328757
  · exact context_13_104653_328802
  · exact context_13_104654_328819
  · exact context_13_104655_328824

theorem unmarked_context_11_6540_328826 : frontier 10 ⟨328826, by decide⟩
    (prefixCache 11 6540) (prefixPartial 11 6540) = false := by
  decide +kernel

theorem node_context_11_6540_328826 : EJMOriginalGlobalDAGData.nodes 10 ⟨328826, by decide⟩ =
    .split (coordinate 11) (![⟨328604, by decide⟩,⟨328679, by decide⟩,⟨328740, by decide⟩,⟨328825, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6540_328826 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6540 ⟨328826, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6540
    ⟨328826, by decide⟩ (by decide) (![⟨328604, by decide⟩,⟨328679, by decide⟩,⟨328740, by decide⟩,⟨328825, by decide⟩]) unmarked_context_11_6540_328826 node_context_11_6540_328826
  intro a
  fin_cases a
  · exact context_12_26160_328604
  · exact context_12_26161_328679
  · exact context_12_26162_328740
  · exact context_12_26163_328825

theorem selected_cut_12436 : selected 8 ⟨328832, by decide⟩
    (prefixPartial 13 104656) = some ⟨13, 2, 0, 328832, 104656, 437, 16384⟩ := by
  decide +kernel

theorem context_13_104656_328832 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104656 ⟨328832, by decide⟩ :=
  accepted_of_selected 13 104656 ⟨328832, by decide⟩ ⟨13, 2, 0, 328832, 104656, 437, 16384⟩
    (by decide) selected_cut_12436

theorem selected_cut_12437 : selected 8 ⟨328858, by decide⟩
    (prefixPartial 13 104657) = some ⟨13, 2, 0, 328858, 104657, 2177, 16384⟩ := by
  decide +kernel

theorem context_13_104657_328858 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104657 ⟨328858, by decide⟩ :=
  accepted_of_selected 13 104657 ⟨328858, by decide⟩ ⟨13, 2, 0, 328858, 104657, 2177, 16384⟩
    (by decide) selected_cut_12437

theorem selected_cut_12438 : selected 8 ⟨328870, by decide⟩
    (prefixPartial 13 104658) = some ⟨13, 2, 0, 328870, 104658, 1137, 16384⟩ := by
  decide +kernel

theorem context_13_104658_328870 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104658 ⟨328870, by decide⟩ :=
  accepted_of_selected 13 104658 ⟨328870, by decide⟩ ⟨13, 2, 0, 328870, 104658, 1137, 16384⟩
    (by decide) selected_cut_12438

theorem selected_cut_12439 : selected 8 ⟨328874, by decide⟩
    (prefixPartial 13 104659) = some ⟨13, 2, 0, 328874, 104659, 809, 16384⟩ := by
  decide +kernel

theorem context_13_104659_328874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104659 ⟨328874, by decide⟩ :=
  accepted_of_selected 13 104659 ⟨328874, by decide⟩ ⟨13, 2, 0, 328874, 104659, 809, 16384⟩
    (by decide) selected_cut_12439

theorem unmarked_context_12_26164_328875 : frontier 9 ⟨328875, by decide⟩
    (prefixCache 12 26164) (prefixPartial 12 26164) = false := by
  decide +kernel

theorem node_context_12_26164_328875 : EJMOriginalGlobalDAGData.nodes 9 ⟨328875, by decide⟩ =
    .split (coordinate 12) (![⟨328832, by decide⟩,⟨328858, by decide⟩,⟨328870, by decide⟩,⟨328874, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26164_328875 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26164 ⟨328875, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26164
    ⟨328875, by decide⟩ (by decide) (![⟨328832, by decide⟩,⟨328858, by decide⟩,⟨328870, by decide⟩,⟨328874, by decide⟩]) unmarked_context_12_26164_328875 node_context_12_26164_328875
  intro a
  fin_cases a
  · exact context_13_104656_328832
  · exact context_13_104657_328858
  · exact context_13_104658_328870
  · exact context_13_104659_328874

theorem selected_cut_12440 : selected 8 ⟨328883, by decide⟩
    (prefixPartial 13 104660) = some ⟨13, 2, 0, 328883, 104660, 593, 16384⟩ := by
  decide +kernel

theorem context_13_104660_328883 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104660 ⟨328883, by decide⟩ :=
  accepted_of_selected 13 104660 ⟨328883, by decide⟩ ⟨13, 2, 0, 328883, 104660, 593, 16384⟩
    (by decide) selected_cut_12440

theorem selected_cut_12441 : selected 8 ⟨328912, by decide⟩
    (prefixPartial 13 104661) = some ⟨13, 2, 0, 328912, 104661, 2397, 16384⟩ := by
  decide +kernel

theorem context_13_104661_328912 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104661 ⟨328912, by decide⟩ :=
  accepted_of_selected 13 104661 ⟨328912, by decide⟩ ⟨13, 2, 0, 328912, 104661, 2397, 16384⟩
    (by decide) selected_cut_12441

theorem selected_cut_12442 : selected 8 ⟨328926, by decide⟩
    (prefixPartial 13 104662) = some ⟨13, 2, 0, 328926, 104662, 1265, 16384⟩ := by
  decide +kernel

theorem context_13_104662_328926 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104662 ⟨328926, by decide⟩ :=
  accepted_of_selected 13 104662 ⟨328926, by decide⟩ ⟨13, 2, 0, 328926, 104662, 1265, 16384⟩
    (by decide) selected_cut_12442

theorem selected_cut_12443 : selected 8 ⟨328930, by decide⟩
    (prefixPartial 13 104663) = some ⟨13, 2, 0, 328930, 104663, 785, 16384⟩ := by
  decide +kernel

theorem context_13_104663_328930 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104663 ⟨328930, by decide⟩ :=
  accepted_of_selected 13 104663 ⟨328930, by decide⟩ ⟨13, 2, 0, 328930, 104663, 785, 16384⟩
    (by decide) selected_cut_12443

theorem unmarked_context_12_26165_328931 : frontier 9 ⟨328931, by decide⟩
    (prefixCache 12 26165) (prefixPartial 12 26165) = false := by
  decide +kernel

theorem node_context_12_26165_328931 : EJMOriginalGlobalDAGData.nodes 9 ⟨328931, by decide⟩ =
    .split (coordinate 12) (![⟨328883, by decide⟩,⟨328912, by decide⟩,⟨328926, by decide⟩,⟨328930, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26165_328931 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26165 ⟨328931, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26165
    ⟨328931, by decide⟩ (by decide) (![⟨328883, by decide⟩,⟨328912, by decide⟩,⟨328926, by decide⟩,⟨328930, by decide⟩]) unmarked_context_12_26165_328931 node_context_12_26165_328931
  intro a
  fin_cases a
  · exact context_13_104660_328883
  · exact context_13_104661_328912
  · exact context_13_104662_328926
  · exact context_13_104663_328930

theorem selected_cut_12444 : selected 8 ⟨328937, by decide⟩
    (prefixPartial 13 104664) = some ⟨13, 2, 0, 328937, 104664, 457, 16384⟩ := by
  decide +kernel

theorem context_13_104664_328937 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104664 ⟨328937, by decide⟩ :=
  accepted_of_selected 13 104664 ⟨328937, by decide⟩ ⟨13, 2, 0, 328937, 104664, 457, 16384⟩
    (by decide) selected_cut_12444

theorem selected_cut_12445 : selected 8 ⟨328963, by decide⟩
    (prefixPartial 13 104665) = some ⟨13, 2, 0, 328963, 104665, 2053, 16384⟩ := by
  decide +kernel

theorem context_13_104665_328963 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104665 ⟨328963, by decide⟩ :=
  accepted_of_selected 13 104665 ⟨328963, by decide⟩ ⟨13, 2, 0, 328963, 104665, 2053, 16384⟩
    (by decide) selected_cut_12445

theorem selected_cut_12446 : selected 8 ⟨328975, by decide⟩
    (prefixPartial 13 104666) = some ⟨13, 2, 0, 328975, 104666, 1037, 16384⟩ := by
  decide +kernel

theorem context_13_104666_328975 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104666 ⟨328975, by decide⟩ :=
  accepted_of_selected 13 104666 ⟨328975, by decide⟩ ⟨13, 2, 0, 328975, 104666, 1037, 16384⟩
    (by decide) selected_cut_12446

theorem selected_cut_12447 : selected 8 ⟨328981, by decide⟩
    (prefixPartial 13 104667) = some ⟨13, 2, 0, 328981, 104667, 845, 16384⟩ := by
  decide +kernel

theorem context_13_104667_328981 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104667 ⟨328981, by decide⟩ :=
  accepted_of_selected 13 104667 ⟨328981, by decide⟩ ⟨13, 2, 0, 328981, 104667, 845, 16384⟩
    (by decide) selected_cut_12447

theorem unmarked_context_12_26166_328982 : frontier 9 ⟨328982, by decide⟩
    (prefixCache 12 26166) (prefixPartial 12 26166) = false := by
  decide +kernel

theorem node_context_12_26166_328982 : EJMOriginalGlobalDAGData.nodes 9 ⟨328982, by decide⟩ =
    .split (coordinate 12) (![⟨328937, by decide⟩,⟨328963, by decide⟩,⟨328975, by decide⟩,⟨328981, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26166_328982 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26166 ⟨328982, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26166
    ⟨328982, by decide⟩ (by decide) (![⟨328937, by decide⟩,⟨328963, by decide⟩,⟨328975, by decide⟩,⟨328981, by decide⟩]) unmarked_context_12_26166_328982 node_context_12_26166_328982
  intro a
  fin_cases a
  · exact context_13_104664_328937
  · exact context_13_104665_328963
  · exact context_13_104666_328975
  · exact context_13_104667_328981

theorem selected_cut_12448 : selected 8 ⟨328994, by decide⟩
    (prefixPartial 13 104668) = some ⟨13, 2, 0, 328994, 104668, 557, 16384⟩ := by
  decide +kernel

theorem context_13_104668_328994 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104668 ⟨328994, by decide⟩ :=
  accepted_of_selected 13 104668 ⟨328994, by decide⟩ ⟨13, 2, 0, 328994, 104668, 557, 16384⟩
    (by decide) selected_cut_12448

theorem selected_cut_12449 : selected 8 ⟨329033, by decide⟩
    (prefixPartial 13 104669) = some ⟨13, 2, 0, 329033, 104669, 2873, 16384⟩ := by
  decide +kernel

theorem context_13_104669_329033 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104669 ⟨329033, by decide⟩ :=
  accepted_of_selected 13 104669 ⟨329033, by decide⟩ ⟨13, 2, 0, 329033, 104669, 2873, 16384⟩
    (by decide) selected_cut_12449

theorem selected_cut_12450 : selected 8 ⟨329048, by decide⟩
    (prefixPartial 13 104670) = some ⟨13, 2, 0, 329048, 104670, 1369, 16384⟩ := by
  decide +kernel

theorem context_13_104670_329048 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104670 ⟨329048, by decide⟩ :=
  accepted_of_selected 13 104670 ⟨329048, by decide⟩ ⟨13, 2, 0, 329048, 104670, 1369, 16384⟩
    (by decide) selected_cut_12450

theorem selected_cut_12451 : selected 8 ⟨329056, by decide⟩
    (prefixPartial 13 104671) = some ⟨13, 2, 0, 329056, 104671, 913, 16384⟩ := by
  decide +kernel

theorem context_13_104671_329056 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104671 ⟨329056, by decide⟩ :=
  accepted_of_selected 13 104671 ⟨329056, by decide⟩ ⟨13, 2, 0, 329056, 104671, 913, 16384⟩
    (by decide) selected_cut_12451

theorem unmarked_context_12_26167_329057 : frontier 9 ⟨329057, by decide⟩
    (prefixCache 12 26167) (prefixPartial 12 26167) = false := by
  decide +kernel

theorem node_context_12_26167_329057 : EJMOriginalGlobalDAGData.nodes 9 ⟨329057, by decide⟩ =
    .split (coordinate 12) (![⟨328994, by decide⟩,⟨329033, by decide⟩,⟨329048, by decide⟩,⟨329056, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26167_329057 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26167 ⟨329057, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26167
    ⟨329057, by decide⟩ (by decide) (![⟨328994, by decide⟩,⟨329033, by decide⟩,⟨329048, by decide⟩,⟨329056, by decide⟩]) unmarked_context_12_26167_329057 node_context_12_26167_329057
  intro a
  fin_cases a
  · exact context_13_104668_328994
  · exact context_13_104669_329033
  · exact context_13_104670_329048
  · exact context_13_104671_329056

theorem unmarked_context_11_6541_329058 : frontier 10 ⟨329058, by decide⟩
    (prefixCache 11 6541) (prefixPartial 11 6541) = false := by
  decide +kernel

theorem node_context_11_6541_329058 : EJMOriginalGlobalDAGData.nodes 10 ⟨329058, by decide⟩ =
    .split (coordinate 11) (![⟨328875, by decide⟩,⟨328931, by decide⟩,⟨328982, by decide⟩,⟨329057, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6541_329058 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6541 ⟨329058, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6541
    ⟨329058, by decide⟩ (by decide) (![⟨328875, by decide⟩,⟨328931, by decide⟩,⟨328982, by decide⟩,⟨329057, by decide⟩]) unmarked_context_11_6541_329058 node_context_11_6541_329058
  intro a
  fin_cases a
  · exact context_12_26164_328875
  · exact context_12_26165_328931
  · exact context_12_26166_328982
  · exact context_12_26167_329057

theorem selected_cut_12452 : selected 8 ⟨329064, by decide⟩
    (prefixPartial 13 104672) = some ⟨13, 2, 0, 329064, 104672, 277, 16384⟩ := by
  decide +kernel

theorem context_13_104672_329064 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104672 ⟨329064, by decide⟩ :=
  accepted_of_selected 13 104672 ⟨329064, by decide⟩ ⟨13, 2, 0, 329064, 104672, 277, 16384⟩
    (by decide) selected_cut_12452

theorem selected_cut_12453 : selected 8 ⟨329093, by decide⟩
    (prefixPartial 13 104673) = some ⟨13, 2, 0, 329093, 104673, 1953, 16384⟩ := by
  decide +kernel

theorem context_13_104673_329093 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104673 ⟨329093, by decide⟩ :=
  accepted_of_selected 13 104673 ⟨329093, by decide⟩ ⟨13, 2, 0, 329093, 104673, 1953, 16384⟩
    (by decide) selected_cut_12453

theorem selected_cut_12454 : selected 8 ⟨329108, by decide⟩
    (prefixPartial 13 104674) = some ⟨13, 2, 0, 329108, 104674, 1081, 16384⟩ := by
  decide +kernel

theorem context_13_104674_329108 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104674 ⟨329108, by decide⟩ :=
  accepted_of_selected 13 104674 ⟨329108, by decide⟩ ⟨13, 2, 0, 329108, 104674, 1081, 16384⟩
    (by decide) selected_cut_12454

theorem selected_cut_12455 : selected 8 ⟨329115, by decide⟩
    (prefixPartial 13 104675) = some ⟨13, 2, 0, 329115, 104675, 829, 16384⟩ := by
  decide +kernel

theorem context_13_104675_329115 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104675 ⟨329115, by decide⟩ :=
  accepted_of_selected 13 104675 ⟨329115, by decide⟩ ⟨13, 2, 0, 329115, 104675, 829, 16384⟩
    (by decide) selected_cut_12455

theorem unmarked_context_12_26168_329116 : frontier 9 ⟨329116, by decide⟩
    (prefixCache 12 26168) (prefixPartial 12 26168) = false := by
  decide +kernel

theorem node_context_12_26168_329116 : EJMOriginalGlobalDAGData.nodes 9 ⟨329116, by decide⟩ =
    .split (coordinate 12) (![⟨329064, by decide⟩,⟨329093, by decide⟩,⟨329108, by decide⟩,⟨329115, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26168_329116 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26168 ⟨329116, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26168
    ⟨329116, by decide⟩ (by decide) (![⟨329064, by decide⟩,⟨329093, by decide⟩,⟨329108, by decide⟩,⟨329115, by decide⟩]) unmarked_context_12_26168_329116 node_context_12_26168_329116
  intro a
  fin_cases a
  · exact context_13_104672_329064
  · exact context_13_104673_329093
  · exact context_13_104674_329108
  · exact context_13_104675_329115

theorem selected_cut_12456 : selected 8 ⟨329124, by decide⟩
    (prefixPartial 13 104676) = some ⟨13, 2, 0, 329124, 104676, 341, 16384⟩ := by
  decide +kernel

theorem context_13_104676_329124 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104676 ⟨329124, by decide⟩ :=
  accepted_of_selected 13 104676 ⟨329124, by decide⟩ ⟨13, 2, 0, 329124, 104676, 341, 16384⟩
    (by decide) selected_cut_12456

theorem selected_cut_12457 : selected 8 ⟨329160, by decide⟩
    (prefixPartial 13 104677) = some ⟨13, 2, 0, 329160, 104677, 2317, 16384⟩ := by
  decide +kernel

theorem context_13_104677_329160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104677 ⟨329160, by decide⟩ :=
  accepted_of_selected 13 104677 ⟨329160, by decide⟩ ⟨13, 2, 0, 329160, 104677, 2317, 16384⟩
    (by decide) selected_cut_12457

theorem selected_cut_12458 : selected 8 ⟨329176, by decide⟩
    (prefixPartial 13 104678) = some ⟨13, 2, 0, 329176, 104678, 1317, 16384⟩ := by
  decide +kernel

theorem context_13_104678_329176 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104678 ⟨329176, by decide⟩ :=
  accepted_of_selected 13 104678 ⟨329176, by decide⟩ ⟨13, 2, 0, 329176, 104678, 1317, 16384⟩
    (by decide) selected_cut_12458

theorem selected_cut_12459 : selected 8 ⟨329183, by decide⟩
    (prefixPartial 13 104679) = some ⟨13, 2, 0, 329183, 104679, 829, 16384⟩ := by
  decide +kernel

theorem context_13_104679_329183 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104679 ⟨329183, by decide⟩ :=
  accepted_of_selected 13 104679 ⟨329183, by decide⟩ ⟨13, 2, 0, 329183, 104679, 829, 16384⟩
    (by decide) selected_cut_12459

theorem unmarked_context_12_26169_329184 : frontier 9 ⟨329184, by decide⟩
    (prefixCache 12 26169) (prefixPartial 12 26169) = false := by
  decide +kernel

theorem node_context_12_26169_329184 : EJMOriginalGlobalDAGData.nodes 9 ⟨329184, by decide⟩ =
    .split (coordinate 12) (![⟨329124, by decide⟩,⟨329160, by decide⟩,⟨329176, by decide⟩,⟨329183, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26169_329184 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26169 ⟨329184, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26169
    ⟨329184, by decide⟩ (by decide) (![⟨329124, by decide⟩,⟨329160, by decide⟩,⟨329176, by decide⟩,⟨329183, by decide⟩]) unmarked_context_12_26169_329184 node_context_12_26169_329184
  intro a
  fin_cases a
  · exact context_13_104676_329124
  · exact context_13_104677_329160
  · exact context_13_104678_329176
  · exact context_13_104679_329183

theorem selected_cut_12460 : selected 8 ⟨329193, by decide⟩
    (prefixPartial 13 104680) = some ⟨13, 2, 0, 329193, 104680, 417, 16384⟩ := by
  decide +kernel

theorem context_13_104680_329193 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104680 ⟨329193, by decide⟩ :=
  accepted_of_selected 13 104680 ⟨329193, by decide⟩ ⟨13, 2, 0, 329193, 104680, 417, 16384⟩
    (by decide) selected_cut_12460

theorem selected_cut_12461 : selected 8 ⟨329242, by decide⟩
    (prefixPartial 13 104681) = some ⟨13, 2, 0, 329242, 104681, 3613, 16384⟩ := by
  decide +kernel

theorem context_13_104681_329242 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104681 ⟨329242, by decide⟩ :=
  accepted_of_selected 13 104681 ⟨329242, by decide⟩ ⟨13, 2, 0, 329242, 104681, 3613, 16384⟩
    (by decide) selected_cut_12461

theorem selected_cut_12462 : selected 8 ⟨329263, by decide⟩
    (prefixPartial 13 104682) = some ⟨13, 2, 0, 329263, 104682, 1969, 16384⟩ := by
  decide +kernel

theorem context_13_104682_329263 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104682 ⟨329263, by decide⟩ :=
  accepted_of_selected 13 104682 ⟨329263, by decide⟩ ⟨13, 2, 0, 329263, 104682, 1969, 16384⟩
    (by decide) selected_cut_12462

theorem selected_cut_12463 : selected 8 ⟨329275, by decide⟩
    (prefixPartial 13 104683) = some ⟨13, 2, 0, 329275, 104683, 1201, 16384⟩ := by
  decide +kernel

theorem context_13_104683_329275 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104683 ⟨329275, by decide⟩ :=
  accepted_of_selected 13 104683 ⟨329275, by decide⟩ ⟨13, 2, 0, 329275, 104683, 1201, 16384⟩
    (by decide) selected_cut_12463

theorem unmarked_context_12_26170_329276 : frontier 9 ⟨329276, by decide⟩
    (prefixCache 12 26170) (prefixPartial 12 26170) = false := by
  decide +kernel

theorem node_context_12_26170_329276 : EJMOriginalGlobalDAGData.nodes 9 ⟨329276, by decide⟩ =
    .split (coordinate 12) (![⟨329193, by decide⟩,⟨329242, by decide⟩,⟨329263, by decide⟩,⟨329275, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26170_329276 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26170 ⟨329276, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26170
    ⟨329276, by decide⟩ (by decide) (![⟨329193, by decide⟩,⟨329242, by decide⟩,⟨329263, by decide⟩,⟨329275, by decide⟩]) unmarked_context_12_26170_329276 node_context_12_26170_329276
  intro a
  fin_cases a
  · exact context_13_104680_329193
  · exact context_13_104681_329242
  · exact context_13_104682_329263
  · exact context_13_104683_329275

theorem selected_cut_12464 : selected 8 ⟨329281, by decide⟩
    (prefixPartial 13 104684) = some ⟨13, 2, 0, 329281, 104684, 269, 16384⟩ := by
  decide +kernel

theorem context_13_104684_329281 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104684 ⟨329281, by decide⟩ :=
  accepted_of_selected 13 104684 ⟨329281, by decide⟩ ⟨13, 2, 0, 329281, 104684, 269, 16384⟩
    (by decide) selected_cut_12464

theorem selected_cut_12465 : selected 8 ⟨329330, by decide⟩
    (prefixPartial 13 104685) = some ⟨13, 2, 0, 329330, 104685, 2933, 16384⟩ := by
  decide +kernel

theorem context_13_104685_329330 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104685 ⟨329330, by decide⟩ :=
  accepted_of_selected 13 104685 ⟨329330, by decide⟩ ⟨13, 2, 0, 329330, 104685, 2933, 16384⟩
    (by decide) selected_cut_12465

theorem selected_cut_12466 : selected 8 ⟨329344, by decide⟩
    (prefixPartial 13 104686) = some ⟨13, 2, 0, 329344, 104686, 1281, 16384⟩ := by
  decide +kernel

theorem context_13_104686_329344 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104686 ⟨329344, by decide⟩ :=
  accepted_of_selected 13 104686 ⟨329344, by decide⟩ ⟨13, 2, 0, 329344, 104686, 1281, 16384⟩
    (by decide) selected_cut_12466

theorem selected_cut_12467 : selected 8 ⟨329348, by decide⟩
    (prefixPartial 13 104687) = some ⟨13, 2, 0, 329348, 104687, 809, 16384⟩ := by
  decide +kernel

theorem context_13_104687_329348 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104687 ⟨329348, by decide⟩ :=
  accepted_of_selected 13 104687 ⟨329348, by decide⟩ ⟨13, 2, 0, 329348, 104687, 809, 16384⟩
    (by decide) selected_cut_12467

theorem unmarked_context_12_26171_329349 : frontier 9 ⟨329349, by decide⟩
    (prefixCache 12 26171) (prefixPartial 12 26171) = false := by
  decide +kernel

theorem node_context_12_26171_329349 : EJMOriginalGlobalDAGData.nodes 9 ⟨329349, by decide⟩ =
    .split (coordinate 12) (![⟨329281, by decide⟩,⟨329330, by decide⟩,⟨329344, by decide⟩,⟨329348, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26171_329349 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26171 ⟨329349, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26171
    ⟨329349, by decide⟩ (by decide) (![⟨329281, by decide⟩,⟨329330, by decide⟩,⟨329344, by decide⟩,⟨329348, by decide⟩]) unmarked_context_12_26171_329349 node_context_12_26171_329349
  intro a
  fin_cases a
  · exact context_13_104684_329281
  · exact context_13_104685_329330
  · exact context_13_104686_329344
  · exact context_13_104687_329348

theorem unmarked_context_11_6542_329350 : frontier 10 ⟨329350, by decide⟩
    (prefixCache 11 6542) (prefixPartial 11 6542) = false := by
  decide +kernel

theorem node_context_11_6542_329350 : EJMOriginalGlobalDAGData.nodes 10 ⟨329350, by decide⟩ =
    .split (coordinate 11) (![⟨329116, by decide⟩,⟨329184, by decide⟩,⟨329276, by decide⟩,⟨329349, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6542_329350 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6542 ⟨329350, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6542
    ⟨329350, by decide⟩ (by decide) (![⟨329116, by decide⟩,⟨329184, by decide⟩,⟨329276, by decide⟩,⟨329349, by decide⟩]) unmarked_context_11_6542_329350 node_context_11_6542_329350
  intro a
  fin_cases a
  · exact context_12_26168_329116
  · exact context_12_26169_329184
  · exact context_12_26170_329276
  · exact context_12_26171_329349

theorem selected_cut_12468 : selected 9 ⟨329395, by decide⟩
    (prefixPartial 12 26172) = some ⟨12, 2, 0, 329395, 26172, 3925, 65536⟩ := by
  decide +kernel

theorem context_12_26172_329395 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26172 ⟨329395, by decide⟩ :=
  accepted_of_selected 12 26172 ⟨329395, by decide⟩ ⟨12, 2, 0, 329395, 26172, 3925, 65536⟩
    (by decide) selected_cut_12468

theorem selected_cut_12469 : selected 8 ⟨329398, by decide⟩
    (prefixPartial 13 104692) = some ⟨13, 2, 0, 329398, 104692, 145, 16384⟩ := by
  decide +kernel

theorem context_13_104692_329398 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104692 ⟨329398, by decide⟩ :=
  accepted_of_selected 13 104692 ⟨329398, by decide⟩ ⟨13, 2, 0, 329398, 104692, 145, 16384⟩
    (by decide) selected_cut_12469

theorem selected_cut_12470 : selected 8 ⟨329437, by decide⟩
    (prefixPartial 13 104693) = some ⟨13, 2, 0, 329437, 104693, 2437, 16384⟩ := by
  decide +kernel

theorem context_13_104693_329437 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104693 ⟨329437, by decide⟩ :=
  accepted_of_selected 13 104693 ⟨329437, by decide⟩ ⟨13, 2, 0, 329437, 104693, 2437, 16384⟩
    (by decide) selected_cut_12470

theorem selected_cut_12471 : selected 8 ⟨329454, by decide⟩
    (prefixPartial 13 104694) = some ⟨13, 2, 0, 329454, 104694, 1317, 16384⟩ := by
  decide +kernel

theorem context_13_104694_329454 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104694 ⟨329454, by decide⟩ :=
  accepted_of_selected 13 104694 ⟨329454, by decide⟩ ⟨13, 2, 0, 329454, 104694, 1317, 16384⟩
    (by decide) selected_cut_12471

theorem selected_cut_12472 : selected 8 ⟨329460, by decide⟩
    (prefixPartial 13 104695) = some ⟨13, 2, 0, 329460, 104695, 753, 16384⟩ := by
  decide +kernel

theorem context_13_104695_329460 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104695 ⟨329460, by decide⟩ :=
  accepted_of_selected 13 104695 ⟨329460, by decide⟩ ⟨13, 2, 0, 329460, 104695, 753, 16384⟩
    (by decide) selected_cut_12472

theorem unmarked_context_12_26173_329461 : frontier 9 ⟨329461, by decide⟩
    (prefixCache 12 26173) (prefixPartial 12 26173) = false := by
  decide +kernel

theorem node_context_12_26173_329461 : EJMOriginalGlobalDAGData.nodes 9 ⟨329461, by decide⟩ =
    .split (coordinate 12) (![⟨329398, by decide⟩,⟨329437, by decide⟩,⟨329454, by decide⟩,⟨329460, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26173_329461 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26173 ⟨329461, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26173
    ⟨329461, by decide⟩ (by decide) (![⟨329398, by decide⟩,⟨329437, by decide⟩,⟨329454, by decide⟩,⟨329460, by decide⟩]) unmarked_context_12_26173_329461 node_context_12_26173_329461
  intro a
  fin_cases a
  · exact context_13_104692_329398
  · exact context_13_104693_329437
  · exact context_13_104694_329454
  · exact context_13_104695_329460

theorem selected_cut_12473 : selected 9 ⟨329519, by decide⟩
    (prefixPartial 12 26174) = some ⟨12, 2, 0, 329519, 26174, 3841, 65536⟩ := by
  decide +kernel

theorem context_12_26174_329519 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26174 ⟨329519, by decide⟩ :=
  accepted_of_selected 12 26174 ⟨329519, by decide⟩ ⟨12, 2, 0, 329519, 26174, 3841, 65536⟩
    (by decide) selected_cut_12473

theorem selected_cut_12474 : selected 8 ⟨329523, by decide⟩
    (prefixPartial 13 104700) = some ⟨13, 2, 0, 329523, 104700, 61, 16384⟩ := by
  decide +kernel

theorem context_13_104700_329523 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104700 ⟨329523, by decide⟩ :=
  accepted_of_selected 13 104700 ⟨329523, by decide⟩ ⟨13, 2, 0, 329523, 104700, 61, 16384⟩
    (by decide) selected_cut_12474

theorem selected_cut_12475 : selected 8 ⟨329567, by decide⟩
    (prefixPartial 13 104701) = some ⟨13, 2, 0, 329567, 104701, 2637, 16384⟩ := by
  decide +kernel

theorem context_13_104701_329567 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104701 ⟨329567, by decide⟩ :=
  accepted_of_selected 13 104701 ⟨329567, by decide⟩ ⟨13, 2, 0, 329567, 104701, 2637, 16384⟩
    (by decide) selected_cut_12475

theorem selected_cut_12476 : selected 8 ⟨329586, by decide⟩
    (prefixPartial 13 104702) = some ⟨13, 2, 0, 329586, 104702, 1393, 16384⟩ := by
  decide +kernel

theorem context_13_104702_329586 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104702 ⟨329586, by decide⟩ :=
  accepted_of_selected 13 104702 ⟨329586, by decide⟩ ⟨13, 2, 0, 329586, 104702, 1393, 16384⟩
    (by decide) selected_cut_12476

theorem selected_cut_12477 : selected 8 ⟨329591, by decide⟩
    (prefixPartial 13 104703) = some ⟨13, 2, 0, 329591, 104703, 813, 16384⟩ := by
  decide +kernel

theorem context_13_104703_329591 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104703 ⟨329591, by decide⟩ :=
  accepted_of_selected 13 104703 ⟨329591, by decide⟩ ⟨13, 2, 0, 329591, 104703, 813, 16384⟩
    (by decide) selected_cut_12477

theorem unmarked_context_12_26175_329592 : frontier 9 ⟨329592, by decide⟩
    (prefixCache 12 26175) (prefixPartial 12 26175) = false := by
  decide +kernel

theorem node_context_12_26175_329592 : EJMOriginalGlobalDAGData.nodes 9 ⟨329592, by decide⟩ =
    .split (coordinate 12) (![⟨329523, by decide⟩,⟨329567, by decide⟩,⟨329586, by decide⟩,⟨329591, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26175_329592 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26175 ⟨329592, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26175
    ⟨329592, by decide⟩ (by decide) (![⟨329523, by decide⟩,⟨329567, by decide⟩,⟨329586, by decide⟩,⟨329591, by decide⟩]) unmarked_context_12_26175_329592 node_context_12_26175_329592
  intro a
  fin_cases a
  · exact context_13_104700_329523
  · exact context_13_104701_329567
  · exact context_13_104702_329586
  · exact context_13_104703_329591

theorem unmarked_context_11_6543_329593 : frontier 10 ⟨329593, by decide⟩
    (prefixCache 11 6543) (prefixPartial 11 6543) = false := by
  decide +kernel

theorem node_context_11_6543_329593 : EJMOriginalGlobalDAGData.nodes 10 ⟨329593, by decide⟩ =
    .split (coordinate 11) (![⟨329395, by decide⟩,⟨329461, by decide⟩,⟨329519, by decide⟩,⟨329592, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6543_329593 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6543 ⟨329593, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6543
    ⟨329593, by decide⟩ (by decide) (![⟨329395, by decide⟩,⟨329461, by decide⟩,⟨329519, by decide⟩,⟨329592, by decide⟩]) unmarked_context_11_6543_329593 node_context_11_6543_329593
  intro a
  fin_cases a
  · exact context_12_26172_329395
  · exact context_12_26173_329461
  · exact context_12_26174_329519
  · exact context_12_26175_329592

theorem unmarked_context_10_1635_329594 : frontier 11 ⟨329594, by decide⟩
    (prefixCache 10 1635) (prefixPartial 10 1635) = false := by
  decide +kernel

theorem node_context_10_1635_329594 : EJMOriginalGlobalDAGData.nodes 11 ⟨329594, by decide⟩ =
    .split (coordinate 10) (![⟨328826, by decide⟩,⟨329058, by decide⟩,⟨329350, by decide⟩,⟨329593, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1635_329594 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1635 ⟨329594, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1635
    ⟨329594, by decide⟩ (by decide) (![⟨328826, by decide⟩,⟨329058, by decide⟩,⟨329350, by decide⟩,⟨329593, by decide⟩]) unmarked_context_10_1635_329594 node_context_10_1635_329594
  intro a
  fin_cases a
  · exact context_11_6540_328826
  · exact context_11_6541_329058
  · exact context_11_6542_329350
  · exact context_11_6543_329593

theorem unmarked_context_9_408_329595 : frontier 12 ⟨329595, by decide⟩
    (prefixCache 9 408) (prefixPartial 9 408) = false := by
  decide +kernel

theorem node_context_9_408_329595 : EJMOriginalGlobalDAGData.nodes 12 ⟨329595, by decide⟩ =
    .split (coordinate 9) (![⟨326191, by decide⟩,⟨327531, by decide⟩,⟨328556, by decide⟩,⟨329594, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_408_329595 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 408 ⟨329595, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 408
    ⟨329595, by decide⟩ (by decide) (![⟨326191, by decide⟩,⟨327531, by decide⟩,⟨328556, by decide⟩,⟨329594, by decide⟩]) unmarked_context_9_408_329595 node_context_9_408_329595
  intro a
  fin_cases a
  · exact context_10_1632_326191
  · exact context_10_1633_327531
  · exact context_10_1634_328556
  · exact context_10_1635_329594

theorem selected_cut_12478 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 104704) = some ⟨13, 1, 0, 3444, 104704, 1, 16384⟩ := by
  decide +kernel

theorem context_13_104704_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104704 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 104704 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 104704, 1, 16384⟩
    (by decide) selected_cut_12478

theorem selected_cut_12479 : selected 8 ⟨329619, by decide⟩
    (prefixPartial 13 104705) = some ⟨13, 2, 0, 329619, 104705, 2541, 16384⟩ := by
  decide +kernel

theorem context_13_104705_329619 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104705 ⟨329619, by decide⟩ :=
  accepted_of_selected 13 104705 ⟨329619, by decide⟩ ⟨13, 2, 0, 329619, 104705, 2541, 16384⟩
    (by decide) selected_cut_12479

theorem selected_cut_12480 : selected 8 ⟨329640, by decide⟩
    (prefixPartial 13 104706) = some ⟨13, 2, 0, 329640, 104706, 1349, 16384⟩ := by
  decide +kernel

theorem context_13_104706_329640 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104706 ⟨329640, by decide⟩ :=
  accepted_of_selected 13 104706 ⟨329640, by decide⟩ ⟨13, 2, 0, 329640, 104706, 1349, 16384⟩
    (by decide) selected_cut_12480

theorem selected_cut_12481 : selected 8 ⟨329646, by decide⟩
    (prefixPartial 13 104707) = some ⟨13, 2, 0, 329646, 104707, 765, 16384⟩ := by
  decide +kernel

theorem context_13_104707_329646 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104707 ⟨329646, by decide⟩ :=
  accepted_of_selected 13 104707 ⟨329646, by decide⟩ ⟨13, 2, 0, 329646, 104707, 765, 16384⟩
    (by decide) selected_cut_12481

theorem unmarked_context_12_26176_329647 : frontier 9 ⟨329647, by decide⟩
    (prefixCache 12 26176) (prefixPartial 12 26176) = false := by
  decide +kernel

theorem node_context_12_26176_329647 : EJMOriginalGlobalDAGData.nodes 9 ⟨329647, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨329619, by decide⟩,⟨329640, by decide⟩,⟨329646, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26176_329647 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26176 ⟨329647, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26176
    ⟨329647, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨329619, by decide⟩,⟨329640, by decide⟩,⟨329646, by decide⟩]) unmarked_context_12_26176_329647 node_context_12_26176_329647
  intro a
  fin_cases a
  · exact context_13_104704_3444
  · exact context_13_104705_329619
  · exact context_13_104706_329640
  · exact context_13_104707_329646

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
