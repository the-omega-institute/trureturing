/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover213
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_20547 : selected 8 ⟨527015, by decide⟩
    (prefixPartial 13 296151) = some ⟨13, 2, 0, 527015, 296151, 1341, 16384⟩ := by
  decide +kernel

theorem context_13_296151_527015 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296151 ⟨527015, by decide⟩ :=
  accepted_of_selected 13 296151 ⟨527015, by decide⟩ ⟨13, 2, 0, 527015, 296151, 1341, 16384⟩
    (by decide) selected_cut_20547

theorem unmarked_context_12_74037_527016 : frontier 9 ⟨527016, by decide⟩
    (prefixCache 12 74037) (prefixPartial 12 74037) = false := by
  decide +kernel

theorem node_context_12_74037_527016 : EJMOriginalGlobalDAGData.nodes 9 ⟨527016, by decide⟩ =
    .split (coordinate 12) (![⟨526932, by decide⟩,⟨526964, by decide⟩,⟨527002, by decide⟩,⟨527015, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74037_527016 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74037 ⟨527016, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74037
    ⟨527016, by decide⟩ (by decide) (![⟨526932, by decide⟩,⟨526964, by decide⟩,⟨527002, by decide⟩,⟨527015, by decide⟩]) unmarked_context_12_74037_527016 node_context_12_74037_527016
  intro a
  fin_cases a
  · exact context_13_296148_526932
  · exact context_13_296149_526964
  · exact context_13_296150_527002
  · exact context_13_296151_527015

theorem selected_cut_20548 : selected 8 ⟨527026, by decide⟩
    (prefixPartial 13 296152) = some ⟨13, 2, 0, 527026, 296152, 405, 16384⟩ := by
  decide +kernel

theorem context_13_296152_527026 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296152 ⟨527026, by decide⟩ :=
  accepted_of_selected 13 296152 ⟨527026, by decide⟩ ⟨13, 2, 0, 527026, 296152, 405, 16384⟩
    (by decide) selected_cut_20548

theorem selected_cut_20549 : selected 8 ⟨527052, by decide⟩
    (prefixPartial 13 296153) = some ⟨13, 2, 0, 527052, 296153, 1769, 16384⟩ := by
  decide +kernel

theorem context_13_296153_527052 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296153 ⟨527052, by decide⟩ :=
  accepted_of_selected 13 296153 ⟨527052, by decide⟩ ⟨13, 2, 0, 527052, 296153, 1769, 16384⟩
    (by decide) selected_cut_20549

theorem selected_cut_20550 : selected 8 ⟨527067, by decide⟩
    (prefixPartial 13 296154) = some ⟨13, 2, 0, 527067, 296154, 1153, 16384⟩ := by
  decide +kernel

theorem context_13_296154_527067 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296154 ⟨527067, by decide⟩ :=
  accepted_of_selected 13 296154 ⟨527067, by decide⟩ ⟨13, 2, 0, 527067, 296154, 1153, 16384⟩
    (by decide) selected_cut_20550

theorem selected_cut_20551 : selected 8 ⟨527075, by decide⟩
    (prefixPartial 13 296155) = some ⟨13, 2, 0, 527075, 296155, 837, 16384⟩ := by
  decide +kernel

theorem context_13_296155_527075 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296155 ⟨527075, by decide⟩ :=
  accepted_of_selected 13 296155 ⟨527075, by decide⟩ ⟨13, 2, 0, 527075, 296155, 837, 16384⟩
    (by decide) selected_cut_20551

theorem unmarked_context_12_74038_527076 : frontier 9 ⟨527076, by decide⟩
    (prefixCache 12 74038) (prefixPartial 12 74038) = false := by
  decide +kernel

theorem node_context_12_74038_527076 : EJMOriginalGlobalDAGData.nodes 9 ⟨527076, by decide⟩ =
    .split (coordinate 12) (![⟨527026, by decide⟩,⟨527052, by decide⟩,⟨527067, by decide⟩,⟨527075, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74038_527076 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74038 ⟨527076, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74038
    ⟨527076, by decide⟩ (by decide) (![⟨527026, by decide⟩,⟨527052, by decide⟩,⟨527067, by decide⟩,⟨527075, by decide⟩]) unmarked_context_12_74038_527076 node_context_12_74038_527076
  intro a
  fin_cases a
  · exact context_13_296152_527026
  · exact context_13_296153_527052
  · exact context_13_296154_527067
  · exact context_13_296155_527075

theorem selected_cut_20552 : selected 8 ⟨527086, by decide⟩
    (prefixPartial 13 296156) = some ⟨13, 2, 0, 527086, 296156, 385, 16384⟩ := by
  decide +kernel

theorem context_13_296156_527086 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296156 ⟨527086, by decide⟩ :=
  accepted_of_selected 13 296156 ⟨527086, by decide⟩ ⟨13, 2, 0, 527086, 296156, 385, 16384⟩
    (by decide) selected_cut_20552

theorem selected_cut_20553 : selected 8 ⟨527113, by decide⟩
    (prefixPartial 13 296157) = some ⟨13, 2, 0, 527113, 296157, 1973, 16384⟩ := by
  decide +kernel

theorem context_13_296157_527113 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296157 ⟨527113, by decide⟩ :=
  accepted_of_selected 13 296157 ⟨527113, by decide⟩ ⟨13, 2, 0, 527113, 296157, 1973, 16384⟩
    (by decide) selected_cut_20553

theorem selected_cut_20554 : selected 8 ⟨527134, by decide⟩
    (prefixPartial 13 296158) = some ⟨13, 2, 0, 527134, 296158, 1569, 16384⟩ := by
  decide +kernel

theorem context_13_296158_527134 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296158 ⟨527134, by decide⟩ :=
  accepted_of_selected 13 296158 ⟨527134, by decide⟩ ⟨13, 2, 0, 527134, 296158, 1569, 16384⟩
    (by decide) selected_cut_20554

theorem selected_cut_20555 : selected 8 ⟨527138, by decide⟩
    (prefixPartial 13 296159) = some ⟨13, 2, 0, 527138, 296159, 613, 16384⟩ := by
  decide +kernel

theorem context_13_296159_527138 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296159 ⟨527138, by decide⟩ :=
  accepted_of_selected 13 296159 ⟨527138, by decide⟩ ⟨13, 2, 0, 527138, 296159, 613, 16384⟩
    (by decide) selected_cut_20555

theorem unmarked_context_12_74039_527139 : frontier 9 ⟨527139, by decide⟩
    (prefixCache 12 74039) (prefixPartial 12 74039) = false := by
  decide +kernel

theorem node_context_12_74039_527139 : EJMOriginalGlobalDAGData.nodes 9 ⟨527139, by decide⟩ =
    .split (coordinate 12) (![⟨527086, by decide⟩,⟨527113, by decide⟩,⟨527134, by decide⟩,⟨527138, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74039_527139 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74039 ⟨527139, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74039
    ⟨527139, by decide⟩ (by decide) (![⟨527086, by decide⟩,⟨527113, by decide⟩,⟨527134, by decide⟩,⟨527138, by decide⟩]) unmarked_context_12_74039_527139 node_context_12_74039_527139
  intro a
  fin_cases a
  · exact context_13_296156_527086
  · exact context_13_296157_527113
  · exact context_13_296158_527134
  · exact context_13_296159_527138

theorem unmarked_context_11_18509_527140 : frontier 10 ⟨527140, by decide⟩
    (prefixCache 11 18509) (prefixPartial 11 18509) = false := by
  decide +kernel

theorem node_context_11_18509_527140 : EJMOriginalGlobalDAGData.nodes 10 ⟨527140, by decide⟩ =
    .split (coordinate 11) (![⟨526918, by decide⟩,⟨527016, by decide⟩,⟨527076, by decide⟩,⟨527139, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18509_527140 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18509 ⟨527140, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18509
    ⟨527140, by decide⟩ (by decide) (![⟨526918, by decide⟩,⟨527016, by decide⟩,⟨527076, by decide⟩,⟨527139, by decide⟩]) unmarked_context_11_18509_527140 node_context_11_18509_527140
  intro a
  fin_cases a
  · exact context_12_74036_526918
  · exact context_12_74037_527016
  · exact context_12_74038_527076
  · exact context_12_74039_527139

theorem selected_cut_20556 : selected 8 ⟨527152, by decide⟩
    (prefixPartial 13 296160) = some ⟨13, 2, 0, 527152, 296160, 457, 16384⟩ := by
  decide +kernel

theorem context_13_296160_527152 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296160 ⟨527152, by decide⟩ :=
  accepted_of_selected 13 296160 ⟨527152, by decide⟩ ⟨13, 2, 0, 527152, 296160, 457, 16384⟩
    (by decide) selected_cut_20556

theorem selected_cut_20557 : selected 8 ⟨527188, by decide⟩
    (prefixPartial 13 296161) = some ⟨13, 2, 0, 527188, 296161, 2969, 16384⟩ := by
  decide +kernel

theorem context_13_296161_527188 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296161 ⟨527188, by decide⟩ :=
  accepted_of_selected 13 296161 ⟨527188, by decide⟩ ⟨13, 2, 0, 527188, 296161, 2969, 16384⟩
    (by decide) selected_cut_20557

theorem selected_cut_20558 : selected 8 ⟨527208, by decide⟩
    (prefixPartial 13 296162) = some ⟨13, 2, 0, 527208, 296162, 2113, 16384⟩ := by
  decide +kernel

theorem context_13_296162_527208 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296162 ⟨527208, by decide⟩ :=
  accepted_of_selected 13 296162 ⟨527208, by decide⟩ ⟨13, 2, 0, 527208, 296162, 2113, 16384⟩
    (by decide) selected_cut_20558

theorem selected_cut_20559 : selected 8 ⟨527214, by decide⟩
    (prefixPartial 13 296163) = some ⟨13, 2, 0, 527214, 296163, 993, 16384⟩ := by
  decide +kernel

theorem context_13_296163_527214 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296163 ⟨527214, by decide⟩ :=
  accepted_of_selected 13 296163 ⟨527214, by decide⟩ ⟨13, 2, 0, 527214, 296163, 993, 16384⟩
    (by decide) selected_cut_20559

theorem unmarked_context_12_74040_527215 : frontier 9 ⟨527215, by decide⟩
    (prefixCache 12 74040) (prefixPartial 12 74040) = false := by
  decide +kernel

theorem node_context_12_74040_527215 : EJMOriginalGlobalDAGData.nodes 9 ⟨527215, by decide⟩ =
    .split (coordinate 12) (![⟨527152, by decide⟩,⟨527188, by decide⟩,⟨527208, by decide⟩,⟨527214, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74040_527215 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74040 ⟨527215, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74040
    ⟨527215, by decide⟩ (by decide) (![⟨527152, by decide⟩,⟨527188, by decide⟩,⟨527208, by decide⟩,⟨527214, by decide⟩]) unmarked_context_12_74040_527215 node_context_12_74040_527215
  intro a
  fin_cases a
  · exact context_13_296160_527152
  · exact context_13_296161_527188
  · exact context_13_296162_527208
  · exact context_13_296163_527214

theorem selected_cut_20560 : selected 8 ⟨527223, by decide⟩
    (prefixPartial 13 296164) = some ⟨13, 2, 0, 527223, 296164, 317, 16384⟩ := by
  decide +kernel

theorem context_13_296164_527223 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296164 ⟨527223, by decide⟩ :=
  accepted_of_selected 13 296164 ⟨527223, by decide⟩ ⟨13, 2, 0, 527223, 296164, 317, 16384⟩
    (by decide) selected_cut_20560

theorem selected_cut_20561 : selected 8 ⟨527249, by decide⟩
    (prefixPartial 13 296165) = some ⟨13, 2, 0, 527249, 296165, 1745, 16384⟩ := by
  decide +kernel

theorem context_13_296165_527249 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296165 ⟨527249, by decide⟩ :=
  accepted_of_selected 13 296165 ⟨527249, by decide⟩ ⟨13, 2, 0, 527249, 296165, 1745, 16384⟩
    (by decide) selected_cut_20561

theorem selected_cut_20562 : selected 8 ⟨527271, by decide⟩
    (prefixPartial 13 296166) = some ⟨13, 2, 0, 527271, 296166, 1905, 16384⟩ := by
  decide +kernel

theorem context_13_296166_527271 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296166 ⟨527271, by decide⟩ :=
  accepted_of_selected 13 296166 ⟨527271, by decide⟩ ⟨13, 2, 0, 527271, 296166, 1905, 16384⟩
    (by decide) selected_cut_20562

theorem selected_cut_20563 : selected 8 ⟨527278, by decide⟩
    (prefixPartial 13 296167) = some ⟨13, 2, 0, 527278, 296167, 957, 16384⟩ := by
  decide +kernel

theorem context_13_296167_527278 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296167 ⟨527278, by decide⟩ :=
  accepted_of_selected 13 296167 ⟨527278, by decide⟩ ⟨13, 2, 0, 527278, 296167, 957, 16384⟩
    (by decide) selected_cut_20563

theorem unmarked_context_12_74041_527279 : frontier 9 ⟨527279, by decide⟩
    (prefixCache 12 74041) (prefixPartial 12 74041) = false := by
  decide +kernel

theorem node_context_12_74041_527279 : EJMOriginalGlobalDAGData.nodes 9 ⟨527279, by decide⟩ =
    .split (coordinate 12) (![⟨527223, by decide⟩,⟨527249, by decide⟩,⟨527271, by decide⟩,⟨527278, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74041_527279 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74041 ⟨527279, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74041
    ⟨527279, by decide⟩ (by decide) (![⟨527223, by decide⟩,⟨527249, by decide⟩,⟨527271, by decide⟩,⟨527278, by decide⟩]) unmarked_context_12_74041_527279 node_context_12_74041_527279
  intro a
  fin_cases a
  · exact context_13_296164_527223
  · exact context_13_296165_527249
  · exact context_13_296166_527271
  · exact context_13_296167_527278

theorem selected_cut_20564 : selected 8 ⟨527285, by decide⟩
    (prefixPartial 13 296168) = some ⟨13, 2, 0, 527285, 296168, 209, 16384⟩ := by
  decide +kernel

theorem context_13_296168_527285 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296168 ⟨527285, by decide⟩ :=
  accepted_of_selected 13 296168 ⟨527285, by decide⟩ ⟨13, 2, 0, 527285, 296168, 209, 16384⟩
    (by decide) selected_cut_20564

theorem selected_cut_20565 : selected 8 ⟨527310, by decide⟩
    (prefixPartial 13 296169) = some ⟨13, 2, 0, 527310, 296169, 1953, 16384⟩ := by
  decide +kernel

theorem context_13_296169_527310 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296169 ⟨527310, by decide⟩ :=
  accepted_of_selected 13 296169 ⟨527310, by decide⟩ ⟨13, 2, 0, 527310, 296169, 1953, 16384⟩
    (by decide) selected_cut_20565

theorem selected_cut_20566 : selected 8 ⟨527328, by decide⟩
    (prefixPartial 13 296170) = some ⟨13, 2, 0, 527328, 296170, 1297, 16384⟩ := by
  decide +kernel

theorem context_13_296170_527328 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296170 ⟨527328, by decide⟩ :=
  accepted_of_selected 13 296170 ⟨527328, by decide⟩ ⟨13, 2, 0, 527328, 296170, 1297, 16384⟩
    (by decide) selected_cut_20566

theorem selected_cut_20567 : selected 8 ⟨527336, by decide⟩
    (prefixPartial 13 296171) = some ⟨13, 2, 0, 527336, 296171, 805, 16384⟩ := by
  decide +kernel

theorem context_13_296171_527336 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296171 ⟨527336, by decide⟩ :=
  accepted_of_selected 13 296171 ⟨527336, by decide⟩ ⟨13, 2, 0, 527336, 296171, 805, 16384⟩
    (by decide) selected_cut_20567

theorem unmarked_context_12_74042_527337 : frontier 9 ⟨527337, by decide⟩
    (prefixCache 12 74042) (prefixPartial 12 74042) = false := by
  decide +kernel

theorem node_context_12_74042_527337 : EJMOriginalGlobalDAGData.nodes 9 ⟨527337, by decide⟩ =
    .split (coordinate 12) (![⟨527285, by decide⟩,⟨527310, by decide⟩,⟨527328, by decide⟩,⟨527336, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74042_527337 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74042 ⟨527337, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74042
    ⟨527337, by decide⟩ (by decide) (![⟨527285, by decide⟩,⟨527310, by decide⟩,⟨527328, by decide⟩,⟨527336, by decide⟩]) unmarked_context_12_74042_527337 node_context_12_74042_527337
  intro a
  fin_cases a
  · exact context_13_296168_527285
  · exact context_13_296169_527310
  · exact context_13_296170_527328
  · exact context_13_296171_527336

theorem selected_cut_20568 : selected 8 ⟨527345, by decide⟩
    (prefixPartial 13 296172) = some ⟨13, 2, 0, 527345, 296172, 177, 16384⟩ := by
  decide +kernel

theorem context_13_296172_527345 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296172 ⟨527345, by decide⟩ :=
  accepted_of_selected 13 296172 ⟨527345, by decide⟩ ⟨13, 2, 0, 527345, 296172, 177, 16384⟩
    (by decide) selected_cut_20568

theorem selected_cut_20569 : selected 8 ⟨527371, by decide⟩
    (prefixPartial 13 296173) = some ⟨13, 2, 0, 527371, 296173, 2161, 16384⟩ := by
  decide +kernel

theorem context_13_296173_527371 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296173 ⟨527371, by decide⟩ :=
  accepted_of_selected 13 296173 ⟨527371, by decide⟩ ⟨13, 2, 0, 527371, 296173, 2161, 16384⟩
    (by decide) selected_cut_20569

theorem selected_cut_20570 : selected 8 ⟨527392, by decide⟩
    (prefixPartial 13 296174) = some ⟨13, 2, 0, 527392, 296174, 1645, 16384⟩ := by
  decide +kernel

theorem context_13_296174_527392 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296174 ⟨527392, by decide⟩ :=
  accepted_of_selected 13 296174 ⟨527392, by decide⟩ ⟨13, 2, 0, 527392, 296174, 1645, 16384⟩
    (by decide) selected_cut_20570

theorem selected_cut_20571 : selected 8 ⟨527398, by decide⟩
    (prefixPartial 13 296175) = some ⟨13, 2, 0, 527398, 296175, 613, 16384⟩ := by
  decide +kernel

theorem context_13_296175_527398 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296175 ⟨527398, by decide⟩ :=
  accepted_of_selected 13 296175 ⟨527398, by decide⟩ ⟨13, 2, 0, 527398, 296175, 613, 16384⟩
    (by decide) selected_cut_20571

theorem unmarked_context_12_74043_527399 : frontier 9 ⟨527399, by decide⟩
    (prefixCache 12 74043) (prefixPartial 12 74043) = false := by
  decide +kernel

theorem node_context_12_74043_527399 : EJMOriginalGlobalDAGData.nodes 9 ⟨527399, by decide⟩ =
    .split (coordinate 12) (![⟨527345, by decide⟩,⟨527371, by decide⟩,⟨527392, by decide⟩,⟨527398, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74043_527399 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74043 ⟨527399, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74043
    ⟨527399, by decide⟩ (by decide) (![⟨527345, by decide⟩,⟨527371, by decide⟩,⟨527392, by decide⟩,⟨527398, by decide⟩]) unmarked_context_12_74043_527399 node_context_12_74043_527399
  intro a
  fin_cases a
  · exact context_13_296172_527345
  · exact context_13_296173_527371
  · exact context_13_296174_527392
  · exact context_13_296175_527398

theorem unmarked_context_11_18510_527400 : frontier 10 ⟨527400, by decide⟩
    (prefixCache 11 18510) (prefixPartial 11 18510) = false := by
  decide +kernel

theorem node_context_11_18510_527400 : EJMOriginalGlobalDAGData.nodes 10 ⟨527400, by decide⟩ =
    .split (coordinate 11) (![⟨527215, by decide⟩,⟨527279, by decide⟩,⟨527337, by decide⟩,⟨527399, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18510_527400 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18510 ⟨527400, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18510
    ⟨527400, by decide⟩ (by decide) (![⟨527215, by decide⟩,⟨527279, by decide⟩,⟨527337, by decide⟩,⟨527399, by decide⟩]) unmarked_context_11_18510_527400 node_context_11_18510_527400
  intro a
  fin_cases a
  · exact context_12_74040_527215
  · exact context_12_74041_527279
  · exact context_12_74042_527337
  · exact context_12_74043_527399

theorem selected_cut_20572 : selected 9 ⟨445562, by decide⟩
    (prefixPartial 12 74044) = some ⟨12, 1, 0, 445562, 74044, 1, 65536⟩ := by
  decide +kernel

theorem context_12_74044_445562 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74044 ⟨445562, by decide⟩ :=
  accepted_of_selected 12 74044 ⟨445562, by decide⟩ ⟨12, 1, 0, 445562, 74044, 1, 65536⟩
    (by decide) selected_cut_20572

theorem selected_cut_20573 : selected 8 ⟨527404, by decide⟩
    (prefixPartial 13 296180) = some ⟨13, 2, 0, 527404, 296180, 101, 16384⟩ := by
  decide +kernel

theorem context_13_296180_527404 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296180 ⟨527404, by decide⟩ :=
  accepted_of_selected 13 296180 ⟨527404, by decide⟩ ⟨13, 2, 0, 527404, 296180, 101, 16384⟩
    (by decide) selected_cut_20573

theorem selected_cut_20574 : selected 8 ⟨527429, by decide⟩
    (prefixPartial 13 296181) = some ⟨13, 2, 0, 527429, 296181, 2005, 16384⟩ := by
  decide +kernel

theorem context_13_296181_527429 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296181 ⟨527429, by decide⟩ :=
  accepted_of_selected 13 296181 ⟨527429, by decide⟩ ⟨13, 2, 0, 527429, 296181, 2005, 16384⟩
    (by decide) selected_cut_20574

theorem selected_cut_20575 : selected 8 ⟨527448, by decide⟩
    (prefixPartial 13 296182) = some ⟨13, 2, 0, 527448, 296182, 1925, 16384⟩ := by
  decide +kernel

theorem context_13_296182_527448 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296182 ⟨527448, by decide⟩ :=
  accepted_of_selected 13 296182 ⟨527448, by decide⟩ ⟨13, 2, 0, 527448, 296182, 1925, 16384⟩
    (by decide) selected_cut_20575

theorem selected_cut_20576 : selected 8 ⟨527456, by decide⟩
    (prefixPartial 13 296183) = some ⟨13, 2, 0, 527456, 296183, 913, 16384⟩ := by
  decide +kernel

theorem context_13_296183_527456 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296183 ⟨527456, by decide⟩ :=
  accepted_of_selected 13 296183 ⟨527456, by decide⟩ ⟨13, 2, 0, 527456, 296183, 913, 16384⟩
    (by decide) selected_cut_20576

theorem unmarked_context_12_74045_527457 : frontier 9 ⟨527457, by decide⟩
    (prefixCache 12 74045) (prefixPartial 12 74045) = false := by
  decide +kernel

theorem node_context_12_74045_527457 : EJMOriginalGlobalDAGData.nodes 9 ⟨527457, by decide⟩ =
    .split (coordinate 12) (![⟨527404, by decide⟩,⟨527429, by decide⟩,⟨527448, by decide⟩,⟨527456, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74045_527457 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74045 ⟨527457, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74045
    ⟨527457, by decide⟩ (by decide) (![⟨527404, by decide⟩,⟨527429, by decide⟩,⟨527448, by decide⟩,⟨527456, by decide⟩]) unmarked_context_12_74045_527457 node_context_12_74045_527457
  intro a
  fin_cases a
  · exact context_13_296180_527404
  · exact context_13_296181_527429
  · exact context_13_296182_527448
  · exact context_13_296183_527456

theorem selected_cut_20577 : selected 8 ⟨527461, by decide⟩
    (prefixPartial 13 296184) = some ⟨13, 2, 0, 527461, 296184, 93, 16384⟩ := by
  decide +kernel

theorem context_13_296184_527461 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296184 ⟨527461, by decide⟩ :=
  accepted_of_selected 13 296184 ⟨527461, by decide⟩ ⟨13, 2, 0, 527461, 296184, 93, 16384⟩
    (by decide) selected_cut_20577

theorem selected_cut_20578 : selected 8 ⟨527488, by decide⟩
    (prefixPartial 13 296185) = some ⟨13, 2, 0, 527488, 296185, 2193, 16384⟩ := by
  decide +kernel

theorem context_13_296185_527488 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296185 ⟨527488, by decide⟩ :=
  accepted_of_selected 13 296185 ⟨527488, by decide⟩ ⟨13, 2, 0, 527488, 296185, 2193, 16384⟩
    (by decide) selected_cut_20578

theorem selected_cut_20579 : selected 8 ⟨527507, by decide⟩
    (prefixPartial 13 296186) = some ⟨13, 2, 0, 527507, 296186, 1329, 16384⟩ := by
  decide +kernel

theorem context_13_296186_527507 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296186 ⟨527507, by decide⟩ :=
  accepted_of_selected 13 296186 ⟨527507, by decide⟩ ⟨13, 2, 0, 527507, 296186, 1329, 16384⟩
    (by decide) selected_cut_20579

theorem selected_cut_20580 : selected 8 ⟨527518, by decide⟩
    (prefixPartial 13 296187) = some ⟨13, 2, 0, 527518, 296187, 909, 16384⟩ := by
  decide +kernel

theorem context_13_296187_527518 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296187 ⟨527518, by decide⟩ :=
  accepted_of_selected 13 296187 ⟨527518, by decide⟩ ⟨13, 2, 0, 527518, 296187, 909, 16384⟩
    (by decide) selected_cut_20580

theorem unmarked_context_12_74046_527519 : frontier 9 ⟨527519, by decide⟩
    (prefixCache 12 74046) (prefixPartial 12 74046) = false := by
  decide +kernel

theorem node_context_12_74046_527519 : EJMOriginalGlobalDAGData.nodes 9 ⟨527519, by decide⟩ =
    .split (coordinate 12) (![⟨527461, by decide⟩,⟨527488, by decide⟩,⟨527507, by decide⟩,⟨527518, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74046_527519 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74046 ⟨527519, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74046
    ⟨527519, by decide⟩ (by decide) (![⟨527461, by decide⟩,⟨527488, by decide⟩,⟨527507, by decide⟩,⟨527518, by decide⟩]) unmarked_context_12_74046_527519 node_context_12_74046_527519
  intro a
  fin_cases a
  · exact context_13_296184_527461
  · exact context_13_296185_527488
  · exact context_13_296186_527507
  · exact context_13_296187_527518

theorem selected_cut_20581 : selected 8 ⟨527523, by decide⟩
    (prefixPartial 13 296188) = some ⟨13, 2, 0, 527523, 296188, 57, 16384⟩ := by
  decide +kernel

theorem context_13_296188_527523 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296188 ⟨527523, by decide⟩ :=
  accepted_of_selected 13 296188 ⟨527523, by decide⟩ ⟨13, 2, 0, 527523, 296188, 57, 16384⟩
    (by decide) selected_cut_20581

theorem selected_cut_20582 : selected 8 ⟨527552, by decide⟩
    (prefixPartial 13 296189) = some ⟨13, 2, 0, 527552, 296189, 2397, 16384⟩ := by
  decide +kernel

theorem context_13_296189_527552 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296189 ⟨527552, by decide⟩ :=
  accepted_of_selected 13 296189 ⟨527552, by decide⟩ ⟨13, 2, 0, 527552, 296189, 2397, 16384⟩
    (by decide) selected_cut_20582

theorem selected_cut_20583 : selected 8 ⟨527573, by decide⟩
    (prefixPartial 13 296190) = some ⟨13, 2, 0, 527573, 296190, 1701, 16384⟩ := by
  decide +kernel

theorem context_13_296190_527573 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296190 ⟨527573, by decide⟩ :=
  accepted_of_selected 13 296190 ⟨527573, by decide⟩ ⟨13, 2, 0, 527573, 296190, 1701, 16384⟩
    (by decide) selected_cut_20583

theorem selected_cut_20584 : selected 8 ⟨527578, by decide⟩
    (prefixPartial 13 296191) = some ⟨13, 2, 0, 527578, 296191, 637, 16384⟩ := by
  decide +kernel

theorem context_13_296191_527578 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296191 ⟨527578, by decide⟩ :=
  accepted_of_selected 13 296191 ⟨527578, by decide⟩ ⟨13, 2, 0, 527578, 296191, 637, 16384⟩
    (by decide) selected_cut_20584

theorem unmarked_context_12_74047_527579 : frontier 9 ⟨527579, by decide⟩
    (prefixCache 12 74047) (prefixPartial 12 74047) = false := by
  decide +kernel

theorem node_context_12_74047_527579 : EJMOriginalGlobalDAGData.nodes 9 ⟨527579, by decide⟩ =
    .split (coordinate 12) (![⟨527523, by decide⟩,⟨527552, by decide⟩,⟨527573, by decide⟩,⟨527578, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74047_527579 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74047 ⟨527579, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74047
    ⟨527579, by decide⟩ (by decide) (![⟨527523, by decide⟩,⟨527552, by decide⟩,⟨527573, by decide⟩,⟨527578, by decide⟩]) unmarked_context_12_74047_527579 node_context_12_74047_527579
  intro a
  fin_cases a
  · exact context_13_296188_527523
  · exact context_13_296189_527552
  · exact context_13_296190_527573
  · exact context_13_296191_527578

theorem unmarked_context_11_18511_527580 : frontier 10 ⟨527580, by decide⟩
    (prefixCache 11 18511) (prefixPartial 11 18511) = false := by
  decide +kernel

theorem node_context_11_18511_527580 : EJMOriginalGlobalDAGData.nodes 10 ⟨527580, by decide⟩ =
    .split (coordinate 11) (![⟨445562, by decide⟩,⟨527457, by decide⟩,⟨527519, by decide⟩,⟨527579, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18511_527580 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18511 ⟨527580, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18511
    ⟨527580, by decide⟩ (by decide) (![⟨445562, by decide⟩,⟨527457, by decide⟩,⟨527519, by decide⟩,⟨527579, by decide⟩]) unmarked_context_11_18511_527580 node_context_11_18511_527580
  intro a
  fin_cases a
  · exact context_12_74044_445562
  · exact context_12_74045_527457
  · exact context_12_74046_527519
  · exact context_12_74047_527579

theorem unmarked_context_10_4627_527581 : frontier 11 ⟨527581, by decide⟩
    (prefixCache 10 4627) (prefixPartial 10 4627) = false := by
  decide +kernel

theorem node_context_10_4627_527581 : EJMOriginalGlobalDAGData.nodes 11 ⟨527581, by decide⟩ =
    .split (coordinate 10) (![⟨526853, by decide⟩,⟨527140, by decide⟩,⟨527400, by decide⟩,⟨527580, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4627_527581 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4627 ⟨527581, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4627
    ⟨527581, by decide⟩ (by decide) (![⟨526853, by decide⟩,⟨527140, by decide⟩,⟨527400, by decide⟩,⟨527580, by decide⟩]) unmarked_context_10_4627_527581 node_context_10_4627_527581
  intro a
  fin_cases a
  · exact context_11_18508_526853
  · exact context_11_18509_527140
  · exact context_11_18510_527400
  · exact context_11_18511_527580

theorem unmarked_context_9_1156_527582 : frontier 12 ⟨527582, by decide⟩
    (prefixCache 9 1156) (prefixPartial 9 1156) = false := by
  decide +kernel

theorem node_context_9_1156_527582 : EJMOriginalGlobalDAGData.nodes 12 ⟨527582, by decide⟩ =
    .split (coordinate 9) (![⟨524650, by decide⟩,⟨525636, by decide⟩,⟨526660, by decide⟩,⟨527581, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1156_527582 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1156 ⟨527582, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1156
    ⟨527582, by decide⟩ (by decide) (![⟨524650, by decide⟩,⟨525636, by decide⟩,⟨526660, by decide⟩,⟨527581, by decide⟩]) unmarked_context_9_1156_527582 node_context_9_1156_527582
  intro a
  fin_cases a
  · exact context_10_4624_524650
  · exact context_10_4625_525636
  · exact context_10_4626_526660
  · exact context_10_4627_527581

theorem selected_cut_20585 : selected 9 ⟨527583, by decide⟩
    (prefixPartial 12 74048) = some ⟨12, 1, 0, 527583, 74048, 1, 65536⟩ := by
  decide +kernel

theorem context_12_74048_527583 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74048 ⟨527583, by decide⟩ :=
  accepted_of_selected 12 74048 ⟨527583, by decide⟩ ⟨12, 1, 0, 527583, 74048, 1, 65536⟩
    (by decide) selected_cut_20585

theorem selected_cut_20586 : selected 9 ⟨527583, by decide⟩
    (prefixPartial 12 74049) = some ⟨12, 1, 0, 527583, 74049, 1, 65536⟩ := by
  decide +kernel

theorem context_12_74049_527583 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74049 ⟨527583, by decide⟩ :=
  accepted_of_selected 12 74049 ⟨527583, by decide⟩ ⟨12, 1, 0, 527583, 74049, 1, 65536⟩
    (by decide) selected_cut_20586

theorem selected_cut_20587 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 296200) = some ⟨13, 1, 0, 3444, 296200, 1, 16384⟩ := by
  decide +kernel

theorem context_13_296200_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296200 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 296200 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 296200, 1, 16384⟩
    (by decide) selected_cut_20587

theorem selected_cut_20588 : selected 8 ⟨527608, by decide⟩
    (prefixPartial 13 296201) = some ⟨13, 2, 0, 527608, 296201, 2173, 16384⟩ := by
  decide +kernel

theorem context_13_296201_527608 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296201 ⟨527608, by decide⟩ :=
  accepted_of_selected 13 296201 ⟨527608, by decide⟩ ⟨13, 2, 0, 527608, 296201, 2173, 16384⟩
    (by decide) selected_cut_20588

theorem selected_cut_20589 : selected 8 ⟨527629, by decide⟩
    (prefixPartial 13 296202) = some ⟨13, 2, 0, 527629, 296202, 2169, 16384⟩ := by
  decide +kernel

theorem context_13_296202_527629 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296202 ⟨527629, by decide⟩ :=
  accepted_of_selected 13 296202 ⟨527629, by decide⟩ ⟨13, 2, 0, 527629, 296202, 2169, 16384⟩
    (by decide) selected_cut_20589

theorem selected_cut_20590 : selected 8 ⟨527641, by decide⟩
    (prefixPartial 13 296203) = some ⟨13, 2, 0, 527641, 296203, 1177, 16384⟩ := by
  decide +kernel

theorem context_13_296203_527641 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296203 ⟨527641, by decide⟩ :=
  accepted_of_selected 13 296203 ⟨527641, by decide⟩ ⟨13, 2, 0, 527641, 296203, 1177, 16384⟩
    (by decide) selected_cut_20590

theorem unmarked_context_12_74050_527642 : frontier 9 ⟨527642, by decide⟩
    (prefixCache 12 74050) (prefixPartial 12 74050) = false := by
  decide +kernel

theorem node_context_12_74050_527642 : EJMOriginalGlobalDAGData.nodes 9 ⟨527642, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨527608, by decide⟩,⟨527629, by decide⟩,⟨527641, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74050_527642 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74050 ⟨527642, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74050
    ⟨527642, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨527608, by decide⟩,⟨527629, by decide⟩,⟨527641, by decide⟩]) unmarked_context_12_74050_527642 node_context_12_74050_527642
  intro a
  fin_cases a
  · exact context_13_296200_3444
  · exact context_13_296201_527608
  · exact context_13_296202_527629
  · exact context_13_296203_527641

theorem selected_cut_20591 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 296204) = some ⟨13, 1, 0, 3444, 296204, 1, 16384⟩ := by
  decide +kernel

theorem context_13_296204_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296204 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 296204 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 296204, 1, 16384⟩
    (by decide) selected_cut_20591

theorem selected_cut_20592 : selected 8 ⟨527666, by decide⟩
    (prefixPartial 13 296205) = some ⟨13, 2, 0, 527666, 296205, 2113, 16384⟩ := by
  decide +kernel

theorem context_13_296205_527666 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296205 ⟨527666, by decide⟩ :=
  accepted_of_selected 13 296205 ⟨527666, by decide⟩ ⟨13, 2, 0, 527666, 296205, 2113, 16384⟩
    (by decide) selected_cut_20592

theorem selected_cut_20593 : selected 8 ⟨527688, by decide⟩
    (prefixPartial 13 296206) = some ⟨13, 2, 0, 527688, 296206, 2321, 16384⟩ := by
  decide +kernel

theorem context_13_296206_527688 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296206 ⟨527688, by decide⟩ :=
  accepted_of_selected 13 296206 ⟨527688, by decide⟩ ⟨13, 2, 0, 527688, 296206, 2321, 16384⟩
    (by decide) selected_cut_20593

theorem selected_cut_20594 : selected 8 ⟨527698, by decide⟩
    (prefixPartial 13 296207) = some ⟨13, 2, 0, 527698, 296207, 1113, 16384⟩ := by
  decide +kernel

theorem context_13_296207_527698 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296207 ⟨527698, by decide⟩ :=
  accepted_of_selected 13 296207 ⟨527698, by decide⟩ ⟨13, 2, 0, 527698, 296207, 1113, 16384⟩
    (by decide) selected_cut_20594

theorem unmarked_context_12_74051_527699 : frontier 9 ⟨527699, by decide⟩
    (prefixCache 12 74051) (prefixPartial 12 74051) = false := by
  decide +kernel

theorem node_context_12_74051_527699 : EJMOriginalGlobalDAGData.nodes 9 ⟨527699, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨527666, by decide⟩,⟨527688, by decide⟩,⟨527698, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74051_527699 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74051 ⟨527699, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74051
    ⟨527699, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨527666, by decide⟩,⟨527688, by decide⟩,⟨527698, by decide⟩]) unmarked_context_12_74051_527699 node_context_12_74051_527699
  intro a
  fin_cases a
  · exact context_13_296204_3444
  · exact context_13_296205_527666
  · exact context_13_296206_527688
  · exact context_13_296207_527698

theorem unmarked_context_11_18512_527700 : frontier 10 ⟨527700, by decide⟩
    (prefixCache 11 18512) (prefixPartial 11 18512) = false := by
  decide +kernel

theorem node_context_11_18512_527700 : EJMOriginalGlobalDAGData.nodes 10 ⟨527700, by decide⟩ =
    .split (coordinate 11) (![⟨527583, by decide⟩,⟨527583, by decide⟩,⟨527642, by decide⟩,⟨527699, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18512_527700 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18512 ⟨527700, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18512
    ⟨527700, by decide⟩ (by decide) (![⟨527583, by decide⟩,⟨527583, by decide⟩,⟨527642, by decide⟩,⟨527699, by decide⟩]) unmarked_context_11_18512_527700 node_context_11_18512_527700
  intro a
  fin_cases a
  · exact context_12_74048_527583
  · exact context_12_74049_527583
  · exact context_12_74050_527642
  · exact context_12_74051_527699

theorem selected_cut_20595 : selected 9 ⟨527735, by decide⟩
    (prefixPartial 12 74052) = some ⟨12, 2, 0, 527735, 74052, 2505, 65536⟩ := by
  decide +kernel

theorem context_12_74052_527735 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74052 ⟨527735, by decide⟩ :=
  accepted_of_selected 12 74052 ⟨527735, by decide⟩ ⟨12, 2, 0, 527735, 74052, 2505, 65536⟩
    (by decide) selected_cut_20595

theorem selected_cut_20596 : selected 9 ⟨441672, by decide⟩
    (prefixPartial 12 74053) = some ⟨12, 1, 0, 441672, 74053, 1, 65536⟩ := by
  decide +kernel

theorem context_12_74053_441672 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74053 ⟨441672, by decide⟩ :=
  accepted_of_selected 12 74053 ⟨441672, by decide⟩ ⟨12, 1, 0, 441672, 74053, 1, 65536⟩
    (by decide) selected_cut_20596

theorem selected_cut_20597 : selected 9 ⟨527784, by decide⟩
    (prefixPartial 12 74054) = some ⟨12, 2, 0, 527784, 74054, 3081, 65536⟩ := by
  decide +kernel

theorem context_12_74054_527784 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74054 ⟨527784, by decide⟩ :=
  accepted_of_selected 12 74054 ⟨527784, by decide⟩ ⟨12, 2, 0, 527784, 74054, 3081, 65536⟩
    (by decide) selected_cut_20597

theorem selected_cut_20598 : selected 9 ⟨527830, by decide⟩
    (prefixPartial 12 74055) = some ⟨12, 2, 0, 527830, 74055, 3209, 65536⟩ := by
  decide +kernel

theorem context_12_74055_527830 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74055 ⟨527830, by decide⟩ :=
  accepted_of_selected 12 74055 ⟨527830, by decide⟩ ⟨12, 2, 0, 527830, 74055, 3209, 65536⟩
    (by decide) selected_cut_20598

theorem unmarked_context_11_18513_527831 : frontier 10 ⟨527831, by decide⟩
    (prefixCache 11 18513) (prefixPartial 11 18513) = false := by
  decide +kernel

theorem node_context_11_18513_527831 : EJMOriginalGlobalDAGData.nodes 10 ⟨527831, by decide⟩ =
    .split (coordinate 11) (![⟨527735, by decide⟩,⟨441672, by decide⟩,⟨527784, by decide⟩,⟨527830, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18513_527831 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18513 ⟨527831, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18513
    ⟨527831, by decide⟩ (by decide) (![⟨527735, by decide⟩,⟨441672, by decide⟩,⟨527784, by decide⟩,⟨527830, by decide⟩]) unmarked_context_11_18513_527831 node_context_11_18513_527831
  intro a
  fin_cases a
  · exact context_12_74052_527735
  · exact context_12_74053_441672
  · exact context_12_74054_527784
  · exact context_12_74055_527830

theorem selected_cut_20599 : selected 9 ⟨527880, by decide⟩
    (prefixPartial 12 74056) = some ⟨12, 2, 0, 527880, 74056, 3613, 65536⟩ := by
  decide +kernel

theorem context_12_74056_527880 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74056 ⟨527880, by decide⟩ :=
  accepted_of_selected 12 74056 ⟨527880, by decide⟩ ⟨12, 2, 0, 527880, 74056, 3613, 65536⟩
    (by decide) selected_cut_20599

theorem selected_cut_20600 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 296228) = some ⟨13, 1, 0, 3444, 296228, 1, 16384⟩ := by
  decide +kernel

theorem context_13_296228_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296228 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 296228 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 296228, 1, 16384⟩
    (by decide) selected_cut_20600

theorem selected_cut_20601 : selected 8 ⟨527904, by decide⟩
    (prefixPartial 13 296229) = some ⟨13, 2, 0, 527904, 296229, 1481, 16384⟩ := by
  decide +kernel

theorem context_13_296229_527904 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296229 ⟨527904, by decide⟩ :=
  accepted_of_selected 13 296229 ⟨527904, by decide⟩ ⟨13, 2, 0, 527904, 296229, 1481, 16384⟩
    (by decide) selected_cut_20601

theorem selected_cut_20602 : selected 8 ⟨527925, by decide⟩
    (prefixPartial 13 296230) = some ⟨13, 2, 0, 527925, 296230, 1737, 16384⟩ := by
  decide +kernel

theorem context_13_296230_527925 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296230 ⟨527925, by decide⟩ :=
  accepted_of_selected 13 296230 ⟨527925, by decide⟩ ⟨13, 2, 0, 527925, 296230, 1737, 16384⟩
    (by decide) selected_cut_20602

theorem selected_cut_20603 : selected 8 ⟨527933, by decide⟩
    (prefixPartial 13 296231) = some ⟨13, 2, 0, 527933, 296231, 889, 16384⟩ := by
  decide +kernel

theorem context_13_296231_527933 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296231 ⟨527933, by decide⟩ :=
  accepted_of_selected 13 296231 ⟨527933, by decide⟩ ⟨13, 2, 0, 527933, 296231, 889, 16384⟩
    (by decide) selected_cut_20603

theorem unmarked_context_12_74057_527934 : frontier 9 ⟨527934, by decide⟩
    (prefixCache 12 74057) (prefixPartial 12 74057) = false := by
  decide +kernel

theorem node_context_12_74057_527934 : EJMOriginalGlobalDAGData.nodes 9 ⟨527934, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨527904, by decide⟩,⟨527925, by decide⟩,⟨527933, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74057_527934 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74057 ⟨527934, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74057
    ⟨527934, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨527904, by decide⟩,⟨527925, by decide⟩,⟨527933, by decide⟩]) unmarked_context_12_74057_527934 node_context_12_74057_527934
  intro a
  fin_cases a
  · exact context_13_296228_3444
  · exact context_13_296229_527904
  · exact context_13_296230_527925
  · exact context_13_296231_527933

theorem selected_cut_20604 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 296232) = some ⟨13, 1, 0, 3444, 296232, 1, 16384⟩ := by
  decide +kernel

theorem context_13_296232_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296232 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 296232 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 296232, 1, 16384⟩
    (by decide) selected_cut_20604

theorem selected_cut_20605 : selected 8 ⟨527956, by decide⟩
    (prefixPartial 13 296233) = some ⟨13, 2, 0, 527956, 296233, 1617, 16384⟩ := by
  decide +kernel

theorem context_13_296233_527956 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296233 ⟨527956, by decide⟩ :=
  accepted_of_selected 13 296233 ⟨527956, by decide⟩ ⟨13, 2, 0, 527956, 296233, 1617, 16384⟩
    (by decide) selected_cut_20605

theorem selected_cut_20606 : selected 8 ⟨527974, by decide⟩
    (prefixPartial 13 296234) = some ⟨13, 2, 0, 527974, 296234, 1649, 16384⟩ := by
  decide +kernel

theorem context_13_296234_527974 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296234 ⟨527974, by decide⟩ :=
  accepted_of_selected 13 296234 ⟨527974, by decide⟩ ⟨13, 2, 0, 527974, 296234, 1649, 16384⟩
    (by decide) selected_cut_20606

theorem selected_cut_20607 : selected 8 ⟨527983, by decide⟩
    (prefixPartial 13 296235) = some ⟨13, 2, 0, 527983, 296235, 957, 16384⟩ := by
  decide +kernel

theorem context_13_296235_527983 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296235 ⟨527983, by decide⟩ :=
  accepted_of_selected 13 296235 ⟨527983, by decide⟩ ⟨13, 2, 0, 527983, 296235, 957, 16384⟩
    (by decide) selected_cut_20607

theorem unmarked_context_12_74058_527984 : frontier 9 ⟨527984, by decide⟩
    (prefixCache 12 74058) (prefixPartial 12 74058) = false := by
  decide +kernel

theorem node_context_12_74058_527984 : EJMOriginalGlobalDAGData.nodes 9 ⟨527984, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨527956, by decide⟩,⟨527974, by decide⟩,⟨527983, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74058_527984 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74058 ⟨527984, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74058
    ⟨527984, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨527956, by decide⟩,⟨527974, by decide⟩,⟨527983, by decide⟩]) unmarked_context_12_74058_527984 node_context_12_74058_527984
  intro a
  fin_cases a
  · exact context_13_296232_3444
  · exact context_13_296233_527956
  · exact context_13_296234_527974
  · exact context_13_296235_527983

theorem selected_cut_20608 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 296236) = some ⟨13, 1, 0, 3444, 296236, 1, 16384⟩ := by
  decide +kernel

theorem context_13_296236_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296236 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 296236 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 296236, 1, 16384⟩
    (by decide) selected_cut_20608

theorem selected_cut_20609 : selected 8 ⟨528007, by decide⟩
    (prefixPartial 13 296237) = some ⟨13, 2, 0, 528007, 296237, 1661, 16384⟩ := by
  decide +kernel

theorem context_13_296237_528007 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296237 ⟨528007, by decide⟩ :=
  accepted_of_selected 13 296237 ⟨528007, by decide⟩ ⟨13, 2, 0, 528007, 296237, 1661, 16384⟩
    (by decide) selected_cut_20609

theorem selected_cut_20610 : selected 8 ⟨528031, by decide⟩
    (prefixPartial 13 296238) = some ⟨13, 2, 0, 528031, 296238, 1865, 16384⟩ := by
  decide +kernel

theorem context_13_296238_528031 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296238 ⟨528031, by decide⟩ :=
  accepted_of_selected 13 296238 ⟨528031, by decide⟩ ⟨13, 2, 0, 528031, 296238, 1865, 16384⟩
    (by decide) selected_cut_20610

theorem selected_cut_20611 : selected 8 ⟨528039, by decide⟩
    (prefixPartial 13 296239) = some ⟨13, 2, 0, 528039, 296239, 925, 16384⟩ := by
  decide +kernel

theorem context_13_296239_528039 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296239 ⟨528039, by decide⟩ :=
  accepted_of_selected 13 296239 ⟨528039, by decide⟩ ⟨13, 2, 0, 528039, 296239, 925, 16384⟩
    (by decide) selected_cut_20611

theorem unmarked_context_12_74059_528040 : frontier 9 ⟨528040, by decide⟩
    (prefixCache 12 74059) (prefixPartial 12 74059) = false := by
  decide +kernel

theorem node_context_12_74059_528040 : EJMOriginalGlobalDAGData.nodes 9 ⟨528040, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨528007, by decide⟩,⟨528031, by decide⟩,⟨528039, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74059_528040 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74059 ⟨528040, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74059
    ⟨528040, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨528007, by decide⟩,⟨528031, by decide⟩,⟨528039, by decide⟩]) unmarked_context_12_74059_528040 node_context_12_74059_528040
  intro a
  fin_cases a
  · exact context_13_296236_3444
  · exact context_13_296237_528007
  · exact context_13_296238_528031
  · exact context_13_296239_528039

theorem unmarked_context_11_18514_528041 : frontier 10 ⟨528041, by decide⟩
    (prefixCache 11 18514) (prefixPartial 11 18514) = false := by
  decide +kernel

theorem node_context_11_18514_528041 : EJMOriginalGlobalDAGData.nodes 10 ⟨528041, by decide⟩ =
    .split (coordinate 11) (![⟨527880, by decide⟩,⟨527934, by decide⟩,⟨527984, by decide⟩,⟨528040, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18514_528041 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18514 ⟨528041, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18514
    ⟨528041, by decide⟩ (by decide) (![⟨527880, by decide⟩,⟨527934, by decide⟩,⟨527984, by decide⟩,⟨528040, by decide⟩]) unmarked_context_11_18514_528041 node_context_11_18514_528041
  intro a
  fin_cases a
  · exact context_12_74056_527880
  · exact context_12_74057_527934
  · exact context_12_74058_527984
  · exact context_12_74059_528040

theorem selected_cut_20612 : selected 9 ⟨528085, by decide⟩
    (prefixPartial 12 74060) = some ⟨12, 2, 0, 528085, 74060, 3321, 65536⟩ := by
  decide +kernel

theorem context_12_74060_528085 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74060 ⟨528085, by decide⟩ :=
  accepted_of_selected 12 74060 ⟨528085, by decide⟩ ⟨12, 2, 0, 528085, 74060, 3321, 65536⟩
    (by decide) selected_cut_20612

theorem selected_cut_20613 : selected 9 ⟨528132, by decide⟩
    (prefixPartial 12 74061) = some ⟨12, 2, 0, 528132, 74061, 3461, 65536⟩ := by
  decide +kernel

theorem context_12_74061_528132 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74061 ⟨528132, by decide⟩ :=
  accepted_of_selected 12 74061 ⟨528132, by decide⟩ ⟨12, 2, 0, 528132, 74061, 3461, 65536⟩
    (by decide) selected_cut_20613

theorem selected_cut_20614 : selected 9 ⟨528175, by decide⟩
    (prefixPartial 12 74062) = some ⟨12, 2, 0, 528175, 74062, 3945, 65536⟩ := by
  decide +kernel

theorem context_12_74062_528175 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74062 ⟨528175, by decide⟩ :=
  accepted_of_selected 12 74062 ⟨528175, by decide⟩ ⟨12, 2, 0, 528175, 74062, 3945, 65536⟩
    (by decide) selected_cut_20614

theorem selected_cut_20615 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 296252) = some ⟨13, 1, 0, 3444, 296252, 1, 16384⟩ := by
  decide +kernel

theorem context_13_296252_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296252 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 296252 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 296252, 1, 16384⟩
    (by decide) selected_cut_20615

theorem selected_cut_20616 : selected 8 ⟨528193, by decide⟩
    (prefixPartial 13 296253) = some ⟨13, 2, 0, 528193, 296253, 1509, 16384⟩ := by
  decide +kernel

theorem context_13_296253_528193 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296253 ⟨528193, by decide⟩ :=
  accepted_of_selected 13 296253 ⟨528193, by decide⟩ ⟨13, 2, 0, 528193, 296253, 1509, 16384⟩
    (by decide) selected_cut_20616

theorem selected_cut_20617 : selected 8 ⟨528212, by decide⟩
    (prefixPartial 13 296254) = some ⟨13, 2, 0, 528212, 296254, 1613, 16384⟩ := by
  decide +kernel

theorem context_13_296254_528212 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296254 ⟨528212, by decide⟩ :=
  accepted_of_selected 13 296254 ⟨528212, by decide⟩ ⟨13, 2, 0, 528212, 296254, 1613, 16384⟩
    (by decide) selected_cut_20617

theorem selected_cut_20618 : selected 8 ⟨528219, by decide⟩
    (prefixPartial 13 296255) = some ⟨13, 2, 0, 528219, 296255, 1037, 16384⟩ := by
  decide +kernel

theorem context_13_296255_528219 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296255 ⟨528219, by decide⟩ :=
  accepted_of_selected 13 296255 ⟨528219, by decide⟩ ⟨13, 2, 0, 528219, 296255, 1037, 16384⟩
    (by decide) selected_cut_20618

theorem unmarked_context_12_74063_528220 : frontier 9 ⟨528220, by decide⟩
    (prefixCache 12 74063) (prefixPartial 12 74063) = false := by
  decide +kernel

theorem node_context_12_74063_528220 : EJMOriginalGlobalDAGData.nodes 9 ⟨528220, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨528193, by decide⟩,⟨528212, by decide⟩,⟨528219, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74063_528220 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74063 ⟨528220, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74063
    ⟨528220, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨528193, by decide⟩,⟨528212, by decide⟩,⟨528219, by decide⟩]) unmarked_context_12_74063_528220 node_context_12_74063_528220
  intro a
  fin_cases a
  · exact context_13_296252_3444
  · exact context_13_296253_528193
  · exact context_13_296254_528212
  · exact context_13_296255_528219

theorem unmarked_context_11_18515_528221 : frontier 10 ⟨528221, by decide⟩
    (prefixCache 11 18515) (prefixPartial 11 18515) = false := by
  decide +kernel

theorem node_context_11_18515_528221 : EJMOriginalGlobalDAGData.nodes 10 ⟨528221, by decide⟩ =
    .split (coordinate 11) (![⟨528085, by decide⟩,⟨528132, by decide⟩,⟨528175, by decide⟩,⟨528220, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18515_528221 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18515 ⟨528221, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18515
    ⟨528221, by decide⟩ (by decide) (![⟨528085, by decide⟩,⟨528132, by decide⟩,⟨528175, by decide⟩,⟨528220, by decide⟩]) unmarked_context_11_18515_528221 node_context_11_18515_528221
  intro a
  fin_cases a
  · exact context_12_74060_528085
  · exact context_12_74061_528132
  · exact context_12_74062_528175
  · exact context_12_74063_528220

theorem unmarked_context_10_4628_528222 : frontier 11 ⟨528222, by decide⟩
    (prefixCache 10 4628) (prefixPartial 10 4628) = false := by
  decide +kernel

theorem node_context_10_4628_528222 : EJMOriginalGlobalDAGData.nodes 11 ⟨528222, by decide⟩ =
    .split (coordinate 10) (![⟨527700, by decide⟩,⟨527831, by decide⟩,⟨528041, by decide⟩,⟨528221, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4628_528222 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4628 ⟨528222, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4628
    ⟨528222, by decide⟩ (by decide) (![⟨527700, by decide⟩,⟨527831, by decide⟩,⟨528041, by decide⟩,⟨528221, by decide⟩]) unmarked_context_10_4628_528222 node_context_10_4628_528222
  intro a
  fin_cases a
  · exact context_11_18512_527700
  · exact context_11_18513_527831
  · exact context_11_18514_528041
  · exact context_11_18515_528221

theorem selected_cut_20619 : selected 9 ⟨528266, by decide⟩
    (prefixPartial 12 74064) = some ⟨12, 2, 0, 528266, 74064, 3501, 65536⟩ := by
  decide +kernel

theorem context_12_74064_528266 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74064 ⟨528266, by decide⟩ :=
  accepted_of_selected 12 74064 ⟨528266, by decide⟩ ⟨12, 2, 0, 528266, 74064, 3501, 65536⟩
    (by decide) selected_cut_20619

theorem selected_cut_20620 : selected 9 ⟨528309, by decide⟩
    (prefixPartial 12 74065) = some ⟨12, 2, 0, 528309, 74065, 3933, 65536⟩ := by
  decide +kernel

theorem context_12_74065_528309 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74065 ⟨528309, by decide⟩ :=
  accepted_of_selected 12 74065 ⟨528309, by decide⟩ ⟨12, 2, 0, 528309, 74065, 3933, 65536⟩
    (by decide) selected_cut_20620

theorem selected_cut_20621 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 296264) = some ⟨13, 1, 0, 3444, 296264, 1, 16384⟩ := by
  decide +kernel

theorem context_13_296264_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296264 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 296264 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 296264, 1, 16384⟩
    (by decide) selected_cut_20621

theorem selected_cut_20622 : selected 8 ⟨528330, by decide⟩
    (prefixPartial 13 296265) = some ⟨13, 2, 0, 528330, 296265, 1653, 16384⟩ := by
  decide +kernel

theorem context_13_296265_528330 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296265 ⟨528330, by decide⟩ :=
  accepted_of_selected 13 296265 ⟨528330, by decide⟩ ⟨13, 2, 0, 528330, 296265, 1653, 16384⟩
    (by decide) selected_cut_20622

theorem selected_cut_20623 : selected 8 ⟨528350, by decide⟩
    (prefixPartial 13 296266) = some ⟨13, 2, 0, 528350, 296266, 1733, 16384⟩ := by
  decide +kernel

theorem context_13_296266_528350 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296266 ⟨528350, by decide⟩ :=
  accepted_of_selected 13 296266 ⟨528350, by decide⟩ ⟨13, 2, 0, 528350, 296266, 1733, 16384⟩
    (by decide) selected_cut_20623

theorem selected_cut_20624 : selected 8 ⟨528359, by decide⟩
    (prefixPartial 13 296267) = some ⟨13, 2, 0, 528359, 296267, 985, 16384⟩ := by
  decide +kernel

theorem context_13_296267_528359 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296267 ⟨528359, by decide⟩ :=
  accepted_of_selected 13 296267 ⟨528359, by decide⟩ ⟨13, 2, 0, 528359, 296267, 985, 16384⟩
    (by decide) selected_cut_20624

theorem unmarked_context_12_74066_528360 : frontier 9 ⟨528360, by decide⟩
    (prefixCache 12 74066) (prefixPartial 12 74066) = false := by
  decide +kernel

theorem node_context_12_74066_528360 : EJMOriginalGlobalDAGData.nodes 9 ⟨528360, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨528330, by decide⟩,⟨528350, by decide⟩,⟨528359, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74066_528360 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74066 ⟨528360, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74066
    ⟨528360, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨528330, by decide⟩,⟨528350, by decide⟩,⟨528359, by decide⟩]) unmarked_context_12_74066_528360 node_context_12_74066_528360
  intro a
  fin_cases a
  · exact context_13_296264_3444
  · exact context_13_296265_528330
  · exact context_13_296266_528350
  · exact context_13_296267_528359

theorem selected_cut_20625 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 296268) = some ⟨13, 1, 0, 3444, 296268, 1, 16384⟩ := by
  decide +kernel

theorem context_13_296268_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296268 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 296268 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 296268, 1, 16384⟩
    (by decide) selected_cut_20625

theorem selected_cut_20626 : selected 8 ⟨528378, by decide⟩
    (prefixPartial 13 296269) = some ⟨13, 2, 0, 528378, 296269, 1661, 16384⟩ := by
  decide +kernel

theorem context_13_296269_528378 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296269 ⟨528378, by decide⟩ :=
  accepted_of_selected 13 296269 ⟨528378, by decide⟩ ⟨13, 2, 0, 528378, 296269, 1661, 16384⟩
    (by decide) selected_cut_20626

theorem selected_cut_20627 : selected 8 ⟨528402, by decide⟩
    (prefixPartial 13 296270) = some ⟨13, 2, 0, 528402, 296270, 2037, 16384⟩ := by
  decide +kernel

theorem context_13_296270_528402 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296270 ⟨528402, by decide⟩ :=
  accepted_of_selected 13 296270 ⟨528402, by decide⟩ ⟨13, 2, 0, 528402, 296270, 2037, 16384⟩
    (by decide) selected_cut_20627

theorem selected_cut_20628 : selected 8 ⟨528410, by decide⟩
    (prefixPartial 13 296271) = some ⟨13, 2, 0, 528410, 296271, 881, 16384⟩ := by
  decide +kernel

theorem context_13_296271_528410 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296271 ⟨528410, by decide⟩ :=
  accepted_of_selected 13 296271 ⟨528410, by decide⟩ ⟨13, 2, 0, 528410, 296271, 881, 16384⟩
    (by decide) selected_cut_20628

theorem unmarked_context_12_74067_528411 : frontier 9 ⟨528411, by decide⟩
    (prefixCache 12 74067) (prefixPartial 12 74067) = false := by
  decide +kernel

theorem node_context_12_74067_528411 : EJMOriginalGlobalDAGData.nodes 9 ⟨528411, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨528378, by decide⟩,⟨528402, by decide⟩,⟨528410, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74067_528411 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74067 ⟨528411, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74067
    ⟨528411, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨528378, by decide⟩,⟨528402, by decide⟩,⟨528410, by decide⟩]) unmarked_context_12_74067_528411 node_context_12_74067_528411
  intro a
  fin_cases a
  · exact context_13_296268_3444
  · exact context_13_296269_528378
  · exact context_13_296270_528402
  · exact context_13_296271_528410

theorem unmarked_context_11_18516_528412 : frontier 10 ⟨528412, by decide⟩
    (prefixCache 11 18516) (prefixPartial 11 18516) = false := by
  decide +kernel

theorem node_context_11_18516_528412 : EJMOriginalGlobalDAGData.nodes 10 ⟨528412, by decide⟩ =
    .split (coordinate 11) (![⟨528266, by decide⟩,⟨528309, by decide⟩,⟨528360, by decide⟩,⟨528411, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18516_528412 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18516 ⟨528412, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18516
    ⟨528412, by decide⟩ (by decide) (![⟨528266, by decide⟩,⟨528309, by decide⟩,⟨528360, by decide⟩,⟨528411, by decide⟩]) unmarked_context_11_18516_528412 node_context_11_18516_528412
  intro a
  fin_cases a
  · exact context_12_74064_528266
  · exact context_12_74065_528309
  · exact context_12_74066_528360
  · exact context_12_74067_528411

theorem selected_cut_20629 : selected 9 ⟨528452, by decide⟩
    (prefixPartial 12 74068) = some ⟨12, 2, 0, 528452, 74068, 3437, 65536⟩ := by
  decide +kernel

theorem context_12_74068_528452 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74068 ⟨528452, by decide⟩ :=
  accepted_of_selected 12 74068 ⟨528452, by decide⟩ ⟨12, 2, 0, 528452, 74068, 3437, 65536⟩
    (by decide) selected_cut_20629

theorem selected_cut_20630 : selected 9 ⟨439069, by decide⟩
    (prefixPartial 12 74069) = some ⟨12, 1, 0, 439069, 74069, 1, 65536⟩ := by
  decide +kernel

theorem context_12_74069_439069 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74069 ⟨439069, by decide⟩ :=
  accepted_of_selected 12 74069 ⟨439069, by decide⟩ ⟨12, 1, 0, 439069, 74069, 1, 65536⟩
    (by decide) selected_cut_20630

theorem selected_cut_20631 : selected 9 ⟨528490, by decide⟩
    (prefixPartial 12 74070) = some ⟨12, 2, 0, 528490, 74070, 4089, 65536⟩ := by
  decide +kernel

theorem context_12_74070_528490 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74070 ⟨528490, by decide⟩ :=
  accepted_of_selected 12 74070 ⟨528490, by decide⟩ ⟨12, 2, 0, 528490, 74070, 4089, 65536⟩
    (by decide) selected_cut_20631

theorem selected_cut_20632 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 296284) = some ⟨13, 1, 0, 3444, 296284, 1, 16384⟩ := by
  decide +kernel

theorem context_13_296284_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296284 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 296284 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 296284, 1, 16384⟩
    (by decide) selected_cut_20632

theorem selected_cut_20633 : selected 8 ⟨528507, by decide⟩
    (prefixPartial 13 296285) = some ⟨13, 2, 0, 528507, 296285, 1445, 16384⟩ := by
  decide +kernel

theorem context_13_296285_528507 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296285 ⟨528507, by decide⟩ :=
  accepted_of_selected 13 296285 ⟨528507, by decide⟩ ⟨13, 2, 0, 528507, 296285, 1445, 16384⟩
    (by decide) selected_cut_20633

theorem selected_cut_20634 : selected 8 ⟨528524, by decide⟩
    (prefixPartial 13 296286) = some ⟨13, 2, 0, 528524, 296286, 2041, 16384⟩ := by
  decide +kernel

theorem context_13_296286_528524 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296286 ⟨528524, by decide⟩ :=
  accepted_of_selected 13 296286 ⟨528524, by decide⟩ ⟨13, 2, 0, 528524, 296286, 2041, 16384⟩
    (by decide) selected_cut_20634

theorem selected_cut_20635 : selected 8 ⟨528529, by decide⟩
    (prefixPartial 13 296287) = some ⟨13, 2, 0, 528529, 296287, 845, 16384⟩ := by
  decide +kernel

theorem context_13_296287_528529 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296287 ⟨528529, by decide⟩ :=
  accepted_of_selected 13 296287 ⟨528529, by decide⟩ ⟨13, 2, 0, 528529, 296287, 845, 16384⟩
    (by decide) selected_cut_20635

theorem unmarked_context_12_74071_528530 : frontier 9 ⟨528530, by decide⟩
    (prefixCache 12 74071) (prefixPartial 12 74071) = false := by
  decide +kernel

theorem node_context_12_74071_528530 : EJMOriginalGlobalDAGData.nodes 9 ⟨528530, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨528507, by decide⟩,⟨528524, by decide⟩,⟨528529, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74071_528530 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74071 ⟨528530, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74071
    ⟨528530, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨528507, by decide⟩,⟨528524, by decide⟩,⟨528529, by decide⟩]) unmarked_context_12_74071_528530 node_context_12_74071_528530
  intro a
  fin_cases a
  · exact context_13_296284_3444
  · exact context_13_296285_528507
  · exact context_13_296286_528524
  · exact context_13_296287_528529

theorem unmarked_context_11_18517_528531 : frontier 10 ⟨528531, by decide⟩
    (prefixCache 11 18517) (prefixPartial 11 18517) = false := by
  decide +kernel

theorem node_context_11_18517_528531 : EJMOriginalGlobalDAGData.nodes 10 ⟨528531, by decide⟩ =
    .split (coordinate 11) (![⟨528452, by decide⟩,⟨439069, by decide⟩,⟨528490, by decide⟩,⟨528530, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18517_528531 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18517 ⟨528531, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18517
    ⟨528531, by decide⟩ (by decide) (![⟨528452, by decide⟩,⟨439069, by decide⟩,⟨528490, by decide⟩,⟨528530, by decide⟩]) unmarked_context_11_18517_528531 node_context_11_18517_528531
  intro a
  fin_cases a
  · exact context_12_74068_528452
  · exact context_12_74069_439069
  · exact context_12_74070_528490
  · exact context_12_74071_528530

theorem selected_cut_20636 : selected 9 ⟨528576, by decide⟩
    (prefixPartial 12 74072) = some ⟨12, 2, 0, 528576, 74072, 3777, 65536⟩ := by
  decide +kernel

theorem context_12_74072_528576 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74072 ⟨528576, by decide⟩ :=
  accepted_of_selected 12 74072 ⟨528576, by decide⟩ ⟨12, 2, 0, 528576, 74072, 3777, 65536⟩
    (by decide) selected_cut_20636

theorem selected_cut_20637 : selected 9 ⟨528621, by decide⟩
    (prefixPartial 12 74073) = some ⟨12, 2, 0, 528621, 74073, 4061, 65536⟩ := by
  decide +kernel

theorem context_12_74073_528621 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74073 ⟨528621, by decide⟩ :=
  accepted_of_selected 12 74073 ⟨528621, by decide⟩ ⟨12, 2, 0, 528621, 74073, 4061, 65536⟩
    (by decide) selected_cut_20637

theorem selected_cut_20638 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 296296) = some ⟨13, 1, 0, 3444, 296296, 1, 16384⟩ := by
  decide +kernel

theorem context_13_296296_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296296 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 296296 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 296296, 1, 16384⟩
    (by decide) selected_cut_20638

theorem selected_cut_20639 : selected 8 ⟨528638, by decide⟩
    (prefixPartial 13 296297) = some ⟨13, 2, 0, 528638, 296297, 1497, 16384⟩ := by
  decide +kernel

theorem context_13_296297_528638 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296297 ⟨528638, by decide⟩ :=
  accepted_of_selected 13 296297 ⟨528638, by decide⟩ ⟨13, 2, 0, 528638, 296297, 1497, 16384⟩
    (by decide) selected_cut_20639

theorem selected_cut_20640 : selected 8 ⟨528658, by decide⟩
    (prefixPartial 13 296298) = some ⟨13, 2, 0, 528658, 296298, 1665, 16384⟩ := by
  decide +kernel

theorem context_13_296298_528658 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296298 ⟨528658, by decide⟩ :=
  accepted_of_selected 13 296298 ⟨528658, by decide⟩ ⟨13, 2, 0, 528658, 296298, 1665, 16384⟩
    (by decide) selected_cut_20640

theorem selected_cut_20641 : selected 8 ⟨528667, by decide⟩
    (prefixPartial 13 296299) = some ⟨13, 2, 0, 528667, 296299, 989, 16384⟩ := by
  decide +kernel

theorem context_13_296299_528667 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296299 ⟨528667, by decide⟩ :=
  accepted_of_selected 13 296299 ⟨528667, by decide⟩ ⟨13, 2, 0, 528667, 296299, 989, 16384⟩
    (by decide) selected_cut_20641

theorem unmarked_context_12_74074_528668 : frontier 9 ⟨528668, by decide⟩
    (prefixCache 12 74074) (prefixPartial 12 74074) = false := by
  decide +kernel

theorem node_context_12_74074_528668 : EJMOriginalGlobalDAGData.nodes 9 ⟨528668, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨528638, by decide⟩,⟨528658, by decide⟩,⟨528667, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74074_528668 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74074 ⟨528668, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74074
    ⟨528668, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨528638, by decide⟩,⟨528658, by decide⟩,⟨528667, by decide⟩]) unmarked_context_12_74074_528668 node_context_12_74074_528668
  intro a
  fin_cases a
  · exact context_13_296296_3444
  · exact context_13_296297_528638
  · exact context_13_296298_528658
  · exact context_13_296299_528667

theorem selected_cut_20642 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 296300) = some ⟨13, 1, 0, 3444, 296300, 1, 16384⟩ := by
  decide +kernel

theorem context_13_296300_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296300 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 296300 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 296300, 1, 16384⟩
    (by decide) selected_cut_20642

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
