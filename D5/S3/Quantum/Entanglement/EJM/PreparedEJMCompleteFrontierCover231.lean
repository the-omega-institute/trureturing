/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover230
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_22179 : selected 8 ⟨565438, by decide⟩
    (prefixPartial 13 302181) = some ⟨13, 2, 0, 565438, 302181, 2129, 16384⟩ := by
  decide +kernel

theorem context_13_302181_565438 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302181 ⟨565438, by decide⟩ :=
  accepted_of_selected 13 302181 ⟨565438, by decide⟩ ⟨13, 2, 0, 565438, 302181, 2129, 16384⟩
    (by decide) selected_cut_22179

theorem selected_cut_22180 : selected 8 ⟨565460, by decide⟩
    (prefixPartial 13 302182) = some ⟨13, 2, 0, 565460, 302182, 1685, 16384⟩ := by
  decide +kernel

theorem context_13_302182_565460 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302182 ⟨565460, by decide⟩ :=
  accepted_of_selected 13 302182 ⟨565460, by decide⟩ ⟨13, 2, 0, 565460, 302182, 1685, 16384⟩
    (by decide) selected_cut_22180

theorem selected_cut_22181 : selected 8 ⟨565468, by decide⟩
    (prefixPartial 13 302183) = some ⟨13, 2, 0, 565468, 302183, 757, 16384⟩ := by
  decide +kernel

theorem context_13_302183_565468 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302183 ⟨565468, by decide⟩ :=
  accepted_of_selected 13 302183 ⟨565468, by decide⟩ ⟨13, 2, 0, 565468, 302183, 757, 16384⟩
    (by decide) selected_cut_22181

theorem unmarked_context_12_75545_565469 : frontier 9 ⟨565469, by decide⟩
    (prefixCache 12 75545) (prefixPartial 12 75545) = false := by
  decide +kernel

theorem node_context_12_75545_565469 : EJMOriginalGlobalDAGData.nodes 9 ⟨565469, by decide⟩ =
    .split (coordinate 12) (![⟨565405, by decide⟩,⟨565438, by decide⟩,⟨565460, by decide⟩,⟨565468, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75545_565469 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75545 ⟨565469, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75545
    ⟨565469, by decide⟩ (by decide) (![⟨565405, by decide⟩,⟨565438, by decide⟩,⟨565460, by decide⟩,⟨565468, by decide⟩]) unmarked_context_12_75545_565469 node_context_12_75545_565469
  intro a
  fin_cases a
  · exact context_13_302180_565405
  · exact context_13_302181_565438
  · exact context_13_302182_565460
  · exact context_13_302183_565468

theorem selected_cut_22182 : selected 8 ⟨565496, by decide⟩
    (prefixPartial 13 302184) = some ⟨13, 2, 0, 565496, 302184, 1509, 16384⟩ := by
  decide +kernel

theorem context_13_302184_565496 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302184 ⟨565496, by decide⟩ :=
  accepted_of_selected 13 302184 ⟨565496, by decide⟩ ⟨13, 2, 0, 565496, 302184, 1509, 16384⟩
    (by decide) selected_cut_22182

theorem selected_cut_22183 : selected 8 ⟨565523, by decide⟩
    (prefixPartial 13 302185) = some ⟨13, 2, 0, 565523, 302185, 2237, 16384⟩ := by
  decide +kernel

theorem context_13_302185_565523 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302185 ⟨565523, by decide⟩ :=
  accepted_of_selected 13 302185 ⟨565523, by decide⟩ ⟨13, 2, 0, 565523, 302185, 2237, 16384⟩
    (by decide) selected_cut_22183

theorem selected_cut_22184 : selected 8 ⟨565550, by decide⟩
    (prefixPartial 13 302186) = some ⟨13, 2, 0, 565550, 302186, 1809, 16384⟩ := by
  decide +kernel

theorem context_13_302186_565550 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302186 ⟨565550, by decide⟩ :=
  accepted_of_selected 13 302186 ⟨565550, by decide⟩ ⟨13, 2, 0, 565550, 302186, 1809, 16384⟩
    (by decide) selected_cut_22184

theorem selected_cut_22185 : selected 8 ⟨565558, by decide⟩
    (prefixPartial 13 302187) = some ⟨13, 2, 0, 565558, 302187, 877, 16384⟩ := by
  decide +kernel

theorem context_13_302187_565558 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302187 ⟨565558, by decide⟩ :=
  accepted_of_selected 13 302187 ⟨565558, by decide⟩ ⟨13, 2, 0, 565558, 302187, 877, 16384⟩
    (by decide) selected_cut_22185

theorem unmarked_context_12_75546_565559 : frontier 9 ⟨565559, by decide⟩
    (prefixCache 12 75546) (prefixPartial 12 75546) = false := by
  decide +kernel

theorem node_context_12_75546_565559 : EJMOriginalGlobalDAGData.nodes 9 ⟨565559, by decide⟩ =
    .split (coordinate 12) (![⟨565496, by decide⟩,⟨565523, by decide⟩,⟨565550, by decide⟩,⟨565558, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75546_565559 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75546 ⟨565559, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75546
    ⟨565559, by decide⟩ (by decide) (![⟨565496, by decide⟩,⟨565523, by decide⟩,⟨565550, by decide⟩,⟨565558, by decide⟩]) unmarked_context_12_75546_565559 node_context_12_75546_565559
  intro a
  fin_cases a
  · exact context_13_302184_565496
  · exact context_13_302185_565523
  · exact context_13_302186_565550
  · exact context_13_302187_565558

theorem selected_cut_22186 : selected 8 ⟨565587, by decide⟩
    (prefixPartial 13 302188) = some ⟨13, 2, 0, 565587, 302188, 1397, 16384⟩ := by
  decide +kernel

theorem context_13_302188_565587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302188 ⟨565587, by decide⟩ :=
  accepted_of_selected 13 302188 ⟨565587, by decide⟩ ⟨13, 2, 0, 565587, 302188, 1397, 16384⟩
    (by decide) selected_cut_22186

theorem selected_cut_22187 : selected 8 ⟨565613, by decide⟩
    (prefixPartial 13 302189) = some ⟨13, 2, 0, 565613, 302189, 2333, 16384⟩ := by
  decide +kernel

theorem context_13_302189_565613 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302189 ⟨565613, by decide⟩ :=
  accepted_of_selected 13 302189 ⟨565613, by decide⟩ ⟨13, 2, 0, 565613, 302189, 2333, 16384⟩
    (by decide) selected_cut_22187

theorem selected_cut_22188 : selected 8 ⟨565635, by decide⟩
    (prefixPartial 13 302190) = some ⟨13, 2, 0, 565635, 302190, 1853, 16384⟩ := by
  decide +kernel

theorem context_13_302190_565635 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302190 ⟨565635, by decide⟩ :=
  accepted_of_selected 13 302190 ⟨565635, by decide⟩ ⟨13, 2, 0, 565635, 302190, 1853, 16384⟩
    (by decide) selected_cut_22188

theorem selected_cut_22189 : selected 8 ⟨565641, by decide⟩
    (prefixPartial 13 302191) = some ⟨13, 2, 0, 565641, 302191, 757, 16384⟩ := by
  decide +kernel

theorem context_13_302191_565641 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302191 ⟨565641, by decide⟩ :=
  accepted_of_selected 13 302191 ⟨565641, by decide⟩ ⟨13, 2, 0, 565641, 302191, 757, 16384⟩
    (by decide) selected_cut_22189

theorem unmarked_context_12_75547_565642 : frontier 9 ⟨565642, by decide⟩
    (prefixCache 12 75547) (prefixPartial 12 75547) = false := by
  decide +kernel

theorem node_context_12_75547_565642 : EJMOriginalGlobalDAGData.nodes 9 ⟨565642, by decide⟩ =
    .split (coordinate 12) (![⟨565587, by decide⟩,⟨565613, by decide⟩,⟨565635, by decide⟩,⟨565641, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75547_565642 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75547 ⟨565642, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75547
    ⟨565642, by decide⟩ (by decide) (![⟨565587, by decide⟩,⟨565613, by decide⟩,⟨565635, by decide⟩,⟨565641, by decide⟩]) unmarked_context_12_75547_565642 node_context_12_75547_565642
  intro a
  fin_cases a
  · exact context_13_302188_565587
  · exact context_13_302189_565613
  · exact context_13_302190_565635
  · exact context_13_302191_565641

theorem unmarked_context_11_18886_565643 : frontier 10 ⟨565643, by decide⟩
    (prefixCache 11 18886) (prefixPartial 11 18886) = false := by
  decide +kernel

theorem node_context_11_18886_565643 : EJMOriginalGlobalDAGData.nodes 10 ⟨565643, by decide⟩ =
    .split (coordinate 11) (![⟨565376, by decide⟩,⟨565469, by decide⟩,⟨565559, by decide⟩,⟨565642, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18886_565643 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18886 ⟨565643, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18886
    ⟨565643, by decide⟩ (by decide) (![⟨565376, by decide⟩,⟨565469, by decide⟩,⟨565559, by decide⟩,⟨565642, by decide⟩]) unmarked_context_11_18886_565643 node_context_11_18886_565643
  intro a
  fin_cases a
  · exact context_12_75544_565376
  · exact context_12_75545_565469
  · exact context_12_75546_565559
  · exact context_12_75547_565642

theorem selected_cut_22190 : selected 8 ⟨565679, by decide⟩
    (prefixPartial 13 302192) = some ⟨13, 2, 0, 565679, 302192, 1741, 16384⟩ := by
  decide +kernel

theorem context_13_302192_565679 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302192 ⟨565679, by decide⟩ :=
  accepted_of_selected 13 302192 ⟨565679, by decide⟩ ⟨13, 2, 0, 565679, 302192, 1741, 16384⟩
    (by decide) selected_cut_22190

theorem selected_cut_22191 : selected 8 ⟨565711, by decide⟩
    (prefixPartial 13 302193) = some ⟨13, 2, 0, 565711, 302193, 3021, 16384⟩ := by
  decide +kernel

theorem context_13_302193_565711 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302193 ⟨565711, by decide⟩ :=
  accepted_of_selected 13 302193 ⟨565711, by decide⟩ ⟨13, 2, 0, 565711, 302193, 3021, 16384⟩
    (by decide) selected_cut_22191

theorem selected_cut_22192 : selected 8 ⟨565751, by decide⟩
    (prefixPartial 13 302194) = some ⟨13, 2, 0, 565751, 302194, 2309, 16384⟩ := by
  decide +kernel

theorem context_13_302194_565751 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302194 ⟨565751, by decide⟩ :=
  accepted_of_selected 13 302194 ⟨565751, by decide⟩ ⟨13, 2, 0, 565751, 302194, 2309, 16384⟩
    (by decide) selected_cut_22192

theorem selected_cut_22193 : selected 8 ⟨565759, by decide⟩
    (prefixPartial 13 302195) = some ⟨13, 2, 0, 565759, 302195, 897, 16384⟩ := by
  decide +kernel

theorem context_13_302195_565759 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302195 ⟨565759, by decide⟩ :=
  accepted_of_selected 13 302195 ⟨565759, by decide⟩ ⟨13, 2, 0, 565759, 302195, 897, 16384⟩
    (by decide) selected_cut_22193

theorem unmarked_context_12_75548_565760 : frontier 9 ⟨565760, by decide⟩
    (prefixCache 12 75548) (prefixPartial 12 75548) = false := by
  decide +kernel

theorem node_context_12_75548_565760 : EJMOriginalGlobalDAGData.nodes 9 ⟨565760, by decide⟩ =
    .split (coordinate 12) (![⟨565679, by decide⟩,⟨565711, by decide⟩,⟨565751, by decide⟩,⟨565759, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75548_565760 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75548 ⟨565760, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75548
    ⟨565760, by decide⟩ (by decide) (![⟨565679, by decide⟩,⟨565711, by decide⟩,⟨565751, by decide⟩,⟨565759, by decide⟩]) unmarked_context_12_75548_565760 node_context_12_75548_565760
  intro a
  fin_cases a
  · exact context_13_302192_565679
  · exact context_13_302193_565711
  · exact context_13_302194_565751
  · exact context_13_302195_565759

theorem selected_cut_22194 : selected 8 ⟨565780, by decide⟩
    (prefixPartial 13 302196) = some ⟨13, 2, 0, 565780, 302196, 1121, 16384⟩ := by
  decide +kernel

theorem context_13_302196_565780 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302196 ⟨565780, by decide⟩ :=
  accepted_of_selected 13 302196 ⟨565780, by decide⟩ ⟨13, 2, 0, 565780, 302196, 1121, 16384⟩
    (by decide) selected_cut_22194

theorem selected_cut_22195 : selected 8 ⟨565807, by decide⟩
    (prefixPartial 13 302197) = some ⟨13, 2, 0, 565807, 302197, 2213, 16384⟩ := by
  decide +kernel

theorem context_13_302197_565807 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302197 ⟨565807, by decide⟩ :=
  accepted_of_selected 13 302197 ⟨565807, by decide⟩ ⟨13, 2, 0, 565807, 302197, 2213, 16384⟩
    (by decide) selected_cut_22195

theorem selected_cut_22196 : selected 8 ⟨565826, by decide⟩
    (prefixPartial 13 302198) = some ⟨13, 2, 0, 565826, 302198, 1597, 16384⟩ := by
  decide +kernel

theorem context_13_302198_565826 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302198 ⟨565826, by decide⟩ :=
  accepted_of_selected 13 302198 ⟨565826, by decide⟩ ⟨13, 2, 0, 565826, 302198, 1597, 16384⟩
    (by decide) selected_cut_22196

theorem selected_cut_22197 : selected 8 ⟨565830, by decide⟩
    (prefixPartial 13 302199) = some ⟨13, 2, 0, 565830, 302199, 649, 16384⟩ := by
  decide +kernel

theorem context_13_302199_565830 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302199 ⟨565830, by decide⟩ :=
  accepted_of_selected 13 302199 ⟨565830, by decide⟩ ⟨13, 2, 0, 565830, 302199, 649, 16384⟩
    (by decide) selected_cut_22197

theorem unmarked_context_12_75549_565831 : frontier 9 ⟨565831, by decide⟩
    (prefixCache 12 75549) (prefixPartial 12 75549) = false := by
  decide +kernel

theorem node_context_12_75549_565831 : EJMOriginalGlobalDAGData.nodes 9 ⟨565831, by decide⟩ =
    .split (coordinate 12) (![⟨565780, by decide⟩,⟨565807, by decide⟩,⟨565826, by decide⟩,⟨565830, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75549_565831 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75549 ⟨565831, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75549
    ⟨565831, by decide⟩ (by decide) (![⟨565780, by decide⟩,⟨565807, by decide⟩,⟨565826, by decide⟩,⟨565830, by decide⟩]) unmarked_context_12_75549_565831 node_context_12_75549_565831
  intro a
  fin_cases a
  · exact context_13_302196_565780
  · exact context_13_302197_565807
  · exact context_13_302198_565826
  · exact context_13_302199_565830

theorem selected_cut_22198 : selected 8 ⟨565858, by decide⟩
    (prefixPartial 13 302200) = some ⟨13, 2, 0, 565858, 302200, 1249, 16384⟩ := by
  decide +kernel

theorem context_13_302200_565858 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302200 ⟨565858, by decide⟩ :=
  accepted_of_selected 13 302200 ⟨565858, by decide⟩ ⟨13, 2, 0, 565858, 302200, 1249, 16384⟩
    (by decide) selected_cut_22198

theorem selected_cut_22199 : selected 8 ⟨565885, by decide⟩
    (prefixPartial 13 302201) = some ⟨13, 2, 0, 565885, 302201, 2505, 16384⟩ := by
  decide +kernel

theorem context_13_302201_565885 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302201 ⟨565885, by decide⟩ :=
  accepted_of_selected 13 302201 ⟨565885, by decide⟩ ⟨13, 2, 0, 565885, 302201, 2505, 16384⟩
    (by decide) selected_cut_22199

theorem selected_cut_22200 : selected 8 ⟨565905, by decide⟩
    (prefixPartial 13 302202) = some ⟨13, 2, 0, 565905, 302202, 1613, 16384⟩ := by
  decide +kernel

theorem context_13_302202_565905 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302202 ⟨565905, by decide⟩ :=
  accepted_of_selected 13 302202 ⟨565905, by decide⟩ ⟨13, 2, 0, 565905, 302202, 1613, 16384⟩
    (by decide) selected_cut_22200

theorem selected_cut_22201 : selected 8 ⟨565911, by decide⟩
    (prefixPartial 13 302203) = some ⟨13, 2, 0, 565911, 302203, 741, 16384⟩ := by
  decide +kernel

theorem context_13_302203_565911 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302203 ⟨565911, by decide⟩ :=
  accepted_of_selected 13 302203 ⟨565911, by decide⟩ ⟨13, 2, 0, 565911, 302203, 741, 16384⟩
    (by decide) selected_cut_22201

theorem unmarked_context_12_75550_565912 : frontier 9 ⟨565912, by decide⟩
    (prefixCache 12 75550) (prefixPartial 12 75550) = false := by
  decide +kernel

theorem node_context_12_75550_565912 : EJMOriginalGlobalDAGData.nodes 9 ⟨565912, by decide⟩ =
    .split (coordinate 12) (![⟨565858, by decide⟩,⟨565885, by decide⟩,⟨565905, by decide⟩,⟨565911, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75550_565912 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75550 ⟨565912, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75550
    ⟨565912, by decide⟩ (by decide) (![⟨565858, by decide⟩,⟨565885, by decide⟩,⟨565905, by decide⟩,⟨565911, by decide⟩]) unmarked_context_12_75550_565912 node_context_12_75550_565912
  intro a
  fin_cases a
  · exact context_13_302200_565858
  · exact context_13_302201_565885
  · exact context_13_302202_565905
  · exact context_13_302203_565911

theorem selected_cut_22202 : selected 8 ⟨565935, by decide⟩
    (prefixPartial 13 302204) = some ⟨13, 2, 0, 565935, 302204, 1925, 16384⟩ := by
  decide +kernel

theorem context_13_302204_565935 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302204 ⟨565935, by decide⟩ :=
  accepted_of_selected 13 302204 ⟨565935, by decide⟩ ⟨13, 2, 0, 565935, 302204, 1925, 16384⟩
    (by decide) selected_cut_22202

theorem selected_cut_22203 : selected 8 ⟨565986, by decide⟩
    (prefixPartial 13 302205) = some ⟨13, 2, 0, 565986, 302205, 3705, 16384⟩ := by
  decide +kernel

theorem context_13_302205_565986 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302205 ⟨565986, by decide⟩ :=
  accepted_of_selected 13 302205 ⟨565986, by decide⟩ ⟨13, 2, 0, 565986, 302205, 3705, 16384⟩
    (by decide) selected_cut_22203

theorem selected_cut_22204 : selected 8 ⟨566030, by decide⟩
    (prefixPartial 13 302206) = some ⟨13, 2, 0, 566030, 302206, 2785, 16384⟩ := by
  decide +kernel

theorem context_13_302206_566030 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302206 ⟨566030, by decide⟩ :=
  accepted_of_selected 13 302206 ⟨566030, by decide⟩ ⟨13, 2, 0, 566030, 302206, 2785, 16384⟩
    (by decide) selected_cut_22204

theorem selected_cut_22205 : selected 8 ⟨566038, by decide⟩
    (prefixPartial 13 302207) = some ⟨13, 2, 0, 566038, 302207, 1013, 16384⟩ := by
  decide +kernel

theorem context_13_302207_566038 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302207 ⟨566038, by decide⟩ :=
  accepted_of_selected 13 302207 ⟨566038, by decide⟩ ⟨13, 2, 0, 566038, 302207, 1013, 16384⟩
    (by decide) selected_cut_22205

theorem unmarked_context_12_75551_566039 : frontier 9 ⟨566039, by decide⟩
    (prefixCache 12 75551) (prefixPartial 12 75551) = false := by
  decide +kernel

theorem node_context_12_75551_566039 : EJMOriginalGlobalDAGData.nodes 9 ⟨566039, by decide⟩ =
    .split (coordinate 12) (![⟨565935, by decide⟩,⟨565986, by decide⟩,⟨566030, by decide⟩,⟨566038, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75551_566039 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75551 ⟨566039, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75551
    ⟨566039, by decide⟩ (by decide) (![⟨565935, by decide⟩,⟨565986, by decide⟩,⟨566030, by decide⟩,⟨566038, by decide⟩]) unmarked_context_12_75551_566039 node_context_12_75551_566039
  intro a
  fin_cases a
  · exact context_13_302204_565935
  · exact context_13_302205_565986
  · exact context_13_302206_566030
  · exact context_13_302207_566038

theorem unmarked_context_11_18887_566040 : frontier 10 ⟨566040, by decide⟩
    (prefixCache 11 18887) (prefixPartial 11 18887) = false := by
  decide +kernel

theorem node_context_11_18887_566040 : EJMOriginalGlobalDAGData.nodes 10 ⟨566040, by decide⟩ =
    .split (coordinate 11) (![⟨565760, by decide⟩,⟨565831, by decide⟩,⟨565912, by decide⟩,⟨566039, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18887_566040 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18887 ⟨566040, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18887
    ⟨566040, by decide⟩ (by decide) (![⟨565760, by decide⟩,⟨565831, by decide⟩,⟨565912, by decide⟩,⟨566039, by decide⟩]) unmarked_context_11_18887_566040 node_context_11_18887_566040
  intro a
  fin_cases a
  · exact context_12_75548_565760
  · exact context_12_75549_565831
  · exact context_12_75550_565912
  · exact context_12_75551_566039

theorem unmarked_context_10_4721_566041 : frontier 11 ⟨566041, by decide⟩
    (prefixCache 10 4721) (prefixPartial 10 4721) = false := by
  decide +kernel

theorem node_context_10_4721_566041 : EJMOriginalGlobalDAGData.nodes 11 ⟨566041, by decide⟩ =
    .split (coordinate 10) (![⟨564945, by decide⟩,⟨565227, by decide⟩,⟨565643, by decide⟩,⟨566040, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4721_566041 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4721 ⟨566041, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4721
    ⟨566041, by decide⟩ (by decide) (![⟨564945, by decide⟩,⟨565227, by decide⟩,⟨565643, by decide⟩,⟨566040, by decide⟩]) unmarked_context_10_4721_566041 node_context_10_4721_566041
  intro a
  fin_cases a
  · exact context_11_18884_564945
  · exact context_11_18885_565227
  · exact context_11_18886_565643
  · exact context_11_18887_566040

theorem selected_cut_22206 : selected 9 ⟨435790, by decide⟩
    (prefixPartial 12 75552) = some ⟨12, 1, 0, 435790, 75552, 1, 65536⟩ := by
  decide +kernel

theorem context_12_75552_435790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75552 ⟨435790, by decide⟩ :=
  accepted_of_selected 12 75552 ⟨435790, by decide⟩ ⟨12, 1, 0, 435790, 75552, 1, 65536⟩
    (by decide) selected_cut_22206

theorem selected_cut_22207 : selected 8 ⟨566064, by decide⟩
    (prefixPartial 13 302212) = some ⟨13, 2, 0, 566064, 302212, 1349, 16384⟩ := by
  decide +kernel

theorem context_13_302212_566064 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302212 ⟨566064, by decide⟩ :=
  accepted_of_selected 13 302212 ⟨566064, by decide⟩ ⟨13, 2, 0, 566064, 302212, 1349, 16384⟩
    (by decide) selected_cut_22207

theorem selected_cut_22208 : selected 8 ⟨566096, by decide⟩
    (prefixPartial 13 302213) = some ⟨13, 2, 0, 566096, 302213, 2229, 16384⟩ := by
  decide +kernel

theorem context_13_302213_566096 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302213 ⟨566096, by decide⟩ :=
  accepted_of_selected 13 302213 ⟨566096, by decide⟩ ⟨13, 2, 0, 566096, 302213, 2229, 16384⟩
    (by decide) selected_cut_22208

theorem selected_cut_22209 : selected 8 ⟨566116, by decide⟩
    (prefixPartial 13 302214) = some ⟨13, 2, 0, 566116, 302214, 1377, 16384⟩ := by
  decide +kernel

theorem context_13_302214_566116 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302214 ⟨566116, by decide⟩ :=
  accepted_of_selected 13 302214 ⟨566116, by decide⟩ ⟨13, 2, 0, 566116, 302214, 1377, 16384⟩
    (by decide) selected_cut_22209

theorem selected_cut_22210 : selected 8 ⟨566122, by decide⟩
    (prefixPartial 13 302215) = some ⟨13, 2, 0, 566122, 302215, 609, 16384⟩ := by
  decide +kernel

theorem context_13_302215_566122 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302215 ⟨566122, by decide⟩ :=
  accepted_of_selected 13 302215 ⟨566122, by decide⟩ ⟨13, 2, 0, 566122, 302215, 609, 16384⟩
    (by decide) selected_cut_22210

theorem unmarked_context_12_75553_566123 : frontier 9 ⟨566123, by decide⟩
    (prefixCache 12 75553) (prefixPartial 12 75553) = false := by
  decide +kernel

theorem node_context_12_75553_566123 : EJMOriginalGlobalDAGData.nodes 9 ⟨566123, by decide⟩ =
    .split (coordinate 12) (![⟨566064, by decide⟩,⟨566096, by decide⟩,⟨566116, by decide⟩,⟨566122, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75553_566123 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75553 ⟨566123, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75553
    ⟨566123, by decide⟩ (by decide) (![⟨566064, by decide⟩,⟨566096, by decide⟩,⟨566116, by decide⟩,⟨566122, by decide⟩]) unmarked_context_12_75553_566123 node_context_12_75553_566123
  intro a
  fin_cases a
  · exact context_13_302212_566064
  · exact context_13_302213_566096
  · exact context_13_302214_566116
  · exact context_13_302215_566122

theorem selected_cut_22211 : selected 8 ⟨566148, by decide⟩
    (prefixPartial 13 302216) = some ⟨13, 2, 0, 566148, 302216, 1401, 16384⟩ := by
  decide +kernel

theorem context_13_302216_566148 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302216 ⟨566148, by decide⟩ :=
  accepted_of_selected 13 302216 ⟨566148, by decide⟩ ⟨13, 2, 0, 566148, 302216, 1401, 16384⟩
    (by decide) selected_cut_22211

theorem selected_cut_22212 : selected 8 ⟨566175, by decide⟩
    (prefixPartial 13 302217) = some ⟨13, 2, 0, 566175, 302217, 2197, 16384⟩ := by
  decide +kernel

theorem context_13_302217_566175 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302217 ⟨566175, by decide⟩ :=
  accepted_of_selected 13 302217 ⟨566175, by decide⟩ ⟨13, 2, 0, 566175, 302217, 2197, 16384⟩
    (by decide) selected_cut_22212

theorem selected_cut_22213 : selected 8 ⟨566192, by decide⟩
    (prefixPartial 13 302218) = some ⟨13, 2, 0, 566192, 302218, 1409, 16384⟩ := by
  decide +kernel

theorem context_13_302218_566192 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302218 ⟨566192, by decide⟩ :=
  accepted_of_selected 13 302218 ⟨566192, by decide⟩ ⟨13, 2, 0, 566192, 302218, 1409, 16384⟩
    (by decide) selected_cut_22213

theorem selected_cut_22214 : selected 8 ⟨566197, by decide⟩
    (prefixPartial 13 302219) = some ⟨13, 2, 0, 566197, 302219, 629, 16384⟩ := by
  decide +kernel

theorem context_13_302219_566197 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302219 ⟨566197, by decide⟩ :=
  accepted_of_selected 13 302219 ⟨566197, by decide⟩ ⟨13, 2, 0, 566197, 302219, 629, 16384⟩
    (by decide) selected_cut_22214

theorem unmarked_context_12_75554_566198 : frontier 9 ⟨566198, by decide⟩
    (prefixCache 12 75554) (prefixPartial 12 75554) = false := by
  decide +kernel

theorem node_context_12_75554_566198 : EJMOriginalGlobalDAGData.nodes 9 ⟨566198, by decide⟩ =
    .split (coordinate 12) (![⟨566148, by decide⟩,⟨566175, by decide⟩,⟨566192, by decide⟩,⟨566197, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75554_566198 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75554 ⟨566198, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75554
    ⟨566198, by decide⟩ (by decide) (![⟨566148, by decide⟩,⟨566175, by decide⟩,⟨566192, by decide⟩,⟨566197, by decide⟩]) unmarked_context_12_75554_566198 node_context_12_75554_566198
  intro a
  fin_cases a
  · exact context_13_302216_566148
  · exact context_13_302217_566175
  · exact context_13_302218_566192
  · exact context_13_302219_566197

theorem selected_cut_22215 : selected 8 ⟨566217, by decide⟩
    (prefixPartial 13 302220) = some ⟨13, 2, 0, 566217, 302220, 1293, 16384⟩ := by
  decide +kernel

theorem context_13_302220_566217 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302220 ⟨566217, by decide⟩ :=
  accepted_of_selected 13 302220 ⟨566217, by decide⟩ ⟨13, 2, 0, 566217, 302220, 1293, 16384⟩
    (by decide) selected_cut_22215

theorem selected_cut_22216 : selected 8 ⟨566241, by decide⟩
    (prefixPartial 13 302221) = some ⟨13, 2, 0, 566241, 302221, 2305, 16384⟩ := by
  decide +kernel

theorem context_13_302221_566241 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302221 ⟨566241, by decide⟩ :=
  accepted_of_selected 13 302221 ⟨566241, by decide⟩ ⟨13, 2, 0, 566241, 302221, 2305, 16384⟩
    (by decide) selected_cut_22216

theorem selected_cut_22217 : selected 8 ⟨566261, by decide⟩
    (prefixPartial 13 302222) = some ⟨13, 2, 0, 566261, 302222, 1565, 16384⟩ := by
  decide +kernel

theorem context_13_302222_566261 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302222 ⟨566261, by decide⟩ :=
  accepted_of_selected 13 302222 ⟨566261, by decide⟩ ⟨13, 2, 0, 566261, 302222, 1565, 16384⟩
    (by decide) selected_cut_22217

theorem selected_cut_22218 : selected 8 ⟨566266, by decide⟩
    (prefixPartial 13 302223) = some ⟨13, 2, 0, 566266, 302223, 565, 16384⟩ := by
  decide +kernel

theorem context_13_302223_566266 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302223 ⟨566266, by decide⟩ :=
  accepted_of_selected 13 302223 ⟨566266, by decide⟩ ⟨13, 2, 0, 566266, 302223, 565, 16384⟩
    (by decide) selected_cut_22218

theorem unmarked_context_12_75555_566267 : frontier 9 ⟨566267, by decide⟩
    (prefixCache 12 75555) (prefixPartial 12 75555) = false := by
  decide +kernel

theorem node_context_12_75555_566267 : EJMOriginalGlobalDAGData.nodes 9 ⟨566267, by decide⟩ =
    .split (coordinate 12) (![⟨566217, by decide⟩,⟨566241, by decide⟩,⟨566261, by decide⟩,⟨566266, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75555_566267 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75555 ⟨566267, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75555
    ⟨566267, by decide⟩ (by decide) (![⟨566217, by decide⟩,⟨566241, by decide⟩,⟨566261, by decide⟩,⟨566266, by decide⟩]) unmarked_context_12_75555_566267 node_context_12_75555_566267
  intro a
  fin_cases a
  · exact context_13_302220_566217
  · exact context_13_302221_566241
  · exact context_13_302222_566261
  · exact context_13_302223_566266

theorem unmarked_context_11_18888_566268 : frontier 10 ⟨566268, by decide⟩
    (prefixCache 11 18888) (prefixPartial 11 18888) = false := by
  decide +kernel

theorem node_context_11_18888_566268 : EJMOriginalGlobalDAGData.nodes 10 ⟨566268, by decide⟩ =
    .split (coordinate 11) (![⟨435790, by decide⟩,⟨566123, by decide⟩,⟨566198, by decide⟩,⟨566267, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18888_566268 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18888 ⟨566268, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18888
    ⟨566268, by decide⟩ (by decide) (![⟨435790, by decide⟩,⟨566123, by decide⟩,⟨566198, by decide⟩,⟨566267, by decide⟩]) unmarked_context_11_18888_566268 node_context_11_18888_566268
  intro a
  fin_cases a
  · exact context_12_75552_435790
  · exact context_12_75553_566123
  · exact context_12_75554_566198
  · exact context_12_75555_566267

theorem selected_cut_22219 : selected 8 ⟨566290, by decide⟩
    (prefixPartial 13 302224) = some ⟨13, 2, 0, 566290, 302224, 1473, 16384⟩ := by
  decide +kernel

theorem context_13_302224_566290 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302224 ⟨566290, by decide⟩ :=
  accepted_of_selected 13 302224 ⟨566290, by decide⟩ ⟨13, 2, 0, 566290, 302224, 1473, 16384⟩
    (by decide) selected_cut_22219

theorem selected_cut_22220 : selected 8 ⟨566342, by decide⟩
    (prefixPartial 13 302225) = some ⟨13, 2, 0, 566342, 302225, 3029, 16384⟩ := by
  decide +kernel

theorem context_13_302225_566342 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302225 ⟨566342, by decide⟩ :=
  accepted_of_selected 13 302225 ⟨566342, by decide⟩ ⟨13, 2, 0, 566342, 302225, 3029, 16384⟩
    (by decide) selected_cut_22220

theorem selected_cut_22221 : selected 8 ⟨566376, by decide⟩
    (prefixPartial 13 302226) = some ⟨13, 2, 0, 566376, 302226, 2053, 16384⟩ := by
  decide +kernel

theorem context_13_302226_566376 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302226 ⟨566376, by decide⟩ :=
  accepted_of_selected 13 302226 ⟨566376, by decide⟩ ⟨13, 2, 0, 566376, 302226, 2053, 16384⟩
    (by decide) selected_cut_22221

theorem selected_cut_22222 : selected 8 ⟨566383, by decide⟩
    (prefixPartial 13 302227) = some ⟨13, 2, 0, 566383, 302227, 1041, 16384⟩ := by
  decide +kernel

theorem context_13_302227_566383 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302227 ⟨566383, by decide⟩ :=
  accepted_of_selected 13 302227 ⟨566383, by decide⟩ ⟨13, 2, 0, 566383, 302227, 1041, 16384⟩
    (by decide) selected_cut_22222

theorem unmarked_context_12_75556_566384 : frontier 9 ⟨566384, by decide⟩
    (prefixCache 12 75556) (prefixPartial 12 75556) = false := by
  decide +kernel

theorem node_context_12_75556_566384 : EJMOriginalGlobalDAGData.nodes 9 ⟨566384, by decide⟩ =
    .split (coordinate 12) (![⟨566290, by decide⟩,⟨566342, by decide⟩,⟨566376, by decide⟩,⟨566383, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75556_566384 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75556 ⟨566384, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75556
    ⟨566384, by decide⟩ (by decide) (![⟨566290, by decide⟩,⟨566342, by decide⟩,⟨566376, by decide⟩,⟨566383, by decide⟩]) unmarked_context_12_75556_566384 node_context_12_75556_566384
  intro a
  fin_cases a
  · exact context_13_302224_566290
  · exact context_13_302225_566342
  · exact context_13_302226_566376
  · exact context_13_302227_566383

theorem selected_cut_22223 : selected 8 ⟨566398, by decide⟩
    (prefixPartial 13 302228) = some ⟨13, 2, 0, 566398, 302228, 1117, 16384⟩ := by
  decide +kernel

theorem context_13_302228_566398 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302228 ⟨566398, by decide⟩ :=
  accepted_of_selected 13 302228 ⟨566398, by decide⟩ ⟨13, 2, 0, 566398, 302228, 1117, 16384⟩
    (by decide) selected_cut_22223

theorem selected_cut_22224 : selected 8 ⟨566418, by decide⟩
    (prefixPartial 13 302229) = some ⟨13, 2, 0, 566418, 302229, 1897, 16384⟩ := by
  decide +kernel

theorem context_13_302229_566418 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302229 ⟨566418, by decide⟩ :=
  accepted_of_selected 13 302229 ⟨566418, by decide⟩ ⟨13, 2, 0, 566418, 302229, 1897, 16384⟩
    (by decide) selected_cut_22224

theorem selected_cut_22225 : selected 8 ⟨566440, by decide⟩
    (prefixPartial 13 302230) = some ⟨13, 2, 0, 566440, 302230, 1389, 16384⟩ := by
  decide +kernel

theorem context_13_302230_566440 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302230 ⟨566440, by decide⟩ :=
  accepted_of_selected 13 302230 ⟨566440, by decide⟩ ⟨13, 2, 0, 566440, 302230, 1389, 16384⟩
    (by decide) selected_cut_22225

theorem selected_cut_22226 : selected 8 ⟨566444, by decide⟩
    (prefixPartial 13 302231) = some ⟨13, 2, 0, 566444, 302231, 649, 16384⟩ := by
  decide +kernel

theorem context_13_302231_566444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302231 ⟨566444, by decide⟩ :=
  accepted_of_selected 13 302231 ⟨566444, by decide⟩ ⟨13, 2, 0, 566444, 302231, 649, 16384⟩
    (by decide) selected_cut_22226

theorem unmarked_context_12_75557_566445 : frontier 9 ⟨566445, by decide⟩
    (prefixCache 12 75557) (prefixPartial 12 75557) = false := by
  decide +kernel

theorem node_context_12_75557_566445 : EJMOriginalGlobalDAGData.nodes 9 ⟨566445, by decide⟩ =
    .split (coordinate 12) (![⟨566398, by decide⟩,⟨566418, by decide⟩,⟨566440, by decide⟩,⟨566444, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75557_566445 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75557 ⟨566445, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75557
    ⟨566445, by decide⟩ (by decide) (![⟨566398, by decide⟩,⟨566418, by decide⟩,⟨566440, by decide⟩,⟨566444, by decide⟩]) unmarked_context_12_75557_566445 node_context_12_75557_566445
  intro a
  fin_cases a
  · exact context_13_302228_566398
  · exact context_13_302229_566418
  · exact context_13_302230_566440
  · exact context_13_302231_566444

theorem selected_cut_22227 : selected 8 ⟨566464, by decide⟩
    (prefixPartial 13 302232) = some ⟨13, 2, 0, 566464, 302232, 1185, 16384⟩ := by
  decide +kernel

theorem context_13_302232_566464 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302232 ⟨566464, by decide⟩ :=
  accepted_of_selected 13 302232 ⟨566464, by decide⟩ ⟨13, 2, 0, 566464, 302232, 1185, 16384⟩
    (by decide) selected_cut_22227

theorem selected_cut_22228 : selected 8 ⟨566492, by decide⟩
    (prefixPartial 13 302233) = some ⟨13, 2, 0, 566492, 302233, 2085, 16384⟩ := by
  decide +kernel

theorem context_13_302233_566492 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302233 ⟨566492, by decide⟩ :=
  accepted_of_selected 13 302233 ⟨566492, by decide⟩ ⟨13, 2, 0, 566492, 302233, 2085, 16384⟩
    (by decide) selected_cut_22228

theorem selected_cut_22229 : selected 8 ⟨566511, by decide⟩
    (prefixPartial 13 302234) = some ⟨13, 2, 0, 566511, 302234, 1373, 16384⟩ := by
  decide +kernel

theorem context_13_302234_566511 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302234 ⟨566511, by decide⟩ :=
  accepted_of_selected 13 302234 ⟨566511, by decide⟩ ⟨13, 2, 0, 566511, 302234, 1373, 16384⟩
    (by decide) selected_cut_22229

theorem selected_cut_22230 : selected 8 ⟨566520, by decide⟩
    (prefixPartial 13 302235) = some ⟨13, 2, 0, 566520, 302235, 813, 16384⟩ := by
  decide +kernel

theorem context_13_302235_566520 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302235 ⟨566520, by decide⟩ :=
  accepted_of_selected 13 302235 ⟨566520, by decide⟩ ⟨13, 2, 0, 566520, 302235, 813, 16384⟩
    (by decide) selected_cut_22230

theorem unmarked_context_12_75558_566521 : frontier 9 ⟨566521, by decide⟩
    (prefixCache 12 75558) (prefixPartial 12 75558) = false := by
  decide +kernel

theorem node_context_12_75558_566521 : EJMOriginalGlobalDAGData.nodes 9 ⟨566521, by decide⟩ =
    .split (coordinate 12) (![⟨566464, by decide⟩,⟨566492, by decide⟩,⟨566511, by decide⟩,⟨566520, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75558_566521 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75558 ⟨566521, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75558
    ⟨566521, by decide⟩ (by decide) (![⟨566464, by decide⟩,⟨566492, by decide⟩,⟨566511, by decide⟩,⟨566520, by decide⟩]) unmarked_context_12_75558_566521 node_context_12_75558_566521
  intro a
  fin_cases a
  · exact context_13_302232_566464
  · exact context_13_302233_566492
  · exact context_13_302234_566511
  · exact context_13_302235_566520

theorem selected_cut_22231 : selected 8 ⟨566544, by decide⟩
    (prefixPartial 13 302236) = some ⟨13, 2, 0, 566544, 302236, 1097, 16384⟩ := by
  decide +kernel

theorem context_13_302236_566544 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302236 ⟨566544, by decide⟩ :=
  accepted_of_selected 13 302236 ⟨566544, by decide⟩ ⟨13, 2, 0, 566544, 302236, 1097, 16384⟩
    (by decide) selected_cut_22231

theorem selected_cut_22232 : selected 8 ⟨566572, by decide⟩
    (prefixPartial 13 302237) = some ⟨13, 2, 0, 566572, 302237, 2117, 16384⟩ := by
  decide +kernel

theorem context_13_302237_566572 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302237 ⟨566572, by decide⟩ :=
  accepted_of_selected 13 302237 ⟨566572, by decide⟩ ⟨13, 2, 0, 566572, 302237, 2117, 16384⟩
    (by decide) selected_cut_22232

theorem selected_cut_22233 : selected 8 ⟨566594, by decide⟩
    (prefixPartial 13 302238) = some ⟨13, 2, 0, 566594, 302238, 1673, 16384⟩ := by
  decide +kernel

theorem context_13_302238_566594 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302238 ⟨566594, by decide⟩ :=
  accepted_of_selected 13 302238 ⟨566594, by decide⟩ ⟨13, 2, 0, 566594, 302238, 1673, 16384⟩
    (by decide) selected_cut_22233

theorem selected_cut_22234 : selected 8 ⟨566601, by decide⟩
    (prefixPartial 13 302239) = some ⟨13, 2, 0, 566601, 302239, 689, 16384⟩ := by
  decide +kernel

theorem context_13_302239_566601 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302239 ⟨566601, by decide⟩ :=
  accepted_of_selected 13 302239 ⟨566601, by decide⟩ ⟨13, 2, 0, 566601, 302239, 689, 16384⟩
    (by decide) selected_cut_22234

theorem unmarked_context_12_75559_566602 : frontier 9 ⟨566602, by decide⟩
    (prefixCache 12 75559) (prefixPartial 12 75559) = false := by
  decide +kernel

theorem node_context_12_75559_566602 : EJMOriginalGlobalDAGData.nodes 9 ⟨566602, by decide⟩ =
    .split (coordinate 12) (![⟨566544, by decide⟩,⟨566572, by decide⟩,⟨566594, by decide⟩,⟨566601, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75559_566602 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75559 ⟨566602, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75559
    ⟨566602, by decide⟩ (by decide) (![⟨566544, by decide⟩,⟨566572, by decide⟩,⟨566594, by decide⟩,⟨566601, by decide⟩]) unmarked_context_12_75559_566602 node_context_12_75559_566602
  intro a
  fin_cases a
  · exact context_13_302236_566544
  · exact context_13_302237_566572
  · exact context_13_302238_566594
  · exact context_13_302239_566601

theorem unmarked_context_11_18889_566603 : frontier 10 ⟨566603, by decide⟩
    (prefixCache 11 18889) (prefixPartial 11 18889) = false := by
  decide +kernel

theorem node_context_11_18889_566603 : EJMOriginalGlobalDAGData.nodes 10 ⟨566603, by decide⟩ =
    .split (coordinate 11) (![⟨566384, by decide⟩,⟨566445, by decide⟩,⟨566521, by decide⟩,⟨566602, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18889_566603 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18889 ⟨566603, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18889
    ⟨566603, by decide⟩ (by decide) (![⟨566384, by decide⟩,⟨566445, by decide⟩,⟨566521, by decide⟩,⟨566602, by decide⟩]) unmarked_context_11_18889_566603 node_context_11_18889_566603
  intro a
  fin_cases a
  · exact context_12_75556_566384
  · exact context_12_75557_566445
  · exact context_12_75558_566521
  · exact context_12_75559_566602

theorem selected_cut_22235 : selected 9 ⟨435790, by decide⟩
    (prefixPartial 12 75560) = some ⟨12, 1, 0, 435790, 75560, 1, 65536⟩ := by
  decide +kernel

theorem context_12_75560_435790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75560 ⟨435790, by decide⟩ :=
  accepted_of_selected 12 75560 ⟨435790, by decide⟩ ⟨12, 1, 0, 435790, 75560, 1, 65536⟩
    (by decide) selected_cut_22235

theorem selected_cut_22236 : selected 8 ⟨566617, by decide⟩
    (prefixPartial 13 302244) = some ⟨13, 2, 0, 566617, 302244, 905, 16384⟩ := by
  decide +kernel

theorem context_13_302244_566617 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302244 ⟨566617, by decide⟩ :=
  accepted_of_selected 13 302244 ⟨566617, by decide⟩ ⟨13, 2, 0, 566617, 302244, 905, 16384⟩
    (by decide) selected_cut_22236

theorem selected_cut_22237 : selected 8 ⟨566644, by decide⟩
    (prefixPartial 13 302245) = some ⟨13, 2, 0, 566644, 302245, 2141, 16384⟩ := by
  decide +kernel

theorem context_13_302245_566644 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302245 ⟨566644, by decide⟩ :=
  accepted_of_selected 13 302245 ⟨566644, by decide⟩ ⟨13, 2, 0, 566644, 302245, 2141, 16384⟩
    (by decide) selected_cut_22237

theorem selected_cut_22238 : selected 8 ⟨566663, by decide⟩
    (prefixPartial 13 302246) = some ⟨13, 2, 0, 566663, 302246, 1445, 16384⟩ := by
  decide +kernel

theorem context_13_302246_566663 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302246 ⟨566663, by decide⟩ :=
  accepted_of_selected 13 302246 ⟨566663, by decide⟩ ⟨13, 2, 0, 566663, 302246, 1445, 16384⟩
    (by decide) selected_cut_22238

theorem selected_cut_22239 : selected 8 ⟨566669, by decide⟩
    (prefixPartial 13 302247) = some ⟨13, 2, 0, 566669, 302247, 749, 16384⟩ := by
  decide +kernel

theorem context_13_302247_566669 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302247 ⟨566669, by decide⟩ :=
  accepted_of_selected 13 302247 ⟨566669, by decide⟩ ⟨13, 2, 0, 566669, 302247, 749, 16384⟩
    (by decide) selected_cut_22239

theorem unmarked_context_12_75561_566670 : frontier 9 ⟨566670, by decide⟩
    (prefixCache 12 75561) (prefixPartial 12 75561) = false := by
  decide +kernel

theorem node_context_12_75561_566670 : EJMOriginalGlobalDAGData.nodes 9 ⟨566670, by decide⟩ =
    .split (coordinate 12) (![⟨566617, by decide⟩,⟨566644, by decide⟩,⟨566663, by decide⟩,⟨566669, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75561_566670 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75561 ⟨566670, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75561
    ⟨566670, by decide⟩ (by decide) (![⟨566617, by decide⟩,⟨566644, by decide⟩,⟨566663, by decide⟩,⟨566669, by decide⟩]) unmarked_context_12_75561_566670 node_context_12_75561_566670
  intro a
  fin_cases a
  · exact context_13_302244_566617
  · exact context_13_302245_566644
  · exact context_13_302246_566663
  · exact context_13_302247_566669

theorem selected_cut_22240 : selected 8 ⟨566689, by decide⟩
    (prefixPartial 13 302248) = some ⟨13, 2, 0, 566689, 302248, 829, 16384⟩ := by
  decide +kernel

theorem context_13_302248_566689 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302248 ⟨566689, by decide⟩ :=
  accepted_of_selected 13 302248 ⟨566689, by decide⟩ ⟨13, 2, 0, 566689, 302248, 829, 16384⟩
    (by decide) selected_cut_22240

theorem selected_cut_22241 : selected 8 ⟨566722, by decide⟩
    (prefixPartial 13 302249) = some ⟨13, 2, 0, 566722, 302249, 2353, 16384⟩ := by
  decide +kernel

theorem context_13_302249_566722 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302249 ⟨566722, by decide⟩ :=
  accepted_of_selected 13 302249 ⟨566722, by decide⟩ ⟨13, 2, 0, 566722, 302249, 2353, 16384⟩
    (by decide) selected_cut_22241

theorem selected_cut_22242 : selected 8 ⟨566743, by decide⟩
    (prefixPartial 13 302250) = some ⟨13, 2, 0, 566743, 302250, 1425, 16384⟩ := by
  decide +kernel

theorem context_13_302250_566743 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302250 ⟨566743, by decide⟩ :=
  accepted_of_selected 13 302250 ⟨566743, by decide⟩ ⟨13, 2, 0, 566743, 302250, 1425, 16384⟩
    (by decide) selected_cut_22242

theorem selected_cut_22243 : selected 8 ⟨566753, by decide⟩
    (prefixPartial 13 302251) = some ⟨13, 2, 0, 566753, 302251, 769, 16384⟩ := by
  decide +kernel

theorem context_13_302251_566753 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302251 ⟨566753, by decide⟩ :=
  accepted_of_selected 13 302251 ⟨566753, by decide⟩ ⟨13, 2, 0, 566753, 302251, 769, 16384⟩
    (by decide) selected_cut_22243

theorem unmarked_context_12_75562_566754 : frontier 9 ⟨566754, by decide⟩
    (prefixCache 12 75562) (prefixPartial 12 75562) = false := by
  decide +kernel

theorem node_context_12_75562_566754 : EJMOriginalGlobalDAGData.nodes 9 ⟨566754, by decide⟩ =
    .split (coordinate 12) (![⟨566689, by decide⟩,⟨566722, by decide⟩,⟨566743, by decide⟩,⟨566753, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75562_566754 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75562 ⟨566754, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75562
    ⟨566754, by decide⟩ (by decide) (![⟨566689, by decide⟩,⟨566722, by decide⟩,⟨566743, by decide⟩,⟨566753, by decide⟩]) unmarked_context_12_75562_566754 node_context_12_75562_566754
  intro a
  fin_cases a
  · exact context_13_302248_566689
  · exact context_13_302249_566722
  · exact context_13_302250_566743
  · exact context_13_302251_566753

theorem selected_cut_22244 : selected 8 ⟨566764, by decide⟩
    (prefixPartial 13 302252) = some ⟨13, 2, 0, 566764, 302252, 785, 16384⟩ := by
  decide +kernel

theorem context_13_302252_566764 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302252 ⟨566764, by decide⟩ :=
  accepted_of_selected 13 302252 ⟨566764, by decide⟩ ⟨13, 2, 0, 566764, 302252, 785, 16384⟩
    (by decide) selected_cut_22244

theorem selected_cut_22245 : selected 8 ⟨566795, by decide⟩
    (prefixPartial 13 302253) = some ⟨13, 2, 0, 566795, 302253, 2505, 16384⟩ := by
  decide +kernel

theorem context_13_302253_566795 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302253 ⟨566795, by decide⟩ :=
  accepted_of_selected 13 302253 ⟨566795, by decide⟩ ⟨13, 2, 0, 566795, 302253, 2505, 16384⟩
    (by decide) selected_cut_22245

theorem selected_cut_22246 : selected 8 ⟨566813, by decide⟩
    (prefixPartial 13 302254) = some ⟨13, 2, 0, 566813, 302254, 1533, 16384⟩ := by
  decide +kernel

theorem context_13_302254_566813 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302254 ⟨566813, by decide⟩ :=
  accepted_of_selected 13 302254 ⟨566813, by decide⟩ ⟨13, 2, 0, 566813, 302254, 1533, 16384⟩
    (by decide) selected_cut_22246

theorem selected_cut_22247 : selected 8 ⟨566820, by decide⟩
    (prefixPartial 13 302255) = some ⟨13, 2, 0, 566820, 302255, 665, 16384⟩ := by
  decide +kernel

theorem context_13_302255_566820 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302255 ⟨566820, by decide⟩ :=
  accepted_of_selected 13 302255 ⟨566820, by decide⟩ ⟨13, 2, 0, 566820, 302255, 665, 16384⟩
    (by decide) selected_cut_22247

theorem unmarked_context_12_75563_566821 : frontier 9 ⟨566821, by decide⟩
    (prefixCache 12 75563) (prefixPartial 12 75563) = false := by
  decide +kernel

theorem node_context_12_75563_566821 : EJMOriginalGlobalDAGData.nodes 9 ⟨566821, by decide⟩ =
    .split (coordinate 12) (![⟨566764, by decide⟩,⟨566795, by decide⟩,⟨566813, by decide⟩,⟨566820, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75563_566821 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75563 ⟨566821, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75563
    ⟨566821, by decide⟩ (by decide) (![⟨566764, by decide⟩,⟨566795, by decide⟩,⟨566813, by decide⟩,⟨566820, by decide⟩]) unmarked_context_12_75563_566821 node_context_12_75563_566821
  intro a
  fin_cases a
  · exact context_13_302252_566764
  · exact context_13_302253_566795
  · exact context_13_302254_566813
  · exact context_13_302255_566820

theorem unmarked_context_11_18890_566822 : frontier 10 ⟨566822, by decide⟩
    (prefixCache 11 18890) (prefixPartial 11 18890) = false := by
  decide +kernel

theorem node_context_11_18890_566822 : EJMOriginalGlobalDAGData.nodes 10 ⟨566822, by decide⟩ =
    .split (coordinate 11) (![⟨435790, by decide⟩,⟨566670, by decide⟩,⟨566754, by decide⟩,⟨566821, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18890_566822 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18890 ⟨566822, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18890
    ⟨566822, by decide⟩ (by decide) (![⟨435790, by decide⟩,⟨566670, by decide⟩,⟨566754, by decide⟩,⟨566821, by decide⟩]) unmarked_context_11_18890_566822 node_context_11_18890_566822
  intro a
  fin_cases a
  · exact context_12_75560_435790
  · exact context_12_75561_566670
  · exact context_12_75562_566754
  · exact context_12_75563_566821

theorem selected_cut_22248 : selected 8 ⟨566837, by decide⟩
    (prefixPartial 13 302256) = some ⟨13, 2, 0, 566837, 302256, 977, 16384⟩ := by
  decide +kernel

theorem context_13_302256_566837 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302256 ⟨566837, by decide⟩ :=
  accepted_of_selected 13 302256 ⟨566837, by decide⟩ ⟨13, 2, 0, 566837, 302256, 977, 16384⟩
    (by decide) selected_cut_22248

theorem selected_cut_22249 : selected 8 ⟨566881, by decide⟩
    (prefixPartial 13 302257) = some ⟨13, 2, 0, 566881, 302257, 3281, 16384⟩ := by
  decide +kernel

theorem context_13_302257_566881 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302257 ⟨566881, by decide⟩ :=
  accepted_of_selected 13 302257 ⟨566881, by decide⟩ ⟨13, 2, 0, 566881, 302257, 3281, 16384⟩
    (by decide) selected_cut_22249

theorem selected_cut_22250 : selected 8 ⟨566903, by decide⟩
    (prefixPartial 13 302258) = some ⟨13, 2, 0, 566903, 302258, 1965, 16384⟩ := by
  decide +kernel

theorem context_13_302258_566903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302258 ⟨566903, by decide⟩ :=
  accepted_of_selected 13 302258 ⟨566903, by decide⟩ ⟨13, 2, 0, 566903, 302258, 1965, 16384⟩
    (by decide) selected_cut_22250

theorem selected_cut_22251 : selected 8 ⟨566910, by decide⟩
    (prefixPartial 13 302259) = some ⟨13, 2, 0, 566910, 302259, 909, 16384⟩ := by
  decide +kernel

theorem context_13_302259_566910 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302259 ⟨566910, by decide⟩ :=
  accepted_of_selected 13 302259 ⟨566910, by decide⟩ ⟨13, 2, 0, 566910, 302259, 909, 16384⟩
    (by decide) selected_cut_22251

theorem unmarked_context_12_75564_566911 : frontier 9 ⟨566911, by decide⟩
    (prefixCache 12 75564) (prefixPartial 12 75564) = false := by
  decide +kernel

theorem node_context_12_75564_566911 : EJMOriginalGlobalDAGData.nodes 9 ⟨566911, by decide⟩ =
    .split (coordinate 12) (![⟨566837, by decide⟩,⟨566881, by decide⟩,⟨566903, by decide⟩,⟨566910, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75564_566911 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75564 ⟨566911, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75564
    ⟨566911, by decide⟩ (by decide) (![⟨566837, by decide⟩,⟨566881, by decide⟩,⟨566903, by decide⟩,⟨566910, by decide⟩]) unmarked_context_12_75564_566911 node_context_12_75564_566911
  intro a
  fin_cases a
  · exact context_13_302256_566837
  · exact context_13_302257_566881
  · exact context_13_302258_566903
  · exact context_13_302259_566910

theorem selected_cut_22252 : selected 8 ⟨566920, by decide⟩
    (prefixPartial 13 302260) = some ⟨13, 2, 0, 566920, 302260, 709, 16384⟩ := by
  decide +kernel

theorem context_13_302260_566920 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302260 ⟨566920, by decide⟩ :=
  accepted_of_selected 13 302260 ⟨566920, by decide⟩ ⟨13, 2, 0, 566920, 302260, 709, 16384⟩
    (by decide) selected_cut_22252

theorem selected_cut_22253 : selected 8 ⟨566946, by decide⟩
    (prefixPartial 13 302261) = some ⟨13, 2, 0, 566946, 302261, 2349, 16384⟩ := by
  decide +kernel

theorem context_13_302261_566946 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302261 ⟨566946, by decide⟩ :=
  accepted_of_selected 13 302261 ⟨566946, by decide⟩ ⟨13, 2, 0, 566946, 302261, 2349, 16384⟩
    (by decide) selected_cut_22253

theorem selected_cut_22254 : selected 8 ⟨566966, by decide⟩
    (prefixPartial 13 302262) = some ⟨13, 2, 0, 566966, 302262, 1521, 16384⟩ := by
  decide +kernel

theorem context_13_302262_566966 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302262 ⟨566966, by decide⟩ :=
  accepted_of_selected 13 302262 ⟨566966, by decide⟩ ⟨13, 2, 0, 566966, 302262, 1521, 16384⟩
    (by decide) selected_cut_22254

theorem selected_cut_22255 : selected 8 ⟨566971, by decide⟩
    (prefixPartial 13 302263) = some ⟨13, 2, 0, 566971, 302263, 629, 16384⟩ := by
  decide +kernel

theorem context_13_302263_566971 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302263 ⟨566971, by decide⟩ :=
  accepted_of_selected 13 302263 ⟨566971, by decide⟩ ⟨13, 2, 0, 566971, 302263, 629, 16384⟩
    (by decide) selected_cut_22255

theorem unmarked_context_12_75565_566972 : frontier 9 ⟨566972, by decide⟩
    (prefixCache 12 75565) (prefixPartial 12 75565) = false := by
  decide +kernel

theorem node_context_12_75565_566972 : EJMOriginalGlobalDAGData.nodes 9 ⟨566972, by decide⟩ =
    .split (coordinate 12) (![⟨566920, by decide⟩,⟨566946, by decide⟩,⟨566966, by decide⟩,⟨566971, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75565_566972 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75565 ⟨566972, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75565
    ⟨566972, by decide⟩ (by decide) (![⟨566920, by decide⟩,⟨566946, by decide⟩,⟨566966, by decide⟩,⟨566971, by decide⟩]) unmarked_context_12_75565_566972 node_context_12_75565_566972
  intro a
  fin_cases a
  · exact context_13_302260_566920
  · exact context_13_302261_566946
  · exact context_13_302262_566966
  · exact context_13_302263_566971

theorem selected_cut_22256 : selected 8 ⟨566985, by decide⟩
    (prefixPartial 13 302264) = some ⟨13, 2, 0, 566985, 302264, 653, 16384⟩ := by
  decide +kernel

theorem context_13_302264_566985 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302264 ⟨566985, by decide⟩ :=
  accepted_of_selected 13 302264 ⟨566985, by decide⟩ ⟨13, 2, 0, 566985, 302264, 653, 16384⟩
    (by decide) selected_cut_22256

theorem selected_cut_22257 : selected 8 ⟨567016, by decide⟩
    (prefixPartial 13 302265) = some ⟨13, 2, 0, 567016, 302265, 2621, 16384⟩ := by
  decide +kernel

theorem context_13_302265_567016 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302265 ⟨567016, by decide⟩ :=
  accepted_of_selected 13 302265 ⟨567016, by decide⟩ ⟨13, 2, 0, 567016, 302265, 2621, 16384⟩
    (by decide) selected_cut_22257

theorem selected_cut_22258 : selected 8 ⟨567031, by decide⟩
    (prefixPartial 13 302266) = some ⟨13, 2, 0, 567031, 302266, 1317, 16384⟩ := by
  decide +kernel

theorem context_13_302266_567031 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302266 ⟨567031, by decide⟩ :=
  accepted_of_selected 13 302266 ⟨567031, by decide⟩ ⟨13, 2, 0, 567031, 302266, 1317, 16384⟩
    (by decide) selected_cut_22258

theorem selected_cut_22259 : selected 8 ⟨567038, by decide⟩
    (prefixPartial 13 302267) = some ⟨13, 2, 0, 567038, 302267, 701, 16384⟩ := by
  decide +kernel

theorem context_13_302267_567038 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302267 ⟨567038, by decide⟩ :=
  accepted_of_selected 13 302267 ⟨567038, by decide⟩ ⟨13, 2, 0, 567038, 302267, 701, 16384⟩
    (by decide) selected_cut_22259

theorem unmarked_context_12_75566_567039 : frontier 9 ⟨567039, by decide⟩
    (prefixCache 12 75566) (prefixPartial 12 75566) = false := by
  decide +kernel

theorem node_context_12_75566_567039 : EJMOriginalGlobalDAGData.nodes 9 ⟨567039, by decide⟩ =
    .split (coordinate 12) (![⟨566985, by decide⟩,⟨567016, by decide⟩,⟨567031, by decide⟩,⟨567038, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75566_567039 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75566 ⟨567039, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75566
    ⟨567039, by decide⟩ (by decide) (![⟨566985, by decide⟩,⟨567016, by decide⟩,⟨567031, by decide⟩,⟨567038, by decide⟩]) unmarked_context_12_75566_567039 node_context_12_75566_567039
  intro a
  fin_cases a
  · exact context_13_302264_566985
  · exact context_13_302265_567016
  · exact context_13_302266_567031
  · exact context_13_302267_567038

theorem selected_cut_22260 : selected 8 ⟨567061, by decide⟩
    (prefixPartial 13 302268) = some ⟨13, 2, 0, 567061, 302268, 949, 16384⟩ := by
  decide +kernel

theorem context_13_302268_567061 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302268 ⟨567061, by decide⟩ :=
  accepted_of_selected 13 302268 ⟨567061, by decide⟩ ⟨13, 2, 0, 567061, 302268, 949, 16384⟩
    (by decide) selected_cut_22260

theorem selected_cut_22261 : selected 8 ⟨567134, by decide⟩
    (prefixPartial 13 302269) = some ⟨13, 2, 0, 567134, 302269, 3949, 16384⟩ := by
  decide +kernel

theorem context_13_302269_567134 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302269 ⟨567134, by decide⟩ :=
  accepted_of_selected 13 302269 ⟨567134, by decide⟩ ⟨13, 2, 0, 567134, 302269, 3949, 16384⟩
    (by decide) selected_cut_22261

theorem selected_cut_22262 : selected 8 ⟨567173, by decide⟩
    (prefixPartial 13 302270) = some ⟨13, 2, 0, 567173, 302270, 2461, 16384⟩ := by
  decide +kernel

theorem context_13_302270_567173 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302270 ⟨567173, by decide⟩ :=
  accepted_of_selected 13 302270 ⟨567173, by decide⟩ ⟨13, 2, 0, 567173, 302270, 2461, 16384⟩
    (by decide) selected_cut_22262

theorem selected_cut_22263 : selected 8 ⟨567178, by decide⟩
    (prefixPartial 13 302271) = some ⟨13, 2, 0, 567178, 302271, 909, 16384⟩ := by
  decide +kernel

theorem context_13_302271_567178 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302271 ⟨567178, by decide⟩ :=
  accepted_of_selected 13 302271 ⟨567178, by decide⟩ ⟨13, 2, 0, 567178, 302271, 909, 16384⟩
    (by decide) selected_cut_22263

theorem unmarked_context_12_75567_567179 : frontier 9 ⟨567179, by decide⟩
    (prefixCache 12 75567) (prefixPartial 12 75567) = false := by
  decide +kernel

theorem node_context_12_75567_567179 : EJMOriginalGlobalDAGData.nodes 9 ⟨567179, by decide⟩ =
    .split (coordinate 12) (![⟨567061, by decide⟩,⟨567134, by decide⟩,⟨567173, by decide⟩,⟨567178, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75567_567179 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75567 ⟨567179, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75567
    ⟨567179, by decide⟩ (by decide) (![⟨567061, by decide⟩,⟨567134, by decide⟩,⟨567173, by decide⟩,⟨567178, by decide⟩]) unmarked_context_12_75567_567179 node_context_12_75567_567179
  intro a
  fin_cases a
  · exact context_13_302268_567061
  · exact context_13_302269_567134
  · exact context_13_302270_567173
  · exact context_13_302271_567178

theorem unmarked_context_11_18891_567180 : frontier 10 ⟨567180, by decide⟩
    (prefixCache 11 18891) (prefixPartial 11 18891) = false := by
  decide +kernel

theorem node_context_11_18891_567180 : EJMOriginalGlobalDAGData.nodes 10 ⟨567180, by decide⟩ =
    .split (coordinate 11) (![⟨566911, by decide⟩,⟨566972, by decide⟩,⟨567039, by decide⟩,⟨567179, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18891_567180 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18891 ⟨567180, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18891
    ⟨567180, by decide⟩ (by decide) (![⟨566911, by decide⟩,⟨566972, by decide⟩,⟨567039, by decide⟩,⟨567179, by decide⟩]) unmarked_context_11_18891_567180 node_context_11_18891_567180
  intro a
  fin_cases a
  · exact context_12_75564_566911
  · exact context_12_75565_566972
  · exact context_12_75566_567039
  · exact context_12_75567_567179

theorem unmarked_context_10_4722_567181 : frontier 11 ⟨567181, by decide⟩
    (prefixCache 10 4722) (prefixPartial 10 4722) = false := by
  decide +kernel

theorem node_context_10_4722_567181 : EJMOriginalGlobalDAGData.nodes 11 ⟨567181, by decide⟩ =
    .split (coordinate 10) (![⟨566268, by decide⟩,⟨566603, by decide⟩,⟨566822, by decide⟩,⟨567180, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4722_567181 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4722 ⟨567181, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4722
    ⟨567181, by decide⟩ (by decide) (![⟨566268, by decide⟩,⟨566603, by decide⟩,⟨566822, by decide⟩,⟨567180, by decide⟩]) unmarked_context_10_4722_567181 node_context_10_4722_567181
  intro a
  fin_cases a
  · exact context_11_18888_566268
  · exact context_11_18889_566603
  · exact context_11_18890_566822
  · exact context_11_18891_567180

theorem selected_cut_22264 : selected 9 ⟨445562, by decide⟩
    (prefixPartial 12 75568) = some ⟨12, 1, 0, 445562, 75568, 1, 65536⟩ := by
  decide +kernel

theorem context_12_75568_445562 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75568 ⟨445562, by decide⟩ :=
  accepted_of_selected 12 75568 ⟨445562, by decide⟩ ⟨12, 1, 0, 445562, 75568, 1, 65536⟩
    (by decide) selected_cut_22264

theorem selected_cut_22265 : selected 8 ⟨567188, by decide⟩
    (prefixPartial 13 302276) = some ⟨13, 2, 0, 567188, 302276, 481, 16384⟩ := by
  decide +kernel

theorem context_13_302276_567188 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302276 ⟨567188, by decide⟩ :=
  accepted_of_selected 13 302276 ⟨567188, by decide⟩ ⟨13, 2, 0, 567188, 302276, 481, 16384⟩
    (by decide) selected_cut_22265

theorem selected_cut_22266 : selected 8 ⟨567232, by decide⟩
    (prefixPartial 13 302277) = some ⟨13, 2, 0, 567232, 302277, 2629, 16384⟩ := by
  decide +kernel

theorem context_13_302277_567232 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302277 ⟨567232, by decide⟩ :=
  accepted_of_selected 13 302277 ⟨567232, by decide⟩ ⟨13, 2, 0, 567232, 302277, 2629, 16384⟩
    (by decide) selected_cut_22266

theorem selected_cut_22267 : selected 8 ⟨567253, by decide⟩
    (prefixPartial 13 302278) = some ⟨13, 2, 0, 567253, 302278, 1585, 16384⟩ := by
  decide +kernel

theorem context_13_302278_567253 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302278 ⟨567253, by decide⟩ :=
  accepted_of_selected 13 302278 ⟨567253, by decide⟩ ⟨13, 2, 0, 567253, 302278, 1585, 16384⟩
    (by decide) selected_cut_22267

theorem selected_cut_22268 : selected 8 ⟨567260, by decide⟩
    (prefixPartial 13 302279) = some ⟨13, 2, 0, 567260, 302279, 737, 16384⟩ := by
  decide +kernel

theorem context_13_302279_567260 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302279 ⟨567260, by decide⟩ :=
  accepted_of_selected 13 302279 ⟨567260, by decide⟩ ⟨13, 2, 0, 567260, 302279, 737, 16384⟩
    (by decide) selected_cut_22268

theorem unmarked_context_12_75569_567261 : frontier 9 ⟨567261, by decide⟩
    (prefixCache 12 75569) (prefixPartial 12 75569) = false := by
  decide +kernel

theorem node_context_12_75569_567261 : EJMOriginalGlobalDAGData.nodes 9 ⟨567261, by decide⟩ =
    .split (coordinate 12) (![⟨567188, by decide⟩,⟨567232, by decide⟩,⟨567253, by decide⟩,⟨567260, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75569_567261 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75569 ⟨567261, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75569
    ⟨567261, by decide⟩ (by decide) (![⟨567188, by decide⟩,⟨567232, by decide⟩,⟨567253, by decide⟩,⟨567260, by decide⟩]) unmarked_context_12_75569_567261 node_context_12_75569_567261
  intro a
  fin_cases a
  · exact context_13_302276_567188
  · exact context_13_302277_567232
  · exact context_13_302278_567253
  · exact context_13_302279_567260

theorem selected_cut_22269 : selected 8 ⟨567268, by decide⟩
    (prefixPartial 13 302280) = some ⟨13, 2, 0, 567268, 302280, 449, 16384⟩ := by
  decide +kernel

theorem context_13_302280_567268 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302280 ⟨567268, by decide⟩ :=
  accepted_of_selected 13 302280 ⟨567268, by decide⟩ ⟨13, 2, 0, 567268, 302280, 449, 16384⟩
    (by decide) selected_cut_22269

theorem selected_cut_22270 : selected 8 ⟨567302, by decide⟩
    (prefixPartial 13 302281) = some ⟨13, 2, 0, 567302, 302281, 2537, 16384⟩ := by
  decide +kernel

theorem context_13_302281_567302 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302281 ⟨567302, by decide⟩ :=
  accepted_of_selected 13 302281 ⟨567302, by decide⟩ ⟨13, 2, 0, 567302, 302281, 2537, 16384⟩
    (by decide) selected_cut_22270

theorem selected_cut_22271 : selected 8 ⟨567321, by decide⟩
    (prefixPartial 13 302282) = some ⟨13, 2, 0, 567321, 302282, 1553, 16384⟩ := by
  decide +kernel

theorem context_13_302282_567321 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302282 ⟨567321, by decide⟩ :=
  accepted_of_selected 13 302282 ⟨567321, by decide⟩ ⟨13, 2, 0, 567321, 302282, 1553, 16384⟩
    (by decide) selected_cut_22271

theorem selected_cut_22272 : selected 8 ⟨567327, by decide⟩
    (prefixPartial 13 302283) = some ⟨13, 2, 0, 567327, 302283, 813, 16384⟩ := by
  decide +kernel

theorem context_13_302283_567327 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302283 ⟨567327, by decide⟩ :=
  accepted_of_selected 13 302283 ⟨567327, by decide⟩ ⟨13, 2, 0, 567327, 302283, 813, 16384⟩
    (by decide) selected_cut_22272

theorem unmarked_context_12_75570_567328 : frontier 9 ⟨567328, by decide⟩
    (prefixCache 12 75570) (prefixPartial 12 75570) = false := by
  decide +kernel

theorem node_context_12_75570_567328 : EJMOriginalGlobalDAGData.nodes 9 ⟨567328, by decide⟩ =
    .split (coordinate 12) (![⟨567268, by decide⟩,⟨567302, by decide⟩,⟨567321, by decide⟩,⟨567327, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75570_567328 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75570 ⟨567328, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75570
    ⟨567328, by decide⟩ (by decide) (![⟨567268, by decide⟩,⟨567302, by decide⟩,⟨567321, by decide⟩,⟨567327, by decide⟩]) unmarked_context_12_75570_567328 node_context_12_75570_567328
  intro a
  fin_cases a
  · exact context_13_302280_567268
  · exact context_13_302281_567302
  · exact context_13_302282_567321
  · exact context_13_302283_567327

theorem selected_cut_22273 : selected 8 ⟨567333, by decide⟩
    (prefixPartial 13 302284) = some ⟨13, 2, 0, 567333, 302284, 377, 16384⟩ := by
  decide +kernel

theorem context_13_302284_567333 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302284 ⟨567333, by decide⟩ :=
  accepted_of_selected 13 302284 ⟨567333, by decide⟩ ⟨13, 2, 0, 567333, 302284, 377, 16384⟩
    (by decide) selected_cut_22273

theorem selected_cut_22274 : selected 8 ⟨567357, by decide⟩
    (prefixPartial 13 302285) = some ⟨13, 2, 0, 567357, 302285, 2441, 16384⟩ := by
  decide +kernel

theorem context_13_302285_567357 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302285 ⟨567357, by decide⟩ :=
  accepted_of_selected 13 302285 ⟨567357, by decide⟩ ⟨13, 2, 0, 567357, 302285, 2441, 16384⟩
    (by decide) selected_cut_22274

theorem selected_cut_22275 : selected 8 ⟨567378, by decide⟩
    (prefixPartial 13 302286) = some ⟨13, 2, 0, 567378, 302286, 1629, 16384⟩ := by
  decide +kernel

theorem context_13_302286_567378 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302286 ⟨567378, by decide⟩ :=
  accepted_of_selected 13 302286 ⟨567378, by decide⟩ ⟨13, 2, 0, 567378, 302286, 1629, 16384⟩
    (by decide) selected_cut_22275

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
