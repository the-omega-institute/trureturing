/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover231
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_22276 : selected 8 ⟨567383, by decide⟩
    (prefixPartial 13 302287) = some ⟨13, 2, 0, 567383, 302287, 697, 16384⟩ := by
  decide +kernel

theorem context_13_302287_567383 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302287 ⟨567383, by decide⟩ :=
  accepted_of_selected 13 302287 ⟨567383, by decide⟩ ⟨13, 2, 0, 567383, 302287, 697, 16384⟩
    (by decide) selected_cut_22276

theorem unmarked_context_12_75571_567384 : frontier 9 ⟨567384, by decide⟩
    (prefixCache 12 75571) (prefixPartial 12 75571) = false := by
  decide +kernel

theorem node_context_12_75571_567384 : EJMOriginalGlobalDAGData.nodes 9 ⟨567384, by decide⟩ =
    .split (coordinate 12) (![⟨567333, by decide⟩,⟨567357, by decide⟩,⟨567378, by decide⟩,⟨567383, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75571_567384 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75571 ⟨567384, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75571
    ⟨567384, by decide⟩ (by decide) (![⟨567333, by decide⟩,⟨567357, by decide⟩,⟨567378, by decide⟩,⟨567383, by decide⟩]) unmarked_context_12_75571_567384 node_context_12_75571_567384
  intro a
  fin_cases a
  · exact context_13_302284_567333
  · exact context_13_302285_567357
  · exact context_13_302286_567378
  · exact context_13_302287_567383

theorem unmarked_context_11_18892_567385 : frontier 10 ⟨567385, by decide⟩
    (prefixCache 11 18892) (prefixPartial 11 18892) = false := by
  decide +kernel

theorem node_context_11_18892_567385 : EJMOriginalGlobalDAGData.nodes 10 ⟨567385, by decide⟩ =
    .split (coordinate 11) (![⟨445562, by decide⟩,⟨567261, by decide⟩,⟨567328, by decide⟩,⟨567384, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18892_567385 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18892 ⟨567385, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18892
    ⟨567385, by decide⟩ (by decide) (![⟨445562, by decide⟩,⟨567261, by decide⟩,⟨567328, by decide⟩,⟨567384, by decide⟩]) unmarked_context_11_18892_567385 node_context_11_18892_567385
  intro a
  fin_cases a
  · exact context_12_75568_445562
  · exact context_12_75569_567261
  · exact context_12_75570_567328
  · exact context_12_75571_567384

theorem selected_cut_22277 : selected 9 ⟨567386, by decide⟩
    (prefixPartial 12 75572) = some ⟨12, 1, 0, 567386, 75572, 1, 65536⟩ := by
  decide +kernel

theorem context_12_75572_567386 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75572 ⟨567386, by decide⟩ :=
  accepted_of_selected 12 75572 ⟨567386, by decide⟩ ⟨12, 1, 0, 567386, 75572, 1, 65536⟩
    (by decide) selected_cut_22277

theorem selected_cut_22278 : selected 8 ⟨567391, by decide⟩
    (prefixPartial 13 302292) = some ⟨13, 2, 0, 567391, 302292, 321, 16384⟩ := by
  decide +kernel

theorem context_13_302292_567391 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302292 ⟨567391, by decide⟩ :=
  accepted_of_selected 13 302292 ⟨567391, by decide⟩ ⟨13, 2, 0, 567391, 302292, 321, 16384⟩
    (by decide) selected_cut_22278

theorem selected_cut_22279 : selected 8 ⟨567421, by decide⟩
    (prefixPartial 13 302293) = some ⟨13, 2, 0, 567421, 302293, 2229, 16384⟩ := by
  decide +kernel

theorem context_13_302293_567421 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302293 ⟨567421, by decide⟩ :=
  accepted_of_selected 13 302293 ⟨567421, by decide⟩ ⟨13, 2, 0, 567421, 302293, 2229, 16384⟩
    (by decide) selected_cut_22279

theorem selected_cut_22280 : selected 8 ⟨567444, by decide⟩
    (prefixPartial 13 302294) = some ⟨13, 2, 0, 567444, 302294, 1549, 16384⟩ := by
  decide +kernel

theorem context_13_302294_567444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302294 ⟨567444, by decide⟩ :=
  accepted_of_selected 13 302294 ⟨567444, by decide⟩ ⟨13, 2, 0, 567444, 302294, 1549, 16384⟩
    (by decide) selected_cut_22280

theorem selected_cut_22281 : selected 8 ⟨567450, by decide⟩
    (prefixPartial 13 302295) = some ⟨13, 2, 0, 567450, 302295, 765, 16384⟩ := by
  decide +kernel

theorem context_13_302295_567450 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302295 ⟨567450, by decide⟩ :=
  accepted_of_selected 13 302295 ⟨567450, by decide⟩ ⟨13, 2, 0, 567450, 302295, 765, 16384⟩
    (by decide) selected_cut_22281

theorem unmarked_context_12_75573_567451 : frontier 9 ⟨567451, by decide⟩
    (prefixCache 12 75573) (prefixPartial 12 75573) = false := by
  decide +kernel

theorem node_context_12_75573_567451 : EJMOriginalGlobalDAGData.nodes 9 ⟨567451, by decide⟩ =
    .split (coordinate 12) (![⟨567391, by decide⟩,⟨567421, by decide⟩,⟨567444, by decide⟩,⟨567450, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75573_567451 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75573 ⟨567451, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75573
    ⟨567451, by decide⟩ (by decide) (![⟨567391, by decide⟩,⟨567421, by decide⟩,⟨567444, by decide⟩,⟨567450, by decide⟩]) unmarked_context_12_75573_567451 node_context_12_75573_567451
  intro a
  fin_cases a
  · exact context_13_302292_567391
  · exact context_13_302293_567421
  · exact context_13_302294_567444
  · exact context_13_302295_567450

theorem selected_cut_22282 : selected 8 ⟨567456, by decide⟩
    (prefixPartial 13 302296) = some ⟨13, 2, 0, 567456, 302296, 297, 16384⟩ := by
  decide +kernel

theorem context_13_302296_567456 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302296 ⟨567456, by decide⟩ :=
  accepted_of_selected 13 302296 ⟨567456, by decide⟩ ⟨13, 2, 0, 567456, 302296, 297, 16384⟩
    (by decide) selected_cut_22282

theorem selected_cut_22283 : selected 8 ⟨567488, by decide⟩
    (prefixPartial 13 302297) = some ⟨13, 2, 0, 567488, 302297, 2349, 16384⟩ := by
  decide +kernel

theorem context_13_302297_567488 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302297 ⟨567488, by decide⟩ :=
  accepted_of_selected 13 302297 ⟨567488, by decide⟩ ⟨13, 2, 0, 567488, 302297, 2349, 16384⟩
    (by decide) selected_cut_22283

theorem selected_cut_22284 : selected 8 ⟨567507, by decide⟩
    (prefixPartial 13 302298) = some ⟨13, 2, 0, 567507, 302298, 1537, 16384⟩ := by
  decide +kernel

theorem context_13_302298_567507 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302298 ⟨567507, by decide⟩ :=
  accepted_of_selected 13 302298 ⟨567507, by decide⟩ ⟨13, 2, 0, 567507, 302298, 1537, 16384⟩
    (by decide) selected_cut_22284

theorem selected_cut_22285 : selected 8 ⟨567518, by decide⟩
    (prefixPartial 13 302299) = some ⟨13, 2, 0, 567518, 302299, 993, 16384⟩ := by
  decide +kernel

theorem context_13_302299_567518 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302299 ⟨567518, by decide⟩ :=
  accepted_of_selected 13 302299 ⟨567518, by decide⟩ ⟨13, 2, 0, 567518, 302299, 993, 16384⟩
    (by decide) selected_cut_22285

theorem unmarked_context_12_75574_567519 : frontier 9 ⟨567519, by decide⟩
    (prefixCache 12 75574) (prefixPartial 12 75574) = false := by
  decide +kernel

theorem node_context_12_75574_567519 : EJMOriginalGlobalDAGData.nodes 9 ⟨567519, by decide⟩ =
    .split (coordinate 12) (![⟨567456, by decide⟩,⟨567488, by decide⟩,⟨567507, by decide⟩,⟨567518, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75574_567519 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75574 ⟨567519, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75574
    ⟨567519, by decide⟩ (by decide) (![⟨567456, by decide⟩,⟨567488, by decide⟩,⟨567507, by decide⟩,⟨567518, by decide⟩]) unmarked_context_12_75574_567519 node_context_12_75574_567519
  intro a
  fin_cases a
  · exact context_13_302296_567456
  · exact context_13_302297_567488
  · exact context_13_302298_567507
  · exact context_13_302299_567518

theorem selected_cut_22286 : selected 8 ⟨567524, by decide⟩
    (prefixPartial 13 302300) = some ⟨13, 2, 0, 567524, 302300, 245, 16384⟩ := by
  decide +kernel

theorem context_13_302300_567524 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302300 ⟨567524, by decide⟩ :=
  accepted_of_selected 13 302300 ⟨567524, by decide⟩ ⟨13, 2, 0, 567524, 302300, 245, 16384⟩
    (by decide) selected_cut_22286

theorem selected_cut_22287 : selected 8 ⟨567552, by decide⟩
    (prefixPartial 13 302301) = some ⟨13, 2, 0, 567552, 302301, 2309, 16384⟩ := by
  decide +kernel

theorem context_13_302301_567552 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302301 ⟨567552, by decide⟩ :=
  accepted_of_selected 13 302301 ⟨567552, by decide⟩ ⟨13, 2, 0, 567552, 302301, 2309, 16384⟩
    (by decide) selected_cut_22287

theorem selected_cut_22288 : selected 8 ⟨567573, by decide⟩
    (prefixPartial 13 302302) = some ⟨13, 2, 0, 567573, 302302, 1785, 16384⟩ := by
  decide +kernel

theorem context_13_302302_567573 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302302 ⟨567573, by decide⟩ :=
  accepted_of_selected 13 302302 ⟨567573, by decide⟩ ⟨13, 2, 0, 567573, 302302, 1785, 16384⟩
    (by decide) selected_cut_22288

theorem selected_cut_22289 : selected 8 ⟨567580, by decide⟩
    (prefixPartial 13 302303) = some ⟨13, 2, 0, 567580, 302303, 893, 16384⟩ := by
  decide +kernel

theorem context_13_302303_567580 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302303 ⟨567580, by decide⟩ :=
  accepted_of_selected 13 302303 ⟨567580, by decide⟩ ⟨13, 2, 0, 567580, 302303, 893, 16384⟩
    (by decide) selected_cut_22289

theorem unmarked_context_12_75575_567581 : frontier 9 ⟨567581, by decide⟩
    (prefixCache 12 75575) (prefixPartial 12 75575) = false := by
  decide +kernel

theorem node_context_12_75575_567581 : EJMOriginalGlobalDAGData.nodes 9 ⟨567581, by decide⟩ =
    .split (coordinate 12) (![⟨567524, by decide⟩,⟨567552, by decide⟩,⟨567573, by decide⟩,⟨567580, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75575_567581 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75575 ⟨567581, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75575
    ⟨567581, by decide⟩ (by decide) (![⟨567524, by decide⟩,⟨567552, by decide⟩,⟨567573, by decide⟩,⟨567580, by decide⟩]) unmarked_context_12_75575_567581 node_context_12_75575_567581
  intro a
  fin_cases a
  · exact context_13_302300_567524
  · exact context_13_302301_567552
  · exact context_13_302302_567573
  · exact context_13_302303_567580

theorem unmarked_context_11_18893_567582 : frontier 10 ⟨567582, by decide⟩
    (prefixCache 11 18893) (prefixPartial 11 18893) = false := by
  decide +kernel

theorem node_context_11_18893_567582 : EJMOriginalGlobalDAGData.nodes 10 ⟨567582, by decide⟩ =
    .split (coordinate 11) (![⟨567386, by decide⟩,⟨567451, by decide⟩,⟨567519, by decide⟩,⟨567581, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18893_567582 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18893 ⟨567582, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18893
    ⟨567582, by decide⟩ (by decide) (![⟨567386, by decide⟩,⟨567451, by decide⟩,⟨567519, by decide⟩,⟨567581, by decide⟩]) unmarked_context_11_18893_567582 node_context_11_18893_567582
  intro a
  fin_cases a
  · exact context_12_75572_567386
  · exact context_12_75573_567451
  · exact context_12_75574_567519
  · exact context_12_75575_567581

theorem selected_cut_22290 : selected 8 ⟨567586, by decide⟩
    (prefixPartial 13 302304) = some ⟨13, 2, 0, 567586, 302304, 49, 16384⟩ := by
  decide +kernel

theorem context_13_302304_567586 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302304 ⟨567586, by decide⟩ :=
  accepted_of_selected 13 302304 ⟨567586, by decide⟩ ⟨13, 2, 0, 567586, 302304, 49, 16384⟩
    (by decide) selected_cut_22290

theorem selected_cut_22291 : selected 8 ⟨567745, by decide⟩
    (prefixPartial 13 302305) = some ⟨13, 2, 0, 567745, 302305, 3945, 16384⟩ := by
  decide +kernel

theorem context_13_302305_567745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302305 ⟨567745, by decide⟩ :=
  accepted_of_selected 13 302305 ⟨567745, by decide⟩ ⟨13, 2, 0, 567745, 302305, 3945, 16384⟩
    (by decide) selected_cut_22291

theorem selected_cut_22292 : selected 8 ⟨567787, by decide⟩
    (prefixPartial 13 302306) = some ⟨13, 2, 0, 567787, 302306, 657, 16384⟩ := by
  decide +kernel

theorem context_13_302306_567787 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302306 ⟨567787, by decide⟩ :=
  accepted_of_selected 13 302306 ⟨567787, by decide⟩ ⟨13, 2, 0, 567787, 302306, 657, 16384⟩
    (by decide) selected_cut_22292

theorem selected_cut_22293 : selected 8 ⟨501106, by decide⟩
    (prefixPartial 13 302307) = some ⟨13, 1, 0, 501106, 302307, 1, 16384⟩ := by
  decide +kernel

theorem context_13_302307_501106 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302307 ⟨501106, by decide⟩ :=
  accepted_of_selected 13 302307 ⟨501106, by decide⟩ ⟨13, 1, 0, 501106, 302307, 1, 16384⟩
    (by decide) selected_cut_22293

theorem unmarked_context_12_75576_567788 : frontier 9 ⟨567788, by decide⟩
    (prefixCache 12 75576) (prefixPartial 12 75576) = false := by
  decide +kernel

theorem node_context_12_75576_567788 : EJMOriginalGlobalDAGData.nodes 9 ⟨567788, by decide⟩ =
    .split (coordinate 12) (![⟨567586, by decide⟩,⟨567745, by decide⟩,⟨567787, by decide⟩,⟨501106, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75576_567788 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75576 ⟨567788, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75576
    ⟨567788, by decide⟩ (by decide) (![⟨567586, by decide⟩,⟨567745, by decide⟩,⟨567787, by decide⟩,⟨501106, by decide⟩]) unmarked_context_12_75576_567788 node_context_12_75576_567788
  intro a
  fin_cases a
  · exact context_13_302304_567586
  · exact context_13_302305_567745
  · exact context_13_302306_567787
  · exact context_13_302307_501106

theorem selected_cut_22294 : selected 8 ⟨567792, by decide⟩
    (prefixPartial 13 302308) = some ⟨13, 2, 0, 567792, 302308, 217, 16384⟩ := by
  decide +kernel

theorem context_13_302308_567792 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302308 ⟨567792, by decide⟩ :=
  accepted_of_selected 13 302308 ⟨567792, by decide⟩ ⟨13, 2, 0, 567792, 302308, 217, 16384⟩
    (by decide) selected_cut_22294

theorem selected_cut_22295 : selected 8 ⟨567845, by decide⟩
    (prefixPartial 13 302309) = some ⟨13, 2, 0, 567845, 302309, 2741, 16384⟩ := by
  decide +kernel

theorem context_13_302309_567845 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302309 ⟨567845, by decide⟩ :=
  accepted_of_selected 13 302309 ⟨567845, by decide⟩ ⟨13, 2, 0, 567845, 302309, 2741, 16384⟩
    (by decide) selected_cut_22295

theorem selected_cut_22296 : selected 8 ⟨567869, by decide⟩
    (prefixPartial 13 302310) = some ⟨13, 2, 0, 567869, 302310, 1689, 16384⟩ := by
  decide +kernel

theorem context_13_302310_567869 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302310 ⟨567869, by decide⟩ :=
  accepted_of_selected 13 302310 ⟨567869, by decide⟩ ⟨13, 2, 0, 567869, 302310, 1689, 16384⟩
    (by decide) selected_cut_22296

theorem selected_cut_22297 : selected 8 ⟨567882, by decide⟩
    (prefixPartial 13 302311) = some ⟨13, 2, 0, 567882, 302311, 905, 16384⟩ := by
  decide +kernel

theorem context_13_302311_567882 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302311 ⟨567882, by decide⟩ :=
  accepted_of_selected 13 302311 ⟨567882, by decide⟩ ⟨13, 2, 0, 567882, 302311, 905, 16384⟩
    (by decide) selected_cut_22297

theorem unmarked_context_12_75577_567883 : frontier 9 ⟨567883, by decide⟩
    (prefixCache 12 75577) (prefixPartial 12 75577) = false := by
  decide +kernel

theorem node_context_12_75577_567883 : EJMOriginalGlobalDAGData.nodes 9 ⟨567883, by decide⟩ =
    .split (coordinate 12) (![⟨567792, by decide⟩,⟨567845, by decide⟩,⟨567869, by decide⟩,⟨567882, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75577_567883 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75577 ⟨567883, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75577
    ⟨567883, by decide⟩ (by decide) (![⟨567792, by decide⟩,⟨567845, by decide⟩,⟨567869, by decide⟩,⟨567882, by decide⟩]) unmarked_context_12_75577_567883 node_context_12_75577_567883
  intro a
  fin_cases a
  · exact context_13_302308_567792
  · exact context_13_302309_567845
  · exact context_13_302310_567869
  · exact context_13_302311_567882

theorem selected_cut_22298 : selected 8 ⟨567887, by decide⟩
    (prefixPartial 13 302312) = some ⟨13, 2, 0, 567887, 302312, 153, 16384⟩ := by
  decide +kernel

theorem context_13_302312_567887 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302312 ⟨567887, by decide⟩ :=
  accepted_of_selected 13 302312 ⟨567887, by decide⟩ ⟨13, 2, 0, 567887, 302312, 153, 16384⟩
    (by decide) selected_cut_22298

theorem selected_cut_22299 : selected 8 ⟨567936, by decide⟩
    (prefixPartial 13 302313) = some ⟨13, 2, 0, 567936, 302313, 2861, 16384⟩ := by
  decide +kernel

theorem context_13_302313_567936 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302313 ⟨567936, by decide⟩ :=
  accepted_of_selected 13 302313 ⟨567936, by decide⟩ ⟨13, 2, 0, 567936, 302313, 2861, 16384⟩
    (by decide) selected_cut_22299

theorem selected_cut_22300 : selected 8 ⟨567959, by decide⟩
    (prefixPartial 13 302314) = some ⟨13, 2, 0, 567959, 302314, 1621, 16384⟩ := by
  decide +kernel

theorem context_13_302314_567959 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302314 ⟨567959, by decide⟩ :=
  accepted_of_selected 13 302314 ⟨567959, by decide⟩ ⟨13, 2, 0, 567959, 302314, 1621, 16384⟩
    (by decide) selected_cut_22300

theorem selected_cut_22301 : selected 8 ⟨567973, by decide⟩
    (prefixPartial 13 302315) = some ⟨13, 2, 0, 567973, 302315, 997, 16384⟩ := by
  decide +kernel

theorem context_13_302315_567973 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302315 ⟨567973, by decide⟩ :=
  accepted_of_selected 13 302315 ⟨567973, by decide⟩ ⟨13, 2, 0, 567973, 302315, 997, 16384⟩
    (by decide) selected_cut_22301

theorem unmarked_context_12_75578_567974 : frontier 9 ⟨567974, by decide⟩
    (prefixCache 12 75578) (prefixPartial 12 75578) = false := by
  decide +kernel

theorem node_context_12_75578_567974 : EJMOriginalGlobalDAGData.nodes 9 ⟨567974, by decide⟩ =
    .split (coordinate 12) (![⟨567887, by decide⟩,⟨567936, by decide⟩,⟨567959, by decide⟩,⟨567973, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75578_567974 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75578 ⟨567974, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75578
    ⟨567974, by decide⟩ (by decide) (![⟨567887, by decide⟩,⟨567936, by decide⟩,⟨567959, by decide⟩,⟨567973, by decide⟩]) unmarked_context_12_75578_567974 node_context_12_75578_567974
  intro a
  fin_cases a
  · exact context_13_302312_567887
  · exact context_13_302313_567936
  · exact context_13_302314_567959
  · exact context_13_302315_567973

theorem selected_cut_22302 : selected 8 ⟨567978, by decide⟩
    (prefixPartial 13 302316) = some ⟨13, 2, 0, 567978, 302316, 121, 16384⟩ := by
  decide +kernel

theorem context_13_302316_567978 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302316 ⟨567978, by decide⟩ :=
  accepted_of_selected 13 302316 ⟨567978, by decide⟩ ⟨13, 2, 0, 567978, 302316, 121, 16384⟩
    (by decide) selected_cut_22302

theorem selected_cut_22303 : selected 8 ⟨568006, by decide⟩
    (prefixPartial 13 302317) = some ⟨13, 2, 0, 568006, 302317, 2733, 16384⟩ := by
  decide +kernel

theorem context_13_302317_568006 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302317 ⟨568006, by decide⟩ :=
  accepted_of_selected 13 302317 ⟨568006, by decide⟩ ⟨13, 2, 0, 568006, 302317, 2733, 16384⟩
    (by decide) selected_cut_22303

theorem selected_cut_22304 : selected 8 ⟨568025, by decide⟩
    (prefixPartial 13 302318) = some ⟨13, 2, 0, 568025, 302318, 1673, 16384⟩ := by
  decide +kernel

theorem context_13_302318_568025 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302318 ⟨568025, by decide⟩ :=
  accepted_of_selected 13 302318 ⟨568025, by decide⟩ ⟨13, 2, 0, 568025, 302318, 1673, 16384⟩
    (by decide) selected_cut_22304

theorem selected_cut_22305 : selected 8 ⟨568031, by decide⟩
    (prefixPartial 13 302319) = some ⟨13, 2, 0, 568031, 302319, 881, 16384⟩ := by
  decide +kernel

theorem context_13_302319_568031 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302319 ⟨568031, by decide⟩ :=
  accepted_of_selected 13 302319 ⟨568031, by decide⟩ ⟨13, 2, 0, 568031, 302319, 881, 16384⟩
    (by decide) selected_cut_22305

theorem unmarked_context_12_75579_568032 : frontier 9 ⟨568032, by decide⟩
    (prefixCache 12 75579) (prefixPartial 12 75579) = false := by
  decide +kernel

theorem node_context_12_75579_568032 : EJMOriginalGlobalDAGData.nodes 9 ⟨568032, by decide⟩ =
    .split (coordinate 12) (![⟨567978, by decide⟩,⟨568006, by decide⟩,⟨568025, by decide⟩,⟨568031, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75579_568032 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75579 ⟨568032, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75579
    ⟨568032, by decide⟩ (by decide) (![⟨567978, by decide⟩,⟨568006, by decide⟩,⟨568025, by decide⟩,⟨568031, by decide⟩]) unmarked_context_12_75579_568032 node_context_12_75579_568032
  intro a
  fin_cases a
  · exact context_13_302316_567978
  · exact context_13_302317_568006
  · exact context_13_302318_568025
  · exact context_13_302319_568031

theorem unmarked_context_11_18894_568033 : frontier 10 ⟨568033, by decide⟩
    (prefixCache 11 18894) (prefixPartial 11 18894) = false := by
  decide +kernel

theorem node_context_11_18894_568033 : EJMOriginalGlobalDAGData.nodes 10 ⟨568033, by decide⟩ =
    .split (coordinate 11) (![⟨567788, by decide⟩,⟨567883, by decide⟩,⟨567974, by decide⟩,⟨568032, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18894_568033 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18894 ⟨568033, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18894
    ⟨568033, by decide⟩ (by decide) (![⟨567788, by decide⟩,⟨567883, by decide⟩,⟨567974, by decide⟩,⟨568032, by decide⟩]) unmarked_context_11_18894_568033 node_context_11_18894_568033
  intro a
  fin_cases a
  · exact context_12_75576_567788
  · exact context_12_75577_567883
  · exact context_12_75578_567974
  · exact context_12_75579_568032

theorem selected_cut_22306 : selected 9 ⟨445562, by decide⟩
    (prefixPartial 12 75580) = some ⟨12, 1, 0, 445562, 75580, 1, 65536⟩ := by
  decide +kernel

theorem context_12_75580_445562 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75580 ⟨445562, by decide⟩ :=
  accepted_of_selected 12 75580 ⟨445562, by decide⟩ ⟨12, 1, 0, 445562, 75580, 1, 65536⟩
    (by decide) selected_cut_22306

theorem selected_cut_22307 : selected 8 ⟨568036, by decide⟩
    (prefixPartial 13 302324) = some ⟨13, 2, 0, 568036, 302324, 73, 16384⟩ := by
  decide +kernel

theorem context_13_302324_568036 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302324 ⟨568036, by decide⟩ :=
  accepted_of_selected 13 302324 ⟨568036, by decide⟩ ⟨13, 2, 0, 568036, 302324, 73, 16384⟩
    (by decide) selected_cut_22307

theorem selected_cut_22308 : selected 8 ⟨568063, by decide⟩
    (prefixPartial 13 302325) = some ⟨13, 2, 0, 568063, 302325, 2377, 16384⟩ := by
  decide +kernel

theorem context_13_302325_568063 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302325 ⟨568063, by decide⟩ :=
  accepted_of_selected 13 302325 ⟨568063, by decide⟩ ⟨13, 2, 0, 568063, 302325, 2377, 16384⟩
    (by decide) selected_cut_22308

theorem selected_cut_22309 : selected 8 ⟨568082, by decide⟩
    (prefixPartial 13 302326) = some ⟨13, 2, 0, 568082, 302326, 1581, 16384⟩ := by
  decide +kernel

theorem context_13_302326_568082 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302326 ⟨568082, by decide⟩ :=
  accepted_of_selected 13 302326 ⟨568082, by decide⟩ ⟨13, 2, 0, 568082, 302326, 1581, 16384⟩
    (by decide) selected_cut_22309

theorem selected_cut_22310 : selected 8 ⟨568086, by decide⟩
    (prefixPartial 13 302327) = some ⟨13, 2, 0, 568086, 302327, 761, 16384⟩ := by
  decide +kernel

theorem context_13_302327_568086 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302327 ⟨568086, by decide⟩ :=
  accepted_of_selected 13 302327 ⟨568086, by decide⟩ ⟨13, 2, 0, 568086, 302327, 761, 16384⟩
    (by decide) selected_cut_22310

theorem unmarked_context_12_75581_568087 : frontier 9 ⟨568087, by decide⟩
    (prefixCache 12 75581) (prefixPartial 12 75581) = false := by
  decide +kernel

theorem node_context_12_75581_568087 : EJMOriginalGlobalDAGData.nodes 9 ⟨568087, by decide⟩ =
    .split (coordinate 12) (![⟨568036, by decide⟩,⟨568063, by decide⟩,⟨568082, by decide⟩,⟨568086, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75581_568087 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75581 ⟨568087, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75581
    ⟨568087, by decide⟩ (by decide) (![⟨568036, by decide⟩,⟨568063, by decide⟩,⟨568082, by decide⟩,⟨568086, by decide⟩]) unmarked_context_12_75581_568087 node_context_12_75581_568087
  intro a
  fin_cases a
  · exact context_13_302324_568036
  · exact context_13_302325_568063
  · exact context_13_302326_568082
  · exact context_13_302327_568086

theorem selected_cut_22311 : selected 8 ⟨568090, by decide⟩
    (prefixPartial 13 302328) = some ⟨13, 2, 0, 568090, 302328, 41, 16384⟩ := by
  decide +kernel

theorem context_13_302328_568090 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302328 ⟨568090, by decide⟩ :=
  accepted_of_selected 13 302328 ⟨568090, by decide⟩ ⟨13, 2, 0, 568090, 302328, 41, 16384⟩
    (by decide) selected_cut_22311

theorem selected_cut_22312 : selected 8 ⟨568117, by decide⟩
    (prefixPartial 13 302329) = some ⟨13, 2, 0, 568117, 302329, 2485, 16384⟩ := by
  decide +kernel

theorem context_13_302329_568117 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302329 ⟨568117, by decide⟩ :=
  accepted_of_selected 13 302329 ⟨568117, by decide⟩ ⟨13, 2, 0, 568117, 302329, 2485, 16384⟩
    (by decide) selected_cut_22312

theorem selected_cut_22313 : selected 8 ⟨568135, by decide⟩
    (prefixPartial 13 302330) = some ⟨13, 2, 0, 568135, 302330, 1393, 16384⟩ := by
  decide +kernel

theorem context_13_302330_568135 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302330 ⟨568135, by decide⟩ :=
  accepted_of_selected 13 302330 ⟨568135, by decide⟩ ⟨13, 2, 0, 568135, 302330, 1393, 16384⟩
    (by decide) selected_cut_22313

theorem selected_cut_22314 : selected 8 ⟨568140, by decide⟩
    (prefixPartial 13 302331) = some ⟨13, 2, 0, 568140, 302331, 853, 16384⟩ := by
  decide +kernel

theorem context_13_302331_568140 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302331 ⟨568140, by decide⟩ :=
  accepted_of_selected 13 302331 ⟨568140, by decide⟩ ⟨13, 2, 0, 568140, 302331, 853, 16384⟩
    (by decide) selected_cut_22314

theorem unmarked_context_12_75582_568141 : frontier 9 ⟨568141, by decide⟩
    (prefixCache 12 75582) (prefixPartial 12 75582) = false := by
  decide +kernel

theorem node_context_12_75582_568141 : EJMOriginalGlobalDAGData.nodes 9 ⟨568141, by decide⟩ =
    .split (coordinate 12) (![⟨568090, by decide⟩,⟨568117, by decide⟩,⟨568135, by decide⟩,⟨568140, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75582_568141 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75582 ⟨568141, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75582
    ⟨568141, by decide⟩ (by decide) (![⟨568090, by decide⟩,⟨568117, by decide⟩,⟨568135, by decide⟩,⟨568140, by decide⟩]) unmarked_context_12_75582_568141 node_context_12_75582_568141
  intro a
  fin_cases a
  · exact context_13_302328_568090
  · exact context_13_302329_568117
  · exact context_13_302330_568135
  · exact context_13_302331_568140

theorem selected_cut_22315 : selected 9 ⟨512556, by decide⟩
    (prefixPartial 12 75583) = some ⟨12, 1, 0, 512556, 75583, 1, 65536⟩ := by
  decide +kernel

theorem context_12_75583_512556 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75583 ⟨512556, by decide⟩ :=
  accepted_of_selected 12 75583 ⟨512556, by decide⟩ ⟨12, 1, 0, 512556, 75583, 1, 65536⟩
    (by decide) selected_cut_22315

theorem unmarked_context_11_18895_568142 : frontier 10 ⟨568142, by decide⟩
    (prefixCache 11 18895) (prefixPartial 11 18895) = false := by
  decide +kernel

theorem node_context_11_18895_568142 : EJMOriginalGlobalDAGData.nodes 10 ⟨568142, by decide⟩ =
    .split (coordinate 11) (![⟨445562, by decide⟩,⟨568087, by decide⟩,⟨568141, by decide⟩,⟨512556, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18895_568142 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18895 ⟨568142, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18895
    ⟨568142, by decide⟩ (by decide) (![⟨445562, by decide⟩,⟨568087, by decide⟩,⟨568141, by decide⟩,⟨512556, by decide⟩]) unmarked_context_11_18895_568142 node_context_11_18895_568142
  intro a
  fin_cases a
  · exact context_12_75580_445562
  · exact context_12_75581_568087
  · exact context_12_75582_568141
  · exact context_12_75583_512556

theorem unmarked_context_10_4723_568143 : frontier 11 ⟨568143, by decide⟩
    (prefixCache 10 4723) (prefixPartial 10 4723) = false := by
  decide +kernel

theorem node_context_10_4723_568143 : EJMOriginalGlobalDAGData.nodes 11 ⟨568143, by decide⟩ =
    .split (coordinate 10) (![⟨567385, by decide⟩,⟨567582, by decide⟩,⟨568033, by decide⟩,⟨568142, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4723_568143 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4723 ⟨568143, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4723
    ⟨568143, by decide⟩ (by decide) (![⟨567385, by decide⟩,⟨567582, by decide⟩,⟨568033, by decide⟩,⟨568142, by decide⟩]) unmarked_context_10_4723_568143 node_context_10_4723_568143
  intro a
  fin_cases a
  · exact context_11_18892_567385
  · exact context_11_18893_567582
  · exact context_11_18894_568033
  · exact context_11_18895_568142

theorem unmarked_context_9_1180_568144 : frontier 12 ⟨568144, by decide⟩
    (prefixCache 9 1180) (prefixPartial 9 1180) = false := by
  decide +kernel

theorem node_context_9_1180_568144 : EJMOriginalGlobalDAGData.nodes 12 ⟨568144, by decide⟩ =
    .split (coordinate 9) (![⟨564671, by decide⟩,⟨566041, by decide⟩,⟨567181, by decide⟩,⟨568143, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1180_568144 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1180 ⟨568144, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1180
    ⟨568144, by decide⟩ (by decide) (![⟨564671, by decide⟩,⟨566041, by decide⟩,⟨567181, by decide⟩,⟨568143, by decide⟩]) unmarked_context_9_1180_568144 node_context_9_1180_568144
  intro a
  fin_cases a
  · exact context_10_4720_564671
  · exact context_10_4721_566041
  · exact context_10_4722_567181
  · exact context_10_4723_568143

theorem selected_cut_22316 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 302336) = some ⟨13, 1, 0, 3444, 302336, 1, 16384⟩ := by
  decide +kernel

theorem context_13_302336_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302336 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 302336 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 302336, 1, 16384⟩
    (by decide) selected_cut_22316

theorem selected_cut_22317 : selected 8 ⟨568178, by decide⟩
    (prefixPartial 13 302337) = some ⟨13, 2, 0, 568178, 302337, 2377, 16384⟩ := by
  decide +kernel

theorem context_13_302337_568178 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302337 ⟨568178, by decide⟩ :=
  accepted_of_selected 13 302337 ⟨568178, by decide⟩ ⟨13, 2, 0, 568178, 302337, 2377, 16384⟩
    (by decide) selected_cut_22317

theorem selected_cut_22318 : selected 8 ⟨568196, by decide⟩
    (prefixPartial 13 302338) = some ⟨13, 2, 0, 568196, 302338, 1293, 16384⟩ := by
  decide +kernel

theorem context_13_302338_568196 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302338 ⟨568196, by decide⟩ :=
  accepted_of_selected 13 302338 ⟨568196, by decide⟩ ⟨13, 2, 0, 568196, 302338, 1293, 16384⟩
    (by decide) selected_cut_22318

theorem selected_cut_22319 : selected 8 ⟨568203, by decide⟩
    (prefixPartial 13 302339) = some ⟨13, 2, 0, 568203, 302339, 649, 16384⟩ := by
  decide +kernel

theorem context_13_302339_568203 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302339 ⟨568203, by decide⟩ :=
  accepted_of_selected 13 302339 ⟨568203, by decide⟩ ⟨13, 2, 0, 568203, 302339, 649, 16384⟩
    (by decide) selected_cut_22319

theorem unmarked_context_12_75584_568204 : frontier 9 ⟨568204, by decide⟩
    (prefixCache 12 75584) (prefixPartial 12 75584) = false := by
  decide +kernel

theorem node_context_12_75584_568204 : EJMOriginalGlobalDAGData.nodes 9 ⟨568204, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨568178, by decide⟩,⟨568196, by decide⟩,⟨568203, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75584_568204 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75584 ⟨568204, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75584
    ⟨568204, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨568178, by decide⟩,⟨568196, by decide⟩,⟨568203, by decide⟩]) unmarked_context_12_75584_568204 node_context_12_75584_568204
  intro a
  fin_cases a
  · exact context_13_302336_3444
  · exact context_13_302337_568178
  · exact context_13_302338_568196
  · exact context_13_302339_568203

theorem selected_cut_22320 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 302340) = some ⟨13, 1, 0, 3444, 302340, 1, 16384⟩ := by
  decide +kernel

theorem context_13_302340_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302340 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 302340 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 302340, 1, 16384⟩
    (by decide) selected_cut_22320

theorem selected_cut_22321 : selected 8 ⟨568254, by decide⟩
    (prefixPartial 13 302341) = some ⟨13, 2, 0, 568254, 302341, 2973, 16384⟩ := by
  decide +kernel

theorem context_13_302341_568254 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302341 ⟨568254, by decide⟩ :=
  accepted_of_selected 13 302341 ⟨568254, by decide⟩ ⟨13, 2, 0, 568254, 302341, 2973, 16384⟩
    (by decide) selected_cut_22321

theorem selected_cut_22322 : selected 8 ⟨568273, by decide⟩
    (prefixPartial 13 302342) = some ⟨13, 2, 0, 568273, 302342, 1405, 16384⟩ := by
  decide +kernel

theorem context_13_302342_568273 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302342 ⟨568273, by decide⟩ :=
  accepted_of_selected 13 302342 ⟨568273, by decide⟩ ⟨13, 2, 0, 568273, 302342, 1405, 16384⟩
    (by decide) selected_cut_22322

theorem selected_cut_22323 : selected 8 ⟨568277, by decide⟩
    (prefixPartial 13 302343) = some ⟨13, 2, 0, 568277, 302343, 585, 16384⟩ := by
  decide +kernel

theorem context_13_302343_568277 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302343 ⟨568277, by decide⟩ :=
  accepted_of_selected 13 302343 ⟨568277, by decide⟩ ⟨13, 2, 0, 568277, 302343, 585, 16384⟩
    (by decide) selected_cut_22323

theorem unmarked_context_12_75585_568278 : frontier 9 ⟨568278, by decide⟩
    (prefixCache 12 75585) (prefixPartial 12 75585) = false := by
  decide +kernel

theorem node_context_12_75585_568278 : EJMOriginalGlobalDAGData.nodes 9 ⟨568278, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨568254, by decide⟩,⟨568273, by decide⟩,⟨568277, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75585_568278 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75585 ⟨568278, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75585
    ⟨568278, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨568254, by decide⟩,⟨568273, by decide⟩,⟨568277, by decide⟩]) unmarked_context_12_75585_568278 node_context_12_75585_568278
  intro a
  fin_cases a
  · exact context_13_302340_3444
  · exact context_13_302341_568254
  · exact context_13_302342_568273
  · exact context_13_302343_568277

theorem selected_cut_22324 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 302344) = some ⟨13, 1, 0, 3444, 302344, 1, 16384⟩ := by
  decide +kernel

theorem context_13_302344_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302344 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 302344 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 302344, 1, 16384⟩
    (by decide) selected_cut_22324

theorem selected_cut_22325 : selected 8 ⟨568337, by decide⟩
    (prefixPartial 13 302345) = some ⟨13, 2, 0, 568337, 302345, 3529, 16384⟩ := by
  decide +kernel

theorem context_13_302345_568337 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302345 ⟨568337, by decide⟩ :=
  accepted_of_selected 13 302345 ⟨568337, by decide⟩ ⟨13, 2, 0, 568337, 302345, 3529, 16384⟩
    (by decide) selected_cut_22325

theorem selected_cut_22326 : selected 8 ⟨568357, by decide⟩
    (prefixPartial 13 302346) = some ⟨13, 2, 0, 568357, 302346, 1701, 16384⟩ := by
  decide +kernel

theorem context_13_302346_568357 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302346 ⟨568357, by decide⟩ :=
  accepted_of_selected 13 302346 ⟨568357, by decide⟩ ⟨13, 2, 0, 568357, 302346, 1701, 16384⟩
    (by decide) selected_cut_22326

theorem selected_cut_22327 : selected 8 ⟨568363, by decide⟩
    (prefixPartial 13 302347) = some ⟨13, 2, 0, 568363, 302347, 705, 16384⟩ := by
  decide +kernel

theorem context_13_302347_568363 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302347 ⟨568363, by decide⟩ :=
  accepted_of_selected 13 302347 ⟨568363, by decide⟩ ⟨13, 2, 0, 568363, 302347, 705, 16384⟩
    (by decide) selected_cut_22327

theorem unmarked_context_12_75586_568364 : frontier 9 ⟨568364, by decide⟩
    (prefixCache 12 75586) (prefixPartial 12 75586) = false := by
  decide +kernel

theorem node_context_12_75586_568364 : EJMOriginalGlobalDAGData.nodes 9 ⟨568364, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨568337, by decide⟩,⟨568357, by decide⟩,⟨568363, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75586_568364 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75586 ⟨568364, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75586
    ⟨568364, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨568337, by decide⟩,⟨568357, by decide⟩,⟨568363, by decide⟩]) unmarked_context_12_75586_568364 node_context_12_75586_568364
  intro a
  fin_cases a
  · exact context_13_302344_3444
  · exact context_13_302345_568337
  · exact context_13_302346_568357
  · exact context_13_302347_568363

theorem selected_cut_22328 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 302348) = some ⟨13, 1, 0, 3444, 302348, 1, 16384⟩ := by
  decide +kernel

theorem context_13_302348_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302348 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 302348 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 302348, 1, 16384⟩
    (by decide) selected_cut_22328

theorem selected_cut_22329 : selected 8 ⟨568405, by decide⟩
    (prefixPartial 13 302349) = some ⟨13, 2, 0, 568405, 302349, 3081, 16384⟩ := by
  decide +kernel

theorem context_13_302349_568405 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302349 ⟨568405, by decide⟩ :=
  accepted_of_selected 13 302349 ⟨568405, by decide⟩ ⟨13, 2, 0, 568405, 302349, 3081, 16384⟩
    (by decide) selected_cut_22329

theorem selected_cut_22330 : selected 8 ⟨568432, by decide⟩
    (prefixPartial 13 302350) = some ⟨13, 2, 0, 568432, 302350, 1689, 16384⟩ := by
  decide +kernel

theorem context_13_302350_568432 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302350 ⟨568432, by decide⟩ :=
  accepted_of_selected 13 302350 ⟨568432, by decide⟩ ⟨13, 2, 0, 568432, 302350, 1689, 16384⟩
    (by decide) selected_cut_22330

theorem selected_cut_22331 : selected 8 ⟨568438, by decide⟩
    (prefixPartial 13 302351) = some ⟨13, 2, 0, 568438, 302351, 569, 16384⟩ := by
  decide +kernel

theorem context_13_302351_568438 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302351 ⟨568438, by decide⟩ :=
  accepted_of_selected 13 302351 ⟨568438, by decide⟩ ⟨13, 2, 0, 568438, 302351, 569, 16384⟩
    (by decide) selected_cut_22331

theorem unmarked_context_12_75587_568439 : frontier 9 ⟨568439, by decide⟩
    (prefixCache 12 75587) (prefixPartial 12 75587) = false := by
  decide +kernel

theorem node_context_12_75587_568439 : EJMOriginalGlobalDAGData.nodes 9 ⟨568439, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨568405, by decide⟩,⟨568432, by decide⟩,⟨568438, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75587_568439 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75587 ⟨568439, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75587
    ⟨568439, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨568405, by decide⟩,⟨568432, by decide⟩,⟨568438, by decide⟩]) unmarked_context_12_75587_568439 node_context_12_75587_568439
  intro a
  fin_cases a
  · exact context_13_302348_3444
  · exact context_13_302349_568405
  · exact context_13_302350_568432
  · exact context_13_302351_568438

theorem unmarked_context_11_18896_568440 : frontier 10 ⟨568440, by decide⟩
    (prefixCache 11 18896) (prefixPartial 11 18896) = false := by
  decide +kernel

theorem node_context_11_18896_568440 : EJMOriginalGlobalDAGData.nodes 10 ⟨568440, by decide⟩ =
    .split (coordinate 11) (![⟨568204, by decide⟩,⟨568278, by decide⟩,⟨568364, by decide⟩,⟨568439, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18896_568440 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18896 ⟨568440, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18896
    ⟨568440, by decide⟩ (by decide) (![⟨568204, by decide⟩,⟨568278, by decide⟩,⟨568364, by decide⟩,⟨568439, by decide⟩]) unmarked_context_11_18896_568440 node_context_11_18896_568440
  intro a
  fin_cases a
  · exact context_12_75584_568204
  · exact context_12_75585_568278
  · exact context_12_75586_568364
  · exact context_12_75587_568439

theorem selected_cut_22332 : selected 9 ⟨568487, by decide⟩
    (prefixPartial 12 75588) = some ⟨12, 2, 0, 568487, 75588, 3965, 65536⟩ := by
  decide +kernel

theorem context_12_75588_568487 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75588 ⟨568487, by decide⟩ :=
  accepted_of_selected 12 75588 ⟨568487, by decide⟩ ⟨12, 2, 0, 568487, 75588, 3965, 65536⟩
    (by decide) selected_cut_22332

theorem selected_cut_22333 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 302356) = some ⟨13, 1, 0, 3444, 302356, 1, 16384⟩ := by
  decide +kernel

theorem context_13_302356_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302356 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 302356 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 302356, 1, 16384⟩
    (by decide) selected_cut_22333

theorem selected_cut_22334 : selected 8 ⟨568517, by decide⟩
    (prefixPartial 13 302357) = some ⟨13, 2, 0, 568517, 302357, 2109, 16384⟩ := by
  decide +kernel

theorem context_13_302357_568517 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302357 ⟨568517, by decide⟩ :=
  accepted_of_selected 13 302357 ⟨568517, by decide⟩ ⟨13, 2, 0, 568517, 302357, 2109, 16384⟩
    (by decide) selected_cut_22334

theorem selected_cut_22335 : selected 8 ⟨568541, by decide⟩
    (prefixPartial 13 302358) = some ⟨13, 2, 0, 568541, 302358, 1401, 16384⟩ := by
  decide +kernel

theorem context_13_302358_568541 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302358 ⟨568541, by decide⟩ :=
  accepted_of_selected 13 302358 ⟨568541, by decide⟩ ⟨13, 2, 0, 568541, 302358, 1401, 16384⟩
    (by decide) selected_cut_22335

theorem selected_cut_22336 : selected 8 ⟨568547, by decide⟩
    (prefixPartial 13 302359) = some ⟨13, 2, 0, 568547, 302359, 653, 16384⟩ := by
  decide +kernel

theorem context_13_302359_568547 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302359 ⟨568547, by decide⟩ :=
  accepted_of_selected 13 302359 ⟨568547, by decide⟩ ⟨13, 2, 0, 568547, 302359, 653, 16384⟩
    (by decide) selected_cut_22336

theorem unmarked_context_12_75589_568548 : frontier 9 ⟨568548, by decide⟩
    (prefixCache 12 75589) (prefixPartial 12 75589) = false := by
  decide +kernel

theorem node_context_12_75589_568548 : EJMOriginalGlobalDAGData.nodes 9 ⟨568548, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨568517, by decide⟩,⟨568541, by decide⟩,⟨568547, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75589_568548 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75589 ⟨568548, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75589
    ⟨568548, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨568517, by decide⟩,⟨568541, by decide⟩,⟨568547, by decide⟩]) unmarked_context_12_75589_568548 node_context_12_75589_568548
  intro a
  fin_cases a
  · exact context_13_302356_3444
  · exact context_13_302357_568517
  · exact context_13_302358_568541
  · exact context_13_302359_568547

theorem selected_cut_22337 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 302360) = some ⟨13, 1, 0, 3444, 302360, 1, 16384⟩ := by
  decide +kernel

theorem context_13_302360_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302360 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 302360 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 302360, 1, 16384⟩
    (by decide) selected_cut_22337

theorem selected_cut_22338 : selected 8 ⟨568586, by decide⟩
    (prefixPartial 13 302361) = some ⟨13, 2, 0, 568586, 302361, 2725, 16384⟩ := by
  decide +kernel

theorem context_13_302361_568586 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302361 ⟨568586, by decide⟩ :=
  accepted_of_selected 13 302361 ⟨568586, by decide⟩ ⟨13, 2, 0, 568586, 302361, 2725, 16384⟩
    (by decide) selected_cut_22338

theorem selected_cut_22339 : selected 8 ⟨568607, by decide⟩
    (prefixPartial 13 302362) = some ⟨13, 2, 0, 568607, 302362, 1665, 16384⟩ := by
  decide +kernel

theorem context_13_302362_568607 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302362 ⟨568607, by decide⟩ :=
  accepted_of_selected 13 302362 ⟨568607, by decide⟩ ⟨13, 2, 0, 568607, 302362, 1665, 16384⟩
    (by decide) selected_cut_22339

theorem selected_cut_22340 : selected 8 ⟨568615, by decide⟩
    (prefixPartial 13 302363) = some ⟨13, 2, 0, 568615, 302363, 877, 16384⟩ := by
  decide +kernel

theorem context_13_302363_568615 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302363 ⟨568615, by decide⟩ :=
  accepted_of_selected 13 302363 ⟨568615, by decide⟩ ⟨13, 2, 0, 568615, 302363, 877, 16384⟩
    (by decide) selected_cut_22340

theorem unmarked_context_12_75590_568616 : frontier 9 ⟨568616, by decide⟩
    (prefixCache 12 75590) (prefixPartial 12 75590) = false := by
  decide +kernel

theorem node_context_12_75590_568616 : EJMOriginalGlobalDAGData.nodes 9 ⟨568616, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨568586, by decide⟩,⟨568607, by decide⟩,⟨568615, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75590_568616 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75590 ⟨568616, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75590
    ⟨568616, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨568586, by decide⟩,⟨568607, by decide⟩,⟨568615, by decide⟩]) unmarked_context_12_75590_568616 node_context_12_75590_568616
  intro a
  fin_cases a
  · exact context_13_302360_3444
  · exact context_13_302361_568586
  · exact context_13_302362_568607
  · exact context_13_302363_568615

theorem selected_cut_22341 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 302364) = some ⟨13, 1, 0, 3444, 302364, 1, 16384⟩ := by
  decide +kernel

theorem context_13_302364_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302364 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 302364 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 302364, 1, 16384⟩
    (by decide) selected_cut_22341

theorem selected_cut_22342 : selected 8 ⟨568649, by decide⟩
    (prefixPartial 13 302365) = some ⟨13, 2, 0, 568649, 302365, 2409, 16384⟩ := by
  decide +kernel

theorem context_13_302365_568649 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302365 ⟨568649, by decide⟩ :=
  accepted_of_selected 13 302365 ⟨568649, by decide⟩ ⟨13, 2, 0, 568649, 302365, 2409, 16384⟩
    (by decide) selected_cut_22342

theorem selected_cut_22343 : selected 8 ⟨568676, by decide⟩
    (prefixPartial 13 302366) = some ⟨13, 2, 0, 568676, 302366, 1793, 16384⟩ := by
  decide +kernel

theorem context_13_302366_568676 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302366 ⟨568676, by decide⟩ :=
  accepted_of_selected 13 302366 ⟨568676, by decide⟩ ⟨13, 2, 0, 568676, 302366, 1793, 16384⟩
    (by decide) selected_cut_22343

theorem selected_cut_22344 : selected 8 ⟨568682, by decide⟩
    (prefixPartial 13 302367) = some ⟨13, 2, 0, 568682, 302367, 693, 16384⟩ := by
  decide +kernel

theorem context_13_302367_568682 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302367 ⟨568682, by decide⟩ :=
  accepted_of_selected 13 302367 ⟨568682, by decide⟩ ⟨13, 2, 0, 568682, 302367, 693, 16384⟩
    (by decide) selected_cut_22344

theorem unmarked_context_12_75591_568683 : frontier 9 ⟨568683, by decide⟩
    (prefixCache 12 75591) (prefixPartial 12 75591) = false := by
  decide +kernel

theorem node_context_12_75591_568683 : EJMOriginalGlobalDAGData.nodes 9 ⟨568683, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨568649, by decide⟩,⟨568676, by decide⟩,⟨568682, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75591_568683 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75591 ⟨568683, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75591
    ⟨568683, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨568649, by decide⟩,⟨568676, by decide⟩,⟨568682, by decide⟩]) unmarked_context_12_75591_568683 node_context_12_75591_568683
  intro a
  fin_cases a
  · exact context_13_302364_3444
  · exact context_13_302365_568649
  · exact context_13_302366_568676
  · exact context_13_302367_568682

theorem unmarked_context_11_18897_568684 : frontier 10 ⟨568684, by decide⟩
    (prefixCache 11 18897) (prefixPartial 11 18897) = false := by
  decide +kernel

theorem node_context_11_18897_568684 : EJMOriginalGlobalDAGData.nodes 10 ⟨568684, by decide⟩ =
    .split (coordinate 11) (![⟨568487, by decide⟩,⟨568548, by decide⟩,⟨568616, by decide⟩,⟨568683, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18897_568684 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18897 ⟨568684, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18897
    ⟨568684, by decide⟩ (by decide) (![⟨568487, by decide⟩,⟨568548, by decide⟩,⟨568616, by decide⟩,⟨568683, by decide⟩]) unmarked_context_11_18897_568684 node_context_11_18897_568684
  intro a
  fin_cases a
  · exact context_12_75588_568487
  · exact context_12_75589_568548
  · exact context_12_75590_568616
  · exact context_12_75591_568683

theorem selected_cut_22345 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 302368) = some ⟨13, 1, 0, 3444, 302368, 1, 16384⟩ := by
  decide +kernel

theorem context_13_302368_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302368 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 302368 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 302368, 1, 16384⟩
    (by decide) selected_cut_22345

theorem selected_cut_22346 : selected 8 ⟨568710, by decide⟩
    (prefixPartial 13 302369) = some ⟨13, 2, 0, 568710, 302369, 2105, 16384⟩ := by
  decide +kernel

theorem context_13_302369_568710 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302369 ⟨568710, by decide⟩ :=
  accepted_of_selected 13 302369 ⟨568710, by decide⟩ ⟨13, 2, 0, 568710, 302369, 2105, 16384⟩
    (by decide) selected_cut_22346

theorem selected_cut_22347 : selected 8 ⟨568725, by decide⟩
    (prefixPartial 13 302370) = some ⟨13, 2, 0, 568725, 302370, 1565, 16384⟩ := by
  decide +kernel

theorem context_13_302370_568725 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302370 ⟨568725, by decide⟩ :=
  accepted_of_selected 13 302370 ⟨568725, by decide⟩ ⟨13, 2, 0, 568725, 302370, 1565, 16384⟩
    (by decide) selected_cut_22347

theorem selected_cut_22348 : selected 8 ⟨568731, by decide⟩
    (prefixPartial 13 302371) = some ⟨13, 2, 0, 568731, 302371, 865, 16384⟩ := by
  decide +kernel

theorem context_13_302371_568731 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302371 ⟨568731, by decide⟩ :=
  accepted_of_selected 13 302371 ⟨568731, by decide⟩ ⟨13, 2, 0, 568731, 302371, 865, 16384⟩
    (by decide) selected_cut_22348

theorem unmarked_context_12_75592_568732 : frontier 9 ⟨568732, by decide⟩
    (prefixCache 12 75592) (prefixPartial 12 75592) = false := by
  decide +kernel

theorem node_context_12_75592_568732 : EJMOriginalGlobalDAGData.nodes 9 ⟨568732, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨568710, by decide⟩,⟨568725, by decide⟩,⟨568731, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75592_568732 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75592 ⟨568732, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75592
    ⟨568732, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨568710, by decide⟩,⟨568725, by decide⟩,⟨568731, by decide⟩]) unmarked_context_12_75592_568732 node_context_12_75592_568732
  intro a
  fin_cases a
  · exact context_13_302368_3444
  · exact context_13_302369_568710
  · exact context_13_302370_568725
  · exact context_13_302371_568731

theorem selected_cut_22349 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 302372) = some ⟨13, 1, 0, 3444, 302372, 1, 16384⟩ := by
  decide +kernel

theorem context_13_302372_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302372 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 302372 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 302372, 1, 16384⟩
    (by decide) selected_cut_22349

theorem selected_cut_22350 : selected 8 ⟨568772, by decide⟩
    (prefixPartial 13 302373) = some ⟨13, 2, 0, 568772, 302373, 2341, 16384⟩ := by
  decide +kernel

theorem context_13_302373_568772 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302373 ⟨568772, by decide⟩ :=
  accepted_of_selected 13 302373 ⟨568772, by decide⟩ ⟨13, 2, 0, 568772, 302373, 2341, 16384⟩
    (by decide) selected_cut_22350

theorem selected_cut_22351 : selected 8 ⟨568793, by decide⟩
    (prefixPartial 13 302374) = some ⟨13, 2, 0, 568793, 302374, 1589, 16384⟩ := by
  decide +kernel

theorem context_13_302374_568793 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302374 ⟨568793, by decide⟩ :=
  accepted_of_selected 13 302374 ⟨568793, by decide⟩ ⟨13, 2, 0, 568793, 302374, 1589, 16384⟩
    (by decide) selected_cut_22351

theorem selected_cut_22352 : selected 8 ⟨568801, by decide⟩
    (prefixPartial 13 302375) = some ⟨13, 2, 0, 568801, 302375, 821, 16384⟩ := by
  decide +kernel

theorem context_13_302375_568801 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302375 ⟨568801, by decide⟩ :=
  accepted_of_selected 13 302375 ⟨568801, by decide⟩ ⟨13, 2, 0, 568801, 302375, 821, 16384⟩
    (by decide) selected_cut_22352

theorem unmarked_context_12_75593_568802 : frontier 9 ⟨568802, by decide⟩
    (prefixCache 12 75593) (prefixPartial 12 75593) = false := by
  decide +kernel

theorem node_context_12_75593_568802 : EJMOriginalGlobalDAGData.nodes 9 ⟨568802, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨568772, by decide⟩,⟨568793, by decide⟩,⟨568801, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75593_568802 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75593 ⟨568802, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75593
    ⟨568802, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨568772, by decide⟩,⟨568793, by decide⟩,⟨568801, by decide⟩]) unmarked_context_12_75593_568802 node_context_12_75593_568802
  intro a
  fin_cases a
  · exact context_13_302372_3444
  · exact context_13_302373_568772
  · exact context_13_302374_568793
  · exact context_13_302375_568801

theorem selected_cut_22353 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 302376) = some ⟨13, 1, 0, 3444, 302376, 1, 16384⟩ := by
  decide +kernel

theorem context_13_302376_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302376 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 302376 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 302376, 1, 16384⟩
    (by decide) selected_cut_22353

theorem selected_cut_22354 : selected 8 ⟨568849, by decide⟩
    (prefixPartial 13 302377) = some ⟨13, 2, 0, 568849, 302377, 2809, 16384⟩ := by
  decide +kernel

theorem context_13_302377_568849 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302377 ⟨568849, by decide⟩ :=
  accepted_of_selected 13 302377 ⟨568849, by decide⟩ ⟨13, 2, 0, 568849, 302377, 2809, 16384⟩
    (by decide) selected_cut_22354

theorem selected_cut_22355 : selected 8 ⟨568871, by decide⟩
    (prefixPartial 13 302378) = some ⟨13, 2, 0, 568871, 302378, 1849, 16384⟩ := by
  decide +kernel

theorem context_13_302378_568871 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302378 ⟨568871, by decide⟩ :=
  accepted_of_selected 13 302378 ⟨568871, by decide⟩ ⟨13, 2, 0, 568871, 302378, 1849, 16384⟩
    (by decide) selected_cut_22355

theorem selected_cut_22356 : selected 8 ⟨568885, by decide⟩
    (prefixPartial 13 302379) = some ⟨13, 2, 0, 568885, 302379, 921, 16384⟩ := by
  decide +kernel

theorem context_13_302379_568885 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302379 ⟨568885, by decide⟩ :=
  accepted_of_selected 13 302379 ⟨568885, by decide⟩ ⟨13, 2, 0, 568885, 302379, 921, 16384⟩
    (by decide) selected_cut_22356

theorem unmarked_context_12_75594_568886 : frontier 9 ⟨568886, by decide⟩
    (prefixCache 12 75594) (prefixPartial 12 75594) = false := by
  decide +kernel

theorem node_context_12_75594_568886 : EJMOriginalGlobalDAGData.nodes 9 ⟨568886, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨568849, by decide⟩,⟨568871, by decide⟩,⟨568885, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75594_568886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75594 ⟨568886, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75594
    ⟨568886, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨568849, by decide⟩,⟨568871, by decide⟩,⟨568885, by decide⟩]) unmarked_context_12_75594_568886 node_context_12_75594_568886
  intro a
  fin_cases a
  · exact context_13_302376_3444
  · exact context_13_302377_568849
  · exact context_13_302378_568871
  · exact context_13_302379_568885

theorem selected_cut_22357 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 302380) = some ⟨13, 1, 0, 3444, 302380, 1, 16384⟩ := by
  decide +kernel

theorem context_13_302380_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302380 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 302380 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 302380, 1, 16384⟩
    (by decide) selected_cut_22357

theorem selected_cut_22358 : selected 8 ⟨568928, by decide⟩
    (prefixPartial 13 302381) = some ⟨13, 2, 0, 568928, 302381, 2605, 16384⟩ := by
  decide +kernel

theorem context_13_302381_568928 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302381 ⟨568928, by decide⟩ :=
  accepted_of_selected 13 302381 ⟨568928, by decide⟩ ⟨13, 2, 0, 568928, 302381, 2605, 16384⟩
    (by decide) selected_cut_22358

theorem selected_cut_22359 : selected 8 ⟨568955, by decide⟩
    (prefixPartial 13 302382) = some ⟨13, 2, 0, 568955, 302382, 1841, 16384⟩ := by
  decide +kernel

theorem context_13_302382_568955 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302382 ⟨568955, by decide⟩ :=
  accepted_of_selected 13 302382 ⟨568955, by decide⟩ ⟨13, 2, 0, 568955, 302382, 1841, 16384⟩
    (by decide) selected_cut_22359

theorem selected_cut_22360 : selected 8 ⟨568967, by decide⟩
    (prefixPartial 13 302383) = some ⟨13, 2, 0, 568967, 302383, 813, 16384⟩ := by
  decide +kernel

theorem context_13_302383_568967 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302383 ⟨568967, by decide⟩ :=
  accepted_of_selected 13 302383 ⟨568967, by decide⟩ ⟨13, 2, 0, 568967, 302383, 813, 16384⟩
    (by decide) selected_cut_22360

theorem unmarked_context_12_75595_568968 : frontier 9 ⟨568968, by decide⟩
    (prefixCache 12 75595) (prefixPartial 12 75595) = false := by
  decide +kernel

theorem node_context_12_75595_568968 : EJMOriginalGlobalDAGData.nodes 9 ⟨568968, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨568928, by decide⟩,⟨568955, by decide⟩,⟨568967, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75595_568968 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75595 ⟨568968, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75595
    ⟨568968, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨568928, by decide⟩,⟨568955, by decide⟩,⟨568967, by decide⟩]) unmarked_context_12_75595_568968 node_context_12_75595_568968
  intro a
  fin_cases a
  · exact context_13_302380_3444
  · exact context_13_302381_568928
  · exact context_13_302382_568955
  · exact context_13_302383_568967

theorem unmarked_context_11_18898_568969 : frontier 10 ⟨568969, by decide⟩
    (prefixCache 11 18898) (prefixPartial 11 18898) = false := by
  decide +kernel

theorem node_context_11_18898_568969 : EJMOriginalGlobalDAGData.nodes 10 ⟨568969, by decide⟩ =
    .split (coordinate 11) (![⟨568732, by decide⟩,⟨568802, by decide⟩,⟨568886, by decide⟩,⟨568968, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18898_568969 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18898 ⟨568969, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18898
    ⟨568969, by decide⟩ (by decide) (![⟨568732, by decide⟩,⟨568802, by decide⟩,⟨568886, by decide⟩,⟨568968, by decide⟩]) unmarked_context_11_18898_568969 node_context_11_18898_568969
  intro a
  fin_cases a
  · exact context_12_75592_568732
  · exact context_12_75593_568802
  · exact context_12_75594_568886
  · exact context_12_75595_568968

theorem selected_cut_22361 : selected 9 ⟨569014, by decide⟩
    (prefixPartial 12 75596) = some ⟨12, 2, 0, 569014, 75596, 3941, 65536⟩ := by
  decide +kernel

theorem context_12_75596_569014 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75596 ⟨569014, by decide⟩ :=
  accepted_of_selected 12 75596 ⟨569014, by decide⟩ ⟨12, 2, 0, 569014, 75596, 3941, 65536⟩
    (by decide) selected_cut_22361

theorem selected_cut_22362 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 302388) = some ⟨13, 1, 0, 3444, 302388, 1, 16384⟩ := by
  decide +kernel

theorem context_13_302388_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302388 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 302388 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 302388, 1, 16384⟩
    (by decide) selected_cut_22362

theorem selected_cut_22363 : selected 8 ⟨569053, by decide⟩
    (prefixPartial 13 302389) = some ⟨13, 2, 0, 569053, 302389, 2141, 16384⟩ := by
  decide +kernel

theorem context_13_302389_569053 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302389 ⟨569053, by decide⟩ :=
  accepted_of_selected 13 302389 ⟨569053, by decide⟩ ⟨13, 2, 0, 569053, 302389, 2141, 16384⟩
    (by decide) selected_cut_22363

theorem selected_cut_22364 : selected 8 ⟨569074, by decide⟩
    (prefixPartial 13 302390) = some ⟨13, 2, 0, 569074, 302390, 1517, 16384⟩ := by
  decide +kernel

theorem context_13_302390_569074 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302390 ⟨569074, by decide⟩ :=
  accepted_of_selected 13 302390 ⟨569074, by decide⟩ ⟨13, 2, 0, 569074, 302390, 1517, 16384⟩
    (by decide) selected_cut_22364

theorem selected_cut_22365 : selected 8 ⟨569079, by decide⟩
    (prefixPartial 13 302391) = some ⟨13, 2, 0, 569079, 302391, 725, 16384⟩ := by
  decide +kernel

theorem context_13_302391_569079 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302391 ⟨569079, by decide⟩ :=
  accepted_of_selected 13 302391 ⟨569079, by decide⟩ ⟨13, 2, 0, 569079, 302391, 725, 16384⟩
    (by decide) selected_cut_22365

theorem unmarked_context_12_75597_569080 : frontier 9 ⟨569080, by decide⟩
    (prefixCache 12 75597) (prefixPartial 12 75597) = false := by
  decide +kernel

theorem node_context_12_75597_569080 : EJMOriginalGlobalDAGData.nodes 9 ⟨569080, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨569053, by decide⟩,⟨569074, by decide⟩,⟨569079, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75597_569080 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75597 ⟨569080, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75597
    ⟨569080, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨569053, by decide⟩,⟨569074, by decide⟩,⟨569079, by decide⟩]) unmarked_context_12_75597_569080 node_context_12_75597_569080
  intro a
  fin_cases a
  · exact context_13_302388_3444
  · exact context_13_302389_569053
  · exact context_13_302390_569074
  · exact context_13_302391_569079

theorem selected_cut_22366 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 302392) = some ⟨13, 1, 0, 3444, 302392, 1, 16384⟩ := by
  decide +kernel

theorem context_13_302392_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302392 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 302392 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 302392, 1, 16384⟩
    (by decide) selected_cut_22366

theorem selected_cut_22367 : selected 8 ⟨569120, by decide⟩
    (prefixPartial 13 302393) = some ⟨13, 2, 0, 569120, 302393, 2573, 16384⟩ := by
  decide +kernel

theorem context_13_302393_569120 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302393 ⟨569120, by decide⟩ :=
  accepted_of_selected 13 302393 ⟨569120, by decide⟩ ⟨13, 2, 0, 569120, 302393, 2573, 16384⟩
    (by decide) selected_cut_22367

theorem selected_cut_22368 : selected 8 ⟨569139, by decide⟩
    (prefixPartial 13 302394) = some ⟨13, 2, 0, 569139, 302394, 1525, 16384⟩ := by
  decide +kernel

theorem context_13_302394_569139 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302394 ⟨569139, by decide⟩ :=
  accepted_of_selected 13 302394 ⟨569139, by decide⟩ ⟨13, 2, 0, 569139, 302394, 1525, 16384⟩
    (by decide) selected_cut_22368

theorem selected_cut_22369 : selected 8 ⟨569147, by decide⟩
    (prefixPartial 13 302395) = some ⟨13, 2, 0, 569147, 302395, 841, 16384⟩ := by
  decide +kernel

theorem context_13_302395_569147 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302395 ⟨569147, by decide⟩ :=
  accepted_of_selected 13 302395 ⟨569147, by decide⟩ ⟨13, 2, 0, 569147, 302395, 841, 16384⟩
    (by decide) selected_cut_22369

theorem unmarked_context_12_75598_569148 : frontier 9 ⟨569148, by decide⟩
    (prefixCache 12 75598) (prefixPartial 12 75598) = false := by
  decide +kernel

theorem node_context_12_75598_569148 : EJMOriginalGlobalDAGData.nodes 9 ⟨569148, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨569120, by decide⟩,⟨569139, by decide⟩,⟨569147, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75598_569148 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75598 ⟨569148, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75598
    ⟨569148, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨569120, by decide⟩,⟨569139, by decide⟩,⟨569147, by decide⟩]) unmarked_context_12_75598_569148 node_context_12_75598_569148
  intro a
  fin_cases a
  · exact context_13_302392_3444
  · exact context_13_302393_569120
  · exact context_13_302394_569139
  · exact context_13_302395_569147

theorem selected_cut_22370 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 302396) = some ⟨13, 1, 0, 3444, 302396, 1, 16384⟩ := by
  decide +kernel

theorem context_13_302396_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302396 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 302396 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 302396, 1, 16384⟩
    (by decide) selected_cut_22370

theorem selected_cut_22371 : selected 8 ⟨569214, by decide⟩
    (prefixPartial 13 302397) = some ⟨13, 2, 0, 569214, 302397, 3541, 16384⟩ := by
  decide +kernel

theorem context_13_302397_569214 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302397 ⟨569214, by decide⟩ :=
  accepted_of_selected 13 302397 ⟨569214, by decide⟩ ⟨13, 2, 0, 569214, 302397, 3541, 16384⟩
    (by decide) selected_cut_22371

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
