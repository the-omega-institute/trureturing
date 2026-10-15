/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover137
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem unmarked_context_12_26642_349574 : frontier 9 ⟨349574, by decide⟩
    (prefixCache 12 26642) (prefixPartial 12 26642) = false := by
  decide +kernel

theorem node_context_12_26642_349574 : EJMOriginalGlobalDAGData.nodes 9 ⟨349574, by decide⟩ =
    .split (coordinate 12) (![⟨349520, by decide⟩,⟨349547, by decide⟩,⟨349565, by decide⟩,⟨349573, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26642_349574 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26642 ⟨349574, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26642
    ⟨349574, by decide⟩ (by decide) (![⟨349520, by decide⟩,⟨349547, by decide⟩,⟨349565, by decide⟩,⟨349573, by decide⟩]) unmarked_context_12_26642_349574 node_context_12_26642_349574
  intro a
  fin_cases a
  · exact context_13_106568_349520
  · exact context_13_106569_349547
  · exact context_13_106570_349565
  · exact context_13_106571_349573

theorem selected_cut_13251 : selected 8 ⟨349591, by decide⟩
    (prefixPartial 13 106572) = some ⟨13, 2, 0, 349591, 106572, 1513, 16384⟩ := by
  decide +kernel

theorem context_13_106572_349591 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106572 ⟨349591, by decide⟩ :=
  accepted_of_selected 13 106572 ⟨349591, by decide⟩ ⟨13, 2, 0, 349591, 106572, 1513, 16384⟩
    (by decide) selected_cut_13251

theorem selected_cut_13252 : selected 8 ⟨349616, by decide⟩
    (prefixPartial 13 106573) = some ⟨13, 2, 0, 349616, 106573, 1865, 16384⟩ := by
  decide +kernel

theorem context_13_106573_349616 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106573 ⟨349616, by decide⟩ :=
  accepted_of_selected 13 106573 ⟨349616, by decide⟩ ⟨13, 2, 0, 349616, 106573, 1865, 16384⟩
    (by decide) selected_cut_13252

theorem selected_cut_13253 : selected 8 ⟨349631, by decide⟩
    (prefixPartial 13 106574) = some ⟨13, 2, 0, 349631, 106574, 1181, 16384⟩ := by
  decide +kernel

theorem context_13_106574_349631 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106574 ⟨349631, by decide⟩ :=
  accepted_of_selected 13 106574 ⟨349631, by decide⟩ ⟨13, 2, 0, 349631, 106574, 1181, 16384⟩
    (by decide) selected_cut_13253

theorem selected_cut_13254 : selected 8 ⟨349636, by decide⟩
    (prefixPartial 13 106575) = some ⟨13, 2, 0, 349636, 106575, 813, 16384⟩ := by
  decide +kernel

theorem context_13_106575_349636 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106575 ⟨349636, by decide⟩ :=
  accepted_of_selected 13 106575 ⟨349636, by decide⟩ ⟨13, 2, 0, 349636, 106575, 813, 16384⟩
    (by decide) selected_cut_13254

theorem unmarked_context_12_26643_349637 : frontier 9 ⟨349637, by decide⟩
    (prefixCache 12 26643) (prefixPartial 12 26643) = false := by
  decide +kernel

theorem node_context_12_26643_349637 : EJMOriginalGlobalDAGData.nodes 9 ⟨349637, by decide⟩ =
    .split (coordinate 12) (![⟨349591, by decide⟩,⟨349616, by decide⟩,⟨349631, by decide⟩,⟨349636, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26643_349637 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26643 ⟨349637, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26643
    ⟨349637, by decide⟩ (by decide) (![⟨349591, by decide⟩,⟨349616, by decide⟩,⟨349631, by decide⟩,⟨349636, by decide⟩]) unmarked_context_12_26643_349637 node_context_12_26643_349637
  intro a
  fin_cases a
  · exact context_13_106572_349591
  · exact context_13_106573_349616
  · exact context_13_106574_349631
  · exact context_13_106575_349636

theorem unmarked_context_11_6660_349638 : frontier 10 ⟨349638, by decide⟩
    (prefixCache 11 6660) (prefixPartial 11 6660) = false := by
  decide +kernel

theorem node_context_11_6660_349638 : EJMOriginalGlobalDAGData.nodes 10 ⟨349638, by decide⟩ =
    .split (coordinate 11) (![⟨266170, by decide⟩,⟨349501, by decide⟩,⟨349574, by decide⟩,⟨349637, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6660_349638 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6660 ⟨349638, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6660
    ⟨349638, by decide⟩ (by decide) (![⟨266170, by decide⟩,⟨349501, by decide⟩,⟨349574, by decide⟩,⟨349637, by decide⟩]) unmarked_context_11_6660_349638 node_context_11_6660_349638
  intro a
  fin_cases a
  · exact context_12_26640_266170
  · exact context_12_26641_349501
  · exact context_12_26642_349574
  · exact context_12_26643_349637

theorem selected_cut_13255 : selected 8 ⟨349656, by decide⟩
    (prefixPartial 13 106576) = some ⟨13, 2, 0, 349656, 106576, 1205, 16384⟩ := by
  decide +kernel

theorem context_13_106576_349656 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106576 ⟨349656, by decide⟩ :=
  accepted_of_selected 13 106576 ⟨349656, by decide⟩ ⟨13, 2, 0, 349656, 106576, 1205, 16384⟩
    (by decide) selected_cut_13255

theorem selected_cut_13256 : selected 8 ⟨349684, by decide⟩
    (prefixPartial 13 106577) = some ⟨13, 2, 0, 349684, 106577, 1905, 16384⟩ := by
  decide +kernel

theorem context_13_106577_349684 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106577 ⟨349684, by decide⟩ :=
  accepted_of_selected 13 106577 ⟨349684, by decide⟩ ⟨13, 2, 0, 349684, 106577, 1905, 16384⟩
    (by decide) selected_cut_13256

theorem selected_cut_13257 : selected 8 ⟨349699, by decide⟩
    (prefixPartial 13 106578) = some ⟨13, 2, 0, 349699, 106578, 1245, 16384⟩ := by
  decide +kernel

theorem context_13_106578_349699 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106578 ⟨349699, by decide⟩ :=
  accepted_of_selected 13 106578 ⟨349699, by decide⟩ ⟨13, 2, 0, 349699, 106578, 1245, 16384⟩
    (by decide) selected_cut_13257

theorem selected_cut_13258 : selected 8 ⟨349711, by decide⟩
    (prefixPartial 13 106579) = some ⟨13, 2, 0, 349711, 106579, 857, 16384⟩ := by
  decide +kernel

theorem context_13_106579_349711 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106579 ⟨349711, by decide⟩ :=
  accepted_of_selected 13 106579 ⟨349711, by decide⟩ ⟨13, 2, 0, 349711, 106579, 857, 16384⟩
    (by decide) selected_cut_13258

theorem unmarked_context_12_26644_349712 : frontier 9 ⟨349712, by decide⟩
    (prefixCache 12 26644) (prefixPartial 12 26644) = false := by
  decide +kernel

theorem node_context_12_26644_349712 : EJMOriginalGlobalDAGData.nodes 9 ⟨349712, by decide⟩ =
    .split (coordinate 12) (![⟨349656, by decide⟩,⟨349684, by decide⟩,⟨349699, by decide⟩,⟨349711, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26644_349712 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26644 ⟨349712, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26644
    ⟨349712, by decide⟩ (by decide) (![⟨349656, by decide⟩,⟨349684, by decide⟩,⟨349699, by decide⟩,⟨349711, by decide⟩]) unmarked_context_12_26644_349712 node_context_12_26644_349712
  intro a
  fin_cases a
  · exact context_13_106576_349656
  · exact context_13_106577_349684
  · exact context_13_106578_349699
  · exact context_13_106579_349711

theorem selected_cut_13259 : selected 8 ⟨349733, by decide⟩
    (prefixPartial 13 106580) = some ⟨13, 2, 0, 349733, 106580, 1381, 16384⟩ := by
  decide +kernel

theorem context_13_106580_349733 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106580 ⟨349733, by decide⟩ :=
  accepted_of_selected 13 106580 ⟨349733, by decide⟩ ⟨13, 2, 0, 349733, 106580, 1381, 16384⟩
    (by decide) selected_cut_13259

theorem selected_cut_13260 : selected 8 ⟨349758, by decide⟩
    (prefixPartial 13 106581) = some ⟨13, 2, 0, 349758, 106581, 1441, 16384⟩ := by
  decide +kernel

theorem context_13_106581_349758 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106581 ⟨349758, by decide⟩ :=
  accepted_of_selected 13 106581 ⟨349758, by decide⟩ ⟨13, 2, 0, 349758, 106581, 1441, 16384⟩
    (by decide) selected_cut_13260

theorem selected_cut_13261 : selected 8 ⟨349772, by decide⟩
    (prefixPartial 13 106582) = some ⟨13, 2, 0, 349772, 106582, 1433, 16384⟩ := by
  decide +kernel

theorem context_13_106582_349772 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106582 ⟨349772, by decide⟩ :=
  accepted_of_selected 13 106582 ⟨349772, by decide⟩ ⟨13, 2, 0, 349772, 106582, 1433, 16384⟩
    (by decide) selected_cut_13261

theorem selected_cut_13262 : selected 8 ⟨349779, by decide⟩
    (prefixPartial 13 106583) = some ⟨13, 2, 0, 349779, 106583, 897, 16384⟩ := by
  decide +kernel

theorem context_13_106583_349779 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106583 ⟨349779, by decide⟩ :=
  accepted_of_selected 13 106583 ⟨349779, by decide⟩ ⟨13, 2, 0, 349779, 106583, 897, 16384⟩
    (by decide) selected_cut_13262

theorem unmarked_context_12_26645_349780 : frontier 9 ⟨349780, by decide⟩
    (prefixCache 12 26645) (prefixPartial 12 26645) = false := by
  decide +kernel

theorem node_context_12_26645_349780 : EJMOriginalGlobalDAGData.nodes 9 ⟨349780, by decide⟩ =
    .split (coordinate 12) (![⟨349733, by decide⟩,⟨349758, by decide⟩,⟨349772, by decide⟩,⟨349779, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26645_349780 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26645 ⟨349780, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26645
    ⟨349780, by decide⟩ (by decide) (![⟨349733, by decide⟩,⟨349758, by decide⟩,⟨349772, by decide⟩,⟨349779, by decide⟩]) unmarked_context_12_26645_349780 node_context_12_26645_349780
  intro a
  fin_cases a
  · exact context_13_106580_349733
  · exact context_13_106581_349758
  · exact context_13_106582_349772
  · exact context_13_106583_349779

theorem selected_cut_13263 : selected 8 ⟨349800, by decide⟩
    (prefixPartial 13 106584) = some ⟨13, 2, 0, 349800, 106584, 1497, 16384⟩ := by
  decide +kernel

theorem context_13_106584_349800 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106584 ⟨349800, by decide⟩ :=
  accepted_of_selected 13 106584 ⟨349800, by decide⟩ ⟨13, 2, 0, 349800, 106584, 1497, 16384⟩
    (by decide) selected_cut_13263

theorem selected_cut_13264 : selected 8 ⟨349823, by decide⟩
    (prefixPartial 13 106585) = some ⟨13, 2, 0, 349823, 106585, 1965, 16384⟩ := by
  decide +kernel

theorem context_13_106585_349823 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106585 ⟨349823, by decide⟩ :=
  accepted_of_selected 13 106585 ⟨349823, by decide⟩ ⟨13, 2, 0, 349823, 106585, 1965, 16384⟩
    (by decide) selected_cut_13264

theorem selected_cut_13265 : selected 8 ⟨349844, by decide⟩
    (prefixPartial 13 106586) = some ⟨13, 2, 0, 349844, 106586, 1497, 16384⟩ := by
  decide +kernel

theorem context_13_106586_349844 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106586 ⟨349844, by decide⟩ :=
  accepted_of_selected 13 106586 ⟨349844, by decide⟩ ⟨13, 2, 0, 349844, 106586, 1497, 16384⟩
    (by decide) selected_cut_13265

theorem selected_cut_13266 : selected 8 ⟨349851, by decide⟩
    (prefixPartial 13 106587) = some ⟨13, 2, 0, 349851, 106587, 1001, 16384⟩ := by
  decide +kernel

theorem context_13_106587_349851 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106587 ⟨349851, by decide⟩ :=
  accepted_of_selected 13 106587 ⟨349851, by decide⟩ ⟨13, 2, 0, 349851, 106587, 1001, 16384⟩
    (by decide) selected_cut_13266

theorem unmarked_context_12_26646_349852 : frontier 9 ⟨349852, by decide⟩
    (prefixCache 12 26646) (prefixPartial 12 26646) = false := by
  decide +kernel

theorem node_context_12_26646_349852 : EJMOriginalGlobalDAGData.nodes 9 ⟨349852, by decide⟩ =
    .split (coordinate 12) (![⟨349800, by decide⟩,⟨349823, by decide⟩,⟨349844, by decide⟩,⟨349851, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26646_349852 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26646 ⟨349852, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26646
    ⟨349852, by decide⟩ (by decide) (![⟨349800, by decide⟩,⟨349823, by decide⟩,⟨349844, by decide⟩,⟨349851, by decide⟩]) unmarked_context_12_26646_349852 node_context_12_26646_349852
  intro a
  fin_cases a
  · exact context_13_106584_349800
  · exact context_13_106585_349823
  · exact context_13_106586_349844
  · exact context_13_106587_349851

theorem selected_cut_13267 : selected 8 ⟨349874, by decide⟩
    (prefixPartial 13 106588) = some ⟨13, 2, 0, 349874, 106588, 1697, 16384⟩ := by
  decide +kernel

theorem context_13_106588_349874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106588 ⟨349874, by decide⟩ :=
  accepted_of_selected 13 106588 ⟨349874, by decide⟩ ⟨13, 2, 0, 349874, 106588, 1697, 16384⟩
    (by decide) selected_cut_13267

theorem selected_cut_13268 : selected 8 ⟨349897, by decide⟩
    (prefixPartial 13 106589) = some ⟨13, 2, 0, 349897, 106589, 2025, 16384⟩ := by
  decide +kernel

theorem context_13_106589_349897 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106589 ⟨349897, by decide⟩ :=
  accepted_of_selected 13 106589 ⟨349897, by decide⟩ ⟨13, 2, 0, 349897, 106589, 2025, 16384⟩
    (by decide) selected_cut_13268

theorem selected_cut_13269 : selected 8 ⟨349916, by decide⟩
    (prefixPartial 13 106590) = some ⟨13, 2, 0, 349916, 106590, 1421, 16384⟩ := by
  decide +kernel

theorem context_13_106590_349916 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106590 ⟨349916, by decide⟩ :=
  accepted_of_selected 13 106590 ⟨349916, by decide⟩ ⟨13, 2, 0, 349916, 106590, 1421, 16384⟩
    (by decide) selected_cut_13269

theorem selected_cut_13270 : selected 8 ⟨349926, by decide⟩
    (prefixPartial 13 106591) = some ⟨13, 2, 0, 349926, 106591, 1005, 16384⟩ := by
  decide +kernel

theorem context_13_106591_349926 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106591 ⟨349926, by decide⟩ :=
  accepted_of_selected 13 106591 ⟨349926, by decide⟩ ⟨13, 2, 0, 349926, 106591, 1005, 16384⟩
    (by decide) selected_cut_13270

theorem unmarked_context_12_26647_349927 : frontier 9 ⟨349927, by decide⟩
    (prefixCache 12 26647) (prefixPartial 12 26647) = false := by
  decide +kernel

theorem node_context_12_26647_349927 : EJMOriginalGlobalDAGData.nodes 9 ⟨349927, by decide⟩ =
    .split (coordinate 12) (![⟨349874, by decide⟩,⟨349897, by decide⟩,⟨349916, by decide⟩,⟨349926, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26647_349927 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26647 ⟨349927, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26647
    ⟨349927, by decide⟩ (by decide) (![⟨349874, by decide⟩,⟨349897, by decide⟩,⟨349916, by decide⟩,⟨349926, by decide⟩]) unmarked_context_12_26647_349927 node_context_12_26647_349927
  intro a
  fin_cases a
  · exact context_13_106588_349874
  · exact context_13_106589_349897
  · exact context_13_106590_349916
  · exact context_13_106591_349926

theorem unmarked_context_11_6661_349928 : frontier 10 ⟨349928, by decide⟩
    (prefixCache 11 6661) (prefixPartial 11 6661) = false := by
  decide +kernel

theorem node_context_11_6661_349928 : EJMOriginalGlobalDAGData.nodes 10 ⟨349928, by decide⟩ =
    .split (coordinate 11) (![⟨349712, by decide⟩,⟨349780, by decide⟩,⟨349852, by decide⟩,⟨349927, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6661_349928 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6661 ⟨349928, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6661
    ⟨349928, by decide⟩ (by decide) (![⟨349712, by decide⟩,⟨349780, by decide⟩,⟨349852, by decide⟩,⟨349927, by decide⟩]) unmarked_context_11_6661_349928 node_context_11_6661_349928
  intro a
  fin_cases a
  · exact context_12_26644_349712
  · exact context_12_26645_349780
  · exact context_12_26646_349852
  · exact context_12_26647_349927

theorem selected_cut_13271 : selected 8 ⟨349943, by decide⟩
    (prefixPartial 13 106592) = some ⟨13, 2, 0, 349943, 106592, 925, 16384⟩ := by
  decide +kernel

theorem context_13_106592_349943 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106592 ⟨349943, by decide⟩ :=
  accepted_of_selected 13 106592 ⟨349943, by decide⟩ ⟨13, 2, 0, 349943, 106592, 925, 16384⟩
    (by decide) selected_cut_13271

theorem selected_cut_13272 : selected 8 ⟨349978, by decide⟩
    (prefixPartial 13 106593) = some ⟨13, 2, 0, 349978, 106593, 2161, 16384⟩ := by
  decide +kernel

theorem context_13_106593_349978 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106593 ⟨349978, by decide⟩ :=
  accepted_of_selected 13 106593 ⟨349978, by decide⟩ ⟨13, 2, 0, 349978, 106593, 2161, 16384⟩
    (by decide) selected_cut_13272

theorem selected_cut_13273 : selected 8 ⟨349993, by decide⟩
    (prefixPartial 13 106594) = some ⟨13, 2, 0, 349993, 106594, 1329, 16384⟩ := by
  decide +kernel

theorem context_13_106594_349993 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106594 ⟨349993, by decide⟩ :=
  accepted_of_selected 13 106594 ⟨349993, by decide⟩ ⟨13, 2, 0, 349993, 106594, 1329, 16384⟩
    (by decide) selected_cut_13273

theorem selected_cut_13274 : selected 8 ⟨350002, by decide⟩
    (prefixPartial 13 106595) = some ⟨13, 2, 0, 350002, 106595, 873, 16384⟩ := by
  decide +kernel

theorem context_13_106595_350002 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106595 ⟨350002, by decide⟩ :=
  accepted_of_selected 13 106595 ⟨350002, by decide⟩ ⟨13, 2, 0, 350002, 106595, 873, 16384⟩
    (by decide) selected_cut_13274

theorem unmarked_context_12_26648_350003 : frontier 9 ⟨350003, by decide⟩
    (prefixCache 12 26648) (prefixPartial 12 26648) = false := by
  decide +kernel

theorem node_context_12_26648_350003 : EJMOriginalGlobalDAGData.nodes 9 ⟨350003, by decide⟩ =
    .split (coordinate 12) (![⟨349943, by decide⟩,⟨349978, by decide⟩,⟨349993, by decide⟩,⟨350002, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26648_350003 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26648 ⟨350003, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26648
    ⟨350003, by decide⟩ (by decide) (![⟨349943, by decide⟩,⟨349978, by decide⟩,⟨349993, by decide⟩,⟨350002, by decide⟩]) unmarked_context_12_26648_350003 node_context_12_26648_350003
  intro a
  fin_cases a
  · exact context_13_106592_349943
  · exact context_13_106593_349978
  · exact context_13_106594_349993
  · exact context_13_106595_350002

theorem selected_cut_13275 : selected 8 ⟨350017, by decide⟩
    (prefixPartial 13 106596) = some ⟨13, 2, 0, 350017, 106596, 1077, 16384⟩ := by
  decide +kernel

theorem context_13_106596_350017 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106596 ⟨350017, by decide⟩ :=
  accepted_of_selected 13 106596 ⟨350017, by decide⟩ ⟨13, 2, 0, 350017, 106596, 1077, 16384⟩
    (by decide) selected_cut_13275

theorem selected_cut_13276 : selected 8 ⟨350041, by decide⟩
    (prefixPartial 13 106597) = some ⟨13, 2, 0, 350041, 106597, 1721, 16384⟩ := by
  decide +kernel

theorem context_13_106597_350041 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106597 ⟨350041, by decide⟩ :=
  accepted_of_selected 13 106597 ⟨350041, by decide⟩ ⟨13, 2, 0, 350041, 106597, 1721, 16384⟩
    (by decide) selected_cut_13276

theorem selected_cut_13277 : selected 8 ⟨350056, by decide⟩
    (prefixPartial 13 106598) = some ⟨13, 2, 0, 350056, 106598, 1281, 16384⟩ := by
  decide +kernel

theorem context_13_106598_350056 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106598 ⟨350056, by decide⟩ :=
  accepted_of_selected 13 106598 ⟨350056, by decide⟩ ⟨13, 2, 0, 350056, 106598, 1281, 16384⟩
    (by decide) selected_cut_13277

theorem selected_cut_13278 : selected 8 ⟨350064, by decide⟩
    (prefixPartial 13 106599) = some ⟨13, 2, 0, 350064, 106599, 849, 16384⟩ := by
  decide +kernel

theorem context_13_106599_350064 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106599 ⟨350064, by decide⟩ :=
  accepted_of_selected 13 106599 ⟨350064, by decide⟩ ⟨13, 2, 0, 350064, 106599, 849, 16384⟩
    (by decide) selected_cut_13278

theorem unmarked_context_12_26649_350065 : frontier 9 ⟨350065, by decide⟩
    (prefixCache 12 26649) (prefixPartial 12 26649) = false := by
  decide +kernel

theorem node_context_12_26649_350065 : EJMOriginalGlobalDAGData.nodes 9 ⟨350065, by decide⟩ =
    .split (coordinate 12) (![⟨350017, by decide⟩,⟨350041, by decide⟩,⟨350056, by decide⟩,⟨350064, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26649_350065 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26649 ⟨350065, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26649
    ⟨350065, by decide⟩ (by decide) (![⟨350017, by decide⟩,⟨350041, by decide⟩,⟨350056, by decide⟩,⟨350064, by decide⟩]) unmarked_context_12_26649_350065 node_context_12_26649_350065
  intro a
  fin_cases a
  · exact context_13_106596_350017
  · exact context_13_106597_350041
  · exact context_13_106598_350056
  · exact context_13_106599_350064

theorem selected_cut_13279 : selected 8 ⟨350079, by decide⟩
    (prefixPartial 13 106600) = some ⟨13, 2, 0, 350079, 106600, 1005, 16384⟩ := by
  decide +kernel

theorem context_13_106600_350079 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106600 ⟨350079, by decide⟩ :=
  accepted_of_selected 13 106600 ⟨350079, by decide⟩ ⟨13, 2, 0, 350079, 106600, 1005, 16384⟩
    (by decide) selected_cut_13279

theorem selected_cut_13280 : selected 8 ⟨350108, by decide⟩
    (prefixPartial 13 106601) = some ⟨13, 2, 0, 350108, 106601, 1913, 16384⟩ := by
  decide +kernel

theorem context_13_106601_350108 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106601 ⟨350108, by decide⟩ :=
  accepted_of_selected 13 106601 ⟨350108, by decide⟩ ⟨13, 2, 0, 350108, 106601, 1913, 16384⟩
    (by decide) selected_cut_13280

theorem selected_cut_13281 : selected 8 ⟨350123, by decide⟩
    (prefixPartial 13 106602) = some ⟨13, 2, 0, 350123, 106602, 1225, 16384⟩ := by
  decide +kernel

theorem context_13_106602_350123 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106602 ⟨350123, by decide⟩ :=
  accepted_of_selected 13 106602 ⟨350123, by decide⟩ ⟨13, 2, 0, 350123, 106602, 1225, 16384⟩
    (by decide) selected_cut_13281

theorem selected_cut_13282 : selected 8 ⟨350129, by decide⟩
    (prefixPartial 13 106603) = some ⟨13, 2, 0, 350129, 106603, 921, 16384⟩ := by
  decide +kernel

theorem context_13_106603_350129 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106603 ⟨350129, by decide⟩ :=
  accepted_of_selected 13 106603 ⟨350129, by decide⟩ ⟨13, 2, 0, 350129, 106603, 921, 16384⟩
    (by decide) selected_cut_13282

theorem unmarked_context_12_26650_350130 : frontier 9 ⟨350130, by decide⟩
    (prefixCache 12 26650) (prefixPartial 12 26650) = false := by
  decide +kernel

theorem node_context_12_26650_350130 : EJMOriginalGlobalDAGData.nodes 9 ⟨350130, by decide⟩ =
    .split (coordinate 12) (![⟨350079, by decide⟩,⟨350108, by decide⟩,⟨350123, by decide⟩,⟨350129, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26650_350130 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26650 ⟨350130, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26650
    ⟨350130, by decide⟩ (by decide) (![⟨350079, by decide⟩,⟨350108, by decide⟩,⟨350123, by decide⟩,⟨350129, by decide⟩]) unmarked_context_12_26650_350130 node_context_12_26650_350130
  intro a
  fin_cases a
  · exact context_13_106600_350079
  · exact context_13_106601_350108
  · exact context_13_106602_350123
  · exact context_13_106603_350129

theorem selected_cut_13283 : selected 8 ⟨350149, by decide⟩
    (prefixPartial 13 106604) = some ⟨13, 2, 0, 350149, 106604, 1241, 16384⟩ := by
  decide +kernel

theorem context_13_106604_350149 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106604 ⟨350149, by decide⟩ :=
  accepted_of_selected 13 106604 ⟨350149, by decide⟩ ⟨13, 2, 0, 350149, 106604, 1241, 16384⟩
    (by decide) selected_cut_13283

theorem selected_cut_13284 : selected 8 ⟨350180, by decide⟩
    (prefixPartial 13 106605) = some ⟨13, 2, 0, 350180, 106605, 2129, 16384⟩ := by
  decide +kernel

theorem context_13_106605_350180 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106605 ⟨350180, by decide⟩ :=
  accepted_of_selected 13 106605 ⟨350180, by decide⟩ ⟨13, 2, 0, 350180, 106605, 2129, 16384⟩
    (by decide) selected_cut_13284

theorem selected_cut_13285 : selected 8 ⟨350198, by decide⟩
    (prefixPartial 13 106606) = some ⟨13, 2, 0, 350198, 106606, 1373, 16384⟩ := by
  decide +kernel

theorem context_13_106606_350198 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106606 ⟨350198, by decide⟩ :=
  accepted_of_selected 13 106606 ⟨350198, by decide⟩ ⟨13, 2, 0, 350198, 106606, 1373, 16384⟩
    (by decide) selected_cut_13285

theorem selected_cut_13286 : selected 8 ⟨350208, by decide⟩
    (prefixPartial 13 106607) = some ⟨13, 2, 0, 350208, 106607, 897, 16384⟩ := by
  decide +kernel

theorem context_13_106607_350208 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106607 ⟨350208, by decide⟩ :=
  accepted_of_selected 13 106607 ⟨350208, by decide⟩ ⟨13, 2, 0, 350208, 106607, 897, 16384⟩
    (by decide) selected_cut_13286

theorem unmarked_context_12_26651_350209 : frontier 9 ⟨350209, by decide⟩
    (prefixCache 12 26651) (prefixPartial 12 26651) = false := by
  decide +kernel

theorem node_context_12_26651_350209 : EJMOriginalGlobalDAGData.nodes 9 ⟨350209, by decide⟩ =
    .split (coordinate 12) (![⟨350149, by decide⟩,⟨350180, by decide⟩,⟨350198, by decide⟩,⟨350208, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26651_350209 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26651 ⟨350209, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26651
    ⟨350209, by decide⟩ (by decide) (![⟨350149, by decide⟩,⟨350180, by decide⟩,⟨350198, by decide⟩,⟨350208, by decide⟩]) unmarked_context_12_26651_350209 node_context_12_26651_350209
  intro a
  fin_cases a
  · exact context_13_106604_350149
  · exact context_13_106605_350180
  · exact context_13_106606_350198
  · exact context_13_106607_350208

theorem unmarked_context_11_6662_350210 : frontier 10 ⟨350210, by decide⟩
    (prefixCache 11 6662) (prefixPartial 11 6662) = false := by
  decide +kernel

theorem node_context_11_6662_350210 : EJMOriginalGlobalDAGData.nodes 10 ⟨350210, by decide⟩ =
    .split (coordinate 11) (![⟨350003, by decide⟩,⟨350065, by decide⟩,⟨350130, by decide⟩,⟨350209, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6662_350210 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6662 ⟨350210, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6662
    ⟨350210, by decide⟩ (by decide) (![⟨350003, by decide⟩,⟨350065, by decide⟩,⟨350130, by decide⟩,⟨350209, by decide⟩]) unmarked_context_11_6662_350210 node_context_11_6662_350210
  intro a
  fin_cases a
  · exact context_12_26648_350003
  · exact context_12_26649_350065
  · exact context_12_26650_350130
  · exact context_12_26651_350209

theorem selected_cut_13287 : selected 8 ⟨350220, by decide⟩
    (prefixPartial 13 106608) = some ⟨13, 2, 0, 350220, 106608, 1029, 16384⟩ := by
  decide +kernel

theorem context_13_106608_350220 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106608 ⟨350220, by decide⟩ :=
  accepted_of_selected 13 106608 ⟨350220, by decide⟩ ⟨13, 2, 0, 350220, 106608, 1029, 16384⟩
    (by decide) selected_cut_13287

theorem selected_cut_13288 : selected 8 ⟨350251, by decide⟩
    (prefixPartial 13 106609) = some ⟨13, 2, 0, 350251, 106609, 1913, 16384⟩ := by
  decide +kernel

theorem context_13_106609_350251 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106609 ⟨350251, by decide⟩ :=
  accepted_of_selected 13 106609 ⟨350251, by decide⟩ ⟨13, 2, 0, 350251, 106609, 1913, 16384⟩
    (by decide) selected_cut_13288

theorem selected_cut_13289 : selected 8 ⟨350266, by decide⟩
    (prefixPartial 13 106610) = some ⟨13, 2, 0, 350266, 106610, 1097, 16384⟩ := by
  decide +kernel

theorem context_13_106610_350266 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106610 ⟨350266, by decide⟩ :=
  accepted_of_selected 13 106610 ⟨350266, by decide⟩ ⟨13, 2, 0, 350266, 106610, 1097, 16384⟩
    (by decide) selected_cut_13289

theorem selected_cut_13290 : selected 8 ⟨350271, by decide⟩
    (prefixPartial 13 106611) = some ⟨13, 2, 0, 350271, 106611, 741, 16384⟩ := by
  decide +kernel

theorem context_13_106611_350271 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106611 ⟨350271, by decide⟩ :=
  accepted_of_selected 13 106611 ⟨350271, by decide⟩ ⟨13, 2, 0, 350271, 106611, 741, 16384⟩
    (by decide) selected_cut_13290

theorem unmarked_context_12_26652_350272 : frontier 9 ⟨350272, by decide⟩
    (prefixCache 12 26652) (prefixPartial 12 26652) = false := by
  decide +kernel

theorem node_context_12_26652_350272 : EJMOriginalGlobalDAGData.nodes 9 ⟨350272, by decide⟩ =
    .split (coordinate 12) (![⟨350220, by decide⟩,⟨350251, by decide⟩,⟨350266, by decide⟩,⟨350271, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26652_350272 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26652 ⟨350272, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26652
    ⟨350272, by decide⟩ (by decide) (![⟨350220, by decide⟩,⟨350251, by decide⟩,⟨350266, by decide⟩,⟨350271, by decide⟩]) unmarked_context_12_26652_350272 node_context_12_26652_350272
  intro a
  fin_cases a
  · exact context_13_106608_350220
  · exact context_13_106609_350251
  · exact context_13_106610_350266
  · exact context_13_106611_350271

theorem selected_cut_13291 : selected 8 ⟨350288, by decide⟩
    (prefixPartial 13 106612) = some ⟨13, 2, 0, 350288, 106612, 1181, 16384⟩ := by
  decide +kernel

theorem context_13_106612_350288 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106612 ⟨350288, by decide⟩ :=
  accepted_of_selected 13 106612 ⟨350288, by decide⟩ ⟨13, 2, 0, 350288, 106612, 1181, 16384⟩
    (by decide) selected_cut_13291

theorem selected_cut_13292 : selected 8 ⟨350314, by decide⟩
    (prefixPartial 13 106613) = some ⟨13, 2, 0, 350314, 106613, 1789, 16384⟩ := by
  decide +kernel

theorem context_13_106613_350314 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106613 ⟨350314, by decide⟩ :=
  accepted_of_selected 13 106613 ⟨350314, by decide⟩ ⟨13, 2, 0, 350314, 106613, 1789, 16384⟩
    (by decide) selected_cut_13292

theorem selected_cut_13293 : selected 8 ⟨350330, by decide⟩
    (prefixPartial 13 106614) = some ⟨13, 2, 0, 350330, 106614, 1305, 16384⟩ := by
  decide +kernel

theorem context_13_106614_350330 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106614 ⟨350330, by decide⟩ :=
  accepted_of_selected 13 106614 ⟨350330, by decide⟩ ⟨13, 2, 0, 350330, 106614, 1305, 16384⟩
    (by decide) selected_cut_13293

theorem selected_cut_13294 : selected 8 ⟨350335, by decide⟩
    (prefixPartial 13 106615) = some ⟨13, 2, 0, 350335, 106615, 745, 16384⟩ := by
  decide +kernel

theorem context_13_106615_350335 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106615 ⟨350335, by decide⟩ :=
  accepted_of_selected 13 106615 ⟨350335, by decide⟩ ⟨13, 2, 0, 350335, 106615, 745, 16384⟩
    (by decide) selected_cut_13294

theorem unmarked_context_12_26653_350336 : frontier 9 ⟨350336, by decide⟩
    (prefixCache 12 26653) (prefixPartial 12 26653) = false := by
  decide +kernel

theorem node_context_12_26653_350336 : EJMOriginalGlobalDAGData.nodes 9 ⟨350336, by decide⟩ =
    .split (coordinate 12) (![⟨350288, by decide⟩,⟨350314, by decide⟩,⟨350330, by decide⟩,⟨350335, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26653_350336 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26653 ⟨350336, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26653
    ⟨350336, by decide⟩ (by decide) (![⟨350288, by decide⟩,⟨350314, by decide⟩,⟨350330, by decide⟩,⟨350335, by decide⟩]) unmarked_context_12_26653_350336 node_context_12_26653_350336
  intro a
  fin_cases a
  · exact context_13_106612_350288
  · exact context_13_106613_350314
  · exact context_13_106614_350330
  · exact context_13_106615_350335

theorem selected_cut_13295 : selected 8 ⟨350350, by decide⟩
    (prefixPartial 13 106616) = some ⟨13, 2, 0, 350350, 106616, 1125, 16384⟩ := by
  decide +kernel

theorem context_13_106616_350350 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106616 ⟨350350, by decide⟩ :=
  accepted_of_selected 13 106616 ⟨350350, by decide⟩ ⟨13, 2, 0, 350350, 106616, 1125, 16384⟩
    (by decide) selected_cut_13295

theorem selected_cut_13296 : selected 8 ⟨350375, by decide⟩
    (prefixPartial 13 106617) = some ⟨13, 2, 0, 350375, 106617, 1989, 16384⟩ := by
  decide +kernel

theorem context_13_106617_350375 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106617 ⟨350375, by decide⟩ :=
  accepted_of_selected 13 106617 ⟨350375, by decide⟩ ⟨13, 2, 0, 350375, 106617, 1989, 16384⟩
    (by decide) selected_cut_13296

theorem selected_cut_13297 : selected 8 ⟨350394, by decide⟩
    (prefixPartial 13 106618) = some ⟨13, 2, 0, 350394, 106618, 1321, 16384⟩ := by
  decide +kernel

theorem context_13_106618_350394 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106618 ⟨350394, by decide⟩ :=
  accepted_of_selected 13 106618 ⟨350394, by decide⟩ ⟨13, 2, 0, 350394, 106618, 1321, 16384⟩
    (by decide) selected_cut_13297

theorem selected_cut_13298 : selected 8 ⟨350400, by decide⟩
    (prefixPartial 13 106619) = some ⟨13, 2, 0, 350400, 106619, 737, 16384⟩ := by
  decide +kernel

theorem context_13_106619_350400 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106619 ⟨350400, by decide⟩ :=
  accepted_of_selected 13 106619 ⟨350400, by decide⟩ ⟨13, 2, 0, 350400, 106619, 737, 16384⟩
    (by decide) selected_cut_13298

theorem unmarked_context_12_26654_350401 : frontier 9 ⟨350401, by decide⟩
    (prefixCache 12 26654) (prefixPartial 12 26654) = false := by
  decide +kernel

theorem node_context_12_26654_350401 : EJMOriginalGlobalDAGData.nodes 9 ⟨350401, by decide⟩ =
    .split (coordinate 12) (![⟨350350, by decide⟩,⟨350375, by decide⟩,⟨350394, by decide⟩,⟨350400, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26654_350401 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26654 ⟨350401, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26654
    ⟨350401, by decide⟩ (by decide) (![⟨350350, by decide⟩,⟨350375, by decide⟩,⟨350394, by decide⟩,⟨350400, by decide⟩]) unmarked_context_12_26654_350401 node_context_12_26654_350401
  intro a
  fin_cases a
  · exact context_13_106616_350350
  · exact context_13_106617_350375
  · exact context_13_106618_350394
  · exact context_13_106619_350400

theorem selected_cut_13299 : selected 8 ⟨350418, by decide⟩
    (prefixPartial 13 106620) = some ⟨13, 2, 0, 350418, 106620, 1201, 16384⟩ := by
  decide +kernel

theorem context_13_106620_350418 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106620 ⟨350418, by decide⟩ :=
  accepted_of_selected 13 106620 ⟨350418, by decide⟩ ⟨13, 2, 0, 350418, 106620, 1201, 16384⟩
    (by decide) selected_cut_13299

theorem selected_cut_13300 : selected 8 ⟨350451, by decide⟩
    (prefixPartial 13 106621) = some ⟨13, 2, 0, 350451, 106621, 2061, 16384⟩ := by
  decide +kernel

theorem context_13_106621_350451 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106621 ⟨350451, by decide⟩ :=
  accepted_of_selected 13 106621 ⟨350451, by decide⟩ ⟨13, 2, 0, 350451, 106621, 2061, 16384⟩
    (by decide) selected_cut_13300

theorem selected_cut_13301 : selected 8 ⟨350470, by decide⟩
    (prefixPartial 13 106622) = some ⟨13, 2, 0, 350470, 106622, 1217, 16384⟩ := by
  decide +kernel

theorem context_13_106622_350470 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106622 ⟨350470, by decide⟩ :=
  accepted_of_selected 13 106622 ⟨350470, by decide⟩ ⟨13, 2, 0, 350470, 106622, 1217, 16384⟩
    (by decide) selected_cut_13301

theorem selected_cut_13302 : selected 8 ⟨350474, by decide⟩
    (prefixPartial 13 106623) = some ⟨13, 2, 0, 350474, 106623, 769, 16384⟩ := by
  decide +kernel

theorem context_13_106623_350474 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106623 ⟨350474, by decide⟩ :=
  accepted_of_selected 13 106623 ⟨350474, by decide⟩ ⟨13, 2, 0, 350474, 106623, 769, 16384⟩
    (by decide) selected_cut_13302

theorem unmarked_context_12_26655_350475 : frontier 9 ⟨350475, by decide⟩
    (prefixCache 12 26655) (prefixPartial 12 26655) = false := by
  decide +kernel

theorem node_context_12_26655_350475 : EJMOriginalGlobalDAGData.nodes 9 ⟨350475, by decide⟩ =
    .split (coordinate 12) (![⟨350418, by decide⟩,⟨350451, by decide⟩,⟨350470, by decide⟩,⟨350474, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26655_350475 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26655 ⟨350475, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26655
    ⟨350475, by decide⟩ (by decide) (![⟨350418, by decide⟩,⟨350451, by decide⟩,⟨350470, by decide⟩,⟨350474, by decide⟩]) unmarked_context_12_26655_350475 node_context_12_26655_350475
  intro a
  fin_cases a
  · exact context_13_106620_350418
  · exact context_13_106621_350451
  · exact context_13_106622_350470
  · exact context_13_106623_350474

theorem unmarked_context_11_6663_350476 : frontier 10 ⟨350476, by decide⟩
    (prefixCache 11 6663) (prefixPartial 11 6663) = false := by
  decide +kernel

theorem node_context_11_6663_350476 : EJMOriginalGlobalDAGData.nodes 10 ⟨350476, by decide⟩ =
    .split (coordinate 11) (![⟨350272, by decide⟩,⟨350336, by decide⟩,⟨350401, by decide⟩,⟨350475, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6663_350476 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6663 ⟨350476, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6663
    ⟨350476, by decide⟩ (by decide) (![⟨350272, by decide⟩,⟨350336, by decide⟩,⟨350401, by decide⟩,⟨350475, by decide⟩]) unmarked_context_11_6663_350476 node_context_11_6663_350476
  intro a
  fin_cases a
  · exact context_12_26652_350272
  · exact context_12_26653_350336
  · exact context_12_26654_350401
  · exact context_12_26655_350475

theorem unmarked_context_10_1665_350477 : frontier 11 ⟨350477, by decide⟩
    (prefixCache 10 1665) (prefixPartial 10 1665) = false := by
  decide +kernel

theorem node_context_10_1665_350477 : EJMOriginalGlobalDAGData.nodes 11 ⟨350477, by decide⟩ =
    .split (coordinate 10) (![⟨349638, by decide⟩,⟨349928, by decide⟩,⟨350210, by decide⟩,⟨350476, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1665_350477 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1665 ⟨350477, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1665
    ⟨350477, by decide⟩ (by decide) (![⟨349638, by decide⟩,⟨349928, by decide⟩,⟨350210, by decide⟩,⟨350476, by decide⟩]) unmarked_context_10_1665_350477 node_context_10_1665_350477
  intro a
  fin_cases a
  · exact context_11_6660_349638
  · exact context_11_6661_349928
  · exact context_11_6662_350210
  · exact context_11_6663_350476

theorem selected_cut_13303 : selected 8 ⟨350489, by decide⟩
    (prefixPartial 13 106624) = some ⟨13, 2, 0, 350489, 106624, 1145, 16384⟩ := by
  decide +kernel

theorem context_13_106624_350489 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106624 ⟨350489, by decide⟩ :=
  accepted_of_selected 13 106624 ⟨350489, by decide⟩ ⟨13, 2, 0, 350489, 106624, 1145, 16384⟩
    (by decide) selected_cut_13303

theorem selected_cut_13304 : selected 8 ⟨350561, by decide⟩
    (prefixPartial 13 106625) = some ⟨13, 2, 0, 350561, 106625, 2241, 16384⟩ := by
  decide +kernel

theorem context_13_106625_350561 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106625 ⟨350561, by decide⟩ :=
  accepted_of_selected 13 106625 ⟨350561, by decide⟩ ⟨13, 2, 0, 350561, 106625, 2241, 16384⟩
    (by decide) selected_cut_13304

theorem selected_cut_13305 : selected 8 ⟨350584, by decide⟩
    (prefixPartial 13 106626) = some ⟨13, 2, 0, 350584, 106626, 825, 16384⟩ := by
  decide +kernel

theorem context_13_106626_350584 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106626 ⟨350584, by decide⟩ :=
  accepted_of_selected 13 106626 ⟨350584, by decide⟩ ⟨13, 2, 0, 350584, 106626, 825, 16384⟩
    (by decide) selected_cut_13305

theorem selected_cut_13306 : selected 8 ⟨350592, by decide⟩
    (prefixPartial 13 106627) = some ⟨13, 2, 0, 350592, 106627, 269, 16384⟩ := by
  decide +kernel

theorem context_13_106627_350592 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106627 ⟨350592, by decide⟩ :=
  accepted_of_selected 13 106627 ⟨350592, by decide⟩ ⟨13, 2, 0, 350592, 106627, 269, 16384⟩
    (by decide) selected_cut_13306

theorem unmarked_context_12_26656_350593 : frontier 9 ⟨350593, by decide⟩
    (prefixCache 12 26656) (prefixPartial 12 26656) = false := by
  decide +kernel

theorem node_context_12_26656_350593 : EJMOriginalGlobalDAGData.nodes 9 ⟨350593, by decide⟩ =
    .split (coordinate 12) (![⟨350489, by decide⟩,⟨350561, by decide⟩,⟨350584, by decide⟩,⟨350592, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26656_350593 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26656 ⟨350593, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26656
    ⟨350593, by decide⟩ (by decide) (![⟨350489, by decide⟩,⟨350561, by decide⟩,⟨350584, by decide⟩,⟨350592, by decide⟩]) unmarked_context_12_26656_350593 node_context_12_26656_350593
  intro a
  fin_cases a
  · exact context_13_106624_350489
  · exact context_13_106625_350561
  · exact context_13_106626_350584
  · exact context_13_106627_350592

theorem selected_cut_13307 : selected 9 ⟨350639, by decide⟩
    (prefixPartial 12 26657) = some ⟨12, 2, 0, 350639, 26657, 3953, 65536⟩ := by
  decide +kernel

theorem context_12_26657_350639 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26657 ⟨350639, by decide⟩ :=
  accepted_of_selected 12 26657 ⟨350639, by decide⟩ ⟨12, 2, 0, 350639, 26657, 3953, 65536⟩
    (by decide) selected_cut_13307

theorem selected_cut_13308 : selected 9 ⟨350695, by decide⟩
    (prefixPartial 12 26658) = some ⟨12, 2, 0, 350695, 26658, 4081, 65536⟩ := by
  decide +kernel

theorem context_12_26658_350695 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26658 ⟨350695, by decide⟩ :=
  accepted_of_selected 12 26658 ⟨350695, by decide⟩ ⟨12, 2, 0, 350695, 26658, 4081, 65536⟩
    (by decide) selected_cut_13308

theorem selected_cut_13309 : selected 8 ⟨350704, by decide⟩
    (prefixPartial 13 106636) = some ⟨13, 2, 0, 350704, 106636, 853, 16384⟩ := by
  decide +kernel

theorem context_13_106636_350704 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106636 ⟨350704, by decide⟩ :=
  accepted_of_selected 13 106636 ⟨350704, by decide⟩ ⟨13, 2, 0, 350704, 106636, 853, 16384⟩
    (by decide) selected_cut_13309

theorem selected_cut_13310 : selected 8 ⟨350728, by decide⟩
    (prefixPartial 13 106637) = some ⟨13, 2, 0, 350728, 106637, 1765, 16384⟩ := by
  decide +kernel

theorem context_13_106637_350728 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106637 ⟨350728, by decide⟩ :=
  accepted_of_selected 13 106637 ⟨350728, by decide⟩ ⟨13, 2, 0, 350728, 106637, 1765, 16384⟩
    (by decide) selected_cut_13310

theorem selected_cut_13311 : selected 8 ⟨350741, by decide⟩
    (prefixPartial 13 106638) = some ⟨13, 2, 0, 350741, 106638, 901, 16384⟩ := by
  decide +kernel

theorem context_13_106638_350741 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106638 ⟨350741, by decide⟩ :=
  accepted_of_selected 13 106638 ⟨350741, by decide⟩ ⟨13, 2, 0, 350741, 106638, 901, 16384⟩
    (by decide) selected_cut_13311

theorem selected_cut_13312 : selected 8 ⟨350745, by decide⟩
    (prefixPartial 13 106639) = some ⟨13, 2, 0, 350745, 106639, 693, 16384⟩ := by
  decide +kernel

theorem context_13_106639_350745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106639 ⟨350745, by decide⟩ :=
  accepted_of_selected 13 106639 ⟨350745, by decide⟩ ⟨13, 2, 0, 350745, 106639, 693, 16384⟩
    (by decide) selected_cut_13312

theorem unmarked_context_12_26659_350746 : frontier 9 ⟨350746, by decide⟩
    (prefixCache 12 26659) (prefixPartial 12 26659) = false := by
  decide +kernel

theorem node_context_12_26659_350746 : EJMOriginalGlobalDAGData.nodes 9 ⟨350746, by decide⟩ =
    .split (coordinate 12) (![⟨350704, by decide⟩,⟨350728, by decide⟩,⟨350741, by decide⟩,⟨350745, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26659_350746 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26659 ⟨350746, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26659
    ⟨350746, by decide⟩ (by decide) (![⟨350704, by decide⟩,⟨350728, by decide⟩,⟨350741, by decide⟩,⟨350745, by decide⟩]) unmarked_context_12_26659_350746 node_context_12_26659_350746
  intro a
  fin_cases a
  · exact context_13_106636_350704
  · exact context_13_106637_350728
  · exact context_13_106638_350741
  · exact context_13_106639_350745

theorem unmarked_context_11_6664_350747 : frontier 10 ⟨350747, by decide⟩
    (prefixCache 11 6664) (prefixPartial 11 6664) = false := by
  decide +kernel

theorem node_context_11_6664_350747 : EJMOriginalGlobalDAGData.nodes 10 ⟨350747, by decide⟩ =
    .split (coordinate 11) (![⟨350593, by decide⟩,⟨350639, by decide⟩,⟨350695, by decide⟩,⟨350746, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6664_350747 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6664 ⟨350747, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6664
    ⟨350747, by decide⟩ (by decide) (![⟨350593, by decide⟩,⟨350639, by decide⟩,⟨350695, by decide⟩,⟨350746, by decide⟩]) unmarked_context_11_6664_350747 node_context_11_6664_350747
  intro a
  fin_cases a
  · exact context_12_26656_350593
  · exact context_12_26657_350639
  · exact context_12_26658_350695
  · exact context_12_26659_350746

theorem selected_cut_13313 : selected 8 ⟨350756, by decide⟩
    (prefixPartial 13 106640) = some ⟨13, 2, 0, 350756, 106640, 649, 16384⟩ := by
  decide +kernel

theorem context_13_106640_350756 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106640 ⟨350756, by decide⟩ :=
  accepted_of_selected 13 106640 ⟨350756, by decide⟩ ⟨13, 2, 0, 350756, 106640, 649, 16384⟩
    (by decide) selected_cut_13313

theorem selected_cut_13314 : selected 8 ⟨350780, by decide⟩
    (prefixPartial 13 106641) = some ⟨13, 2, 0, 350780, 106641, 1649, 16384⟩ := by
  decide +kernel

theorem context_13_106641_350780 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106641 ⟨350780, by decide⟩ :=
  accepted_of_selected 13 106641 ⟨350780, by decide⟩ ⟨13, 2, 0, 350780, 106641, 1649, 16384⟩
    (by decide) selected_cut_13314

theorem selected_cut_13315 : selected 8 ⟨350795, by decide⟩
    (prefixPartial 13 106642) = some ⟨13, 2, 0, 350795, 106642, 1241, 16384⟩ := by
  decide +kernel

theorem context_13_106642_350795 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106642 ⟨350795, by decide⟩ :=
  accepted_of_selected 13 106642 ⟨350795, by decide⟩ ⟨13, 2, 0, 350795, 106642, 1241, 16384⟩
    (by decide) selected_cut_13315

theorem selected_cut_13316 : selected 8 ⟨350799, by decide⟩
    (prefixPartial 13 106643) = some ⟨13, 2, 0, 350799, 106643, 681, 16384⟩ := by
  decide +kernel

theorem context_13_106643_350799 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106643 ⟨350799, by decide⟩ :=
  accepted_of_selected 13 106643 ⟨350799, by decide⟩ ⟨13, 2, 0, 350799, 106643, 681, 16384⟩
    (by decide) selected_cut_13316

theorem unmarked_context_12_26660_350800 : frontier 9 ⟨350800, by decide⟩
    (prefixCache 12 26660) (prefixPartial 12 26660) = false := by
  decide +kernel

theorem node_context_12_26660_350800 : EJMOriginalGlobalDAGData.nodes 9 ⟨350800, by decide⟩ =
    .split (coordinate 12) (![⟨350756, by decide⟩,⟨350780, by decide⟩,⟨350795, by decide⟩,⟨350799, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26660_350800 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26660 ⟨350800, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26660
    ⟨350800, by decide⟩ (by decide) (![⟨350756, by decide⟩,⟨350780, by decide⟩,⟨350795, by decide⟩,⟨350799, by decide⟩]) unmarked_context_12_26660_350800 node_context_12_26660_350800
  intro a
  fin_cases a
  · exact context_13_106640_350756
  · exact context_13_106641_350780
  · exact context_13_106642_350795
  · exact context_13_106643_350799

theorem selected_cut_13317 : selected 8 ⟨350808, by decide⟩
    (prefixPartial 13 106644) = some ⟨13, 2, 0, 350808, 106644, 733, 16384⟩ := by
  decide +kernel

theorem context_13_106644_350808 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106644 ⟨350808, by decide⟩ :=
  accepted_of_selected 13 106644 ⟨350808, by decide⟩ ⟨13, 2, 0, 350808, 106644, 733, 16384⟩
    (by decide) selected_cut_13317

theorem selected_cut_13318 : selected 8 ⟨350829, by decide⟩
    (prefixPartial 13 106645) = some ⟨13, 2, 0, 350829, 106645, 1369, 16384⟩ := by
  decide +kernel

theorem context_13_106645_350829 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106645 ⟨350829, by decide⟩ :=
  accepted_of_selected 13 106645 ⟨350829, by decide⟩ ⟨13, 2, 0, 350829, 106645, 1369, 16384⟩
    (by decide) selected_cut_13318

theorem selected_cut_13319 : selected 8 ⟨350846, by decide⟩
    (prefixPartial 13 106646) = some ⟨13, 2, 0, 350846, 106646, 1357, 16384⟩ := by
  decide +kernel

theorem context_13_106646_350846 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106646 ⟨350846, by decide⟩ :=
  accepted_of_selected 13 106646 ⟨350846, by decide⟩ ⟨13, 2, 0, 350846, 106646, 1357, 16384⟩
    (by decide) selected_cut_13319

theorem selected_cut_13320 : selected 8 ⟨350852, by decide⟩
    (prefixPartial 13 106647) = some ⟨13, 2, 0, 350852, 106647, 713, 16384⟩ := by
  decide +kernel

theorem context_13_106647_350852 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106647 ⟨350852, by decide⟩ :=
  accepted_of_selected 13 106647 ⟨350852, by decide⟩ ⟨13, 2, 0, 350852, 106647, 713, 16384⟩
    (by decide) selected_cut_13320

theorem unmarked_context_12_26661_350853 : frontier 9 ⟨350853, by decide⟩
    (prefixCache 12 26661) (prefixPartial 12 26661) = false := by
  decide +kernel

theorem node_context_12_26661_350853 : EJMOriginalGlobalDAGData.nodes 9 ⟨350853, by decide⟩ =
    .split (coordinate 12) (![⟨350808, by decide⟩,⟨350829, by decide⟩,⟨350846, by decide⟩,⟨350852, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26661_350853 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26661 ⟨350853, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26661
    ⟨350853, by decide⟩ (by decide) (![⟨350808, by decide⟩,⟨350829, by decide⟩,⟨350846, by decide⟩,⟨350852, by decide⟩]) unmarked_context_12_26661_350853 node_context_12_26661_350853
  intro a
  fin_cases a
  · exact context_13_106644_350808
  · exact context_13_106645_350829
  · exact context_13_106646_350846
  · exact context_13_106647_350852

theorem selected_cut_13321 : selected 8 ⟨350862, by decide⟩
    (prefixPartial 13 106648) = some ⟨13, 2, 0, 350862, 106648, 641, 16384⟩ := by
  decide +kernel

theorem context_13_106648_350862 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106648 ⟨350862, by decide⟩ :=
  accepted_of_selected 13 106648 ⟨350862, by decide⟩ ⟨13, 2, 0, 350862, 106648, 641, 16384⟩
    (by decide) selected_cut_13321

theorem selected_cut_13322 : selected 8 ⟨350885, by decide⟩
    (prefixPartial 13 106649) = some ⟨13, 2, 0, 350885, 106649, 1725, 16384⟩ := by
  decide +kernel

theorem context_13_106649_350885 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106649 ⟨350885, by decide⟩ :=
  accepted_of_selected 13 106649 ⟨350885, by decide⟩ ⟨13, 2, 0, 350885, 106649, 1725, 16384⟩
    (by decide) selected_cut_13322

theorem selected_cut_13323 : selected 8 ⟨350901, by decide⟩
    (prefixPartial 13 106650) = some ⟨13, 2, 0, 350901, 106650, 1293, 16384⟩ := by
  decide +kernel

theorem context_13_106650_350901 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106650 ⟨350901, by decide⟩ :=
  accepted_of_selected 13 106650 ⟨350901, by decide⟩ ⟨13, 2, 0, 350901, 106650, 1293, 16384⟩
    (by decide) selected_cut_13323

theorem selected_cut_13324 : selected 8 ⟨350906, by decide⟩
    (prefixPartial 13 106651) = some ⟨13, 2, 0, 350906, 106651, 757, 16384⟩ := by
  decide +kernel

theorem context_13_106651_350906 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106651 ⟨350906, by decide⟩ :=
  accepted_of_selected 13 106651 ⟨350906, by decide⟩ ⟨13, 2, 0, 350906, 106651, 757, 16384⟩
    (by decide) selected_cut_13324

theorem unmarked_context_12_26662_350907 : frontier 9 ⟨350907, by decide⟩
    (prefixCache 12 26662) (prefixPartial 12 26662) = false := by
  decide +kernel

theorem node_context_12_26662_350907 : EJMOriginalGlobalDAGData.nodes 9 ⟨350907, by decide⟩ =
    .split (coordinate 12) (![⟨350862, by decide⟩,⟨350885, by decide⟩,⟨350901, by decide⟩,⟨350906, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26662_350907 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26662 ⟨350907, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26662
    ⟨350907, by decide⟩ (by decide) (![⟨350862, by decide⟩,⟨350885, by decide⟩,⟨350901, by decide⟩,⟨350906, by decide⟩]) unmarked_context_12_26662_350907 node_context_12_26662_350907
  intro a
  fin_cases a
  · exact context_13_106648_350862
  · exact context_13_106649_350885
  · exact context_13_106650_350901
  · exact context_13_106651_350906

theorem selected_cut_13325 : selected 8 ⟨350921, by decide⟩
    (prefixPartial 13 106652) = some ⟨13, 2, 0, 350921, 106652, 833, 16384⟩ := by
  decide +kernel

theorem context_13_106652_350921 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106652 ⟨350921, by decide⟩ :=
  accepted_of_selected 13 106652 ⟨350921, by decide⟩ ⟨13, 2, 0, 350921, 106652, 833, 16384⟩
    (by decide) selected_cut_13325

theorem selected_cut_13326 : selected 8 ⟨350948, by decide⟩
    (prefixPartial 13 106653) = some ⟨13, 2, 0, 350948, 106653, 1849, 16384⟩ := by
  decide +kernel

theorem context_13_106653_350948 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106653 ⟨350948, by decide⟩ :=
  accepted_of_selected 13 106653 ⟨350948, by decide⟩ ⟨13, 2, 0, 350948, 106653, 1849, 16384⟩
    (by decide) selected_cut_13326

theorem selected_cut_13327 : selected 8 ⟨350967, by decide⟩
    (prefixPartial 13 106654) = some ⟨13, 2, 0, 350967, 106654, 1213, 16384⟩ := by
  decide +kernel

theorem context_13_106654_350967 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106654 ⟨350967, by decide⟩ :=
  accepted_of_selected 13 106654 ⟨350967, by decide⟩ ⟨13, 2, 0, 350967, 106654, 1213, 16384⟩
    (by decide) selected_cut_13327

theorem selected_cut_13328 : selected 8 ⟨350975, by decide⟩
    (prefixPartial 13 106655) = some ⟨13, 2, 0, 350975, 106655, 805, 16384⟩ := by
  decide +kernel

theorem context_13_106655_350975 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106655 ⟨350975, by decide⟩ :=
  accepted_of_selected 13 106655 ⟨350975, by decide⟩ ⟨13, 2, 0, 350975, 106655, 805, 16384⟩
    (by decide) selected_cut_13328

theorem unmarked_context_12_26663_350976 : frontier 9 ⟨350976, by decide⟩
    (prefixCache 12 26663) (prefixPartial 12 26663) = false := by
  decide +kernel

theorem node_context_12_26663_350976 : EJMOriginalGlobalDAGData.nodes 9 ⟨350976, by decide⟩ =
    .split (coordinate 12) (![⟨350921, by decide⟩,⟨350948, by decide⟩,⟨350967, by decide⟩,⟨350975, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26663_350976 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26663 ⟨350976, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26663
    ⟨350976, by decide⟩ (by decide) (![⟨350921, by decide⟩,⟨350948, by decide⟩,⟨350967, by decide⟩,⟨350975, by decide⟩]) unmarked_context_12_26663_350976 node_context_12_26663_350976
  intro a
  fin_cases a
  · exact context_13_106652_350921
  · exact context_13_106653_350948
  · exact context_13_106654_350967
  · exact context_13_106655_350975

theorem unmarked_context_11_6665_350977 : frontier 10 ⟨350977, by decide⟩
    (prefixCache 11 6665) (prefixPartial 11 6665) = false := by
  decide +kernel

theorem node_context_11_6665_350977 : EJMOriginalGlobalDAGData.nodes 10 ⟨350977, by decide⟩ =
    .split (coordinate 11) (![⟨350800, by decide⟩,⟨350853, by decide⟩,⟨350907, by decide⟩,⟨350976, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6665_350977 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6665 ⟨350977, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6665
    ⟨350977, by decide⟩ (by decide) (![⟨350800, by decide⟩,⟨350853, by decide⟩,⟨350907, by decide⟩,⟨350976, by decide⟩]) unmarked_context_11_6665_350977 node_context_11_6665_350977
  intro a
  fin_cases a
  · exact context_12_26660_350800
  · exact context_12_26661_350853
  · exact context_12_26662_350907
  · exact context_12_26663_350976

theorem selected_cut_13329 : selected 8 ⟨350986, by decide⟩
    (prefixPartial 13 106656) = some ⟨13, 2, 0, 350986, 106656, 761, 16384⟩ := by
  decide +kernel

theorem context_13_106656_350986 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106656 ⟨350986, by decide⟩ :=
  accepted_of_selected 13 106656 ⟨350986, by decide⟩ ⟨13, 2, 0, 350986, 106656, 761, 16384⟩
    (by decide) selected_cut_13329

theorem selected_cut_13330 : selected 8 ⟨351038, by decide⟩
    (prefixPartial 13 106657) = some ⟨13, 2, 0, 351038, 106657, 3061, 16384⟩ := by
  decide +kernel

theorem context_13_106657_351038 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106657 ⟨351038, by decide⟩ :=
  accepted_of_selected 13 106657 ⟨351038, by decide⟩ ⟨13, 2, 0, 351038, 106657, 3061, 16384⟩
    (by decide) selected_cut_13330

theorem selected_cut_13331 : selected 8 ⟨351057, by decide⟩
    (prefixPartial 13 106658) = some ⟨13, 2, 0, 351057, 106658, 1717, 16384⟩ := by
  decide +kernel

theorem context_13_106658_351057 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106658 ⟨351057, by decide⟩ :=
  accepted_of_selected 13 106658 ⟨351057, by decide⟩ ⟨13, 2, 0, 351057, 106658, 1717, 16384⟩
    (by decide) selected_cut_13331

theorem selected_cut_13332 : selected 8 ⟨351068, by decide⟩
    (prefixPartial 13 106659) = some ⟨13, 2, 0, 351068, 106659, 1017, 16384⟩ := by
  decide +kernel

theorem context_13_106659_351068 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106659 ⟨351068, by decide⟩ :=
  accepted_of_selected 13 106659 ⟨351068, by decide⟩ ⟨13, 2, 0, 351068, 106659, 1017, 16384⟩
    (by decide) selected_cut_13332

theorem unmarked_context_12_26664_351069 : frontier 9 ⟨351069, by decide⟩
    (prefixCache 12 26664) (prefixPartial 12 26664) = false := by
  decide +kernel

theorem node_context_12_26664_351069 : EJMOriginalGlobalDAGData.nodes 9 ⟨351069, by decide⟩ =
    .split (coordinate 12) (![⟨350986, by decide⟩,⟨351038, by decide⟩,⟨351057, by decide⟩,⟨351068, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26664_351069 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26664 ⟨351069, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26664
    ⟨351069, by decide⟩ (by decide) (![⟨350986, by decide⟩,⟨351038, by decide⟩,⟨351057, by decide⟩,⟨351068, by decide⟩]) unmarked_context_12_26664_351069 node_context_12_26664_351069
  intro a
  fin_cases a
  · exact context_13_106656_350986
  · exact context_13_106657_351038
  · exact context_13_106658_351057
  · exact context_13_106659_351068

theorem selected_cut_13333 : selected 8 ⟨351083, by decide⟩
    (prefixPartial 13 106660) = some ⟨13, 2, 0, 351083, 106660, 1049, 16384⟩ := by
  decide +kernel

theorem context_13_106660_351083 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106660 ⟨351083, by decide⟩ :=
  accepted_of_selected 13 106660 ⟨351083, by decide⟩ ⟨13, 2, 0, 351083, 106660, 1049, 16384⟩
    (by decide) selected_cut_13333

theorem selected_cut_13334 : selected 8 ⟨351118, by decide⟩
    (prefixPartial 13 106661) = some ⟨13, 2, 0, 351118, 106661, 2769, 16384⟩ := by
  decide +kernel

theorem context_13_106661_351118 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106661 ⟨351118, by decide⟩ :=
  accepted_of_selected 13 106661 ⟨351118, by decide⟩ ⟨13, 2, 0, 351118, 106661, 2769, 16384⟩
    (by decide) selected_cut_13334

theorem selected_cut_13335 : selected 8 ⟨351137, by decide⟩
    (prefixPartial 13 106662) = some ⟨13, 2, 0, 351137, 106662, 1673, 16384⟩ := by
  decide +kernel

theorem context_13_106662_351137 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106662 ⟨351137, by decide⟩ :=
  accepted_of_selected 13 106662 ⟨351137, by decide⟩ ⟨13, 2, 0, 351137, 106662, 1673, 16384⟩
    (by decide) selected_cut_13335

theorem selected_cut_13336 : selected 8 ⟨351145, by decide⟩
    (prefixPartial 13 106663) = some ⟨13, 2, 0, 351145, 106663, 1017, 16384⟩ := by
  decide +kernel

theorem context_13_106663_351145 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106663 ⟨351145, by decide⟩ :=
  accepted_of_selected 13 106663 ⟨351145, by decide⟩ ⟨13, 2, 0, 351145, 106663, 1017, 16384⟩
    (by decide) selected_cut_13336

theorem unmarked_context_12_26665_351146 : frontier 9 ⟨351146, by decide⟩
    (prefixCache 12 26665) (prefixPartial 12 26665) = false := by
  decide +kernel

theorem node_context_12_26665_351146 : EJMOriginalGlobalDAGData.nodes 9 ⟨351146, by decide⟩ =
    .split (coordinate 12) (![⟨351083, by decide⟩,⟨351118, by decide⟩,⟨351137, by decide⟩,⟨351145, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26665_351146 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26665 ⟨351146, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26665
    ⟨351146, by decide⟩ (by decide) (![⟨351083, by decide⟩,⟨351118, by decide⟩,⟨351137, by decide⟩,⟨351145, by decide⟩]) unmarked_context_12_26665_351146 node_context_12_26665_351146
  intro a
  fin_cases a
  · exact context_13_106660_351083
  · exact context_13_106661_351118
  · exact context_13_106662_351137
  · exact context_13_106663_351145

theorem selected_cut_13337 : selected 9 ⟨101803, by decide⟩
    (prefixPartial 12 26666) = some ⟨12, 1, 0, 101803, 26666, 1, 65536⟩ := by
  decide +kernel

theorem context_12_26666_101803 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26666 ⟨101803, by decide⟩ :=
  accepted_of_selected 12 26666 ⟨101803, by decide⟩ ⟨12, 1, 0, 101803, 26666, 1, 65536⟩
    (by decide) selected_cut_13337

theorem selected_cut_13338 : selected 8 ⟨351157, by decide⟩
    (prefixPartial 13 106668) = some ⟨13, 2, 0, 351157, 106668, 1037, 16384⟩ := by
  decide +kernel

theorem context_13_106668_351157 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106668 ⟨351157, by decide⟩ :=
  accepted_of_selected 13 106668 ⟨351157, by decide⟩ ⟨13, 2, 0, 351157, 106668, 1037, 16384⟩
    (by decide) selected_cut_13338

theorem selected_cut_13339 : selected 8 ⟨351205, by decide⟩
    (prefixPartial 13 106669) = some ⟨13, 2, 0, 351205, 106669, 3229, 16384⟩ := by
  decide +kernel

theorem context_13_106669_351205 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106669 ⟨351205, by decide⟩ :=
  accepted_of_selected 13 106669 ⟨351205, by decide⟩ ⟨13, 2, 0, 351205, 106669, 3229, 16384⟩
    (by decide) selected_cut_13339

theorem selected_cut_13340 : selected 8 ⟨351224, by decide⟩
    (prefixPartial 13 106670) = some ⟨13, 2, 0, 351224, 106670, 1581, 16384⟩ := by
  decide +kernel

theorem context_13_106670_351224 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106670 ⟨351224, by decide⟩ :=
  accepted_of_selected 13 106670 ⟨351224, by decide⟩ ⟨13, 2, 0, 351224, 106670, 1581, 16384⟩
    (by decide) selected_cut_13340

theorem selected_cut_13341 : selected 8 ⟨351235, by decide⟩
    (prefixPartial 13 106671) = some ⟨13, 2, 0, 351235, 106671, 1037, 16384⟩ := by
  decide +kernel

theorem context_13_106671_351235 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106671 ⟨351235, by decide⟩ :=
  accepted_of_selected 13 106671 ⟨351235, by decide⟩ ⟨13, 2, 0, 351235, 106671, 1037, 16384⟩
    (by decide) selected_cut_13341

theorem unmarked_context_12_26667_351236 : frontier 9 ⟨351236, by decide⟩
    (prefixCache 12 26667) (prefixPartial 12 26667) = false := by
  decide +kernel

theorem node_context_12_26667_351236 : EJMOriginalGlobalDAGData.nodes 9 ⟨351236, by decide⟩ =
    .split (coordinate 12) (![⟨351157, by decide⟩,⟨351205, by decide⟩,⟨351224, by decide⟩,⟨351235, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26667_351236 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26667 ⟨351236, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26667
    ⟨351236, by decide⟩ (by decide) (![⟨351157, by decide⟩,⟨351205, by decide⟩,⟨351224, by decide⟩,⟨351235, by decide⟩]) unmarked_context_12_26667_351236 node_context_12_26667_351236
  intro a
  fin_cases a
  · exact context_13_106668_351157
  · exact context_13_106669_351205
  · exact context_13_106670_351224
  · exact context_13_106671_351235

theorem unmarked_context_11_6666_351237 : frontier 10 ⟨351237, by decide⟩
    (prefixCache 11 6666) (prefixPartial 11 6666) = false := by
  decide +kernel

theorem node_context_11_6666_351237 : EJMOriginalGlobalDAGData.nodes 10 ⟨351237, by decide⟩ =
    .split (coordinate 11) (![⟨351069, by decide⟩,⟨351146, by decide⟩,⟨101803, by decide⟩,⟨351236, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6666_351237 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6666 ⟨351237, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6666
    ⟨351237, by decide⟩ (by decide) (![⟨351069, by decide⟩,⟨351146, by decide⟩,⟨101803, by decide⟩,⟨351236, by decide⟩]) unmarked_context_11_6666_351237 node_context_11_6666_351237
  intro a
  fin_cases a
  · exact context_12_26664_351069
  · exact context_12_26665_351146
  · exact context_12_26666_101803
  · exact context_12_26667_351236

theorem selected_cut_13342 : selected 8 ⟨351244, by decide⟩
    (prefixPartial 13 106672) = some ⟨13, 2, 0, 351244, 106672, 533, 16384⟩ := by
  decide +kernel

theorem context_13_106672_351244 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106672 ⟨351244, by decide⟩ :=
  accepted_of_selected 13 106672 ⟨351244, by decide⟩ ⟨13, 2, 0, 351244, 106672, 533, 16384⟩
    (by decide) selected_cut_13342

theorem selected_cut_13343 : selected 8 ⟨351267, by decide⟩
    (prefixPartial 13 106673) = some ⟨13, 2, 0, 351267, 106673, 1993, 16384⟩ := by
  decide +kernel

theorem context_13_106673_351267 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106673 ⟨351267, by decide⟩ :=
  accepted_of_selected 13 106673 ⟨351267, by decide⟩ ⟨13, 2, 0, 351267, 106673, 1993, 16384⟩
    (by decide) selected_cut_13343

theorem selected_cut_13344 : selected 8 ⟨351282, by decide⟩
    (prefixPartial 13 106674) = some ⟨13, 2, 0, 351282, 106674, 1137, 16384⟩ := by
  decide +kernel

theorem context_13_106674_351282 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106674 ⟨351282, by decide⟩ :=
  accepted_of_selected 13 106674 ⟨351282, by decide⟩ ⟨13, 2, 0, 351282, 106674, 1137, 16384⟩
    (by decide) selected_cut_13344

theorem selected_cut_13345 : selected 8 ⟨351286, by decide⟩
    (prefixPartial 13 106675) = some ⟨13, 2, 0, 351286, 106675, 725, 16384⟩ := by
  decide +kernel

theorem context_13_106675_351286 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106675 ⟨351286, by decide⟩ :=
  accepted_of_selected 13 106675 ⟨351286, by decide⟩ ⟨13, 2, 0, 351286, 106675, 725, 16384⟩
    (by decide) selected_cut_13345

theorem unmarked_context_12_26668_351287 : frontier 9 ⟨351287, by decide⟩
    (prefixCache 12 26668) (prefixPartial 12 26668) = false := by
  decide +kernel

theorem node_context_12_26668_351287 : EJMOriginalGlobalDAGData.nodes 9 ⟨351287, by decide⟩ =
    .split (coordinate 12) (![⟨351244, by decide⟩,⟨351267, by decide⟩,⟨351282, by decide⟩,⟨351286, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26668_351287 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26668 ⟨351287, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26668
    ⟨351287, by decide⟩ (by decide) (![⟨351244, by decide⟩,⟨351267, by decide⟩,⟨351282, by decide⟩,⟨351286, by decide⟩]) unmarked_context_12_26668_351287 node_context_12_26668_351287
  intro a
  fin_cases a
  · exact context_13_106672_351244
  · exact context_13_106673_351267
  · exact context_13_106674_351282
  · exact context_13_106675_351286

theorem selected_cut_13346 : selected 8 ⟨351298, by decide⟩
    (prefixPartial 13 106676) = some ⟨13, 2, 0, 351298, 106676, 641, 16384⟩ := by
  decide +kernel

theorem context_13_106676_351298 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106676 ⟨351298, by decide⟩ :=
  accepted_of_selected 13 106676 ⟨351298, by decide⟩ ⟨13, 2, 0, 351298, 106676, 641, 16384⟩
    (by decide) selected_cut_13346

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
