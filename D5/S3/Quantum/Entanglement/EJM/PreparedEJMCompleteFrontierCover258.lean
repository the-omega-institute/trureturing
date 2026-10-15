/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover257
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem unmarked_context_12_77379_625529 : frontier 9 ⟨625529, by decide⟩
    (prefixCache 12 77379) (prefixPartial 12 77379) = false := by
  decide +kernel

theorem node_context_12_77379_625529 : EJMOriginalGlobalDAGData.nodes 9 ⟨625529, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨625491, by decide⟩,⟨625517, by decide⟩,⟨625528, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77379_625529 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77379 ⟨625529, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77379
    ⟨625529, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨625491, by decide⟩,⟨625517, by decide⟩,⟨625528, by decide⟩]) unmarked_context_12_77379_625529 node_context_12_77379_625529
  intro a
  fin_cases a
  · exact context_13_309516_3444
  · exact context_13_309517_625491
  · exact context_13_309518_625517
  · exact context_13_309519_625528

theorem unmarked_context_11_19344_625530 : frontier 10 ⟨625530, by decide⟩
    (prefixCache 11 19344) (prefixPartial 11 19344) = false := by
  decide +kernel

theorem node_context_11_19344_625530 : EJMOriginalGlobalDAGData.nodes 10 ⟨625530, by decide⟩ =
    .split (coordinate 11) (![⟨625330, by decide⟩,⟨625385, by decide⟩,⟨625455, by decide⟩,⟨625529, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19344_625530 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19344 ⟨625530, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19344
    ⟨625530, by decide⟩ (by decide) (![⟨625330, by decide⟩,⟨625385, by decide⟩,⟨625455, by decide⟩,⟨625529, by decide⟩]) unmarked_context_11_19344_625530 node_context_11_19344_625530
  intro a
  fin_cases a
  · exact context_12_77376_625330
  · exact context_12_77377_625385
  · exact context_12_77378_625455
  · exact context_12_77379_625529

theorem selected_cut_24772 : selected 9 ⟨625589, by decide⟩
    (prefixPartial 12 77380) = some ⟨12, 2, 0, 625589, 77380, 3981, 65536⟩ := by
  decide +kernel

theorem context_12_77380_625589 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77380 ⟨625589, by decide⟩ :=
  accepted_of_selected 12 77380 ⟨625589, by decide⟩ ⟨12, 2, 0, 625589, 77380, 3981, 65536⟩
    (by decide) selected_cut_24772

theorem selected_cut_24773 : selected 9 ⟨625641, by decide⟩
    (prefixPartial 12 77381) = some ⟨12, 2, 0, 625641, 77381, 3913, 65536⟩ := by
  decide +kernel

theorem context_12_77381_625641 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77381 ⟨625641, by decide⟩ :=
  accepted_of_selected 12 77381 ⟨625641, by decide⟩ ⟨12, 2, 0, 625641, 77381, 3913, 65536⟩
    (by decide) selected_cut_24773

theorem selected_cut_24774 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 309528) = some ⟨13, 1, 0, 3444, 309528, 1, 16384⟩ := by
  decide +kernel

theorem context_13_309528_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309528 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 309528 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 309528, 1, 16384⟩
    (by decide) selected_cut_24774

theorem selected_cut_24775 : selected 8 ⟨625669, by decide⟩
    (prefixPartial 13 309529) = some ⟨13, 2, 0, 625669, 309529, 1993, 16384⟩ := by
  decide +kernel

theorem context_13_309529_625669 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309529 ⟨625669, by decide⟩ :=
  accepted_of_selected 13 309529 ⟨625669, by decide⟩ ⟨13, 2, 0, 625669, 309529, 1993, 16384⟩
    (by decide) selected_cut_24775

theorem selected_cut_24776 : selected 8 ⟨625692, by decide⟩
    (prefixPartial 13 309530) = some ⟨13, 2, 0, 625692, 309530, 1593, 16384⟩ := by
  decide +kernel

theorem context_13_309530_625692 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309530 ⟨625692, by decide⟩ :=
  accepted_of_selected 13 309530 ⟨625692, by decide⟩ ⟨13, 2, 0, 625692, 309530, 1593, 16384⟩
    (by decide) selected_cut_24776

theorem selected_cut_24777 : selected 8 ⟨625702, by decide⟩
    (prefixPartial 13 309531) = some ⟨13, 2, 0, 625702, 309531, 861, 16384⟩ := by
  decide +kernel

theorem context_13_309531_625702 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309531 ⟨625702, by decide⟩ :=
  accepted_of_selected 13 309531 ⟨625702, by decide⟩ ⟨13, 2, 0, 625702, 309531, 861, 16384⟩
    (by decide) selected_cut_24777

theorem unmarked_context_12_77382_625703 : frontier 9 ⟨625703, by decide⟩
    (prefixCache 12 77382) (prefixPartial 12 77382) = false := by
  decide +kernel

theorem node_context_12_77382_625703 : EJMOriginalGlobalDAGData.nodes 9 ⟨625703, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨625669, by decide⟩,⟨625692, by decide⟩,⟨625702, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77382_625703 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77382 ⟨625703, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77382
    ⟨625703, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨625669, by decide⟩,⟨625692, by decide⟩,⟨625702, by decide⟩]) unmarked_context_12_77382_625703 node_context_12_77382_625703
  intro a
  fin_cases a
  · exact context_13_309528_3444
  · exact context_13_309529_625669
  · exact context_13_309530_625692
  · exact context_13_309531_625702

theorem selected_cut_24778 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 309532) = some ⟨13, 1, 0, 3444, 309532, 1, 16384⟩ := by
  decide +kernel

theorem context_13_309532_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309532 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 309532 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 309532, 1, 16384⟩
    (by decide) selected_cut_24778

theorem selected_cut_24779 : selected 8 ⟨625738, by decide⟩
    (prefixPartial 13 309533) = some ⟨13, 2, 0, 625738, 309533, 2233, 16384⟩ := by
  decide +kernel

theorem context_13_309533_625738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309533 ⟨625738, by decide⟩ :=
  accepted_of_selected 13 309533 ⟨625738, by decide⟩ ⟨13, 2, 0, 625738, 309533, 2233, 16384⟩
    (by decide) selected_cut_24779

theorem selected_cut_24780 : selected 8 ⟨625762, by decide⟩
    (prefixPartial 13 309534) = some ⟨13, 2, 0, 625762, 309534, 1693, 16384⟩ := by
  decide +kernel

theorem context_13_309534_625762 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309534 ⟨625762, by decide⟩ :=
  accepted_of_selected 13 309534 ⟨625762, by decide⟩ ⟨13, 2, 0, 625762, 309534, 1693, 16384⟩
    (by decide) selected_cut_24780

theorem selected_cut_24781 : selected 8 ⟨625772, by decide⟩
    (prefixPartial 13 309535) = some ⟨13, 2, 0, 625772, 309535, 881, 16384⟩ := by
  decide +kernel

theorem context_13_309535_625772 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309535 ⟨625772, by decide⟩ :=
  accepted_of_selected 13 309535 ⟨625772, by decide⟩ ⟨13, 2, 0, 625772, 309535, 881, 16384⟩
    (by decide) selected_cut_24781

theorem unmarked_context_12_77383_625773 : frontier 9 ⟨625773, by decide⟩
    (prefixCache 12 77383) (prefixPartial 12 77383) = false := by
  decide +kernel

theorem node_context_12_77383_625773 : EJMOriginalGlobalDAGData.nodes 9 ⟨625773, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨625738, by decide⟩,⟨625762, by decide⟩,⟨625772, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77383_625773 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77383 ⟨625773, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77383
    ⟨625773, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨625738, by decide⟩,⟨625762, by decide⟩,⟨625772, by decide⟩]) unmarked_context_12_77383_625773 node_context_12_77383_625773
  intro a
  fin_cases a
  · exact context_13_309532_3444
  · exact context_13_309533_625738
  · exact context_13_309534_625762
  · exact context_13_309535_625772

theorem unmarked_context_11_19345_625774 : frontier 10 ⟨625774, by decide⟩
    (prefixCache 11 19345) (prefixPartial 11 19345) = false := by
  decide +kernel

theorem node_context_11_19345_625774 : EJMOriginalGlobalDAGData.nodes 10 ⟨625774, by decide⟩ =
    .split (coordinate 11) (![⟨625589, by decide⟩,⟨625641, by decide⟩,⟨625703, by decide⟩,⟨625773, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19345_625774 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19345 ⟨625774, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19345
    ⟨625774, by decide⟩ (by decide) (![⟨625589, by decide⟩,⟨625641, by decide⟩,⟨625703, by decide⟩,⟨625773, by decide⟩]) unmarked_context_11_19345_625774 node_context_11_19345_625774
  intro a
  fin_cases a
  · exact context_12_77380_625589
  · exact context_12_77381_625641
  · exact context_12_77382_625703
  · exact context_12_77383_625773

theorem selected_cut_24782 : selected 9 ⟨625829, by decide⟩
    (prefixPartial 12 77384) = some ⟨12, 2, 0, 625829, 77384, 3821, 65536⟩ := by
  decide +kernel

theorem context_12_77384_625829 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77384 ⟨625829, by decide⟩ :=
  accepted_of_selected 12 77384 ⟨625829, by decide⟩ ⟨12, 2, 0, 625829, 77384, 3821, 65536⟩
    (by decide) selected_cut_24782

theorem selected_cut_24783 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 309540) = some ⟨13, 1, 0, 3444, 309540, 1, 16384⟩ := by
  decide +kernel

theorem context_13_309540_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309540 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 309540 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 309540, 1, 16384⟩
    (by decide) selected_cut_24783

theorem selected_cut_24784 : selected 8 ⟨625858, by decide⟩
    (prefixPartial 13 309541) = some ⟨13, 2, 0, 625858, 309541, 1841, 16384⟩ := by
  decide +kernel

theorem context_13_309541_625858 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309541 ⟨625858, by decide⟩ :=
  accepted_of_selected 13 309541 ⟨625858, by decide⟩ ⟨13, 2, 0, 625858, 309541, 1841, 16384⟩
    (by decide) selected_cut_24784

theorem selected_cut_24785 : selected 8 ⟨625877, by decide⟩
    (prefixPartial 13 309542) = some ⟨13, 2, 0, 625877, 309542, 1477, 16384⟩ := by
  decide +kernel

theorem context_13_309542_625877 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309542 ⟨625877, by decide⟩ :=
  accepted_of_selected 13 309542 ⟨625877, by decide⟩ ⟨13, 2, 0, 625877, 309542, 1477, 16384⟩
    (by decide) selected_cut_24785

theorem selected_cut_24786 : selected 8 ⟨625885, by decide⟩
    (prefixPartial 13 309543) = some ⟨13, 2, 0, 625885, 309543, 789, 16384⟩ := by
  decide +kernel

theorem context_13_309543_625885 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309543 ⟨625885, by decide⟩ :=
  accepted_of_selected 13 309543 ⟨625885, by decide⟩ ⟨13, 2, 0, 625885, 309543, 789, 16384⟩
    (by decide) selected_cut_24786

theorem unmarked_context_12_77385_625886 : frontier 9 ⟨625886, by decide⟩
    (prefixCache 12 77385) (prefixPartial 12 77385) = false := by
  decide +kernel

theorem node_context_12_77385_625886 : EJMOriginalGlobalDAGData.nodes 9 ⟨625886, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨625858, by decide⟩,⟨625877, by decide⟩,⟨625885, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77385_625886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77385 ⟨625886, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77385
    ⟨625886, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨625858, by decide⟩,⟨625877, by decide⟩,⟨625885, by decide⟩]) unmarked_context_12_77385_625886 node_context_12_77385_625886
  intro a
  fin_cases a
  · exact context_13_309540_3444
  · exact context_13_309541_625858
  · exact context_13_309542_625877
  · exact context_13_309543_625885

theorem selected_cut_24787 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 309544) = some ⟨13, 1, 0, 3444, 309544, 1, 16384⟩ := by
  decide +kernel

theorem context_13_309544_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309544 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 309544 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 309544, 1, 16384⟩
    (by decide) selected_cut_24787

theorem selected_cut_24788 : selected 8 ⟨625940, by decide⟩
    (prefixPartial 13 309545) = some ⟨13, 2, 0, 625940, 309545, 3101, 16384⟩ := by
  decide +kernel

theorem context_13_309545_625940 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309545 ⟨625940, by decide⟩ :=
  accepted_of_selected 13 309545 ⟨625940, by decide⟩ ⟨13, 2, 0, 625940, 309545, 3101, 16384⟩
    (by decide) selected_cut_24788

theorem selected_cut_24789 : selected 8 ⟨625990, by decide⟩
    (prefixPartial 13 309546) = some ⟨13, 2, 0, 625990, 309546, 2497, 16384⟩ := by
  decide +kernel

theorem context_13_309546_625990 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309546 ⟨625990, by decide⟩ :=
  accepted_of_selected 13 309546 ⟨625990, by decide⟩ ⟨13, 2, 0, 625990, 309546, 2497, 16384⟩
    (by decide) selected_cut_24789

theorem selected_cut_24790 : selected 8 ⟨626003, by decide⟩
    (prefixPartial 13 309547) = some ⟨13, 2, 0, 626003, 309547, 1205, 16384⟩ := by
  decide +kernel

theorem context_13_309547_626003 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309547 ⟨626003, by decide⟩ :=
  accepted_of_selected 13 309547 ⟨626003, by decide⟩ ⟨13, 2, 0, 626003, 309547, 1205, 16384⟩
    (by decide) selected_cut_24790

theorem unmarked_context_12_77386_626004 : frontier 9 ⟨626004, by decide⟩
    (prefixCache 12 77386) (prefixPartial 12 77386) = false := by
  decide +kernel

theorem node_context_12_77386_626004 : EJMOriginalGlobalDAGData.nodes 9 ⟨626004, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨625940, by decide⟩,⟨625990, by decide⟩,⟨626003, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77386_626004 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77386 ⟨626004, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77386
    ⟨626004, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨625940, by decide⟩,⟨625990, by decide⟩,⟨626003, by decide⟩]) unmarked_context_12_77386_626004 node_context_12_77386_626004
  intro a
  fin_cases a
  · exact context_13_309544_3444
  · exact context_13_309545_625940
  · exact context_13_309546_625990
  · exact context_13_309547_626003

theorem selected_cut_24791 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 309548) = some ⟨13, 1, 0, 3444, 309548, 1, 16384⟩ := by
  decide +kernel

theorem context_13_309548_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309548 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 309548 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 309548, 1, 16384⟩
    (by decide) selected_cut_24791

theorem selected_cut_24792 : selected 8 ⟨626033, by decide⟩
    (prefixPartial 13 309549) = some ⟨13, 2, 0, 626033, 309549, 2169, 16384⟩ := by
  decide +kernel

theorem context_13_309549_626033 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309549 ⟨626033, by decide⟩ :=
  accepted_of_selected 13 309549 ⟨626033, by decide⟩ ⟨13, 2, 0, 626033, 309549, 2169, 16384⟩
    (by decide) selected_cut_24792

theorem selected_cut_24793 : selected 8 ⟨626052, by decide⟩
    (prefixPartial 13 309550) = some ⟨13, 2, 0, 626052, 309550, 1489, 16384⟩ := by
  decide +kernel

theorem context_13_309550_626052 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309550 ⟨626052, by decide⟩ :=
  accepted_of_selected 13 309550 ⟨626052, by decide⟩ ⟨13, 2, 0, 626052, 309550, 1489, 16384⟩
    (by decide) selected_cut_24793

theorem selected_cut_24794 : selected 8 ⟨626065, by decide⟩
    (prefixPartial 13 309551) = some ⟨13, 2, 0, 626065, 309551, 901, 16384⟩ := by
  decide +kernel

theorem context_13_309551_626065 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309551 ⟨626065, by decide⟩ :=
  accepted_of_selected 13 309551 ⟨626065, by decide⟩ ⟨13, 2, 0, 626065, 309551, 901, 16384⟩
    (by decide) selected_cut_24794

theorem unmarked_context_12_77387_626066 : frontier 9 ⟨626066, by decide⟩
    (prefixCache 12 77387) (prefixPartial 12 77387) = false := by
  decide +kernel

theorem node_context_12_77387_626066 : EJMOriginalGlobalDAGData.nodes 9 ⟨626066, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨626033, by decide⟩,⟨626052, by decide⟩,⟨626065, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77387_626066 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77387 ⟨626066, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77387
    ⟨626066, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨626033, by decide⟩,⟨626052, by decide⟩,⟨626065, by decide⟩]) unmarked_context_12_77387_626066 node_context_12_77387_626066
  intro a
  fin_cases a
  · exact context_13_309548_3444
  · exact context_13_309549_626033
  · exact context_13_309550_626052
  · exact context_13_309551_626065

theorem unmarked_context_11_19346_626067 : frontier 10 ⟨626067, by decide⟩
    (prefixCache 11 19346) (prefixPartial 11 19346) = false := by
  decide +kernel

theorem node_context_11_19346_626067 : EJMOriginalGlobalDAGData.nodes 10 ⟨626067, by decide⟩ =
    .split (coordinate 11) (![⟨625829, by decide⟩,⟨625886, by decide⟩,⟨626004, by decide⟩,⟨626066, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19346_626067 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19346 ⟨626067, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19346
    ⟨626067, by decide⟩ (by decide) (![⟨625829, by decide⟩,⟨625886, by decide⟩,⟨626004, by decide⟩,⟨626066, by decide⟩]) unmarked_context_11_19346_626067 node_context_11_19346_626067
  intro a
  fin_cases a
  · exact context_12_77384_625829
  · exact context_12_77385_625886
  · exact context_12_77386_626004
  · exact context_12_77387_626066

theorem selected_cut_24795 : selected 9 ⟨626113, by decide⟩
    (prefixPartial 12 77388) = some ⟨12, 2, 0, 626113, 77388, 3501, 65536⟩ := by
  decide +kernel

theorem context_12_77388_626113 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77388 ⟨626113, by decide⟩ :=
  accepted_of_selected 12 77388 ⟨626113, by decide⟩ ⟨12, 2, 0, 626113, 77388, 3501, 65536⟩
    (by decide) selected_cut_24795

theorem selected_cut_24796 : selected 9 ⟨626162, by decide⟩
    (prefixPartial 12 77389) = some ⟨12, 2, 0, 626162, 77389, 3657, 65536⟩ := by
  decide +kernel

theorem context_12_77389_626162 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77389 ⟨626162, by decide⟩ :=
  accepted_of_selected 12 77389 ⟨626162, by decide⟩ ⟨12, 2, 0, 626162, 77389, 3657, 65536⟩
    (by decide) selected_cut_24796

theorem selected_cut_24797 : selected 9 ⟨626223, by decide⟩
    (prefixPartial 12 77390) = some ⟨12, 2, 0, 626223, 77390, 4021, 65536⟩ := by
  decide +kernel

theorem context_12_77390_626223 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77390 ⟨626223, by decide⟩ :=
  accepted_of_selected 12 77390 ⟨626223, by decide⟩ ⟨12, 2, 0, 626223, 77390, 4021, 65536⟩
    (by decide) selected_cut_24797

theorem selected_cut_24798 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 309564) = some ⟨13, 1, 0, 3444, 309564, 1, 16384⟩ := by
  decide +kernel

theorem context_13_309564_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309564 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 309564 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 309564, 1, 16384⟩
    (by decide) selected_cut_24798

theorem selected_cut_24799 : selected 8 ⟨626247, by decide⟩
    (prefixPartial 13 309565) = some ⟨13, 2, 0, 626247, 309565, 1873, 16384⟩ := by
  decide +kernel

theorem context_13_309565_626247 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309565 ⟨626247, by decide⟩ :=
  accepted_of_selected 13 309565 ⟨626247, by decide⟩ ⟨13, 2, 0, 626247, 309565, 1873, 16384⟩
    (by decide) selected_cut_24799

theorem selected_cut_24800 : selected 8 ⟨626266, by decide⟩
    (prefixPartial 13 309566) = some ⟨13, 2, 0, 626266, 309566, 1549, 16384⟩ := by
  decide +kernel

theorem context_13_309566_626266 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309566 ⟨626266, by decide⟩ :=
  accepted_of_selected 13 309566 ⟨626266, by decide⟩ ⟨13, 2, 0, 626266, 309566, 1549, 16384⟩
    (by decide) selected_cut_24800

theorem selected_cut_24801 : selected 8 ⟨626277, by decide⟩
    (prefixPartial 13 309567) = some ⟨13, 2, 0, 626277, 309567, 885, 16384⟩ := by
  decide +kernel

theorem context_13_309567_626277 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309567 ⟨626277, by decide⟩ :=
  accepted_of_selected 13 309567 ⟨626277, by decide⟩ ⟨13, 2, 0, 626277, 309567, 885, 16384⟩
    (by decide) selected_cut_24801

theorem unmarked_context_12_77391_626278 : frontier 9 ⟨626278, by decide⟩
    (prefixCache 12 77391) (prefixPartial 12 77391) = false := by
  decide +kernel

theorem node_context_12_77391_626278 : EJMOriginalGlobalDAGData.nodes 9 ⟨626278, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨626247, by decide⟩,⟨626266, by decide⟩,⟨626277, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77391_626278 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77391 ⟨626278, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77391
    ⟨626278, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨626247, by decide⟩,⟨626266, by decide⟩,⟨626277, by decide⟩]) unmarked_context_12_77391_626278 node_context_12_77391_626278
  intro a
  fin_cases a
  · exact context_13_309564_3444
  · exact context_13_309565_626247
  · exact context_13_309566_626266
  · exact context_13_309567_626277

theorem unmarked_context_11_19347_626279 : frontier 10 ⟨626279, by decide⟩
    (prefixCache 11 19347) (prefixPartial 11 19347) = false := by
  decide +kernel

theorem node_context_11_19347_626279 : EJMOriginalGlobalDAGData.nodes 10 ⟨626279, by decide⟩ =
    .split (coordinate 11) (![⟨626113, by decide⟩,⟨626162, by decide⟩,⟨626223, by decide⟩,⟨626278, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19347_626279 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19347 ⟨626279, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19347
    ⟨626279, by decide⟩ (by decide) (![⟨626113, by decide⟩,⟨626162, by decide⟩,⟨626223, by decide⟩,⟨626278, by decide⟩]) unmarked_context_11_19347_626279 node_context_11_19347_626279
  intro a
  fin_cases a
  · exact context_12_77388_626113
  · exact context_12_77389_626162
  · exact context_12_77390_626223
  · exact context_12_77391_626278

theorem unmarked_context_10_4836_626280 : frontier 11 ⟨626280, by decide⟩
    (prefixCache 10 4836) (prefixPartial 10 4836) = false := by
  decide +kernel

theorem node_context_10_4836_626280 : EJMOriginalGlobalDAGData.nodes 11 ⟨626280, by decide⟩ =
    .split (coordinate 10) (![⟨625530, by decide⟩,⟨625774, by decide⟩,⟨626067, by decide⟩,⟨626279, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4836_626280 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4836 ⟨626280, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4836
    ⟨626280, by decide⟩ (by decide) (![⟨625530, by decide⟩,⟨625774, by decide⟩,⟨626067, by decide⟩,⟨626279, by decide⟩]) unmarked_context_10_4836_626280 node_context_10_4836_626280
  intro a
  fin_cases a
  · exact context_11_19344_625530
  · exact context_11_19345_625774
  · exact context_11_19346_626067
  · exact context_11_19347_626279

theorem selected_cut_24802 : selected 9 ⟨626341, by decide⟩
    (prefixPartial 12 77392) = some ⟨12, 2, 0, 626341, 77392, 3881, 65536⟩ := by
  decide +kernel

theorem context_12_77392_626341 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77392 ⟨626341, by decide⟩ :=
  accepted_of_selected 12 77392 ⟨626341, by decide⟩ ⟨12, 2, 0, 626341, 77392, 3881, 65536⟩
    (by decide) selected_cut_24802

theorem selected_cut_24803 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 309572) = some ⟨13, 1, 0, 3444, 309572, 1, 16384⟩ := by
  decide +kernel

theorem context_13_309572_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309572 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 309572 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 309572, 1, 16384⟩
    (by decide) selected_cut_24803

theorem selected_cut_24804 : selected 8 ⟨626370, by decide⟩
    (prefixPartial 13 309573) = some ⟨13, 2, 0, 626370, 309573, 1757, 16384⟩ := by
  decide +kernel

theorem context_13_309573_626370 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309573 ⟨626370, by decide⟩ :=
  accepted_of_selected 13 309573 ⟨626370, by decide⟩ ⟨13, 2, 0, 626370, 309573, 1757, 16384⟩
    (by decide) selected_cut_24804

theorem selected_cut_24805 : selected 8 ⟨626394, by decide⟩
    (prefixPartial 13 309574) = some ⟨13, 2, 0, 626394, 309574, 1701, 16384⟩ := by
  decide +kernel

theorem context_13_309574_626394 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309574 ⟨626394, by decide⟩ :=
  accepted_of_selected 13 309574 ⟨626394, by decide⟩ ⟨13, 2, 0, 626394, 309574, 1701, 16384⟩
    (by decide) selected_cut_24805

theorem selected_cut_24806 : selected 8 ⟨626403, by decide⟩
    (prefixPartial 13 309575) = some ⟨13, 2, 0, 626403, 309575, 785, 16384⟩ := by
  decide +kernel

theorem context_13_309575_626403 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309575 ⟨626403, by decide⟩ :=
  accepted_of_selected 13 309575 ⟨626403, by decide⟩ ⟨13, 2, 0, 626403, 309575, 785, 16384⟩
    (by decide) selected_cut_24806

theorem unmarked_context_12_77393_626404 : frontier 9 ⟨626404, by decide⟩
    (prefixCache 12 77393) (prefixPartial 12 77393) = false := by
  decide +kernel

theorem node_context_12_77393_626404 : EJMOriginalGlobalDAGData.nodes 9 ⟨626404, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨626370, by decide⟩,⟨626394, by decide⟩,⟨626403, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77393_626404 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77393 ⟨626404, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77393
    ⟨626404, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨626370, by decide⟩,⟨626394, by decide⟩,⟨626403, by decide⟩]) unmarked_context_12_77393_626404 node_context_12_77393_626404
  intro a
  fin_cases a
  · exact context_13_309572_3444
  · exact context_13_309573_626370
  · exact context_13_309574_626394
  · exact context_13_309575_626403

theorem selected_cut_24807 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 309576) = some ⟨13, 1, 0, 3444, 309576, 1, 16384⟩ := by
  decide +kernel

theorem context_13_309576_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309576 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 309576 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 309576, 1, 16384⟩
    (by decide) selected_cut_24807

theorem selected_cut_24808 : selected 8 ⟨626426, by decide⟩
    (prefixPartial 13 309577) = some ⟨13, 2, 0, 626426, 309577, 1853, 16384⟩ := by
  decide +kernel

theorem context_13_309577_626426 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309577 ⟨626426, by decide⟩ :=
  accepted_of_selected 13 309577 ⟨626426, by decide⟩ ⟨13, 2, 0, 626426, 309577, 1853, 16384⟩
    (by decide) selected_cut_24808

theorem selected_cut_24809 : selected 8 ⟨626450, by decide⟩
    (prefixPartial 13 309578) = some ⟨13, 2, 0, 626450, 309578, 1513, 16384⟩ := by
  decide +kernel

theorem context_13_309578_626450 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309578 ⟨626450, by decide⟩ :=
  accepted_of_selected 13 309578 ⟨626450, by decide⟩ ⟨13, 2, 0, 626450, 309578, 1513, 16384⟩
    (by decide) selected_cut_24809

theorem selected_cut_24810 : selected 8 ⟨626461, by decide⟩
    (prefixPartial 13 309579) = some ⟨13, 2, 0, 626461, 309579, 929, 16384⟩ := by
  decide +kernel

theorem context_13_309579_626461 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309579 ⟨626461, by decide⟩ :=
  accepted_of_selected 13 309579 ⟨626461, by decide⟩ ⟨13, 2, 0, 626461, 309579, 929, 16384⟩
    (by decide) selected_cut_24810

theorem unmarked_context_12_77394_626462 : frontier 9 ⟨626462, by decide⟩
    (prefixCache 12 77394) (prefixPartial 12 77394) = false := by
  decide +kernel

theorem node_context_12_77394_626462 : EJMOriginalGlobalDAGData.nodes 9 ⟨626462, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨626426, by decide⟩,⟨626450, by decide⟩,⟨626461, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77394_626462 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77394 ⟨626462, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77394
    ⟨626462, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨626426, by decide⟩,⟨626450, by decide⟩,⟨626461, by decide⟩]) unmarked_context_12_77394_626462 node_context_12_77394_626462
  intro a
  fin_cases a
  · exact context_13_309576_3444
  · exact context_13_309577_626426
  · exact context_13_309578_626450
  · exact context_13_309579_626461

theorem selected_cut_24811 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 309580) = some ⟨13, 1, 0, 3444, 309580, 1, 16384⟩ := by
  decide +kernel

theorem context_13_309580_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309580 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 309580 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 309580, 1, 16384⟩
    (by decide) selected_cut_24811

theorem selected_cut_24812 : selected 8 ⟨626502, by decide⟩
    (prefixPartial 13 309581) = some ⟨13, 2, 0, 626502, 309581, 2297, 16384⟩ := by
  decide +kernel

theorem context_13_309581_626502 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309581 ⟨626502, by decide⟩ :=
  accepted_of_selected 13 309581 ⟨626502, by decide⟩ ⟨13, 2, 0, 626502, 309581, 2297, 16384⟩
    (by decide) selected_cut_24812

theorem selected_cut_24813 : selected 8 ⟨626530, by decide⟩
    (prefixPartial 13 309582) = some ⟨13, 2, 0, 626530, 309582, 1773, 16384⟩ := by
  decide +kernel

theorem context_13_309582_626530 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309582 ⟨626530, by decide⟩ :=
  accepted_of_selected 13 309582 ⟨626530, by decide⟩ ⟨13, 2, 0, 626530, 309582, 1773, 16384⟩
    (by decide) selected_cut_24813

theorem selected_cut_24814 : selected 8 ⟨626541, by decide⟩
    (prefixPartial 13 309583) = some ⟨13, 2, 0, 626541, 309583, 877, 16384⟩ := by
  decide +kernel

theorem context_13_309583_626541 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309583 ⟨626541, by decide⟩ :=
  accepted_of_selected 13 309583 ⟨626541, by decide⟩ ⟨13, 2, 0, 626541, 309583, 877, 16384⟩
    (by decide) selected_cut_24814

theorem unmarked_context_12_77395_626542 : frontier 9 ⟨626542, by decide⟩
    (prefixCache 12 77395) (prefixPartial 12 77395) = false := by
  decide +kernel

theorem node_context_12_77395_626542 : EJMOriginalGlobalDAGData.nodes 9 ⟨626542, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨626502, by decide⟩,⟨626530, by decide⟩,⟨626541, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77395_626542 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77395 ⟨626542, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77395
    ⟨626542, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨626502, by decide⟩,⟨626530, by decide⟩,⟨626541, by decide⟩]) unmarked_context_12_77395_626542 node_context_12_77395_626542
  intro a
  fin_cases a
  · exact context_13_309580_3444
  · exact context_13_309581_626502
  · exact context_13_309582_626530
  · exact context_13_309583_626541

theorem unmarked_context_11_19348_626543 : frontier 10 ⟨626543, by decide⟩
    (prefixCache 11 19348) (prefixPartial 11 19348) = false := by
  decide +kernel

theorem node_context_11_19348_626543 : EJMOriginalGlobalDAGData.nodes 10 ⟨626543, by decide⟩ =
    .split (coordinate 11) (![⟨626341, by decide⟩,⟨626404, by decide⟩,⟨626462, by decide⟩,⟨626542, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19348_626543 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19348 ⟨626543, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19348
    ⟨626543, by decide⟩ (by decide) (![⟨626341, by decide⟩,⟨626404, by decide⟩,⟨626462, by decide⟩,⟨626542, by decide⟩]) unmarked_context_11_19348_626543 node_context_11_19348_626543
  intro a
  fin_cases a
  · exact context_12_77392_626341
  · exact context_12_77393_626404
  · exact context_12_77394_626462
  · exact context_12_77395_626542

theorem selected_cut_24815 : selected 9 ⟨626596, by decide⟩
    (prefixPartial 12 77396) = some ⟨12, 2, 0, 626596, 77396, 3965, 65536⟩ := by
  decide +kernel

theorem context_12_77396_626596 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77396 ⟨626596, by decide⟩ :=
  accepted_of_selected 12 77396 ⟨626596, by decide⟩ ⟨12, 2, 0, 626596, 77396, 3965, 65536⟩
    (by decide) selected_cut_24815

theorem selected_cut_24816 : selected 9 ⟨626643, by decide⟩
    (prefixPartial 12 77397) = some ⟨12, 2, 0, 626643, 77397, 3981, 65536⟩ := by
  decide +kernel

theorem context_12_77397_626643 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77397 ⟨626643, by decide⟩ :=
  accepted_of_selected 12 77397 ⟨626643, by decide⟩ ⟨12, 2, 0, 626643, 77397, 3981, 65536⟩
    (by decide) selected_cut_24816

theorem selected_cut_24817 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 309592) = some ⟨13, 1, 0, 3444, 309592, 1, 16384⟩ := by
  decide +kernel

theorem context_13_309592_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309592 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 309592 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 309592, 1, 16384⟩
    (by decide) selected_cut_24817

theorem selected_cut_24818 : selected 8 ⟨626664, by decide⟩
    (prefixPartial 13 309593) = some ⟨13, 2, 0, 626664, 309593, 1677, 16384⟩ := by
  decide +kernel

theorem context_13_309593_626664 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309593 ⟨626664, by decide⟩ :=
  accepted_of_selected 13 309593 ⟨626664, by decide⟩ ⟨13, 2, 0, 626664, 309593, 1677, 16384⟩
    (by decide) selected_cut_24818

theorem selected_cut_24819 : selected 8 ⟨626688, by decide⟩
    (prefixPartial 13 309594) = some ⟨13, 2, 0, 626688, 309594, 1705, 16384⟩ := by
  decide +kernel

theorem context_13_309594_626688 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309594 ⟨626688, by decide⟩ :=
  accepted_of_selected 13 309594 ⟨626688, by decide⟩ ⟨13, 2, 0, 626688, 309594, 1705, 16384⟩
    (by decide) selected_cut_24819

theorem selected_cut_24820 : selected 8 ⟨626698, by decide⟩
    (prefixPartial 13 309595) = some ⟨13, 2, 0, 626698, 309595, 921, 16384⟩ := by
  decide +kernel

theorem context_13_309595_626698 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309595 ⟨626698, by decide⟩ :=
  accepted_of_selected 13 309595 ⟨626698, by decide⟩ ⟨13, 2, 0, 626698, 309595, 921, 16384⟩
    (by decide) selected_cut_24820

theorem unmarked_context_12_77398_626699 : frontier 9 ⟨626699, by decide⟩
    (prefixCache 12 77398) (prefixPartial 12 77398) = false := by
  decide +kernel

theorem node_context_12_77398_626699 : EJMOriginalGlobalDAGData.nodes 9 ⟨626699, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨626664, by decide⟩,⟨626688, by decide⟩,⟨626698, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77398_626699 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77398 ⟨626699, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77398
    ⟨626699, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨626664, by decide⟩,⟨626688, by decide⟩,⟨626698, by decide⟩]) unmarked_context_12_77398_626699 node_context_12_77398_626699
  intro a
  fin_cases a
  · exact context_13_309592_3444
  · exact context_13_309593_626664
  · exact context_13_309594_626688
  · exact context_13_309595_626698

theorem selected_cut_24821 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 309596) = some ⟨13, 1, 0, 3444, 309596, 1, 16384⟩ := by
  decide +kernel

theorem context_13_309596_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309596 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 309596 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 309596, 1, 16384⟩
    (by decide) selected_cut_24821

theorem selected_cut_24822 : selected 8 ⟨626730, by decide⟩
    (prefixPartial 13 309597) = some ⟨13, 2, 0, 626730, 309597, 2005, 16384⟩ := by
  decide +kernel

theorem context_13_309597_626730 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309597 ⟨626730, by decide⟩ :=
  accepted_of_selected 13 309597 ⟨626730, by decide⟩ ⟨13, 2, 0, 626730, 309597, 2005, 16384⟩
    (by decide) selected_cut_24822

theorem selected_cut_24823 : selected 8 ⟨626762, by decide⟩
    (prefixPartial 13 309598) = some ⟨13, 2, 0, 626762, 309598, 2061, 16384⟩ := by
  decide +kernel

theorem context_13_309598_626762 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309598 ⟨626762, by decide⟩ :=
  accepted_of_selected 13 309598 ⟨626762, by decide⟩ ⟨13, 2, 0, 626762, 309598, 2061, 16384⟩
    (by decide) selected_cut_24823

theorem selected_cut_24824 : selected 8 ⟨626769, by decide⟩
    (prefixPartial 13 309599) = some ⟨13, 2, 0, 626769, 309599, 913, 16384⟩ := by
  decide +kernel

theorem context_13_309599_626769 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309599 ⟨626769, by decide⟩ :=
  accepted_of_selected 13 309599 ⟨626769, by decide⟩ ⟨13, 2, 0, 626769, 309599, 913, 16384⟩
    (by decide) selected_cut_24824

theorem unmarked_context_12_77399_626770 : frontier 9 ⟨626770, by decide⟩
    (prefixCache 12 77399) (prefixPartial 12 77399) = false := by
  decide +kernel

theorem node_context_12_77399_626770 : EJMOriginalGlobalDAGData.nodes 9 ⟨626770, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨626730, by decide⟩,⟨626762, by decide⟩,⟨626769, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77399_626770 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77399 ⟨626770, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77399
    ⟨626770, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨626730, by decide⟩,⟨626762, by decide⟩,⟨626769, by decide⟩]) unmarked_context_12_77399_626770 node_context_12_77399_626770
  intro a
  fin_cases a
  · exact context_13_309596_3444
  · exact context_13_309597_626730
  · exact context_13_309598_626762
  · exact context_13_309599_626769

theorem unmarked_context_11_19349_626771 : frontier 10 ⟨626771, by decide⟩
    (prefixCache 11 19349) (prefixPartial 11 19349) = false := by
  decide +kernel

theorem node_context_11_19349_626771 : EJMOriginalGlobalDAGData.nodes 10 ⟨626771, by decide⟩ =
    .split (coordinate 11) (![⟨626596, by decide⟩,⟨626643, by decide⟩,⟨626699, by decide⟩,⟨626770, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19349_626771 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19349 ⟨626771, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19349
    ⟨626771, by decide⟩ (by decide) (![⟨626596, by decide⟩,⟨626643, by decide⟩,⟨626699, by decide⟩,⟨626770, by decide⟩]) unmarked_context_11_19349_626771 node_context_11_19349_626771
  intro a
  fin_cases a
  · exact context_12_77396_626596
  · exact context_12_77397_626643
  · exact context_12_77398_626699
  · exact context_12_77399_626770

theorem selected_cut_24825 : selected 9 ⟨626816, by decide⟩
    (prefixPartial 12 77400) = some ⟨12, 2, 0, 626816, 77400, 3597, 65536⟩ := by
  decide +kernel

theorem context_12_77400_626816 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77400 ⟨626816, by decide⟩ :=
  accepted_of_selected 12 77400 ⟨626816, by decide⟩ ⟨12, 2, 0, 626816, 77400, 3597, 65536⟩
    (by decide) selected_cut_24825

theorem selected_cut_24826 : selected 9 ⟨626874, by decide⟩
    (prefixPartial 12 77401) = some ⟨12, 2, 0, 626874, 77401, 3869, 65536⟩ := by
  decide +kernel

theorem context_12_77401_626874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77401 ⟨626874, by decide⟩ :=
  accepted_of_selected 12 77401 ⟨626874, by decide⟩ ⟨12, 2, 0, 626874, 77401, 3869, 65536⟩
    (by decide) selected_cut_24826

theorem selected_cut_24827 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 309608) = some ⟨13, 1, 0, 3444, 309608, 1, 16384⟩ := by
  decide +kernel

theorem context_13_309608_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309608 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 309608 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 309608, 1, 16384⟩
    (by decide) selected_cut_24827

theorem selected_cut_24828 : selected 8 ⟨626919, by decide⟩
    (prefixPartial 13 309609) = some ⟨13, 2, 0, 626919, 309609, 2293, 16384⟩ := by
  decide +kernel

theorem context_13_309609_626919 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309609 ⟨626919, by decide⟩ :=
  accepted_of_selected 13 309609 ⟨626919, by decide⟩ ⟨13, 2, 0, 626919, 309609, 2293, 16384⟩
    (by decide) selected_cut_24828

theorem selected_cut_24829 : selected 8 ⟨626978, by decide⟩
    (prefixPartial 13 309610) = some ⟨13, 2, 0, 626978, 309610, 2677, 16384⟩ := by
  decide +kernel

theorem context_13_309610_626978 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309610 ⟨626978, by decide⟩ :=
  accepted_of_selected 13 309610 ⟨626978, by decide⟩ ⟨13, 2, 0, 626978, 309610, 2677, 16384⟩
    (by decide) selected_cut_24829

theorem selected_cut_24830 : selected 8 ⟨627009, by decide⟩
    (prefixPartial 13 309611) = some ⟨13, 2, 0, 627009, 309611, 1353, 16384⟩ := by
  decide +kernel

theorem context_13_309611_627009 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309611 ⟨627009, by decide⟩ :=
  accepted_of_selected 13 309611 ⟨627009, by decide⟩ ⟨13, 2, 0, 627009, 309611, 1353, 16384⟩
    (by decide) selected_cut_24830

theorem unmarked_context_12_77402_627010 : frontier 9 ⟨627010, by decide⟩
    (prefixCache 12 77402) (prefixPartial 12 77402) = false := by
  decide +kernel

theorem node_context_12_77402_627010 : EJMOriginalGlobalDAGData.nodes 9 ⟨627010, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨626919, by decide⟩,⟨626978, by decide⟩,⟨627009, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77402_627010 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77402 ⟨627010, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77402
    ⟨627010, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨626919, by decide⟩,⟨626978, by decide⟩,⟨627009, by decide⟩]) unmarked_context_12_77402_627010 node_context_12_77402_627010
  intro a
  fin_cases a
  · exact context_13_309608_3444
  · exact context_13_309609_626919
  · exact context_13_309610_626978
  · exact context_13_309611_627009

theorem selected_cut_24831 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 309612) = some ⟨13, 1, 0, 3444, 309612, 1, 16384⟩ := by
  decide +kernel

theorem context_13_309612_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309612 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 309612 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 309612, 1, 16384⟩
    (by decide) selected_cut_24831

theorem selected_cut_24832 : selected 8 ⟨627040, by decide⟩
    (prefixPartial 13 309613) = some ⟨13, 2, 0, 627040, 309613, 1637, 16384⟩ := by
  decide +kernel

theorem context_13_309613_627040 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309613 ⟨627040, by decide⟩ :=
  accepted_of_selected 13 309613 ⟨627040, by decide⟩ ⟨13, 2, 0, 627040, 309613, 1637, 16384⟩
    (by decide) selected_cut_24832

theorem selected_cut_24833 : selected 8 ⟨627062, by decide⟩
    (prefixPartial 13 309614) = some ⟨13, 2, 0, 627062, 309614, 1693, 16384⟩ := by
  decide +kernel

theorem context_13_309614_627062 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309614 ⟨627062, by decide⟩ :=
  accepted_of_selected 13 309614 ⟨627062, by decide⟩ ⟨13, 2, 0, 627062, 309614, 1693, 16384⟩
    (by decide) selected_cut_24833

theorem selected_cut_24834 : selected 8 ⟨627077, by decide⟩
    (prefixPartial 13 309615) = some ⟨13, 2, 0, 627077, 309615, 925, 16384⟩ := by
  decide +kernel

theorem context_13_309615_627077 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309615 ⟨627077, by decide⟩ :=
  accepted_of_selected 13 309615 ⟨627077, by decide⟩ ⟨13, 2, 0, 627077, 309615, 925, 16384⟩
    (by decide) selected_cut_24834

theorem unmarked_context_12_77403_627078 : frontier 9 ⟨627078, by decide⟩
    (prefixCache 12 77403) (prefixPartial 12 77403) = false := by
  decide +kernel

theorem node_context_12_77403_627078 : EJMOriginalGlobalDAGData.nodes 9 ⟨627078, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨627040, by decide⟩,⟨627062, by decide⟩,⟨627077, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77403_627078 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77403 ⟨627078, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77403
    ⟨627078, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨627040, by decide⟩,⟨627062, by decide⟩,⟨627077, by decide⟩]) unmarked_context_12_77403_627078 node_context_12_77403_627078
  intro a
  fin_cases a
  · exact context_13_309612_3444
  · exact context_13_309613_627040
  · exact context_13_309614_627062
  · exact context_13_309615_627077

theorem unmarked_context_11_19350_627079 : frontier 10 ⟨627079, by decide⟩
    (prefixCache 11 19350) (prefixPartial 11 19350) = false := by
  decide +kernel

theorem node_context_11_19350_627079 : EJMOriginalGlobalDAGData.nodes 10 ⟨627079, by decide⟩ =
    .split (coordinate 11) (![⟨626816, by decide⟩,⟨626874, by decide⟩,⟨627010, by decide⟩,⟨627078, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19350_627079 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19350 ⟨627079, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19350
    ⟨627079, by decide⟩ (by decide) (![⟨626816, by decide⟩,⟨626874, by decide⟩,⟨627010, by decide⟩,⟨627078, by decide⟩]) unmarked_context_11_19350_627079 node_context_11_19350_627079
  intro a
  fin_cases a
  · exact context_12_77400_626816
  · exact context_12_77401_626874
  · exact context_12_77402_627010
  · exact context_12_77403_627078

theorem selected_cut_24835 : selected 9 ⟨627130, by decide⟩
    (prefixPartial 12 77404) = some ⟨12, 2, 0, 627130, 77404, 3545, 65536⟩ := by
  decide +kernel

theorem context_12_77404_627130 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77404 ⟨627130, by decide⟩ :=
  accepted_of_selected 12 77404 ⟨627130, by decide⟩ ⟨12, 2, 0, 627130, 77404, 3545, 65536⟩
    (by decide) selected_cut_24835

theorem selected_cut_24836 : selected 9 ⟨627183, by decide⟩
    (prefixPartial 12 77405) = some ⟨12, 2, 0, 627183, 77405, 3717, 65536⟩ := by
  decide +kernel

theorem context_12_77405_627183 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77405 ⟨627183, by decide⟩ :=
  accepted_of_selected 12 77405 ⟨627183, by decide⟩ ⟨12, 2, 0, 627183, 77405, 3717, 65536⟩
    (by decide) selected_cut_24836

theorem selected_cut_24837 : selected 9 ⟨627229, by decide⟩
    (prefixPartial 12 77406) = some ⟨12, 2, 0, 627229, 77406, 3813, 65536⟩ := by
  decide +kernel

theorem context_12_77406_627229 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77406 ⟨627229, by decide⟩ :=
  accepted_of_selected 12 77406 ⟨627229, by decide⟩ ⟨12, 2, 0, 627229, 77406, 3813, 65536⟩
    (by decide) selected_cut_24837

theorem selected_cut_24838 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 309628) = some ⟨13, 1, 0, 3444, 309628, 1, 16384⟩ := by
  decide +kernel

theorem context_13_309628_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309628 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 309628 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 309628, 1, 16384⟩
    (by decide) selected_cut_24838

theorem selected_cut_24839 : selected 8 ⟨627250, by decide⟩
    (prefixPartial 13 309629) = some ⟨13, 2, 0, 627250, 309629, 1469, 16384⟩ := by
  decide +kernel

theorem context_13_309629_627250 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309629 ⟨627250, by decide⟩ :=
  accepted_of_selected 13 309629 ⟨627250, by decide⟩ ⟨13, 2, 0, 627250, 309629, 1469, 16384⟩
    (by decide) selected_cut_24839

theorem selected_cut_24840 : selected 8 ⟨627270, by decide⟩
    (prefixPartial 13 309630) = some ⟨13, 2, 0, 627270, 309630, 1805, 16384⟩ := by
  decide +kernel

theorem context_13_309630_627270 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309630 ⟨627270, by decide⟩ :=
  accepted_of_selected 13 309630 ⟨627270, by decide⟩ ⟨13, 2, 0, 627270, 309630, 1805, 16384⟩
    (by decide) selected_cut_24840

theorem selected_cut_24841 : selected 8 ⟨627280, by decide⟩
    (prefixPartial 13 309631) = some ⟨13, 2, 0, 627280, 309631, 969, 16384⟩ := by
  decide +kernel

theorem context_13_309631_627280 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309631 ⟨627280, by decide⟩ :=
  accepted_of_selected 13 309631 ⟨627280, by decide⟩ ⟨13, 2, 0, 627280, 309631, 969, 16384⟩
    (by decide) selected_cut_24841

theorem unmarked_context_12_77407_627281 : frontier 9 ⟨627281, by decide⟩
    (prefixCache 12 77407) (prefixPartial 12 77407) = false := by
  decide +kernel

theorem node_context_12_77407_627281 : EJMOriginalGlobalDAGData.nodes 9 ⟨627281, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨627250, by decide⟩,⟨627270, by decide⟩,⟨627280, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77407_627281 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77407 ⟨627281, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77407
    ⟨627281, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨627250, by decide⟩,⟨627270, by decide⟩,⟨627280, by decide⟩]) unmarked_context_12_77407_627281 node_context_12_77407_627281
  intro a
  fin_cases a
  · exact context_13_309628_3444
  · exact context_13_309629_627250
  · exact context_13_309630_627270
  · exact context_13_309631_627280

theorem unmarked_context_11_19351_627282 : frontier 10 ⟨627282, by decide⟩
    (prefixCache 11 19351) (prefixPartial 11 19351) = false := by
  decide +kernel

theorem node_context_11_19351_627282 : EJMOriginalGlobalDAGData.nodes 10 ⟨627282, by decide⟩ =
    .split (coordinate 11) (![⟨627130, by decide⟩,⟨627183, by decide⟩,⟨627229, by decide⟩,⟨627281, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19351_627282 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19351 ⟨627282, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19351
    ⟨627282, by decide⟩ (by decide) (![⟨627130, by decide⟩,⟨627183, by decide⟩,⟨627229, by decide⟩,⟨627281, by decide⟩]) unmarked_context_11_19351_627282 node_context_11_19351_627282
  intro a
  fin_cases a
  · exact context_12_77404_627130
  · exact context_12_77405_627183
  · exact context_12_77406_627229
  · exact context_12_77407_627281

theorem unmarked_context_10_4837_627283 : frontier 11 ⟨627283, by decide⟩
    (prefixCache 10 4837) (prefixPartial 10 4837) = false := by
  decide +kernel

theorem node_context_10_4837_627283 : EJMOriginalGlobalDAGData.nodes 11 ⟨627283, by decide⟩ =
    .split (coordinate 10) (![⟨626543, by decide⟩,⟨626771, by decide⟩,⟨627079, by decide⟩,⟨627282, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4837_627283 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4837 ⟨627283, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4837
    ⟨627283, by decide⟩ (by decide) (![⟨626543, by decide⟩,⟨626771, by decide⟩,⟨627079, by decide⟩,⟨627282, by decide⟩]) unmarked_context_10_4837_627283 node_context_10_4837_627283
  intro a
  fin_cases a
  · exact context_11_19348_626543
  · exact context_11_19349_626771
  · exact context_11_19350_627079
  · exact context_11_19351_627282

theorem selected_cut_24842 : selected 9 ⟨627332, by decide⟩
    (prefixPartial 12 77408) = some ⟨12, 2, 0, 627332, 77408, 3285, 65536⟩ := by
  decide +kernel

theorem context_12_77408_627332 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77408 ⟨627332, by decide⟩ :=
  accepted_of_selected 12 77408 ⟨627332, by decide⟩ ⟨12, 2, 0, 627332, 77408, 3285, 65536⟩
    (by decide) selected_cut_24842

theorem selected_cut_24843 : selected 9 ⟨627385, by decide⟩
    (prefixPartial 12 77409) = some ⟨12, 2, 0, 627385, 77409, 3649, 65536⟩ := by
  decide +kernel

theorem context_12_77409_627385 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77409 ⟨627385, by decide⟩ :=
  accepted_of_selected 12 77409 ⟨627385, by decide⟩ ⟨12, 2, 0, 627385, 77409, 3649, 65536⟩
    (by decide) selected_cut_24843

theorem selected_cut_24844 : selected 9 ⟨627439, by decide⟩
    (prefixPartial 12 77410) = some ⟨12, 2, 0, 627439, 77410, 3537, 65536⟩ := by
  decide +kernel

theorem context_12_77410_627439 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77410 ⟨627439, by decide⟩ :=
  accepted_of_selected 12 77410 ⟨627439, by decide⟩ ⟨12, 2, 0, 627439, 77410, 3537, 65536⟩
    (by decide) selected_cut_24844

theorem selected_cut_24845 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 309644) = some ⟨13, 1, 0, 3444, 309644, 1, 16384⟩ := by
  decide +kernel

theorem context_13_309644_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309644 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 309644 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 309644, 1, 16384⟩
    (by decide) selected_cut_24845

theorem selected_cut_24846 : selected 8 ⟨627462, by decide⟩
    (prefixPartial 13 309645) = some ⟨13, 2, 0, 627462, 309645, 1429, 16384⟩ := by
  decide +kernel

theorem context_13_309645_627462 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309645 ⟨627462, by decide⟩ :=
  accepted_of_selected 13 309645 ⟨627462, by decide⟩ ⟨13, 2, 0, 627462, 309645, 1429, 16384⟩
    (by decide) selected_cut_24846

theorem selected_cut_24847 : selected 8 ⟨627488, by decide⟩
    (prefixPartial 13 309646) = some ⟨13, 2, 0, 627488, 309646, 1825, 16384⟩ := by
  decide +kernel

theorem context_13_309646_627488 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309646 ⟨627488, by decide⟩ :=
  accepted_of_selected 13 309646 ⟨627488, by decide⟩ ⟨13, 2, 0, 627488, 309646, 1825, 16384⟩
    (by decide) selected_cut_24847

theorem selected_cut_24848 : selected 8 ⟨627497, by decide⟩
    (prefixPartial 13 309647) = some ⟨13, 2, 0, 627497, 309647, 877, 16384⟩ := by
  decide +kernel

theorem context_13_309647_627497 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309647 ⟨627497, by decide⟩ :=
  accepted_of_selected 13 309647 ⟨627497, by decide⟩ ⟨13, 2, 0, 627497, 309647, 877, 16384⟩
    (by decide) selected_cut_24848

theorem unmarked_context_12_77411_627498 : frontier 9 ⟨627498, by decide⟩
    (prefixCache 12 77411) (prefixPartial 12 77411) = false := by
  decide +kernel

theorem node_context_12_77411_627498 : EJMOriginalGlobalDAGData.nodes 9 ⟨627498, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨627462, by decide⟩,⟨627488, by decide⟩,⟨627497, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77411_627498 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77411 ⟨627498, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77411
    ⟨627498, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨627462, by decide⟩,⟨627488, by decide⟩,⟨627497, by decide⟩]) unmarked_context_12_77411_627498 node_context_12_77411_627498
  intro a
  fin_cases a
  · exact context_13_309644_3444
  · exact context_13_309645_627462
  · exact context_13_309646_627488
  · exact context_13_309647_627497

theorem unmarked_context_11_19352_627499 : frontier 10 ⟨627499, by decide⟩
    (prefixCache 11 19352) (prefixPartial 11 19352) = false := by
  decide +kernel

theorem node_context_11_19352_627499 : EJMOriginalGlobalDAGData.nodes 10 ⟨627499, by decide⟩ =
    .split (coordinate 11) (![⟨627332, by decide⟩,⟨627385, by decide⟩,⟨627439, by decide⟩,⟨627498, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19352_627499 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19352 ⟨627499, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19352
    ⟨627499, by decide⟩ (by decide) (![⟨627332, by decide⟩,⟨627385, by decide⟩,⟨627439, by decide⟩,⟨627498, by decide⟩]) unmarked_context_11_19352_627499 node_context_11_19352_627499
  intro a
  fin_cases a
  · exact context_12_77408_627332
  · exact context_12_77409_627385
  · exact context_12_77410_627439
  · exact context_12_77411_627498

theorem selected_cut_24849 : selected 9 ⟨627557, by decide⟩
    (prefixPartial 12 77412) = some ⟨12, 2, 0, 627557, 77412, 3661, 65536⟩ := by
  decide +kernel

theorem context_12_77412_627557 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77412 ⟨627557, by decide⟩ :=
  accepted_of_selected 12 77412 ⟨627557, by decide⟩ ⟨12, 2, 0, 627557, 77412, 3661, 65536⟩
    (by decide) selected_cut_24849

theorem selected_cut_24850 : selected 9 ⟨627607, by decide⟩
    (prefixPartial 12 77413) = some ⟨12, 2, 0, 627607, 77413, 3717, 65536⟩ := by
  decide +kernel

theorem context_12_77413_627607 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77413 ⟨627607, by decide⟩ :=
  accepted_of_selected 12 77413 ⟨627607, by decide⟩ ⟨12, 2, 0, 627607, 77413, 3717, 65536⟩
    (by decide) selected_cut_24850

theorem selected_cut_24851 : selected 9 ⟨627657, by decide⟩
    (prefixPartial 12 77414) = some ⟨12, 2, 0, 627657, 77414, 3817, 65536⟩ := by
  decide +kernel

theorem context_12_77414_627657 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77414 ⟨627657, by decide⟩ :=
  accepted_of_selected 12 77414 ⟨627657, by decide⟩ ⟨12, 2, 0, 627657, 77414, 3817, 65536⟩
    (by decide) selected_cut_24851

theorem selected_cut_24852 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 309660) = some ⟨13, 1, 0, 3444, 309660, 1, 16384⟩ := by
  decide +kernel

theorem context_13_309660_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309660 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 309660 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 309660, 1, 16384⟩
    (by decide) selected_cut_24852

theorem selected_cut_24853 : selected 8 ⟨627677, by decide⟩
    (prefixPartial 13 309661) = some ⟨13, 2, 0, 627677, 309661, 1213, 16384⟩ := by
  decide +kernel

theorem context_13_309661_627677 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309661 ⟨627677, by decide⟩ :=
  accepted_of_selected 13 309661 ⟨627677, by decide⟩ ⟨13, 2, 0, 627677, 309661, 1213, 16384⟩
    (by decide) selected_cut_24853

theorem selected_cut_24854 : selected 8 ⟨627706, by decide⟩
    (prefixPartial 13 309662) = some ⟨13, 2, 0, 627706, 309662, 2185, 16384⟩ := by
  decide +kernel

theorem context_13_309662_627706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309662 ⟨627706, by decide⟩ :=
  accepted_of_selected 13 309662 ⟨627706, by decide⟩ ⟨13, 2, 0, 627706, 309662, 2185, 16384⟩
    (by decide) selected_cut_24854

theorem selected_cut_24855 : selected 8 ⟨627723, by decide⟩
    (prefixPartial 13 309663) = some ⟨13, 2, 0, 627723, 309663, 981, 16384⟩ := by
  decide +kernel

theorem context_13_309663_627723 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309663 ⟨627723, by decide⟩ :=
  accepted_of_selected 13 309663 ⟨627723, by decide⟩ ⟨13, 2, 0, 627723, 309663, 981, 16384⟩
    (by decide) selected_cut_24855

theorem unmarked_context_12_77415_627724 : frontier 9 ⟨627724, by decide⟩
    (prefixCache 12 77415) (prefixPartial 12 77415) = false := by
  decide +kernel

theorem node_context_12_77415_627724 : EJMOriginalGlobalDAGData.nodes 9 ⟨627724, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨627677, by decide⟩,⟨627706, by decide⟩,⟨627723, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77415_627724 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77415 ⟨627724, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77415
    ⟨627724, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨627677, by decide⟩,⟨627706, by decide⟩,⟨627723, by decide⟩]) unmarked_context_12_77415_627724 node_context_12_77415_627724
  intro a
  fin_cases a
  · exact context_13_309660_3444
  · exact context_13_309661_627677
  · exact context_13_309662_627706
  · exact context_13_309663_627723

theorem unmarked_context_11_19353_627725 : frontier 10 ⟨627725, by decide⟩
    (prefixCache 11 19353) (prefixPartial 11 19353) = false := by
  decide +kernel

theorem node_context_11_19353_627725 : EJMOriginalGlobalDAGData.nodes 10 ⟨627725, by decide⟩ =
    .split (coordinate 11) (![⟨627557, by decide⟩,⟨627607, by decide⟩,⟨627657, by decide⟩,⟨627724, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19353_627725 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19353 ⟨627725, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19353
    ⟨627725, by decide⟩ (by decide) (![⟨627557, by decide⟩,⟨627607, by decide⟩,⟨627657, by decide⟩,⟨627724, by decide⟩]) unmarked_context_11_19353_627725 node_context_11_19353_627725
  intro a
  fin_cases a
  · exact context_12_77412_627557
  · exact context_12_77413_627607
  · exact context_12_77414_627657
  · exact context_12_77415_627724

theorem selected_cut_24856 : selected 9 ⟨627773, by decide⟩
    (prefixPartial 12 77416) = some ⟨12, 2, 0, 627773, 77416, 3185, 65536⟩ := by
  decide +kernel

theorem context_12_77416_627773 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77416 ⟨627773, by decide⟩ :=
  accepted_of_selected 12 77416 ⟨627773, by decide⟩ ⟨12, 2, 0, 627773, 77416, 3185, 65536⟩
    (by decide) selected_cut_24856

theorem selected_cut_24857 : selected 9 ⟨627816, by decide⟩
    (prefixPartial 12 77417) = some ⟨12, 2, 0, 627816, 77417, 3469, 65536⟩ := by
  decide +kernel

theorem context_12_77417_627816 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77417 ⟨627816, by decide⟩ :=
  accepted_of_selected 12 77417 ⟨627816, by decide⟩ ⟨12, 2, 0, 627816, 77417, 3469, 65536⟩
    (by decide) selected_cut_24857

theorem selected_cut_24858 : selected 9 ⟨445248, by decide⟩
    (prefixPartial 12 77418) = some ⟨12, 1, 0, 445248, 77418, 1, 65536⟩ := by
  decide +kernel

theorem context_12_77418_445248 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77418 ⟨445248, by decide⟩ :=
  accepted_of_selected 12 77418 ⟨445248, by decide⟩ ⟨12, 1, 0, 445248, 77418, 1, 65536⟩
    (by decide) selected_cut_24858

theorem selected_cut_24859 : selected 9 ⟨627862, by decide⟩
    (prefixPartial 12 77419) = some ⟨12, 2, 0, 627862, 77419, 3685, 65536⟩ := by
  decide +kernel

theorem context_12_77419_627862 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77419 ⟨627862, by decide⟩ :=
  accepted_of_selected 12 77419 ⟨627862, by decide⟩ ⟨12, 2, 0, 627862, 77419, 3685, 65536⟩
    (by decide) selected_cut_24859

theorem unmarked_context_11_19354_627863 : frontier 10 ⟨627863, by decide⟩
    (prefixCache 11 19354) (prefixPartial 11 19354) = false := by
  decide +kernel

theorem node_context_11_19354_627863 : EJMOriginalGlobalDAGData.nodes 10 ⟨627863, by decide⟩ =
    .split (coordinate 11) (![⟨627773, by decide⟩,⟨627816, by decide⟩,⟨445248, by decide⟩,⟨627862, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19354_627863 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19354 ⟨627863, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19354
    ⟨627863, by decide⟩ (by decide) (![⟨627773, by decide⟩,⟨627816, by decide⟩,⟨445248, by decide⟩,⟨627862, by decide⟩]) unmarked_context_11_19354_627863 node_context_11_19354_627863
  intro a
  fin_cases a
  · exact context_12_77416_627773
  · exact context_12_77417_627816
  · exact context_12_77418_445248
  · exact context_12_77419_627862

theorem selected_cut_24860 : selected 9 ⟨627907, by decide⟩
    (prefixPartial 12 77420) = some ⟨12, 2, 0, 627907, 77420, 3205, 65536⟩ := by
  decide +kernel

theorem context_12_77420_627907 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77420 ⟨627907, by decide⟩ :=
  accepted_of_selected 12 77420 ⟨627907, by decide⟩ ⟨12, 2, 0, 627907, 77420, 3205, 65536⟩
    (by decide) selected_cut_24860

theorem selected_cut_24861 : selected 9 ⟨627953, by decide⟩
    (prefixPartial 12 77421) = some ⟨12, 2, 0, 627953, 77421, 3329, 65536⟩ := by
  decide +kernel

theorem context_12_77421_627953 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77421 ⟨627953, by decide⟩ :=
  accepted_of_selected 12 77421 ⟨627953, by decide⟩ ⟨12, 2, 0, 627953, 77421, 3329, 65536⟩
    (by decide) selected_cut_24861

theorem selected_cut_24862 : selected 9 ⟨627996, by decide⟩
    (prefixPartial 12 77422) = some ⟨12, 2, 0, 627996, 77422, 3265, 65536⟩ := by
  decide +kernel

theorem context_12_77422_627996 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77422 ⟨627996, by decide⟩ :=
  accepted_of_selected 12 77422 ⟨627996, by decide⟩ ⟨12, 2, 0, 627996, 77422, 3265, 65536⟩
    (by decide) selected_cut_24862

theorem selected_cut_24863 : selected 9 ⟨628040, by decide⟩
    (prefixPartial 12 77423) = some ⟨12, 2, 0, 628040, 77423, 3597, 65536⟩ := by
  decide +kernel

theorem context_12_77423_628040 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77423 ⟨628040, by decide⟩ :=
  accepted_of_selected 12 77423 ⟨628040, by decide⟩ ⟨12, 2, 0, 628040, 77423, 3597, 65536⟩
    (by decide) selected_cut_24863

theorem unmarked_context_11_19355_628041 : frontier 10 ⟨628041, by decide⟩
    (prefixCache 11 19355) (prefixPartial 11 19355) = false := by
  decide +kernel

theorem node_context_11_19355_628041 : EJMOriginalGlobalDAGData.nodes 10 ⟨628041, by decide⟩ =
    .split (coordinate 11) (![⟨627907, by decide⟩,⟨627953, by decide⟩,⟨627996, by decide⟩,⟨628040, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19355_628041 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19355 ⟨628041, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19355
    ⟨628041, by decide⟩ (by decide) (![⟨627907, by decide⟩,⟨627953, by decide⟩,⟨627996, by decide⟩,⟨628040, by decide⟩]) unmarked_context_11_19355_628041 node_context_11_19355_628041
  intro a
  fin_cases a
  · exact context_12_77420_627907
  · exact context_12_77421_627953
  · exact context_12_77422_627996
  · exact context_12_77423_628040

theorem unmarked_context_10_4838_628042 : frontier 11 ⟨628042, by decide⟩
    (prefixCache 10 4838) (prefixPartial 10 4838) = false := by
  decide +kernel

theorem node_context_10_4838_628042 : EJMOriginalGlobalDAGData.nodes 11 ⟨628042, by decide⟩ =
    .split (coordinate 10) (![⟨627499, by decide⟩,⟨627725, by decide⟩,⟨627863, by decide⟩,⟨628041, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4838_628042 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4838 ⟨628042, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4838
    ⟨628042, by decide⟩ (by decide) (![⟨627499, by decide⟩,⟨627725, by decide⟩,⟨627863, by decide⟩,⟨628041, by decide⟩]) unmarked_context_10_4838_628042 node_context_10_4838_628042
  intro a
  fin_cases a
  · exact context_11_19352_627499
  · exact context_11_19353_627725
  · exact context_11_19354_627863
  · exact context_11_19355_628041

theorem selected_cut_24864 : selected 9 ⟨628086, by decide⟩
    (prefixPartial 12 77424) = some ⟨12, 2, 0, 628086, 77424, 2693, 65536⟩ := by
  decide +kernel

theorem context_12_77424_628086 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77424 ⟨628086, by decide⟩ :=
  accepted_of_selected 12 77424 ⟨628086, by decide⟩ ⟨12, 2, 0, 628086, 77424, 2693, 65536⟩
    (by decide) selected_cut_24864

theorem selected_cut_24865 : selected 9 ⟨628123, by decide⟩
    (prefixPartial 12 77425) = some ⟨12, 2, 0, 628123, 77425, 2953, 65536⟩ := by
  decide +kernel

theorem context_12_77425_628123 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77425 ⟨628123, by decide⟩ :=
  accepted_of_selected 12 77425 ⟨628123, by decide⟩ ⟨12, 2, 0, 628123, 77425, 2953, 65536⟩
    (by decide) selected_cut_24865

theorem selected_cut_24866 : selected 9 ⟨628164, by decide⟩
    (prefixPartial 12 77426) = some ⟨12, 2, 0, 628164, 77426, 2905, 65536⟩ := by
  decide +kernel

theorem context_12_77426_628164 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77426 ⟨628164, by decide⟩ :=
  accepted_of_selected 12 77426 ⟨628164, by decide⟩ ⟨12, 2, 0, 628164, 77426, 2905, 65536⟩
    (by decide) selected_cut_24866

theorem selected_cut_24867 : selected 9 ⟨628204, by decide⟩
    (prefixPartial 12 77427) = some ⟨12, 2, 0, 628204, 77427, 3101, 65536⟩ := by
  decide +kernel

theorem context_12_77427_628204 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77427 ⟨628204, by decide⟩ :=
  accepted_of_selected 12 77427 ⟨628204, by decide⟩ ⟨12, 2, 0, 628204, 77427, 3101, 65536⟩
    (by decide) selected_cut_24867

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
