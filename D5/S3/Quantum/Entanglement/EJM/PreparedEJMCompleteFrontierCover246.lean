/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover245
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem unmarked_context_12_76578_597763 : frontier 9 ⟨597763, by decide⟩
    (prefixCache 12 76578) (prefixPartial 12 76578) = false := by
  decide +kernel

theorem node_context_12_76578_597763 : EJMOriginalGlobalDAGData.nodes 9 ⟨597763, by decide⟩ =
    .split (coordinate 12) (![⟨597714, by decide⟩,⟨597740, by decide⟩,⟨597758, by decide⟩,⟨597762, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76578_597763 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76578 ⟨597763, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76578
    ⟨597763, by decide⟩ (by decide) (![⟨597714, by decide⟩,⟨597740, by decide⟩,⟨597758, by decide⟩,⟨597762, by decide⟩]) unmarked_context_12_76578_597763 node_context_12_76578_597763
  intro a
  fin_cases a
  · exact context_13_306312_597714
  · exact context_13_306313_597740
  · exact context_13_306314_597758
  · exact context_13_306315_597762

theorem selected_cut_23620 : selected 8 ⟨597780, by decide⟩
    (prefixPartial 13 306316) = some ⟨13, 2, 0, 597780, 306316, 837, 16384⟩ := by
  decide +kernel

theorem context_13_306316_597780 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306316 ⟨597780, by decide⟩ :=
  accepted_of_selected 13 306316 ⟨597780, by decide⟩ ⟨13, 2, 0, 597780, 306316, 837, 16384⟩
    (by decide) selected_cut_23620

theorem selected_cut_23621 : selected 8 ⟨597802, by decide⟩
    (prefixPartial 13 306317) = some ⟨13, 2, 0, 597802, 306317, 1853, 16384⟩ := by
  decide +kernel

theorem context_13_306317_597802 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306317 ⟨597802, by decide⟩ :=
  accepted_of_selected 13 306317 ⟨597802, by decide⟩ ⟨13, 2, 0, 597802, 306317, 1853, 16384⟩
    (by decide) selected_cut_23621

theorem selected_cut_23622 : selected 8 ⟨597821, by decide⟩
    (prefixPartial 13 306318) = some ⟨13, 2, 0, 597821, 306318, 1345, 16384⟩ := by
  decide +kernel

theorem context_13_306318_597821 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306318 ⟨597821, by decide⟩ :=
  accepted_of_selected 13 306318 ⟨597821, by decide⟩ ⟨13, 2, 0, 597821, 306318, 1345, 16384⟩
    (by decide) selected_cut_23622

theorem selected_cut_23623 : selected 8 ⟨597825, by decide⟩
    (prefixPartial 13 306319) = some ⟨13, 2, 0, 597825, 306319, 537, 16384⟩ := by
  decide +kernel

theorem context_13_306319_597825 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306319 ⟨597825, by decide⟩ :=
  accepted_of_selected 13 306319 ⟨597825, by decide⟩ ⟨13, 2, 0, 597825, 306319, 537, 16384⟩
    (by decide) selected_cut_23623

theorem unmarked_context_12_76579_597826 : frontier 9 ⟨597826, by decide⟩
    (prefixCache 12 76579) (prefixPartial 12 76579) = false := by
  decide +kernel

theorem node_context_12_76579_597826 : EJMOriginalGlobalDAGData.nodes 9 ⟨597826, by decide⟩ =
    .split (coordinate 12) (![⟨597780, by decide⟩,⟨597802, by decide⟩,⟨597821, by decide⟩,⟨597825, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76579_597826 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76579 ⟨597826, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76579
    ⟨597826, by decide⟩ (by decide) (![⟨597780, by decide⟩,⟨597802, by decide⟩,⟨597821, by decide⟩,⟨597825, by decide⟩]) unmarked_context_12_76579_597826 node_context_12_76579_597826
  intro a
  fin_cases a
  · exact context_13_306316_597780
  · exact context_13_306317_597802
  · exact context_13_306318_597821
  · exact context_13_306319_597825

theorem unmarked_context_11_19144_597827 : frontier 10 ⟨597827, by decide⟩
    (prefixCache 11 19144) (prefixPartial 11 19144) = false := by
  decide +kernel

theorem node_context_11_19144_597827 : EJMOriginalGlobalDAGData.nodes 10 ⟨597827, by decide⟩ =
    .split (coordinate 11) (![⟨435790, by decide⟩,⟨597699, by decide⟩,⟨597763, by decide⟩,⟨597826, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19144_597827 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19144 ⟨597827, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19144
    ⟨597827, by decide⟩ (by decide) (![⟨435790, by decide⟩,⟨597699, by decide⟩,⟨597763, by decide⟩,⟨597826, by decide⟩]) unmarked_context_11_19144_597827 node_context_11_19144_597827
  intro a
  fin_cases a
  · exact context_12_76576_435790
  · exact context_12_76577_597699
  · exact context_12_76578_597763
  · exact context_12_76579_597826

theorem selected_cut_23624 : selected 8 ⟨597861, by decide⟩
    (prefixPartial 13 306320) = some ⟨13, 2, 0, 597861, 306320, 1473, 16384⟩ := by
  decide +kernel

theorem context_13_306320_597861 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306320 ⟨597861, by decide⟩ :=
  accepted_of_selected 13 306320 ⟨597861, by decide⟩ ⟨13, 2, 0, 597861, 306320, 1473, 16384⟩
    (by decide) selected_cut_23624

theorem selected_cut_23625 : selected 8 ⟨597905, by decide⟩
    (prefixPartial 13 306321) = some ⟨13, 2, 0, 597905, 306321, 2837, 16384⟩ := by
  decide +kernel

theorem context_13_306321_597905 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306321 ⟨597905, by decide⟩ :=
  accepted_of_selected 13 306321 ⟨597905, by decide⟩ ⟨13, 2, 0, 597905, 306321, 2837, 16384⟩
    (by decide) selected_cut_23625

theorem selected_cut_23626 : selected 8 ⟨597932, by decide⟩
    (prefixPartial 13 306322) = some ⟨13, 2, 0, 597932, 306322, 1893, 16384⟩ := by
  decide +kernel

theorem context_13_306322_597932 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306322 ⟨597932, by decide⟩ :=
  accepted_of_selected 13 306322 ⟨597932, by decide⟩ ⟨13, 2, 0, 597932, 306322, 1893, 16384⟩
    (by decide) selected_cut_23626

theorem selected_cut_23627 : selected 8 ⟨597941, by decide⟩
    (prefixPartial 13 306323) = some ⟨13, 2, 0, 597941, 306323, 1081, 16384⟩ := by
  decide +kernel

theorem context_13_306323_597941 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306323 ⟨597941, by decide⟩ :=
  accepted_of_selected 13 306323 ⟨597941, by decide⟩ ⟨13, 2, 0, 597941, 306323, 1081, 16384⟩
    (by decide) selected_cut_23627

theorem unmarked_context_12_76580_597942 : frontier 9 ⟨597942, by decide⟩
    (prefixCache 12 76580) (prefixPartial 12 76580) = false := by
  decide +kernel

theorem node_context_12_76580_597942 : EJMOriginalGlobalDAGData.nodes 9 ⟨597942, by decide⟩ =
    .split (coordinate 12) (![⟨597861, by decide⟩,⟨597905, by decide⟩,⟨597932, by decide⟩,⟨597941, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76580_597942 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76580 ⟨597942, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76580
    ⟨597942, by decide⟩ (by decide) (![⟨597861, by decide⟩,⟨597905, by decide⟩,⟨597932, by decide⟩,⟨597941, by decide⟩]) unmarked_context_12_76580_597942 node_context_12_76580_597942
  intro a
  fin_cases a
  · exact context_13_306320_597861
  · exact context_13_306321_597905
  · exact context_13_306322_597932
  · exact context_13_306323_597941

theorem selected_cut_23628 : selected 8 ⟨597958, by decide⟩
    (prefixPartial 13 306324) = some ⟨13, 2, 0, 597958, 306324, 1033, 16384⟩ := by
  decide +kernel

theorem context_13_306324_597958 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306324 ⟨597958, by decide⟩ :=
  accepted_of_selected 13 306324 ⟨597958, by decide⟩ ⟨13, 2, 0, 597958, 306324, 1033, 16384⟩
    (by decide) selected_cut_23628

theorem selected_cut_23629 : selected 8 ⟨597978, by decide⟩
    (prefixPartial 13 306325) = some ⟨13, 2, 0, 597978, 306325, 1625, 16384⟩ := by
  decide +kernel

theorem context_13_306325_597978 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306325 ⟨597978, by decide⟩ :=
  accepted_of_selected 13 306325 ⟨597978, by decide⟩ ⟨13, 2, 0, 597978, 306325, 1625, 16384⟩
    (by decide) selected_cut_23629

theorem selected_cut_23630 : selected 8 ⟨597995, by decide⟩
    (prefixPartial 13 306326) = some ⟨13, 2, 0, 597995, 306326, 1469, 16384⟩ := by
  decide +kernel

theorem context_13_306326_597995 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306326 ⟨597995, by decide⟩ :=
  accepted_of_selected 13 306326 ⟨597995, by decide⟩ ⟨13, 2, 0, 597995, 306326, 1469, 16384⟩
    (by decide) selected_cut_23630

theorem selected_cut_23631 : selected 8 ⟨597999, by decide⟩
    (prefixPartial 13 306327) = some ⟨13, 2, 0, 597999, 306327, 753, 16384⟩ := by
  decide +kernel

theorem context_13_306327_597999 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306327 ⟨597999, by decide⟩ :=
  accepted_of_selected 13 306327 ⟨597999, by decide⟩ ⟨13, 2, 0, 597999, 306327, 753, 16384⟩
    (by decide) selected_cut_23631

theorem unmarked_context_12_76581_598000 : frontier 9 ⟨598000, by decide⟩
    (prefixCache 12 76581) (prefixPartial 12 76581) = false := by
  decide +kernel

theorem node_context_12_76581_598000 : EJMOriginalGlobalDAGData.nodes 9 ⟨598000, by decide⟩ =
    .split (coordinate 12) (![⟨597958, by decide⟩,⟨597978, by decide⟩,⟨597995, by decide⟩,⟨597999, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76581_598000 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76581 ⟨598000, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76581
    ⟨598000, by decide⟩ (by decide) (![⟨597958, by decide⟩,⟨597978, by decide⟩,⟨597995, by decide⟩,⟨597999, by decide⟩]) unmarked_context_12_76581_598000 node_context_12_76581_598000
  intro a
  fin_cases a
  · exact context_13_306324_597958
  · exact context_13_306325_597978
  · exact context_13_306326_597995
  · exact context_13_306327_597999

theorem selected_cut_23632 : selected 8 ⟨598016, by decide⟩
    (prefixPartial 13 306328) = some ⟨13, 2, 0, 598016, 306328, 949, 16384⟩ := by
  decide +kernel

theorem context_13_306328_598016 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306328 ⟨598016, by decide⟩ :=
  accepted_of_selected 13 306328 ⟨598016, by decide⟩ ⟨13, 2, 0, 598016, 306328, 949, 16384⟩
    (by decide) selected_cut_23632

theorem selected_cut_23633 : selected 8 ⟨598037, by decide⟩
    (prefixPartial 13 306329) = some ⟨13, 2, 0, 598037, 306329, 1929, 16384⟩ := by
  decide +kernel

theorem context_13_306329_598037 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306329 ⟨598037, by decide⟩ :=
  accepted_of_selected 13 306329 ⟨598037, by decide⟩ ⟨13, 2, 0, 598037, 306329, 1929, 16384⟩
    (by decide) selected_cut_23633

theorem selected_cut_23634 : selected 8 ⟨598053, by decide⟩
    (prefixPartial 13 306330) = some ⟨13, 2, 0, 598053, 306330, 1425, 16384⟩ := by
  decide +kernel

theorem context_13_306330_598053 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306330 ⟨598053, by decide⟩ :=
  accepted_of_selected 13 306330 ⟨598053, by decide⟩ ⟨13, 2, 0, 598053, 306330, 1425, 16384⟩
    (by decide) selected_cut_23634

theorem selected_cut_23635 : selected 8 ⟨598059, by decide⟩
    (prefixPartial 13 306331) = some ⟨13, 2, 0, 598059, 306331, 829, 16384⟩ := by
  decide +kernel

theorem context_13_306331_598059 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306331 ⟨598059, by decide⟩ :=
  accepted_of_selected 13 306331 ⟨598059, by decide⟩ ⟨13, 2, 0, 598059, 306331, 829, 16384⟩
    (by decide) selected_cut_23635

theorem unmarked_context_12_76582_598060 : frontier 9 ⟨598060, by decide⟩
    (prefixCache 12 76582) (prefixPartial 12 76582) = false := by
  decide +kernel

theorem node_context_12_76582_598060 : EJMOriginalGlobalDAGData.nodes 9 ⟨598060, by decide⟩ =
    .split (coordinate 12) (![⟨598016, by decide⟩,⟨598037, by decide⟩,⟨598053, by decide⟩,⟨598059, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76582_598060 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76582 ⟨598060, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76582
    ⟨598060, by decide⟩ (by decide) (![⟨598016, by decide⟩,⟨598037, by decide⟩,⟨598053, by decide⟩,⟨598059, by decide⟩]) unmarked_context_12_76582_598060 node_context_12_76582_598060
  intro a
  fin_cases a
  · exact context_13_306328_598016
  · exact context_13_306329_598037
  · exact context_13_306330_598053
  · exact context_13_306331_598059

theorem selected_cut_23636 : selected 8 ⟨598073, by decide⟩
    (prefixPartial 13 306332) = some ⟨13, 2, 0, 598073, 306332, 817, 16384⟩ := by
  decide +kernel

theorem context_13_306332_598073 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306332 ⟨598073, by decide⟩ :=
  accepted_of_selected 13 306332 ⟨598073, by decide⟩ ⟨13, 2, 0, 598073, 306332, 817, 16384⟩
    (by decide) selected_cut_23636

theorem selected_cut_23637 : selected 8 ⟨598092, by decide⟩
    (prefixPartial 13 306333) = some ⟨13, 2, 0, 598092, 306333, 1717, 16384⟩ := by
  decide +kernel

theorem context_13_306333_598092 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306333 ⟨598092, by decide⟩ :=
  accepted_of_selected 13 306333 ⟨598092, by decide⟩ ⟨13, 2, 0, 598092, 306333, 1717, 16384⟩
    (by decide) selected_cut_23637

theorem selected_cut_23638 : selected 8 ⟨598110, by decide⟩
    (prefixPartial 13 306334) = some ⟨13, 2, 0, 598110, 306334, 1461, 16384⟩ := by
  decide +kernel

theorem context_13_306334_598110 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306334 ⟨598110, by decide⟩ :=
  accepted_of_selected 13 306334 ⟨598110, by decide⟩ ⟨13, 2, 0, 598110, 306334, 1461, 16384⟩
    (by decide) selected_cut_23638

theorem selected_cut_23639 : selected 8 ⟨598114, by decide⟩
    (prefixPartial 13 306335) = some ⟨13, 2, 0, 598114, 306335, 717, 16384⟩ := by
  decide +kernel

theorem context_13_306335_598114 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306335 ⟨598114, by decide⟩ :=
  accepted_of_selected 13 306335 ⟨598114, by decide⟩ ⟨13, 2, 0, 598114, 306335, 717, 16384⟩
    (by decide) selected_cut_23639

theorem unmarked_context_12_76583_598115 : frontier 9 ⟨598115, by decide⟩
    (prefixCache 12 76583) (prefixPartial 12 76583) = false := by
  decide +kernel

theorem node_context_12_76583_598115 : EJMOriginalGlobalDAGData.nodes 9 ⟨598115, by decide⟩ =
    .split (coordinate 12) (![⟨598073, by decide⟩,⟨598092, by decide⟩,⟨598110, by decide⟩,⟨598114, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76583_598115 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76583 ⟨598115, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76583
    ⟨598115, by decide⟩ (by decide) (![⟨598073, by decide⟩,⟨598092, by decide⟩,⟨598110, by decide⟩,⟨598114, by decide⟩]) unmarked_context_12_76583_598115 node_context_12_76583_598115
  intro a
  fin_cases a
  · exact context_13_306332_598073
  · exact context_13_306333_598092
  · exact context_13_306334_598110
  · exact context_13_306335_598114

theorem unmarked_context_11_19145_598116 : frontier 10 ⟨598116, by decide⟩
    (prefixCache 11 19145) (prefixPartial 11 19145) = false := by
  decide +kernel

theorem node_context_11_19145_598116 : EJMOriginalGlobalDAGData.nodes 10 ⟨598116, by decide⟩ =
    .split (coordinate 11) (![⟨597942, by decide⟩,⟨598000, by decide⟩,⟨598060, by decide⟩,⟨598115, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19145_598116 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19145 ⟨598116, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19145
    ⟨598116, by decide⟩ (by decide) (![⟨597942, by decide⟩,⟨598000, by decide⟩,⟨598060, by decide⟩,⟨598115, by decide⟩]) unmarked_context_11_19145_598116 node_context_11_19145_598116
  intro a
  fin_cases a
  · exact context_12_76580_597942
  · exact context_12_76581_598000
  · exact context_12_76582_598060
  · exact context_12_76583_598115

theorem selected_cut_23640 : selected 9 ⟨435790, by decide⟩
    (prefixPartial 12 76584) = some ⟨12, 1, 0, 435790, 76584, 1, 65536⟩ := by
  decide +kernel

theorem context_12_76584_435790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76584 ⟨435790, by decide⟩ :=
  accepted_of_selected 12 76584 ⟨435790, by decide⟩ ⟨12, 1, 0, 435790, 76584, 1, 65536⟩
    (by decide) selected_cut_23640

theorem selected_cut_23641 : selected 8 ⟨598131, by decide⟩
    (prefixPartial 13 306340) = some ⟨13, 2, 0, 598131, 306340, 1125, 16384⟩ := by
  decide +kernel

theorem context_13_306340_598131 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306340 ⟨598131, by decide⟩ :=
  accepted_of_selected 13 306340 ⟨598131, by decide⟩ ⟨13, 2, 0, 598131, 306340, 1125, 16384⟩
    (by decide) selected_cut_23641

theorem selected_cut_23642 : selected 8 ⟨598167, by decide⟩
    (prefixPartial 13 306341) = some ⟨13, 2, 0, 598167, 306341, 2465, 16384⟩ := by
  decide +kernel

theorem context_13_306341_598167 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306341 ⟨598167, by decide⟩ :=
  accepted_of_selected 13 306341 ⟨598167, by decide⟩ ⟨13, 2, 0, 598167, 306341, 2465, 16384⟩
    (by decide) selected_cut_23642

theorem selected_cut_23643 : selected 8 ⟨598189, by decide⟩
    (prefixPartial 13 306342) = some ⟨13, 2, 0, 598189, 306342, 1933, 16384⟩ := by
  decide +kernel

theorem context_13_306342_598189 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306342 ⟨598189, by decide⟩ :=
  accepted_of_selected 13 306342 ⟨598189, by decide⟩ ⟨13, 2, 0, 598189, 306342, 1933, 16384⟩
    (by decide) selected_cut_23643

theorem selected_cut_23644 : selected 8 ⟨598196, by decide⟩
    (prefixPartial 13 306343) = some ⟨13, 2, 0, 598196, 306343, 1017, 16384⟩ := by
  decide +kernel

theorem context_13_306343_598196 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306343 ⟨598196, by decide⟩ :=
  accepted_of_selected 13 306343 ⟨598196, by decide⟩ ⟨13, 2, 0, 598196, 306343, 1017, 16384⟩
    (by decide) selected_cut_23644

theorem unmarked_context_12_76585_598197 : frontier 9 ⟨598197, by decide⟩
    (prefixCache 12 76585) (prefixPartial 12 76585) = false := by
  decide +kernel

theorem node_context_12_76585_598197 : EJMOriginalGlobalDAGData.nodes 9 ⟨598197, by decide⟩ =
    .split (coordinate 12) (![⟨598131, by decide⟩,⟨598167, by decide⟩,⟨598189, by decide⟩,⟨598196, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76585_598197 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76585 ⟨598197, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76585
    ⟨598197, by decide⟩ (by decide) (![⟨598131, by decide⟩,⟨598167, by decide⟩,⟨598189, by decide⟩,⟨598196, by decide⟩]) unmarked_context_12_76585_598197 node_context_12_76585_598197
  intro a
  fin_cases a
  · exact context_13_306340_598131
  · exact context_13_306341_598167
  · exact context_13_306342_598189
  · exact context_13_306343_598196

theorem selected_cut_23645 : selected 9 ⟨474208, by decide⟩
    (prefixPartial 12 76586) = some ⟨12, 1, 0, 474208, 76586, 1, 65536⟩ := by
  decide +kernel

theorem context_12_76586_474208 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76586 ⟨474208, by decide⟩ :=
  accepted_of_selected 12 76586 ⟨474208, by decide⟩ ⟨12, 1, 0, 474208, 76586, 1, 65536⟩
    (by decide) selected_cut_23645

theorem selected_cut_23646 : selected 8 ⟨598211, by decide⟩
    (prefixPartial 13 306348) = some ⟨13, 2, 0, 598211, 306348, 769, 16384⟩ := by
  decide +kernel

theorem context_13_306348_598211 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306348 ⟨598211, by decide⟩ :=
  accepted_of_selected 13 306348 ⟨598211, by decide⟩ ⟨13, 2, 0, 598211, 306348, 769, 16384⟩
    (by decide) selected_cut_23646

theorem selected_cut_23647 : selected 8 ⟨598241, by decide⟩
    (prefixPartial 13 306349) = some ⟨13, 2, 0, 598241, 306349, 2581, 16384⟩ := by
  decide +kernel

theorem context_13_306349_598241 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306349 ⟨598241, by decide⟩ :=
  accepted_of_selected 13 306349 ⟨598241, by decide⟩ ⟨13, 2, 0, 598241, 306349, 2581, 16384⟩
    (by decide) selected_cut_23647

theorem selected_cut_23648 : selected 8 ⟨598259, by decide⟩
    (prefixPartial 13 306350) = some ⟨13, 2, 0, 598259, 306350, 1741, 16384⟩ := by
  decide +kernel

theorem context_13_306350_598259 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306350 ⟨598259, by decide⟩ :=
  accepted_of_selected 13 306350 ⟨598259, by decide⟩ ⟨13, 2, 0, 598259, 306350, 1741, 16384⟩
    (by decide) selected_cut_23648

theorem selected_cut_23649 : selected 8 ⟨598264, by decide⟩
    (prefixPartial 13 306351) = some ⟨13, 2, 0, 598264, 306351, 849, 16384⟩ := by
  decide +kernel

theorem context_13_306351_598264 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306351 ⟨598264, by decide⟩ :=
  accepted_of_selected 13 306351 ⟨598264, by decide⟩ ⟨13, 2, 0, 598264, 306351, 849, 16384⟩
    (by decide) selected_cut_23649

theorem unmarked_context_12_76587_598265 : frontier 9 ⟨598265, by decide⟩
    (prefixCache 12 76587) (prefixPartial 12 76587) = false := by
  decide +kernel

theorem node_context_12_76587_598265 : EJMOriginalGlobalDAGData.nodes 9 ⟨598265, by decide⟩ =
    .split (coordinate 12) (![⟨598211, by decide⟩,⟨598241, by decide⟩,⟨598259, by decide⟩,⟨598264, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76587_598265 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76587 ⟨598265, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76587
    ⟨598265, by decide⟩ (by decide) (![⟨598211, by decide⟩,⟨598241, by decide⟩,⟨598259, by decide⟩,⟨598264, by decide⟩]) unmarked_context_12_76587_598265 node_context_12_76587_598265
  intro a
  fin_cases a
  · exact context_13_306348_598211
  · exact context_13_306349_598241
  · exact context_13_306350_598259
  · exact context_13_306351_598264

theorem unmarked_context_11_19146_598266 : frontier 10 ⟨598266, by decide⟩
    (prefixCache 11 19146) (prefixPartial 11 19146) = false := by
  decide +kernel

theorem node_context_11_19146_598266 : EJMOriginalGlobalDAGData.nodes 10 ⟨598266, by decide⟩ =
    .split (coordinate 11) (![⟨435790, by decide⟩,⟨598197, by decide⟩,⟨474208, by decide⟩,⟨598265, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19146_598266 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19146 ⟨598266, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19146
    ⟨598266, by decide⟩ (by decide) (![⟨435790, by decide⟩,⟨598197, by decide⟩,⟨474208, by decide⟩,⟨598265, by decide⟩]) unmarked_context_11_19146_598266 node_context_11_19146_598266
  intro a
  fin_cases a
  · exact context_12_76584_435790
  · exact context_12_76585_598197
  · exact context_12_76586_474208
  · exact context_12_76587_598265

theorem selected_cut_23650 : selected 9 ⟨510901, by decide⟩
    (prefixPartial 12 76588) = some ⟨12, 1, 0, 510901, 76588, 1, 65536⟩ := by
  decide +kernel

theorem context_12_76588_510901 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76588 ⟨510901, by decide⟩ :=
  accepted_of_selected 12 76588 ⟨510901, by decide⟩ ⟨12, 1, 0, 510901, 76588, 1, 65536⟩
    (by decide) selected_cut_23650

theorem selected_cut_23651 : selected 8 ⟨598276, by decide⟩
    (prefixPartial 13 306356) = some ⟨13, 2, 0, 598276, 306356, 689, 16384⟩ := by
  decide +kernel

theorem context_13_306356_598276 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306356 ⟨598276, by decide⟩ :=
  accepted_of_selected 13 306356 ⟨598276, by decide⟩ ⟨13, 2, 0, 598276, 306356, 689, 16384⟩
    (by decide) selected_cut_23651

theorem selected_cut_23652 : selected 8 ⟨598298, by decide⟩
    (prefixPartial 13 306357) = some ⟨13, 2, 0, 598298, 306357, 1853, 16384⟩ := by
  decide +kernel

theorem context_13_306357_598298 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306357 ⟨598298, by decide⟩ :=
  accepted_of_selected 13 306357 ⟨598298, by decide⟩ ⟨13, 2, 0, 598298, 306357, 1853, 16384⟩
    (by decide) selected_cut_23652

theorem selected_cut_23653 : selected 8 ⟨598313, by decide⟩
    (prefixPartial 13 306358) = some ⟨13, 2, 0, 598313, 306358, 1717, 16384⟩ := by
  decide +kernel

theorem context_13_306358_598313 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306358 ⟨598313, by decide⟩ :=
  accepted_of_selected 13 306358 ⟨598313, by decide⟩ ⟨13, 2, 0, 598313, 306358, 1717, 16384⟩
    (by decide) selected_cut_23653

theorem selected_cut_23654 : selected 8 ⟨598317, by decide⟩
    (prefixPartial 13 306359) = some ⟨13, 2, 0, 598317, 306359, 697, 16384⟩ := by
  decide +kernel

theorem context_13_306359_598317 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306359 ⟨598317, by decide⟩ :=
  accepted_of_selected 13 306359 ⟨598317, by decide⟩ ⟨13, 2, 0, 598317, 306359, 697, 16384⟩
    (by decide) selected_cut_23654

theorem unmarked_context_12_76589_598318 : frontier 9 ⟨598318, by decide⟩
    (prefixCache 12 76589) (prefixPartial 12 76589) = false := by
  decide +kernel

theorem node_context_12_76589_598318 : EJMOriginalGlobalDAGData.nodes 9 ⟨598318, by decide⟩ =
    .split (coordinate 12) (![⟨598276, by decide⟩,⟨598298, by decide⟩,⟨598313, by decide⟩,⟨598317, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76589_598318 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76589 ⟨598318, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76589
    ⟨598318, by decide⟩ (by decide) (![⟨598276, by decide⟩,⟨598298, by decide⟩,⟨598313, by decide⟩,⟨598317, by decide⟩]) unmarked_context_12_76589_598318 node_context_12_76589_598318
  intro a
  fin_cases a
  · exact context_13_306356_598276
  · exact context_13_306357_598298
  · exact context_13_306358_598313
  · exact context_13_306359_598317

theorem selected_cut_23655 : selected 8 ⟨598328, by decide⟩
    (prefixPartial 13 306360) = some ⟨13, 2, 0, 598328, 306360, 577, 16384⟩ := by
  decide +kernel

theorem context_13_306360_598328 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306360 ⟨598328, by decide⟩ :=
  accepted_of_selected 13 306360 ⟨598328, by decide⟩ ⟨13, 2, 0, 598328, 306360, 577, 16384⟩
    (by decide) selected_cut_23655

theorem selected_cut_23656 : selected 8 ⟨598352, by decide⟩
    (prefixPartial 13 306361) = some ⟨13, 2, 0, 598352, 306361, 2249, 16384⟩ := by
  decide +kernel

theorem context_13_306361_598352 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306361 ⟨598352, by decide⟩ :=
  accepted_of_selected 13 306361 ⟨598352, by decide⟩ ⟨13, 2, 0, 598352, 306361, 2249, 16384⟩
    (by decide) selected_cut_23656

theorem selected_cut_23657 : selected 8 ⟨598370, by decide⟩
    (prefixPartial 13 306362) = some ⟨13, 2, 0, 598370, 306362, 1401, 16384⟩ := by
  decide +kernel

theorem context_13_306362_598370 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306362 ⟨598370, by decide⟩ :=
  accepted_of_selected 13 306362 ⟨598370, by decide⟩ ⟨13, 2, 0, 598370, 306362, 1401, 16384⟩
    (by decide) selected_cut_23657

theorem selected_cut_23658 : selected 8 ⟨598374, by decide⟩
    (prefixPartial 13 306363) = some ⟨13, 2, 0, 598374, 306363, 693, 16384⟩ := by
  decide +kernel

theorem context_13_306363_598374 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306363 ⟨598374, by decide⟩ :=
  accepted_of_selected 13 306363 ⟨598374, by decide⟩ ⟨13, 2, 0, 598374, 306363, 693, 16384⟩
    (by decide) selected_cut_23658

theorem unmarked_context_12_76590_598375 : frontier 9 ⟨598375, by decide⟩
    (prefixCache 12 76590) (prefixPartial 12 76590) = false := by
  decide +kernel

theorem node_context_12_76590_598375 : EJMOriginalGlobalDAGData.nodes 9 ⟨598375, by decide⟩ =
    .split (coordinate 12) (![⟨598328, by decide⟩,⟨598352, by decide⟩,⟨598370, by decide⟩,⟨598374, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76590_598375 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76590 ⟨598375, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76590
    ⟨598375, by decide⟩ (by decide) (![⟨598328, by decide⟩,⟨598352, by decide⟩,⟨598370, by decide⟩,⟨598374, by decide⟩]) unmarked_context_12_76590_598375 node_context_12_76590_598375
  intro a
  fin_cases a
  · exact context_13_306360_598328
  · exact context_13_306361_598352
  · exact context_13_306362_598370
  · exact context_13_306363_598374

theorem selected_cut_23659 : selected 8 ⟨598390, by decide⟩
    (prefixPartial 13 306364) = some ⟨13, 2, 0, 598390, 306364, 845, 16384⟩ := by
  decide +kernel

theorem context_13_306364_598390 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306364 ⟨598390, by decide⟩ :=
  accepted_of_selected 13 306364 ⟨598390, by decide⟩ ⟨13, 2, 0, 598390, 306364, 845, 16384⟩
    (by decide) selected_cut_23659

theorem selected_cut_23660 : selected 8 ⟨598428, by decide⟩
    (prefixPartial 13 306365) = some ⟨13, 2, 0, 598428, 306365, 3357, 16384⟩ := by
  decide +kernel

theorem context_13_306365_598428 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306365 ⟨598428, by decide⟩ :=
  accepted_of_selected 13 306365 ⟨598428, by decide⟩ ⟨13, 2, 0, 598428, 306365, 3357, 16384⟩
    (by decide) selected_cut_23660

theorem selected_cut_23661 : selected 8 ⟨598453, by decide⟩
    (prefixPartial 13 306366) = some ⟨13, 2, 0, 598453, 306366, 2321, 16384⟩ := by
  decide +kernel

theorem context_13_306366_598453 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306366 ⟨598453, by decide⟩ :=
  accepted_of_selected 13 306366 ⟨598453, by decide⟩ ⟨13, 2, 0, 598453, 306366, 2321, 16384⟩
    (by decide) selected_cut_23661

theorem selected_cut_23662 : selected 8 ⟨598458, by decide⟩
    (prefixPartial 13 306367) = some ⟨13, 2, 0, 598458, 306367, 969, 16384⟩ := by
  decide +kernel

theorem context_13_306367_598458 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306367 ⟨598458, by decide⟩ :=
  accepted_of_selected 13 306367 ⟨598458, by decide⟩ ⟨13, 2, 0, 598458, 306367, 969, 16384⟩
    (by decide) selected_cut_23662

theorem unmarked_context_12_76591_598459 : frontier 9 ⟨598459, by decide⟩
    (prefixCache 12 76591) (prefixPartial 12 76591) = false := by
  decide +kernel

theorem node_context_12_76591_598459 : EJMOriginalGlobalDAGData.nodes 9 ⟨598459, by decide⟩ =
    .split (coordinate 12) (![⟨598390, by decide⟩,⟨598428, by decide⟩,⟨598453, by decide⟩,⟨598458, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76591_598459 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76591 ⟨598459, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76591
    ⟨598459, by decide⟩ (by decide) (![⟨598390, by decide⟩,⟨598428, by decide⟩,⟨598453, by decide⟩,⟨598458, by decide⟩]) unmarked_context_12_76591_598459 node_context_12_76591_598459
  intro a
  fin_cases a
  · exact context_13_306364_598390
  · exact context_13_306365_598428
  · exact context_13_306366_598453
  · exact context_13_306367_598458

theorem unmarked_context_11_19147_598460 : frontier 10 ⟨598460, by decide⟩
    (prefixCache 11 19147) (prefixPartial 11 19147) = false := by
  decide +kernel

theorem node_context_11_19147_598460 : EJMOriginalGlobalDAGData.nodes 10 ⟨598460, by decide⟩ =
    .split (coordinate 11) (![⟨510901, by decide⟩,⟨598318, by decide⟩,⟨598375, by decide⟩,⟨598459, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19147_598460 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19147 ⟨598460, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19147
    ⟨598460, by decide⟩ (by decide) (![⟨510901, by decide⟩,⟨598318, by decide⟩,⟨598375, by decide⟩,⟨598459, by decide⟩]) unmarked_context_11_19147_598460 node_context_11_19147_598460
  intro a
  fin_cases a
  · exact context_12_76588_510901
  · exact context_12_76589_598318
  · exact context_12_76590_598375
  · exact context_12_76591_598459

theorem unmarked_context_10_4786_598461 : frontier 11 ⟨598461, by decide⟩
    (prefixCache 10 4786) (prefixPartial 10 4786) = false := by
  decide +kernel

theorem node_context_10_4786_598461 : EJMOriginalGlobalDAGData.nodes 11 ⟨598461, by decide⟩ =
    .split (coordinate 10) (![⟨597827, by decide⟩,⟨598116, by decide⟩,⟨598266, by decide⟩,⟨598460, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4786_598461 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4786 ⟨598461, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4786
    ⟨598461, by decide⟩ (by decide) (![⟨597827, by decide⟩,⟨598116, by decide⟩,⟨598266, by decide⟩,⟨598460, by decide⟩]) unmarked_context_10_4786_598461 node_context_10_4786_598461
  intro a
  fin_cases a
  · exact context_11_19144_597827
  · exact context_11_19145_598116
  · exact context_11_19146_598266
  · exact context_11_19147_598460

theorem selected_cut_23663 : selected 9 ⟨445562, by decide⟩
    (prefixPartial 12 76592) = some ⟨12, 1, 0, 445562, 76592, 1, 65536⟩ := by
  decide +kernel

theorem context_12_76592_445562 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76592 ⟨445562, by decide⟩ :=
  accepted_of_selected 12 76592 ⟨445562, by decide⟩ ⟨12, 1, 0, 445562, 76592, 1, 65536⟩
    (by decide) selected_cut_23663

theorem selected_cut_23664 : selected 8 ⟨598469, by decide⟩
    (prefixPartial 13 306372) = some ⟨13, 2, 0, 598469, 306372, 513, 16384⟩ := by
  decide +kernel

theorem context_13_306372_598469 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306372 ⟨598469, by decide⟩ :=
  accepted_of_selected 13 306372 ⟨598469, by decide⟩ ⟨13, 2, 0, 598469, 306372, 513, 16384⟩
    (by decide) selected_cut_23664

theorem selected_cut_23665 : selected 8 ⟨598508, by decide⟩
    (prefixPartial 13 306373) = some ⟨13, 2, 0, 598508, 306373, 2701, 16384⟩ := by
  decide +kernel

theorem context_13_306373_598508 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306373 ⟨598508, by decide⟩ :=
  accepted_of_selected 13 306373 ⟨598508, by decide⟩ ⟨13, 2, 0, 598508, 306373, 2701, 16384⟩
    (by decide) selected_cut_23665

theorem selected_cut_23666 : selected 8 ⟨598528, by decide⟩
    (prefixPartial 13 306374) = some ⟨13, 2, 0, 598528, 306374, 1685, 16384⟩ := by
  decide +kernel

theorem context_13_306374_598528 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306374 ⟨598528, by decide⟩ :=
  accepted_of_selected 13 306374 ⟨598528, by decide⟩ ⟨13, 2, 0, 598528, 306374, 1685, 16384⟩
    (by decide) selected_cut_23666

theorem selected_cut_23667 : selected 8 ⟨598535, by decide⟩
    (prefixPartial 13 306375) = some ⟨13, 2, 0, 598535, 306375, 897, 16384⟩ := by
  decide +kernel

theorem context_13_306375_598535 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306375 ⟨598535, by decide⟩ :=
  accepted_of_selected 13 306375 ⟨598535, by decide⟩ ⟨13, 2, 0, 598535, 306375, 897, 16384⟩
    (by decide) selected_cut_23667

theorem unmarked_context_12_76593_598536 : frontier 9 ⟨598536, by decide⟩
    (prefixCache 12 76593) (prefixPartial 12 76593) = false := by
  decide +kernel

theorem node_context_12_76593_598536 : EJMOriginalGlobalDAGData.nodes 9 ⟨598536, by decide⟩ =
    .split (coordinate 12) (![⟨598469, by decide⟩,⟨598508, by decide⟩,⟨598528, by decide⟩,⟨598535, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76593_598536 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76593 ⟨598536, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76593
    ⟨598536, by decide⟩ (by decide) (![⟨598469, by decide⟩,⟨598508, by decide⟩,⟨598528, by decide⟩,⟨598535, by decide⟩]) unmarked_context_12_76593_598536 node_context_12_76593_598536
  intro a
  fin_cases a
  · exact context_13_306372_598469
  · exact context_13_306373_598508
  · exact context_13_306374_598528
  · exact context_13_306375_598535

theorem selected_cut_23668 : selected 8 ⟨598544, by decide⟩
    (prefixPartial 13 306376) = some ⟨13, 2, 0, 598544, 306376, 493, 16384⟩ := by
  decide +kernel

theorem context_13_306376_598544 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306376 ⟨598544, by decide⟩ :=
  accepted_of_selected 13 306376 ⟨598544, by decide⟩ ⟨13, 2, 0, 598544, 306376, 493, 16384⟩
    (by decide) selected_cut_23668

theorem selected_cut_23669 : selected 8 ⟨598574, by decide⟩
    (prefixPartial 13 306377) = some ⟨13, 2, 0, 598574, 306377, 2621, 16384⟩ := by
  decide +kernel

theorem context_13_306377_598574 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306377 ⟨598574, by decide⟩ :=
  accepted_of_selected 13 306377 ⟨598574, by decide⟩ ⟨13, 2, 0, 598574, 306377, 2621, 16384⟩
    (by decide) selected_cut_23669

theorem selected_cut_23670 : selected 8 ⟨598592, by decide⟩
    (prefixPartial 13 306378) = some ⟨13, 2, 0, 598592, 306378, 1841, 16384⟩ := by
  decide +kernel

theorem context_13_306378_598592 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306378 ⟨598592, by decide⟩ :=
  accepted_of_selected 13 306378 ⟨598592, by decide⟩ ⟨13, 2, 0, 598592, 306378, 1841, 16384⟩
    (by decide) selected_cut_23670

theorem selected_cut_23671 : selected 8 ⟨598596, by decide⟩
    (prefixPartial 13 306379) = some ⟨13, 2, 0, 598596, 306379, 849, 16384⟩ := by
  decide +kernel

theorem context_13_306379_598596 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306379 ⟨598596, by decide⟩ :=
  accepted_of_selected 13 306379 ⟨598596, by decide⟩ ⟨13, 2, 0, 598596, 306379, 849, 16384⟩
    (by decide) selected_cut_23671

theorem unmarked_context_12_76594_598597 : frontier 9 ⟨598597, by decide⟩
    (prefixCache 12 76594) (prefixPartial 12 76594) = false := by
  decide +kernel

theorem node_context_12_76594_598597 : EJMOriginalGlobalDAGData.nodes 9 ⟨598597, by decide⟩ =
    .split (coordinate 12) (![⟨598544, by decide⟩,⟨598574, by decide⟩,⟨598592, by decide⟩,⟨598596, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76594_598597 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76594 ⟨598597, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76594
    ⟨598597, by decide⟩ (by decide) (![⟨598544, by decide⟩,⟨598574, by decide⟩,⟨598592, by decide⟩,⟨598596, by decide⟩]) unmarked_context_12_76594_598597 node_context_12_76594_598597
  intro a
  fin_cases a
  · exact context_13_306376_598544
  · exact context_13_306377_598574
  · exact context_13_306378_598592
  · exact context_13_306379_598596

theorem selected_cut_23672 : selected 8 ⟨598603, by decide⟩
    (prefixPartial 13 306380) = some ⟨13, 2, 0, 598603, 306380, 385, 16384⟩ := by
  decide +kernel

theorem context_13_306380_598603 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306380 ⟨598603, by decide⟩ :=
  accepted_of_selected 13 306380 ⟨598603, by decide⟩ ⟨13, 2, 0, 598603, 306380, 385, 16384⟩
    (by decide) selected_cut_23672

theorem selected_cut_23673 : selected 8 ⟨598626, by decide⟩
    (prefixPartial 13 306381) = some ⟨13, 2, 0, 598626, 306381, 2209, 16384⟩ := by
  decide +kernel

theorem context_13_306381_598626 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306381 ⟨598626, by decide⟩ :=
  accepted_of_selected 13 306381 ⟨598626, by decide⟩ ⟨13, 2, 0, 598626, 306381, 2209, 16384⟩
    (by decide) selected_cut_23673

theorem selected_cut_23674 : selected 8 ⟨598644, by decide⟩
    (prefixPartial 13 306382) = some ⟨13, 2, 0, 598644, 306382, 1609, 16384⟩ := by
  decide +kernel

theorem context_13_306382_598644 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306382 ⟨598644, by decide⟩ :=
  accepted_of_selected 13 306382 ⟨598644, by decide⟩ ⟨13, 2, 0, 598644, 306382, 1609, 16384⟩
    (by decide) selected_cut_23674

theorem selected_cut_23675 : selected 8 ⟨598650, by decide⟩
    (prefixPartial 13 306383) = some ⟨13, 2, 0, 598650, 306383, 713, 16384⟩ := by
  decide +kernel

theorem context_13_306383_598650 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306383 ⟨598650, by decide⟩ :=
  accepted_of_selected 13 306383 ⟨598650, by decide⟩ ⟨13, 2, 0, 598650, 306383, 713, 16384⟩
    (by decide) selected_cut_23675

theorem unmarked_context_12_76595_598651 : frontier 9 ⟨598651, by decide⟩
    (prefixCache 12 76595) (prefixPartial 12 76595) = false := by
  decide +kernel

theorem node_context_12_76595_598651 : EJMOriginalGlobalDAGData.nodes 9 ⟨598651, by decide⟩ =
    .split (coordinate 12) (![⟨598603, by decide⟩,⟨598626, by decide⟩,⟨598644, by decide⟩,⟨598650, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76595_598651 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76595 ⟨598651, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76595
    ⟨598651, by decide⟩ (by decide) (![⟨598603, by decide⟩,⟨598626, by decide⟩,⟨598644, by decide⟩,⟨598650, by decide⟩]) unmarked_context_12_76595_598651 node_context_12_76595_598651
  intro a
  fin_cases a
  · exact context_13_306380_598603
  · exact context_13_306381_598626
  · exact context_13_306382_598644
  · exact context_13_306383_598650

theorem unmarked_context_11_19148_598652 : frontier 10 ⟨598652, by decide⟩
    (prefixCache 11 19148) (prefixPartial 11 19148) = false := by
  decide +kernel

theorem node_context_11_19148_598652 : EJMOriginalGlobalDAGData.nodes 10 ⟨598652, by decide⟩ =
    .split (coordinate 11) (![⟨445562, by decide⟩,⟨598536, by decide⟩,⟨598597, by decide⟩,⟨598651, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19148_598652 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19148 ⟨598652, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19148
    ⟨598652, by decide⟩ (by decide) (![⟨445562, by decide⟩,⟨598536, by decide⟩,⟨598597, by decide⟩,⟨598651, by decide⟩]) unmarked_context_11_19148_598652 node_context_11_19148_598652
  intro a
  fin_cases a
  · exact context_12_76592_445562
  · exact context_12_76593_598536
  · exact context_12_76594_598597
  · exact context_12_76595_598651

theorem selected_cut_23676 : selected 9 ⟨475533, by decide⟩
    (prefixPartial 12 76596) = some ⟨12, 1, 0, 475533, 76596, 1, 65536⟩ := by
  decide +kernel

theorem context_12_76596_475533 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76596 ⟨475533, by decide⟩ :=
  accepted_of_selected 12 76596 ⟨475533, by decide⟩ ⟨12, 1, 0, 475533, 76596, 1, 65536⟩
    (by decide) selected_cut_23676

theorem selected_cut_23677 : selected 8 ⟨598657, by decide⟩
    (prefixPartial 13 306388) = some ⟨13, 2, 0, 598657, 306388, 333, 16384⟩ := by
  decide +kernel

theorem context_13_306388_598657 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306388 ⟨598657, by decide⟩ :=
  accepted_of_selected 13 306388 ⟨598657, by decide⟩ ⟨13, 2, 0, 598657, 306388, 333, 16384⟩
    (by decide) selected_cut_23677

theorem selected_cut_23678 : selected 8 ⟨598687, by decide⟩
    (prefixPartial 13 306389) = some ⟨13, 2, 0, 598687, 306389, 2445, 16384⟩ := by
  decide +kernel

theorem context_13_306389_598687 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306389 ⟨598687, by decide⟩ :=
  accepted_of_selected 13 306389 ⟨598687, by decide⟩ ⟨13, 2, 0, 598687, 306389, 2445, 16384⟩
    (by decide) selected_cut_23678

theorem selected_cut_23679 : selected 8 ⟨598705, by decide⟩
    (prefixPartial 13 306390) = some ⟨13, 2, 0, 598705, 306390, 1665, 16384⟩ := by
  decide +kernel

theorem context_13_306390_598705 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306390 ⟨598705, by decide⟩ :=
  accepted_of_selected 13 306390 ⟨598705, by decide⟩ ⟨13, 2, 0, 598705, 306390, 1665, 16384⟩
    (by decide) selected_cut_23679

theorem selected_cut_23680 : selected 8 ⟨598711, by decide⟩
    (prefixPartial 13 306391) = some ⟨13, 2, 0, 598711, 306391, 1013, 16384⟩ := by
  decide +kernel

theorem context_13_306391_598711 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306391 ⟨598711, by decide⟩ :=
  accepted_of_selected 13 306391 ⟨598711, by decide⟩ ⟨13, 2, 0, 598711, 306391, 1013, 16384⟩
    (by decide) selected_cut_23680

theorem unmarked_context_12_76597_598712 : frontier 9 ⟨598712, by decide⟩
    (prefixCache 12 76597) (prefixPartial 12 76597) = false := by
  decide +kernel

theorem node_context_12_76597_598712 : EJMOriginalGlobalDAGData.nodes 9 ⟨598712, by decide⟩ =
    .split (coordinate 12) (![⟨598657, by decide⟩,⟨598687, by decide⟩,⟨598705, by decide⟩,⟨598711, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76597_598712 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76597 ⟨598712, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76597
    ⟨598712, by decide⟩ (by decide) (![⟨598657, by decide⟩,⟨598687, by decide⟩,⟨598705, by decide⟩,⟨598711, by decide⟩]) unmarked_context_12_76597_598712 node_context_12_76597_598712
  intro a
  fin_cases a
  · exact context_13_306388_598657
  · exact context_13_306389_598687
  · exact context_13_306390_598705
  · exact context_13_306391_598711

theorem selected_cut_23681 : selected 8 ⟨598719, by decide⟩
    (prefixPartial 13 306392) = some ⟨13, 2, 0, 598719, 306392, 341, 16384⟩ := by
  decide +kernel

theorem context_13_306392_598719 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306392 ⟨598719, by decide⟩ :=
  accepted_of_selected 13 306392 ⟨598719, by decide⟩ ⟨13, 2, 0, 598719, 306392, 341, 16384⟩
    (by decide) selected_cut_23681

theorem selected_cut_23682 : selected 8 ⟨598746, by decide⟩
    (prefixPartial 13 306393) = some ⟨13, 2, 0, 598746, 306393, 2549, 16384⟩ := by
  decide +kernel

theorem context_13_306393_598746 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306393 ⟨598746, by decide⟩ :=
  accepted_of_selected 13 306393 ⟨598746, by decide⟩ ⟨13, 2, 0, 598746, 306393, 2549, 16384⟩
    (by decide) selected_cut_23682

theorem selected_cut_23683 : selected 8 ⟨598763, by decide⟩
    (prefixPartial 13 306394) = some ⟨13, 2, 0, 598763, 306394, 1753, 16384⟩ := by
  decide +kernel

theorem context_13_306394_598763 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306394 ⟨598763, by decide⟩ :=
  accepted_of_selected 13 306394 ⟨598763, by decide⟩ ⟨13, 2, 0, 598763, 306394, 1753, 16384⟩
    (by decide) selected_cut_23683

theorem selected_cut_23684 : selected 8 ⟨598770, by decide⟩
    (prefixPartial 13 306395) = some ⟨13, 2, 0, 598770, 306395, 1001, 16384⟩ := by
  decide +kernel

theorem context_13_306395_598770 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306395 ⟨598770, by decide⟩ :=
  accepted_of_selected 13 306395 ⟨598770, by decide⟩ ⟨13, 2, 0, 598770, 306395, 1001, 16384⟩
    (by decide) selected_cut_23684

theorem unmarked_context_12_76598_598771 : frontier 9 ⟨598771, by decide⟩
    (prefixCache 12 76598) (prefixPartial 12 76598) = false := by
  decide +kernel

theorem node_context_12_76598_598771 : EJMOriginalGlobalDAGData.nodes 9 ⟨598771, by decide⟩ =
    .split (coordinate 12) (![⟨598719, by decide⟩,⟨598746, by decide⟩,⟨598763, by decide⟩,⟨598770, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76598_598771 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76598 ⟨598771, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76598
    ⟨598771, by decide⟩ (by decide) (![⟨598719, by decide⟩,⟨598746, by decide⟩,⟨598763, by decide⟩,⟨598770, by decide⟩]) unmarked_context_12_76598_598771 node_context_12_76598_598771
  intro a
  fin_cases a
  · exact context_13_306392_598719
  · exact context_13_306393_598746
  · exact context_13_306394_598763
  · exact context_13_306395_598770

theorem selected_cut_23685 : selected 8 ⟨598776, by decide⟩
    (prefixPartial 13 306396) = some ⟨13, 2, 0, 598776, 306396, 245, 16384⟩ := by
  decide +kernel

theorem context_13_306396_598776 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306396 ⟨598776, by decide⟩ :=
  accepted_of_selected 13 306396 ⟨598776, by decide⟩ ⟨13, 2, 0, 598776, 306396, 245, 16384⟩
    (by decide) selected_cut_23685

theorem selected_cut_23686 : selected 8 ⟨598799, by decide⟩
    (prefixPartial 13 306397) = some ⟨13, 2, 0, 598799, 306397, 2137, 16384⟩ := by
  decide +kernel

theorem context_13_306397_598799 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306397 ⟨598799, by decide⟩ :=
  accepted_of_selected 13 306397 ⟨598799, by decide⟩ ⟨13, 2, 0, 598799, 306397, 2137, 16384⟩
    (by decide) selected_cut_23686

theorem selected_cut_23687 : selected 8 ⟨598818, by decide⟩
    (prefixPartial 13 306398) = some ⟨13, 2, 0, 598818, 306398, 1661, 16384⟩ := by
  decide +kernel

theorem context_13_306398_598818 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306398 ⟨598818, by decide⟩ :=
  accepted_of_selected 13 306398 ⟨598818, by decide⟩ ⟨13, 2, 0, 598818, 306398, 1661, 16384⟩
    (by decide) selected_cut_23687

theorem selected_cut_23688 : selected 8 ⟨598822, by decide⟩
    (prefixPartial 13 306399) = some ⟨13, 2, 0, 598822, 306399, 889, 16384⟩ := by
  decide +kernel

theorem context_13_306399_598822 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306399 ⟨598822, by decide⟩ :=
  accepted_of_selected 13 306399 ⟨598822, by decide⟩ ⟨13, 2, 0, 598822, 306399, 889, 16384⟩
    (by decide) selected_cut_23688

theorem unmarked_context_12_76599_598823 : frontier 9 ⟨598823, by decide⟩
    (prefixCache 12 76599) (prefixPartial 12 76599) = false := by
  decide +kernel

theorem node_context_12_76599_598823 : EJMOriginalGlobalDAGData.nodes 9 ⟨598823, by decide⟩ =
    .split (coordinate 12) (![⟨598776, by decide⟩,⟨598799, by decide⟩,⟨598818, by decide⟩,⟨598822, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76599_598823 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76599 ⟨598823, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76599
    ⟨598823, by decide⟩ (by decide) (![⟨598776, by decide⟩,⟨598799, by decide⟩,⟨598818, by decide⟩,⟨598822, by decide⟩]) unmarked_context_12_76599_598823 node_context_12_76599_598823
  intro a
  fin_cases a
  · exact context_13_306396_598776
  · exact context_13_306397_598799
  · exact context_13_306398_598818
  · exact context_13_306399_598822

theorem unmarked_context_11_19149_598824 : frontier 10 ⟨598824, by decide⟩
    (prefixCache 11 19149) (prefixPartial 11 19149) = false := by
  decide +kernel

theorem node_context_11_19149_598824 : EJMOriginalGlobalDAGData.nodes 10 ⟨598824, by decide⟩ =
    .split (coordinate 11) (![⟨475533, by decide⟩,⟨598712, by decide⟩,⟨598771, by decide⟩,⟨598823, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19149_598824 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19149 ⟨598824, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19149
    ⟨598824, by decide⟩ (by decide) (![⟨475533, by decide⟩,⟨598712, by decide⟩,⟨598771, by decide⟩,⟨598823, by decide⟩]) unmarked_context_11_19149_598824 node_context_11_19149_598824
  intro a
  fin_cases a
  · exact context_12_76596_475533
  · exact context_12_76597_598712
  · exact context_12_76598_598771
  · exact context_12_76599_598823

theorem selected_cut_23689 : selected 9 ⟨540780, by decide⟩
    (prefixPartial 12 76600) = some ⟨12, 1, 0, 540780, 76600, 1, 65536⟩ := by
  decide +kernel

theorem context_12_76600_540780 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76600 ⟨540780, by decide⟩ :=
  accepted_of_selected 12 76600 ⟨540780, by decide⟩ ⟨12, 1, 0, 540780, 76600, 1, 65536⟩
    (by decide) selected_cut_23689

theorem selected_cut_23690 : selected 8 ⟨598828, by decide⟩
    (prefixPartial 13 306404) = some ⟨13, 2, 0, 598828, 306404, 229, 16384⟩ := by
  decide +kernel

theorem context_13_306404_598828 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306404 ⟨598828, by decide⟩ :=
  accepted_of_selected 13 306404 ⟨598828, by decide⟩ ⟨13, 2, 0, 598828, 306404, 229, 16384⟩
    (by decide) selected_cut_23690

theorem selected_cut_23691 : selected 8 ⟨598866, by decide⟩
    (prefixPartial 13 306405) = some ⟨13, 2, 0, 598866, 306405, 2441, 16384⟩ := by
  decide +kernel

theorem context_13_306405_598866 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306405 ⟨598866, by decide⟩ :=
  accepted_of_selected 13 306405 ⟨598866, by decide⟩ ⟨13, 2, 0, 598866, 306405, 2441, 16384⟩
    (by decide) selected_cut_23691

theorem selected_cut_23692 : selected 8 ⟨598882, by decide⟩
    (prefixPartial 13 306406) = some ⟨13, 2, 0, 598882, 306406, 1457, 16384⟩ := by
  decide +kernel

theorem context_13_306406_598882 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306406 ⟨598882, by decide⟩ :=
  accepted_of_selected 13 306406 ⟨598882, by decide⟩ ⟨13, 2, 0, 598882, 306406, 1457, 16384⟩
    (by decide) selected_cut_23692

theorem selected_cut_23693 : selected 8 ⟨598895, by decide⟩
    (prefixPartial 13 306407) = some ⟨13, 2, 0, 598895, 306407, 1057, 16384⟩ := by
  decide +kernel

theorem context_13_306407_598895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306407 ⟨598895, by decide⟩ :=
  accepted_of_selected 13 306407 ⟨598895, by decide⟩ ⟨13, 2, 0, 598895, 306407, 1057, 16384⟩
    (by decide) selected_cut_23693

theorem unmarked_context_12_76601_598896 : frontier 9 ⟨598896, by decide⟩
    (prefixCache 12 76601) (prefixPartial 12 76601) = false := by
  decide +kernel

theorem node_context_12_76601_598896 : EJMOriginalGlobalDAGData.nodes 9 ⟨598896, by decide⟩ =
    .split (coordinate 12) (![⟨598828, by decide⟩,⟨598866, by decide⟩,⟨598882, by decide⟩,⟨598895, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76601_598896 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76601 ⟨598896, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76601
    ⟨598896, by decide⟩ (by decide) (![⟨598828, by decide⟩,⟨598866, by decide⟩,⟨598882, by decide⟩,⟨598895, by decide⟩]) unmarked_context_12_76601_598896 node_context_12_76601_598896
  intro a
  fin_cases a
  · exact context_13_306404_598828
  · exact context_13_306405_598866
  · exact context_13_306406_598882
  · exact context_13_306407_598895

theorem selected_cut_23694 : selected 8 ⟨598899, by decide⟩
    (prefixPartial 13 306408) = some ⟨13, 2, 0, 598899, 306408, 177, 16384⟩ := by
  decide +kernel

theorem context_13_306408_598899 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306408 ⟨598899, by decide⟩ :=
  accepted_of_selected 13 306408 ⟨598899, by decide⟩ ⟨13, 2, 0, 598899, 306408, 177, 16384⟩
    (by decide) selected_cut_23694

theorem selected_cut_23695 : selected 8 ⟨598931, by decide⟩
    (prefixPartial 13 306409) = some ⟨13, 2, 0, 598931, 306409, 2481, 16384⟩ := by
  decide +kernel

theorem context_13_306409_598931 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306409 ⟨598931, by decide⟩ :=
  accepted_of_selected 13 306409 ⟨598931, by decide⟩ ⟨13, 2, 0, 598931, 306409, 2481, 16384⟩
    (by decide) selected_cut_23695

theorem selected_cut_23696 : selected 8 ⟨598950, by decide⟩
    (prefixPartial 13 306410) = some ⟨13, 2, 0, 598950, 306410, 1521, 16384⟩ := by
  decide +kernel

theorem context_13_306410_598950 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306410 ⟨598950, by decide⟩ :=
  accepted_of_selected 13 306410 ⟨598950, by decide⟩ ⟨13, 2, 0, 598950, 306410, 1521, 16384⟩
    (by decide) selected_cut_23696

theorem selected_cut_23697 : selected 8 ⟨598958, by decide⟩
    (prefixPartial 13 306411) = some ⟨13, 2, 0, 598958, 306411, 925, 16384⟩ := by
  decide +kernel

theorem context_13_306411_598958 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306411 ⟨598958, by decide⟩ :=
  accepted_of_selected 13 306411 ⟨598958, by decide⟩ ⟨13, 2, 0, 598958, 306411, 925, 16384⟩
    (by decide) selected_cut_23697

theorem unmarked_context_12_76602_598959 : frontier 9 ⟨598959, by decide⟩
    (prefixCache 12 76602) (prefixPartial 12 76602) = false := by
  decide +kernel

theorem node_context_12_76602_598959 : EJMOriginalGlobalDAGData.nodes 9 ⟨598959, by decide⟩ =
    .split (coordinate 12) (![⟨598899, by decide⟩,⟨598931, by decide⟩,⟨598950, by decide⟩,⟨598958, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76602_598959 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76602 ⟨598959, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76602
    ⟨598959, by decide⟩ (by decide) (![⟨598899, by decide⟩,⟨598931, by decide⟩,⟨598950, by decide⟩,⟨598958, by decide⟩]) unmarked_context_12_76602_598959 node_context_12_76602_598959
  intro a
  fin_cases a
  · exact context_13_306408_598899
  · exact context_13_306409_598931
  · exact context_13_306410_598950
  · exact context_13_306411_598958

theorem selected_cut_23698 : selected 8 ⟨598963, by decide⟩
    (prefixPartial 13 306412) = some ⟨13, 2, 0, 598963, 306412, 121, 16384⟩ := by
  decide +kernel

theorem context_13_306412_598963 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306412 ⟨598963, by decide⟩ :=
  accepted_of_selected 13 306412 ⟨598963, by decide⟩ ⟨13, 2, 0, 598963, 306412, 121, 16384⟩
    (by decide) selected_cut_23698

theorem selected_cut_23699 : selected 8 ⟨598988, by decide⟩
    (prefixPartial 13 306413) = some ⟨13, 2, 0, 598988, 306413, 2149, 16384⟩ := by
  decide +kernel

theorem context_13_306413_598988 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306413 ⟨598988, by decide⟩ :=
  accepted_of_selected 13 306413 ⟨598988, by decide⟩ ⟨13, 2, 0, 598988, 306413, 2149, 16384⟩
    (by decide) selected_cut_23699

theorem selected_cut_23700 : selected 8 ⟨599007, by decide⟩
    (prefixPartial 13 306414) = some ⟨13, 2, 0, 599007, 306414, 1293, 16384⟩ := by
  decide +kernel

theorem context_13_306414_599007 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306414 ⟨599007, by decide⟩ :=
  accepted_of_selected 13 306414 ⟨599007, by decide⟩ ⟨13, 2, 0, 599007, 306414, 1293, 16384⟩
    (by decide) selected_cut_23700

theorem selected_cut_23701 : selected 8 ⟨599014, by decide⟩
    (prefixPartial 13 306415) = some ⟨13, 2, 0, 599014, 306415, 785, 16384⟩ := by
  decide +kernel

theorem context_13_306415_599014 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306415 ⟨599014, by decide⟩ :=
  accepted_of_selected 13 306415 ⟨599014, by decide⟩ ⟨13, 2, 0, 599014, 306415, 785, 16384⟩
    (by decide) selected_cut_23701

theorem unmarked_context_12_76603_599015 : frontier 9 ⟨599015, by decide⟩
    (prefixCache 12 76603) (prefixPartial 12 76603) = false := by
  decide +kernel

theorem node_context_12_76603_599015 : EJMOriginalGlobalDAGData.nodes 9 ⟨599015, by decide⟩ =
    .split (coordinate 12) (![⟨598963, by decide⟩,⟨598988, by decide⟩,⟨599007, by decide⟩,⟨599014, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76603_599015 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76603 ⟨599015, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76603
    ⟨599015, by decide⟩ (by decide) (![⟨598963, by decide⟩,⟨598988, by decide⟩,⟨599007, by decide⟩,⟨599014, by decide⟩]) unmarked_context_12_76603_599015 node_context_12_76603_599015
  intro a
  fin_cases a
  · exact context_13_306412_598963
  · exact context_13_306413_598988
  · exact context_13_306414_599007
  · exact context_13_306415_599014

theorem unmarked_context_11_19150_599016 : frontier 10 ⟨599016, by decide⟩
    (prefixCache 11 19150) (prefixPartial 11 19150) = false := by
  decide +kernel

theorem node_context_11_19150_599016 : EJMOriginalGlobalDAGData.nodes 10 ⟨599016, by decide⟩ =
    .split (coordinate 11) (![⟨540780, by decide⟩,⟨598896, by decide⟩,⟨598959, by decide⟩,⟨599015, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19150_599016 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19150 ⟨599016, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19150
    ⟨599016, by decide⟩ (by decide) (![⟨540780, by decide⟩,⟨598896, by decide⟩,⟨598959, by decide⟩,⟨599015, by decide⟩]) unmarked_context_11_19150_599016 node_context_11_19150_599016
  intro a
  fin_cases a
  · exact context_12_76600_540780
  · exact context_12_76601_598896
  · exact context_12_76602_598959
  · exact context_12_76603_599015

theorem selected_cut_23702 : selected 9 ⟨445562, by decide⟩
    (prefixPartial 12 76604) = some ⟨12, 1, 0, 445562, 76604, 1, 65536⟩ := by
  decide +kernel

theorem context_12_76604_445562 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76604 ⟨445562, by decide⟩ :=
  accepted_of_selected 12 76604 ⟨445562, by decide⟩ ⟨12, 1, 0, 445562, 76604, 1, 65536⟩
    (by decide) selected_cut_23702

theorem selected_cut_23703 : selected 8 ⟨599020, by decide⟩
    (prefixPartial 13 306420) = some ⟨13, 2, 0, 599020, 306420, 105, 16384⟩ := by
  decide +kernel

theorem context_13_306420_599020 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306420 ⟨599020, by decide⟩ :=
  accepted_of_selected 13 306420 ⟨599020, by decide⟩ ⟨13, 2, 0, 599020, 306420, 105, 16384⟩
    (by decide) selected_cut_23703

theorem selected_cut_23704 : selected 8 ⟨599049, by decide⟩
    (prefixPartial 13 306421) = some ⟨13, 2, 0, 599049, 306421, 2605, 16384⟩ := by
  decide +kernel

theorem context_13_306421_599049 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306421 ⟨599049, by decide⟩ :=
  accepted_of_selected 13 306421 ⟨599049, by decide⟩ ⟨13, 2, 0, 599049, 306421, 2605, 16384⟩
    (by decide) selected_cut_23704

theorem selected_cut_23705 : selected 8 ⟨599067, by decide⟩
    (prefixPartial 13 306422) = some ⟨13, 2, 0, 599067, 306422, 1665, 16384⟩ := by
  decide +kernel

theorem context_13_306422_599067 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306422 ⟨599067, by decide⟩ :=
  accepted_of_selected 13 306422 ⟨599067, by decide⟩ ⟨13, 2, 0, 599067, 306422, 1665, 16384⟩
    (by decide) selected_cut_23705

theorem selected_cut_23706 : selected 8 ⟨599071, by decide⟩
    (prefixPartial 13 306423) = some ⟨13, 2, 0, 599071, 306423, 929, 16384⟩ := by
  decide +kernel

theorem context_13_306423_599071 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306423 ⟨599071, by decide⟩ :=
  accepted_of_selected 13 306423 ⟨599071, by decide⟩ ⟨13, 2, 0, 599071, 306423, 929, 16384⟩
    (by decide) selected_cut_23706

theorem unmarked_context_12_76605_599072 : frontier 9 ⟨599072, by decide⟩
    (prefixCache 12 76605) (prefixPartial 12 76605) = false := by
  decide +kernel

theorem node_context_12_76605_599072 : EJMOriginalGlobalDAGData.nodes 9 ⟨599072, by decide⟩ =
    .split (coordinate 12) (![⟨599020, by decide⟩,⟨599049, by decide⟩,⟨599067, by decide⟩,⟨599071, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76605_599072 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76605 ⟨599072, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76605
    ⟨599072, by decide⟩ (by decide) (![⟨599020, by decide⟩,⟨599049, by decide⟩,⟨599067, by decide⟩,⟨599071, by decide⟩]) unmarked_context_12_76605_599072 node_context_12_76605_599072
  intro a
  fin_cases a
  · exact context_13_306420_599020
  · exact context_13_306421_599049
  · exact context_13_306422_599067
  · exact context_13_306423_599071

theorem selected_cut_23707 : selected 8 ⟨599075, by decide⟩
    (prefixPartial 13 306424) = some ⟨13, 2, 0, 599075, 306424, 53, 16384⟩ := by
  decide +kernel

theorem context_13_306424_599075 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306424 ⟨599075, by decide⟩ :=
  accepted_of_selected 13 306424 ⟨599075, by decide⟩ ⟨13, 2, 0, 599075, 306424, 53, 16384⟩
    (by decide) selected_cut_23707

theorem selected_cut_23708 : selected 8 ⟨599110, by decide⟩
    (prefixPartial 13 306425) = some ⟨13, 2, 0, 599110, 306425, 2865, 16384⟩ := by
  decide +kernel

theorem context_13_306425_599110 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306425 ⟨599110, by decide⟩ :=
  accepted_of_selected 13 306425 ⟨599110, by decide⟩ ⟨13, 2, 0, 599110, 306425, 2865, 16384⟩
    (by decide) selected_cut_23708

theorem selected_cut_23709 : selected 8 ⟨599129, by decide⟩
    (prefixPartial 13 306426) = some ⟨13, 2, 0, 599129, 306426, 1621, 16384⟩ := by
  decide +kernel

theorem context_13_306426_599129 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306426 ⟨599129, by decide⟩ :=
  accepted_of_selected 13 306426 ⟨599129, by decide⟩ ⟨13, 2, 0, 599129, 306426, 1621, 16384⟩
    (by decide) selected_cut_23709

theorem selected_cut_23710 : selected 8 ⟨599134, by decide⟩
    (prefixPartial 13 306427) = some ⟨13, 2, 0, 599134, 306427, 905, 16384⟩ := by
  decide +kernel

theorem context_13_306427_599134 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306427 ⟨599134, by decide⟩ :=
  accepted_of_selected 13 306427 ⟨599134, by decide⟩ ⟨13, 2, 0, 599134, 306427, 905, 16384⟩
    (by decide) selected_cut_23710

theorem unmarked_context_12_76606_599135 : frontier 9 ⟨599135, by decide⟩
    (prefixCache 12 76606) (prefixPartial 12 76606) = false := by
  decide +kernel

theorem node_context_12_76606_599135 : EJMOriginalGlobalDAGData.nodes 9 ⟨599135, by decide⟩ =
    .split (coordinate 12) (![⟨599075, by decide⟩,⟨599110, by decide⟩,⟨599129, by decide⟩,⟨599134, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76606_599135 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76606 ⟨599135, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76606
    ⟨599135, by decide⟩ (by decide) (![⟨599075, by decide⟩,⟨599110, by decide⟩,⟨599129, by decide⟩,⟨599134, by decide⟩]) unmarked_context_12_76606_599135 node_context_12_76606_599135
  intro a
  fin_cases a
  · exact context_13_306424_599075
  · exact context_13_306425_599110
  · exact context_13_306426_599129
  · exact context_13_306427_599134

theorem selected_cut_23711 : selected 9 ⟨512556, by decide⟩
    (prefixPartial 12 76607) = some ⟨12, 1, 0, 512556, 76607, 1, 65536⟩ := by
  decide +kernel

theorem context_12_76607_512556 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76607 ⟨512556, by decide⟩ :=
  accepted_of_selected 12 76607 ⟨512556, by decide⟩ ⟨12, 1, 0, 512556, 76607, 1, 65536⟩
    (by decide) selected_cut_23711

theorem unmarked_context_11_19151_599136 : frontier 10 ⟨599136, by decide⟩
    (prefixCache 11 19151) (prefixPartial 11 19151) = false := by
  decide +kernel

theorem node_context_11_19151_599136 : EJMOriginalGlobalDAGData.nodes 10 ⟨599136, by decide⟩ =
    .split (coordinate 11) (![⟨445562, by decide⟩,⟨599072, by decide⟩,⟨599135, by decide⟩,⟨512556, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19151_599136 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19151 ⟨599136, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19151
    ⟨599136, by decide⟩ (by decide) (![⟨445562, by decide⟩,⟨599072, by decide⟩,⟨599135, by decide⟩,⟨512556, by decide⟩]) unmarked_context_11_19151_599136 node_context_11_19151_599136
  intro a
  fin_cases a
  · exact context_12_76604_445562
  · exact context_12_76605_599072
  · exact context_12_76606_599135
  · exact context_12_76607_512556

theorem unmarked_context_10_4787_599137 : frontier 11 ⟨599137, by decide⟩
    (prefixCache 10 4787) (prefixPartial 10 4787) = false := by
  decide +kernel

theorem node_context_10_4787_599137 : EJMOriginalGlobalDAGData.nodes 11 ⟨599137, by decide⟩ =
    .split (coordinate 10) (![⟨598652, by decide⟩,⟨598824, by decide⟩,⟨599016, by decide⟩,⟨599136, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4787_599137 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4787 ⟨599137, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4787
    ⟨599137, by decide⟩ (by decide) (![⟨598652, by decide⟩,⟨598824, by decide⟩,⟨599016, by decide⟩,⟨599136, by decide⟩]) unmarked_context_10_4787_599137 node_context_10_4787_599137
  intro a
  fin_cases a
  · exact context_11_19148_598652
  · exact context_11_19149_598824
  · exact context_11_19150_599016
  · exact context_11_19151_599136

theorem unmarked_context_9_1196_599138 : frontier 12 ⟨599138, by decide⟩
    (prefixCache 9 1196) (prefixPartial 9 1196) = false := by
  decide +kernel

theorem node_context_9_1196_599138 : EJMOriginalGlobalDAGData.nodes 12 ⟨599138, by decide⟩ =
    .split (coordinate 9) (![⟨596221, by decide⟩,⟨597630, by decide⟩,⟨598461, by decide⟩,⟨599137, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1196_599138 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1196 ⟨599138, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1196
    ⟨599138, by decide⟩ (by decide) (![⟨596221, by decide⟩,⟨597630, by decide⟩,⟨598461, by decide⟩,⟨599137, by decide⟩]) unmarked_context_9_1196_599138 node_context_9_1196_599138
  intro a
  fin_cases a
  · exact context_10_4784_596221
  · exact context_10_4785_597630
  · exact context_10_4786_598461
  · exact context_10_4787_599137

theorem selected_cut_23712 : selected 9 ⟨599183, by decide⟩
    (prefixPartial 12 76608) = some ⟨12, 2, 0, 599183, 76608, 3917, 65536⟩ := by
  decide +kernel

theorem context_12_76608_599183 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76608 ⟨599183, by decide⟩ :=
  accepted_of_selected 12 76608 ⟨599183, by decide⟩ ⟨12, 2, 0, 599183, 76608, 3917, 65536⟩
    (by decide) selected_cut_23712

theorem selected_cut_23713 : selected 9 ⟨599224, by decide⟩
    (prefixPartial 12 76609) = some ⟨12, 2, 0, 599224, 76609, 3765, 65536⟩ := by
  decide +kernel

theorem context_12_76609_599224 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76609 ⟨599224, by decide⟩ :=
  accepted_of_selected 12 76609 ⟨599224, by decide⟩ ⟨12, 2, 0, 599224, 76609, 3765, 65536⟩
    (by decide) selected_cut_23713

theorem selected_cut_23714 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 306440) = some ⟨13, 1, 0, 3444, 306440, 1, 16384⟩ := by
  decide +kernel

theorem context_13_306440_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306440 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 306440 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 306440, 1, 16384⟩
    (by decide) selected_cut_23714

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
