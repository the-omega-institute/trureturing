/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover339
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_32644 : selected 8 ⟨839851, by decide⟩
    (prefixPartial 13 438475) = some ⟨13, 2, 0, 839851, 438475, 641, 16384⟩ := by
  decide +kernel

theorem context_13_438475_839851 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438475 ⟨839851, by decide⟩ :=
  accepted_of_selected 13 438475 ⟨839851, by decide⟩ ⟨13, 2, 0, 839851, 438475, 641, 16384⟩
    (by decide) selected_cut_32644

theorem unmarked_context_12_109618_839852 : frontier 9 ⟨839852, by decide⟩
    (prefixCache 12 109618) (prefixPartial 12 109618) = false := by
  decide +kernel

theorem node_context_12_109618_839852 : EJMOriginalGlobalDAGData.nodes 9 ⟨839852, by decide⟩ =
    .split (coordinate 12) (![⟨839800, by decide⟩,⟨839829, by decide⟩,⟨839844, by decide⟩,⟨839851, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_109618_839852 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109618 ⟨839852, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 109618
    ⟨839852, by decide⟩ (by decide) (![⟨839800, by decide⟩,⟨839829, by decide⟩,⟨839844, by decide⟩,⟨839851, by decide⟩]) unmarked_context_12_109618_839852 node_context_12_109618_839852
  intro a
  fin_cases a
  · exact context_13_438472_839800
  · exact context_13_438473_839829
  · exact context_13_438474_839844
  · exact context_13_438475_839851

theorem selected_cut_32645 : selected 8 ⟨839863, by decide⟩
    (prefixPartial 13 438476) = some ⟨13, 2, 0, 839863, 438476, 505, 16384⟩ := by
  decide +kernel

theorem context_13_438476_839863 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438476 ⟨839863, by decide⟩ :=
  accepted_of_selected 13 438476 ⟨839863, by decide⟩ ⟨13, 2, 0, 839863, 438476, 505, 16384⟩
    (by decide) selected_cut_32645

theorem selected_cut_32646 : selected 8 ⟨839895, by decide⟩
    (prefixPartial 13 438477) = some ⟨13, 2, 0, 839895, 438477, 2585, 16384⟩ := by
  decide +kernel

theorem context_13_438477_839895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438477 ⟨839895, by decide⟩ :=
  accepted_of_selected 13 438477 ⟨839895, by decide⟩ ⟨13, 2, 0, 839895, 438477, 2585, 16384⟩
    (by decide) selected_cut_32646

theorem selected_cut_32647 : selected 8 ⟨839914, by decide⟩
    (prefixPartial 13 438478) = some ⟨13, 2, 0, 839914, 438478, 1205, 16384⟩ := by
  decide +kernel

theorem context_13_438478_839914 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438478 ⟨839914, by decide⟩ :=
  accepted_of_selected 13 438478 ⟨839914, by decide⟩ ⟨13, 2, 0, 839914, 438478, 1205, 16384⟩
    (by decide) selected_cut_32647

theorem selected_cut_32648 : selected 8 ⟨839922, by decide⟩
    (prefixPartial 13 438479) = some ⟨13, 2, 0, 839922, 438479, 649, 16384⟩ := by
  decide +kernel

theorem context_13_438479_839922 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438479 ⟨839922, by decide⟩ :=
  accepted_of_selected 13 438479 ⟨839922, by decide⟩ ⟨13, 2, 0, 839922, 438479, 649, 16384⟩
    (by decide) selected_cut_32648

theorem unmarked_context_12_109619_839923 : frontier 9 ⟨839923, by decide⟩
    (prefixCache 12 109619) (prefixPartial 12 109619) = false := by
  decide +kernel

theorem node_context_12_109619_839923 : EJMOriginalGlobalDAGData.nodes 9 ⟨839923, by decide⟩ =
    .split (coordinate 12) (![⟨839863, by decide⟩,⟨839895, by decide⟩,⟨839914, by decide⟩,⟨839922, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_109619_839923 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109619 ⟨839923, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 109619
    ⟨839923, by decide⟩ (by decide) (![⟨839863, by decide⟩,⟨839895, by decide⟩,⟨839914, by decide⟩,⟨839922, by decide⟩]) unmarked_context_12_109619_839923 node_context_12_109619_839923
  intro a
  fin_cases a
  · exact context_13_438476_839863
  · exact context_13_438477_839895
  · exact context_13_438478_839914
  · exact context_13_438479_839922

theorem unmarked_context_11_27404_839924 : frontier 10 ⟨839924, by decide⟩
    (prefixCache 11 27404) (prefixPartial 11 27404) = false := by
  decide +kernel

theorem node_context_11_27404_839924 : EJMOriginalGlobalDAGData.nodes 10 ⟨839924, by decide⟩ =
    .split (coordinate 11) (![⟨792260, by decide⟩,⟨839791, by decide⟩,⟨839852, by decide⟩,⟨839923, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27404_839924 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27404 ⟨839924, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27404
    ⟨839924, by decide⟩ (by decide) (![⟨792260, by decide⟩,⟨839791, by decide⟩,⟨839852, by decide⟩,⟨839923, by decide⟩]) unmarked_context_11_27404_839924 node_context_11_27404_839924
  intro a
  fin_cases a
  · exact context_12_109616_792260
  · exact context_12_109617_839791
  · exact context_12_109618_839852
  · exact context_12_109619_839923

theorem selected_cut_32649 : selected 8 ⟨839932, by decide⟩
    (prefixPartial 13 438480) = some ⟨13, 2, 0, 839932, 438480, 409, 16384⟩ := by
  decide +kernel

theorem context_13_438480_839932 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438480 ⟨839932, by decide⟩ :=
  accepted_of_selected 13 438480 ⟨839932, by decide⟩ ⟨13, 2, 0, 839932, 438480, 409, 16384⟩
    (by decide) selected_cut_32649

theorem selected_cut_32650 : selected 8 ⟨839966, by decide⟩
    (prefixPartial 13 438481) = some ⟨13, 2, 0, 839966, 438481, 2469, 16384⟩ := by
  decide +kernel

theorem context_13_438481_839966 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438481 ⟨839966, by decide⟩ :=
  accepted_of_selected 13 438481 ⟨839966, by decide⟩ ⟨13, 2, 0, 839966, 438481, 2469, 16384⟩
    (by decide) selected_cut_32650

theorem selected_cut_32651 : selected 8 ⟨839984, by decide⟩
    (prefixPartial 13 438482) = some ⟨13, 2, 0, 839984, 438482, 1373, 16384⟩ := by
  decide +kernel

theorem context_13_438482_839984 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438482 ⟨839984, by decide⟩ :=
  accepted_of_selected 13 438482 ⟨839984, by decide⟩ ⟨13, 2, 0, 839984, 438482, 1373, 16384⟩
    (by decide) selected_cut_32651

theorem selected_cut_32652 : selected 8 ⟨839992, by decide⟩
    (prefixPartial 13 438483) = some ⟨13, 2, 0, 839992, 438483, 669, 16384⟩ := by
  decide +kernel

theorem context_13_438483_839992 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438483 ⟨839992, by decide⟩ :=
  accepted_of_selected 13 438483 ⟨839992, by decide⟩ ⟨13, 2, 0, 839992, 438483, 669, 16384⟩
    (by decide) selected_cut_32652

theorem unmarked_context_12_109620_839993 : frontier 9 ⟨839993, by decide⟩
    (prefixCache 12 109620) (prefixPartial 12 109620) = false := by
  decide +kernel

theorem node_context_12_109620_839993 : EJMOriginalGlobalDAGData.nodes 9 ⟨839993, by decide⟩ =
    .split (coordinate 12) (![⟨839932, by decide⟩,⟨839966, by decide⟩,⟨839984, by decide⟩,⟨839992, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_109620_839993 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109620 ⟨839993, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 109620
    ⟨839993, by decide⟩ (by decide) (![⟨839932, by decide⟩,⟨839966, by decide⟩,⟨839984, by decide⟩,⟨839992, by decide⟩]) unmarked_context_12_109620_839993 node_context_12_109620_839993
  intro a
  fin_cases a
  · exact context_13_438480_839932
  · exact context_13_438481_839966
  · exact context_13_438482_839984
  · exact context_13_438483_839992

theorem selected_cut_32653 : selected 8 ⟨840004, by decide⟩
    (prefixPartial 13 438484) = some ⟨13, 2, 0, 840004, 438484, 413, 16384⟩ := by
  decide +kernel

theorem context_13_438484_840004 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438484 ⟨840004, by decide⟩ :=
  accepted_of_selected 13 438484 ⟨840004, by decide⟩ ⟨13, 2, 0, 840004, 438484, 413, 16384⟩
    (by decide) selected_cut_32653

theorem selected_cut_32654 : selected 8 ⟨840031, by decide⟩
    (prefixPartial 13 438485) = some ⟨13, 2, 0, 840031, 438485, 2125, 16384⟩ := by
  decide +kernel

theorem context_13_438485_840031 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438485 ⟨840031, by decide⟩ :=
  accepted_of_selected 13 438485 ⟨840031, by decide⟩ ⟨13, 2, 0, 840031, 438485, 2125, 16384⟩
    (by decide) selected_cut_32654

theorem selected_cut_32655 : selected 8 ⟨840055, by decide⟩
    (prefixPartial 13 438486) = some ⟨13, 2, 0, 840055, 438486, 1585, 16384⟩ := by
  decide +kernel

theorem context_13_438486_840055 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438486 ⟨840055, by decide⟩ :=
  accepted_of_selected 13 438486 ⟨840055, by decide⟩ ⟨13, 2, 0, 840055, 438486, 1585, 16384⟩
    (by decide) selected_cut_32655

theorem selected_cut_32656 : selected 8 ⟨840060, by decide⟩
    (prefixPartial 13 438487) = some ⟨13, 2, 0, 840060, 438487, 625, 16384⟩ := by
  decide +kernel

theorem context_13_438487_840060 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438487 ⟨840060, by decide⟩ :=
  accepted_of_selected 13 438487 ⟨840060, by decide⟩ ⟨13, 2, 0, 840060, 438487, 625, 16384⟩
    (by decide) selected_cut_32656

theorem unmarked_context_12_109621_840061 : frontier 9 ⟨840061, by decide⟩
    (prefixCache 12 109621) (prefixPartial 12 109621) = false := by
  decide +kernel

theorem node_context_12_109621_840061 : EJMOriginalGlobalDAGData.nodes 9 ⟨840061, by decide⟩ =
    .split (coordinate 12) (![⟨840004, by decide⟩,⟨840031, by decide⟩,⟨840055, by decide⟩,⟨840060, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_109621_840061 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109621 ⟨840061, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 109621
    ⟨840061, by decide⟩ (by decide) (![⟨840004, by decide⟩,⟨840031, by decide⟩,⟨840055, by decide⟩,⟨840060, by decide⟩]) unmarked_context_12_109621_840061 node_context_12_109621_840061
  intro a
  fin_cases a
  · exact context_13_438484_840004
  · exact context_13_438485_840031
  · exact context_13_438486_840055
  · exact context_13_438487_840060

theorem selected_cut_32657 : selected 8 ⟨840067, by decide⟩
    (prefixPartial 13 438488) = some ⟨13, 2, 0, 840067, 438488, 337, 16384⟩ := by
  decide +kernel

theorem context_13_438488_840067 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438488 ⟨840067, by decide⟩ :=
  accepted_of_selected 13 438488 ⟨840067, by decide⟩ ⟨13, 2, 0, 840067, 438488, 337, 16384⟩
    (by decide) selected_cut_32657

theorem selected_cut_32658 : selected 8 ⟨840097, by decide⟩
    (prefixPartial 13 438489) = some ⟨13, 2, 0, 840097, 438489, 2537, 16384⟩ := by
  decide +kernel

theorem context_13_438489_840097 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438489 ⟨840097, by decide⟩ :=
  accepted_of_selected 13 438489 ⟨840097, by decide⟩ ⟨13, 2, 0, 840097, 438489, 2537, 16384⟩
    (by decide) selected_cut_32658

theorem selected_cut_32659 : selected 8 ⟨840114, by decide⟩
    (prefixPartial 13 438490) = some ⟨13, 2, 0, 840114, 438490, 1069, 16384⟩ := by
  decide +kernel

theorem context_13_438490_840114 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438490 ⟨840114, by decide⟩ :=
  accepted_of_selected 13 438490 ⟨840114, by decide⟩ ⟨13, 2, 0, 840114, 438490, 1069, 16384⟩
    (by decide) selected_cut_32659

theorem selected_cut_32660 : selected 8 ⟨840120, by decide⟩
    (prefixPartial 13 438491) = some ⟨13, 2, 0, 840120, 438491, 625, 16384⟩ := by
  decide +kernel

theorem context_13_438491_840120 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438491 ⟨840120, by decide⟩ :=
  accepted_of_selected 13 438491 ⟨840120, by decide⟩ ⟨13, 2, 0, 840120, 438491, 625, 16384⟩
    (by decide) selected_cut_32660

theorem unmarked_context_12_109622_840121 : frontier 9 ⟨840121, by decide⟩
    (prefixCache 12 109622) (prefixPartial 12 109622) = false := by
  decide +kernel

theorem node_context_12_109622_840121 : EJMOriginalGlobalDAGData.nodes 9 ⟨840121, by decide⟩ =
    .split (coordinate 12) (![⟨840067, by decide⟩,⟨840097, by decide⟩,⟨840114, by decide⟩,⟨840120, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_109622_840121 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109622 ⟨840121, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 109622
    ⟨840121, by decide⟩ (by decide) (![⟨840067, by decide⟩,⟨840097, by decide⟩,⟨840114, by decide⟩,⟨840120, by decide⟩]) unmarked_context_12_109622_840121 node_context_12_109622_840121
  intro a
  fin_cases a
  · exact context_13_438488_840067
  · exact context_13_438489_840097
  · exact context_13_438490_840114
  · exact context_13_438491_840120

theorem selected_cut_32661 : selected 8 ⟨840129, by decide⟩
    (prefixPartial 13 438492) = some ⟨13, 2, 0, 840129, 438492, 369, 16384⟩ := by
  decide +kernel

theorem context_13_438492_840129 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438492 ⟨840129, by decide⟩ :=
  accepted_of_selected 13 438492 ⟨840129, by decide⟩ ⟨13, 2, 0, 840129, 438492, 369, 16384⟩
    (by decide) selected_cut_32661

theorem selected_cut_32662 : selected 8 ⟨840178, by decide⟩
    (prefixPartial 13 438493) = some ⟨13, 2, 0, 840178, 438493, 2977, 16384⟩ := by
  decide +kernel

theorem context_13_438493_840178 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438493 ⟨840178, by decide⟩ :=
  accepted_of_selected 13 438493 ⟨840178, by decide⟩ ⟨13, 2, 0, 840178, 438493, 2977, 16384⟩
    (by decide) selected_cut_32662

theorem selected_cut_32663 : selected 8 ⟨840211, by decide⟩
    (prefixPartial 13 438494) = some ⟨13, 2, 0, 840211, 438494, 1665, 16384⟩ := by
  decide +kernel

theorem context_13_438494_840211 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438494 ⟨840211, by decide⟩ :=
  accepted_of_selected 13 438494 ⟨840211, by decide⟩ ⟨13, 2, 0, 840211, 438494, 1665, 16384⟩
    (by decide) selected_cut_32663

theorem selected_cut_32664 : selected 8 ⟨840218, by decide⟩
    (prefixPartial 13 438495) = some ⟨13, 2, 0, 840218, 438495, 745, 16384⟩ := by
  decide +kernel

theorem context_13_438495_840218 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438495 ⟨840218, by decide⟩ :=
  accepted_of_selected 13 438495 ⟨840218, by decide⟩ ⟨13, 2, 0, 840218, 438495, 745, 16384⟩
    (by decide) selected_cut_32664

theorem unmarked_context_12_109623_840219 : frontier 9 ⟨840219, by decide⟩
    (prefixCache 12 109623) (prefixPartial 12 109623) = false := by
  decide +kernel

theorem node_context_12_109623_840219 : EJMOriginalGlobalDAGData.nodes 9 ⟨840219, by decide⟩ =
    .split (coordinate 12) (![⟨840129, by decide⟩,⟨840178, by decide⟩,⟨840211, by decide⟩,⟨840218, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_109623_840219 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109623 ⟨840219, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 109623
    ⟨840219, by decide⟩ (by decide) (![⟨840129, by decide⟩,⟨840178, by decide⟩,⟨840211, by decide⟩,⟨840218, by decide⟩]) unmarked_context_12_109623_840219 node_context_12_109623_840219
  intro a
  fin_cases a
  · exact context_13_438492_840129
  · exact context_13_438493_840178
  · exact context_13_438494_840211
  · exact context_13_438495_840218

theorem unmarked_context_11_27405_840220 : frontier 10 ⟨840220, by decide⟩
    (prefixCache 11 27405) (prefixPartial 11 27405) = false := by
  decide +kernel

theorem node_context_11_27405_840220 : EJMOriginalGlobalDAGData.nodes 10 ⟨840220, by decide⟩ =
    .split (coordinate 11) (![⟨839993, by decide⟩,⟨840061, by decide⟩,⟨840121, by decide⟩,⟨840219, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27405_840220 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27405 ⟨840220, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27405
    ⟨840220, by decide⟩ (by decide) (![⟨839993, by decide⟩,⟨840061, by decide⟩,⟨840121, by decide⟩,⟨840219, by decide⟩]) unmarked_context_11_27405_840220 node_context_11_27405_840220
  intro a
  fin_cases a
  · exact context_12_109620_839993
  · exact context_12_109621_840061
  · exact context_12_109622_840121
  · exact context_12_109623_840219

theorem selected_cut_32665 : selected 8 ⟨840224, by decide⟩
    (prefixPartial 13 438496) = some ⟨13, 2, 0, 840224, 438496, 161, 16384⟩ := by
  decide +kernel

theorem context_13_438496_840224 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438496 ⟨840224, by decide⟩ :=
  accepted_of_selected 13 438496 ⟨840224, by decide⟩ ⟨13, 2, 0, 840224, 438496, 161, 16384⟩
    (by decide) selected_cut_32665

theorem selected_cut_32666 : selected 8 ⟨840255, by decide⟩
    (prefixPartial 13 438497) = some ⟨13, 2, 0, 840255, 438497, 2497, 16384⟩ := by
  decide +kernel

theorem context_13_438497_840255 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438497 ⟨840255, by decide⟩ :=
  accepted_of_selected 13 438497 ⟨840255, by decide⟩ ⟨13, 2, 0, 840255, 438497, 2497, 16384⟩
    (by decide) selected_cut_32666

theorem selected_cut_32667 : selected 8 ⟨840278, by decide⟩
    (prefixPartial 13 438498) = some ⟨13, 2, 0, 840278, 438498, 1453, 16384⟩ := by
  decide +kernel

theorem context_13_438498_840278 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438498 ⟨840278, by decide⟩ :=
  accepted_of_selected 13 438498 ⟨840278, by decide⟩ ⟨13, 2, 0, 840278, 438498, 1453, 16384⟩
    (by decide) selected_cut_32667

theorem selected_cut_32668 : selected 8 ⟨840283, by decide⟩
    (prefixPartial 13 438499) = some ⟨13, 2, 0, 840283, 438499, 601, 16384⟩ := by
  decide +kernel

theorem context_13_438499_840283 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438499 ⟨840283, by decide⟩ :=
  accepted_of_selected 13 438499 ⟨840283, by decide⟩ ⟨13, 2, 0, 840283, 438499, 601, 16384⟩
    (by decide) selected_cut_32668

theorem unmarked_context_12_109624_840284 : frontier 9 ⟨840284, by decide⟩
    (prefixCache 12 109624) (prefixPartial 12 109624) = false := by
  decide +kernel

theorem node_context_12_109624_840284 : EJMOriginalGlobalDAGData.nodes 9 ⟨840284, by decide⟩ =
    .split (coordinate 12) (![⟨840224, by decide⟩,⟨840255, by decide⟩,⟨840278, by decide⟩,⟨840283, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_109624_840284 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109624 ⟨840284, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 109624
    ⟨840284, by decide⟩ (by decide) (![⟨840224, by decide⟩,⟨840255, by decide⟩,⟨840278, by decide⟩,⟨840283, by decide⟩]) unmarked_context_12_109624_840284 node_context_12_109624_840284
  intro a
  fin_cases a
  · exact context_13_438496_840224
  · exact context_13_438497_840255
  · exact context_13_438498_840278
  · exact context_13_438499_840283

theorem selected_cut_32669 : selected 8 ⟨840288, by decide⟩
    (prefixPartial 13 438500) = some ⟨13, 2, 0, 840288, 438500, 197, 16384⟩ := by
  decide +kernel

theorem context_13_438500_840288 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438500 ⟨840288, by decide⟩ :=
  accepted_of_selected 13 438500 ⟨840288, by decide⟩ ⟨13, 2, 0, 840288, 438500, 197, 16384⟩
    (by decide) selected_cut_32669

theorem selected_cut_32670 : selected 8 ⟨840316, by decide⟩
    (prefixPartial 13 438501) = some ⟨13, 2, 0, 840316, 438501, 2505, 16384⟩ := by
  decide +kernel

theorem context_13_438501_840316 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438501 ⟨840316, by decide⟩ :=
  accepted_of_selected 13 438501 ⟨840316, by decide⟩ ⟨13, 2, 0, 840316, 438501, 2505, 16384⟩
    (by decide) selected_cut_32670

theorem selected_cut_32671 : selected 8 ⟨840352, by decide⟩
    (prefixPartial 13 438502) = some ⟨13, 2, 0, 840352, 438502, 1761, 16384⟩ := by
  decide +kernel

theorem context_13_438502_840352 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438502 ⟨840352, by decide⟩ :=
  accepted_of_selected 13 438502 ⟨840352, by decide⟩ ⟨13, 2, 0, 840352, 438502, 1761, 16384⟩
    (by decide) selected_cut_32671

theorem selected_cut_32672 : selected 8 ⟨840358, by decide⟩
    (prefixPartial 13 438503) = some ⟨13, 2, 0, 840358, 438503, 653, 16384⟩ := by
  decide +kernel

theorem context_13_438503_840358 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438503 ⟨840358, by decide⟩ :=
  accepted_of_selected 13 438503 ⟨840358, by decide⟩ ⟨13, 2, 0, 840358, 438503, 653, 16384⟩
    (by decide) selected_cut_32672

theorem unmarked_context_12_109625_840359 : frontier 9 ⟨840359, by decide⟩
    (prefixCache 12 109625) (prefixPartial 12 109625) = false := by
  decide +kernel

theorem node_context_12_109625_840359 : EJMOriginalGlobalDAGData.nodes 9 ⟨840359, by decide⟩ =
    .split (coordinate 12) (![⟨840288, by decide⟩,⟨840316, by decide⟩,⟨840352, by decide⟩,⟨840358, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_109625_840359 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109625 ⟨840359, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 109625
    ⟨840359, by decide⟩ (by decide) (![⟨840288, by decide⟩,⟨840316, by decide⟩,⟨840352, by decide⟩,⟨840358, by decide⟩]) unmarked_context_12_109625_840359 node_context_12_109625_840359
  intro a
  fin_cases a
  · exact context_13_438500_840288
  · exact context_13_438501_840316
  · exact context_13_438502_840352
  · exact context_13_438503_840358

theorem selected_cut_32673 : selected 9 ⟨840419, by decide⟩
    (prefixPartial 12 109626) = some ⟨12, 2, 0, 840419, 109626, 4005, 65536⟩ := by
  decide +kernel

theorem context_12_109626_840419 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109626 ⟨840419, by decide⟩ :=
  accepted_of_selected 12 109626 ⟨840419, by decide⟩ ⟨12, 2, 0, 840419, 109626, 4005, 65536⟩
    (by decide) selected_cut_32673

theorem selected_cut_32674 : selected 8 ⟨840422, by decide⟩
    (prefixPartial 13 438508) = some ⟨13, 2, 0, 840422, 438508, 81, 16384⟩ := by
  decide +kernel

theorem context_13_438508_840422 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438508 ⟨840422, by decide⟩ :=
  accepted_of_selected 13 438508 ⟨840422, by decide⟩ ⟨13, 2, 0, 840422, 438508, 81, 16384⟩
    (by decide) selected_cut_32674

theorem selected_cut_32675 : selected 8 ⟨840468, by decide⟩
    (prefixPartial 13 438509) = some ⟨13, 2, 0, 840468, 438509, 2981, 16384⟩ := by
  decide +kernel

theorem context_13_438509_840468 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438509 ⟨840468, by decide⟩ :=
  accepted_of_selected 13 438509 ⟨840468, by decide⟩ ⟨13, 2, 0, 840468, 438509, 2981, 16384⟩
    (by decide) selected_cut_32675

theorem selected_cut_32676 : selected 8 ⟨840494, by decide⟩
    (prefixPartial 13 438510) = some ⟨13, 2, 0, 840494, 438510, 1653, 16384⟩ := by
  decide +kernel

theorem context_13_438510_840494 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438510 ⟨840494, by decide⟩ :=
  accepted_of_selected 13 438510 ⟨840494, by decide⟩ ⟨13, 2, 0, 840494, 438510, 1653, 16384⟩
    (by decide) selected_cut_32676

theorem selected_cut_32677 : selected 8 ⟨840502, by decide⟩
    (prefixPartial 13 438511) = some ⟨13, 2, 0, 840502, 438511, 661, 16384⟩ := by
  decide +kernel

theorem context_13_438511_840502 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438511 ⟨840502, by decide⟩ :=
  accepted_of_selected 13 438511 ⟨840502, by decide⟩ ⟨13, 2, 0, 840502, 438511, 661, 16384⟩
    (by decide) selected_cut_32677

theorem unmarked_context_12_109627_840503 : frontier 9 ⟨840503, by decide⟩
    (prefixCache 12 109627) (prefixPartial 12 109627) = false := by
  decide +kernel

theorem node_context_12_109627_840503 : EJMOriginalGlobalDAGData.nodes 9 ⟨840503, by decide⟩ =
    .split (coordinate 12) (![⟨840422, by decide⟩,⟨840468, by decide⟩,⟨840494, by decide⟩,⟨840502, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_109627_840503 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109627 ⟨840503, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 109627
    ⟨840503, by decide⟩ (by decide) (![⟨840422, by decide⟩,⟨840468, by decide⟩,⟨840494, by decide⟩,⟨840502, by decide⟩]) unmarked_context_12_109627_840503 node_context_12_109627_840503
  intro a
  fin_cases a
  · exact context_13_438508_840422
  · exact context_13_438509_840468
  · exact context_13_438510_840494
  · exact context_13_438511_840502

theorem unmarked_context_11_27406_840504 : frontier 10 ⟨840504, by decide⟩
    (prefixCache 11 27406) (prefixPartial 11 27406) = false := by
  decide +kernel

theorem node_context_11_27406_840504 : EJMOriginalGlobalDAGData.nodes 10 ⟨840504, by decide⟩ =
    .split (coordinate 11) (![⟨840284, by decide⟩,⟨840359, by decide⟩,⟨840419, by decide⟩,⟨840503, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27406_840504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27406 ⟨840504, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27406
    ⟨840504, by decide⟩ (by decide) (![⟨840284, by decide⟩,⟨840359, by decide⟩,⟨840419, by decide⟩,⟨840503, by decide⟩]) unmarked_context_11_27406_840504 node_context_11_27406_840504
  intro a
  fin_cases a
  · exact context_12_109624_840284
  · exact context_12_109625_840359
  · exact context_12_109626_840419
  · exact context_12_109627_840503

theorem selected_cut_32678 : selected 10 ⟨793294, by decide⟩
    (prefixPartial 11 27407) = some ⟨11, 1, 0, 793294, 27407, 1, 262144⟩ := by
  decide +kernel

theorem context_11_27407_793294 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27407 ⟨793294, by decide⟩ :=
  accepted_of_selected 11 27407 ⟨793294, by decide⟩ ⟨11, 1, 0, 793294, 27407, 1, 262144⟩
    (by decide) selected_cut_32678

theorem unmarked_context_10_6851_840505 : frontier 11 ⟨840505, by decide⟩
    (prefixCache 10 6851) (prefixPartial 10 6851) = false := by
  decide +kernel

theorem node_context_10_6851_840505 : EJMOriginalGlobalDAGData.nodes 11 ⟨840505, by decide⟩ =
    .split (coordinate 10) (![⟨839924, by decide⟩,⟨840220, by decide⟩,⟨840504, by decide⟩,⟨793294, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6851_840505 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6851 ⟨840505, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6851
    ⟨840505, by decide⟩ (by decide) (![⟨839924, by decide⟩,⟨840220, by decide⟩,⟨840504, by decide⟩,⟨793294, by decide⟩]) unmarked_context_10_6851_840505 node_context_10_6851_840505
  intro a
  fin_cases a
  · exact context_11_27404_839924
  · exact context_11_27405_840220
  · exact context_11_27406_840504
  · exact context_11_27407_793294

theorem unmarked_context_9_1712_840506 : frontier 12 ⟨840506, by decide⟩
    (prefixCache 9 1712) (prefixPartial 9 1712) = false := by
  decide +kernel

theorem node_context_9_1712_840506 : EJMOriginalGlobalDAGData.nodes 12 ⟨840506, by decide⟩ =
    .split (coordinate 9) (![⟨836724, by decide⟩,⟨838313, by decide⟩,⟨839723, by decide⟩,⟨840505, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1712_840506 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1712 ⟨840506, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1712
    ⟨840506, by decide⟩ (by decide) (![⟨836724, by decide⟩,⟨838313, by decide⟩,⟨839723, by decide⟩,⟨840505, by decide⟩]) unmarked_context_9_1712_840506 node_context_9_1712_840506
  intro a
  fin_cases a
  · exact context_10_6848_836724
  · exact context_10_6849_838313
  · exact context_10_6850_839723
  · exact context_10_6851_840505

theorem selected_cut_32679 : selected 9 ⟨450982, by decide⟩
    (prefixPartial 12 109632) = some ⟨12, 1, 0, 450982, 109632, 1, 65536⟩ := by
  decide +kernel

theorem context_12_109632_450982 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109632 ⟨450982, by decide⟩ :=
  accepted_of_selected 12 109632 ⟨450982, by decide⟩ ⟨12, 1, 0, 450982, 109632, 1, 65536⟩
    (by decide) selected_cut_32679

theorem selected_cut_32680 : selected 9 ⟨840583, by decide⟩
    (prefixPartial 12 109633) = some ⟨12, 2, 0, 840583, 109633, 3909, 65536⟩ := by
  decide +kernel

theorem context_12_109633_840583 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109633 ⟨840583, by decide⟩ :=
  accepted_of_selected 12 109633 ⟨840583, by decide⟩ ⟨12, 2, 0, 840583, 109633, 3909, 65536⟩
    (by decide) selected_cut_32680

theorem selected_cut_32681 : selected 9 ⟨840639, by decide⟩
    (prefixPartial 12 109634) = some ⟨12, 2, 0, 840639, 109634, 3749, 65536⟩ := by
  decide +kernel

theorem context_12_109634_840639 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109634 ⟨840639, by decide⟩ :=
  accepted_of_selected 12 109634 ⟨840639, by decide⟩ ⟨12, 2, 0, 840639, 109634, 3749, 65536⟩
    (by decide) selected_cut_32681

theorem selected_cut_32682 : selected 9 ⟨840696, by decide⟩
    (prefixPartial 12 109635) = some ⟨12, 2, 0, 840696, 109635, 3957, 65536⟩ := by
  decide +kernel

theorem context_12_109635_840696 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109635 ⟨840696, by decide⟩ :=
  accepted_of_selected 12 109635 ⟨840696, by decide⟩ ⟨12, 2, 0, 840696, 109635, 3957, 65536⟩
    (by decide) selected_cut_32682

theorem unmarked_context_11_27408_840697 : frontier 10 ⟨840697, by decide⟩
    (prefixCache 11 27408) (prefixPartial 11 27408) = false := by
  decide +kernel

theorem node_context_11_27408_840697 : EJMOriginalGlobalDAGData.nodes 10 ⟨840697, by decide⟩ =
    .split (coordinate 11) (![⟨450982, by decide⟩,⟨840583, by decide⟩,⟨840639, by decide⟩,⟨840696, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27408_840697 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27408 ⟨840697, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27408
    ⟨840697, by decide⟩ (by decide) (![⟨450982, by decide⟩,⟨840583, by decide⟩,⟨840639, by decide⟩,⟨840696, by decide⟩]) unmarked_context_11_27408_840697 node_context_11_27408_840697
  intro a
  fin_cases a
  · exact context_12_109632_450982
  · exact context_12_109633_840583
  · exact context_12_109634_840639
  · exact context_12_109635_840696

theorem selected_cut_32683 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 438544) = some ⟨13, 1, 0, 3444, 438544, 1, 16384⟩ := by
  decide +kernel

theorem context_13_438544_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438544 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 438544 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 438544, 1, 16384⟩
    (by decide) selected_cut_32683

theorem selected_cut_32684 : selected 8 ⟨840735, by decide⟩
    (prefixPartial 13 438545) = some ⟨13, 2, 0, 840735, 438545, 2485, 16384⟩ := by
  decide +kernel

theorem context_13_438545_840735 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438545 ⟨840735, by decide⟩ :=
  accepted_of_selected 13 438545 ⟨840735, by decide⟩ ⟨13, 2, 0, 840735, 438545, 2485, 16384⟩
    (by decide) selected_cut_32684

theorem selected_cut_32685 : selected 8 ⟨840761, by decide⟩
    (prefixPartial 13 438546) = some ⟨13, 2, 0, 840761, 438546, 1293, 16384⟩ := by
  decide +kernel

theorem context_13_438546_840761 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438546 ⟨840761, by decide⟩ :=
  accepted_of_selected 13 438546 ⟨840761, by decide⟩ ⟨13, 2, 0, 840761, 438546, 1293, 16384⟩
    (by decide) selected_cut_32685

theorem selected_cut_32686 : selected 8 ⟨840767, by decide⟩
    (prefixPartial 13 438547) = some ⟨13, 2, 0, 840767, 438547, 649, 16384⟩ := by
  decide +kernel

theorem context_13_438547_840767 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438547 ⟨840767, by decide⟩ :=
  accepted_of_selected 13 438547 ⟨840767, by decide⟩ ⟨13, 2, 0, 840767, 438547, 649, 16384⟩
    (by decide) selected_cut_32686

theorem unmarked_context_12_109636_840768 : frontier 9 ⟨840768, by decide⟩
    (prefixCache 12 109636) (prefixPartial 12 109636) = false := by
  decide +kernel

theorem node_context_12_109636_840768 : EJMOriginalGlobalDAGData.nodes 9 ⟨840768, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨840735, by decide⟩,⟨840761, by decide⟩,⟨840767, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_109636_840768 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109636 ⟨840768, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 109636
    ⟨840768, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨840735, by decide⟩,⟨840761, by decide⟩,⟨840767, by decide⟩]) unmarked_context_12_109636_840768 node_context_12_109636_840768
  intro a
  fin_cases a
  · exact context_13_438544_3444
  · exact context_13_438545_840735
  · exact context_13_438546_840761
  · exact context_13_438547_840767

theorem selected_cut_32687 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 438548) = some ⟨13, 1, 0, 3444, 438548, 1, 16384⟩ := by
  decide +kernel

theorem context_13_438548_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438548 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 438548 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 438548, 1, 16384⟩
    (by decide) selected_cut_32687

theorem selected_cut_32688 : selected 8 ⟨840810, by decide⟩
    (prefixPartial 13 438549) = some ⟨13, 2, 0, 840810, 438549, 2009, 16384⟩ := by
  decide +kernel

theorem context_13_438549_840810 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438549 ⟨840810, by decide⟩ :=
  accepted_of_selected 13 438549 ⟨840810, by decide⟩ ⟨13, 2, 0, 840810, 438549, 2009, 16384⟩
    (by decide) selected_cut_32688

theorem selected_cut_32689 : selected 8 ⟨840836, by decide⟩
    (prefixPartial 13 438550) = some ⟨13, 2, 0, 840836, 438550, 1401, 16384⟩ := by
  decide +kernel

theorem context_13_438550_840836 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438550 ⟨840836, by decide⟩ :=
  accepted_of_selected 13 438550 ⟨840836, by decide⟩ ⟨13, 2, 0, 840836, 438550, 1401, 16384⟩
    (by decide) selected_cut_32689

theorem selected_cut_32690 : selected 8 ⟨840848, by decide⟩
    (prefixPartial 13 438551) = some ⟨13, 2, 0, 840848, 438551, 693, 16384⟩ := by
  decide +kernel

theorem context_13_438551_840848 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438551 ⟨840848, by decide⟩ :=
  accepted_of_selected 13 438551 ⟨840848, by decide⟩ ⟨13, 2, 0, 840848, 438551, 693, 16384⟩
    (by decide) selected_cut_32690

theorem unmarked_context_12_109637_840849 : frontier 9 ⟨840849, by decide⟩
    (prefixCache 12 109637) (prefixPartial 12 109637) = false := by
  decide +kernel

theorem node_context_12_109637_840849 : EJMOriginalGlobalDAGData.nodes 9 ⟨840849, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨840810, by decide⟩,⟨840836, by decide⟩,⟨840848, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_109637_840849 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109637 ⟨840849, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 109637
    ⟨840849, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨840810, by decide⟩,⟨840836, by decide⟩,⟨840848, by decide⟩]) unmarked_context_12_109637_840849 node_context_12_109637_840849
  intro a
  fin_cases a
  · exact context_13_438548_3444
  · exact context_13_438549_840810
  · exact context_13_438550_840836
  · exact context_13_438551_840848

theorem selected_cut_32691 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 438552) = some ⟨13, 1, 0, 3444, 438552, 1, 16384⟩ := by
  decide +kernel

theorem context_13_438552_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438552 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 438552 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 438552, 1, 16384⟩
    (by decide) selected_cut_32691

theorem selected_cut_32692 : selected 8 ⟨840890, by decide⟩
    (prefixPartial 13 438553) = some ⟨13, 2, 0, 840890, 438553, 2353, 16384⟩ := by
  decide +kernel

theorem context_13_438553_840890 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438553 ⟨840890, by decide⟩ :=
  accepted_of_selected 13 438553 ⟨840890, by decide⟩ ⟨13, 2, 0, 840890, 438553, 2353, 16384⟩
    (by decide) selected_cut_32692

theorem selected_cut_32693 : selected 8 ⟨840915, by decide⟩
    (prefixPartial 13 438554) = some ⟨13, 2, 0, 840915, 438554, 1301, 16384⟩ := by
  decide +kernel

theorem context_13_438554_840915 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438554 ⟨840915, by decide⟩ :=
  accepted_of_selected 13 438554 ⟨840915, by decide⟩ ⟨13, 2, 0, 840915, 438554, 1301, 16384⟩
    (by decide) selected_cut_32693

theorem selected_cut_32694 : selected 8 ⟨840922, by decide⟩
    (prefixPartial 13 438555) = some ⟨13, 2, 0, 840922, 438555, 721, 16384⟩ := by
  decide +kernel

theorem context_13_438555_840922 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438555 ⟨840922, by decide⟩ :=
  accepted_of_selected 13 438555 ⟨840922, by decide⟩ ⟨13, 2, 0, 840922, 438555, 721, 16384⟩
    (by decide) selected_cut_32694

theorem unmarked_context_12_109638_840923 : frontier 9 ⟨840923, by decide⟩
    (prefixCache 12 109638) (prefixPartial 12 109638) = false := by
  decide +kernel

theorem node_context_12_109638_840923 : EJMOriginalGlobalDAGData.nodes 9 ⟨840923, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨840890, by decide⟩,⟨840915, by decide⟩,⟨840922, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_109638_840923 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109638 ⟨840923, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 109638
    ⟨840923, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨840890, by decide⟩,⟨840915, by decide⟩,⟨840922, by decide⟩]) unmarked_context_12_109638_840923 node_context_12_109638_840923
  intro a
  fin_cases a
  · exact context_13_438552_3444
  · exact context_13_438553_840890
  · exact context_13_438554_840915
  · exact context_13_438555_840922

theorem selected_cut_32695 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 438556) = some ⟨13, 1, 0, 3444, 438556, 1, 16384⟩ := by
  decide +kernel

theorem context_13_438556_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438556 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 438556 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 438556, 1, 16384⟩
    (by decide) selected_cut_32695

theorem selected_cut_32696 : selected 8 ⟨840969, by decide⟩
    (prefixPartial 13 438557) = some ⟨13, 2, 0, 840969, 438557, 2389, 16384⟩ := by
  decide +kernel

theorem context_13_438557_840969 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438557 ⟨840969, by decide⟩ :=
  accepted_of_selected 13 438557 ⟨840969, by decide⟩ ⟨13, 2, 0, 840969, 438557, 2389, 16384⟩
    (by decide) selected_cut_32696

theorem selected_cut_32697 : selected 8 ⟨840997, by decide⟩
    (prefixPartial 13 438558) = some ⟨13, 2, 0, 840997, 438558, 1501, 16384⟩ := by
  decide +kernel

theorem context_13_438558_840997 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438558 ⟨840997, by decide⟩ :=
  accepted_of_selected 13 438558 ⟨840997, by decide⟩ ⟨13, 2, 0, 840997, 438558, 1501, 16384⟩
    (by decide) selected_cut_32697

theorem selected_cut_32698 : selected 8 ⟨841003, by decide⟩
    (prefixPartial 13 438559) = some ⟨13, 2, 0, 841003, 438559, 733, 16384⟩ := by
  decide +kernel

theorem context_13_438559_841003 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438559 ⟨841003, by decide⟩ :=
  accepted_of_selected 13 438559 ⟨841003, by decide⟩ ⟨13, 2, 0, 841003, 438559, 733, 16384⟩
    (by decide) selected_cut_32698

theorem unmarked_context_12_109639_841004 : frontier 9 ⟨841004, by decide⟩
    (prefixCache 12 109639) (prefixPartial 12 109639) = false := by
  decide +kernel

theorem node_context_12_109639_841004 : EJMOriginalGlobalDAGData.nodes 9 ⟨841004, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨840969, by decide⟩,⟨840997, by decide⟩,⟨841003, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_109639_841004 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109639 ⟨841004, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 109639
    ⟨841004, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨840969, by decide⟩,⟨840997, by decide⟩,⟨841003, by decide⟩]) unmarked_context_12_109639_841004 node_context_12_109639_841004
  intro a
  fin_cases a
  · exact context_13_438556_3444
  · exact context_13_438557_840969
  · exact context_13_438558_840997
  · exact context_13_438559_841003

theorem unmarked_context_11_27409_841005 : frontier 10 ⟨841005, by decide⟩
    (prefixCache 11 27409) (prefixPartial 11 27409) = false := by
  decide +kernel

theorem node_context_11_27409_841005 : EJMOriginalGlobalDAGData.nodes 10 ⟨841005, by decide⟩ =
    .split (coordinate 11) (![⟨840768, by decide⟩,⟨840849, by decide⟩,⟨840923, by decide⟩,⟨841004, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27409_841005 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27409 ⟨841005, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27409
    ⟨841005, by decide⟩ (by decide) (![⟨840768, by decide⟩,⟨840849, by decide⟩,⟨840923, by decide⟩,⟨841004, by decide⟩]) unmarked_context_11_27409_841005 node_context_11_27409_841005
  intro a
  fin_cases a
  · exact context_12_109636_840768
  · exact context_12_109637_840849
  · exact context_12_109638_840923
  · exact context_12_109639_841004

theorem selected_cut_32699 : selected 9 ⟨841064, by decide⟩
    (prefixPartial 12 109640) = some ⟨12, 2, 0, 841064, 109640, 3913, 65536⟩ := by
  decide +kernel

theorem context_12_109640_841064 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109640 ⟨841064, by decide⟩ :=
  accepted_of_selected 12 109640 ⟨841064, by decide⟩ ⟨12, 2, 0, 841064, 109640, 3913, 65536⟩
    (by decide) selected_cut_32699

theorem selected_cut_32700 : selected 9 ⟨841116, by decide⟩
    (prefixPartial 12 109641) = some ⟨12, 2, 0, 841116, 109641, 3841, 65536⟩ := by
  decide +kernel

theorem context_12_109641_841116 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109641 ⟨841116, by decide⟩ :=
  accepted_of_selected 12 109641 ⟨841116, by decide⟩ ⟨12, 2, 0, 841116, 109641, 3841, 65536⟩
    (by decide) selected_cut_32700

theorem selected_cut_32701 : selected 9 ⟨841168, by decide⟩
    (prefixPartial 12 109642) = some ⟨12, 2, 0, 841168, 109642, 3517, 65536⟩ := by
  decide +kernel

theorem context_12_109642_841168 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109642 ⟨841168, by decide⟩ :=
  accepted_of_selected 12 109642 ⟨841168, by decide⟩ ⟨12, 2, 0, 841168, 109642, 3517, 65536⟩
    (by decide) selected_cut_32701

theorem selected_cut_32702 : selected 9 ⟨841236, by decide⟩
    (prefixPartial 12 109643) = some ⟨12, 2, 0, 841236, 109643, 3945, 65536⟩ := by
  decide +kernel

theorem context_12_109643_841236 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109643 ⟨841236, by decide⟩ :=
  accepted_of_selected 12 109643 ⟨841236, by decide⟩ ⟨12, 2, 0, 841236, 109643, 3945, 65536⟩
    (by decide) selected_cut_32702

theorem unmarked_context_11_27410_841237 : frontier 10 ⟨841237, by decide⟩
    (prefixCache 11 27410) (prefixPartial 11 27410) = false := by
  decide +kernel

theorem node_context_11_27410_841237 : EJMOriginalGlobalDAGData.nodes 10 ⟨841237, by decide⟩ =
    .split (coordinate 11) (![⟨841064, by decide⟩,⟨841116, by decide⟩,⟨841168, by decide⟩,⟨841236, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27410_841237 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27410 ⟨841237, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27410
    ⟨841237, by decide⟩ (by decide) (![⟨841064, by decide⟩,⟨841116, by decide⟩,⟨841168, by decide⟩,⟨841236, by decide⟩]) unmarked_context_11_27410_841237 node_context_11_27410_841237
  intro a
  fin_cases a
  · exact context_12_109640_841064
  · exact context_12_109641_841116
  · exact context_12_109642_841168
  · exact context_12_109643_841236

theorem selected_cut_32703 : selected 9 ⟨841281, by decide⟩
    (prefixPartial 12 109644) = some ⟨12, 2, 0, 841281, 109644, 3677, 65536⟩ := by
  decide +kernel

theorem context_12_109644_841281 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109644 ⟨841281, by decide⟩ :=
  accepted_of_selected 12 109644 ⟨841281, by decide⟩ ⟨12, 2, 0, 841281, 109644, 3677, 65536⟩
    (by decide) selected_cut_32703

theorem selected_cut_32704 : selected 9 ⟨841347, by decide⟩
    (prefixPartial 12 109645) = some ⟨12, 2, 0, 841347, 109645, 3853, 65536⟩ := by
  decide +kernel

theorem context_12_109645_841347 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109645 ⟨841347, by decide⟩ :=
  accepted_of_selected 12 109645 ⟨841347, by decide⟩ ⟨12, 2, 0, 841347, 109645, 3853, 65536⟩
    (by decide) selected_cut_32704

theorem selected_cut_32705 : selected 9 ⟨841392, by decide⟩
    (prefixPartial 12 109646) = some ⟨12, 2, 0, 841392, 109646, 3641, 65536⟩ := by
  decide +kernel

theorem context_12_109646_841392 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109646 ⟨841392, by decide⟩ :=
  accepted_of_selected 12 109646 ⟨841392, by decide⟩ ⟨12, 2, 0, 841392, 109646, 3641, 65536⟩
    (by decide) selected_cut_32705

theorem selected_cut_32706 : selected 9 ⟨841453, by decide⟩
    (prefixPartial 12 109647) = some ⟨12, 2, 0, 841453, 109647, 3609, 65536⟩ := by
  decide +kernel

theorem context_12_109647_841453 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109647 ⟨841453, by decide⟩ :=
  accepted_of_selected 12 109647 ⟨841453, by decide⟩ ⟨12, 2, 0, 841453, 109647, 3609, 65536⟩
    (by decide) selected_cut_32706

theorem unmarked_context_11_27411_841454 : frontier 10 ⟨841454, by decide⟩
    (prefixCache 11 27411) (prefixPartial 11 27411) = false := by
  decide +kernel

theorem node_context_11_27411_841454 : EJMOriginalGlobalDAGData.nodes 10 ⟨841454, by decide⟩ =
    .split (coordinate 11) (![⟨841281, by decide⟩,⟨841347, by decide⟩,⟨841392, by decide⟩,⟨841453, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27411_841454 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27411 ⟨841454, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27411
    ⟨841454, by decide⟩ (by decide) (![⟨841281, by decide⟩,⟨841347, by decide⟩,⟨841392, by decide⟩,⟨841453, by decide⟩]) unmarked_context_11_27411_841454 node_context_11_27411_841454
  intro a
  fin_cases a
  · exact context_12_109644_841281
  · exact context_12_109645_841347
  · exact context_12_109646_841392
  · exact context_12_109647_841453

theorem unmarked_context_10_6852_841455 : frontier 11 ⟨841455, by decide⟩
    (prefixCache 10 6852) (prefixPartial 10 6852) = false := by
  decide +kernel

theorem node_context_10_6852_841455 : EJMOriginalGlobalDAGData.nodes 11 ⟨841455, by decide⟩ =
    .split (coordinate 10) (![⟨840697, by decide⟩,⟨841005, by decide⟩,⟨841237, by decide⟩,⟨841454, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6852_841455 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6852 ⟨841455, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6852
    ⟨841455, by decide⟩ (by decide) (![⟨840697, by decide⟩,⟨841005, by decide⟩,⟨841237, by decide⟩,⟨841454, by decide⟩]) unmarked_context_10_6852_841455 node_context_10_6852_841455
  intro a
  fin_cases a
  · exact context_11_27408_840697
  · exact context_11_27409_841005
  · exact context_11_27410_841237
  · exact context_11_27411_841454

theorem selected_cut_32707 : selected 9 ⟨789343, by decide⟩
    (prefixPartial 12 109648) = some ⟨12, 1, 0, 789343, 109648, 1, 65536⟩ := by
  decide +kernel

theorem context_12_109648_789343 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109648 ⟨789343, by decide⟩ :=
  accepted_of_selected 12 109648 ⟨789343, by decide⟩ ⟨12, 1, 0, 789343, 109648, 1, 65536⟩
    (by decide) selected_cut_32707

theorem selected_cut_32708 : selected 9 ⟨841513, by decide⟩
    (prefixPartial 12 109649) = some ⟨12, 2, 0, 841513, 109649, 3993, 65536⟩ := by
  decide +kernel

theorem context_12_109649_841513 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109649 ⟨841513, by decide⟩ :=
  accepted_of_selected 12 109649 ⟨841513, by decide⟩ ⟨12, 2, 0, 841513, 109649, 3993, 65536⟩
    (by decide) selected_cut_32708

theorem selected_cut_32709 : selected 9 ⟨841552, by decide⟩
    (prefixPartial 12 109650) = some ⟨12, 2, 0, 841552, 109650, 3417, 65536⟩ := by
  decide +kernel

theorem context_12_109650_841552 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109650 ⟨841552, by decide⟩ :=
  accepted_of_selected 12 109650 ⟨841552, by decide⟩ ⟨12, 2, 0, 841552, 109650, 3417, 65536⟩
    (by decide) selected_cut_32709

theorem selected_cut_32710 : selected 9 ⟨841613, by decide⟩
    (prefixPartial 12 109651) = some ⟨12, 2, 0, 841613, 109651, 3929, 65536⟩ := by
  decide +kernel

theorem context_12_109651_841613 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109651 ⟨841613, by decide⟩ :=
  accepted_of_selected 12 109651 ⟨841613, by decide⟩ ⟨12, 2, 0, 841613, 109651, 3929, 65536⟩
    (by decide) selected_cut_32710

theorem unmarked_context_11_27412_841614 : frontier 10 ⟨841614, by decide⟩
    (prefixCache 11 27412) (prefixPartial 11 27412) = false := by
  decide +kernel

theorem node_context_11_27412_841614 : EJMOriginalGlobalDAGData.nodes 10 ⟨841614, by decide⟩ =
    .split (coordinate 11) (![⟨789343, by decide⟩,⟨841513, by decide⟩,⟨841552, by decide⟩,⟨841613, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27412_841614 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27412 ⟨841614, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27412
    ⟨841614, by decide⟩ (by decide) (![⟨789343, by decide⟩,⟨841513, by decide⟩,⟨841552, by decide⟩,⟨841613, by decide⟩]) unmarked_context_11_27412_841614 node_context_11_27412_841614
  intro a
  fin_cases a
  · exact context_12_109648_789343
  · exact context_12_109649_841513
  · exact context_12_109650_841552
  · exact context_12_109651_841613

theorem selected_cut_32711 : selected 9 ⟨841662, by decide⟩
    (prefixPartial 12 109652) = some ⟨12, 2, 0, 841662, 109652, 3929, 65536⟩ := by
  decide +kernel

theorem context_12_109652_841662 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109652 ⟨841662, by decide⟩ :=
  accepted_of_selected 12 109652 ⟨841662, by decide⟩ ⟨12, 2, 0, 841662, 109652, 3929, 65536⟩
    (by decide) selected_cut_32711

theorem selected_cut_32712 : selected 9 ⟨841717, by decide⟩
    (prefixPartial 12 109653) = some ⟨12, 2, 0, 841717, 109653, 3997, 65536⟩ := by
  decide +kernel

theorem context_12_109653_841717 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109653 ⟨841717, by decide⟩ :=
  accepted_of_selected 12 109653 ⟨841717, by decide⟩ ⟨12, 2, 0, 841717, 109653, 3997, 65536⟩
    (by decide) selected_cut_32712

theorem selected_cut_32713 : selected 9 ⟨841761, by decide⟩
    (prefixPartial 12 109654) = some ⟨12, 2, 0, 841761, 109654, 3797, 65536⟩ := by
  decide +kernel

theorem context_12_109654_841761 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109654 ⟨841761, by decide⟩ :=
  accepted_of_selected 12 109654 ⟨841761, by decide⟩ ⟨12, 2, 0, 841761, 109654, 3797, 65536⟩
    (by decide) selected_cut_32713

theorem selected_cut_32714 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 438620) = some ⟨13, 1, 0, 3444, 438620, 1, 16384⟩ := by
  decide +kernel

theorem context_13_438620_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438620 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 438620 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 438620, 1, 16384⟩
    (by decide) selected_cut_32714

theorem selected_cut_32715 : selected 8 ⟨841783, by decide⟩
    (prefixPartial 13 438621) = some ⟨13, 2, 0, 841783, 438621, 1561, 16384⟩ := by
  decide +kernel

theorem context_13_438621_841783 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438621 ⟨841783, by decide⟩ :=
  accepted_of_selected 13 438621 ⟨841783, by decide⟩ ⟨13, 2, 0, 841783, 438621, 1561, 16384⟩
    (by decide) selected_cut_32715

theorem selected_cut_32716 : selected 8 ⟨841822, by decide⟩
    (prefixPartial 13 438622) = some ⟨13, 2, 0, 841822, 438622, 1837, 16384⟩ := by
  decide +kernel

theorem context_13_438622_841822 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438622 ⟨841822, by decide⟩ :=
  accepted_of_selected 13 438622 ⟨841822, by decide⟩ ⟨13, 2, 0, 841822, 438622, 1837, 16384⟩
    (by decide) selected_cut_32716

theorem selected_cut_32717 : selected 8 ⟨841828, by decide⟩
    (prefixPartial 13 438623) = some ⟨13, 2, 0, 841828, 438623, 853, 16384⟩ := by
  decide +kernel

theorem context_13_438623_841828 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438623 ⟨841828, by decide⟩ :=
  accepted_of_selected 13 438623 ⟨841828, by decide⟩ ⟨13, 2, 0, 841828, 438623, 853, 16384⟩
    (by decide) selected_cut_32717

theorem unmarked_context_12_109655_841829 : frontier 9 ⟨841829, by decide⟩
    (prefixCache 12 109655) (prefixPartial 12 109655) = false := by
  decide +kernel

theorem node_context_12_109655_841829 : EJMOriginalGlobalDAGData.nodes 9 ⟨841829, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨841783, by decide⟩,⟨841822, by decide⟩,⟨841828, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_109655_841829 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109655 ⟨841829, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 109655
    ⟨841829, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨841783, by decide⟩,⟨841822, by decide⟩,⟨841828, by decide⟩]) unmarked_context_12_109655_841829 node_context_12_109655_841829
  intro a
  fin_cases a
  · exact context_13_438620_3444
  · exact context_13_438621_841783
  · exact context_13_438622_841822
  · exact context_13_438623_841828

theorem unmarked_context_11_27413_841830 : frontier 10 ⟨841830, by decide⟩
    (prefixCache 11 27413) (prefixPartial 11 27413) = false := by
  decide +kernel

theorem node_context_11_27413_841830 : EJMOriginalGlobalDAGData.nodes 10 ⟨841830, by decide⟩ =
    .split (coordinate 11) (![⟨841662, by decide⟩,⟨841717, by decide⟩,⟨841761, by decide⟩,⟨841829, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27413_841830 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27413 ⟨841830, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27413
    ⟨841830, by decide⟩ (by decide) (![⟨841662, by decide⟩,⟨841717, by decide⟩,⟨841761, by decide⟩,⟨841829, by decide⟩]) unmarked_context_11_27413_841830 node_context_11_27413_841830
  intro a
  fin_cases a
  · exact context_12_109652_841662
  · exact context_12_109653_841717
  · exact context_12_109654_841761
  · exact context_12_109655_841829

theorem selected_cut_32718 : selected 9 ⟨841881, by decide⟩
    (prefixPartial 12 109656) = some ⟨12, 2, 0, 841881, 109656, 3397, 65536⟩ := by
  decide +kernel

theorem context_12_109656_841881 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109656 ⟨841881, by decide⟩ :=
  accepted_of_selected 12 109656 ⟨841881, by decide⟩ ⟨12, 2, 0, 841881, 109656, 3397, 65536⟩
    (by decide) selected_cut_32718

theorem selected_cut_32719 : selected 9 ⟨841927, by decide⟩
    (prefixPartial 12 109657) = some ⟨12, 2, 0, 841927, 109657, 3573, 65536⟩ := by
  decide +kernel

theorem context_12_109657_841927 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109657 ⟨841927, by decide⟩ :=
  accepted_of_selected 12 109657 ⟨841927, by decide⟩ ⟨12, 2, 0, 841927, 109657, 3573, 65536⟩
    (by decide) selected_cut_32719

theorem selected_cut_32720 : selected 9 ⟨841963, by decide⟩
    (prefixPartial 12 109658) = some ⟨12, 2, 0, 841963, 109658, 2897, 65536⟩ := by
  decide +kernel

theorem context_12_109658_841963 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109658 ⟨841963, by decide⟩ :=
  accepted_of_selected 12 109658 ⟨841963, by decide⟩ ⟨12, 2, 0, 841963, 109658, 2897, 65536⟩
    (by decide) selected_cut_32720

theorem selected_cut_32721 : selected 9 ⟨842015, by decide⟩
    (prefixPartial 12 109659) = some ⟨12, 2, 0, 842015, 109659, 3545, 65536⟩ := by
  decide +kernel

theorem context_12_109659_842015 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109659 ⟨842015, by decide⟩ :=
  accepted_of_selected 12 109659 ⟨842015, by decide⟩ ⟨12, 2, 0, 842015, 109659, 3545, 65536⟩
    (by decide) selected_cut_32721

theorem unmarked_context_11_27414_842016 : frontier 10 ⟨842016, by decide⟩
    (prefixCache 11 27414) (prefixPartial 11 27414) = false := by
  decide +kernel

theorem node_context_11_27414_842016 : EJMOriginalGlobalDAGData.nodes 10 ⟨842016, by decide⟩ =
    .split (coordinate 11) (![⟨841881, by decide⟩,⟨841927, by decide⟩,⟨841963, by decide⟩,⟨842015, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27414_842016 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27414 ⟨842016, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27414
    ⟨842016, by decide⟩ (by decide) (![⟨841881, by decide⟩,⟨841927, by decide⟩,⟨841963, by decide⟩,⟨842015, by decide⟩]) unmarked_context_11_27414_842016 node_context_11_27414_842016
  intro a
  fin_cases a
  · exact context_12_109656_841881
  · exact context_12_109657_841927
  · exact context_12_109658_841963
  · exact context_12_109659_842015

theorem selected_cut_32722 : selected 9 ⟨842059, by decide⟩
    (prefixPartial 12 109660) = some ⟨12, 2, 0, 842059, 109660, 3421, 65536⟩ := by
  decide +kernel

theorem context_12_109660_842059 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109660 ⟨842059, by decide⟩ :=
  accepted_of_selected 12 109660 ⟨842059, by decide⟩ ⟨12, 2, 0, 842059, 109660, 3421, 65536⟩
    (by decide) selected_cut_32722

theorem selected_cut_32723 : selected 9 ⟨842111, by decide⟩
    (prefixPartial 12 109661) = some ⟨12, 2, 0, 842111, 109661, 3785, 65536⟩ := by
  decide +kernel

theorem context_12_109661_842111 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109661 ⟨842111, by decide⟩ :=
  accepted_of_selected 12 109661 ⟨842111, by decide⟩ ⟨12, 2, 0, 842111, 109661, 3785, 65536⟩
    (by decide) selected_cut_32723

theorem selected_cut_32724 : selected 9 ⟨842152, by decide⟩
    (prefixPartial 12 109662) = some ⟨12, 2, 0, 842152, 109662, 3305, 65536⟩ := by
  decide +kernel

theorem context_12_109662_842152 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109662 ⟨842152, by decide⟩ :=
  accepted_of_selected 12 109662 ⟨842152, by decide⟩ ⟨12, 2, 0, 842152, 109662, 3305, 65536⟩
    (by decide) selected_cut_32724

theorem selected_cut_32725 : selected 9 ⟨842195, by decide⟩
    (prefixPartial 12 109663) = some ⟨12, 2, 0, 842195, 109663, 3389, 65536⟩ := by
  decide +kernel

theorem context_12_109663_842195 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109663 ⟨842195, by decide⟩ :=
  accepted_of_selected 12 109663 ⟨842195, by decide⟩ ⟨12, 2, 0, 842195, 109663, 3389, 65536⟩
    (by decide) selected_cut_32725

theorem unmarked_context_11_27415_842196 : frontier 10 ⟨842196, by decide⟩
    (prefixCache 11 27415) (prefixPartial 11 27415) = false := by
  decide +kernel

theorem node_context_11_27415_842196 : EJMOriginalGlobalDAGData.nodes 10 ⟨842196, by decide⟩ =
    .split (coordinate 11) (![⟨842059, by decide⟩,⟨842111, by decide⟩,⟨842152, by decide⟩,⟨842195, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27415_842196 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27415 ⟨842196, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27415
    ⟨842196, by decide⟩ (by decide) (![⟨842059, by decide⟩,⟨842111, by decide⟩,⟨842152, by decide⟩,⟨842195, by decide⟩]) unmarked_context_11_27415_842196 node_context_11_27415_842196
  intro a
  fin_cases a
  · exact context_12_109660_842059
  · exact context_12_109661_842111
  · exact context_12_109662_842152
  · exact context_12_109663_842195

theorem unmarked_context_10_6853_842197 : frontier 11 ⟨842197, by decide⟩
    (prefixCache 10 6853) (prefixPartial 10 6853) = false := by
  decide +kernel

theorem node_context_10_6853_842197 : EJMOriginalGlobalDAGData.nodes 11 ⟨842197, by decide⟩ =
    .split (coordinate 10) (![⟨841614, by decide⟩,⟨841830, by decide⟩,⟨842016, by decide⟩,⟨842196, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6853_842197 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6853 ⟨842197, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6853
    ⟨842197, by decide⟩ (by decide) (![⟨841614, by decide⟩,⟨841830, by decide⟩,⟨842016, by decide⟩,⟨842196, by decide⟩]) unmarked_context_10_6853_842197 node_context_10_6853_842197
  intro a
  fin_cases a
  · exact context_11_27412_841614
  · exact context_11_27413_841830
  · exact context_11_27414_842016
  · exact context_11_27415_842196

theorem selected_cut_32726 : selected 9 ⟨842359, by decide⟩
    (prefixPartial 12 109664) = some ⟨12, 2, 0, 842359, 109664, 2441, 65536⟩ := by
  decide +kernel

theorem context_12_109664_842359 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109664 ⟨842359, by decide⟩ :=
  accepted_of_selected 12 109664 ⟨842359, by decide⟩ ⟨12, 2, 0, 842359, 109664, 2441, 65536⟩
    (by decide) selected_cut_32726

theorem selected_cut_32727 : selected 9 ⟨842407, by decide⟩
    (prefixPartial 12 109665) = some ⟨12, 2, 0, 842407, 109665, 3257, 65536⟩ := by
  decide +kernel

theorem context_12_109665_842407 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109665 ⟨842407, by decide⟩ :=
  accepted_of_selected 12 109665 ⟨842407, by decide⟩ ⟨12, 2, 0, 842407, 109665, 3257, 65536⟩
    (by decide) selected_cut_32727

theorem selected_cut_32728 : selected 9 ⟨842438, by decide⟩
    (prefixPartial 12 109666) = some ⟨12, 2, 0, 842438, 109666, 2989, 65536⟩ := by
  decide +kernel

theorem context_12_109666_842438 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109666 ⟨842438, by decide⟩ :=
  accepted_of_selected 12 109666 ⟨842438, by decide⟩ ⟨12, 2, 0, 842438, 109666, 2989, 65536⟩
    (by decide) selected_cut_32728

theorem selected_cut_32729 : selected 9 ⟨842478, by decide⟩
    (prefixPartial 12 109667) = some ⟨12, 2, 0, 842478, 109667, 3189, 65536⟩ := by
  decide +kernel

theorem context_12_109667_842478 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109667 ⟨842478, by decide⟩ :=
  accepted_of_selected 12 109667 ⟨842478, by decide⟩ ⟨12, 2, 0, 842478, 109667, 3189, 65536⟩
    (by decide) selected_cut_32729

theorem unmarked_context_11_27416_842479 : frontier 10 ⟨842479, by decide⟩
    (prefixCache 11 27416) (prefixPartial 11 27416) = false := by
  decide +kernel

theorem node_context_11_27416_842479 : EJMOriginalGlobalDAGData.nodes 10 ⟨842479, by decide⟩ =
    .split (coordinate 11) (![⟨842359, by decide⟩,⟨842407, by decide⟩,⟨842438, by decide⟩,⟨842478, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27416_842479 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27416 ⟨842479, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27416
    ⟨842479, by decide⟩ (by decide) (![⟨842359, by decide⟩,⟨842407, by decide⟩,⟨842438, by decide⟩,⟨842478, by decide⟩]) unmarked_context_11_27416_842479 node_context_11_27416_842479
  intro a
  fin_cases a
  · exact context_12_109664_842359
  · exact context_12_109665_842407
  · exact context_12_109666_842438
  · exact context_12_109667_842478

theorem selected_cut_32730 : selected 9 ⟨842530, by decide⟩
    (prefixPartial 12 109668) = some ⟨12, 2, 0, 842530, 109668, 3497, 65536⟩ := by
  decide +kernel

theorem context_12_109668_842530 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109668 ⟨842530, by decide⟩ :=
  accepted_of_selected 12 109668 ⟨842530, by decide⟩ ⟨12, 2, 0, 842530, 109668, 3497, 65536⟩
    (by decide) selected_cut_32730

theorem selected_cut_32731 : selected 9 ⟨842579, by decide⟩
    (prefixPartial 12 109669) = some ⟨12, 2, 0, 842579, 109669, 3401, 65536⟩ := by
  decide +kernel

theorem context_12_109669_842579 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109669 ⟨842579, by decide⟩ :=
  accepted_of_selected 12 109669 ⟨842579, by decide⟩ ⟨12, 2, 0, 842579, 109669, 3401, 65536⟩
    (by decide) selected_cut_32731

theorem selected_cut_32732 : selected 9 ⟨842625, by decide⟩
    (prefixPartial 12 109670) = some ⟨12, 2, 0, 842625, 109670, 3341, 65536⟩ := by
  decide +kernel

theorem context_12_109670_842625 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109670 ⟨842625, by decide⟩ :=
  accepted_of_selected 12 109670 ⟨842625, by decide⟩ ⟨12, 2, 0, 842625, 109670, 3341, 65536⟩
    (by decide) selected_cut_32732

theorem selected_cut_32733 : selected 9 ⟨842688, by decide⟩
    (prefixPartial 12 109671) = some ⟨12, 2, 0, 842688, 109671, 3749, 65536⟩ := by
  decide +kernel

theorem context_12_109671_842688 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109671 ⟨842688, by decide⟩ :=
  accepted_of_selected 12 109671 ⟨842688, by decide⟩ ⟨12, 2, 0, 842688, 109671, 3749, 65536⟩
    (by decide) selected_cut_32733

theorem unmarked_context_11_27417_842689 : frontier 10 ⟨842689, by decide⟩
    (prefixCache 11 27417) (prefixPartial 11 27417) = false := by
  decide +kernel

theorem node_context_11_27417_842689 : EJMOriginalGlobalDAGData.nodes 10 ⟨842689, by decide⟩ =
    .split (coordinate 11) (![⟨842530, by decide⟩,⟨842579, by decide⟩,⟨842625, by decide⟩,⟨842688, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27417_842689 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27417 ⟨842689, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27417
    ⟨842689, by decide⟩ (by decide) (![⟨842530, by decide⟩,⟨842579, by decide⟩,⟨842625, by decide⟩,⟨842688, by decide⟩]) unmarked_context_11_27417_842689 node_context_11_27417_842689
  intro a
  fin_cases a
  · exact context_12_109668_842530
  · exact context_12_109669_842579
  · exact context_12_109670_842625
  · exact context_12_109671_842688

theorem selected_cut_32734 : selected 9 ⟨842727, by decide⟩
    (prefixPartial 12 109672) = some ⟨12, 2, 0, 842727, 109672, 2941, 65536⟩ := by
  decide +kernel

theorem context_12_109672_842727 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109672 ⟨842727, by decide⟩ :=
  accepted_of_selected 12 109672 ⟨842727, by decide⟩ ⟨12, 2, 0, 842727, 109672, 2941, 65536⟩
    (by decide) selected_cut_32734

theorem selected_cut_32735 : selected 9 ⟨842764, by decide⟩
    (prefixPartial 12 109673) = some ⟨12, 2, 0, 842764, 109673, 3073, 65536⟩ := by
  decide +kernel

theorem context_12_109673_842764 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109673 ⟨842764, by decide⟩ :=
  accepted_of_selected 12 109673 ⟨842764, by decide⟩ ⟨12, 2, 0, 842764, 109673, 3073, 65536⟩
    (by decide) selected_cut_32735

theorem selected_cut_32736 : selected 9 ⟨842797, by decide⟩
    (prefixPartial 12 109674) = some ⟨12, 2, 0, 842797, 109674, 2581, 65536⟩ := by
  decide +kernel

theorem context_12_109674_842797 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109674 ⟨842797, by decide⟩ :=
  accepted_of_selected 12 109674 ⟨842797, by decide⟩ ⟨12, 2, 0, 842797, 109674, 2581, 65536⟩
    (by decide) selected_cut_32736

theorem selected_cut_32737 : selected 9 ⟨842842, by decide⟩
    (prefixPartial 12 109675) = some ⟨12, 2, 0, 842842, 109675, 2917, 65536⟩ := by
  decide +kernel

theorem context_12_109675_842842 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109675 ⟨842842, by decide⟩ :=
  accepted_of_selected 12 109675 ⟨842842, by decide⟩ ⟨12, 2, 0, 842842, 109675, 2917, 65536⟩
    (by decide) selected_cut_32737

theorem unmarked_context_11_27418_842843 : frontier 10 ⟨842843, by decide⟩
    (prefixCache 11 27418) (prefixPartial 11 27418) = false := by
  decide +kernel

theorem node_context_11_27418_842843 : EJMOriginalGlobalDAGData.nodes 10 ⟨842843, by decide⟩ =
    .split (coordinate 11) (![⟨842727, by decide⟩,⟨842764, by decide⟩,⟨842797, by decide⟩,⟨842842, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27418_842843 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27418 ⟨842843, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27418
    ⟨842843, by decide⟩ (by decide) (![⟨842727, by decide⟩,⟨842764, by decide⟩,⟨842797, by decide⟩,⟨842842, by decide⟩]) unmarked_context_11_27418_842843 node_context_11_27418_842843
  intro a
  fin_cases a
  · exact context_12_109672_842727
  · exact context_12_109673_842764
  · exact context_12_109674_842797
  · exact context_12_109675_842842

theorem selected_cut_32738 : selected 9 ⟨842881, by decide⟩
    (prefixPartial 12 109676) = some ⟨12, 2, 0, 842881, 109676, 3065, 65536⟩ := by
  decide +kernel

theorem context_12_109676_842881 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109676 ⟨842881, by decide⟩ :=
  accepted_of_selected 12 109676 ⟨842881, by decide⟩ ⟨12, 2, 0, 842881, 109676, 3065, 65536⟩
    (by decide) selected_cut_32738

theorem selected_cut_32739 : selected 9 ⟨842926, by decide⟩
    (prefixPartial 12 109677) = some ⟨12, 2, 0, 842926, 109677, 3257, 65536⟩ := by
  decide +kernel

theorem context_12_109677_842926 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109677 ⟨842926, by decide⟩ :=
  accepted_of_selected 12 109677 ⟨842926, by decide⟩ ⟨12, 2, 0, 842926, 109677, 3257, 65536⟩
    (by decide) selected_cut_32739

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
