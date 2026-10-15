/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover176
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_16996 : selected 8 ⟨431922, by decide⟩
    (prefixPartial 13 114085) = some ⟨13, 2, 0, 431922, 114085, 1481, 16384⟩ := by
  decide +kernel

theorem context_13_114085_431922 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 114085 ⟨431922, by decide⟩ :=
  accepted_of_selected 13 114085 ⟨431922, by decide⟩ ⟨13, 2, 0, 431922, 114085, 1481, 16384⟩
    (by decide) selected_cut_16996

theorem selected_cut_16997 : selected 8 ⟨431969, by decide⟩
    (prefixPartial 13 114086) = some ⟨13, 2, 0, 431969, 114086, 2597, 16384⟩ := by
  decide +kernel

theorem context_13_114086_431969 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 114086 ⟨431969, by decide⟩ :=
  accepted_of_selected 13 114086 ⟨431969, by decide⟩ ⟨13, 2, 0, 431969, 114086, 2597, 16384⟩
    (by decide) selected_cut_16997

theorem selected_cut_16998 : selected 8 ⟨431992, by decide⟩
    (prefixPartial 13 114087) = some ⟨13, 2, 0, 431992, 114087, 1093, 16384⟩ := by
  decide +kernel

theorem context_13_114087_431992 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 114087 ⟨431992, by decide⟩ :=
  accepted_of_selected 13 114087 ⟨431992, by decide⟩ ⟨13, 2, 0, 431992, 114087, 1093, 16384⟩
    (by decide) selected_cut_16998

theorem unmarked_context_12_28521_431993 : frontier 9 ⟨431993, by decide⟩
    (prefixCache 12 28521) (prefixPartial 12 28521) = false := by
  decide +kernel

theorem node_context_12_28521_431993 : EJMOriginalGlobalDAGData.nodes 9 ⟨431993, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨431922, by decide⟩,⟨431969, by decide⟩,⟨431992, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28521_431993 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28521 ⟨431993, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28521
    ⟨431993, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨431922, by decide⟩,⟨431969, by decide⟩,⟨431992, by decide⟩]) unmarked_context_12_28521_431993 node_context_12_28521_431993
  intro a
  fin_cases a
  · exact context_13_114084_3444
  · exact context_13_114085_431922
  · exact context_13_114086_431969
  · exact context_13_114087_431992

theorem selected_cut_16999 : selected 9 ⟨432036, by decide⟩
    (prefixPartial 12 28522) = some ⟨12, 2, 0, 432036, 28522, 3525, 65536⟩ := by
  decide +kernel

theorem context_12_28522_432036 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28522 ⟨432036, by decide⟩ :=
  accepted_of_selected 12 28522 ⟨432036, by decide⟩ ⟨12, 2, 0, 432036, 28522, 3525, 65536⟩
    (by decide) selected_cut_16999

theorem selected_cut_17000 : selected 9 ⟨432079, by decide⟩
    (prefixPartial 12 28523) = some ⟨12, 2, 0, 432079, 28523, 3253, 65536⟩ := by
  decide +kernel

theorem context_12_28523_432079 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28523 ⟨432079, by decide⟩ :=
  accepted_of_selected 12 28523 ⟨432079, by decide⟩ ⟨12, 2, 0, 432079, 28523, 3253, 65536⟩
    (by decide) selected_cut_17000

theorem unmarked_context_11_7130_432080 : frontier 10 ⟨432080, by decide⟩
    (prefixCache 11 7130) (prefixPartial 11 7130) = false := by
  decide +kernel

theorem node_context_11_7130_432080 : EJMOriginalGlobalDAGData.nodes 10 ⟨432080, by decide⟩ =
    .split (coordinate 11) (![⟨431897, by decide⟩,⟨431993, by decide⟩,⟨432036, by decide⟩,⟨432079, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_7130_432080 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7130 ⟨432080, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 7130
    ⟨432080, by decide⟩ (by decide) (![⟨431897, by decide⟩,⟨431993, by decide⟩,⟨432036, by decide⟩,⟨432079, by decide⟩]) unmarked_context_11_7130_432080 node_context_11_7130_432080
  intro a
  fin_cases a
  · exact context_12_28520_431897
  · exact context_12_28521_431993
  · exact context_12_28522_432036
  · exact context_12_28523_432079

theorem selected_cut_17001 : selected 9 ⟨432111, by decide⟩
    (prefixPartial 12 28524) = some ⟨12, 2, 0, 432111, 28524, 2649, 65536⟩ := by
  decide +kernel

theorem context_12_28524_432111 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28524 ⟨432111, by decide⟩ :=
  accepted_of_selected 12 28524 ⟨432111, by decide⟩ ⟨12, 2, 0, 432111, 28524, 2649, 65536⟩
    (by decide) selected_cut_17001

theorem selected_cut_17002 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 114100) = some ⟨13, 1, 0, 3444, 114100, 1, 16384⟩ := by
  decide +kernel

theorem context_13_114100_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 114100 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 114100 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 114100, 1, 16384⟩
    (by decide) selected_cut_17002

theorem selected_cut_17003 : selected 8 ⟨432131, by decide⟩
    (prefixPartial 13 114101) = some ⟨13, 2, 0, 432131, 114101, 1205, 16384⟩ := by
  decide +kernel

theorem context_13_114101_432131 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 114101 ⟨432131, by decide⟩ :=
  accepted_of_selected 13 114101 ⟨432131, by decide⟩ ⟨13, 2, 0, 432131, 114101, 1205, 16384⟩
    (by decide) selected_cut_17003

theorem selected_cut_17004 : selected 8 ⟨432160, by decide⟩
    (prefixPartial 13 114102) = some ⟨13, 2, 0, 432160, 114102, 2449, 16384⟩ := by
  decide +kernel

theorem context_13_114102_432160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 114102 ⟨432160, by decide⟩ :=
  accepted_of_selected 13 114102 ⟨432160, by decide⟩ ⟨13, 2, 0, 432160, 114102, 2449, 16384⟩
    (by decide) selected_cut_17004

theorem selected_cut_17005 : selected 8 ⟨432173, by decide⟩
    (prefixPartial 13 114103) = some ⟨13, 2, 0, 432173, 114103, 933, 16384⟩ := by
  decide +kernel

theorem context_13_114103_432173 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 114103 ⟨432173, by decide⟩ :=
  accepted_of_selected 13 114103 ⟨432173, by decide⟩ ⟨13, 2, 0, 432173, 114103, 933, 16384⟩
    (by decide) selected_cut_17005

theorem unmarked_context_12_28525_432174 : frontier 9 ⟨432174, by decide⟩
    (prefixCache 12 28525) (prefixPartial 12 28525) = false := by
  decide +kernel

theorem node_context_12_28525_432174 : EJMOriginalGlobalDAGData.nodes 9 ⟨432174, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨432131, by decide⟩,⟨432160, by decide⟩,⟨432173, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28525_432174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28525 ⟨432174, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28525
    ⟨432174, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨432131, by decide⟩,⟨432160, by decide⟩,⟨432173, by decide⟩]) unmarked_context_12_28525_432174 node_context_12_28525_432174
  intro a
  fin_cases a
  · exact context_13_114100_3444
  · exact context_13_114101_432131
  · exact context_13_114102_432160
  · exact context_13_114103_432173

theorem selected_cut_17006 : selected 9 ⟨432217, by decide⟩
    (prefixPartial 12 28526) = some ⟨12, 2, 0, 432217, 28526, 3021, 65536⟩ := by
  decide +kernel

theorem context_12_28526_432217 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28526 ⟨432217, by decide⟩ :=
  accepted_of_selected 12 28526 ⟨432217, by decide⟩ ⟨12, 2, 0, 432217, 28526, 3021, 65536⟩
    (by decide) selected_cut_17006

theorem selected_cut_17007 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 114108) = some ⟨13, 1, 0, 3444, 114108, 1, 16384⟩ := by
  decide +kernel

theorem context_13_114108_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 114108 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 114108 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 114108, 1, 16384⟩
    (by decide) selected_cut_17007

theorem selected_cut_17008 : selected 8 ⟨432244, by decide⟩
    (prefixPartial 13 114109) = some ⟨13, 2, 0, 432244, 114109, 1233, 16384⟩ := by
  decide +kernel

theorem context_13_114109_432244 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 114109 ⟨432244, by decide⟩ :=
  accepted_of_selected 13 114109 ⟨432244, by decide⟩ ⟨13, 2, 0, 432244, 114109, 1233, 16384⟩
    (by decide) selected_cut_17008

theorem selected_cut_17009 : selected 8 ⟨432285, by decide⟩
    (prefixPartial 13 114110) = some ⟨13, 2, 0, 432285, 114110, 2625, 16384⟩ := by
  decide +kernel

theorem context_13_114110_432285 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 114110 ⟨432285, by decide⟩ :=
  accepted_of_selected 13 114110 ⟨432285, by decide⟩ ⟨13, 2, 0, 432285, 114110, 2625, 16384⟩
    (by decide) selected_cut_17009

theorem selected_cut_17010 : selected 8 ⟨432305, by decide⟩
    (prefixPartial 13 114111) = some ⟨13, 2, 0, 432305, 114111, 1213, 16384⟩ := by
  decide +kernel

theorem context_13_114111_432305 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 114111 ⟨432305, by decide⟩ :=
  accepted_of_selected 13 114111 ⟨432305, by decide⟩ ⟨13, 2, 0, 432305, 114111, 1213, 16384⟩
    (by decide) selected_cut_17010

theorem unmarked_context_12_28527_432306 : frontier 9 ⟨432306, by decide⟩
    (prefixCache 12 28527) (prefixPartial 12 28527) = false := by
  decide +kernel

theorem node_context_12_28527_432306 : EJMOriginalGlobalDAGData.nodes 9 ⟨432306, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨432244, by decide⟩,⟨432285, by decide⟩,⟨432305, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28527_432306 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28527 ⟨432306, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28527
    ⟨432306, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨432244, by decide⟩,⟨432285, by decide⟩,⟨432305, by decide⟩]) unmarked_context_12_28527_432306 node_context_12_28527_432306
  intro a
  fin_cases a
  · exact context_13_114108_3444
  · exact context_13_114109_432244
  · exact context_13_114110_432285
  · exact context_13_114111_432305

theorem unmarked_context_11_7131_432307 : frontier 10 ⟨432307, by decide⟩
    (prefixCache 11 7131) (prefixPartial 11 7131) = false := by
  decide +kernel

theorem node_context_11_7131_432307 : EJMOriginalGlobalDAGData.nodes 10 ⟨432307, by decide⟩ =
    .split (coordinate 11) (![⟨432111, by decide⟩,⟨432174, by decide⟩,⟨432217, by decide⟩,⟨432306, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_7131_432307 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7131 ⟨432307, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 7131
    ⟨432307, by decide⟩ (by decide) (![⟨432111, by decide⟩,⟨432174, by decide⟩,⟨432217, by decide⟩,⟨432306, by decide⟩]) unmarked_context_11_7131_432307 node_context_11_7131_432307
  intro a
  fin_cases a
  · exact context_12_28524_432111
  · exact context_12_28525_432174
  · exact context_12_28526_432217
  · exact context_12_28527_432306

theorem unmarked_context_10_1782_432308 : frontier 11 ⟨432308, by decide⟩
    (prefixCache 10 1782) (prefixPartial 10 1782) = false := by
  decide +kernel

theorem node_context_10_1782_432308 : EJMOriginalGlobalDAGData.nodes 11 ⟨432308, by decide⟩ =
    .split (coordinate 10) (![⟨431727, by decide⟩,⟨431855, by decide⟩,⟨432080, by decide⟩,⟨432307, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1782_432308 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1782 ⟨432308, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1782
    ⟨432308, by decide⟩ (by decide) (![⟨431727, by decide⟩,⟨431855, by decide⟩,⟨432080, by decide⟩,⟨432307, by decide⟩]) unmarked_context_10_1782_432308 node_context_10_1782_432308
  intro a
  fin_cases a
  · exact context_11_7128_431727
  · exact context_11_7129_431855
  · exact context_11_7130_432080
  · exact context_11_7131_432307

theorem selected_cut_17011 : selected 9 ⟨432348, by decide⟩
    (prefixPartial 12 28528) = some ⟨12, 2, 0, 432348, 28528, 3237, 65536⟩ := by
  decide +kernel

theorem context_12_28528_432348 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28528 ⟨432348, by decide⟩ :=
  accepted_of_selected 12 28528 ⟨432348, by decide⟩ ⟨12, 2, 0, 432348, 28528, 3237, 65536⟩
    (by decide) selected_cut_17011

theorem selected_cut_17012 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 114116) = some ⟨13, 1, 0, 3444, 114116, 1, 16384⟩ := by
  decide +kernel

theorem context_13_114116_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 114116 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 114116 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 114116, 1, 16384⟩
    (by decide) selected_cut_17012

theorem selected_cut_17013 : selected 8 ⟨432376, by decide⟩
    (prefixPartial 13 114117) = some ⟨13, 2, 0, 432376, 114117, 1077, 16384⟩ := by
  decide +kernel

theorem context_13_114117_432376 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 114117 ⟨432376, by decide⟩ :=
  accepted_of_selected 13 114117 ⟨432376, by decide⟩ ⟨13, 2, 0, 432376, 114117, 1077, 16384⟩
    (by decide) selected_cut_17013

theorem selected_cut_17014 : selected 8 ⟨432416, by decide⟩
    (prefixPartial 13 114118) = some ⟨13, 2, 0, 432416, 114118, 2581, 16384⟩ := by
  decide +kernel

theorem context_13_114118_432416 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 114118 ⟨432416, by decide⟩ :=
  accepted_of_selected 13 114118 ⟨432416, by decide⟩ ⟨13, 2, 0, 432416, 114118, 2581, 16384⟩
    (by decide) selected_cut_17014

theorem selected_cut_17015 : selected 8 ⟨432425, by decide⟩
    (prefixPartial 13 114119) = some ⟨13, 2, 0, 432425, 114119, 889, 16384⟩ := by
  decide +kernel

theorem context_13_114119_432425 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 114119 ⟨432425, by decide⟩ :=
  accepted_of_selected 13 114119 ⟨432425, by decide⟩ ⟨13, 2, 0, 432425, 114119, 889, 16384⟩
    (by decide) selected_cut_17015

theorem unmarked_context_12_28529_432426 : frontier 9 ⟨432426, by decide⟩
    (prefixCache 12 28529) (prefixPartial 12 28529) = false := by
  decide +kernel

theorem node_context_12_28529_432426 : EJMOriginalGlobalDAGData.nodes 9 ⟨432426, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨432376, by decide⟩,⟨432416, by decide⟩,⟨432425, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28529_432426 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28529 ⟨432426, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28529
    ⟨432426, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨432376, by decide⟩,⟨432416, by decide⟩,⟨432425, by decide⟩]) unmarked_context_12_28529_432426 node_context_12_28529_432426
  intro a
  fin_cases a
  · exact context_13_114116_3444
  · exact context_13_114117_432376
  · exact context_13_114118_432416
  · exact context_13_114119_432425

theorem selected_cut_17016 : selected 9 ⟨432473, by decide⟩
    (prefixPartial 12 28530) = some ⟨12, 2, 0, 432473, 28530, 3385, 65536⟩ := by
  decide +kernel

theorem context_12_28530_432473 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28530 ⟨432473, by decide⟩ :=
  accepted_of_selected 12 28530 ⟨432473, by decide⟩ ⟨12, 2, 0, 432473, 28530, 3385, 65536⟩
    (by decide) selected_cut_17016

theorem selected_cut_17017 : selected 9 ⟨432505, by decide⟩
    (prefixPartial 12 28531) = some ⟨12, 2, 0, 432505, 28531, 3125, 65536⟩ := by
  decide +kernel

theorem context_12_28531_432505 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28531 ⟨432505, by decide⟩ :=
  accepted_of_selected 12 28531 ⟨432505, by decide⟩ ⟨12, 2, 0, 432505, 28531, 3125, 65536⟩
    (by decide) selected_cut_17017

theorem unmarked_context_11_7132_432506 : frontier 10 ⟨432506, by decide⟩
    (prefixCache 11 7132) (prefixPartial 11 7132) = false := by
  decide +kernel

theorem node_context_11_7132_432506 : EJMOriginalGlobalDAGData.nodes 10 ⟨432506, by decide⟩ =
    .split (coordinate 11) (![⟨432348, by decide⟩,⟨432426, by decide⟩,⟨432473, by decide⟩,⟨432505, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_7132_432506 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7132 ⟨432506, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 7132
    ⟨432506, by decide⟩ (by decide) (![⟨432348, by decide⟩,⟨432426, by decide⟩,⟨432473, by decide⟩,⟨432505, by decide⟩]) unmarked_context_11_7132_432506 node_context_11_7132_432506
  intro a
  fin_cases a
  · exact context_12_28528_432348
  · exact context_12_28529_432426
  · exact context_12_28530_432473
  · exact context_12_28531_432505

theorem selected_cut_17018 : selected 9 ⟨432545, by decide⟩
    (prefixPartial 12 28532) = some ⟨12, 2, 0, 432545, 28532, 3217, 65536⟩ := by
  decide +kernel

theorem context_12_28532_432545 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28532 ⟨432545, by decide⟩ :=
  accepted_of_selected 12 28532 ⟨432545, by decide⟩ ⟨12, 2, 0, 432545, 28532, 3217, 65536⟩
    (by decide) selected_cut_17018

theorem selected_cut_17019 : selected 9 ⟨299350, by decide⟩
    (prefixPartial 12 28533) = some ⟨12, 1, 0, 299350, 28533, 1, 65536⟩ := by
  decide +kernel

theorem context_12_28533_299350 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28533 ⟨299350, by decide⟩ :=
  accepted_of_selected 12 28533 ⟨299350, by decide⟩ ⟨12, 1, 0, 299350, 28533, 1, 65536⟩
    (by decide) selected_cut_17019

theorem selected_cut_17020 : selected 9 ⟨432595, by decide⟩
    (prefixPartial 12 28534) = some ⟨12, 2, 0, 432595, 28534, 3497, 65536⟩ := by
  decide +kernel

theorem context_12_28534_432595 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28534 ⟨432595, by decide⟩ :=
  accepted_of_selected 12 28534 ⟨432595, by decide⟩ ⟨12, 2, 0, 432595, 28534, 3497, 65536⟩
    (by decide) selected_cut_17020

theorem selected_cut_17021 : selected 9 ⟨432629, by decide⟩
    (prefixPartial 12 28535) = some ⟨12, 2, 0, 432629, 28535, 3193, 65536⟩ := by
  decide +kernel

theorem context_12_28535_432629 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28535 ⟨432629, by decide⟩ :=
  accepted_of_selected 12 28535 ⟨432629, by decide⟩ ⟨12, 2, 0, 432629, 28535, 3193, 65536⟩
    (by decide) selected_cut_17021

theorem unmarked_context_11_7133_432630 : frontier 10 ⟨432630, by decide⟩
    (prefixCache 11 7133) (prefixPartial 11 7133) = false := by
  decide +kernel

theorem node_context_11_7133_432630 : EJMOriginalGlobalDAGData.nodes 10 ⟨432630, by decide⟩ =
    .split (coordinate 11) (![⟨432545, by decide⟩,⟨299350, by decide⟩,⟨432595, by decide⟩,⟨432629, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_7133_432630 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7133 ⟨432630, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 7133
    ⟨432630, by decide⟩ (by decide) (![⟨432545, by decide⟩,⟨299350, by decide⟩,⟨432595, by decide⟩,⟨432629, by decide⟩]) unmarked_context_11_7133_432630 node_context_11_7133_432630
  intro a
  fin_cases a
  · exact context_12_28532_432545
  · exact context_12_28533_299350
  · exact context_12_28534_432595
  · exact context_12_28535_432629

theorem selected_cut_17022 : selected 9 ⟨432676, by decide⟩
    (prefixPartial 12 28536) = some ⟨12, 2, 0, 432676, 28536, 3249, 65536⟩ := by
  decide +kernel

theorem context_12_28536_432676 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28536 ⟨432676, by decide⟩ :=
  accepted_of_selected 12 28536 ⟨432676, by decide⟩ ⟨12, 2, 0, 432676, 28536, 3249, 65536⟩
    (by decide) selected_cut_17022

theorem selected_cut_17023 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 114148) = some ⟨13, 1, 0, 3444, 114148, 1, 16384⟩ := by
  decide +kernel

theorem context_13_114148_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 114148 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 114148 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 114148, 1, 16384⟩
    (by decide) selected_cut_17023

theorem selected_cut_17024 : selected 8 ⟨432688, by decide⟩
    (prefixPartial 13 114149) = some ⟨13, 2, 0, 432688, 114149, 521, 16384⟩ := by
  decide +kernel

theorem context_13_114149_432688 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 114149 ⟨432688, by decide⟩ :=
  accepted_of_selected 13 114149 ⟨432688, by decide⟩ ⟨13, 2, 0, 432688, 114149, 521, 16384⟩
    (by decide) selected_cut_17024

theorem selected_cut_17025 : selected 8 ⟨432736, by decide⟩
    (prefixPartial 13 114150) = some ⟨13, 2, 0, 432736, 114150, 2733, 16384⟩ := by
  decide +kernel

theorem context_13_114150_432736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 114150 ⟨432736, by decide⟩ :=
  accepted_of_selected 13 114150 ⟨432736, by decide⟩ ⟨13, 2, 0, 432736, 114150, 2733, 16384⟩
    (by decide) selected_cut_17025

theorem selected_cut_17026 : selected 8 ⟨432764, by decide⟩
    (prefixPartial 13 114151) = some ⟨13, 2, 0, 432764, 114151, 1205, 16384⟩ := by
  decide +kernel

theorem context_13_114151_432764 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 114151 ⟨432764, by decide⟩ :=
  accepted_of_selected 13 114151 ⟨432764, by decide⟩ ⟨13, 2, 0, 432764, 114151, 1205, 16384⟩
    (by decide) selected_cut_17026

theorem unmarked_context_12_28537_432765 : frontier 9 ⟨432765, by decide⟩
    (prefixCache 12 28537) (prefixPartial 12 28537) = false := by
  decide +kernel

theorem node_context_12_28537_432765 : EJMOriginalGlobalDAGData.nodes 9 ⟨432765, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨432688, by decide⟩,⟨432736, by decide⟩,⟨432764, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28537_432765 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28537 ⟨432765, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28537
    ⟨432765, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨432688, by decide⟩,⟨432736, by decide⟩,⟨432764, by decide⟩]) unmarked_context_12_28537_432765 node_context_12_28537_432765
  intro a
  fin_cases a
  · exact context_13_114148_3444
  · exact context_13_114149_432688
  · exact context_13_114150_432736
  · exact context_13_114151_432764

theorem selected_cut_17027 : selected 9 ⟨432809, by decide⟩
    (prefixPartial 12 28538) = some ⟨12, 2, 0, 432809, 28538, 3177, 65536⟩ := by
  decide +kernel

theorem context_12_28538_432809 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28538 ⟨432809, by decide⟩ :=
  accepted_of_selected 12 28538 ⟨432809, by decide⟩ ⟨12, 2, 0, 432809, 28538, 3177, 65536⟩
    (by decide) selected_cut_17027

theorem selected_cut_17028 : selected 9 ⟨432847, by decide⟩
    (prefixPartial 12 28539) = some ⟨12, 2, 0, 432847, 28539, 2745, 65536⟩ := by
  decide +kernel

theorem context_12_28539_432847 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28539 ⟨432847, by decide⟩ :=
  accepted_of_selected 12 28539 ⟨432847, by decide⟩ ⟨12, 2, 0, 432847, 28539, 2745, 65536⟩
    (by decide) selected_cut_17028

theorem unmarked_context_11_7134_432848 : frontier 10 ⟨432848, by decide⟩
    (prefixCache 11 7134) (prefixPartial 11 7134) = false := by
  decide +kernel

theorem node_context_11_7134_432848 : EJMOriginalGlobalDAGData.nodes 10 ⟨432848, by decide⟩ =
    .split (coordinate 11) (![⟨432676, by decide⟩,⟨432765, by decide⟩,⟨432809, by decide⟩,⟨432847, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_7134_432848 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7134 ⟨432848, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 7134
    ⟨432848, by decide⟩ (by decide) (![⟨432676, by decide⟩,⟨432765, by decide⟩,⟨432809, by decide⟩,⟨432847, by decide⟩]) unmarked_context_11_7134_432848 node_context_11_7134_432848
  intro a
  fin_cases a
  · exact context_12_28536_432676
  · exact context_12_28537_432765
  · exact context_12_28538_432809
  · exact context_12_28539_432847

theorem selected_cut_17029 : selected 9 ⟨432886, by decide⟩
    (prefixPartial 12 28540) = some ⟨12, 2, 0, 432886, 28540, 3041, 65536⟩ := by
  decide +kernel

theorem context_12_28540_432886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28540 ⟨432886, by decide⟩ :=
  accepted_of_selected 12 28540 ⟨432886, by decide⟩ ⟨12, 2, 0, 432886, 28540, 3041, 65536⟩
    (by decide) selected_cut_17029

theorem selected_cut_17030 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 114164) = some ⟨13, 1, 0, 3444, 114164, 1, 16384⟩ := by
  decide +kernel

theorem context_13_114164_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 114164 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 114164 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 114164, 1, 16384⟩
    (by decide) selected_cut_17030

theorem selected_cut_17031 : selected 8 ⟨432892, by decide⟩
    (prefixPartial 13 114165) = some ⟨13, 2, 0, 432892, 114165, 237, 16384⟩ := by
  decide +kernel

theorem context_13_114165_432892 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 114165 ⟨432892, by decide⟩ :=
  accepted_of_selected 13 114165 ⟨432892, by decide⟩ ⟨13, 2, 0, 432892, 114165, 237, 16384⟩
    (by decide) selected_cut_17031

theorem selected_cut_17032 : selected 8 ⟨432956, by decide⟩
    (prefixPartial 13 114166) = some ⟨13, 2, 0, 432956, 114166, 3037, 16384⟩ := by
  decide +kernel

theorem context_13_114166_432956 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 114166 ⟨432956, by decide⟩ :=
  accepted_of_selected 13 114166 ⟨432956, by decide⟩ ⟨13, 2, 0, 432956, 114166, 3037, 16384⟩
    (by decide) selected_cut_17032

theorem selected_cut_17033 : selected 8 ⟨432981, by decide⟩
    (prefixPartial 13 114167) = some ⟨13, 2, 0, 432981, 114167, 1249, 16384⟩ := by
  decide +kernel

theorem context_13_114167_432981 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 114167 ⟨432981, by decide⟩ :=
  accepted_of_selected 13 114167 ⟨432981, by decide⟩ ⟨13, 2, 0, 432981, 114167, 1249, 16384⟩
    (by decide) selected_cut_17033

theorem unmarked_context_12_28541_432982 : frontier 9 ⟨432982, by decide⟩
    (prefixCache 12 28541) (prefixPartial 12 28541) = false := by
  decide +kernel

theorem node_context_12_28541_432982 : EJMOriginalGlobalDAGData.nodes 9 ⟨432982, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨432892, by decide⟩,⟨432956, by decide⟩,⟨432981, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28541_432982 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28541 ⟨432982, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28541
    ⟨432982, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨432892, by decide⟩,⟨432956, by decide⟩,⟨432981, by decide⟩]) unmarked_context_12_28541_432982 node_context_12_28541_432982
  intro a
  fin_cases a
  · exact context_13_114164_3444
  · exact context_13_114165_432892
  · exact context_13_114166_432956
  · exact context_13_114167_432981

theorem selected_cut_17034 : selected 9 ⟨433015, by decide⟩
    (prefixPartial 12 28542) = some ⟨12, 2, 0, 433015, 28542, 3101, 65536⟩ := by
  decide +kernel

theorem context_12_28542_433015 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28542 ⟨433015, by decide⟩ :=
  accepted_of_selected 12 28542 ⟨433015, by decide⟩ ⟨12, 2, 0, 433015, 28542, 3101, 65536⟩
    (by decide) selected_cut_17034

theorem selected_cut_17035 : selected 9 ⟨429285, by decide⟩
    (prefixPartial 12 28543) = some ⟨12, 1, 0, 429285, 28543, 1, 65536⟩ := by
  decide +kernel

theorem context_12_28543_429285 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28543 ⟨429285, by decide⟩ :=
  accepted_of_selected 12 28543 ⟨429285, by decide⟩ ⟨12, 1, 0, 429285, 28543, 1, 65536⟩
    (by decide) selected_cut_17035

theorem unmarked_context_11_7135_433016 : frontier 10 ⟨433016, by decide⟩
    (prefixCache 11 7135) (prefixPartial 11 7135) = false := by
  decide +kernel

theorem node_context_11_7135_433016 : EJMOriginalGlobalDAGData.nodes 10 ⟨433016, by decide⟩ =
    .split (coordinate 11) (![⟨432886, by decide⟩,⟨432982, by decide⟩,⟨433015, by decide⟩,⟨429285, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_7135_433016 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7135 ⟨433016, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 7135
    ⟨433016, by decide⟩ (by decide) (![⟨432886, by decide⟩,⟨432982, by decide⟩,⟨433015, by decide⟩,⟨429285, by decide⟩]) unmarked_context_11_7135_433016 node_context_11_7135_433016
  intro a
  fin_cases a
  · exact context_12_28540_432886
  · exact context_12_28541_432982
  · exact context_12_28542_433015
  · exact context_12_28543_429285

theorem unmarked_context_10_1783_433017 : frontier 11 ⟨433017, by decide⟩
    (prefixCache 10 1783) (prefixPartial 10 1783) = false := by
  decide +kernel

theorem node_context_10_1783_433017 : EJMOriginalGlobalDAGData.nodes 11 ⟨433017, by decide⟩ =
    .split (coordinate 10) (![⟨432506, by decide⟩,⟨432630, by decide⟩,⟨432848, by decide⟩,⟨433016, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1783_433017 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1783 ⟨433017, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1783
    ⟨433017, by decide⟩ (by decide) (![⟨432506, by decide⟩,⟨432630, by decide⟩,⟨432848, by decide⟩,⟨433016, by decide⟩]) unmarked_context_10_1783_433017 node_context_10_1783_433017
  intro a
  fin_cases a
  · exact context_11_7132_432506
  · exact context_11_7133_432630
  · exact context_11_7134_432848
  · exact context_11_7135_433016

theorem unmarked_context_9_445_433018 : frontier 12 ⟨433018, by decide⟩
    (prefixCache 9 445) (prefixPartial 9 445) = false := by
  decide +kernel

theorem node_context_9_445_433018 : EJMOriginalGlobalDAGData.nodes 12 ⟨433018, by decide⟩ =
    .split (coordinate 9) (![⟨430730, by decide⟩,⟨431477, by decide⟩,⟨432308, by decide⟩,⟨433017, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_445_433018 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 445 ⟨433018, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 445
    ⟨433018, by decide⟩ (by decide) (![⟨430730, by decide⟩,⟨431477, by decide⟩,⟨432308, by decide⟩,⟨433017, by decide⟩]) unmarked_context_9_445_433018 node_context_9_445_433018
  intro a
  fin_cases a
  · exact context_10_1780_430730
  · exact context_10_1781_431477
  · exact context_10_1782_432308
  · exact context_10_1783_433017

theorem selected_cut_17036 : selected 9 ⟨433052, by decide⟩
    (prefixPartial 12 28544) = some ⟨12, 2, 0, 433052, 28544, 3077, 65536⟩ := by
  decide +kernel

theorem context_12_28544_433052 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28544 ⟨433052, by decide⟩ :=
  accepted_of_selected 12 28544 ⟨433052, by decide⟩ ⟨12, 2, 0, 433052, 28544, 3077, 65536⟩
    (by decide) selected_cut_17036

theorem selected_cut_17037 : selected 9 ⟨433089, by decide⟩
    (prefixPartial 12 28545) = some ⟨12, 2, 0, 433089, 28545, 2957, 65536⟩ := by
  decide +kernel

theorem context_12_28545_433089 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28545 ⟨433089, by decide⟩ :=
  accepted_of_selected 12 28545 ⟨433089, by decide⟩ ⟨12, 2, 0, 433089, 28545, 2957, 65536⟩
    (by decide) selected_cut_17037

theorem selected_cut_17038 : selected 9 ⟨433119, by decide⟩
    (prefixPartial 12 28546) = some ⟨12, 2, 0, 433119, 28546, 2953, 65536⟩ := by
  decide +kernel

theorem context_12_28546_433119 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28546 ⟨433119, by decide⟩ :=
  accepted_of_selected 12 28546 ⟨433119, by decide⟩ ⟨12, 2, 0, 433119, 28546, 2953, 65536⟩
    (by decide) selected_cut_17038

theorem selected_cut_17039 : selected 9 ⟨433151, by decide⟩
    (prefixPartial 12 28547) = some ⟨12, 2, 0, 433151, 28547, 3041, 65536⟩ := by
  decide +kernel

theorem context_12_28547_433151 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28547 ⟨433151, by decide⟩ :=
  accepted_of_selected 12 28547 ⟨433151, by decide⟩ ⟨12, 2, 0, 433151, 28547, 3041, 65536⟩
    (by decide) selected_cut_17039

theorem unmarked_context_11_7136_433152 : frontier 10 ⟨433152, by decide⟩
    (prefixCache 11 7136) (prefixPartial 11 7136) = false := by
  decide +kernel

theorem node_context_11_7136_433152 : EJMOriginalGlobalDAGData.nodes 10 ⟨433152, by decide⟩ =
    .split (coordinate 11) (![⟨433052, by decide⟩,⟨433089, by decide⟩,⟨433119, by decide⟩,⟨433151, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_7136_433152 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7136 ⟨433152, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 7136
    ⟨433152, by decide⟩ (by decide) (![⟨433052, by decide⟩,⟨433089, by decide⟩,⟨433119, by decide⟩,⟨433151, by decide⟩]) unmarked_context_11_7136_433152 node_context_11_7136_433152
  intro a
  fin_cases a
  · exact context_12_28544_433052
  · exact context_12_28545_433089
  · exact context_12_28546_433119
  · exact context_12_28547_433151

theorem selected_cut_17040 : selected 9 ⟨433190, by decide⟩
    (prefixPartial 12 28548) = some ⟨12, 2, 0, 433190, 28548, 3053, 65536⟩ := by
  decide +kernel

theorem context_12_28548_433190 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28548 ⟨433190, by decide⟩ :=
  accepted_of_selected 12 28548 ⟨433190, by decide⟩ ⟨12, 2, 0, 433190, 28548, 3053, 65536⟩
    (by decide) selected_cut_17040

theorem selected_cut_17041 : selected 9 ⟨433214, by decide⟩
    (prefixPartial 12 28549) = some ⟨12, 2, 0, 433214, 28549, 2773, 65536⟩ := by
  decide +kernel

theorem context_12_28549_433214 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28549 ⟨433214, by decide⟩ :=
  accepted_of_selected 12 28549 ⟨433214, by decide⟩ ⟨12, 2, 0, 433214, 28549, 2773, 65536⟩
    (by decide) selected_cut_17041

theorem selected_cut_17042 : selected 9 ⟨433238, by decide⟩
    (prefixPartial 12 28550) = some ⟨12, 2, 0, 433238, 28550, 2989, 65536⟩ := by
  decide +kernel

theorem context_12_28550_433238 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28550 ⟨433238, by decide⟩ :=
  accepted_of_selected 12 28550 ⟨433238, by decide⟩ ⟨12, 2, 0, 433238, 28550, 2989, 65536⟩
    (by decide) selected_cut_17042

theorem selected_cut_17043 : selected 9 ⟨433278, by decide⟩
    (prefixPartial 12 28551) = some ⟨12, 2, 0, 433278, 28551, 3117, 65536⟩ := by
  decide +kernel

theorem context_12_28551_433278 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28551 ⟨433278, by decide⟩ :=
  accepted_of_selected 12 28551 ⟨433278, by decide⟩ ⟨12, 2, 0, 433278, 28551, 3117, 65536⟩
    (by decide) selected_cut_17043

theorem unmarked_context_11_7137_433279 : frontier 10 ⟨433279, by decide⟩
    (prefixCache 11 7137) (prefixPartial 11 7137) = false := by
  decide +kernel

theorem node_context_11_7137_433279 : EJMOriginalGlobalDAGData.nodes 10 ⟨433279, by decide⟩ =
    .split (coordinate 11) (![⟨433190, by decide⟩,⟨433214, by decide⟩,⟨433238, by decide⟩,⟨433278, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_7137_433279 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7137 ⟨433279, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 7137
    ⟨433279, by decide⟩ (by decide) (![⟨433190, by decide⟩,⟨433214, by decide⟩,⟨433238, by decide⟩,⟨433278, by decide⟩]) unmarked_context_11_7137_433279 node_context_11_7137_433279
  intro a
  fin_cases a
  · exact context_12_28548_433190
  · exact context_12_28549_433214
  · exact context_12_28550_433238
  · exact context_12_28551_433278

theorem selected_cut_17044 : selected 9 ⟨433326, by decide⟩
    (prefixPartial 12 28552) = some ⟨12, 2, 0, 433326, 28552, 3265, 65536⟩ := by
  decide +kernel

theorem context_12_28552_433326 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28552 ⟨433326, by decide⟩ :=
  accepted_of_selected 12 28552 ⟨433326, by decide⟩ ⟨12, 2, 0, 433326, 28552, 3265, 65536⟩
    (by decide) selected_cut_17044

theorem selected_cut_17045 : selected 9 ⟨433354, by decide⟩
    (prefixPartial 12 28553) = some ⟨12, 2, 0, 433354, 28553, 2961, 65536⟩ := by
  decide +kernel

theorem context_12_28553_433354 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28553 ⟨433354, by decide⟩ :=
  accepted_of_selected 12 28553 ⟨433354, by decide⟩ ⟨12, 2, 0, 433354, 28553, 2961, 65536⟩
    (by decide) selected_cut_17045

theorem selected_cut_17046 : selected 9 ⟨433384, by decide⟩
    (prefixPartial 12 28554) = some ⟨12, 2, 0, 433384, 28554, 2937, 65536⟩ := by
  decide +kernel

theorem context_12_28554_433384 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28554 ⟨433384, by decide⟩ :=
  accepted_of_selected 12 28554 ⟨433384, by decide⟩ ⟨12, 2, 0, 433384, 28554, 2937, 65536⟩
    (by decide) selected_cut_17046

theorem selected_cut_17047 : selected 9 ⟨433415, by decide⟩
    (prefixPartial 12 28555) = some ⟨12, 2, 0, 433415, 28555, 2805, 65536⟩ := by
  decide +kernel

theorem context_12_28555_433415 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28555 ⟨433415, by decide⟩ :=
  accepted_of_selected 12 28555 ⟨433415, by decide⟩ ⟨12, 2, 0, 433415, 28555, 2805, 65536⟩
    (by decide) selected_cut_17047

theorem unmarked_context_11_7138_433416 : frontier 10 ⟨433416, by decide⟩
    (prefixCache 11 7138) (prefixPartial 11 7138) = false := by
  decide +kernel

theorem node_context_11_7138_433416 : EJMOriginalGlobalDAGData.nodes 10 ⟨433416, by decide⟩ =
    .split (coordinate 11) (![⟨433326, by decide⟩,⟨433354, by decide⟩,⟨433384, by decide⟩,⟨433415, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_7138_433416 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7138 ⟨433416, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 7138
    ⟨433416, by decide⟩ (by decide) (![⟨433326, by decide⟩,⟨433354, by decide⟩,⟨433384, by decide⟩,⟨433415, by decide⟩]) unmarked_context_11_7138_433416 node_context_11_7138_433416
  intro a
  fin_cases a
  · exact context_12_28552_433326
  · exact context_12_28553_433354
  · exact context_12_28554_433384
  · exact context_12_28555_433415

theorem selected_cut_17048 : selected 9 ⟨433441, by decide⟩
    (prefixPartial 12 28556) = some ⟨12, 2, 0, 433441, 28556, 2433, 65536⟩ := by
  decide +kernel

theorem context_12_28556_433441 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28556 ⟨433441, by decide⟩ :=
  accepted_of_selected 12 28556 ⟨433441, by decide⟩ ⟨12, 2, 0, 433441, 28556, 2433, 65536⟩
    (by decide) selected_cut_17048

theorem selected_cut_17049 : selected 9 ⟨433463, by decide⟩
    (prefixPartial 12 28557) = some ⟨12, 2, 0, 433463, 28557, 2321, 65536⟩ := by
  decide +kernel

theorem context_12_28557_433463 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28557 ⟨433463, by decide⟩ :=
  accepted_of_selected 12 28557 ⟨433463, by decide⟩ ⟨12, 2, 0, 433463, 28557, 2321, 65536⟩
    (by decide) selected_cut_17049

theorem selected_cut_17050 : selected 9 ⟨433487, by decide⟩
    (prefixPartial 12 28558) = some ⟨12, 2, 0, 433487, 28558, 2333, 65536⟩ := by
  decide +kernel

theorem context_12_28558_433487 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28558 ⟨433487, by decide⟩ :=
  accepted_of_selected 12 28558 ⟨433487, by decide⟩ ⟨12, 2, 0, 433487, 28558, 2333, 65536⟩
    (by decide) selected_cut_17050

theorem selected_cut_17051 : selected 9 ⟨433558, by decide⟩
    (prefixPartial 12 28559) = some ⟨12, 2, 0, 433558, 28559, 3581, 65536⟩ := by
  decide +kernel

theorem context_12_28559_433558 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28559 ⟨433558, by decide⟩ :=
  accepted_of_selected 12 28559 ⟨433558, by decide⟩ ⟨12, 2, 0, 433558, 28559, 3581, 65536⟩
    (by decide) selected_cut_17051

theorem unmarked_context_11_7139_433559 : frontier 10 ⟨433559, by decide⟩
    (prefixCache 11 7139) (prefixPartial 11 7139) = false := by
  decide +kernel

theorem node_context_11_7139_433559 : EJMOriginalGlobalDAGData.nodes 10 ⟨433559, by decide⟩ =
    .split (coordinate 11) (![⟨433441, by decide⟩,⟨433463, by decide⟩,⟨433487, by decide⟩,⟨433558, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_7139_433559 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7139 ⟨433559, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 7139
    ⟨433559, by decide⟩ (by decide) (![⟨433441, by decide⟩,⟨433463, by decide⟩,⟨433487, by decide⟩,⟨433558, by decide⟩]) unmarked_context_11_7139_433559 node_context_11_7139_433559
  intro a
  fin_cases a
  · exact context_12_28556_433441
  · exact context_12_28557_433463
  · exact context_12_28558_433487
  · exact context_12_28559_433558

theorem unmarked_context_10_1784_433560 : frontier 11 ⟨433560, by decide⟩
    (prefixCache 10 1784) (prefixPartial 10 1784) = false := by
  decide +kernel

theorem node_context_10_1784_433560 : EJMOriginalGlobalDAGData.nodes 11 ⟨433560, by decide⟩ =
    .split (coordinate 10) (![⟨433152, by decide⟩,⟨433279, by decide⟩,⟨433416, by decide⟩,⟨433559, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1784_433560 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1784 ⟨433560, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1784
    ⟨433560, by decide⟩ (by decide) (![⟨433152, by decide⟩,⟨433279, by decide⟩,⟨433416, by decide⟩,⟨433559, by decide⟩]) unmarked_context_10_1784_433560 node_context_10_1784_433560
  intro a
  fin_cases a
  · exact context_11_7136_433152
  · exact context_11_7137_433279
  · exact context_11_7138_433416
  · exact context_11_7139_433559

theorem selected_cut_17052 : selected 9 ⟨433581, by decide⟩
    (prefixPartial 12 28560) = some ⟨12, 2, 0, 433581, 28560, 2245, 65536⟩ := by
  decide +kernel

theorem context_12_28560_433581 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28560 ⟨433581, by decide⟩ :=
  accepted_of_selected 12 28560 ⟨433581, by decide⟩ ⟨12, 2, 0, 433581, 28560, 2245, 65536⟩
    (by decide) selected_cut_17052

theorem selected_cut_17053 : selected 9 ⟨433618, by decide⟩
    (prefixPartial 12 28561) = some ⟨12, 2, 0, 433618, 28561, 2337, 65536⟩ := by
  decide +kernel

theorem context_12_28561_433618 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28561 ⟨433618, by decide⟩ :=
  accepted_of_selected 12 28561 ⟨433618, by decide⟩ ⟨12, 2, 0, 433618, 28561, 2337, 65536⟩
    (by decide) selected_cut_17053

theorem selected_cut_17054 : selected 9 ⟨433658, by decide⟩
    (prefixPartial 12 28562) = some ⟨12, 2, 0, 433658, 28562, 2381, 65536⟩ := by
  decide +kernel

theorem context_12_28562_433658 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28562 ⟨433658, by decide⟩ :=
  accepted_of_selected 12 28562 ⟨433658, by decide⟩ ⟨12, 2, 0, 433658, 28562, 2381, 65536⟩
    (by decide) selected_cut_17054

theorem selected_cut_17055 : selected 9 ⟨433682, by decide⟩
    (prefixPartial 12 28563) = some ⟨12, 2, 0, 433682, 28563, 2373, 65536⟩ := by
  decide +kernel

theorem context_12_28563_433682 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28563 ⟨433682, by decide⟩ :=
  accepted_of_selected 12 28563 ⟨433682, by decide⟩ ⟨12, 2, 0, 433682, 28563, 2373, 65536⟩
    (by decide) selected_cut_17055

theorem unmarked_context_11_7140_433683 : frontier 10 ⟨433683, by decide⟩
    (prefixCache 11 7140) (prefixPartial 11 7140) = false := by
  decide +kernel

theorem node_context_11_7140_433683 : EJMOriginalGlobalDAGData.nodes 10 ⟨433683, by decide⟩ =
    .split (coordinate 11) (![⟨433581, by decide⟩,⟨433618, by decide⟩,⟨433658, by decide⟩,⟨433682, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_7140_433683 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7140 ⟨433683, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 7140
    ⟨433683, by decide⟩ (by decide) (![⟨433581, by decide⟩,⟨433618, by decide⟩,⟨433658, by decide⟩,⟨433682, by decide⟩]) unmarked_context_11_7140_433683 node_context_11_7140_433683
  intro a
  fin_cases a
  · exact context_12_28560_433581
  · exact context_12_28561_433618
  · exact context_12_28562_433658
  · exact context_12_28563_433682

theorem selected_cut_17056 : selected 9 ⟨433704, by decide⟩
    (prefixPartial 12 28564) = some ⟨12, 2, 0, 433704, 28564, 2029, 65536⟩ := by
  decide +kernel

theorem context_12_28564_433704 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28564 ⟨433704, by decide⟩ :=
  accepted_of_selected 12 28564 ⟨433704, by decide⟩ ⟨12, 2, 0, 433704, 28564, 2029, 65536⟩
    (by decide) selected_cut_17056

theorem selected_cut_17057 : selected 9 ⟨433726, by decide⟩
    (prefixPartial 12 28565) = some ⟨12, 2, 0, 433726, 28565, 2033, 65536⟩ := by
  decide +kernel

theorem context_12_28565_433726 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28565 ⟨433726, by decide⟩ :=
  accepted_of_selected 12 28565 ⟨433726, by decide⟩ ⟨12, 2, 0, 433726, 28565, 2033, 65536⟩
    (by decide) selected_cut_17057

theorem selected_cut_17058 : selected 9 ⟨433755, by decide⟩
    (prefixPartial 12 28566) = some ⟨12, 2, 0, 433755, 28566, 2269, 65536⟩ := by
  decide +kernel

theorem context_12_28566_433755 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28566 ⟨433755, by decide⟩ :=
  accepted_of_selected 12 28566 ⟨433755, by decide⟩ ⟨12, 2, 0, 433755, 28566, 2269, 65536⟩
    (by decide) selected_cut_17058

theorem selected_cut_17059 : selected 9 ⟨433776, by decide⟩
    (prefixPartial 12 28567) = some ⟨12, 2, 0, 433776, 28567, 2317, 65536⟩ := by
  decide +kernel

theorem context_12_28567_433776 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28567 ⟨433776, by decide⟩ :=
  accepted_of_selected 12 28567 ⟨433776, by decide⟩ ⟨12, 2, 0, 433776, 28567, 2317, 65536⟩
    (by decide) selected_cut_17059

theorem unmarked_context_11_7141_433777 : frontier 10 ⟨433777, by decide⟩
    (prefixCache 11 7141) (prefixPartial 11 7141) = false := by
  decide +kernel

theorem node_context_11_7141_433777 : EJMOriginalGlobalDAGData.nodes 10 ⟨433777, by decide⟩ =
    .split (coordinate 11) (![⟨433704, by decide⟩,⟨433726, by decide⟩,⟨433755, by decide⟩,⟨433776, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_7141_433777 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7141 ⟨433777, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 7141
    ⟨433777, by decide⟩ (by decide) (![⟨433704, by decide⟩,⟨433726, by decide⟩,⟨433755, by decide⟩,⟨433776, by decide⟩]) unmarked_context_11_7141_433777 node_context_11_7141_433777
  intro a
  fin_cases a
  · exact context_12_28564_433704
  · exact context_12_28565_433726
  · exact context_12_28566_433755
  · exact context_12_28567_433776

theorem selected_cut_17060 : selected 9 ⟨433799, by decide⟩
    (prefixPartial 12 28568) = some ⟨12, 2, 0, 433799, 28568, 1869, 65536⟩ := by
  decide +kernel

theorem context_12_28568_433799 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28568 ⟨433799, by decide⟩ :=
  accepted_of_selected 12 28568 ⟨433799, by decide⟩ ⟨12, 2, 0, 433799, 28568, 1869, 65536⟩
    (by decide) selected_cut_17060

theorem selected_cut_17061 : selected 9 ⟨433825, by decide⟩
    (prefixPartial 12 28569) = some ⟨12, 2, 0, 433825, 28569, 1977, 65536⟩ := by
  decide +kernel

theorem context_12_28569_433825 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28569 ⟨433825, by decide⟩ :=
  accepted_of_selected 12 28569 ⟨433825, by decide⟩ ⟨12, 2, 0, 433825, 28569, 1977, 65536⟩
    (by decide) selected_cut_17061

theorem selected_cut_17062 : selected 9 ⟨433846, by decide⟩
    (prefixPartial 12 28570) = some ⟨12, 2, 0, 433846, 28570, 1961, 65536⟩ := by
  decide +kernel

theorem context_12_28570_433846 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28570 ⟨433846, by decide⟩ :=
  accepted_of_selected 12 28570 ⟨433846, by decide⟩ ⟨12, 2, 0, 433846, 28570, 1961, 65536⟩
    (by decide) selected_cut_17062

theorem selected_cut_17063 : selected 9 ⟨433866, by decide⟩
    (prefixPartial 12 28571) = some ⟨12, 2, 0, 433866, 28571, 1845, 65536⟩ := by
  decide +kernel

theorem context_12_28571_433866 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28571 ⟨433866, by decide⟩ :=
  accepted_of_selected 12 28571 ⟨433866, by decide⟩ ⟨12, 2, 0, 433866, 28571, 1845, 65536⟩
    (by decide) selected_cut_17063

theorem unmarked_context_11_7142_433867 : frontier 10 ⟨433867, by decide⟩
    (prefixCache 11 7142) (prefixPartial 11 7142) = false := by
  decide +kernel

theorem node_context_11_7142_433867 : EJMOriginalGlobalDAGData.nodes 10 ⟨433867, by decide⟩ =
    .split (coordinate 11) (![⟨433799, by decide⟩,⟨433825, by decide⟩,⟨433846, by decide⟩,⟨433866, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_7142_433867 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7142 ⟨433867, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 7142
    ⟨433867, by decide⟩ (by decide) (![⟨433799, by decide⟩,⟨433825, by decide⟩,⟨433846, by decide⟩,⟨433866, by decide⟩]) unmarked_context_11_7142_433867 node_context_11_7142_433867
  intro a
  fin_cases a
  · exact context_12_28568_433799
  · exact context_12_28569_433825
  · exact context_12_28570_433846
  · exact context_12_28571_433866

theorem selected_cut_17064 : selected 9 ⟨433885, by decide⟩
    (prefixPartial 12 28572) = some ⟨12, 2, 0, 433885, 28572, 1445, 65536⟩ := by
  decide +kernel

theorem context_12_28572_433885 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28572 ⟨433885, by decide⟩ :=
  accepted_of_selected 12 28572 ⟨433885, by decide⟩ ⟨12, 2, 0, 433885, 28572, 1445, 65536⟩
    (by decide) selected_cut_17064

theorem selected_cut_17065 : selected 9 ⟨433905, by decide⟩
    (prefixPartial 12 28573) = some ⟨12, 2, 0, 433905, 28573, 1637, 65536⟩ := by
  decide +kernel

theorem context_12_28573_433905 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28573 ⟨433905, by decide⟩ :=
  accepted_of_selected 12 28573 ⟨433905, by decide⟩ ⟨12, 2, 0, 433905, 28573, 1637, 65536⟩
    (by decide) selected_cut_17065

theorem selected_cut_17066 : selected 9 ⟨433924, by decide⟩
    (prefixPartial 12 28574) = some ⟨12, 2, 0, 433924, 28574, 1665, 65536⟩ := by
  decide +kernel

theorem context_12_28574_433924 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28574 ⟨433924, by decide⟩ :=
  accepted_of_selected 12 28574 ⟨433924, by decide⟩ ⟨12, 2, 0, 433924, 28574, 1665, 65536⟩
    (by decide) selected_cut_17066

theorem selected_cut_17067 : selected 9 ⟨433962, by decide⟩
    (prefixPartial 12 28575) = some ⟨12, 2, 0, 433962, 28575, 2485, 65536⟩ := by
  decide +kernel

theorem context_12_28575_433962 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28575 ⟨433962, by decide⟩ :=
  accepted_of_selected 12 28575 ⟨433962, by decide⟩ ⟨12, 2, 0, 433962, 28575, 2485, 65536⟩
    (by decide) selected_cut_17067

theorem unmarked_context_11_7143_433963 : frontier 10 ⟨433963, by decide⟩
    (prefixCache 11 7143) (prefixPartial 11 7143) = false := by
  decide +kernel

theorem node_context_11_7143_433963 : EJMOriginalGlobalDAGData.nodes 10 ⟨433963, by decide⟩ =
    .split (coordinate 11) (![⟨433885, by decide⟩,⟨433905, by decide⟩,⟨433924, by decide⟩,⟨433962, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_7143_433963 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7143 ⟨433963, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 7143
    ⟨433963, by decide⟩ (by decide) (![⟨433885, by decide⟩,⟨433905, by decide⟩,⟨433924, by decide⟩,⟨433962, by decide⟩]) unmarked_context_11_7143_433963 node_context_11_7143_433963
  intro a
  fin_cases a
  · exact context_12_28572_433885
  · exact context_12_28573_433905
  · exact context_12_28574_433924
  · exact context_12_28575_433962

theorem unmarked_context_10_1785_433964 : frontier 11 ⟨433964, by decide⟩
    (prefixCache 10 1785) (prefixPartial 10 1785) = false := by
  decide +kernel

theorem node_context_10_1785_433964 : EJMOriginalGlobalDAGData.nodes 11 ⟨433964, by decide⟩ =
    .split (coordinate 10) (![⟨433683, by decide⟩,⟨433777, by decide⟩,⟨433867, by decide⟩,⟨433963, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1785_433964 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1785 ⟨433964, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1785
    ⟨433964, by decide⟩ (by decide) (![⟨433683, by decide⟩,⟨433777, by decide⟩,⟨433867, by decide⟩,⟨433963, by decide⟩]) unmarked_context_10_1785_433964 node_context_10_1785_433964
  intro a
  fin_cases a
  · exact context_11_7140_433683
  · exact context_11_7141_433777
  · exact context_11_7142_433867
  · exact context_11_7143_433963

theorem selected_cut_17068 : selected 9 ⟨433980, by decide⟩
    (prefixPartial 12 28576) = some ⟨12, 2, 0, 433980, 28576, 1425, 65536⟩ := by
  decide +kernel

theorem context_12_28576_433980 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28576 ⟨433980, by decide⟩ :=
  accepted_of_selected 12 28576 ⟨433980, by decide⟩ ⟨12, 2, 0, 433980, 28576, 1425, 65536⟩
    (by decide) selected_cut_17068

theorem selected_cut_17069 : selected 9 ⟨433995, by decide⟩
    (prefixPartial 12 28577) = some ⟨12, 2, 0, 433995, 28577, 1545, 65536⟩ := by
  decide +kernel

theorem context_12_28577_433995 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28577 ⟨433995, by decide⟩ :=
  accepted_of_selected 12 28577 ⟨433995, by decide⟩ ⟨12, 2, 0, 433995, 28577, 1545, 65536⟩
    (by decide) selected_cut_17069

theorem selected_cut_17070 : selected 9 ⟨434017, by decide⟩
    (prefixPartial 12 28578) = some ⟨12, 2, 0, 434017, 28578, 1573, 65536⟩ := by
  decide +kernel

theorem context_12_28578_434017 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28578 ⟨434017, by decide⟩ :=
  accepted_of_selected 12 28578 ⟨434017, by decide⟩ ⟨12, 2, 0, 434017, 28578, 1573, 65536⟩
    (by decide) selected_cut_17070

theorem selected_cut_17071 : selected 9 ⟨434032, by decide⟩
    (prefixPartial 12 28579) = some ⟨12, 2, 0, 434032, 28579, 1637, 65536⟩ := by
  decide +kernel

theorem context_12_28579_434032 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28579 ⟨434032, by decide⟩ :=
  accepted_of_selected 12 28579 ⟨434032, by decide⟩ ⟨12, 2, 0, 434032, 28579, 1637, 65536⟩
    (by decide) selected_cut_17071

theorem unmarked_context_11_7144_434033 : frontier 10 ⟨434033, by decide⟩
    (prefixCache 11 7144) (prefixPartial 11 7144) = false := by
  decide +kernel

theorem node_context_11_7144_434033 : EJMOriginalGlobalDAGData.nodes 10 ⟨434033, by decide⟩ =
    .split (coordinate 11) (![⟨433980, by decide⟩,⟨433995, by decide⟩,⟨434017, by decide⟩,⟨434032, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_7144_434033 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7144 ⟨434033, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 7144
    ⟨434033, by decide⟩ (by decide) (![⟨433980, by decide⟩,⟨433995, by decide⟩,⟨434017, by decide⟩,⟨434032, by decide⟩]) unmarked_context_11_7144_434033 node_context_11_7144_434033
  intro a
  fin_cases a
  · exact context_12_28576_433980
  · exact context_12_28577_433995
  · exact context_12_28578_434017
  · exact context_12_28579_434032

theorem selected_cut_17072 : selected 9 ⟨434046, by decide⟩
    (prefixPartial 12 28580) = some ⟨12, 2, 0, 434046, 28580, 1297, 65536⟩ := by
  decide +kernel

theorem context_12_28580_434046 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28580 ⟨434046, by decide⟩ :=
  accepted_of_selected 12 28580 ⟨434046, by decide⟩ ⟨12, 2, 0, 434046, 28580, 1297, 65536⟩
    (by decide) selected_cut_17072

theorem selected_cut_17073 : selected 9 ⟨434063, by decide⟩
    (prefixPartial 12 28581) = some ⟨12, 2, 0, 434063, 28581, 1401, 65536⟩ := by
  decide +kernel

theorem context_12_28581_434063 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28581 ⟨434063, by decide⟩ :=
  accepted_of_selected 12 28581 ⟨434063, by decide⟩ ⟨12, 2, 0, 434063, 28581, 1401, 65536⟩
    (by decide) selected_cut_17073

theorem selected_cut_17074 : selected 9 ⟨434079, by decide⟩
    (prefixPartial 12 28582) = some ⟨12, 2, 0, 434079, 28582, 1545, 65536⟩ := by
  decide +kernel

theorem context_12_28582_434079 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28582 ⟨434079, by decide⟩ :=
  accepted_of_selected 12 28582 ⟨434079, by decide⟩ ⟨12, 2, 0, 434079, 28582, 1545, 65536⟩
    (by decide) selected_cut_17074

theorem selected_cut_17075 : selected 9 ⟨434100, by decide⟩
    (prefixPartial 12 28583) = some ⟨12, 2, 0, 434100, 28583, 1565, 65536⟩ := by
  decide +kernel

theorem context_12_28583_434100 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28583 ⟨434100, by decide⟩ :=
  accepted_of_selected 12 28583 ⟨434100, by decide⟩ ⟨12, 2, 0, 434100, 28583, 1565, 65536⟩
    (by decide) selected_cut_17075

theorem unmarked_context_11_7145_434101 : frontier 10 ⟨434101, by decide⟩
    (prefixCache 11 7145) (prefixPartial 11 7145) = false := by
  decide +kernel

theorem node_context_11_7145_434101 : EJMOriginalGlobalDAGData.nodes 10 ⟨434101, by decide⟩ =
    .split (coordinate 11) (![⟨434046, by decide⟩,⟨434063, by decide⟩,⟨434079, by decide⟩,⟨434100, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_7145_434101 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7145 ⟨434101, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 7145
    ⟨434101, by decide⟩ (by decide) (![⟨434046, by decide⟩,⟨434063, by decide⟩,⟨434079, by decide⟩,⟨434100, by decide⟩]) unmarked_context_11_7145_434101 node_context_11_7145_434101
  intro a
  fin_cases a
  · exact context_12_28580_434046
  · exact context_12_28581_434063
  · exact context_12_28582_434079
  · exact context_12_28583_434100

theorem selected_cut_17076 : selected 9 ⟨434116, by decide⟩
    (prefixPartial 12 28584) = some ⟨12, 2, 0, 434116, 28584, 1317, 65536⟩ := by
  decide +kernel

theorem context_12_28584_434116 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28584 ⟨434116, by decide⟩ :=
  accepted_of_selected 12 28584 ⟨434116, by decide⟩ ⟨12, 2, 0, 434116, 28584, 1317, 65536⟩
    (by decide) selected_cut_17076

theorem selected_cut_17077 : selected 9 ⟨434136, by decide⟩
    (prefixPartial 12 28585) = some ⟨12, 2, 0, 434136, 28585, 1417, 65536⟩ := by
  decide +kernel

theorem context_12_28585_434136 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28585 ⟨434136, by decide⟩ :=
  accepted_of_selected 12 28585 ⟨434136, by decide⟩ ⟨12, 2, 0, 434136, 28585, 1417, 65536⟩
    (by decide) selected_cut_17077

theorem selected_cut_17078 : selected 9 ⟨434153, by decide⟩
    (prefixPartial 12 28586) = some ⟨12, 2, 0, 434153, 28586, 1353, 65536⟩ := by
  decide +kernel

theorem context_12_28586_434153 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28586 ⟨434153, by decide⟩ :=
  accepted_of_selected 12 28586 ⟨434153, by decide⟩ ⟨12, 2, 0, 434153, 28586, 1353, 65536⟩
    (by decide) selected_cut_17078

theorem selected_cut_17079 : selected 9 ⟨434165, by decide⟩
    (prefixPartial 12 28587) = some ⟨12, 2, 0, 434165, 28587, 1317, 65536⟩ := by
  decide +kernel

theorem context_12_28587_434165 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28587 ⟨434165, by decide⟩ :=
  accepted_of_selected 12 28587 ⟨434165, by decide⟩ ⟨12, 2, 0, 434165, 28587, 1317, 65536⟩
    (by decide) selected_cut_17079

theorem unmarked_context_11_7146_434166 : frontier 10 ⟨434166, by decide⟩
    (prefixCache 11 7146) (prefixPartial 11 7146) = false := by
  decide +kernel

theorem node_context_11_7146_434166 : EJMOriginalGlobalDAGData.nodes 10 ⟨434166, by decide⟩ =
    .split (coordinate 11) (![⟨434116, by decide⟩,⟨434136, by decide⟩,⟨434153, by decide⟩,⟨434165, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_7146_434166 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7146 ⟨434166, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 7146
    ⟨434166, by decide⟩ (by decide) (![⟨434116, by decide⟩,⟨434136, by decide⟩,⟨434153, by decide⟩,⟨434165, by decide⟩]) unmarked_context_11_7146_434166 node_context_11_7146_434166
  intro a
  fin_cases a
  · exact context_12_28584_434116
  · exact context_12_28585_434136
  · exact context_12_28586_434153
  · exact context_12_28587_434165

theorem selected_cut_17080 : selected 9 ⟨434178, by decide⟩
    (prefixPartial 12 28588) = some ⟨12, 2, 0, 434178, 28588, 1073, 65536⟩ := by
  decide +kernel

theorem context_12_28588_434178 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28588 ⟨434178, by decide⟩ :=
  accepted_of_selected 12 28588 ⟨434178, by decide⟩ ⟨12, 2, 0, 434178, 28588, 1073, 65536⟩
    (by decide) selected_cut_17080

theorem selected_cut_17081 : selected 9 ⟨434191, by decide⟩
    (prefixPartial 12 28589) = some ⟨12, 2, 0, 434191, 28589, 1205, 65536⟩ := by
  decide +kernel

theorem context_12_28589_434191 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28589 ⟨434191, by decide⟩ :=
  accepted_of_selected 12 28589 ⟨434191, by decide⟩ ⟨12, 2, 0, 434191, 28589, 1205, 65536⟩
    (by decide) selected_cut_17081

theorem selected_cut_17082 : selected 9 ⟨434205, by decide⟩
    (prefixPartial 12 28590) = some ⟨12, 2, 0, 434205, 28590, 1149, 65536⟩ := by
  decide +kernel

theorem context_12_28590_434205 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28590 ⟨434205, by decide⟩ :=
  accepted_of_selected 12 28590 ⟨434205, by decide⟩ ⟨12, 2, 0, 434205, 28590, 1149, 65536⟩
    (by decide) selected_cut_17082

theorem selected_cut_17083 : selected 9 ⟨434243, by decide⟩
    (prefixPartial 12 28591) = some ⟨12, 2, 0, 434243, 28591, 1897, 65536⟩ := by
  decide +kernel

theorem context_12_28591_434243 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28591 ⟨434243, by decide⟩ :=
  accepted_of_selected 12 28591 ⟨434243, by decide⟩ ⟨12, 2, 0, 434243, 28591, 1897, 65536⟩
    (by decide) selected_cut_17083

theorem unmarked_context_11_7147_434244 : frontier 10 ⟨434244, by decide⟩
    (prefixCache 11 7147) (prefixPartial 11 7147) = false := by
  decide +kernel

theorem node_context_11_7147_434244 : EJMOriginalGlobalDAGData.nodes 10 ⟨434244, by decide⟩ =
    .split (coordinate 11) (![⟨434178, by decide⟩,⟨434191, by decide⟩,⟨434205, by decide⟩,⟨434243, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_7147_434244 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7147 ⟨434244, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 7147
    ⟨434244, by decide⟩ (by decide) (![⟨434178, by decide⟩,⟨434191, by decide⟩,⟨434205, by decide⟩,⟨434243, by decide⟩]) unmarked_context_11_7147_434244 node_context_11_7147_434244
  intro a
  fin_cases a
  · exact context_12_28588_434178
  · exact context_12_28589_434191
  · exact context_12_28590_434205
  · exact context_12_28591_434243

theorem unmarked_context_10_1786_434245 : frontier 11 ⟨434245, by decide⟩
    (prefixCache 10 1786) (prefixPartial 10 1786) = false := by
  decide +kernel

theorem node_context_10_1786_434245 : EJMOriginalGlobalDAGData.nodes 11 ⟨434245, by decide⟩ =
    .split (coordinate 10) (![⟨434033, by decide⟩,⟨434101, by decide⟩,⟨434166, by decide⟩,⟨434244, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1786_434245 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1786 ⟨434245, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1786
    ⟨434245, by decide⟩ (by decide) (![⟨434033, by decide⟩,⟨434101, by decide⟩,⟨434166, by decide⟩,⟨434244, by decide⟩]) unmarked_context_10_1786_434245 node_context_10_1786_434245
  intro a
  fin_cases a
  · exact context_11_7144_434033
  · exact context_11_7145_434101
  · exact context_11_7146_434166
  · exact context_11_7147_434244

theorem selected_cut_17084 : selected 9 ⟨434257, by decide⟩
    (prefixPartial 12 28592) = some ⟨12, 2, 0, 434257, 28592, 1273, 65536⟩ := by
  decide +kernel

theorem context_12_28592_434257 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28592 ⟨434257, by decide⟩ :=
  accepted_of_selected 12 28592 ⟨434257, by decide⟩ ⟨12, 2, 0, 434257, 28592, 1273, 65536⟩
    (by decide) selected_cut_17084

theorem selected_cut_17085 : selected 9 ⟨434273, by decide⟩
    (prefixPartial 12 28593) = some ⟨12, 2, 0, 434273, 28593, 1109, 65536⟩ := by
  decide +kernel

theorem context_12_28593_434273 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28593 ⟨434273, by decide⟩ :=
  accepted_of_selected 12 28593 ⟨434273, by decide⟩ ⟨12, 2, 0, 434273, 28593, 1109, 65536⟩
    (by decide) selected_cut_17085

theorem selected_cut_17086 : selected 9 ⟨434286, by decide⟩
    (prefixPartial 12 28594) = some ⟨12, 2, 0, 434286, 28594, 1129, 65536⟩ := by
  decide +kernel

theorem context_12_28594_434286 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28594 ⟨434286, by decide⟩ :=
  accepted_of_selected 12 28594 ⟨434286, by decide⟩ ⟨12, 2, 0, 434286, 28594, 1129, 65536⟩
    (by decide) selected_cut_17086

theorem selected_cut_17087 : selected 9 ⟨434297, by decide⟩
    (prefixPartial 12 28595) = some ⟨12, 2, 0, 434297, 28595, 1077, 65536⟩ := by
  decide +kernel

theorem context_12_28595_434297 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28595 ⟨434297, by decide⟩ :=
  accepted_of_selected 12 28595 ⟨434297, by decide⟩ ⟨12, 2, 0, 434297, 28595, 1077, 65536⟩
    (by decide) selected_cut_17087

theorem unmarked_context_11_7148_434298 : frontier 10 ⟨434298, by decide⟩
    (prefixCache 11 7148) (prefixPartial 11 7148) = false := by
  decide +kernel

theorem node_context_11_7148_434298 : EJMOriginalGlobalDAGData.nodes 10 ⟨434298, by decide⟩ =
    .split (coordinate 11) (![⟨434257, by decide⟩,⟨434273, by decide⟩,⟨434286, by decide⟩,⟨434297, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_7148_434298 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7148 ⟨434298, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 7148
    ⟨434298, by decide⟩ (by decide) (![⟨434257, by decide⟩,⟨434273, by decide⟩,⟨434286, by decide⟩,⟨434297, by decide⟩]) unmarked_context_11_7148_434298 node_context_11_7148_434298
  intro a
  fin_cases a
  · exact context_12_28592_434257
  · exact context_12_28593_434273
  · exact context_12_28594_434286
  · exact context_12_28595_434297

theorem selected_cut_17088 : selected 9 ⟨434313, by decide⟩
    (prefixPartial 12 28596) = some ⟨12, 2, 0, 434313, 28596, 1261, 65536⟩ := by
  decide +kernel

theorem context_12_28596_434313 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28596 ⟨434313, by decide⟩ :=
  accepted_of_selected 12 28596 ⟨434313, by decide⟩ ⟨12, 2, 0, 434313, 28596, 1261, 65536⟩
    (by decide) selected_cut_17088

theorem selected_cut_17089 : selected 9 ⟨434329, by decide⟩
    (prefixPartial 12 28597) = some ⟨12, 2, 0, 434329, 28597, 1217, 65536⟩ := by
  decide +kernel

theorem context_12_28597_434329 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28597 ⟨434329, by decide⟩ :=
  accepted_of_selected 12 28597 ⟨434329, by decide⟩ ⟨12, 2, 0, 434329, 28597, 1217, 65536⟩
    (by decide) selected_cut_17089

theorem selected_cut_17090 : selected 9 ⟨434343, by decide⟩
    (prefixPartial 12 28598) = some ⟨12, 2, 0, 434343, 28598, 1281, 65536⟩ := by
  decide +kernel

theorem context_12_28598_434343 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28598 ⟨434343, by decide⟩ :=
  accepted_of_selected 12 28598 ⟨434343, by decide⟩ ⟨12, 2, 0, 434343, 28598, 1281, 65536⟩
    (by decide) selected_cut_17090

theorem selected_cut_17091 : selected 9 ⟨434354, by decide⟩
    (prefixPartial 12 28599) = some ⟨12, 2, 0, 434354, 28599, 1241, 65536⟩ := by
  decide +kernel

theorem context_12_28599_434354 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28599 ⟨434354, by decide⟩ :=
  accepted_of_selected 12 28599 ⟨434354, by decide⟩ ⟨12, 2, 0, 434354, 28599, 1241, 65536⟩
    (by decide) selected_cut_17091

theorem unmarked_context_11_7149_434355 : frontier 10 ⟨434355, by decide⟩
    (prefixCache 11 7149) (prefixPartial 11 7149) = false := by
  decide +kernel

theorem node_context_11_7149_434355 : EJMOriginalGlobalDAGData.nodes 10 ⟨434355, by decide⟩ =
    .split (coordinate 11) (![⟨434313, by decide⟩,⟨434329, by decide⟩,⟨434343, by decide⟩,⟨434354, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_7149_434355 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7149 ⟨434355, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 7149
    ⟨434355, by decide⟩ (by decide) (![⟨434313, by decide⟩,⟨434329, by decide⟩,⟨434343, by decide⟩,⟨434354, by decide⟩]) unmarked_context_11_7149_434355 node_context_11_7149_434355
  intro a
  fin_cases a
  · exact context_12_28596_434313
  · exact context_12_28597_434329
  · exact context_12_28598_434343
  · exact context_12_28599_434354

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
