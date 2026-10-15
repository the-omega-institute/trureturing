/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover155
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_14980 : selected 8 ⟨385068, by decide⟩
    (prefixPartial 13 109927) = some ⟨13, 2, 0, 385068, 109927, 1113, 16384⟩ := by
  decide +kernel

theorem context_13_109927_385068 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109927 ⟨385068, by decide⟩ :=
  accepted_of_selected 13 109927 ⟨385068, by decide⟩ ⟨13, 2, 0, 385068, 109927, 1113, 16384⟩
    (by decide) selected_cut_14980

theorem unmarked_context_12_27481_385069 : frontier 9 ⟨385069, by decide⟩
    (prefixCache 12 27481) (prefixPartial 12 27481) = false := by
  decide +kernel

theorem node_context_12_27481_385069 : EJMOriginalGlobalDAGData.nodes 9 ⟨385069, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨385027, by decide⟩,⟨385051, by decide⟩,⟨385068, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27481_385069 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27481 ⟨385069, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27481
    ⟨385069, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨385027, by decide⟩,⟨385051, by decide⟩,⟨385068, by decide⟩]) unmarked_context_12_27481_385069 node_context_12_27481_385069
  intro a
  fin_cases a
  · exact context_13_109924_3444
  · exact context_13_109925_385027
  · exact context_13_109926_385051
  · exact context_13_109927_385068

theorem selected_cut_14981 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 109928) = some ⟨13, 1, 0, 3444, 109928, 1, 16384⟩ := by
  decide +kernel

theorem context_13_109928_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109928 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 109928 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 109928, 1, 16384⟩
    (by decide) selected_cut_14981

theorem selected_cut_14982 : selected 8 ⟨385089, by decide⟩
    (prefixPartial 13 109929) = some ⟨13, 2, 0, 385089, 109929, 1549, 16384⟩ := by
  decide +kernel

theorem context_13_109929_385089 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109929 ⟨385089, by decide⟩ :=
  accepted_of_selected 13 109929 ⟨385089, by decide⟩ ⟨13, 2, 0, 385089, 109929, 1549, 16384⟩
    (by decide) selected_cut_14982

theorem selected_cut_14983 : selected 8 ⟨385110, by decide⟩
    (prefixPartial 13 109930) = some ⟨13, 2, 0, 385110, 109930, 1753, 16384⟩ := by
  decide +kernel

theorem context_13_109930_385110 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109930 ⟨385110, by decide⟩ :=
  accepted_of_selected 13 109930 ⟨385110, by decide⟩ ⟨13, 2, 0, 385110, 109930, 1753, 16384⟩
    (by decide) selected_cut_14983

theorem selected_cut_14984 : selected 8 ⟨385119, by decide⟩
    (prefixPartial 13 109931) = some ⟨13, 2, 0, 385119, 109931, 853, 16384⟩ := by
  decide +kernel

theorem context_13_109931_385119 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109931 ⟨385119, by decide⟩ :=
  accepted_of_selected 13 109931 ⟨385119, by decide⟩ ⟨13, 2, 0, 385119, 109931, 853, 16384⟩
    (by decide) selected_cut_14984

theorem unmarked_context_12_27482_385120 : frontier 9 ⟨385120, by decide⟩
    (prefixCache 12 27482) (prefixPartial 12 27482) = false := by
  decide +kernel

theorem node_context_12_27482_385120 : EJMOriginalGlobalDAGData.nodes 9 ⟨385120, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨385089, by decide⟩,⟨385110, by decide⟩,⟨385119, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27482_385120 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27482 ⟨385120, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27482
    ⟨385120, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨385089, by decide⟩,⟨385110, by decide⟩,⟨385119, by decide⟩]) unmarked_context_12_27482_385120 node_context_12_27482_385120
  intro a
  fin_cases a
  · exact context_13_109928_3444
  · exact context_13_109929_385089
  · exact context_13_109930_385110
  · exact context_13_109931_385119

theorem selected_cut_14985 : selected 9 ⟨385168, by decide⟩
    (prefixPartial 12 27483) = some ⟨12, 2, 0, 385168, 27483, 3729, 65536⟩ := by
  decide +kernel

theorem context_12_27483_385168 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27483 ⟨385168, by decide⟩ :=
  accepted_of_selected 12 27483 ⟨385168, by decide⟩ ⟨12, 2, 0, 385168, 27483, 3729, 65536⟩
    (by decide) selected_cut_14985

theorem unmarked_context_11_6870_385169 : frontier 10 ⟨385169, by decide⟩
    (prefixCache 11 6870) (prefixPartial 11 6870) = false := by
  decide +kernel

theorem node_context_11_6870_385169 : EJMOriginalGlobalDAGData.nodes 10 ⟨385169, by decide⟩ =
    .split (coordinate 11) (![⟨384992, by decide⟩,⟨385069, by decide⟩,⟨385120, by decide⟩,⟨385168, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6870_385169 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6870 ⟨385169, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6870
    ⟨385169, by decide⟩ (by decide) (![⟨384992, by decide⟩,⟨385069, by decide⟩,⟨385120, by decide⟩,⟨385168, by decide⟩]) unmarked_context_11_6870_385169 node_context_11_6870_385169
  intro a
  fin_cases a
  · exact context_12_27480_384992
  · exact context_12_27481_385069
  · exact context_12_27482_385120
  · exact context_12_27483_385168

theorem selected_cut_14986 : selected 9 ⟨385207, by decide⟩
    (prefixPartial 12 27484) = some ⟨12, 2, 0, 385207, 27484, 3021, 65536⟩ := by
  decide +kernel

theorem context_12_27484_385207 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27484 ⟨385207, by decide⟩ :=
  accepted_of_selected 12 27484 ⟨385207, by decide⟩ ⟨12, 2, 0, 385207, 27484, 3021, 65536⟩
    (by decide) selected_cut_14986

theorem selected_cut_14987 : selected 9 ⟨385236, by decide⟩
    (prefixPartial 12 27485) = some ⟨12, 2, 0, 385236, 27485, 1877, 65536⟩ := by
  decide +kernel

theorem context_12_27485_385236 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27485 ⟨385236, by decide⟩ :=
  accepted_of_selected 12 27485 ⟨385236, by decide⟩ ⟨12, 2, 0, 385236, 27485, 1877, 65536⟩
    (by decide) selected_cut_14987

theorem selected_cut_14988 : selected 9 ⟨385281, by decide⟩
    (prefixPartial 12 27486) = some ⟨12, 2, 0, 385281, 27486, 3641, 65536⟩ := by
  decide +kernel

theorem context_12_27486_385281 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27486 ⟨385281, by decide⟩ :=
  accepted_of_selected 12 27486 ⟨385281, by decide⟩ ⟨12, 2, 0, 385281, 27486, 3641, 65536⟩
    (by decide) selected_cut_14988

theorem selected_cut_14989 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 109948) = some ⟨13, 1, 0, 3444, 109948, 1, 16384⟩ := by
  decide +kernel

theorem context_13_109948_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109948 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 109948 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 109948, 1, 16384⟩
    (by decide) selected_cut_14989

theorem selected_cut_14990 : selected 8 ⟨385327, by decide⟩
    (prefixPartial 13 109949) = some ⟨13, 2, 0, 385327, 109949, 2021, 16384⟩ := by
  decide +kernel

theorem context_13_109949_385327 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109949 ⟨385327, by decide⟩ :=
  accepted_of_selected 13 109949 ⟨385327, by decide⟩ ⟨13, 2, 0, 385327, 109949, 2021, 16384⟩
    (by decide) selected_cut_14990

theorem selected_cut_14991 : selected 8 ⟨385356, by decide⟩
    (prefixPartial 13 109950) = some ⟨13, 2, 0, 385356, 109950, 2413, 16384⟩ := by
  decide +kernel

theorem context_13_109950_385356 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109950 ⟨385356, by decide⟩ :=
  accepted_of_selected 13 109950 ⟨385356, by decide⟩ ⟨13, 2, 0, 385356, 109950, 2413, 16384⟩
    (by decide) selected_cut_14991

theorem selected_cut_14992 : selected 8 ⟨385375, by decide⟩
    (prefixPartial 13 109951) = some ⟨13, 2, 0, 385375, 109951, 1153, 16384⟩ := by
  decide +kernel

theorem context_13_109951_385375 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109951 ⟨385375, by decide⟩ :=
  accepted_of_selected 13 109951 ⟨385375, by decide⟩ ⟨13, 2, 0, 385375, 109951, 1153, 16384⟩
    (by decide) selected_cut_14992

theorem unmarked_context_12_27487_385376 : frontier 9 ⟨385376, by decide⟩
    (prefixCache 12 27487) (prefixPartial 12 27487) = false := by
  decide +kernel

theorem node_context_12_27487_385376 : EJMOriginalGlobalDAGData.nodes 9 ⟨385376, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨385327, by decide⟩,⟨385356, by decide⟩,⟨385375, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27487_385376 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27487 ⟨385376, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27487
    ⟨385376, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨385327, by decide⟩,⟨385356, by decide⟩,⟨385375, by decide⟩]) unmarked_context_12_27487_385376 node_context_12_27487_385376
  intro a
  fin_cases a
  · exact context_13_109948_3444
  · exact context_13_109949_385327
  · exact context_13_109950_385356
  · exact context_13_109951_385375

theorem unmarked_context_11_6871_385377 : frontier 10 ⟨385377, by decide⟩
    (prefixCache 11 6871) (prefixPartial 11 6871) = false := by
  decide +kernel

theorem node_context_11_6871_385377 : EJMOriginalGlobalDAGData.nodes 10 ⟨385377, by decide⟩ =
    .split (coordinate 11) (![⟨385207, by decide⟩,⟨385236, by decide⟩,⟨385281, by decide⟩,⟨385376, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6871_385377 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6871 ⟨385377, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6871
    ⟨385377, by decide⟩ (by decide) (![⟨385207, by decide⟩,⟨385236, by decide⟩,⟨385281, by decide⟩,⟨385376, by decide⟩]) unmarked_context_11_6871_385377 node_context_11_6871_385377
  intro a
  fin_cases a
  · exact context_12_27484_385207
  · exact context_12_27485_385236
  · exact context_12_27486_385281
  · exact context_12_27487_385376

theorem unmarked_context_10_1717_385378 : frontier 11 ⟨385378, by decide⟩
    (prefixCache 10 1717) (prefixPartial 10 1717) = false := by
  decide +kernel

theorem node_context_10_1717_385378 : EJMOriginalGlobalDAGData.nodes 11 ⟨385378, by decide⟩ =
    .split (coordinate 10) (![⟨384785, by decide⟩,⟨384950, by decide⟩,⟨385169, by decide⟩,⟨385377, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1717_385378 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1717 ⟨385378, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1717
    ⟨385378, by decide⟩ (by decide) (![⟨384785, by decide⟩,⟨384950, by decide⟩,⟨385169, by decide⟩,⟨385377, by decide⟩]) unmarked_context_10_1717_385378 node_context_10_1717_385378
  intro a
  fin_cases a
  · exact context_11_6868_384785
  · exact context_11_6869_384950
  · exact context_11_6870_385169
  · exact context_11_6871_385377

theorem selected_cut_14993 : selected 9 ⟨385419, by decide⟩
    (prefixPartial 12 27488) = some ⟨12, 2, 0, 385419, 27488, 3517, 65536⟩ := by
  decide +kernel

theorem context_12_27488_385419 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27488 ⟨385419, by decide⟩ :=
  accepted_of_selected 12 27488 ⟨385419, by decide⟩ ⟨12, 2, 0, 385419, 27488, 3517, 65536⟩
    (by decide) selected_cut_14993

theorem selected_cut_14994 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 109956) = some ⟨13, 1, 0, 3444, 109956, 1, 16384⟩ := by
  decide +kernel

theorem context_13_109956_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109956 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 109956 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 109956, 1, 16384⟩
    (by decide) selected_cut_14994

theorem selected_cut_14995 : selected 8 ⟨385462, by decide⟩
    (prefixPartial 13 109957) = some ⟨13, 2, 0, 385462, 109957, 2177, 16384⟩ := by
  decide +kernel

theorem context_13_109957_385462 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109957 ⟨385462, by decide⟩ :=
  accepted_of_selected 13 109957 ⟨385462, by decide⟩ ⟨13, 2, 0, 385462, 109957, 2177, 16384⟩
    (by decide) selected_cut_14995

theorem selected_cut_14996 : selected 8 ⟨385488, by decide⟩
    (prefixPartial 13 109958) = some ⟨13, 2, 0, 385488, 109958, 1905, 16384⟩ := by
  decide +kernel

theorem context_13_109958_385488 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109958 ⟨385488, by decide⟩ :=
  accepted_of_selected 13 109958 ⟨385488, by decide⟩ ⟨13, 2, 0, 385488, 109958, 1905, 16384⟩
    (by decide) selected_cut_14996

theorem selected_cut_14997 : selected 8 ⟨385493, by decide⟩
    (prefixPartial 13 109959) = some ⟨13, 2, 0, 385493, 109959, 865, 16384⟩ := by
  decide +kernel

theorem context_13_109959_385493 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109959 ⟨385493, by decide⟩ :=
  accepted_of_selected 13 109959 ⟨385493, by decide⟩ ⟨13, 2, 0, 385493, 109959, 865, 16384⟩
    (by decide) selected_cut_14997

theorem unmarked_context_12_27489_385494 : frontier 9 ⟨385494, by decide⟩
    (prefixCache 12 27489) (prefixPartial 12 27489) = false := by
  decide +kernel

theorem node_context_12_27489_385494 : EJMOriginalGlobalDAGData.nodes 9 ⟨385494, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨385462, by decide⟩,⟨385488, by decide⟩,⟨385493, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27489_385494 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27489 ⟨385494, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27489
    ⟨385494, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨385462, by decide⟩,⟨385488, by decide⟩,⟨385493, by decide⟩]) unmarked_context_12_27489_385494 node_context_12_27489_385494
  intro a
  fin_cases a
  · exact context_13_109956_3444
  · exact context_13_109957_385462
  · exact context_13_109958_385488
  · exact context_13_109959_385493

theorem selected_cut_14998 : selected 9 ⟨385553, by decide⟩
    (prefixPartial 12 27490) = some ⟨12, 2, 0, 385553, 27490, 3649, 65536⟩ := by
  decide +kernel

theorem context_12_27490_385553 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27490 ⟨385553, by decide⟩ :=
  accepted_of_selected 12 27490 ⟨385553, by decide⟩ ⟨12, 2, 0, 385553, 27490, 3649, 65536⟩
    (by decide) selected_cut_14998

theorem selected_cut_14999 : selected 9 ⟨385598, by decide⟩
    (prefixPartial 12 27491) = some ⟨12, 2, 0, 385598, 27491, 3497, 65536⟩ := by
  decide +kernel

theorem context_12_27491_385598 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27491 ⟨385598, by decide⟩ :=
  accepted_of_selected 12 27491 ⟨385598, by decide⟩ ⟨12, 2, 0, 385598, 27491, 3497, 65536⟩
    (by decide) selected_cut_14999

theorem unmarked_context_11_6872_385599 : frontier 10 ⟨385599, by decide⟩
    (prefixCache 11 6872) (prefixPartial 11 6872) = false := by
  decide +kernel

theorem node_context_11_6872_385599 : EJMOriginalGlobalDAGData.nodes 10 ⟨385599, by decide⟩ =
    .split (coordinate 11) (![⟨385419, by decide⟩,⟨385494, by decide⟩,⟨385553, by decide⟩,⟨385598, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6872_385599 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6872 ⟨385599, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6872
    ⟨385599, by decide⟩ (by decide) (![⟨385419, by decide⟩,⟨385494, by decide⟩,⟨385553, by decide⟩,⟨385598, by decide⟩]) unmarked_context_11_6872_385599 node_context_11_6872_385599
  intro a
  fin_cases a
  · exact context_12_27488_385419
  · exact context_12_27489_385494
  · exact context_12_27490_385553
  · exact context_12_27491_385598

theorem selected_cut_15000 : selected 9 ⟨385640, by decide⟩
    (prefixPartial 12 27492) = some ⟨12, 2, 0, 385640, 27492, 3797, 65536⟩ := by
  decide +kernel

theorem context_12_27492_385640 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27492 ⟨385640, by decide⟩ :=
  accepted_of_selected 12 27492 ⟨385640, by decide⟩ ⟨12, 2, 0, 385640, 27492, 3797, 65536⟩
    (by decide) selected_cut_15000

theorem selected_cut_15001 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 109972) = some ⟨13, 1, 0, 3444, 109972, 1, 16384⟩ := by
  decide +kernel

theorem context_13_109972_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109972 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 109972 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 109972, 1, 16384⟩
    (by decide) selected_cut_15001

theorem selected_cut_15002 : selected 8 ⟨385674, by decide⟩
    (prefixPartial 13 109973) = some ⟨13, 2, 0, 385674, 109973, 1753, 16384⟩ := by
  decide +kernel

theorem context_13_109973_385674 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109973 ⟨385674, by decide⟩ :=
  accepted_of_selected 13 109973 ⟨385674, by decide⟩ ⟨13, 2, 0, 385674, 109973, 1753, 16384⟩
    (by decide) selected_cut_15002

theorem selected_cut_15003 : selected 8 ⟨385709, by decide⟩
    (prefixPartial 13 109974) = some ⟨13, 2, 0, 385709, 109974, 2225, 16384⟩ := by
  decide +kernel

theorem context_13_109974_385709 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109974 ⟨385709, by decide⟩ :=
  accepted_of_selected 13 109974 ⟨385709, by decide⟩ ⟨13, 2, 0, 385709, 109974, 2225, 16384⟩
    (by decide) selected_cut_15003

theorem selected_cut_15004 : selected 8 ⟨385719, by decide⟩
    (prefixPartial 13 109975) = some ⟨13, 2, 0, 385719, 109975, 1041, 16384⟩ := by
  decide +kernel

theorem context_13_109975_385719 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109975 ⟨385719, by decide⟩ :=
  accepted_of_selected 13 109975 ⟨385719, by decide⟩ ⟨13, 2, 0, 385719, 109975, 1041, 16384⟩
    (by decide) selected_cut_15004

theorem unmarked_context_12_27493_385720 : frontier 9 ⟨385720, by decide⟩
    (prefixCache 12 27493) (prefixPartial 12 27493) = false := by
  decide +kernel

theorem node_context_12_27493_385720 : EJMOriginalGlobalDAGData.nodes 9 ⟨385720, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨385674, by decide⟩,⟨385709, by decide⟩,⟨385719, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27493_385720 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27493 ⟨385720, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27493
    ⟨385720, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨385674, by decide⟩,⟨385709, by decide⟩,⟨385719, by decide⟩]) unmarked_context_12_27493_385720 node_context_12_27493_385720
  intro a
  fin_cases a
  · exact context_13_109972_3444
  · exact context_13_109973_385674
  · exact context_13_109974_385709
  · exact context_13_109975_385719

theorem selected_cut_15005 : selected 9 ⟨385775, by decide⟩
    (prefixPartial 12 27494) = some ⟨12, 2, 0, 385775, 27494, 3869, 65536⟩ := by
  decide +kernel

theorem context_12_27494_385775 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27494 ⟨385775, by decide⟩ :=
  accepted_of_selected 12 27494 ⟨385775, by decide⟩ ⟨12, 2, 0, 385775, 27494, 3869, 65536⟩
    (by decide) selected_cut_15005

theorem selected_cut_15006 : selected 9 ⟨385822, by decide⟩
    (prefixPartial 12 27495) = some ⟨12, 2, 0, 385822, 27495, 3801, 65536⟩ := by
  decide +kernel

theorem context_12_27495_385822 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27495 ⟨385822, by decide⟩ :=
  accepted_of_selected 12 27495 ⟨385822, by decide⟩ ⟨12, 2, 0, 385822, 27495, 3801, 65536⟩
    (by decide) selected_cut_15006

theorem unmarked_context_11_6873_385823 : frontier 10 ⟨385823, by decide⟩
    (prefixCache 11 6873) (prefixPartial 11 6873) = false := by
  decide +kernel

theorem node_context_11_6873_385823 : EJMOriginalGlobalDAGData.nodes 10 ⟨385823, by decide⟩ =
    .split (coordinate 11) (![⟨385640, by decide⟩,⟨385720, by decide⟩,⟨385775, by decide⟩,⟨385822, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6873_385823 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6873 ⟨385823, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6873
    ⟨385823, by decide⟩ (by decide) (![⟨385640, by decide⟩,⟨385720, by decide⟩,⟨385775, by decide⟩,⟨385822, by decide⟩]) unmarked_context_11_6873_385823 node_context_11_6873_385823
  intro a
  fin_cases a
  · exact context_12_27492_385640
  · exact context_12_27493_385720
  · exact context_12_27494_385775
  · exact context_12_27495_385822

theorem selected_cut_15007 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 109984) = some ⟨13, 1, 0, 3444, 109984, 1, 16384⟩ := by
  decide +kernel

theorem context_13_109984_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109984 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 109984 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 109984, 1, 16384⟩
    (by decide) selected_cut_15007

theorem selected_cut_15008 : selected 8 ⟨385854, by decide⟩
    (prefixPartial 13 109985) = some ⟨13, 2, 0, 385854, 109985, 1529, 16384⟩ := by
  decide +kernel

theorem context_13_109985_385854 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109985 ⟨385854, by decide⟩ :=
  accepted_of_selected 13 109985 ⟨385854, by decide⟩ ⟨13, 2, 0, 385854, 109985, 1529, 16384⟩
    (by decide) selected_cut_15008

theorem selected_cut_15009 : selected 8 ⟨385893, by decide⟩
    (prefixPartial 13 109986) = some ⟨13, 2, 0, 385893, 109986, 2153, 16384⟩ := by
  decide +kernel

theorem context_13_109986_385893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109986 ⟨385893, by decide⟩ :=
  accepted_of_selected 13 109986 ⟨385893, by decide⟩ ⟨13, 2, 0, 385893, 109986, 2153, 16384⟩
    (by decide) selected_cut_15009

theorem selected_cut_15010 : selected 8 ⟨385917, by decide⟩
    (prefixPartial 13 109987) = some ⟨13, 2, 0, 385917, 109987, 1181, 16384⟩ := by
  decide +kernel

theorem context_13_109987_385917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109987 ⟨385917, by decide⟩ :=
  accepted_of_selected 13 109987 ⟨385917, by decide⟩ ⟨13, 2, 0, 385917, 109987, 1181, 16384⟩
    (by decide) selected_cut_15010

theorem unmarked_context_12_27496_385918 : frontier 9 ⟨385918, by decide⟩
    (prefixCache 12 27496) (prefixPartial 12 27496) = false := by
  decide +kernel

theorem node_context_12_27496_385918 : EJMOriginalGlobalDAGData.nodes 9 ⟨385918, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨385854, by decide⟩,⟨385893, by decide⟩,⟨385917, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27496_385918 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27496 ⟨385918, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27496
    ⟨385918, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨385854, by decide⟩,⟨385893, by decide⟩,⟨385917, by decide⟩]) unmarked_context_12_27496_385918 node_context_12_27496_385918
  intro a
  fin_cases a
  · exact context_13_109984_3444
  · exact context_13_109985_385854
  · exact context_13_109986_385893
  · exact context_13_109987_385917

theorem selected_cut_15011 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 109988) = some ⟨13, 1, 0, 3444, 109988, 1, 16384⟩ := by
  decide +kernel

theorem context_13_109988_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109988 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 109988 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 109988, 1, 16384⟩
    (by decide) selected_cut_15011

theorem selected_cut_15012 : selected 8 ⟨385974, by decide⟩
    (prefixPartial 13 109989) = some ⟨13, 2, 0, 385974, 109989, 2101, 16384⟩ := by
  decide +kernel

theorem context_13_109989_385974 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109989 ⟨385974, by decide⟩ :=
  accepted_of_selected 13 109989 ⟨385974, by decide⟩ ⟨13, 2, 0, 385974, 109989, 2101, 16384⟩
    (by decide) selected_cut_15012

theorem selected_cut_15013 : selected 8 ⟨386045, by decide⟩
    (prefixPartial 13 109990) = some ⟨13, 2, 0, 386045, 109990, 3013, 16384⟩ := by
  decide +kernel

theorem context_13_109990_386045 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109990 ⟨386045, by decide⟩ :=
  accepted_of_selected 13 109990 ⟨386045, by decide⟩ ⟨13, 2, 0, 386045, 109990, 3013, 16384⟩
    (by decide) selected_cut_15013

theorem selected_cut_15014 : selected 8 ⟨386111, by decide⟩
    (prefixPartial 13 109991) = some ⟨13, 2, 0, 386111, 109991, 1621, 16384⟩ := by
  decide +kernel

theorem context_13_109991_386111 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109991 ⟨386111, by decide⟩ :=
  accepted_of_selected 13 109991 ⟨386111, by decide⟩ ⟨13, 2, 0, 386111, 109991, 1621, 16384⟩
    (by decide) selected_cut_15014

theorem unmarked_context_12_27497_386112 : frontier 9 ⟨386112, by decide⟩
    (prefixCache 12 27497) (prefixPartial 12 27497) = false := by
  decide +kernel

theorem node_context_12_27497_386112 : EJMOriginalGlobalDAGData.nodes 9 ⟨386112, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨385974, by decide⟩,⟨386045, by decide⟩,⟨386111, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27497_386112 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27497 ⟨386112, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27497
    ⟨386112, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨385974, by decide⟩,⟨386045, by decide⟩,⟨386111, by decide⟩]) unmarked_context_12_27497_386112 node_context_12_27497_386112
  intro a
  fin_cases a
  · exact context_13_109988_3444
  · exact context_13_109989_385974
  · exact context_13_109990_386045
  · exact context_13_109991_386111

theorem selected_cut_15015 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 109992) = some ⟨13, 1, 0, 3444, 109992, 1, 16384⟩ := by
  decide +kernel

theorem context_13_109992_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109992 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 109992 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 109992, 1, 16384⟩
    (by decide) selected_cut_15015

theorem selected_cut_15016 : selected 8 ⟨386149, by decide⟩
    (prefixPartial 13 109993) = some ⟨13, 2, 0, 386149, 109993, 1357, 16384⟩ := by
  decide +kernel

theorem context_13_109993_386149 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109993 ⟨386149, by decide⟩ :=
  accepted_of_selected 13 109993 ⟨386149, by decide⟩ ⟨13, 2, 0, 386149, 109993, 1357, 16384⟩
    (by decide) selected_cut_15016

theorem selected_cut_15017 : selected 8 ⟨386184, by decide⟩
    (prefixPartial 13 109994) = some ⟨13, 2, 0, 386184, 109994, 2261, 16384⟩ := by
  decide +kernel

theorem context_13_109994_386184 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109994 ⟨386184, by decide⟩ :=
  accepted_of_selected 13 109994 ⟨386184, by decide⟩ ⟨13, 2, 0, 386184, 109994, 2261, 16384⟩
    (by decide) selected_cut_15017

theorem selected_cut_15018 : selected 8 ⟨386201, by decide⟩
    (prefixPartial 13 109995) = some ⟨13, 2, 0, 386201, 109995, 1145, 16384⟩ := by
  decide +kernel

theorem context_13_109995_386201 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109995 ⟨386201, by decide⟩ :=
  accepted_of_selected 13 109995 ⟨386201, by decide⟩ ⟨13, 2, 0, 386201, 109995, 1145, 16384⟩
    (by decide) selected_cut_15018

theorem unmarked_context_12_27498_386202 : frontier 9 ⟨386202, by decide⟩
    (prefixCache 12 27498) (prefixPartial 12 27498) = false := by
  decide +kernel

theorem node_context_12_27498_386202 : EJMOriginalGlobalDAGData.nodes 9 ⟨386202, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨386149, by decide⟩,⟨386184, by decide⟩,⟨386201, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27498_386202 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27498 ⟨386202, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27498
    ⟨386202, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨386149, by decide⟩,⟨386184, by decide⟩,⟨386201, by decide⟩]) unmarked_context_12_27498_386202 node_context_12_27498_386202
  intro a
  fin_cases a
  · exact context_13_109992_3444
  · exact context_13_109993_386149
  · exact context_13_109994_386184
  · exact context_13_109995_386201

theorem selected_cut_15019 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 109996) = some ⟨13, 1, 0, 3444, 109996, 1, 16384⟩ := by
  decide +kernel

theorem context_13_109996_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109996 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 109996 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 109996, 1, 16384⟩
    (by decide) selected_cut_15019

theorem selected_cut_15020 : selected 8 ⟨386232, by decide⟩
    (prefixPartial 13 109997) = some ⟨13, 2, 0, 386232, 109997, 1241, 16384⟩ := by
  decide +kernel

theorem context_13_109997_386232 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109997 ⟨386232, by decide⟩ :=
  accepted_of_selected 13 109997 ⟨386232, by decide⟩ ⟨13, 2, 0, 386232, 109997, 1241, 16384⟩
    (by decide) selected_cut_15020

theorem selected_cut_15021 : selected 8 ⟨386256, by decide⟩
    (prefixPartial 13 109998) = some ⟨13, 2, 0, 386256, 109998, 2225, 16384⟩ := by
  decide +kernel

theorem context_13_109998_386256 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109998 ⟨386256, by decide⟩ :=
  accepted_of_selected 13 109998 ⟨386256, by decide⟩ ⟨13, 2, 0, 386256, 109998, 2225, 16384⟩
    (by decide) selected_cut_15021

theorem selected_cut_15022 : selected 8 ⟨386268, by decide⟩
    (prefixPartial 13 109999) = some ⟨13, 2, 0, 386268, 109999, 1025, 16384⟩ := by
  decide +kernel

theorem context_13_109999_386268 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109999 ⟨386268, by decide⟩ :=
  accepted_of_selected 13 109999 ⟨386268, by decide⟩ ⟨13, 2, 0, 386268, 109999, 1025, 16384⟩
    (by decide) selected_cut_15022

theorem unmarked_context_12_27499_386269 : frontier 9 ⟨386269, by decide⟩
    (prefixCache 12 27499) (prefixPartial 12 27499) = false := by
  decide +kernel

theorem node_context_12_27499_386269 : EJMOriginalGlobalDAGData.nodes 9 ⟨386269, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨386232, by decide⟩,⟨386256, by decide⟩,⟨386268, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27499_386269 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27499 ⟨386269, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27499
    ⟨386269, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨386232, by decide⟩,⟨386256, by decide⟩,⟨386268, by decide⟩]) unmarked_context_12_27499_386269 node_context_12_27499_386269
  intro a
  fin_cases a
  · exact context_13_109996_3444
  · exact context_13_109997_386232
  · exact context_13_109998_386256
  · exact context_13_109999_386268

theorem unmarked_context_11_6874_386270 : frontier 10 ⟨386270, by decide⟩
    (prefixCache 11 6874) (prefixPartial 11 6874) = false := by
  decide +kernel

theorem node_context_11_6874_386270 : EJMOriginalGlobalDAGData.nodes 10 ⟨386270, by decide⟩ =
    .split (coordinate 11) (![⟨385918, by decide⟩,⟨386112, by decide⟩,⟨386202, by decide⟩,⟨386269, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6874_386270 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6874 ⟨386270, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6874
    ⟨386270, by decide⟩ (by decide) (![⟨385918, by decide⟩,⟨386112, by decide⟩,⟨386202, by decide⟩,⟨386269, by decide⟩]) unmarked_context_11_6874_386270 node_context_11_6874_386270
  intro a
  fin_cases a
  · exact context_12_27496_385918
  · exact context_12_27497_386112
  · exact context_12_27498_386202
  · exact context_12_27499_386269

theorem selected_cut_15023 : selected 9 ⟨386306, by decide⟩
    (prefixPartial 12 27500) = some ⟨12, 2, 0, 386306, 27500, 2741, 65536⟩ := by
  decide +kernel

theorem context_12_27500_386306 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27500 ⟨386306, by decide⟩ :=
  accepted_of_selected 12 27500 ⟨386306, by decide⟩ ⟨12, 2, 0, 386306, 27500, 2741, 65536⟩
    (by decide) selected_cut_15023

theorem selected_cut_15024 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 110004) = some ⟨13, 1, 0, 3444, 110004, 1, 16384⟩ := by
  decide +kernel

theorem context_13_110004_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110004 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 110004 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 110004, 1, 16384⟩
    (by decide) selected_cut_15024

theorem selected_cut_15025 : selected 8 ⟨386330, by decide⟩
    (prefixPartial 13 110005) = some ⟨13, 2, 0, 386330, 110005, 1065, 16384⟩ := by
  decide +kernel

theorem context_13_110005_386330 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110005 ⟨386330, by decide⟩ :=
  accepted_of_selected 13 110005 ⟨386330, by decide⟩ ⟨13, 2, 0, 386330, 110005, 1065, 16384⟩
    (by decide) selected_cut_15025

theorem selected_cut_15026 : selected 8 ⟨386354, by decide⟩
    (prefixPartial 13 110006) = some ⟨13, 2, 0, 386354, 110006, 2001, 16384⟩ := by
  decide +kernel

theorem context_13_110006_386354 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110006 ⟨386354, by decide⟩ :=
  accepted_of_selected 13 110006 ⟨386354, by decide⟩ ⟨13, 2, 0, 386354, 110006, 2001, 16384⟩
    (by decide) selected_cut_15026

theorem selected_cut_15027 : selected 8 ⟨386370, by decide⟩
    (prefixPartial 13 110007) = some ⟨13, 2, 0, 386370, 110007, 1057, 16384⟩ := by
  decide +kernel

theorem context_13_110007_386370 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110007 ⟨386370, by decide⟩ :=
  accepted_of_selected 13 110007 ⟨386370, by decide⟩ ⟨13, 2, 0, 386370, 110007, 1057, 16384⟩
    (by decide) selected_cut_15027

theorem unmarked_context_12_27501_386371 : frontier 9 ⟨386371, by decide⟩
    (prefixCache 12 27501) (prefixPartial 12 27501) = false := by
  decide +kernel

theorem node_context_12_27501_386371 : EJMOriginalGlobalDAGData.nodes 9 ⟨386371, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨386330, by decide⟩,⟨386354, by decide⟩,⟨386370, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27501_386371 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27501 ⟨386371, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27501
    ⟨386371, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨386330, by decide⟩,⟨386354, by decide⟩,⟨386370, by decide⟩]) unmarked_context_12_27501_386371 node_context_12_27501_386371
  intro a
  fin_cases a
  · exact context_13_110004_3444
  · exact context_13_110005_386330
  · exact context_13_110006_386354
  · exact context_13_110007_386370

theorem selected_cut_15028 : selected 9 ⟨386413, by decide⟩
    (prefixPartial 12 27502) = some ⟨12, 2, 0, 386413, 27502, 2885, 65536⟩ := by
  decide +kernel

theorem context_12_27502_386413 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27502 ⟨386413, by decide⟩ :=
  accepted_of_selected 12 27502 ⟨386413, by decide⟩ ⟨12, 2, 0, 386413, 27502, 2885, 65536⟩
    (by decide) selected_cut_15028

theorem selected_cut_15029 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 110012) = some ⟨13, 1, 0, 3444, 110012, 1, 16384⟩ := by
  decide +kernel

theorem context_13_110012_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110012 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 110012 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 110012, 1, 16384⟩
    (by decide) selected_cut_15029

theorem selected_cut_15030 : selected 8 ⟨386440, by decide⟩
    (prefixPartial 13 110013) = some ⟨13, 2, 0, 386440, 110013, 1073, 16384⟩ := by
  decide +kernel

theorem context_13_110013_386440 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110013 ⟨386440, by decide⟩ :=
  accepted_of_selected 13 110013 ⟨386440, by decide⟩ ⟨13, 2, 0, 386440, 110013, 1073, 16384⟩
    (by decide) selected_cut_15030

theorem selected_cut_15031 : selected 8 ⟨386483, by decide⟩
    (prefixPartial 13 110014) = some ⟨13, 2, 0, 386483, 110014, 2541, 16384⟩ := by
  decide +kernel

theorem context_13_110014_386483 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110014 ⟨386483, by decide⟩ :=
  accepted_of_selected 13 110014 ⟨386483, by decide⟩ ⟨13, 2, 0, 386483, 110014, 2541, 16384⟩
    (by decide) selected_cut_15031

theorem selected_cut_15032 : selected 8 ⟨386507, by decide⟩
    (prefixPartial 13 110015) = some ⟨13, 2, 0, 386507, 110015, 1225, 16384⟩ := by
  decide +kernel

theorem context_13_110015_386507 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110015 ⟨386507, by decide⟩ :=
  accepted_of_selected 13 110015 ⟨386507, by decide⟩ ⟨13, 2, 0, 386507, 110015, 1225, 16384⟩
    (by decide) selected_cut_15032

theorem unmarked_context_12_27503_386508 : frontier 9 ⟨386508, by decide⟩
    (prefixCache 12 27503) (prefixPartial 12 27503) = false := by
  decide +kernel

theorem node_context_12_27503_386508 : EJMOriginalGlobalDAGData.nodes 9 ⟨386508, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨386440, by decide⟩,⟨386483, by decide⟩,⟨386507, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27503_386508 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27503 ⟨386508, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27503
    ⟨386508, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨386440, by decide⟩,⟨386483, by decide⟩,⟨386507, by decide⟩]) unmarked_context_12_27503_386508 node_context_12_27503_386508
  intro a
  fin_cases a
  · exact context_13_110012_3444
  · exact context_13_110013_386440
  · exact context_13_110014_386483
  · exact context_13_110015_386507

theorem unmarked_context_11_6875_386509 : frontier 10 ⟨386509, by decide⟩
    (prefixCache 11 6875) (prefixPartial 11 6875) = false := by
  decide +kernel

theorem node_context_11_6875_386509 : EJMOriginalGlobalDAGData.nodes 10 ⟨386509, by decide⟩ =
    .split (coordinate 11) (![⟨386306, by decide⟩,⟨386371, by decide⟩,⟨386413, by decide⟩,⟨386508, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6875_386509 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6875 ⟨386509, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6875
    ⟨386509, by decide⟩ (by decide) (![⟨386306, by decide⟩,⟨386371, by decide⟩,⟨386413, by decide⟩,⟨386508, by decide⟩]) unmarked_context_11_6875_386509 node_context_11_6875_386509
  intro a
  fin_cases a
  · exact context_12_27500_386306
  · exact context_12_27501_386371
  · exact context_12_27502_386413
  · exact context_12_27503_386508

theorem unmarked_context_10_1718_386510 : frontier 11 ⟨386510, by decide⟩
    (prefixCache 10 1718) (prefixPartial 10 1718) = false := by
  decide +kernel

theorem node_context_10_1718_386510 : EJMOriginalGlobalDAGData.nodes 11 ⟨386510, by decide⟩ =
    .split (coordinate 10) (![⟨385599, by decide⟩,⟨385823, by decide⟩,⟨386270, by decide⟩,⟨386509, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1718_386510 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1718 ⟨386510, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1718
    ⟨386510, by decide⟩ (by decide) (![⟨385599, by decide⟩,⟨385823, by decide⟩,⟨386270, by decide⟩,⟨386509, by decide⟩]) unmarked_context_10_1718_386510 node_context_10_1718_386510
  intro a
  fin_cases a
  · exact context_11_6872_385599
  · exact context_11_6873_385823
  · exact context_11_6874_386270
  · exact context_11_6875_386509

theorem selected_cut_15033 : selected 9 ⟨386555, by decide⟩
    (prefixPartial 12 27504) = some ⟨12, 2, 0, 386555, 27504, 2957, 65536⟩ := by
  decide +kernel

theorem context_12_27504_386555 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27504 ⟨386555, by decide⟩ :=
  accepted_of_selected 12 27504 ⟨386555, by decide⟩ ⟨12, 2, 0, 386555, 27504, 2957, 65536⟩
    (by decide) selected_cut_15033

theorem selected_cut_15034 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 110020) = some ⟨13, 1, 0, 3444, 110020, 1, 16384⟩ := by
  decide +kernel

theorem context_13_110020_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110020 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 110020 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 110020, 1, 16384⟩
    (by decide) selected_cut_15034

theorem selected_cut_15035 : selected 8 ⟨386589, by decide⟩
    (prefixPartial 13 110021) = some ⟨13, 2, 0, 386589, 110021, 945, 16384⟩ := by
  decide +kernel

theorem context_13_110021_386589 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110021 ⟨386589, by decide⟩ :=
  accepted_of_selected 13 110021 ⟨386589, by decide⟩ ⟨13, 2, 0, 386589, 110021, 945, 16384⟩
    (by decide) selected_cut_15035

theorem selected_cut_15036 : selected 8 ⟨386637, by decide⟩
    (prefixPartial 13 110022) = some ⟨13, 2, 0, 386637, 110022, 2273, 16384⟩ := by
  decide +kernel

theorem context_13_110022_386637 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110022 ⟨386637, by decide⟩ :=
  accepted_of_selected 13 110022 ⟨386637, by decide⟩ ⟨13, 2, 0, 386637, 110022, 2273, 16384⟩
    (by decide) selected_cut_15036

theorem selected_cut_15037 : selected 8 ⟨386668, by decide⟩
    (prefixPartial 13 110023) = some ⟨13, 2, 0, 386668, 110023, 1093, 16384⟩ := by
  decide +kernel

theorem context_13_110023_386668 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110023 ⟨386668, by decide⟩ :=
  accepted_of_selected 13 110023 ⟨386668, by decide⟩ ⟨13, 2, 0, 386668, 110023, 1093, 16384⟩
    (by decide) selected_cut_15037

theorem unmarked_context_12_27505_386669 : frontier 9 ⟨386669, by decide⟩
    (prefixCache 12 27505) (prefixPartial 12 27505) = false := by
  decide +kernel

theorem node_context_12_27505_386669 : EJMOriginalGlobalDAGData.nodes 9 ⟨386669, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨386589, by decide⟩,⟨386637, by decide⟩,⟨386668, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27505_386669 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27505 ⟨386669, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27505
    ⟨386669, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨386589, by decide⟩,⟨386637, by decide⟩,⟨386668, by decide⟩]) unmarked_context_12_27505_386669 node_context_12_27505_386669
  intro a
  fin_cases a
  · exact context_13_110020_3444
  · exact context_13_110021_386589
  · exact context_13_110022_386637
  · exact context_13_110023_386668

theorem selected_cut_15038 : selected 9 ⟨386719, by decide⟩
    (prefixPartial 12 27506) = some ⟨12, 2, 0, 386719, 27506, 3337, 65536⟩ := by
  decide +kernel

theorem context_12_27506_386719 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27506 ⟨386719, by decide⟩ :=
  accepted_of_selected 12 27506 ⟨386719, by decide⟩ ⟨12, 2, 0, 386719, 27506, 3337, 65536⟩
    (by decide) selected_cut_15038

theorem selected_cut_15039 : selected 9 ⟨386752, by decide⟩
    (prefixPartial 12 27507) = some ⟨12, 2, 0, 386752, 27507, 3161, 65536⟩ := by
  decide +kernel

theorem context_12_27507_386752 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27507 ⟨386752, by decide⟩ :=
  accepted_of_selected 12 27507 ⟨386752, by decide⟩ ⟨12, 2, 0, 386752, 27507, 3161, 65536⟩
    (by decide) selected_cut_15039

theorem unmarked_context_11_6876_386753 : frontier 10 ⟨386753, by decide⟩
    (prefixCache 11 6876) (prefixPartial 11 6876) = false := by
  decide +kernel

theorem node_context_11_6876_386753 : EJMOriginalGlobalDAGData.nodes 10 ⟨386753, by decide⟩ =
    .split (coordinate 11) (![⟨386555, by decide⟩,⟨386669, by decide⟩,⟨386719, by decide⟩,⟨386752, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6876_386753 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6876 ⟨386753, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6876
    ⟨386753, by decide⟩ (by decide) (![⟨386555, by decide⟩,⟨386669, by decide⟩,⟨386719, by decide⟩,⟨386752, by decide⟩]) unmarked_context_11_6876_386753 node_context_11_6876_386753
  intro a
  fin_cases a
  · exact context_12_27504_386555
  · exact context_12_27505_386669
  · exact context_12_27506_386719
  · exact context_12_27507_386752

theorem selected_cut_15040 : selected 9 ⟨386788, by decide⟩
    (prefixPartial 12 27508) = some ⟨12, 2, 0, 386788, 27508, 2969, 65536⟩ := by
  decide +kernel

theorem context_12_27508_386788 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27508 ⟨386788, by decide⟩ :=
  accepted_of_selected 12 27508 ⟨386788, by decide⟩ ⟨12, 2, 0, 386788, 27508, 2969, 65536⟩
    (by decide) selected_cut_15040

theorem selected_cut_15041 : selected 9 ⟨299350, by decide⟩
    (prefixPartial 12 27509) = some ⟨12, 1, 0, 299350, 27509, 1, 65536⟩ := by
  decide +kernel

theorem context_12_27509_299350 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27509 ⟨299350, by decide⟩ :=
  accepted_of_selected 12 27509 ⟨299350, by decide⟩ ⟨12, 1, 0, 299350, 27509, 1, 65536⟩
    (by decide) selected_cut_15041

theorem selected_cut_15042 : selected 9 ⟨386830, by decide⟩
    (prefixPartial 12 27510) = some ⟨12, 2, 0, 386830, 27510, 3313, 65536⟩ := by
  decide +kernel

theorem context_12_27510_386830 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27510 ⟨386830, by decide⟩ :=
  accepted_of_selected 12 27510 ⟨386830, by decide⟩ ⟨12, 2, 0, 386830, 27510, 3313, 65536⟩
    (by decide) selected_cut_15042

theorem selected_cut_15043 : selected 9 ⟨386862, by decide⟩
    (prefixPartial 12 27511) = some ⟨12, 2, 0, 386862, 27511, 3201, 65536⟩ := by
  decide +kernel

theorem context_12_27511_386862 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27511 ⟨386862, by decide⟩ :=
  accepted_of_selected 12 27511 ⟨386862, by decide⟩ ⟨12, 2, 0, 386862, 27511, 3201, 65536⟩
    (by decide) selected_cut_15043

theorem unmarked_context_11_6877_386863 : frontier 10 ⟨386863, by decide⟩
    (prefixCache 11 6877) (prefixPartial 11 6877) = false := by
  decide +kernel

theorem node_context_11_6877_386863 : EJMOriginalGlobalDAGData.nodes 10 ⟨386863, by decide⟩ =
    .split (coordinate 11) (![⟨386788, by decide⟩,⟨299350, by decide⟩,⟨386830, by decide⟩,⟨386862, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6877_386863 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6877 ⟨386863, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6877
    ⟨386863, by decide⟩ (by decide) (![⟨386788, by decide⟩,⟨299350, by decide⟩,⟨386830, by decide⟩,⟨386862, by decide⟩]) unmarked_context_11_6877_386863 node_context_11_6877_386863
  intro a
  fin_cases a
  · exact context_12_27508_386788
  · exact context_12_27509_299350
  · exact context_12_27510_386830
  · exact context_12_27511_386862

theorem selected_cut_15044 : selected 9 ⟨386906, by decide⟩
    (prefixPartial 12 27512) = some ⟨12, 2, 0, 386906, 27512, 3101, 65536⟩ := by
  decide +kernel

theorem context_12_27512_386906 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27512 ⟨386906, by decide⟩ :=
  accepted_of_selected 12 27512 ⟨386906, by decide⟩ ⟨12, 2, 0, 386906, 27512, 3101, 65536⟩
    (by decide) selected_cut_15044

theorem selected_cut_15045 : selected 9 ⟨386996, by decide⟩
    (prefixPartial 12 27513) = some ⟨12, 2, 0, 386996, 27513, 4073, 65536⟩ := by
  decide +kernel

theorem context_12_27513_386996 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27513 ⟨386996, by decide⟩ :=
  accepted_of_selected 12 27513 ⟨386996, by decide⟩ ⟨12, 2, 0, 386996, 27513, 4073, 65536⟩
    (by decide) selected_cut_15045

theorem selected_cut_15046 : selected 9 ⟨387036, by decide⟩
    (prefixPartial 12 27514) = some ⟨12, 2, 0, 387036, 27514, 3181, 65536⟩ := by
  decide +kernel

theorem context_12_27514_387036 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27514 ⟨387036, by decide⟩ :=
  accepted_of_selected 12 27514 ⟨387036, by decide⟩ ⟨12, 2, 0, 387036, 27514, 3181, 65536⟩
    (by decide) selected_cut_15046

theorem selected_cut_15047 : selected 9 ⟨387072, by decide⟩
    (prefixPartial 12 27515) = some ⟨12, 2, 0, 387072, 27515, 2929, 65536⟩ := by
  decide +kernel

theorem context_12_27515_387072 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27515 ⟨387072, by decide⟩ :=
  accepted_of_selected 12 27515 ⟨387072, by decide⟩ ⟨12, 2, 0, 387072, 27515, 2929, 65536⟩
    (by decide) selected_cut_15047

theorem unmarked_context_11_6878_387073 : frontier 10 ⟨387073, by decide⟩
    (prefixCache 11 6878) (prefixPartial 11 6878) = false := by
  decide +kernel

theorem node_context_11_6878_387073 : EJMOriginalGlobalDAGData.nodes 10 ⟨387073, by decide⟩ =
    .split (coordinate 11) (![⟨386906, by decide⟩,⟨386996, by decide⟩,⟨387036, by decide⟩,⟨387072, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6878_387073 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6878 ⟨387073, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6878
    ⟨387073, by decide⟩ (by decide) (![⟨386906, by decide⟩,⟨386996, by decide⟩,⟨387036, by decide⟩,⟨387072, by decide⟩]) unmarked_context_11_6878_387073 node_context_11_6878_387073
  intro a
  fin_cases a
  · exact context_12_27512_386906
  · exact context_12_27513_386996
  · exact context_12_27514_387036
  · exact context_12_27515_387072

theorem selected_cut_15048 : selected 9 ⟨387099, by decide⟩
    (prefixPartial 12 27516) = some ⟨12, 2, 0, 387099, 27516, 2373, 65536⟩ := by
  decide +kernel

theorem context_12_27516_387099 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27516 ⟨387099, by decide⟩ :=
  accepted_of_selected 12 27516 ⟨387099, by decide⟩ ⟨12, 2, 0, 387099, 27516, 2373, 65536⟩
    (by decide) selected_cut_15048

theorem selected_cut_15049 : selected 9 ⟨387151, by decide⟩
    (prefixPartial 12 27517) = some ⟨12, 2, 0, 387151, 27517, 3273, 65536⟩ := by
  decide +kernel

theorem context_12_27517_387151 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27517 ⟨387151, by decide⟩ :=
  accepted_of_selected 12 27517 ⟨387151, by decide⟩ ⟨12, 2, 0, 387151, 27517, 3273, 65536⟩
    (by decide) selected_cut_15049

theorem selected_cut_15050 : selected 9 ⟨387183, by decide⟩
    (prefixPartial 12 27518) = some ⟨12, 2, 0, 387183, 27518, 2437, 65536⟩ := by
  decide +kernel

theorem context_12_27518_387183 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27518 ⟨387183, by decide⟩ :=
  accepted_of_selected 12 27518 ⟨387183, by decide⟩ ⟨12, 2, 0, 387183, 27518, 2437, 65536⟩
    (by decide) selected_cut_15050

theorem selected_cut_15051 : selected 9 ⟨387261, by decide⟩
    (prefixPartial 12 27519) = some ⟨12, 2, 0, 387261, 27519, 1297, 65536⟩ := by
  decide +kernel

theorem context_12_27519_387261 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27519 ⟨387261, by decide⟩ :=
  accepted_of_selected 12 27519 ⟨387261, by decide⟩ ⟨12, 2, 0, 387261, 27519, 1297, 65536⟩
    (by decide) selected_cut_15051

theorem unmarked_context_11_6879_387262 : frontier 10 ⟨387262, by decide⟩
    (prefixCache 11 6879) (prefixPartial 11 6879) = false := by
  decide +kernel

theorem node_context_11_6879_387262 : EJMOriginalGlobalDAGData.nodes 10 ⟨387262, by decide⟩ =
    .split (coordinate 11) (![⟨387099, by decide⟩,⟨387151, by decide⟩,⟨387183, by decide⟩,⟨387261, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6879_387262 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6879 ⟨387262, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6879
    ⟨387262, by decide⟩ (by decide) (![⟨387099, by decide⟩,⟨387151, by decide⟩,⟨387183, by decide⟩,⟨387261, by decide⟩]) unmarked_context_11_6879_387262 node_context_11_6879_387262
  intro a
  fin_cases a
  · exact context_12_27516_387099
  · exact context_12_27517_387151
  · exact context_12_27518_387183
  · exact context_12_27519_387261

theorem unmarked_context_10_1719_387263 : frontier 11 ⟨387263, by decide⟩
    (prefixCache 10 1719) (prefixPartial 10 1719) = false := by
  decide +kernel

theorem node_context_10_1719_387263 : EJMOriginalGlobalDAGData.nodes 11 ⟨387263, by decide⟩ =
    .split (coordinate 10) (![⟨386753, by decide⟩,⟨386863, by decide⟩,⟨387073, by decide⟩,⟨387262, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1719_387263 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1719 ⟨387263, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1719
    ⟨387263, by decide⟩ (by decide) (![⟨386753, by decide⟩,⟨386863, by decide⟩,⟨387073, by decide⟩,⟨387262, by decide⟩]) unmarked_context_10_1719_387263 node_context_10_1719_387263
  intro a
  fin_cases a
  · exact context_11_6876_386753
  · exact context_11_6877_386863
  · exact context_11_6878_387073
  · exact context_11_6879_387262

theorem unmarked_context_9_429_387264 : frontier 12 ⟨387264, by decide⟩
    (prefixCache 9 429) (prefixPartial 9 429) = false := by
  decide +kernel

theorem node_context_9_429_387264 : EJMOriginalGlobalDAGData.nodes 12 ⟨387264, by decide⟩ =
    .split (coordinate 9) (![⟨384609, by decide⟩,⟨385378, by decide⟩,⟨386510, by decide⟩,⟨387263, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_429_387264 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 429 ⟨387264, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 429
    ⟨387264, by decide⟩ (by decide) (![⟨384609, by decide⟩,⟨385378, by decide⟩,⟨386510, by decide⟩,⟨387263, by decide⟩]) unmarked_context_9_429_387264 node_context_9_429_387264
  intro a
  fin_cases a
  · exact context_10_1716_384609
  · exact context_10_1717_385378
  · exact context_10_1718_386510
  · exact context_10_1719_387263

theorem selected_cut_15052 : selected 9 ⟨387289, by decide⟩
    (prefixPartial 12 27520) = some ⟨12, 2, 0, 387289, 27520, 2601, 65536⟩ := by
  decide +kernel

theorem context_12_27520_387289 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27520 ⟨387289, by decide⟩ :=
  accepted_of_selected 12 27520 ⟨387289, by decide⟩ ⟨12, 2, 0, 387289, 27520, 2601, 65536⟩
    (by decide) selected_cut_15052

theorem selected_cut_15053 : selected 9 ⟨387318, by decide⟩
    (prefixPartial 12 27521) = some ⟨12, 2, 0, 387318, 27521, 2349, 65536⟩ := by
  decide +kernel

theorem context_12_27521_387318 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27521 ⟨387318, by decide⟩ :=
  accepted_of_selected 12 27521 ⟨387318, by decide⟩ ⟨12, 2, 0, 387318, 27521, 2349, 65536⟩
    (by decide) selected_cut_15053

theorem selected_cut_15054 : selected 9 ⟨387347, by decide⟩
    (prefixPartial 12 27522) = some ⟨12, 2, 0, 387347, 27522, 2417, 65536⟩ := by
  decide +kernel

theorem context_12_27522_387347 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27522 ⟨387347, by decide⟩ :=
  accepted_of_selected 12 27522 ⟨387347, by decide⟩ ⟨12, 2, 0, 387347, 27522, 2417, 65536⟩
    (by decide) selected_cut_15054

theorem selected_cut_15055 : selected 9 ⟨387371, by decide⟩
    (prefixPartial 12 27523) = some ⟨12, 2, 0, 387371, 27523, 2209, 65536⟩ := by
  decide +kernel

theorem context_12_27523_387371 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27523 ⟨387371, by decide⟩ :=
  accepted_of_selected 12 27523 ⟨387371, by decide⟩ ⟨12, 2, 0, 387371, 27523, 2209, 65536⟩
    (by decide) selected_cut_15055

theorem unmarked_context_11_6880_387372 : frontier 10 ⟨387372, by decide⟩
    (prefixCache 11 6880) (prefixPartial 11 6880) = false := by
  decide +kernel

theorem node_context_11_6880_387372 : EJMOriginalGlobalDAGData.nodes 10 ⟨387372, by decide⟩ =
    .split (coordinate 11) (![⟨387289, by decide⟩,⟨387318, by decide⟩,⟨387347, by decide⟩,⟨387371, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6880_387372 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6880 ⟨387372, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6880
    ⟨387372, by decide⟩ (by decide) (![⟨387289, by decide⟩,⟨387318, by decide⟩,⟨387347, by decide⟩,⟨387371, by decide⟩]) unmarked_context_11_6880_387372 node_context_11_6880_387372
  intro a
  fin_cases a
  · exact context_12_27520_387289
  · exact context_12_27521_387318
  · exact context_12_27522_387347
  · exact context_12_27523_387371

theorem selected_cut_15056 : selected 9 ⟨387399, by decide⟩
    (prefixPartial 12 27524) = some ⟨12, 2, 0, 387399, 27524, 2809, 65536⟩ := by
  decide +kernel

theorem context_12_27524_387399 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27524 ⟨387399, by decide⟩ :=
  accepted_of_selected 12 27524 ⟨387399, by decide⟩ ⟨12, 2, 0, 387399, 27524, 2809, 65536⟩
    (by decide) selected_cut_15056

theorem selected_cut_15057 : selected 9 ⟨387428, by decide⟩
    (prefixPartial 12 27525) = some ⟨12, 2, 0, 387428, 27525, 2473, 65536⟩ := by
  decide +kernel

theorem context_12_27525_387428 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27525 ⟨387428, by decide⟩ :=
  accepted_of_selected 12 27525 ⟨387428, by decide⟩ ⟨12, 2, 0, 387428, 27525, 2473, 65536⟩
    (by decide) selected_cut_15057

theorem selected_cut_15058 : selected 9 ⟨387455, by decide⟩
    (prefixPartial 12 27526) = some ⟨12, 2, 0, 387455, 27526, 2753, 65536⟩ := by
  decide +kernel

theorem context_12_27526_387455 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27526 ⟨387455, by decide⟩ :=
  accepted_of_selected 12 27526 ⟨387455, by decide⟩ ⟨12, 2, 0, 387455, 27526, 2753, 65536⟩
    (by decide) selected_cut_15058

theorem selected_cut_15059 : selected 9 ⟨387479, by decide⟩
    (prefixPartial 12 27527) = some ⟨12, 2, 0, 387479, 27527, 2549, 65536⟩ := by
  decide +kernel

theorem context_12_27527_387479 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27527 ⟨387479, by decide⟩ :=
  accepted_of_selected 12 27527 ⟨387479, by decide⟩ ⟨12, 2, 0, 387479, 27527, 2549, 65536⟩
    (by decide) selected_cut_15059

theorem unmarked_context_11_6881_387480 : frontier 10 ⟨387480, by decide⟩
    (prefixCache 11 6881) (prefixPartial 11 6881) = false := by
  decide +kernel

theorem node_context_11_6881_387480 : EJMOriginalGlobalDAGData.nodes 10 ⟨387480, by decide⟩ =
    .split (coordinate 11) (![⟨387399, by decide⟩,⟨387428, by decide⟩,⟨387455, by decide⟩,⟨387479, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6881_387480 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6881 ⟨387480, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6881
    ⟨387480, by decide⟩ (by decide) (![⟨387399, by decide⟩,⟨387428, by decide⟩,⟨387455, by decide⟩,⟨387479, by decide⟩]) unmarked_context_11_6881_387480 node_context_11_6881_387480
  intro a
  fin_cases a
  · exact context_12_27524_387399
  · exact context_12_27525_387428
  · exact context_12_27526_387455
  · exact context_12_27527_387479

theorem selected_cut_15060 : selected 9 ⟨387509, by decide⟩
    (prefixPartial 12 27528) = some ⟨12, 2, 0, 387509, 27528, 2669, 65536⟩ := by
  decide +kernel

theorem context_12_27528_387509 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27528 ⟨387509, by decide⟩ :=
  accepted_of_selected 12 27528 ⟨387509, by decide⟩ ⟨12, 2, 0, 387509, 27528, 2669, 65536⟩
    (by decide) selected_cut_15060

theorem selected_cut_15061 : selected 9 ⟨387537, by decide⟩
    (prefixPartial 12 27529) = some ⟨12, 2, 0, 387537, 27529, 2433, 65536⟩ := by
  decide +kernel

theorem context_12_27529_387537 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27529 ⟨387537, by decide⟩ :=
  accepted_of_selected 12 27529 ⟨387537, by decide⟩ ⟨12, 2, 0, 387537, 27529, 2433, 65536⟩
    (by decide) selected_cut_15061

theorem selected_cut_15062 : selected 9 ⟨387567, by decide⟩
    (prefixPartial 12 27530) = some ⟨12, 2, 0, 387567, 27530, 2377, 65536⟩ := by
  decide +kernel

theorem context_12_27530_387567 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27530 ⟨387567, by decide⟩ :=
  accepted_of_selected 12 27530 ⟨387567, by decide⟩ ⟨12, 2, 0, 387567, 27530, 2377, 65536⟩
    (by decide) selected_cut_15062

theorem selected_cut_15063 : selected 9 ⟨387593, by decide⟩
    (prefixPartial 12 27531) = some ⟨12, 2, 0, 387593, 27531, 2021, 65536⟩ := by
  decide +kernel

theorem context_12_27531_387593 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27531 ⟨387593, by decide⟩ :=
  accepted_of_selected 12 27531 ⟨387593, by decide⟩ ⟨12, 2, 0, 387593, 27531, 2021, 65536⟩
    (by decide) selected_cut_15063

theorem unmarked_context_11_6882_387594 : frontier 10 ⟨387594, by decide⟩
    (prefixCache 11 6882) (prefixPartial 11 6882) = false := by
  decide +kernel

theorem node_context_11_6882_387594 : EJMOriginalGlobalDAGData.nodes 10 ⟨387594, by decide⟩ =
    .split (coordinate 11) (![⟨387509, by decide⟩,⟨387537, by decide⟩,⟨387567, by decide⟩,⟨387593, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6882_387594 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6882 ⟨387594, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6882
    ⟨387594, by decide⟩ (by decide) (![⟨387509, by decide⟩,⟨387537, by decide⟩,⟨387567, by decide⟩,⟨387593, by decide⟩]) unmarked_context_11_6882_387594 node_context_11_6882_387594
  intro a
  fin_cases a
  · exact context_12_27528_387509
  · exact context_12_27529_387537
  · exact context_12_27530_387567
  · exact context_12_27531_387593

theorem selected_cut_15064 : selected 9 ⟨387619, by decide⟩
    (prefixPartial 12 27532) = some ⟨12, 2, 0, 387619, 27532, 2293, 65536⟩ := by
  decide +kernel

theorem context_12_27532_387619 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27532 ⟨387619, by decide⟩ :=
  accepted_of_selected 12 27532 ⟨387619, by decide⟩ ⟨12, 2, 0, 387619, 27532, 2293, 65536⟩
    (by decide) selected_cut_15064

theorem selected_cut_15065 : selected 9 ⟨387644, by decide⟩
    (prefixPartial 12 27533) = some ⟨12, 2, 0, 387644, 27533, 2113, 65536⟩ := by
  decide +kernel

theorem context_12_27533_387644 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27533 ⟨387644, by decide⟩ :=
  accepted_of_selected 12 27533 ⟨387644, by decide⟩ ⟨12, 2, 0, 387644, 27533, 2113, 65536⟩
    (by decide) selected_cut_15065

theorem selected_cut_15066 : selected 9 ⟨387667, by decide⟩
    (prefixPartial 12 27534) = some ⟨12, 2, 0, 387667, 27534, 2101, 65536⟩ := by
  decide +kernel

theorem context_12_27534_387667 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27534 ⟨387667, by decide⟩ :=
  accepted_of_selected 12 27534 ⟨387667, by decide⟩ ⟨12, 2, 0, 387667, 27534, 2101, 65536⟩
    (by decide) selected_cut_15066

theorem selected_cut_15067 : selected 9 ⟨387720, by decide⟩
    (prefixPartial 12 27535) = some ⟨12, 2, 0, 387720, 27535, 2913, 65536⟩ := by
  decide +kernel

theorem context_12_27535_387720 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27535 ⟨387720, by decide⟩ :=
  accepted_of_selected 12 27535 ⟨387720, by decide⟩ ⟨12, 2, 0, 387720, 27535, 2913, 65536⟩
    (by decide) selected_cut_15067

theorem unmarked_context_11_6883_387721 : frontier 10 ⟨387721, by decide⟩
    (prefixCache 11 6883) (prefixPartial 11 6883) = false := by
  decide +kernel

theorem node_context_11_6883_387721 : EJMOriginalGlobalDAGData.nodes 10 ⟨387721, by decide⟩ =
    .split (coordinate 11) (![⟨387619, by decide⟩,⟨387644, by decide⟩,⟨387667, by decide⟩,⟨387720, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6883_387721 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6883 ⟨387721, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6883
    ⟨387721, by decide⟩ (by decide) (![⟨387619, by decide⟩,⟨387644, by decide⟩,⟨387667, by decide⟩,⟨387720, by decide⟩]) unmarked_context_11_6883_387721 node_context_11_6883_387721
  intro a
  fin_cases a
  · exact context_12_27532_387619
  · exact context_12_27533_387644
  · exact context_12_27534_387667
  · exact context_12_27535_387720

theorem unmarked_context_10_1720_387722 : frontier 11 ⟨387722, by decide⟩
    (prefixCache 10 1720) (prefixPartial 10 1720) = false := by
  decide +kernel

theorem node_context_10_1720_387722 : EJMOriginalGlobalDAGData.nodes 11 ⟨387722, by decide⟩ =
    .split (coordinate 10) (![⟨387372, by decide⟩,⟨387480, by decide⟩,⟨387594, by decide⟩,⟨387721, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1720_387722 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1720 ⟨387722, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1720
    ⟨387722, by decide⟩ (by decide) (![⟨387372, by decide⟩,⟨387480, by decide⟩,⟨387594, by decide⟩,⟨387721, by decide⟩]) unmarked_context_10_1720_387722 node_context_10_1720_387722
  intro a
  fin_cases a
  · exact context_11_6880_387372
  · exact context_11_6881_387480
  · exact context_11_6882_387594
  · exact context_11_6883_387721

theorem selected_cut_15068 : selected 9 ⟨387743, by decide⟩
    (prefixPartial 12 27536) = some ⟨12, 2, 0, 387743, 27536, 2129, 65536⟩ := by
  decide +kernel

theorem context_12_27536_387743 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27536 ⟨387743, by decide⟩ :=
  accepted_of_selected 12 27536 ⟨387743, by decide⟩ ⟨12, 2, 0, 387743, 27536, 2129, 65536⟩
    (by decide) selected_cut_15068

theorem selected_cut_15069 : selected 9 ⟨387764, by decide⟩
    (prefixPartial 12 27537) = some ⟨12, 2, 0, 387764, 27537, 2125, 65536⟩ := by
  decide +kernel

theorem context_12_27537_387764 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27537 ⟨387764, by decide⟩ :=
  accepted_of_selected 12 27537 ⟨387764, by decide⟩ ⟨12, 2, 0, 387764, 27537, 2125, 65536⟩
    (by decide) selected_cut_15069

theorem selected_cut_15070 : selected 9 ⟨387790, by decide⟩
    (prefixPartial 12 27538) = some ⟨12, 2, 0, 387790, 27538, 2173, 65536⟩ := by
  decide +kernel

theorem context_12_27538_387790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27538 ⟨387790, by decide⟩ :=
  accepted_of_selected 12 27538 ⟨387790, by decide⟩ ⟨12, 2, 0, 387790, 27538, 2173, 65536⟩
    (by decide) selected_cut_15070

theorem selected_cut_15071 : selected 9 ⟨387812, by decide⟩
    (prefixPartial 12 27539) = some ⟨12, 2, 0, 387812, 27539, 1941, 65536⟩ := by
  decide +kernel

theorem context_12_27539_387812 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27539 ⟨387812, by decide⟩ :=
  accepted_of_selected 12 27539 ⟨387812, by decide⟩ ⟨12, 2, 0, 387812, 27539, 1941, 65536⟩
    (by decide) selected_cut_15071

theorem unmarked_context_11_6884_387813 : frontier 10 ⟨387813, by decide⟩
    (prefixCache 11 6884) (prefixPartial 11 6884) = false := by
  decide +kernel

theorem node_context_11_6884_387813 : EJMOriginalGlobalDAGData.nodes 10 ⟨387813, by decide⟩ =
    .split (coordinate 11) (![⟨387743, by decide⟩,⟨387764, by decide⟩,⟨387790, by decide⟩,⟨387812, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6884_387813 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6884 ⟨387813, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6884
    ⟨387813, by decide⟩ (by decide) (![⟨387743, by decide⟩,⟨387764, by decide⟩,⟨387790, by decide⟩,⟨387812, by decide⟩]) unmarked_context_11_6884_387813 node_context_11_6884_387813
  intro a
  fin_cases a
  · exact context_12_27536_387743
  · exact context_12_27537_387764
  · exact context_12_27538_387790
  · exact context_12_27539_387812

theorem selected_cut_15072 : selected 9 ⟨387835, by decide⟩
    (prefixPartial 12 27540) = some ⟨12, 2, 0, 387835, 27540, 2177, 65536⟩ := by
  decide +kernel

theorem context_12_27540_387835 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27540 ⟨387835, by decide⟩ :=
  accepted_of_selected 12 27540 ⟨387835, by decide⟩ ⟨12, 2, 0, 387835, 27540, 2177, 65536⟩
    (by decide) selected_cut_15072

theorem selected_cut_15073 : selected 9 ⟨387854, by decide⟩
    (prefixPartial 12 27541) = some ⟨12, 2, 0, 387854, 27541, 2085, 65536⟩ := by
  decide +kernel

theorem context_12_27541_387854 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27541 ⟨387854, by decide⟩ :=
  accepted_of_selected 12 27541 ⟨387854, by decide⟩ ⟨12, 2, 0, 387854, 27541, 2085, 65536⟩
    (by decide) selected_cut_15073

theorem selected_cut_15074 : selected 9 ⟨387881, by decide⟩
    (prefixPartial 12 27542) = some ⟨12, 2, 0, 387881, 27542, 2333, 65536⟩ := by
  decide +kernel

theorem context_12_27542_387881 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27542 ⟨387881, by decide⟩ :=
  accepted_of_selected 12 27542 ⟨387881, by decide⟩ ⟨12, 2, 0, 387881, 27542, 2333, 65536⟩
    (by decide) selected_cut_15074

theorem selected_cut_15075 : selected 9 ⟨387901, by decide⟩
    (prefixPartial 12 27543) = some ⟨12, 2, 0, 387901, 27543, 2053, 65536⟩ := by
  decide +kernel

theorem context_12_27543_387901 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27543 ⟨387901, by decide⟩ :=
  accepted_of_selected 12 27543 ⟨387901, by decide⟩ ⟨12, 2, 0, 387901, 27543, 2053, 65536⟩
    (by decide) selected_cut_15075

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
