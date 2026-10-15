/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover037
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_03651 : selected 9 ⟨113637, by decide⟩
    (prefixPartial 12 7050) = some ⟨12, 2, 0, 113637, 7050, 2693, 65536⟩ := by
  decide +kernel

theorem context_12_7050_113637 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 7050 ⟨113637, by decide⟩ :=
  accepted_of_selected 12 7050 ⟨113637, by decide⟩ ⟨12, 2, 0, 113637, 7050, 2693, 65536⟩
    (by decide) selected_cut_03651

theorem selected_cut_03652 : selected 9 ⟨113685, by decide⟩
    (prefixPartial 12 7051) = some ⟨12, 2, 0, 113685, 7051, 2697, 65536⟩ := by
  decide +kernel

theorem context_12_7051_113685 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 7051 ⟨113685, by decide⟩ :=
  accepted_of_selected 12 7051 ⟨113685, by decide⟩ ⟨12, 2, 0, 113685, 7051, 2697, 65536⟩
    (by decide) selected_cut_03652

theorem unmarked_context_11_1762_113686 : frontier 10 ⟨113686, by decide⟩
    (prefixCache 11 1762) (prefixPartial 11 1762) = false := by
  decide +kernel

theorem node_context_11_1762_113686 : EJMOriginalGlobalDAGData.nodes 10 ⟨113686, by decide⟩ =
    .split (coordinate 11) (![⟨113535, by decide⟩,⟨113590, by decide⟩,⟨113637, by decide⟩,⟨113685, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1762_113686 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1762 ⟨113686, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1762
    ⟨113686, by decide⟩ (by decide) (![⟨113535, by decide⟩,⟨113590, by decide⟩,⟨113637, by decide⟩,⟨113685, by decide⟩]) unmarked_context_11_1762_113686 node_context_11_1762_113686
  intro a
  fin_cases a
  · exact context_12_7048_113535
  · exact context_12_7049_113590
  · exact context_12_7050_113637
  · exact context_12_7051_113685

theorem selected_cut_03653 : selected 9 ⟨113733, by decide⟩
    (prefixPartial 12 7052) = some ⟨12, 2, 0, 113733, 7052, 2561, 65536⟩ := by
  decide +kernel

theorem context_12_7052_113733 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 7052 ⟨113733, by decide⟩ :=
  accepted_of_selected 12 7052 ⟨113733, by decide⟩ ⟨12, 2, 0, 113733, 7052, 2561, 65536⟩
    (by decide) selected_cut_03653

theorem selected_cut_03654 : selected 9 ⟨113808, by decide⟩
    (prefixPartial 12 7053) = some ⟨12, 2, 0, 113808, 7053, 3197, 65536⟩ := by
  decide +kernel

theorem context_12_7053_113808 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 7053 ⟨113808, by decide⟩ :=
  accepted_of_selected 12 7053 ⟨113808, by decide⟩ ⟨12, 2, 0, 113808, 7053, 3197, 65536⟩
    (by decide) selected_cut_03654

theorem selected_cut_03655 : selected 9 ⟨113870, by decide⟩
    (prefixPartial 12 7054) = some ⟨12, 2, 0, 113870, 7054, 2761, 65536⟩ := by
  decide +kernel

theorem context_12_7054_113870 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 7054 ⟨113870, by decide⟩ :=
  accepted_of_selected 12 7054 ⟨113870, by decide⟩ ⟨12, 2, 0, 113870, 7054, 2761, 65536⟩
    (by decide) selected_cut_03655

theorem selected_cut_03656 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 28220) = some ⟨13, 1, 0, 3444, 28220, 1, 16384⟩ := by
  decide +kernel

theorem context_13_28220_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 28220 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 28220 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 28220, 1, 16384⟩
    (by decide) selected_cut_03656

theorem selected_cut_03657 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 28221) = some ⟨13, 1, 0, 3444, 28221, 1, 16384⟩ := by
  decide +kernel

theorem context_13_28221_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 28221 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 28221 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 28221, 1, 16384⟩
    (by decide) selected_cut_03657

theorem selected_cut_03658 : selected 8 ⟨113952, by decide⟩
    (prefixPartial 13 28222) = some ⟨13, 2, 0, 113952, 28222, 3073, 16384⟩ := by
  decide +kernel

theorem context_13_28222_113952 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 28222 ⟨113952, by decide⟩ :=
  accepted_of_selected 13 28222 ⟨113952, by decide⟩ ⟨13, 2, 0, 113952, 28222, 3073, 16384⟩
    (by decide) selected_cut_03658

theorem selected_cut_03659 : selected 8 ⟨114023, by decide⟩
    (prefixPartial 13 28223) = some ⟨13, 2, 0, 114023, 28223, 1261, 16384⟩ := by
  decide +kernel

theorem context_13_28223_114023 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 28223 ⟨114023, by decide⟩ :=
  accepted_of_selected 13 28223 ⟨114023, by decide⟩ ⟨13, 2, 0, 114023, 28223, 1261, 16384⟩
    (by decide) selected_cut_03659

theorem unmarked_context_12_7055_114024 : frontier 9 ⟨114024, by decide⟩
    (prefixCache 12 7055) (prefixPartial 12 7055) = false := by
  decide +kernel

theorem node_context_12_7055_114024 : EJMOriginalGlobalDAGData.nodes 9 ⟨114024, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨3444, by decide⟩,⟨113952, by decide⟩,⟨114023, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_7055_114024 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 7055 ⟨114024, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 7055
    ⟨114024, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨3444, by decide⟩,⟨113952, by decide⟩,⟨114023, by decide⟩]) unmarked_context_12_7055_114024 node_context_12_7055_114024
  intro a
  fin_cases a
  · exact context_13_28220_3444
  · exact context_13_28221_3444
  · exact context_13_28222_113952
  · exact context_13_28223_114023

theorem unmarked_context_11_1763_114025 : frontier 10 ⟨114025, by decide⟩
    (prefixCache 11 1763) (prefixPartial 11 1763) = false := by
  decide +kernel

theorem node_context_11_1763_114025 : EJMOriginalGlobalDAGData.nodes 10 ⟨114025, by decide⟩ =
    .split (coordinate 11) (![⟨113733, by decide⟩,⟨113808, by decide⟩,⟨113870, by decide⟩,⟨114024, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1763_114025 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1763 ⟨114025, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1763
    ⟨114025, by decide⟩ (by decide) (![⟨113733, by decide⟩,⟨113808, by decide⟩,⟨113870, by decide⟩,⟨114024, by decide⟩]) unmarked_context_11_1763_114025 node_context_11_1763_114025
  intro a
  fin_cases a
  · exact context_12_7052_113733
  · exact context_12_7053_113808
  · exact context_12_7054_113870
  · exact context_12_7055_114024

theorem unmarked_context_10_440_114026 : frontier 11 ⟨114026, by decide⟩
    (prefixCache 10 440) (prefixPartial 10 440) = false := by
  decide +kernel

theorem node_context_10_440_114026 : EJMOriginalGlobalDAGData.nodes 11 ⟨114026, by decide⟩ =
    .split (coordinate 10) (![⟨113277, by decide⟩,⟨113504, by decide⟩,⟨113686, by decide⟩,⟨114025, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_440_114026 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 440 ⟨114026, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 440
    ⟨114026, by decide⟩ (by decide) (![⟨113277, by decide⟩,⟨113504, by decide⟩,⟨113686, by decide⟩,⟨114025, by decide⟩]) unmarked_context_10_440_114026 node_context_10_440_114026
  intro a
  fin_cases a
  · exact context_11_1760_113277
  · exact context_11_1761_113504
  · exact context_11_1762_113686
  · exact context_11_1763_114025

theorem selected_cut_03660 : selected 9 ⟨114077, by decide⟩
    (prefixPartial 12 7056) = some ⟨12, 2, 0, 114077, 7056, 2293, 65536⟩ := by
  decide +kernel

theorem context_12_7056_114077 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 7056 ⟨114077, by decide⟩ :=
  accepted_of_selected 12 7056 ⟨114077, by decide⟩ ⟨12, 2, 0, 114077, 7056, 2293, 65536⟩
    (by decide) selected_cut_03660

theorem selected_cut_03661 : selected 9 ⟨114151, by decide⟩
    (prefixPartial 12 7057) = some ⟨12, 2, 0, 114151, 7057, 2781, 65536⟩ := by
  decide +kernel

theorem context_12_7057_114151 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 7057 ⟨114151, by decide⟩ :=
  accepted_of_selected 12 7057 ⟨114151, by decide⟩ ⟨12, 2, 0, 114151, 7057, 2781, 65536⟩
    (by decide) selected_cut_03661

theorem selected_cut_03662 : selected 9 ⟨114204, by decide⟩
    (prefixPartial 12 7058) = some ⟨12, 2, 0, 114204, 7058, 2693, 65536⟩ := by
  decide +kernel

theorem context_12_7058_114204 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 7058 ⟨114204, by decide⟩ :=
  accepted_of_selected 12 7058 ⟨114204, by decide⟩ ⟨12, 2, 0, 114204, 7058, 2693, 65536⟩
    (by decide) selected_cut_03662

theorem selected_cut_03663 : selected 9 ⟨114243, by decide⟩
    (prefixPartial 12 7059) = some ⟨12, 2, 0, 114243, 7059, 2473, 65536⟩ := by
  decide +kernel

theorem context_12_7059_114243 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 7059 ⟨114243, by decide⟩ :=
  accepted_of_selected 12 7059 ⟨114243, by decide⟩ ⟨12, 2, 0, 114243, 7059, 2473, 65536⟩
    (by decide) selected_cut_03663

theorem unmarked_context_11_1764_114244 : frontier 10 ⟨114244, by decide⟩
    (prefixCache 11 1764) (prefixPartial 11 1764) = false := by
  decide +kernel

theorem node_context_11_1764_114244 : EJMOriginalGlobalDAGData.nodes 10 ⟨114244, by decide⟩ =
    .split (coordinate 11) (![⟨114077, by decide⟩,⟨114151, by decide⟩,⟨114204, by decide⟩,⟨114243, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1764_114244 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1764 ⟨114244, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1764
    ⟨114244, by decide⟩ (by decide) (![⟨114077, by decide⟩,⟨114151, by decide⟩,⟨114204, by decide⟩,⟨114243, by decide⟩]) unmarked_context_11_1764_114244 node_context_11_1764_114244
  intro a
  fin_cases a
  · exact context_12_7056_114077
  · exact context_12_7057_114151
  · exact context_12_7058_114204
  · exact context_12_7059_114243

theorem selected_cut_03664 : selected 9 ⟨114295, by decide⟩
    (prefixPartial 12 7060) = some ⟨12, 2, 0, 114295, 7060, 2253, 65536⟩ := by
  decide +kernel

theorem context_12_7060_114295 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 7060 ⟨114295, by decide⟩ :=
  accepted_of_selected 12 7060 ⟨114295, by decide⟩ ⟨12, 2, 0, 114295, 7060, 2253, 65536⟩
    (by decide) selected_cut_03664

theorem selected_cut_03665 : selected 9 ⟨114361, by decide⟩
    (prefixPartial 12 7061) = some ⟨12, 2, 0, 114361, 7061, 2641, 65536⟩ := by
  decide +kernel

theorem context_12_7061_114361 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 7061 ⟨114361, by decide⟩ :=
  accepted_of_selected 12 7061 ⟨114361, by decide⟩ ⟨12, 2, 0, 114361, 7061, 2641, 65536⟩
    (by decide) selected_cut_03665

theorem selected_cut_03666 : selected 9 ⟨114428, by decide⟩
    (prefixPartial 12 7062) = some ⟨12, 2, 0, 114428, 7062, 2765, 65536⟩ := by
  decide +kernel

theorem context_12_7062_114428 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 7062 ⟨114428, by decide⟩ :=
  accepted_of_selected 12 7062 ⟨114428, by decide⟩ ⟨12, 2, 0, 114428, 7062, 2765, 65536⟩
    (by decide) selected_cut_03666

theorem selected_cut_03667 : selected 9 ⟨114477, by decide⟩
    (prefixPartial 12 7063) = some ⟨12, 2, 0, 114477, 7063, 2457, 65536⟩ := by
  decide +kernel

theorem context_12_7063_114477 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 7063 ⟨114477, by decide⟩ :=
  accepted_of_selected 12 7063 ⟨114477, by decide⟩ ⟨12, 2, 0, 114477, 7063, 2457, 65536⟩
    (by decide) selected_cut_03667

theorem unmarked_context_11_1765_114478 : frontier 10 ⟨114478, by decide⟩
    (prefixCache 11 1765) (prefixPartial 11 1765) = false := by
  decide +kernel

theorem node_context_11_1765_114478 : EJMOriginalGlobalDAGData.nodes 10 ⟨114478, by decide⟩ =
    .split (coordinate 11) (![⟨114295, by decide⟩,⟨114361, by decide⟩,⟨114428, by decide⟩,⟨114477, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1765_114478 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1765 ⟨114478, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1765
    ⟨114478, by decide⟩ (by decide) (![⟨114295, by decide⟩,⟨114361, by decide⟩,⟨114428, by decide⟩,⟨114477, by decide⟩]) unmarked_context_11_1765_114478 node_context_11_1765_114478
  intro a
  fin_cases a
  · exact context_12_7060_114295
  · exact context_12_7061_114361
  · exact context_12_7062_114428
  · exact context_12_7063_114477

theorem selected_cut_03668 : selected 9 ⟨114516, by decide⟩
    (prefixPartial 12 7064) = some ⟨12, 2, 0, 114516, 7064, 2097, 65536⟩ := by
  decide +kernel

theorem context_12_7064_114516 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 7064 ⟨114516, by decide⟩ :=
  accepted_of_selected 12 7064 ⟨114516, by decide⟩ ⟨12, 2, 0, 114516, 7064, 2097, 65536⟩
    (by decide) selected_cut_03668

theorem selected_cut_03669 : selected 9 ⟨114594, by decide⟩
    (prefixPartial 12 7065) = some ⟨12, 2, 0, 114594, 7065, 2669, 65536⟩ := by
  decide +kernel

theorem context_12_7065_114594 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 7065 ⟨114594, by decide⟩ :=
  accepted_of_selected 12 7065 ⟨114594, by decide⟩ ⟨12, 2, 0, 114594, 7065, 2669, 65536⟩
    (by decide) selected_cut_03669

theorem selected_cut_03670 : selected 9 ⟨114673, by decide⟩
    (prefixPartial 12 7066) = some ⟨12, 2, 0, 114673, 7066, 2301, 65536⟩ := by
  decide +kernel

theorem context_12_7066_114673 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 7066 ⟨114673, by decide⟩ :=
  accepted_of_selected 12 7066 ⟨114673, by decide⟩ ⟨12, 2, 0, 114673, 7066, 2301, 65536⟩
    (by decide) selected_cut_03670

theorem selected_cut_03671 : selected 9 ⟨114725, by decide⟩
    (prefixPartial 12 7067) = some ⟨12, 2, 0, 114725, 7067, 2065, 65536⟩ := by
  decide +kernel

theorem context_12_7067_114725 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 7067 ⟨114725, by decide⟩ :=
  accepted_of_selected 12 7067 ⟨114725, by decide⟩ ⟨12, 2, 0, 114725, 7067, 2065, 65536⟩
    (by decide) selected_cut_03671

theorem unmarked_context_11_1766_114726 : frontier 10 ⟨114726, by decide⟩
    (prefixCache 11 1766) (prefixPartial 11 1766) = false := by
  decide +kernel

theorem node_context_11_1766_114726 : EJMOriginalGlobalDAGData.nodes 10 ⟨114726, by decide⟩ =
    .split (coordinate 11) (![⟨114516, by decide⟩,⟨114594, by decide⟩,⟨114673, by decide⟩,⟨114725, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1766_114726 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1766 ⟨114726, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1766
    ⟨114726, by decide⟩ (by decide) (![⟨114516, by decide⟩,⟨114594, by decide⟩,⟨114673, by decide⟩,⟨114725, by decide⟩]) unmarked_context_11_1766_114726 node_context_11_1766_114726
  intro a
  fin_cases a
  · exact context_12_7064_114516
  · exact context_12_7065_114594
  · exact context_12_7066_114673
  · exact context_12_7067_114725

theorem selected_cut_03672 : selected 9 ⟨114773, by decide⟩
    (prefixPartial 12 7068) = some ⟨12, 2, 0, 114773, 7068, 1857, 65536⟩ := by
  decide +kernel

theorem context_12_7068_114773 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 7068 ⟨114773, by decide⟩ :=
  accepted_of_selected 12 7068 ⟨114773, by decide⟩ ⟨12, 2, 0, 114773, 7068, 1857, 65536⟩
    (by decide) selected_cut_03672

theorem selected_cut_03673 : selected 9 ⟨114844, by decide⟩
    (prefixPartial 12 7069) = some ⟨12, 2, 0, 114844, 7069, 2317, 65536⟩ := by
  decide +kernel

theorem context_12_7069_114844 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 7069 ⟨114844, by decide⟩ :=
  accepted_of_selected 12 7069 ⟨114844, by decide⟩ ⟨12, 2, 0, 114844, 7069, 2317, 65536⟩
    (by decide) selected_cut_03673

theorem selected_cut_03674 : selected 9 ⟨114900, by decide⟩
    (prefixPartial 12 7070) = some ⟨12, 2, 0, 114900, 7070, 2089, 65536⟩ := by
  decide +kernel

theorem context_12_7070_114900 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 7070 ⟨114900, by decide⟩ :=
  accepted_of_selected 12 7070 ⟨114900, by decide⟩ ⟨12, 2, 0, 114900, 7070, 2089, 65536⟩
    (by decide) selected_cut_03674

theorem selected_cut_03675 : selected 9 ⟨115029, by decide⟩
    (prefixPartial 12 7071) = some ⟨12, 2, 0, 115029, 7071, 3169, 65536⟩ := by
  decide +kernel

theorem context_12_7071_115029 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 7071 ⟨115029, by decide⟩ :=
  accepted_of_selected 12 7071 ⟨115029, by decide⟩ ⟨12, 2, 0, 115029, 7071, 3169, 65536⟩
    (by decide) selected_cut_03675

theorem unmarked_context_11_1767_115030 : frontier 10 ⟨115030, by decide⟩
    (prefixCache 11 1767) (prefixPartial 11 1767) = false := by
  decide +kernel

theorem node_context_11_1767_115030 : EJMOriginalGlobalDAGData.nodes 10 ⟨115030, by decide⟩ =
    .split (coordinate 11) (![⟨114773, by decide⟩,⟨114844, by decide⟩,⟨114900, by decide⟩,⟨115029, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1767_115030 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1767 ⟨115030, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1767
    ⟨115030, by decide⟩ (by decide) (![⟨114773, by decide⟩,⟨114844, by decide⟩,⟨114900, by decide⟩,⟨115029, by decide⟩]) unmarked_context_11_1767_115030 node_context_11_1767_115030
  intro a
  fin_cases a
  · exact context_12_7068_114773
  · exact context_12_7069_114844
  · exact context_12_7070_114900
  · exact context_12_7071_115029

theorem unmarked_context_10_441_115031 : frontier 11 ⟨115031, by decide⟩
    (prefixCache 10 441) (prefixPartial 10 441) = false := by
  decide +kernel

theorem node_context_10_441_115031 : EJMOriginalGlobalDAGData.nodes 11 ⟨115031, by decide⟩ =
    .split (coordinate 10) (![⟨114244, by decide⟩,⟨114478, by decide⟩,⟨114726, by decide⟩,⟨115030, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_441_115031 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 441 ⟨115031, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 441
    ⟨115031, by decide⟩ (by decide) (![⟨114244, by decide⟩,⟨114478, by decide⟩,⟨114726, by decide⟩,⟨115030, by decide⟩]) unmarked_context_10_441_115031 node_context_10_441_115031
  intro a
  fin_cases a
  · exact context_11_1764_114244
  · exact context_11_1765_114478
  · exact context_11_1766_114726
  · exact context_11_1767_115030

theorem selected_cut_03676 : selected 9 ⟨115067, by decide⟩
    (prefixPartial 12 7072) = some ⟨12, 2, 0, 115067, 7072, 1405, 65536⟩ := by
  decide +kernel

theorem context_12_7072_115067 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 7072 ⟨115067, by decide⟩ :=
  accepted_of_selected 12 7072 ⟨115067, by decide⟩ ⟨12, 2, 0, 115067, 7072, 1405, 65536⟩
    (by decide) selected_cut_03676

theorem selected_cut_03677 : selected 9 ⟨115121, by decide⟩
    (prefixPartial 12 7073) = some ⟨12, 2, 0, 115121, 7073, 1645, 65536⟩ := by
  decide +kernel

theorem context_12_7073_115121 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 7073 ⟨115121, by decide⟩ :=
  accepted_of_selected 12 7073 ⟨115121, by decide⟩ ⟨12, 2, 0, 115121, 7073, 1645, 65536⟩
    (by decide) selected_cut_03677

theorem selected_cut_03678 : selected 9 ⟨115158, by decide⟩
    (prefixPartial 12 7074) = some ⟨12, 2, 0, 115158, 7074, 1553, 65536⟩ := by
  decide +kernel

theorem context_12_7074_115158 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 7074 ⟨115158, by decide⟩ :=
  accepted_of_selected 12 7074 ⟨115158, by decide⟩ ⟨12, 2, 0, 115158, 7074, 1553, 65536⟩
    (by decide) selected_cut_03678

theorem selected_cut_03679 : selected 9 ⟨115195, by decide⟩
    (prefixPartial 12 7075) = some ⟨12, 2, 0, 115195, 7075, 1533, 65536⟩ := by
  decide +kernel

theorem context_12_7075_115195 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 7075 ⟨115195, by decide⟩ :=
  accepted_of_selected 12 7075 ⟨115195, by decide⟩ ⟨12, 2, 0, 115195, 7075, 1533, 65536⟩
    (by decide) selected_cut_03679

theorem unmarked_context_11_1768_115196 : frontier 10 ⟨115196, by decide⟩
    (prefixCache 11 1768) (prefixPartial 11 1768) = false := by
  decide +kernel

theorem node_context_11_1768_115196 : EJMOriginalGlobalDAGData.nodes 10 ⟨115196, by decide⟩ =
    .split (coordinate 11) (![⟨115067, by decide⟩,⟨115121, by decide⟩,⟨115158, by decide⟩,⟨115195, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1768_115196 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1768 ⟨115196, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1768
    ⟨115196, by decide⟩ (by decide) (![⟨115067, by decide⟩,⟨115121, by decide⟩,⟨115158, by decide⟩,⟨115195, by decide⟩]) unmarked_context_11_1768_115196 node_context_11_1768_115196
  intro a
  fin_cases a
  · exact context_12_7072_115067
  · exact context_12_7073_115121
  · exact context_12_7074_115158
  · exact context_12_7075_115195

theorem selected_cut_03680 : selected 9 ⟨115255, by decide⟩
    (prefixPartial 12 7076) = some ⟨12, 2, 0, 115255, 7076, 1481, 65536⟩ := by
  decide +kernel

theorem context_12_7076_115255 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 7076 ⟨115255, by decide⟩ :=
  accepted_of_selected 12 7076 ⟨115255, by decide⟩ ⟨12, 2, 0, 115255, 7076, 1481, 65536⟩
    (by decide) selected_cut_03680

theorem selected_cut_03681 : selected 9 ⟨115312, by decide⟩
    (prefixPartial 12 7077) = some ⟨12, 2, 0, 115312, 7077, 1629, 65536⟩ := by
  decide +kernel

theorem context_12_7077_115312 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 7077 ⟨115312, by decide⟩ :=
  accepted_of_selected 12 7077 ⟨115312, by decide⟩ ⟨12, 2, 0, 115312, 7077, 1629, 65536⟩
    (by decide) selected_cut_03681

theorem selected_cut_03682 : selected 9 ⟨115375, by decide⟩
    (prefixPartial 12 7078) = some ⟨12, 2, 0, 115375, 7078, 1653, 65536⟩ := by
  decide +kernel

theorem context_12_7078_115375 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 7078 ⟨115375, by decide⟩ :=
  accepted_of_selected 12 7078 ⟨115375, by decide⟩ ⟨12, 2, 0, 115375, 7078, 1653, 65536⟩
    (by decide) selected_cut_03682

theorem selected_cut_03683 : selected 9 ⟨115429, by decide⟩
    (prefixPartial 12 7079) = some ⟨12, 2, 0, 115429, 7079, 1565, 65536⟩ := by
  decide +kernel

theorem context_12_7079_115429 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 7079 ⟨115429, by decide⟩ :=
  accepted_of_selected 12 7079 ⟨115429, by decide⟩ ⟨12, 2, 0, 115429, 7079, 1565, 65536⟩
    (by decide) selected_cut_03683

theorem unmarked_context_11_1769_115430 : frontier 10 ⟨115430, by decide⟩
    (prefixCache 11 1769) (prefixPartial 11 1769) = false := by
  decide +kernel

theorem node_context_11_1769_115430 : EJMOriginalGlobalDAGData.nodes 10 ⟨115430, by decide⟩ =
    .split (coordinate 11) (![⟨115255, by decide⟩,⟨115312, by decide⟩,⟨115375, by decide⟩,⟨115429, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1769_115430 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1769 ⟨115430, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1769
    ⟨115430, by decide⟩ (by decide) (![⟨115255, by decide⟩,⟨115312, by decide⟩,⟨115375, by decide⟩,⟨115429, by decide⟩]) unmarked_context_11_1769_115430 node_context_11_1769_115430
  intro a
  fin_cases a
  · exact context_12_7076_115255
  · exact context_12_7077_115312
  · exact context_12_7078_115375
  · exact context_12_7079_115429

theorem selected_cut_03684 : selected 9 ⟨115508, by decide⟩
    (prefixPartial 12 7080) = some ⟨12, 2, 0, 115508, 7080, 1769, 65536⟩ := by
  decide +kernel

theorem context_12_7080_115508 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 7080 ⟨115508, by decide⟩ :=
  accepted_of_selected 12 7080 ⟨115508, by decide⟩ ⟨12, 2, 0, 115508, 7080, 1769, 65536⟩
    (by decide) selected_cut_03684

theorem selected_cut_03685 : selected 9 ⟨115613, by decide⟩
    (prefixPartial 12 7081) = some ⟨12, 2, 0, 115613, 7081, 2241, 65536⟩ := by
  decide +kernel

theorem context_12_7081_115613 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 7081 ⟨115613, by decide⟩ :=
  accepted_of_selected 12 7081 ⟨115613, by decide⟩ ⟨12, 2, 0, 115613, 7081, 2241, 65536⟩
    (by decide) selected_cut_03685

theorem selected_cut_03686 : selected 9 ⟨115692, by decide⟩
    (prefixPartial 12 7082) = some ⟨12, 2, 0, 115692, 7082, 1613, 65536⟩ := by
  decide +kernel

theorem context_12_7082_115692 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 7082 ⟨115692, by decide⟩ :=
  accepted_of_selected 12 7082 ⟨115692, by decide⟩ ⟨12, 2, 0, 115692, 7082, 1613, 65536⟩
    (by decide) selected_cut_03686

theorem selected_cut_03687 : selected 9 ⟨115758, by decide⟩
    (prefixPartial 12 7083) = some ⟨12, 2, 0, 115758, 7083, 1577, 65536⟩ := by
  decide +kernel

theorem context_12_7083_115758 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 7083 ⟨115758, by decide⟩ :=
  accepted_of_selected 12 7083 ⟨115758, by decide⟩ ⟨12, 2, 0, 115758, 7083, 1577, 65536⟩
    (by decide) selected_cut_03687

theorem unmarked_context_11_1770_115759 : frontier 10 ⟨115759, by decide⟩
    (prefixCache 11 1770) (prefixPartial 11 1770) = false := by
  decide +kernel

theorem node_context_11_1770_115759 : EJMOriginalGlobalDAGData.nodes 10 ⟨115759, by decide⟩ =
    .split (coordinate 11) (![⟨115508, by decide⟩,⟨115613, by decide⟩,⟨115692, by decide⟩,⟨115758, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1770_115759 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1770 ⟨115759, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1770
    ⟨115759, by decide⟩ (by decide) (![⟨115508, by decide⟩,⟨115613, by decide⟩,⟨115692, by decide⟩,⟨115758, by decide⟩]) unmarked_context_11_1770_115759 node_context_11_1770_115759
  intro a
  fin_cases a
  · exact context_12_7080_115508
  · exact context_12_7081_115613
  · exact context_12_7082_115692
  · exact context_12_7083_115758

theorem selected_cut_03688 : selected 9 ⟨115794, by decide⟩
    (prefixPartial 12 7084) = some ⟨12, 2, 0, 115794, 7084, 921, 65536⟩ := by
  decide +kernel

theorem context_12_7084_115794 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 7084 ⟨115794, by decide⟩ :=
  accepted_of_selected 12 7084 ⟨115794, by decide⟩ ⟨12, 2, 0, 115794, 7084, 921, 65536⟩
    (by decide) selected_cut_03688

theorem selected_cut_03689 : selected 9 ⟨115832, by decide⟩
    (prefixPartial 12 7085) = some ⟨12, 2, 0, 115832, 7085, 1089, 65536⟩ := by
  decide +kernel

theorem context_12_7085_115832 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 7085 ⟨115832, by decide⟩ :=
  accepted_of_selected 12 7085 ⟨115832, by decide⟩ ⟨12, 2, 0, 115832, 7085, 1089, 65536⟩
    (by decide) selected_cut_03689

theorem selected_cut_03690 : selected 9 ⟨115865, by decide⟩
    (prefixPartial 12 7086) = some ⟨12, 2, 0, 115865, 7086, 873, 65536⟩ := by
  decide +kernel

theorem context_12_7086_115865 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 7086 ⟨115865, by decide⟩ :=
  accepted_of_selected 12 7086 ⟨115865, by decide⟩ ⟨12, 2, 0, 115865, 7086, 873, 65536⟩
    (by decide) selected_cut_03690

theorem selected_cut_03691 : selected 9 ⟨115948, by decide⟩
    (prefixPartial 12 7087) = some ⟨12, 2, 0, 115948, 7087, 1393, 65536⟩ := by
  decide +kernel

theorem context_12_7087_115948 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 7087 ⟨115948, by decide⟩ :=
  accepted_of_selected 12 7087 ⟨115948, by decide⟩ ⟨12, 2, 0, 115948, 7087, 1393, 65536⟩
    (by decide) selected_cut_03691

theorem unmarked_context_11_1771_115949 : frontier 10 ⟨115949, by decide⟩
    (prefixCache 11 1771) (prefixPartial 11 1771) = false := by
  decide +kernel

theorem node_context_11_1771_115949 : EJMOriginalGlobalDAGData.nodes 10 ⟨115949, by decide⟩ =
    .split (coordinate 11) (![⟨115794, by decide⟩,⟨115832, by decide⟩,⟨115865, by decide⟩,⟨115948, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1771_115949 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1771 ⟨115949, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1771
    ⟨115949, by decide⟩ (by decide) (![⟨115794, by decide⟩,⟨115832, by decide⟩,⟨115865, by decide⟩,⟨115948, by decide⟩]) unmarked_context_11_1771_115949 node_context_11_1771_115949
  intro a
  fin_cases a
  · exact context_12_7084_115794
  · exact context_12_7085_115832
  · exact context_12_7086_115865
  · exact context_12_7087_115948

theorem unmarked_context_10_442_115950 : frontier 11 ⟨115950, by decide⟩
    (prefixCache 10 442) (prefixPartial 10 442) = false := by
  decide +kernel

theorem node_context_10_442_115950 : EJMOriginalGlobalDAGData.nodes 11 ⟨115950, by decide⟩ =
    .split (coordinate 10) (![⟨115196, by decide⟩,⟨115430, by decide⟩,⟨115759, by decide⟩,⟨115949, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_442_115950 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 442 ⟨115950, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 442
    ⟨115950, by decide⟩ (by decide) (![⟨115196, by decide⟩,⟨115430, by decide⟩,⟨115759, by decide⟩,⟨115949, by decide⟩]) unmarked_context_10_442_115950 node_context_10_442_115950
  intro a
  fin_cases a
  · exact context_11_1768_115196
  · exact context_11_1769_115430
  · exact context_11_1770_115759
  · exact context_11_1771_115949

theorem selected_cut_03692 : selected 10 ⟨116097, by decide⟩
    (prefixPartial 11 1772) = some ⟨11, 2, 0, 116097, 1772, 3357, 262144⟩ := by
  decide +kernel

theorem context_11_1772_116097 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1772 ⟨116097, by decide⟩ :=
  accepted_of_selected 11 1772 ⟨116097, by decide⟩ ⟨11, 2, 0, 116097, 1772, 3357, 262144⟩
    (by decide) selected_cut_03692

theorem selected_cut_03693 : selected 10 ⟨116203, by decide⟩
    (prefixPartial 11 1773) = some ⟨11, 2, 0, 116203, 1773, 2753, 262144⟩ := by
  decide +kernel

theorem context_11_1773_116203 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1773 ⟨116203, by decide⟩ :=
  accepted_of_selected 11 1773 ⟨116203, by decide⟩ ⟨11, 2, 0, 116203, 1773, 2753, 262144⟩
    (by decide) selected_cut_03693

theorem selected_cut_03694 : selected 10 ⟨116264, by decide⟩
    (prefixPartial 11 1774) = some ⟨11, 2, 0, 116264, 1774, 1609, 262144⟩ := by
  decide +kernel

theorem context_11_1774_116264 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1774 ⟨116264, by decide⟩ :=
  accepted_of_selected 11 1774 ⟨116264, by decide⟩ ⟨11, 2, 0, 116264, 1774, 1609, 262144⟩
    (by decide) selected_cut_03694

theorem selected_cut_03695 : selected 10 ⟨116306, by decide⟩
    (prefixPartial 11 1775) = some ⟨11, 2, 0, 116306, 1775, 897, 262144⟩ := by
  decide +kernel

theorem context_11_1775_116306 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1775 ⟨116306, by decide⟩ :=
  accepted_of_selected 11 1775 ⟨116306, by decide⟩ ⟨11, 2, 0, 116306, 1775, 897, 262144⟩
    (by decide) selected_cut_03695

theorem unmarked_context_10_443_116307 : frontier 11 ⟨116307, by decide⟩
    (prefixCache 10 443) (prefixPartial 10 443) = false := by
  decide +kernel

theorem node_context_10_443_116307 : EJMOriginalGlobalDAGData.nodes 11 ⟨116307, by decide⟩ =
    .split (coordinate 10) (![⟨116097, by decide⟩,⟨116203, by decide⟩,⟨116264, by decide⟩,⟨116306, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_443_116307 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 443 ⟨116307, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 443
    ⟨116307, by decide⟩ (by decide) (![⟨116097, by decide⟩,⟨116203, by decide⟩,⟨116264, by decide⟩,⟨116306, by decide⟩]) unmarked_context_10_443_116307 node_context_10_443_116307
  intro a
  fin_cases a
  · exact context_11_1772_116097
  · exact context_11_1773_116203
  · exact context_11_1774_116264
  · exact context_11_1775_116306

theorem unmarked_context_9_110_116308 : frontier 12 ⟨116308, by decide⟩
    (prefixCache 9 110) (prefixPartial 9 110) = false := by
  decide +kernel

theorem node_context_9_110_116308 : EJMOriginalGlobalDAGData.nodes 12 ⟨116308, by decide⟩ =
    .split (coordinate 9) (![⟨114026, by decide⟩,⟨115031, by decide⟩,⟨115950, by decide⟩,⟨116307, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_110_116308 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 110 ⟨116308, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 110
    ⟨116308, by decide⟩ (by decide) (![⟨114026, by decide⟩,⟨115031, by decide⟩,⟨115950, by decide⟩,⟨116307, by decide⟩]) unmarked_context_9_110_116308 node_context_9_110_116308
  intro a
  fin_cases a
  · exact context_10_440_114026
  · exact context_10_441_115031
  · exact context_10_442_115950
  · exact context_10_443_116307

theorem selected_cut_03696 : selected 12 ⟨116309, by decide⟩
    (prefixPartial 9 111) = some ⟨9, 1, 0, 116309, 111, 1, 4194304⟩ := by
  decide +kernel

theorem context_9_111_116309 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 111 ⟨116309, by decide⟩ :=
  accepted_of_selected 9 111 ⟨116309, by decide⟩ ⟨9, 1, 0, 116309, 111, 1, 4194304⟩
    (by decide) selected_cut_03696

theorem unmarked_context_8_27_116310 : frontier 13 ⟨116310, by decide⟩
    (prefixCache 8 27) (prefixPartial 8 27) = false := by
  decide +kernel

theorem node_context_8_27_116310 : EJMOriginalGlobalDAGData.nodes 13 ⟨116310, by decide⟩ =
    .split (coordinate 8) (![⟨109218, by decide⟩,⟨113098, by decide⟩,⟨116308, by decide⟩,⟨116309, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_27_116310 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 27 ⟨116310, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 27
    ⟨116310, by decide⟩ (by decide) (![⟨109218, by decide⟩,⟨113098, by decide⟩,⟨116308, by decide⟩,⟨116309, by decide⟩]) unmarked_context_8_27_116310 node_context_8_27_116310
  intro a
  fin_cases a
  · exact context_9_108_109218
  · exact context_9_109_113098
  · exact context_9_110_116308
  · exact context_9_111_116309

theorem unmarked_context_7_6_116311 : frontier 14 ⟨116311, by decide⟩
    (prefixCache 7 6) (prefixPartial 7 6) = false := by
  decide +kernel

theorem node_context_7_6_116311 : EJMOriginalGlobalDAGData.nodes 14 ⟨116311, by decide⟩ =
    .split (coordinate 7) (![⟨14300, by decide⟩,⟨14300, by decide⟩,⟨102866, by decide⟩,⟨116310, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_7_6_116311 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 6 ⟨116311, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 7 6
    ⟨116311, by decide⟩ (by decide) (![⟨14300, by decide⟩,⟨14300, by decide⟩,⟨102866, by decide⟩,⟨116310, by decide⟩]) unmarked_context_7_6_116311 node_context_7_6_116311
  intro a
  fin_cases a
  · exact context_8_24_14300
  · exact context_8_25_14300
  · exact context_8_26_102866
  · exact context_8_27_116310

theorem selected_cut_03697 : selected 14 ⟨34032, by decide⟩
    (prefixPartial 7 7) = some ⟨7, 1, 0, 34032, 7, 1, 67108864⟩ := by
  decide +kernel

theorem context_7_7_34032 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 7 ⟨34032, by decide⟩ :=
  accepted_of_selected 7 7 ⟨34032, by decide⟩ ⟨7, 1, 0, 34032, 7, 1, 67108864⟩
    (by decide) selected_cut_03697

theorem unmarked_context_6_1_116312 : frontier 15 ⟨116312, by decide⟩
    (prefixCache 6 1) (prefixPartial 6 1) = false := by
  decide +kernel

theorem node_context_6_1_116312 : EJMOriginalGlobalDAGData.nodes 15 ⟨116312, by decide⟩ =
    .split (coordinate 6) (![⟨63749, by decide⟩,⟨86586, by decide⟩,⟨116311, by decide⟩,⟨34032, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_6_1_116312 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 6 1 ⟨116312, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 6 1
    ⟨116312, by decide⟩ (by decide) (![⟨63749, by decide⟩,⟨86586, by decide⟩,⟨116311, by decide⟩,⟨34032, by decide⟩]) unmarked_context_6_1_116312 node_context_6_1_116312
  intro a
  fin_cases a
  · exact context_7_4_63749
  · exact context_7_5_86586
  · exact context_7_6_116311
  · exact context_7_7_34032

theorem selected_cut_03698 : selected 15 ⟨116313, by decide⟩
    (prefixPartial 6 2) = some ⟨6, 1, 0, 116313, 2, 1, 268435456⟩ := by
  decide +kernel

theorem context_6_2_116313 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 6 2 ⟨116313, by decide⟩ :=
  accepted_of_selected 6 2 ⟨116313, by decide⟩ ⟨6, 1, 0, 116313, 2, 1, 268435456⟩
    (by decide) selected_cut_03698

theorem selected_cut_03699 : selected 15 ⟨116314, by decide⟩
    (prefixPartial 6 3) = some ⟨6, 1, 0, 116314, 3, 1, 268435456⟩ := by
  decide +kernel

theorem context_6_3_116314 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 6 3 ⟨116314, by decide⟩ :=
  accepted_of_selected 6 3 ⟨116314, by decide⟩ ⟨6, 1, 0, 116314, 3, 1, 268435456⟩
    (by decide) selected_cut_03699

theorem unmarked_context_5_0_116315 : frontier 16 ⟨116315, by decide⟩
    (prefixCache 5 0) (prefixPartial 5 0) = false := by
  decide +kernel

theorem node_context_5_0_116315 : EJMOriginalGlobalDAGData.nodes 16 ⟨116315, by decide⟩ =
    .split (coordinate 5) (![⟨34033, by decide⟩,⟨116312, by decide⟩,⟨116313, by decide⟩,⟨116314, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_5_0_116315 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 5 0 ⟨116315, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 5 0
    ⟨116315, by decide⟩ (by decide) (![⟨34033, by decide⟩,⟨116312, by decide⟩,⟨116313, by decide⟩,⟨116314, by decide⟩]) unmarked_context_5_0_116315 node_context_5_0_116315
  intro a
  fin_cases a
  · exact context_6_0_34033
  · exact context_6_1_116312
  · exact context_6_2_116313
  · exact context_6_3_116314

theorem selected_cut_03700 : selected 14 ⟨116316, by decide⟩
    (prefixPartial 7 16) = some ⟨7, 1, 0, 116316, 16, 1, 67108864⟩ := by
  decide +kernel

theorem context_7_16_116316 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 16 ⟨116316, by decide⟩ :=
  accepted_of_selected 7 16 ⟨116316, by decide⟩ ⟨7, 1, 0, 116316, 16, 1, 67108864⟩
    (by decide) selected_cut_03700

theorem selected_cut_03701 : selected 8 ⟨116550, by decide⟩
    (prefixPartial 13 69632) = some ⟨13, 2, 0, 116550, 69632, 3457, 16384⟩ := by
  decide +kernel

theorem context_13_69632_116550 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 69632 ⟨116550, by decide⟩ :=
  accepted_of_selected 13 69632 ⟨116550, by decide⟩ ⟨13, 2, 0, 116550, 69632, 3457, 16384⟩
    (by decide) selected_cut_03701

theorem selected_cut_03702 : selected 8 ⟨116681, by decide⟩
    (prefixPartial 13 69633) = some ⟨13, 2, 0, 116681, 69633, 1105, 16384⟩ := by
  decide +kernel

theorem context_13_69633_116681 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 69633 ⟨116681, by decide⟩ :=
  accepted_of_selected 13 69633 ⟨116681, by decide⟩ ⟨13, 2, 0, 116681, 69633, 1105, 16384⟩
    (by decide) selected_cut_03702

theorem selected_cut_03703 : selected 8 ⟨116706, by decide⟩
    (prefixPartial 13 69634) = some ⟨13, 2, 0, 116706, 69634, 181, 16384⟩ := by
  decide +kernel

theorem context_13_69634_116706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 69634 ⟨116706, by decide⟩ :=
  accepted_of_selected 13 69634 ⟨116706, by decide⟩ ⟨13, 2, 0, 116706, 69634, 181, 16384⟩
    (by decide) selected_cut_03703

theorem selected_cut_03704 : selected 8 ⟨414, by decide⟩
    (prefixPartial 13 69635) = some ⟨13, 1, 0, 414, 69635, 1, 16384⟩ := by
  decide +kernel

theorem context_13_69635_414 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 69635 ⟨414, by decide⟩ :=
  accepted_of_selected 13 69635 ⟨414, by decide⟩ ⟨13, 1, 0, 414, 69635, 1, 16384⟩
    (by decide) selected_cut_03704

theorem unmarked_context_12_17408_116707 : frontier 9 ⟨116707, by decide⟩
    (prefixCache 12 17408) (prefixPartial 12 17408) = false := by
  decide +kernel

theorem node_context_12_17408_116707 : EJMOriginalGlobalDAGData.nodes 9 ⟨116707, by decide⟩ =
    .split (coordinate 12) (![⟨116550, by decide⟩,⟨116681, by decide⟩,⟨116706, by decide⟩,⟨414, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_17408_116707 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17408 ⟨116707, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 17408
    ⟨116707, by decide⟩ (by decide) (![⟨116550, by decide⟩,⟨116681, by decide⟩,⟨116706, by decide⟩,⟨414, by decide⟩]) unmarked_context_12_17408_116707 node_context_12_17408_116707
  intro a
  fin_cases a
  · exact context_13_69632_116550
  · exact context_13_69633_116681
  · exact context_13_69634_116706
  · exact context_13_69635_414

theorem selected_cut_03705 : selected 8 ⟨116776, by decide⟩
    (prefixPartial 13 69636) = some ⟨13, 2, 0, 116776, 69636, 3181, 16384⟩ := by
  decide +kernel

theorem context_13_69636_116776 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 69636 ⟨116776, by decide⟩ :=
  accepted_of_selected 13 69636 ⟨116776, by decide⟩ ⟨13, 2, 0, 116776, 69636, 3181, 16384⟩
    (by decide) selected_cut_03705

theorem selected_cut_03706 : selected 8 ⟨116836, by decide⟩
    (prefixPartial 13 69637) = some ⟨13, 2, 0, 116836, 69637, 2137, 16384⟩ := by
  decide +kernel

theorem context_13_69637_116836 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 69637 ⟨116836, by decide⟩ :=
  accepted_of_selected 13 69637 ⟨116836, by decide⟩ ⟨13, 2, 0, 116836, 69637, 2137, 16384⟩
    (by decide) selected_cut_03706

theorem selected_cut_03707 : selected 8 ⟨116890, by decide⟩
    (prefixPartial 13 69638) = some ⟨13, 2, 0, 116890, 69638, 2185, 16384⟩ := by
  decide +kernel

theorem context_13_69638_116890 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 69638 ⟨116890, by decide⟩ :=
  accepted_of_selected 13 69638 ⟨116890, by decide⟩ ⟨13, 2, 0, 116890, 69638, 2185, 16384⟩
    (by decide) selected_cut_03707

theorem selected_cut_03708 : selected 8 ⟨414, by decide⟩
    (prefixPartial 13 69639) = some ⟨13, 1, 0, 414, 69639, 1, 16384⟩ := by
  decide +kernel

theorem context_13_69639_414 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 69639 ⟨414, by decide⟩ :=
  accepted_of_selected 13 69639 ⟨414, by decide⟩ ⟨13, 1, 0, 414, 69639, 1, 16384⟩
    (by decide) selected_cut_03708

theorem unmarked_context_12_17409_116891 : frontier 9 ⟨116891, by decide⟩
    (prefixCache 12 17409) (prefixPartial 12 17409) = false := by
  decide +kernel

theorem node_context_12_17409_116891 : EJMOriginalGlobalDAGData.nodes 9 ⟨116891, by decide⟩ =
    .split (coordinate 12) (![⟨116776, by decide⟩,⟨116836, by decide⟩,⟨116890, by decide⟩,⟨414, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_17409_116891 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17409 ⟨116891, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 17409
    ⟨116891, by decide⟩ (by decide) (![⟨116776, by decide⟩,⟨116836, by decide⟩,⟨116890, by decide⟩,⟨414, by decide⟩]) unmarked_context_12_17409_116891 node_context_12_17409_116891
  intro a
  fin_cases a
  · exact context_13_69636_116776
  · exact context_13_69637_116836
  · exact context_13_69638_116890
  · exact context_13_69639_414

theorem selected_cut_03709 : selected 7 ⟨116930, by decide⟩
    (prefixPartial 14 278560) = some ⟨14, 2, 0, 116930, 278560, 1577, 4096⟩ := by
  decide +kernel

theorem context_14_278560_116930 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 278560 ⟨116930, by decide⟩ :=
  accepted_of_selected 14 278560 ⟨116930, by decide⟩ ⟨14, 2, 0, 116930, 278560, 1577, 4096⟩
    (by decide) selected_cut_03709

theorem selected_cut_03710 : selected 7 ⟨116965, by decide⟩
    (prefixPartial 14 278561) = some ⟨14, 2, 0, 116965, 278561, 1617, 4096⟩ := by
  decide +kernel

theorem context_14_278561_116965 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 278561 ⟨116965, by decide⟩ :=
  accepted_of_selected 14 278561 ⟨116965, by decide⟩ ⟨14, 2, 0, 116965, 278561, 1617, 4096⟩
    (by decide) selected_cut_03710

theorem selected_cut_03711 : selected 7 ⟨116994, by decide⟩
    (prefixPartial 14 278562) = some ⟨14, 2, 0, 116994, 278562, 1597, 4096⟩ := by
  decide +kernel

theorem context_14_278562_116994 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 278562 ⟨116994, by decide⟩ :=
  accepted_of_selected 14 278562 ⟨116994, by decide⟩ ⟨14, 2, 0, 116994, 278562, 1597, 4096⟩
    (by decide) selected_cut_03711

theorem selected_cut_03712 : selected 7 ⟨117038, by decide⟩
    (prefixPartial 14 278563) = some ⟨14, 2, 0, 117038, 278563, 1673, 4096⟩ := by
  decide +kernel

theorem context_14_278563_117038 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 278563 ⟨117038, by decide⟩ :=
  accepted_of_selected 14 278563 ⟨117038, by decide⟩ ⟨14, 2, 0, 117038, 278563, 1673, 4096⟩
    (by decide) selected_cut_03712

theorem unmarked_context_13_69640_117039 : frontier 8 ⟨117039, by decide⟩
    (prefixCache 13 69640) (prefixPartial 13 69640) = false := by
  decide +kernel

theorem node_context_13_69640_117039 : EJMOriginalGlobalDAGData.nodes 8 ⟨117039, by decide⟩ =
    .split (coordinate 13) (![⟨116930, by decide⟩,⟨116965, by decide⟩,⟨116994, by decide⟩,⟨117038, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_69640_117039 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 69640 ⟨117039, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 69640
    ⟨117039, by decide⟩ (by decide) (![⟨116930, by decide⟩,⟨116965, by decide⟩,⟨116994, by decide⟩,⟨117038, by decide⟩]) unmarked_context_13_69640_117039 node_context_13_69640_117039
  intro a
  fin_cases a
  · exact context_14_278560_116930
  · exact context_14_278561_116965
  · exact context_14_278562_116994
  · exact context_14_278563_117038

theorem selected_cut_03713 : selected 7 ⟨117047, by decide⟩
    (prefixPartial 14 278564) = some ⟨14, 2, 0, 117047, 278564, 709, 4096⟩ := by
  decide +kernel

theorem context_14_278564_117047 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 278564 ⟨117047, by decide⟩ :=
  accepted_of_selected 14 278564 ⟨117047, by decide⟩ ⟨14, 2, 0, 117047, 278564, 709, 4096⟩
    (by decide) selected_cut_03713

theorem selected_cut_03714 : selected 7 ⟨117088, by decide⟩
    (prefixPartial 14 278565) = some ⟨14, 2, 0, 117088, 278565, 1477, 4096⟩ := by
  decide +kernel

theorem context_14_278565_117088 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 278565 ⟨117088, by decide⟩ :=
  accepted_of_selected 14 278565 ⟨117088, by decide⟩ ⟨14, 2, 0, 117088, 278565, 1477, 4096⟩
    (by decide) selected_cut_03714

theorem selected_cut_03715 : selected 7 ⟨117118, by decide⟩
    (prefixPartial 14 278566) = some ⟨14, 2, 0, 117118, 278566, 1253, 4096⟩ := by
  decide +kernel

theorem context_14_278566_117118 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 278566 ⟨117118, by decide⟩ :=
  accepted_of_selected 14 278566 ⟨117118, by decide⟩ ⟨14, 2, 0, 117118, 278566, 1253, 4096⟩
    (by decide) selected_cut_03715

theorem selected_cut_03716 : selected 7 ⟨117142, by decide⟩
    (prefixPartial 14 278567) = some ⟨14, 2, 0, 117142, 278567, 1121, 4096⟩ := by
  decide +kernel

theorem context_14_278567_117142 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 278567 ⟨117142, by decide⟩ :=
  accepted_of_selected 14 278567 ⟨117142, by decide⟩ ⟨14, 2, 0, 117142, 278567, 1121, 4096⟩
    (by decide) selected_cut_03716

theorem unmarked_context_13_69641_117143 : frontier 8 ⟨117143, by decide⟩
    (prefixCache 13 69641) (prefixPartial 13 69641) = false := by
  decide +kernel

theorem node_context_13_69641_117143 : EJMOriginalGlobalDAGData.nodes 8 ⟨117143, by decide⟩ =
    .split (coordinate 13) (![⟨117047, by decide⟩,⟨117088, by decide⟩,⟨117118, by decide⟩,⟨117142, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_69641_117143 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 69641 ⟨117143, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 69641
    ⟨117143, by decide⟩ (by decide) (![⟨117047, by decide⟩,⟨117088, by decide⟩,⟨117118, by decide⟩,⟨117142, by decide⟩]) unmarked_context_13_69641_117143 node_context_13_69641_117143
  intro a
  fin_cases a
  · exact context_14_278564_117047
  · exact context_14_278565_117088
  · exact context_14_278566_117118
  · exact context_14_278567_117142

theorem selected_cut_03717 : selected 8 ⟨117193, by decide⟩
    (prefixPartial 13 69642) = some ⟨13, 2, 0, 117193, 69642, 2461, 16384⟩ := by
  decide +kernel

theorem context_13_69642_117193 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 69642 ⟨117193, by decide⟩ :=
  accepted_of_selected 13 69642 ⟨117193, by decide⟩ ⟨13, 2, 0, 117193, 69642, 2461, 16384⟩
    (by decide) selected_cut_03717

theorem selected_cut_03718 : selected 8 ⟨117232, by decide⟩
    (prefixPartial 13 69643) = some ⟨13, 2, 0, 117232, 69643, 1353, 16384⟩ := by
  decide +kernel

theorem context_13_69643_117232 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 69643 ⟨117232, by decide⟩ :=
  accepted_of_selected 13 69643 ⟨117232, by decide⟩ ⟨13, 2, 0, 117232, 69643, 1353, 16384⟩
    (by decide) selected_cut_03718

theorem unmarked_context_12_17410_117233 : frontier 9 ⟨117233, by decide⟩
    (prefixCache 12 17410) (prefixPartial 12 17410) = false := by
  decide +kernel

theorem node_context_12_17410_117233 : EJMOriginalGlobalDAGData.nodes 9 ⟨117233, by decide⟩ =
    .split (coordinate 12) (![⟨117039, by decide⟩,⟨117143, by decide⟩,⟨117193, by decide⟩,⟨117232, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_17410_117233 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17410 ⟨117233, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 17410
    ⟨117233, by decide⟩ (by decide) (![⟨117039, by decide⟩,⟨117143, by decide⟩,⟨117193, by decide⟩,⟨117232, by decide⟩]) unmarked_context_12_17410_117233 node_context_12_17410_117233
  intro a
  fin_cases a
  · exact context_13_69640_117039
  · exact context_13_69641_117143
  · exact context_13_69642_117193
  · exact context_13_69643_117232

theorem selected_cut_03719 : selected 9 ⟨893, by decide⟩
    (prefixPartial 12 17411) = some ⟨12, 1, 0, 893, 17411, 1, 65536⟩ := by
  decide +kernel

theorem context_12_17411_893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17411 ⟨893, by decide⟩ :=
  accepted_of_selected 12 17411 ⟨893, by decide⟩ ⟨12, 1, 0, 893, 17411, 1, 65536⟩
    (by decide) selected_cut_03719

theorem unmarked_context_11_4352_117234 : frontier 10 ⟨117234, by decide⟩
    (prefixCache 11 4352) (prefixPartial 11 4352) = false := by
  decide +kernel

theorem node_context_11_4352_117234 : EJMOriginalGlobalDAGData.nodes 10 ⟨117234, by decide⟩ =
    .split (coordinate 11) (![⟨116707, by decide⟩,⟨116891, by decide⟩,⟨117233, by decide⟩,⟨893, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4352_117234 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4352 ⟨117234, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4352
    ⟨117234, by decide⟩ (by decide) (![⟨116707, by decide⟩,⟨116891, by decide⟩,⟨117233, by decide⟩,⟨893, by decide⟩]) unmarked_context_11_4352_117234 node_context_11_4352_117234
  intro a
  fin_cases a
  · exact context_12_17408_116707
  · exact context_12_17409_116891
  · exact context_12_17410_117233
  · exact context_12_17411_893

theorem selected_cut_03720 : selected 9 ⟨895, by decide⟩
    (prefixPartial 12 17412) = some ⟨12, 1, 0, 895, 17412, 1, 65536⟩ := by
  decide +kernel

theorem context_12_17412_895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17412 ⟨895, by decide⟩ :=
  accepted_of_selected 12 17412 ⟨895, by decide⟩ ⟨12, 1, 0, 895, 17412, 1, 65536⟩
    (by decide) selected_cut_03720

theorem selected_cut_03721 : selected 8 ⟨117306, by decide⟩
    (prefixPartial 13 69652) = some ⟨13, 2, 0, 117306, 69652, 2277, 16384⟩ := by
  decide +kernel

theorem context_13_69652_117306 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 69652 ⟨117306, by decide⟩ :=
  accepted_of_selected 13 69652 ⟨117306, by decide⟩ ⟨13, 2, 0, 117306, 69652, 2277, 16384⟩
    (by decide) selected_cut_03721

theorem selected_cut_03722 : selected 8 ⟨117365, by decide⟩
    (prefixPartial 13 69653) = some ⟨13, 2, 0, 117365, 69653, 1489, 16384⟩ := by
  decide +kernel

theorem context_13_69653_117365 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 69653 ⟨117365, by decide⟩ :=
  accepted_of_selected 13 69653 ⟨117365, by decide⟩ ⟨13, 2, 0, 117365, 69653, 1489, 16384⟩
    (by decide) selected_cut_03722

theorem selected_cut_03723 : selected 8 ⟨117387, by decide⟩
    (prefixPartial 13 69654) = some ⟨13, 2, 0, 117387, 69654, 593, 16384⟩ := by
  decide +kernel

theorem context_13_69654_117387 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 69654 ⟨117387, by decide⟩ :=
  accepted_of_selected 13 69654 ⟨117387, by decide⟩ ⟨13, 2, 0, 117387, 69654, 593, 16384⟩
    (by decide) selected_cut_03723

theorem selected_cut_03724 : selected 8 ⟨414, by decide⟩
    (prefixPartial 13 69655) = some ⟨13, 1, 0, 414, 69655, 1, 16384⟩ := by
  decide +kernel

theorem context_13_69655_414 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 69655 ⟨414, by decide⟩ :=
  accepted_of_selected 13 69655 ⟨414, by decide⟩ ⟨13, 1, 0, 414, 69655, 1, 16384⟩
    (by decide) selected_cut_03724

theorem unmarked_context_12_17413_117388 : frontier 9 ⟨117388, by decide⟩
    (prefixCache 12 17413) (prefixPartial 12 17413) = false := by
  decide +kernel

theorem node_context_12_17413_117388 : EJMOriginalGlobalDAGData.nodes 9 ⟨117388, by decide⟩ =
    .split (coordinate 12) (![⟨117306, by decide⟩,⟨117365, by decide⟩,⟨117387, by decide⟩,⟨414, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_17413_117388 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17413 ⟨117388, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 17413
    ⟨117388, by decide⟩ (by decide) (![⟨117306, by decide⟩,⟨117365, by decide⟩,⟨117387, by decide⟩,⟨414, by decide⟩]) unmarked_context_12_17413_117388 node_context_12_17413_117388
  intro a
  fin_cases a
  · exact context_13_69652_117306
  · exact context_13_69653_117365
  · exact context_13_69654_117387
  · exact context_13_69655_414

theorem selected_cut_03725 : selected 7 ⟨117436, by decide⟩
    (prefixPartial 14 278624) = some ⟨14, 2, 0, 117436, 278624, 1265, 4096⟩ := by
  decide +kernel

theorem context_14_278624_117436 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 278624 ⟨117436, by decide⟩ :=
  accepted_of_selected 14 278624 ⟨117436, by decide⟩ ⟨14, 2, 0, 117436, 278624, 1265, 4096⟩
    (by decide) selected_cut_03725

theorem selected_cut_03726 : selected 7 ⟨117472, by decide⟩
    (prefixPartial 14 278625) = some ⟨14, 2, 0, 117472, 278625, 1641, 4096⟩ := by
  decide +kernel

theorem context_14_278625_117472 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 278625 ⟨117472, by decide⟩ :=
  accepted_of_selected 14 278625 ⟨117472, by decide⟩ ⟨14, 2, 0, 117472, 278625, 1641, 4096⟩
    (by decide) selected_cut_03726

theorem selected_cut_03727 : selected 7 ⟨117500, by decide⟩
    (prefixPartial 14 278626) = some ⟨14, 2, 0, 117500, 278626, 1397, 4096⟩ := by
  decide +kernel

theorem context_14_278626_117500 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 278626 ⟨117500, by decide⟩ :=
  accepted_of_selected 14 278626 ⟨117500, by decide⟩ ⟨14, 2, 0, 117500, 278626, 1397, 4096⟩
    (by decide) selected_cut_03727

theorem selected_cut_03728 : selected 7 ⟨117530, by decide⟩
    (prefixPartial 14 278627) = some ⟨14, 2, 0, 117530, 278627, 1453, 4096⟩ := by
  decide +kernel

theorem context_14_278627_117530 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 278627 ⟨117530, by decide⟩ :=
  accepted_of_selected 14 278627 ⟨117530, by decide⟩ ⟨14, 2, 0, 117530, 278627, 1453, 4096⟩
    (by decide) selected_cut_03728

theorem unmarked_context_13_69656_117531 : frontier 8 ⟨117531, by decide⟩
    (prefixCache 13 69656) (prefixPartial 13 69656) = false := by
  decide +kernel

theorem node_context_13_69656_117531 : EJMOriginalGlobalDAGData.nodes 8 ⟨117531, by decide⟩ =
    .split (coordinate 13) (![⟨117436, by decide⟩,⟨117472, by decide⟩,⟨117500, by decide⟩,⟨117530, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_69656_117531 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 69656 ⟨117531, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 69656
    ⟨117531, by decide⟩ (by decide) (![⟨117436, by decide⟩,⟨117472, by decide⟩,⟨117500, by decide⟩,⟨117530, by decide⟩]) unmarked_context_13_69656_117531 node_context_13_69656_117531
  intro a
  fin_cases a
  · exact context_14_278624_117436
  · exact context_14_278625_117472
  · exact context_14_278626_117500
  · exact context_14_278627_117530

theorem selected_cut_03729 : selected 7 ⟨117575, by decide⟩
    (prefixPartial 14 278628) = some ⟨14, 2, 0, 117575, 278628, 1377, 4096⟩ := by
  decide +kernel

theorem context_14_278628_117575 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 278628 ⟨117575, by decide⟩ :=
  accepted_of_selected 14 278628 ⟨117575, by decide⟩ ⟨14, 2, 0, 117575, 278628, 1377, 4096⟩
    (by decide) selected_cut_03729

theorem selected_cut_03730 : selected 7 ⟨117637, by decide⟩
    (prefixPartial 14 278629) = some ⟨14, 2, 0, 117637, 278629, 1593, 4096⟩ := by
  decide +kernel

theorem context_14_278629_117637 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 278629 ⟨117637, by decide⟩ :=
  accepted_of_selected 14 278629 ⟨117637, by decide⟩ ⟨14, 2, 0, 117637, 278629, 1593, 4096⟩
    (by decide) selected_cut_03730

theorem selected_cut_03731 : selected 7 ⟨117677, by decide⟩
    (prefixPartial 14 278630) = some ⟨14, 2, 0, 117677, 278630, 1269, 4096⟩ := by
  decide +kernel

theorem context_14_278630_117677 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 278630 ⟨117677, by decide⟩ :=
  accepted_of_selected 14 278630 ⟨117677, by decide⟩ ⟨14, 2, 0, 117677, 278630, 1269, 4096⟩
    (by decide) selected_cut_03731

theorem selected_cut_03732 : selected 7 ⟨117710, by decide⟩
    (prefixPartial 14 278631) = some ⟨14, 2, 0, 117710, 278631, 1097, 4096⟩ := by
  decide +kernel

theorem context_14_278631_117710 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 278631 ⟨117710, by decide⟩ :=
  accepted_of_selected 14 278631 ⟨117710, by decide⟩ ⟨14, 2, 0, 117710, 278631, 1097, 4096⟩
    (by decide) selected_cut_03732

theorem unmarked_context_13_69657_117711 : frontier 8 ⟨117711, by decide⟩
    (prefixCache 13 69657) (prefixPartial 13 69657) = false := by
  decide +kernel

theorem node_context_13_69657_117711 : EJMOriginalGlobalDAGData.nodes 8 ⟨117711, by decide⟩ =
    .split (coordinate 13) (![⟨117575, by decide⟩,⟨117637, by decide⟩,⟨117677, by decide⟩,⟨117710, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_69657_117711 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 69657 ⟨117711, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 69657
    ⟨117711, by decide⟩ (by decide) (![⟨117575, by decide⟩,⟨117637, by decide⟩,⟨117677, by decide⟩,⟨117710, by decide⟩]) unmarked_context_13_69657_117711 node_context_13_69657_117711
  intro a
  fin_cases a
  · exact context_14_278628_117575
  · exact context_14_278629_117637
  · exact context_14_278630_117677
  · exact context_14_278631_117710

theorem selected_cut_03733 : selected 8 ⟨117791, by decide⟩
    (prefixPartial 13 69658) = some ⟨13, 2, 0, 117791, 69658, 3021, 16384⟩ := by
  decide +kernel

theorem context_13_69658_117791 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 69658 ⟨117791, by decide⟩ :=
  accepted_of_selected 13 69658 ⟨117791, by decide⟩ ⟨13, 2, 0, 117791, 69658, 3021, 16384⟩
    (by decide) selected_cut_03733

theorem selected_cut_03734 : selected 8 ⟨117833, by decide⟩
    (prefixPartial 13 69659) = some ⟨13, 2, 0, 117833, 69659, 1497, 16384⟩ := by
  decide +kernel

theorem context_13_69659_117833 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 69659 ⟨117833, by decide⟩ :=
  accepted_of_selected 13 69659 ⟨117833, by decide⟩ ⟨13, 2, 0, 117833, 69659, 1497, 16384⟩
    (by decide) selected_cut_03734

theorem unmarked_context_12_17414_117834 : frontier 9 ⟨117834, by decide⟩
    (prefixCache 12 17414) (prefixPartial 12 17414) = false := by
  decide +kernel

theorem node_context_12_17414_117834 : EJMOriginalGlobalDAGData.nodes 9 ⟨117834, by decide⟩ =
    .split (coordinate 12) (![⟨117531, by decide⟩,⟨117711, by decide⟩,⟨117791, by decide⟩,⟨117833, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_17414_117834 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17414 ⟨117834, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 17414
    ⟨117834, by decide⟩ (by decide) (![⟨117531, by decide⟩,⟨117711, by decide⟩,⟨117791, by decide⟩,⟨117833, by decide⟩]) unmarked_context_12_17414_117834 node_context_12_17414_117834
  intro a
  fin_cases a
  · exact context_13_69656_117531
  · exact context_13_69657_117711
  · exact context_13_69658_117791
  · exact context_13_69659_117833

theorem selected_cut_03735 : selected 9 ⟨893, by decide⟩
    (prefixPartial 12 17415) = some ⟨12, 1, 0, 893, 17415, 1, 65536⟩ := by
  decide +kernel

theorem context_12_17415_893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17415 ⟨893, by decide⟩ :=
  accepted_of_selected 12 17415 ⟨893, by decide⟩ ⟨12, 1, 0, 893, 17415, 1, 65536⟩
    (by decide) selected_cut_03735

theorem unmarked_context_11_4353_117835 : frontier 10 ⟨117835, by decide⟩
    (prefixCache 11 4353) (prefixPartial 11 4353) = false := by
  decide +kernel

theorem node_context_11_4353_117835 : EJMOriginalGlobalDAGData.nodes 10 ⟨117835, by decide⟩ =
    .split (coordinate 11) (![⟨895, by decide⟩,⟨117388, by decide⟩,⟨117834, by decide⟩,⟨893, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4353_117835 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4353 ⟨117835, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4353
    ⟨117835, by decide⟩ (by decide) (![⟨895, by decide⟩,⟨117388, by decide⟩,⟨117834, by decide⟩,⟨893, by decide⟩]) unmarked_context_11_4353_117835 node_context_11_4353_117835
  intro a
  fin_cases a
  · exact context_12_17412_895
  · exact context_12_17413_117388
  · exact context_12_17414_117834
  · exact context_12_17415_893

theorem selected_cut_03736 : selected 9 ⟨895, by decide⟩
    (prefixPartial 12 17416) = some ⟨12, 1, 0, 895, 17416, 1, 65536⟩ := by
  decide +kernel

theorem context_12_17416_895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17416 ⟨895, by decide⟩ :=
  accepted_of_selected 12 17416 ⟨895, by decide⟩ ⟨12, 1, 0, 895, 17416, 1, 65536⟩
    (by decide) selected_cut_03736

theorem selected_cut_03737 : selected 9 ⟨895, by decide⟩
    (prefixPartial 12 17417) = some ⟨12, 1, 0, 895, 17417, 1, 65536⟩ := by
  decide +kernel

theorem context_12_17417_895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17417 ⟨895, by decide⟩ :=
  accepted_of_selected 12 17417 ⟨895, by decide⟩ ⟨12, 1, 0, 895, 17417, 1, 65536⟩
    (by decide) selected_cut_03737

theorem selected_cut_03738 : selected 7 ⟨117857, by decide⟩
    (prefixPartial 14 278688) = some ⟨14, 2, 0, 117857, 278688, 361, 4096⟩ := by
  decide +kernel

theorem context_14_278688_117857 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 278688 ⟨117857, by decide⟩ :=
  accepted_of_selected 14 278688 ⟨117857, by decide⟩ ⟨14, 2, 0, 117857, 278688, 361, 4096⟩
    (by decide) selected_cut_03738

theorem selected_cut_03739 : selected 7 ⟨117914, by decide⟩
    (prefixPartial 14 278689) = some ⟨14, 2, 0, 117914, 278689, 1549, 4096⟩ := by
  decide +kernel

theorem context_14_278689_117914 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 278689 ⟨117914, by decide⟩ :=
  accepted_of_selected 14 278689 ⟨117914, by decide⟩ ⟨14, 2, 0, 117914, 278689, 1549, 4096⟩
    (by decide) selected_cut_03739

theorem selected_cut_03740 : selected 7 ⟨117943, by decide⟩
    (prefixPartial 14 278690) = some ⟨14, 2, 0, 117943, 278690, 1161, 4096⟩ := by
  decide +kernel

theorem context_14_278690_117943 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 278690 ⟨117943, by decide⟩ :=
  accepted_of_selected 14 278690 ⟨117943, by decide⟩ ⟨14, 2, 0, 117943, 278690, 1161, 4096⟩
    (by decide) selected_cut_03740

theorem selected_cut_03741 : selected 7 ⟨117985, by decide⟩
    (prefixPartial 14 278691) = some ⟨14, 2, 0, 117985, 278691, 1149, 4096⟩ := by
  decide +kernel

theorem context_14_278691_117985 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 278691 ⟨117985, by decide⟩ :=
  accepted_of_selected 14 278691 ⟨117985, by decide⟩ ⟨14, 2, 0, 117985, 278691, 1149, 4096⟩
    (by decide) selected_cut_03741

theorem unmarked_context_13_69672_117986 : frontier 8 ⟨117986, by decide⟩
    (prefixCache 13 69672) (prefixPartial 13 69672) = false := by
  decide +kernel

theorem node_context_13_69672_117986 : EJMOriginalGlobalDAGData.nodes 8 ⟨117986, by decide⟩ =
    .split (coordinate 13) (![⟨117857, by decide⟩,⟨117914, by decide⟩,⟨117943, by decide⟩,⟨117985, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_69672_117986 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 69672 ⟨117986, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 69672
    ⟨117986, by decide⟩ (by decide) (![⟨117857, by decide⟩,⟨117914, by decide⟩,⟨117943, by decide⟩,⟨117985, by decide⟩]) unmarked_context_13_69672_117986 node_context_13_69672_117986
  intro a
  fin_cases a
  · exact context_14_278688_117857
  · exact context_14_278689_117914
  · exact context_14_278690_117943
  · exact context_14_278691_117985

theorem selected_cut_03742 : selected 8 ⟨118103, by decide⟩
    (prefixPartial 13 69673) = some ⟨13, 2, 0, 118103, 69673, 2761, 16384⟩ := by
  decide +kernel

theorem context_13_69673_118103 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 69673 ⟨118103, by decide⟩ :=
  accepted_of_selected 13 69673 ⟨118103, by decide⟩ ⟨13, 2, 0, 118103, 69673, 2761, 16384⟩
    (by decide) selected_cut_03742

theorem selected_cut_03743 : selected 8 ⟨118128, by decide⟩
    (prefixPartial 13 69674) = some ⟨13, 2, 0, 118128, 69674, 701, 16384⟩ := by
  decide +kernel

theorem context_13_69674_118128 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 69674 ⟨118128, by decide⟩ :=
  accepted_of_selected 13 69674 ⟨118128, by decide⟩ ⟨13, 2, 0, 118128, 69674, 701, 16384⟩
    (by decide) selected_cut_03743

theorem selected_cut_03744 : selected 8 ⟨118136, by decide⟩
    (prefixPartial 13 69675) = some ⟨13, 2, 0, 118136, 69675, 149, 16384⟩ := by
  decide +kernel

theorem context_13_69675_118136 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 69675 ⟨118136, by decide⟩ :=
  accepted_of_selected 13 69675 ⟨118136, by decide⟩ ⟨13, 2, 0, 118136, 69675, 149, 16384⟩
    (by decide) selected_cut_03744

theorem unmarked_context_12_17418_118137 : frontier 9 ⟨118137, by decide⟩
    (prefixCache 12 17418) (prefixPartial 12 17418) = false := by
  decide +kernel

theorem node_context_12_17418_118137 : EJMOriginalGlobalDAGData.nodes 9 ⟨118137, by decide⟩ =
    .split (coordinate 12) (![⟨117986, by decide⟩,⟨118103, by decide⟩,⟨118128, by decide⟩,⟨118136, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_17418_118137 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17418 ⟨118137, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 17418
    ⟨118137, by decide⟩ (by decide) (![⟨117986, by decide⟩,⟨118103, by decide⟩,⟨118128, by decide⟩,⟨118136, by decide⟩]) unmarked_context_12_17418_118137 node_context_12_17418_118137
  intro a
  fin_cases a
  · exact context_13_69672_117986
  · exact context_13_69673_118103
  · exact context_13_69674_118128
  · exact context_13_69675_118136

theorem selected_cut_03745 : selected 7 ⟨118152, by decide⟩
    (prefixPartial 14 278704) = some ⟨14, 2, 0, 118152, 278704, 261, 4096⟩ := by
  decide +kernel

theorem context_14_278704_118152 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 278704 ⟨118152, by decide⟩ :=
  accepted_of_selected 14 278704 ⟨118152, by decide⟩ ⟨14, 2, 0, 118152, 278704, 261, 4096⟩
    (by decide) selected_cut_03745

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
