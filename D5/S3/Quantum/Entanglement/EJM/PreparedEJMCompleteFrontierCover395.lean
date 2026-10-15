/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover394
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_37923 : selected 9 ⟨1017537, by decide⟩
    (prefixPartial 12 300585) = some ⟨12, 2, 0, 1017537, 300585, 3989, 65536⟩ := by
  decide +kernel

theorem context_12_300585_1017537 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300585 ⟨1017537, by decide⟩ :=
  accepted_of_selected 12 300585 ⟨1017537, by decide⟩ ⟨12, 2, 0, 1017537, 300585, 3989, 65536⟩
    (by decide) selected_cut_37923

theorem selected_cut_37924 : selected 9 ⟨661671, by decide⟩
    (prefixPartial 12 300586) = some ⟨12, 1, 0, 661671, 300586, 1, 65536⟩ := by
  decide +kernel

theorem context_12_300586_661671 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300586 ⟨661671, by decide⟩ :=
  accepted_of_selected 12 300586 ⟨661671, by decide⟩ ⟨12, 1, 0, 661671, 300586, 1, 65536⟩
    (by decide) selected_cut_37924

theorem selected_cut_37925 : selected 9 ⟨1017602, by decide⟩
    (prefixPartial 12 300587) = some ⟨12, 2, 0, 1017602, 300587, 4069, 65536⟩ := by
  decide +kernel

theorem context_12_300587_1017602 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300587 ⟨1017602, by decide⟩ :=
  accepted_of_selected 12 300587 ⟨1017602, by decide⟩ ⟨12, 2, 0, 1017602, 300587, 4069, 65536⟩
    (by decide) selected_cut_37925

theorem unmarked_context_11_75146_1017603 : frontier 10 ⟨1017603, by decide⟩
    (prefixCache 11 75146) (prefixPartial 11 75146) = false := by
  decide +kernel

theorem node_context_11_75146_1017603 : EJMOriginalGlobalDAGData.nodes 10 ⟨1017603, by decide⟩ =
    .split (coordinate 11) (![⟨1017467, by decide⟩,⟨1017537, by decide⟩,⟨661671, by decide⟩,⟨1017602, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75146_1017603 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75146 ⟨1017603, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75146
    ⟨1017603, by decide⟩ (by decide) (![⟨1017467, by decide⟩,⟨1017537, by decide⟩,⟨661671, by decide⟩,⟨1017602, by decide⟩]) unmarked_context_11_75146_1017603 node_context_11_75146_1017603
  intro a
  fin_cases a
  · exact context_12_300584_1017467
  · exact context_12_300585_1017537
  · exact context_12_300586_661671
  · exact context_12_300587_1017602

theorem selected_cut_37926 : selected 9 ⟨1017660, by decide⟩
    (prefixPartial 12 300588) = some ⟨12, 2, 0, 1017660, 300588, 3945, 65536⟩ := by
  decide +kernel

theorem context_12_300588_1017660 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300588 ⟨1017660, by decide⟩ :=
  accepted_of_selected 12 300588 ⟨1017660, by decide⟩ ⟨12, 2, 0, 1017660, 300588, 3945, 65536⟩
    (by decide) selected_cut_37926

theorem selected_cut_37927 : selected 9 ⟨1017741, by decide⟩
    (prefixPartial 12 300589) = some ⟨12, 2, 0, 1017741, 300589, 4001, 65536⟩ := by
  decide +kernel

theorem context_12_300589_1017741 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300589 ⟨1017741, by decide⟩ :=
  accepted_of_selected 12 300589 ⟨1017741, by decide⟩ ⟨12, 2, 0, 1017741, 300589, 4001, 65536⟩
    (by decide) selected_cut_37927

theorem selected_cut_37928 : selected 9 ⟨1017793, by decide⟩
    (prefixPartial 12 300590) = some ⟨12, 2, 0, 1017793, 300590, 3529, 65536⟩ := by
  decide +kernel

theorem context_12_300590_1017793 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300590 ⟨1017793, by decide⟩ :=
  accepted_of_selected 12 300590 ⟨1017793, by decide⟩ ⟨12, 2, 0, 1017793, 300590, 3529, 65536⟩
    (by decide) selected_cut_37928

theorem selected_cut_37929 : selected 9 ⟨1017854, by decide⟩
    (prefixPartial 12 300591) = some ⟨12, 2, 0, 1017854, 300591, 3801, 65536⟩ := by
  decide +kernel

theorem context_12_300591_1017854 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300591 ⟨1017854, by decide⟩ :=
  accepted_of_selected 12 300591 ⟨1017854, by decide⟩ ⟨12, 2, 0, 1017854, 300591, 3801, 65536⟩
    (by decide) selected_cut_37929

theorem unmarked_context_11_75147_1017855 : frontier 10 ⟨1017855, by decide⟩
    (prefixCache 11 75147) (prefixPartial 11 75147) = false := by
  decide +kernel

theorem node_context_11_75147_1017855 : EJMOriginalGlobalDAGData.nodes 10 ⟨1017855, by decide⟩ =
    .split (coordinate 11) (![⟨1017660, by decide⟩,⟨1017741, by decide⟩,⟨1017793, by decide⟩,⟨1017854, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75147_1017855 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75147 ⟨1017855, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75147
    ⟨1017855, by decide⟩ (by decide) (![⟨1017660, by decide⟩,⟨1017741, by decide⟩,⟨1017793, by decide⟩,⟨1017854, by decide⟩]) unmarked_context_11_75147_1017855 node_context_11_75147_1017855
  intro a
  fin_cases a
  · exact context_12_300588_1017660
  · exact context_12_300589_1017741
  · exact context_12_300590_1017793
  · exact context_12_300591_1017854

theorem unmarked_context_10_18786_1017856 : frontier 11 ⟨1017856, by decide⟩
    (prefixCache 10 18786) (prefixPartial 10 18786) = false := by
  decide +kernel

theorem node_context_10_18786_1017856 : EJMOriginalGlobalDAGData.nodes 11 ⟨1017856, by decide⟩ =
    .split (coordinate 10) (![⟨1017193, by decide⟩,⟨1017411, by decide⟩,⟨1017603, by decide⟩,⟨1017855, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18786_1017856 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18786 ⟨1017856, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18786
    ⟨1017856, by decide⟩ (by decide) (![⟨1017193, by decide⟩,⟨1017411, by decide⟩,⟨1017603, by decide⟩,⟨1017855, by decide⟩]) unmarked_context_10_18786_1017856 node_context_10_18786_1017856
  intro a
  fin_cases a
  · exact context_11_75144_1017193
  · exact context_11_75145_1017411
  · exact context_11_75146_1017603
  · exact context_11_75147_1017855

theorem selected_cut_37930 : selected 9 ⟨994572, by decide⟩
    (prefixPartial 12 300592) = some ⟨12, 1, 0, 994572, 300592, 1, 65536⟩ := by
  decide +kernel

theorem context_12_300592_994572 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300592 ⟨994572, by decide⟩ :=
  accepted_of_selected 12 300592 ⟨994572, by decide⟩ ⟨12, 1, 0, 994572, 300592, 1, 65536⟩
    (by decide) selected_cut_37930

theorem selected_cut_37931 : selected 9 ⟨1017916, by decide⟩
    (prefixPartial 12 300593) = some ⟨12, 2, 0, 1017916, 300593, 3509, 65536⟩ := by
  decide +kernel

theorem context_12_300593_1017916 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300593 ⟨1017916, by decide⟩ :=
  accepted_of_selected 12 300593 ⟨1017916, by decide⟩ ⟨12, 2, 0, 1017916, 300593, 3509, 65536⟩
    (by decide) selected_cut_37931

theorem selected_cut_37932 : selected 9 ⟨1017962, by decide⟩
    (prefixPartial 12 300594) = some ⟨12, 2, 0, 1017962, 300594, 3233, 65536⟩ := by
  decide +kernel

theorem context_12_300594_1017962 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300594 ⟨1017962, by decide⟩ :=
  accepted_of_selected 12 300594 ⟨1017962, by decide⟩ ⟨12, 2, 0, 1017962, 300594, 3233, 65536⟩
    (by decide) selected_cut_37932

theorem selected_cut_37933 : selected 9 ⟨1018036, by decide⟩
    (prefixPartial 12 300595) = some ⟨12, 2, 0, 1018036, 300595, 3693, 65536⟩ := by
  decide +kernel

theorem context_12_300595_1018036 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300595 ⟨1018036, by decide⟩ :=
  accepted_of_selected 12 300595 ⟨1018036, by decide⟩ ⟨12, 2, 0, 1018036, 300595, 3693, 65536⟩
    (by decide) selected_cut_37933

theorem unmarked_context_11_75148_1018037 : frontier 10 ⟨1018037, by decide⟩
    (prefixCache 11 75148) (prefixPartial 11 75148) = false := by
  decide +kernel

theorem node_context_11_75148_1018037 : EJMOriginalGlobalDAGData.nodes 10 ⟨1018037, by decide⟩ =
    .split (coordinate 11) (![⟨994572, by decide⟩,⟨1017916, by decide⟩,⟨1017962, by decide⟩,⟨1018036, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75148_1018037 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75148 ⟨1018037, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75148
    ⟨1018037, by decide⟩ (by decide) (![⟨994572, by decide⟩,⟨1017916, by decide⟩,⟨1017962, by decide⟩,⟨1018036, by decide⟩]) unmarked_context_11_75148_1018037 node_context_11_75148_1018037
  intro a
  fin_cases a
  · exact context_12_300592_994572
  · exact context_12_300593_1017916
  · exact context_12_300594_1017962
  · exact context_12_300595_1018036

theorem selected_cut_37934 : selected 9 ⟨1018095, by decide⟩
    (prefixPartial 12 300596) = some ⟨12, 2, 0, 1018095, 300596, 3557, 65536⟩ := by
  decide +kernel

theorem context_12_300596_1018095 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300596 ⟨1018095, by decide⟩ :=
  accepted_of_selected 12 300596 ⟨1018095, by decide⟩ ⟨12, 2, 0, 1018095, 300596, 3557, 65536⟩
    (by decide) selected_cut_37934

theorem selected_cut_37935 : selected 9 ⟨1018157, by decide⟩
    (prefixPartial 12 300597) = some ⟨12, 2, 0, 1018157, 300597, 3453, 65536⟩ := by
  decide +kernel

theorem context_12_300597_1018157 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300597 ⟨1018157, by decide⟩ :=
  accepted_of_selected 12 300597 ⟨1018157, by decide⟩ ⟨12, 2, 0, 1018157, 300597, 3453, 65536⟩
    (by decide) selected_cut_37935

theorem selected_cut_37936 : selected 9 ⟨1018204, by decide⟩
    (prefixPartial 12 300598) = some ⟨12, 2, 0, 1018204, 300598, 3157, 65536⟩ := by
  decide +kernel

theorem context_12_300598_1018204 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300598 ⟨1018204, by decide⟩ :=
  accepted_of_selected 12 300598 ⟨1018204, by decide⟩ ⟨12, 2, 0, 1018204, 300598, 3157, 65536⟩
    (by decide) selected_cut_37936

theorem selected_cut_37937 : selected 9 ⟨1018269, by decide⟩
    (prefixPartial 12 300599) = some ⟨12, 2, 0, 1018269, 300599, 3429, 65536⟩ := by
  decide +kernel

theorem context_12_300599_1018269 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300599 ⟨1018269, by decide⟩ :=
  accepted_of_selected 12 300599 ⟨1018269, by decide⟩ ⟨12, 2, 0, 1018269, 300599, 3429, 65536⟩
    (by decide) selected_cut_37937

theorem unmarked_context_11_75149_1018270 : frontier 10 ⟨1018270, by decide⟩
    (prefixCache 11 75149) (prefixPartial 11 75149) = false := by
  decide +kernel

theorem node_context_11_75149_1018270 : EJMOriginalGlobalDAGData.nodes 10 ⟨1018270, by decide⟩ =
    .split (coordinate 11) (![⟨1018095, by decide⟩,⟨1018157, by decide⟩,⟨1018204, by decide⟩,⟨1018269, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75149_1018270 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75149 ⟨1018270, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75149
    ⟨1018270, by decide⟩ (by decide) (![⟨1018095, by decide⟩,⟨1018157, by decide⟩,⟨1018204, by decide⟩,⟨1018269, by decide⟩]) unmarked_context_11_75149_1018270 node_context_11_75149_1018270
  intro a
  fin_cases a
  · exact context_12_300596_1018095
  · exact context_12_300597_1018157
  · exact context_12_300598_1018204
  · exact context_12_300599_1018269

theorem selected_cut_37938 : selected 9 ⟨1018325, by decide⟩
    (prefixPartial 12 300600) = some ⟨12, 2, 0, 1018325, 300600, 3505, 65536⟩ := by
  decide +kernel

theorem context_12_300600_1018325 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300600 ⟨1018325, by decide⟩ :=
  accepted_of_selected 12 300600 ⟨1018325, by decide⟩ ⟨12, 2, 0, 1018325, 300600, 3505, 65536⟩
    (by decide) selected_cut_37938

theorem selected_cut_37939 : selected 9 ⟨1018379, by decide⟩
    (prefixPartial 12 300601) = some ⟨12, 2, 0, 1018379, 300601, 3469, 65536⟩ := by
  decide +kernel

theorem context_12_300601_1018379 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300601 ⟨1018379, by decide⟩ :=
  accepted_of_selected 12 300601 ⟨1018379, by decide⟩ ⟨12, 2, 0, 1018379, 300601, 3469, 65536⟩
    (by decide) selected_cut_37939

theorem selected_cut_37940 : selected 9 ⟨893903, by decide⟩
    (prefixPartial 12 300602) = some ⟨12, 1, 0, 893903, 300602, 1, 65536⟩ := by
  decide +kernel

theorem context_12_300602_893903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300602 ⟨893903, by decide⟩ :=
  accepted_of_selected 12 300602 ⟨893903, by decide⟩ ⟨12, 1, 0, 893903, 300602, 1, 65536⟩
    (by decide) selected_cut_37940

theorem selected_cut_37941 : selected 9 ⟨1018444, by decide⟩
    (prefixPartial 12 300603) = some ⟨12, 2, 0, 1018444, 300603, 3717, 65536⟩ := by
  decide +kernel

theorem context_12_300603_1018444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300603 ⟨1018444, by decide⟩ :=
  accepted_of_selected 12 300603 ⟨1018444, by decide⟩ ⟨12, 2, 0, 1018444, 300603, 3717, 65536⟩
    (by decide) selected_cut_37941

theorem unmarked_context_11_75150_1018445 : frontier 10 ⟨1018445, by decide⟩
    (prefixCache 11 75150) (prefixPartial 11 75150) = false := by
  decide +kernel

theorem node_context_11_75150_1018445 : EJMOriginalGlobalDAGData.nodes 10 ⟨1018445, by decide⟩ =
    .split (coordinate 11) (![⟨1018325, by decide⟩,⟨1018379, by decide⟩,⟨893903, by decide⟩,⟨1018444, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75150_1018445 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75150 ⟨1018445, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75150
    ⟨1018445, by decide⟩ (by decide) (![⟨1018325, by decide⟩,⟨1018379, by decide⟩,⟨893903, by decide⟩,⟨1018444, by decide⟩]) unmarked_context_11_75150_1018445 node_context_11_75150_1018445
  intro a
  fin_cases a
  · exact context_12_300600_1018325
  · exact context_12_300601_1018379
  · exact context_12_300602_893903
  · exact context_12_300603_1018444

theorem selected_cut_37942 : selected 9 ⟨1018500, by decide⟩
    (prefixPartial 12 300604) = some ⟨12, 2, 0, 1018500, 300604, 3597, 65536⟩ := by
  decide +kernel

theorem context_12_300604_1018500 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300604 ⟨1018500, by decide⟩ :=
  accepted_of_selected 12 300604 ⟨1018500, by decide⟩ ⟨12, 2, 0, 1018500, 300604, 3597, 65536⟩
    (by decide) selected_cut_37942

theorem selected_cut_37943 : selected 9 ⟨1018557, by decide⟩
    (prefixPartial 12 300605) = some ⟨12, 2, 0, 1018557, 300605, 3369, 65536⟩ := by
  decide +kernel

theorem context_12_300605_1018557 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300605 ⟨1018557, by decide⟩ :=
  accepted_of_selected 12 300605 ⟨1018557, by decide⟩ ⟨12, 2, 0, 1018557, 300605, 3369, 65536⟩
    (by decide) selected_cut_37943

theorem selected_cut_37944 : selected 9 ⟨1018608, by decide⟩
    (prefixPartial 12 300606) = some ⟨12, 2, 0, 1018608, 300606, 3269, 65536⟩ := by
  decide +kernel

theorem context_12_300606_1018608 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300606 ⟨1018608, by decide⟩ :=
  accepted_of_selected 12 300606 ⟨1018608, by decide⟩ ⟨12, 2, 0, 1018608, 300606, 3269, 65536⟩
    (by decide) selected_cut_37944

theorem selected_cut_37945 : selected 9 ⟨1018662, by decide⟩
    (prefixPartial 12 300607) = some ⟨12, 2, 0, 1018662, 300607, 3333, 65536⟩ := by
  decide +kernel

theorem context_12_300607_1018662 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300607 ⟨1018662, by decide⟩ :=
  accepted_of_selected 12 300607 ⟨1018662, by decide⟩ ⟨12, 2, 0, 1018662, 300607, 3333, 65536⟩
    (by decide) selected_cut_37945

theorem unmarked_context_11_75151_1018663 : frontier 10 ⟨1018663, by decide⟩
    (prefixCache 11 75151) (prefixPartial 11 75151) = false := by
  decide +kernel

theorem node_context_11_75151_1018663 : EJMOriginalGlobalDAGData.nodes 10 ⟨1018663, by decide⟩ =
    .split (coordinate 11) (![⟨1018500, by decide⟩,⟨1018557, by decide⟩,⟨1018608, by decide⟩,⟨1018662, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75151_1018663 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75151 ⟨1018663, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75151
    ⟨1018663, by decide⟩ (by decide) (![⟨1018500, by decide⟩,⟨1018557, by decide⟩,⟨1018608, by decide⟩,⟨1018662, by decide⟩]) unmarked_context_11_75151_1018663 node_context_11_75151_1018663
  intro a
  fin_cases a
  · exact context_12_300604_1018500
  · exact context_12_300605_1018557
  · exact context_12_300606_1018608
  · exact context_12_300607_1018662

theorem unmarked_context_10_18787_1018664 : frontier 11 ⟨1018664, by decide⟩
    (prefixCache 10 18787) (prefixPartial 10 18787) = false := by
  decide +kernel

theorem node_context_10_18787_1018664 : EJMOriginalGlobalDAGData.nodes 11 ⟨1018664, by decide⟩ =
    .split (coordinate 10) (![⟨1018037, by decide⟩,⟨1018270, by decide⟩,⟨1018445, by decide⟩,⟨1018663, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18787_1018664 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18787 ⟨1018664, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18787
    ⟨1018664, by decide⟩ (by decide) (![⟨1018037, by decide⟩,⟨1018270, by decide⟩,⟨1018445, by decide⟩,⟨1018663, by decide⟩]) unmarked_context_10_18787_1018664 node_context_10_18787_1018664
  intro a
  fin_cases a
  · exact context_11_75148_1018037
  · exact context_11_75149_1018270
  · exact context_11_75150_1018445
  · exact context_11_75151_1018663

theorem unmarked_context_9_4696_1018665 : frontier 12 ⟨1018665, by decide⟩
    (prefixCache 9 4696) (prefixPartial 9 4696) = false := by
  decide +kernel

theorem node_context_9_4696_1018665 : EJMOriginalGlobalDAGData.nodes 12 ⟨1018665, by decide⟩ =
    .split (coordinate 9) (![⟨1016390, by decide⟩,⟨1016996, by decide⟩,⟨1017856, by decide⟩,⟨1018664, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4696_1018665 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4696 ⟨1018665, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4696
    ⟨1018665, by decide⟩ (by decide) (![⟨1016390, by decide⟩,⟨1016996, by decide⟩,⟨1017856, by decide⟩,⟨1018664, by decide⟩]) unmarked_context_9_4696_1018665 node_context_9_4696_1018665
  intro a
  fin_cases a
  · exact context_10_18784_1016390
  · exact context_10_18785_1016996
  · exact context_10_18786_1017856
  · exact context_10_18787_1018664

theorem selected_cut_37946 : selected 9 ⟨1018820, by decide⟩
    (prefixPartial 12 300608) = some ⟨12, 2, 0, 1018820, 300608, 2129, 65536⟩ := by
  decide +kernel

theorem context_12_300608_1018820 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300608 ⟨1018820, by decide⟩ :=
  accepted_of_selected 12 300608 ⟨1018820, by decide⟩ ⟨12, 2, 0, 1018820, 300608, 2129, 65536⟩
    (by decide) selected_cut_37946

theorem selected_cut_37947 : selected 9 ⟨1018877, by decide⟩
    (prefixPartial 12 300609) = some ⟨12, 2, 0, 1018877, 300609, 2909, 65536⟩ := by
  decide +kernel

theorem context_12_300609_1018877 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300609 ⟨1018877, by decide⟩ :=
  accepted_of_selected 12 300609 ⟨1018877, by decide⟩ ⟨12, 2, 0, 1018877, 300609, 2909, 65536⟩
    (by decide) selected_cut_37947

theorem selected_cut_37948 : selected 9 ⟨1018934, by decide⟩
    (prefixPartial 12 300610) = some ⟨12, 2, 0, 1018934, 300610, 2945, 65536⟩ := by
  decide +kernel

theorem context_12_300610_1018934 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300610 ⟨1018934, by decide⟩ :=
  accepted_of_selected 12 300610 ⟨1018934, by decide⟩ ⟨12, 2, 0, 1018934, 300610, 2945, 65536⟩
    (by decide) selected_cut_37948

theorem selected_cut_37949 : selected 9 ⟨1018991, by decide⟩
    (prefixPartial 12 300611) = some ⟨12, 2, 0, 1018991, 300611, 3085, 65536⟩ := by
  decide +kernel

theorem context_12_300611_1018991 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300611 ⟨1018991, by decide⟩ :=
  accepted_of_selected 12 300611 ⟨1018991, by decide⟩ ⟨12, 2, 0, 1018991, 300611, 3085, 65536⟩
    (by decide) selected_cut_37949

theorem unmarked_context_11_75152_1018992 : frontier 10 ⟨1018992, by decide⟩
    (prefixCache 11 75152) (prefixPartial 11 75152) = false := by
  decide +kernel

theorem node_context_11_75152_1018992 : EJMOriginalGlobalDAGData.nodes 10 ⟨1018992, by decide⟩ =
    .split (coordinate 11) (![⟨1018820, by decide⟩,⟨1018877, by decide⟩,⟨1018934, by decide⟩,⟨1018991, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75152_1018992 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75152 ⟨1018992, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75152
    ⟨1018992, by decide⟩ (by decide) (![⟨1018820, by decide⟩,⟨1018877, by decide⟩,⟨1018934, by decide⟩,⟨1018991, by decide⟩]) unmarked_context_11_75152_1018992 node_context_11_75152_1018992
  intro a
  fin_cases a
  · exact context_12_300608_1018820
  · exact context_12_300609_1018877
  · exact context_12_300610_1018934
  · exact context_12_300611_1018991

theorem selected_cut_37950 : selected 9 ⟨1019074, by decide⟩
    (prefixPartial 12 300612) = some ⟨12, 2, 0, 1019074, 300612, 3257, 65536⟩ := by
  decide +kernel

theorem context_12_300612_1019074 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300612 ⟨1019074, by decide⟩ :=
  accepted_of_selected 12 300612 ⟨1019074, by decide⟩ ⟨12, 2, 0, 1019074, 300612, 3257, 65536⟩
    (by decide) selected_cut_37950

theorem selected_cut_37951 : selected 9 ⟨691709, by decide⟩
    (prefixPartial 12 300613) = some ⟨12, 1, 0, 691709, 300613, 1, 65536⟩ := by
  decide +kernel

theorem context_12_300613_691709 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300613 ⟨691709, by decide⟩ :=
  accepted_of_selected 12 300613 ⟨691709, by decide⟩ ⟨12, 1, 0, 691709, 300613, 1, 65536⟩
    (by decide) selected_cut_37951

theorem selected_cut_37952 : selected 9 ⟨1019122, by decide⟩
    (prefixPartial 12 300614) = some ⟨12, 2, 0, 1019122, 300614, 2569, 65536⟩ := by
  decide +kernel

theorem context_12_300614_1019122 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300614 ⟨1019122, by decide⟩ :=
  accepted_of_selected 12 300614 ⟨1019122, by decide⟩ ⟨12, 2, 0, 1019122, 300614, 2569, 65536⟩
    (by decide) selected_cut_37952

theorem selected_cut_37953 : selected 9 ⟨1019178, by decide⟩
    (prefixPartial 12 300615) = some ⟨12, 2, 0, 1019178, 300615, 2705, 65536⟩ := by
  decide +kernel

theorem context_12_300615_1019178 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300615 ⟨1019178, by decide⟩ :=
  accepted_of_selected 12 300615 ⟨1019178, by decide⟩ ⟨12, 2, 0, 1019178, 300615, 2705, 65536⟩
    (by decide) selected_cut_37953

theorem unmarked_context_11_75153_1019179 : frontier 10 ⟨1019179, by decide⟩
    (prefixCache 11 75153) (prefixPartial 11 75153) = false := by
  decide +kernel

theorem node_context_11_75153_1019179 : EJMOriginalGlobalDAGData.nodes 10 ⟨1019179, by decide⟩ =
    .split (coordinate 11) (![⟨1019074, by decide⟩,⟨691709, by decide⟩,⟨1019122, by decide⟩,⟨1019178, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75153_1019179 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75153 ⟨1019179, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75153
    ⟨1019179, by decide⟩ (by decide) (![⟨1019074, by decide⟩,⟨691709, by decide⟩,⟨1019122, by decide⟩,⟨1019178, by decide⟩]) unmarked_context_11_75153_1019179 node_context_11_75153_1019179
  intro a
  fin_cases a
  · exact context_12_300612_1019074
  · exact context_12_300613_691709
  · exact context_12_300614_1019122
  · exact context_12_300615_1019178

theorem selected_cut_37954 : selected 9 ⟨1019261, by decide⟩
    (prefixPartial 12 300616) = some ⟨12, 2, 0, 1019261, 300616, 3657, 65536⟩ := by
  decide +kernel

theorem context_12_300616_1019261 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300616 ⟨1019261, by decide⟩ :=
  accepted_of_selected 12 300616 ⟨1019261, by decide⟩ ⟨12, 2, 0, 1019261, 300616, 3657, 65536⟩
    (by decide) selected_cut_37954

theorem selected_cut_37955 : selected 9 ⟨1019314, by decide⟩
    (prefixPartial 12 300617) = some ⟨12, 2, 0, 1019314, 300617, 3089, 65536⟩ := by
  decide +kernel

theorem context_12_300617_1019314 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300617 ⟨1019314, by decide⟩ :=
  accepted_of_selected 12 300617 ⟨1019314, by decide⟩ ⟨12, 2, 0, 1019314, 300617, 3089, 65536⟩
    (by decide) selected_cut_37955

theorem selected_cut_37956 : selected 9 ⟨893903, by decide⟩
    (prefixPartial 12 300618) = some ⟨12, 1, 0, 893903, 300618, 1, 65536⟩ := by
  decide +kernel

theorem context_12_300618_893903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300618 ⟨893903, by decide⟩ :=
  accepted_of_selected 12 300618 ⟨893903, by decide⟩ ⟨12, 1, 0, 893903, 300618, 1, 65536⟩
    (by decide) selected_cut_37956

theorem selected_cut_37957 : selected 9 ⟨1019377, by decide⟩
    (prefixPartial 12 300619) = some ⟨12, 2, 0, 1019377, 300619, 3325, 65536⟩ := by
  decide +kernel

theorem context_12_300619_1019377 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300619 ⟨1019377, by decide⟩ :=
  accepted_of_selected 12 300619 ⟨1019377, by decide⟩ ⟨12, 2, 0, 1019377, 300619, 3325, 65536⟩
    (by decide) selected_cut_37957

theorem unmarked_context_11_75154_1019378 : frontier 10 ⟨1019378, by decide⟩
    (prefixCache 11 75154) (prefixPartial 11 75154) = false := by
  decide +kernel

theorem node_context_11_75154_1019378 : EJMOriginalGlobalDAGData.nodes 10 ⟨1019378, by decide⟩ =
    .split (coordinate 11) (![⟨1019261, by decide⟩,⟨1019314, by decide⟩,⟨893903, by decide⟩,⟨1019377, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75154_1019378 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75154 ⟨1019378, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75154
    ⟨1019378, by decide⟩ (by decide) (![⟨1019261, by decide⟩,⟨1019314, by decide⟩,⟨893903, by decide⟩,⟨1019377, by decide⟩]) unmarked_context_11_75154_1019378 node_context_11_75154_1019378
  intro a
  fin_cases a
  · exact context_12_300616_1019261
  · exact context_12_300617_1019314
  · exact context_12_300618_893903
  · exact context_12_300619_1019377

theorem selected_cut_37958 : selected 9 ⟨1019444, by decide⟩
    (prefixPartial 12 300620) = some ⟨12, 2, 0, 1019444, 300620, 3729, 65536⟩ := by
  decide +kernel

theorem context_12_300620_1019444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300620 ⟨1019444, by decide⟩ :=
  accepted_of_selected 12 300620 ⟨1019444, by decide⟩ ⟨12, 2, 0, 1019444, 300620, 3729, 65536⟩
    (by decide) selected_cut_37958

theorem selected_cut_37959 : selected 9 ⟨1019491, by decide⟩
    (prefixPartial 12 300621) = some ⟨12, 2, 0, 1019491, 300621, 2993, 65536⟩ := by
  decide +kernel

theorem context_12_300621_1019491 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300621 ⟨1019491, by decide⟩ :=
  accepted_of_selected 12 300621 ⟨1019491, by decide⟩ ⟨12, 2, 0, 1019491, 300621, 2993, 65536⟩
    (by decide) selected_cut_37959

theorem selected_cut_37960 : selected 9 ⟨1019539, by decide⟩
    (prefixPartial 12 300622) = some ⟨12, 2, 0, 1019539, 300622, 3269, 65536⟩ := by
  decide +kernel

theorem context_12_300622_1019539 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300622 ⟨1019539, by decide⟩ :=
  accepted_of_selected 12 300622 ⟨1019539, by decide⟩ ⟨12, 2, 0, 1019539, 300622, 3269, 65536⟩
    (by decide) selected_cut_37960

theorem selected_cut_37961 : selected 9 ⟨1019591, by decide⟩
    (prefixPartial 12 300623) = some ⟨12, 2, 0, 1019591, 300623, 3013, 65536⟩ := by
  decide +kernel

theorem context_12_300623_1019591 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300623 ⟨1019591, by decide⟩ :=
  accepted_of_selected 12 300623 ⟨1019591, by decide⟩ ⟨12, 2, 0, 1019591, 300623, 3013, 65536⟩
    (by decide) selected_cut_37961

theorem unmarked_context_11_75155_1019592 : frontier 10 ⟨1019592, by decide⟩
    (prefixCache 11 75155) (prefixPartial 11 75155) = false := by
  decide +kernel

theorem node_context_11_75155_1019592 : EJMOriginalGlobalDAGData.nodes 10 ⟨1019592, by decide⟩ =
    .split (coordinate 11) (![⟨1019444, by decide⟩,⟨1019491, by decide⟩,⟨1019539, by decide⟩,⟨1019591, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75155_1019592 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75155 ⟨1019592, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75155
    ⟨1019592, by decide⟩ (by decide) (![⟨1019444, by decide⟩,⟨1019491, by decide⟩,⟨1019539, by decide⟩,⟨1019591, by decide⟩]) unmarked_context_11_75155_1019592 node_context_11_75155_1019592
  intro a
  fin_cases a
  · exact context_12_300620_1019444
  · exact context_12_300621_1019491
  · exact context_12_300622_1019539
  · exact context_12_300623_1019591

theorem unmarked_context_10_18788_1019593 : frontier 11 ⟨1019593, by decide⟩
    (prefixCache 10 18788) (prefixPartial 10 18788) = false := by
  decide +kernel

theorem node_context_10_18788_1019593 : EJMOriginalGlobalDAGData.nodes 11 ⟨1019593, by decide⟩ =
    .split (coordinate 10) (![⟨1018992, by decide⟩,⟨1019179, by decide⟩,⟨1019378, by decide⟩,⟨1019592, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18788_1019593 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18788 ⟨1019593, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18788
    ⟨1019593, by decide⟩ (by decide) (![⟨1018992, by decide⟩,⟨1019179, by decide⟩,⟨1019378, by decide⟩,⟨1019592, by decide⟩]) unmarked_context_10_18788_1019593 node_context_10_18788_1019593
  intro a
  fin_cases a
  · exact context_11_75152_1018992
  · exact context_11_75153_1019179
  · exact context_11_75154_1019378
  · exact context_11_75155_1019592

theorem selected_cut_37962 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 18789) = some ⟨10, 1, 0, 893098, 18789, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_18789_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18789 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 18789 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 18789, 1, 1048576⟩
    (by decide) selected_cut_37962

theorem selected_cut_37963 : selected 9 ⟨1019633, by decide⟩
    (prefixPartial 12 300640) = some ⟨12, 2, 0, 1019633, 300640, 2529, 65536⟩ := by
  decide +kernel

theorem context_12_300640_1019633 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300640 ⟨1019633, by decide⟩ :=
  accepted_of_selected 12 300640 ⟨1019633, by decide⟩ ⟨12, 2, 0, 1019633, 300640, 2529, 65536⟩
    (by decide) selected_cut_37963

theorem selected_cut_37964 : selected 9 ⟨1019668, by decide⟩
    (prefixPartial 12 300641) = some ⟨12, 2, 0, 1019668, 300641, 2413, 65536⟩ := by
  decide +kernel

theorem context_12_300641_1019668 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300641 ⟨1019668, by decide⟩ :=
  accepted_of_selected 12 300641 ⟨1019668, by decide⟩ ⟨12, 2, 0, 1019668, 300641, 2413, 65536⟩
    (by decide) selected_cut_37964

theorem selected_cut_37965 : selected 9 ⟨1019699, by decide⟩
    (prefixPartial 12 300642) = some ⟨12, 2, 0, 1019699, 300642, 2133, 65536⟩ := by
  decide +kernel

theorem context_12_300642_1019699 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300642 ⟨1019699, by decide⟩ :=
  accepted_of_selected 12 300642 ⟨1019699, by decide⟩ ⟨12, 2, 0, 1019699, 300642, 2133, 65536⟩
    (by decide) selected_cut_37965

theorem selected_cut_37966 : selected 9 ⟨1019746, by decide⟩
    (prefixPartial 12 300643) = some ⟨12, 2, 0, 1019746, 300643, 2417, 65536⟩ := by
  decide +kernel

theorem context_12_300643_1019746 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300643 ⟨1019746, by decide⟩ :=
  accepted_of_selected 12 300643 ⟨1019746, by decide⟩ ⟨12, 2, 0, 1019746, 300643, 2417, 65536⟩
    (by decide) selected_cut_37966

theorem unmarked_context_11_75160_1019747 : frontier 10 ⟨1019747, by decide⟩
    (prefixCache 11 75160) (prefixPartial 11 75160) = false := by
  decide +kernel

theorem node_context_11_75160_1019747 : EJMOriginalGlobalDAGData.nodes 10 ⟨1019747, by decide⟩ =
    .split (coordinate 11) (![⟨1019633, by decide⟩,⟨1019668, by decide⟩,⟨1019699, by decide⟩,⟨1019746, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75160_1019747 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75160 ⟨1019747, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75160
    ⟨1019747, by decide⟩ (by decide) (![⟨1019633, by decide⟩,⟨1019668, by decide⟩,⟨1019699, by decide⟩,⟨1019746, by decide⟩]) unmarked_context_11_75160_1019747 node_context_11_75160_1019747
  intro a
  fin_cases a
  · exact context_12_300640_1019633
  · exact context_12_300641_1019668
  · exact context_12_300642_1019699
  · exact context_12_300643_1019746

theorem selected_cut_37967 : selected 9 ⟨1019778, by decide⟩
    (prefixPartial 12 300644) = some ⟨12, 2, 0, 1019778, 300644, 2029, 65536⟩ := by
  decide +kernel

theorem context_12_300644_1019778 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300644 ⟨1019778, by decide⟩ :=
  accepted_of_selected 12 300644 ⟨1019778, by decide⟩ ⟨12, 2, 0, 1019778, 300644, 2029, 65536⟩
    (by decide) selected_cut_37967

theorem selected_cut_37968 : selected 9 ⟨691709, by decide⟩
    (prefixPartial 12 300645) = some ⟨12, 1, 0, 691709, 300645, 1, 65536⟩ := by
  decide +kernel

theorem context_12_300645_691709 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300645 ⟨691709, by decide⟩ :=
  accepted_of_selected 12 300645 ⟨691709, by decide⟩ ⟨12, 1, 0, 691709, 300645, 1, 65536⟩
    (by decide) selected_cut_37968

theorem selected_cut_37969 : selected 9 ⟨1019813, by decide⟩
    (prefixPartial 12 300646) = some ⟨12, 2, 0, 1019813, 300646, 1753, 65536⟩ := by
  decide +kernel

theorem context_12_300646_1019813 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300646 ⟨1019813, by decide⟩ :=
  accepted_of_selected 12 300646 ⟨1019813, by decide⟩ ⟨12, 2, 0, 1019813, 300646, 1753, 65536⟩
    (by decide) selected_cut_37969

theorem selected_cut_37970 : selected 9 ⟨1019847, by decide⟩
    (prefixPartial 12 300647) = some ⟨12, 2, 0, 1019847, 300647, 1949, 65536⟩ := by
  decide +kernel

theorem context_12_300647_1019847 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300647 ⟨1019847, by decide⟩ :=
  accepted_of_selected 12 300647 ⟨1019847, by decide⟩ ⟨12, 2, 0, 1019847, 300647, 1949, 65536⟩
    (by decide) selected_cut_37970

theorem unmarked_context_11_75161_1019848 : frontier 10 ⟨1019848, by decide⟩
    (prefixCache 11 75161) (prefixPartial 11 75161) = false := by
  decide +kernel

theorem node_context_11_75161_1019848 : EJMOriginalGlobalDAGData.nodes 10 ⟨1019848, by decide⟩ =
    .split (coordinate 11) (![⟨1019778, by decide⟩,⟨691709, by decide⟩,⟨1019813, by decide⟩,⟨1019847, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75161_1019848 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75161 ⟨1019848, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75161
    ⟨1019848, by decide⟩ (by decide) (![⟨1019778, by decide⟩,⟨691709, by decide⟩,⟨1019813, by decide⟩,⟨1019847, by decide⟩]) unmarked_context_11_75161_1019848 node_context_11_75161_1019848
  intro a
  fin_cases a
  · exact context_12_300644_1019778
  · exact context_12_300645_691709
  · exact context_12_300646_1019813
  · exact context_12_300647_1019847

theorem selected_cut_37971 : selected 9 ⟨1019893, by decide⟩
    (prefixPartial 12 300648) = some ⟨12, 2, 0, 1019893, 300648, 2553, 65536⟩ := by
  decide +kernel

theorem context_12_300648_1019893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300648 ⟨1019893, by decide⟩ :=
  accepted_of_selected 12 300648 ⟨1019893, by decide⟩ ⟨12, 2, 0, 1019893, 300648, 2553, 65536⟩
    (by decide) selected_cut_37971

theorem selected_cut_37972 : selected 9 ⟨1019943, by decide⟩
    (prefixPartial 12 300649) = some ⟨12, 2, 0, 1019943, 300649, 2433, 65536⟩ := by
  decide +kernel

theorem context_12_300649_1019943 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300649 ⟨1019943, by decide⟩ :=
  accepted_of_selected 12 300649 ⟨1019943, by decide⟩ ⟨12, 2, 0, 1019943, 300649, 2433, 65536⟩
    (by decide) selected_cut_37972

theorem selected_cut_37973 : selected 9 ⟨661671, by decide⟩
    (prefixPartial 12 300650) = some ⟨12, 1, 0, 661671, 300650, 1, 65536⟩ := by
  decide +kernel

theorem context_12_300650_661671 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300650 ⟨661671, by decide⟩ :=
  accepted_of_selected 12 300650 ⟨661671, by decide⟩ ⟨12, 1, 0, 661671, 300650, 1, 65536⟩
    (by decide) selected_cut_37973

theorem selected_cut_37974 : selected 9 ⟨1019988, by decide⟩
    (prefixPartial 12 300651) = some ⟨12, 2, 0, 1019988, 300651, 2501, 65536⟩ := by
  decide +kernel

theorem context_12_300651_1019988 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300651 ⟨1019988, by decide⟩ :=
  accepted_of_selected 12 300651 ⟨1019988, by decide⟩ ⟨12, 2, 0, 1019988, 300651, 2501, 65536⟩
    (by decide) selected_cut_37974

theorem unmarked_context_11_75162_1019989 : frontier 10 ⟨1019989, by decide⟩
    (prefixCache 11 75162) (prefixPartial 11 75162) = false := by
  decide +kernel

theorem node_context_11_75162_1019989 : EJMOriginalGlobalDAGData.nodes 10 ⟨1019989, by decide⟩ =
    .split (coordinate 11) (![⟨1019893, by decide⟩,⟨1019943, by decide⟩,⟨661671, by decide⟩,⟨1019988, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75162_1019989 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75162 ⟨1019989, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75162
    ⟨1019989, by decide⟩ (by decide) (![⟨1019893, by decide⟩,⟨1019943, by decide⟩,⟨661671, by decide⟩,⟨1019988, by decide⟩]) unmarked_context_11_75162_1019989 node_context_11_75162_1019989
  intro a
  fin_cases a
  · exact context_12_300648_1019893
  · exact context_12_300649_1019943
  · exact context_12_300650_661671
  · exact context_12_300651_1019988

theorem selected_cut_37975 : selected 9 ⟨1020031, by decide⟩
    (prefixPartial 12 300652) = some ⟨12, 2, 0, 1020031, 300652, 2485, 65536⟩ := by
  decide +kernel

theorem context_12_300652_1020031 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300652 ⟨1020031, by decide⟩ :=
  accepted_of_selected 12 300652 ⟨1020031, by decide⟩ ⟨12, 2, 0, 1020031, 300652, 2485, 65536⟩
    (by decide) selected_cut_37975

theorem selected_cut_37976 : selected 9 ⟨1020064, by decide⟩
    (prefixPartial 12 300653) = some ⟨12, 2, 0, 1020064, 300653, 2241, 65536⟩ := by
  decide +kernel

theorem context_12_300653_1020064 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300653 ⟨1020064, by decide⟩ :=
  accepted_of_selected 12 300653 ⟨1020064, by decide⟩ ⟨12, 2, 0, 1020064, 300653, 2241, 65536⟩
    (by decide) selected_cut_37976

theorem selected_cut_37977 : selected 9 ⟨1020103, by decide⟩
    (prefixPartial 12 300654) = some ⟨12, 2, 0, 1020103, 300654, 2165, 65536⟩ := by
  decide +kernel

theorem context_12_300654_1020103 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300654 ⟨1020103, by decide⟩ :=
  accepted_of_selected 12 300654 ⟨1020103, by decide⟩ ⟨12, 2, 0, 1020103, 300654, 2165, 65536⟩
    (by decide) selected_cut_37977

theorem selected_cut_37978 : selected 9 ⟨1020136, by decide⟩
    (prefixPartial 12 300655) = some ⟨12, 2, 0, 1020136, 300655, 2193, 65536⟩ := by
  decide +kernel

theorem context_12_300655_1020136 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300655 ⟨1020136, by decide⟩ :=
  accepted_of_selected 12 300655 ⟨1020136, by decide⟩ ⟨12, 2, 0, 1020136, 300655, 2193, 65536⟩
    (by decide) selected_cut_37978

theorem unmarked_context_11_75163_1020137 : frontier 10 ⟨1020137, by decide⟩
    (prefixCache 11 75163) (prefixPartial 11 75163) = false := by
  decide +kernel

theorem node_context_11_75163_1020137 : EJMOriginalGlobalDAGData.nodes 10 ⟨1020137, by decide⟩ =
    .split (coordinate 11) (![⟨1020031, by decide⟩,⟨1020064, by decide⟩,⟨1020103, by decide⟩,⟨1020136, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75163_1020137 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75163 ⟨1020137, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75163
    ⟨1020137, by decide⟩ (by decide) (![⟨1020031, by decide⟩,⟨1020064, by decide⟩,⟨1020103, by decide⟩,⟨1020136, by decide⟩]) unmarked_context_11_75163_1020137 node_context_11_75163_1020137
  intro a
  fin_cases a
  · exact context_12_300652_1020031
  · exact context_12_300653_1020064
  · exact context_12_300654_1020103
  · exact context_12_300655_1020136

theorem unmarked_context_10_18790_1020138 : frontier 11 ⟨1020138, by decide⟩
    (prefixCache 10 18790) (prefixPartial 10 18790) = false := by
  decide +kernel

theorem node_context_10_18790_1020138 : EJMOriginalGlobalDAGData.nodes 11 ⟨1020138, by decide⟩ =
    .split (coordinate 10) (![⟨1019747, by decide⟩,⟨1019848, by decide⟩,⟨1019989, by decide⟩,⟨1020137, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18790_1020138 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18790 ⟨1020138, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18790
    ⟨1020138, by decide⟩ (by decide) (![⟨1019747, by decide⟩,⟨1019848, by decide⟩,⟨1019989, by decide⟩,⟨1020137, by decide⟩]) unmarked_context_10_18790_1020138 node_context_10_18790_1020138
  intro a
  fin_cases a
  · exact context_11_75160_1019747
  · exact context_11_75161_1019848
  · exact context_11_75162_1019989
  · exact context_11_75163_1020137

theorem selected_cut_37979 : selected 9 ⟨1020186, by decide⟩
    (prefixPartial 12 300656) = some ⟨12, 2, 0, 1020186, 300656, 2373, 65536⟩ := by
  decide +kernel

theorem context_12_300656_1020186 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300656 ⟨1020186, by decide⟩ :=
  accepted_of_selected 12 300656 ⟨1020186, by decide⟩ ⟨12, 2, 0, 1020186, 300656, 2373, 65536⟩
    (by decide) selected_cut_37979

theorem selected_cut_37980 : selected 9 ⟨1020219, by decide⟩
    (prefixPartial 12 300657) = some ⟨12, 2, 0, 1020219, 300657, 2033, 65536⟩ := by
  decide +kernel

theorem context_12_300657_1020219 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300657 ⟨1020219, by decide⟩ :=
  accepted_of_selected 12 300657 ⟨1020219, by decide⟩ ⟨12, 2, 0, 1020219, 300657, 2033, 65536⟩
    (by decide) selected_cut_37980

theorem selected_cut_37981 : selected 9 ⟨1020244, by decide⟩
    (prefixPartial 12 300658) = some ⟨12, 2, 0, 1020244, 300658, 1925, 65536⟩ := by
  decide +kernel

theorem context_12_300658_1020244 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300658 ⟨1020244, by decide⟩ :=
  accepted_of_selected 12 300658 ⟨1020244, by decide⟩ ⟨12, 2, 0, 1020244, 300658, 1925, 65536⟩
    (by decide) selected_cut_37981

theorem selected_cut_37982 : selected 9 ⟨1020289, by decide⟩
    (prefixPartial 12 300659) = some ⟨12, 2, 0, 1020289, 300659, 2041, 65536⟩ := by
  decide +kernel

theorem context_12_300659_1020289 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300659 ⟨1020289, by decide⟩ :=
  accepted_of_selected 12 300659 ⟨1020289, by decide⟩ ⟨12, 2, 0, 1020289, 300659, 2041, 65536⟩
    (by decide) selected_cut_37982

theorem unmarked_context_11_75164_1020290 : frontier 10 ⟨1020290, by decide⟩
    (prefixCache 11 75164) (prefixPartial 11 75164) = false := by
  decide +kernel

theorem node_context_11_75164_1020290 : EJMOriginalGlobalDAGData.nodes 10 ⟨1020290, by decide⟩ =
    .split (coordinate 11) (![⟨1020186, by decide⟩,⟨1020219, by decide⟩,⟨1020244, by decide⟩,⟨1020289, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75164_1020290 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75164 ⟨1020290, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75164
    ⟨1020290, by decide⟩ (by decide) (![⟨1020186, by decide⟩,⟨1020219, by decide⟩,⟨1020244, by decide⟩,⟨1020289, by decide⟩]) unmarked_context_11_75164_1020290 node_context_11_75164_1020290
  intro a
  fin_cases a
  · exact context_12_300656_1020186
  · exact context_12_300657_1020219
  · exact context_12_300658_1020244
  · exact context_12_300659_1020289

theorem selected_cut_37983 : selected 9 ⟨1020320, by decide⟩
    (prefixPartial 12 300660) = some ⟨12, 2, 0, 1020320, 300660, 1889, 65536⟩ := by
  decide +kernel

theorem context_12_300660_1020320 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300660 ⟨1020320, by decide⟩ :=
  accepted_of_selected 12 300660 ⟨1020320, by decide⟩ ⟨12, 2, 0, 1020320, 300660, 1889, 65536⟩
    (by decide) selected_cut_37983

theorem selected_cut_37984 : selected 9 ⟨691709, by decide⟩
    (prefixPartial 12 300661) = some ⟨12, 1, 0, 691709, 300661, 1, 65536⟩ := by
  decide +kernel

theorem context_12_300661_691709 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300661 ⟨691709, by decide⟩ :=
  accepted_of_selected 12 300661 ⟨691709, by decide⟩ ⟨12, 1, 0, 691709, 300661, 1, 65536⟩
    (by decide) selected_cut_37984

theorem selected_cut_37985 : selected 9 ⟨1020352, by decide⟩
    (prefixPartial 12 300662) = some ⟨12, 2, 0, 1020352, 300662, 1661, 65536⟩ := by
  decide +kernel

theorem context_12_300662_1020352 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300662 ⟨1020352, by decide⟩ :=
  accepted_of_selected 12 300662 ⟨1020352, by decide⟩ ⟨12, 2, 0, 1020352, 300662, 1661, 65536⟩
    (by decide) selected_cut_37985

theorem selected_cut_37986 : selected 9 ⟨1020381, by decide⟩
    (prefixPartial 12 300663) = some ⟨12, 2, 0, 1020381, 300663, 1641, 65536⟩ := by
  decide +kernel

theorem context_12_300663_1020381 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300663 ⟨1020381, by decide⟩ :=
  accepted_of_selected 12 300663 ⟨1020381, by decide⟩ ⟨12, 2, 0, 1020381, 300663, 1641, 65536⟩
    (by decide) selected_cut_37986

theorem unmarked_context_11_75165_1020382 : frontier 10 ⟨1020382, by decide⟩
    (prefixCache 11 75165) (prefixPartial 11 75165) = false := by
  decide +kernel

theorem node_context_11_75165_1020382 : EJMOriginalGlobalDAGData.nodes 10 ⟨1020382, by decide⟩ =
    .split (coordinate 11) (![⟨1020320, by decide⟩,⟨691709, by decide⟩,⟨1020352, by decide⟩,⟨1020381, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75165_1020382 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75165 ⟨1020382, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75165
    ⟨1020382, by decide⟩ (by decide) (![⟨1020320, by decide⟩,⟨691709, by decide⟩,⟨1020352, by decide⟩,⟨1020381, by decide⟩]) unmarked_context_11_75165_1020382 node_context_11_75165_1020382
  intro a
  fin_cases a
  · exact context_12_300660_1020320
  · exact context_12_300661_691709
  · exact context_12_300662_1020352
  · exact context_12_300663_1020381

theorem selected_cut_37987 : selected 9 ⟨1020424, by decide⟩
    (prefixPartial 12 300664) = some ⟨12, 2, 0, 1020424, 300664, 2133, 65536⟩ := by
  decide +kernel

theorem context_12_300664_1020424 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300664 ⟨1020424, by decide⟩ :=
  accepted_of_selected 12 300664 ⟨1020424, by decide⟩ ⟨12, 2, 0, 1020424, 300664, 2133, 65536⟩
    (by decide) selected_cut_37987

theorem selected_cut_37988 : selected 9 ⟨1020463, by decide⟩
    (prefixPartial 12 300665) = some ⟨12, 2, 0, 1020463, 300665, 1937, 65536⟩ := by
  decide +kernel

theorem context_12_300665_1020463 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300665 ⟨1020463, by decide⟩ :=
  accepted_of_selected 12 300665 ⟨1020463, by decide⟩ ⟨12, 2, 0, 1020463, 300665, 1937, 65536⟩
    (by decide) selected_cut_37988

theorem selected_cut_37989 : selected 9 ⟨893903, by decide⟩
    (prefixPartial 12 300666) = some ⟨12, 1, 0, 893903, 300666, 1, 65536⟩ := by
  decide +kernel

theorem context_12_300666_893903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300666 ⟨893903, by decide⟩ :=
  accepted_of_selected 12 300666 ⟨893903, by decide⟩ ⟨12, 1, 0, 893903, 300666, 1, 65536⟩
    (by decide) selected_cut_37989

theorem selected_cut_37990 : selected 9 ⟨1020507, by decide⟩
    (prefixPartial 12 300667) = some ⟨12, 2, 0, 1020507, 300667, 2085, 65536⟩ := by
  decide +kernel

theorem context_12_300667_1020507 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300667 ⟨1020507, by decide⟩ :=
  accepted_of_selected 12 300667 ⟨1020507, by decide⟩ ⟨12, 2, 0, 1020507, 300667, 2085, 65536⟩
    (by decide) selected_cut_37990

theorem unmarked_context_11_75166_1020508 : frontier 10 ⟨1020508, by decide⟩
    (prefixCache 11 75166) (prefixPartial 11 75166) = false := by
  decide +kernel

theorem node_context_11_75166_1020508 : EJMOriginalGlobalDAGData.nodes 10 ⟨1020508, by decide⟩ =
    .split (coordinate 11) (![⟨1020424, by decide⟩,⟨1020463, by decide⟩,⟨893903, by decide⟩,⟨1020507, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75166_1020508 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75166 ⟨1020508, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75166
    ⟨1020508, by decide⟩ (by decide) (![⟨1020424, by decide⟩,⟨1020463, by decide⟩,⟨893903, by decide⟩,⟨1020507, by decide⟩]) unmarked_context_11_75166_1020508 node_context_11_75166_1020508
  intro a
  fin_cases a
  · exact context_12_300664_1020424
  · exact context_12_300665_1020463
  · exact context_12_300666_893903
  · exact context_12_300667_1020507

theorem selected_cut_37991 : selected 9 ⟨1020546, by decide⟩
    (prefixPartial 12 300668) = some ⟨12, 2, 0, 1020546, 300668, 2261, 65536⟩ := by
  decide +kernel

theorem context_12_300668_1020546 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300668 ⟨1020546, by decide⟩ :=
  accepted_of_selected 12 300668 ⟨1020546, by decide⟩ ⟨12, 2, 0, 1020546, 300668, 2261, 65536⟩
    (by decide) selected_cut_37991

theorem selected_cut_37992 : selected 9 ⟨1020579, by decide⟩
    (prefixPartial 12 300669) = some ⟨12, 2, 0, 1020579, 300669, 1989, 65536⟩ := by
  decide +kernel

theorem context_12_300669_1020579 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300669 ⟨1020579, by decide⟩ :=
  accepted_of_selected 12 300669 ⟨1020579, by decide⟩ ⟨12, 2, 0, 1020579, 300669, 1989, 65536⟩
    (by decide) selected_cut_37992

theorem selected_cut_37993 : selected 9 ⟨1020614, by decide⟩
    (prefixPartial 12 300670) = some ⟨12, 2, 0, 1020614, 300670, 1961, 65536⟩ := by
  decide +kernel

theorem context_12_300670_1020614 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300670 ⟨1020614, by decide⟩ :=
  accepted_of_selected 12 300670 ⟨1020614, by decide⟩ ⟨12, 2, 0, 1020614, 300670, 1961, 65536⟩
    (by decide) selected_cut_37993

theorem selected_cut_37994 : selected 9 ⟨1020677, by decide⟩
    (prefixPartial 12 300671) = some ⟨12, 2, 0, 1020677, 300671, 745, 65536⟩ := by
  decide +kernel

theorem context_12_300671_1020677 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300671 ⟨1020677, by decide⟩ :=
  accepted_of_selected 12 300671 ⟨1020677, by decide⟩ ⟨12, 2, 0, 1020677, 300671, 745, 65536⟩
    (by decide) selected_cut_37994

theorem unmarked_context_11_75167_1020678 : frontier 10 ⟨1020678, by decide⟩
    (prefixCache 11 75167) (prefixPartial 11 75167) = false := by
  decide +kernel

theorem node_context_11_75167_1020678 : EJMOriginalGlobalDAGData.nodes 10 ⟨1020678, by decide⟩ =
    .split (coordinate 11) (![⟨1020546, by decide⟩,⟨1020579, by decide⟩,⟨1020614, by decide⟩,⟨1020677, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75167_1020678 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75167 ⟨1020678, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75167
    ⟨1020678, by decide⟩ (by decide) (![⟨1020546, by decide⟩,⟨1020579, by decide⟩,⟨1020614, by decide⟩,⟨1020677, by decide⟩]) unmarked_context_11_75167_1020678 node_context_11_75167_1020678
  intro a
  fin_cases a
  · exact context_12_300668_1020546
  · exact context_12_300669_1020579
  · exact context_12_300670_1020614
  · exact context_12_300671_1020677

theorem unmarked_context_10_18791_1020679 : frontier 11 ⟨1020679, by decide⟩
    (prefixCache 10 18791) (prefixPartial 10 18791) = false := by
  decide +kernel

theorem node_context_10_18791_1020679 : EJMOriginalGlobalDAGData.nodes 11 ⟨1020679, by decide⟩ =
    .split (coordinate 10) (![⟨1020290, by decide⟩,⟨1020382, by decide⟩,⟨1020508, by decide⟩,⟨1020678, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18791_1020679 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18791 ⟨1020679, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18791
    ⟨1020679, by decide⟩ (by decide) (![⟨1020290, by decide⟩,⟨1020382, by decide⟩,⟨1020508, by decide⟩,⟨1020678, by decide⟩]) unmarked_context_10_18791_1020679 node_context_10_18791_1020679
  intro a
  fin_cases a
  · exact context_11_75164_1020290
  · exact context_11_75165_1020382
  · exact context_11_75166_1020508
  · exact context_11_75167_1020678

theorem unmarked_context_9_4697_1020680 : frontier 12 ⟨1020680, by decide⟩
    (prefixCache 9 4697) (prefixPartial 9 4697) = false := by
  decide +kernel

theorem node_context_9_4697_1020680 : EJMOriginalGlobalDAGData.nodes 12 ⟨1020680, by decide⟩ =
    .split (coordinate 9) (![⟨1019593, by decide⟩,⟨893098, by decide⟩,⟨1020138, by decide⟩,⟨1020679, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4697_1020680 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4697 ⟨1020680, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4697
    ⟨1020680, by decide⟩ (by decide) (![⟨1019593, by decide⟩,⟨893098, by decide⟩,⟨1020138, by decide⟩,⟨1020679, by decide⟩]) unmarked_context_9_4697_1020680 node_context_9_4697_1020680
  intro a
  fin_cases a
  · exact context_10_18788_1019593
  · exact context_10_18789_893098
  · exact context_10_18790_1020138
  · exact context_10_18791_1020679

theorem selected_cut_37995 : selected 10 ⟨1020817, by decide⟩
    (prefixPartial 11 75168) = some ⟨11, 2, 0, 1020817, 75168, 3973, 262144⟩ := by
  decide +kernel

theorem context_11_75168_1020817 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75168 ⟨1020817, by decide⟩ :=
  accepted_of_selected 11 75168 ⟨1020817, by decide⟩ ⟨11, 2, 0, 1020817, 75168, 3973, 262144⟩
    (by decide) selected_cut_37995

theorem selected_cut_37996 : selected 9 ⟨1020849, by decide⟩
    (prefixPartial 12 300676) = some ⟨12, 2, 0, 1020849, 300676, 1637, 65536⟩ := by
  decide +kernel

theorem context_12_300676_1020849 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300676 ⟨1020849, by decide⟩ :=
  accepted_of_selected 12 300676 ⟨1020849, by decide⟩ ⟨12, 2, 0, 1020849, 300676, 1637, 65536⟩
    (by decide) selected_cut_37996

theorem selected_cut_37997 : selected 9 ⟨1020867, by decide⟩
    (prefixPartial 12 300677) = some ⟨12, 2, 0, 1020867, 300677, 1321, 65536⟩ := by
  decide +kernel

theorem context_12_300677_1020867 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300677 ⟨1020867, by decide⟩ :=
  accepted_of_selected 12 300677 ⟨1020867, by decide⟩ ⟨12, 2, 0, 1020867, 300677, 1321, 65536⟩
    (by decide) selected_cut_37997

theorem selected_cut_37998 : selected 9 ⟨984676, by decide⟩
    (prefixPartial 12 300678) = some ⟨12, 1, 0, 984676, 300678, 1, 65536⟩ := by
  decide +kernel

theorem context_12_300678_984676 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300678 ⟨984676, by decide⟩ :=
  accepted_of_selected 12 300678 ⟨984676, by decide⟩ ⟨12, 1, 0, 984676, 300678, 1, 65536⟩
    (by decide) selected_cut_37998

theorem selected_cut_37999 : selected 9 ⟨1020891, by decide⟩
    (prefixPartial 12 300679) = some ⟨12, 2, 0, 1020891, 300679, 1397, 65536⟩ := by
  decide +kernel

theorem context_12_300679_1020891 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300679 ⟨1020891, by decide⟩ :=
  accepted_of_selected 12 300679 ⟨1020891, by decide⟩ ⟨12, 2, 0, 1020891, 300679, 1397, 65536⟩
    (by decide) selected_cut_37999

theorem unmarked_context_11_75169_1020892 : frontier 10 ⟨1020892, by decide⟩
    (prefixCache 11 75169) (prefixPartial 11 75169) = false := by
  decide +kernel

theorem node_context_11_75169_1020892 : EJMOriginalGlobalDAGData.nodes 10 ⟨1020892, by decide⟩ =
    .split (coordinate 11) (![⟨1020849, by decide⟩,⟨1020867, by decide⟩,⟨984676, by decide⟩,⟨1020891, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75169_1020892 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75169 ⟨1020892, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75169
    ⟨1020892, by decide⟩ (by decide) (![⟨1020849, by decide⟩,⟨1020867, by decide⟩,⟨984676, by decide⟩,⟨1020891, by decide⟩]) unmarked_context_11_75169_1020892 node_context_11_75169_1020892
  intro a
  fin_cases a
  · exact context_12_300676_1020849
  · exact context_12_300677_1020867
  · exact context_12_300678_984676
  · exact context_12_300679_1020891

theorem selected_cut_38000 : selected 9 ⟨1020925, by decide⟩
    (prefixPartial 12 300680) = some ⟨12, 2, 0, 1020925, 300680, 1649, 65536⟩ := by
  decide +kernel

theorem context_12_300680_1020925 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300680 ⟨1020925, by decide⟩ :=
  accepted_of_selected 12 300680 ⟨1020925, by decide⟩ ⟨12, 2, 0, 1020925, 300680, 1649, 65536⟩
    (by decide) selected_cut_38000

theorem selected_cut_38001 : selected 9 ⟨1020948, by decide⟩
    (prefixPartial 12 300681) = some ⟨12, 2, 0, 1020948, 300681, 1293, 65536⟩ := by
  decide +kernel

theorem context_12_300681_1020948 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300681 ⟨1020948, by decide⟩ :=
  accepted_of_selected 12 300681 ⟨1020948, by decide⟩ ⟨12, 2, 0, 1020948, 300681, 1293, 65536⟩
    (by decide) selected_cut_38001

theorem selected_cut_38002 : selected 9 ⟨984676, by decide⟩
    (prefixPartial 12 300682) = some ⟨12, 1, 0, 984676, 300682, 1, 65536⟩ := by
  decide +kernel

theorem context_12_300682_984676 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300682 ⟨984676, by decide⟩ :=
  accepted_of_selected 12 300682 ⟨984676, by decide⟩ ⟨12, 1, 0, 984676, 300682, 1, 65536⟩
    (by decide) selected_cut_38002

theorem selected_cut_38003 : selected 9 ⟨1020975, by decide⟩
    (prefixPartial 12 300683) = some ⟨12, 2, 0, 1020975, 300683, 1409, 65536⟩ := by
  decide +kernel

theorem context_12_300683_1020975 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300683 ⟨1020975, by decide⟩ :=
  accepted_of_selected 12 300683 ⟨1020975, by decide⟩ ⟨12, 2, 0, 1020975, 300683, 1409, 65536⟩
    (by decide) selected_cut_38003

theorem unmarked_context_11_75170_1020976 : frontier 10 ⟨1020976, by decide⟩
    (prefixCache 11 75170) (prefixPartial 11 75170) = false := by
  decide +kernel

theorem node_context_11_75170_1020976 : EJMOriginalGlobalDAGData.nodes 10 ⟨1020976, by decide⟩ =
    .split (coordinate 11) (![⟨1020925, by decide⟩,⟨1020948, by decide⟩,⟨984676, by decide⟩,⟨1020975, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75170_1020976 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75170 ⟨1020976, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75170
    ⟨1020976, by decide⟩ (by decide) (![⟨1020925, by decide⟩,⟨1020948, by decide⟩,⟨984676, by decide⟩,⟨1020975, by decide⟩]) unmarked_context_11_75170_1020976 node_context_11_75170_1020976
  intro a
  fin_cases a
  · exact context_12_300680_1020925
  · exact context_12_300681_1020948
  · exact context_12_300682_984676
  · exact context_12_300683_1020975

theorem selected_cut_38004 : selected 9 ⟨1021003, by decide⟩
    (prefixPartial 12 300684) = some ⟨12, 2, 0, 1021003, 300684, 1761, 65536⟩ := by
  decide +kernel

theorem context_12_300684_1021003 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300684 ⟨1021003, by decide⟩ :=
  accepted_of_selected 12 300684 ⟨1021003, by decide⟩ ⟨12, 2, 0, 1021003, 300684, 1761, 65536⟩
    (by decide) selected_cut_38004

theorem selected_cut_38005 : selected 9 ⟨1021027, by decide⟩
    (prefixPartial 12 300685) = some ⟨12, 2, 0, 1021027, 300685, 1469, 65536⟩ := by
  decide +kernel

theorem context_12_300685_1021027 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300685 ⟨1021027, by decide⟩ :=
  accepted_of_selected 12 300685 ⟨1021027, by decide⟩ ⟨12, 2, 0, 1021027, 300685, 1469, 65536⟩
    (by decide) selected_cut_38005

theorem selected_cut_38006 : selected 9 ⟨984676, by decide⟩
    (prefixPartial 12 300686) = some ⟨12, 1, 0, 984676, 300686, 1, 65536⟩ := by
  decide +kernel

theorem context_12_300686_984676 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300686 ⟨984676, by decide⟩ :=
  accepted_of_selected 12 300686 ⟨984676, by decide⟩ ⟨12, 1, 0, 984676, 300686, 1, 65536⟩
    (by decide) selected_cut_38006

theorem selected_cut_38007 : selected 9 ⟨1021057, by decide⟩
    (prefixPartial 12 300687) = some ⟨12, 2, 0, 1021057, 300687, 1469, 65536⟩ := by
  decide +kernel

theorem context_12_300687_1021057 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300687 ⟨1021057, by decide⟩ :=
  accepted_of_selected 12 300687 ⟨1021057, by decide⟩ ⟨12, 2, 0, 1021057, 300687, 1469, 65536⟩
    (by decide) selected_cut_38007

theorem unmarked_context_11_75171_1021058 : frontier 10 ⟨1021058, by decide⟩
    (prefixCache 11 75171) (prefixPartial 11 75171) = false := by
  decide +kernel

theorem node_context_11_75171_1021058 : EJMOriginalGlobalDAGData.nodes 10 ⟨1021058, by decide⟩ =
    .split (coordinate 11) (![⟨1021003, by decide⟩,⟨1021027, by decide⟩,⟨984676, by decide⟩,⟨1021057, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75171_1021058 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75171 ⟨1021058, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75171
    ⟨1021058, by decide⟩ (by decide) (![⟨1021003, by decide⟩,⟨1021027, by decide⟩,⟨984676, by decide⟩,⟨1021057, by decide⟩]) unmarked_context_11_75171_1021058 node_context_11_75171_1021058
  intro a
  fin_cases a
  · exact context_12_300684_1021003
  · exact context_12_300685_1021027
  · exact context_12_300686_984676
  · exact context_12_300687_1021057

theorem unmarked_context_10_18792_1021059 : frontier 11 ⟨1021059, by decide⟩
    (prefixCache 10 18792) (prefixPartial 10 18792) = false := by
  decide +kernel

theorem node_context_10_18792_1021059 : EJMOriginalGlobalDAGData.nodes 11 ⟨1021059, by decide⟩ =
    .split (coordinate 10) (![⟨1020817, by decide⟩,⟨1020892, by decide⟩,⟨1020976, by decide⟩,⟨1021058, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18792_1021059 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18792 ⟨1021059, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18792
    ⟨1021059, by decide⟩ (by decide) (![⟨1020817, by decide⟩,⟨1020892, by decide⟩,⟨1020976, by decide⟩,⟨1021058, by decide⟩]) unmarked_context_10_18792_1021059 node_context_10_18792_1021059
  intro a
  fin_cases a
  · exact context_11_75168_1020817
  · exact context_11_75169_1020892
  · exact context_11_75170_1020976
  · exact context_11_75171_1021058

theorem selected_cut_38008 : selected 10 ⟨1021130, by decide⟩
    (prefixPartial 11 75172) = some ⟨11, 2, 0, 1021130, 75172, 3725, 262144⟩ := by
  decide +kernel

theorem context_11_75172_1021130 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75172 ⟨1021130, by decide⟩ :=
  accepted_of_selected 11 75172 ⟨1021130, by decide⟩ ⟨11, 2, 0, 1021130, 75172, 3725, 262144⟩
    (by decide) selected_cut_38008

theorem selected_cut_38009 : selected 10 ⟨892405, by decide⟩
    (prefixPartial 11 75173) = some ⟨11, 1, 0, 892405, 75173, 1, 262144⟩ := by
  decide +kernel

theorem context_11_75173_892405 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75173 ⟨892405, by decide⟩ :=
  accepted_of_selected 11 75173 ⟨892405, by decide⟩ ⟨11, 1, 0, 892405, 75173, 1, 262144⟩
    (by decide) selected_cut_38009

theorem selected_cut_38010 : selected 10 ⟨1021185, by decide⟩
    (prefixPartial 11 75174) = some ⟨11, 2, 0, 1021185, 75174, 3117, 262144⟩ := by
  decide +kernel

theorem context_11_75174_1021185 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75174 ⟨1021185, by decide⟩ :=
  accepted_of_selected 11 75174 ⟨1021185, by decide⟩ ⟨11, 2, 0, 1021185, 75174, 3117, 262144⟩
    (by decide) selected_cut_38010

theorem selected_cut_38011 : selected 10 ⟨1021244, by decide⟩
    (prefixPartial 11 75175) = some ⟨11, 2, 0, 1021244, 75175, 3653, 262144⟩ := by
  decide +kernel

theorem context_11_75175_1021244 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75175 ⟨1021244, by decide⟩ :=
  accepted_of_selected 11 75175 ⟨1021244, by decide⟩ ⟨11, 2, 0, 1021244, 75175, 3653, 262144⟩
    (by decide) selected_cut_38011

theorem unmarked_context_10_18793_1021245 : frontier 11 ⟨1021245, by decide⟩
    (prefixCache 10 18793) (prefixPartial 10 18793) = false := by
  decide +kernel

theorem node_context_10_18793_1021245 : EJMOriginalGlobalDAGData.nodes 11 ⟨1021245, by decide⟩ =
    .split (coordinate 10) (![⟨1021130, by decide⟩,⟨892405, by decide⟩,⟨1021185, by decide⟩,⟨1021244, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18793_1021245 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18793 ⟨1021245, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18793
    ⟨1021245, by decide⟩ (by decide) (![⟨1021130, by decide⟩,⟨892405, by decide⟩,⟨1021185, by decide⟩,⟨1021244, by decide⟩]) unmarked_context_10_18793_1021245 node_context_10_18793_1021245
  intro a
  fin_cases a
  · exact context_11_75172_1021130
  · exact context_11_75173_892405
  · exact context_11_75174_1021185
  · exact context_11_75175_1021244

theorem selected_cut_38012 : selected 10 ⟨1021299, by decide⟩
    (prefixPartial 11 75176) = some ⟨11, 2, 0, 1021299, 75176, 3069, 262144⟩ := by
  decide +kernel

theorem context_11_75176_1021299 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75176 ⟨1021299, by decide⟩ :=
  accepted_of_selected 11 75176 ⟨1021299, by decide⟩ ⟨11, 2, 0, 1021299, 75176, 3069, 262144⟩
    (by decide) selected_cut_38012

theorem selected_cut_38013 : selected 10 ⟨1021336, by decide⟩
    (prefixPartial 11 75177) = some ⟨11, 2, 0, 1021336, 75177, 2409, 262144⟩ := by
  decide +kernel

theorem context_11_75177_1021336 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75177 ⟨1021336, by decide⟩ :=
  accepted_of_selected 11 75177 ⟨1021336, by decide⟩ ⟨11, 2, 0, 1021336, 75177, 2409, 262144⟩
    (by decide) selected_cut_38013

theorem selected_cut_38014 : selected 10 ⟨906566, by decide⟩
    (prefixPartial 11 75178) = some ⟨11, 1, 0, 906566, 75178, 1, 262144⟩ := by
  decide +kernel

theorem context_11_75178_906566 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75178 ⟨906566, by decide⟩ :=
  accepted_of_selected 11 75178 ⟨906566, by decide⟩ ⟨11, 1, 0, 906566, 75178, 1, 262144⟩
    (by decide) selected_cut_38014

theorem selected_cut_38015 : selected 10 ⟨1021374, by decide⟩
    (prefixPartial 11 75179) = some ⟨11, 2, 0, 1021374, 75179, 2685, 262144⟩ := by
  decide +kernel

theorem context_11_75179_1021374 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75179 ⟨1021374, by decide⟩ :=
  accepted_of_selected 11 75179 ⟨1021374, by decide⟩ ⟨11, 2, 0, 1021374, 75179, 2685, 262144⟩
    (by decide) selected_cut_38015

theorem unmarked_context_10_18794_1021375 : frontier 11 ⟨1021375, by decide⟩
    (prefixCache 10 18794) (prefixPartial 10 18794) = false := by
  decide +kernel

theorem node_context_10_18794_1021375 : EJMOriginalGlobalDAGData.nodes 11 ⟨1021375, by decide⟩ =
    .split (coordinate 10) (![⟨1021299, by decide⟩,⟨1021336, by decide⟩,⟨906566, by decide⟩,⟨1021374, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18794_1021375 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18794 ⟨1021375, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18794
    ⟨1021375, by decide⟩ (by decide) (![⟨1021299, by decide⟩,⟨1021336, by decide⟩,⟨906566, by decide⟩,⟨1021374, by decide⟩]) unmarked_context_10_18794_1021375 node_context_10_18794_1021375
  intro a
  fin_cases a
  · exact context_11_75176_1021299
  · exact context_11_75177_1021336
  · exact context_11_75178_906566
  · exact context_11_75179_1021374

theorem selected_cut_38016 : selected 10 ⟨1021422, by decide⟩
    (prefixPartial 11 75180) = some ⟨11, 2, 0, 1021422, 75180, 2489, 262144⟩ := by
  decide +kernel

theorem context_11_75180_1021422 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75180 ⟨1021422, by decide⟩ :=
  accepted_of_selected 11 75180 ⟨1021422, by decide⟩ ⟨11, 2, 0, 1021422, 75180, 2489, 262144⟩
    (by decide) selected_cut_38016

theorem selected_cut_38017 : selected 10 ⟨1021456, by decide⟩
    (prefixPartial 11 75181) = some ⟨11, 2, 0, 1021456, 75181, 2145, 262144⟩ := by
  decide +kernel

theorem context_11_75181_1021456 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75181 ⟨1021456, by decide⟩ :=
  accepted_of_selected 11 75181 ⟨1021456, by decide⟩ ⟨11, 2, 0, 1021456, 75181, 2145, 262144⟩
    (by decide) selected_cut_38017

theorem selected_cut_38018 : selected 10 ⟨1021490, by decide⟩
    (prefixPartial 11 75182) = some ⟨11, 2, 0, 1021490, 75182, 1857, 262144⟩ := by
  decide +kernel

theorem context_11_75182_1021490 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75182 ⟨1021490, by decide⟩ :=
  accepted_of_selected 11 75182 ⟨1021490, by decide⟩ ⟨11, 2, 0, 1021490, 75182, 1857, 262144⟩
    (by decide) selected_cut_38018

theorem selected_cut_38019 : selected 10 ⟨1021529, by decide⟩
    (prefixPartial 11 75183) = some ⟨11, 2, 0, 1021529, 75183, 1713, 262144⟩ := by
  decide +kernel

theorem context_11_75183_1021529 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75183 ⟨1021529, by decide⟩ :=
  accepted_of_selected 11 75183 ⟨1021529, by decide⟩ ⟨11, 2, 0, 1021529, 75183, 1713, 262144⟩
    (by decide) selected_cut_38019

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
