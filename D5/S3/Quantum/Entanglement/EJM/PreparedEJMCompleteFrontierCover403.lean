/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover402
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_38692 : selected 9 ⟨1045484, by decide⟩
    (prefixPartial 12 301879) = some ⟨12, 2, 0, 1045484, 301879, 2821, 65536⟩ := by
  decide +kernel

theorem context_12_301879_1045484 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301879 ⟨1045484, by decide⟩ :=
  accepted_of_selected 12 301879 ⟨1045484, by decide⟩ ⟨12, 2, 0, 1045484, 301879, 2821, 65536⟩
    (by decide) selected_cut_38692

theorem unmarked_context_11_75469_1045485 : frontier 10 ⟨1045485, by decide⟩
    (prefixCache 11 75469) (prefixPartial 11 75469) = false := by
  decide +kernel

theorem node_context_11_75469_1045485 : EJMOriginalGlobalDAGData.nodes 10 ⟨1045485, by decide⟩ =
    .split (coordinate 11) (![⟨1045313, by decide⟩,⟨1045378, by decide⟩,⟨1045436, by decide⟩,⟨1045484, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75469_1045485 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75469 ⟨1045485, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75469
    ⟨1045485, by decide⟩ (by decide) (![⟨1045313, by decide⟩,⟨1045378, by decide⟩,⟨1045436, by decide⟩,⟨1045484, by decide⟩]) unmarked_context_11_75469_1045485 node_context_11_75469_1045485
  intro a
  fin_cases a
  · exact context_12_301876_1045313
  · exact context_12_301877_1045378
  · exact context_12_301878_1045436
  · exact context_12_301879_1045484

theorem selected_cut_38693 : selected 9 ⟨1045534, by decide⟩
    (prefixPartial 12 301880) = some ⟨12, 2, 0, 1045534, 301880, 2741, 65536⟩ := by
  decide +kernel

theorem context_12_301880_1045534 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301880 ⟨1045534, by decide⟩ :=
  accepted_of_selected 12 301880 ⟨1045534, by decide⟩ ⟨12, 2, 0, 1045534, 301880, 2741, 65536⟩
    (by decide) selected_cut_38693

theorem selected_cut_38694 : selected 9 ⟨1045583, by decide⟩
    (prefixPartial 12 301881) = some ⟨12, 2, 0, 1045583, 301881, 3261, 65536⟩ := by
  decide +kernel

theorem context_12_301881_1045583 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301881 ⟨1045583, by decide⟩ :=
  accepted_of_selected 12 301881 ⟨1045583, by decide⟩ ⟨12, 2, 0, 1045583, 301881, 3261, 65536⟩
    (by decide) selected_cut_38694

theorem selected_cut_38695 : selected 9 ⟨1045633, by decide⟩
    (prefixPartial 12 301882) = some ⟨12, 2, 0, 1045633, 301882, 2861, 65536⟩ := by
  decide +kernel

theorem context_12_301882_1045633 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301882 ⟨1045633, by decide⟩ :=
  accepted_of_selected 12 301882 ⟨1045633, by decide⟩ ⟨12, 2, 0, 1045633, 301882, 2861, 65536⟩
    (by decide) selected_cut_38695

theorem selected_cut_38696 : selected 9 ⟨1045681, by decide⟩
    (prefixPartial 12 301883) = some ⟨12, 2, 0, 1045681, 301883, 2905, 65536⟩ := by
  decide +kernel

theorem context_12_301883_1045681 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301883 ⟨1045681, by decide⟩ :=
  accepted_of_selected 12 301883 ⟨1045681, by decide⟩ ⟨12, 2, 0, 1045681, 301883, 2905, 65536⟩
    (by decide) selected_cut_38696

theorem unmarked_context_11_75470_1045682 : frontier 10 ⟨1045682, by decide⟩
    (prefixCache 11 75470) (prefixPartial 11 75470) = false := by
  decide +kernel

theorem node_context_11_75470_1045682 : EJMOriginalGlobalDAGData.nodes 10 ⟨1045682, by decide⟩ =
    .split (coordinate 11) (![⟨1045534, by decide⟩,⟨1045583, by decide⟩,⟨1045633, by decide⟩,⟨1045681, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75470_1045682 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75470 ⟨1045682, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75470
    ⟨1045682, by decide⟩ (by decide) (![⟨1045534, by decide⟩,⟨1045583, by decide⟩,⟨1045633, by decide⟩,⟨1045681, by decide⟩]) unmarked_context_11_75470_1045682 node_context_11_75470_1045682
  intro a
  fin_cases a
  · exact context_12_301880_1045534
  · exact context_12_301881_1045583
  · exact context_12_301882_1045633
  · exact context_12_301883_1045681

theorem selected_cut_38697 : selected 9 ⟨1045716, by decide⟩
    (prefixPartial 12 301884) = some ⟨12, 2, 0, 1045716, 301884, 2429, 65536⟩ := by
  decide +kernel

theorem context_12_301884_1045716 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301884 ⟨1045716, by decide⟩ :=
  accepted_of_selected 12 301884 ⟨1045716, by decide⟩ ⟨12, 2, 0, 1045716, 301884, 2429, 65536⟩
    (by decide) selected_cut_38697

theorem selected_cut_38698 : selected 9 ⟨1045781, by decide⟩
    (prefixPartial 12 301885) = some ⟨12, 2, 0, 1045781, 301885, 3069, 65536⟩ := by
  decide +kernel

theorem context_12_301885_1045781 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301885 ⟨1045781, by decide⟩ :=
  accepted_of_selected 12 301885 ⟨1045781, by decide⟩ ⟨12, 2, 0, 1045781, 301885, 3069, 65536⟩
    (by decide) selected_cut_38698

theorem selected_cut_38699 : selected 9 ⟨1045832, by decide⟩
    (prefixPartial 12 301886) = some ⟨12, 2, 0, 1045832, 301886, 2805, 65536⟩ := by
  decide +kernel

theorem context_12_301886_1045832 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301886 ⟨1045832, by decide⟩ :=
  accepted_of_selected 12 301886 ⟨1045832, by decide⟩ ⟨12, 2, 0, 1045832, 301886, 2805, 65536⟩
    (by decide) selected_cut_38699

theorem selected_cut_38700 : selected 9 ⟨762109, by decide⟩
    (prefixPartial 12 301887) = some ⟨12, 1, 0, 762109, 301887, 1, 65536⟩ := by
  decide +kernel

theorem context_12_301887_762109 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301887 ⟨762109, by decide⟩ :=
  accepted_of_selected 12 301887 ⟨762109, by decide⟩ ⟨12, 1, 0, 762109, 301887, 1, 65536⟩
    (by decide) selected_cut_38700

theorem unmarked_context_11_75471_1045833 : frontier 10 ⟨1045833, by decide⟩
    (prefixCache 11 75471) (prefixPartial 11 75471) = false := by
  decide +kernel

theorem node_context_11_75471_1045833 : EJMOriginalGlobalDAGData.nodes 10 ⟨1045833, by decide⟩ =
    .split (coordinate 11) (![⟨1045716, by decide⟩,⟨1045781, by decide⟩,⟨1045832, by decide⟩,⟨762109, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75471_1045833 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75471 ⟨1045833, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75471
    ⟨1045833, by decide⟩ (by decide) (![⟨1045716, by decide⟩,⟨1045781, by decide⟩,⟨1045832, by decide⟩,⟨762109, by decide⟩]) unmarked_context_11_75471_1045833 node_context_11_75471_1045833
  intro a
  fin_cases a
  · exact context_12_301884_1045716
  · exact context_12_301885_1045781
  · exact context_12_301886_1045832
  · exact context_12_301887_762109

theorem unmarked_context_10_18867_1045834 : frontier 11 ⟨1045834, by decide⟩
    (prefixCache 10 18867) (prefixPartial 10 18867) = false := by
  decide +kernel

theorem node_context_10_18867_1045834 : EJMOriginalGlobalDAGData.nodes 11 ⟨1045834, by decide⟩ =
    .split (coordinate 10) (![⟨1045262, by decide⟩,⟨1045485, by decide⟩,⟨1045682, by decide⟩,⟨1045833, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18867_1045834 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18867 ⟨1045834, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18867
    ⟨1045834, by decide⟩ (by decide) (![⟨1045262, by decide⟩,⟨1045485, by decide⟩,⟨1045682, by decide⟩,⟨1045833, by decide⟩]) unmarked_context_10_18867_1045834 node_context_10_18867_1045834
  intro a
  fin_cases a
  · exact context_11_75468_1045262
  · exact context_11_75469_1045485
  · exact context_11_75470_1045682
  · exact context_11_75471_1045833

theorem unmarked_context_9_4716_1045835 : frontier 12 ⟨1045835, by decide⟩
    (prefixCache 9 4716) (prefixPartial 9 4716) = false := by
  decide +kernel

theorem node_context_9_4716_1045835 : EJMOriginalGlobalDAGData.nodes 12 ⟨1045835, by decide⟩ =
    .split (coordinate 9) (![⟨1043824, by decide⟩,⟨1044546, by decide⟩,⟨1045073, by decide⟩,⟨1045834, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4716_1045835 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4716 ⟨1045835, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4716
    ⟨1045835, by decide⟩ (by decide) (![⟨1043824, by decide⟩,⟨1044546, by decide⟩,⟨1045073, by decide⟩,⟨1045834, by decide⟩]) unmarked_context_9_4716_1045835 node_context_9_4716_1045835
  intro a
  fin_cases a
  · exact context_10_18864_1043824
  · exact context_10_18865_1044546
  · exact context_10_18866_1045073
  · exact context_10_18867_1045834

theorem selected_cut_38701 : selected 9 ⟨1045881, by decide⟩
    (prefixPartial 12 301888) = some ⟨12, 2, 0, 1045881, 301888, 2741, 65536⟩ := by
  decide +kernel

theorem context_12_301888_1045881 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301888 ⟨1045881, by decide⟩ :=
  accepted_of_selected 12 301888 ⟨1045881, by decide⟩ ⟨12, 2, 0, 1045881, 301888, 2741, 65536⟩
    (by decide) selected_cut_38701

theorem selected_cut_38702 : selected 9 ⟨1045923, by decide⟩
    (prefixPartial 12 301889) = some ⟨12, 2, 0, 1045923, 301889, 2529, 65536⟩ := by
  decide +kernel

theorem context_12_301889_1045923 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301889 ⟨1045923, by decide⟩ :=
  accepted_of_selected 12 301889 ⟨1045923, by decide⟩ ⟨12, 2, 0, 1045923, 301889, 2529, 65536⟩
    (by decide) selected_cut_38702

theorem selected_cut_38703 : selected 9 ⟨1045959, by decide⟩
    (prefixPartial 12 301890) = some ⟨12, 2, 0, 1045959, 301890, 2381, 65536⟩ := by
  decide +kernel

theorem context_12_301890_1045959 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301890 ⟨1045959, by decide⟩ :=
  accepted_of_selected 12 301890 ⟨1045959, by decide⟩ ⟨12, 2, 0, 1045959, 301890, 2381, 65536⟩
    (by decide) selected_cut_38703

theorem selected_cut_38704 : selected 9 ⟨1045991, by decide⟩
    (prefixPartial 12 301891) = some ⟨12, 2, 0, 1045991, 301891, 2281, 65536⟩ := by
  decide +kernel

theorem context_12_301891_1045991 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301891 ⟨1045991, by decide⟩ :=
  accepted_of_selected 12 301891 ⟨1045991, by decide⟩ ⟨12, 2, 0, 1045991, 301891, 2281, 65536⟩
    (by decide) selected_cut_38704

theorem unmarked_context_11_75472_1045992 : frontier 10 ⟨1045992, by decide⟩
    (prefixCache 11 75472) (prefixPartial 11 75472) = false := by
  decide +kernel

theorem node_context_11_75472_1045992 : EJMOriginalGlobalDAGData.nodes 10 ⟨1045992, by decide⟩ =
    .split (coordinate 11) (![⟨1045881, by decide⟩,⟨1045923, by decide⟩,⟨1045959, by decide⟩,⟨1045991, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75472_1045992 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75472 ⟨1045992, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75472
    ⟨1045992, by decide⟩ (by decide) (![⟨1045881, by decide⟩,⟨1045923, by decide⟩,⟨1045959, by decide⟩,⟨1045991, by decide⟩]) unmarked_context_11_75472_1045992 node_context_11_75472_1045992
  intro a
  fin_cases a
  · exact context_12_301888_1045881
  · exact context_12_301889_1045923
  · exact context_12_301890_1045959
  · exact context_12_301891_1045991

theorem selected_cut_38705 : selected 9 ⟨1046061, by decide⟩
    (prefixPartial 12 301892) = some ⟨12, 2, 0, 1046061, 301892, 3081, 65536⟩ := by
  decide +kernel

theorem context_12_301892_1046061 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301892 ⟨1046061, by decide⟩ :=
  accepted_of_selected 12 301892 ⟨1046061, by decide⟩ ⟨12, 2, 0, 1046061, 301892, 3081, 65536⟩
    (by decide) selected_cut_38705

theorem selected_cut_38706 : selected 9 ⟨1046126, by decide⟩
    (prefixPartial 12 301893) = some ⟨12, 2, 0, 1046126, 301893, 2873, 65536⟩ := by
  decide +kernel

theorem context_12_301893_1046126 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301893 ⟨1046126, by decide⟩ :=
  accepted_of_selected 12 301893 ⟨1046126, by decide⟩ ⟨12, 2, 0, 1046126, 301893, 2873, 65536⟩
    (by decide) selected_cut_38706

theorem selected_cut_38707 : selected 9 ⟨1046173, by decide⟩
    (prefixPartial 12 301894) = some ⟨12, 2, 0, 1046173, 301894, 2545, 65536⟩ := by
  decide +kernel

theorem context_12_301894_1046173 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301894 ⟨1046173, by decide⟩ :=
  accepted_of_selected 12 301894 ⟨1046173, by decide⟩ ⟨12, 2, 0, 1046173, 301894, 2545, 65536⟩
    (by decide) selected_cut_38707

theorem selected_cut_38708 : selected 9 ⟨1046216, by decide⟩
    (prefixPartial 12 301895) = some ⟨12, 2, 0, 1046216, 301895, 2453, 65536⟩ := by
  decide +kernel

theorem context_12_301895_1046216 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301895 ⟨1046216, by decide⟩ :=
  accepted_of_selected 12 301895 ⟨1046216, by decide⟩ ⟨12, 2, 0, 1046216, 301895, 2453, 65536⟩
    (by decide) selected_cut_38708

theorem unmarked_context_11_75473_1046217 : frontier 10 ⟨1046217, by decide⟩
    (prefixCache 11 75473) (prefixPartial 11 75473) = false := by
  decide +kernel

theorem node_context_11_75473_1046217 : EJMOriginalGlobalDAGData.nodes 10 ⟨1046217, by decide⟩ =
    .split (coordinate 11) (![⟨1046061, by decide⟩,⟨1046126, by decide⟩,⟨1046173, by decide⟩,⟨1046216, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75473_1046217 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75473 ⟨1046217, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75473
    ⟨1046217, by decide⟩ (by decide) (![⟨1046061, by decide⟩,⟨1046126, by decide⟩,⟨1046173, by decide⟩,⟨1046216, by decide⟩]) unmarked_context_11_75473_1046217 node_context_11_75473_1046217
  intro a
  fin_cases a
  · exact context_12_301892_1046061
  · exact context_12_301893_1046126
  · exact context_12_301894_1046173
  · exact context_12_301895_1046216

theorem selected_cut_38709 : selected 9 ⟨1046260, by decide⟩
    (prefixPartial 12 301896) = some ⟨12, 2, 0, 1046260, 301896, 2853, 65536⟩ := by
  decide +kernel

theorem context_12_301896_1046260 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301896 ⟨1046260, by decide⟩ :=
  accepted_of_selected 12 301896 ⟨1046260, by decide⟩ ⟨12, 2, 0, 1046260, 301896, 2853, 65536⟩
    (by decide) selected_cut_38709

theorem selected_cut_38710 : selected 9 ⟨1046308, by decide⟩
    (prefixPartial 12 301897) = some ⟨12, 2, 0, 1046308, 301897, 2665, 65536⟩ := by
  decide +kernel

theorem context_12_301897_1046308 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301897 ⟨1046308, by decide⟩ :=
  accepted_of_selected 12 301897 ⟨1046308, by decide⟩ ⟨12, 2, 0, 1046308, 301897, 2665, 65536⟩
    (by decide) selected_cut_38710

theorem selected_cut_38711 : selected 9 ⟨1046347, by decide⟩
    (prefixPartial 12 301898) = some ⟨12, 2, 0, 1046347, 301898, 2397, 65536⟩ := by
  decide +kernel

theorem context_12_301898_1046347 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301898 ⟨1046347, by decide⟩ :=
  accepted_of_selected 12 301898 ⟨1046347, by decide⟩ ⟨12, 2, 0, 1046347, 301898, 2397, 65536⟩
    (by decide) selected_cut_38711

theorem selected_cut_38712 : selected 9 ⟨1046383, by decide⟩
    (prefixPartial 12 301899) = some ⟨12, 2, 0, 1046383, 301899, 2389, 65536⟩ := by
  decide +kernel

theorem context_12_301899_1046383 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301899 ⟨1046383, by decide⟩ :=
  accepted_of_selected 12 301899 ⟨1046383, by decide⟩ ⟨12, 2, 0, 1046383, 301899, 2389, 65536⟩
    (by decide) selected_cut_38712

theorem unmarked_context_11_75474_1046384 : frontier 10 ⟨1046384, by decide⟩
    (prefixCache 11 75474) (prefixPartial 11 75474) = false := by
  decide +kernel

theorem node_context_11_75474_1046384 : EJMOriginalGlobalDAGData.nodes 10 ⟨1046384, by decide⟩ =
    .split (coordinate 11) (![⟨1046260, by decide⟩,⟨1046308, by decide⟩,⟨1046347, by decide⟩,⟨1046383, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75474_1046384 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75474 ⟨1046384, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75474
    ⟨1046384, by decide⟩ (by decide) (![⟨1046260, by decide⟩,⟨1046308, by decide⟩,⟨1046347, by decide⟩,⟨1046383, by decide⟩]) unmarked_context_11_75474_1046384 node_context_11_75474_1046384
  intro a
  fin_cases a
  · exact context_12_301896_1046260
  · exact context_12_301897_1046308
  · exact context_12_301898_1046347
  · exact context_12_301899_1046383

theorem selected_cut_38713 : selected 9 ⟨1046437, by decide⟩
    (prefixPartial 12 301900) = some ⟨12, 2, 0, 1046437, 301900, 2805, 65536⟩ := by
  decide +kernel

theorem context_12_301900_1046437 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301900 ⟨1046437, by decide⟩ :=
  accepted_of_selected 12 301900 ⟨1046437, by decide⟩ ⟨12, 2, 0, 1046437, 301900, 2805, 65536⟩
    (by decide) selected_cut_38713

theorem selected_cut_38714 : selected 9 ⟨1046501, by decide⟩
    (prefixPartial 12 301901) = some ⟨12, 2, 0, 1046501, 301901, 2813, 65536⟩ := by
  decide +kernel

theorem context_12_301901_1046501 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301901 ⟨1046501, by decide⟩ :=
  accepted_of_selected 12 301901 ⟨1046501, by decide⟩ ⟨12, 2, 0, 1046501, 301901, 2813, 65536⟩
    (by decide) selected_cut_38714

theorem selected_cut_38715 : selected 9 ⟨1046545, by decide⟩
    (prefixPartial 12 301902) = some ⟨12, 2, 0, 1046545, 301902, 2545, 65536⟩ := by
  decide +kernel

theorem context_12_301902_1046545 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301902 ⟨1046545, by decide⟩ :=
  accepted_of_selected 12 301902 ⟨1046545, by decide⟩ ⟨12, 2, 0, 1046545, 301902, 2545, 65536⟩
    (by decide) selected_cut_38715

theorem selected_cut_38716 : selected 9 ⟨903806, by decide⟩
    (prefixPartial 12 301903) = some ⟨12, 1, 0, 903806, 301903, 1, 65536⟩ := by
  decide +kernel

theorem context_12_301903_903806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301903 ⟨903806, by decide⟩ :=
  accepted_of_selected 12 301903 ⟨903806, by decide⟩ ⟨12, 1, 0, 903806, 301903, 1, 65536⟩
    (by decide) selected_cut_38716

theorem unmarked_context_11_75475_1046546 : frontier 10 ⟨1046546, by decide⟩
    (prefixCache 11 75475) (prefixPartial 11 75475) = false := by
  decide +kernel

theorem node_context_11_75475_1046546 : EJMOriginalGlobalDAGData.nodes 10 ⟨1046546, by decide⟩ =
    .split (coordinate 11) (![⟨1046437, by decide⟩,⟨1046501, by decide⟩,⟨1046545, by decide⟩,⟨903806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75475_1046546 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75475 ⟨1046546, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75475
    ⟨1046546, by decide⟩ (by decide) (![⟨1046437, by decide⟩,⟨1046501, by decide⟩,⟨1046545, by decide⟩,⟨903806, by decide⟩]) unmarked_context_11_75475_1046546 node_context_11_75475_1046546
  intro a
  fin_cases a
  · exact context_12_301900_1046437
  · exact context_12_301901_1046501
  · exact context_12_301902_1046545
  · exact context_12_301903_903806

theorem unmarked_context_10_18868_1046547 : frontier 11 ⟨1046547, by decide⟩
    (prefixCache 10 18868) (prefixPartial 10 18868) = false := by
  decide +kernel

theorem node_context_10_18868_1046547 : EJMOriginalGlobalDAGData.nodes 11 ⟨1046547, by decide⟩ =
    .split (coordinate 10) (![⟨1045992, by decide⟩,⟨1046217, by decide⟩,⟨1046384, by decide⟩,⟨1046546, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18868_1046547 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18868 ⟨1046547, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18868
    ⟨1046547, by decide⟩ (by decide) (![⟨1045992, by decide⟩,⟨1046217, by decide⟩,⟨1046384, by decide⟩,⟨1046546, by decide⟩]) unmarked_context_10_18868_1046547 node_context_10_18868_1046547
  intro a
  fin_cases a
  · exact context_11_75472_1045992
  · exact context_11_75473_1046217
  · exact context_11_75474_1046384
  · exact context_11_75475_1046546

theorem selected_cut_38717 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 18869) = some ⟨10, 1, 0, 893098, 18869, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_18869_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18869 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 18869 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 18869, 1, 1048576⟩
    (by decide) selected_cut_38717

theorem selected_cut_38718 : selected 9 ⟨1046574, by decide⟩
    (prefixPartial 12 301920) = some ⟨12, 2, 0, 1046574, 301920, 1689, 65536⟩ := by
  decide +kernel

theorem context_12_301920_1046574 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301920 ⟨1046574, by decide⟩ :=
  accepted_of_selected 12 301920 ⟨1046574, by decide⟩ ⟨12, 2, 0, 1046574, 301920, 1689, 65536⟩
    (by decide) selected_cut_38718

theorem selected_cut_38719 : selected 9 ⟨1046600, by decide⟩
    (prefixPartial 12 301921) = some ⟨12, 2, 0, 1046600, 301921, 1785, 65536⟩ := by
  decide +kernel

theorem context_12_301921_1046600 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301921 ⟨1046600, by decide⟩ :=
  accepted_of_selected 12 301921 ⟨1046600, by decide⟩ ⟨12, 2, 0, 1046600, 301921, 1785, 65536⟩
    (by decide) selected_cut_38719

theorem selected_cut_38720 : selected 9 ⟨1046626, by decide⟩
    (prefixPartial 12 301922) = some ⟨12, 2, 0, 1046626, 301922, 1581, 65536⟩ := by
  decide +kernel

theorem context_12_301922_1046626 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301922 ⟨1046626, by decide⟩ :=
  accepted_of_selected 12 301922 ⟨1046626, by decide⟩ ⟨12, 2, 0, 1046626, 301922, 1581, 65536⟩
    (by decide) selected_cut_38720

theorem selected_cut_38721 : selected 9 ⟨1046645, by decide⟩
    (prefixPartial 12 301923) = some ⟨12, 2, 0, 1046645, 301923, 1485, 65536⟩ := by
  decide +kernel

theorem context_12_301923_1046645 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301923 ⟨1046645, by decide⟩ :=
  accepted_of_selected 12 301923 ⟨1046645, by decide⟩ ⟨12, 2, 0, 1046645, 301923, 1485, 65536⟩
    (by decide) selected_cut_38721

theorem unmarked_context_11_75480_1046646 : frontier 10 ⟨1046646, by decide⟩
    (prefixCache 11 75480) (prefixPartial 11 75480) = false := by
  decide +kernel

theorem node_context_11_75480_1046646 : EJMOriginalGlobalDAGData.nodes 10 ⟨1046646, by decide⟩ =
    .split (coordinate 11) (![⟨1046574, by decide⟩,⟨1046600, by decide⟩,⟨1046626, by decide⟩,⟨1046645, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75480_1046646 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75480 ⟨1046646, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75480
    ⟨1046646, by decide⟩ (by decide) (![⟨1046574, by decide⟩,⟨1046600, by decide⟩,⟨1046626, by decide⟩,⟨1046645, by decide⟩]) unmarked_context_11_75480_1046646 node_context_11_75480_1046646
  intro a
  fin_cases a
  · exact context_12_301920_1046574
  · exact context_12_301921_1046600
  · exact context_12_301922_1046626
  · exact context_12_301923_1046645

theorem selected_cut_38722 : selected 9 ⟨1046677, by decide⟩
    (prefixPartial 12 301924) = some ⟨12, 2, 0, 1046677, 301924, 1853, 65536⟩ := by
  decide +kernel

theorem context_12_301924_1046677 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301924 ⟨1046677, by decide⟩ :=
  accepted_of_selected 12 301924 ⟨1046677, by decide⟩ ⟨12, 2, 0, 1046677, 301924, 1853, 65536⟩
    (by decide) selected_cut_38722

theorem selected_cut_38723 : selected 9 ⟨1025817, by decide⟩
    (prefixPartial 12 301925) = some ⟨12, 1, 0, 1025817, 301925, 1, 65536⟩ := by
  decide +kernel

theorem context_12_301925_1025817 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301925 ⟨1025817, by decide⟩ :=
  accepted_of_selected 12 301925 ⟨1025817, by decide⟩ ⟨12, 1, 0, 1025817, 301925, 1, 65536⟩
    (by decide) selected_cut_38723

theorem selected_cut_38724 : selected 9 ⟨1046712, by decide⟩
    (prefixPartial 12 301926) = some ⟨12, 2, 0, 1046712, 301926, 1641, 65536⟩ := by
  decide +kernel

theorem context_12_301926_1046712 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301926 ⟨1046712, by decide⟩ :=
  accepted_of_selected 12 301926 ⟨1046712, by decide⟩ ⟨12, 2, 0, 1046712, 301926, 1641, 65536⟩
    (by decide) selected_cut_38724

theorem selected_cut_38725 : selected 9 ⟨1046735, by decide⟩
    (prefixPartial 12 301927) = some ⟨12, 2, 0, 1046735, 301927, 1693, 65536⟩ := by
  decide +kernel

theorem context_12_301927_1046735 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301927 ⟨1046735, by decide⟩ :=
  accepted_of_selected 12 301927 ⟨1046735, by decide⟩ ⟨12, 2, 0, 1046735, 301927, 1693, 65536⟩
    (by decide) selected_cut_38725

theorem unmarked_context_11_75481_1046736 : frontier 10 ⟨1046736, by decide⟩
    (prefixCache 11 75481) (prefixPartial 11 75481) = false := by
  decide +kernel

theorem node_context_11_75481_1046736 : EJMOriginalGlobalDAGData.nodes 10 ⟨1046736, by decide⟩ =
    .split (coordinate 11) (![⟨1046677, by decide⟩,⟨1025817, by decide⟩,⟨1046712, by decide⟩,⟨1046735, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75481_1046736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75481 ⟨1046736, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75481
    ⟨1046736, by decide⟩ (by decide) (![⟨1046677, by decide⟩,⟨1025817, by decide⟩,⟨1046712, by decide⟩,⟨1046735, by decide⟩]) unmarked_context_11_75481_1046736 node_context_11_75481_1046736
  intro a
  fin_cases a
  · exact context_12_301924_1046677
  · exact context_12_301925_1025817
  · exact context_12_301926_1046712
  · exact context_12_301927_1046735

theorem selected_cut_38726 : selected 10 ⟨900587, by decide⟩
    (prefixPartial 11 75482) = some ⟨11, 1, 0, 900587, 75482, 1, 262144⟩ := by
  decide +kernel

theorem context_11_75482_900587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75482 ⟨900587, by decide⟩ :=
  accepted_of_selected 11 75482 ⟨900587, by decide⟩ ⟨11, 1, 0, 900587, 75482, 1, 262144⟩
    (by decide) selected_cut_38726

theorem selected_cut_38727 : selected 9 ⟨1046773, by decide⟩
    (prefixPartial 12 301932) = some ⟨12, 2, 0, 1046773, 301932, 1925, 65536⟩ := by
  decide +kernel

theorem context_12_301932_1046773 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301932 ⟨1046773, by decide⟩ :=
  accepted_of_selected 12 301932 ⟨1046773, by decide⟩ ⟨12, 2, 0, 1046773, 301932, 1925, 65536⟩
    (by decide) selected_cut_38727

theorem selected_cut_38728 : selected 9 ⟨1046812, by decide⟩
    (prefixPartial 12 301933) = some ⟨12, 2, 0, 1046812, 301933, 2081, 65536⟩ := by
  decide +kernel

theorem context_12_301933_1046812 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301933 ⟨1046812, by decide⟩ :=
  accepted_of_selected 12 301933 ⟨1046812, by decide⟩ ⟨12, 2, 0, 1046812, 301933, 2081, 65536⟩
    (by decide) selected_cut_38728

theorem selected_cut_38729 : selected 9 ⟨1046843, by decide⟩
    (prefixPartial 12 301934) = some ⟨12, 2, 0, 1046843, 301934, 1777, 65536⟩ := by
  decide +kernel

theorem context_12_301934_1046843 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301934 ⟨1046843, by decide⟩ :=
  accepted_of_selected 12 301934 ⟨1046843, by decide⟩ ⟨12, 2, 0, 1046843, 301934, 1777, 65536⟩
    (by decide) selected_cut_38729

theorem selected_cut_38730 : selected 9 ⟨903806, by decide⟩
    (prefixPartial 12 301935) = some ⟨12, 1, 0, 903806, 301935, 1, 65536⟩ := by
  decide +kernel

theorem context_12_301935_903806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301935 ⟨903806, by decide⟩ :=
  accepted_of_selected 12 301935 ⟨903806, by decide⟩ ⟨12, 1, 0, 903806, 301935, 1, 65536⟩
    (by decide) selected_cut_38730

theorem unmarked_context_11_75483_1046844 : frontier 10 ⟨1046844, by decide⟩
    (prefixCache 11 75483) (prefixPartial 11 75483) = false := by
  decide +kernel

theorem node_context_11_75483_1046844 : EJMOriginalGlobalDAGData.nodes 10 ⟨1046844, by decide⟩ =
    .split (coordinate 11) (![⟨1046773, by decide⟩,⟨1046812, by decide⟩,⟨1046843, by decide⟩,⟨903806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75483_1046844 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75483 ⟨1046844, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75483
    ⟨1046844, by decide⟩ (by decide) (![⟨1046773, by decide⟩,⟨1046812, by decide⟩,⟨1046843, by decide⟩,⟨903806, by decide⟩]) unmarked_context_11_75483_1046844 node_context_11_75483_1046844
  intro a
  fin_cases a
  · exact context_12_301932_1046773
  · exact context_12_301933_1046812
  · exact context_12_301934_1046843
  · exact context_12_301935_903806

theorem unmarked_context_10_18870_1046845 : frontier 11 ⟨1046845, by decide⟩
    (prefixCache 10 18870) (prefixPartial 10 18870) = false := by
  decide +kernel

theorem node_context_10_18870_1046845 : EJMOriginalGlobalDAGData.nodes 11 ⟨1046845, by decide⟩ =
    .split (coordinate 10) (![⟨1046646, by decide⟩,⟨1046736, by decide⟩,⟨900587, by decide⟩,⟨1046844, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18870_1046845 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18870 ⟨1046845, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18870
    ⟨1046845, by decide⟩ (by decide) (![⟨1046646, by decide⟩,⟨1046736, by decide⟩,⟨900587, by decide⟩,⟨1046844, by decide⟩]) unmarked_context_10_18870_1046845 node_context_10_18870_1046845
  intro a
  fin_cases a
  · exact context_11_75480_1046646
  · exact context_11_75481_1046736
  · exact context_11_75482_900587
  · exact context_11_75483_1046844

theorem selected_cut_38731 : selected 9 ⟨1046870, by decide⟩
    (prefixPartial 12 301936) = some ⟨12, 2, 0, 1046870, 301936, 1665, 65536⟩ := by
  decide +kernel

theorem context_12_301936_1046870 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301936 ⟨1046870, by decide⟩ :=
  accepted_of_selected 12 301936 ⟨1046870, by decide⟩ ⟨12, 2, 0, 1046870, 301936, 1665, 65536⟩
    (by decide) selected_cut_38731

theorem selected_cut_38732 : selected 9 ⟨1046906, by decide⟩
    (prefixPartial 12 301937) = some ⟨12, 2, 0, 1046906, 301937, 1945, 65536⟩ := by
  decide +kernel

theorem context_12_301937_1046906 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301937 ⟨1046906, by decide⟩ :=
  accepted_of_selected 12 301937 ⟨1046906, by decide⟩ ⟨12, 2, 0, 1046906, 301937, 1945, 65536⟩
    (by decide) selected_cut_38732

theorem selected_cut_38733 : selected 9 ⟨1046929, by decide⟩
    (prefixPartial 12 301938) = some ⟨12, 2, 0, 1046929, 301938, 1697, 65536⟩ := by
  decide +kernel

theorem context_12_301938_1046929 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301938 ⟨1046929, by decide⟩ :=
  accepted_of_selected 12 301938 ⟨1046929, by decide⟩ ⟨12, 2, 0, 1046929, 301938, 1697, 65536⟩
    (by decide) selected_cut_38733

theorem selected_cut_38734 : selected 9 ⟨1046950, by decide⟩
    (prefixPartial 12 301939) = some ⟨12, 2, 0, 1046950, 301939, 1485, 65536⟩ := by
  decide +kernel

theorem context_12_301939_1046950 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301939 ⟨1046950, by decide⟩ :=
  accepted_of_selected 12 301939 ⟨1046950, by decide⟩ ⟨12, 2, 0, 1046950, 301939, 1485, 65536⟩
    (by decide) selected_cut_38734

theorem unmarked_context_11_75484_1046951 : frontier 10 ⟨1046951, by decide⟩
    (prefixCache 11 75484) (prefixPartial 11 75484) = false := by
  decide +kernel

theorem node_context_11_75484_1046951 : EJMOriginalGlobalDAGData.nodes 10 ⟨1046951, by decide⟩ =
    .split (coordinate 11) (![⟨1046870, by decide⟩,⟨1046906, by decide⟩,⟨1046929, by decide⟩,⟨1046950, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75484_1046951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75484 ⟨1046951, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75484
    ⟨1046951, by decide⟩ (by decide) (![⟨1046870, by decide⟩,⟨1046906, by decide⟩,⟨1046929, by decide⟩,⟨1046950, by decide⟩]) unmarked_context_11_75484_1046951 node_context_11_75484_1046951
  intro a
  fin_cases a
  · exact context_12_301936_1046870
  · exact context_12_301937_1046906
  · exact context_12_301938_1046929
  · exact context_12_301939_1046950

theorem selected_cut_38735 : selected 9 ⟨1046981, by decide⟩
    (prefixPartial 12 301940) = some ⟨12, 2, 0, 1046981, 301940, 1773, 65536⟩ := by
  decide +kernel

theorem context_12_301940_1046981 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301940 ⟨1046981, by decide⟩ :=
  accepted_of_selected 12 301940 ⟨1046981, by decide⟩ ⟨12, 2, 0, 1046981, 301940, 1773, 65536⟩
    (by decide) selected_cut_38735

theorem selected_cut_38736 : selected 9 ⟨1046982, by decide⟩
    (prefixPartial 12 301941) = some ⟨12, 1, 0, 1046982, 301941, 1, 65536⟩ := by
  decide +kernel

theorem context_12_301941_1046982 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301941 ⟨1046982, by decide⟩ :=
  accepted_of_selected 12 301941 ⟨1046982, by decide⟩ ⟨12, 1, 0, 1046982, 301941, 1, 65536⟩
    (by decide) selected_cut_38736

theorem selected_cut_38737 : selected 9 ⟨1047019, by decide⟩
    (prefixPartial 12 301942) = some ⟨12, 2, 0, 1047019, 301942, 1765, 65536⟩ := by
  decide +kernel

theorem context_12_301942_1047019 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301942 ⟨1047019, by decide⟩ :=
  accepted_of_selected 12 301942 ⟨1047019, by decide⟩ ⟨12, 2, 0, 1047019, 301942, 1765, 65536⟩
    (by decide) selected_cut_38737

theorem selected_cut_38738 : selected 9 ⟨1047042, by decide⟩
    (prefixPartial 12 301943) = some ⟨12, 2, 0, 1047042, 301943, 1597, 65536⟩ := by
  decide +kernel

theorem context_12_301943_1047042 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301943 ⟨1047042, by decide⟩ :=
  accepted_of_selected 12 301943 ⟨1047042, by decide⟩ ⟨12, 2, 0, 1047042, 301943, 1597, 65536⟩
    (by decide) selected_cut_38738

theorem unmarked_context_11_75485_1047043 : frontier 10 ⟨1047043, by decide⟩
    (prefixCache 11 75485) (prefixPartial 11 75485) = false := by
  decide +kernel

theorem node_context_11_75485_1047043 : EJMOriginalGlobalDAGData.nodes 10 ⟨1047043, by decide⟩ =
    .split (coordinate 11) (![⟨1046981, by decide⟩,⟨1046982, by decide⟩,⟨1047019, by decide⟩,⟨1047042, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75485_1047043 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75485 ⟨1047043, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75485
    ⟨1047043, by decide⟩ (by decide) (![⟨1046981, by decide⟩,⟨1046982, by decide⟩,⟨1047019, by decide⟩,⟨1047042, by decide⟩]) unmarked_context_11_75485_1047043 node_context_11_75485_1047043
  intro a
  fin_cases a
  · exact context_12_301940_1046981
  · exact context_12_301941_1046982
  · exact context_12_301942_1047019
  · exact context_12_301943_1047042

theorem selected_cut_38739 : selected 9 ⟨1047071, by decide⟩
    (prefixPartial 12 301944) = some ⟨12, 2, 0, 1047071, 301944, 1761, 65536⟩ := by
  decide +kernel

theorem context_12_301944_1047071 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301944 ⟨1047071, by decide⟩ :=
  accepted_of_selected 12 301944 ⟨1047071, by decide⟩ ⟨12, 2, 0, 1047071, 301944, 1761, 65536⟩
    (by decide) selected_cut_38739

theorem selected_cut_38740 : selected 9 ⟨1047101, by decide⟩
    (prefixPartial 12 301945) = some ⟨12, 2, 0, 1047101, 301945, 1821, 65536⟩ := by
  decide +kernel

theorem context_12_301945_1047101 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301945 ⟨1047101, by decide⟩ :=
  accepted_of_selected 12 301945 ⟨1047101, by decide⟩ ⟨12, 2, 0, 1047101, 301945, 1821, 65536⟩
    (by decide) selected_cut_38740

theorem selected_cut_38741 : selected 9 ⟨1047128, by decide⟩
    (prefixPartial 12 301946) = some ⟨12, 2, 0, 1047128, 301946, 1589, 65536⟩ := by
  decide +kernel

theorem context_12_301946_1047128 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301946 ⟨1047128, by decide⟩ :=
  accepted_of_selected 12 301946 ⟨1047128, by decide⟩ ⟨12, 2, 0, 1047128, 301946, 1589, 65536⟩
    (by decide) selected_cut_38741

theorem selected_cut_38742 : selected 9 ⟨1047147, by decide⟩
    (prefixPartial 12 301947) = some ⟨12, 2, 0, 1047147, 301947, 1525, 65536⟩ := by
  decide +kernel

theorem context_12_301947_1047147 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301947 ⟨1047147, by decide⟩ :=
  accepted_of_selected 12 301947 ⟨1047147, by decide⟩ ⟨12, 2, 0, 1047147, 301947, 1525, 65536⟩
    (by decide) selected_cut_38742

theorem unmarked_context_11_75486_1047148 : frontier 10 ⟨1047148, by decide⟩
    (prefixCache 11 75486) (prefixPartial 11 75486) = false := by
  decide +kernel

theorem node_context_11_75486_1047148 : EJMOriginalGlobalDAGData.nodes 10 ⟨1047148, by decide⟩ =
    .split (coordinate 11) (![⟨1047071, by decide⟩,⟨1047101, by decide⟩,⟨1047128, by decide⟩,⟨1047147, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75486_1047148 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75486 ⟨1047148, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75486
    ⟨1047148, by decide⟩ (by decide) (![⟨1047071, by decide⟩,⟨1047101, by decide⟩,⟨1047128, by decide⟩,⟨1047147, by decide⟩]) unmarked_context_11_75486_1047148 node_context_11_75486_1047148
  intro a
  fin_cases a
  · exact context_12_301944_1047071
  · exact context_12_301945_1047101
  · exact context_12_301946_1047128
  · exact context_12_301947_1047147

theorem selected_cut_38743 : selected 9 ⟨1047180, by decide⟩
    (prefixPartial 12 301948) = some ⟨12, 2, 0, 1047180, 301948, 1721, 65536⟩ := by
  decide +kernel

theorem context_12_301948_1047180 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301948 ⟨1047180, by decide⟩ :=
  accepted_of_selected 12 301948 ⟨1047180, by decide⟩ ⟨12, 2, 0, 1047180, 301948, 1721, 65536⟩
    (by decide) selected_cut_38743

theorem selected_cut_38744 : selected 9 ⟨1047228, by decide⟩
    (prefixPartial 12 301949) = some ⟨12, 2, 0, 1047228, 301949, 1889, 65536⟩ := by
  decide +kernel

theorem context_12_301949_1047228 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301949 ⟨1047228, by decide⟩ :=
  accepted_of_selected 12 301949 ⟨1047228, by decide⟩ ⟨12, 2, 0, 1047228, 301949, 1889, 65536⟩
    (by decide) selected_cut_38744

theorem selected_cut_38745 : selected 9 ⟨1047261, by decide⟩
    (prefixPartial 12 301950) = some ⟨12, 2, 0, 1047261, 301950, 1717, 65536⟩ := by
  decide +kernel

theorem context_12_301950_1047261 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301950 ⟨1047261, by decide⟩ :=
  accepted_of_selected 12 301950 ⟨1047261, by decide⟩ ⟨12, 2, 0, 1047261, 301950, 1717, 65536⟩
    (by decide) selected_cut_38745

theorem selected_cut_38746 : selected 9 ⟨762109, by decide⟩
    (prefixPartial 12 301951) = some ⟨12, 1, 0, 762109, 301951, 1, 65536⟩ := by
  decide +kernel

theorem context_12_301951_762109 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301951 ⟨762109, by decide⟩ :=
  accepted_of_selected 12 301951 ⟨762109, by decide⟩ ⟨12, 1, 0, 762109, 301951, 1, 65536⟩
    (by decide) selected_cut_38746

theorem unmarked_context_11_75487_1047262 : frontier 10 ⟨1047262, by decide⟩
    (prefixCache 11 75487) (prefixPartial 11 75487) = false := by
  decide +kernel

theorem node_context_11_75487_1047262 : EJMOriginalGlobalDAGData.nodes 10 ⟨1047262, by decide⟩ =
    .split (coordinate 11) (![⟨1047180, by decide⟩,⟨1047228, by decide⟩,⟨1047261, by decide⟩,⟨762109, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75487_1047262 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75487 ⟨1047262, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75487
    ⟨1047262, by decide⟩ (by decide) (![⟨1047180, by decide⟩,⟨1047228, by decide⟩,⟨1047261, by decide⟩,⟨762109, by decide⟩]) unmarked_context_11_75487_1047262 node_context_11_75487_1047262
  intro a
  fin_cases a
  · exact context_12_301948_1047180
  · exact context_12_301949_1047228
  · exact context_12_301950_1047261
  · exact context_12_301951_762109

theorem unmarked_context_10_18871_1047263 : frontier 11 ⟨1047263, by decide⟩
    (prefixCache 10 18871) (prefixPartial 10 18871) = false := by
  decide +kernel

theorem node_context_10_18871_1047263 : EJMOriginalGlobalDAGData.nodes 11 ⟨1047263, by decide⟩ =
    .split (coordinate 10) (![⟨1046951, by decide⟩,⟨1047043, by decide⟩,⟨1047148, by decide⟩,⟨1047262, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18871_1047263 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18871 ⟨1047263, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18871
    ⟨1047263, by decide⟩ (by decide) (![⟨1046951, by decide⟩,⟨1047043, by decide⟩,⟨1047148, by decide⟩,⟨1047262, by decide⟩]) unmarked_context_10_18871_1047263 node_context_10_18871_1047263
  intro a
  fin_cases a
  · exact context_11_75484_1046951
  · exact context_11_75485_1047043
  · exact context_11_75486_1047148
  · exact context_11_75487_1047262

theorem unmarked_context_9_4717_1047264 : frontier 12 ⟨1047264, by decide⟩
    (prefixCache 9 4717) (prefixPartial 9 4717) = false := by
  decide +kernel

theorem node_context_9_4717_1047264 : EJMOriginalGlobalDAGData.nodes 12 ⟨1047264, by decide⟩ =
    .split (coordinate 9) (![⟨1046547, by decide⟩,⟨893098, by decide⟩,⟨1046845, by decide⟩,⟨1047263, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4717_1047264 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4717 ⟨1047264, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4717
    ⟨1047264, by decide⟩ (by decide) (![⟨1046547, by decide⟩,⟨893098, by decide⟩,⟨1046845, by decide⟩,⟨1047263, by decide⟩]) unmarked_context_9_4717_1047264 node_context_9_4717_1047264
  intro a
  fin_cases a
  · exact context_10_18868_1046547
  · exact context_10_18869_893098
  · exact context_10_18870_1046845
  · exact context_10_18871_1047263

theorem selected_cut_38747 : selected 10 ⟨1047321, by decide⟩
    (prefixPartial 11 75488) = some ⟨11, 2, 0, 1047321, 75488, 3825, 262144⟩ := by
  decide +kernel

theorem context_11_75488_1047321 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75488 ⟨1047321, by decide⟩ :=
  accepted_of_selected 11 75488 ⟨1047321, by decide⟩ ⟨11, 2, 0, 1047321, 75488, 3825, 262144⟩
    (by decide) selected_cut_38747

theorem selected_cut_38748 : selected 9 ⟨1047354, by decide⟩
    (prefixPartial 12 301956) = some ⟨12, 2, 0, 1047354, 301956, 1485, 65536⟩ := by
  decide +kernel

theorem context_12_301956_1047354 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301956 ⟨1047354, by decide⟩ :=
  accepted_of_selected 12 301956 ⟨1047354, by decide⟩ ⟨12, 2, 0, 1047354, 301956, 1485, 65536⟩
    (by decide) selected_cut_38748

theorem selected_cut_38749 : selected 9 ⟨1047391, by decide⟩
    (prefixPartial 12 301957) = some ⟨12, 2, 0, 1047391, 301957, 1493, 65536⟩ := by
  decide +kernel

theorem context_12_301957_1047391 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301957 ⟨1047391, by decide⟩ :=
  accepted_of_selected 12 301957 ⟨1047391, by decide⟩ ⟨12, 2, 0, 1047391, 301957, 1493, 65536⟩
    (by decide) selected_cut_38749

theorem selected_cut_38750 : selected 9 ⟨984676, by decide⟩
    (prefixPartial 12 301958) = some ⟨12, 1, 0, 984676, 301958, 1, 65536⟩ := by
  decide +kernel

theorem context_12_301958_984676 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301958 ⟨984676, by decide⟩ :=
  accepted_of_selected 12 301958 ⟨984676, by decide⟩ ⟨12, 1, 0, 984676, 301958, 1, 65536⟩
    (by decide) selected_cut_38750

theorem selected_cut_38751 : selected 9 ⟨1047418, by decide⟩
    (prefixPartial 12 301959) = some ⟨12, 2, 0, 1047418, 301959, 1293, 65536⟩ := by
  decide +kernel

theorem context_12_301959_1047418 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301959 ⟨1047418, by decide⟩ :=
  accepted_of_selected 12 301959 ⟨1047418, by decide⟩ ⟨12, 2, 0, 1047418, 301959, 1293, 65536⟩
    (by decide) selected_cut_38751

theorem unmarked_context_11_75489_1047419 : frontier 10 ⟨1047419, by decide⟩
    (prefixCache 11 75489) (prefixPartial 11 75489) = false := by
  decide +kernel

theorem node_context_11_75489_1047419 : EJMOriginalGlobalDAGData.nodes 10 ⟨1047419, by decide⟩ =
    .split (coordinate 11) (![⟨1047354, by decide⟩,⟨1047391, by decide⟩,⟨984676, by decide⟩,⟨1047418, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75489_1047419 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75489 ⟨1047419, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75489
    ⟨1047419, by decide⟩ (by decide) (![⟨1047354, by decide⟩,⟨1047391, by decide⟩,⟨984676, by decide⟩,⟨1047418, by decide⟩]) unmarked_context_11_75489_1047419 node_context_11_75489_1047419
  intro a
  fin_cases a
  · exact context_12_301956_1047354
  · exact context_12_301957_1047391
  · exact context_12_301958_984676
  · exact context_12_301959_1047418

theorem selected_cut_38752 : selected 9 ⟨1047443, by decide⟩
    (prefixPartial 12 301960) = some ⟨12, 2, 0, 1047443, 301960, 1409, 65536⟩ := by
  decide +kernel

theorem context_12_301960_1047443 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301960 ⟨1047443, by decide⟩ :=
  accepted_of_selected 12 301960 ⟨1047443, by decide⟩ ⟨12, 2, 0, 1047443, 301960, 1409, 65536⟩
    (by decide) selected_cut_38752

theorem selected_cut_38753 : selected 9 ⟨1047472, by decide⟩
    (prefixPartial 12 301961) = some ⟨12, 2, 0, 1047472, 301961, 1397, 65536⟩ := by
  decide +kernel

theorem context_12_301961_1047472 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301961 ⟨1047472, by decide⟩ :=
  accepted_of_selected 12 301961 ⟨1047472, by decide⟩ ⟨12, 2, 0, 1047472, 301961, 1397, 65536⟩
    (by decide) selected_cut_38753

theorem selected_cut_38754 : selected 9 ⟨984676, by decide⟩
    (prefixPartial 12 301962) = some ⟨12, 1, 0, 984676, 301962, 1, 65536⟩ := by
  decide +kernel

theorem context_12_301962_984676 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301962 ⟨984676, by decide⟩ :=
  accepted_of_selected 12 301962 ⟨984676, by decide⟩ ⟨12, 1, 0, 984676, 301962, 1, 65536⟩
    (by decide) selected_cut_38754

theorem selected_cut_38755 : selected 9 ⟨1047494, by decide⟩
    (prefixPartial 12 301963) = some ⟨12, 2, 0, 1047494, 301963, 1289, 65536⟩ := by
  decide +kernel

theorem context_12_301963_1047494 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301963 ⟨1047494, by decide⟩ :=
  accepted_of_selected 12 301963 ⟨1047494, by decide⟩ ⟨12, 2, 0, 1047494, 301963, 1289, 65536⟩
    (by decide) selected_cut_38755

theorem unmarked_context_11_75490_1047495 : frontier 10 ⟨1047495, by decide⟩
    (prefixCache 11 75490) (prefixPartial 11 75490) = false := by
  decide +kernel

theorem node_context_11_75490_1047495 : EJMOriginalGlobalDAGData.nodes 10 ⟨1047495, by decide⟩ =
    .split (coordinate 11) (![⟨1047443, by decide⟩,⟨1047472, by decide⟩,⟨984676, by decide⟩,⟨1047494, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75490_1047495 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75490 ⟨1047495, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75490
    ⟨1047495, by decide⟩ (by decide) (![⟨1047443, by decide⟩,⟨1047472, by decide⟩,⟨984676, by decide⟩,⟨1047494, by decide⟩]) unmarked_context_11_75490_1047495 node_context_11_75490_1047495
  intro a
  fin_cases a
  · exact context_12_301960_1047443
  · exact context_12_301961_1047472
  · exact context_12_301962_984676
  · exact context_12_301963_1047494

theorem selected_cut_38756 : selected 10 ⟨1047546, by decide⟩
    (prefixPartial 11 75491) = some ⟨11, 2, 0, 1047546, 75491, 2577, 262144⟩ := by
  decide +kernel

theorem context_11_75491_1047546 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75491 ⟨1047546, by decide⟩ :=
  accepted_of_selected 11 75491 ⟨1047546, by decide⟩ ⟨11, 2, 0, 1047546, 75491, 2577, 262144⟩
    (by decide) selected_cut_38756

theorem unmarked_context_10_18872_1047547 : frontier 11 ⟨1047547, by decide⟩
    (prefixCache 10 18872) (prefixPartial 10 18872) = false := by
  decide +kernel

theorem node_context_10_18872_1047547 : EJMOriginalGlobalDAGData.nodes 11 ⟨1047547, by decide⟩ =
    .split (coordinate 10) (![⟨1047321, by decide⟩,⟨1047419, by decide⟩,⟨1047495, by decide⟩,⟨1047546, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18872_1047547 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18872 ⟨1047547, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18872
    ⟨1047547, by decide⟩ (by decide) (![⟨1047321, by decide⟩,⟨1047419, by decide⟩,⟨1047495, by decide⟩,⟨1047546, by decide⟩]) unmarked_context_10_18872_1047547 node_context_10_18872_1047547
  intro a
  fin_cases a
  · exact context_11_75488_1047321
  · exact context_11_75489_1047419
  · exact context_11_75490_1047495
  · exact context_11_75491_1047546

theorem selected_cut_38757 : selected 10 ⟨1047589, by decide⟩
    (prefixPartial 11 75492) = some ⟨11, 2, 0, 1047589, 75492, 2917, 262144⟩ := by
  decide +kernel

theorem context_11_75492_1047589 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75492 ⟨1047589, by decide⟩ :=
  accepted_of_selected 11 75492 ⟨1047589, by decide⟩ ⟨11, 2, 0, 1047589, 75492, 2917, 262144⟩
    (by decide) selected_cut_38757

theorem selected_cut_38758 : selected 10 ⟨1047611, by decide⟩
    (prefixPartial 11 75493) = some ⟨11, 2, 0, 1047611, 75493, 1825, 262144⟩ := by
  decide +kernel

theorem context_11_75493_1047611 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75493 ⟨1047611, by decide⟩ :=
  accepted_of_selected 11 75493 ⟨1047611, by decide⟩ ⟨11, 2, 0, 1047611, 75493, 1825, 262144⟩
    (by decide) selected_cut_38758

theorem selected_cut_38759 : selected 10 ⟨1047663, by decide⟩
    (prefixPartial 11 75494) = some ⟨11, 2, 0, 1047663, 75494, 2789, 262144⟩ := by
  decide +kernel

theorem context_11_75494_1047663 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75494 ⟨1047663, by decide⟩ :=
  accepted_of_selected 11 75494 ⟨1047663, by decide⟩ ⟨11, 2, 0, 1047663, 75494, 2789, 262144⟩
    (by decide) selected_cut_38759

theorem selected_cut_38760 : selected 10 ⟨1047697, by decide⟩
    (prefixPartial 11 75495) = some ⟨11, 2, 0, 1047697, 75495, 1865, 262144⟩ := by
  decide +kernel

theorem context_11_75495_1047697 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75495 ⟨1047697, by decide⟩ :=
  accepted_of_selected 11 75495 ⟨1047697, by decide⟩ ⟨11, 2, 0, 1047697, 75495, 1865, 262144⟩
    (by decide) selected_cut_38760

theorem unmarked_context_10_18873_1047698 : frontier 11 ⟨1047698, by decide⟩
    (prefixCache 10 18873) (prefixPartial 10 18873) = false := by
  decide +kernel

theorem node_context_10_18873_1047698 : EJMOriginalGlobalDAGData.nodes 11 ⟨1047698, by decide⟩ =
    .split (coordinate 10) (![⟨1047589, by decide⟩,⟨1047611, by decide⟩,⟨1047663, by decide⟩,⟨1047697, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18873_1047698 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18873 ⟨1047698, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18873
    ⟨1047698, by decide⟩ (by decide) (![⟨1047589, by decide⟩,⟨1047611, by decide⟩,⟨1047663, by decide⟩,⟨1047697, by decide⟩]) unmarked_context_10_18873_1047698 node_context_10_18873_1047698
  intro a
  fin_cases a
  · exact context_11_75492_1047589
  · exact context_11_75493_1047611
  · exact context_11_75494_1047663
  · exact context_11_75495_1047697

theorem selected_cut_38761 : selected 10 ⟨1047724, by decide⟩
    (prefixPartial 11 75496) = some ⟨11, 2, 0, 1047724, 75496, 2145, 262144⟩ := by
  decide +kernel

theorem context_11_75496_1047724 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75496 ⟨1047724, by decide⟩ :=
  accepted_of_selected 11 75496 ⟨1047724, by decide⟩ ⟨11, 2, 0, 1047724, 75496, 2145, 262144⟩
    (by decide) selected_cut_38761

theorem selected_cut_38762 : selected 10 ⟨1047755, by decide⟩
    (prefixPartial 11 75497) = some ⟨11, 2, 0, 1047755, 75497, 2165, 262144⟩ := by
  decide +kernel

theorem context_11_75497_1047755 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75497 ⟨1047755, by decide⟩ :=
  accepted_of_selected 11 75497 ⟨1047755, by decide⟩ ⟨11, 2, 0, 1047755, 75497, 2165, 262144⟩
    (by decide) selected_cut_38762

theorem selected_cut_38763 : selected 10 ⟨906566, by decide⟩
    (prefixPartial 11 75498) = some ⟨11, 1, 0, 906566, 75498, 1, 262144⟩ := by
  decide +kernel

theorem context_11_75498_906566 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75498 ⟨906566, by decide⟩ :=
  accepted_of_selected 11 75498 ⟨906566, by decide⟩ ⟨11, 1, 0, 906566, 75498, 1, 262144⟩
    (by decide) selected_cut_38763

theorem selected_cut_38764 : selected 10 ⟨1047778, by decide⟩
    (prefixPartial 11 75499) = some ⟨11, 2, 0, 1047778, 75499, 1561, 262144⟩ := by
  decide +kernel

theorem context_11_75499_1047778 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75499 ⟨1047778, by decide⟩ :=
  accepted_of_selected 11 75499 ⟨1047778, by decide⟩ ⟨11, 2, 0, 1047778, 75499, 1561, 262144⟩
    (by decide) selected_cut_38764

theorem unmarked_context_10_18874_1047779 : frontier 11 ⟨1047779, by decide⟩
    (prefixCache 10 18874) (prefixPartial 10 18874) = false := by
  decide +kernel

theorem node_context_10_18874_1047779 : EJMOriginalGlobalDAGData.nodes 11 ⟨1047779, by decide⟩ =
    .split (coordinate 10) (![⟨1047724, by decide⟩,⟨1047755, by decide⟩,⟨906566, by decide⟩,⟨1047778, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18874_1047779 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18874 ⟨1047779, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18874
    ⟨1047779, by decide⟩ (by decide) (![⟨1047724, by decide⟩,⟨1047755, by decide⟩,⟨906566, by decide⟩,⟨1047778, by decide⟩]) unmarked_context_10_18874_1047779 node_context_10_18874_1047779
  intro a
  fin_cases a
  · exact context_11_75496_1047724
  · exact context_11_75497_1047755
  · exact context_11_75498_906566
  · exact context_11_75499_1047778

theorem selected_cut_38765 : selected 10 ⟨1047819, by decide⟩
    (prefixPartial 11 75500) = some ⟨11, 2, 0, 1047819, 75500, 2209, 262144⟩ := by
  decide +kernel

theorem context_11_75500_1047819 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75500 ⟨1047819, by decide⟩ :=
  accepted_of_selected 11 75500 ⟨1047819, by decide⟩ ⟨11, 2, 0, 1047819, 75500, 2209, 262144⟩
    (by decide) selected_cut_38765

theorem selected_cut_38766 : selected 10 ⟨1047854, by decide⟩
    (prefixPartial 11 75501) = some ⟨11, 2, 0, 1047854, 75501, 2065, 262144⟩ := by
  decide +kernel

theorem context_11_75501_1047854 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75501 ⟨1047854, by decide⟩ :=
  accepted_of_selected 11 75501 ⟨1047854, by decide⟩ ⟨11, 2, 0, 1047854, 75501, 2065, 262144⟩
    (by decide) selected_cut_38766

theorem selected_cut_38767 : selected 10 ⟨1047882, by decide⟩
    (prefixPartial 11 75502) = some ⟨11, 2, 0, 1047882, 75502, 1861, 262144⟩ := by
  decide +kernel

theorem context_11_75502_1047882 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75502 ⟨1047882, by decide⟩ :=
  accepted_of_selected 11 75502 ⟨1047882, by decide⟩ ⟨11, 2, 0, 1047882, 75502, 1861, 262144⟩
    (by decide) selected_cut_38767

theorem selected_cut_38768 : selected 10 ⟨1047904, by decide⟩
    (prefixPartial 11 75503) = some ⟨11, 2, 0, 1047904, 75503, 1281, 262144⟩ := by
  decide +kernel

theorem context_11_75503_1047904 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75503 ⟨1047904, by decide⟩ :=
  accepted_of_selected 11 75503 ⟨1047904, by decide⟩ ⟨11, 2, 0, 1047904, 75503, 1281, 262144⟩
    (by decide) selected_cut_38768

theorem unmarked_context_10_18875_1047905 : frontier 11 ⟨1047905, by decide⟩
    (prefixCache 10 18875) (prefixPartial 10 18875) = false := by
  decide +kernel

theorem node_context_10_18875_1047905 : EJMOriginalGlobalDAGData.nodes 11 ⟨1047905, by decide⟩ =
    .split (coordinate 10) (![⟨1047819, by decide⟩,⟨1047854, by decide⟩,⟨1047882, by decide⟩,⟨1047904, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18875_1047905 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18875 ⟨1047905, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18875
    ⟨1047905, by decide⟩ (by decide) (![⟨1047819, by decide⟩,⟨1047854, by decide⟩,⟨1047882, by decide⟩,⟨1047904, by decide⟩]) unmarked_context_10_18875_1047905 node_context_10_18875_1047905
  intro a
  fin_cases a
  · exact context_11_75500_1047819
  · exact context_11_75501_1047854
  · exact context_11_75502_1047882
  · exact context_11_75503_1047904

theorem unmarked_context_9_4718_1047906 : frontier 12 ⟨1047906, by decide⟩
    (prefixCache 9 4718) (prefixPartial 9 4718) = false := by
  decide +kernel

theorem node_context_9_4718_1047906 : EJMOriginalGlobalDAGData.nodes 12 ⟨1047906, by decide⟩ =
    .split (coordinate 9) (![⟨1047547, by decide⟩,⟨1047698, by decide⟩,⟨1047779, by decide⟩,⟨1047905, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4718_1047906 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4718 ⟨1047906, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4718
    ⟨1047906, by decide⟩ (by decide) (![⟨1047547, by decide⟩,⟨1047698, by decide⟩,⟨1047779, by decide⟩,⟨1047905, by decide⟩]) unmarked_context_9_4718_1047906 node_context_9_4718_1047906
  intro a
  fin_cases a
  · exact context_10_18872_1047547
  · exact context_10_18873_1047698
  · exact context_10_18874_1047779
  · exact context_10_18875_1047905

theorem selected_cut_38769 : selected 10 ⟨1047931, by decide⟩
    (prefixPartial 11 75504) = some ⟨11, 2, 0, 1047931, 75504, 1429, 262144⟩ := by
  decide +kernel

theorem context_11_75504_1047931 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75504 ⟨1047931, by decide⟩ :=
  accepted_of_selected 11 75504 ⟨1047931, by decide⟩ ⟨11, 2, 0, 1047931, 75504, 1429, 262144⟩
    (by decide) selected_cut_38769

theorem selected_cut_38770 : selected 10 ⟨1047964, by decide⟩
    (prefixPartial 11 75505) = some ⟨11, 2, 0, 1047964, 75505, 1857, 262144⟩ := by
  decide +kernel

theorem context_11_75505_1047964 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75505 ⟨1047964, by decide⟩ :=
  accepted_of_selected 11 75505 ⟨1047964, by decide⟩ ⟨11, 2, 0, 1047964, 75505, 1857, 262144⟩
    (by decide) selected_cut_38770

theorem selected_cut_38771 : selected 10 ⟨1047993, by decide⟩
    (prefixPartial 11 75506) = some ⟨11, 2, 0, 1047993, 75506, 1889, 262144⟩ := by
  decide +kernel

theorem context_11_75506_1047993 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75506 ⟨1047993, by decide⟩ :=
  accepted_of_selected 11 75506 ⟨1047993, by decide⟩ ⟨11, 2, 0, 1047993, 75506, 1889, 262144⟩
    (by decide) selected_cut_38771

theorem selected_cut_38772 : selected 10 ⟨1048026, by decide⟩
    (prefixPartial 11 75507) = some ⟨11, 2, 0, 1048026, 75507, 1481, 262144⟩ := by
  decide +kernel

theorem context_11_75507_1048026 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75507 ⟨1048026, by decide⟩ :=
  accepted_of_selected 11 75507 ⟨1048026, by decide⟩ ⟨11, 2, 0, 1048026, 75507, 1481, 262144⟩
    (by decide) selected_cut_38772

theorem unmarked_context_10_18876_1048027 : frontier 11 ⟨1048027, by decide⟩
    (prefixCache 10 18876) (prefixPartial 10 18876) = false := by
  decide +kernel

theorem node_context_10_18876_1048027 : EJMOriginalGlobalDAGData.nodes 11 ⟨1048027, by decide⟩ =
    .split (coordinate 10) (![⟨1047931, by decide⟩,⟨1047964, by decide⟩,⟨1047993, by decide⟩,⟨1048026, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18876_1048027 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18876 ⟨1048027, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18876
    ⟨1048027, by decide⟩ (by decide) (![⟨1047931, by decide⟩,⟨1047964, by decide⟩,⟨1047993, by decide⟩,⟨1048026, by decide⟩]) unmarked_context_10_18876_1048027 node_context_10_18876_1048027
  intro a
  fin_cases a
  · exact context_11_75504_1047931
  · exact context_11_75505_1047964
  · exact context_11_75506_1047993
  · exact context_11_75507_1048026

theorem selected_cut_38773 : selected 10 ⟨1048045, by decide⟩
    (prefixPartial 11 75508) = some ⟨11, 2, 0, 1048045, 75508, 1345, 262144⟩ := by
  decide +kernel

theorem context_11_75508_1048045 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75508 ⟨1048045, by decide⟩ :=
  accepted_of_selected 11 75508 ⟨1048045, by decide⟩ ⟨11, 2, 0, 1048045, 75508, 1345, 262144⟩
    (by decide) selected_cut_38773

theorem selected_cut_38774 : selected 10 ⟨1048063, by decide⟩
    (prefixPartial 11 75509) = some ⟨11, 2, 0, 1048063, 75509, 937, 262144⟩ := by
  decide +kernel

theorem context_11_75509_1048063 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75509 ⟨1048063, by decide⟩ :=
  accepted_of_selected 11 75509 ⟨1048063, by decide⟩ ⟨11, 2, 0, 1048063, 75509, 937, 262144⟩
    (by decide) selected_cut_38774

theorem selected_cut_38775 : selected 10 ⟨1048082, by decide⟩
    (prefixPartial 11 75510) = some ⟨11, 2, 0, 1048082, 75510, 1253, 262144⟩ := by
  decide +kernel

theorem context_11_75510_1048082 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75510 ⟨1048082, by decide⟩ :=
  accepted_of_selected 11 75510 ⟨1048082, by decide⟩ ⟨11, 2, 0, 1048082, 75510, 1253, 262144⟩
    (by decide) selected_cut_38775

theorem selected_cut_38776 : selected 10 ⟨1048104, by decide⟩
    (prefixPartial 11 75511) = some ⟨11, 2, 0, 1048104, 75511, 917, 262144⟩ := by
  decide +kernel

theorem context_11_75511_1048104 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75511 ⟨1048104, by decide⟩ :=
  accepted_of_selected 11 75511 ⟨1048104, by decide⟩ ⟨11, 2, 0, 1048104, 75511, 917, 262144⟩
    (by decide) selected_cut_38776

theorem unmarked_context_10_18877_1048105 : frontier 11 ⟨1048105, by decide⟩
    (prefixCache 10 18877) (prefixPartial 10 18877) = false := by
  decide +kernel

theorem node_context_10_18877_1048105 : EJMOriginalGlobalDAGData.nodes 11 ⟨1048105, by decide⟩ =
    .split (coordinate 10) (![⟨1048045, by decide⟩,⟨1048063, by decide⟩,⟨1048082, by decide⟩,⟨1048104, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18877_1048105 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18877 ⟨1048105, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18877
    ⟨1048105, by decide⟩ (by decide) (![⟨1048045, by decide⟩,⟨1048063, by decide⟩,⟨1048082, by decide⟩,⟨1048104, by decide⟩]) unmarked_context_10_18877_1048105 node_context_10_18877_1048105
  intro a
  fin_cases a
  · exact context_11_75508_1048045
  · exact context_11_75509_1048063
  · exact context_11_75510_1048082
  · exact context_11_75511_1048104

theorem selected_cut_38777 : selected 11 ⟨1048150, by decide⟩
    (prefixPartial 10 18878) = some ⟨10, 2, 0, 1048150, 18878, 2101, 1048576⟩ := by
  decide +kernel

theorem context_10_18878_1048150 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18878 ⟨1048150, by decide⟩ :=
  accepted_of_selected 10 18878 ⟨1048150, by decide⟩ ⟨10, 2, 0, 1048150, 18878, 2101, 1048576⟩
    (by decide) selected_cut_38777

theorem selected_cut_38778 : selected 11 ⟨1048190, by decide⟩
    (prefixPartial 10 18879) = some ⟨10, 2, 0, 1048190, 18879, 937, 1048576⟩ := by
  decide +kernel

theorem context_10_18879_1048190 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18879 ⟨1048190, by decide⟩ :=
  accepted_of_selected 10 18879 ⟨1048190, by decide⟩ ⟨10, 2, 0, 1048190, 18879, 937, 1048576⟩
    (by decide) selected_cut_38778

theorem unmarked_context_9_4719_1048191 : frontier 12 ⟨1048191, by decide⟩
    (prefixCache 9 4719) (prefixPartial 9 4719) = false := by
  decide +kernel

theorem node_context_9_4719_1048191 : EJMOriginalGlobalDAGData.nodes 12 ⟨1048191, by decide⟩ =
    .split (coordinate 9) (![⟨1048027, by decide⟩,⟨1048105, by decide⟩,⟨1048150, by decide⟩,⟨1048190, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4719_1048191 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4719 ⟨1048191, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4719
    ⟨1048191, by decide⟩ (by decide) (![⟨1048027, by decide⟩,⟨1048105, by decide⟩,⟨1048150, by decide⟩,⟨1048190, by decide⟩]) unmarked_context_9_4719_1048191 node_context_9_4719_1048191
  intro a
  fin_cases a
  · exact context_10_18876_1048027
  · exact context_10_18877_1048105
  · exact context_10_18878_1048150
  · exact context_10_18879_1048190

theorem unmarked_context_8_1179_1048192 : frontier 13 ⟨1048192, by decide⟩
    (prefixCache 8 1179) (prefixPartial 8 1179) = false := by
  decide +kernel

theorem node_context_8_1179_1048192 : EJMOriginalGlobalDAGData.nodes 13 ⟨1048192, by decide⟩ =
    .split (coordinate 8) (![⟨1045835, by decide⟩,⟨1047264, by decide⟩,⟨1047906, by decide⟩,⟨1048191, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1179_1048192 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1179 ⟨1048192, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1179
    ⟨1048192, by decide⟩ (by decide) (![⟨1045835, by decide⟩,⟨1047264, by decide⟩,⟨1047906, by decide⟩,⟨1048191, by decide⟩]) unmarked_context_8_1179_1048192 node_context_8_1179_1048192
  intro a
  fin_cases a
  · exact context_9_4716_1045835
  · exact context_9_4717_1047264
  · exact context_9_4718_1047906
  · exact context_9_4719_1048191

theorem unmarked_context_7_294_1048193 : frontier 14 ⟨1048193, by decide⟩
    (prefixCache 7 294) (prefixPartial 7 294) = false := by
  decide +kernel

theorem node_context_7_294_1048193 : EJMOriginalGlobalDAGData.nodes 14 ⟨1048193, by decide⟩ =
    .split (coordinate 7) (![⟨1032277, by decide⟩,⟨1037195, by decide⟩,⟨1042910, by decide⟩,⟨1048192, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_7_294_1048193 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 294 ⟨1048193, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 7 294
    ⟨1048193, by decide⟩ (by decide) (![⟨1032277, by decide⟩,⟨1037195, by decide⟩,⟨1042910, by decide⟩,⟨1048192, by decide⟩]) unmarked_context_7_294_1048193 node_context_7_294_1048193
  intro a
  fin_cases a
  · exact context_8_1176_1032277
  · exact context_8_1177_1037195
  · exact context_8_1178_1042910
  · exact context_8_1179_1048192

theorem selected_cut_38779 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 302080) = some ⟨12, 1, 0, 34034, 302080, 1, 65536⟩ := by
  decide +kernel

theorem context_12_302080_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302080 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 302080 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 302080, 1, 65536⟩
    (by decide) selected_cut_38779

theorem selected_cut_38780 : selected 9 ⟨1048287, by decide⟩
    (prefixPartial 12 302081) = some ⟨12, 2, 0, 1048287, 302081, 2485, 65536⟩ := by
  decide +kernel

theorem context_12_302081_1048287 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302081 ⟨1048287, by decide⟩ :=
  accepted_of_selected 12 302081 ⟨1048287, by decide⟩ ⟨12, 2, 0, 1048287, 302081, 2485, 65536⟩
    (by decide) selected_cut_38780

theorem selected_cut_38781 : selected 9 ⟨1048372, by decide⟩
    (prefixPartial 12 302082) = some ⟨12, 2, 0, 1048372, 302082, 3493, 65536⟩ := by
  decide +kernel

theorem context_12_302082_1048372 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302082 ⟨1048372, by decide⟩ :=
  accepted_of_selected 12 302082 ⟨1048372, by decide⟩ ⟨12, 2, 0, 1048372, 302082, 3493, 65536⟩
    (by decide) selected_cut_38781

theorem selected_cut_38782 : selected 9 ⟨1048373, by decide⟩
    (prefixPartial 12 302083) = some ⟨12, 1, 0, 1048373, 302083, 1, 65536⟩ := by
  decide +kernel

theorem context_12_302083_1048373 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302083 ⟨1048373, by decide⟩ :=
  accepted_of_selected 12 302083 ⟨1048373, by decide⟩ ⟨12, 1, 0, 1048373, 302083, 1, 65536⟩
    (by decide) selected_cut_38782

theorem unmarked_context_11_75520_1048374 : frontier 10 ⟨1048374, by decide⟩
    (prefixCache 11 75520) (prefixPartial 11 75520) = false := by
  decide +kernel

theorem node_context_11_75520_1048374 : EJMOriginalGlobalDAGData.nodes 10 ⟨1048374, by decide⟩ =
    .split (coordinate 11) (![⟨34034, by decide⟩,⟨1048287, by decide⟩,⟨1048372, by decide⟩,⟨1048373, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75520_1048374 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75520 ⟨1048374, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75520
    ⟨1048374, by decide⟩ (by decide) (![⟨34034, by decide⟩,⟨1048287, by decide⟩,⟨1048372, by decide⟩,⟨1048373, by decide⟩]) unmarked_context_11_75520_1048374 node_context_11_75520_1048374
  intro a
  fin_cases a
  · exact context_12_302080_34034
  · exact context_12_302081_1048287
  · exact context_12_302082_1048372
  · exact context_12_302083_1048373

theorem selected_cut_38783 : selected 9 ⟨1048498, by decide⟩
    (prefixPartial 12 302084) = some ⟨12, 2, 0, 1048498, 302084, 4037, 65536⟩ := by
  decide +kernel

theorem context_12_302084_1048498 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302084 ⟨1048498, by decide⟩ :=
  accepted_of_selected 12 302084 ⟨1048498, by decide⟩ ⟨12, 2, 0, 1048498, 302084, 4037, 65536⟩
    (by decide) selected_cut_38783

theorem selected_cut_38784 : selected 8 ⟨1048543, by decide⟩
    (prefixPartial 13 1208340) = some ⟨13, 2, 0, 1048543, 1208340, 1753, 16384⟩ := by
  decide +kernel

theorem context_13_1208340_1048543 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1208340 ⟨1048543, by decide⟩ :=
  accepted_of_selected 13 1208340 ⟨1048543, by decide⟩ ⟨13, 2, 0, 1048543, 1208340, 1753, 16384⟩
    (by decide) selected_cut_38784

theorem selected_cut_38785 : selected 8 ⟨1048564, by decide⟩
    (prefixPartial 13 1208341) = some ⟨13, 2, 0, 1048564, 1208341, 993, 16384⟩ := by
  decide +kernel

theorem context_13_1208341_1048564 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1208341 ⟨1048564, by decide⟩ :=
  accepted_of_selected 13 1208341 ⟨1048564, by decide⟩ ⟨13, 2, 0, 1048564, 1208341, 993, 16384⟩
    (by decide) selected_cut_38785

theorem selected_cut_38786 : selected 8 ⟨1048593, by decide⟩
    (prefixPartial 13 1208342) = some ⟨13, 2, 0, 1048593, 1208342, 1041, 16384⟩ := by
  decide +kernel

theorem context_13_1208342_1048593 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1208342 ⟨1048593, by decide⟩ :=
  accepted_of_selected 13 1208342 ⟨1048593, by decide⟩ ⟨13, 2, 0, 1048593, 1208342, 1041, 16384⟩
    (by decide) selected_cut_38786

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
