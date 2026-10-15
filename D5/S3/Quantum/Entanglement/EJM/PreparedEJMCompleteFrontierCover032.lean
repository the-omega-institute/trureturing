/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover031
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_03074 : selected 8 ⟨95283, by decide⟩
    (prefixPartial 13 26885) = some ⟨13, 2, 0, 95283, 26885, 3733, 16384⟩ := by
  decide +kernel

theorem context_13_26885_95283 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26885 ⟨95283, by decide⟩ :=
  accepted_of_selected 13 26885 ⟨95283, by decide⟩ ⟨13, 2, 0, 95283, 26885, 3733, 16384⟩
    (by decide) selected_cut_03074

theorem selected_cut_03075 : selected 8 ⟨95309, by decide⟩
    (prefixPartial 13 26886) = some ⟨13, 2, 0, 95309, 26886, 1865, 16384⟩ := by
  decide +kernel

theorem context_13_26886_95309 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26886 ⟨95309, by decide⟩ :=
  accepted_of_selected 13 26886 ⟨95309, by decide⟩ ⟨13, 2, 0, 95309, 26886, 1865, 16384⟩
    (by decide) selected_cut_03075

theorem selected_cut_03076 : selected 8 ⟨95325, by decide⟩
    (prefixPartial 13 26887) = some ⟨13, 2, 0, 95325, 26887, 1133, 16384⟩ := by
  decide +kernel

theorem context_13_26887_95325 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26887 ⟨95325, by decide⟩ :=
  accepted_of_selected 13 26887 ⟨95325, by decide⟩ ⟨13, 2, 0, 95325, 26887, 1133, 16384⟩
    (by decide) selected_cut_03076

theorem unmarked_context_12_6721_95326 : frontier 9 ⟨95326, by decide⟩
    (prefixCache 12 6721) (prefixPartial 12 6721) = false := by
  decide +kernel

theorem node_context_12_6721_95326 : EJMOriginalGlobalDAGData.nodes 9 ⟨95326, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨95283, by decide⟩,⟨95309, by decide⟩,⟨95325, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_6721_95326 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6721 ⟨95326, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 6721
    ⟨95326, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨95283, by decide⟩,⟨95309, by decide⟩,⟨95325, by decide⟩]) unmarked_context_12_6721_95326 node_context_12_6721_95326
  intro a
  fin_cases a
  · exact context_13_26884_3444
  · exact context_13_26885_95283
  · exact context_13_26886_95309
  · exact context_13_26887_95325

theorem selected_cut_03077 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 26888) = some ⟨13, 1, 0, 3444, 26888, 1, 16384⟩ := by
  decide +kernel

theorem context_13_26888_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26888 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 26888 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 26888, 1, 16384⟩
    (by decide) selected_cut_03077

theorem selected_cut_03078 : selected 8 ⟨95386, by decide⟩
    (prefixPartial 13 26889) = some ⟨13, 2, 0, 95386, 26889, 3681, 16384⟩ := by
  decide +kernel

theorem context_13_26889_95386 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26889 ⟨95386, by decide⟩ :=
  accepted_of_selected 13 26889 ⟨95386, by decide⟩ ⟨13, 2, 0, 95386, 26889, 3681, 16384⟩
    (by decide) selected_cut_03078

theorem selected_cut_03079 : selected 8 ⟨95412, by decide⟩
    (prefixPartial 13 26890) = some ⟨13, 2, 0, 95412, 26890, 2013, 16384⟩ := by
  decide +kernel

theorem context_13_26890_95412 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26890 ⟨95412, by decide⟩ :=
  accepted_of_selected 13 26890 ⟨95412, by decide⟩ ⟨13, 2, 0, 95412, 26890, 2013, 16384⟩
    (by decide) selected_cut_03079

theorem selected_cut_03080 : selected 8 ⟨95427, by decide⟩
    (prefixPartial 13 26891) = some ⟨13, 2, 0, 95427, 26891, 969, 16384⟩ := by
  decide +kernel

theorem context_13_26891_95427 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26891 ⟨95427, by decide⟩ :=
  accepted_of_selected 13 26891 ⟨95427, by decide⟩ ⟨13, 2, 0, 95427, 26891, 969, 16384⟩
    (by decide) selected_cut_03080

theorem unmarked_context_12_6722_95428 : frontier 9 ⟨95428, by decide⟩
    (prefixCache 12 6722) (prefixPartial 12 6722) = false := by
  decide +kernel

theorem node_context_12_6722_95428 : EJMOriginalGlobalDAGData.nodes 9 ⟨95428, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨95386, by decide⟩,⟨95412, by decide⟩,⟨95427, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_6722_95428 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6722 ⟨95428, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 6722
    ⟨95428, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨95386, by decide⟩,⟨95412, by decide⟩,⟨95427, by decide⟩]) unmarked_context_12_6722_95428 node_context_12_6722_95428
  intro a
  fin_cases a
  · exact context_13_26888_3444
  · exact context_13_26889_95386
  · exact context_13_26890_95412
  · exact context_13_26891_95427

theorem selected_cut_03081 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 26892) = some ⟨13, 1, 0, 3444, 26892, 1, 16384⟩ := by
  decide +kernel

theorem context_13_26892_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26892 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 26892 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 26892, 1, 16384⟩
    (by decide) selected_cut_03081

theorem selected_cut_03082 : selected 8 ⟨95487, by decide⟩
    (prefixPartial 13 26893) = some ⟨13, 2, 0, 95487, 26893, 3821, 16384⟩ := by
  decide +kernel

theorem context_13_26893_95487 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26893 ⟨95487, by decide⟩ :=
  accepted_of_selected 13 26893 ⟨95487, by decide⟩ ⟨13, 2, 0, 95487, 26893, 3821, 16384⟩
    (by decide) selected_cut_03082

theorem selected_cut_03083 : selected 8 ⟨95516, by decide⟩
    (prefixPartial 13 26894) = some ⟨13, 2, 0, 95516, 26894, 2129, 16384⟩ := by
  decide +kernel

theorem context_13_26894_95516 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26894 ⟨95516, by decide⟩ :=
  accepted_of_selected 13 26894 ⟨95516, by decide⟩ ⟨13, 2, 0, 95516, 26894, 2129, 16384⟩
    (by decide) selected_cut_03083

theorem selected_cut_03084 : selected 8 ⟨95533, by decide⟩
    (prefixPartial 13 26895) = some ⟨13, 2, 0, 95533, 26895, 1109, 16384⟩ := by
  decide +kernel

theorem context_13_26895_95533 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26895 ⟨95533, by decide⟩ :=
  accepted_of_selected 13 26895 ⟨95533, by decide⟩ ⟨13, 2, 0, 95533, 26895, 1109, 16384⟩
    (by decide) selected_cut_03084

theorem unmarked_context_12_6723_95534 : frontier 9 ⟨95534, by decide⟩
    (prefixCache 12 6723) (prefixPartial 12 6723) = false := by
  decide +kernel

theorem node_context_12_6723_95534 : EJMOriginalGlobalDAGData.nodes 9 ⟨95534, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨95487, by decide⟩,⟨95516, by decide⟩,⟨95533, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_6723_95534 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6723 ⟨95534, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 6723
    ⟨95534, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨95487, by decide⟩,⟨95516, by decide⟩,⟨95533, by decide⟩]) unmarked_context_12_6723_95534 node_context_12_6723_95534
  intro a
  fin_cases a
  · exact context_13_26892_3444
  · exact context_13_26893_95487
  · exact context_13_26894_95516
  · exact context_13_26895_95533

theorem unmarked_context_11_1680_95535 : frontier 10 ⟨95535, by decide⟩
    (prefixCache 11 1680) (prefixPartial 11 1680) = false := by
  decide +kernel

theorem node_context_11_1680_95535 : EJMOriginalGlobalDAGData.nodes 10 ⟨95535, by decide⟩ =
    .split (coordinate 11) (![⟨95214, by decide⟩,⟨95326, by decide⟩,⟨95428, by decide⟩,⟨95534, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1680_95535 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1680 ⟨95535, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1680
    ⟨95535, by decide⟩ (by decide) (![⟨95214, by decide⟩,⟨95326, by decide⟩,⟨95428, by decide⟩,⟨95534, by decide⟩]) unmarked_context_11_1680_95535 node_context_11_1680_95535
  intro a
  fin_cases a
  · exact context_12_6720_95214
  · exact context_12_6721_95326
  · exact context_12_6722_95428
  · exact context_12_6723_95534

theorem selected_cut_03085 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 26896) = some ⟨13, 1, 0, 3444, 26896, 1, 16384⟩ := by
  decide +kernel

theorem context_13_26896_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26896 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 26896 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 26896, 1, 16384⟩
    (by decide) selected_cut_03085

theorem selected_cut_03086 : selected 8 ⟨95615, by decide⟩
    (prefixPartial 13 26897) = some ⟨13, 2, 0, 95615, 26897, 2793, 16384⟩ := by
  decide +kernel

theorem context_13_26897_95615 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26897 ⟨95615, by decide⟩ :=
  accepted_of_selected 13 26897 ⟨95615, by decide⟩ ⟨13, 2, 0, 95615, 26897, 2793, 16384⟩
    (by decide) selected_cut_03086

theorem selected_cut_03087 : selected 8 ⟨95674, by decide⟩
    (prefixPartial 13 26898) = some ⟨13, 2, 0, 95674, 26898, 1785, 16384⟩ := by
  decide +kernel

theorem context_13_26898_95674 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26898 ⟨95674, by decide⟩ :=
  accepted_of_selected 13 26898 ⟨95674, by decide⟩ ⟨13, 2, 0, 95674, 26898, 1785, 16384⟩
    (by decide) selected_cut_03087

theorem selected_cut_03088 : selected 8 ⟨95699, by decide⟩
    (prefixPartial 13 26899) = some ⟨13, 2, 0, 95699, 26899, 881, 16384⟩ := by
  decide +kernel

theorem context_13_26899_95699 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26899 ⟨95699, by decide⟩ :=
  accepted_of_selected 13 26899 ⟨95699, by decide⟩ ⟨13, 2, 0, 95699, 26899, 881, 16384⟩
    (by decide) selected_cut_03088

theorem unmarked_context_12_6724_95700 : frontier 9 ⟨95700, by decide⟩
    (prefixCache 12 6724) (prefixPartial 12 6724) = false := by
  decide +kernel

theorem node_context_12_6724_95700 : EJMOriginalGlobalDAGData.nodes 9 ⟨95700, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨95615, by decide⟩,⟨95674, by decide⟩,⟨95699, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_6724_95700 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6724 ⟨95700, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 6724
    ⟨95700, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨95615, by decide⟩,⟨95674, by decide⟩,⟨95699, by decide⟩]) unmarked_context_12_6724_95700 node_context_12_6724_95700
  intro a
  fin_cases a
  · exact context_13_26896_3444
  · exact context_13_26897_95615
  · exact context_13_26898_95674
  · exact context_13_26899_95699

theorem selected_cut_03089 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 26900) = some ⟨13, 1, 0, 3444, 26900, 1, 16384⟩ := by
  decide +kernel

theorem context_13_26900_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26900 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 26900 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 26900, 1, 16384⟩
    (by decide) selected_cut_03089

theorem selected_cut_03090 : selected 8 ⟨95775, by decide⟩
    (prefixPartial 13 26901) = some ⟨13, 2, 0, 95775, 26901, 3969, 16384⟩ := by
  decide +kernel

theorem context_13_26901_95775 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26901 ⟨95775, by decide⟩ :=
  accepted_of_selected 13 26901 ⟨95775, by decide⟩ ⟨13, 2, 0, 95775, 26901, 3969, 16384⟩
    (by decide) selected_cut_03090

theorem selected_cut_03091 : selected 8 ⟨95814, by decide⟩
    (prefixPartial 13 26902) = some ⟨13, 2, 0, 95814, 26902, 2533, 16384⟩ := by
  decide +kernel

theorem context_13_26902_95814 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26902 ⟨95814, by decide⟩ :=
  accepted_of_selected 13 26902 ⟨95814, by decide⟩ ⟨13, 2, 0, 95814, 26902, 2533, 16384⟩
    (by decide) selected_cut_03091

theorem selected_cut_03092 : selected 8 ⟨95835, by decide⟩
    (prefixPartial 13 26903) = some ⟨13, 2, 0, 95835, 26903, 1361, 16384⟩ := by
  decide +kernel

theorem context_13_26903_95835 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26903 ⟨95835, by decide⟩ :=
  accepted_of_selected 13 26903 ⟨95835, by decide⟩ ⟨13, 2, 0, 95835, 26903, 1361, 16384⟩
    (by decide) selected_cut_03092

theorem unmarked_context_12_6725_95836 : frontier 9 ⟨95836, by decide⟩
    (prefixCache 12 6725) (prefixPartial 12 6725) = false := by
  decide +kernel

theorem node_context_12_6725_95836 : EJMOriginalGlobalDAGData.nodes 9 ⟨95836, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨95775, by decide⟩,⟨95814, by decide⟩,⟨95835, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_6725_95836 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6725 ⟨95836, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 6725
    ⟨95836, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨95775, by decide⟩,⟨95814, by decide⟩,⟨95835, by decide⟩]) unmarked_context_12_6725_95836 node_context_12_6725_95836
  intro a
  fin_cases a
  · exact context_13_26900_3444
  · exact context_13_26901_95775
  · exact context_13_26902_95814
  · exact context_13_26903_95835

theorem selected_cut_03093 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 26904) = some ⟨13, 1, 0, 3444, 26904, 1, 16384⟩ := by
  decide +kernel

theorem context_13_26904_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26904 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 26904 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 26904, 1, 16384⟩
    (by decide) selected_cut_03093

theorem selected_cut_03094 : selected 8 ⟨95924, by decide⟩
    (prefixPartial 13 26905) = some ⟨13, 2, 0, 95924, 26905, 3853, 16384⟩ := by
  decide +kernel

theorem context_13_26905_95924 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26905 ⟨95924, by decide⟩ :=
  accepted_of_selected 13 26905 ⟨95924, by decide⟩ ⟨13, 2, 0, 95924, 26905, 3853, 16384⟩
    (by decide) selected_cut_03094

theorem selected_cut_03095 : selected 8 ⟨95971, by decide⟩
    (prefixPartial 13 26906) = some ⟨13, 2, 0, 95971, 26906, 2705, 16384⟩ := by
  decide +kernel

theorem context_13_26906_95971 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26906 ⟨95971, by decide⟩ :=
  accepted_of_selected 13 26906 ⟨95971, by decide⟩ ⟨13, 2, 0, 95971, 26906, 2705, 16384⟩
    (by decide) selected_cut_03095

theorem selected_cut_03096 : selected 8 ⟨95996, by decide⟩
    (prefixPartial 13 26907) = some ⟨13, 2, 0, 95996, 26907, 1285, 16384⟩ := by
  decide +kernel

theorem context_13_26907_95996 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26907 ⟨95996, by decide⟩ :=
  accepted_of_selected 13 26907 ⟨95996, by decide⟩ ⟨13, 2, 0, 95996, 26907, 1285, 16384⟩
    (by decide) selected_cut_03096

theorem unmarked_context_12_6726_95997 : frontier 9 ⟨95997, by decide⟩
    (prefixCache 12 6726) (prefixPartial 12 6726) = false := by
  decide +kernel

theorem node_context_12_6726_95997 : EJMOriginalGlobalDAGData.nodes 9 ⟨95997, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨95924, by decide⟩,⟨95971, by decide⟩,⟨95996, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_6726_95997 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6726 ⟨95997, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 6726
    ⟨95997, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨95924, by decide⟩,⟨95971, by decide⟩,⟨95996, by decide⟩]) unmarked_context_12_6726_95997 node_context_12_6726_95997
  intro a
  fin_cases a
  · exact context_13_26904_3444
  · exact context_13_26905_95924
  · exact context_13_26906_95971
  · exact context_13_26907_95996

theorem selected_cut_03097 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 26908) = some ⟨13, 1, 0, 3444, 26908, 1, 16384⟩ := by
  decide +kernel

theorem context_13_26908_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26908 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 26908 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 26908, 1, 16384⟩
    (by decide) selected_cut_03097

theorem selected_cut_03098 : selected 8 ⟨96075, by decide⟩
    (prefixPartial 13 26909) = some ⟨13, 2, 0, 96075, 26909, 3949, 16384⟩ := by
  decide +kernel

theorem context_13_26909_96075 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26909 ⟨96075, by decide⟩ :=
  accepted_of_selected 13 26909 ⟨96075, by decide⟩ ⟨13, 2, 0, 96075, 26909, 3949, 16384⟩
    (by decide) selected_cut_03098

theorem selected_cut_03099 : selected 8 ⟨96141, by decide⟩
    (prefixPartial 13 26910) = some ⟨13, 2, 0, 96141, 26910, 3025, 16384⟩ := by
  decide +kernel

theorem context_13_26910_96141 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26910 ⟨96141, by decide⟩ :=
  accepted_of_selected 13 26910 ⟨96141, by decide⟩ ⟨13, 2, 0, 96141, 26910, 3025, 16384⟩
    (by decide) selected_cut_03099

theorem selected_cut_03100 : selected 8 ⟨96165, by decide⟩
    (prefixPartial 13 26911) = some ⟨13, 2, 0, 96165, 26911, 1361, 16384⟩ := by
  decide +kernel

theorem context_13_26911_96165 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26911 ⟨96165, by decide⟩ :=
  accepted_of_selected 13 26911 ⟨96165, by decide⟩ ⟨13, 2, 0, 96165, 26911, 1361, 16384⟩
    (by decide) selected_cut_03100

theorem unmarked_context_12_6727_96166 : frontier 9 ⟨96166, by decide⟩
    (prefixCache 12 6727) (prefixPartial 12 6727) = false := by
  decide +kernel

theorem node_context_12_6727_96166 : EJMOriginalGlobalDAGData.nodes 9 ⟨96166, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨96075, by decide⟩,⟨96141, by decide⟩,⟨96165, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_6727_96166 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6727 ⟨96166, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 6727
    ⟨96166, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨96075, by decide⟩,⟨96141, by decide⟩,⟨96165, by decide⟩]) unmarked_context_12_6727_96166 node_context_12_6727_96166
  intro a
  fin_cases a
  · exact context_13_26908_3444
  · exact context_13_26909_96075
  · exact context_13_26910_96141
  · exact context_13_26911_96165

theorem unmarked_context_11_1681_96167 : frontier 10 ⟨96167, by decide⟩
    (prefixCache 11 1681) (prefixPartial 11 1681) = false := by
  decide +kernel

theorem node_context_11_1681_96167 : EJMOriginalGlobalDAGData.nodes 10 ⟨96167, by decide⟩ =
    .split (coordinate 11) (![⟨95700, by decide⟩,⟨95836, by decide⟩,⟨95997, by decide⟩,⟨96166, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1681_96167 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1681 ⟨96167, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1681
    ⟨96167, by decide⟩ (by decide) (![⟨95700, by decide⟩,⟨95836, by decide⟩,⟨95997, by decide⟩,⟨96166, by decide⟩]) unmarked_context_11_1681_96167 node_context_11_1681_96167
  intro a
  fin_cases a
  · exact context_12_6724_95700
  · exact context_12_6725_95836
  · exact context_12_6726_95997
  · exact context_12_6727_96166

theorem selected_cut_03101 : selected 9 ⟨96259, by decide⟩
    (prefixPartial 12 6728) = some ⟨12, 2, 0, 96259, 6728, 3717, 65536⟩ := by
  decide +kernel

theorem context_12_6728_96259 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6728 ⟨96259, by decide⟩ :=
  accepted_of_selected 12 6728 ⟨96259, by decide⟩ ⟨12, 2, 0, 96259, 6728, 3717, 65536⟩
    (by decide) selected_cut_03101

theorem selected_cut_03102 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 26916) = some ⟨13, 1, 0, 3444, 26916, 1, 16384⟩ := by
  decide +kernel

theorem context_13_26916_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26916 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 26916 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 26916, 1, 16384⟩
    (by decide) selected_cut_03102

theorem selected_cut_03103 : selected 8 ⟨96293, by decide⟩
    (prefixPartial 13 26917) = some ⟨13, 2, 0, 96293, 26917, 2557, 16384⟩ := by
  decide +kernel

theorem context_13_26917_96293 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26917 ⟨96293, by decide⟩ :=
  accepted_of_selected 13 26917 ⟨96293, by decide⟩ ⟨13, 2, 0, 96293, 26917, 2557, 16384⟩
    (by decide) selected_cut_03103

theorem selected_cut_03104 : selected 8 ⟨96333, by decide⟩
    (prefixPartial 13 26918) = some ⟨13, 2, 0, 96333, 26918, 2041, 16384⟩ := by
  decide +kernel

theorem context_13_26918_96333 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26918 ⟨96333, by decide⟩ :=
  accepted_of_selected 13 26918 ⟨96333, by decide⟩ ⟨13, 2, 0, 96333, 26918, 2041, 16384⟩
    (by decide) selected_cut_03104

theorem selected_cut_03105 : selected 8 ⟨96354, by decide⟩
    (prefixPartial 13 26919) = some ⟨13, 2, 0, 96354, 26919, 1153, 16384⟩ := by
  decide +kernel

theorem context_13_26919_96354 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26919 ⟨96354, by decide⟩ :=
  accepted_of_selected 13 26919 ⟨96354, by decide⟩ ⟨13, 2, 0, 96354, 26919, 1153, 16384⟩
    (by decide) selected_cut_03105

theorem unmarked_context_12_6729_96355 : frontier 9 ⟨96355, by decide⟩
    (prefixCache 12 6729) (prefixPartial 12 6729) = false := by
  decide +kernel

theorem node_context_12_6729_96355 : EJMOriginalGlobalDAGData.nodes 9 ⟨96355, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨96293, by decide⟩,⟨96333, by decide⟩,⟨96354, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_6729_96355 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6729 ⟨96355, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 6729
    ⟨96355, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨96293, by decide⟩,⟨96333, by decide⟩,⟨96354, by decide⟩]) unmarked_context_12_6729_96355 node_context_12_6729_96355
  intro a
  fin_cases a
  · exact context_13_26916_3444
  · exact context_13_26917_96293
  · exact context_13_26918_96333
  · exact context_13_26919_96354

theorem selected_cut_03106 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 26920) = some ⟨13, 1, 0, 3444, 26920, 1, 16384⟩ := by
  decide +kernel

theorem context_13_26920_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26920 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 26920 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 26920, 1, 16384⟩
    (by decide) selected_cut_03106

theorem selected_cut_03107 : selected 8 ⟨96470, by decide⟩
    (prefixPartial 13 26921) = some ⟨13, 2, 0, 96470, 26921, 3885, 16384⟩ := by
  decide +kernel

theorem context_13_26921_96470 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26921 ⟨96470, by decide⟩ :=
  accepted_of_selected 13 26921 ⟨96470, by decide⟩ ⟨13, 2, 0, 96470, 26921, 3885, 16384⟩
    (by decide) selected_cut_03107

theorem selected_cut_03108 : selected 8 ⟨96586, by decide⟩
    (prefixPartial 13 26922) = some ⟨13, 2, 0, 96586, 26922, 3597, 16384⟩ := by
  decide +kernel

theorem context_13_26922_96586 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26922 ⟨96586, by decide⟩ :=
  accepted_of_selected 13 26922 ⟨96586, by decide⟩ ⟨13, 2, 0, 96586, 26922, 3597, 16384⟩
    (by decide) selected_cut_03108

theorem selected_cut_03109 : selected 8 ⟨96632, by decide⟩
    (prefixPartial 13 26923) = some ⟨13, 2, 0, 96632, 26923, 1353, 16384⟩ := by
  decide +kernel

theorem context_13_26923_96632 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26923 ⟨96632, by decide⟩ :=
  accepted_of_selected 13 26923 ⟨96632, by decide⟩ ⟨13, 2, 0, 96632, 26923, 1353, 16384⟩
    (by decide) selected_cut_03109

theorem unmarked_context_12_6730_96633 : frontier 9 ⟨96633, by decide⟩
    (prefixCache 12 6730) (prefixPartial 12 6730) = false := by
  decide +kernel

theorem node_context_12_6730_96633 : EJMOriginalGlobalDAGData.nodes 9 ⟨96633, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨96470, by decide⟩,⟨96586, by decide⟩,⟨96632, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_6730_96633 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6730 ⟨96633, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 6730
    ⟨96633, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨96470, by decide⟩,⟨96586, by decide⟩,⟨96632, by decide⟩]) unmarked_context_12_6730_96633 node_context_12_6730_96633
  intro a
  fin_cases a
  · exact context_13_26920_3444
  · exact context_13_26921_96470
  · exact context_13_26922_96586
  · exact context_13_26923_96632

theorem selected_cut_03110 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 26924) = some ⟨13, 1, 0, 3444, 26924, 1, 16384⟩ := by
  decide +kernel

theorem context_13_26924_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26924 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 26924 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 26924, 1, 16384⟩
    (by decide) selected_cut_03110

theorem selected_cut_03111 : selected 8 ⟨96684, by decide⟩
    (prefixPartial 13 26925) = some ⟨13, 2, 0, 96684, 26925, 2525, 16384⟩ := by
  decide +kernel

theorem context_13_26925_96684 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26925 ⟨96684, by decide⟩ :=
  accepted_of_selected 13 26925 ⟨96684, by decide⟩ ⟨13, 2, 0, 96684, 26925, 2525, 16384⟩
    (by decide) selected_cut_03111

theorem selected_cut_03112 : selected 8 ⟨96723, by decide⟩
    (prefixPartial 13 26926) = some ⟨13, 2, 0, 96723, 26926, 2241, 16384⟩ := by
  decide +kernel

theorem context_13_26926_96723 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26926 ⟨96723, by decide⟩ :=
  accepted_of_selected 13 26926 ⟨96723, by decide⟩ ⟨13, 2, 0, 96723, 26926, 2241, 16384⟩
    (by decide) selected_cut_03112

theorem selected_cut_03113 : selected 8 ⟨96736, by decide⟩
    (prefixPartial 13 26927) = some ⟨13, 2, 0, 96736, 26927, 1133, 16384⟩ := by
  decide +kernel

theorem context_13_26927_96736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26927 ⟨96736, by decide⟩ :=
  accepted_of_selected 13 26927 ⟨96736, by decide⟩ ⟨13, 2, 0, 96736, 26927, 1133, 16384⟩
    (by decide) selected_cut_03113

theorem unmarked_context_12_6731_96737 : frontier 9 ⟨96737, by decide⟩
    (prefixCache 12 6731) (prefixPartial 12 6731) = false := by
  decide +kernel

theorem node_context_12_6731_96737 : EJMOriginalGlobalDAGData.nodes 9 ⟨96737, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨96684, by decide⟩,⟨96723, by decide⟩,⟨96736, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_6731_96737 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6731 ⟨96737, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 6731
    ⟨96737, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨96684, by decide⟩,⟨96723, by decide⟩,⟨96736, by decide⟩]) unmarked_context_12_6731_96737 node_context_12_6731_96737
  intro a
  fin_cases a
  · exact context_13_26924_3444
  · exact context_13_26925_96684
  · exact context_13_26926_96723
  · exact context_13_26927_96736

theorem unmarked_context_11_1682_96738 : frontier 10 ⟨96738, by decide⟩
    (prefixCache 11 1682) (prefixPartial 11 1682) = false := by
  decide +kernel

theorem node_context_11_1682_96738 : EJMOriginalGlobalDAGData.nodes 10 ⟨96738, by decide⟩ =
    .split (coordinate 11) (![⟨96259, by decide⟩,⟨96355, by decide⟩,⟨96633, by decide⟩,⟨96737, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1682_96738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1682 ⟨96738, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1682
    ⟨96738, by decide⟩ (by decide) (![⟨96259, by decide⟩,⟨96355, by decide⟩,⟨96633, by decide⟩,⟨96737, by decide⟩]) unmarked_context_11_1682_96738 node_context_11_1682_96738
  intro a
  fin_cases a
  · exact context_12_6728_96259
  · exact context_12_6729_96355
  · exact context_12_6730_96633
  · exact context_12_6731_96737

theorem selected_cut_03114 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 26928) = some ⟨13, 1, 0, 3444, 26928, 1, 16384⟩ := by
  decide +kernel

theorem context_13_26928_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26928 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 26928 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 26928, 1, 16384⟩
    (by decide) selected_cut_03114

theorem selected_cut_03115 : selected 8 ⟨96790, by decide⟩
    (prefixPartial 13 26929) = some ⟨13, 2, 0, 96790, 26929, 1949, 16384⟩ := by
  decide +kernel

theorem context_13_26929_96790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26929 ⟨96790, by decide⟩ :=
  accepted_of_selected 13 26929 ⟨96790, by decide⟩ ⟨13, 2, 0, 96790, 26929, 1949, 16384⟩
    (by decide) selected_cut_03115

theorem selected_cut_03116 : selected 8 ⟨96843, by decide⟩
    (prefixPartial 13 26930) = some ⟨13, 2, 0, 96843, 26930, 1825, 16384⟩ := by
  decide +kernel

theorem context_13_26930_96843 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26930 ⟨96843, by decide⟩ :=
  accepted_of_selected 13 26930 ⟨96843, by decide⟩ ⟨13, 2, 0, 96843, 26930, 1825, 16384⟩
    (by decide) selected_cut_03116

theorem selected_cut_03117 : selected 8 ⟨96875, by decide⟩
    (prefixPartial 13 26931) = some ⟨13, 2, 0, 96875, 26931, 985, 16384⟩ := by
  decide +kernel

theorem context_13_26931_96875 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26931 ⟨96875, by decide⟩ :=
  accepted_of_selected 13 26931 ⟨96875, by decide⟩ ⟨13, 2, 0, 96875, 26931, 985, 16384⟩
    (by decide) selected_cut_03117

theorem unmarked_context_12_6732_96876 : frontier 9 ⟨96876, by decide⟩
    (prefixCache 12 6732) (prefixPartial 12 6732) = false := by
  decide +kernel

theorem node_context_12_6732_96876 : EJMOriginalGlobalDAGData.nodes 9 ⟨96876, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨96790, by decide⟩,⟨96843, by decide⟩,⟨96875, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_6732_96876 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6732 ⟨96876, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 6732
    ⟨96876, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨96790, by decide⟩,⟨96843, by decide⟩,⟨96875, by decide⟩]) unmarked_context_12_6732_96876 node_context_12_6732_96876
  intro a
  fin_cases a
  · exact context_13_26928_3444
  · exact context_13_26929_96790
  · exact context_13_26930_96843
  · exact context_13_26931_96875

theorem selected_cut_03118 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 26932) = some ⟨13, 1, 0, 3444, 26932, 1, 16384⟩ := by
  decide +kernel

theorem context_13_26932_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26932 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 26932 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 26932, 1, 16384⟩
    (by decide) selected_cut_03118

theorem selected_cut_03119 : selected 8 ⟨96935, by decide⟩
    (prefixPartial 13 26933) = some ⟨13, 2, 0, 96935, 26933, 2853, 16384⟩ := by
  decide +kernel

theorem context_13_26933_96935 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26933 ⟨96935, by decide⟩ :=
  accepted_of_selected 13 26933 ⟨96935, by decide⟩ ⟨13, 2, 0, 96935, 26933, 2853, 16384⟩
    (by decide) selected_cut_03119

theorem selected_cut_03120 : selected 8 ⟨96979, by decide⟩
    (prefixPartial 13 26934) = some ⟨13, 2, 0, 96979, 26934, 2593, 16384⟩ := by
  decide +kernel

theorem context_13_26934_96979 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26934 ⟨96979, by decide⟩ :=
  accepted_of_selected 13 26934 ⟨96979, by decide⟩ ⟨13, 2, 0, 96979, 26934, 2593, 16384⟩
    (by decide) selected_cut_03120

theorem selected_cut_03121 : selected 8 ⟨97000, by decide⟩
    (prefixPartial 13 26935) = some ⟨13, 2, 0, 97000, 26935, 1437, 16384⟩ := by
  decide +kernel

theorem context_13_26935_97000 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26935 ⟨97000, by decide⟩ :=
  accepted_of_selected 13 26935 ⟨97000, by decide⟩ ⟨13, 2, 0, 97000, 26935, 1437, 16384⟩
    (by decide) selected_cut_03121

theorem unmarked_context_12_6733_97001 : frontier 9 ⟨97001, by decide⟩
    (prefixCache 12 6733) (prefixPartial 12 6733) = false := by
  decide +kernel

theorem node_context_12_6733_97001 : EJMOriginalGlobalDAGData.nodes 9 ⟨97001, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨96935, by decide⟩,⟨96979, by decide⟩,⟨97000, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_6733_97001 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6733 ⟨97001, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 6733
    ⟨97001, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨96935, by decide⟩,⟨96979, by decide⟩,⟨97000, by decide⟩]) unmarked_context_12_6733_97001 node_context_12_6733_97001
  intro a
  fin_cases a
  · exact context_13_26932_3444
  · exact context_13_26933_96935
  · exact context_13_26934_96979
  · exact context_13_26935_97000

theorem selected_cut_03122 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 26936) = some ⟨13, 1, 0, 3444, 26936, 1, 16384⟩ := by
  decide +kernel

theorem context_13_26936_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26936 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 26936 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 26936, 1, 16384⟩
    (by decide) selected_cut_03122

theorem selected_cut_03123 : selected 8 ⟨97056, by decide⟩
    (prefixPartial 13 26937) = some ⟨13, 2, 0, 97056, 26937, 2773, 16384⟩ := by
  decide +kernel

theorem context_13_26937_97056 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26937 ⟨97056, by decide⟩ :=
  accepted_of_selected 13 26937 ⟨97056, by decide⟩ ⟨13, 2, 0, 97056, 26937, 2773, 16384⟩
    (by decide) selected_cut_03123

theorem selected_cut_03124 : selected 8 ⟨97114, by decide⟩
    (prefixPartial 13 26938) = some ⟨13, 2, 0, 97114, 26938, 2673, 16384⟩ := by
  decide +kernel

theorem context_13_26938_97114 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26938 ⟨97114, by decide⟩ :=
  accepted_of_selected 13 26938 ⟨97114, by decide⟩ ⟨13, 2, 0, 97114, 26938, 2673, 16384⟩
    (by decide) selected_cut_03124

theorem selected_cut_03125 : selected 8 ⟨97151, by decide⟩
    (prefixPartial 13 26939) = some ⟨13, 2, 0, 97151, 26939, 1257, 16384⟩ := by
  decide +kernel

theorem context_13_26939_97151 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26939 ⟨97151, by decide⟩ :=
  accepted_of_selected 13 26939 ⟨97151, by decide⟩ ⟨13, 2, 0, 97151, 26939, 1257, 16384⟩
    (by decide) selected_cut_03125

theorem unmarked_context_12_6734_97152 : frontier 9 ⟨97152, by decide⟩
    (prefixCache 12 6734) (prefixPartial 12 6734) = false := by
  decide +kernel

theorem node_context_12_6734_97152 : EJMOriginalGlobalDAGData.nodes 9 ⟨97152, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨97056, by decide⟩,⟨97114, by decide⟩,⟨97151, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_6734_97152 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6734 ⟨97152, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 6734
    ⟨97152, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨97056, by decide⟩,⟨97114, by decide⟩,⟨97151, by decide⟩]) unmarked_context_12_6734_97152 node_context_12_6734_97152
  intro a
  fin_cases a
  · exact context_13_26936_3444
  · exact context_13_26937_97056
  · exact context_13_26938_97114
  · exact context_13_26939_97151

theorem selected_cut_03126 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 26940) = some ⟨13, 1, 0, 3444, 26940, 1, 16384⟩ := by
  decide +kernel

theorem context_13_26940_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26940 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 26940 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 26940, 1, 16384⟩
    (by decide) selected_cut_03126

theorem selected_cut_03127 : selected 8 ⟨97207, by decide⟩
    (prefixPartial 13 26941) = some ⟨13, 2, 0, 97207, 26941, 2513, 16384⟩ := by
  decide +kernel

theorem context_13_26941_97207 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26941 ⟨97207, by decide⟩ :=
  accepted_of_selected 13 26941 ⟨97207, by decide⟩ ⟨13, 2, 0, 97207, 26941, 2513, 16384⟩
    (by decide) selected_cut_03127

theorem selected_cut_03128 : selected 8 ⟨97238, by decide⟩
    (prefixPartial 13 26942) = some ⟨13, 2, 0, 97238, 26942, 2669, 16384⟩ := by
  decide +kernel

theorem context_13_26942_97238 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26942 ⟨97238, by decide⟩ :=
  accepted_of_selected 13 26942 ⟨97238, by decide⟩ ⟨13, 2, 0, 97238, 26942, 2669, 16384⟩
    (by decide) selected_cut_03128

theorem selected_cut_03129 : selected 8 ⟨97259, by decide⟩
    (prefixPartial 13 26943) = some ⟨13, 2, 0, 97259, 26943, 1429, 16384⟩ := by
  decide +kernel

theorem context_13_26943_97259 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26943 ⟨97259, by decide⟩ :=
  accepted_of_selected 13 26943 ⟨97259, by decide⟩ ⟨13, 2, 0, 97259, 26943, 1429, 16384⟩
    (by decide) selected_cut_03129

theorem unmarked_context_12_6735_97260 : frontier 9 ⟨97260, by decide⟩
    (prefixCache 12 6735) (prefixPartial 12 6735) = false := by
  decide +kernel

theorem node_context_12_6735_97260 : EJMOriginalGlobalDAGData.nodes 9 ⟨97260, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨97207, by decide⟩,⟨97238, by decide⟩,⟨97259, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_6735_97260 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6735 ⟨97260, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 6735
    ⟨97260, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨97207, by decide⟩,⟨97238, by decide⟩,⟨97259, by decide⟩]) unmarked_context_12_6735_97260 node_context_12_6735_97260
  intro a
  fin_cases a
  · exact context_13_26940_3444
  · exact context_13_26941_97207
  · exact context_13_26942_97238
  · exact context_13_26943_97259

theorem unmarked_context_11_1683_97261 : frontier 10 ⟨97261, by decide⟩
    (prefixCache 11 1683) (prefixPartial 11 1683) = false := by
  decide +kernel

theorem node_context_11_1683_97261 : EJMOriginalGlobalDAGData.nodes 10 ⟨97261, by decide⟩ =
    .split (coordinate 11) (![⟨96876, by decide⟩,⟨97001, by decide⟩,⟨97152, by decide⟩,⟨97260, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1683_97261 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1683 ⟨97261, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1683
    ⟨97261, by decide⟩ (by decide) (![⟨96876, by decide⟩,⟨97001, by decide⟩,⟨97152, by decide⟩,⟨97260, by decide⟩]) unmarked_context_11_1683_97261 node_context_11_1683_97261
  intro a
  fin_cases a
  · exact context_12_6732_96876
  · exact context_12_6733_97001
  · exact context_12_6734_97152
  · exact context_12_6735_97260

theorem unmarked_context_10_420_97262 : frontier 11 ⟨97262, by decide⟩
    (prefixCache 10 420) (prefixPartial 10 420) = false := by
  decide +kernel

theorem node_context_10_420_97262 : EJMOriginalGlobalDAGData.nodes 11 ⟨97262, by decide⟩ =
    .split (coordinate 10) (![⟨95535, by decide⟩,⟨96167, by decide⟩,⟨96738, by decide⟩,⟨97261, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_420_97262 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 420 ⟨97262, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 420
    ⟨97262, by decide⟩ (by decide) (![⟨95535, by decide⟩,⟨96167, by decide⟩,⟨96738, by decide⟩,⟨97261, by decide⟩]) unmarked_context_10_420_97262 node_context_10_420_97262
  intro a
  fin_cases a
  · exact context_11_1680_95535
  · exact context_11_1681_96167
  · exact context_11_1682_96738
  · exact context_11_1683_97261

theorem selected_cut_03130 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 6736) = some ⟨12, 1, 0, 1738, 6736, 1, 65536⟩ := by
  decide +kernel

theorem context_12_6736_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6736 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 6736 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 6736, 1, 65536⟩
    (by decide) selected_cut_03130

theorem selected_cut_03131 : selected 9 ⟨97390, by decide⟩
    (prefixPartial 12 6737) = some ⟨12, 2, 0, 97390, 6737, 3753, 65536⟩ := by
  decide +kernel

theorem context_12_6737_97390 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6737 ⟨97390, by decide⟩ :=
  accepted_of_selected 12 6737 ⟨97390, by decide⟩ ⟨12, 2, 0, 97390, 6737, 3753, 65536⟩
    (by decide) selected_cut_03131

theorem selected_cut_03132 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 26952) = some ⟨13, 1, 0, 3444, 26952, 1, 16384⟩ := by
  decide +kernel

theorem context_13_26952_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26952 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 26952 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 26952, 1, 16384⟩
    (by decide) selected_cut_03132

theorem selected_cut_03133 : selected 8 ⟨97459, by decide⟩
    (prefixPartial 13 26953) = some ⟨13, 2, 0, 97459, 26953, 2417, 16384⟩ := by
  decide +kernel

theorem context_13_26953_97459 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26953 ⟨97459, by decide⟩ :=
  accepted_of_selected 13 26953 ⟨97459, by decide⟩ ⟨13, 2, 0, 97459, 26953, 2417, 16384⟩
    (by decide) selected_cut_03133

theorem selected_cut_03134 : selected 8 ⟨97483, by decide⟩
    (prefixPartial 13 26954) = some ⟨13, 2, 0, 97483, 26954, 1901, 16384⟩ := by
  decide +kernel

theorem context_13_26954_97483 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26954 ⟨97483, by decide⟩ :=
  accepted_of_selected 13 26954 ⟨97483, by decide⟩ ⟨13, 2, 0, 97483, 26954, 1901, 16384⟩
    (by decide) selected_cut_03134

theorem selected_cut_03135 : selected 8 ⟨97501, by decide⟩
    (prefixPartial 13 26955) = some ⟨13, 2, 0, 97501, 26955, 1113, 16384⟩ := by
  decide +kernel

theorem context_13_26955_97501 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26955 ⟨97501, by decide⟩ :=
  accepted_of_selected 13 26955 ⟨97501, by decide⟩ ⟨13, 2, 0, 97501, 26955, 1113, 16384⟩
    (by decide) selected_cut_03135

theorem unmarked_context_12_6738_97502 : frontier 9 ⟨97502, by decide⟩
    (prefixCache 12 6738) (prefixPartial 12 6738) = false := by
  decide +kernel

theorem node_context_12_6738_97502 : EJMOriginalGlobalDAGData.nodes 9 ⟨97502, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨97459, by decide⟩,⟨97483, by decide⟩,⟨97501, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_6738_97502 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6738 ⟨97502, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 6738
    ⟨97502, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨97459, by decide⟩,⟨97483, by decide⟩,⟨97501, by decide⟩]) unmarked_context_12_6738_97502 node_context_12_6738_97502
  intro a
  fin_cases a
  · exact context_13_26952_3444
  · exact context_13_26953_97459
  · exact context_13_26954_97483
  · exact context_13_26955_97501

theorem selected_cut_03136 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 26956) = some ⟨13, 1, 0, 3444, 26956, 1, 16384⟩ := by
  decide +kernel

theorem context_13_26956_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26956 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 26956 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 26956, 1, 16384⟩
    (by decide) selected_cut_03136

theorem selected_cut_03137 : selected 8 ⟨97570, by decide⟩
    (prefixPartial 13 26957) = some ⟨13, 2, 0, 97570, 26957, 2513, 16384⟩ := by
  decide +kernel

theorem context_13_26957_97570 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26957 ⟨97570, by decide⟩ :=
  accepted_of_selected 13 26957 ⟨97570, by decide⟩ ⟨13, 2, 0, 97570, 26957, 2513, 16384⟩
    (by decide) selected_cut_03137

theorem selected_cut_03138 : selected 8 ⟨97615, by decide⟩
    (prefixPartial 13 26958) = some ⟨13, 2, 0, 97615, 26958, 2161, 16384⟩ := by
  decide +kernel

theorem context_13_26958_97615 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26958 ⟨97615, by decide⟩ :=
  accepted_of_selected 13 26958 ⟨97615, by decide⟩ ⟨13, 2, 0, 97615, 26958, 2161, 16384⟩
    (by decide) selected_cut_03138

theorem selected_cut_03139 : selected 8 ⟨97641, by decide⟩
    (prefixPartial 13 26959) = some ⟨13, 2, 0, 97641, 26959, 1265, 16384⟩ := by
  decide +kernel

theorem context_13_26959_97641 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26959 ⟨97641, by decide⟩ :=
  accepted_of_selected 13 26959 ⟨97641, by decide⟩ ⟨13, 2, 0, 97641, 26959, 1265, 16384⟩
    (by decide) selected_cut_03139

theorem unmarked_context_12_6739_97642 : frontier 9 ⟨97642, by decide⟩
    (prefixCache 12 6739) (prefixPartial 12 6739) = false := by
  decide +kernel

theorem node_context_12_6739_97642 : EJMOriginalGlobalDAGData.nodes 9 ⟨97642, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨97570, by decide⟩,⟨97615, by decide⟩,⟨97641, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_6739_97642 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6739 ⟨97642, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 6739
    ⟨97642, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨97570, by decide⟩,⟨97615, by decide⟩,⟨97641, by decide⟩]) unmarked_context_12_6739_97642 node_context_12_6739_97642
  intro a
  fin_cases a
  · exact context_13_26956_3444
  · exact context_13_26957_97570
  · exact context_13_26958_97615
  · exact context_13_26959_97641

theorem unmarked_context_11_1684_97643 : frontier 10 ⟨97643, by decide⟩
    (prefixCache 11 1684) (prefixPartial 11 1684) = false := by
  decide +kernel

theorem node_context_11_1684_97643 : EJMOriginalGlobalDAGData.nodes 10 ⟨97643, by decide⟩ =
    .split (coordinate 11) (![⟨1738, by decide⟩,⟨97390, by decide⟩,⟨97502, by decide⟩,⟨97642, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1684_97643 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1684 ⟨97643, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1684
    ⟨97643, by decide⟩ (by decide) (![⟨1738, by decide⟩,⟨97390, by decide⟩,⟨97502, by decide⟩,⟨97642, by decide⟩]) unmarked_context_11_1684_97643 node_context_11_1684_97643
  intro a
  fin_cases a
  · exact context_12_6736_1738
  · exact context_12_6737_97390
  · exact context_12_6738_97502
  · exact context_12_6739_97642

theorem selected_cut_03140 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 6740) = some ⟨12, 1, 0, 1738, 6740, 1, 65536⟩ := by
  decide +kernel

theorem context_12_6740_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6740 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 6740 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 6740, 1, 65536⟩
    (by decide) selected_cut_03140

theorem selected_cut_03141 : selected 9 ⟨97739, by decide⟩
    (prefixPartial 12 6741) = some ⟨12, 2, 0, 97739, 6741, 3953, 65536⟩ := by
  decide +kernel

theorem context_12_6741_97739 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6741 ⟨97739, by decide⟩ :=
  accepted_of_selected 12 6741 ⟨97739, by decide⟩ ⟨12, 2, 0, 97739, 6741, 3953, 65536⟩
    (by decide) selected_cut_03141

theorem selected_cut_03142 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 26968) = some ⟨13, 1, 0, 3444, 26968, 1, 16384⟩ := by
  decide +kernel

theorem context_13_26968_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26968 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 26968 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 26968, 1, 16384⟩
    (by decide) selected_cut_03142

theorem selected_cut_03143 : selected 8 ⟨97786, by decide⟩
    (prefixPartial 13 26969) = some ⟨13, 2, 0, 97786, 26969, 1897, 16384⟩ := by
  decide +kernel

theorem context_13_26969_97786 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26969 ⟨97786, by decide⟩ :=
  accepted_of_selected 13 26969 ⟨97786, by decide⟩ ⟨13, 2, 0, 97786, 26969, 1897, 16384⟩
    (by decide) selected_cut_03143

theorem selected_cut_03144 : selected 8 ⟨97823, by decide⟩
    (prefixPartial 13 26970) = some ⟨13, 2, 0, 97823, 26970, 2317, 16384⟩ := by
  decide +kernel

theorem context_13_26970_97823 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26970 ⟨97823, by decide⟩ :=
  accepted_of_selected 13 26970 ⟨97823, by decide⟩ ⟨13, 2, 0, 97823, 26970, 2317, 16384⟩
    (by decide) selected_cut_03144

theorem selected_cut_03145 : selected 8 ⟨97846, by decide⟩
    (prefixPartial 13 26971) = some ⟨13, 2, 0, 97846, 26971, 1301, 16384⟩ := by
  decide +kernel

theorem context_13_26971_97846 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26971 ⟨97846, by decide⟩ :=
  accepted_of_selected 13 26971 ⟨97846, by decide⟩ ⟨13, 2, 0, 97846, 26971, 1301, 16384⟩
    (by decide) selected_cut_03145

theorem unmarked_context_12_6742_97847 : frontier 9 ⟨97847, by decide⟩
    (prefixCache 12 6742) (prefixPartial 12 6742) = false := by
  decide +kernel

theorem node_context_12_6742_97847 : EJMOriginalGlobalDAGData.nodes 9 ⟨97847, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨97786, by decide⟩,⟨97823, by decide⟩,⟨97846, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_6742_97847 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6742 ⟨97847, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 6742
    ⟨97847, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨97786, by decide⟩,⟨97823, by decide⟩,⟨97846, by decide⟩]) unmarked_context_12_6742_97847 node_context_12_6742_97847
  intro a
  fin_cases a
  · exact context_13_26968_3444
  · exact context_13_26969_97786
  · exact context_13_26970_97823
  · exact context_13_26971_97846

theorem selected_cut_03146 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 26972) = some ⟨13, 1, 0, 3444, 26972, 1, 16384⟩ := by
  decide +kernel

theorem context_13_26972_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26972 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 26972 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 26972, 1, 16384⟩
    (by decide) selected_cut_03146

theorem selected_cut_03147 : selected 8 ⟨97903, by decide⟩
    (prefixPartial 13 26973) = some ⟨13, 2, 0, 97903, 26973, 2053, 16384⟩ := by
  decide +kernel

theorem context_13_26973_97903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26973 ⟨97903, by decide⟩ :=
  accepted_of_selected 13 26973 ⟨97903, by decide⟩ ⟨13, 2, 0, 97903, 26973, 2053, 16384⟩
    (by decide) selected_cut_03147

theorem selected_cut_03148 : selected 8 ⟨97963, by decide⟩
    (prefixPartial 13 26974) = some ⟨13, 2, 0, 97963, 26974, 2797, 16384⟩ := by
  decide +kernel

theorem context_13_26974_97963 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26974 ⟨97963, by decide⟩ :=
  accepted_of_selected 13 26974 ⟨97963, by decide⟩ ⟨13, 2, 0, 97963, 26974, 2797, 16384⟩
    (by decide) selected_cut_03148

theorem selected_cut_03149 : selected 8 ⟨97983, by decide⟩
    (prefixPartial 13 26975) = some ⟨13, 2, 0, 97983, 26975, 1417, 16384⟩ := by
  decide +kernel

theorem context_13_26975_97983 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26975 ⟨97983, by decide⟩ :=
  accepted_of_selected 13 26975 ⟨97983, by decide⟩ ⟨13, 2, 0, 97983, 26975, 1417, 16384⟩
    (by decide) selected_cut_03149

theorem unmarked_context_12_6743_97984 : frontier 9 ⟨97984, by decide⟩
    (prefixCache 12 6743) (prefixPartial 12 6743) = false := by
  decide +kernel

theorem node_context_12_6743_97984 : EJMOriginalGlobalDAGData.nodes 9 ⟨97984, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨97903, by decide⟩,⟨97963, by decide⟩,⟨97983, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_6743_97984 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6743 ⟨97984, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 6743
    ⟨97984, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨97903, by decide⟩,⟨97963, by decide⟩,⟨97983, by decide⟩]) unmarked_context_12_6743_97984 node_context_12_6743_97984
  intro a
  fin_cases a
  · exact context_13_26972_3444
  · exact context_13_26973_97903
  · exact context_13_26974_97963
  · exact context_13_26975_97983

theorem unmarked_context_11_1685_97985 : frontier 10 ⟨97985, by decide⟩
    (prefixCache 11 1685) (prefixPartial 11 1685) = false := by
  decide +kernel

theorem node_context_11_1685_97985 : EJMOriginalGlobalDAGData.nodes 10 ⟨97985, by decide⟩ =
    .split (coordinate 11) (![⟨1738, by decide⟩,⟨97739, by decide⟩,⟨97847, by decide⟩,⟨97984, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1685_97985 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1685 ⟨97985, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1685
    ⟨97985, by decide⟩ (by decide) (![⟨1738, by decide⟩,⟨97739, by decide⟩,⟨97847, by decide⟩,⟨97984, by decide⟩]) unmarked_context_11_1685_97985 node_context_11_1685_97985
  intro a
  fin_cases a
  · exact context_12_6740_1738
  · exact context_12_6741_97739
  · exact context_12_6742_97847
  · exact context_12_6743_97984

theorem selected_cut_03150 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 6744) = some ⟨12, 1, 0, 1738, 6744, 1, 65536⟩ := by
  decide +kernel

theorem context_12_6744_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6744 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 6744 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 6744, 1, 65536⟩
    (by decide) selected_cut_03150

theorem selected_cut_03151 : selected 9 ⟨98100, by decide⟩
    (prefixPartial 12 6745) = some ⟨12, 2, 0, 98100, 6745, 3253, 65536⟩ := by
  decide +kernel

theorem context_12_6745_98100 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6745 ⟨98100, by decide⟩ :=
  accepted_of_selected 12 6745 ⟨98100, by decide⟩ ⟨12, 2, 0, 98100, 6745, 3253, 65536⟩
    (by decide) selected_cut_03151

theorem selected_cut_03152 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 26984) = some ⟨13, 1, 0, 3444, 26984, 1, 16384⟩ := by
  decide +kernel

theorem context_13_26984_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26984 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 26984 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 26984, 1, 16384⟩
    (by decide) selected_cut_03152

theorem selected_cut_03153 : selected 8 ⟨98166, by decide⟩
    (prefixPartial 13 26985) = some ⟨13, 2, 0, 98166, 26985, 2245, 16384⟩ := by
  decide +kernel

theorem context_13_26985_98166 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26985 ⟨98166, by decide⟩ :=
  accepted_of_selected 13 26985 ⟨98166, by decide⟩ ⟨13, 2, 0, 98166, 26985, 2245, 16384⟩
    (by decide) selected_cut_03153

theorem selected_cut_03154 : selected 8 ⟨98262, by decide⟩
    (prefixPartial 13 26986) = some ⟨13, 2, 0, 98262, 26986, 3457, 16384⟩ := by
  decide +kernel

theorem context_13_26986_98262 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26986 ⟨98262, by decide⟩ :=
  accepted_of_selected 13 26986 ⟨98262, by decide⟩ ⟨13, 2, 0, 98262, 26986, 3457, 16384⟩
    (by decide) selected_cut_03154

theorem selected_cut_03155 : selected 8 ⟨98325, by decide⟩
    (prefixPartial 13 26987) = some ⟨13, 2, 0, 98325, 26987, 1569, 16384⟩ := by
  decide +kernel

theorem context_13_26987_98325 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26987 ⟨98325, by decide⟩ :=
  accepted_of_selected 13 26987 ⟨98325, by decide⟩ ⟨13, 2, 0, 98325, 26987, 1569, 16384⟩
    (by decide) selected_cut_03155

theorem unmarked_context_12_6746_98326 : frontier 9 ⟨98326, by decide⟩
    (prefixCache 12 6746) (prefixPartial 12 6746) = false := by
  decide +kernel

theorem node_context_12_6746_98326 : EJMOriginalGlobalDAGData.nodes 9 ⟨98326, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨98166, by decide⟩,⟨98262, by decide⟩,⟨98325, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_6746_98326 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6746 ⟨98326, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 6746
    ⟨98326, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨98166, by decide⟩,⟨98262, by decide⟩,⟨98325, by decide⟩]) unmarked_context_12_6746_98326 node_context_12_6746_98326
  intro a
  fin_cases a
  · exact context_13_26984_3444
  · exact context_13_26985_98166
  · exact context_13_26986_98262
  · exact context_13_26987_98325

theorem selected_cut_03156 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 26988) = some ⟨13, 1, 0, 3444, 26988, 1, 16384⟩ := by
  decide +kernel

theorem context_13_26988_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26988 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 26988 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 26988, 1, 16384⟩
    (by decide) selected_cut_03156

theorem selected_cut_03157 : selected 8 ⟨98363, by decide⟩
    (prefixPartial 13 26989) = some ⟨13, 2, 0, 98363, 26989, 1317, 16384⟩ := by
  decide +kernel

theorem context_13_26989_98363 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26989 ⟨98363, by decide⟩ :=
  accepted_of_selected 13 26989 ⟨98363, by decide⟩ ⟨13, 2, 0, 98363, 26989, 1317, 16384⟩
    (by decide) selected_cut_03157

theorem selected_cut_03158 : selected 8 ⟨98409, by decide⟩
    (prefixPartial 13 26990) = some ⟨13, 2, 0, 98409, 26990, 2285, 16384⟩ := by
  decide +kernel

theorem context_13_26990_98409 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26990 ⟨98409, by decide⟩ :=
  accepted_of_selected 13 26990 ⟨98409, by decide⟩ ⟨13, 2, 0, 98409, 26990, 2285, 16384⟩
    (by decide) selected_cut_03158

theorem selected_cut_03159 : selected 8 ⟨98426, by decide⟩
    (prefixPartial 13 26991) = some ⟨13, 2, 0, 98426, 26991, 1229, 16384⟩ := by
  decide +kernel

theorem context_13_26991_98426 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26991 ⟨98426, by decide⟩ :=
  accepted_of_selected 13 26991 ⟨98426, by decide⟩ ⟨13, 2, 0, 98426, 26991, 1229, 16384⟩
    (by decide) selected_cut_03159

theorem unmarked_context_12_6747_98427 : frontier 9 ⟨98427, by decide⟩
    (prefixCache 12 6747) (prefixPartial 12 6747) = false := by
  decide +kernel

theorem node_context_12_6747_98427 : EJMOriginalGlobalDAGData.nodes 9 ⟨98427, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨98363, by decide⟩,⟨98409, by decide⟩,⟨98426, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_6747_98427 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6747 ⟨98427, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 6747
    ⟨98427, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨98363, by decide⟩,⟨98409, by decide⟩,⟨98426, by decide⟩]) unmarked_context_12_6747_98427 node_context_12_6747_98427
  intro a
  fin_cases a
  · exact context_13_26988_3444
  · exact context_13_26989_98363
  · exact context_13_26990_98409
  · exact context_13_26991_98426

theorem unmarked_context_11_1686_98428 : frontier 10 ⟨98428, by decide⟩
    (prefixCache 11 1686) (prefixPartial 11 1686) = false := by
  decide +kernel

theorem node_context_11_1686_98428 : EJMOriginalGlobalDAGData.nodes 10 ⟨98428, by decide⟩ =
    .split (coordinate 11) (![⟨1738, by decide⟩,⟨98100, by decide⟩,⟨98326, by decide⟩,⟨98427, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1686_98428 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1686 ⟨98428, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1686
    ⟨98428, by decide⟩ (by decide) (![⟨1738, by decide⟩,⟨98100, by decide⟩,⟨98326, by decide⟩,⟨98427, by decide⟩]) unmarked_context_11_1686_98428 node_context_11_1686_98428
  intro a
  fin_cases a
  · exact context_12_6744_1738
  · exact context_12_6745_98100
  · exact context_12_6746_98326
  · exact context_12_6747_98427

theorem selected_cut_03160 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 6748) = some ⟨12, 1, 0, 1738, 6748, 1, 65536⟩ := by
  decide +kernel

theorem context_12_6748_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6748 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 6748 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 6748, 1, 65536⟩
    (by decide) selected_cut_03160

theorem selected_cut_03161 : selected 9 ⟨98537, by decide⟩
    (prefixPartial 12 6749) = some ⟨12, 2, 0, 98537, 6749, 3925, 65536⟩ := by
  decide +kernel

theorem context_12_6749_98537 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6749 ⟨98537, by decide⟩ :=
  accepted_of_selected 12 6749 ⟨98537, by decide⟩ ⟨12, 2, 0, 98537, 6749, 3925, 65536⟩
    (by decide) selected_cut_03161

theorem selected_cut_03162 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 27000) = some ⟨13, 1, 0, 3444, 27000, 1, 16384⟩ := by
  decide +kernel

theorem context_13_27000_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27000 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 27000 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 27000, 1, 16384⟩
    (by decide) selected_cut_03162

theorem selected_cut_03163 : selected 8 ⟨98576, by decide⟩
    (prefixPartial 13 27001) = some ⟨13, 2, 0, 98576, 27001, 1417, 16384⟩ := by
  decide +kernel

theorem context_13_27001_98576 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27001 ⟨98576, by decide⟩ :=
  accepted_of_selected 13 27001 ⟨98576, by decide⟩ ⟨13, 2, 0, 98576, 27001, 1417, 16384⟩
    (by decide) selected_cut_03163

theorem selected_cut_03164 : selected 8 ⟨98632, by decide⟩
    (prefixPartial 13 27002) = some ⟨13, 2, 0, 98632, 27002, 2517, 16384⟩ := by
  decide +kernel

theorem context_13_27002_98632 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27002 ⟨98632, by decide⟩ :=
  accepted_of_selected 13 27002 ⟨98632, by decide⟩ ⟨13, 2, 0, 98632, 27002, 2517, 16384⟩
    (by decide) selected_cut_03164

theorem selected_cut_03165 : selected 8 ⟨98670, by decide⟩
    (prefixPartial 13 27003) = some ⟨13, 2, 0, 98670, 27003, 1245, 16384⟩ := by
  decide +kernel

theorem context_13_27003_98670 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27003 ⟨98670, by decide⟩ :=
  accepted_of_selected 13 27003 ⟨98670, by decide⟩ ⟨13, 2, 0, 98670, 27003, 1245, 16384⟩
    (by decide) selected_cut_03165

theorem unmarked_context_12_6750_98671 : frontier 9 ⟨98671, by decide⟩
    (prefixCache 12 6750) (prefixPartial 12 6750) = false := by
  decide +kernel

theorem node_context_12_6750_98671 : EJMOriginalGlobalDAGData.nodes 9 ⟨98671, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨98576, by decide⟩,⟨98632, by decide⟩,⟨98670, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_6750_98671 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6750 ⟨98671, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 6750
    ⟨98671, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨98576, by decide⟩,⟨98632, by decide⟩,⟨98670, by decide⟩]) unmarked_context_12_6750_98671 node_context_12_6750_98671
  intro a
  fin_cases a
  · exact context_13_27000_3444
  · exact context_13_27001_98576
  · exact context_13_27002_98632
  · exact context_13_27003_98670

theorem selected_cut_03166 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 27004) = some ⟨13, 1, 0, 3444, 27004, 1, 16384⟩ := by
  decide +kernel

theorem context_13_27004_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27004 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 27004 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 27004, 1, 16384⟩
    (by decide) selected_cut_03166

theorem selected_cut_03167 : selected 8 ⟨98710, by decide⟩
    (prefixPartial 13 27005) = some ⟨13, 2, 0, 98710, 27005, 1297, 16384⟩ := by
  decide +kernel

theorem context_13_27005_98710 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27005 ⟨98710, by decide⟩ :=
  accepted_of_selected 13 27005 ⟨98710, by decide⟩ ⟨13, 2, 0, 98710, 27005, 1297, 16384⟩
    (by decide) selected_cut_03167

theorem selected_cut_03168 : selected 8 ⟨98749, by decide⟩
    (prefixPartial 13 27006) = some ⟨13, 2, 0, 98749, 27006, 2681, 16384⟩ := by
  decide +kernel

theorem context_13_27006_98749 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27006 ⟨98749, by decide⟩ :=
  accepted_of_selected 13 27006 ⟨98749, by decide⟩ ⟨13, 2, 0, 98749, 27006, 2681, 16384⟩
    (by decide) selected_cut_03168

theorem selected_cut_03169 : selected 8 ⟨98787, by decide⟩
    (prefixPartial 13 27007) = some ⟨13, 2, 0, 98787, 27007, 1481, 16384⟩ := by
  decide +kernel

theorem context_13_27007_98787 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27007 ⟨98787, by decide⟩ :=
  accepted_of_selected 13 27007 ⟨98787, by decide⟩ ⟨13, 2, 0, 98787, 27007, 1481, 16384⟩
    (by decide) selected_cut_03169

theorem unmarked_context_12_6751_98788 : frontier 9 ⟨98788, by decide⟩
    (prefixCache 12 6751) (prefixPartial 12 6751) = false := by
  decide +kernel

theorem node_context_12_6751_98788 : EJMOriginalGlobalDAGData.nodes 9 ⟨98788, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨98710, by decide⟩,⟨98749, by decide⟩,⟨98787, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_6751_98788 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6751 ⟨98788, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 6751
    ⟨98788, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨98710, by decide⟩,⟨98749, by decide⟩,⟨98787, by decide⟩]) unmarked_context_12_6751_98788 node_context_12_6751_98788
  intro a
  fin_cases a
  · exact context_13_27004_3444
  · exact context_13_27005_98710
  · exact context_13_27006_98749
  · exact context_13_27007_98787

theorem unmarked_context_11_1687_98789 : frontier 10 ⟨98789, by decide⟩
    (prefixCache 11 1687) (prefixPartial 11 1687) = false := by
  decide +kernel

theorem node_context_11_1687_98789 : EJMOriginalGlobalDAGData.nodes 10 ⟨98789, by decide⟩ =
    .split (coordinate 11) (![⟨1738, by decide⟩,⟨98537, by decide⟩,⟨98671, by decide⟩,⟨98788, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1687_98789 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1687 ⟨98789, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1687
    ⟨98789, by decide⟩ (by decide) (![⟨1738, by decide⟩,⟨98537, by decide⟩,⟨98671, by decide⟩,⟨98788, by decide⟩]) unmarked_context_11_1687_98789 node_context_11_1687_98789
  intro a
  fin_cases a
  · exact context_12_6748_1738
  · exact context_12_6749_98537
  · exact context_12_6750_98671
  · exact context_12_6751_98788

theorem unmarked_context_10_421_98790 : frontier 11 ⟨98790, by decide⟩
    (prefixCache 10 421) (prefixPartial 10 421) = false := by
  decide +kernel

theorem node_context_10_421_98790 : EJMOriginalGlobalDAGData.nodes 11 ⟨98790, by decide⟩ =
    .split (coordinate 10) (![⟨97643, by decide⟩,⟨97985, by decide⟩,⟨98428, by decide⟩,⟨98789, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_421_98790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 421 ⟨98790, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 421
    ⟨98790, by decide⟩ (by decide) (![⟨97643, by decide⟩,⟨97985, by decide⟩,⟨98428, by decide⟩,⟨98789, by decide⟩]) unmarked_context_10_421_98790 node_context_10_421_98790
  intro a
  fin_cases a
  · exact context_11_1684_97643
  · exact context_11_1685_97985
  · exact context_11_1686_98428
  · exact context_11_1687_98789

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
