/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover301
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_28995 : selected 8 ⟨732385, by decide⟩
    (prefixPartial 13 372897) = some ⟨13, 2, 0, 732385, 372897, 1741, 16384⟩ := by
  decide +kernel

theorem context_13_372897_732385 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372897 ⟨732385, by decide⟩ :=
  accepted_of_selected 13 372897 ⟨732385, by decide⟩ ⟨13, 2, 0, 732385, 372897, 1741, 16384⟩
    (by decide) selected_cut_28995

theorem selected_cut_28996 : selected 8 ⟨732407, by decide⟩
    (prefixPartial 13 372898) = some ⟨13, 2, 0, 732407, 372898, 1417, 16384⟩ := by
  decide +kernel

theorem context_13_372898_732407 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372898 ⟨732407, by decide⟩ :=
  accepted_of_selected 13 372898 ⟨732407, by decide⟩ ⟨13, 2, 0, 732407, 372898, 1417, 16384⟩
    (by decide) selected_cut_28996

theorem selected_cut_28997 : selected 8 ⟨732417, by decide⟩
    (prefixPartial 13 372899) = some ⟨13, 2, 0, 732417, 372899, 789, 16384⟩ := by
  decide +kernel

theorem context_13_372899_732417 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372899 ⟨732417, by decide⟩ :=
  accepted_of_selected 13 372899 ⟨732417, by decide⟩ ⟨13, 2, 0, 732417, 372899, 789, 16384⟩
    (by decide) selected_cut_28997

theorem unmarked_context_12_93224_732418 : frontier 9 ⟨732418, by decide⟩
    (prefixCache 12 93224) (prefixPartial 12 93224) = false := by
  decide +kernel

theorem node_context_12_93224_732418 : EJMOriginalGlobalDAGData.nodes 9 ⟨732418, by decide⟩ =
    .split (coordinate 12) (![⟨732356, by decide⟩,⟨732385, by decide⟩,⟨732407, by decide⟩,⟨732417, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93224_732418 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93224 ⟨732418, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93224
    ⟨732418, by decide⟩ (by decide) (![⟨732356, by decide⟩,⟨732385, by decide⟩,⟨732407, by decide⟩,⟨732417, by decide⟩]) unmarked_context_12_93224_732418 node_context_12_93224_732418
  intro a
  fin_cases a
  · exact context_13_372896_732356
  · exact context_13_372897_732385
  · exact context_13_372898_732407
  · exact context_13_372899_732417

theorem selected_cut_28998 : selected 8 ⟨732437, by decide⟩
    (prefixPartial 13 372900) = some ⟨13, 2, 0, 732437, 372900, 1045, 16384⟩ := by
  decide +kernel

theorem context_13_372900_732437 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372900 ⟨732437, by decide⟩ :=
  accepted_of_selected 13 372900 ⟨732437, by decide⟩ ⟨13, 2, 0, 732437, 372900, 1045, 16384⟩
    (by decide) selected_cut_28998

theorem selected_cut_28999 : selected 8 ⟨732473, by decide⟩
    (prefixPartial 13 372901) = some ⟨13, 2, 0, 732473, 372901, 1893, 16384⟩ := by
  decide +kernel

theorem context_13_372901_732473 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372901 ⟨732473, by decide⟩ :=
  accepted_of_selected 13 372901 ⟨732473, by decide⟩ ⟨13, 2, 0, 732473, 372901, 1893, 16384⟩
    (by decide) selected_cut_28999

theorem selected_cut_29000 : selected 8 ⟨732501, by decide⟩
    (prefixPartial 13 372902) = some ⟨13, 2, 0, 732501, 372902, 1941, 16384⟩ := by
  decide +kernel

theorem context_13_372902_732501 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372902 ⟨732501, by decide⟩ :=
  accepted_of_selected 13 372902 ⟨732501, by decide⟩ ⟨13, 2, 0, 732501, 372902, 1941, 16384⟩
    (by decide) selected_cut_29000

theorem selected_cut_29001 : selected 8 ⟨732510, by decide⟩
    (prefixPartial 13 372903) = some ⟨13, 2, 0, 732510, 372903, 897, 16384⟩ := by
  decide +kernel

theorem context_13_372903_732510 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372903 ⟨732510, by decide⟩ :=
  accepted_of_selected 13 372903 ⟨732510, by decide⟩ ⟨13, 2, 0, 732510, 372903, 897, 16384⟩
    (by decide) selected_cut_29001

theorem unmarked_context_12_93225_732511 : frontier 9 ⟨732511, by decide⟩
    (prefixCache 12 93225) (prefixPartial 12 93225) = false := by
  decide +kernel

theorem node_context_12_93225_732511 : EJMOriginalGlobalDAGData.nodes 9 ⟨732511, by decide⟩ =
    .split (coordinate 12) (![⟨732437, by decide⟩,⟨732473, by decide⟩,⟨732501, by decide⟩,⟨732510, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93225_732511 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93225 ⟨732511, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93225
    ⟨732511, by decide⟩ (by decide) (![⟨732437, by decide⟩,⟨732473, by decide⟩,⟨732501, by decide⟩,⟨732510, by decide⟩]) unmarked_context_12_93225_732511 node_context_12_93225_732511
  intro a
  fin_cases a
  · exact context_13_372900_732437
  · exact context_13_372901_732473
  · exact context_13_372902_732501
  · exact context_13_372903_732510

theorem selected_cut_29002 : selected 8 ⟨732525, by decide⟩
    (prefixPartial 13 372904) = some ⟨13, 2, 0, 732525, 372904, 733, 16384⟩ := by
  decide +kernel

theorem context_13_372904_732525 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372904 ⟨732525, by decide⟩ :=
  accepted_of_selected 13 372904 ⟨732525, by decide⟩ ⟨13, 2, 0, 732525, 372904, 733, 16384⟩
    (by decide) selected_cut_29002

theorem selected_cut_29003 : selected 8 ⟨732560, by decide⟩
    (prefixPartial 13 372905) = some ⟨13, 2, 0, 732560, 372905, 1857, 16384⟩ := by
  decide +kernel

theorem context_13_372905_732560 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372905 ⟨732560, by decide⟩ :=
  accepted_of_selected 13 372905 ⟨732560, by decide⟩ ⟨13, 2, 0, 732560, 372905, 1857, 16384⟩
    (by decide) selected_cut_29003

theorem selected_cut_29004 : selected 8 ⟨732590, by decide⟩
    (prefixPartial 13 372906) = some ⟨13, 2, 0, 732590, 372906, 1453, 16384⟩ := by
  decide +kernel

theorem context_13_372906_732590 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372906 ⟨732590, by decide⟩ :=
  accepted_of_selected 13 372906 ⟨732590, by decide⟩ ⟨13, 2, 0, 732590, 372906, 1453, 16384⟩
    (by decide) selected_cut_29004

theorem selected_cut_29005 : selected 8 ⟨732597, by decide⟩
    (prefixPartial 13 372907) = some ⟨13, 2, 0, 732597, 372907, 881, 16384⟩ := by
  decide +kernel

theorem context_13_372907_732597 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372907 ⟨732597, by decide⟩ :=
  accepted_of_selected 13 372907 ⟨732597, by decide⟩ ⟨13, 2, 0, 732597, 372907, 881, 16384⟩
    (by decide) selected_cut_29005

theorem unmarked_context_12_93226_732598 : frontier 9 ⟨732598, by decide⟩
    (prefixCache 12 93226) (prefixPartial 12 93226) = false := by
  decide +kernel

theorem node_context_12_93226_732598 : EJMOriginalGlobalDAGData.nodes 9 ⟨732598, by decide⟩ =
    .split (coordinate 12) (![⟨732525, by decide⟩,⟨732560, by decide⟩,⟨732590, by decide⟩,⟨732597, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93226_732598 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93226 ⟨732598, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93226
    ⟨732598, by decide⟩ (by decide) (![⟨732525, by decide⟩,⟨732560, by decide⟩,⟨732590, by decide⟩,⟨732597, by decide⟩]) unmarked_context_12_93226_732598 node_context_12_93226_732598
  intro a
  fin_cases a
  · exact context_13_372904_732525
  · exact context_13_372905_732560
  · exact context_13_372906_732590
  · exact context_13_372907_732597

theorem selected_cut_29006 : selected 8 ⟨732614, by decide⟩
    (prefixPartial 13 372908) = some ⟨13, 2, 0, 732614, 372908, 857, 16384⟩ := by
  decide +kernel

theorem context_13_372908_732614 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372908 ⟨732614, by decide⟩ :=
  accepted_of_selected 13 372908 ⟨732614, by decide⟩ ⟨13, 2, 0, 732614, 372908, 857, 16384⟩
    (by decide) selected_cut_29006

theorem selected_cut_29007 : selected 8 ⟨732640, by decide⟩
    (prefixPartial 13 372909) = some ⟨13, 2, 0, 732640, 372909, 1953, 16384⟩ := by
  decide +kernel

theorem context_13_372909_732640 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372909 ⟨732640, by decide⟩ :=
  accepted_of_selected 13 372909 ⟨732640, by decide⟩ ⟨13, 2, 0, 732640, 372909, 1953, 16384⟩
    (by decide) selected_cut_29007

theorem selected_cut_29008 : selected 8 ⟨732667, by decide⟩
    (prefixPartial 13 372910) = some ⟨13, 2, 0, 732667, 372910, 1785, 16384⟩ := by
  decide +kernel

theorem context_13_372910_732667 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372910 ⟨732667, by decide⟩ :=
  accepted_of_selected 13 372910 ⟨732667, by decide⟩ ⟨13, 2, 0, 732667, 372910, 1785, 16384⟩
    (by decide) selected_cut_29008

theorem selected_cut_29009 : selected 8 ⟨732678, by decide⟩
    (prefixPartial 13 372911) = some ⟨13, 2, 0, 732678, 372911, 905, 16384⟩ := by
  decide +kernel

theorem context_13_372911_732678 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372911 ⟨732678, by decide⟩ :=
  accepted_of_selected 13 372911 ⟨732678, by decide⟩ ⟨13, 2, 0, 732678, 372911, 905, 16384⟩
    (by decide) selected_cut_29009

theorem unmarked_context_12_93227_732679 : frontier 9 ⟨732679, by decide⟩
    (prefixCache 12 93227) (prefixPartial 12 93227) = false := by
  decide +kernel

theorem node_context_12_93227_732679 : EJMOriginalGlobalDAGData.nodes 9 ⟨732679, by decide⟩ =
    .split (coordinate 12) (![⟨732614, by decide⟩,⟨732640, by decide⟩,⟨732667, by decide⟩,⟨732678, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93227_732679 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93227 ⟨732679, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93227
    ⟨732679, by decide⟩ (by decide) (![⟨732614, by decide⟩,⟨732640, by decide⟩,⟨732667, by decide⟩,⟨732678, by decide⟩]) unmarked_context_12_93227_732679 node_context_12_93227_732679
  intro a
  fin_cases a
  · exact context_13_372908_732614
  · exact context_13_372909_732640
  · exact context_13_372910_732667
  · exact context_13_372911_732678

theorem unmarked_context_11_23306_732680 : frontier 10 ⟨732680, by decide⟩
    (prefixCache 11 23306) (prefixPartial 11 23306) = false := by
  decide +kernel

theorem node_context_11_23306_732680 : EJMOriginalGlobalDAGData.nodes 10 ⟨732680, by decide⟩ =
    .split (coordinate 11) (![⟨732418, by decide⟩,⟨732511, by decide⟩,⟨732598, by decide⟩,⟨732679, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23306_732680 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23306 ⟨732680, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23306
    ⟨732680, by decide⟩ (by decide) (![⟨732418, by decide⟩,⟨732511, by decide⟩,⟨732598, by decide⟩,⟨732679, by decide⟩]) unmarked_context_11_23306_732680 node_context_11_23306_732680
  intro a
  fin_cases a
  · exact context_12_93224_732418
  · exact context_12_93225_732511
  · exact context_12_93226_732598
  · exact context_12_93227_732679

theorem selected_cut_29010 : selected 9 ⟨732739, by decide⟩
    (prefixPartial 12 93228) = some ⟨12, 2, 0, 732739, 93228, 4065, 65536⟩ := by
  decide +kernel

theorem context_12_93228_732739 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93228 ⟨732739, by decide⟩ :=
  accepted_of_selected 12 93228 ⟨732739, by decide⟩ ⟨12, 2, 0, 732739, 93228, 4065, 65536⟩
    (by decide) selected_cut_29010

theorem selected_cut_29011 : selected 8 ⟨732753, by decide⟩
    (prefixPartial 13 372916) = some ⟨13, 2, 0, 732753, 372916, 749, 16384⟩ := by
  decide +kernel

theorem context_13_372916_732753 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372916 ⟨732753, by decide⟩ :=
  accepted_of_selected 13 372916 ⟨732753, by decide⟩ ⟨13, 2, 0, 732753, 372916, 749, 16384⟩
    (by decide) selected_cut_29011

theorem selected_cut_29012 : selected 8 ⟨732786, by decide⟩
    (prefixPartial 13 372917) = some ⟨13, 2, 0, 732786, 372917, 1905, 16384⟩ := by
  decide +kernel

theorem context_13_372917_732786 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372917 ⟨732786, by decide⟩ :=
  accepted_of_selected 13 372917 ⟨732786, by decide⟩ ⟨13, 2, 0, 732786, 372917, 1905, 16384⟩
    (by decide) selected_cut_29012

theorem selected_cut_29013 : selected 8 ⟨732808, by decide⟩
    (prefixPartial 13 372918) = some ⟨13, 2, 0, 732808, 372918, 1621, 16384⟩ := by
  decide +kernel

theorem context_13_372918_732808 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372918 ⟨732808, by decide⟩ :=
  accepted_of_selected 13 372918 ⟨732808, by decide⟩ ⟨13, 2, 0, 732808, 372918, 1621, 16384⟩
    (by decide) selected_cut_29013

theorem selected_cut_29014 : selected 8 ⟨732821, by decide⟩
    (prefixPartial 13 372919) = some ⟨13, 2, 0, 732821, 372919, 733, 16384⟩ := by
  decide +kernel

theorem context_13_372919_732821 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372919 ⟨732821, by decide⟩ :=
  accepted_of_selected 13 372919 ⟨732821, by decide⟩ ⟨13, 2, 0, 732821, 372919, 733, 16384⟩
    (by decide) selected_cut_29014

theorem unmarked_context_12_93229_732822 : frontier 9 ⟨732822, by decide⟩
    (prefixCache 12 93229) (prefixPartial 12 93229) = false := by
  decide +kernel

theorem node_context_12_93229_732822 : EJMOriginalGlobalDAGData.nodes 9 ⟨732822, by decide⟩ =
    .split (coordinate 12) (![⟨732753, by decide⟩,⟨732786, by decide⟩,⟨732808, by decide⟩,⟨732821, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93229_732822 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93229 ⟨732822, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93229
    ⟨732822, by decide⟩ (by decide) (![⟨732753, by decide⟩,⟨732786, by decide⟩,⟨732808, by decide⟩,⟨732821, by decide⟩]) unmarked_context_12_93229_732822 node_context_12_93229_732822
  intro a
  fin_cases a
  · exact context_13_372916_732753
  · exact context_13_372917_732786
  · exact context_13_372918_732808
  · exact context_13_372919_732821

theorem selected_cut_29015 : selected 8 ⟨732833, by decide⟩
    (prefixPartial 13 372920) = some ⟨13, 2, 0, 732833, 372920, 593, 16384⟩ := by
  decide +kernel

theorem context_13_372920_732833 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372920 ⟨732833, by decide⟩ :=
  accepted_of_selected 13 372920 ⟨732833, by decide⟩ ⟨13, 2, 0, 732833, 372920, 593, 16384⟩
    (by decide) selected_cut_29015

theorem selected_cut_29016 : selected 8 ⟨732866, by decide⟩
    (prefixPartial 13 372921) = some ⟨13, 2, 0, 732866, 372921, 2109, 16384⟩ := by
  decide +kernel

theorem context_13_372921_732866 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372921 ⟨732866, by decide⟩ :=
  accepted_of_selected 13 372921 ⟨732866, by decide⟩ ⟨13, 2, 0, 732866, 372921, 2109, 16384⟩
    (by decide) selected_cut_29016

theorem selected_cut_29017 : selected 8 ⟨732886, by decide⟩
    (prefixPartial 13 372922) = some ⟨13, 2, 0, 732886, 372922, 1393, 16384⟩ := by
  decide +kernel

theorem context_13_372922_732886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372922 ⟨732886, by decide⟩ :=
  accepted_of_selected 13 372922 ⟨732886, by decide⟩ ⟨13, 2, 0, 732886, 372922, 1393, 16384⟩
    (by decide) selected_cut_29017

theorem selected_cut_29018 : selected 8 ⟨732894, by decide⟩
    (prefixPartial 13 372923) = some ⟨13, 2, 0, 732894, 372923, 881, 16384⟩ := by
  decide +kernel

theorem context_13_372923_732894 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372923 ⟨732894, by decide⟩ :=
  accepted_of_selected 13 372923 ⟨732894, by decide⟩ ⟨13, 2, 0, 732894, 372923, 881, 16384⟩
    (by decide) selected_cut_29018

theorem unmarked_context_12_93230_732895 : frontier 9 ⟨732895, by decide⟩
    (prefixCache 12 93230) (prefixPartial 12 93230) = false := by
  decide +kernel

theorem node_context_12_93230_732895 : EJMOriginalGlobalDAGData.nodes 9 ⟨732895, by decide⟩ =
    .split (coordinate 12) (![⟨732833, by decide⟩,⟨732866, by decide⟩,⟨732886, by decide⟩,⟨732894, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93230_732895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93230 ⟨732895, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93230
    ⟨732895, by decide⟩ (by decide) (![⟨732833, by decide⟩,⟨732866, by decide⟩,⟨732886, by decide⟩,⟨732894, by decide⟩]) unmarked_context_12_93230_732895 node_context_12_93230_732895
  intro a
  fin_cases a
  · exact context_13_372920_732833
  · exact context_13_372921_732866
  · exact context_13_372922_732886
  · exact context_13_372923_732894

theorem selected_cut_29019 : selected 8 ⟨732905, by decide⟩
    (prefixPartial 13 372924) = some ⟨13, 2, 0, 732905, 372924, 473, 16384⟩ := by
  decide +kernel

theorem context_13_372924_732905 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372924 ⟨732905, by decide⟩ :=
  accepted_of_selected 13 372924 ⟨732905, by decide⟩ ⟨13, 2, 0, 732905, 372924, 473, 16384⟩
    (by decide) selected_cut_29019

theorem selected_cut_29020 : selected 8 ⟨732932, by decide⟩
    (prefixPartial 13 372925) = some ⟨13, 2, 0, 732932, 372925, 1805, 16384⟩ := by
  decide +kernel

theorem context_13_372925_732932 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372925 ⟨732932, by decide⟩ :=
  accepted_of_selected 13 372925 ⟨732932, by decide⟩ ⟨13, 2, 0, 732932, 372925, 1805, 16384⟩
    (by decide) selected_cut_29020

theorem selected_cut_29021 : selected 8 ⟨732955, by decide⟩
    (prefixPartial 13 372926) = some ⟨13, 2, 0, 732955, 372926, 1437, 16384⟩ := by
  decide +kernel

theorem context_13_372926_732955 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372926 ⟨732955, by decide⟩ :=
  accepted_of_selected 13 372926 ⟨732955, by decide⟩ ⟨13, 2, 0, 732955, 372926, 1437, 16384⟩
    (by decide) selected_cut_29021

theorem selected_cut_29022 : selected 8 ⟨732964, by decide⟩
    (prefixPartial 13 372927) = some ⟨13, 2, 0, 732964, 372927, 813, 16384⟩ := by
  decide +kernel

theorem context_13_372927_732964 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372927 ⟨732964, by decide⟩ :=
  accepted_of_selected 13 372927 ⟨732964, by decide⟩ ⟨13, 2, 0, 732964, 372927, 813, 16384⟩
    (by decide) selected_cut_29022

theorem unmarked_context_12_93231_732965 : frontier 9 ⟨732965, by decide⟩
    (prefixCache 12 93231) (prefixPartial 12 93231) = false := by
  decide +kernel

theorem node_context_12_93231_732965 : EJMOriginalGlobalDAGData.nodes 9 ⟨732965, by decide⟩ =
    .split (coordinate 12) (![⟨732905, by decide⟩,⟨732932, by decide⟩,⟨732955, by decide⟩,⟨732964, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93231_732965 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93231 ⟨732965, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93231
    ⟨732965, by decide⟩ (by decide) (![⟨732905, by decide⟩,⟨732932, by decide⟩,⟨732955, by decide⟩,⟨732964, by decide⟩]) unmarked_context_12_93231_732965 node_context_12_93231_732965
  intro a
  fin_cases a
  · exact context_13_372924_732905
  · exact context_13_372925_732932
  · exact context_13_372926_732955
  · exact context_13_372927_732964

theorem unmarked_context_11_23307_732966 : frontier 10 ⟨732966, by decide⟩
    (prefixCache 11 23307) (prefixPartial 11 23307) = false := by
  decide +kernel

theorem node_context_11_23307_732966 : EJMOriginalGlobalDAGData.nodes 10 ⟨732966, by decide⟩ =
    .split (coordinate 11) (![⟨732739, by decide⟩,⟨732822, by decide⟩,⟨732895, by decide⟩,⟨732965, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23307_732966 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23307 ⟨732966, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23307
    ⟨732966, by decide⟩ (by decide) (![⟨732739, by decide⟩,⟨732822, by decide⟩,⟨732895, by decide⟩,⟨732965, by decide⟩]) unmarked_context_11_23307_732966 node_context_11_23307_732966
  intro a
  fin_cases a
  · exact context_12_93228_732739
  · exact context_12_93229_732822
  · exact context_12_93230_732895
  · exact context_12_93231_732965

theorem unmarked_context_10_5826_732967 : frontier 11 ⟨732967, by decide⟩
    (prefixCache 10 5826) (prefixPartial 10 5826) = false := by
  decide +kernel

theorem node_context_10_5826_732967 : EJMOriginalGlobalDAGData.nodes 11 ⟨732967, by decide⟩ =
    .split (coordinate 10) (![⟨732023, by decide⟩,⟨732346, by decide⟩,⟨732680, by decide⟩,⟨732966, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5826_732967 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5826 ⟨732967, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5826
    ⟨732967, by decide⟩ (by decide) (![⟨732023, by decide⟩,⟨732346, by decide⟩,⟨732680, by decide⟩,⟨732966, by decide⟩]) unmarked_context_10_5826_732967 node_context_10_5826_732967
  intro a
  fin_cases a
  · exact context_11_23304_732023
  · exact context_11_23305_732346
  · exact context_11_23306_732680
  · exact context_11_23307_732966

theorem selected_cut_29023 : selected 9 ⟨399079, by decide⟩
    (prefixPartial 12 93232) = some ⟨12, 1, 0, 399079, 93232, 1, 65536⟩ := by
  decide +kernel

theorem context_12_93232_399079 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93232 ⟨399079, by decide⟩ :=
  accepted_of_selected 12 93232 ⟨399079, by decide⟩ ⟨12, 1, 0, 399079, 93232, 1, 65536⟩
    (by decide) selected_cut_29023

theorem selected_cut_29024 : selected 8 ⟨732981, by decide⟩
    (prefixPartial 13 372932) = some ⟨13, 2, 0, 732981, 372932, 617, 16384⟩ := by
  decide +kernel

theorem context_13_372932_732981 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372932 ⟨732981, by decide⟩ :=
  accepted_of_selected 13 372932 ⟨732981, by decide⟩ ⟨13, 2, 0, 732981, 372932, 617, 16384⟩
    (by decide) selected_cut_29024

theorem selected_cut_29025 : selected 8 ⟨733003, by decide⟩
    (prefixPartial 13 372933) = some ⟨13, 2, 0, 733003, 372933, 1601, 16384⟩ := by
  decide +kernel

theorem context_13_372933_733003 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372933 ⟨733003, by decide⟩ :=
  accepted_of_selected 13 372933 ⟨733003, by decide⟩ ⟨13, 2, 0, 733003, 372933, 1601, 16384⟩
    (by decide) selected_cut_29025

theorem selected_cut_29026 : selected 8 ⟨733023, by decide⟩
    (prefixPartial 13 372934) = some ⟨13, 2, 0, 733023, 372934, 1737, 16384⟩ := by
  decide +kernel

theorem context_13_372934_733023 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372934 ⟨733023, by decide⟩ :=
  accepted_of_selected 13 372934 ⟨733023, by decide⟩ ⟨13, 2, 0, 733023, 372934, 1737, 16384⟩
    (by decide) selected_cut_29026

theorem selected_cut_29027 : selected 8 ⟨733030, by decide⟩
    (prefixPartial 13 372935) = some ⟨13, 2, 0, 733030, 372935, 809, 16384⟩ := by
  decide +kernel

theorem context_13_372935_733030 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372935 ⟨733030, by decide⟩ :=
  accepted_of_selected 13 372935 ⟨733030, by decide⟩ ⟨13, 2, 0, 733030, 372935, 809, 16384⟩
    (by decide) selected_cut_29027

theorem unmarked_context_12_93233_733031 : frontier 9 ⟨733031, by decide⟩
    (prefixCache 12 93233) (prefixPartial 12 93233) = false := by
  decide +kernel

theorem node_context_12_93233_733031 : EJMOriginalGlobalDAGData.nodes 9 ⟨733031, by decide⟩ =
    .split (coordinate 12) (![⟨732981, by decide⟩,⟨733003, by decide⟩,⟨733023, by decide⟩,⟨733030, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93233_733031 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93233 ⟨733031, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93233
    ⟨733031, by decide⟩ (by decide) (![⟨732981, by decide⟩,⟨733003, by decide⟩,⟨733023, by decide⟩,⟨733030, by decide⟩]) unmarked_context_12_93233_733031 node_context_12_93233_733031
  intro a
  fin_cases a
  · exact context_13_372932_732981
  · exact context_13_372933_733003
  · exact context_13_372934_733023
  · exact context_13_372935_733030

theorem selected_cut_29028 : selected 8 ⟨733043, by decide⟩
    (prefixPartial 13 372936) = some ⟨13, 2, 0, 733043, 372936, 601, 16384⟩ := by
  decide +kernel

theorem context_13_372936_733043 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372936 ⟨733043, by decide⟩ :=
  accepted_of_selected 13 372936 ⟨733043, by decide⟩ ⟨13, 2, 0, 733043, 372936, 601, 16384⟩
    (by decide) selected_cut_29028

theorem selected_cut_29029 : selected 8 ⟨733066, by decide⟩
    (prefixPartial 13 372937) = some ⟨13, 2, 0, 733066, 372937, 1805, 16384⟩ := by
  decide +kernel

theorem context_13_372937_733066 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372937 ⟨733066, by decide⟩ :=
  accepted_of_selected 13 372937 ⟨733066, by decide⟩ ⟨13, 2, 0, 733066, 372937, 1805, 16384⟩
    (by decide) selected_cut_29029

theorem selected_cut_29030 : selected 8 ⟨733083, by decide⟩
    (prefixPartial 13 372938) = some ⟨13, 2, 0, 733083, 372938, 1377, 16384⟩ := by
  decide +kernel

theorem context_13_372938_733083 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372938 ⟨733083, by decide⟩ :=
  accepted_of_selected 13 372938 ⟨733083, by decide⟩ ⟨13, 2, 0, 733083, 372938, 1377, 16384⟩
    (by decide) selected_cut_29030

theorem selected_cut_29031 : selected 8 ⟨733089, by decide⟩
    (prefixPartial 13 372939) = some ⟨13, 2, 0, 733089, 372939, 789, 16384⟩ := by
  decide +kernel

theorem context_13_372939_733089 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372939 ⟨733089, by decide⟩ :=
  accepted_of_selected 13 372939 ⟨733089, by decide⟩ ⟨13, 2, 0, 733089, 372939, 789, 16384⟩
    (by decide) selected_cut_29031

theorem unmarked_context_12_93234_733090 : frontier 9 ⟨733090, by decide⟩
    (prefixCache 12 93234) (prefixPartial 12 93234) = false := by
  decide +kernel

theorem node_context_12_93234_733090 : EJMOriginalGlobalDAGData.nodes 9 ⟨733090, by decide⟩ =
    .split (coordinate 12) (![⟨733043, by decide⟩,⟨733066, by decide⟩,⟨733083, by decide⟩,⟨733089, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93234_733090 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93234 ⟨733090, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93234
    ⟨733090, by decide⟩ (by decide) (![⟨733043, by decide⟩,⟨733066, by decide⟩,⟨733083, by decide⟩,⟨733089, by decide⟩]) unmarked_context_12_93234_733090 node_context_12_93234_733090
  intro a
  fin_cases a
  · exact context_13_372936_733043
  · exact context_13_372937_733066
  · exact context_13_372938_733083
  · exact context_13_372939_733089

theorem selected_cut_29032 : selected 8 ⟨733102, by decide⟩
    (prefixPartial 13 372940) = some ⟨13, 2, 0, 733102, 372940, 525, 16384⟩ := by
  decide +kernel

theorem context_13_372940_733102 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372940 ⟨733102, by decide⟩ :=
  accepted_of_selected 13 372940 ⟨733102, by decide⟩ ⟨13, 2, 0, 733102, 372940, 525, 16384⟩
    (by decide) selected_cut_29032

theorem selected_cut_29033 : selected 8 ⟨733130, by decide⟩
    (prefixPartial 13 372941) = some ⟨13, 2, 0, 733130, 372941, 2001, 16384⟩ := by
  decide +kernel

theorem context_13_372941_733130 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372941 ⟨733130, by decide⟩ :=
  accepted_of_selected 13 372941 ⟨733130, by decide⟩ ⟨13, 2, 0, 733130, 372941, 2001, 16384⟩
    (by decide) selected_cut_29033

theorem selected_cut_29034 : selected 8 ⟨733155, by decide⟩
    (prefixPartial 13 372942) = some ⟨13, 2, 0, 733155, 372942, 1741, 16384⟩ := by
  decide +kernel

theorem context_13_372942_733155 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372942 ⟨733155, by decide⟩ :=
  accepted_of_selected 13 372942 ⟨733155, by decide⟩ ⟨13, 2, 0, 733155, 372942, 1741, 16384⟩
    (by decide) selected_cut_29034

theorem selected_cut_29035 : selected 8 ⟨733162, by decide⟩
    (prefixPartial 13 372943) = some ⟨13, 2, 0, 733162, 372943, 841, 16384⟩ := by
  decide +kernel

theorem context_13_372943_733162 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372943 ⟨733162, by decide⟩ :=
  accepted_of_selected 13 372943 ⟨733162, by decide⟩ ⟨13, 2, 0, 733162, 372943, 841, 16384⟩
    (by decide) selected_cut_29035

theorem unmarked_context_12_93235_733163 : frontier 9 ⟨733163, by decide⟩
    (prefixCache 12 93235) (prefixPartial 12 93235) = false := by
  decide +kernel

theorem node_context_12_93235_733163 : EJMOriginalGlobalDAGData.nodes 9 ⟨733163, by decide⟩ =
    .split (coordinate 12) (![⟨733102, by decide⟩,⟨733130, by decide⟩,⟨733155, by decide⟩,⟨733162, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93235_733163 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93235 ⟨733163, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93235
    ⟨733163, by decide⟩ (by decide) (![⟨733102, by decide⟩,⟨733130, by decide⟩,⟨733155, by decide⟩,⟨733162, by decide⟩]) unmarked_context_12_93235_733163 node_context_12_93235_733163
  intro a
  fin_cases a
  · exact context_13_372940_733102
  · exact context_13_372941_733130
  · exact context_13_372942_733155
  · exact context_13_372943_733162

theorem unmarked_context_11_23308_733164 : frontier 10 ⟨733164, by decide⟩
    (prefixCache 11 23308) (prefixPartial 11 23308) = false := by
  decide +kernel

theorem node_context_11_23308_733164 : EJMOriginalGlobalDAGData.nodes 10 ⟨733164, by decide⟩ =
    .split (coordinate 11) (![⟨399079, by decide⟩,⟨733031, by decide⟩,⟨733090, by decide⟩,⟨733163, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23308_733164 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23308 ⟨733164, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23308
    ⟨733164, by decide⟩ (by decide) (![⟨399079, by decide⟩,⟨733031, by decide⟩,⟨733090, by decide⟩,⟨733163, by decide⟩]) unmarked_context_11_23308_733164 node_context_11_23308_733164
  intro a
  fin_cases a
  · exact context_12_93232_399079
  · exact context_12_93233_733031
  · exact context_12_93234_733090
  · exact context_12_93235_733163

theorem selected_cut_29036 : selected 8 ⟨733168, by decide⟩
    (prefixPartial 13 372944) = some ⟨13, 2, 0, 733168, 372944, 373, 16384⟩ := by
  decide +kernel

theorem context_13_372944_733168 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372944 ⟨733168, by decide⟩ :=
  accepted_of_selected 13 372944 ⟨733168, by decide⟩ ⟨13, 2, 0, 733168, 372944, 373, 16384⟩
    (by decide) selected_cut_29036

theorem selected_cut_29037 : selected 8 ⟨733195, by decide⟩
    (prefixPartial 13 372945) = some ⟨13, 2, 0, 733195, 372945, 1701, 16384⟩ := by
  decide +kernel

theorem context_13_372945_733195 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372945 ⟨733195, by decide⟩ :=
  accepted_of_selected 13 372945 ⟨733195, by decide⟩ ⟨13, 2, 0, 733195, 372945, 1701, 16384⟩
    (by decide) selected_cut_29037

theorem selected_cut_29038 : selected 8 ⟨733216, by decide⟩
    (prefixPartial 13 372946) = some ⟨13, 2, 0, 733216, 372946, 1517, 16384⟩ := by
  decide +kernel

theorem context_13_372946_733216 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372946 ⟨733216, by decide⟩ :=
  accepted_of_selected 13 372946 ⟨733216, by decide⟩ ⟨13, 2, 0, 733216, 372946, 1517, 16384⟩
    (by decide) selected_cut_29038

theorem selected_cut_29039 : selected 8 ⟨733225, by decide⟩
    (prefixPartial 13 372947) = some ⟨13, 2, 0, 733225, 372947, 757, 16384⟩ := by
  decide +kernel

theorem context_13_372947_733225 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372947 ⟨733225, by decide⟩ :=
  accepted_of_selected 13 372947 ⟨733225, by decide⟩ ⟨13, 2, 0, 733225, 372947, 757, 16384⟩
    (by decide) selected_cut_29039

theorem unmarked_context_12_93236_733226 : frontier 9 ⟨733226, by decide⟩
    (prefixCache 12 93236) (prefixPartial 12 93236) = false := by
  decide +kernel

theorem node_context_12_93236_733226 : EJMOriginalGlobalDAGData.nodes 9 ⟨733226, by decide⟩ =
    .split (coordinate 12) (![⟨733168, by decide⟩,⟨733195, by decide⟩,⟨733216, by decide⟩,⟨733225, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93236_733226 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93236 ⟨733226, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93236
    ⟨733226, by decide⟩ (by decide) (![⟨733168, by decide⟩,⟨733195, by decide⟩,⟨733216, by decide⟩,⟨733225, by decide⟩]) unmarked_context_12_93236_733226 node_context_12_93236_733226
  intro a
  fin_cases a
  · exact context_13_372944_733168
  · exact context_13_372945_733195
  · exact context_13_372946_733216
  · exact context_13_372947_733225

theorem selected_cut_29040 : selected 8 ⟨733236, by decide⟩
    (prefixPartial 13 372948) = some ⟨13, 2, 0, 733236, 372948, 433, 16384⟩ := by
  decide +kernel

theorem context_13_372948_733236 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372948 ⟨733236, by decide⟩ :=
  accepted_of_selected 13 372948 ⟨733236, by decide⟩ ⟨13, 2, 0, 733236, 372948, 433, 16384⟩
    (by decide) selected_cut_29040

theorem selected_cut_29041 : selected 8 ⟨733260, by decide⟩
    (prefixPartial 13 372949) = some ⟨13, 2, 0, 733260, 372949, 1517, 16384⟩ := by
  decide +kernel

theorem context_13_372949_733260 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372949 ⟨733260, by decide⟩ :=
  accepted_of_selected 13 372949 ⟨733260, by decide⟩ ⟨13, 2, 0, 733260, 372949, 1517, 16384⟩
    (by decide) selected_cut_29041

theorem selected_cut_29042 : selected 8 ⟨733287, by decide⟩
    (prefixPartial 13 372950) = some ⟨13, 2, 0, 733287, 372950, 1797, 16384⟩ := by
  decide +kernel

theorem context_13_372950_733287 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372950 ⟨733287, by decide⟩ :=
  accepted_of_selected 13 372950 ⟨733287, by decide⟩ ⟨13, 2, 0, 733287, 372950, 1797, 16384⟩
    (by decide) selected_cut_29042

theorem selected_cut_29043 : selected 8 ⟨733293, by decide⟩
    (prefixPartial 13 372951) = some ⟨13, 2, 0, 733293, 372951, 773, 16384⟩ := by
  decide +kernel

theorem context_13_372951_733293 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372951 ⟨733293, by decide⟩ :=
  accepted_of_selected 13 372951 ⟨733293, by decide⟩ ⟨13, 2, 0, 733293, 372951, 773, 16384⟩
    (by decide) selected_cut_29043

theorem unmarked_context_12_93237_733294 : frontier 9 ⟨733294, by decide⟩
    (prefixCache 12 93237) (prefixPartial 12 93237) = false := by
  decide +kernel

theorem node_context_12_93237_733294 : EJMOriginalGlobalDAGData.nodes 9 ⟨733294, by decide⟩ =
    .split (coordinate 12) (![⟨733236, by decide⟩,⟨733260, by decide⟩,⟨733287, by decide⟩,⟨733293, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93237_733294 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93237 ⟨733294, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93237
    ⟨733294, by decide⟩ (by decide) (![⟨733236, by decide⟩,⟨733260, by decide⟩,⟨733287, by decide⟩,⟨733293, by decide⟩]) unmarked_context_12_93237_733294 node_context_12_93237_733294
  intro a
  fin_cases a
  · exact context_13_372948_733236
  · exact context_13_372949_733260
  · exact context_13_372950_733287
  · exact context_13_372951_733293

theorem selected_cut_29044 : selected 8 ⟨733300, by decide⟩
    (prefixPartial 13 372952) = some ⟨13, 2, 0, 733300, 372952, 389, 16384⟩ := by
  decide +kernel

theorem context_13_372952_733300 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372952 ⟨733300, by decide⟩ :=
  accepted_of_selected 13 372952 ⟨733300, by decide⟩ ⟨13, 2, 0, 733300, 372952, 389, 16384⟩
    (by decide) selected_cut_29044

theorem selected_cut_29045 : selected 8 ⟨733332, by decide⟩
    (prefixPartial 13 372953) = some ⟨13, 2, 0, 733332, 372953, 1961, 16384⟩ := by
  decide +kernel

theorem context_13_372953_733332 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372953 ⟨733332, by decide⟩ :=
  accepted_of_selected 13 372953 ⟨733332, by decide⟩ ⟨13, 2, 0, 733332, 372953, 1961, 16384⟩
    (by decide) selected_cut_29045

theorem selected_cut_29046 : selected 8 ⟨733354, by decide⟩
    (prefixPartial 13 372954) = some ⟨13, 2, 0, 733354, 372954, 1617, 16384⟩ := by
  decide +kernel

theorem context_13_372954_733354 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372954 ⟨733354, by decide⟩ :=
  accepted_of_selected 13 372954 ⟨733354, by decide⟩ ⟨13, 2, 0, 733354, 372954, 1617, 16384⟩
    (by decide) selected_cut_29046

theorem selected_cut_29047 : selected 8 ⟨733363, by decide⟩
    (prefixPartial 13 372955) = some ⟨13, 2, 0, 733363, 372955, 805, 16384⟩ := by
  decide +kernel

theorem context_13_372955_733363 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372955 ⟨733363, by decide⟩ :=
  accepted_of_selected 13 372955 ⟨733363, by decide⟩ ⟨13, 2, 0, 733363, 372955, 805, 16384⟩
    (by decide) selected_cut_29047

theorem unmarked_context_12_93238_733364 : frontier 9 ⟨733364, by decide⟩
    (prefixCache 12 93238) (prefixPartial 12 93238) = false := by
  decide +kernel

theorem node_context_12_93238_733364 : EJMOriginalGlobalDAGData.nodes 9 ⟨733364, by decide⟩ =
    .split (coordinate 12) (![⟨733300, by decide⟩,⟨733332, by decide⟩,⟨733354, by decide⟩,⟨733363, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93238_733364 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93238 ⟨733364, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93238
    ⟨733364, by decide⟩ (by decide) (![⟨733300, by decide⟩,⟨733332, by decide⟩,⟨733354, by decide⟩,⟨733363, by decide⟩]) unmarked_context_12_93238_733364 node_context_12_93238_733364
  intro a
  fin_cases a
  · exact context_13_372952_733300
  · exact context_13_372953_733332
  · exact context_13_372954_733354
  · exact context_13_372955_733363

theorem selected_cut_29048 : selected 8 ⟨733373, by decide⟩
    (prefixPartial 13 372956) = some ⟨13, 2, 0, 733373, 372956, 377, 16384⟩ := by
  decide +kernel

theorem context_13_372956_733373 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372956 ⟨733373, by decide⟩ :=
  accepted_of_selected 13 372956 ⟨733373, by decide⟩ ⟨13, 2, 0, 733373, 372956, 377, 16384⟩
    (by decide) selected_cut_29048

theorem selected_cut_29049 : selected 8 ⟨733399, by decide⟩
    (prefixPartial 13 372957) = some ⟨13, 2, 0, 733399, 372957, 1985, 16384⟩ := by
  decide +kernel

theorem context_13_372957_733399 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372957 ⟨733399, by decide⟩ :=
  accepted_of_selected 13 372957 ⟨733399, by decide⟩ ⟨13, 2, 0, 733399, 372957, 1985, 16384⟩
    (by decide) selected_cut_29049

theorem selected_cut_29050 : selected 8 ⟨733430, by decide⟩
    (prefixPartial 13 372958) = some ⟨13, 2, 0, 733430, 372958, 1969, 16384⟩ := by
  decide +kernel

theorem context_13_372958_733430 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372958 ⟨733430, by decide⟩ :=
  accepted_of_selected 13 372958 ⟨733430, by decide⟩ ⟨13, 2, 0, 733430, 372958, 1969, 16384⟩
    (by decide) selected_cut_29050

theorem selected_cut_29051 : selected 8 ⟨733436, by decide⟩
    (prefixPartial 13 372959) = some ⟨13, 2, 0, 733436, 372959, 857, 16384⟩ := by
  decide +kernel

theorem context_13_372959_733436 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372959 ⟨733436, by decide⟩ :=
  accepted_of_selected 13 372959 ⟨733436, by decide⟩ ⟨13, 2, 0, 733436, 372959, 857, 16384⟩
    (by decide) selected_cut_29051

theorem unmarked_context_12_93239_733437 : frontier 9 ⟨733437, by decide⟩
    (prefixCache 12 93239) (prefixPartial 12 93239) = false := by
  decide +kernel

theorem node_context_12_93239_733437 : EJMOriginalGlobalDAGData.nodes 9 ⟨733437, by decide⟩ =
    .split (coordinate 12) (![⟨733373, by decide⟩,⟨733399, by decide⟩,⟨733430, by decide⟩,⟨733436, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93239_733437 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93239 ⟨733437, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93239
    ⟨733437, by decide⟩ (by decide) (![⟨733373, by decide⟩,⟨733399, by decide⟩,⟨733430, by decide⟩,⟨733436, by decide⟩]) unmarked_context_12_93239_733437 node_context_12_93239_733437
  intro a
  fin_cases a
  · exact context_13_372956_733373
  · exact context_13_372957_733399
  · exact context_13_372958_733430
  · exact context_13_372959_733436

theorem unmarked_context_11_23309_733438 : frontier 10 ⟨733438, by decide⟩
    (prefixCache 11 23309) (prefixPartial 11 23309) = false := by
  decide +kernel

theorem node_context_11_23309_733438 : EJMOriginalGlobalDAGData.nodes 10 ⟨733438, by decide⟩ =
    .split (coordinate 11) (![⟨733226, by decide⟩,⟨733294, by decide⟩,⟨733364, by decide⟩,⟨733437, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23309_733438 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23309 ⟨733438, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23309
    ⟨733438, by decide⟩ (by decide) (![⟨733226, by decide⟩,⟨733294, by decide⟩,⟨733364, by decide⟩,⟨733437, by decide⟩]) unmarked_context_11_23309_733438 node_context_11_23309_733438
  intro a
  fin_cases a
  · exact context_12_93236_733226
  · exact context_12_93237_733294
  · exact context_12_93238_733364
  · exact context_12_93239_733437

theorem selected_cut_29052 : selected 8 ⟨733447, by decide⟩
    (prefixPartial 13 372960) = some ⟨13, 2, 0, 733447, 372960, 245, 16384⟩ := by
  decide +kernel

theorem context_13_372960_733447 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372960 ⟨733447, by decide⟩ :=
  accepted_of_selected 13 372960 ⟨733447, by decide⟩ ⟨13, 2, 0, 733447, 372960, 245, 16384⟩
    (by decide) selected_cut_29052

theorem selected_cut_29053 : selected 8 ⟨733474, by decide⟩
    (prefixPartial 13 372961) = some ⟨13, 2, 0, 733474, 372961, 1905, 16384⟩ := by
  decide +kernel

theorem context_13_372961_733474 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372961 ⟨733474, by decide⟩ :=
  accepted_of_selected 13 372961 ⟨733474, by decide⟩ ⟨13, 2, 0, 733474, 372961, 1905, 16384⟩
    (by decide) selected_cut_29053

theorem selected_cut_29054 : selected 8 ⟨733492, by decide⟩
    (prefixPartial 13 372962) = some ⟨13, 2, 0, 733492, 372962, 1577, 16384⟩ := by
  decide +kernel

theorem context_13_372962_733492 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372962 ⟨733492, by decide⟩ :=
  accepted_of_selected 13 372962 ⟨733492, by decide⟩ ⟨13, 2, 0, 733492, 372962, 1577, 16384⟩
    (by decide) selected_cut_29054

theorem selected_cut_29055 : selected 8 ⟨733503, by decide⟩
    (prefixPartial 13 372963) = some ⟨13, 2, 0, 733503, 372963, 845, 16384⟩ := by
  decide +kernel

theorem context_13_372963_733503 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372963 ⟨733503, by decide⟩ :=
  accepted_of_selected 13 372963 ⟨733503, by decide⟩ ⟨13, 2, 0, 733503, 372963, 845, 16384⟩
    (by decide) selected_cut_29055

theorem unmarked_context_12_93240_733504 : frontier 9 ⟨733504, by decide⟩
    (prefixCache 12 93240) (prefixPartial 12 93240) = false := by
  decide +kernel

theorem node_context_12_93240_733504 : EJMOriginalGlobalDAGData.nodes 9 ⟨733504, by decide⟩ =
    .split (coordinate 12) (![⟨733447, by decide⟩,⟨733474, by decide⟩,⟨733492, by decide⟩,⟨733503, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93240_733504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93240 ⟨733504, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93240
    ⟨733504, by decide⟩ (by decide) (![⟨733447, by decide⟩,⟨733474, by decide⟩,⟨733492, by decide⟩,⟨733503, by decide⟩]) unmarked_context_12_93240_733504 node_context_12_93240_733504
  intro a
  fin_cases a
  · exact context_13_372960_733447
  · exact context_13_372961_733474
  · exact context_13_372962_733492
  · exact context_13_372963_733503

theorem selected_cut_29056 : selected 8 ⟨733510, by decide⟩
    (prefixPartial 13 372964) = some ⟨13, 2, 0, 733510, 372964, 273, 16384⟩ := by
  decide +kernel

theorem context_13_372964_733510 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372964 ⟨733510, by decide⟩ :=
  accepted_of_selected 13 372964 ⟨733510, by decide⟩ ⟨13, 2, 0, 733510, 372964, 273, 16384⟩
    (by decide) selected_cut_29056

theorem selected_cut_29057 : selected 8 ⟨733537, by decide⟩
    (prefixPartial 13 372965) = some ⟨13, 2, 0, 733537, 372965, 1841, 16384⟩ := by
  decide +kernel

theorem context_13_372965_733537 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372965 ⟨733537, by decide⟩ :=
  accepted_of_selected 13 372965 ⟨733537, by decide⟩ ⟨13, 2, 0, 733537, 372965, 1841, 16384⟩
    (by decide) selected_cut_29057

theorem selected_cut_29058 : selected 8 ⟨733567, by decide⟩
    (prefixPartial 13 372966) = some ⟨13, 2, 0, 733567, 372966, 2081, 16384⟩ := by
  decide +kernel

theorem context_13_372966_733567 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372966 ⟨733567, by decide⟩ :=
  accepted_of_selected 13 372966 ⟨733567, by decide⟩ ⟨13, 2, 0, 733567, 372966, 2081, 16384⟩
    (by decide) selected_cut_29058

theorem selected_cut_29059 : selected 8 ⟨733583, by decide⟩
    (prefixPartial 13 372967) = some ⟨13, 2, 0, 733583, 372967, 969, 16384⟩ := by
  decide +kernel

theorem context_13_372967_733583 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372967 ⟨733583, by decide⟩ :=
  accepted_of_selected 13 372967 ⟨733583, by decide⟩ ⟨13, 2, 0, 733583, 372967, 969, 16384⟩
    (by decide) selected_cut_29059

theorem unmarked_context_12_93241_733584 : frontier 9 ⟨733584, by decide⟩
    (prefixCache 12 93241) (prefixPartial 12 93241) = false := by
  decide +kernel

theorem node_context_12_93241_733584 : EJMOriginalGlobalDAGData.nodes 9 ⟨733584, by decide⟩ =
    .split (coordinate 12) (![⟨733510, by decide⟩,⟨733537, by decide⟩,⟨733567, by decide⟩,⟨733583, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93241_733584 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93241 ⟨733584, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93241
    ⟨733584, by decide⟩ (by decide) (![⟨733510, by decide⟩,⟨733537, by decide⟩,⟨733567, by decide⟩,⟨733583, by decide⟩]) unmarked_context_12_93241_733584 node_context_12_93241_733584
  intro a
  fin_cases a
  · exact context_13_372964_733510
  · exact context_13_372965_733537
  · exact context_13_372966_733567
  · exact context_13_372967_733583

theorem selected_cut_29060 : selected 8 ⟨733590, by decide⟩
    (prefixPartial 13 372968) = some ⟨13, 2, 0, 733590, 372968, 157, 16384⟩ := by
  decide +kernel

theorem context_13_372968_733590 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372968 ⟨733590, by decide⟩ :=
  accepted_of_selected 13 372968 ⟨733590, by decide⟩ ⟨13, 2, 0, 733590, 372968, 157, 16384⟩
    (by decide) selected_cut_29060

theorem selected_cut_29061 : selected 8 ⟨733615, by decide⟩
    (prefixPartial 13 372969) = some ⟨13, 2, 0, 733615, 372969, 1905, 16384⟩ := by
  decide +kernel

theorem context_13_372969_733615 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372969 ⟨733615, by decide⟩ :=
  accepted_of_selected 13 372969 ⟨733615, by decide⟩ ⟨13, 2, 0, 733615, 372969, 1905, 16384⟩
    (by decide) selected_cut_29061

theorem selected_cut_29062 : selected 8 ⟨733640, by decide⟩
    (prefixPartial 13 372970) = some ⟨13, 2, 0, 733640, 372970, 1569, 16384⟩ := by
  decide +kernel

theorem context_13_372970_733640 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372970 ⟨733640, by decide⟩ :=
  accepted_of_selected 13 372970 ⟨733640, by decide⟩ ⟨13, 2, 0, 733640, 372970, 1569, 16384⟩
    (by decide) selected_cut_29062

theorem selected_cut_29063 : selected 8 ⟨733649, by decide⟩
    (prefixPartial 13 372971) = some ⟨13, 2, 0, 733649, 372971, 841, 16384⟩ := by
  decide +kernel

theorem context_13_372971_733649 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372971 ⟨733649, by decide⟩ :=
  accepted_of_selected 13 372971 ⟨733649, by decide⟩ ⟨13, 2, 0, 733649, 372971, 841, 16384⟩
    (by decide) selected_cut_29063

theorem unmarked_context_12_93242_733650 : frontier 9 ⟨733650, by decide⟩
    (prefixCache 12 93242) (prefixPartial 12 93242) = false := by
  decide +kernel

theorem node_context_12_93242_733650 : EJMOriginalGlobalDAGData.nodes 9 ⟨733650, by decide⟩ =
    .split (coordinate 12) (![⟨733590, by decide⟩,⟨733615, by decide⟩,⟨733640, by decide⟩,⟨733649, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93242_733650 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93242 ⟨733650, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93242
    ⟨733650, by decide⟩ (by decide) (![⟨733590, by decide⟩,⟨733615, by decide⟩,⟨733640, by decide⟩,⟨733649, by decide⟩]) unmarked_context_12_93242_733650 node_context_12_93242_733650
  intro a
  fin_cases a
  · exact context_13_372968_733590
  · exact context_13_372969_733615
  · exact context_13_372970_733640
  · exact context_13_372971_733649

theorem selected_cut_29064 : selected 8 ⟨733654, by decide⟩
    (prefixPartial 13 372972) = some ⟨13, 2, 0, 733654, 372972, 129, 16384⟩ := by
  decide +kernel

theorem context_13_372972_733654 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372972 ⟨733654, by decide⟩ :=
  accepted_of_selected 13 372972 ⟨733654, by decide⟩ ⟨13, 2, 0, 733654, 372972, 129, 16384⟩
    (by decide) selected_cut_29064

theorem selected_cut_29065 : selected 8 ⟨733684, by decide⟩
    (prefixPartial 13 372973) = some ⟨13, 2, 0, 733684, 372973, 2277, 16384⟩ := by
  decide +kernel

theorem context_13_372973_733684 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372973 ⟨733684, by decide⟩ :=
  accepted_of_selected 13 372973 ⟨733684, by decide⟩ ⟨13, 2, 0, 733684, 372973, 2277, 16384⟩
    (by decide) selected_cut_29065

theorem selected_cut_29066 : selected 8 ⟨733716, by decide⟩
    (prefixPartial 13 372974) = some ⟨13, 2, 0, 733716, 372974, 2025, 16384⟩ := by
  decide +kernel

theorem context_13_372974_733716 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372974 ⟨733716, by decide⟩ :=
  accepted_of_selected 13 372974 ⟨733716, by decide⟩ ⟨13, 2, 0, 733716, 372974, 2025, 16384⟩
    (by decide) selected_cut_29066

theorem selected_cut_29067 : selected 8 ⟨733728, by decide⟩
    (prefixPartial 13 372975) = some ⟨13, 2, 0, 733728, 372975, 969, 16384⟩ := by
  decide +kernel

theorem context_13_372975_733728 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 372975 ⟨733728, by decide⟩ :=
  accepted_of_selected 13 372975 ⟨733728, by decide⟩ ⟨13, 2, 0, 733728, 372975, 969, 16384⟩
    (by decide) selected_cut_29067

theorem unmarked_context_12_93243_733729 : frontier 9 ⟨733729, by decide⟩
    (prefixCache 12 93243) (prefixPartial 12 93243) = false := by
  decide +kernel

theorem node_context_12_93243_733729 : EJMOriginalGlobalDAGData.nodes 9 ⟨733729, by decide⟩ =
    .split (coordinate 12) (![⟨733654, by decide⟩,⟨733684, by decide⟩,⟨733716, by decide⟩,⟨733728, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93243_733729 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93243 ⟨733729, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93243
    ⟨733729, by decide⟩ (by decide) (![⟨733654, by decide⟩,⟨733684, by decide⟩,⟨733716, by decide⟩,⟨733728, by decide⟩]) unmarked_context_12_93243_733729 node_context_12_93243_733729
  intro a
  fin_cases a
  · exact context_13_372972_733654
  · exact context_13_372973_733684
  · exact context_13_372974_733716
  · exact context_13_372975_733728

theorem unmarked_context_11_23310_733730 : frontier 10 ⟨733730, by decide⟩
    (prefixCache 11 23310) (prefixPartial 11 23310) = false := by
  decide +kernel

theorem node_context_11_23310_733730 : EJMOriginalGlobalDAGData.nodes 10 ⟨733730, by decide⟩ =
    .split (coordinate 11) (![⟨733504, by decide⟩,⟨733584, by decide⟩,⟨733650, by decide⟩,⟨733729, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23310_733730 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23310 ⟨733730, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23310
    ⟨733730, by decide⟩ (by decide) (![⟨733504, by decide⟩,⟨733584, by decide⟩,⟨733650, by decide⟩,⟨733729, by decide⟩]) unmarked_context_11_23310_733730 node_context_11_23310_733730
  intro a
  fin_cases a
  · exact context_12_93240_733504
  · exact context_12_93241_733584
  · exact context_12_93242_733650
  · exact context_12_93243_733729

theorem selected_cut_29068 : selected 10 ⟨399386, by decide⟩
    (prefixPartial 11 23311) = some ⟨11, 2, 0, 399386, 23311, 5, 262144⟩ := by
  decide +kernel

theorem context_11_23311_399386 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23311 ⟨399386, by decide⟩ :=
  accepted_of_selected 11 23311 ⟨399386, by decide⟩ ⟨11, 2, 0, 399386, 23311, 5, 262144⟩
    (by decide) selected_cut_29068

theorem unmarked_context_10_5827_733731 : frontier 11 ⟨733731, by decide⟩
    (prefixCache 10 5827) (prefixPartial 10 5827) = false := by
  decide +kernel

theorem node_context_10_5827_733731 : EJMOriginalGlobalDAGData.nodes 11 ⟨733731, by decide⟩ =
    .split (coordinate 10) (![⟨733164, by decide⟩,⟨733438, by decide⟩,⟨733730, by decide⟩,⟨399386, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5827_733731 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5827 ⟨733731, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5827
    ⟨733731, by decide⟩ (by decide) (![⟨733164, by decide⟩,⟨733438, by decide⟩,⟨733730, by decide⟩,⟨399386, by decide⟩]) unmarked_context_10_5827_733731 node_context_10_5827_733731
  intro a
  fin_cases a
  · exact context_11_23308_733164
  · exact context_11_23309_733438
  · exact context_11_23310_733730
  · exact context_11_23311_399386

theorem unmarked_context_9_1456_733732 : frontier 12 ⟨733732, by decide⟩
    (prefixCache 9 1456) (prefixPartial 9 1456) = false := by
  decide +kernel

theorem node_context_9_1456_733732 : EJMOriginalGlobalDAGData.nodes 12 ⟨733732, by decide⟩ =
    .split (coordinate 9) (![⟨730318, by decide⟩,⟨731763, by decide⟩,⟨732967, by decide⟩,⟨733731, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1456_733732 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1456 ⟨733732, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1456
    ⟨733732, by decide⟩ (by decide) (![⟨730318, by decide⟩,⟨731763, by decide⟩,⟨732967, by decide⟩,⟨733731, by decide⟩]) unmarked_context_9_1456_733732 node_context_9_1456_733732
  intro a
  fin_cases a
  · exact context_10_5824_730318
  · exact context_10_5825_731763
  · exact context_10_5826_732967
  · exact context_10_5827_733731

theorem selected_cut_29069 : selected 9 ⟨450982, by decide⟩
    (prefixPartial 12 93248) = some ⟨12, 1, 0, 450982, 93248, 1, 65536⟩ := by
  decide +kernel

theorem context_12_93248_450982 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93248 ⟨450982, by decide⟩ :=
  accepted_of_selected 12 93248 ⟨450982, by decide⟩ ⟨12, 1, 0, 450982, 93248, 1, 65536⟩
    (by decide) selected_cut_29069

theorem selected_cut_29070 : selected 9 ⟨170504, by decide⟩
    (prefixPartial 12 93249) = some ⟨12, 1, 0, 170504, 93249, 1, 65536⟩ := by
  decide +kernel

theorem context_12_93249_170504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93249 ⟨170504, by decide⟩ :=
  accepted_of_selected 12 93249 ⟨170504, by decide⟩ ⟨12, 1, 0, 170504, 93249, 1, 65536⟩
    (by decide) selected_cut_29070

theorem selected_cut_29071 : selected 9 ⟨733792, by decide⟩
    (prefixPartial 12 93250) = some ⟨12, 2, 0, 733792, 93250, 3733, 65536⟩ := by
  decide +kernel

theorem context_12_93250_733792 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93250 ⟨733792, by decide⟩ :=
  accepted_of_selected 12 93250 ⟨733792, by decide⟩ ⟨12, 2, 0, 733792, 93250, 3733, 65536⟩
    (by decide) selected_cut_29071

theorem selected_cut_29072 : selected 9 ⟨733850, by decide⟩
    (prefixPartial 12 93251) = some ⟨12, 2, 0, 733850, 93251, 3829, 65536⟩ := by
  decide +kernel

theorem context_12_93251_733850 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93251 ⟨733850, by decide⟩ :=
  accepted_of_selected 12 93251 ⟨733850, by decide⟩ ⟨12, 2, 0, 733850, 93251, 3829, 65536⟩
    (by decide) selected_cut_29072

theorem unmarked_context_11_23312_733851 : frontier 10 ⟨733851, by decide⟩
    (prefixCache 11 23312) (prefixPartial 11 23312) = false := by
  decide +kernel

theorem node_context_11_23312_733851 : EJMOriginalGlobalDAGData.nodes 10 ⟨733851, by decide⟩ =
    .split (coordinate 11) (![⟨450982, by decide⟩,⟨170504, by decide⟩,⟨733792, by decide⟩,⟨733850, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23312_733851 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23312 ⟨733851, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23312
    ⟨733851, by decide⟩ (by decide) (![⟨450982, by decide⟩,⟨170504, by decide⟩,⟨733792, by decide⟩,⟨733850, by decide⟩]) unmarked_context_11_23312_733851 node_context_11_23312_733851
  intro a
  fin_cases a
  · exact context_12_93248_450982
  · exact context_12_93249_170504
  · exact context_12_93250_733792
  · exact context_12_93251_733850

theorem selected_cut_29073 : selected 9 ⟨733907, by decide⟩
    (prefixPartial 12 93252) = some ⟨12, 2, 0, 733907, 93252, 3517, 65536⟩ := by
  decide +kernel

theorem context_12_93252_733907 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93252 ⟨733907, by decide⟩ :=
  accepted_of_selected 12 93252 ⟨733907, by decide⟩ ⟨12, 2, 0, 733907, 93252, 3517, 65536⟩
    (by decide) selected_cut_29073

theorem selected_cut_29074 : selected 9 ⟨170504, by decide⟩
    (prefixPartial 12 93253) = some ⟨12, 1, 0, 170504, 93253, 1, 65536⟩ := by
  decide +kernel

theorem context_12_93253_170504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93253 ⟨170504, by decide⟩ :=
  accepted_of_selected 12 93253 ⟨170504, by decide⟩ ⟨12, 1, 0, 170504, 93253, 1, 65536⟩
    (by decide) selected_cut_29074

theorem selected_cut_29075 : selected 9 ⟨733966, by decide⟩
    (prefixPartial 12 93254) = some ⟨12, 2, 0, 733966, 93254, 3789, 65536⟩ := by
  decide +kernel

theorem context_12_93254_733966 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93254 ⟨733966, by decide⟩ :=
  accepted_of_selected 12 93254 ⟨733966, by decide⟩ ⟨12, 2, 0, 733966, 93254, 3789, 65536⟩
    (by decide) selected_cut_29075

theorem selected_cut_29076 : selected 9 ⟨734017, by decide⟩
    (prefixPartial 12 93255) = some ⟨12, 2, 0, 734017, 93255, 3973, 65536⟩ := by
  decide +kernel

theorem context_12_93255_734017 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93255 ⟨734017, by decide⟩ :=
  accepted_of_selected 12 93255 ⟨734017, by decide⟩ ⟨12, 2, 0, 734017, 93255, 3973, 65536⟩
    (by decide) selected_cut_29076

theorem unmarked_context_11_23313_734018 : frontier 10 ⟨734018, by decide⟩
    (prefixCache 11 23313) (prefixPartial 11 23313) = false := by
  decide +kernel

theorem node_context_11_23313_734018 : EJMOriginalGlobalDAGData.nodes 10 ⟨734018, by decide⟩ =
    .split (coordinate 11) (![⟨733907, by decide⟩,⟨170504, by decide⟩,⟨733966, by decide⟩,⟨734017, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23313_734018 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23313 ⟨734018, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23313
    ⟨734018, by decide⟩ (by decide) (![⟨733907, by decide⟩,⟨170504, by decide⟩,⟨733966, by decide⟩,⟨734017, by decide⟩]) unmarked_context_11_23313_734018 node_context_11_23313_734018
  intro a
  fin_cases a
  · exact context_12_93252_733907
  · exact context_12_93253_170504
  · exact context_12_93254_733966
  · exact context_12_93255_734017

theorem selected_cut_29077 : selected 9 ⟨734073, by decide⟩
    (prefixPartial 12 93256) = some ⟨12, 2, 0, 734073, 93256, 3405, 65536⟩ := by
  decide +kernel

theorem context_12_93256_734073 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93256 ⟨734073, by decide⟩ :=
  accepted_of_selected 12 93256 ⟨734073, by decide⟩ ⟨12, 2, 0, 734073, 93256, 3405, 65536⟩
    (by decide) selected_cut_29077

theorem selected_cut_29078 : selected 9 ⟨126371, by decide⟩
    (prefixPartial 12 93257) = some ⟨12, 1, 0, 126371, 93257, 1, 65536⟩ := by
  decide +kernel

theorem context_12_93257_126371 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93257 ⟨126371, by decide⟩ :=
  accepted_of_selected 12 93257 ⟨126371, by decide⟩ ⟨12, 1, 0, 126371, 93257, 1, 65536⟩
    (by decide) selected_cut_29078

theorem selected_cut_29079 : selected 9 ⟨734130, by decide⟩
    (prefixPartial 12 93258) = some ⟨12, 2, 0, 734130, 93258, 3409, 65536⟩ := by
  decide +kernel

theorem context_12_93258_734130 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93258 ⟨734130, by decide⟩ :=
  accepted_of_selected 12 93258 ⟨734130, by decide⟩ ⟨12, 2, 0, 734130, 93258, 3409, 65536⟩
    (by decide) selected_cut_29079

theorem selected_cut_29080 : selected 9 ⟨734188, by decide⟩
    (prefixPartial 12 93259) = some ⟨12, 2, 0, 734188, 93259, 3825, 65536⟩ := by
  decide +kernel

theorem context_12_93259_734188 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93259 ⟨734188, by decide⟩ :=
  accepted_of_selected 12 93259 ⟨734188, by decide⟩ ⟨12, 2, 0, 734188, 93259, 3825, 65536⟩
    (by decide) selected_cut_29080

theorem unmarked_context_11_23314_734189 : frontier 10 ⟨734189, by decide⟩
    (prefixCache 11 23314) (prefixPartial 11 23314) = false := by
  decide +kernel

theorem node_context_11_23314_734189 : EJMOriginalGlobalDAGData.nodes 10 ⟨734189, by decide⟩ =
    .split (coordinate 11) (![⟨734073, by decide⟩,⟨126371, by decide⟩,⟨734130, by decide⟩,⟨734188, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23314_734189 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23314 ⟨734189, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23314
    ⟨734189, by decide⟩ (by decide) (![⟨734073, by decide⟩,⟨126371, by decide⟩,⟨734130, by decide⟩,⟨734188, by decide⟩]) unmarked_context_11_23314_734189 node_context_11_23314_734189
  intro a
  fin_cases a
  · exact context_12_93256_734073
  · exact context_12_93257_126371
  · exact context_12_93258_734130
  · exact context_12_93259_734188

theorem selected_cut_29081 : selected 9 ⟨734240, by decide⟩
    (prefixPartial 12 93260) = some ⟨12, 2, 0, 734240, 93260, 2973, 65536⟩ := by
  decide +kernel

theorem context_12_93260_734240 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93260 ⟨734240, by decide⟩ :=
  accepted_of_selected 12 93260 ⟨734240, by decide⟩ ⟨12, 2, 0, 734240, 93260, 2973, 65536⟩
    (by decide) selected_cut_29081

theorem selected_cut_29082 : selected 9 ⟨320864, by decide⟩
    (prefixPartial 12 93261) = some ⟨12, 1, 0, 320864, 93261, 1, 65536⟩ := by
  decide +kernel

theorem context_12_93261_320864 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93261 ⟨320864, by decide⟩ :=
  accepted_of_selected 12 93261 ⟨320864, by decide⟩ ⟨12, 1, 0, 320864, 93261, 1, 65536⟩
    (by decide) selected_cut_29082

theorem selected_cut_29083 : selected 9 ⟨734293, by decide⟩
    (prefixPartial 12 93262) = some ⟨12, 2, 0, 734293, 93262, 3521, 65536⟩ := by
  decide +kernel

theorem context_12_93262_734293 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93262 ⟨734293, by decide⟩ :=
  accepted_of_selected 12 93262 ⟨734293, by decide⟩ ⟨12, 2, 0, 734293, 93262, 3521, 65536⟩
    (by decide) selected_cut_29083

theorem selected_cut_29084 : selected 9 ⟨734343, by decide⟩
    (prefixPartial 12 93263) = some ⟨12, 2, 0, 734343, 93263, 3249, 65536⟩ := by
  decide +kernel

theorem context_12_93263_734343 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93263 ⟨734343, by decide⟩ :=
  accepted_of_selected 12 93263 ⟨734343, by decide⟩ ⟨12, 2, 0, 734343, 93263, 3249, 65536⟩
    (by decide) selected_cut_29084

theorem unmarked_context_11_23315_734344 : frontier 10 ⟨734344, by decide⟩
    (prefixCache 11 23315) (prefixPartial 11 23315) = false := by
  decide +kernel

theorem node_context_11_23315_734344 : EJMOriginalGlobalDAGData.nodes 10 ⟨734344, by decide⟩ =
    .split (coordinate 11) (![⟨734240, by decide⟩,⟨320864, by decide⟩,⟨734293, by decide⟩,⟨734343, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23315_734344 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23315 ⟨734344, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23315
    ⟨734344, by decide⟩ (by decide) (![⟨734240, by decide⟩,⟨320864, by decide⟩,⟨734293, by decide⟩,⟨734343, by decide⟩]) unmarked_context_11_23315_734344 node_context_11_23315_734344
  intro a
  fin_cases a
  · exact context_12_93260_734240
  · exact context_12_93261_320864
  · exact context_12_93262_734293
  · exact context_12_93263_734343

theorem unmarked_context_10_5828_734345 : frontier 11 ⟨734345, by decide⟩
    (prefixCache 10 5828) (prefixPartial 10 5828) = false := by
  decide +kernel

theorem node_context_10_5828_734345 : EJMOriginalGlobalDAGData.nodes 11 ⟨734345, by decide⟩ =
    .split (coordinate 10) (![⟨733851, by decide⟩,⟨734018, by decide⟩,⟨734189, by decide⟩,⟨734344, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5828_734345 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5828 ⟨734345, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5828
    ⟨734345, by decide⟩ (by decide) (![⟨733851, by decide⟩,⟨734018, by decide⟩,⟨734189, by decide⟩,⟨734344, by decide⟩]) unmarked_context_10_5828_734345 node_context_10_5828_734345
  intro a
  fin_cases a
  · exact context_11_23312_733851
  · exact context_11_23313_734018
  · exact context_11_23314_734189
  · exact context_11_23315_734344

theorem selected_cut_29085 : selected 9 ⟨266170, by decide⟩
    (prefixPartial 12 93264) = some ⟨12, 1, 0, 266170, 93264, 1, 65536⟩ := by
  decide +kernel

theorem context_12_93264_266170 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93264 ⟨266170, by decide⟩ :=
  accepted_of_selected 12 93264 ⟨266170, by decide⟩ ⟨12, 1, 0, 266170, 93264, 1, 65536⟩
    (by decide) selected_cut_29085

theorem selected_cut_29086 : selected 9 ⟨642341, by decide⟩
    (prefixPartial 12 93265) = some ⟨12, 1, 0, 642341, 93265, 1, 65536⟩ := by
  decide +kernel

theorem context_12_93265_642341 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93265 ⟨642341, by decide⟩ :=
  accepted_of_selected 12 93265 ⟨642341, by decide⟩ ⟨12, 1, 0, 642341, 93265, 1, 65536⟩
    (by decide) selected_cut_29086

theorem selected_cut_29087 : selected 9 ⟨734386, by decide⟩
    (prefixPartial 12 93266) = some ⟨12, 2, 0, 734386, 93266, 3397, 65536⟩ := by
  decide +kernel

theorem context_12_93266_734386 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93266 ⟨734386, by decide⟩ :=
  accepted_of_selected 12 93266 ⟨734386, by decide⟩ ⟨12, 2, 0, 734386, 93266, 3397, 65536⟩
    (by decide) selected_cut_29087

theorem selected_cut_29088 : selected 9 ⟨734436, by decide⟩
    (prefixPartial 12 93267) = some ⟨12, 2, 0, 734436, 93267, 3717, 65536⟩ := by
  decide +kernel

theorem context_12_93267_734436 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93267 ⟨734436, by decide⟩ :=
  accepted_of_selected 12 93267 ⟨734436, by decide⟩ ⟨12, 2, 0, 734436, 93267, 3717, 65536⟩
    (by decide) selected_cut_29088

theorem unmarked_context_11_23316_734437 : frontier 10 ⟨734437, by decide⟩
    (prefixCache 11 23316) (prefixPartial 11 23316) = false := by
  decide +kernel

theorem node_context_11_23316_734437 : EJMOriginalGlobalDAGData.nodes 10 ⟨734437, by decide⟩ =
    .split (coordinate 11) (![⟨266170, by decide⟩,⟨642341, by decide⟩,⟨734386, by decide⟩,⟨734436, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23316_734437 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23316 ⟨734437, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23316
    ⟨734437, by decide⟩ (by decide) (![⟨266170, by decide⟩,⟨642341, by decide⟩,⟨734386, by decide⟩,⟨734436, by decide⟩]) unmarked_context_11_23316_734437 node_context_11_23316_734437
  intro a
  fin_cases a
  · exact context_12_93264_266170
  · exact context_12_93265_642341
  · exact context_12_93266_734386
  · exact context_12_93267_734436

theorem selected_cut_29089 : selected 9 ⟨734487, by decide⟩
    (prefixPartial 12 93268) = some ⟨12, 2, 0, 734487, 93268, 3569, 65536⟩ := by
  decide +kernel

theorem context_12_93268_734487 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93268 ⟨734487, by decide⟩ :=
  accepted_of_selected 12 93268 ⟨734487, by decide⟩ ⟨12, 2, 0, 734487, 93268, 3569, 65536⟩
    (by decide) selected_cut_29089

theorem selected_cut_29090 : selected 9 ⟨642341, by decide⟩
    (prefixPartial 12 93269) = some ⟨12, 1, 0, 642341, 93269, 1, 65536⟩ := by
  decide +kernel

theorem context_12_93269_642341 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93269 ⟨642341, by decide⟩ :=
  accepted_of_selected 12 93269 ⟨642341, by decide⟩ ⟨12, 1, 0, 642341, 93269, 1, 65536⟩
    (by decide) selected_cut_29090

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
