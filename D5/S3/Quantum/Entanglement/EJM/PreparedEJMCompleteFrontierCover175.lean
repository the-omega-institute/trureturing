/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover174
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_16804 : selected 8 ⟨427820, by decide⟩
    (prefixPartial 13 113845) = some ⟨13, 2, 0, 427820, 113845, 2249, 16384⟩ := by
  decide +kernel

theorem context_13_113845_427820 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113845 ⟨427820, by decide⟩ :=
  accepted_of_selected 13 113845 ⟨427820, by decide⟩ ⟨13, 2, 0, 427820, 113845, 2249, 16384⟩
    (by decide) selected_cut_16804

theorem selected_cut_16805 : selected 8 ⟨427844, by decide⟩
    (prefixPartial 13 113846) = some ⟨13, 2, 0, 427844, 113846, 1513, 16384⟩ := by
  decide +kernel

theorem context_13_113846_427844 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113846 ⟨427844, by decide⟩ :=
  accepted_of_selected 13 113846 ⟨427844, by decide⟩ ⟨13, 2, 0, 427844, 113846, 1513, 16384⟩
    (by decide) selected_cut_16805

theorem selected_cut_16806 : selected 8 ⟨427851, by decide⟩
    (prefixPartial 13 113847) = some ⟨13, 2, 0, 427851, 113847, 733, 16384⟩ := by
  decide +kernel

theorem context_13_113847_427851 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113847 ⟨427851, by decide⟩ :=
  accepted_of_selected 13 113847 ⟨427851, by decide⟩ ⟨13, 2, 0, 427851, 113847, 733, 16384⟩
    (by decide) selected_cut_16806

theorem unmarked_context_12_28461_427852 : frontier 9 ⟨427852, by decide⟩
    (prefixCache 12 28461) (prefixPartial 12 28461) = false := by
  decide +kernel

theorem node_context_12_28461_427852 : EJMOriginalGlobalDAGData.nodes 9 ⟨427852, by decide⟩ =
    .split (coordinate 12) (![⟨427787, by decide⟩,⟨427820, by decide⟩,⟨427844, by decide⟩,⟨427851, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28461_427852 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28461 ⟨427852, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28461
    ⟨427852, by decide⟩ (by decide) (![⟨427787, by decide⟩,⟨427820, by decide⟩,⟨427844, by decide⟩,⟨427851, by decide⟩]) unmarked_context_12_28461_427852 node_context_12_28461_427852
  intro a
  fin_cases a
  · exact context_13_113844_427787
  · exact context_13_113845_427820
  · exact context_13_113846_427844
  · exact context_13_113847_427851

theorem selected_cut_16807 : selected 8 ⟨427869, by decide⟩
    (prefixPartial 13 113848) = some ⟨13, 2, 0, 427869, 113848, 901, 16384⟩ := by
  decide +kernel

theorem context_13_113848_427869 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113848 ⟨427869, by decide⟩ :=
  accepted_of_selected 13 113848 ⟨427869, by decide⟩ ⟨13, 2, 0, 427869, 113848, 901, 16384⟩
    (by decide) selected_cut_16807

theorem selected_cut_16808 : selected 8 ⟨427909, by decide⟩
    (prefixPartial 13 113849) = some ⟨13, 2, 0, 427909, 113849, 2377, 16384⟩ := by
  decide +kernel

theorem context_13_113849_427909 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113849 ⟨427909, by decide⟩ :=
  accepted_of_selected 13 113849 ⟨427909, by decide⟩ ⟨13, 2, 0, 427909, 113849, 2377, 16384⟩
    (by decide) selected_cut_16808

theorem selected_cut_16809 : selected 8 ⟨427929, by decide⟩
    (prefixPartial 13 113850) = some ⟨13, 2, 0, 427929, 113850, 1421, 16384⟩ := by
  decide +kernel

theorem context_13_113850_427929 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113850 ⟨427929, by decide⟩ :=
  accepted_of_selected 13 113850 ⟨427929, by decide⟩ ⟨13, 2, 0, 427929, 113850, 1421, 16384⟩
    (by decide) selected_cut_16809

theorem selected_cut_16810 : selected 8 ⟨427932, by decide⟩
    (prefixPartial 13 113851) = some ⟨13, 2, 0, 427932, 113851, 705, 16384⟩ := by
  decide +kernel

theorem context_13_113851_427932 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113851 ⟨427932, by decide⟩ :=
  accepted_of_selected 13 113851 ⟨427932, by decide⟩ ⟨13, 2, 0, 427932, 113851, 705, 16384⟩
    (by decide) selected_cut_16810

theorem unmarked_context_12_28462_427933 : frontier 9 ⟨427933, by decide⟩
    (prefixCache 12 28462) (prefixPartial 12 28462) = false := by
  decide +kernel

theorem node_context_12_28462_427933 : EJMOriginalGlobalDAGData.nodes 9 ⟨427933, by decide⟩ =
    .split (coordinate 12) (![⟨427869, by decide⟩,⟨427909, by decide⟩,⟨427929, by decide⟩,⟨427932, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28462_427933 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28462 ⟨427933, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28462
    ⟨427933, by decide⟩ (by decide) (![⟨427869, by decide⟩,⟨427909, by decide⟩,⟨427929, by decide⟩,⟨427932, by decide⟩]) unmarked_context_12_28462_427933 node_context_12_28462_427933
  intro a
  fin_cases a
  · exact context_13_113848_427869
  · exact context_13_113849_427909
  · exact context_13_113850_427929
  · exact context_13_113851_427932

theorem selected_cut_16811 : selected 8 ⟨427954, by decide⟩
    (prefixPartial 13 113852) = some ⟨13, 2, 0, 427954, 113852, 1321, 16384⟩ := by
  decide +kernel

theorem context_13_113852_427954 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113852 ⟨427954, by decide⟩ :=
  accepted_of_selected 13 113852 ⟨427954, by decide⟩ ⟨13, 2, 0, 427954, 113852, 1321, 16384⟩
    (by decide) selected_cut_16811

theorem selected_cut_16812 : selected 7 ⟨427978, by decide⟩
    (prefixPartial 14 455412) = some ⟨14, 2, 0, 427978, 455412, 1213, 4096⟩ := by
  decide +kernel

theorem context_14_455412_427978 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 455412 ⟨427978, by decide⟩ :=
  accepted_of_selected 14 455412 ⟨427978, by decide⟩ ⟨14, 2, 0, 427978, 455412, 1213, 4096⟩
    (by decide) selected_cut_16812

theorem selected_cut_16813 : selected 7 ⟨428002, by decide⟩
    (prefixPartial 14 455413) = some ⟨14, 2, 0, 428002, 455413, 893, 4096⟩ := by
  decide +kernel

theorem context_14_455413_428002 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 455413 ⟨428002, by decide⟩ :=
  accepted_of_selected 14 455413 ⟨428002, by decide⟩ ⟨14, 2, 0, 428002, 455413, 893, 4096⟩
    (by decide) selected_cut_16813

theorem selected_cut_16814 : selected 7 ⟨428022, by decide⟩
    (prefixPartial 14 455414) = some ⟨14, 2, 0, 428022, 455414, 1065, 4096⟩ := by
  decide +kernel

theorem context_14_455414_428022 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 455414 ⟨428022, by decide⟩ :=
  accepted_of_selected 14 455414 ⟨428022, by decide⟩ ⟨14, 2, 0, 428022, 455414, 1065, 4096⟩
    (by decide) selected_cut_16814

theorem selected_cut_16815 : selected 7 ⟨428042, by decide⟩
    (prefixPartial 14 455415) = some ⟨14, 2, 0, 428042, 455415, 993, 4096⟩ := by
  decide +kernel

theorem context_14_455415_428042 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 455415 ⟨428042, by decide⟩ :=
  accepted_of_selected 14 455415 ⟨428042, by decide⟩ ⟨14, 2, 0, 428042, 455415, 993, 4096⟩
    (by decide) selected_cut_16815

theorem unmarked_context_13_113853_428043 : frontier 8 ⟨428043, by decide⟩
    (prefixCache 13 113853) (prefixPartial 13 113853) = false := by
  decide +kernel

theorem node_context_13_113853_428043 : EJMOriginalGlobalDAGData.nodes 8 ⟨428043, by decide⟩ =
    .split (coordinate 13) (![⟨427978, by decide⟩,⟨428002, by decide⟩,⟨428022, by decide⟩,⟨428042, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_113853_428043 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113853 ⟨428043, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 113853
    ⟨428043, by decide⟩ (by decide) (![⟨427978, by decide⟩,⟨428002, by decide⟩,⟨428022, by decide⟩,⟨428042, by decide⟩]) unmarked_context_13_113853_428043 node_context_13_113853_428043
  intro a
  fin_cases a
  · exact context_14_455412_427978
  · exact context_14_455413_428002
  · exact context_14_455414_428022
  · exact context_14_455415_428042

theorem selected_cut_16816 : selected 8 ⟨428076, by decide⟩
    (prefixPartial 13 113854) = some ⟨13, 2, 0, 428076, 113854, 2549, 16384⟩ := by
  decide +kernel

theorem context_13_113854_428076 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113854 ⟨428076, by decide⟩ :=
  accepted_of_selected 13 113854 ⟨428076, by decide⟩ ⟨13, 2, 0, 428076, 113854, 2549, 16384⟩
    (by decide) selected_cut_16816

theorem selected_cut_16817 : selected 8 ⟨428103, by decide⟩
    (prefixPartial 13 113855) = some ⟨13, 2, 0, 428103, 113855, 1261, 16384⟩ := by
  decide +kernel

theorem context_13_113855_428103 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113855 ⟨428103, by decide⟩ :=
  accepted_of_selected 13 113855 ⟨428103, by decide⟩ ⟨13, 2, 0, 428103, 113855, 1261, 16384⟩
    (by decide) selected_cut_16817

theorem unmarked_context_12_28463_428104 : frontier 9 ⟨428104, by decide⟩
    (prefixCache 12 28463) (prefixPartial 12 28463) = false := by
  decide +kernel

theorem node_context_12_28463_428104 : EJMOriginalGlobalDAGData.nodes 9 ⟨428104, by decide⟩ =
    .split (coordinate 12) (![⟨427954, by decide⟩,⟨428043, by decide⟩,⟨428076, by decide⟩,⟨428103, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28463_428104 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28463 ⟨428104, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28463
    ⟨428104, by decide⟩ (by decide) (![⟨427954, by decide⟩,⟨428043, by decide⟩,⟨428076, by decide⟩,⟨428103, by decide⟩]) unmarked_context_12_28463_428104 node_context_12_28463_428104
  intro a
  fin_cases a
  · exact context_13_113852_427954
  · exact context_13_113853_428043
  · exact context_13_113854_428076
  · exact context_13_113855_428103

theorem unmarked_context_11_7115_428105 : frontier 10 ⟨428105, by decide⟩
    (prefixCache 11 7115) (prefixPartial 11 7115) = false := by
  decide +kernel

theorem node_context_11_7115_428105 : EJMOriginalGlobalDAGData.nodes 10 ⟨428105, by decide⟩ =
    .split (coordinate 11) (![⟨427768, by decide⟩,⟨427852, by decide⟩,⟨427933, by decide⟩,⟨428104, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_7115_428105 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7115 ⟨428105, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 7115
    ⟨428105, by decide⟩ (by decide) (![⟨427768, by decide⟩,⟨427852, by decide⟩,⟨427933, by decide⟩,⟨428104, by decide⟩]) unmarked_context_11_7115_428105 node_context_11_7115_428105
  intro a
  fin_cases a
  · exact context_12_28460_427768
  · exact context_12_28461_427852
  · exact context_12_28462_427933
  · exact context_12_28463_428104

theorem unmarked_context_10_1778_428106 : frontier 11 ⟨428106, by decide⟩
    (prefixCache 10 1778) (prefixPartial 10 1778) = false := by
  decide +kernel

theorem node_context_10_1778_428106 : EJMOriginalGlobalDAGData.nodes 11 ⟨428106, by decide⟩ =
    .split (coordinate 10) (![⟨427065, by decide⟩,⟨427401, by decide⟩,⟨427709, by decide⟩,⟨428105, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1778_428106 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1778 ⟨428106, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1778
    ⟨428106, by decide⟩ (by decide) (![⟨427065, by decide⟩,⟨427401, by decide⟩,⟨427709, by decide⟩,⟨428105, by decide⟩]) unmarked_context_10_1778_428106 node_context_10_1778_428106
  intro a
  fin_cases a
  · exact context_11_7112_427065
  · exact context_11_7113_427401
  · exact context_11_7114_427709
  · exact context_11_7115_428105

theorem selected_cut_16818 : selected 8 ⟨428112, by decide⟩
    (prefixPartial 13 113856) = some ⟨13, 2, 0, 428112, 113856, 617, 16384⟩ := by
  decide +kernel

theorem context_13_113856_428112 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113856 ⟨428112, by decide⟩ :=
  accepted_of_selected 13 113856 ⟨428112, by decide⟩ ⟨13, 2, 0, 428112, 113856, 617, 16384⟩
    (by decide) selected_cut_16818

theorem selected_cut_16819 : selected 8 ⟨428138, by decide⟩
    (prefixPartial 13 113857) = some ⟨13, 2, 0, 428138, 113857, 2477, 16384⟩ := by
  decide +kernel

theorem context_13_113857_428138 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113857 ⟨428138, by decide⟩ :=
  accepted_of_selected 13 113857 ⟨428138, by decide⟩ ⟨13, 2, 0, 428138, 113857, 2477, 16384⟩
    (by decide) selected_cut_16819

theorem selected_cut_16820 : selected 8 ⟨428159, by decide⟩
    (prefixPartial 13 113858) = some ⟨13, 2, 0, 428159, 113858, 1497, 16384⟩ := by
  decide +kernel

theorem context_13_113858_428159 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113858 ⟨428159, by decide⟩ :=
  accepted_of_selected 13 113858 ⟨428159, by decide⟩ ⟨13, 2, 0, 428159, 113858, 1497, 16384⟩
    (by decide) selected_cut_16820

theorem selected_cut_16821 : selected 8 ⟨428163, by decide⟩
    (prefixPartial 13 113859) = some ⟨13, 2, 0, 428163, 113859, 725, 16384⟩ := by
  decide +kernel

theorem context_13_113859_428163 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113859 ⟨428163, by decide⟩ :=
  accepted_of_selected 13 113859 ⟨428163, by decide⟩ ⟨13, 2, 0, 428163, 113859, 725, 16384⟩
    (by decide) selected_cut_16821

theorem unmarked_context_12_28464_428164 : frontier 9 ⟨428164, by decide⟩
    (prefixCache 12 28464) (prefixPartial 12 28464) = false := by
  decide +kernel

theorem node_context_12_28464_428164 : EJMOriginalGlobalDAGData.nodes 9 ⟨428164, by decide⟩ =
    .split (coordinate 12) (![⟨428112, by decide⟩,⟨428138, by decide⟩,⟨428159, by decide⟩,⟨428163, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28464_428164 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28464 ⟨428164, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28464
    ⟨428164, by decide⟩ (by decide) (![⟨428112, by decide⟩,⟨428138, by decide⟩,⟨428159, by decide⟩,⟨428163, by decide⟩]) unmarked_context_12_28464_428164 node_context_12_28464_428164
  intro a
  fin_cases a
  · exact context_13_113856_428112
  · exact context_13_113857_428138
  · exact context_13_113858_428159
  · exact context_13_113859_428163

theorem selected_cut_16822 : selected 8 ⟨428171, by decide⟩
    (prefixPartial 13 113860) = some ⟨13, 2, 0, 428171, 113860, 645, 16384⟩ := by
  decide +kernel

theorem context_13_113860_428171 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113860 ⟨428171, by decide⟩ :=
  accepted_of_selected 13 113860 ⟨428171, by decide⟩ ⟨13, 2, 0, 428171, 113860, 645, 16384⟩
    (by decide) selected_cut_16822

theorem selected_cut_16823 : selected 8 ⟨428207, by decide⟩
    (prefixPartial 13 113861) = some ⟨13, 2, 0, 428207, 113861, 2645, 16384⟩ := by
  decide +kernel

theorem context_13_113861_428207 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113861 ⟨428207, by decide⟩ :=
  accepted_of_selected 13 113861 ⟨428207, by decide⟩ ⟨13, 2, 0, 428207, 113861, 2645, 16384⟩
    (by decide) selected_cut_16823

theorem selected_cut_16824 : selected 8 ⟨428228, by decide⟩
    (prefixPartial 13 113862) = some ⟨13, 2, 0, 428228, 113862, 1805, 16384⟩ := by
  decide +kernel

theorem context_13_113862_428228 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113862 ⟨428228, by decide⟩ :=
  accepted_of_selected 13 113862 ⟨428228, by decide⟩ ⟨13, 2, 0, 428228, 113862, 1805, 16384⟩
    (by decide) selected_cut_16824

theorem selected_cut_16825 : selected 8 ⟨428232, by decide⟩
    (prefixPartial 13 113863) = some ⟨13, 2, 0, 428232, 113863, 625, 16384⟩ := by
  decide +kernel

theorem context_13_113863_428232 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113863 ⟨428232, by decide⟩ :=
  accepted_of_selected 13 113863 ⟨428232, by decide⟩ ⟨13, 2, 0, 428232, 113863, 625, 16384⟩
    (by decide) selected_cut_16825

theorem unmarked_context_12_28465_428233 : frontier 9 ⟨428233, by decide⟩
    (prefixCache 12 28465) (prefixPartial 12 28465) = false := by
  decide +kernel

theorem node_context_12_28465_428233 : EJMOriginalGlobalDAGData.nodes 9 ⟨428233, by decide⟩ =
    .split (coordinate 12) (![⟨428171, by decide⟩,⟨428207, by decide⟩,⟨428228, by decide⟩,⟨428232, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28465_428233 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28465 ⟨428233, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28465
    ⟨428233, by decide⟩ (by decide) (![⟨428171, by decide⟩,⟨428207, by decide⟩,⟨428228, by decide⟩,⟨428232, by decide⟩]) unmarked_context_12_28465_428233 node_context_12_28465_428233
  intro a
  fin_cases a
  · exact context_13_113860_428171
  · exact context_13_113861_428207
  · exact context_13_113862_428228
  · exact context_13_113863_428232

theorem selected_cut_16826 : selected 8 ⟨428240, by decide⟩
    (prefixPartial 13 113864) = some ⟨13, 2, 0, 428240, 113864, 661, 16384⟩ := by
  decide +kernel

theorem context_13_113864_428240 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113864 ⟨428240, by decide⟩ :=
  accepted_of_selected 13 113864 ⟨428240, by decide⟩ ⟨13, 2, 0, 428240, 113864, 661, 16384⟩
    (by decide) selected_cut_16826

theorem selected_cut_16827 : selected 8 ⟨428274, by decide⟩
    (prefixPartial 13 113865) = some ⟨13, 2, 0, 428274, 113865, 2549, 16384⟩ := by
  decide +kernel

theorem context_13_113865_428274 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113865 ⟨428274, by decide⟩ :=
  accepted_of_selected 13 113865 ⟨428274, by decide⟩ ⟨13, 2, 0, 428274, 113865, 2549, 16384⟩
    (by decide) selected_cut_16827

theorem selected_cut_16828 : selected 8 ⟨428298, by decide⟩
    (prefixPartial 13 113866) = some ⟨13, 2, 0, 428298, 113866, 1805, 16384⟩ := by
  decide +kernel

theorem context_13_113866_428298 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113866 ⟨428298, by decide⟩ :=
  accepted_of_selected 13 113866 ⟨428298, by decide⟩ ⟨13, 2, 0, 428298, 113866, 1805, 16384⟩
    (by decide) selected_cut_16828

theorem selected_cut_16829 : selected 8 ⟨428303, by decide⟩
    (prefixPartial 13 113867) = some ⟨13, 2, 0, 428303, 113867, 661, 16384⟩ := by
  decide +kernel

theorem context_13_113867_428303 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113867 ⟨428303, by decide⟩ :=
  accepted_of_selected 13 113867 ⟨428303, by decide⟩ ⟨13, 2, 0, 428303, 113867, 661, 16384⟩
    (by decide) selected_cut_16829

theorem unmarked_context_12_28466_428304 : frontier 9 ⟨428304, by decide⟩
    (prefixCache 12 28466) (prefixPartial 12 28466) = false := by
  decide +kernel

theorem node_context_12_28466_428304 : EJMOriginalGlobalDAGData.nodes 9 ⟨428304, by decide⟩ =
    .split (coordinate 12) (![⟨428240, by decide⟩,⟨428274, by decide⟩,⟨428298, by decide⟩,⟨428303, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28466_428304 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28466 ⟨428304, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28466
    ⟨428304, by decide⟩ (by decide) (![⟨428240, by decide⟩,⟨428274, by decide⟩,⟨428298, by decide⟩,⟨428303, by decide⟩]) unmarked_context_12_28466_428304 node_context_12_28466_428304
  intro a
  fin_cases a
  · exact context_13_113864_428240
  · exact context_13_113865_428274
  · exact context_13_113866_428298
  · exact context_13_113867_428303

theorem selected_cut_16830 : selected 8 ⟨428311, by decide⟩
    (prefixPartial 13 113868) = some ⟨13, 2, 0, 428311, 113868, 657, 16384⟩ := by
  decide +kernel

theorem context_13_113868_428311 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113868 ⟨428311, by decide⟩ :=
  accepted_of_selected 13 113868 ⟨428311, by decide⟩ ⟨13, 2, 0, 428311, 113868, 657, 16384⟩
    (by decide) selected_cut_16830

theorem selected_cut_16831 : selected 8 ⟨428343, by decide⟩
    (prefixPartial 13 113869) = some ⟨13, 2, 0, 428343, 113869, 2681, 16384⟩ := by
  decide +kernel

theorem context_13_113869_428343 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113869 ⟨428343, by decide⟩ :=
  accepted_of_selected 13 113869 ⟨428343, by decide⟩ ⟨13, 2, 0, 428343, 113869, 2681, 16384⟩
    (by decide) selected_cut_16831

theorem selected_cut_16832 : selected 8 ⟨428361, by decide⟩
    (prefixPartial 13 113870) = some ⟨13, 2, 0, 428361, 113870, 1829, 16384⟩ := by
  decide +kernel

theorem context_13_113870_428361 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113870 ⟨428361, by decide⟩ :=
  accepted_of_selected 13 113870 ⟨428361, by decide⟩ ⟨13, 2, 0, 428361, 113870, 1829, 16384⟩
    (by decide) selected_cut_16832

theorem selected_cut_16833 : selected 8 ⟨428368, by decide⟩
    (prefixPartial 13 113871) = some ⟨13, 2, 0, 428368, 113871, 641, 16384⟩ := by
  decide +kernel

theorem context_13_113871_428368 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113871 ⟨428368, by decide⟩ :=
  accepted_of_selected 13 113871 ⟨428368, by decide⟩ ⟨13, 2, 0, 428368, 113871, 641, 16384⟩
    (by decide) selected_cut_16833

theorem unmarked_context_12_28467_428369 : frontier 9 ⟨428369, by decide⟩
    (prefixCache 12 28467) (prefixPartial 12 28467) = false := by
  decide +kernel

theorem node_context_12_28467_428369 : EJMOriginalGlobalDAGData.nodes 9 ⟨428369, by decide⟩ =
    .split (coordinate 12) (![⟨428311, by decide⟩,⟨428343, by decide⟩,⟨428361, by decide⟩,⟨428368, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28467_428369 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28467 ⟨428369, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28467
    ⟨428369, by decide⟩ (by decide) (![⟨428311, by decide⟩,⟨428343, by decide⟩,⟨428361, by decide⟩,⟨428368, by decide⟩]) unmarked_context_12_28467_428369 node_context_12_28467_428369
  intro a
  fin_cases a
  · exact context_13_113868_428311
  · exact context_13_113869_428343
  · exact context_13_113870_428361
  · exact context_13_113871_428368

theorem unmarked_context_11_7116_428370 : frontier 10 ⟨428370, by decide⟩
    (prefixCache 11 7116) (prefixPartial 11 7116) = false := by
  decide +kernel

theorem node_context_11_7116_428370 : EJMOriginalGlobalDAGData.nodes 10 ⟨428370, by decide⟩ =
    .split (coordinate 11) (![⟨428164, by decide⟩,⟨428233, by decide⟩,⟨428304, by decide⟩,⟨428369, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_7116_428370 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7116 ⟨428370, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 7116
    ⟨428370, by decide⟩ (by decide) (![⟨428164, by decide⟩,⟨428233, by decide⟩,⟨428304, by decide⟩,⟨428369, by decide⟩]) unmarked_context_11_7116_428370 node_context_11_7116_428370
  intro a
  fin_cases a
  · exact context_12_28464_428164
  · exact context_12_28465_428233
  · exact context_12_28466_428304
  · exact context_12_28467_428369

theorem selected_cut_16834 : selected 8 ⟨428375, by decide⟩
    (prefixPartial 13 113872) = some ⟨13, 2, 0, 428375, 113872, 401, 16384⟩ := by
  decide +kernel

theorem context_13_113872_428375 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113872 ⟨428375, by decide⟩ :=
  accepted_of_selected 13 113872 ⟨428375, by decide⟩ ⟨13, 2, 0, 428375, 113872, 401, 16384⟩
    (by decide) selected_cut_16834

theorem selected_cut_16835 : selected 8 ⟨428412, by decide⟩
    (prefixPartial 13 113873) = some ⟨13, 2, 0, 428412, 113873, 2633, 16384⟩ := by
  decide +kernel

theorem context_13_113873_428412 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113873 ⟨428412, by decide⟩ :=
  accepted_of_selected 13 113873 ⟨428412, by decide⟩ ⟨13, 2, 0, 428412, 113873, 2633, 16384⟩
    (by decide) selected_cut_16835

theorem selected_cut_16836 : selected 8 ⟨428438, by decide⟩
    (prefixPartial 13 113874) = some ⟨13, 2, 0, 428438, 113874, 1629, 16384⟩ := by
  decide +kernel

theorem context_13_113874_428438 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113874 ⟨428438, by decide⟩ :=
  accepted_of_selected 13 113874 ⟨428438, by decide⟩ ⟨13, 2, 0, 428438, 113874, 1629, 16384⟩
    (by decide) selected_cut_16836

theorem selected_cut_16837 : selected 8 ⟨428449, by decide⟩
    (prefixPartial 13 113875) = some ⟨13, 2, 0, 428449, 113875, 829, 16384⟩ := by
  decide +kernel

theorem context_13_113875_428449 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113875 ⟨428449, by decide⟩ :=
  accepted_of_selected 13 113875 ⟨428449, by decide⟩ ⟨13, 2, 0, 428449, 113875, 829, 16384⟩
    (by decide) selected_cut_16837

theorem unmarked_context_12_28468_428450 : frontier 9 ⟨428450, by decide⟩
    (prefixCache 12 28468) (prefixPartial 12 28468) = false := by
  decide +kernel

theorem node_context_12_28468_428450 : EJMOriginalGlobalDAGData.nodes 9 ⟨428450, by decide⟩ =
    .split (coordinate 12) (![⟨428375, by decide⟩,⟨428412, by decide⟩,⟨428438, by decide⟩,⟨428449, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28468_428450 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28468 ⟨428450, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28468
    ⟨428450, by decide⟩ (by decide) (![⟨428375, by decide⟩,⟨428412, by decide⟩,⟨428438, by decide⟩,⟨428449, by decide⟩]) unmarked_context_12_28468_428450 node_context_12_28468_428450
  intro a
  fin_cases a
  · exact context_13_113872_428375
  · exact context_13_113873_428412
  · exact context_13_113874_428438
  · exact context_13_113875_428449

theorem selected_cut_16838 : selected 8 ⟨428455, by decide⟩
    (prefixPartial 13 113876) = some ⟨13, 2, 0, 428455, 113876, 349, 16384⟩ := by
  decide +kernel

theorem context_13_113876_428455 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113876 ⟨428455, by decide⟩ :=
  accepted_of_selected 13 113876 ⟨428455, by decide⟩ ⟨13, 2, 0, 428455, 113876, 349, 16384⟩
    (by decide) selected_cut_16838

theorem selected_cut_16839 : selected 8 ⟨428485, by decide⟩
    (prefixPartial 13 113877) = some ⟨13, 2, 0, 428485, 113877, 2425, 16384⟩ := by
  decide +kernel

theorem context_13_113877_428485 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113877 ⟨428485, by decide⟩ :=
  accepted_of_selected 13 113877 ⟨428485, by decide⟩ ⟨13, 2, 0, 428485, 113877, 2425, 16384⟩
    (by decide) selected_cut_16839

theorem selected_cut_16840 : selected 8 ⟨428505, by decide⟩
    (prefixPartial 13 113878) = some ⟨13, 2, 0, 428505, 113878, 1633, 16384⟩ := by
  decide +kernel

theorem context_13_113878_428505 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113878 ⟨428505, by decide⟩ :=
  accepted_of_selected 13 113878 ⟨428505, by decide⟩ ⟨13, 2, 0, 428505, 113878, 1633, 16384⟩
    (by decide) selected_cut_16840

theorem selected_cut_16841 : selected 8 ⟨428513, by decide⟩
    (prefixPartial 13 113879) = some ⟨13, 2, 0, 428513, 113879, 797, 16384⟩ := by
  decide +kernel

theorem context_13_113879_428513 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113879 ⟨428513, by decide⟩ :=
  accepted_of_selected 13 113879 ⟨428513, by decide⟩ ⟨13, 2, 0, 428513, 113879, 797, 16384⟩
    (by decide) selected_cut_16841

theorem unmarked_context_12_28469_428514 : frontier 9 ⟨428514, by decide⟩
    (prefixCache 12 28469) (prefixPartial 12 28469) = false := by
  decide +kernel

theorem node_context_12_28469_428514 : EJMOriginalGlobalDAGData.nodes 9 ⟨428514, by decide⟩ =
    .split (coordinate 12) (![⟨428455, by decide⟩,⟨428485, by decide⟩,⟨428505, by decide⟩,⟨428513, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28469_428514 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28469 ⟨428514, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28469
    ⟨428514, by decide⟩ (by decide) (![⟨428455, by decide⟩,⟨428485, by decide⟩,⟨428505, by decide⟩,⟨428513, by decide⟩]) unmarked_context_12_28469_428514 node_context_12_28469_428514
  intro a
  fin_cases a
  · exact context_13_113876_428455
  · exact context_13_113877_428485
  · exact context_13_113878_428505
  · exact context_13_113879_428513

theorem selected_cut_16842 : selected 8 ⟨428519, by decide⟩
    (prefixPartial 13 113880) = some ⟨13, 2, 0, 428519, 113880, 401, 16384⟩ := by
  decide +kernel

theorem context_13_113880_428519 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113880 ⟨428519, by decide⟩ :=
  accepted_of_selected 13 113880 ⟨428519, by decide⟩ ⟨13, 2, 0, 428519, 113880, 401, 16384⟩
    (by decide) selected_cut_16842

theorem selected_cut_16843 : selected 8 ⟨428547, by decide⟩
    (prefixPartial 13 113881) = some ⟨13, 2, 0, 428547, 113881, 2381, 16384⟩ := by
  decide +kernel

theorem context_13_113881_428547 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113881 ⟨428547, by decide⟩ :=
  accepted_of_selected 13 113881 ⟨428547, by decide⟩ ⟨13, 2, 0, 428547, 113881, 2381, 16384⟩
    (by decide) selected_cut_16843

theorem selected_cut_16844 : selected 8 ⟨428572, by decide⟩
    (prefixPartial 13 113882) = some ⟨13, 2, 0, 428572, 113882, 1713, 16384⟩ := by
  decide +kernel

theorem context_13_113882_428572 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113882 ⟨428572, by decide⟩ :=
  accepted_of_selected 13 113882 ⟨428572, by decide⟩ ⟨13, 2, 0, 428572, 113882, 1713, 16384⟩
    (by decide) selected_cut_16844

theorem selected_cut_16845 : selected 8 ⟨428581, by decide⟩
    (prefixPartial 13 113883) = some ⟨13, 2, 0, 428581, 113883, 893, 16384⟩ := by
  decide +kernel

theorem context_13_113883_428581 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113883 ⟨428581, by decide⟩ :=
  accepted_of_selected 13 113883 ⟨428581, by decide⟩ ⟨13, 2, 0, 428581, 113883, 893, 16384⟩
    (by decide) selected_cut_16845

theorem unmarked_context_12_28470_428582 : frontier 9 ⟨428582, by decide⟩
    (prefixCache 12 28470) (prefixPartial 12 28470) = false := by
  decide +kernel

theorem node_context_12_28470_428582 : EJMOriginalGlobalDAGData.nodes 9 ⟨428582, by decide⟩ =
    .split (coordinate 12) (![⟨428519, by decide⟩,⟨428547, by decide⟩,⟨428572, by decide⟩,⟨428581, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28470_428582 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28470 ⟨428582, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28470
    ⟨428582, by decide⟩ (by decide) (![⟨428519, by decide⟩,⟨428547, by decide⟩,⟨428572, by decide⟩,⟨428581, by decide⟩]) unmarked_context_12_28470_428582 node_context_12_28470_428582
  intro a
  fin_cases a
  · exact context_13_113880_428519
  · exact context_13_113881_428547
  · exact context_13_113882_428572
  · exact context_13_113883_428581

theorem selected_cut_16846 : selected 8 ⟨428587, by decide⟩
    (prefixPartial 13 113884) = some ⟨13, 2, 0, 428587, 113884, 361, 16384⟩ := by
  decide +kernel

theorem context_13_113884_428587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113884 ⟨428587, by decide⟩ :=
  accepted_of_selected 13 113884 ⟨428587, by decide⟩ ⟨13, 2, 0, 428587, 113884, 361, 16384⟩
    (by decide) selected_cut_16846

theorem selected_cut_16847 : selected 8 ⟨428622, by decide⟩
    (prefixPartial 13 113885) = some ⟨13, 2, 0, 428622, 113885, 2505, 16384⟩ := by
  decide +kernel

theorem context_13_113885_428622 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113885 ⟨428622, by decide⟩ :=
  accepted_of_selected 13 113885 ⟨428622, by decide⟩ ⟨13, 2, 0, 428622, 113885, 2505, 16384⟩
    (by decide) selected_cut_16847

theorem selected_cut_16848 : selected 8 ⟨428644, by decide⟩
    (prefixPartial 13 113886) = some ⟨13, 2, 0, 428644, 113886, 1793, 16384⟩ := by
  decide +kernel

theorem context_13_113886_428644 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113886 ⟨428644, by decide⟩ :=
  accepted_of_selected 13 113886 ⟨428644, by decide⟩ ⟨13, 2, 0, 428644, 113886, 1793, 16384⟩
    (by decide) selected_cut_16848

theorem selected_cut_16849 : selected 8 ⟨428653, by decide⟩
    (prefixPartial 13 113887) = some ⟨13, 2, 0, 428653, 113887, 841, 16384⟩ := by
  decide +kernel

theorem context_13_113887_428653 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113887 ⟨428653, by decide⟩ :=
  accepted_of_selected 13 113887 ⟨428653, by decide⟩ ⟨13, 2, 0, 428653, 113887, 841, 16384⟩
    (by decide) selected_cut_16849

theorem unmarked_context_12_28471_428654 : frontier 9 ⟨428654, by decide⟩
    (prefixCache 12 28471) (prefixPartial 12 28471) = false := by
  decide +kernel

theorem node_context_12_28471_428654 : EJMOriginalGlobalDAGData.nodes 9 ⟨428654, by decide⟩ =
    .split (coordinate 12) (![⟨428587, by decide⟩,⟨428622, by decide⟩,⟨428644, by decide⟩,⟨428653, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28471_428654 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28471 ⟨428654, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28471
    ⟨428654, by decide⟩ (by decide) (![⟨428587, by decide⟩,⟨428622, by decide⟩,⟨428644, by decide⟩,⟨428653, by decide⟩]) unmarked_context_12_28471_428654 node_context_12_28471_428654
  intro a
  fin_cases a
  · exact context_13_113884_428587
  · exact context_13_113885_428622
  · exact context_13_113886_428644
  · exact context_13_113887_428653

theorem unmarked_context_11_7117_428655 : frontier 10 ⟨428655, by decide⟩
    (prefixCache 11 7117) (prefixPartial 11 7117) = false := by
  decide +kernel

theorem node_context_11_7117_428655 : EJMOriginalGlobalDAGData.nodes 10 ⟨428655, by decide⟩ =
    .split (coordinate 11) (![⟨428450, by decide⟩,⟨428514, by decide⟩,⟨428582, by decide⟩,⟨428654, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_7117_428655 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7117 ⟨428655, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 7117
    ⟨428655, by decide⟩ (by decide) (![⟨428450, by decide⟩,⟨428514, by decide⟩,⟨428582, by decide⟩,⟨428654, by decide⟩]) unmarked_context_11_7117_428655 node_context_11_7117_428655
  intro a
  fin_cases a
  · exact context_12_28468_428450
  · exact context_12_28469_428514
  · exact context_12_28470_428582
  · exact context_12_28471_428654

theorem selected_cut_16850 : selected 8 ⟨428660, by decide⟩
    (prefixPartial 13 113888) = some ⟨13, 2, 0, 428660, 113888, 297, 16384⟩ := by
  decide +kernel

theorem context_13_113888_428660 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113888 ⟨428660, by decide⟩ :=
  accepted_of_selected 13 113888 ⟨428660, by decide⟩ ⟨13, 2, 0, 428660, 113888, 297, 16384⟩
    (by decide) selected_cut_16850

theorem selected_cut_16851 : selected 8 ⟨428705, by decide⟩
    (prefixPartial 13 113889) = some ⟨13, 2, 0, 428705, 113889, 2993, 16384⟩ := by
  decide +kernel

theorem context_13_113889_428705 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113889 ⟨428705, by decide⟩ :=
  accepted_of_selected 13 113889 ⟨428705, by decide⟩ ⟨13, 2, 0, 428705, 113889, 2993, 16384⟩
    (by decide) selected_cut_16851

theorem selected_cut_16852 : selected 8 ⟨428732, by decide⟩
    (prefixPartial 13 113890) = some ⟨13, 2, 0, 428732, 113890, 1737, 16384⟩ := by
  decide +kernel

theorem context_13_113890_428732 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113890 ⟨428732, by decide⟩ :=
  accepted_of_selected 13 113890 ⟨428732, by decide⟩ ⟨13, 2, 0, 428732, 113890, 1737, 16384⟩
    (by decide) selected_cut_16852

theorem selected_cut_16853 : selected 8 ⟨428739, by decide⟩
    (prefixPartial 13 113891) = some ⟨13, 2, 0, 428739, 113891, 749, 16384⟩ := by
  decide +kernel

theorem context_13_113891_428739 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113891 ⟨428739, by decide⟩ :=
  accepted_of_selected 13 113891 ⟨428739, by decide⟩ ⟨13, 2, 0, 428739, 113891, 749, 16384⟩
    (by decide) selected_cut_16853

theorem unmarked_context_12_28472_428740 : frontier 9 ⟨428740, by decide⟩
    (prefixCache 12 28472) (prefixPartial 12 28472) = false := by
  decide +kernel

theorem node_context_12_28472_428740 : EJMOriginalGlobalDAGData.nodes 9 ⟨428740, by decide⟩ =
    .split (coordinate 12) (![⟨428660, by decide⟩,⟨428705, by decide⟩,⟨428732, by decide⟩,⟨428739, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28472_428740 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28472 ⟨428740, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28472
    ⟨428740, by decide⟩ (by decide) (![⟨428660, by decide⟩,⟨428705, by decide⟩,⟨428732, by decide⟩,⟨428739, by decide⟩]) unmarked_context_12_28472_428740 node_context_12_28472_428740
  intro a
  fin_cases a
  · exact context_13_113888_428660
  · exact context_13_113889_428705
  · exact context_13_113890_428732
  · exact context_13_113891_428739

theorem selected_cut_16854 : selected 8 ⟨428748, by decide⟩
    (prefixPartial 13 113892) = some ⟨13, 2, 0, 428748, 113892, 325, 16384⟩ := by
  decide +kernel

theorem context_13_113892_428748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113892 ⟨428748, by decide⟩ :=
  accepted_of_selected 13 113892 ⟨428748, by decide⟩ ⟨13, 2, 0, 428748, 113892, 325, 16384⟩
    (by decide) selected_cut_16854

theorem selected_cut_16855 : selected 8 ⟨428790, by decide⟩
    (prefixPartial 13 113893) = some ⟨13, 2, 0, 428790, 113893, 2969, 16384⟩ := by
  decide +kernel

theorem context_13_113893_428790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113893 ⟨428790, by decide⟩ :=
  accepted_of_selected 13 113893 ⟨428790, by decide⟩ ⟨13, 2, 0, 428790, 113893, 2969, 16384⟩
    (by decide) selected_cut_16855

theorem selected_cut_16856 : selected 8 ⟨428812, by decide⟩
    (prefixPartial 13 113894) = some ⟨13, 2, 0, 428812, 113894, 1621, 16384⟩ := by
  decide +kernel

theorem context_13_113894_428812 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113894 ⟨428812, by decide⟩ :=
  accepted_of_selected 13 113894 ⟨428812, by decide⟩ ⟨13, 2, 0, 428812, 113894, 1621, 16384⟩
    (by decide) selected_cut_16856

theorem selected_cut_16857 : selected 8 ⟨428822, by decide⟩
    (prefixPartial 13 113895) = some ⟨13, 2, 0, 428822, 113895, 841, 16384⟩ := by
  decide +kernel

theorem context_13_113895_428822 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113895 ⟨428822, by decide⟩ :=
  accepted_of_selected 13 113895 ⟨428822, by decide⟩ ⟨13, 2, 0, 428822, 113895, 841, 16384⟩
    (by decide) selected_cut_16857

theorem unmarked_context_12_28473_428823 : frontier 9 ⟨428823, by decide⟩
    (prefixCache 12 28473) (prefixPartial 12 28473) = false := by
  decide +kernel

theorem node_context_12_28473_428823 : EJMOriginalGlobalDAGData.nodes 9 ⟨428823, by decide⟩ =
    .split (coordinate 12) (![⟨428748, by decide⟩,⟨428790, by decide⟩,⟨428812, by decide⟩,⟨428822, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28473_428823 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28473 ⟨428823, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28473
    ⟨428823, by decide⟩ (by decide) (![⟨428748, by decide⟩,⟨428790, by decide⟩,⟨428812, by decide⟩,⟨428822, by decide⟩]) unmarked_context_12_28473_428823 node_context_12_28473_428823
  intro a
  fin_cases a
  · exact context_13_113892_428748
  · exact context_13_113893_428790
  · exact context_13_113894_428812
  · exact context_13_113895_428822

theorem selected_cut_16858 : selected 8 ⟨428828, by decide⟩
    (prefixPartial 13 113896) = some ⟨13, 2, 0, 428828, 113896, 253, 16384⟩ := by
  decide +kernel

theorem context_13_113896_428828 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113896 ⟨428828, by decide⟩ :=
  accepted_of_selected 13 113896 ⟨428828, by decide⟩ ⟨13, 2, 0, 428828, 113896, 253, 16384⟩
    (by decide) selected_cut_16858

theorem selected_cut_16859 : selected 8 ⟨428864, by decide⟩
    (prefixPartial 13 113897) = some ⟨13, 2, 0, 428864, 113897, 2765, 16384⟩ := by
  decide +kernel

theorem context_13_113897_428864 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113897 ⟨428864, by decide⟩ :=
  accepted_of_selected 13 113897 ⟨428864, by decide⟩ ⟨13, 2, 0, 428864, 113897, 2765, 16384⟩
    (by decide) selected_cut_16859

theorem selected_cut_16860 : selected 8 ⟨428886, by decide⟩
    (prefixPartial 13 113898) = some ⟨13, 2, 0, 428886, 113898, 1705, 16384⟩ := by
  decide +kernel

theorem context_13_113898_428886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113898 ⟨428886, by decide⟩ :=
  accepted_of_selected 13 113898 ⟨428886, by decide⟩ ⟨13, 2, 0, 428886, 113898, 1705, 16384⟩
    (by decide) selected_cut_16860

theorem selected_cut_16861 : selected 8 ⟨428893, by decide⟩
    (prefixPartial 13 113899) = some ⟨13, 2, 0, 428893, 113899, 793, 16384⟩ := by
  decide +kernel

theorem context_13_113899_428893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113899 ⟨428893, by decide⟩ :=
  accepted_of_selected 13 113899 ⟨428893, by decide⟩ ⟨13, 2, 0, 428893, 113899, 793, 16384⟩
    (by decide) selected_cut_16861

theorem unmarked_context_12_28474_428894 : frontier 9 ⟨428894, by decide⟩
    (prefixCache 12 28474) (prefixPartial 12 28474) = false := by
  decide +kernel

theorem node_context_12_28474_428894 : EJMOriginalGlobalDAGData.nodes 9 ⟨428894, by decide⟩ =
    .split (coordinate 12) (![⟨428828, by decide⟩,⟨428864, by decide⟩,⟨428886, by decide⟩,⟨428893, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28474_428894 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28474 ⟨428894, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28474
    ⟨428894, by decide⟩ (by decide) (![⟨428828, by decide⟩,⟨428864, by decide⟩,⟨428886, by decide⟩,⟨428893, by decide⟩]) unmarked_context_12_28474_428894 node_context_12_28474_428894
  intro a
  fin_cases a
  · exact context_13_113896_428828
  · exact context_13_113897_428864
  · exact context_13_113898_428886
  · exact context_13_113899_428893

theorem selected_cut_16862 : selected 8 ⟨428902, by decide⟩
    (prefixPartial 13 113900) = some ⟨13, 2, 0, 428902, 113900, 261, 16384⟩ := by
  decide +kernel

theorem context_13_113900_428902 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113900 ⟨428902, by decide⟩ :=
  accepted_of_selected 13 113900 ⟨428902, by decide⟩ ⟨13, 2, 0, 428902, 113900, 261, 16384⟩
    (by decide) selected_cut_16862

theorem selected_cut_16863 : selected 8 ⟨428955, by decide⟩
    (prefixPartial 13 113901) = some ⟨13, 2, 0, 428955, 113901, 3005, 16384⟩ := by
  decide +kernel

theorem context_13_113901_428955 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113901 ⟨428955, by decide⟩ :=
  accepted_of_selected 13 113901 ⟨428955, by decide⟩ ⟨13, 2, 0, 428955, 113901, 3005, 16384⟩
    (by decide) selected_cut_16863

theorem selected_cut_16864 : selected 8 ⟨428977, by decide⟩
    (prefixPartial 13 113902) = some ⟨13, 2, 0, 428977, 113902, 1613, 16384⟩ := by
  decide +kernel

theorem context_13_113902_428977 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113902 ⟨428977, by decide⟩ :=
  accepted_of_selected 13 113902 ⟨428977, by decide⟩ ⟨13, 2, 0, 428977, 113902, 1613, 16384⟩
    (by decide) selected_cut_16864

theorem selected_cut_16865 : selected 8 ⟨428984, by decide⟩
    (prefixPartial 13 113903) = some ⟨13, 2, 0, 428984, 113903, 709, 16384⟩ := by
  decide +kernel

theorem context_13_113903_428984 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113903 ⟨428984, by decide⟩ :=
  accepted_of_selected 13 113903 ⟨428984, by decide⟩ ⟨13, 2, 0, 428984, 113903, 709, 16384⟩
    (by decide) selected_cut_16865

theorem unmarked_context_12_28475_428985 : frontier 9 ⟨428985, by decide⟩
    (prefixCache 12 28475) (prefixPartial 12 28475) = false := by
  decide +kernel

theorem node_context_12_28475_428985 : EJMOriginalGlobalDAGData.nodes 9 ⟨428985, by decide⟩ =
    .split (coordinate 12) (![⟨428902, by decide⟩,⟨428955, by decide⟩,⟨428977, by decide⟩,⟨428984, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28475_428985 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28475 ⟨428985, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28475
    ⟨428985, by decide⟩ (by decide) (![⟨428902, by decide⟩,⟨428955, by decide⟩,⟨428977, by decide⟩,⟨428984, by decide⟩]) unmarked_context_12_28475_428985 node_context_12_28475_428985
  intro a
  fin_cases a
  · exact context_13_113900_428902
  · exact context_13_113901_428955
  · exact context_13_113902_428977
  · exact context_13_113903_428984

theorem unmarked_context_11_7118_428986 : frontier 10 ⟨428986, by decide⟩
    (prefixCache 11 7118) (prefixPartial 11 7118) = false := by
  decide +kernel

theorem node_context_11_7118_428986 : EJMOriginalGlobalDAGData.nodes 10 ⟨428986, by decide⟩ =
    .split (coordinate 11) (![⟨428740, by decide⟩,⟨428823, by decide⟩,⟨428894, by decide⟩,⟨428985, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_7118_428986 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7118 ⟨428986, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 7118
    ⟨428986, by decide⟩ (by decide) (![⟨428740, by decide⟩,⟨428823, by decide⟩,⟨428894, by decide⟩,⟨428985, by decide⟩]) unmarked_context_11_7118_428986 node_context_11_7118_428986
  intro a
  fin_cases a
  · exact context_12_28472_428740
  · exact context_12_28473_428823
  · exact context_12_28474_428894
  · exact context_12_28475_428985

theorem selected_cut_16866 : selected 8 ⟨428990, by decide⟩
    (prefixPartial 13 113904) = some ⟨13, 2, 0, 428990, 113904, 213, 16384⟩ := by
  decide +kernel

theorem context_13_113904_428990 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113904 ⟨428990, by decide⟩ :=
  accepted_of_selected 13 113904 ⟨428990, by decide⟩ ⟨13, 2, 0, 428990, 113904, 213, 16384⟩
    (by decide) selected_cut_16866

theorem selected_cut_16867 : selected 8 ⟨429039, by decide⟩
    (prefixPartial 13 113905) = some ⟨13, 2, 0, 429039, 113905, 3221, 16384⟩ := by
  decide +kernel

theorem context_13_113905_429039 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113905 ⟨429039, by decide⟩ :=
  accepted_of_selected 13 113905 ⟨429039, by decide⟩ ⟨13, 2, 0, 429039, 113905, 3221, 16384⟩
    (by decide) selected_cut_16867

theorem selected_cut_16868 : selected 8 ⟨429061, by decide⟩
    (prefixPartial 13 113906) = some ⟨13, 2, 0, 429061, 113906, 1765, 16384⟩ := by
  decide +kernel

theorem context_13_113906_429061 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113906 ⟨429061, by decide⟩ :=
  accepted_of_selected 13 113906 ⟨429061, by decide⟩ ⟨13, 2, 0, 429061, 113906, 1765, 16384⟩
    (by decide) selected_cut_16868

theorem selected_cut_16869 : selected 8 ⟨429076, by decide⟩
    (prefixPartial 13 113907) = some ⟨13, 2, 0, 429076, 113907, 937, 16384⟩ := by
  decide +kernel

theorem context_13_113907_429076 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113907 ⟨429076, by decide⟩ :=
  accepted_of_selected 13 113907 ⟨429076, by decide⟩ ⟨13, 2, 0, 429076, 113907, 937, 16384⟩
    (by decide) selected_cut_16869

theorem unmarked_context_12_28476_429077 : frontier 9 ⟨429077, by decide⟩
    (prefixCache 12 28476) (prefixPartial 12 28476) = false := by
  decide +kernel

theorem node_context_12_28476_429077 : EJMOriginalGlobalDAGData.nodes 9 ⟨429077, by decide⟩ =
    .split (coordinate 12) (![⟨428990, by decide⟩,⟨429039, by decide⟩,⟨429061, by decide⟩,⟨429076, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28476_429077 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28476 ⟨429077, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28476
    ⟨429077, by decide⟩ (by decide) (![⟨428990, by decide⟩,⟨429039, by decide⟩,⟨429061, by decide⟩,⟨429076, by decide⟩]) unmarked_context_12_28476_429077 node_context_12_28476_429077
  intro a
  fin_cases a
  · exact context_13_113904_428990
  · exact context_13_113905_429039
  · exact context_13_113906_429061
  · exact context_13_113907_429076

theorem selected_cut_16870 : selected 8 ⟨429082, by decide⟩
    (prefixPartial 13 113908) = some ⟨13, 2, 0, 429082, 113908, 177, 16384⟩ := by
  decide +kernel

theorem context_13_113908_429082 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113908 ⟨429082, by decide⟩ :=
  accepted_of_selected 13 113908 ⟨429082, by decide⟩ ⟨13, 2, 0, 429082, 113908, 177, 16384⟩
    (by decide) selected_cut_16870

theorem selected_cut_16871 : selected 8 ⟨429144, by decide⟩
    (prefixPartial 13 113909) = some ⟨13, 2, 0, 429144, 113909, 3413, 16384⟩ := by
  decide +kernel

theorem context_13_113909_429144 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113909 ⟨429144, by decide⟩ :=
  accepted_of_selected 13 113909 ⟨429144, by decide⟩ ⟨13, 2, 0, 429144, 113909, 3413, 16384⟩
    (by decide) selected_cut_16871

theorem selected_cut_16872 : selected 8 ⟨429165, by decide⟩
    (prefixPartial 13 113910) = some ⟨13, 2, 0, 429165, 113910, 2025, 16384⟩ := by
  decide +kernel

theorem context_13_113910_429165 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113910 ⟨429165, by decide⟩ :=
  accepted_of_selected 13 113910 ⟨429165, by decide⟩ ⟨13, 2, 0, 429165, 113910, 2025, 16384⟩
    (by decide) selected_cut_16872

theorem selected_cut_16873 : selected 8 ⟨429175, by decide⟩
    (prefixPartial 13 113911) = some ⟨13, 2, 0, 429175, 113911, 953, 16384⟩ := by
  decide +kernel

theorem context_13_113911_429175 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113911 ⟨429175, by decide⟩ :=
  accepted_of_selected 13 113911 ⟨429175, by decide⟩ ⟨13, 2, 0, 429175, 113911, 953, 16384⟩
    (by decide) selected_cut_16873

theorem unmarked_context_12_28477_429176 : frontier 9 ⟨429176, by decide⟩
    (prefixCache 12 28477) (prefixPartial 12 28477) = false := by
  decide +kernel

theorem node_context_12_28477_429176 : EJMOriginalGlobalDAGData.nodes 9 ⟨429176, by decide⟩ =
    .split (coordinate 12) (![⟨429082, by decide⟩,⟨429144, by decide⟩,⟨429165, by decide⟩,⟨429175, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28477_429176 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28477 ⟨429176, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28477
    ⟨429176, by decide⟩ (by decide) (![⟨429082, by decide⟩,⟨429144, by decide⟩,⟨429165, by decide⟩,⟨429175, by decide⟩]) unmarked_context_12_28477_429176 node_context_12_28477_429176
  intro a
  fin_cases a
  · exact context_13_113908_429082
  · exact context_13_113909_429144
  · exact context_13_113910_429165
  · exact context_13_113911_429175

theorem selected_cut_16874 : selected 8 ⟨429181, by decide⟩
    (prefixPartial 13 113912) = some ⟨13, 2, 0, 429181, 113912, 101, 16384⟩ := by
  decide +kernel

theorem context_13_113912_429181 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113912 ⟨429181, by decide⟩ :=
  accepted_of_selected 13 113912 ⟨429181, by decide⟩ ⟨13, 2, 0, 429181, 113912, 101, 16384⟩
    (by decide) selected_cut_16874

theorem selected_cut_16875 : selected 8 ⟨429248, by decide⟩
    (prefixPartial 13 113913) = some ⟨13, 2, 0, 429248, 113913, 3321, 16384⟩ := by
  decide +kernel

theorem context_13_113913_429248 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113913 ⟨429248, by decide⟩ :=
  accepted_of_selected 13 113913 ⟨429248, by decide⟩ ⟨13, 2, 0, 429248, 113913, 3321, 16384⟩
    (by decide) selected_cut_16875

theorem selected_cut_16876 : selected 8 ⟨429274, by decide⟩
    (prefixPartial 13 113914) = some ⟨13, 2, 0, 429274, 113914, 1905, 16384⟩ := by
  decide +kernel

theorem context_13_113914_429274 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113914 ⟨429274, by decide⟩ :=
  accepted_of_selected 13 113914 ⟨429274, by decide⟩ ⟨13, 2, 0, 429274, 113914, 1905, 16384⟩
    (by decide) selected_cut_16876

theorem selected_cut_16877 : selected 8 ⟨429283, by decide⟩
    (prefixPartial 13 113915) = some ⟨13, 2, 0, 429283, 113915, 933, 16384⟩ := by
  decide +kernel

theorem context_13_113915_429283 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113915 ⟨429283, by decide⟩ :=
  accepted_of_selected 13 113915 ⟨429283, by decide⟩ ⟨13, 2, 0, 429283, 113915, 933, 16384⟩
    (by decide) selected_cut_16877

theorem unmarked_context_12_28478_429284 : frontier 9 ⟨429284, by decide⟩
    (prefixCache 12 28478) (prefixPartial 12 28478) = false := by
  decide +kernel

theorem node_context_12_28478_429284 : EJMOriginalGlobalDAGData.nodes 9 ⟨429284, by decide⟩ =
    .split (coordinate 12) (![⟨429181, by decide⟩,⟨429248, by decide⟩,⟨429274, by decide⟩,⟨429283, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28478_429284 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28478 ⟨429284, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28478
    ⟨429284, by decide⟩ (by decide) (![⟨429181, by decide⟩,⟨429248, by decide⟩,⟨429274, by decide⟩,⟨429283, by decide⟩]) unmarked_context_12_28478_429284 node_context_12_28478_429284
  intro a
  fin_cases a
  · exact context_13_113912_429181
  · exact context_13_113913_429248
  · exact context_13_113914_429274
  · exact context_13_113915_429283

theorem selected_cut_16878 : selected 9 ⟨429285, by decide⟩
    (prefixPartial 12 28479) = some ⟨12, 1, 0, 429285, 28479, 1, 65536⟩ := by
  decide +kernel

theorem context_12_28479_429285 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28479 ⟨429285, by decide⟩ :=
  accepted_of_selected 12 28479 ⟨429285, by decide⟩ ⟨12, 1, 0, 429285, 28479, 1, 65536⟩
    (by decide) selected_cut_16878

theorem unmarked_context_11_7119_429286 : frontier 10 ⟨429286, by decide⟩
    (prefixCache 11 7119) (prefixPartial 11 7119) = false := by
  decide +kernel

theorem node_context_11_7119_429286 : EJMOriginalGlobalDAGData.nodes 10 ⟨429286, by decide⟩ =
    .split (coordinate 11) (![⟨429077, by decide⟩,⟨429176, by decide⟩,⟨429284, by decide⟩,⟨429285, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_7119_429286 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7119 ⟨429286, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 7119
    ⟨429286, by decide⟩ (by decide) (![⟨429077, by decide⟩,⟨429176, by decide⟩,⟨429284, by decide⟩,⟨429285, by decide⟩]) unmarked_context_11_7119_429286 node_context_11_7119_429286
  intro a
  fin_cases a
  · exact context_12_28476_429077
  · exact context_12_28477_429176
  · exact context_12_28478_429284
  · exact context_12_28479_429285

theorem unmarked_context_10_1779_429287 : frontier 11 ⟨429287, by decide⟩
    (prefixCache 10 1779) (prefixPartial 10 1779) = false := by
  decide +kernel

theorem node_context_10_1779_429287 : EJMOriginalGlobalDAGData.nodes 11 ⟨429287, by decide⟩ =
    .split (coordinate 10) (![⟨428370, by decide⟩,⟨428655, by decide⟩,⟨428986, by decide⟩,⟨429286, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1779_429287 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1779 ⟨429287, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1779
    ⟨429287, by decide⟩ (by decide) (![⟨428370, by decide⟩,⟨428655, by decide⟩,⟨428986, by decide⟩,⟨429286, by decide⟩]) unmarked_context_10_1779_429287 node_context_10_1779_429287
  intro a
  fin_cases a
  · exact context_11_7116_428370
  · exact context_11_7117_428655
  · exact context_11_7118_428986
  · exact context_11_7119_429286

theorem unmarked_context_9_444_429288 : frontier 12 ⟨429288, by decide⟩
    (prefixCache 9 444) (prefixPartial 9 444) = false := by
  decide +kernel

theorem node_context_9_444_429288 : EJMOriginalGlobalDAGData.nodes 12 ⟨429288, by decide⟩ =
    .split (coordinate 9) (![⟨424901, by decide⟩,⟨426721, by decide⟩,⟨428106, by decide⟩,⟨429287, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_444_429288 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 444 ⟨429288, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 444
    ⟨429288, by decide⟩ (by decide) (![⟨424901, by decide⟩,⟨426721, by decide⟩,⟨428106, by decide⟩,⟨429287, by decide⟩]) unmarked_context_9_444_429288 node_context_9_444_429288
  intro a
  fin_cases a
  · exact context_10_1776_424901
  · exact context_10_1777_426721
  · exact context_10_1778_428106
  · exact context_10_1779_429287

theorem selected_cut_16879 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 113920) = some ⟨13, 1, 0, 3444, 113920, 1, 16384⟩ := by
  decide +kernel

theorem context_13_113920_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113920 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 113920 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 113920, 1, 16384⟩
    (by decide) selected_cut_16879

theorem selected_cut_16880 : selected 8 ⟨429338, by decide⟩
    (prefixPartial 13 113921) = some ⟨13, 2, 0, 429338, 113921, 3381, 16384⟩ := by
  decide +kernel

theorem context_13_113921_429338 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113921 ⟨429338, by decide⟩ :=
  accepted_of_selected 13 113921 ⟨429338, by decide⟩ ⟨13, 2, 0, 429338, 113921, 3381, 16384⟩
    (by decide) selected_cut_16880

theorem selected_cut_16881 : selected 8 ⟨429368, by decide⟩
    (prefixPartial 13 113922) = some ⟨13, 2, 0, 429368, 113922, 1837, 16384⟩ := by
  decide +kernel

theorem context_13_113922_429368 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113922 ⟨429368, by decide⟩ :=
  accepted_of_selected 13 113922 ⟨429368, by decide⟩ ⟨13, 2, 0, 429368, 113922, 1837, 16384⟩
    (by decide) selected_cut_16881

theorem selected_cut_16882 : selected 8 ⟨429373, by decide⟩
    (prefixPartial 13 113923) = some ⟨13, 2, 0, 429373, 113923, 717, 16384⟩ := by
  decide +kernel

theorem context_13_113923_429373 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113923 ⟨429373, by decide⟩ :=
  accepted_of_selected 13 113923 ⟨429373, by decide⟩ ⟨13, 2, 0, 429373, 113923, 717, 16384⟩
    (by decide) selected_cut_16882

theorem unmarked_context_12_28480_429374 : frontier 9 ⟨429374, by decide⟩
    (prefixCache 12 28480) (prefixPartial 12 28480) = false := by
  decide +kernel

theorem node_context_12_28480_429374 : EJMOriginalGlobalDAGData.nodes 9 ⟨429374, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨429338, by decide⟩,⟨429368, by decide⟩,⟨429373, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28480_429374 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28480 ⟨429374, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28480
    ⟨429374, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨429338, by decide⟩,⟨429368, by decide⟩,⟨429373, by decide⟩]) unmarked_context_12_28480_429374 node_context_12_28480_429374
  intro a
  fin_cases a
  · exact context_13_113920_3444
  · exact context_13_113921_429338
  · exact context_13_113922_429368
  · exact context_13_113923_429373

theorem selected_cut_16883 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 113924) = some ⟨13, 1, 0, 3444, 113924, 1, 16384⟩ := by
  decide +kernel

theorem context_13_113924_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113924 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 113924 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 113924, 1, 16384⟩
    (by decide) selected_cut_16883

theorem selected_cut_16884 : selected 7 ⟨429404, by decide⟩
    (prefixPartial 14 455700) = some ⟨14, 2, 0, 429404, 455700, 1357, 4096⟩ := by
  decide +kernel

theorem context_14_455700_429404 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 455700 ⟨429404, by decide⟩ :=
  accepted_of_selected 14 455700 ⟨429404, by decide⟩ ⟨14, 2, 0, 429404, 455700, 1357, 4096⟩
    (by decide) selected_cut_16884

theorem selected_cut_16885 : selected 7 ⟨429428, by decide⟩
    (prefixPartial 14 455701) = some ⟨14, 2, 0, 429428, 455701, 929, 4096⟩ := by
  decide +kernel

theorem context_14_455701_429428 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 455701 ⟨429428, by decide⟩ :=
  accepted_of_selected 14 455701 ⟨429428, by decide⟩ ⟨14, 2, 0, 429428, 455701, 929, 4096⟩
    (by decide) selected_cut_16885

theorem selected_cut_16886 : selected 7 ⟨429456, by decide⟩
    (prefixPartial 14 455702) = some ⟨14, 2, 0, 429456, 455702, 1241, 4096⟩ := by
  decide +kernel

theorem context_14_455702_429456 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 455702 ⟨429456, by decide⟩ :=
  accepted_of_selected 14 455702 ⟨429456, by decide⟩ ⟨14, 2, 0, 429456, 455702, 1241, 4096⟩
    (by decide) selected_cut_16886

theorem selected_cut_16887 : selected 7 ⟨429486, by decide⟩
    (prefixPartial 14 455703) = some ⟨14, 2, 0, 429486, 455703, 1277, 4096⟩ := by
  decide +kernel

theorem context_14_455703_429486 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 455703 ⟨429486, by decide⟩ :=
  accepted_of_selected 14 455703 ⟨429486, by decide⟩ ⟨14, 2, 0, 429486, 455703, 1277, 4096⟩
    (by decide) selected_cut_16887

theorem unmarked_context_13_113925_429487 : frontier 8 ⟨429487, by decide⟩
    (prefixCache 13 113925) (prefixPartial 13 113925) = false := by
  decide +kernel

theorem node_context_13_113925_429487 : EJMOriginalGlobalDAGData.nodes 8 ⟨429487, by decide⟩ =
    .split (coordinate 13) (![⟨429404, by decide⟩,⟨429428, by decide⟩,⟨429456, by decide⟩,⟨429486, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_113925_429487 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113925 ⟨429487, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 113925
    ⟨429487, by decide⟩ (by decide) (![⟨429404, by decide⟩,⟨429428, by decide⟩,⟨429456, by decide⟩,⟨429486, by decide⟩]) unmarked_context_13_113925_429487 node_context_13_113925_429487
  intro a
  fin_cases a
  · exact context_14_455700_429404
  · exact context_14_455701_429428
  · exact context_14_455702_429456
  · exact context_14_455703_429486

theorem selected_cut_16888 : selected 8 ⟨429538, by decide⟩
    (prefixPartial 13 113926) = some ⟨13, 2, 0, 429538, 113926, 2609, 16384⟩ := by
  decide +kernel

theorem context_13_113926_429538 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113926 ⟨429538, by decide⟩ :=
  accepted_of_selected 13 113926 ⟨429538, by decide⟩ ⟨13, 2, 0, 429538, 113926, 2609, 16384⟩
    (by decide) selected_cut_16888

theorem selected_cut_16889 : selected 8 ⟨429546, by decide⟩
    (prefixPartial 13 113927) = some ⟨13, 2, 0, 429546, 113927, 749, 16384⟩ := by
  decide +kernel

theorem context_13_113927_429546 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113927 ⟨429546, by decide⟩ :=
  accepted_of_selected 13 113927 ⟨429546, by decide⟩ ⟨13, 2, 0, 429546, 113927, 749, 16384⟩
    (by decide) selected_cut_16889

theorem unmarked_context_12_28481_429547 : frontier 9 ⟨429547, by decide⟩
    (prefixCache 12 28481) (prefixPartial 12 28481) = false := by
  decide +kernel

theorem node_context_12_28481_429547 : EJMOriginalGlobalDAGData.nodes 9 ⟨429547, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨429487, by decide⟩,⟨429538, by decide⟩,⟨429546, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28481_429547 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28481 ⟨429547, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28481
    ⟨429547, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨429487, by decide⟩,⟨429538, by decide⟩,⟨429546, by decide⟩]) unmarked_context_12_28481_429547 node_context_12_28481_429547
  intro a
  fin_cases a
  · exact context_13_113924_3444
  · exact context_13_113925_429487
  · exact context_13_113926_429538
  · exact context_13_113927_429546

theorem selected_cut_16890 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 113928) = some ⟨13, 1, 0, 3444, 113928, 1, 16384⟩ := by
  decide +kernel

theorem context_13_113928_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113928 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 113928 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 113928, 1, 16384⟩
    (by decide) selected_cut_16890

theorem selected_cut_16891 : selected 8 ⟨429595, by decide⟩
    (prefixPartial 13 113929) = some ⟨13, 2, 0, 429595, 113929, 3173, 16384⟩ := by
  decide +kernel

theorem context_13_113929_429595 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113929 ⟨429595, by decide⟩ :=
  accepted_of_selected 13 113929 ⟨429595, by decide⟩ ⟨13, 2, 0, 429595, 113929, 3173, 16384⟩
    (by decide) selected_cut_16891

theorem selected_cut_16892 : selected 8 ⟨429615, by decide⟩
    (prefixPartial 13 113930) = some ⟨13, 2, 0, 429615, 113930, 1989, 16384⟩ := by
  decide +kernel

theorem context_13_113930_429615 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113930 ⟨429615, by decide⟩ :=
  accepted_of_selected 13 113930 ⟨429615, by decide⟩ ⟨13, 2, 0, 429615, 113930, 1989, 16384⟩
    (by decide) selected_cut_16892

theorem selected_cut_16893 : selected 8 ⟨429624, by decide⟩
    (prefixPartial 13 113931) = some ⟨13, 2, 0, 429624, 113931, 585, 16384⟩ := by
  decide +kernel

theorem context_13_113931_429624 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113931 ⟨429624, by decide⟩ :=
  accepted_of_selected 13 113931 ⟨429624, by decide⟩ ⟨13, 2, 0, 429624, 113931, 585, 16384⟩
    (by decide) selected_cut_16893

theorem unmarked_context_12_28482_429625 : frontier 9 ⟨429625, by decide⟩
    (prefixCache 12 28482) (prefixPartial 12 28482) = false := by
  decide +kernel

theorem node_context_12_28482_429625 : EJMOriginalGlobalDAGData.nodes 9 ⟨429625, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨429595, by decide⟩,⟨429615, by decide⟩,⟨429624, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28482_429625 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28482 ⟨429625, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28482
    ⟨429625, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨429595, by decide⟩,⟨429615, by decide⟩,⟨429624, by decide⟩]) unmarked_context_12_28482_429625 node_context_12_28482_429625
  intro a
  fin_cases a
  · exact context_13_113928_3444
  · exact context_13_113929_429595
  · exact context_13_113930_429615
  · exact context_13_113931_429624

theorem selected_cut_16894 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 113932) = some ⟨13, 1, 0, 3444, 113932, 1, 16384⟩ := by
  decide +kernel

theorem context_13_113932_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113932 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 113932 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 113932, 1, 16384⟩
    (by decide) selected_cut_16894

theorem selected_cut_16895 : selected 8 ⟨429679, by decide⟩
    (prefixPartial 13 113933) = some ⟨13, 2, 0, 429679, 113933, 3333, 16384⟩ := by
  decide +kernel

theorem context_13_113933_429679 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113933 ⟨429679, by decide⟩ :=
  accepted_of_selected 13 113933 ⟨429679, by decide⟩ ⟨13, 2, 0, 429679, 113933, 3333, 16384⟩
    (by decide) selected_cut_16895

theorem selected_cut_16896 : selected 8 ⟨429706, by decide⟩
    (prefixPartial 13 113934) = some ⟨13, 2, 0, 429706, 113934, 1813, 16384⟩ := by
  decide +kernel

theorem context_13_113934_429706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113934 ⟨429706, by decide⟩ :=
  accepted_of_selected 13 113934 ⟨429706, by decide⟩ ⟨13, 2, 0, 429706, 113934, 1813, 16384⟩
    (by decide) selected_cut_16896

theorem selected_cut_16897 : selected 8 ⟨429714, by decide⟩
    (prefixPartial 13 113935) = some ⟨13, 2, 0, 429714, 113935, 721, 16384⟩ := by
  decide +kernel

theorem context_13_113935_429714 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113935 ⟨429714, by decide⟩ :=
  accepted_of_selected 13 113935 ⟨429714, by decide⟩ ⟨13, 2, 0, 429714, 113935, 721, 16384⟩
    (by decide) selected_cut_16897

theorem unmarked_context_12_28483_429715 : frontier 9 ⟨429715, by decide⟩
    (prefixCache 12 28483) (prefixPartial 12 28483) = false := by
  decide +kernel

theorem node_context_12_28483_429715 : EJMOriginalGlobalDAGData.nodes 9 ⟨429715, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨429679, by decide⟩,⟨429706, by decide⟩,⟨429714, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28483_429715 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28483 ⟨429715, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28483
    ⟨429715, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨429679, by decide⟩,⟨429706, by decide⟩,⟨429714, by decide⟩]) unmarked_context_12_28483_429715 node_context_12_28483_429715
  intro a
  fin_cases a
  · exact context_13_113932_3444
  · exact context_13_113933_429679
  · exact context_13_113934_429706
  · exact context_13_113935_429714

theorem unmarked_context_11_7120_429716 : frontier 10 ⟨429716, by decide⟩
    (prefixCache 11 7120) (prefixPartial 11 7120) = false := by
  decide +kernel

theorem node_context_11_7120_429716 : EJMOriginalGlobalDAGData.nodes 10 ⟨429716, by decide⟩ =
    .split (coordinate 11) (![⟨429374, by decide⟩,⟨429547, by decide⟩,⟨429625, by decide⟩,⟨429715, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_7120_429716 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7120 ⟨429716, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 7120
    ⟨429716, by decide⟩ (by decide) (![⟨429374, by decide⟩,⟨429547, by decide⟩,⟨429625, by decide⟩,⟨429715, by decide⟩]) unmarked_context_11_7120_429716 node_context_11_7120_429716
  intro a
  fin_cases a
  · exact context_12_28480_429374
  · exact context_12_28481_429547
  · exact context_12_28482_429625
  · exact context_12_28483_429715

theorem selected_cut_16898 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 113936) = some ⟨13, 1, 0, 3444, 113936, 1, 16384⟩ := by
  decide +kernel

theorem context_13_113936_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113936 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 113936 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 113936, 1, 16384⟩
    (by decide) selected_cut_16898

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
