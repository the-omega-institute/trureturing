/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover507
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem unmarked_context_11_100806_1371312 : frontier 10 ⟨1371312, by decide⟩
    (prefixCache 11 100806) (prefixPartial 11 100806) = false := by
  decide +kernel

theorem node_context_11_100806_1371312 : EJMOriginalGlobalDAGData.nodes 10 ⟨1371312, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1371219, by decide⟩,⟨1371268, by decide⟩,⟨1371311, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_100806_1371312 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100806 ⟨1371312, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 100806
    ⟨1371312, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1371219, by decide⟩,⟨1371268, by decide⟩,⟨1371311, by decide⟩]) unmarked_context_11_100806_1371312 node_context_11_100806_1371312
  intro a
  fin_cases a
  · exact context_12_403224_1108174
  · exact context_12_403225_1371219
  · exact context_12_403226_1371268
  · exact context_12_403227_1371311

theorem selected_cut_48772 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 403228) = some ⟨12, 1, 0, 1108174, 403228, 1, 65536⟩ := by
  decide +kernel

theorem context_12_403228_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 403228 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 403228 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 403228, 1, 65536⟩
    (by decide) selected_cut_48772

theorem selected_cut_48773 : selected 9 ⟨1371364, by decide⟩
    (prefixPartial 12 403229) = some ⟨12, 2, 0, 1371364, 403229, 2173, 65536⟩ := by
  decide +kernel

theorem context_12_403229_1371364 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 403229 ⟨1371364, by decide⟩ :=
  accepted_of_selected 12 403229 ⟨1371364, by decide⟩ ⟨12, 2, 0, 1371364, 403229, 2173, 65536⟩
    (by decide) selected_cut_48773

theorem selected_cut_48774 : selected 9 ⟨1371419, by decide⟩
    (prefixPartial 12 403230) = some ⟨12, 2, 0, 1371419, 403230, 2293, 65536⟩ := by
  decide +kernel

theorem context_12_403230_1371419 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 403230 ⟨1371419, by decide⟩ :=
  accepted_of_selected 12 403230 ⟨1371419, by decide⟩ ⟨12, 2, 0, 1371419, 403230, 2293, 65536⟩
    (by decide) selected_cut_48774

theorem selected_cut_48775 : selected 9 ⟨903806, by decide⟩
    (prefixPartial 12 403231) = some ⟨12, 1, 0, 903806, 403231, 1, 65536⟩ := by
  decide +kernel

theorem context_12_403231_903806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 403231 ⟨903806, by decide⟩ :=
  accepted_of_selected 12 403231 ⟨903806, by decide⟩ ⟨12, 1, 0, 903806, 403231, 1, 65536⟩
    (by decide) selected_cut_48775

theorem unmarked_context_11_100807_1371420 : frontier 10 ⟨1371420, by decide⟩
    (prefixCache 11 100807) (prefixPartial 11 100807) = false := by
  decide +kernel

theorem node_context_11_100807_1371420 : EJMOriginalGlobalDAGData.nodes 10 ⟨1371420, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1371364, by decide⟩,⟨1371419, by decide⟩,⟨903806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_100807_1371420 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100807 ⟨1371420, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 100807
    ⟨1371420, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1371364, by decide⟩,⟨1371419, by decide⟩,⟨903806, by decide⟩]) unmarked_context_11_100807_1371420 node_context_11_100807_1371420
  intro a
  fin_cases a
  · exact context_12_403228_1108174
  · exact context_12_403229_1371364
  · exact context_12_403230_1371419
  · exact context_12_403231_903806

theorem unmarked_context_10_25201_1371421 : frontier 11 ⟨1371421, by decide⟩
    (prefixCache 10 25201) (prefixPartial 10 25201) = false := by
  decide +kernel

theorem node_context_10_25201_1371421 : EJMOriginalGlobalDAGData.nodes 11 ⟨1371421, by decide⟩ =
    .split (coordinate 10) (![⟨1371177, by decide⟩,⟨892405, by decide⟩,⟨1371312, by decide⟩,⟨1371420, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25201_1371421 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25201 ⟨1371421, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25201
    ⟨1371421, by decide⟩ (by decide) (![⟨1371177, by decide⟩,⟨892405, by decide⟩,⟨1371312, by decide⟩,⟨1371420, by decide⟩]) unmarked_context_10_25201_1371421 node_context_10_25201_1371421
  intro a
  fin_cases a
  · exact context_11_100804_1371177
  · exact context_11_100805_892405
  · exact context_11_100806_1371312
  · exact context_11_100807_1371420

theorem selected_cut_48776 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 403232) = some ⟨12, 1, 0, 1108174, 403232, 1, 65536⟩ := by
  decide +kernel

theorem context_12_403232_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 403232 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 403232 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 403232, 1, 65536⟩
    (by decide) selected_cut_48776

theorem selected_cut_48777 : selected 9 ⟨1371480, by decide⟩
    (prefixPartial 12 403233) = some ⟨12, 2, 0, 1371480, 403233, 2209, 65536⟩ := by
  decide +kernel

theorem context_12_403233_1371480 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 403233 ⟨1371480, by decide⟩ :=
  accepted_of_selected 12 403233 ⟨1371480, by decide⟩ ⟨12, 2, 0, 1371480, 403233, 2209, 65536⟩
    (by decide) selected_cut_48777

theorem selected_cut_48778 : selected 9 ⟨1371541, by decide⟩
    (prefixPartial 12 403234) = some ⟨12, 2, 0, 1371541, 403234, 2265, 65536⟩ := by
  decide +kernel

theorem context_12_403234_1371541 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 403234 ⟨1371541, by decide⟩ :=
  accepted_of_selected 12 403234 ⟨1371541, by decide⟩ ⟨12, 2, 0, 1371541, 403234, 2265, 65536⟩
    (by decide) selected_cut_48778

theorem selected_cut_48779 : selected 9 ⟨1371606, by decide⟩
    (prefixPartial 12 403235) = some ⟨12, 2, 0, 1371606, 403235, 2397, 65536⟩ := by
  decide +kernel

theorem context_12_403235_1371606 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 403235 ⟨1371606, by decide⟩ :=
  accepted_of_selected 12 403235 ⟨1371606, by decide⟩ ⟨12, 2, 0, 1371606, 403235, 2397, 65536⟩
    (by decide) selected_cut_48779

theorem unmarked_context_11_100808_1371607 : frontier 10 ⟨1371607, by decide⟩
    (prefixCache 11 100808) (prefixPartial 11 100808) = false := by
  decide +kernel

theorem node_context_11_100808_1371607 : EJMOriginalGlobalDAGData.nodes 10 ⟨1371607, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1371480, by decide⟩,⟨1371541, by decide⟩,⟨1371606, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_100808_1371607 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100808 ⟨1371607, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 100808
    ⟨1371607, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1371480, by decide⟩,⟨1371541, by decide⟩,⟨1371606, by decide⟩]) unmarked_context_11_100808_1371607 node_context_11_100808_1371607
  intro a
  fin_cases a
  · exact context_12_403232_1108174
  · exact context_12_403233_1371480
  · exact context_12_403234_1371541
  · exact context_12_403235_1371606

theorem selected_cut_48780 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 403236) = some ⟨12, 1, 0, 1108174, 403236, 1, 65536⟩ := by
  decide +kernel

theorem context_12_403236_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 403236 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 403236 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 403236, 1, 65536⟩
    (by decide) selected_cut_48780

theorem selected_cut_48781 : selected 9 ⟨1371645, by decide⟩
    (prefixPartial 12 403237) = some ⟨12, 2, 0, 1371645, 403237, 1737, 65536⟩ := by
  decide +kernel

theorem context_12_403237_1371645 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 403237 ⟨1371645, by decide⟩ :=
  accepted_of_selected 12 403237 ⟨1371645, by decide⟩ ⟨12, 2, 0, 1371645, 403237, 1737, 65536⟩
    (by decide) selected_cut_48781

theorem selected_cut_48782 : selected 9 ⟨1371683, by decide⟩
    (prefixPartial 12 403238) = some ⟨12, 2, 0, 1371683, 403238, 1793, 65536⟩ := by
  decide +kernel

theorem context_12_403238_1371683 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 403238 ⟨1371683, by decide⟩ :=
  accepted_of_selected 12 403238 ⟨1371683, by decide⟩ ⟨12, 2, 0, 1371683, 403238, 1793, 65536⟩
    (by decide) selected_cut_48782

theorem selected_cut_48783 : selected 9 ⟨1371725, by decide⟩
    (prefixPartial 12 403239) = some ⟨12, 2, 0, 1371725, 403239, 1797, 65536⟩ := by
  decide +kernel

theorem context_12_403239_1371725 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 403239 ⟨1371725, by decide⟩ :=
  accepted_of_selected 12 403239 ⟨1371725, by decide⟩ ⟨12, 2, 0, 1371725, 403239, 1797, 65536⟩
    (by decide) selected_cut_48783

theorem unmarked_context_11_100809_1371726 : frontier 10 ⟨1371726, by decide⟩
    (prefixCache 11 100809) (prefixPartial 11 100809) = false := by
  decide +kernel

theorem node_context_11_100809_1371726 : EJMOriginalGlobalDAGData.nodes 10 ⟨1371726, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1371645, by decide⟩,⟨1371683, by decide⟩,⟨1371725, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_100809_1371726 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100809 ⟨1371726, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 100809
    ⟨1371726, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1371645, by decide⟩,⟨1371683, by decide⟩,⟨1371725, by decide⟩]) unmarked_context_11_100809_1371726 node_context_11_100809_1371726
  intro a
  fin_cases a
  · exact context_12_403236_1108174
  · exact context_12_403237_1371645
  · exact context_12_403238_1371683
  · exact context_12_403239_1371725

theorem selected_cut_48784 : selected 10 ⟨1371775, by decide⟩
    (prefixPartial 11 100810) = some ⟨11, 2, 0, 1371775, 100810, 1969, 262144⟩ := by
  decide +kernel

theorem context_11_100810_1371775 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100810 ⟨1371775, by decide⟩ :=
  accepted_of_selected 11 100810 ⟨1371775, by decide⟩ ⟨11, 2, 0, 1371775, 100810, 1969, 262144⟩
    (by decide) selected_cut_48784

theorem selected_cut_48785 : selected 10 ⟨1371853, by decide⟩
    (prefixPartial 11 100811) = some ⟨11, 2, 0, 1371853, 100811, 3761, 262144⟩ := by
  decide +kernel

theorem context_11_100811_1371853 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100811 ⟨1371853, by decide⟩ :=
  accepted_of_selected 11 100811 ⟨1371853, by decide⟩ ⟨11, 2, 0, 1371853, 100811, 3761, 262144⟩
    (by decide) selected_cut_48785

theorem unmarked_context_10_25202_1371854 : frontier 11 ⟨1371854, by decide⟩
    (prefixCache 10 25202) (prefixPartial 10 25202) = false := by
  decide +kernel

theorem node_context_10_25202_1371854 : EJMOriginalGlobalDAGData.nodes 11 ⟨1371854, by decide⟩ =
    .split (coordinate 10) (![⟨1371607, by decide⟩,⟨1371726, by decide⟩,⟨1371775, by decide⟩,⟨1371853, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25202_1371854 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25202 ⟨1371854, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25202
    ⟨1371854, by decide⟩ (by decide) (![⟨1371607, by decide⟩,⟨1371726, by decide⟩,⟨1371775, by decide⟩,⟨1371853, by decide⟩]) unmarked_context_10_25202_1371854 node_context_10_25202_1371854
  intro a
  fin_cases a
  · exact context_11_100808_1371607
  · exact context_11_100809_1371726
  · exact context_11_100810_1371775
  · exact context_11_100811_1371853

theorem selected_cut_48786 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 403248) = some ⟨12, 1, 0, 1108174, 403248, 1, 65536⟩ := by
  decide +kernel

theorem context_12_403248_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 403248 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 403248 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 403248, 1, 65536⟩
    (by decide) selected_cut_48786

theorem selected_cut_48787 : selected 9 ⟨1371909, by decide⟩
    (prefixPartial 12 403249) = some ⟨12, 2, 0, 1371909, 403249, 2225, 65536⟩ := by
  decide +kernel

theorem context_12_403249_1371909 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 403249 ⟨1371909, by decide⟩ :=
  accepted_of_selected 12 403249 ⟨1371909, by decide⟩ ⟨12, 2, 0, 1371909, 403249, 2225, 65536⟩
    (by decide) selected_cut_48787

theorem selected_cut_48788 : selected 9 ⟨1371967, by decide⟩
    (prefixPartial 12 403250) = some ⟨12, 2, 0, 1371967, 403250, 2189, 65536⟩ := by
  decide +kernel

theorem context_12_403250_1371967 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 403250 ⟨1371967, by decide⟩ :=
  accepted_of_selected 12 403250 ⟨1371967, by decide⟩ ⟨12, 2, 0, 1371967, 403250, 2189, 65536⟩
    (by decide) selected_cut_48788

theorem selected_cut_48789 : selected 9 ⟨1372033, by decide⟩
    (prefixPartial 12 403251) = some ⟨12, 2, 0, 1372033, 403251, 2385, 65536⟩ := by
  decide +kernel

theorem context_12_403251_1372033 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 403251 ⟨1372033, by decide⟩ :=
  accepted_of_selected 12 403251 ⟨1372033, by decide⟩ ⟨12, 2, 0, 1372033, 403251, 2385, 65536⟩
    (by decide) selected_cut_48789

theorem unmarked_context_11_100812_1372034 : frontier 10 ⟨1372034, by decide⟩
    (prefixCache 11 100812) (prefixPartial 11 100812) = false := by
  decide +kernel

theorem node_context_11_100812_1372034 : EJMOriginalGlobalDAGData.nodes 10 ⟨1372034, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1371909, by decide⟩,⟨1371967, by decide⟩,⟨1372033, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_100812_1372034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100812 ⟨1372034, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 100812
    ⟨1372034, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1371909, by decide⟩,⟨1371967, by decide⟩,⟨1372033, by decide⟩]) unmarked_context_11_100812_1372034 node_context_11_100812_1372034
  intro a
  fin_cases a
  · exact context_12_403248_1108174
  · exact context_12_403249_1371909
  · exact context_12_403250_1371967
  · exact context_12_403251_1372033

theorem selected_cut_48790 : selected 10 ⟨1372121, by decide⟩
    (prefixPartial 11 100813) = some ⟨11, 2, 0, 1372121, 100813, 3653, 262144⟩ := by
  decide +kernel

theorem context_11_100813_1372121 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100813 ⟨1372121, by decide⟩ :=
  accepted_of_selected 11 100813 ⟨1372121, by decide⟩ ⟨11, 2, 0, 1372121, 100813, 3653, 262144⟩
    (by decide) selected_cut_48790

theorem selected_cut_48791 : selected 10 ⟨1372203, by decide⟩
    (prefixPartial 11 100814) = some ⟨11, 2, 0, 1372203, 100814, 3697, 262144⟩ := by
  decide +kernel

theorem context_11_100814_1372203 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100814 ⟨1372203, by decide⟩ :=
  accepted_of_selected 11 100814 ⟨1372203, by decide⟩ ⟨11, 2, 0, 1372203, 100814, 3697, 262144⟩
    (by decide) selected_cut_48791

theorem selected_cut_48792 : selected 10 ⟨1372242, by decide⟩
    (prefixPartial 11 100815) = some ⟨11, 2, 0, 1372242, 100815, 1909, 262144⟩ := by
  decide +kernel

theorem context_11_100815_1372242 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100815 ⟨1372242, by decide⟩ :=
  accepted_of_selected 11 100815 ⟨1372242, by decide⟩ ⟨11, 2, 0, 1372242, 100815, 1909, 262144⟩
    (by decide) selected_cut_48792

theorem unmarked_context_10_25203_1372243 : frontier 11 ⟨1372243, by decide⟩
    (prefixCache 10 25203) (prefixPartial 10 25203) = false := by
  decide +kernel

theorem node_context_10_25203_1372243 : EJMOriginalGlobalDAGData.nodes 11 ⟨1372243, by decide⟩ =
    .split (coordinate 10) (![⟨1372034, by decide⟩,⟨1372121, by decide⟩,⟨1372203, by decide⟩,⟨1372242, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25203_1372243 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25203 ⟨1372243, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25203
    ⟨1372243, by decide⟩ (by decide) (![⟨1372034, by decide⟩,⟨1372121, by decide⟩,⟨1372203, by decide⟩,⟨1372242, by decide⟩]) unmarked_context_10_25203_1372243 node_context_10_25203_1372243
  intro a
  fin_cases a
  · exact context_11_100812_1372034
  · exact context_11_100813_1372121
  · exact context_11_100814_1372203
  · exact context_11_100815_1372242

theorem unmarked_context_9_6300_1372244 : frontier 12 ⟨1372244, by decide⟩
    (prefixCache 9 6300) (prefixPartial 9 6300) = false := by
  decide +kernel

theorem node_context_9_6300_1372244 : EJMOriginalGlobalDAGData.nodes 12 ⟨1372244, by decide⟩ =
    .split (coordinate 9) (![⟨1370961, by decide⟩,⟨1371421, by decide⟩,⟨1371854, by decide⟩,⟨1372243, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6300_1372244 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6300 ⟨1372244, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6300
    ⟨1372244, by decide⟩ (by decide) (![⟨1370961, by decide⟩,⟨1371421, by decide⟩,⟨1371854, by decide⟩,⟨1372243, by decide⟩]) unmarked_context_9_6300_1372244 node_context_9_6300_1372244
  intro a
  fin_cases a
  · exact context_10_25200_1370961
  · exact context_10_25201_1371421
  · exact context_10_25202_1371854
  · exact context_10_25203_1372243

theorem selected_cut_48793 : selected 10 ⟨1369428, by decide⟩
    (prefixPartial 11 100816) = some ⟨11, 1, 0, 1369428, 100816, 1, 262144⟩ := by
  decide +kernel

theorem context_11_100816_1369428 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100816 ⟨1369428, by decide⟩ :=
  accepted_of_selected 11 100816 ⟨1369428, by decide⟩ ⟨11, 1, 0, 1369428, 100816, 1, 262144⟩
    (by decide) selected_cut_48793

theorem selected_cut_48794 : selected 9 ⟨1372274, by decide⟩
    (prefixPartial 12 403268) = some ⟨12, 2, 0, 1372274, 403268, 1421, 65536⟩ := by
  decide +kernel

theorem context_12_403268_1372274 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 403268 ⟨1372274, by decide⟩ :=
  accepted_of_selected 12 403268 ⟨1372274, by decide⟩ ⟨12, 2, 0, 1372274, 403268, 1421, 65536⟩
    (by decide) selected_cut_48794

theorem selected_cut_48795 : selected 9 ⟨642341, by decide⟩
    (prefixPartial 12 403269) = some ⟨12, 1, 0, 642341, 403269, 1, 65536⟩ := by
  decide +kernel

theorem context_12_403269_642341 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 403269 ⟨642341, by decide⟩ :=
  accepted_of_selected 12 403269 ⟨642341, by decide⟩ ⟨12, 1, 0, 642341, 403269, 1, 65536⟩
    (by decide) selected_cut_48795

theorem selected_cut_48796 : selected 9 ⟨1372308, by decide⟩
    (prefixPartial 12 403270) = some ⟨12, 2, 0, 1372308, 403270, 1569, 65536⟩ := by
  decide +kernel

theorem context_12_403270_1372308 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 403270 ⟨1372308, by decide⟩ :=
  accepted_of_selected 12 403270 ⟨1372308, by decide⟩ ⟨12, 2, 0, 1372308, 403270, 1569, 65536⟩
    (by decide) selected_cut_48796

theorem selected_cut_48797 : selected 9 ⟨1372340, by decide⟩
    (prefixPartial 12 403271) = some ⟨12, 2, 0, 1372340, 403271, 1529, 65536⟩ := by
  decide +kernel

theorem context_12_403271_1372340 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 403271 ⟨1372340, by decide⟩ :=
  accepted_of_selected 12 403271 ⟨1372340, by decide⟩ ⟨12, 2, 0, 1372340, 403271, 1529, 65536⟩
    (by decide) selected_cut_48797

theorem unmarked_context_11_100817_1372341 : frontier 10 ⟨1372341, by decide⟩
    (prefixCache 11 100817) (prefixPartial 11 100817) = false := by
  decide +kernel

theorem node_context_11_100817_1372341 : EJMOriginalGlobalDAGData.nodes 10 ⟨1372341, by decide⟩ =
    .split (coordinate 11) (![⟨1372274, by decide⟩,⟨642341, by decide⟩,⟨1372308, by decide⟩,⟨1372340, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_100817_1372341 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100817 ⟨1372341, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 100817
    ⟨1372341, by decide⟩ (by decide) (![⟨1372274, by decide⟩,⟨642341, by decide⟩,⟨1372308, by decide⟩,⟨1372340, by decide⟩]) unmarked_context_11_100817_1372341 node_context_11_100817_1372341
  intro a
  fin_cases a
  · exact context_12_403268_1372274
  · exact context_12_403269_642341
  · exact context_12_403270_1372308
  · exact context_12_403271_1372340

theorem selected_cut_48798 : selected 9 ⟨1372372, by decide⟩
    (prefixPartial 12 403272) = some ⟨12, 2, 0, 1372372, 403272, 1497, 65536⟩ := by
  decide +kernel

theorem context_12_403272_1372372 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 403272 ⟨1372372, by decide⟩ :=
  accepted_of_selected 12 403272 ⟨1372372, by decide⟩ ⟨12, 2, 0, 1372372, 403272, 1497, 65536⟩
    (by decide) selected_cut_48798

theorem selected_cut_48799 : selected 9 ⟨642341, by decide⟩
    (prefixPartial 12 403273) = some ⟨12, 1, 0, 642341, 403273, 1, 65536⟩ := by
  decide +kernel

theorem context_12_403273_642341 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 403273 ⟨642341, by decide⟩ :=
  accepted_of_selected 12 403273 ⟨642341, by decide⟩ ⟨12, 1, 0, 642341, 403273, 1, 65536⟩
    (by decide) selected_cut_48799

theorem selected_cut_48800 : selected 9 ⟨1372406, by decide⟩
    (prefixPartial 12 403274) = some ⟨12, 2, 0, 1372406, 403274, 1629, 65536⟩ := by
  decide +kernel

theorem context_12_403274_1372406 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 403274 ⟨1372406, by decide⟩ :=
  accepted_of_selected 12 403274 ⟨1372406, by decide⟩ ⟨12, 2, 0, 1372406, 403274, 1629, 65536⟩
    (by decide) selected_cut_48800

theorem selected_cut_48801 : selected 9 ⟨1372441, by decide⟩
    (prefixPartial 12 403275) = some ⟨12, 2, 0, 1372441, 403275, 1617, 65536⟩ := by
  decide +kernel

theorem context_12_403275_1372441 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 403275 ⟨1372441, by decide⟩ :=
  accepted_of_selected 12 403275 ⟨1372441, by decide⟩ ⟨12, 2, 0, 1372441, 403275, 1617, 65536⟩
    (by decide) selected_cut_48801

theorem unmarked_context_11_100818_1372442 : frontier 10 ⟨1372442, by decide⟩
    (prefixCache 11 100818) (prefixPartial 11 100818) = false := by
  decide +kernel

theorem node_context_11_100818_1372442 : EJMOriginalGlobalDAGData.nodes 10 ⟨1372442, by decide⟩ =
    .split (coordinate 11) (![⟨1372372, by decide⟩,⟨642341, by decide⟩,⟨1372406, by decide⟩,⟨1372441, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_100818_1372442 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100818 ⟨1372442, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 100818
    ⟨1372442, by decide⟩ (by decide) (![⟨1372372, by decide⟩,⟨642341, by decide⟩,⟨1372406, by decide⟩,⟨1372441, by decide⟩]) unmarked_context_11_100818_1372442 node_context_11_100818_1372442
  intro a
  fin_cases a
  · exact context_12_403272_1372372
  · exact context_12_403273_642341
  · exact context_12_403274_1372406
  · exact context_12_403275_1372441

theorem selected_cut_48802 : selected 10 ⟨1372513, by decide⟩
    (prefixPartial 11 100819) = some ⟨11, 2, 0, 1372513, 100819, 3245, 262144⟩ := by
  decide +kernel

theorem context_11_100819_1372513 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100819 ⟨1372513, by decide⟩ :=
  accepted_of_selected 11 100819 ⟨1372513, by decide⟩ ⟨11, 2, 0, 1372513, 100819, 3245, 262144⟩
    (by decide) selected_cut_48802

theorem unmarked_context_10_25204_1372514 : frontier 11 ⟨1372514, by decide⟩
    (prefixCache 10 25204) (prefixPartial 10 25204) = false := by
  decide +kernel

theorem node_context_10_25204_1372514 : EJMOriginalGlobalDAGData.nodes 11 ⟨1372514, by decide⟩ =
    .split (coordinate 10) (![⟨1369428, by decide⟩,⟨1372341, by decide⟩,⟨1372442, by decide⟩,⟨1372513, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25204_1372514 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25204 ⟨1372514, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25204
    ⟨1372514, by decide⟩ (by decide) (![⟨1369428, by decide⟩,⟨1372341, by decide⟩,⟨1372442, by decide⟩,⟨1372513, by decide⟩]) unmarked_context_10_25204_1372514 node_context_10_25204_1372514
  intro a
  fin_cases a
  · exact context_11_100816_1369428
  · exact context_11_100817_1372341
  · exact context_11_100818_1372442
  · exact context_11_100819_1372513

theorem selected_cut_48803 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 25205) = some ⟨10, 1, 0, 893098, 25205, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_25205_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25205 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 25205 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 25205, 1, 1048576⟩
    (by decide) selected_cut_48803

theorem selected_cut_48804 : selected 9 ⟨1372551, by decide⟩
    (prefixPartial 12 403296) = some ⟨12, 2, 0, 1372551, 403296, 1625, 65536⟩ := by
  decide +kernel

theorem context_12_403296_1372551 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 403296 ⟨1372551, by decide⟩ :=
  accepted_of_selected 12 403296 ⟨1372551, by decide⟩ ⟨12, 2, 0, 1372551, 403296, 1625, 65536⟩
    (by decide) selected_cut_48804

theorem selected_cut_48805 : selected 9 ⟨170504, by decide⟩
    (prefixPartial 12 403297) = some ⟨12, 1, 0, 170504, 403297, 1, 65536⟩ := by
  decide +kernel

theorem context_12_403297_170504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 403297 ⟨170504, by decide⟩ :=
  accepted_of_selected 12 403297 ⟨170504, by decide⟩ ⟨12, 1, 0, 170504, 403297, 1, 65536⟩
    (by decide) selected_cut_48805

theorem selected_cut_48806 : selected 9 ⟨1372584, by decide⟩
    (prefixPartial 12 403298) = some ⟨12, 2, 0, 1372584, 403298, 1545, 65536⟩ := by
  decide +kernel

theorem context_12_403298_1372584 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 403298 ⟨1372584, by decide⟩ :=
  accepted_of_selected 12 403298 ⟨1372584, by decide⟩ ⟨12, 2, 0, 1372584, 403298, 1545, 65536⟩
    (by decide) selected_cut_48806

theorem selected_cut_48807 : selected 9 ⟨1372619, by decide⟩
    (prefixPartial 12 403299) = some ⟨12, 2, 0, 1372619, 403299, 1617, 65536⟩ := by
  decide +kernel

theorem context_12_403299_1372619 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 403299 ⟨1372619, by decide⟩ :=
  accepted_of_selected 12 403299 ⟨1372619, by decide⟩ ⟨12, 2, 0, 1372619, 403299, 1617, 65536⟩
    (by decide) selected_cut_48807

theorem unmarked_context_11_100824_1372620 : frontier 10 ⟨1372620, by decide⟩
    (prefixCache 11 100824) (prefixPartial 11 100824) = false := by
  decide +kernel

theorem node_context_11_100824_1372620 : EJMOriginalGlobalDAGData.nodes 10 ⟨1372620, by decide⟩ =
    .split (coordinate 11) (![⟨1372551, by decide⟩,⟨170504, by decide⟩,⟨1372584, by decide⟩,⟨1372619, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_100824_1372620 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100824 ⟨1372620, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 100824
    ⟨1372620, by decide⟩ (by decide) (![⟨1372551, by decide⟩,⟨170504, by decide⟩,⟨1372584, by decide⟩,⟨1372619, by decide⟩]) unmarked_context_11_100824_1372620 node_context_11_100824_1372620
  intro a
  fin_cases a
  · exact context_12_403296_1372551
  · exact context_12_403297_170504
  · exact context_12_403298_1372584
  · exact context_12_403299_1372619

theorem selected_cut_48808 : selected 10 ⟨1372692, by decide⟩
    (prefixPartial 11 100825) = some ⟨11, 2, 0, 1372692, 100825, 3541, 262144⟩ := by
  decide +kernel

theorem context_11_100825_1372692 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100825 ⟨1372692, by decide⟩ :=
  accepted_of_selected 11 100825 ⟨1372692, by decide⟩ ⟨11, 2, 0, 1372692, 100825, 3541, 262144⟩
    (by decide) selected_cut_48808

theorem selected_cut_48809 : selected 10 ⟨1369759, by decide⟩
    (prefixPartial 11 100826) = some ⟨11, 1, 0, 1369759, 100826, 1, 262144⟩ := by
  decide +kernel

theorem context_11_100826_1369759 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100826 ⟨1369759, by decide⟩ :=
  accepted_of_selected 11 100826 ⟨1369759, by decide⟩ ⟨11, 1, 0, 1369759, 100826, 1, 262144⟩
    (by decide) selected_cut_48809

theorem selected_cut_48810 : selected 10 ⟨1372788, by decide⟩
    (prefixPartial 11 100827) = some ⟨11, 2, 0, 1372788, 100827, 3749, 262144⟩ := by
  decide +kernel

theorem context_11_100827_1372788 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100827 ⟨1372788, by decide⟩ :=
  accepted_of_selected 11 100827 ⟨1372788, by decide⟩ ⟨11, 2, 0, 1372788, 100827, 3749, 262144⟩
    (by decide) selected_cut_48810

theorem unmarked_context_10_25206_1372789 : frontier 11 ⟨1372789, by decide⟩
    (prefixCache 10 25206) (prefixPartial 10 25206) = false := by
  decide +kernel

theorem node_context_10_25206_1372789 : EJMOriginalGlobalDAGData.nodes 11 ⟨1372789, by decide⟩ =
    .split (coordinate 10) (![⟨1372620, by decide⟩,⟨1372692, by decide⟩,⟨1369759, by decide⟩,⟨1372788, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25206_1372789 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25206 ⟨1372789, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25206
    ⟨1372789, by decide⟩ (by decide) (![⟨1372620, by decide⟩,⟨1372692, by decide⟩,⟨1369759, by decide⟩,⟨1372788, by decide⟩]) unmarked_context_10_25206_1372789 node_context_10_25206_1372789
  intro a
  fin_cases a
  · exact context_11_100824_1372620
  · exact context_11_100825_1372692
  · exact context_11_100826_1369759
  · exact context_11_100827_1372788

theorem selected_cut_48811 : selected 10 ⟨1372862, by decide⟩
    (prefixPartial 11 100828) = some ⟨11, 2, 0, 1372862, 100828, 3161, 262144⟩ := by
  decide +kernel

theorem context_11_100828_1372862 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100828 ⟨1372862, by decide⟩ :=
  accepted_of_selected 11 100828 ⟨1372862, by decide⟩ ⟨11, 2, 0, 1372862, 100828, 3161, 262144⟩
    (by decide) selected_cut_48811

theorem selected_cut_48812 : selected 10 ⟨1372935, by decide⟩
    (prefixPartial 11 100829) = some ⟨11, 2, 0, 1372935, 100829, 3505, 262144⟩ := by
  decide +kernel

theorem context_11_100829_1372935 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100829 ⟨1372935, by decide⟩ :=
  accepted_of_selected 11 100829 ⟨1372935, by decide⟩ ⟨11, 2, 0, 1372935, 100829, 3505, 262144⟩
    (by decide) selected_cut_48812

theorem selected_cut_48813 : selected 10 ⟨1373002, by decide⟩
    (prefixPartial 11 100830) = some ⟨11, 2, 0, 1373002, 100830, 3281, 262144⟩ := by
  decide +kernel

theorem context_11_100830_1373002 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100830 ⟨1373002, by decide⟩ :=
  accepted_of_selected 11 100830 ⟨1373002, by decide⟩ ⟨11, 2, 0, 1373002, 100830, 3281, 262144⟩
    (by decide) selected_cut_48813

theorem selected_cut_48814 : selected 10 ⟨1370051, by decide⟩
    (prefixPartial 11 100831) = some ⟨11, 1, 0, 1370051, 100831, 1, 262144⟩ := by
  decide +kernel

theorem context_11_100831_1370051 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100831 ⟨1370051, by decide⟩ :=
  accepted_of_selected 11 100831 ⟨1370051, by decide⟩ ⟨11, 1, 0, 1370051, 100831, 1, 262144⟩
    (by decide) selected_cut_48814

theorem unmarked_context_10_25207_1373003 : frontier 11 ⟨1373003, by decide⟩
    (prefixCache 10 25207) (prefixPartial 10 25207) = false := by
  decide +kernel

theorem node_context_10_25207_1373003 : EJMOriginalGlobalDAGData.nodes 11 ⟨1373003, by decide⟩ =
    .split (coordinate 10) (![⟨1372862, by decide⟩,⟨1372935, by decide⟩,⟨1373002, by decide⟩,⟨1370051, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25207_1373003 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25207 ⟨1373003, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25207
    ⟨1373003, by decide⟩ (by decide) (![⟨1372862, by decide⟩,⟨1372935, by decide⟩,⟨1373002, by decide⟩,⟨1370051, by decide⟩]) unmarked_context_10_25207_1373003 node_context_10_25207_1373003
  intro a
  fin_cases a
  · exact context_11_100828_1372862
  · exact context_11_100829_1372935
  · exact context_11_100830_1373002
  · exact context_11_100831_1370051

theorem unmarked_context_9_6301_1373004 : frontier 12 ⟨1373004, by decide⟩
    (prefixCache 9 6301) (prefixPartial 9 6301) = false := by
  decide +kernel

theorem node_context_9_6301_1373004 : EJMOriginalGlobalDAGData.nodes 12 ⟨1373004, by decide⟩ =
    .split (coordinate 9) (![⟨1372514, by decide⟩,⟨893098, by decide⟩,⟨1372789, by decide⟩,⟨1373003, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6301_1373004 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6301 ⟨1373004, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6301
    ⟨1373004, by decide⟩ (by decide) (![⟨1372514, by decide⟩,⟨893098, by decide⟩,⟨1372789, by decide⟩,⟨1373003, by decide⟩]) unmarked_context_9_6301_1373004 node_context_9_6301_1373004
  intro a
  fin_cases a
  · exact context_10_25204_1372514
  · exact context_10_25205_893098
  · exact context_10_25206_1372789
  · exact context_10_25207_1373003

theorem selected_cut_48815 : selected 10 ⟨1373030, by decide⟩
    (prefixPartial 11 100832) = some ⟨11, 2, 0, 1373030, 100832, 1101, 262144⟩ := by
  decide +kernel

theorem context_11_100832_1373030 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100832 ⟨1373030, by decide⟩ :=
  accepted_of_selected 11 100832 ⟨1373030, by decide⟩ ⟨11, 2, 0, 1373030, 100832, 1101, 262144⟩
    (by decide) selected_cut_48815

theorem selected_cut_48816 : selected 10 ⟨1373080, by decide⟩
    (prefixPartial 11 100833) = some ⟨11, 2, 0, 1373080, 100833, 2641, 262144⟩ := by
  decide +kernel

theorem context_11_100833_1373080 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100833 ⟨1373080, by decide⟩ :=
  accepted_of_selected 11 100833 ⟨1373080, by decide⟩ ⟨11, 2, 0, 1373080, 100833, 2641, 262144⟩
    (by decide) selected_cut_48816

theorem selected_cut_48817 : selected 10 ⟨1373130, by decide⟩
    (prefixPartial 11 100834) = some ⟨11, 2, 0, 1373130, 100834, 2737, 262144⟩ := by
  decide +kernel

theorem context_11_100834_1373130 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100834 ⟨1373130, by decide⟩ :=
  accepted_of_selected 11 100834 ⟨1373130, by decide⟩ ⟨11, 2, 0, 1373130, 100834, 2737, 262144⟩
    (by decide) selected_cut_48817

theorem selected_cut_48818 : selected 10 ⟨1373167, by decide⟩
    (prefixPartial 11 100835) = some ⟨11, 2, 0, 1373167, 100835, 1677, 262144⟩ := by
  decide +kernel

theorem context_11_100835_1373167 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100835 ⟨1373167, by decide⟩ :=
  accepted_of_selected 11 100835 ⟨1373167, by decide⟩ ⟨11, 2, 0, 1373167, 100835, 1677, 262144⟩
    (by decide) selected_cut_48818

theorem unmarked_context_10_25208_1373168 : frontier 11 ⟨1373168, by decide⟩
    (prefixCache 10 25208) (prefixPartial 10 25208) = false := by
  decide +kernel

theorem node_context_10_25208_1373168 : EJMOriginalGlobalDAGData.nodes 11 ⟨1373168, by decide⟩ =
    .split (coordinate 10) (![⟨1373030, by decide⟩,⟨1373080, by decide⟩,⟨1373130, by decide⟩,⟨1373167, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25208_1373168 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25208 ⟨1373168, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25208
    ⟨1373168, by decide⟩ (by decide) (![⟨1373030, by decide⟩,⟨1373080, by decide⟩,⟨1373130, by decide⟩,⟨1373167, by decide⟩]) unmarked_context_10_25208_1373168 node_context_10_25208_1373168
  intro a
  fin_cases a
  · exact context_11_100832_1373030
  · exact context_11_100833_1373080
  · exact context_11_100834_1373130
  · exact context_11_100835_1373167

theorem selected_cut_48819 : selected 10 ⟨1373229, by decide⟩
    (prefixPartial 11 100836) = some ⟨11, 2, 0, 1373229, 100836, 2729, 262144⟩ := by
  decide +kernel

theorem context_11_100836_1373229 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100836 ⟨1373229, by decide⟩ :=
  accepted_of_selected 11 100836 ⟨1373229, by decide⟩ ⟨11, 2, 0, 1373229, 100836, 2729, 262144⟩
    (by decide) selected_cut_48819

theorem selected_cut_48820 : selected 10 ⟨892405, by decide⟩
    (prefixPartial 11 100837) = some ⟨11, 1, 0, 892405, 100837, 1, 262144⟩ := by
  decide +kernel

theorem context_11_100837_892405 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100837 ⟨892405, by decide⟩ :=
  accepted_of_selected 11 100837 ⟨892405, by decide⟩ ⟨11, 1, 0, 892405, 100837, 1, 262144⟩
    (by decide) selected_cut_48820

theorem selected_cut_48821 : selected 10 ⟨1373277, by decide⟩
    (prefixPartial 11 100838) = some ⟨11, 2, 0, 1373277, 100838, 2173, 262144⟩ := by
  decide +kernel

theorem context_11_100838_1373277 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100838 ⟨1373277, by decide⟩ :=
  accepted_of_selected 11 100838 ⟨1373277, by decide⟩ ⟨11, 2, 0, 1373277, 100838, 2173, 262144⟩
    (by decide) selected_cut_48821

theorem selected_cut_48822 : selected 10 ⟨1373321, by decide⟩
    (prefixPartial 11 100839) = some ⟨11, 2, 0, 1373321, 100839, 1933, 262144⟩ := by
  decide +kernel

theorem context_11_100839_1373321 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100839 ⟨1373321, by decide⟩ :=
  accepted_of_selected 11 100839 ⟨1373321, by decide⟩ ⟨11, 2, 0, 1373321, 100839, 1933, 262144⟩
    (by decide) selected_cut_48822

theorem unmarked_context_10_25209_1373322 : frontier 11 ⟨1373322, by decide⟩
    (prefixCache 10 25209) (prefixPartial 10 25209) = false := by
  decide +kernel

theorem node_context_10_25209_1373322 : EJMOriginalGlobalDAGData.nodes 11 ⟨1373322, by decide⟩ =
    .split (coordinate 10) (![⟨1373229, by decide⟩,⟨892405, by decide⟩,⟨1373277, by decide⟩,⟨1373321, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25209_1373322 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25209 ⟨1373322, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25209
    ⟨1373322, by decide⟩ (by decide) (![⟨1373229, by decide⟩,⟨892405, by decide⟩,⟨1373277, by decide⟩,⟨1373321, by decide⟩]) unmarked_context_10_25209_1373322 node_context_10_25209_1373322
  intro a
  fin_cases a
  · exact context_11_100836_1373229
  · exact context_11_100837_892405
  · exact context_11_100838_1373277
  · exact context_11_100839_1373321

theorem selected_cut_48823 : selected 11 ⟨1373363, by decide⟩
    (prefixPartial 10 25210) = some ⟨10, 2, 0, 1373363, 25210, 1809, 1048576⟩ := by
  decide +kernel

theorem context_10_25210_1373363 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25210 ⟨1373363, by decide⟩ :=
  accepted_of_selected 10 25210 ⟨1373363, by decide⟩ ⟨10, 2, 0, 1373363, 25210, 1809, 1048576⟩
    (by decide) selected_cut_48823

theorem selected_cut_48824 : selected 10 ⟨1373393, by decide⟩
    (prefixPartial 11 100844) = some ⟨11, 2, 0, 1373393, 100844, 1357, 262144⟩ := by
  decide +kernel

theorem context_11_100844_1373393 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100844 ⟨1373393, by decide⟩ :=
  accepted_of_selected 11 100844 ⟨1373393, by decide⟩ ⟨11, 2, 0, 1373393, 100844, 1357, 262144⟩
    (by decide) selected_cut_48824

theorem selected_cut_48825 : selected 10 ⟨1373445, by decide⟩
    (prefixPartial 11 100845) = some ⟨11, 2, 0, 1373445, 100845, 1817, 262144⟩ := by
  decide +kernel

theorem context_11_100845_1373445 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100845 ⟨1373445, by decide⟩ :=
  accepted_of_selected 11 100845 ⟨1373445, by decide⟩ ⟨11, 2, 0, 1373445, 100845, 1817, 262144⟩
    (by decide) selected_cut_48825

theorem selected_cut_48826 : selected 10 ⟨1373476, by decide⟩
    (prefixPartial 11 100846) = some ⟨11, 2, 0, 1373476, 100846, 1429, 262144⟩ := by
  decide +kernel

theorem context_11_100846_1373476 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100846 ⟨1373476, by decide⟩ :=
  accepted_of_selected 11 100846 ⟨1373476, by decide⟩ ⟨11, 2, 0, 1373476, 100846, 1429, 262144⟩
    (by decide) selected_cut_48826

theorem selected_cut_48827 : selected 10 ⟨1373504, by decide⟩
    (prefixPartial 11 100847) = some ⟨11, 2, 0, 1373504, 100847, 617, 262144⟩ := by
  decide +kernel

theorem context_11_100847_1373504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100847 ⟨1373504, by decide⟩ :=
  accepted_of_selected 11 100847 ⟨1373504, by decide⟩ ⟨11, 2, 0, 1373504, 100847, 617, 262144⟩
    (by decide) selected_cut_48827

theorem unmarked_context_10_25211_1373505 : frontier 11 ⟨1373505, by decide⟩
    (prefixCache 10 25211) (prefixPartial 10 25211) = false := by
  decide +kernel

theorem node_context_10_25211_1373505 : EJMOriginalGlobalDAGData.nodes 11 ⟨1373505, by decide⟩ =
    .split (coordinate 10) (![⟨1373393, by decide⟩,⟨1373445, by decide⟩,⟨1373476, by decide⟩,⟨1373504, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25211_1373505 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25211 ⟨1373505, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25211
    ⟨1373505, by decide⟩ (by decide) (![⟨1373393, by decide⟩,⟨1373445, by decide⟩,⟨1373476, by decide⟩,⟨1373504, by decide⟩]) unmarked_context_10_25211_1373505 node_context_10_25211_1373505
  intro a
  fin_cases a
  · exact context_11_100844_1373393
  · exact context_11_100845_1373445
  · exact context_11_100846_1373476
  · exact context_11_100847_1373504

theorem unmarked_context_9_6302_1373506 : frontier 12 ⟨1373506, by decide⟩
    (prefixCache 9 6302) (prefixPartial 9 6302) = false := by
  decide +kernel

theorem node_context_9_6302_1373506 : EJMOriginalGlobalDAGData.nodes 12 ⟨1373506, by decide⟩ =
    .split (coordinate 9) (![⟨1373168, by decide⟩,⟨1373322, by decide⟩,⟨1373363, by decide⟩,⟨1373505, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6302_1373506 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6302 ⟨1373506, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6302
    ⟨1373506, by decide⟩ (by decide) (![⟨1373168, by decide⟩,⟨1373322, by decide⟩,⟨1373363, by decide⟩,⟨1373505, by decide⟩]) unmarked_context_9_6302_1373506 node_context_9_6302_1373506
  intro a
  fin_cases a
  · exact context_10_25208_1373168
  · exact context_10_25209_1373322
  · exact context_10_25210_1373363
  · exact context_10_25211_1373505

theorem selected_cut_48828 : selected 11 ⟨1373561, by decide⟩
    (prefixPartial 10 25212) = some ⟨10, 2, 0, 1373561, 25212, 2401, 1048576⟩ := by
  decide +kernel

theorem context_10_25212_1373561 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25212 ⟨1373561, by decide⟩ :=
  accepted_of_selected 10 25212 ⟨1373561, by decide⟩ ⟨10, 2, 0, 1373561, 25212, 2401, 1048576⟩
    (by decide) selected_cut_48828

theorem selected_cut_48829 : selected 11 ⟨1373592, by decide⟩
    (prefixPartial 10 25213) = some ⟨10, 2, 0, 1373592, 25213, 1549, 1048576⟩ := by
  decide +kernel

theorem context_10_25213_1373592 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25213 ⟨1373592, by decide⟩ :=
  accepted_of_selected 10 25213 ⟨1373592, by decide⟩ ⟨10, 2, 0, 1373592, 25213, 1549, 1048576⟩
    (by decide) selected_cut_48829

theorem selected_cut_48830 : selected 11 ⟨1373639, by decide⟩
    (prefixPartial 10 25214) = some ⟨10, 2, 0, 1373639, 25214, 1153, 1048576⟩ := by
  decide +kernel

theorem context_10_25214_1373639 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25214 ⟨1373639, by decide⟩ :=
  accepted_of_selected 10 25214 ⟨1373639, by decide⟩ ⟨10, 2, 0, 1373639, 25214, 1153, 1048576⟩
    (by decide) selected_cut_48830

theorem selected_cut_48831 : selected 11 ⟨1373648, by decide⟩
    (prefixPartial 10 25215) = some ⟨10, 2, 0, 1373648, 25215, 85, 1048576⟩ := by
  decide +kernel

theorem context_10_25215_1373648 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25215 ⟨1373648, by decide⟩ :=
  accepted_of_selected 10 25215 ⟨1373648, by decide⟩ ⟨10, 2, 0, 1373648, 25215, 85, 1048576⟩
    (by decide) selected_cut_48831

theorem unmarked_context_9_6303_1373649 : frontier 12 ⟨1373649, by decide⟩
    (prefixCache 9 6303) (prefixPartial 9 6303) = false := by
  decide +kernel

theorem node_context_9_6303_1373649 : EJMOriginalGlobalDAGData.nodes 12 ⟨1373649, by decide⟩ =
    .split (coordinate 9) (![⟨1373561, by decide⟩,⟨1373592, by decide⟩,⟨1373639, by decide⟩,⟨1373648, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6303_1373649 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6303 ⟨1373649, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6303
    ⟨1373649, by decide⟩ (by decide) (![⟨1373561, by decide⟩,⟨1373592, by decide⟩,⟨1373639, by decide⟩,⟨1373648, by decide⟩]) unmarked_context_9_6303_1373649 node_context_9_6303_1373649
  intro a
  fin_cases a
  · exact context_10_25212_1373561
  · exact context_10_25213_1373592
  · exact context_10_25214_1373639
  · exact context_10_25215_1373648

theorem unmarked_context_8_1575_1373650 : frontier 13 ⟨1373650, by decide⟩
    (prefixCache 8 1575) (prefixPartial 8 1575) = false := by
  decide +kernel

theorem node_context_8_1575_1373650 : EJMOriginalGlobalDAGData.nodes 13 ⟨1373650, by decide⟩ =
    .split (coordinate 8) (![⟨1372244, by decide⟩,⟨1373004, by decide⟩,⟨1373506, by decide⟩,⟨1373649, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1575_1373650 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1575 ⟨1373650, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1575
    ⟨1373650, by decide⟩ (by decide) (![⟨1372244, by decide⟩,⟨1373004, by decide⟩,⟨1373506, by decide⟩,⟨1373649, by decide⟩]) unmarked_context_8_1575_1373650 node_context_8_1575_1373650
  intro a
  fin_cases a
  · exact context_9_6300_1372244
  · exact context_9_6301_1373004
  · exact context_9_6302_1373506
  · exact context_9_6303_1373649

theorem unmarked_context_7_393_1373651 : frontier 14 ⟨1373651, by decide⟩
    (prefixCache 7 393) (prefixPartial 7 393) = false := by
  decide +kernel

theorem node_context_7_393_1373651 : EJMOriginalGlobalDAGData.nodes 14 ⟨1373651, by decide⟩ =
    .split (coordinate 7) (![⟨1364555, by decide⟩,⟨1370758, by decide⟩,⟨1366235, by decide⟩,⟨1373650, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_7_393_1373651 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 393 ⟨1373651, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 7 393
    ⟨1373651, by decide⟩ (by decide) (![⟨1364555, by decide⟩,⟨1370758, by decide⟩,⟨1366235, by decide⟩,⟨1373650, by decide⟩]) unmarked_context_7_393_1373651 node_context_7_393_1373651
  intro a
  fin_cases a
  · exact context_8_1572_1364555
  · exact context_8_1573_1370758
  · exact context_8_1574_1366235
  · exact context_8_1575_1373650

theorem selected_cut_48832 : selected 13 ⟨1364555, by decide⟩
    (prefixPartial 8 1576) = some ⟨8, 1, 0, 1364555, 1576, 1, 16777216⟩ := by
  decide +kernel

theorem context_8_1576_1364555 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1576 ⟨1364555, by decide⟩ :=
  accepted_of_selected 8 1576 ⟨1364555, by decide⟩ ⟨8, 1, 0, 1364555, 1576, 1, 16777216⟩
    (by decide) selected_cut_48832

theorem selected_cut_48833 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 100928) = some ⟨11, 1, 0, 434745, 100928, 1, 262144⟩ := by
  decide +kernel

theorem context_11_100928_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100928 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 100928 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 100928, 1, 262144⟩
    (by decide) selected_cut_48833

theorem selected_cut_48834 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 100929) = some ⟨11, 1, 0, 434745, 100929, 1, 262144⟩ := by
  decide +kernel

theorem context_11_100929_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100929 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 100929 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 100929, 1, 262144⟩
    (by decide) selected_cut_48834

theorem selected_cut_48835 : selected 10 ⟨1373798, by decide⟩
    (prefixPartial 11 100930) = some ⟨11, 2, 0, 1373798, 100930, 2993, 262144⟩ := by
  decide +kernel

theorem context_11_100930_1373798 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100930 ⟨1373798, by decide⟩ :=
  accepted_of_selected 11 100930 ⟨1373798, by decide⟩ ⟨11, 2, 0, 1373798, 100930, 2993, 262144⟩
    (by decide) selected_cut_48835

theorem selected_cut_48836 : selected 10 ⟨1373917, by decide⟩
    (prefixPartial 11 100931) = some ⟨11, 2, 0, 1373917, 100931, 4009, 262144⟩ := by
  decide +kernel

theorem context_11_100931_1373917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100931 ⟨1373917, by decide⟩ :=
  accepted_of_selected 11 100931 ⟨1373917, by decide⟩ ⟨11, 2, 0, 1373917, 100931, 4009, 262144⟩
    (by decide) selected_cut_48836

theorem unmarked_context_10_25232_1373918 : frontier 11 ⟨1373918, by decide⟩
    (prefixCache 10 25232) (prefixPartial 10 25232) = false := by
  decide +kernel

theorem node_context_10_25232_1373918 : EJMOriginalGlobalDAGData.nodes 11 ⟨1373918, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨434745, by decide⟩,⟨1373798, by decide⟩,⟨1373917, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25232_1373918 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25232 ⟨1373918, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25232
    ⟨1373918, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨434745, by decide⟩,⟨1373798, by decide⟩,⟨1373917, by decide⟩]) unmarked_context_10_25232_1373918 node_context_10_25232_1373918
  intro a
  fin_cases a
  · exact context_11_100928_434745
  · exact context_11_100929_434745
  · exact context_11_100930_1373798
  · exact context_11_100931_1373917

theorem selected_cut_48837 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 403728) = some ⟨12, 1, 0, 1108174, 403728, 1, 65536⟩ := by
  decide +kernel

theorem context_12_403728_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 403728 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 403728 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 403728, 1, 65536⟩
    (by decide) selected_cut_48837

theorem selected_cut_48838 : selected 9 ⟨1374010, by decide⟩
    (prefixPartial 12 403729) = some ⟨12, 2, 0, 1374010, 403729, 2325, 65536⟩ := by
  decide +kernel

theorem context_12_403729_1374010 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 403729 ⟨1374010, by decide⟩ :=
  accepted_of_selected 12 403729 ⟨1374010, by decide⟩ ⟨12, 2, 0, 1374010, 403729, 2325, 65536⟩
    (by decide) selected_cut_48838

theorem selected_cut_48839 : selected 9 ⟨1374075, by decide⟩
    (prefixPartial 12 403730) = some ⟨12, 2, 0, 1374075, 403730, 2037, 65536⟩ := by
  decide +kernel

theorem context_12_403730_1374075 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 403730 ⟨1374075, by decide⟩ :=
  accepted_of_selected 12 403730 ⟨1374075, by decide⟩ ⟨12, 2, 0, 1374075, 403730, 2037, 65536⟩
    (by decide) selected_cut_48839

theorem selected_cut_48840 : selected 9 ⟨1374144, by decide⟩
    (prefixPartial 12 403731) = some ⟨12, 2, 0, 1374144, 403731, 2125, 65536⟩ := by
  decide +kernel

theorem context_12_403731_1374144 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 403731 ⟨1374144, by decide⟩ :=
  accepted_of_selected 12 403731 ⟨1374144, by decide⟩ ⟨12, 2, 0, 1374144, 403731, 2125, 65536⟩
    (by decide) selected_cut_48840

theorem unmarked_context_11_100932_1374145 : frontier 10 ⟨1374145, by decide⟩
    (prefixCache 11 100932) (prefixPartial 11 100932) = false := by
  decide +kernel

theorem node_context_11_100932_1374145 : EJMOriginalGlobalDAGData.nodes 10 ⟨1374145, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1374010, by decide⟩,⟨1374075, by decide⟩,⟨1374144, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_100932_1374145 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100932 ⟨1374145, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 100932
    ⟨1374145, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1374010, by decide⟩,⟨1374075, by decide⟩,⟨1374144, by decide⟩]) unmarked_context_11_100932_1374145 node_context_11_100932_1374145
  intro a
  fin_cases a
  · exact context_12_403728_1108174
  · exact context_12_403729_1374010
  · exact context_12_403730_1374075
  · exact context_12_403731_1374144

theorem selected_cut_48841 : selected 10 ⟨1374215, by decide⟩
    (prefixPartial 11 100933) = some ⟨11, 2, 0, 1374215, 100933, 2057, 262144⟩ := by
  decide +kernel

theorem context_11_100933_1374215 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100933 ⟨1374215, by decide⟩ :=
  accepted_of_selected 11 100933 ⟨1374215, by decide⟩ ⟨11, 2, 0, 1374215, 100933, 2057, 262144⟩
    (by decide) selected_cut_48841

theorem selected_cut_48842 : selected 10 ⟨1374304, by decide⟩
    (prefixPartial 11 100934) = some ⟨11, 2, 0, 1374304, 100934, 2885, 262144⟩ := by
  decide +kernel

theorem context_11_100934_1374304 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100934 ⟨1374304, by decide⟩ :=
  accepted_of_selected 11 100934 ⟨1374304, by decide⟩ ⟨11, 2, 0, 1374304, 100934, 2885, 262144⟩
    (by decide) selected_cut_48842

theorem selected_cut_48843 : selected 10 ⟨1374392, by decide⟩
    (prefixPartial 11 100935) = some ⟨11, 2, 0, 1374392, 100935, 3409, 262144⟩ := by
  decide +kernel

theorem context_11_100935_1374392 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100935 ⟨1374392, by decide⟩ :=
  accepted_of_selected 11 100935 ⟨1374392, by decide⟩ ⟨11, 2, 0, 1374392, 100935, 3409, 262144⟩
    (by decide) selected_cut_48843

theorem unmarked_context_10_25233_1374393 : frontier 11 ⟨1374393, by decide⟩
    (prefixCache 10 25233) (prefixPartial 10 25233) = false := by
  decide +kernel

theorem node_context_10_25233_1374393 : EJMOriginalGlobalDAGData.nodes 11 ⟨1374393, by decide⟩ =
    .split (coordinate 10) (![⟨1374145, by decide⟩,⟨1374215, by decide⟩,⟨1374304, by decide⟩,⟨1374392, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25233_1374393 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25233 ⟨1374393, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25233
    ⟨1374393, by decide⟩ (by decide) (![⟨1374145, by decide⟩,⟨1374215, by decide⟩,⟨1374304, by decide⟩,⟨1374392, by decide⟩]) unmarked_context_10_25233_1374393 node_context_10_25233_1374393
  intro a
  fin_cases a
  · exact context_11_100932_1374145
  · exact context_11_100933_1374215
  · exact context_11_100934_1374304
  · exact context_11_100935_1374392

theorem selected_cut_48844 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 403744) = some ⟨12, 1, 0, 1108174, 403744, 1, 65536⟩ := by
  decide +kernel

theorem context_12_403744_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 403744 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 403744 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 403744, 1, 65536⟩
    (by decide) selected_cut_48844

theorem selected_cut_48845 : selected 9 ⟨1374449, by decide⟩
    (prefixPartial 12 403745) = some ⟨12, 2, 0, 1374449, 403745, 1661, 65536⟩ := by
  decide +kernel

theorem context_12_403745_1374449 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 403745 ⟨1374449, by decide⟩ :=
  accepted_of_selected 12 403745 ⟨1374449, by decide⟩ ⟨12, 2, 0, 1374449, 403745, 1661, 65536⟩
    (by decide) selected_cut_48845

theorem selected_cut_48846 : selected 9 ⟨1374486, by decide⟩
    (prefixPartial 12 403746) = some ⟨12, 2, 0, 1374486, 403746, 1401, 65536⟩ := by
  decide +kernel

theorem context_12_403746_1374486 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 403746 ⟨1374486, by decide⟩ :=
  accepted_of_selected 12 403746 ⟨1374486, by decide⟩ ⟨12, 2, 0, 1374486, 403746, 1401, 65536⟩
    (by decide) selected_cut_48846

theorem selected_cut_48847 : selected 9 ⟨1374524, by decide⟩
    (prefixPartial 12 403747) = some ⟨12, 2, 0, 1374524, 403747, 1465, 65536⟩ := by
  decide +kernel

theorem context_12_403747_1374524 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 403747 ⟨1374524, by decide⟩ :=
  accepted_of_selected 12 403747 ⟨1374524, by decide⟩ ⟨12, 2, 0, 1374524, 403747, 1465, 65536⟩
    (by decide) selected_cut_48847

theorem unmarked_context_11_100936_1374525 : frontier 10 ⟨1374525, by decide⟩
    (prefixCache 11 100936) (prefixPartial 11 100936) = false := by
  decide +kernel

theorem node_context_11_100936_1374525 : EJMOriginalGlobalDAGData.nodes 10 ⟨1374525, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1374449, by decide⟩,⟨1374486, by decide⟩,⟨1374524, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_100936_1374525 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100936 ⟨1374525, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 100936
    ⟨1374525, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1374449, by decide⟩,⟨1374486, by decide⟩,⟨1374524, by decide⟩]) unmarked_context_11_100936_1374525 node_context_11_100936_1374525
  intro a
  fin_cases a
  · exact context_12_403744_1108174
  · exact context_12_403745_1374449
  · exact context_12_403746_1374486
  · exact context_12_403747_1374524

theorem selected_cut_48848 : selected 10 ⟨1374612, by decide⟩
    (prefixPartial 11 100937) = some ⟨11, 2, 0, 1374612, 100937, 2993, 262144⟩ := by
  decide +kernel

theorem context_11_100937_1374612 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100937 ⟨1374612, by decide⟩ :=
  accepted_of_selected 11 100937 ⟨1374612, by decide⟩ ⟨11, 2, 0, 1374612, 100937, 2993, 262144⟩
    (by decide) selected_cut_48848

theorem selected_cut_48849 : selected 10 ⟨900587, by decide⟩
    (prefixPartial 11 100938) = some ⟨11, 1, 0, 900587, 100938, 1, 262144⟩ := by
  decide +kernel

theorem context_11_100938_900587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100938 ⟨900587, by decide⟩ :=
  accepted_of_selected 11 100938 ⟨900587, by decide⟩ ⟨11, 1, 0, 900587, 100938, 1, 262144⟩
    (by decide) selected_cut_48849

theorem selected_cut_48850 : selected 10 ⟨1374710, by decide⟩
    (prefixPartial 11 100939) = some ⟨11, 2, 0, 1374710, 100939, 3845, 262144⟩ := by
  decide +kernel

theorem context_11_100939_1374710 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100939 ⟨1374710, by decide⟩ :=
  accepted_of_selected 11 100939 ⟨1374710, by decide⟩ ⟨11, 2, 0, 1374710, 100939, 3845, 262144⟩
    (by decide) selected_cut_48850

theorem unmarked_context_10_25234_1374711 : frontier 11 ⟨1374711, by decide⟩
    (prefixCache 10 25234) (prefixPartial 10 25234) = false := by
  decide +kernel

theorem node_context_10_25234_1374711 : EJMOriginalGlobalDAGData.nodes 11 ⟨1374711, by decide⟩ =
    .split (coordinate 10) (![⟨1374525, by decide⟩,⟨1374612, by decide⟩,⟨900587, by decide⟩,⟨1374710, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25234_1374711 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25234 ⟨1374711, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25234
    ⟨1374711, by decide⟩ (by decide) (![⟨1374525, by decide⟩,⟨1374612, by decide⟩,⟨900587, by decide⟩,⟨1374710, by decide⟩]) unmarked_context_10_25234_1374711 node_context_10_25234_1374711
  intro a
  fin_cases a
  · exact context_11_100936_1374525
  · exact context_11_100937_1374612
  · exact context_11_100938_900587
  · exact context_11_100939_1374710

theorem selected_cut_48851 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 403760) = some ⟨12, 1, 0, 1108174, 403760, 1, 65536⟩ := by
  decide +kernel

theorem context_12_403760_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 403760 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 403760 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 403760, 1, 65536⟩
    (by decide) selected_cut_48851

theorem selected_cut_48852 : selected 9 ⟨1374784, by decide⟩
    (prefixPartial 12 403761) = some ⟨12, 2, 0, 1374784, 403761, 1833, 65536⟩ := by
  decide +kernel

theorem context_12_403761_1374784 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 403761 ⟨1374784, by decide⟩ :=
  accepted_of_selected 12 403761 ⟨1374784, by decide⟩ ⟨12, 2, 0, 1374784, 403761, 1833, 65536⟩
    (by decide) selected_cut_48852

theorem selected_cut_48853 : selected 9 ⟨1374825, by decide⟩
    (prefixPartial 12 403762) = some ⟨12, 2, 0, 1374825, 403762, 1437, 65536⟩ := by
  decide +kernel

theorem context_12_403762_1374825 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 403762 ⟨1374825, by decide⟩ :=
  accepted_of_selected 12 403762 ⟨1374825, by decide⟩ ⟨12, 2, 0, 1374825, 403762, 1437, 65536⟩
    (by decide) selected_cut_48853

theorem selected_cut_48854 : selected 9 ⟨1374886, by decide⟩
    (prefixPartial 12 403763) = some ⟨12, 2, 0, 1374886, 403763, 1657, 65536⟩ := by
  decide +kernel

theorem context_12_403763_1374886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 403763 ⟨1374886, by decide⟩ :=
  accepted_of_selected 12 403763 ⟨1374886, by decide⟩ ⟨12, 2, 0, 1374886, 403763, 1657, 65536⟩
    (by decide) selected_cut_48854

theorem unmarked_context_11_100940_1374887 : frontier 10 ⟨1374887, by decide⟩
    (prefixCache 11 100940) (prefixPartial 11 100940) = false := by
  decide +kernel

theorem node_context_11_100940_1374887 : EJMOriginalGlobalDAGData.nodes 10 ⟨1374887, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1374784, by decide⟩,⟨1374825, by decide⟩,⟨1374886, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_100940_1374887 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100940 ⟨1374887, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 100940
    ⟨1374887, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1374784, by decide⟩,⟨1374825, by decide⟩,⟨1374886, by decide⟩]) unmarked_context_11_100940_1374887 node_context_11_100940_1374887
  intro a
  fin_cases a
  · exact context_12_403760_1108174
  · exact context_12_403761_1374784
  · exact context_12_403762_1374825
  · exact context_12_403763_1374886

theorem selected_cut_48855 : selected 10 ⟨1374967, by decide⟩
    (prefixPartial 11 100941) = some ⟨11, 2, 0, 1374967, 100941, 2793, 262144⟩ := by
  decide +kernel

theorem context_11_100941_1374967 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100941 ⟨1374967, by decide⟩ :=
  accepted_of_selected 11 100941 ⟨1374967, by decide⟩ ⟨11, 2, 0, 1374967, 100941, 2793, 262144⟩
    (by decide) selected_cut_48855

theorem selected_cut_48856 : selected 10 ⟨1375025, by decide⟩
    (prefixPartial 11 100942) = some ⟨11, 2, 0, 1375025, 100942, 793, 262144⟩ := by
  decide +kernel

theorem context_11_100942_1375025 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100942 ⟨1375025, by decide⟩ :=
  accepted_of_selected 11 100942 ⟨1375025, by decide⟩ ⟨11, 2, 0, 1375025, 100942, 793, 262144⟩
    (by decide) selected_cut_48856

theorem selected_cut_48857 : selected 10 ⟨1375054, by decide⟩
    (prefixPartial 11 100943) = some ⟨11, 2, 0, 1375054, 100943, 1121, 262144⟩ := by
  decide +kernel

theorem context_11_100943_1375054 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100943 ⟨1375054, by decide⟩ :=
  accepted_of_selected 11 100943 ⟨1375054, by decide⟩ ⟨11, 2, 0, 1375054, 100943, 1121, 262144⟩
    (by decide) selected_cut_48857

theorem unmarked_context_10_25235_1375055 : frontier 11 ⟨1375055, by decide⟩
    (prefixCache 10 25235) (prefixPartial 10 25235) = false := by
  decide +kernel

theorem node_context_10_25235_1375055 : EJMOriginalGlobalDAGData.nodes 11 ⟨1375055, by decide⟩ =
    .split (coordinate 10) (![⟨1374887, by decide⟩,⟨1374967, by decide⟩,⟨1375025, by decide⟩,⟨1375054, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25235_1375055 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25235 ⟨1375055, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25235
    ⟨1375055, by decide⟩ (by decide) (![⟨1374887, by decide⟩,⟨1374967, by decide⟩,⟨1375025, by decide⟩,⟨1375054, by decide⟩]) unmarked_context_10_25235_1375055 node_context_10_25235_1375055
  intro a
  fin_cases a
  · exact context_11_100940_1374887
  · exact context_11_100941_1374967
  · exact context_11_100942_1375025
  · exact context_11_100943_1375054

theorem unmarked_context_9_6308_1375056 : frontier 12 ⟨1375056, by decide⟩
    (prefixCache 9 6308) (prefixPartial 9 6308) = false := by
  decide +kernel

theorem node_context_9_6308_1375056 : EJMOriginalGlobalDAGData.nodes 12 ⟨1375056, by decide⟩ =
    .split (coordinate 9) (![⟨1373918, by decide⟩,⟨1374393, by decide⟩,⟨1374711, by decide⟩,⟨1375055, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6308_1375056 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6308 ⟨1375056, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6308
    ⟨1375056, by decide⟩ (by decide) (![⟨1373918, by decide⟩,⟨1374393, by decide⟩,⟨1374711, by decide⟩,⟨1375055, by decide⟩]) unmarked_context_9_6308_1375056 node_context_9_6308_1375056
  intro a
  fin_cases a
  · exact context_10_25232_1373918
  · exact context_10_25233_1374393
  · exact context_10_25234_1374711
  · exact context_10_25235_1375055

theorem selected_cut_48858 : selected 10 ⟨1375137, by decide⟩
    (prefixPartial 11 100944) = some ⟨11, 2, 0, 1375137, 100944, 1133, 262144⟩ := by
  decide +kernel

theorem context_11_100944_1375137 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100944 ⟨1375137, by decide⟩ :=
  accepted_of_selected 11 100944 ⟨1375137, by decide⟩ ⟨11, 2, 0, 1375137, 100944, 1133, 262144⟩
    (by decide) selected_cut_48858

theorem selected_cut_48859 : selected 10 ⟨1375263, by decide⟩
    (prefixPartial 11 100945) = some ⟨11, 2, 0, 1375263, 100945, 2581, 262144⟩ := by
  decide +kernel

theorem context_11_100945_1375263 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100945 ⟨1375263, by decide⟩ :=
  accepted_of_selected 11 100945 ⟨1375263, by decide⟩ ⟨11, 2, 0, 1375263, 100945, 2581, 262144⟩
    (by decide) selected_cut_48859

theorem selected_cut_48860 : selected 10 ⟨1375264, by decide⟩
    (prefixPartial 11 100946) = some ⟨11, 1, 0, 1375264, 100946, 1, 262144⟩ := by
  decide +kernel

theorem context_11_100946_1375264 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100946 ⟨1375264, by decide⟩ :=
  accepted_of_selected 11 100946 ⟨1375264, by decide⟩ ⟨11, 1, 0, 1375264, 100946, 1, 262144⟩
    (by decide) selected_cut_48860

theorem selected_cut_48861 : selected 10 ⟨1375325, by decide⟩
    (prefixPartial 11 100947) = some ⟨11, 2, 0, 1375325, 100947, 1741, 262144⟩ := by
  decide +kernel

theorem context_11_100947_1375325 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100947 ⟨1375325, by decide⟩ :=
  accepted_of_selected 11 100947 ⟨1375325, by decide⟩ ⟨11, 2, 0, 1375325, 100947, 1741, 262144⟩
    (by decide) selected_cut_48861

theorem unmarked_context_10_25236_1375326 : frontier 11 ⟨1375326, by decide⟩
    (prefixCache 10 25236) (prefixPartial 10 25236) = false := by
  decide +kernel

theorem node_context_10_25236_1375326 : EJMOriginalGlobalDAGData.nodes 11 ⟨1375326, by decide⟩ =
    .split (coordinate 10) (![⟨1375137, by decide⟩,⟨1375263, by decide⟩,⟨1375264, by decide⟩,⟨1375325, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25236_1375326 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25236 ⟨1375326, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25236
    ⟨1375326, by decide⟩ (by decide) (![⟨1375137, by decide⟩,⟨1375263, by decide⟩,⟨1375264, by decide⟩,⟨1375325, by decide⟩]) unmarked_context_10_25236_1375326 node_context_10_25236_1375326
  intro a
  fin_cases a
  · exact context_11_100944_1375137
  · exact context_11_100945_1375263
  · exact context_11_100946_1375264
  · exact context_11_100947_1375325

theorem selected_cut_48862 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 25237) = some ⟨10, 1, 0, 893098, 25237, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_25237_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25237 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 25237 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 25237, 1, 1048576⟩
    (by decide) selected_cut_48862

theorem selected_cut_48863 : selected 10 ⟨1375389, by decide⟩
    (prefixPartial 11 100952) = some ⟨11, 2, 0, 1375389, 100952, 1617, 262144⟩ := by
  decide +kernel

theorem context_11_100952_1375389 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100952 ⟨1375389, by decide⟩ :=
  accepted_of_selected 11 100952 ⟨1375389, by decide⟩ ⟨11, 2, 0, 1375389, 100952, 1617, 262144⟩
    (by decide) selected_cut_48863

theorem selected_cut_48864 : selected 10 ⟨1375461, by decide⟩
    (prefixPartial 11 100953) = some ⟨11, 2, 0, 1375461, 100953, 1301, 262144⟩ := by
  decide +kernel

theorem context_11_100953_1375461 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100953 ⟨1375461, by decide⟩ :=
  accepted_of_selected 11 100953 ⟨1375461, by decide⟩ ⟨11, 2, 0, 1375461, 100953, 1301, 262144⟩
    (by decide) selected_cut_48864

theorem selected_cut_48865 : selected 10 ⟨1375264, by decide⟩
    (prefixPartial 11 100954) = some ⟨11, 1, 0, 1375264, 100954, 1, 262144⟩ := by
  decide +kernel

theorem context_11_100954_1375264 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100954 ⟨1375264, by decide⟩ :=
  accepted_of_selected 11 100954 ⟨1375264, by decide⟩ ⟨11, 1, 0, 1375264, 100954, 1, 262144⟩
    (by decide) selected_cut_48865

theorem selected_cut_48866 : selected 10 ⟨1375532, by decide⟩
    (prefixPartial 11 100955) = some ⟨11, 2, 0, 1375532, 100955, 2013, 262144⟩ := by
  decide +kernel

theorem context_11_100955_1375532 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100955 ⟨1375532, by decide⟩ :=
  accepted_of_selected 11 100955 ⟨1375532, by decide⟩ ⟨11, 2, 0, 1375532, 100955, 2013, 262144⟩
    (by decide) selected_cut_48866

theorem unmarked_context_10_25238_1375533 : frontier 11 ⟨1375533, by decide⟩
    (prefixCache 10 25238) (prefixPartial 10 25238) = false := by
  decide +kernel

theorem node_context_10_25238_1375533 : EJMOriginalGlobalDAGData.nodes 11 ⟨1375533, by decide⟩ =
    .split (coordinate 10) (![⟨1375389, by decide⟩,⟨1375461, by decide⟩,⟨1375264, by decide⟩,⟨1375532, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25238_1375533 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25238 ⟨1375533, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25238
    ⟨1375533, by decide⟩ (by decide) (![⟨1375389, by decide⟩,⟨1375461, by decide⟩,⟨1375264, by decide⟩,⟨1375532, by decide⟩]) unmarked_context_10_25238_1375533 node_context_10_25238_1375533
  intro a
  fin_cases a
  · exact context_11_100952_1375389
  · exact context_11_100953_1375461
  · exact context_11_100954_1375264
  · exact context_11_100955_1375532

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
