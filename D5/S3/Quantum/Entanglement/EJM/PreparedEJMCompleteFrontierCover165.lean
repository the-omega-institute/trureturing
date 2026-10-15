/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover164
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_15844 : selected 8 ⟨405136, by decide⟩
    (prefixPartial 13 111847) = some ⟨13, 2, 0, 405136, 111847, 925, 16384⟩ := by
  decide +kernel

theorem context_13_111847_405136 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111847 ⟨405136, by decide⟩ :=
  accepted_of_selected 13 111847 ⟨405136, by decide⟩ ⟨13, 2, 0, 405136, 111847, 925, 16384⟩
    (by decide) selected_cut_15844

theorem unmarked_context_12_27961_405137 : frontier 9 ⟨405137, by decide⟩
    (prefixCache 12 27961) (prefixPartial 12 27961) = false := by
  decide +kernel

theorem node_context_12_27961_405137 : EJMOriginalGlobalDAGData.nodes 9 ⟨405137, by decide⟩ =
    .split (coordinate 12) (![⟨405087, by decide⟩,⟨405110, by decide⟩,⟨405130, by decide⟩,⟨405136, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27961_405137 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27961 ⟨405137, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27961
    ⟨405137, by decide⟩ (by decide) (![⟨405087, by decide⟩,⟨405110, by decide⟩,⟨405130, by decide⟩,⟨405136, by decide⟩]) unmarked_context_12_27961_405137 node_context_12_27961_405137
  intro a
  fin_cases a
  · exact context_13_111844_405087
  · exact context_13_111845_405110
  · exact context_13_111846_405130
  · exact context_13_111847_405136

theorem selected_cut_15845 : selected 8 ⟨405144, by decide⟩
    (prefixPartial 13 111848) = some ⟨13, 2, 0, 405144, 111848, 397, 16384⟩ := by
  decide +kernel

theorem context_13_111848_405144 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111848 ⟨405144, by decide⟩ :=
  accepted_of_selected 13 111848 ⟨405144, by decide⟩ ⟨13, 2, 0, 405144, 111848, 397, 16384⟩
    (by decide) selected_cut_15845

theorem selected_cut_15846 : selected 8 ⟨405177, by decide⟩
    (prefixPartial 13 111849) = some ⟨13, 2, 0, 405177, 111849, 2669, 16384⟩ := by
  decide +kernel

theorem context_13_111849_405177 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111849 ⟨405177, by decide⟩ :=
  accepted_of_selected 13 111849 ⟨405177, by decide⟩ ⟨13, 2, 0, 405177, 111849, 2669, 16384⟩
    (by decide) selected_cut_15846

theorem selected_cut_15847 : selected 8 ⟨405199, by decide⟩
    (prefixPartial 13 111850) = some ⟨13, 2, 0, 405199, 111850, 1729, 16384⟩ := by
  decide +kernel

theorem context_13_111850_405199 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111850 ⟨405199, by decide⟩ :=
  accepted_of_selected 13 111850 ⟨405199, by decide⟩ ⟨13, 2, 0, 405199, 111850, 1729, 16384⟩
    (by decide) selected_cut_15847

theorem selected_cut_15848 : selected 8 ⟨405206, by decide⟩
    (prefixPartial 13 111851) = some ⟨13, 2, 0, 405206, 111851, 929, 16384⟩ := by
  decide +kernel

theorem context_13_111851_405206 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111851 ⟨405206, by decide⟩ :=
  accepted_of_selected 13 111851 ⟨405206, by decide⟩ ⟨13, 2, 0, 405206, 111851, 929, 16384⟩
    (by decide) selected_cut_15848

theorem unmarked_context_12_27962_405207 : frontier 9 ⟨405207, by decide⟩
    (prefixCache 12 27962) (prefixPartial 12 27962) = false := by
  decide +kernel

theorem node_context_12_27962_405207 : EJMOriginalGlobalDAGData.nodes 9 ⟨405207, by decide⟩ =
    .split (coordinate 12) (![⟨405144, by decide⟩,⟨405177, by decide⟩,⟨405199, by decide⟩,⟨405206, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27962_405207 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27962 ⟨405207, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27962
    ⟨405207, by decide⟩ (by decide) (![⟨405144, by decide⟩,⟨405177, by decide⟩,⟨405199, by decide⟩,⟨405206, by decide⟩]) unmarked_context_12_27962_405207 node_context_12_27962_405207
  intro a
  fin_cases a
  · exact context_13_111848_405144
  · exact context_13_111849_405177
  · exact context_13_111850_405199
  · exact context_13_111851_405206

theorem selected_cut_15849 : selected 8 ⟨405216, by decide⟩
    (prefixPartial 13 111852) = some ⟨13, 2, 0, 405216, 111852, 401, 16384⟩ := by
  decide +kernel

theorem context_13_111852_405216 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111852 ⟨405216, by decide⟩ :=
  accepted_of_selected 13 111852 ⟨405216, by decide⟩ ⟨13, 2, 0, 405216, 111852, 401, 16384⟩
    (by decide) selected_cut_15849

theorem selected_cut_15850 : selected 8 ⟨405258, by decide⟩
    (prefixPartial 13 111853) = some ⟨13, 2, 0, 405258, 111853, 3125, 16384⟩ := by
  decide +kernel

theorem context_13_111853_405258 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111853 ⟨405258, by decide⟩ :=
  accepted_of_selected 13 111853 ⟨405258, by decide⟩ ⟨13, 2, 0, 405258, 111853, 3125, 16384⟩
    (by decide) selected_cut_15850

theorem selected_cut_15851 : selected 8 ⟨405279, by decide⟩
    (prefixPartial 13 111854) = some ⟨13, 2, 0, 405279, 111854, 1917, 16384⟩ := by
  decide +kernel

theorem context_13_111854_405279 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111854 ⟨405279, by decide⟩ :=
  accepted_of_selected 13 111854 ⟨405279, by decide⟩ ⟨13, 2, 0, 405279, 111854, 1917, 16384⟩
    (by decide) selected_cut_15851

theorem selected_cut_15852 : selected 8 ⟨405285, by decide⟩
    (prefixPartial 13 111855) = some ⟨13, 2, 0, 405285, 111855, 973, 16384⟩ := by
  decide +kernel

theorem context_13_111855_405285 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111855 ⟨405285, by decide⟩ :=
  accepted_of_selected 13 111855 ⟨405285, by decide⟩ ⟨13, 2, 0, 405285, 111855, 973, 16384⟩
    (by decide) selected_cut_15852

theorem unmarked_context_12_27963_405286 : frontier 9 ⟨405286, by decide⟩
    (prefixCache 12 27963) (prefixPartial 12 27963) = false := by
  decide +kernel

theorem node_context_12_27963_405286 : EJMOriginalGlobalDAGData.nodes 9 ⟨405286, by decide⟩ =
    .split (coordinate 12) (![⟨405216, by decide⟩,⟨405258, by decide⟩,⟨405279, by decide⟩,⟨405285, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27963_405286 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27963 ⟨405286, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27963
    ⟨405286, by decide⟩ (by decide) (![⟨405216, by decide⟩,⟨405258, by decide⟩,⟨405279, by decide⟩,⟨405285, by decide⟩]) unmarked_context_12_27963_405286 node_context_12_27963_405286
  intro a
  fin_cases a
  · exact context_13_111852_405216
  · exact context_13_111853_405258
  · exact context_13_111854_405279
  · exact context_13_111855_405285

theorem unmarked_context_11_6990_405287 : frontier 10 ⟨405287, by decide⟩
    (prefixCache 11 6990) (prefixPartial 11 6990) = false := by
  decide +kernel

theorem node_context_11_6990_405287 : EJMOriginalGlobalDAGData.nodes 10 ⟨405287, by decide⟩ =
    .split (coordinate 11) (![⟨405081, by decide⟩,⟨405137, by decide⟩,⟨405207, by decide⟩,⟨405286, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6990_405287 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6990 ⟨405287, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6990
    ⟨405287, by decide⟩ (by decide) (![⟨405081, by decide⟩,⟨405137, by decide⟩,⟨405207, by decide⟩,⟨405286, by decide⟩]) unmarked_context_11_6990_405287 node_context_11_6990_405287
  intro a
  fin_cases a
  · exact context_12_27960_405081
  · exact context_12_27961_405137
  · exact context_12_27962_405207
  · exact context_12_27963_405286

theorem selected_cut_15853 : selected 8 ⟨405291, by decide⟩
    (prefixPartial 13 111856) = some ⟨13, 2, 0, 405291, 111856, 237, 16384⟩ := by
  decide +kernel

theorem context_13_111856_405291 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111856 ⟨405291, by decide⟩ :=
  accepted_of_selected 13 111856 ⟨405291, by decide⟩ ⟨13, 2, 0, 405291, 111856, 237, 16384⟩
    (by decide) selected_cut_15853

theorem selected_cut_15854 : selected 8 ⟨405340, by decide⟩
    (prefixPartial 13 111857) = some ⟨13, 2, 0, 405340, 111857, 3365, 16384⟩ := by
  decide +kernel

theorem context_13_111857_405340 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111857 ⟨405340, by decide⟩ :=
  accepted_of_selected 13 111857 ⟨405340, by decide⟩ ⟨13, 2, 0, 405340, 111857, 3365, 16384⟩
    (by decide) selected_cut_15854

theorem selected_cut_15855 : selected 8 ⟨405361, by decide⟩
    (prefixPartial 13 111858) = some ⟨13, 2, 0, 405361, 111858, 1961, 16384⟩ := by
  decide +kernel

theorem context_13_111858_405361 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111858 ⟨405361, by decide⟩ :=
  accepted_of_selected 13 111858 ⟨405361, by decide⟩ ⟨13, 2, 0, 405361, 111858, 1961, 16384⟩
    (by decide) selected_cut_15855

theorem selected_cut_15856 : selected 8 ⟨405367, by decide⟩
    (prefixPartial 13 111859) = some ⟨13, 2, 0, 405367, 111859, 1081, 16384⟩ := by
  decide +kernel

theorem context_13_111859_405367 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111859 ⟨405367, by decide⟩ :=
  accepted_of_selected 13 111859 ⟨405367, by decide⟩ ⟨13, 2, 0, 405367, 111859, 1081, 16384⟩
    (by decide) selected_cut_15856

theorem unmarked_context_12_27964_405368 : frontier 9 ⟨405368, by decide⟩
    (prefixCache 12 27964) (prefixPartial 12 27964) = false := by
  decide +kernel

theorem node_context_12_27964_405368 : EJMOriginalGlobalDAGData.nodes 9 ⟨405368, by decide⟩ =
    .split (coordinate 12) (![⟨405291, by decide⟩,⟨405340, by decide⟩,⟨405361, by decide⟩,⟨405367, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27964_405368 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27964 ⟨405368, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27964
    ⟨405368, by decide⟩ (by decide) (![⟨405291, by decide⟩,⟨405340, by decide⟩,⟨405361, by decide⟩,⟨405367, by decide⟩]) unmarked_context_12_27964_405368 node_context_12_27964_405368
  intro a
  fin_cases a
  · exact context_13_111856_405291
  · exact context_13_111857_405340
  · exact context_13_111858_405361
  · exact context_13_111859_405367

theorem selected_cut_15857 : selected 8 ⟨405371, by decide⟩
    (prefixPartial 13 111860) = some ⟨13, 2, 0, 405371, 111860, 145, 16384⟩ := by
  decide +kernel

theorem context_13_111860_405371 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111860 ⟨405371, by decide⟩ :=
  accepted_of_selected 13 111860 ⟨405371, by decide⟩ ⟨13, 2, 0, 405371, 111860, 145, 16384⟩
    (by decide) selected_cut_15857

theorem selected_cut_15858 : selected 8 ⟨405402, by decide⟩
    (prefixPartial 13 111861) = some ⟨13, 2, 0, 405402, 111861, 3069, 16384⟩ := by
  decide +kernel

theorem context_13_111861_405402 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111861 ⟨405402, by decide⟩ :=
  accepted_of_selected 13 111861 ⟨405402, by decide⟩ ⟨13, 2, 0, 405402, 111861, 3069, 16384⟩
    (by decide) selected_cut_15858

theorem selected_cut_15859 : selected 8 ⟨405429, by decide⟩
    (prefixPartial 13 111862) = some ⟨13, 2, 0, 405429, 111862, 2121, 16384⟩ := by
  decide +kernel

theorem context_13_111862_405429 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111862 ⟨405429, by decide⟩ :=
  accepted_of_selected 13 111862 ⟨405429, by decide⟩ ⟨13, 2, 0, 405429, 111862, 2121, 16384⟩
    (by decide) selected_cut_15859

theorem selected_cut_15860 : selected 8 ⟨405433, by decide⟩
    (prefixPartial 13 111863) = some ⟨13, 2, 0, 405433, 111863, 1101, 16384⟩ := by
  decide +kernel

theorem context_13_111863_405433 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111863 ⟨405433, by decide⟩ :=
  accepted_of_selected 13 111863 ⟨405433, by decide⟩ ⟨13, 2, 0, 405433, 111863, 1101, 16384⟩
    (by decide) selected_cut_15860

theorem unmarked_context_12_27965_405434 : frontier 9 ⟨405434, by decide⟩
    (prefixCache 12 27965) (prefixPartial 12 27965) = false := by
  decide +kernel

theorem node_context_12_27965_405434 : EJMOriginalGlobalDAGData.nodes 9 ⟨405434, by decide⟩ =
    .split (coordinate 12) (![⟨405371, by decide⟩,⟨405402, by decide⟩,⟨405429, by decide⟩,⟨405433, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27965_405434 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27965 ⟨405434, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27965
    ⟨405434, by decide⟩ (by decide) (![⟨405371, by decide⟩,⟨405402, by decide⟩,⟨405429, by decide⟩,⟨405433, by decide⟩]) unmarked_context_12_27965_405434 node_context_12_27965_405434
  intro a
  fin_cases a
  · exact context_13_111860_405371
  · exact context_13_111861_405402
  · exact context_13_111862_405429
  · exact context_13_111863_405433

theorem selected_cut_15861 : selected 8 ⟨405438, by decide⟩
    (prefixPartial 13 111864) = some ⟨13, 2, 0, 405438, 111864, 117, 16384⟩ := by
  decide +kernel

theorem context_13_111864_405438 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111864 ⟨405438, by decide⟩ :=
  accepted_of_selected 13 111864 ⟨405438, by decide⟩ ⟨13, 2, 0, 405438, 111864, 117, 16384⟩
    (by decide) selected_cut_15861

theorem selected_cut_15862 : selected 8 ⟨405500, by decide⟩
    (prefixPartial 13 111865) = some ⟨13, 2, 0, 405500, 111865, 3697, 16384⟩ := by
  decide +kernel

theorem context_13_111865_405500 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111865 ⟨405500, by decide⟩ :=
  accepted_of_selected 13 111865 ⟨405500, by decide⟩ ⟨13, 2, 0, 405500, 111865, 3697, 16384⟩
    (by decide) selected_cut_15862

theorem selected_cut_15863 : selected 8 ⟨405529, by decide⟩
    (prefixPartial 13 111866) = some ⟨13, 2, 0, 405529, 111866, 2081, 16384⟩ := by
  decide +kernel

theorem context_13_111866_405529 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111866 ⟨405529, by decide⟩ :=
  accepted_of_selected 13 111866 ⟨405529, by decide⟩ ⟨13, 2, 0, 405529, 111866, 2081, 16384⟩
    (by decide) selected_cut_15863

theorem selected_cut_15864 : selected 8 ⟨405543, by decide⟩
    (prefixPartial 13 111867) = some ⟨13, 2, 0, 405543, 111867, 1153, 16384⟩ := by
  decide +kernel

theorem context_13_111867_405543 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111867 ⟨405543, by decide⟩ :=
  accepted_of_selected 13 111867 ⟨405543, by decide⟩ ⟨13, 2, 0, 405543, 111867, 1153, 16384⟩
    (by decide) selected_cut_15864

theorem unmarked_context_12_27966_405544 : frontier 9 ⟨405544, by decide⟩
    (prefixCache 12 27966) (prefixPartial 12 27966) = false := by
  decide +kernel

theorem node_context_12_27966_405544 : EJMOriginalGlobalDAGData.nodes 9 ⟨405544, by decide⟩ =
    .split (coordinate 12) (![⟨405438, by decide⟩,⟨405500, by decide⟩,⟨405529, by decide⟩,⟨405543, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27966_405544 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27966 ⟨405544, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27966
    ⟨405544, by decide⟩ (by decide) (![⟨405438, by decide⟩,⟨405500, by decide⟩,⟨405529, by decide⟩,⟨405543, by decide⟩]) unmarked_context_12_27966_405544 node_context_12_27966_405544
  intro a
  fin_cases a
  · exact context_13_111864_405438
  · exact context_13_111865_405500
  · exact context_13_111866_405529
  · exact context_13_111867_405543

theorem selected_cut_15865 : selected 9 ⟨405545, by decide⟩
    (prefixPartial 12 27967) = some ⟨12, 1, 0, 405545, 27967, 1, 65536⟩ := by
  decide +kernel

theorem context_12_27967_405545 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27967 ⟨405545, by decide⟩ :=
  accepted_of_selected 12 27967 ⟨405545, by decide⟩ ⟨12, 1, 0, 405545, 27967, 1, 65536⟩
    (by decide) selected_cut_15865

theorem unmarked_context_11_6991_405546 : frontier 10 ⟨405546, by decide⟩
    (prefixCache 11 6991) (prefixPartial 11 6991) = false := by
  decide +kernel

theorem node_context_11_6991_405546 : EJMOriginalGlobalDAGData.nodes 10 ⟨405546, by decide⟩ =
    .split (coordinate 11) (![⟨405368, by decide⟩,⟨405434, by decide⟩,⟨405544, by decide⟩,⟨405545, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6991_405546 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6991 ⟨405546, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6991
    ⟨405546, by decide⟩ (by decide) (![⟨405368, by decide⟩,⟨405434, by decide⟩,⟨405544, by decide⟩,⟨405545, by decide⟩]) unmarked_context_11_6991_405546 node_context_11_6991_405546
  intro a
  fin_cases a
  · exact context_12_27964_405368
  · exact context_12_27965_405434
  · exact context_12_27966_405544
  · exact context_12_27967_405545

theorem unmarked_context_10_1747_405547 : frontier 11 ⟨405547, by decide⟩
    (prefixCache 10 1747) (prefixPartial 10 1747) = false := by
  decide +kernel

theorem node_context_10_1747_405547 : EJMOriginalGlobalDAGData.nodes 11 ⟨405547, by decide⟩ =
    .split (coordinate 10) (![⟨404739, by decide⟩,⟨405017, by decide⟩,⟨405287, by decide⟩,⟨405546, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1747_405547 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1747 ⟨405547, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1747
    ⟨405547, by decide⟩ (by decide) (![⟨404739, by decide⟩,⟨405017, by decide⟩,⟨405287, by decide⟩,⟨405546, by decide⟩]) unmarked_context_10_1747_405547 node_context_10_1747_405547
  intro a
  fin_cases a
  · exact context_11_6988_404739
  · exact context_11_6989_405017
  · exact context_11_6990_405287
  · exact context_11_6991_405546

theorem unmarked_context_9_436_405548 : frontier 12 ⟨405548, by decide⟩
    (prefixCache 9 436) (prefixPartial 9 436) = false := by
  decide +kernel

theorem node_context_9_436_405548 : EJMOriginalGlobalDAGData.nodes 12 ⟨405548, by decide⟩ =
    .split (coordinate 9) (![⟨401841, by decide⟩,⟨403144, by decide⟩,⟨404424, by decide⟩,⟨405547, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_436_405548 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 436 ⟨405548, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 436
    ⟨405548, by decide⟩ (by decide) (![⟨401841, by decide⟩,⟨403144, by decide⟩,⟨404424, by decide⟩,⟨405547, by decide⟩]) unmarked_context_9_436_405548 node_context_9_436_405548
  intro a
  fin_cases a
  · exact context_10_1744_401841
  · exact context_10_1745_403144
  · exact context_10_1746_404424
  · exact context_10_1747_405547

theorem selected_cut_15866 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 111872) = some ⟨13, 1, 0, 3444, 111872, 1, 16384⟩ := by
  decide +kernel

theorem context_13_111872_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111872 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 111872 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 111872, 1, 16384⟩
    (by decide) selected_cut_15866

theorem selected_cut_15867 : selected 8 ⟨405576, by decide⟩
    (prefixPartial 13 111873) = some ⟨13, 2, 0, 405576, 111873, 2873, 16384⟩ := by
  decide +kernel

theorem context_13_111873_405576 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111873 ⟨405576, by decide⟩ :=
  accepted_of_selected 13 111873 ⟨405576, by decide⟩ ⟨13, 2, 0, 405576, 111873, 2873, 16384⟩
    (by decide) selected_cut_15867

theorem selected_cut_15868 : selected 8 ⟨405603, by decide⟩
    (prefixPartial 13 111874) = some ⟨13, 2, 0, 405603, 111874, 2021, 16384⟩ := by
  decide +kernel

theorem context_13_111874_405603 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111874 ⟨405603, by decide⟩ :=
  accepted_of_selected 13 111874 ⟨405603, by decide⟩ ⟨13, 2, 0, 405603, 111874, 2021, 16384⟩
    (by decide) selected_cut_15868

theorem selected_cut_15869 : selected 8 ⟨405612, by decide⟩
    (prefixPartial 13 111875) = some ⟨13, 2, 0, 405612, 111875, 805, 16384⟩ := by
  decide +kernel

theorem context_13_111875_405612 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111875 ⟨405612, by decide⟩ :=
  accepted_of_selected 13 111875 ⟨405612, by decide⟩ ⟨13, 2, 0, 405612, 111875, 805, 16384⟩
    (by decide) selected_cut_15869

theorem unmarked_context_12_27968_405613 : frontier 9 ⟨405613, by decide⟩
    (prefixCache 12 27968) (prefixPartial 12 27968) = false := by
  decide +kernel

theorem node_context_12_27968_405613 : EJMOriginalGlobalDAGData.nodes 9 ⟨405613, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨405576, by decide⟩,⟨405603, by decide⟩,⟨405612, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27968_405613 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27968 ⟨405613, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27968
    ⟨405613, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨405576, by decide⟩,⟨405603, by decide⟩,⟨405612, by decide⟩]) unmarked_context_12_27968_405613 node_context_12_27968_405613
  intro a
  fin_cases a
  · exact context_13_111872_3444
  · exact context_13_111873_405576
  · exact context_13_111874_405603
  · exact context_13_111875_405612

theorem selected_cut_15870 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 111876) = some ⟨13, 1, 0, 3444, 111876, 1, 16384⟩ := by
  decide +kernel

theorem context_13_111876_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111876 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 111876 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 111876, 1, 16384⟩
    (by decide) selected_cut_15870

theorem selected_cut_15871 : selected 8 ⟨405663, by decide⟩
    (prefixPartial 13 111877) = some ⟨13, 2, 0, 405663, 111877, 3421, 16384⟩ := by
  decide +kernel

theorem context_13_111877_405663 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111877 ⟨405663, by decide⟩ :=
  accepted_of_selected 13 111877 ⟨405663, by decide⟩ ⟨13, 2, 0, 405663, 111877, 3421, 16384⟩
    (by decide) selected_cut_15871

theorem selected_cut_15872 : selected 8 ⟨405724, by decide⟩
    (prefixPartial 13 111878) = some ⟨13, 2, 0, 405724, 111878, 3089, 16384⟩ := by
  decide +kernel

theorem context_13_111878_405724 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111878 ⟨405724, by decide⟩ :=
  accepted_of_selected 13 111878 ⟨405724, by decide⟩ ⟨13, 2, 0, 405724, 111878, 3089, 16384⟩
    (by decide) selected_cut_15872

theorem selected_cut_15873 : selected 8 ⟨405742, by decide⟩
    (prefixPartial 13 111879) = some ⟨13, 2, 0, 405742, 111879, 1169, 16384⟩ := by
  decide +kernel

theorem context_13_111879_405742 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111879 ⟨405742, by decide⟩ :=
  accepted_of_selected 13 111879 ⟨405742, by decide⟩ ⟨13, 2, 0, 405742, 111879, 1169, 16384⟩
    (by decide) selected_cut_15873

theorem unmarked_context_12_27969_405743 : frontier 9 ⟨405743, by decide⟩
    (prefixCache 12 27969) (prefixPartial 12 27969) = false := by
  decide +kernel

theorem node_context_12_27969_405743 : EJMOriginalGlobalDAGData.nodes 9 ⟨405743, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨405663, by decide⟩,⟨405724, by decide⟩,⟨405742, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27969_405743 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27969 ⟨405743, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27969
    ⟨405743, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨405663, by decide⟩,⟨405724, by decide⟩,⟨405742, by decide⟩]) unmarked_context_12_27969_405743 node_context_12_27969_405743
  intro a
  fin_cases a
  · exact context_13_111876_3444
  · exact context_13_111877_405663
  · exact context_13_111878_405724
  · exact context_13_111879_405742

theorem selected_cut_15874 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 111880) = some ⟨13, 1, 0, 3444, 111880, 1, 16384⟩ := by
  decide +kernel

theorem context_13_111880_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111880 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 111880 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 111880, 1, 16384⟩
    (by decide) selected_cut_15874

theorem selected_cut_15875 : selected 8 ⟨405768, by decide⟩
    (prefixPartial 13 111881) = some ⟨13, 2, 0, 405768, 111881, 2853, 16384⟩ := by
  decide +kernel

theorem context_13_111881_405768 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111881 ⟨405768, by decide⟩ :=
  accepted_of_selected 13 111881 ⟨405768, by decide⟩ ⟨13, 2, 0, 405768, 111881, 2853, 16384⟩
    (by decide) selected_cut_15875

theorem selected_cut_15876 : selected 8 ⟨405790, by decide⟩
    (prefixPartial 13 111882) = some ⟨13, 2, 0, 405790, 111882, 2317, 16384⟩ := by
  decide +kernel

theorem context_13_111882_405790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111882 ⟨405790, by decide⟩ :=
  accepted_of_selected 13 111882 ⟨405790, by decide⟩ ⟨13, 2, 0, 405790, 111882, 2317, 16384⟩
    (by decide) selected_cut_15876

theorem selected_cut_15877 : selected 8 ⟨405797, by decide⟩
    (prefixPartial 13 111883) = some ⟨13, 2, 0, 405797, 111883, 1009, 16384⟩ := by
  decide +kernel

theorem context_13_111883_405797 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111883 ⟨405797, by decide⟩ :=
  accepted_of_selected 13 111883 ⟨405797, by decide⟩ ⟨13, 2, 0, 405797, 111883, 1009, 16384⟩
    (by decide) selected_cut_15877

theorem unmarked_context_12_27970_405798 : frontier 9 ⟨405798, by decide⟩
    (prefixCache 12 27970) (prefixPartial 12 27970) = false := by
  decide +kernel

theorem node_context_12_27970_405798 : EJMOriginalGlobalDAGData.nodes 9 ⟨405798, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨405768, by decide⟩,⟨405790, by decide⟩,⟨405797, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27970_405798 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27970 ⟨405798, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27970
    ⟨405798, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨405768, by decide⟩,⟨405790, by decide⟩,⟨405797, by decide⟩]) unmarked_context_12_27970_405798 node_context_12_27970_405798
  intro a
  fin_cases a
  · exact context_13_111880_3444
  · exact context_13_111881_405768
  · exact context_13_111882_405790
  · exact context_13_111883_405797

theorem selected_cut_15878 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 111884) = some ⟨13, 1, 0, 3444, 111884, 1, 16384⟩ := by
  decide +kernel

theorem context_13_111884_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111884 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 111884 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 111884, 1, 16384⟩
    (by decide) selected_cut_15878

theorem selected_cut_15879 : selected 8 ⟨405828, by decide⟩
    (prefixPartial 13 111885) = some ⟨13, 2, 0, 405828, 111885, 2861, 16384⟩ := by
  decide +kernel

theorem context_13_111885_405828 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111885 ⟨405828, by decide⟩ :=
  accepted_of_selected 13 111885 ⟨405828, by decide⟩ ⟨13, 2, 0, 405828, 111885, 2861, 16384⟩
    (by decide) selected_cut_15879

theorem selected_cut_15880 : selected 8 ⟨405857, by decide⟩
    (prefixPartial 13 111886) = some ⟨13, 2, 0, 405857, 111886, 2433, 16384⟩ := by
  decide +kernel

theorem context_13_111886_405857 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111886 ⟨405857, by decide⟩ :=
  accepted_of_selected 13 111886 ⟨405857, by decide⟩ ⟨13, 2, 0, 405857, 111886, 2433, 16384⟩
    (by decide) selected_cut_15880

theorem selected_cut_15881 : selected 8 ⟨405867, by decide⟩
    (prefixPartial 13 111887) = some ⟨13, 2, 0, 405867, 111887, 1037, 16384⟩ := by
  decide +kernel

theorem context_13_111887_405867 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111887 ⟨405867, by decide⟩ :=
  accepted_of_selected 13 111887 ⟨405867, by decide⟩ ⟨13, 2, 0, 405867, 111887, 1037, 16384⟩
    (by decide) selected_cut_15881

theorem unmarked_context_12_27971_405868 : frontier 9 ⟨405868, by decide⟩
    (prefixCache 12 27971) (prefixPartial 12 27971) = false := by
  decide +kernel

theorem node_context_12_27971_405868 : EJMOriginalGlobalDAGData.nodes 9 ⟨405868, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨405828, by decide⟩,⟨405857, by decide⟩,⟨405867, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27971_405868 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27971 ⟨405868, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27971
    ⟨405868, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨405828, by decide⟩,⟨405857, by decide⟩,⟨405867, by decide⟩]) unmarked_context_12_27971_405868 node_context_12_27971_405868
  intro a
  fin_cases a
  · exact context_13_111884_3444
  · exact context_13_111885_405828
  · exact context_13_111886_405857
  · exact context_13_111887_405867

theorem unmarked_context_11_6992_405869 : frontier 10 ⟨405869, by decide⟩
    (prefixCache 11 6992) (prefixPartial 11 6992) = false := by
  decide +kernel

theorem node_context_11_6992_405869 : EJMOriginalGlobalDAGData.nodes 10 ⟨405869, by decide⟩ =
    .split (coordinate 11) (![⟨405613, by decide⟩,⟨405743, by decide⟩,⟨405798, by decide⟩,⟨405868, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6992_405869 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6992 ⟨405869, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6992
    ⟨405869, by decide⟩ (by decide) (![⟨405613, by decide⟩,⟨405743, by decide⟩,⟨405798, by decide⟩,⟨405868, by decide⟩]) unmarked_context_11_6992_405869 node_context_11_6992_405869
  intro a
  fin_cases a
  · exact context_12_27968_405613
  · exact context_12_27969_405743
  · exact context_12_27970_405798
  · exact context_12_27971_405868

theorem selected_cut_15882 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 111888) = some ⟨13, 1, 0, 3444, 111888, 1, 16384⟩ := by
  decide +kernel

theorem context_13_111888_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111888 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 111888 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 111888, 1, 16384⟩
    (by decide) selected_cut_15882

theorem selected_cut_15883 : selected 8 ⟨405897, by decide⟩
    (prefixPartial 13 111889) = some ⟨13, 2, 0, 405897, 111889, 2225, 16384⟩ := by
  decide +kernel

theorem context_13_111889_405897 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111889 ⟨405897, by decide⟩ :=
  accepted_of_selected 13 111889 ⟨405897, by decide⟩ ⟨13, 2, 0, 405897, 111889, 2225, 16384⟩
    (by decide) selected_cut_15883

theorem selected_cut_15884 : selected 8 ⟨405926, by decide⟩
    (prefixPartial 13 111890) = some ⟨13, 2, 0, 405926, 111890, 1837, 16384⟩ := by
  decide +kernel

theorem context_13_111890_405926 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111890 ⟨405926, by decide⟩ :=
  accepted_of_selected 13 111890 ⟨405926, by decide⟩ ⟨13, 2, 0, 405926, 111890, 1837, 16384⟩
    (by decide) selected_cut_15884

theorem selected_cut_15885 : selected 8 ⟨405931, by decide⟩
    (prefixPartial 13 111891) = some ⟨13, 2, 0, 405931, 111891, 733, 16384⟩ := by
  decide +kernel

theorem context_13_111891_405931 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111891 ⟨405931, by decide⟩ :=
  accepted_of_selected 13 111891 ⟨405931, by decide⟩ ⟨13, 2, 0, 405931, 111891, 733, 16384⟩
    (by decide) selected_cut_15885

theorem unmarked_context_12_27972_405932 : frontier 9 ⟨405932, by decide⟩
    (prefixCache 12 27972) (prefixPartial 12 27972) = false := by
  decide +kernel

theorem node_context_12_27972_405932 : EJMOriginalGlobalDAGData.nodes 9 ⟨405932, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨405897, by decide⟩,⟨405926, by decide⟩,⟨405931, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27972_405932 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27972 ⟨405932, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27972
    ⟨405932, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨405897, by decide⟩,⟨405926, by decide⟩,⟨405931, by decide⟩]) unmarked_context_12_27972_405932 node_context_12_27972_405932
  intro a
  fin_cases a
  · exact context_13_111888_3444
  · exact context_13_111889_405897
  · exact context_13_111890_405926
  · exact context_13_111891_405931

theorem selected_cut_15886 : selected 9 ⟨126884, by decide⟩
    (prefixPartial 12 27973) = some ⟨12, 1, 0, 126884, 27973, 1, 65536⟩ := by
  decide +kernel

theorem context_12_27973_126884 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27973 ⟨126884, by decide⟩ :=
  accepted_of_selected 12 27973 ⟨126884, by decide⟩ ⟨12, 1, 0, 126884, 27973, 1, 65536⟩
    (by decide) selected_cut_15886

theorem selected_cut_15887 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 111896) = some ⟨13, 1, 0, 3444, 111896, 1, 16384⟩ := by
  decide +kernel

theorem context_13_111896_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111896 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 111896 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 111896, 1, 16384⟩
    (by decide) selected_cut_15887

theorem selected_cut_15888 : selected 8 ⟨405952, by decide⟩
    (prefixPartial 13 111897) = some ⟨13, 2, 0, 405952, 111897, 2177, 16384⟩ := by
  decide +kernel

theorem context_13_111897_405952 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111897 ⟨405952, by decide⟩ :=
  accepted_of_selected 13 111897 ⟨405952, by decide⟩ ⟨13, 2, 0, 405952, 111897, 2177, 16384⟩
    (by decide) selected_cut_15888

theorem selected_cut_15889 : selected 8 ⟨405974, by decide⟩
    (prefixPartial 13 111898) = some ⟨13, 2, 0, 405974, 111898, 2093, 16384⟩ := by
  decide +kernel

theorem context_13_111898_405974 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111898 ⟨405974, by decide⟩ :=
  accepted_of_selected 13 111898 ⟨405974, by decide⟩ ⟨13, 2, 0, 405974, 111898, 2093, 16384⟩
    (by decide) selected_cut_15889

theorem selected_cut_15890 : selected 8 ⟨405982, by decide⟩
    (prefixPartial 13 111899) = some ⟨13, 2, 0, 405982, 111899, 881, 16384⟩ := by
  decide +kernel

theorem context_13_111899_405982 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111899 ⟨405982, by decide⟩ :=
  accepted_of_selected 13 111899 ⟨405982, by decide⟩ ⟨13, 2, 0, 405982, 111899, 881, 16384⟩
    (by decide) selected_cut_15890

theorem unmarked_context_12_27974_405983 : frontier 9 ⟨405983, by decide⟩
    (prefixCache 12 27974) (prefixPartial 12 27974) = false := by
  decide +kernel

theorem node_context_12_27974_405983 : EJMOriginalGlobalDAGData.nodes 9 ⟨405983, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨405952, by decide⟩,⟨405974, by decide⟩,⟨405982, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27974_405983 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27974 ⟨405983, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27974
    ⟨405983, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨405952, by decide⟩,⟨405974, by decide⟩,⟨405982, by decide⟩]) unmarked_context_12_27974_405983 node_context_12_27974_405983
  intro a
  fin_cases a
  · exact context_13_111896_3444
  · exact context_13_111897_405952
  · exact context_13_111898_405974
  · exact context_13_111899_405982

theorem selected_cut_15891 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 111900) = some ⟨13, 1, 0, 3444, 111900, 1, 16384⟩ := by
  decide +kernel

theorem context_13_111900_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111900 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 111900 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 111900, 1, 16384⟩
    (by decide) selected_cut_15891

theorem selected_cut_15892 : selected 8 ⟨406012, by decide⟩
    (prefixPartial 13 111901) = some ⟨13, 2, 0, 406012, 111901, 2273, 16384⟩ := by
  decide +kernel

theorem context_13_111901_406012 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111901 ⟨406012, by decide⟩ :=
  accepted_of_selected 13 111901 ⟨406012, by decide⟩ ⟨13, 2, 0, 406012, 111901, 2273, 16384⟩
    (by decide) selected_cut_15892

theorem selected_cut_15893 : selected 8 ⟨406035, by decide⟩
    (prefixPartial 13 111902) = some ⟨13, 2, 0, 406035, 111902, 2137, 16384⟩ := by
  decide +kernel

theorem context_13_111902_406035 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111902 ⟨406035, by decide⟩ :=
  accepted_of_selected 13 111902 ⟨406035, by decide⟩ ⟨13, 2, 0, 406035, 111902, 2137, 16384⟩
    (by decide) selected_cut_15893

theorem selected_cut_15894 : selected 8 ⟨406043, by decide⟩
    (prefixPartial 13 111903) = some ⟨13, 2, 0, 406043, 111903, 965, 16384⟩ := by
  decide +kernel

theorem context_13_111903_406043 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111903 ⟨406043, by decide⟩ :=
  accepted_of_selected 13 111903 ⟨406043, by decide⟩ ⟨13, 2, 0, 406043, 111903, 965, 16384⟩
    (by decide) selected_cut_15894

theorem unmarked_context_12_27975_406044 : frontier 9 ⟨406044, by decide⟩
    (prefixCache 12 27975) (prefixPartial 12 27975) = false := by
  decide +kernel

theorem node_context_12_27975_406044 : EJMOriginalGlobalDAGData.nodes 9 ⟨406044, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨406012, by decide⟩,⟨406035, by decide⟩,⟨406043, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27975_406044 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27975 ⟨406044, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27975
    ⟨406044, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨406012, by decide⟩,⟨406035, by decide⟩,⟨406043, by decide⟩]) unmarked_context_12_27975_406044 node_context_12_27975_406044
  intro a
  fin_cases a
  · exact context_13_111900_3444
  · exact context_13_111901_406012
  · exact context_13_111902_406035
  · exact context_13_111903_406043

theorem unmarked_context_11_6993_406045 : frontier 10 ⟨406045, by decide⟩
    (prefixCache 11 6993) (prefixPartial 11 6993) = false := by
  decide +kernel

theorem node_context_11_6993_406045 : EJMOriginalGlobalDAGData.nodes 10 ⟨406045, by decide⟩ =
    .split (coordinate 11) (![⟨405932, by decide⟩,⟨126884, by decide⟩,⟨405983, by decide⟩,⟨406044, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6993_406045 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6993 ⟨406045, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6993
    ⟨406045, by decide⟩ (by decide) (![⟨405932, by decide⟩,⟨126884, by decide⟩,⟨405983, by decide⟩,⟨406044, by decide⟩]) unmarked_context_11_6993_406045 node_context_11_6993_406045
  intro a
  fin_cases a
  · exact context_12_27972_405932
  · exact context_12_27973_126884
  · exact context_12_27974_405983
  · exact context_12_27975_406044

theorem selected_cut_15895 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 111904) = some ⟨13, 1, 0, 3444, 111904, 1, 16384⟩ := by
  decide +kernel

theorem context_13_111904_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111904 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 111904 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 111904, 1, 16384⟩
    (by decide) selected_cut_15895

theorem selected_cut_15896 : selected 8 ⟨406074, by decide⟩
    (prefixPartial 13 111905) = some ⟨13, 2, 0, 406074, 111905, 2361, 16384⟩ := by
  decide +kernel

theorem context_13_111905_406074 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111905 ⟨406074, by decide⟩ :=
  accepted_of_selected 13 111905 ⟨406074, by decide⟩ ⟨13, 2, 0, 406074, 111905, 2361, 16384⟩
    (by decide) selected_cut_15896

theorem selected_cut_15897 : selected 8 ⟨406107, by decide⟩
    (prefixPartial 13 111906) = some ⟨13, 2, 0, 406107, 111906, 2217, 16384⟩ := by
  decide +kernel

theorem context_13_111906_406107 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111906 ⟨406107, by decide⟩ :=
  accepted_of_selected 13 111906 ⟨406107, by decide⟩ ⟨13, 2, 0, 406107, 111906, 2217, 16384⟩
    (by decide) selected_cut_15897

theorem selected_cut_15898 : selected 8 ⟨406117, by decide⟩
    (prefixPartial 13 111907) = some ⟨13, 2, 0, 406117, 111907, 905, 16384⟩ := by
  decide +kernel

theorem context_13_111907_406117 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111907 ⟨406117, by decide⟩ :=
  accepted_of_selected 13 111907 ⟨406117, by decide⟩ ⟨13, 2, 0, 406117, 111907, 905, 16384⟩
    (by decide) selected_cut_15898

theorem unmarked_context_12_27976_406118 : frontier 9 ⟨406118, by decide⟩
    (prefixCache 12 27976) (prefixPartial 12 27976) = false := by
  decide +kernel

theorem node_context_12_27976_406118 : EJMOriginalGlobalDAGData.nodes 9 ⟨406118, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨406074, by decide⟩,⟨406107, by decide⟩,⟨406117, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27976_406118 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27976 ⟨406118, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27976
    ⟨406118, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨406074, by decide⟩,⟨406107, by decide⟩,⟨406117, by decide⟩]) unmarked_context_12_27976_406118 node_context_12_27976_406118
  intro a
  fin_cases a
  · exact context_13_111904_3444
  · exact context_13_111905_406074
  · exact context_13_111906_406107
  · exact context_13_111907_406117

theorem selected_cut_15899 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 111908) = some ⟨13, 1, 0, 3444, 111908, 1, 16384⟩ := by
  decide +kernel

theorem context_13_111908_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111908 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 111908 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 111908, 1, 16384⟩
    (by decide) selected_cut_15899

theorem selected_cut_15900 : selected 8 ⟨406159, by decide⟩
    (prefixPartial 13 111909) = some ⟨13, 2, 0, 406159, 111909, 2701, 16384⟩ := by
  decide +kernel

theorem context_13_111909_406159 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111909 ⟨406159, by decide⟩ :=
  accepted_of_selected 13 111909 ⟨406159, by decide⟩ ⟨13, 2, 0, 406159, 111909, 2701, 16384⟩
    (by decide) selected_cut_15900

theorem selected_cut_15901 : selected 8 ⟨406209, by decide⟩
    (prefixPartial 13 111910) = some ⟨13, 2, 0, 406209, 111910, 2913, 16384⟩ := by
  decide +kernel

theorem context_13_111910_406209 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111910 ⟨406209, by decide⟩ :=
  accepted_of_selected 13 111910 ⟨406209, by decide⟩ ⟨13, 2, 0, 406209, 111910, 2913, 16384⟩
    (by decide) selected_cut_15901

theorem selected_cut_15902 : selected 8 ⟨406227, by decide⟩
    (prefixPartial 13 111911) = some ⟨13, 2, 0, 406227, 111911, 1249, 16384⟩ := by
  decide +kernel

theorem context_13_111911_406227 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111911 ⟨406227, by decide⟩ :=
  accepted_of_selected 13 111911 ⟨406227, by decide⟩ ⟨13, 2, 0, 406227, 111911, 1249, 16384⟩
    (by decide) selected_cut_15902

theorem unmarked_context_12_27977_406228 : frontier 9 ⟨406228, by decide⟩
    (prefixCache 12 27977) (prefixPartial 12 27977) = false := by
  decide +kernel

theorem node_context_12_27977_406228 : EJMOriginalGlobalDAGData.nodes 9 ⟨406228, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨406159, by decide⟩,⟨406209, by decide⟩,⟨406227, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27977_406228 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27977 ⟨406228, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27977
    ⟨406228, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨406159, by decide⟩,⟨406209, by decide⟩,⟨406227, by decide⟩]) unmarked_context_12_27977_406228 node_context_12_27977_406228
  intro a
  fin_cases a
  · exact context_13_111908_3444
  · exact context_13_111909_406159
  · exact context_13_111910_406209
  · exact context_13_111911_406227

theorem selected_cut_15903 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 111912) = some ⟨13, 1, 0, 3444, 111912, 1, 16384⟩ := by
  decide +kernel

theorem context_13_111912_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111912 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 111912 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 111912, 1, 16384⟩
    (by decide) selected_cut_15903

theorem selected_cut_15904 : selected 8 ⟨406253, by decide⟩
    (prefixPartial 13 111913) = some ⟨13, 2, 0, 406253, 111913, 2181, 16384⟩ := by
  decide +kernel

theorem context_13_111913_406253 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111913 ⟨406253, by decide⟩ :=
  accepted_of_selected 13 111913 ⟨406253, by decide⟩ ⟨13, 2, 0, 406253, 111913, 2181, 16384⟩
    (by decide) selected_cut_15904

theorem selected_cut_15905 : selected 8 ⟨406276, by decide⟩
    (prefixPartial 13 111914) = some ⟨13, 2, 0, 406276, 111914, 2341, 16384⟩ := by
  decide +kernel

theorem context_13_111914_406276 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111914 ⟨406276, by decide⟩ :=
  accepted_of_selected 13 111914 ⟨406276, by decide⟩ ⟨13, 2, 0, 406276, 111914, 2341, 16384⟩
    (by decide) selected_cut_15905

theorem selected_cut_15906 : selected 8 ⟨406285, by decide⟩
    (prefixPartial 13 111915) = some ⟨13, 2, 0, 406285, 111915, 1057, 16384⟩ := by
  decide +kernel

theorem context_13_111915_406285 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111915 ⟨406285, by decide⟩ :=
  accepted_of_selected 13 111915 ⟨406285, by decide⟩ ⟨13, 2, 0, 406285, 111915, 1057, 16384⟩
    (by decide) selected_cut_15906

theorem unmarked_context_12_27978_406286 : frontier 9 ⟨406286, by decide⟩
    (prefixCache 12 27978) (prefixPartial 12 27978) = false := by
  decide +kernel

theorem node_context_12_27978_406286 : EJMOriginalGlobalDAGData.nodes 9 ⟨406286, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨406253, by decide⟩,⟨406276, by decide⟩,⟨406285, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27978_406286 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27978 ⟨406286, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27978
    ⟨406286, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨406253, by decide⟩,⟨406276, by decide⟩,⟨406285, by decide⟩]) unmarked_context_12_27978_406286 node_context_12_27978_406286
  intro a
  fin_cases a
  · exact context_13_111912_3444
  · exact context_13_111913_406253
  · exact context_13_111914_406276
  · exact context_13_111915_406285

theorem selected_cut_15907 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 111916) = some ⟨13, 1, 0, 3444, 111916, 1, 16384⟩ := by
  decide +kernel

theorem context_13_111916_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111916 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 111916 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 111916, 1, 16384⟩
    (by decide) selected_cut_15907

theorem selected_cut_15908 : selected 8 ⟨406316, by decide⟩
    (prefixPartial 13 111917) = some ⟨13, 2, 0, 406316, 111917, 2385, 16384⟩ := by
  decide +kernel

theorem context_13_111917_406316 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111917 ⟨406316, by decide⟩ :=
  accepted_of_selected 13 111917 ⟨406316, by decide⟩ ⟨13, 2, 0, 406316, 111917, 2385, 16384⟩
    (by decide) selected_cut_15908

theorem selected_cut_15909 : selected 8 ⟨406343, by decide⟩
    (prefixPartial 13 111918) = some ⟨13, 2, 0, 406343, 111918, 2277, 16384⟩ := by
  decide +kernel

theorem context_13_111918_406343 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111918 ⟨406343, by decide⟩ :=
  accepted_of_selected 13 111918 ⟨406343, by decide⟩ ⟨13, 2, 0, 406343, 111918, 2277, 16384⟩
    (by decide) selected_cut_15909

theorem selected_cut_15910 : selected 8 ⟨406350, by decide⟩
    (prefixPartial 13 111919) = some ⟨13, 2, 0, 406350, 111919, 1109, 16384⟩ := by
  decide +kernel

theorem context_13_111919_406350 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111919 ⟨406350, by decide⟩ :=
  accepted_of_selected 13 111919 ⟨406350, by decide⟩ ⟨13, 2, 0, 406350, 111919, 1109, 16384⟩
    (by decide) selected_cut_15910

theorem unmarked_context_12_27979_406351 : frontier 9 ⟨406351, by decide⟩
    (prefixCache 12 27979) (prefixPartial 12 27979) = false := by
  decide +kernel

theorem node_context_12_27979_406351 : EJMOriginalGlobalDAGData.nodes 9 ⟨406351, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨406316, by decide⟩,⟨406343, by decide⟩,⟨406350, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27979_406351 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27979 ⟨406351, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27979
    ⟨406351, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨406316, by decide⟩,⟨406343, by decide⟩,⟨406350, by decide⟩]) unmarked_context_12_27979_406351 node_context_12_27979_406351
  intro a
  fin_cases a
  · exact context_13_111916_3444
  · exact context_13_111917_406316
  · exact context_13_111918_406343
  · exact context_13_111919_406350

theorem unmarked_context_11_6994_406352 : frontier 10 ⟨406352, by decide⟩
    (prefixCache 11 6994) (prefixPartial 11 6994) = false := by
  decide +kernel

theorem node_context_11_6994_406352 : EJMOriginalGlobalDAGData.nodes 10 ⟨406352, by decide⟩ =
    .split (coordinate 11) (![⟨406118, by decide⟩,⟨406228, by decide⟩,⟨406286, by decide⟩,⟨406351, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6994_406352 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6994 ⟨406352, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6994
    ⟨406352, by decide⟩ (by decide) (![⟨406118, by decide⟩,⟨406228, by decide⟩,⟨406286, by decide⟩,⟨406351, by decide⟩]) unmarked_context_11_6994_406352 node_context_11_6994_406352
  intro a
  fin_cases a
  · exact context_12_27976_406118
  · exact context_12_27977_406228
  · exact context_12_27978_406286
  · exact context_12_27979_406351

theorem selected_cut_15911 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 111920) = some ⟨13, 1, 0, 3444, 111920, 1, 16384⟩ := by
  decide +kernel

theorem context_13_111920_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111920 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 111920 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 111920, 1, 16384⟩
    (by decide) selected_cut_15911

theorem selected_cut_15912 : selected 8 ⟨406382, by decide⟩
    (prefixPartial 13 111921) = some ⟨13, 2, 0, 406382, 111921, 2065, 16384⟩ := by
  decide +kernel

theorem context_13_111921_406382 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111921 ⟨406382, by decide⟩ :=
  accepted_of_selected 13 111921 ⟨406382, by decide⟩ ⟨13, 2, 0, 406382, 111921, 2065, 16384⟩
    (by decide) selected_cut_15912

theorem selected_cut_15913 : selected 8 ⟨406399, by decide⟩
    (prefixPartial 13 111922) = some ⟨13, 2, 0, 406399, 111922, 1913, 16384⟩ := by
  decide +kernel

theorem context_13_111922_406399 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111922 ⟨406399, by decide⟩ :=
  accepted_of_selected 13 111922 ⟨406399, by decide⟩ ⟨13, 2, 0, 406399, 111922, 1913, 16384⟩
    (by decide) selected_cut_15913

theorem selected_cut_15914 : selected 8 ⟨406405, by decide⟩
    (prefixPartial 13 111923) = some ⟨13, 2, 0, 406405, 111923, 1021, 16384⟩ := by
  decide +kernel

theorem context_13_111923_406405 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111923 ⟨406405, by decide⟩ :=
  accepted_of_selected 13 111923 ⟨406405, by decide⟩ ⟨13, 2, 0, 406405, 111923, 1021, 16384⟩
    (by decide) selected_cut_15914

theorem unmarked_context_12_27980_406406 : frontier 9 ⟨406406, by decide⟩
    (prefixCache 12 27980) (prefixPartial 12 27980) = false := by
  decide +kernel

theorem node_context_12_27980_406406 : EJMOriginalGlobalDAGData.nodes 9 ⟨406406, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨406382, by decide⟩,⟨406399, by decide⟩,⟨406405, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27980_406406 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27980 ⟨406406, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27980
    ⟨406406, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨406382, by decide⟩,⟨406399, by decide⟩,⟨406405, by decide⟩]) unmarked_context_12_27980_406406 node_context_12_27980_406406
  intro a
  fin_cases a
  · exact context_13_111920_3444
  · exact context_13_111921_406382
  · exact context_13_111922_406399
  · exact context_13_111923_406405

theorem selected_cut_15915 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 111924) = some ⟨13, 1, 0, 3444, 111924, 1, 16384⟩ := by
  decide +kernel

theorem context_13_111924_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111924 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 111924 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 111924, 1, 16384⟩
    (by decide) selected_cut_15915

theorem selected_cut_15916 : selected 8 ⟨406439, by decide⟩
    (prefixPartial 13 111925) = some ⟨13, 2, 0, 406439, 111925, 2513, 16384⟩ := by
  decide +kernel

theorem context_13_111925_406439 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111925 ⟨406439, by decide⟩ :=
  accepted_of_selected 13 111925 ⟨406439, by decide⟩ ⟨13, 2, 0, 406439, 111925, 2513, 16384⟩
    (by decide) selected_cut_15916

theorem selected_cut_15917 : selected 8 ⟨406470, by decide⟩
    (prefixPartial 13 111926) = some ⟨13, 2, 0, 406470, 111926, 2625, 16384⟩ := by
  decide +kernel

theorem context_13_111926_406470 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111926 ⟨406470, by decide⟩ :=
  accepted_of_selected 13 111926 ⟨406470, by decide⟩ ⟨13, 2, 0, 406470, 111926, 2625, 16384⟩
    (by decide) selected_cut_15917

theorem selected_cut_15918 : selected 8 ⟨406481, by decide⟩
    (prefixPartial 13 111927) = some ⟨13, 2, 0, 406481, 111927, 1237, 16384⟩ := by
  decide +kernel

theorem context_13_111927_406481 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111927 ⟨406481, by decide⟩ :=
  accepted_of_selected 13 111927 ⟨406481, by decide⟩ ⟨13, 2, 0, 406481, 111927, 1237, 16384⟩
    (by decide) selected_cut_15918

theorem unmarked_context_12_27981_406482 : frontier 9 ⟨406482, by decide⟩
    (prefixCache 12 27981) (prefixPartial 12 27981) = false := by
  decide +kernel

theorem node_context_12_27981_406482 : EJMOriginalGlobalDAGData.nodes 9 ⟨406482, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨406439, by decide⟩,⟨406470, by decide⟩,⟨406481, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27981_406482 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27981 ⟨406482, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27981
    ⟨406482, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨406439, by decide⟩,⟨406470, by decide⟩,⟨406481, by decide⟩]) unmarked_context_12_27981_406482 node_context_12_27981_406482
  intro a
  fin_cases a
  · exact context_13_111924_3444
  · exact context_13_111925_406439
  · exact context_13_111926_406470
  · exact context_13_111927_406481

theorem selected_cut_15919 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 111928) = some ⟨13, 1, 0, 3444, 111928, 1, 16384⟩ := by
  decide +kernel

theorem context_13_111928_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111928 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 111928 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 111928, 1, 16384⟩
    (by decide) selected_cut_15919

theorem selected_cut_15920 : selected 8 ⟨406500, by decide⟩
    (prefixPartial 13 111929) = some ⟨13, 2, 0, 406500, 111929, 2053, 16384⟩ := by
  decide +kernel

theorem context_13_111929_406500 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111929 ⟨406500, by decide⟩ :=
  accepted_of_selected 13 111929 ⟨406500, by decide⟩ ⟨13, 2, 0, 406500, 111929, 2053, 16384⟩
    (by decide) selected_cut_15920

theorem selected_cut_15921 : selected 8 ⟨406521, by decide⟩
    (prefixPartial 13 111930) = some ⟨13, 2, 0, 406521, 111930, 2121, 16384⟩ := by
  decide +kernel

theorem context_13_111930_406521 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111930 ⟨406521, by decide⟩ :=
  accepted_of_selected 13 111930 ⟨406521, by decide⟩ ⟨13, 2, 0, 406521, 111930, 2121, 16384⟩
    (by decide) selected_cut_15921

theorem selected_cut_15922 : selected 8 ⟨406527, by decide⟩
    (prefixPartial 13 111931) = some ⟨13, 2, 0, 406527, 111931, 1101, 16384⟩ := by
  decide +kernel

theorem context_13_111931_406527 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111931 ⟨406527, by decide⟩ :=
  accepted_of_selected 13 111931 ⟨406527, by decide⟩ ⟨13, 2, 0, 406527, 111931, 1101, 16384⟩
    (by decide) selected_cut_15922

theorem unmarked_context_12_27982_406528 : frontier 9 ⟨406528, by decide⟩
    (prefixCache 12 27982) (prefixPartial 12 27982) = false := by
  decide +kernel

theorem node_context_12_27982_406528 : EJMOriginalGlobalDAGData.nodes 9 ⟨406528, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨406500, by decide⟩,⟨406521, by decide⟩,⟨406527, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27982_406528 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27982 ⟨406528, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27982
    ⟨406528, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨406500, by decide⟩,⟨406521, by decide⟩,⟨406527, by decide⟩]) unmarked_context_12_27982_406528 node_context_12_27982_406528
  intro a
  fin_cases a
  · exact context_13_111928_3444
  · exact context_13_111929_406500
  · exact context_13_111930_406521
  · exact context_13_111931_406527

theorem selected_cut_15923 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 111932) = some ⟨13, 1, 0, 3444, 111932, 1, 16384⟩ := by
  decide +kernel

theorem context_13_111932_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111932 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 111932 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 111932, 1, 16384⟩
    (by decide) selected_cut_15923

theorem selected_cut_15924 : selected 8 ⟨406546, by decide⟩
    (prefixPartial 13 111933) = some ⟨13, 2, 0, 406546, 111933, 1941, 16384⟩ := by
  decide +kernel

theorem context_13_111933_406546 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111933 ⟨406546, by decide⟩ :=
  accepted_of_selected 13 111933 ⟨406546, by decide⟩ ⟨13, 2, 0, 406546, 111933, 1941, 16384⟩
    (by decide) selected_cut_15924

theorem selected_cut_15925 : selected 8 ⟨406566, by decide⟩
    (prefixPartial 13 111934) = some ⟨13, 2, 0, 406566, 111934, 2077, 16384⟩ := by
  decide +kernel

theorem context_13_111934_406566 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111934 ⟨406566, by decide⟩ :=
  accepted_of_selected 13 111934 ⟨406566, by decide⟩ ⟨13, 2, 0, 406566, 111934, 2077, 16384⟩
    (by decide) selected_cut_15925

theorem selected_cut_15926 : selected 8 ⟨406574, by decide⟩
    (prefixPartial 13 111935) = some ⟨13, 2, 0, 406574, 111935, 1153, 16384⟩ := by
  decide +kernel

theorem context_13_111935_406574 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111935 ⟨406574, by decide⟩ :=
  accepted_of_selected 13 111935 ⟨406574, by decide⟩ ⟨13, 2, 0, 406574, 111935, 1153, 16384⟩
    (by decide) selected_cut_15926

theorem unmarked_context_12_27983_406575 : frontier 9 ⟨406575, by decide⟩
    (prefixCache 12 27983) (prefixPartial 12 27983) = false := by
  decide +kernel

theorem node_context_12_27983_406575 : EJMOriginalGlobalDAGData.nodes 9 ⟨406575, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨406546, by decide⟩,⟨406566, by decide⟩,⟨406574, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27983_406575 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27983 ⟨406575, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27983
    ⟨406575, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨406546, by decide⟩,⟨406566, by decide⟩,⟨406574, by decide⟩]) unmarked_context_12_27983_406575 node_context_12_27983_406575
  intro a
  fin_cases a
  · exact context_13_111932_3444
  · exact context_13_111933_406546
  · exact context_13_111934_406566
  · exact context_13_111935_406574

theorem unmarked_context_11_6995_406576 : frontier 10 ⟨406576, by decide⟩
    (prefixCache 11 6995) (prefixPartial 11 6995) = false := by
  decide +kernel

theorem node_context_11_6995_406576 : EJMOriginalGlobalDAGData.nodes 10 ⟨406576, by decide⟩ =
    .split (coordinate 11) (![⟨406406, by decide⟩,⟨406482, by decide⟩,⟨406528, by decide⟩,⟨406575, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6995_406576 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6995 ⟨406576, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6995
    ⟨406576, by decide⟩ (by decide) (![⟨406406, by decide⟩,⟨406482, by decide⟩,⟨406528, by decide⟩,⟨406575, by decide⟩]) unmarked_context_11_6995_406576 node_context_11_6995_406576
  intro a
  fin_cases a
  · exact context_12_27980_406406
  · exact context_12_27981_406482
  · exact context_12_27982_406528
  · exact context_12_27983_406575

theorem unmarked_context_10_1748_406577 : frontier 11 ⟨406577, by decide⟩
    (prefixCache 10 1748) (prefixPartial 10 1748) = false := by
  decide +kernel

theorem node_context_10_1748_406577 : EJMOriginalGlobalDAGData.nodes 11 ⟨406577, by decide⟩ =
    .split (coordinate 10) (![⟨405869, by decide⟩,⟨406045, by decide⟩,⟨406352, by decide⟩,⟨406576, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1748_406577 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1748 ⟨406577, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1748
    ⟨406577, by decide⟩ (by decide) (![⟨405869, by decide⟩,⟨406045, by decide⟩,⟨406352, by decide⟩,⟨406576, by decide⟩]) unmarked_context_10_1748_406577 node_context_10_1748_406577
  intro a
  fin_cases a
  · exact context_11_6992_405869
  · exact context_11_6993_406045
  · exact context_11_6994_406352
  · exact context_11_6995_406576

theorem selected_cut_15927 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 111936) = some ⟨13, 1, 0, 3444, 111936, 1, 16384⟩ := by
  decide +kernel

theorem context_13_111936_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111936 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 111936 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 111936, 1, 16384⟩
    (by decide) selected_cut_15927

theorem selected_cut_15928 : selected 8 ⟨406594, by decide⟩
    (prefixPartial 13 111937) = some ⟨13, 2, 0, 406594, 111937, 1789, 16384⟩ := by
  decide +kernel

theorem context_13_111937_406594 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111937 ⟨406594, by decide⟩ :=
  accepted_of_selected 13 111937 ⟨406594, by decide⟩ ⟨13, 2, 0, 406594, 111937, 1789, 16384⟩
    (by decide) selected_cut_15928

theorem selected_cut_15929 : selected 8 ⟨406618, by decide⟩
    (prefixPartial 13 111938) = some ⟨13, 2, 0, 406618, 111938, 1809, 16384⟩ := by
  decide +kernel

theorem context_13_111938_406618 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111938 ⟨406618, by decide⟩ :=
  accepted_of_selected 13 111938 ⟨406618, by decide⟩ ⟨13, 2, 0, 406618, 111938, 1809, 16384⟩
    (by decide) selected_cut_15929

theorem selected_cut_15930 : selected 8 ⟨406625, by decide⟩
    (prefixPartial 13 111939) = some ⟨13, 2, 0, 406625, 111939, 789, 16384⟩ := by
  decide +kernel

theorem context_13_111939_406625 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111939 ⟨406625, by decide⟩ :=
  accepted_of_selected 13 111939 ⟨406625, by decide⟩ ⟨13, 2, 0, 406625, 111939, 789, 16384⟩
    (by decide) selected_cut_15930

theorem unmarked_context_12_27984_406626 : frontier 9 ⟨406626, by decide⟩
    (prefixCache 12 27984) (prefixPartial 12 27984) = false := by
  decide +kernel

theorem node_context_12_27984_406626 : EJMOriginalGlobalDAGData.nodes 9 ⟨406626, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨406594, by decide⟩,⟨406618, by decide⟩,⟨406625, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27984_406626 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27984 ⟨406626, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27984
    ⟨406626, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨406594, by decide⟩,⟨406618, by decide⟩,⟨406625, by decide⟩]) unmarked_context_12_27984_406626 node_context_12_27984_406626
  intro a
  fin_cases a
  · exact context_13_111936_3444
  · exact context_13_111937_406594
  · exact context_13_111938_406618
  · exact context_13_111939_406625

theorem selected_cut_15931 : selected 9 ⟨170504, by decide⟩
    (prefixPartial 12 27985) = some ⟨12, 1, 0, 170504, 27985, 1, 65536⟩ := by
  decide +kernel

theorem context_12_27985_170504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27985 ⟨170504, by decide⟩ :=
  accepted_of_selected 12 27985 ⟨170504, by decide⟩ ⟨12, 1, 0, 170504, 27985, 1, 65536⟩
    (by decide) selected_cut_15931

theorem selected_cut_15932 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 111944) = some ⟨13, 1, 0, 3444, 111944, 1, 16384⟩ := by
  decide +kernel

theorem context_13_111944_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111944 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 111944 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 111944, 1, 16384⟩
    (by decide) selected_cut_15932

theorem selected_cut_15933 : selected 8 ⟨406641, by decide⟩
    (prefixPartial 13 111945) = some ⟨13, 2, 0, 406641, 111945, 1957, 16384⟩ := by
  decide +kernel

theorem context_13_111945_406641 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111945 ⟨406641, by decide⟩ :=
  accepted_of_selected 13 111945 ⟨406641, by decide⟩ ⟨13, 2, 0, 406641, 111945, 1957, 16384⟩
    (by decide) selected_cut_15933

theorem selected_cut_15934 : selected 8 ⟨406672, by decide⟩
    (prefixPartial 13 111946) = some ⟨13, 2, 0, 406672, 111946, 2345, 16384⟩ := by
  decide +kernel

theorem context_13_111946_406672 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111946 ⟨406672, by decide⟩ :=
  accepted_of_selected 13 111946 ⟨406672, by decide⟩ ⟨13, 2, 0, 406672, 111946, 2345, 16384⟩
    (by decide) selected_cut_15934

theorem selected_cut_15935 : selected 8 ⟨406679, by decide⟩
    (prefixPartial 13 111947) = some ⟨13, 2, 0, 406679, 111947, 1065, 16384⟩ := by
  decide +kernel

theorem context_13_111947_406679 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111947 ⟨406679, by decide⟩ :=
  accepted_of_selected 13 111947 ⟨406679, by decide⟩ ⟨13, 2, 0, 406679, 111947, 1065, 16384⟩
    (by decide) selected_cut_15935

theorem unmarked_context_12_27986_406680 : frontier 9 ⟨406680, by decide⟩
    (prefixCache 12 27986) (prefixPartial 12 27986) = false := by
  decide +kernel

theorem node_context_12_27986_406680 : EJMOriginalGlobalDAGData.nodes 9 ⟨406680, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨406641, by decide⟩,⟨406672, by decide⟩,⟨406679, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27986_406680 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27986 ⟨406680, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27986
    ⟨406680, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨406641, by decide⟩,⟨406672, by decide⟩,⟨406679, by decide⟩]) unmarked_context_12_27986_406680 node_context_12_27986_406680
  intro a
  fin_cases a
  · exact context_13_111944_3444
  · exact context_13_111945_406641
  · exact context_13_111946_406672
  · exact context_13_111947_406679

theorem selected_cut_15936 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 111948) = some ⟨13, 1, 0, 3444, 111948, 1, 16384⟩ := by
  decide +kernel

theorem context_13_111948_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111948 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 111948 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 111948, 1, 16384⟩
    (by decide) selected_cut_15936

theorem selected_cut_15937 : selected 8 ⟨406710, by decide⟩
    (prefixPartial 13 111949) = some ⟨13, 2, 0, 406710, 111949, 2049, 16384⟩ := by
  decide +kernel

theorem context_13_111949_406710 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111949 ⟨406710, by decide⟩ :=
  accepted_of_selected 13 111949 ⟨406710, by decide⟩ ⟨13, 2, 0, 406710, 111949, 2049, 16384⟩
    (by decide) selected_cut_15937

theorem selected_cut_15938 : selected 8 ⟨406748, by decide⟩
    (prefixPartial 13 111950) = some ⟨13, 2, 0, 406748, 111950, 2381, 16384⟩ := by
  decide +kernel

theorem context_13_111950_406748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111950 ⟨406748, by decide⟩ :=
  accepted_of_selected 13 111950 ⟨406748, by decide⟩ ⟨13, 2, 0, 406748, 111950, 2381, 16384⟩
    (by decide) selected_cut_15938

theorem selected_cut_15939 : selected 8 ⟨406757, by decide⟩
    (prefixPartial 13 111951) = some ⟨13, 2, 0, 406757, 111951, 1081, 16384⟩ := by
  decide +kernel

theorem context_13_111951_406757 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111951 ⟨406757, by decide⟩ :=
  accepted_of_selected 13 111951 ⟨406757, by decide⟩ ⟨13, 2, 0, 406757, 111951, 1081, 16384⟩
    (by decide) selected_cut_15939

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
