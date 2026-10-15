/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover365
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_35139 : selected 9 ⟨920915, by decide⟩
    (prefixPartial 12 284199) = some ⟨12, 2, 0, 920915, 284199, 2557, 65536⟩ := by
  decide +kernel

theorem context_12_284199_920915 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284199 ⟨920915, by decide⟩ :=
  accepted_of_selected 12 284199 ⟨920915, by decide⟩ ⟨12, 2, 0, 920915, 284199, 2557, 65536⟩
    (by decide) selected_cut_35139

theorem unmarked_context_11_71049_920916 : frontier 10 ⟨920916, by decide⟩
    (prefixCache 11 71049) (prefixPartial 11 71049) = false := by
  decide +kernel

theorem node_context_11_71049_920916 : EJMOriginalGlobalDAGData.nodes 10 ⟨920916, by decide⟩ =
    .split (coordinate 11) (![⟨920797, by decide⟩,⟨920829, by decide⟩,⟨920874, by decide⟩,⟨920915, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71049_920916 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71049 ⟨920916, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71049
    ⟨920916, by decide⟩ (by decide) (![⟨920797, by decide⟩,⟨920829, by decide⟩,⟨920874, by decide⟩,⟨920915, by decide⟩]) unmarked_context_11_71049_920916 node_context_11_71049_920916
  intro a
  fin_cases a
  · exact context_12_284196_920797
  · exact context_12_284197_920829
  · exact context_12_284198_920874
  · exact context_12_284199_920915

theorem selected_cut_35140 : selected 9 ⟨920966, by decide⟩
    (prefixPartial 12 284200) = some ⟨12, 2, 0, 920966, 284200, 3033, 65536⟩ := by
  decide +kernel

theorem context_12_284200_920966 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284200 ⟨920966, by decide⟩ :=
  accepted_of_selected 12 284200 ⟨920966, by decide⟩ ⟨12, 2, 0, 920966, 284200, 3033, 65536⟩
    (by decide) selected_cut_35140

theorem selected_cut_35141 : selected 9 ⟨921001, by decide⟩
    (prefixPartial 12 284201) = some ⟨12, 2, 0, 921001, 284201, 2585, 65536⟩ := by
  decide +kernel

theorem context_12_284201_921001 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284201 ⟨921001, by decide⟩ :=
  accepted_of_selected 12 284201 ⟨921001, by decide⟩ ⟨12, 2, 0, 921001, 284201, 2585, 65536⟩
    (by decide) selected_cut_35141

theorem selected_cut_35142 : selected 9 ⟨661671, by decide⟩
    (prefixPartial 12 284202) = some ⟨12, 1, 0, 661671, 284202, 1, 65536⟩ := by
  decide +kernel

theorem context_12_284202_661671 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284202 ⟨661671, by decide⟩ :=
  accepted_of_selected 12 284202 ⟨661671, by decide⟩ ⟨12, 1, 0, 661671, 284202, 1, 65536⟩
    (by decide) selected_cut_35142

theorem selected_cut_35143 : selected 9 ⟨921063, by decide⟩
    (prefixPartial 12 284203) = some ⟨12, 2, 0, 921063, 284203, 3261, 65536⟩ := by
  decide +kernel

theorem context_12_284203_921063 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284203 ⟨921063, by decide⟩ :=
  accepted_of_selected 12 284203 ⟨921063, by decide⟩ ⟨12, 2, 0, 921063, 284203, 3261, 65536⟩
    (by decide) selected_cut_35143

theorem unmarked_context_11_71050_921064 : frontier 10 ⟨921064, by decide⟩
    (prefixCache 11 71050) (prefixPartial 11 71050) = false := by
  decide +kernel

theorem node_context_11_71050_921064 : EJMOriginalGlobalDAGData.nodes 10 ⟨921064, by decide⟩ =
    .split (coordinate 11) (![⟨920966, by decide⟩,⟨921001, by decide⟩,⟨661671, by decide⟩,⟨921063, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71050_921064 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71050 ⟨921064, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71050
    ⟨921064, by decide⟩ (by decide) (![⟨920966, by decide⟩,⟨921001, by decide⟩,⟨661671, by decide⟩,⟨921063, by decide⟩]) unmarked_context_11_71050_921064 node_context_11_71050_921064
  intro a
  fin_cases a
  · exact context_12_284200_920966
  · exact context_12_284201_921001
  · exact context_12_284202_661671
  · exact context_12_284203_921063

theorem selected_cut_35144 : selected 9 ⟨921126, by decide⟩
    (prefixPartial 12 284204) = some ⟨12, 2, 0, 921126, 284204, 3225, 65536⟩ := by
  decide +kernel

theorem context_12_284204_921126 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284204 ⟨921126, by decide⟩ :=
  accepted_of_selected 12 284204 ⟨921126, by decide⟩ ⟨12, 2, 0, 921126, 284204, 3225, 65536⟩
    (by decide) selected_cut_35144

theorem selected_cut_35145 : selected 9 ⟨921170, by decide⟩
    (prefixPartial 12 284205) = some ⟨12, 2, 0, 921170, 284205, 2629, 65536⟩ := by
  decide +kernel

theorem context_12_284205_921170 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284205 ⟨921170, by decide⟩ :=
  accepted_of_selected 12 284205 ⟨921170, by decide⟩ ⟨12, 2, 0, 921170, 284205, 2629, 65536⟩
    (by decide) selected_cut_35145

theorem selected_cut_35146 : selected 9 ⟨921238, by decide⟩
    (prefixPartial 12 284206) = some ⟨12, 2, 0, 921238, 284206, 3345, 65536⟩ := by
  decide +kernel

theorem context_12_284206_921238 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284206 ⟨921238, by decide⟩ :=
  accepted_of_selected 12 284206 ⟨921238, by decide⟩ ⟨12, 2, 0, 921238, 284206, 3345, 65536⟩
    (by decide) selected_cut_35146

theorem selected_cut_35147 : selected 9 ⟨921290, by decide⟩
    (prefixPartial 12 284207) = some ⟨12, 2, 0, 921290, 284207, 3021, 65536⟩ := by
  decide +kernel

theorem context_12_284207_921290 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284207 ⟨921290, by decide⟩ :=
  accepted_of_selected 12 284207 ⟨921290, by decide⟩ ⟨12, 2, 0, 921290, 284207, 3021, 65536⟩
    (by decide) selected_cut_35147

theorem unmarked_context_11_71051_921291 : frontier 10 ⟨921291, by decide⟩
    (prefixCache 11 71051) (prefixPartial 11 71051) = false := by
  decide +kernel

theorem node_context_11_71051_921291 : EJMOriginalGlobalDAGData.nodes 10 ⟨921291, by decide⟩ =
    .split (coordinate 11) (![⟨921126, by decide⟩,⟨921170, by decide⟩,⟨921238, by decide⟩,⟨921290, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71051_921291 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71051 ⟨921291, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71051
    ⟨921291, by decide⟩ (by decide) (![⟨921126, by decide⟩,⟨921170, by decide⟩,⟨921238, by decide⟩,⟨921290, by decide⟩]) unmarked_context_11_71051_921291 node_context_11_71051_921291
  intro a
  fin_cases a
  · exact context_12_284204_921126
  · exact context_12_284205_921170
  · exact context_12_284206_921238
  · exact context_12_284207_921290

theorem unmarked_context_10_17762_921292 : frontier 11 ⟨921292, by decide⟩
    (prefixCache 10 17762) (prefixPartial 10 17762) = false := by
  decide +kernel

theorem node_context_10_17762_921292 : EJMOriginalGlobalDAGData.nodes 11 ⟨921292, by decide⟩ =
    .split (coordinate 10) (![⟨920756, by decide⟩,⟨920916, by decide⟩,⟨921064, by decide⟩,⟨921291, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17762_921292 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17762 ⟨921292, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17762
    ⟨921292, by decide⟩ (by decide) (![⟨920756, by decide⟩,⟨920916, by decide⟩,⟨921064, by decide⟩,⟨921291, by decide⟩]) unmarked_context_10_17762_921292 node_context_10_17762_921292
  intro a
  fin_cases a
  · exact context_11_71048_920756
  · exact context_11_71049_920916
  · exact context_11_71050_921064
  · exact context_11_71051_921291

theorem selected_cut_35148 : selected 9 ⟨921321, by decide⟩
    (prefixPartial 12 284208) = some ⟨12, 2, 0, 921321, 284208, 2301, 65536⟩ := by
  decide +kernel

theorem context_12_284208_921321 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284208 ⟨921321, by decide⟩ :=
  accepted_of_selected 12 284208 ⟨921321, by decide⟩ ⟨12, 2, 0, 921321, 284208, 2301, 65536⟩
    (by decide) selected_cut_35148

theorem selected_cut_35149 : selected 9 ⟨921354, by decide⟩
    (prefixPartial 12 284209) = some ⟨12, 2, 0, 921354, 284209, 2113, 65536⟩ := by
  decide +kernel

theorem context_12_284209_921354 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284209 ⟨921354, by decide⟩ :=
  accepted_of_selected 12 284209 ⟨921354, by decide⟩ ⟨12, 2, 0, 921354, 284209, 2113, 65536⟩
    (by decide) selected_cut_35149

theorem selected_cut_35150 : selected 9 ⟨921392, by decide⟩
    (prefixPartial 12 284210) = some ⟨12, 2, 0, 921392, 284210, 2269, 65536⟩ := by
  decide +kernel

theorem context_12_284210_921392 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284210 ⟨921392, by decide⟩ :=
  accepted_of_selected 12 284210 ⟨921392, by decide⟩ ⟨12, 2, 0, 921392, 284210, 2269, 65536⟩
    (by decide) selected_cut_35150

theorem selected_cut_35151 : selected 9 ⟨921457, by decide⟩
    (prefixPartial 12 284211) = some ⟨12, 2, 0, 921457, 284211, 2853, 65536⟩ := by
  decide +kernel

theorem context_12_284211_921457 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284211 ⟨921457, by decide⟩ :=
  accepted_of_selected 12 284211 ⟨921457, by decide⟩ ⟨12, 2, 0, 921457, 284211, 2853, 65536⟩
    (by decide) selected_cut_35151

theorem unmarked_context_11_71052_921458 : frontier 10 ⟨921458, by decide⟩
    (prefixCache 11 71052) (prefixPartial 11 71052) = false := by
  decide +kernel

theorem node_context_11_71052_921458 : EJMOriginalGlobalDAGData.nodes 10 ⟨921458, by decide⟩ =
    .split (coordinate 11) (![⟨921321, by decide⟩,⟨921354, by decide⟩,⟨921392, by decide⟩,⟨921457, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71052_921458 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71052 ⟨921458, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71052
    ⟨921458, by decide⟩ (by decide) (![⟨921321, by decide⟩,⟨921354, by decide⟩,⟨921392, by decide⟩,⟨921457, by decide⟩]) unmarked_context_11_71052_921458 node_context_11_71052_921458
  intro a
  fin_cases a
  · exact context_12_284208_921321
  · exact context_12_284209_921354
  · exact context_12_284210_921392
  · exact context_12_284211_921457

theorem selected_cut_35152 : selected 9 ⟨921487, by decide⟩
    (prefixPartial 12 284212) = some ⟨12, 2, 0, 921487, 284212, 2181, 65536⟩ := by
  decide +kernel

theorem context_12_284212_921487 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284212 ⟨921487, by decide⟩ :=
  accepted_of_selected 12 284212 ⟨921487, by decide⟩ ⟨12, 2, 0, 921487, 284212, 2181, 65536⟩
    (by decide) selected_cut_35152

theorem selected_cut_35153 : selected 9 ⟨921512, by decide⟩
    (prefixPartial 12 284213) = some ⟨12, 2, 0, 921512, 284213, 1765, 65536⟩ := by
  decide +kernel

theorem context_12_284213_921512 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284213 ⟨921512, by decide⟩ :=
  accepted_of_selected 12 284213 ⟨921512, by decide⟩ ⟨12, 2, 0, 921512, 284213, 1765, 65536⟩
    (by decide) selected_cut_35153

theorem selected_cut_35154 : selected 9 ⟨921537, by decide⟩
    (prefixPartial 12 284214) = some ⟨12, 2, 0, 921537, 284214, 2005, 65536⟩ := by
  decide +kernel

theorem context_12_284214_921537 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284214 ⟨921537, by decide⟩ :=
  accepted_of_selected 12 284214 ⟨921537, by decide⟩ ⟨12, 2, 0, 921537, 284214, 2005, 65536⟩
    (by decide) selected_cut_35154

theorem selected_cut_35155 : selected 9 ⟨921583, by decide⟩
    (prefixPartial 12 284215) = some ⟨12, 2, 0, 921583, 284215, 2341, 65536⟩ := by
  decide +kernel

theorem context_12_284215_921583 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284215 ⟨921583, by decide⟩ :=
  accepted_of_selected 12 284215 ⟨921583, by decide⟩ ⟨12, 2, 0, 921583, 284215, 2341, 65536⟩
    (by decide) selected_cut_35155

theorem unmarked_context_11_71053_921584 : frontier 10 ⟨921584, by decide⟩
    (prefixCache 11 71053) (prefixPartial 11 71053) = false := by
  decide +kernel

theorem node_context_11_71053_921584 : EJMOriginalGlobalDAGData.nodes 10 ⟨921584, by decide⟩ =
    .split (coordinate 11) (![⟨921487, by decide⟩,⟨921512, by decide⟩,⟨921537, by decide⟩,⟨921583, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71053_921584 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71053 ⟨921584, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71053
    ⟨921584, by decide⟩ (by decide) (![⟨921487, by decide⟩,⟨921512, by decide⟩,⟨921537, by decide⟩,⟨921583, by decide⟩]) unmarked_context_11_71053_921584 node_context_11_71053_921584
  intro a
  fin_cases a
  · exact context_12_284212_921487
  · exact context_12_284213_921512
  · exact context_12_284214_921537
  · exact context_12_284215_921583

theorem selected_cut_35156 : selected 9 ⟨921617, by decide⟩
    (prefixPartial 12 284216) = some ⟨12, 2, 0, 921617, 284216, 2453, 65536⟩ := by
  decide +kernel

theorem context_12_284216_921617 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284216 ⟨921617, by decide⟩ :=
  accepted_of_selected 12 284216 ⟨921617, by decide⟩ ⟨12, 2, 0, 921617, 284216, 2453, 65536⟩
    (by decide) selected_cut_35156

theorem selected_cut_35157 : selected 9 ⟨921643, by decide⟩
    (prefixPartial 12 284217) = some ⟨12, 2, 0, 921643, 284217, 2089, 65536⟩ := by
  decide +kernel

theorem context_12_284217_921643 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284217 ⟨921643, by decide⟩ :=
  accepted_of_selected 12 284217 ⟨921643, by decide⟩ ⟨12, 2, 0, 921643, 284217, 2089, 65536⟩
    (by decide) selected_cut_35157

theorem selected_cut_35158 : selected 9 ⟨893903, by decide⟩
    (prefixPartial 12 284218) = some ⟨12, 1, 0, 893903, 284218, 1, 65536⟩ := by
  decide +kernel

theorem context_12_284218_893903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284218 ⟨893903, by decide⟩ :=
  accepted_of_selected 12 284218 ⟨893903, by decide⟩ ⟨12, 1, 0, 893903, 284218, 1, 65536⟩
    (by decide) selected_cut_35158

theorem selected_cut_35159 : selected 9 ⟨921702, by decide⟩
    (prefixPartial 12 284219) = some ⟨12, 2, 0, 921702, 284219, 2989, 65536⟩ := by
  decide +kernel

theorem context_12_284219_921702 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284219 ⟨921702, by decide⟩ :=
  accepted_of_selected 12 284219 ⟨921702, by decide⟩ ⟨12, 2, 0, 921702, 284219, 2989, 65536⟩
    (by decide) selected_cut_35159

theorem unmarked_context_11_71054_921703 : frontier 10 ⟨921703, by decide⟩
    (prefixCache 11 71054) (prefixPartial 11 71054) = false := by
  decide +kernel

theorem node_context_11_71054_921703 : EJMOriginalGlobalDAGData.nodes 10 ⟨921703, by decide⟩ =
    .split (coordinate 11) (![⟨921617, by decide⟩,⟨921643, by decide⟩,⟨893903, by decide⟩,⟨921702, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71054_921703 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71054 ⟨921703, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71054
    ⟨921703, by decide⟩ (by decide) (![⟨921617, by decide⟩,⟨921643, by decide⟩,⟨893903, by decide⟩,⟨921702, by decide⟩]) unmarked_context_11_71054_921703 node_context_11_71054_921703
  intro a
  fin_cases a
  · exact context_12_284216_921617
  · exact context_12_284217_921643
  · exact context_12_284218_893903
  · exact context_12_284219_921702

theorem selected_cut_35160 : selected 9 ⟨921743, by decide⟩
    (prefixPartial 12 284220) = some ⟨12, 2, 0, 921743, 284220, 2597, 65536⟩ := by
  decide +kernel

theorem context_12_284220_921743 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284220 ⟨921743, by decide⟩ :=
  accepted_of_selected 12 284220 ⟨921743, by decide⟩ ⟨12, 2, 0, 921743, 284220, 2597, 65536⟩
    (by decide) selected_cut_35160

theorem selected_cut_35161 : selected 9 ⟨921774, by decide⟩
    (prefixPartial 12 284221) = some ⟨12, 2, 0, 921774, 284221, 2073, 65536⟩ := by
  decide +kernel

theorem context_12_284221_921774 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284221 ⟨921774, by decide⟩ :=
  accepted_of_selected 12 284221 ⟨921774, by decide⟩ ⟨12, 2, 0, 921774, 284221, 2073, 65536⟩
    (by decide) selected_cut_35161

theorem selected_cut_35162 : selected 9 ⟨921815, by decide⟩
    (prefixPartial 12 284222) = some ⟨12, 2, 0, 921815, 284222, 2457, 65536⟩ := by
  decide +kernel

theorem context_12_284222_921815 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284222 ⟨921815, by decide⟩ :=
  accepted_of_selected 12 284222 ⟨921815, by decide⟩ ⟨12, 2, 0, 921815, 284222, 2457, 65536⟩
    (by decide) selected_cut_35162

theorem selected_cut_35163 : selected 9 ⟨921872, by decide⟩
    (prefixPartial 12 284223) = some ⟨12, 2, 0, 921872, 284223, 2725, 65536⟩ := by
  decide +kernel

theorem context_12_284223_921872 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284223 ⟨921872, by decide⟩ :=
  accepted_of_selected 12 284223 ⟨921872, by decide⟩ ⟨12, 2, 0, 921872, 284223, 2725, 65536⟩
    (by decide) selected_cut_35163

theorem unmarked_context_11_71055_921873 : frontier 10 ⟨921873, by decide⟩
    (prefixCache 11 71055) (prefixPartial 11 71055) = false := by
  decide +kernel

theorem node_context_11_71055_921873 : EJMOriginalGlobalDAGData.nodes 10 ⟨921873, by decide⟩ =
    .split (coordinate 11) (![⟨921743, by decide⟩,⟨921774, by decide⟩,⟨921815, by decide⟩,⟨921872, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71055_921873 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71055 ⟨921873, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71055
    ⟨921873, by decide⟩ (by decide) (![⟨921743, by decide⟩,⟨921774, by decide⟩,⟨921815, by decide⟩,⟨921872, by decide⟩]) unmarked_context_11_71055_921873 node_context_11_71055_921873
  intro a
  fin_cases a
  · exact context_12_284220_921743
  · exact context_12_284221_921774
  · exact context_12_284222_921815
  · exact context_12_284223_921872

theorem unmarked_context_10_17763_921874 : frontier 11 ⟨921874, by decide⟩
    (prefixCache 10 17763) (prefixPartial 10 17763) = false := by
  decide +kernel

theorem node_context_10_17763_921874 : EJMOriginalGlobalDAGData.nodes 11 ⟨921874, by decide⟩ =
    .split (coordinate 10) (![⟨921458, by decide⟩,⟨921584, by decide⟩,⟨921703, by decide⟩,⟨921873, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17763_921874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17763 ⟨921874, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17763
    ⟨921874, by decide⟩ (by decide) (![⟨921458, by decide⟩,⟨921584, by decide⟩,⟨921703, by decide⟩,⟨921873, by decide⟩]) unmarked_context_10_17763_921874 node_context_10_17763_921874
  intro a
  fin_cases a
  · exact context_11_71052_921458
  · exact context_11_71053_921584
  · exact context_11_71054_921703
  · exact context_11_71055_921873

theorem unmarked_context_9_4440_921875 : frontier 12 ⟨921875, by decide⟩
    (prefixCache 9 4440) (prefixPartial 9 4440) = false := by
  decide +kernel

theorem node_context_9_4440_921875 : EJMOriginalGlobalDAGData.nodes 12 ⟨921875, by decide⟩ =
    .split (coordinate 9) (![⟨920051, by decide⟩,⟨920558, by decide⟩,⟨921292, by decide⟩,⟨921874, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4440_921875 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4440 ⟨921875, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4440
    ⟨921875, by decide⟩ (by decide) (![⟨920051, by decide⟩,⟨920558, by decide⟩,⟨921292, by decide⟩,⟨921874, by decide⟩]) unmarked_context_9_4440_921875 node_context_9_4440_921875
  intro a
  fin_cases a
  · exact context_10_17760_920051
  · exact context_10_17761_920558
  · exact context_10_17762_921292
  · exact context_10_17763_921874

theorem selected_cut_35164 : selected 9 ⟨921945, by decide⟩
    (prefixPartial 12 284224) = some ⟨12, 2, 0, 921945, 284224, 3065, 65536⟩ := by
  decide +kernel

theorem context_12_284224_921945 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284224 ⟨921945, by decide⟩ :=
  accepted_of_selected 12 284224 ⟨921945, by decide⟩ ⟨12, 2, 0, 921945, 284224, 3065, 65536⟩
    (by decide) selected_cut_35164

theorem selected_cut_35165 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 284225) = some ⟨12, 1, 0, 896706, 284225, 1, 65536⟩ := by
  decide +kernel

theorem context_12_284225_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284225 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 284225 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 284225, 1, 65536⟩
    (by decide) selected_cut_35165

theorem selected_cut_35166 : selected 9 ⟨922002, by decide⟩
    (prefixPartial 12 284226) = some ⟨12, 2, 0, 922002, 284226, 2361, 65536⟩ := by
  decide +kernel

theorem context_12_284226_922002 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284226 ⟨922002, by decide⟩ :=
  accepted_of_selected 12 284226 ⟨922002, by decide⟩ ⟨12, 2, 0, 922002, 284226, 2361, 65536⟩
    (by decide) selected_cut_35166

theorem selected_cut_35167 : selected 9 ⟨922051, by decide⟩
    (prefixPartial 12 284227) = some ⟨12, 2, 0, 922051, 284227, 2529, 65536⟩ := by
  decide +kernel

theorem context_12_284227_922051 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284227 ⟨922051, by decide⟩ :=
  accepted_of_selected 12 284227 ⟨922051, by decide⟩ ⟨12, 2, 0, 922051, 284227, 2529, 65536⟩
    (by decide) selected_cut_35167

theorem unmarked_context_11_71056_922052 : frontier 10 ⟨922052, by decide⟩
    (prefixCache 11 71056) (prefixPartial 11 71056) = false := by
  decide +kernel

theorem node_context_11_71056_922052 : EJMOriginalGlobalDAGData.nodes 10 ⟨922052, by decide⟩ =
    .split (coordinate 11) (![⟨921945, by decide⟩,⟨896706, by decide⟩,⟨922002, by decide⟩,⟨922051, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71056_922052 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71056 ⟨922052, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71056
    ⟨922052, by decide⟩ (by decide) (![⟨921945, by decide⟩,⟨896706, by decide⟩,⟨922002, by decide⟩,⟨922051, by decide⟩]) unmarked_context_11_71056_922052 node_context_11_71056_922052
  intro a
  fin_cases a
  · exact context_12_284224_921945
  · exact context_12_284225_896706
  · exact context_12_284226_922002
  · exact context_12_284227_922051

theorem selected_cut_35168 : selected 9 ⟨922110, by decide⟩
    (prefixPartial 12 284228) = some ⟨12, 2, 0, 922110, 284228, 2409, 65536⟩ := by
  decide +kernel

theorem context_12_284228_922110 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284228 ⟨922110, by decide⟩ :=
  accepted_of_selected 12 284228 ⟨922110, by decide⟩ ⟨12, 2, 0, 922110, 284228, 2409, 65536⟩
    (by decide) selected_cut_35168

theorem selected_cut_35169 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 284229) = some ⟨12, 1, 0, 896706, 284229, 1, 65536⟩ := by
  decide +kernel

theorem context_12_284229_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284229 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 284229 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 284229, 1, 65536⟩
    (by decide) selected_cut_35169

theorem selected_cut_35170 : selected 9 ⟨922141, by decide⟩
    (prefixPartial 12 284230) = some ⟨12, 2, 0, 922141, 284230, 1909, 65536⟩ := by
  decide +kernel

theorem context_12_284230_922141 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284230 ⟨922141, by decide⟩ :=
  accepted_of_selected 12 284230 ⟨922141, by decide⟩ ⟨12, 2, 0, 922141, 284230, 1909, 65536⟩
    (by decide) selected_cut_35170

theorem selected_cut_35171 : selected 9 ⟨922178, by decide⟩
    (prefixPartial 12 284231) = some ⟨12, 2, 0, 922178, 284231, 1973, 65536⟩ := by
  decide +kernel

theorem context_12_284231_922178 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284231 ⟨922178, by decide⟩ :=
  accepted_of_selected 12 284231 ⟨922178, by decide⟩ ⟨12, 2, 0, 922178, 284231, 1973, 65536⟩
    (by decide) selected_cut_35171

theorem unmarked_context_11_71057_922179 : frontier 10 ⟨922179, by decide⟩
    (prefixCache 11 71057) (prefixPartial 11 71057) = false := by
  decide +kernel

theorem node_context_11_71057_922179 : EJMOriginalGlobalDAGData.nodes 10 ⟨922179, by decide⟩ =
    .split (coordinate 11) (![⟨922110, by decide⟩,⟨896706, by decide⟩,⟨922141, by decide⟩,⟨922178, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71057_922179 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71057 ⟨922179, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71057
    ⟨922179, by decide⟩ (by decide) (![⟨922110, by decide⟩,⟨896706, by decide⟩,⟨922141, by decide⟩,⟨922178, by decide⟩]) unmarked_context_11_71057_922179 node_context_11_71057_922179
  intro a
  fin_cases a
  · exact context_12_284228_922110
  · exact context_12_284229_896706
  · exact context_12_284230_922141
  · exact context_12_284231_922178

theorem selected_cut_35172 : selected 9 ⟨922236, by decide⟩
    (prefixPartial 12 284232) = some ⟨12, 2, 0, 922236, 284232, 2717, 65536⟩ := by
  decide +kernel

theorem context_12_284232_922236 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284232 ⟨922236, by decide⟩ :=
  accepted_of_selected 12 284232 ⟨922236, by decide⟩ ⟨12, 2, 0, 922236, 284232, 2717, 65536⟩
    (by decide) selected_cut_35172

theorem selected_cut_35173 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 284233) = some ⟨12, 1, 0, 896706, 284233, 1, 65536⟩ := by
  decide +kernel

theorem context_12_284233_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284233 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 284233 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 284233, 1, 65536⟩
    (by decide) selected_cut_35173

theorem selected_cut_35174 : selected 9 ⟨893903, by decide⟩
    (prefixPartial 12 284234) = some ⟨12, 1, 0, 893903, 284234, 1, 65536⟩ := by
  decide +kernel

theorem context_12_284234_893903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284234 ⟨893903, by decide⟩ :=
  accepted_of_selected 12 284234 ⟨893903, by decide⟩ ⟨12, 1, 0, 893903, 284234, 1, 65536⟩
    (by decide) selected_cut_35174

theorem selected_cut_35175 : selected 9 ⟨922286, by decide⟩
    (prefixPartial 12 284235) = some ⟨12, 2, 0, 922286, 284235, 2529, 65536⟩ := by
  decide +kernel

theorem context_12_284235_922286 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284235 ⟨922286, by decide⟩ :=
  accepted_of_selected 12 284235 ⟨922286, by decide⟩ ⟨12, 2, 0, 922286, 284235, 2529, 65536⟩
    (by decide) selected_cut_35175

theorem unmarked_context_11_71058_922287 : frontier 10 ⟨922287, by decide⟩
    (prefixCache 11 71058) (prefixPartial 11 71058) = false := by
  decide +kernel

theorem node_context_11_71058_922287 : EJMOriginalGlobalDAGData.nodes 10 ⟨922287, by decide⟩ =
    .split (coordinate 11) (![⟨922236, by decide⟩,⟨896706, by decide⟩,⟨893903, by decide⟩,⟨922286, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71058_922287 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71058 ⟨922287, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71058
    ⟨922287, by decide⟩ (by decide) (![⟨922236, by decide⟩,⟨896706, by decide⟩,⟨893903, by decide⟩,⟨922286, by decide⟩]) unmarked_context_11_71058_922287 node_context_11_71058_922287
  intro a
  fin_cases a
  · exact context_12_284232_922236
  · exact context_12_284233_896706
  · exact context_12_284234_893903
  · exact context_12_284235_922286

theorem selected_cut_35176 : selected 9 ⟨922347, by decide⟩
    (prefixPartial 12 284236) = some ⟨12, 2, 0, 922347, 284236, 3037, 65536⟩ := by
  decide +kernel

theorem context_12_284236_922347 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284236 ⟨922347, by decide⟩ :=
  accepted_of_selected 12 284236 ⟨922347, by decide⟩ ⟨12, 2, 0, 922347, 284236, 3037, 65536⟩
    (by decide) selected_cut_35176

theorem selected_cut_35177 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 284237) = some ⟨12, 1, 0, 896706, 284237, 1, 65536⟩ := by
  decide +kernel

theorem context_12_284237_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284237 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 284237 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 284237, 1, 65536⟩
    (by decide) selected_cut_35177

theorem selected_cut_35178 : selected 9 ⟨922392, by decide⟩
    (prefixPartial 12 284238) = some ⟨12, 2, 0, 922392, 284238, 2477, 65536⟩ := by
  decide +kernel

theorem context_12_284238_922392 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284238 ⟨922392, by decide⟩ :=
  accepted_of_selected 12 284238 ⟨922392, by decide⟩ ⟨12, 2, 0, 922392, 284238, 2477, 65536⟩
    (by decide) selected_cut_35178

theorem selected_cut_35179 : selected 9 ⟨922430, by decide⟩
    (prefixPartial 12 284239) = some ⟨12, 2, 0, 922430, 284239, 2389, 65536⟩ := by
  decide +kernel

theorem context_12_284239_922430 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284239 ⟨922430, by decide⟩ :=
  accepted_of_selected 12 284239 ⟨922430, by decide⟩ ⟨12, 2, 0, 922430, 284239, 2389, 65536⟩
    (by decide) selected_cut_35179

theorem unmarked_context_11_71059_922431 : frontier 10 ⟨922431, by decide⟩
    (prefixCache 11 71059) (prefixPartial 11 71059) = false := by
  decide +kernel

theorem node_context_11_71059_922431 : EJMOriginalGlobalDAGData.nodes 10 ⟨922431, by decide⟩ =
    .split (coordinate 11) (![⟨922347, by decide⟩,⟨896706, by decide⟩,⟨922392, by decide⟩,⟨922430, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71059_922431 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71059 ⟨922431, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71059
    ⟨922431, by decide⟩ (by decide) (![⟨922347, by decide⟩,⟨896706, by decide⟩,⟨922392, by decide⟩,⟨922430, by decide⟩]) unmarked_context_11_71059_922431 node_context_11_71059_922431
  intro a
  fin_cases a
  · exact context_12_284236_922347
  · exact context_12_284237_896706
  · exact context_12_284238_922392
  · exact context_12_284239_922430

theorem unmarked_context_10_17764_922432 : frontier 11 ⟨922432, by decide⟩
    (prefixCache 10 17764) (prefixPartial 10 17764) = false := by
  decide +kernel

theorem node_context_10_17764_922432 : EJMOriginalGlobalDAGData.nodes 11 ⟨922432, by decide⟩ =
    .split (coordinate 10) (![⟨922052, by decide⟩,⟨922179, by decide⟩,⟨922287, by decide⟩,⟨922431, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17764_922432 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17764 ⟨922432, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17764
    ⟨922432, by decide⟩ (by decide) (![⟨922052, by decide⟩,⟨922179, by decide⟩,⟨922287, by decide⟩,⟨922431, by decide⟩]) unmarked_context_10_17764_922432 node_context_10_17764_922432
  intro a
  fin_cases a
  · exact context_11_71056_922052
  · exact context_11_71057_922179
  · exact context_11_71058_922287
  · exact context_11_71059_922431

theorem selected_cut_35180 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 17765) = some ⟨10, 1, 0, 893098, 17765, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_17765_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17765 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 17765 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 17765, 1, 1048576⟩
    (by decide) selected_cut_35180

theorem selected_cut_35181 : selected 9 ⟨922467, by decide⟩
    (prefixPartial 12 284256) = some ⟨12, 2, 0, 922467, 284256, 1945, 65536⟩ := by
  decide +kernel

theorem context_12_284256_922467 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284256 ⟨922467, by decide⟩ :=
  accepted_of_selected 12 284256 ⟨922467, by decide⟩ ⟨12, 2, 0, 922467, 284256, 1945, 65536⟩
    (by decide) selected_cut_35181

theorem selected_cut_35182 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 284257) = some ⟨12, 1, 0, 896706, 284257, 1, 65536⟩ := by
  decide +kernel

theorem context_12_284257_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284257 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 284257 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 284257, 1, 65536⟩
    (by decide) selected_cut_35182

theorem selected_cut_35183 : selected 9 ⟨922508, by decide⟩
    (prefixPartial 12 284258) = some ⟨12, 2, 0, 922508, 284258, 2109, 65536⟩ := by
  decide +kernel

theorem context_12_284258_922508 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284258 ⟨922508, by decide⟩ :=
  accepted_of_selected 12 284258 ⟨922508, by decide⟩ ⟨12, 2, 0, 922508, 284258, 2109, 65536⟩
    (by decide) selected_cut_35183

theorem selected_cut_35184 : selected 9 ⟨922542, by decide⟩
    (prefixPartial 12 284259) = some ⟨12, 2, 0, 922542, 284259, 2077, 65536⟩ := by
  decide +kernel

theorem context_12_284259_922542 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284259 ⟨922542, by decide⟩ :=
  accepted_of_selected 12 284259 ⟨922542, by decide⟩ ⟨12, 2, 0, 922542, 284259, 2077, 65536⟩
    (by decide) selected_cut_35184

theorem unmarked_context_11_71064_922543 : frontier 10 ⟨922543, by decide⟩
    (prefixCache 11 71064) (prefixPartial 11 71064) = false := by
  decide +kernel

theorem node_context_11_71064_922543 : EJMOriginalGlobalDAGData.nodes 10 ⟨922543, by decide⟩ =
    .split (coordinate 11) (![⟨922467, by decide⟩,⟨896706, by decide⟩,⟨922508, by decide⟩,⟨922542, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71064_922543 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71064 ⟨922543, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71064
    ⟨922543, by decide⟩ (by decide) (![⟨922467, by decide⟩,⟨896706, by decide⟩,⟨922508, by decide⟩,⟨922542, by decide⟩]) unmarked_context_11_71064_922543 node_context_11_71064_922543
  intro a
  fin_cases a
  · exact context_12_284256_922467
  · exact context_12_284257_896706
  · exact context_12_284258_922508
  · exact context_12_284259_922542

theorem selected_cut_35185 : selected 9 ⟨922564, by decide⟩
    (prefixPartial 12 284260) = some ⟨12, 2, 0, 922564, 284260, 1601, 65536⟩ := by
  decide +kernel

theorem context_12_284260_922564 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284260 ⟨922564, by decide⟩ :=
  accepted_of_selected 12 284260 ⟨922564, by decide⟩ ⟨12, 2, 0, 922564, 284260, 1601, 65536⟩
    (by decide) selected_cut_35185

theorem selected_cut_35186 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 284261) = some ⟨12, 1, 0, 896706, 284261, 1, 65536⟩ := by
  decide +kernel

theorem context_12_284261_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284261 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 284261 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 284261, 1, 65536⟩
    (by decide) selected_cut_35186

theorem selected_cut_35187 : selected 9 ⟨922593, by decide⟩
    (prefixPartial 12 284262) = some ⟨12, 2, 0, 922593, 284262, 1613, 65536⟩ := by
  decide +kernel

theorem context_12_284262_922593 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284262 ⟨922593, by decide⟩ :=
  accepted_of_selected 12 284262 ⟨922593, by decide⟩ ⟨12, 2, 0, 922593, 284262, 1613, 65536⟩
    (by decide) selected_cut_35187

theorem selected_cut_35188 : selected 9 ⟨922615, by decide⟩
    (prefixPartial 12 284263) = some ⟨12, 2, 0, 922615, 284263, 1613, 65536⟩ := by
  decide +kernel

theorem context_12_284263_922615 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284263 ⟨922615, by decide⟩ :=
  accepted_of_selected 12 284263 ⟨922615, by decide⟩ ⟨12, 2, 0, 922615, 284263, 1613, 65536⟩
    (by decide) selected_cut_35188

theorem unmarked_context_11_71065_922616 : frontier 10 ⟨922616, by decide⟩
    (prefixCache 11 71065) (prefixPartial 11 71065) = false := by
  decide +kernel

theorem node_context_11_71065_922616 : EJMOriginalGlobalDAGData.nodes 10 ⟨922616, by decide⟩ =
    .split (coordinate 11) (![⟨922564, by decide⟩,⟨896706, by decide⟩,⟨922593, by decide⟩,⟨922615, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71065_922616 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71065 ⟨922616, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71065
    ⟨922616, by decide⟩ (by decide) (![⟨922564, by decide⟩,⟨896706, by decide⟩,⟨922593, by decide⟩,⟨922615, by decide⟩]) unmarked_context_11_71065_922616 node_context_11_71065_922616
  intro a
  fin_cases a
  · exact context_12_284260_922564
  · exact context_12_284261_896706
  · exact context_12_284262_922593
  · exact context_12_284263_922615

theorem selected_cut_35189 : selected 9 ⟨922655, by decide⟩
    (prefixPartial 12 284264) = some ⟨12, 2, 0, 922655, 284264, 2157, 65536⟩ := by
  decide +kernel

theorem context_12_284264_922655 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284264 ⟨922655, by decide⟩ :=
  accepted_of_selected 12 284264 ⟨922655, by decide⟩ ⟨12, 2, 0, 922655, 284264, 2157, 65536⟩
    (by decide) selected_cut_35189

theorem selected_cut_35190 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 284265) = some ⟨12, 1, 0, 896706, 284265, 1, 65536⟩ := by
  decide +kernel

theorem context_12_284265_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284265 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 284265 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 284265, 1, 65536⟩
    (by decide) selected_cut_35190

theorem selected_cut_35191 : selected 9 ⟨661671, by decide⟩
    (prefixPartial 12 284266) = some ⟨12, 1, 0, 661671, 284266, 1, 65536⟩ := by
  decide +kernel

theorem context_12_284266_661671 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284266 ⟨661671, by decide⟩ :=
  accepted_of_selected 12 284266 ⟨661671, by decide⟩ ⟨12, 1, 0, 661671, 284266, 1, 65536⟩
    (by decide) selected_cut_35191

theorem selected_cut_35192 : selected 9 ⟨922699, by decide⟩
    (prefixPartial 12 284267) = some ⟨12, 2, 0, 922699, 284267, 2313, 65536⟩ := by
  decide +kernel

theorem context_12_284267_922699 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284267 ⟨922699, by decide⟩ :=
  accepted_of_selected 12 284267 ⟨922699, by decide⟩ ⟨12, 2, 0, 922699, 284267, 2313, 65536⟩
    (by decide) selected_cut_35192

theorem unmarked_context_11_71066_922700 : frontier 10 ⟨922700, by decide⟩
    (prefixCache 11 71066) (prefixPartial 11 71066) = false := by
  decide +kernel

theorem node_context_11_71066_922700 : EJMOriginalGlobalDAGData.nodes 10 ⟨922700, by decide⟩ =
    .split (coordinate 11) (![⟨922655, by decide⟩,⟨896706, by decide⟩,⟨661671, by decide⟩,⟨922699, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71066_922700 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71066 ⟨922700, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71066
    ⟨922700, by decide⟩ (by decide) (![⟨922655, by decide⟩,⟨896706, by decide⟩,⟨661671, by decide⟩,⟨922699, by decide⟩]) unmarked_context_11_71066_922700 node_context_11_71066_922700
  intro a
  fin_cases a
  · exact context_12_284264_922655
  · exact context_12_284265_896706
  · exact context_12_284266_661671
  · exact context_12_284267_922699

theorem selected_cut_35193 : selected 9 ⟨922741, by decide⟩
    (prefixPartial 12 284268) = some ⟨12, 2, 0, 922741, 284268, 2233, 65536⟩ := by
  decide +kernel

theorem context_12_284268_922741 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284268 ⟨922741, by decide⟩ :=
  accepted_of_selected 12 284268 ⟨922741, by decide⟩ ⟨12, 2, 0, 922741, 284268, 2233, 65536⟩
    (by decide) selected_cut_35193

theorem selected_cut_35194 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 284269) = some ⟨12, 1, 0, 896706, 284269, 1, 65536⟩ := by
  decide +kernel

theorem context_12_284269_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284269 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 284269 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 284269, 1, 65536⟩
    (by decide) selected_cut_35194

theorem selected_cut_35195 : selected 9 ⟨922781, by decide⟩
    (prefixPartial 12 284270) = some ⟨12, 2, 0, 922781, 284270, 2181, 65536⟩ := by
  decide +kernel

theorem context_12_284270_922781 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284270 ⟨922781, by decide⟩ :=
  accepted_of_selected 12 284270 ⟨922781, by decide⟩ ⟨12, 2, 0, 922781, 284270, 2181, 65536⟩
    (by decide) selected_cut_35195

theorem selected_cut_35196 : selected 9 ⟨922820, by decide⟩
    (prefixPartial 12 284271) = some ⟨12, 2, 0, 922820, 284271, 2045, 65536⟩ := by
  decide +kernel

theorem context_12_284271_922820 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284271 ⟨922820, by decide⟩ :=
  accepted_of_selected 12 284271 ⟨922820, by decide⟩ ⟨12, 2, 0, 922820, 284271, 2045, 65536⟩
    (by decide) selected_cut_35196

theorem unmarked_context_11_71067_922821 : frontier 10 ⟨922821, by decide⟩
    (prefixCache 11 71067) (prefixPartial 11 71067) = false := by
  decide +kernel

theorem node_context_11_71067_922821 : EJMOriginalGlobalDAGData.nodes 10 ⟨922821, by decide⟩ =
    .split (coordinate 11) (![⟨922741, by decide⟩,⟨896706, by decide⟩,⟨922781, by decide⟩,⟨922820, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71067_922821 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71067 ⟨922821, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71067
    ⟨922821, by decide⟩ (by decide) (![⟨922741, by decide⟩,⟨896706, by decide⟩,⟨922781, by decide⟩,⟨922820, by decide⟩]) unmarked_context_11_71067_922821 node_context_11_71067_922821
  intro a
  fin_cases a
  · exact context_12_284268_922741
  · exact context_12_284269_896706
  · exact context_12_284270_922781
  · exact context_12_284271_922820

theorem unmarked_context_10_17766_922822 : frontier 11 ⟨922822, by decide⟩
    (prefixCache 10 17766) (prefixPartial 10 17766) = false := by
  decide +kernel

theorem node_context_10_17766_922822 : EJMOriginalGlobalDAGData.nodes 11 ⟨922822, by decide⟩ =
    .split (coordinate 10) (![⟨922543, by decide⟩,⟨922616, by decide⟩,⟨922700, by decide⟩,⟨922821, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17766_922822 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17766 ⟨922822, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17766
    ⟨922822, by decide⟩ (by decide) (![⟨922543, by decide⟩,⟨922616, by decide⟩,⟨922700, by decide⟩,⟨922821, by decide⟩]) unmarked_context_10_17766_922822 node_context_10_17766_922822
  intro a
  fin_cases a
  · exact context_11_71064_922543
  · exact context_11_71065_922616
  · exact context_11_71066_922700
  · exact context_11_71067_922821

theorem selected_cut_35197 : selected 9 ⟨922849, by decide⟩
    (prefixPartial 12 284272) = some ⟨12, 2, 0, 922849, 284272, 1557, 65536⟩ := by
  decide +kernel

theorem context_12_284272_922849 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284272 ⟨922849, by decide⟩ :=
  accepted_of_selected 12 284272 ⟨922849, by decide⟩ ⟨12, 2, 0, 922849, 284272, 1557, 65536⟩
    (by decide) selected_cut_35197

theorem selected_cut_35198 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 284273) = some ⟨12, 1, 0, 896706, 284273, 1, 65536⟩ := by
  decide +kernel

theorem context_12_284273_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284273 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 284273 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 284273, 1, 65536⟩
    (by decide) selected_cut_35198

theorem selected_cut_35199 : selected 9 ⟨922871, by decide⟩
    (prefixPartial 12 284274) = some ⟨12, 2, 0, 922871, 284274, 1565, 65536⟩ := by
  decide +kernel

theorem context_12_284274_922871 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284274 ⟨922871, by decide⟩ :=
  accepted_of_selected 12 284274 ⟨922871, by decide⟩ ⟨12, 2, 0, 922871, 284274, 1565, 65536⟩
    (by decide) selected_cut_35199

theorem selected_cut_35200 : selected 9 ⟨922900, by decide⟩
    (prefixPartial 12 284275) = some ⟨12, 2, 0, 922900, 284275, 1753, 65536⟩ := by
  decide +kernel

theorem context_12_284275_922900 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284275 ⟨922900, by decide⟩ :=
  accepted_of_selected 12 284275 ⟨922900, by decide⟩ ⟨12, 2, 0, 922900, 284275, 1753, 65536⟩
    (by decide) selected_cut_35200

theorem unmarked_context_11_71068_922901 : frontier 10 ⟨922901, by decide⟩
    (prefixCache 11 71068) (prefixPartial 11 71068) = false := by
  decide +kernel

theorem node_context_11_71068_922901 : EJMOriginalGlobalDAGData.nodes 10 ⟨922901, by decide⟩ =
    .split (coordinate 11) (![⟨922849, by decide⟩,⟨896706, by decide⟩,⟨922871, by decide⟩,⟨922900, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71068_922901 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71068 ⟨922901, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71068
    ⟨922901, by decide⟩ (by decide) (![⟨922849, by decide⟩,⟨896706, by decide⟩,⟨922871, by decide⟩,⟨922900, by decide⟩]) unmarked_context_11_71068_922901 node_context_11_71068_922901
  intro a
  fin_cases a
  · exact context_12_284272_922849
  · exact context_12_284273_896706
  · exact context_12_284274_922871
  · exact context_12_284275_922900

theorem selected_cut_35201 : selected 10 ⟨922957, by decide⟩
    (prefixPartial 11 71069) = some ⟨11, 2, 0, 922957, 71069, 4021, 262144⟩ := by
  decide +kernel

theorem context_11_71069_922957 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71069 ⟨922957, by decide⟩ :=
  accepted_of_selected 11 71069 ⟨922957, by decide⟩ ⟨11, 2, 0, 922957, 71069, 4021, 262144⟩
    (by decide) selected_cut_35201

theorem selected_cut_35202 : selected 10 ⟨923015, by decide⟩
    (prefixPartial 11 71070) = some ⟨11, 2, 0, 923015, 71070, 3693, 262144⟩ := by
  decide +kernel

theorem context_11_71070_923015 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71070 ⟨923015, by decide⟩ :=
  accepted_of_selected 11 71070 ⟨923015, by decide⟩ ⟨11, 2, 0, 923015, 71070, 3693, 262144⟩
    (by decide) selected_cut_35202

theorem selected_cut_35203 : selected 9 ⟨923051, by decide⟩
    (prefixPartial 12 284284) = some ⟨12, 2, 0, 923051, 284284, 1857, 65536⟩ := by
  decide +kernel

theorem context_12_284284_923051 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284284 ⟨923051, by decide⟩ :=
  accepted_of_selected 12 284284 ⟨923051, by decide⟩ ⟨12, 2, 0, 923051, 284284, 1857, 65536⟩
    (by decide) selected_cut_35203

theorem selected_cut_35204 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 284285) = some ⟨12, 1, 0, 896706, 284285, 1, 65536⟩ := by
  decide +kernel

theorem context_12_284285_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284285 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 284285 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 284285, 1, 65536⟩
    (by decide) selected_cut_35204

theorem selected_cut_35205 : selected 9 ⟨923081, by decide⟩
    (prefixPartial 12 284286) = some ⟨12, 2, 0, 923081, 284286, 1737, 65536⟩ := by
  decide +kernel

theorem context_12_284286_923081 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284286 ⟨923081, by decide⟩ :=
  accepted_of_selected 12 284286 ⟨923081, by decide⟩ ⟨12, 2, 0, 923081, 284286, 1737, 65536⟩
    (by decide) selected_cut_35205

theorem selected_cut_35206 : selected 9 ⟨923115, by decide⟩
    (prefixPartial 12 284287) = some ⟨12, 2, 0, 923115, 284287, 1805, 65536⟩ := by
  decide +kernel

theorem context_12_284287_923115 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284287 ⟨923115, by decide⟩ :=
  accepted_of_selected 12 284287 ⟨923115, by decide⟩ ⟨12, 2, 0, 923115, 284287, 1805, 65536⟩
    (by decide) selected_cut_35206

theorem unmarked_context_11_71071_923116 : frontier 10 ⟨923116, by decide⟩
    (prefixCache 11 71071) (prefixPartial 11 71071) = false := by
  decide +kernel

theorem node_context_11_71071_923116 : EJMOriginalGlobalDAGData.nodes 10 ⟨923116, by decide⟩ =
    .split (coordinate 11) (![⟨923051, by decide⟩,⟨896706, by decide⟩,⟨923081, by decide⟩,⟨923115, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71071_923116 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71071 ⟨923116, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71071
    ⟨923116, by decide⟩ (by decide) (![⟨923051, by decide⟩,⟨896706, by decide⟩,⟨923081, by decide⟩,⟨923115, by decide⟩]) unmarked_context_11_71071_923116 node_context_11_71071_923116
  intro a
  fin_cases a
  · exact context_12_284284_923051
  · exact context_12_284285_896706
  · exact context_12_284286_923081
  · exact context_12_284287_923115

theorem unmarked_context_10_17767_923117 : frontier 11 ⟨923117, by decide⟩
    (prefixCache 10 17767) (prefixPartial 10 17767) = false := by
  decide +kernel

theorem node_context_10_17767_923117 : EJMOriginalGlobalDAGData.nodes 11 ⟨923117, by decide⟩ =
    .split (coordinate 10) (![⟨922901, by decide⟩,⟨922957, by decide⟩,⟨923015, by decide⟩,⟨923116, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17767_923117 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17767 ⟨923117, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17767
    ⟨923117, by decide⟩ (by decide) (![⟨922901, by decide⟩,⟨922957, by decide⟩,⟨923015, by decide⟩,⟨923116, by decide⟩]) unmarked_context_10_17767_923117 node_context_10_17767_923117
  intro a
  fin_cases a
  · exact context_11_71068_922901
  · exact context_11_71069_922957
  · exact context_11_71070_923015
  · exact context_11_71071_923116

theorem unmarked_context_9_4441_923118 : frontier 12 ⟨923118, by decide⟩
    (prefixCache 9 4441) (prefixPartial 9 4441) = false := by
  decide +kernel

theorem node_context_9_4441_923118 : EJMOriginalGlobalDAGData.nodes 12 ⟨923118, by decide⟩ =
    .split (coordinate 9) (![⟨922432, by decide⟩,⟨893098, by decide⟩,⟨922822, by decide⟩,⟨923117, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4441_923118 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4441 ⟨923118, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4441
    ⟨923118, by decide⟩ (by decide) (![⟨922432, by decide⟩,⟨893098, by decide⟩,⟨922822, by decide⟩,⟨923117, by decide⟩]) unmarked_context_9_4441_923118 node_context_9_4441_923118
  intro a
  fin_cases a
  · exact context_10_17764_922432
  · exact context_10_17765_893098
  · exact context_10_17766_922822
  · exact context_10_17767_923117

theorem selected_cut_35207 : selected 9 ⟨923150, by decide⟩
    (prefixPartial 12 284288) = some ⟨12, 2, 0, 923150, 284288, 1805, 65536⟩ := by
  decide +kernel

theorem context_12_284288_923150 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284288 ⟨923150, by decide⟩ :=
  accepted_of_selected 12 284288 ⟨923150, by decide⟩ ⟨12, 2, 0, 923150, 284288, 1805, 65536⟩
    (by decide) selected_cut_35207

theorem selected_cut_35208 : selected 9 ⟨923163, by decide⟩
    (prefixPartial 12 284289) = some ⟨12, 2, 0, 923163, 284289, 1221, 65536⟩ := by
  decide +kernel

theorem context_12_284289_923163 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284289 ⟨923163, by decide⟩ :=
  accepted_of_selected 12 284289 ⟨923163, by decide⟩ ⟨12, 2, 0, 923163, 284289, 1221, 65536⟩
    (by decide) selected_cut_35208

theorem selected_cut_35209 : selected 9 ⟨923179, by decide⟩
    (prefixPartial 12 284290) = some ⟨12, 2, 0, 923179, 284290, 1261, 65536⟩ := by
  decide +kernel

theorem context_12_284290_923179 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284290 ⟨923179, by decide⟩ :=
  accepted_of_selected 12 284290 ⟨923179, by decide⟩ ⟨12, 2, 0, 923179, 284290, 1261, 65536⟩
    (by decide) selected_cut_35209

theorem selected_cut_35210 : selected 9 ⟨923197, by decide⟩
    (prefixPartial 12 284291) = some ⟨12, 2, 0, 923197, 284291, 1453, 65536⟩ := by
  decide +kernel

theorem context_12_284291_923197 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284291 ⟨923197, by decide⟩ :=
  accepted_of_selected 12 284291 ⟨923197, by decide⟩ ⟨12, 2, 0, 923197, 284291, 1453, 65536⟩
    (by decide) selected_cut_35210

theorem unmarked_context_11_71072_923198 : frontier 10 ⟨923198, by decide⟩
    (prefixCache 11 71072) (prefixPartial 11 71072) = false := by
  decide +kernel

theorem node_context_11_71072_923198 : EJMOriginalGlobalDAGData.nodes 10 ⟨923198, by decide⟩ =
    .split (coordinate 11) (![⟨923150, by decide⟩,⟨923163, by decide⟩,⟨923179, by decide⟩,⟨923197, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71072_923198 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71072 ⟨923198, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71072
    ⟨923198, by decide⟩ (by decide) (![⟨923150, by decide⟩,⟨923163, by decide⟩,⟨923179, by decide⟩,⟨923197, by decide⟩]) unmarked_context_11_71072_923198 node_context_11_71072_923198
  intro a
  fin_cases a
  · exact context_12_284288_923150
  · exact context_12_284289_923163
  · exact context_12_284290_923179
  · exact context_12_284291_923197

theorem selected_cut_35211 : selected 9 ⟨923225, by decide⟩
    (prefixPartial 12 284292) = some ⟨12, 2, 0, 923225, 284292, 1573, 65536⟩ := by
  decide +kernel

theorem context_12_284292_923225 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284292 ⟨923225, by decide⟩ :=
  accepted_of_selected 12 284292 ⟨923225, by decide⟩ ⟨12, 2, 0, 923225, 284292, 1573, 65536⟩
    (by decide) selected_cut_35211

theorem selected_cut_35212 : selected 9 ⟨923240, by decide⟩
    (prefixPartial 12 284293) = some ⟨12, 2, 0, 923240, 284293, 1125, 65536⟩ := by
  decide +kernel

theorem context_12_284293_923240 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284293 ⟨923240, by decide⟩ :=
  accepted_of_selected 12 284293 ⟨923240, by decide⟩ ⟨12, 2, 0, 923240, 284293, 1125, 65536⟩
    (by decide) selected_cut_35212

theorem selected_cut_35213 : selected 9 ⟨923255, by decide⟩
    (prefixPartial 12 284294) = some ⟨12, 2, 0, 923255, 284294, 1197, 65536⟩ := by
  decide +kernel

theorem context_12_284294_923255 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284294 ⟨923255, by decide⟩ :=
  accepted_of_selected 12 284294 ⟨923255, by decide⟩ ⟨12, 2, 0, 923255, 284294, 1197, 65536⟩
    (by decide) selected_cut_35213

theorem selected_cut_35214 : selected 9 ⟨923273, by decide⟩
    (prefixPartial 12 284295) = some ⟨12, 2, 0, 923273, 284295, 1245, 65536⟩ := by
  decide +kernel

theorem context_12_284295_923273 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284295 ⟨923273, by decide⟩ :=
  accepted_of_selected 12 284295 ⟨923273, by decide⟩ ⟨12, 2, 0, 923273, 284295, 1245, 65536⟩
    (by decide) selected_cut_35214

theorem unmarked_context_11_71073_923274 : frontier 10 ⟨923274, by decide⟩
    (prefixCache 11 71073) (prefixPartial 11 71073) = false := by
  decide +kernel

theorem node_context_11_71073_923274 : EJMOriginalGlobalDAGData.nodes 10 ⟨923274, by decide⟩ =
    .split (coordinate 11) (![⟨923225, by decide⟩,⟨923240, by decide⟩,⟨923255, by decide⟩,⟨923273, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71073_923274 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71073 ⟨923274, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71073
    ⟨923274, by decide⟩ (by decide) (![⟨923225, by decide⟩,⟨923240, by decide⟩,⟨923255, by decide⟩,⟨923273, by decide⟩]) unmarked_context_11_71073_923274 node_context_11_71073_923274
  intro a
  fin_cases a
  · exact context_12_284292_923225
  · exact context_12_284293_923240
  · exact context_12_284294_923255
  · exact context_12_284295_923273

theorem selected_cut_35215 : selected 9 ⟨923311, by decide⟩
    (prefixPartial 12 284296) = some ⟨12, 2, 0, 923311, 284296, 1669, 65536⟩ := by
  decide +kernel

theorem context_12_284296_923311 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284296 ⟨923311, by decide⟩ :=
  accepted_of_selected 12 284296 ⟨923311, by decide⟩ ⟨12, 2, 0, 923311, 284296, 1669, 65536⟩
    (by decide) selected_cut_35215

theorem selected_cut_35216 : selected 9 ⟨923323, by decide⟩
    (prefixPartial 12 284297) = some ⟨12, 2, 0, 923323, 284297, 1137, 65536⟩ := by
  decide +kernel

theorem context_12_284297_923323 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284297 ⟨923323, by decide⟩ :=
  accepted_of_selected 12 284297 ⟨923323, by decide⟩ ⟨12, 2, 0, 923323, 284297, 1137, 65536⟩
    (by decide) selected_cut_35216

theorem selected_cut_35217 : selected 9 ⟨893903, by decide⟩
    (prefixPartial 12 284298) = some ⟨12, 1, 0, 893903, 284298, 1, 65536⟩ := by
  decide +kernel

theorem context_12_284298_893903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284298 ⟨893903, by decide⟩ :=
  accepted_of_selected 12 284298 ⟨893903, by decide⟩ ⟨12, 1, 0, 893903, 284298, 1, 65536⟩
    (by decide) selected_cut_35217

theorem selected_cut_35218 : selected 9 ⟨923343, by decide⟩
    (prefixPartial 12 284299) = some ⟨12, 2, 0, 923343, 284299, 1341, 65536⟩ := by
  decide +kernel

theorem context_12_284299_923343 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284299 ⟨923343, by decide⟩ :=
  accepted_of_selected 12 284299 ⟨923343, by decide⟩ ⟨12, 2, 0, 923343, 284299, 1341, 65536⟩
    (by decide) selected_cut_35218

theorem unmarked_context_11_71074_923344 : frontier 10 ⟨923344, by decide⟩
    (prefixCache 11 71074) (prefixPartial 11 71074) = false := by
  decide +kernel

theorem node_context_11_71074_923344 : EJMOriginalGlobalDAGData.nodes 10 ⟨923344, by decide⟩ =
    .split (coordinate 11) (![⟨923311, by decide⟩,⟨923323, by decide⟩,⟨893903, by decide⟩,⟨923343, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71074_923344 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71074 ⟨923344, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71074
    ⟨923344, by decide⟩ (by decide) (![⟨923311, by decide⟩,⟨923323, by decide⟩,⟨893903, by decide⟩,⟨923343, by decide⟩]) unmarked_context_11_71074_923344 node_context_11_71074_923344
  intro a
  fin_cases a
  · exact context_12_284296_923311
  · exact context_12_284297_923323
  · exact context_12_284298_893903
  · exact context_12_284299_923343

theorem selected_cut_35219 : selected 9 ⟨923373, by decide⟩
    (prefixPartial 12 284300) = some ⟨12, 2, 0, 923373, 284300, 1725, 65536⟩ := by
  decide +kernel

theorem context_12_284300_923373 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284300 ⟨923373, by decide⟩ :=
  accepted_of_selected 12 284300 ⟨923373, by decide⟩ ⟨12, 2, 0, 923373, 284300, 1725, 65536⟩
    (by decide) selected_cut_35219

theorem selected_cut_35220 : selected 9 ⟨923392, by decide⟩
    (prefixPartial 12 284301) = some ⟨12, 2, 0, 923392, 284301, 1165, 65536⟩ := by
  decide +kernel

theorem context_12_284301_923392 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284301 ⟨923392, by decide⟩ :=
  accepted_of_selected 12 284301 ⟨923392, by decide⟩ ⟨12, 2, 0, 923392, 284301, 1165, 65536⟩
    (by decide) selected_cut_35220

theorem selected_cut_35221 : selected 9 ⟨923409, by decide⟩
    (prefixPartial 12 284302) = some ⟨12, 2, 0, 923409, 284302, 1257, 65536⟩ := by
  decide +kernel

theorem context_12_284302_923409 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284302 ⟨923409, by decide⟩ :=
  accepted_of_selected 12 284302 ⟨923409, by decide⟩ ⟨12, 2, 0, 923409, 284302, 1257, 65536⟩
    (by decide) selected_cut_35221

theorem selected_cut_35222 : selected 9 ⟨923425, by decide⟩
    (prefixPartial 12 284303) = some ⟨12, 2, 0, 923425, 284303, 1241, 65536⟩ := by
  decide +kernel

theorem context_12_284303_923425 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284303 ⟨923425, by decide⟩ :=
  accepted_of_selected 12 284303 ⟨923425, by decide⟩ ⟨12, 2, 0, 923425, 284303, 1241, 65536⟩
    (by decide) selected_cut_35222

theorem unmarked_context_11_71075_923426 : frontier 10 ⟨923426, by decide⟩
    (prefixCache 11 71075) (prefixPartial 11 71075) = false := by
  decide +kernel

theorem node_context_11_71075_923426 : EJMOriginalGlobalDAGData.nodes 10 ⟨923426, by decide⟩ =
    .split (coordinate 11) (![⟨923373, by decide⟩,⟨923392, by decide⟩,⟨923409, by decide⟩,⟨923425, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71075_923426 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71075 ⟨923426, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71075
    ⟨923426, by decide⟩ (by decide) (![⟨923373, by decide⟩,⟨923392, by decide⟩,⟨923409, by decide⟩,⟨923425, by decide⟩]) unmarked_context_11_71075_923426 node_context_11_71075_923426
  intro a
  fin_cases a
  · exact context_12_284300_923373
  · exact context_12_284301_923392
  · exact context_12_284302_923409
  · exact context_12_284303_923425

theorem unmarked_context_10_17768_923427 : frontier 11 ⟨923427, by decide⟩
    (prefixCache 10 17768) (prefixPartial 10 17768) = false := by
  decide +kernel

theorem node_context_10_17768_923427 : EJMOriginalGlobalDAGData.nodes 11 ⟨923427, by decide⟩ =
    .split (coordinate 10) (![⟨923198, by decide⟩,⟨923274, by decide⟩,⟨923344, by decide⟩,⟨923426, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17768_923427 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17768 ⟨923427, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17768
    ⟨923427, by decide⟩ (by decide) (![⟨923198, by decide⟩,⟨923274, by decide⟩,⟨923344, by decide⟩,⟨923426, by decide⟩]) unmarked_context_10_17768_923427 node_context_10_17768_923427
  intro a
  fin_cases a
  · exact context_11_71072_923198
  · exact context_11_71073_923274
  · exact context_11_71074_923344
  · exact context_11_71075_923426

theorem selected_cut_35223 : selected 9 ⟨923448, by decide⟩
    (prefixPartial 12 284304) = some ⟨12, 2, 0, 923448, 284304, 1277, 65536⟩ := by
  decide +kernel

theorem context_12_284304_923448 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284304 ⟨923448, by decide⟩ :=
  accepted_of_selected 12 284304 ⟨923448, by decide⟩ ⟨12, 2, 0, 923448, 284304, 1277, 65536⟩
    (by decide) selected_cut_35223

theorem selected_cut_35224 : selected 9 ⟨923464, by decide⟩
    (prefixPartial 12 284305) = some ⟨12, 2, 0, 923464, 284305, 1001, 65536⟩ := by
  decide +kernel

theorem context_12_284305_923464 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284305 ⟨923464, by decide⟩ :=
  accepted_of_selected 12 284305 ⟨923464, by decide⟩ ⟨12, 2, 0, 923464, 284305, 1001, 65536⟩
    (by decide) selected_cut_35224

theorem selected_cut_35225 : selected 9 ⟨923477, by decide⟩
    (prefixPartial 12 284306) = some ⟨12, 2, 0, 923477, 284306, 1089, 65536⟩ := by
  decide +kernel

theorem context_12_284306_923477 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284306 ⟨923477, by decide⟩ :=
  accepted_of_selected 12 284306 ⟨923477, by decide⟩ ⟨12, 2, 0, 923477, 284306, 1089, 65536⟩
    (by decide) selected_cut_35225

theorem selected_cut_35226 : selected 9 ⟨923493, by decide⟩
    (prefixPartial 12 284307) = some ⟨12, 2, 0, 923493, 284307, 1205, 65536⟩ := by
  decide +kernel

theorem context_12_284307_923493 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284307 ⟨923493, by decide⟩ :=
  accepted_of_selected 12 284307 ⟨923493, by decide⟩ ⟨12, 2, 0, 923493, 284307, 1205, 65536⟩
    (by decide) selected_cut_35226

theorem unmarked_context_11_71076_923494 : frontier 10 ⟨923494, by decide⟩
    (prefixCache 11 71076) (prefixPartial 11 71076) = false := by
  decide +kernel

theorem node_context_11_71076_923494 : EJMOriginalGlobalDAGData.nodes 10 ⟨923494, by decide⟩ =
    .split (coordinate 11) (![⟨923448, by decide⟩,⟨923464, by decide⟩,⟨923477, by decide⟩,⟨923493, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71076_923494 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71076 ⟨923494, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71076
    ⟨923494, by decide⟩ (by decide) (![⟨923448, by decide⟩,⟨923464, by decide⟩,⟨923477, by decide⟩,⟨923493, by decide⟩]) unmarked_context_11_71076_923494 node_context_11_71076_923494
  intro a
  fin_cases a
  · exact context_12_284304_923448
  · exact context_12_284305_923464
  · exact context_12_284306_923477
  · exact context_12_284307_923493

theorem selected_cut_35227 : selected 10 ⟨892405, by decide⟩
    (prefixPartial 11 71077) = some ⟨11, 1, 0, 892405, 71077, 1, 262144⟩ := by
  decide +kernel

theorem context_11_71077_892405 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71077 ⟨892405, by decide⟩ :=
  accepted_of_selected 11 71077 ⟨892405, by decide⟩ ⟨11, 1, 0, 892405, 71077, 1, 262144⟩
    (by decide) selected_cut_35227

theorem selected_cut_35228 : selected 10 ⟨923542, by decide⟩
    (prefixPartial 11 71078) = some ⟨11, 2, 0, 923542, 71078, 3337, 262144⟩ := by
  decide +kernel

theorem context_11_71078_923542 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71078 ⟨923542, by decide⟩ :=
  accepted_of_selected 11 71078 ⟨923542, by decide⟩ ⟨11, 2, 0, 923542, 71078, 3337, 262144⟩
    (by decide) selected_cut_35228

theorem selected_cut_35229 : selected 9 ⟨923563, by decide⟩
    (prefixPartial 12 284316) = some ⟨12, 2, 0, 923563, 284316, 1293, 65536⟩ := by
  decide +kernel

theorem context_12_284316_923563 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284316 ⟨923563, by decide⟩ :=
  accepted_of_selected 12 284316 ⟨923563, by decide⟩ ⟨12, 2, 0, 923563, 284316, 1293, 65536⟩
    (by decide) selected_cut_35229

theorem selected_cut_35230 : selected 9 ⟨923575, by decide⟩
    (prefixPartial 12 284317) = some ⟨12, 2, 0, 923575, 284317, 889, 65536⟩ := by
  decide +kernel

theorem context_12_284317_923575 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284317 ⟨923575, by decide⟩ :=
  accepted_of_selected 12 284317 ⟨923575, by decide⟩ ⟨12, 2, 0, 923575, 284317, 889, 65536⟩
    (by decide) selected_cut_35230

theorem selected_cut_35231 : selected 9 ⟨923590, by decide⟩
    (prefixPartial 12 284318) = some ⟨12, 2, 0, 923590, 284318, 1045, 65536⟩ := by
  decide +kernel

theorem context_12_284318_923590 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284318 ⟨923590, by decide⟩ :=
  accepted_of_selected 12 284318 ⟨923590, by decide⟩ ⟨12, 2, 0, 923590, 284318, 1045, 65536⟩
    (by decide) selected_cut_35231

theorem selected_cut_35232 : selected 9 ⟨923608, by decide⟩
    (prefixPartial 12 284319) = some ⟨12, 2, 0, 923608, 284319, 1077, 65536⟩ := by
  decide +kernel

theorem context_12_284319_923608 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 284319 ⟨923608, by decide⟩ :=
  accepted_of_selected 12 284319 ⟨923608, by decide⟩ ⟨12, 2, 0, 923608, 284319, 1077, 65536⟩
    (by decide) selected_cut_35232

theorem unmarked_context_11_71079_923609 : frontier 10 ⟨923609, by decide⟩
    (prefixCache 11 71079) (prefixPartial 11 71079) = false := by
  decide +kernel

theorem node_context_11_71079_923609 : EJMOriginalGlobalDAGData.nodes 10 ⟨923609, by decide⟩ =
    .split (coordinate 11) (![⟨923563, by decide⟩,⟨923575, by decide⟩,⟨923590, by decide⟩,⟨923608, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71079_923609 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71079 ⟨923609, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71079
    ⟨923609, by decide⟩ (by decide) (![⟨923563, by decide⟩,⟨923575, by decide⟩,⟨923590, by decide⟩,⟨923608, by decide⟩]) unmarked_context_11_71079_923609 node_context_11_71079_923609
  intro a
  fin_cases a
  · exact context_12_284316_923563
  · exact context_12_284317_923575
  · exact context_12_284318_923590
  · exact context_12_284319_923608

theorem unmarked_context_10_17769_923610 : frontier 11 ⟨923610, by decide⟩
    (prefixCache 10 17769) (prefixPartial 10 17769) = false := by
  decide +kernel

theorem node_context_10_17769_923610 : EJMOriginalGlobalDAGData.nodes 11 ⟨923610, by decide⟩ =
    .split (coordinate 10) (![⟨923494, by decide⟩,⟨892405, by decide⟩,⟨923542, by decide⟩,⟨923609, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17769_923610 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17769 ⟨923610, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17769
    ⟨923610, by decide⟩ (by decide) (![⟨923494, by decide⟩,⟨892405, by decide⟩,⟨923542, by decide⟩,⟨923609, by decide⟩]) unmarked_context_10_17769_923610 node_context_10_17769_923610
  intro a
  fin_cases a
  · exact context_11_71076_923494
  · exact context_11_71077_892405
  · exact context_11_71078_923542
  · exact context_11_71079_923609

theorem selected_cut_35233 : selected 10 ⟨923658, by decide⟩
    (prefixPartial 11 71080) = some ⟨11, 2, 0, 923658, 71080, 3805, 262144⟩ := by
  decide +kernel

theorem context_11_71080_923658 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71080 ⟨923658, by decide⟩ :=
  accepted_of_selected 11 71080 ⟨923658, by decide⟩ ⟨11, 2, 0, 923658, 71080, 3805, 262144⟩
    (by decide) selected_cut_35233

theorem selected_cut_35234 : selected 10 ⟨923681, by decide⟩
    (prefixPartial 11 71081) = some ⟨11, 2, 0, 923681, 71081, 2393, 262144⟩ := by
  decide +kernel

theorem context_11_71081_923681 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71081 ⟨923681, by decide⟩ :=
  accepted_of_selected 11 71081 ⟨923681, by decide⟩ ⟨11, 2, 0, 923681, 71081, 2393, 262144⟩
    (by decide) selected_cut_35234

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
