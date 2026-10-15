/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover210
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_20258 : selected 8 ⟨518596, by decide⟩
    (prefixPartial 13 295001) = some ⟨13, 2, 0, 518596, 295001, 1721, 16384⟩ := by
  decide +kernel

theorem context_13_295001_518596 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 295001 ⟨518596, by decide⟩ :=
  accepted_of_selected 13 295001 ⟨518596, by decide⟩ ⟨13, 2, 0, 518596, 295001, 1721, 16384⟩
    (by decide) selected_cut_20258

theorem selected_cut_20259 : selected 8 ⟨518616, by decide⟩
    (prefixPartial 13 295002) = some ⟨13, 2, 0, 518616, 295002, 1273, 16384⟩ := by
  decide +kernel

theorem context_13_295002_518616 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 295002 ⟨518616, by decide⟩ :=
  accepted_of_selected 13 295002 ⟨518616, by decide⟩ ⟨13, 2, 0, 518616, 295002, 1273, 16384⟩
    (by decide) selected_cut_20259

theorem selected_cut_20260 : selected 8 ⟨518621, by decide⟩
    (prefixPartial 13 295003) = some ⟨13, 2, 0, 518621, 295003, 773, 16384⟩ := by
  decide +kernel

theorem context_13_295003_518621 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 295003 ⟨518621, by decide⟩ :=
  accepted_of_selected 13 295003 ⟨518621, by decide⟩ ⟨13, 2, 0, 518621, 295003, 773, 16384⟩
    (by decide) selected_cut_20260

theorem unmarked_context_12_73750_518622 : frontier 9 ⟨518622, by decide⟩
    (prefixCache 12 73750) (prefixPartial 12 73750) = false := by
  decide +kernel

theorem node_context_12_73750_518622 : EJMOriginalGlobalDAGData.nodes 9 ⟨518622, by decide⟩ =
    .split (coordinate 12) (![⟨518572, by decide⟩,⟨518596, by decide⟩,⟨518616, by decide⟩,⟨518621, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_73750_518622 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 73750 ⟨518622, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 73750
    ⟨518622, by decide⟩ (by decide) (![⟨518572, by decide⟩,⟨518596, by decide⟩,⟨518616, by decide⟩,⟨518621, by decide⟩]) unmarked_context_12_73750_518622 node_context_12_73750_518622
  intro a
  fin_cases a
  · exact context_13_295000_518572
  · exact context_13_295001_518596
  · exact context_13_295002_518616
  · exact context_13_295003_518621

theorem selected_cut_20261 : selected 8 ⟨518648, by decide⟩
    (prefixPartial 13 295004) = some ⟨13, 2, 0, 518648, 295004, 1201, 16384⟩ := by
  decide +kernel

theorem context_13_295004_518648 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 295004 ⟨518648, by decide⟩ :=
  accepted_of_selected 13 295004 ⟨518648, by decide⟩ ⟨13, 2, 0, 518648, 295004, 1201, 16384⟩
    (by decide) selected_cut_20261

theorem selected_cut_20262 : selected 8 ⟨518671, by decide⟩
    (prefixPartial 13 295005) = some ⟨13, 2, 0, 518671, 295005, 1905, 16384⟩ := by
  decide +kernel

theorem context_13_295005_518671 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 295005 ⟨518671, by decide⟩ :=
  accepted_of_selected 13 295005 ⟨518671, by decide⟩ ⟨13, 2, 0, 518671, 295005, 1905, 16384⟩
    (by decide) selected_cut_20262

theorem selected_cut_20263 : selected 8 ⟨518701, by decide⟩
    (prefixPartial 13 295006) = some ⟨13, 2, 0, 518701, 295006, 1649, 16384⟩ := by
  decide +kernel

theorem context_13_295006_518701 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 295006 ⟨518701, by decide⟩ :=
  accepted_of_selected 13 295006 ⟨518701, by decide⟩ ⟨13, 2, 0, 518701, 295006, 1649, 16384⟩
    (by decide) selected_cut_20263

theorem selected_cut_20264 : selected 8 ⟨518707, by decide⟩
    (prefixPartial 13 295007) = some ⟨13, 2, 0, 518707, 295007, 633, 16384⟩ := by
  decide +kernel

theorem context_13_295007_518707 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 295007 ⟨518707, by decide⟩ :=
  accepted_of_selected 13 295007 ⟨518707, by decide⟩ ⟨13, 2, 0, 518707, 295007, 633, 16384⟩
    (by decide) selected_cut_20264

theorem unmarked_context_12_73751_518708 : frontier 9 ⟨518708, by decide⟩
    (prefixCache 12 73751) (prefixPartial 12 73751) = false := by
  decide +kernel

theorem node_context_12_73751_518708 : EJMOriginalGlobalDAGData.nodes 9 ⟨518708, by decide⟩ =
    .split (coordinate 12) (![⟨518648, by decide⟩,⟨518671, by decide⟩,⟨518701, by decide⟩,⟨518707, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_73751_518708 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 73751 ⟨518708, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 73751
    ⟨518708, by decide⟩ (by decide) (![⟨518648, by decide⟩,⟨518671, by decide⟩,⟨518701, by decide⟩,⟨518707, by decide⟩]) unmarked_context_12_73751_518708 node_context_12_73751_518708
  intro a
  fin_cases a
  · exact context_13_295004_518648
  · exact context_13_295005_518671
  · exact context_13_295006_518701
  · exact context_13_295007_518707

theorem unmarked_context_11_18437_518709 : frontier 10 ⟨518709, by decide⟩
    (prefixCache 11 18437) (prefixPartial 11 18437) = false := by
  decide +kernel

theorem node_context_11_18437_518709 : EJMOriginalGlobalDAGData.nodes 10 ⟨518709, by decide⟩ =
    .split (coordinate 11) (![⟨435160, by decide⟩,⟨518546, by decide⟩,⟨518622, by decide⟩,⟨518708, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18437_518709 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18437 ⟨518709, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18437
    ⟨518709, by decide⟩ (by decide) (![⟨435160, by decide⟩,⟨518546, by decide⟩,⟨518622, by decide⟩,⟨518708, by decide⟩]) unmarked_context_11_18437_518709 node_context_11_18437_518709
  intro a
  fin_cases a
  · exact context_12_73748_435160
  · exact context_12_73749_518546
  · exact context_12_73750_518622
  · exact context_12_73751_518708

theorem selected_cut_20265 : selected 9 ⟨518820, by decide⟩
    (prefixPartial 12 73752) = some ⟨12, 2, 0, 518820, 73752, 3437, 65536⟩ := by
  decide +kernel

theorem context_12_73752_518820 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 73752 ⟨518820, by decide⟩ :=
  accepted_of_selected 12 73752 ⟨518820, by decide⟩ ⟨12, 2, 0, 518820, 73752, 3437, 65536⟩
    (by decide) selected_cut_20265

theorem selected_cut_20266 : selected 8 ⟨518851, by decide⟩
    (prefixPartial 13 295012) = some ⟨13, 2, 0, 518851, 295012, 1329, 16384⟩ := by
  decide +kernel

theorem context_13_295012_518851 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 295012 ⟨518851, by decide⟩ :=
  accepted_of_selected 13 295012 ⟨518851, by decide⟩ ⟨13, 2, 0, 518851, 295012, 1329, 16384⟩
    (by decide) selected_cut_20266

theorem selected_cut_20267 : selected 8 ⟨518873, by decide⟩
    (prefixPartial 13 295013) = some ⟨13, 2, 0, 518873, 295013, 1377, 16384⟩ := by
  decide +kernel

theorem context_13_295013_518873 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 295013 ⟨518873, by decide⟩ :=
  accepted_of_selected 13 295013 ⟨518873, by decide⟩ ⟨13, 2, 0, 518873, 295013, 1377, 16384⟩
    (by decide) selected_cut_20267

theorem selected_cut_20268 : selected 8 ⟨518897, by decide⟩
    (prefixPartial 13 295014) = some ⟨13, 2, 0, 518897, 295014, 1513, 16384⟩ := by
  decide +kernel

theorem context_13_295014_518897 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 295014 ⟨518897, by decide⟩ :=
  accepted_of_selected 13 295014 ⟨518897, by decide⟩ ⟨13, 2, 0, 518897, 295014, 1513, 16384⟩
    (by decide) selected_cut_20268

theorem selected_cut_20269 : selected 8 ⟨518908, by decide⟩
    (prefixPartial 13 295015) = some ⟨13, 2, 0, 518908, 295015, 717, 16384⟩ := by
  decide +kernel

theorem context_13_295015_518908 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 295015 ⟨518908, by decide⟩ :=
  accepted_of_selected 13 295015 ⟨518908, by decide⟩ ⟨13, 2, 0, 518908, 295015, 717, 16384⟩
    (by decide) selected_cut_20269

theorem unmarked_context_12_73753_518909 : frontier 9 ⟨518909, by decide⟩
    (prefixCache 12 73753) (prefixPartial 12 73753) = false := by
  decide +kernel

theorem node_context_12_73753_518909 : EJMOriginalGlobalDAGData.nodes 9 ⟨518909, by decide⟩ =
    .split (coordinate 12) (![⟨518851, by decide⟩,⟨518873, by decide⟩,⟨518897, by decide⟩,⟨518908, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_73753_518909 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 73753 ⟨518909, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 73753
    ⟨518909, by decide⟩ (by decide) (![⟨518851, by decide⟩,⟨518873, by decide⟩,⟨518897, by decide⟩,⟨518908, by decide⟩]) unmarked_context_12_73753_518909 node_context_12_73753_518909
  intro a
  fin_cases a
  · exact context_13_295012_518851
  · exact context_13_295013_518873
  · exact context_13_295014_518897
  · exact context_13_295015_518908

theorem selected_cut_20270 : selected 9 ⟨518960, by decide⟩
    (prefixPartial 12 73754) = some ⟨12, 2, 0, 518960, 73754, 3733, 65536⟩ := by
  decide +kernel

theorem context_12_73754_518960 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 73754 ⟨518960, by decide⟩ :=
  accepted_of_selected 12 73754 ⟨518960, by decide⟩ ⟨12, 2, 0, 518960, 73754, 3733, 65536⟩
    (by decide) selected_cut_20270

theorem selected_cut_20271 : selected 8 ⟨518981, by decide⟩
    (prefixPartial 13 295020) = some ⟨13, 2, 0, 518981, 295020, 921, 16384⟩ := by
  decide +kernel

theorem context_13_295020_518981 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 295020 ⟨518981, by decide⟩ :=
  accepted_of_selected 13 295020 ⟨518981, by decide⟩ ⟨13, 2, 0, 518981, 295020, 921, 16384⟩
    (by decide) selected_cut_20271

theorem selected_cut_20272 : selected 8 ⟨519006, by decide⟩
    (prefixPartial 13 295021) = some ⟨13, 2, 0, 519006, 295021, 1877, 16384⟩ := by
  decide +kernel

theorem context_13_295021_519006 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 295021 ⟨519006, by decide⟩ :=
  accepted_of_selected 13 295021 ⟨519006, by decide⟩ ⟨13, 2, 0, 519006, 295021, 1877, 16384⟩
    (by decide) selected_cut_20272

theorem selected_cut_20273 : selected 8 ⟨519026, by decide⟩
    (prefixPartial 13 295022) = some ⟨13, 2, 0, 519026, 295022, 1149, 16384⟩ := by
  decide +kernel

theorem context_13_295022_519026 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 295022 ⟨519026, by decide⟩ :=
  accepted_of_selected 13 295022 ⟨519026, by decide⟩ ⟨13, 2, 0, 519026, 295022, 1149, 16384⟩
    (by decide) selected_cut_20273

theorem selected_cut_20274 : selected 8 ⟨519027, by decide⟩
    (prefixPartial 13 295023) = some ⟨13, 2, 0, 519027, 295023, 577, 16384⟩ := by
  decide +kernel

theorem context_13_295023_519027 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 295023 ⟨519027, by decide⟩ :=
  accepted_of_selected 13 295023 ⟨519027, by decide⟩ ⟨13, 2, 0, 519027, 295023, 577, 16384⟩
    (by decide) selected_cut_20274

theorem unmarked_context_12_73755_519028 : frontier 9 ⟨519028, by decide⟩
    (prefixCache 12 73755) (prefixPartial 12 73755) = false := by
  decide +kernel

theorem node_context_12_73755_519028 : EJMOriginalGlobalDAGData.nodes 9 ⟨519028, by decide⟩ =
    .split (coordinate 12) (![⟨518981, by decide⟩,⟨519006, by decide⟩,⟨519026, by decide⟩,⟨519027, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_73755_519028 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 73755 ⟨519028, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 73755
    ⟨519028, by decide⟩ (by decide) (![⟨518981, by decide⟩,⟨519006, by decide⟩,⟨519026, by decide⟩,⟨519027, by decide⟩]) unmarked_context_12_73755_519028 node_context_12_73755_519028
  intro a
  fin_cases a
  · exact context_13_295020_518981
  · exact context_13_295021_519006
  · exact context_13_295022_519026
  · exact context_13_295023_519027

theorem unmarked_context_11_18438_519029 : frontier 10 ⟨519029, by decide⟩
    (prefixCache 11 18438) (prefixPartial 11 18438) = false := by
  decide +kernel

theorem node_context_11_18438_519029 : EJMOriginalGlobalDAGData.nodes 10 ⟨519029, by decide⟩ =
    .split (coordinate 11) (![⟨518820, by decide⟩,⟨518909, by decide⟩,⟨518960, by decide⟩,⟨519028, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18438_519029 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18438 ⟨519029, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18438
    ⟨519029, by decide⟩ (by decide) (![⟨518820, by decide⟩,⟨518909, by decide⟩,⟨518960, by decide⟩,⟨519028, by decide⟩]) unmarked_context_11_18438_519029 node_context_11_18438_519029
  intro a
  fin_cases a
  · exact context_12_73752_518820
  · exact context_12_73753_518909
  · exact context_12_73754_518960
  · exact context_12_73755_519028

theorem selected_cut_20275 : selected 9 ⟨519115, by decide⟩
    (prefixPartial 12 73756) = some ⟨12, 2, 0, 519115, 73756, 3161, 65536⟩ := by
  decide +kernel

theorem context_12_73756_519115 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 73756 ⟨519115, by decide⟩ :=
  accepted_of_selected 12 73756 ⟨519115, by decide⟩ ⟨12, 2, 0, 519115, 73756, 3161, 65536⟩
    (by decide) selected_cut_20275

theorem selected_cut_20276 : selected 8 ⟨519138, by decide⟩
    (prefixPartial 13 295028) = some ⟨13, 2, 0, 519138, 295028, 1109, 16384⟩ := by
  decide +kernel

theorem context_13_295028_519138 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 295028 ⟨519138, by decide⟩ :=
  accepted_of_selected 13 295028 ⟨519138, by decide⟩ ⟨13, 2, 0, 519138, 295028, 1109, 16384⟩
    (by decide) selected_cut_20276

theorem selected_cut_20277 : selected 8 ⟨519170, by decide⟩
    (prefixPartial 13 295029) = some ⟨13, 2, 0, 519170, 295029, 1689, 16384⟩ := by
  decide +kernel

theorem context_13_295029_519170 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 295029 ⟨519170, by decide⟩ :=
  accepted_of_selected 13 295029 ⟨519170, by decide⟩ ⟨13, 2, 0, 519170, 295029, 1689, 16384⟩
    (by decide) selected_cut_20277

theorem selected_cut_20278 : selected 8 ⟨519188, by decide⟩
    (prefixPartial 13 295030) = some ⟨13, 2, 0, 519188, 295030, 1361, 16384⟩ := by
  decide +kernel

theorem context_13_295030_519188 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 295030 ⟨519188, by decide⟩ :=
  accepted_of_selected 13 295030 ⟨519188, by decide⟩ ⟨13, 2, 0, 519188, 295030, 1361, 16384⟩
    (by decide) selected_cut_20278

theorem selected_cut_20279 : selected 8 ⟨519200, by decide⟩
    (prefixPartial 13 295031) = some ⟨13, 2, 0, 519200, 295031, 741, 16384⟩ := by
  decide +kernel

theorem context_13_295031_519200 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 295031 ⟨519200, by decide⟩ :=
  accepted_of_selected 13 295031 ⟨519200, by decide⟩ ⟨13, 2, 0, 519200, 295031, 741, 16384⟩
    (by decide) selected_cut_20279

theorem unmarked_context_12_73757_519201 : frontier 9 ⟨519201, by decide⟩
    (prefixCache 12 73757) (prefixPartial 12 73757) = false := by
  decide +kernel

theorem node_context_12_73757_519201 : EJMOriginalGlobalDAGData.nodes 9 ⟨519201, by decide⟩ =
    .split (coordinate 12) (![⟨519138, by decide⟩,⟨519170, by decide⟩,⟨519188, by decide⟩,⟨519200, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_73757_519201 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 73757 ⟨519201, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 73757
    ⟨519201, by decide⟩ (by decide) (![⟨519138, by decide⟩,⟨519170, by decide⟩,⟨519188, by decide⟩,⟨519200, by decide⟩]) unmarked_context_12_73757_519201 node_context_12_73757_519201
  intro a
  fin_cases a
  · exact context_13_295028_519138
  · exact context_13_295029_519170
  · exact context_13_295030_519188
  · exact context_13_295031_519200

theorem selected_cut_20280 : selected 8 ⟨519217, by decide⟩
    (prefixPartial 13 295032) = some ⟨13, 2, 0, 519217, 295032, 805, 16384⟩ := by
  decide +kernel

theorem context_13_295032_519217 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 295032 ⟨519217, by decide⟩ :=
  accepted_of_selected 13 295032 ⟨519217, by decide⟩ ⟨13, 2, 0, 519217, 295032, 805, 16384⟩
    (by decide) selected_cut_20280

theorem selected_cut_20281 : selected 8 ⟨519240, by decide⟩
    (prefixPartial 13 295033) = some ⟨13, 2, 0, 519240, 295033, 1961, 16384⟩ := by
  decide +kernel

theorem context_13_295033_519240 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 295033 ⟨519240, by decide⟩ :=
  accepted_of_selected 13 295033 ⟨519240, by decide⟩ ⟨13, 2, 0, 519240, 295033, 1961, 16384⟩
    (by decide) selected_cut_20281

theorem selected_cut_20282 : selected 8 ⟨519253, by decide⟩
    (prefixPartial 13 295034) = some ⟨13, 2, 0, 519253, 295034, 941, 16384⟩ := by
  decide +kernel

theorem context_13_295034_519253 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 295034 ⟨519253, by decide⟩ :=
  accepted_of_selected 13 295034 ⟨519253, by decide⟩ ⟨13, 2, 0, 519253, 295034, 941, 16384⟩
    (by decide) selected_cut_20282

theorem selected_cut_20283 : selected 8 ⟨519258, by decide⟩
    (prefixPartial 13 295035) = some ⟨13, 2, 0, 519258, 295035, 733, 16384⟩ := by
  decide +kernel

theorem context_13_295035_519258 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 295035 ⟨519258, by decide⟩ :=
  accepted_of_selected 13 295035 ⟨519258, by decide⟩ ⟨13, 2, 0, 519258, 295035, 733, 16384⟩
    (by decide) selected_cut_20283

theorem unmarked_context_12_73758_519259 : frontier 9 ⟨519259, by decide⟩
    (prefixCache 12 73758) (prefixPartial 12 73758) = false := by
  decide +kernel

theorem node_context_12_73758_519259 : EJMOriginalGlobalDAGData.nodes 9 ⟨519259, by decide⟩ =
    .split (coordinate 12) (![⟨519217, by decide⟩,⟨519240, by decide⟩,⟨519253, by decide⟩,⟨519258, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_73758_519259 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 73758 ⟨519259, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 73758
    ⟨519259, by decide⟩ (by decide) (![⟨519217, by decide⟩,⟨519240, by decide⟩,⟨519253, by decide⟩,⟨519258, by decide⟩]) unmarked_context_12_73758_519259 node_context_12_73758_519259
  intro a
  fin_cases a
  · exact context_13_295032_519217
  · exact context_13_295033_519240
  · exact context_13_295034_519253
  · exact context_13_295035_519258

theorem selected_cut_20284 : selected 8 ⟨519277, by decide⟩
    (prefixPartial 13 295036) = some ⟨13, 2, 0, 519277, 295036, 825, 16384⟩ := by
  decide +kernel

theorem context_13_295036_519277 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 295036 ⟨519277, by decide⟩ :=
  accepted_of_selected 13 295036 ⟨519277, by decide⟩ ⟨13, 2, 0, 519277, 295036, 825, 16384⟩
    (by decide) selected_cut_20284

theorem selected_cut_20285 : selected 8 ⟨519298, by decide⟩
    (prefixPartial 13 295037) = some ⟨13, 2, 0, 519298, 295037, 1917, 16384⟩ := by
  decide +kernel

theorem context_13_295037_519298 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 295037 ⟨519298, by decide⟩ :=
  accepted_of_selected 13 295037 ⟨519298, by decide⟩ ⟨13, 2, 0, 519298, 295037, 1917, 16384⟩
    (by decide) selected_cut_20285

theorem selected_cut_20286 : selected 8 ⟨519312, by decide⟩
    (prefixPartial 13 295038) = some ⟨13, 2, 0, 519312, 295038, 1089, 16384⟩ := by
  decide +kernel

theorem context_13_295038_519312 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 295038 ⟨519312, by decide⟩ :=
  accepted_of_selected 13 295038 ⟨519312, by decide⟩ ⟨13, 2, 0, 519312, 295038, 1089, 16384⟩
    (by decide) selected_cut_20286

theorem selected_cut_20287 : selected 8 ⟨519315, by decide⟩
    (prefixPartial 13 295039) = some ⟨13, 2, 0, 519315, 295039, 605, 16384⟩ := by
  decide +kernel

theorem context_13_295039_519315 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 295039 ⟨519315, by decide⟩ :=
  accepted_of_selected 13 295039 ⟨519315, by decide⟩ ⟨13, 2, 0, 519315, 295039, 605, 16384⟩
    (by decide) selected_cut_20287

theorem unmarked_context_12_73759_519316 : frontier 9 ⟨519316, by decide⟩
    (prefixCache 12 73759) (prefixPartial 12 73759) = false := by
  decide +kernel

theorem node_context_12_73759_519316 : EJMOriginalGlobalDAGData.nodes 9 ⟨519316, by decide⟩ =
    .split (coordinate 12) (![⟨519277, by decide⟩,⟨519298, by decide⟩,⟨519312, by decide⟩,⟨519315, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_73759_519316 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 73759 ⟨519316, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 73759
    ⟨519316, by decide⟩ (by decide) (![⟨519277, by decide⟩,⟨519298, by decide⟩,⟨519312, by decide⟩,⟨519315, by decide⟩]) unmarked_context_12_73759_519316 node_context_12_73759_519316
  intro a
  fin_cases a
  · exact context_13_295036_519277
  · exact context_13_295037_519298
  · exact context_13_295038_519312
  · exact context_13_295039_519315

theorem unmarked_context_11_18439_519317 : frontier 10 ⟨519317, by decide⟩
    (prefixCache 11 18439) (prefixPartial 11 18439) = false := by
  decide +kernel

theorem node_context_11_18439_519317 : EJMOriginalGlobalDAGData.nodes 10 ⟨519317, by decide⟩ =
    .split (coordinate 11) (![⟨519115, by decide⟩,⟨519201, by decide⟩,⟨519259, by decide⟩,⟨519316, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18439_519317 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18439 ⟨519317, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18439
    ⟨519317, by decide⟩ (by decide) (![⟨519115, by decide⟩,⟨519201, by decide⟩,⟨519259, by decide⟩,⟨519316, by decide⟩]) unmarked_context_11_18439_519317 node_context_11_18439_519317
  intro a
  fin_cases a
  · exact context_12_73756_519115
  · exact context_12_73757_519201
  · exact context_12_73758_519259
  · exact context_12_73759_519316

theorem unmarked_context_10_4609_519318 : frontier 11 ⟨519318, by decide⟩
    (prefixCache 10 4609) (prefixPartial 10 4609) = false := by
  decide +kernel

theorem node_context_10_4609_519318 : EJMOriginalGlobalDAGData.nodes 11 ⟨519318, by decide⟩ =
    .split (coordinate 10) (![⟨518455, by decide⟩,⟨518709, by decide⟩,⟨519029, by decide⟩,⟨519317, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4609_519318 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4609 ⟨519318, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4609
    ⟨519318, by decide⟩ (by decide) (![⟨518455, by decide⟩,⟨518709, by decide⟩,⟨519029, by decide⟩,⟨519317, by decide⟩]) unmarked_context_10_4609_519318 node_context_10_4609_519318
  intro a
  fin_cases a
  · exact context_11_18436_518455
  · exact context_11_18437_518709
  · exact context_11_18438_519029
  · exact context_11_18439_519317

theorem selected_cut_20288 : selected 9 ⟨435790, by decide⟩
    (prefixPartial 12 73760) = some ⟨12, 1, 0, 435790, 73760, 1, 65536⟩ := by
  decide +kernel

theorem context_12_73760_435790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 73760 ⟨435790, by decide⟩ :=
  accepted_of_selected 12 73760 ⟨435790, by decide⟩ ⟨12, 1, 0, 435790, 73760, 1, 65536⟩
    (by decide) selected_cut_20288

theorem selected_cut_20289 : selected 9 ⟨519388, by decide⟩
    (prefixPartial 12 73761) = some ⟨12, 2, 0, 519388, 73761, 3025, 65536⟩ := by
  decide +kernel

theorem context_12_73761_519388 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 73761 ⟨519388, by decide⟩ :=
  accepted_of_selected 12 73761 ⟨519388, by decide⟩ ⟨12, 2, 0, 519388, 73761, 3025, 65536⟩
    (by decide) selected_cut_20289

theorem selected_cut_20290 : selected 9 ⟨519459, by decide⟩
    (prefixPartial 12 73762) = some ⟨12, 2, 0, 519459, 73762, 2821, 65536⟩ := by
  decide +kernel

theorem context_12_73762_519459 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 73762 ⟨519459, by decide⟩ :=
  accepted_of_selected 12 73762 ⟨519459, by decide⟩ ⟨12, 2, 0, 519459, 73762, 2821, 65536⟩
    (by decide) selected_cut_20290

theorem selected_cut_20291 : selected 9 ⟨519523, by decide⟩
    (prefixPartial 12 73763) = some ⟨12, 2, 0, 519523, 73763, 2797, 65536⟩ := by
  decide +kernel

theorem context_12_73763_519523 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 73763 ⟨519523, by decide⟩ :=
  accepted_of_selected 12 73763 ⟨519523, by decide⟩ ⟨12, 2, 0, 519523, 73763, 2797, 65536⟩
    (by decide) selected_cut_20291

theorem unmarked_context_11_18440_519524 : frontier 10 ⟨519524, by decide⟩
    (prefixCache 11 18440) (prefixPartial 11 18440) = false := by
  decide +kernel

theorem node_context_11_18440_519524 : EJMOriginalGlobalDAGData.nodes 10 ⟨519524, by decide⟩ =
    .split (coordinate 11) (![⟨435790, by decide⟩,⟨519388, by decide⟩,⟨519459, by decide⟩,⟨519523, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18440_519524 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18440 ⟨519524, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18440
    ⟨519524, by decide⟩ (by decide) (![⟨435790, by decide⟩,⟨519388, by decide⟩,⟨519459, by decide⟩,⟨519523, by decide⟩]) unmarked_context_11_18440_519524 node_context_11_18440_519524
  intro a
  fin_cases a
  · exact context_12_73760_435790
  · exact context_12_73761_519388
  · exact context_12_73762_519459
  · exact context_12_73763_519523

theorem selected_cut_20292 : selected 9 ⟨519622, by decide⟩
    (prefixPartial 12 73764) = some ⟨12, 2, 0, 519622, 73764, 2721, 65536⟩ := by
  decide +kernel

theorem context_12_73764_519622 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 73764 ⟨519622, by decide⟩ :=
  accepted_of_selected 12 73764 ⟨519622, by decide⟩ ⟨12, 2, 0, 519622, 73764, 2721, 65536⟩
    (by decide) selected_cut_20292

theorem selected_cut_20293 : selected 8 ⟨519642, by decide⟩
    (prefixPartial 13 295060) = some ⟨13, 2, 0, 519642, 295060, 717, 16384⟩ := by
  decide +kernel

theorem context_13_295060_519642 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 295060 ⟨519642, by decide⟩ :=
  accepted_of_selected 13 295060 ⟨519642, by decide⟩ ⟨13, 2, 0, 519642, 295060, 717, 16384⟩
    (by decide) selected_cut_20293

theorem selected_cut_20294 : selected 8 ⟨519676, by decide⟩
    (prefixPartial 13 295061) = some ⟨13, 2, 0, 519676, 295061, 1297, 16384⟩ := by
  decide +kernel

theorem context_13_295061_519676 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 295061 ⟨519676, by decide⟩ :=
  accepted_of_selected 13 295061 ⟨519676, by decide⟩ ⟨13, 2, 0, 519676, 295061, 1297, 16384⟩
    (by decide) selected_cut_20294

theorem selected_cut_20295 : selected 8 ⟨519695, by decide⟩
    (prefixPartial 13 295062) = some ⟨13, 2, 0, 519695, 295062, 1385, 16384⟩ := by
  decide +kernel

theorem context_13_295062_519695 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 295062 ⟨519695, by decide⟩ :=
  accepted_of_selected 13 295062 ⟨519695, by decide⟩ ⟨13, 2, 0, 519695, 295062, 1385, 16384⟩
    (by decide) selected_cut_20295

theorem selected_cut_20296 : selected 8 ⟨519701, by decide⟩
    (prefixPartial 13 295063) = some ⟨13, 2, 0, 519701, 295063, 741, 16384⟩ := by
  decide +kernel

theorem context_13_295063_519701 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 295063 ⟨519701, by decide⟩ :=
  accepted_of_selected 13 295063 ⟨519701, by decide⟩ ⟨13, 2, 0, 519701, 295063, 741, 16384⟩
    (by decide) selected_cut_20296

theorem unmarked_context_12_73765_519702 : frontier 9 ⟨519702, by decide⟩
    (prefixCache 12 73765) (prefixPartial 12 73765) = false := by
  decide +kernel

theorem node_context_12_73765_519702 : EJMOriginalGlobalDAGData.nodes 9 ⟨519702, by decide⟩ =
    .split (coordinate 12) (![⟨519642, by decide⟩,⟨519676, by decide⟩,⟨519695, by decide⟩,⟨519701, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_73765_519702 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 73765 ⟨519702, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 73765
    ⟨519702, by decide⟩ (by decide) (![⟨519642, by decide⟩,⟨519676, by decide⟩,⟨519695, by decide⟩,⟨519701, by decide⟩]) unmarked_context_12_73765_519702 node_context_12_73765_519702
  intro a
  fin_cases a
  · exact context_13_295060_519642
  · exact context_13_295061_519676
  · exact context_13_295062_519695
  · exact context_13_295063_519701

theorem selected_cut_20297 : selected 9 ⟨519786, by decide⟩
    (prefixPartial 12 73766) = some ⟨12, 2, 0, 519786, 73766, 4009, 65536⟩ := by
  decide +kernel

theorem context_12_73766_519786 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 73766 ⟨519786, by decide⟩ :=
  accepted_of_selected 12 73766 ⟨519786, by decide⟩ ⟨12, 2, 0, 519786, 73766, 4009, 65536⟩
    (by decide) selected_cut_20297

theorem selected_cut_20298 : selected 8 ⟨519807, by decide⟩
    (prefixPartial 13 295068) = some ⟨13, 2, 0, 519807, 295068, 641, 16384⟩ := by
  decide +kernel

theorem context_13_295068_519807 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 295068 ⟨519807, by decide⟩ :=
  accepted_of_selected 13 295068 ⟨519807, by decide⟩ ⟨13, 2, 0, 519807, 295068, 641, 16384⟩
    (by decide) selected_cut_20298

theorem selected_cut_20299 : selected 8 ⟨519849, by decide⟩
    (prefixPartial 13 295069) = some ⟨13, 2, 0, 519849, 295069, 1669, 16384⟩ := by
  decide +kernel

theorem context_13_295069_519849 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 295069 ⟨519849, by decide⟩ :=
  accepted_of_selected 13 295069 ⟨519849, by decide⟩ ⟨13, 2, 0, 519849, 295069, 1669, 16384⟩
    (by decide) selected_cut_20299

theorem selected_cut_20300 : selected 8 ⟨519863, by decide⟩
    (prefixPartial 13 295070) = some ⟨13, 2, 0, 519863, 295070, 1161, 16384⟩ := by
  decide +kernel

theorem context_13_295070_519863 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 295070 ⟨519863, by decide⟩ :=
  accepted_of_selected 13 295070 ⟨519863, by decide⟩ ⟨13, 2, 0, 519863, 295070, 1161, 16384⟩
    (by decide) selected_cut_20300

theorem selected_cut_20301 : selected 8 ⟨519868, by decide⟩
    (prefixPartial 13 295071) = some ⟨13, 2, 0, 519868, 295071, 645, 16384⟩ := by
  decide +kernel

theorem context_13_295071_519868 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 295071 ⟨519868, by decide⟩ :=
  accepted_of_selected 13 295071 ⟨519868, by decide⟩ ⟨13, 2, 0, 519868, 295071, 645, 16384⟩
    (by decide) selected_cut_20301

theorem unmarked_context_12_73767_519869 : frontier 9 ⟨519869, by decide⟩
    (prefixCache 12 73767) (prefixPartial 12 73767) = false := by
  decide +kernel

theorem node_context_12_73767_519869 : EJMOriginalGlobalDAGData.nodes 9 ⟨519869, by decide⟩ =
    .split (coordinate 12) (![⟨519807, by decide⟩,⟨519849, by decide⟩,⟨519863, by decide⟩,⟨519868, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_73767_519869 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 73767 ⟨519869, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 73767
    ⟨519869, by decide⟩ (by decide) (![⟨519807, by decide⟩,⟨519849, by decide⟩,⟨519863, by decide⟩,⟨519868, by decide⟩]) unmarked_context_12_73767_519869 node_context_12_73767_519869
  intro a
  fin_cases a
  · exact context_13_295068_519807
  · exact context_13_295069_519849
  · exact context_13_295070_519863
  · exact context_13_295071_519868

theorem unmarked_context_11_18441_519870 : frontier 10 ⟨519870, by decide⟩
    (prefixCache 11 18441) (prefixPartial 11 18441) = false := by
  decide +kernel

theorem node_context_11_18441_519870 : EJMOriginalGlobalDAGData.nodes 10 ⟨519870, by decide⟩ =
    .split (coordinate 11) (![⟨519622, by decide⟩,⟨519702, by decide⟩,⟨519786, by decide⟩,⟨519869, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18441_519870 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18441 ⟨519870, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18441
    ⟨519870, by decide⟩ (by decide) (![⟨519622, by decide⟩,⟨519702, by decide⟩,⟨519786, by decide⟩,⟨519869, by decide⟩]) unmarked_context_11_18441_519870 node_context_11_18441_519870
  intro a
  fin_cases a
  · exact context_12_73764_519622
  · exact context_12_73765_519702
  · exact context_12_73766_519786
  · exact context_12_73767_519869

theorem selected_cut_20302 : selected 9 ⟨435790, by decide⟩
    (prefixPartial 12 73768) = some ⟨12, 1, 0, 435790, 73768, 1, 65536⟩ := by
  decide +kernel

theorem context_12_73768_435790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 73768 ⟨435790, by decide⟩ :=
  accepted_of_selected 12 73768 ⟨435790, by decide⟩ ⟨12, 1, 0, 435790, 73768, 1, 65536⟩
    (by decide) selected_cut_20302

theorem selected_cut_20303 : selected 9 ⟨519951, by decide⟩
    (prefixPartial 12 73769) = some ⟨12, 2, 0, 519951, 73769, 4073, 65536⟩ := by
  decide +kernel

theorem context_12_73769_519951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 73769 ⟨519951, by decide⟩ :=
  accepted_of_selected 12 73769 ⟨519951, by decide⟩ ⟨12, 2, 0, 519951, 73769, 4073, 65536⟩
    (by decide) selected_cut_20303

theorem selected_cut_20304 : selected 9 ⟨520023, by decide⟩
    (prefixPartial 12 73770) = some ⟨12, 2, 0, 520023, 73770, 3269, 65536⟩ := by
  decide +kernel

theorem context_12_73770_520023 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 73770 ⟨520023, by decide⟩ :=
  accepted_of_selected 12 73770 ⟨520023, by decide⟩ ⟨12, 2, 0, 520023, 73770, 3269, 65536⟩
    (by decide) selected_cut_20304

theorem selected_cut_20305 : selected 9 ⟨520091, by decide⟩
    (prefixPartial 12 73771) = some ⟨12, 2, 0, 520091, 73771, 3653, 65536⟩ := by
  decide +kernel

theorem context_12_73771_520091 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 73771 ⟨520091, by decide⟩ :=
  accepted_of_selected 12 73771 ⟨520091, by decide⟩ ⟨12, 2, 0, 520091, 73771, 3653, 65536⟩
    (by decide) selected_cut_20305

theorem unmarked_context_11_18442_520092 : frontier 10 ⟨520092, by decide⟩
    (prefixCache 11 18442) (prefixPartial 11 18442) = false := by
  decide +kernel

theorem node_context_11_18442_520092 : EJMOriginalGlobalDAGData.nodes 10 ⟨520092, by decide⟩ =
    .split (coordinate 11) (![⟨435790, by decide⟩,⟨519951, by decide⟩,⟨520023, by decide⟩,⟨520091, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18442_520092 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18442 ⟨520092, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18442
    ⟨520092, by decide⟩ (by decide) (![⟨435790, by decide⟩,⟨519951, by decide⟩,⟨520023, by decide⟩,⟨520091, by decide⟩]) unmarked_context_11_18442_520092 node_context_11_18442_520092
  intro a
  fin_cases a
  · exact context_12_73768_435790
  · exact context_12_73769_519951
  · exact context_12_73770_520023
  · exact context_12_73771_520091

theorem selected_cut_20306 : selected 8 ⟨520103, by decide⟩
    (prefixPartial 13 295088) = some ⟨13, 2, 0, 520103, 295088, 197, 16384⟩ := by
  decide +kernel

theorem context_13_295088_520103 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 295088 ⟨520103, by decide⟩ :=
  accepted_of_selected 13 295088 ⟨520103, by decide⟩ ⟨13, 2, 0, 520103, 295088, 197, 16384⟩
    (by decide) selected_cut_20306

theorem selected_cut_20307 : selected 8 ⟨520165, by decide⟩
    (prefixPartial 13 295089) = some ⟨13, 2, 0, 520165, 295089, 2345, 16384⟩ := by
  decide +kernel

theorem context_13_295089_520165 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 295089 ⟨520165, by decide⟩ :=
  accepted_of_selected 13 295089 ⟨520165, by decide⟩ ⟨13, 2, 0, 520165, 295089, 2345, 16384⟩
    (by decide) selected_cut_20307

theorem selected_cut_20308 : selected 8 ⟨520198, by decide⟩
    (prefixPartial 13 295090) = some ⟨13, 2, 0, 520198, 295090, 1193, 16384⟩ := by
  decide +kernel

theorem context_13_295090_520198 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 295090 ⟨520198, by decide⟩ :=
  accepted_of_selected 13 295090 ⟨520198, by decide⟩ ⟨13, 2, 0, 520198, 295090, 1193, 16384⟩
    (by decide) selected_cut_20308

theorem selected_cut_20309 : selected 8 ⟨520220, by decide⟩
    (prefixPartial 13 295091) = some ⟨13, 2, 0, 520220, 295091, 625, 16384⟩ := by
  decide +kernel

theorem context_13_295091_520220 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 295091 ⟨520220, by decide⟩ :=
  accepted_of_selected 13 295091 ⟨520220, by decide⟩ ⟨13, 2, 0, 520220, 295091, 625, 16384⟩
    (by decide) selected_cut_20309

theorem unmarked_context_12_73772_520221 : frontier 9 ⟨520221, by decide⟩
    (prefixCache 12 73772) (prefixPartial 12 73772) = false := by
  decide +kernel

theorem node_context_12_73772_520221 : EJMOriginalGlobalDAGData.nodes 9 ⟨520221, by decide⟩ =
    .split (coordinate 12) (![⟨520103, by decide⟩,⟨520165, by decide⟩,⟨520198, by decide⟩,⟨520220, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_73772_520221 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 73772 ⟨520221, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 73772
    ⟨520221, by decide⟩ (by decide) (![⟨520103, by decide⟩,⟨520165, by decide⟩,⟨520198, by decide⟩,⟨520220, by decide⟩]) unmarked_context_12_73772_520221 node_context_12_73772_520221
  intro a
  fin_cases a
  · exact context_13_295088_520103
  · exact context_13_295089_520165
  · exact context_13_295090_520198
  · exact context_13_295091_520220

theorem selected_cut_20310 : selected 8 ⟨520233, by decide⟩
    (prefixPartial 13 295092) = some ⟨13, 2, 0, 520233, 295092, 465, 16384⟩ := by
  decide +kernel

theorem context_13_295092_520233 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 295092 ⟨520233, by decide⟩ :=
  accepted_of_selected 13 295092 ⟨520233, by decide⟩ ⟨13, 2, 0, 520233, 295092, 465, 16384⟩
    (by decide) selected_cut_20310

theorem selected_cut_20311 : selected 8 ⟨520280, by decide⟩
    (prefixPartial 13 295093) = some ⟨13, 2, 0, 520280, 295093, 1637, 16384⟩ := by
  decide +kernel

theorem context_13_295093_520280 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 295093 ⟨520280, by decide⟩ :=
  accepted_of_selected 13 295093 ⟨520280, by decide⟩ ⟨13, 2, 0, 520280, 295093, 1637, 16384⟩
    (by decide) selected_cut_20311

theorem selected_cut_20312 : selected 8 ⟨520296, by decide⟩
    (prefixPartial 13 295094) = some ⟨13, 2, 0, 520296, 295094, 1365, 16384⟩ := by
  decide +kernel

theorem context_13_295094_520296 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 295094 ⟨520296, by decide⟩ :=
  accepted_of_selected 13 295094 ⟨520296, by decide⟩ ⟨13, 2, 0, 520296, 295094, 1365, 16384⟩
    (by decide) selected_cut_20312

theorem selected_cut_20313 : selected 8 ⟨520307, by decide⟩
    (prefixPartial 13 295095) = some ⟨13, 2, 0, 520307, 295095, 745, 16384⟩ := by
  decide +kernel

theorem context_13_295095_520307 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 295095 ⟨520307, by decide⟩ :=
  accepted_of_selected 13 295095 ⟨520307, by decide⟩ ⟨13, 2, 0, 520307, 295095, 745, 16384⟩
    (by decide) selected_cut_20313

theorem unmarked_context_12_73773_520308 : frontier 9 ⟨520308, by decide⟩
    (prefixCache 12 73773) (prefixPartial 12 73773) = false := by
  decide +kernel

theorem node_context_12_73773_520308 : EJMOriginalGlobalDAGData.nodes 9 ⟨520308, by decide⟩ =
    .split (coordinate 12) (![⟨520233, by decide⟩,⟨520280, by decide⟩,⟨520296, by decide⟩,⟨520307, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_73773_520308 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 73773 ⟨520308, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 73773
    ⟨520308, by decide⟩ (by decide) (![⟨520233, by decide⟩,⟨520280, by decide⟩,⟨520296, by decide⟩,⟨520307, by decide⟩]) unmarked_context_12_73773_520308 node_context_12_73773_520308
  intro a
  fin_cases a
  · exact context_13_295092_520233
  · exact context_13_295093_520280
  · exact context_13_295094_520296
  · exact context_13_295095_520307

theorem selected_cut_20314 : selected 9 ⟨520379, by decide⟩
    (prefixPartial 12 73774) = some ⟨12, 2, 0, 520379, 73774, 3797, 65536⟩ := by
  decide +kernel

theorem context_12_73774_520379 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 73774 ⟨520379, by decide⟩ :=
  accepted_of_selected 12 73774 ⟨520379, by decide⟩ ⟨12, 2, 0, 520379, 73774, 3797, 65536⟩
    (by decide) selected_cut_20314

theorem selected_cut_20315 : selected 9 ⟨520451, by decide⟩
    (prefixPartial 12 73775) = some ⟨12, 2, 0, 520451, 73775, 3657, 65536⟩ := by
  decide +kernel

theorem context_12_73775_520451 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 73775 ⟨520451, by decide⟩ :=
  accepted_of_selected 12 73775 ⟨520451, by decide⟩ ⟨12, 2, 0, 520451, 73775, 3657, 65536⟩
    (by decide) selected_cut_20315

theorem unmarked_context_11_18443_520452 : frontier 10 ⟨520452, by decide⟩
    (prefixCache 11 18443) (prefixPartial 11 18443) = false := by
  decide +kernel

theorem node_context_11_18443_520452 : EJMOriginalGlobalDAGData.nodes 10 ⟨520452, by decide⟩ =
    .split (coordinate 11) (![⟨520221, by decide⟩,⟨520308, by decide⟩,⟨520379, by decide⟩,⟨520451, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18443_520452 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18443 ⟨520452, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18443
    ⟨520452, by decide⟩ (by decide) (![⟨520221, by decide⟩,⟨520308, by decide⟩,⟨520379, by decide⟩,⟨520451, by decide⟩]) unmarked_context_11_18443_520452 node_context_11_18443_520452
  intro a
  fin_cases a
  · exact context_12_73772_520221
  · exact context_12_73773_520308
  · exact context_12_73774_520379
  · exact context_12_73775_520451

theorem unmarked_context_10_4610_520453 : frontier 11 ⟨520453, by decide⟩
    (prefixCache 10 4610) (prefixPartial 10 4610) = false := by
  decide +kernel

theorem node_context_10_4610_520453 : EJMOriginalGlobalDAGData.nodes 11 ⟨520453, by decide⟩ =
    .split (coordinate 10) (![⟨519524, by decide⟩,⟨519870, by decide⟩,⟨520092, by decide⟩,⟨520452, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4610_520453 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4610 ⟨520453, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4610
    ⟨520453, by decide⟩ (by decide) (![⟨519524, by decide⟩,⟨519870, by decide⟩,⟨520092, by decide⟩,⟨520452, by decide⟩]) unmarked_context_10_4610_520453 node_context_10_4610_520453
  intro a
  fin_cases a
  · exact context_11_18440_519524
  · exact context_11_18441_519870
  · exact context_11_18442_520092
  · exact context_11_18443_520452

theorem selected_cut_20316 : selected 9 ⟨445562, by decide⟩
    (prefixPartial 12 73776) = some ⟨12, 1, 0, 445562, 73776, 1, 65536⟩ := by
  decide +kernel

theorem context_12_73776_445562 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 73776 ⟨445562, by decide⟩ :=
  accepted_of_selected 12 73776 ⟨445562, by decide⟩ ⟨12, 1, 0, 445562, 73776, 1, 65536⟩
    (by decide) selected_cut_20316

theorem selected_cut_20317 : selected 9 ⟨520508, by decide⟩
    (prefixPartial 12 73777) = some ⟨12, 2, 0, 520508, 73777, 2773, 65536⟩ := by
  decide +kernel

theorem context_12_73777_520508 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 73777 ⟨520508, by decide⟩ :=
  accepted_of_selected 12 73777 ⟨520508, by decide⟩ ⟨12, 2, 0, 520508, 73777, 2773, 65536⟩
    (by decide) selected_cut_20317

theorem selected_cut_20318 : selected 9 ⟨520559, by decide⟩
    (prefixPartial 12 73778) = some ⟨12, 2, 0, 520559, 73778, 2561, 65536⟩ := by
  decide +kernel

theorem context_12_73778_520559 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 73778 ⟨520559, by decide⟩ :=
  accepted_of_selected 12 73778 ⟨520559, by decide⟩ ⟨12, 2, 0, 520559, 73778, 2561, 65536⟩
    (by decide) selected_cut_20318

theorem selected_cut_20319 : selected 9 ⟨520615, by decide⟩
    (prefixPartial 12 73779) = some ⟨12, 2, 0, 520615, 73779, 2533, 65536⟩ := by
  decide +kernel

theorem context_12_73779_520615 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 73779 ⟨520615, by decide⟩ :=
  accepted_of_selected 12 73779 ⟨520615, by decide⟩ ⟨12, 2, 0, 520615, 73779, 2533, 65536⟩
    (by decide) selected_cut_20319

theorem unmarked_context_11_18444_520616 : frontier 10 ⟨520616, by decide⟩
    (prefixCache 11 18444) (prefixPartial 11 18444) = false := by
  decide +kernel

theorem node_context_11_18444_520616 : EJMOriginalGlobalDAGData.nodes 10 ⟨520616, by decide⟩ =
    .split (coordinate 11) (![⟨445562, by decide⟩,⟨520508, by decide⟩,⟨520559, by decide⟩,⟨520615, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18444_520616 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18444 ⟨520616, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18444
    ⟨520616, by decide⟩ (by decide) (![⟨445562, by decide⟩,⟨520508, by decide⟩,⟨520559, by decide⟩,⟨520615, by decide⟩]) unmarked_context_11_18444_520616 node_context_11_18444_520616
  intro a
  fin_cases a
  · exact context_12_73776_445562
  · exact context_12_73777_520508
  · exact context_12_73778_520559
  · exact context_12_73779_520615

theorem selected_cut_20320 : selected 9 ⟨520617, by decide⟩
    (prefixPartial 12 73780) = some ⟨12, 1, 0, 520617, 73780, 1, 65536⟩ := by
  decide +kernel

theorem context_12_73780_520617 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 73780 ⟨520617, by decide⟩ :=
  accepted_of_selected 12 73780 ⟨520617, by decide⟩ ⟨12, 1, 0, 520617, 73780, 1, 65536⟩
    (by decide) selected_cut_20320

theorem selected_cut_20321 : selected 9 ⟨520683, by decide⟩
    (prefixPartial 12 73781) = some ⟨12, 2, 0, 520683, 73781, 3673, 65536⟩ := by
  decide +kernel

theorem context_12_73781_520683 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 73781 ⟨520683, by decide⟩ :=
  accepted_of_selected 12 73781 ⟨520683, by decide⟩ ⟨12, 2, 0, 520683, 73781, 3673, 65536⟩
    (by decide) selected_cut_20321

theorem selected_cut_20322 : selected 9 ⟨520749, by decide⟩
    (prefixPartial 12 73782) = some ⟨12, 2, 0, 520749, 73782, 3505, 65536⟩ := by
  decide +kernel

theorem context_12_73782_520749 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 73782 ⟨520749, by decide⟩ :=
  accepted_of_selected 12 73782 ⟨520749, by decide⟩ ⟨12, 2, 0, 520749, 73782, 3505, 65536⟩
    (by decide) selected_cut_20322

theorem selected_cut_20323 : selected 9 ⟨520818, by decide⟩
    (prefixPartial 12 73783) = some ⟨12, 2, 0, 520818, 73783, 3665, 65536⟩ := by
  decide +kernel

theorem context_12_73783_520818 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 73783 ⟨520818, by decide⟩ :=
  accepted_of_selected 12 73783 ⟨520818, by decide⟩ ⟨12, 2, 0, 520818, 73783, 3665, 65536⟩
    (by decide) selected_cut_20323

theorem unmarked_context_11_18445_520819 : frontier 10 ⟨520819, by decide⟩
    (prefixCache 11 18445) (prefixPartial 11 18445) = false := by
  decide +kernel

theorem node_context_11_18445_520819 : EJMOriginalGlobalDAGData.nodes 10 ⟨520819, by decide⟩ =
    .split (coordinate 11) (![⟨520617, by decide⟩,⟨520683, by decide⟩,⟨520749, by decide⟩,⟨520818, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18445_520819 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18445 ⟨520819, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18445
    ⟨520819, by decide⟩ (by decide) (![⟨520617, by decide⟩,⟨520683, by decide⟩,⟨520749, by decide⟩,⟨520818, by decide⟩]) unmarked_context_11_18445_520819 node_context_11_18445_520819
  intro a
  fin_cases a
  · exact context_12_73780_520617
  · exact context_12_73781_520683
  · exact context_12_73782_520749
  · exact context_12_73783_520818

theorem selected_cut_20324 : selected 9 ⟨520923, by decide⟩
    (prefixPartial 12 73784) = some ⟨12, 2, 0, 520923, 73784, 2381, 65536⟩ := by
  decide +kernel

theorem context_12_73784_520923 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 73784 ⟨520923, by decide⟩ :=
  accepted_of_selected 12 73784 ⟨520923, by decide⟩ ⟨12, 2, 0, 520923, 73784, 2381, 65536⟩
    (by decide) selected_cut_20324

theorem selected_cut_20325 : selected 9 ⟨520981, by decide⟩
    (prefixPartial 12 73785) = some ⟨12, 2, 0, 520981, 73785, 3661, 65536⟩ := by
  decide +kernel

theorem context_12_73785_520981 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 73785 ⟨520981, by decide⟩ :=
  accepted_of_selected 12 73785 ⟨520981, by decide⟩ ⟨12, 2, 0, 520981, 73785, 3661, 65536⟩
    (by decide) selected_cut_20325

theorem selected_cut_20326 : selected 9 ⟨521032, by decide⟩
    (prefixPartial 12 73786) = some ⟨12, 2, 0, 521032, 73786, 2957, 65536⟩ := by
  decide +kernel

theorem context_12_73786_521032 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 73786 ⟨521032, by decide⟩ :=
  accepted_of_selected 12 73786 ⟨521032, by decide⟩ ⟨12, 2, 0, 521032, 73786, 2957, 65536⟩
    (by decide) selected_cut_20326

theorem selected_cut_20327 : selected 9 ⟨521094, by decide⟩
    (prefixPartial 12 73787) = some ⟨12, 2, 0, 521094, 73787, 3277, 65536⟩ := by
  decide +kernel

theorem context_12_73787_521094 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 73787 ⟨521094, by decide⟩ :=
  accepted_of_selected 12 73787 ⟨521094, by decide⟩ ⟨12, 2, 0, 521094, 73787, 3277, 65536⟩
    (by decide) selected_cut_20327

theorem unmarked_context_11_18446_521095 : frontier 10 ⟨521095, by decide⟩
    (prefixCache 11 18446) (prefixPartial 11 18446) = false := by
  decide +kernel

theorem node_context_11_18446_521095 : EJMOriginalGlobalDAGData.nodes 10 ⟨521095, by decide⟩ =
    .split (coordinate 11) (![⟨520923, by decide⟩,⟨520981, by decide⟩,⟨521032, by decide⟩,⟨521094, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18446_521095 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18446 ⟨521095, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18446
    ⟨521095, by decide⟩ (by decide) (![⟨520923, by decide⟩,⟨520981, by decide⟩,⟨521032, by decide⟩,⟨521094, by decide⟩]) unmarked_context_11_18446_521095 node_context_11_18446_521095
  intro a
  fin_cases a
  · exact context_12_73784_520923
  · exact context_12_73785_520981
  · exact context_12_73786_521032
  · exact context_12_73787_521094

theorem selected_cut_20328 : selected 9 ⟨445562, by decide⟩
    (prefixPartial 12 73788) = some ⟨12, 1, 0, 445562, 73788, 1, 65536⟩ := by
  decide +kernel

theorem context_12_73788_445562 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 73788 ⟨445562, by decide⟩ :=
  accepted_of_selected 12 73788 ⟨445562, by decide⟩ ⟨12, 1, 0, 445562, 73788, 1, 65536⟩
    (by decide) selected_cut_20328

theorem selected_cut_20329 : selected 9 ⟨521152, by decide⟩
    (prefixPartial 12 73789) = some ⟨12, 2, 0, 521152, 73789, 3829, 65536⟩ := by
  decide +kernel

theorem context_12_73789_521152 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 73789 ⟨521152, by decide⟩ :=
  accepted_of_selected 12 73789 ⟨521152, by decide⟩ ⟨12, 2, 0, 521152, 73789, 3829, 65536⟩
    (by decide) selected_cut_20329

theorem selected_cut_20330 : selected 9 ⟨521213, by decide⟩
    (prefixPartial 12 73790) = some ⟨12, 2, 0, 521213, 73790, 3445, 65536⟩ := by
  decide +kernel

theorem context_12_73790_521213 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 73790 ⟨521213, by decide⟩ :=
  accepted_of_selected 12 73790 ⟨521213, by decide⟩ ⟨12, 2, 0, 521213, 73790, 3445, 65536⟩
    (by decide) selected_cut_20330

theorem selected_cut_20331 : selected 9 ⟨521270, by decide⟩
    (prefixPartial 12 73791) = some ⟨12, 2, 0, 521270, 73791, 3333, 65536⟩ := by
  decide +kernel

theorem context_12_73791_521270 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 73791 ⟨521270, by decide⟩ :=
  accepted_of_selected 12 73791 ⟨521270, by decide⟩ ⟨12, 2, 0, 521270, 73791, 3333, 65536⟩
    (by decide) selected_cut_20331

theorem unmarked_context_11_18447_521271 : frontier 10 ⟨521271, by decide⟩
    (prefixCache 11 18447) (prefixPartial 11 18447) = false := by
  decide +kernel

theorem node_context_11_18447_521271 : EJMOriginalGlobalDAGData.nodes 10 ⟨521271, by decide⟩ =
    .split (coordinate 11) (![⟨445562, by decide⟩,⟨521152, by decide⟩,⟨521213, by decide⟩,⟨521270, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18447_521271 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18447 ⟨521271, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18447
    ⟨521271, by decide⟩ (by decide) (![⟨445562, by decide⟩,⟨521152, by decide⟩,⟨521213, by decide⟩,⟨521270, by decide⟩]) unmarked_context_11_18447_521271 node_context_11_18447_521271
  intro a
  fin_cases a
  · exact context_12_73788_445562
  · exact context_12_73789_521152
  · exact context_12_73790_521213
  · exact context_12_73791_521270

theorem unmarked_context_10_4611_521272 : frontier 11 ⟨521272, by decide⟩
    (prefixCache 10 4611) (prefixPartial 10 4611) = false := by
  decide +kernel

theorem node_context_10_4611_521272 : EJMOriginalGlobalDAGData.nodes 11 ⟨521272, by decide⟩ =
    .split (coordinate 10) (![⟨520616, by decide⟩,⟨520819, by decide⟩,⟨521095, by decide⟩,⟨521271, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4611_521272 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4611 ⟨521272, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4611
    ⟨521272, by decide⟩ (by decide) (![⟨520616, by decide⟩,⟨520819, by decide⟩,⟨521095, by decide⟩,⟨521271, by decide⟩]) unmarked_context_10_4611_521272 node_context_10_4611_521272
  intro a
  fin_cases a
  · exact context_11_18444_520616
  · exact context_11_18445_520819
  · exact context_11_18446_521095
  · exact context_11_18447_521271

theorem unmarked_context_9_1152_521273 : frontier 12 ⟨521273, by decide⟩
    (prefixCache 9 1152) (prefixPartial 9 1152) = false := by
  decide +kernel

theorem node_context_9_1152_521273 : EJMOriginalGlobalDAGData.nodes 12 ⟨521273, by decide⟩ =
    .split (coordinate 9) (![⟨518280, by decide⟩,⟨519318, by decide⟩,⟨520453, by decide⟩,⟨521272, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1152_521273 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1152 ⟨521273, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1152
    ⟨521273, by decide⟩ (by decide) (![⟨518280, by decide⟩,⟨519318, by decide⟩,⟨520453, by decide⟩,⟨521272, by decide⟩]) unmarked_context_9_1152_521273 node_context_9_1152_521273
  intro a
  fin_cases a
  · exact context_10_4608_518280
  · exact context_10_4609_519318
  · exact context_10_4610_520453
  · exact context_10_4611_521272

theorem selected_cut_20332 : selected 11 ⟨145424, by decide⟩
    (prefixPartial 10 4612) = some ⟨10, 1, 0, 145424, 4612, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_4612_145424 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4612 ⟨145424, by decide⟩ :=
  accepted_of_selected 10 4612 ⟨145424, by decide⟩ ⟨10, 1, 0, 145424, 4612, 1, 1048576⟩
    (by decide) selected_cut_20332

theorem selected_cut_20333 : selected 9 ⟨307381, by decide⟩
    (prefixPartial 12 73808) = some ⟨12, 1, 0, 307381, 73808, 1, 65536⟩ := by
  decide +kernel

theorem context_12_73808_307381 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 73808 ⟨307381, by decide⟩ :=
  accepted_of_selected 12 73808 ⟨307381, by decide⟩ ⟨12, 1, 0, 307381, 73808, 1, 65536⟩
    (by decide) selected_cut_20333

theorem selected_cut_20334 : selected 9 ⟨521358, by decide⟩
    (prefixPartial 12 73809) = some ⟨12, 2, 0, 521358, 73809, 3209, 65536⟩ := by
  decide +kernel

theorem context_12_73809_521358 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 73809 ⟨521358, by decide⟩ :=
  accepted_of_selected 12 73809 ⟨521358, by decide⟩ ⟨12, 2, 0, 521358, 73809, 3209, 65536⟩
    (by decide) selected_cut_20334

theorem selected_cut_20335 : selected 9 ⟨521428, by decide⟩
    (prefixPartial 12 73810) = some ⟨12, 2, 0, 521428, 73810, 3177, 65536⟩ := by
  decide +kernel

theorem context_12_73810_521428 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 73810 ⟨521428, by decide⟩ :=
  accepted_of_selected 12 73810 ⟨521428, by decide⟩ ⟨12, 2, 0, 521428, 73810, 3177, 65536⟩
    (by decide) selected_cut_20335

theorem selected_cut_20336 : selected 9 ⟨521475, by decide⟩
    (prefixPartial 12 73811) = some ⟨12, 2, 0, 521475, 73811, 3153, 65536⟩ := by
  decide +kernel

theorem context_12_73811_521475 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 73811 ⟨521475, by decide⟩ :=
  accepted_of_selected 12 73811 ⟨521475, by decide⟩ ⟨12, 2, 0, 521475, 73811, 3153, 65536⟩
    (by decide) selected_cut_20336

theorem unmarked_context_11_18452_521476 : frontier 10 ⟨521476, by decide⟩
    (prefixCache 11 18452) (prefixPartial 11 18452) = false := by
  decide +kernel

theorem node_context_11_18452_521476 : EJMOriginalGlobalDAGData.nodes 10 ⟨521476, by decide⟩ =
    .split (coordinate 11) (![⟨307381, by decide⟩,⟨521358, by decide⟩,⟨521428, by decide⟩,⟨521475, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18452_521476 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18452 ⟨521476, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18452
    ⟨521476, by decide⟩ (by decide) (![⟨307381, by decide⟩,⟨521358, by decide⟩,⟨521428, by decide⟩,⟨521475, by decide⟩]) unmarked_context_11_18452_521476 node_context_11_18452_521476
  intro a
  fin_cases a
  · exact context_12_73808_307381
  · exact context_12_73809_521358
  · exact context_12_73810_521428
  · exact context_12_73811_521475

theorem selected_cut_20337 : selected 9 ⟨521532, by decide⟩
    (prefixPartial 12 73812) = some ⟨12, 2, 0, 521532, 73812, 2697, 65536⟩ := by
  decide +kernel

theorem context_12_73812_521532 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 73812 ⟨521532, by decide⟩ :=
  accepted_of_selected 12 73812 ⟨521532, by decide⟩ ⟨12, 2, 0, 521532, 73812, 2697, 65536⟩
    (by decide) selected_cut_20337

theorem selected_cut_20338 : selected 9 ⟨521631, by decide⟩
    (prefixPartial 12 73813) = some ⟨12, 2, 0, 521631, 73813, 3461, 65536⟩ := by
  decide +kernel

theorem context_12_73813_521631 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 73813 ⟨521631, by decide⟩ :=
  accepted_of_selected 12 73813 ⟨521631, by decide⟩ ⟨12, 2, 0, 521631, 73813, 3461, 65536⟩
    (by decide) selected_cut_20338

theorem selected_cut_20339 : selected 9 ⟨521713, by decide⟩
    (prefixPartial 12 73814) = some ⟨12, 2, 0, 521713, 73814, 3593, 65536⟩ := by
  decide +kernel

theorem context_12_73814_521713 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 73814 ⟨521713, by decide⟩ :=
  accepted_of_selected 12 73814 ⟨521713, by decide⟩ ⟨12, 2, 0, 521713, 73814, 3593, 65536⟩
    (by decide) selected_cut_20339

theorem selected_cut_20340 : selected 9 ⟨521789, by decide⟩
    (prefixPartial 12 73815) = some ⟨12, 2, 0, 521789, 73815, 3553, 65536⟩ := by
  decide +kernel

theorem context_12_73815_521789 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 73815 ⟨521789, by decide⟩ :=
  accepted_of_selected 12 73815 ⟨521789, by decide⟩ ⟨12, 2, 0, 521789, 73815, 3553, 65536⟩
    (by decide) selected_cut_20340

theorem unmarked_context_11_18453_521790 : frontier 10 ⟨521790, by decide⟩
    (prefixCache 11 18453) (prefixPartial 11 18453) = false := by
  decide +kernel

theorem node_context_11_18453_521790 : EJMOriginalGlobalDAGData.nodes 10 ⟨521790, by decide⟩ =
    .split (coordinate 11) (![⟨521532, by decide⟩,⟨521631, by decide⟩,⟨521713, by decide⟩,⟨521789, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18453_521790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18453 ⟨521790, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18453
    ⟨521790, by decide⟩ (by decide) (![⟨521532, by decide⟩,⟨521631, by decide⟩,⟨521713, by decide⟩,⟨521789, by decide⟩]) unmarked_context_11_18453_521790 node_context_11_18453_521790
  intro a
  fin_cases a
  · exact context_12_73812_521532
  · exact context_12_73813_521631
  · exact context_12_73814_521713
  · exact context_12_73815_521789

theorem selected_cut_20341 : selected 9 ⟨521836, by decide⟩
    (prefixPartial 12 73816) = some ⟨12, 2, 0, 521836, 73816, 2705, 65536⟩ := by
  decide +kernel

theorem context_12_73816_521836 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 73816 ⟨521836, by decide⟩ :=
  accepted_of_selected 12 73816 ⟨521836, by decide⟩ ⟨12, 2, 0, 521836, 73816, 2705, 65536⟩
    (by decide) selected_cut_20341

theorem selected_cut_20342 : selected 9 ⟨521913, by decide⟩
    (prefixPartial 12 73817) = some ⟨12, 2, 0, 521913, 73817, 3321, 65536⟩ := by
  decide +kernel

theorem context_12_73817_521913 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 73817 ⟨521913, by decide⟩ :=
  accepted_of_selected 12 73817 ⟨521913, by decide⟩ ⟨12, 2, 0, 521913, 73817, 3321, 65536⟩
    (by decide) selected_cut_20342

theorem selected_cut_20343 : selected 9 ⟨521970, by decide⟩
    (prefixPartial 12 73818) = some ⟨12, 2, 0, 521970, 73818, 3249, 65536⟩ := by
  decide +kernel

theorem context_12_73818_521970 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 73818 ⟨521970, by decide⟩ :=
  accepted_of_selected 12 73818 ⟨521970, by decide⟩ ⟨12, 2, 0, 521970, 73818, 3249, 65536⟩
    (by decide) selected_cut_20343

theorem selected_cut_20344 : selected 9 ⟨522030, by decide⟩
    (prefixPartial 12 73819) = some ⟨12, 2, 0, 522030, 73819, 3345, 65536⟩ := by
  decide +kernel

theorem context_12_73819_522030 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 73819 ⟨522030, by decide⟩ :=
  accepted_of_selected 12 73819 ⟨522030, by decide⟩ ⟨12, 2, 0, 522030, 73819, 3345, 65536⟩
    (by decide) selected_cut_20344

theorem unmarked_context_11_18454_522031 : frontier 10 ⟨522031, by decide⟩
    (prefixCache 11 18454) (prefixPartial 11 18454) = false := by
  decide +kernel

theorem node_context_11_18454_522031 : EJMOriginalGlobalDAGData.nodes 10 ⟨522031, by decide⟩ =
    .split (coordinate 11) (![⟨521836, by decide⟩,⟨521913, by decide⟩,⟨521970, by decide⟩,⟨522030, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18454_522031 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18454 ⟨522031, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18454
    ⟨522031, by decide⟩ (by decide) (![⟨521836, by decide⟩,⟨521913, by decide⟩,⟨521970, by decide⟩,⟨522030, by decide⟩]) unmarked_context_11_18454_522031 node_context_11_18454_522031
  intro a
  fin_cases a
  · exact context_12_73816_521836
  · exact context_12_73817_521913
  · exact context_12_73818_521970
  · exact context_12_73819_522030

theorem selected_cut_20345 : selected 9 ⟨522072, by decide⟩
    (prefixPartial 12 73820) = some ⟨12, 2, 0, 522072, 73820, 2445, 65536⟩ := by
  decide +kernel

theorem context_12_73820_522072 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 73820 ⟨522072, by decide⟩ :=
  accepted_of_selected 12 73820 ⟨522072, by decide⟩ ⟨12, 2, 0, 522072, 73820, 2445, 65536⟩
    (by decide) selected_cut_20345

theorem selected_cut_20346 : selected 9 ⟨522133, by decide⟩
    (prefixPartial 12 73821) = some ⟨12, 2, 0, 522133, 73821, 3277, 65536⟩ := by
  decide +kernel

theorem context_12_73821_522133 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 73821 ⟨522133, by decide⟩ :=
  accepted_of_selected 12 73821 ⟨522133, by decide⟩ ⟨12, 2, 0, 522133, 73821, 3277, 65536⟩
    (by decide) selected_cut_20346

theorem selected_cut_20347 : selected 9 ⟨522182, by decide⟩
    (prefixPartial 12 73822) = some ⟨12, 2, 0, 522182, 73822, 3285, 65536⟩ := by
  decide +kernel

theorem context_12_73822_522182 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 73822 ⟨522182, by decide⟩ :=
  accepted_of_selected 12 73822 ⟨522182, by decide⟩ ⟨12, 2, 0, 522182, 73822, 3285, 65536⟩
    (by decide) selected_cut_20347

theorem selected_cut_20348 : selected 9 ⟨522225, by decide⟩
    (prefixPartial 12 73823) = some ⟨12, 2, 0, 522225, 73823, 3089, 65536⟩ := by
  decide +kernel

theorem context_12_73823_522225 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 73823 ⟨522225, by decide⟩ :=
  accepted_of_selected 12 73823 ⟨522225, by decide⟩ ⟨12, 2, 0, 522225, 73823, 3089, 65536⟩
    (by decide) selected_cut_20348

theorem unmarked_context_11_18455_522226 : frontier 10 ⟨522226, by decide⟩
    (prefixCache 11 18455) (prefixPartial 11 18455) = false := by
  decide +kernel

theorem node_context_11_18455_522226 : EJMOriginalGlobalDAGData.nodes 10 ⟨522226, by decide⟩ =
    .split (coordinate 11) (![⟨522072, by decide⟩,⟨522133, by decide⟩,⟨522182, by decide⟩,⟨522225, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18455_522226 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18455 ⟨522226, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18455
    ⟨522226, by decide⟩ (by decide) (![⟨522072, by decide⟩,⟨522133, by decide⟩,⟨522182, by decide⟩,⟨522225, by decide⟩]) unmarked_context_11_18455_522226 node_context_11_18455_522226
  intro a
  fin_cases a
  · exact context_12_73820_522072
  · exact context_12_73821_522133
  · exact context_12_73822_522182
  · exact context_12_73823_522225

theorem unmarked_context_10_4613_522227 : frontier 11 ⟨522227, by decide⟩
    (prefixCache 10 4613) (prefixPartial 10 4613) = false := by
  decide +kernel

theorem node_context_10_4613_522227 : EJMOriginalGlobalDAGData.nodes 11 ⟨522227, by decide⟩ =
    .split (coordinate 10) (![⟨521476, by decide⟩,⟨521790, by decide⟩,⟨522031, by decide⟩,⟨522226, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4613_522227 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4613 ⟨522227, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4613
    ⟨522227, by decide⟩ (by decide) (![⟨521476, by decide⟩,⟨521790, by decide⟩,⟨522031, by decide⟩,⟨522226, by decide⟩]) unmarked_context_10_4613_522227 node_context_10_4613_522227
  intro a
  fin_cases a
  · exact context_11_18452_521476
  · exact context_11_18453_521790
  · exact context_11_18454_522031
  · exact context_11_18455_522226

theorem selected_cut_20349 : selected 9 ⟨522297, by decide⟩
    (prefixPartial 12 73824) = some ⟨12, 2, 0, 522297, 73824, 717, 65536⟩ := by
  decide +kernel

theorem context_12_73824_522297 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 73824 ⟨522297, by decide⟩ :=
  accepted_of_selected 12 73824 ⟨522297, by decide⟩ ⟨12, 2, 0, 522297, 73824, 717, 65536⟩
    (by decide) selected_cut_20349

theorem selected_cut_20350 : selected 9 ⟨522351, by decide⟩
    (prefixPartial 12 73825) = some ⟨12, 2, 0, 522351, 73825, 2325, 65536⟩ := by
  decide +kernel

theorem context_12_73825_522351 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 73825 ⟨522351, by decide⟩ :=
  accepted_of_selected 12 73825 ⟨522351, by decide⟩ ⟨12, 2, 0, 522351, 73825, 2325, 65536⟩
    (by decide) selected_cut_20350

theorem selected_cut_20351 : selected 9 ⟨522396, by decide⟩
    (prefixPartial 12 73826) = some ⟨12, 2, 0, 522396, 73826, 2157, 65536⟩ := by
  decide +kernel

theorem context_12_73826_522396 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 73826 ⟨522396, by decide⟩ :=
  accepted_of_selected 12 73826 ⟨522396, by decide⟩ ⟨12, 2, 0, 522396, 73826, 2157, 65536⟩
    (by decide) selected_cut_20351

theorem selected_cut_20352 : selected 9 ⟨522438, by decide⟩
    (prefixPartial 12 73827) = some ⟨12, 2, 0, 522438, 73827, 2229, 65536⟩ := by
  decide +kernel

theorem context_12_73827_522438 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 73827 ⟨522438, by decide⟩ :=
  accepted_of_selected 12 73827 ⟨522438, by decide⟩ ⟨12, 2, 0, 522438, 73827, 2229, 65536⟩
    (by decide) selected_cut_20352

theorem unmarked_context_11_18456_522439 : frontier 10 ⟨522439, by decide⟩
    (prefixCache 11 18456) (prefixPartial 11 18456) = false := by
  decide +kernel

theorem node_context_11_18456_522439 : EJMOriginalGlobalDAGData.nodes 10 ⟨522439, by decide⟩ =
    .split (coordinate 11) (![⟨522297, by decide⟩,⟨522351, by decide⟩,⟨522396, by decide⟩,⟨522438, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18456_522439 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18456 ⟨522439, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18456
    ⟨522439, by decide⟩ (by decide) (![⟨522297, by decide⟩,⟨522351, by decide⟩,⟨522396, by decide⟩,⟨522438, by decide⟩]) unmarked_context_11_18456_522439 node_context_11_18456_522439
  intro a
  fin_cases a
  · exact context_12_73824_522297
  · exact context_12_73825_522351
  · exact context_12_73826_522396
  · exact context_12_73827_522438

theorem selected_cut_20353 : selected 9 ⟨4595, by decide⟩
    (prefixPartial 12 73828) = some ⟨12, 1, 0, 4595, 73828, 1, 65536⟩ := by
  decide +kernel

theorem context_12_73828_4595 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 73828 ⟨4595, by decide⟩ :=
  accepted_of_selected 12 73828 ⟨4595, by decide⟩ ⟨12, 1, 0, 4595, 73828, 1, 65536⟩
    (by decide) selected_cut_20353

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
