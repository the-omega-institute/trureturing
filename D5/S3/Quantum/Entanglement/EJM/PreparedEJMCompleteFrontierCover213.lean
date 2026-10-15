/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover212
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_20451 : selected 8 ⟨525319, by decide⟩
    (prefixPartial 13 296046) = some ⟨13, 2, 0, 525319, 296046, 1369, 16384⟩ := by
  decide +kernel

theorem context_13_296046_525319 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296046 ⟨525319, by decide⟩ :=
  accepted_of_selected 13 296046 ⟨525319, by decide⟩ ⟨13, 2, 0, 525319, 296046, 1369, 16384⟩
    (by decide) selected_cut_20451

theorem selected_cut_20452 : selected 8 ⟨525322, by decide⟩
    (prefixPartial 13 296047) = some ⟨13, 2, 0, 525322, 296047, 593, 16384⟩ := by
  decide +kernel

theorem context_13_296047_525322 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296047 ⟨525322, by decide⟩ :=
  accepted_of_selected 13 296047 ⟨525322, by decide⟩ ⟨13, 2, 0, 525322, 296047, 593, 16384⟩
    (by decide) selected_cut_20452

theorem unmarked_context_12_74011_525323 : frontier 9 ⟨525323, by decide⟩
    (prefixCache 12 74011) (prefixPartial 12 74011) = false := by
  decide +kernel

theorem node_context_12_74011_525323 : EJMOriginalGlobalDAGData.nodes 9 ⟨525323, by decide⟩ =
    .split (coordinate 12) (![⟨525277, by decide⟩,⟨525301, by decide⟩,⟨525319, by decide⟩,⟨525322, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74011_525323 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74011 ⟨525323, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74011
    ⟨525323, by decide⟩ (by decide) (![⟨525277, by decide⟩,⟨525301, by decide⟩,⟨525319, by decide⟩,⟨525322, by decide⟩]) unmarked_context_12_74011_525323 node_context_12_74011_525323
  intro a
  fin_cases a
  · exact context_13_296044_525277
  · exact context_13_296045_525301
  · exact context_13_296046_525319
  · exact context_13_296047_525322

theorem unmarked_context_11_18502_525324 : frontier 10 ⟨525324, by decide⟩
    (prefixCache 11 18502) (prefixPartial 11 18502) = false := by
  decide +kernel

theorem node_context_11_18502_525324 : EJMOriginalGlobalDAGData.nodes 10 ⟨525324, by decide⟩ =
    .split (coordinate 11) (![⟨525102, by decide⟩,⟨525184, by decide⟩,⟨525252, by decide⟩,⟨525323, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18502_525324 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18502 ⟨525324, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18502
    ⟨525324, by decide⟩ (by decide) (![⟨525102, by decide⟩,⟨525184, by decide⟩,⟨525252, by decide⟩,⟨525323, by decide⟩]) unmarked_context_11_18502_525324 node_context_11_18502_525324
  intro a
  fin_cases a
  · exact context_12_74008_525102
  · exact context_12_74009_525184
  · exact context_12_74010_525252
  · exact context_12_74011_525323

theorem selected_cut_20453 : selected 8 ⟨525347, by decide⟩
    (prefixPartial 13 296048) = some ⟨13, 2, 0, 525347, 296048, 1553, 16384⟩ := by
  decide +kernel

theorem context_13_296048_525347 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296048 ⟨525347, by decide⟩ :=
  accepted_of_selected 13 296048 ⟨525347, by decide⟩ ⟨13, 2, 0, 525347, 296048, 1553, 16384⟩
    (by decide) selected_cut_20453

theorem selected_cut_20454 : selected 8 ⟨525387, by decide⟩
    (prefixPartial 13 296049) = some ⟨13, 2, 0, 525387, 296049, 3161, 16384⟩ := by
  decide +kernel

theorem context_13_296049_525387 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296049 ⟨525387, by decide⟩ :=
  accepted_of_selected 13 296049 ⟨525387, by decide⟩ ⟨13, 2, 0, 525387, 296049, 3161, 16384⟩
    (by decide) selected_cut_20454

theorem selected_cut_20455 : selected 8 ⟨525406, by decide⟩
    (prefixPartial 13 296050) = some ⟨13, 2, 0, 525406, 296050, 1725, 16384⟩ := by
  decide +kernel

theorem context_13_296050_525406 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296050 ⟨525406, by decide⟩ :=
  accepted_of_selected 13 296050 ⟨525406, by decide⟩ ⟨13, 2, 0, 525406, 296050, 1725, 16384⟩
    (by decide) selected_cut_20455

theorem selected_cut_20456 : selected 8 ⟨525413, by decide⟩
    (prefixPartial 13 296051) = some ⟨13, 2, 0, 525413, 296051, 957, 16384⟩ := by
  decide +kernel

theorem context_13_296051_525413 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296051 ⟨525413, by decide⟩ :=
  accepted_of_selected 13 296051 ⟨525413, by decide⟩ ⟨13, 2, 0, 525413, 296051, 957, 16384⟩
    (by decide) selected_cut_20456

theorem unmarked_context_12_74012_525414 : frontier 9 ⟨525414, by decide⟩
    (prefixCache 12 74012) (prefixPartial 12 74012) = false := by
  decide +kernel

theorem node_context_12_74012_525414 : EJMOriginalGlobalDAGData.nodes 9 ⟨525414, by decide⟩ =
    .split (coordinate 12) (![⟨525347, by decide⟩,⟨525387, by decide⟩,⟨525406, by decide⟩,⟨525413, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74012_525414 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74012 ⟨525414, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74012
    ⟨525414, by decide⟩ (by decide) (![⟨525347, by decide⟩,⟨525387, by decide⟩,⟨525406, by decide⟩,⟨525413, by decide⟩]) unmarked_context_12_74012_525414 node_context_12_74012_525414
  intro a
  fin_cases a
  · exact context_13_296048_525347
  · exact context_13_296049_525387
  · exact context_13_296050_525406
  · exact context_13_296051_525413

theorem selected_cut_20457 : selected 8 ⟨525439, by decide⟩
    (prefixPartial 13 296052) = some ⟨13, 2, 0, 525439, 296052, 1381, 16384⟩ := by
  decide +kernel

theorem context_13_296052_525439 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296052 ⟨525439, by decide⟩ :=
  accepted_of_selected 13 296052 ⟨525439, by decide⟩ ⟨13, 2, 0, 525439, 296052, 1381, 16384⟩
    (by decide) selected_cut_20457

theorem selected_cut_20458 : selected 8 ⟨525462, by decide⟩
    (prefixPartial 13 296053) = some ⟨13, 2, 0, 525462, 296053, 1789, 16384⟩ := by
  decide +kernel

theorem context_13_296053_525462 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296053 ⟨525462, by decide⟩ :=
  accepted_of_selected 13 296053 ⟨525462, by decide⟩ ⟨13, 2, 0, 525462, 296053, 1789, 16384⟩
    (by decide) selected_cut_20458

theorem selected_cut_20459 : selected 8 ⟨525482, by decide⟩
    (prefixPartial 13 296054) = some ⟨13, 2, 0, 525482, 296054, 1505, 16384⟩ := by
  decide +kernel

theorem context_13_296054_525482 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296054 ⟨525482, by decide⟩ :=
  accepted_of_selected 13 296054 ⟨525482, by decide⟩ ⟨13, 2, 0, 525482, 296054, 1505, 16384⟩
    (by decide) selected_cut_20459

theorem selected_cut_20460 : selected 8 ⟨525491, by decide⟩
    (prefixPartial 13 296055) = some ⟨13, 2, 0, 525491, 296055, 785, 16384⟩ := by
  decide +kernel

theorem context_13_296055_525491 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296055 ⟨525491, by decide⟩ :=
  accepted_of_selected 13 296055 ⟨525491, by decide⟩ ⟨13, 2, 0, 525491, 296055, 785, 16384⟩
    (by decide) selected_cut_20460

theorem unmarked_context_12_74013_525492 : frontier 9 ⟨525492, by decide⟩
    (prefixCache 12 74013) (prefixPartial 12 74013) = false := by
  decide +kernel

theorem node_context_12_74013_525492 : EJMOriginalGlobalDAGData.nodes 9 ⟨525492, by decide⟩ =
    .split (coordinate 12) (![⟨525439, by decide⟩,⟨525462, by decide⟩,⟨525482, by decide⟩,⟨525491, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74013_525492 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74013 ⟨525492, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74013
    ⟨525492, by decide⟩ (by decide) (![⟨525439, by decide⟩,⟨525462, by decide⟩,⟨525482, by decide⟩,⟨525491, by decide⟩]) unmarked_context_12_74013_525492 node_context_12_74013_525492
  intro a
  fin_cases a
  · exact context_13_296052_525439
  · exact context_13_296053_525462
  · exact context_13_296054_525482
  · exact context_13_296055_525491

theorem selected_cut_20461 : selected 8 ⟨525514, by decide⟩
    (prefixPartial 13 296056) = some ⟨13, 2, 0, 525514, 296056, 1257, 16384⟩ := by
  decide +kernel

theorem context_13_296056_525514 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296056 ⟨525514, by decide⟩ :=
  accepted_of_selected 13 296056 ⟨525514, by decide⟩ ⟨13, 2, 0, 525514, 296056, 1257, 16384⟩
    (by decide) selected_cut_20461

theorem selected_cut_20462 : selected 8 ⟨525536, by decide⟩
    (prefixPartial 13 296057) = some ⟨13, 2, 0, 525536, 296057, 2253, 16384⟩ := by
  decide +kernel

theorem context_13_296057_525536 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296057 ⟨525536, by decide⟩ :=
  accepted_of_selected 13 296057 ⟨525536, by decide⟩ ⟨13, 2, 0, 525536, 296057, 2253, 16384⟩
    (by decide) selected_cut_20462

theorem selected_cut_20463 : selected 8 ⟨525551, by decide⟩
    (prefixPartial 13 296058) = some ⟨13, 2, 0, 525551, 296058, 1073, 16384⟩ := by
  decide +kernel

theorem context_13_296058_525551 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296058 ⟨525551, by decide⟩ :=
  accepted_of_selected 13 296058 ⟨525551, by decide⟩ ⟨13, 2, 0, 525551, 296058, 1073, 16384⟩
    (by decide) selected_cut_20463

theorem selected_cut_20464 : selected 8 ⟨525558, by decide⟩
    (prefixPartial 13 296059) = some ⟨13, 2, 0, 525558, 296059, 853, 16384⟩ := by
  decide +kernel

theorem context_13_296059_525558 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296059 ⟨525558, by decide⟩ :=
  accepted_of_selected 13 296059 ⟨525558, by decide⟩ ⟨13, 2, 0, 525558, 296059, 853, 16384⟩
    (by decide) selected_cut_20464

theorem unmarked_context_12_74014_525559 : frontier 9 ⟨525559, by decide⟩
    (prefixCache 12 74014) (prefixPartial 12 74014) = false := by
  decide +kernel

theorem node_context_12_74014_525559 : EJMOriginalGlobalDAGData.nodes 9 ⟨525559, by decide⟩ =
    .split (coordinate 12) (![⟨525514, by decide⟩,⟨525536, by decide⟩,⟨525551, by decide⟩,⟨525558, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74014_525559 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74014 ⟨525559, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74014
    ⟨525559, by decide⟩ (by decide) (![⟨525514, by decide⟩,⟨525536, by decide⟩,⟨525551, by decide⟩,⟨525558, by decide⟩]) unmarked_context_12_74014_525559 node_context_12_74014_525559
  intro a
  fin_cases a
  · exact context_13_296056_525514
  · exact context_13_296057_525536
  · exact context_13_296058_525551
  · exact context_13_296059_525558

theorem selected_cut_20465 : selected 8 ⟨525586, by decide⟩
    (prefixPartial 13 296060) = some ⟨13, 2, 0, 525586, 296060, 1405, 16384⟩ := by
  decide +kernel

theorem context_13_296060_525586 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296060 ⟨525586, by decide⟩ :=
  accepted_of_selected 13 296060 ⟨525586, by decide⟩ ⟨13, 2, 0, 525586, 296060, 1405, 16384⟩
    (by decide) selected_cut_20465

theorem selected_cut_20466 : selected 8 ⟨525608, by decide⟩
    (prefixPartial 13 296061) = some ⟨13, 2, 0, 525608, 296061, 2473, 16384⟩ := by
  decide +kernel

theorem context_13_296061_525608 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296061 ⟨525608, by decide⟩ :=
  accepted_of_selected 13 296061 ⟨525608, by decide⟩ ⟨13, 2, 0, 525608, 296061, 2473, 16384⟩
    (by decide) selected_cut_20466

theorem selected_cut_20467 : selected 8 ⟨525628, by decide⟩
    (prefixPartial 13 296062) = some ⟨13, 2, 0, 525628, 296062, 1365, 16384⟩ := by
  decide +kernel

theorem context_13_296062_525628 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296062 ⟨525628, by decide⟩ :=
  accepted_of_selected 13 296062 ⟨525628, by decide⟩ ⟨13, 2, 0, 525628, 296062, 1365, 16384⟩
    (by decide) selected_cut_20467

theorem selected_cut_20468 : selected 8 ⟨525633, by decide⟩
    (prefixPartial 13 296063) = some ⟨13, 2, 0, 525633, 296063, 673, 16384⟩ := by
  decide +kernel

theorem context_13_296063_525633 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296063 ⟨525633, by decide⟩ :=
  accepted_of_selected 13 296063 ⟨525633, by decide⟩ ⟨13, 2, 0, 525633, 296063, 673, 16384⟩
    (by decide) selected_cut_20468

theorem unmarked_context_12_74015_525634 : frontier 9 ⟨525634, by decide⟩
    (prefixCache 12 74015) (prefixPartial 12 74015) = false := by
  decide +kernel

theorem node_context_12_74015_525634 : EJMOriginalGlobalDAGData.nodes 9 ⟨525634, by decide⟩ =
    .split (coordinate 12) (![⟨525586, by decide⟩,⟨525608, by decide⟩,⟨525628, by decide⟩,⟨525633, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74015_525634 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74015 ⟨525634, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74015
    ⟨525634, by decide⟩ (by decide) (![⟨525586, by decide⟩,⟨525608, by decide⟩,⟨525628, by decide⟩,⟨525633, by decide⟩]) unmarked_context_12_74015_525634 node_context_12_74015_525634
  intro a
  fin_cases a
  · exact context_13_296060_525586
  · exact context_13_296061_525608
  · exact context_13_296062_525628
  · exact context_13_296063_525633

theorem unmarked_context_11_18503_525635 : frontier 10 ⟨525635, by decide⟩
    (prefixCache 11 18503) (prefixPartial 11 18503) = false := by
  decide +kernel

theorem node_context_11_18503_525635 : EJMOriginalGlobalDAGData.nodes 10 ⟨525635, by decide⟩ =
    .split (coordinate 11) (![⟨525414, by decide⟩,⟨525492, by decide⟩,⟨525559, by decide⟩,⟨525634, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18503_525635 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18503 ⟨525635, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18503
    ⟨525635, by decide⟩ (by decide) (![⟨525414, by decide⟩,⟨525492, by decide⟩,⟨525559, by decide⟩,⟨525634, by decide⟩]) unmarked_context_11_18503_525635 node_context_11_18503_525635
  intro a
  fin_cases a
  · exact context_12_74012_525414
  · exact context_12_74013_525492
  · exact context_12_74014_525559
  · exact context_12_74015_525634

theorem unmarked_context_10_4625_525636 : frontier 11 ⟨525636, by decide⟩
    (prefixCache 10 4625) (prefixPartial 10 4625) = false := by
  decide +kernel

theorem node_context_10_4625_525636 : EJMOriginalGlobalDAGData.nodes 11 ⟨525636, by decide⟩ =
    .split (coordinate 10) (![⟨524847, by decide⟩,⟨525022, by decide⟩,⟨525324, by decide⟩,⟨525635, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4625_525636 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4625 ⟨525636, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4625
    ⟨525636, by decide⟩ (by decide) (![⟨524847, by decide⟩,⟨525022, by decide⟩,⟨525324, by decide⟩,⟨525635, by decide⟩]) unmarked_context_10_4625_525636 node_context_10_4625_525636
  intro a
  fin_cases a
  · exact context_11_18500_524847
  · exact context_11_18501_525022
  · exact context_11_18502_525324
  · exact context_11_18503_525635

theorem selected_cut_20469 : selected 9 ⟨435790, by decide⟩
    (prefixPartial 12 74016) = some ⟨12, 1, 0, 435790, 74016, 1, 65536⟩ := by
  decide +kernel

theorem context_12_74016_435790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74016 ⟨435790, by decide⟩ :=
  accepted_of_selected 12 74016 ⟨435790, by decide⟩ ⟨12, 1, 0, 435790, 74016, 1, 65536⟩
    (by decide) selected_cut_20469

theorem selected_cut_20470 : selected 8 ⟨525655, by decide⟩
    (prefixPartial 13 296068) = some ⟨13, 2, 0, 525655, 296068, 1049, 16384⟩ := by
  decide +kernel

theorem context_13_296068_525655 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296068 ⟨525655, by decide⟩ :=
  accepted_of_selected 13 296068 ⟨525655, by decide⟩ ⟨13, 2, 0, 525655, 296068, 1049, 16384⟩
    (by decide) selected_cut_20470

theorem selected_cut_20471 : selected 8 ⟨525675, by decide⟩
    (prefixPartial 13 296069) = some ⟨13, 2, 0, 525675, 296069, 1349, 16384⟩ := by
  decide +kernel

theorem context_13_296069_525675 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296069 ⟨525675, by decide⟩ :=
  accepted_of_selected 13 296069 ⟨525675, by decide⟩ ⟨13, 2, 0, 525675, 296069, 1349, 16384⟩
    (by decide) selected_cut_20471

theorem selected_cut_20472 : selected 8 ⟨525694, by decide⟩
    (prefixPartial 13 296070) = some ⟨13, 2, 0, 525694, 296070, 1305, 16384⟩ := by
  decide +kernel

theorem context_13_296070_525694 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296070 ⟨525694, by decide⟩ :=
  accepted_of_selected 13 296070 ⟨525694, by decide⟩ ⟨13, 2, 0, 525694, 296070, 1305, 16384⟩
    (by decide) selected_cut_20472

theorem selected_cut_20473 : selected 8 ⟨525700, by decide⟩
    (prefixPartial 13 296071) = some ⟨13, 2, 0, 525700, 296071, 765, 16384⟩ := by
  decide +kernel

theorem context_13_296071_525700 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296071 ⟨525700, by decide⟩ :=
  accepted_of_selected 13 296071 ⟨525700, by decide⟩ ⟨13, 2, 0, 525700, 296071, 765, 16384⟩
    (by decide) selected_cut_20473

theorem unmarked_context_12_74017_525701 : frontier 9 ⟨525701, by decide⟩
    (prefixCache 12 74017) (prefixPartial 12 74017) = false := by
  decide +kernel

theorem node_context_12_74017_525701 : EJMOriginalGlobalDAGData.nodes 9 ⟨525701, by decide⟩ =
    .split (coordinate 12) (![⟨525655, by decide⟩,⟨525675, by decide⟩,⟨525694, by decide⟩,⟨525700, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74017_525701 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74017 ⟨525701, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74017
    ⟨525701, by decide⟩ (by decide) (![⟨525655, by decide⟩,⟨525675, by decide⟩,⟨525694, by decide⟩,⟨525700, by decide⟩]) unmarked_context_12_74017_525701 node_context_12_74017_525701
  intro a
  fin_cases a
  · exact context_13_296068_525655
  · exact context_13_296069_525675
  · exact context_13_296070_525694
  · exact context_13_296071_525700

theorem selected_cut_20474 : selected 8 ⟨525720, by decide⟩
    (prefixPartial 13 296072) = some ⟨13, 2, 0, 525720, 296072, 977, 16384⟩ := by
  decide +kernel

theorem context_13_296072_525720 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296072 ⟨525720, by decide⟩ :=
  accepted_of_selected 13 296072 ⟨525720, by decide⟩ ⟨13, 2, 0, 525720, 296072, 977, 16384⟩
    (by decide) selected_cut_20474

theorem selected_cut_20475 : selected 8 ⟨525743, by decide⟩
    (prefixPartial 13 296073) = some ⟨13, 2, 0, 525743, 296073, 1537, 16384⟩ := by
  decide +kernel

theorem context_13_296073_525743 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296073 ⟨525743, by decide⟩ :=
  accepted_of_selected 13 296073 ⟨525743, by decide⟩ ⟨13, 2, 0, 525743, 296073, 1537, 16384⟩
    (by decide) selected_cut_20475

theorem selected_cut_20476 : selected 8 ⟨525756, by decide⟩
    (prefixPartial 13 296074) = some ⟨13, 2, 0, 525756, 296074, 877, 16384⟩ := by
  decide +kernel

theorem context_13_296074_525756 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296074 ⟨525756, by decide⟩ :=
  accepted_of_selected 13 296074 ⟨525756, by decide⟩ ⟨13, 2, 0, 525756, 296074, 877, 16384⟩
    (by decide) selected_cut_20476

theorem selected_cut_20477 : selected 8 ⟨525766, by decide⟩
    (prefixPartial 13 296075) = some ⟨13, 2, 0, 525766, 296075, 777, 16384⟩ := by
  decide +kernel

theorem context_13_296075_525766 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296075 ⟨525766, by decide⟩ :=
  accepted_of_selected 13 296075 ⟨525766, by decide⟩ ⟨13, 2, 0, 525766, 296075, 777, 16384⟩
    (by decide) selected_cut_20477

theorem unmarked_context_12_74018_525767 : frontier 9 ⟨525767, by decide⟩
    (prefixCache 12 74018) (prefixPartial 12 74018) = false := by
  decide +kernel

theorem node_context_12_74018_525767 : EJMOriginalGlobalDAGData.nodes 9 ⟨525767, by decide⟩ =
    .split (coordinate 12) (![⟨525720, by decide⟩,⟨525743, by decide⟩,⟨525756, by decide⟩,⟨525766, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74018_525767 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74018 ⟨525767, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74018
    ⟨525767, by decide⟩ (by decide) (![⟨525720, by decide⟩,⟨525743, by decide⟩,⟨525756, by decide⟩,⟨525766, by decide⟩]) unmarked_context_12_74018_525767 node_context_12_74018_525767
  intro a
  fin_cases a
  · exact context_13_296072_525720
  · exact context_13_296073_525743
  · exact context_13_296074_525756
  · exact context_13_296075_525766

theorem selected_cut_20478 : selected 8 ⟨525789, by decide⟩
    (prefixPartial 13 296076) = some ⟨13, 2, 0, 525789, 296076, 1041, 16384⟩ := by
  decide +kernel

theorem context_13_296076_525789 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296076 ⟨525789, by decide⟩ :=
  accepted_of_selected 13 296076 ⟨525789, by decide⟩ ⟨13, 2, 0, 525789, 296076, 1041, 16384⟩
    (by decide) selected_cut_20478

theorem selected_cut_20479 : selected 8 ⟨525815, by decide⟩
    (prefixPartial 13 296077) = some ⟨13, 2, 0, 525815, 296077, 1793, 16384⟩ := by
  decide +kernel

theorem context_13_296077_525815 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296077 ⟨525815, by decide⟩ :=
  accepted_of_selected 13 296077 ⟨525815, by decide⟩ ⟨13, 2, 0, 525815, 296077, 1793, 16384⟩
    (by decide) selected_cut_20479

theorem selected_cut_20480 : selected 8 ⟨525832, by decide⟩
    (prefixPartial 13 296078) = some ⟨13, 2, 0, 525832, 296078, 1145, 16384⟩ := by
  decide +kernel

theorem context_13_296078_525832 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296078 ⟨525832, by decide⟩ :=
  accepted_of_selected 13 296078 ⟨525832, by decide⟩ ⟨13, 2, 0, 525832, 296078, 1145, 16384⟩
    (by decide) selected_cut_20480

theorem selected_cut_20481 : selected 8 ⟨525836, by decide⟩
    (prefixPartial 13 296079) = some ⟨13, 2, 0, 525836, 296079, 625, 16384⟩ := by
  decide +kernel

theorem context_13_296079_525836 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296079 ⟨525836, by decide⟩ :=
  accepted_of_selected 13 296079 ⟨525836, by decide⟩ ⟨13, 2, 0, 525836, 296079, 625, 16384⟩
    (by decide) selected_cut_20481

theorem unmarked_context_12_74019_525837 : frontier 9 ⟨525837, by decide⟩
    (prefixCache 12 74019) (prefixPartial 12 74019) = false := by
  decide +kernel

theorem node_context_12_74019_525837 : EJMOriginalGlobalDAGData.nodes 9 ⟨525837, by decide⟩ =
    .split (coordinate 12) (![⟨525789, by decide⟩,⟨525815, by decide⟩,⟨525832, by decide⟩,⟨525836, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74019_525837 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74019 ⟨525837, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74019
    ⟨525837, by decide⟩ (by decide) (![⟨525789, by decide⟩,⟨525815, by decide⟩,⟨525832, by decide⟩,⟨525836, by decide⟩]) unmarked_context_12_74019_525837 node_context_12_74019_525837
  intro a
  fin_cases a
  · exact context_13_296076_525789
  · exact context_13_296077_525815
  · exact context_13_296078_525832
  · exact context_13_296079_525836

theorem unmarked_context_11_18504_525838 : frontier 10 ⟨525838, by decide⟩
    (prefixCache 11 18504) (prefixPartial 11 18504) = false := by
  decide +kernel

theorem node_context_11_18504_525838 : EJMOriginalGlobalDAGData.nodes 10 ⟨525838, by decide⟩ =
    .split (coordinate 11) (![⟨435790, by decide⟩,⟨525701, by decide⟩,⟨525767, by decide⟩,⟨525837, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18504_525838 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18504 ⟨525838, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18504
    ⟨525838, by decide⟩ (by decide) (![⟨435790, by decide⟩,⟨525701, by decide⟩,⟨525767, by decide⟩,⟨525837, by decide⟩]) unmarked_context_11_18504_525838 node_context_11_18504_525838
  intro a
  fin_cases a
  · exact context_12_74016_435790
  · exact context_12_74017_525701
  · exact context_12_74018_525767
  · exact context_12_74019_525837

theorem selected_cut_20482 : selected 8 ⟨525867, by decide⟩
    (prefixPartial 13 296080) = some ⟨13, 2, 0, 525867, 296080, 1377, 16384⟩ := by
  decide +kernel

theorem context_13_296080_525867 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296080 ⟨525867, by decide⟩ :=
  accepted_of_selected 13 296080 ⟨525867, by decide⟩ ⟨13, 2, 0, 525867, 296080, 1377, 16384⟩
    (by decide) selected_cut_20482

theorem selected_cut_20483 : selected 8 ⟨525892, by decide⟩
    (prefixPartial 13 296081) = some ⟨13, 2, 0, 525892, 296081, 2437, 16384⟩ := by
  decide +kernel

theorem context_13_296081_525892 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296081 ⟨525892, by decide⟩ :=
  accepted_of_selected 13 296081 ⟨525892, by decide⟩ ⟨13, 2, 0, 525892, 296081, 2437, 16384⟩
    (by decide) selected_cut_20483

theorem selected_cut_20484 : selected 8 ⟨525914, by decide⟩
    (prefixPartial 13 296082) = some ⟨13, 2, 0, 525914, 296082, 1773, 16384⟩ := by
  decide +kernel

theorem context_13_296082_525914 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296082 ⟨525914, by decide⟩ :=
  accepted_of_selected 13 296082 ⟨525914, by decide⟩ ⟨13, 2, 0, 525914, 296082, 1773, 16384⟩
    (by decide) selected_cut_20484

theorem selected_cut_20485 : selected 8 ⟨525924, by decide⟩
    (prefixPartial 13 296083) = some ⟨13, 2, 0, 525924, 296083, 889, 16384⟩ := by
  decide +kernel

theorem context_13_296083_525924 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296083 ⟨525924, by decide⟩ :=
  accepted_of_selected 13 296083 ⟨525924, by decide⟩ ⟨13, 2, 0, 525924, 296083, 889, 16384⟩
    (by decide) selected_cut_20485

theorem unmarked_context_12_74020_525925 : frontier 9 ⟨525925, by decide⟩
    (prefixCache 12 74020) (prefixPartial 12 74020) = false := by
  decide +kernel

theorem node_context_12_74020_525925 : EJMOriginalGlobalDAGData.nodes 9 ⟨525925, by decide⟩ =
    .split (coordinate 12) (![⟨525867, by decide⟩,⟨525892, by decide⟩,⟨525914, by decide⟩,⟨525924, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74020_525925 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74020 ⟨525925, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74020
    ⟨525925, by decide⟩ (by decide) (![⟨525867, by decide⟩,⟨525892, by decide⟩,⟨525914, by decide⟩,⟨525924, by decide⟩]) unmarked_context_12_74020_525925 node_context_12_74020_525925
  intro a
  fin_cases a
  · exact context_13_296080_525867
  · exact context_13_296081_525892
  · exact context_13_296082_525914
  · exact context_13_296083_525924

theorem selected_cut_20486 : selected 8 ⟨525962, by decide⟩
    (prefixPartial 13 296084) = some ⟨13, 2, 0, 525962, 296084, 2053, 16384⟩ := by
  decide +kernel

theorem context_13_296084_525962 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296084 ⟨525962, by decide⟩ :=
  accepted_of_selected 13 296084 ⟨525962, by decide⟩ ⟨13, 2, 0, 525962, 296084, 2053, 16384⟩
    (by decide) selected_cut_20486

theorem selected_cut_20487 : selected 8 ⟨525995, by decide⟩
    (prefixPartial 13 296085) = some ⟨13, 2, 0, 525995, 296085, 2729, 16384⟩ := by
  decide +kernel

theorem context_13_296085_525995 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296085 ⟨525995, by decide⟩ :=
  accepted_of_selected 13 296085 ⟨525995, by decide⟩ ⟨13, 2, 0, 525995, 296085, 2729, 16384⟩
    (by decide) selected_cut_20487

theorem selected_cut_20488 : selected 8 ⟨526019, by decide⟩
    (prefixPartial 13 296086) = some ⟨13, 2, 0, 526019, 296086, 2505, 16384⟩ := by
  decide +kernel

theorem context_13_296086_526019 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296086 ⟨526019, by decide⟩ :=
  accepted_of_selected 13 296086 ⟨526019, by decide⟩ ⟨13, 2, 0, 526019, 296086, 2505, 16384⟩
    (by decide) selected_cut_20488

theorem selected_cut_20489 : selected 8 ⟨526031, by decide⟩
    (prefixPartial 13 296087) = some ⟨13, 2, 0, 526031, 296087, 1209, 16384⟩ := by
  decide +kernel

theorem context_13_296087_526031 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296087 ⟨526031, by decide⟩ :=
  accepted_of_selected 13 296087 ⟨526031, by decide⟩ ⟨13, 2, 0, 526031, 296087, 1209, 16384⟩
    (by decide) selected_cut_20489

theorem unmarked_context_12_74021_526032 : frontier 9 ⟨526032, by decide⟩
    (prefixCache 12 74021) (prefixPartial 12 74021) = false := by
  decide +kernel

theorem node_context_12_74021_526032 : EJMOriginalGlobalDAGData.nodes 9 ⟨526032, by decide⟩ =
    .split (coordinate 12) (![⟨525962, by decide⟩,⟨525995, by decide⟩,⟨526019, by decide⟩,⟨526031, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74021_526032 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74021 ⟨526032, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74021
    ⟨526032, by decide⟩ (by decide) (![⟨525962, by decide⟩,⟨525995, by decide⟩,⟨526019, by decide⟩,⟨526031, by decide⟩]) unmarked_context_12_74021_526032 node_context_12_74021_526032
  intro a
  fin_cases a
  · exact context_13_296084_525962
  · exact context_13_296085_525995
  · exact context_13_296086_526019
  · exact context_13_296087_526031

theorem selected_cut_20490 : selected 8 ⟨526055, by decide⟩
    (prefixPartial 13 296088) = some ⟨13, 2, 0, 526055, 296088, 969, 16384⟩ := by
  decide +kernel

theorem context_13_296088_526055 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296088 ⟨526055, by decide⟩ :=
  accepted_of_selected 13 296088 ⟨526055, by decide⟩ ⟨13, 2, 0, 526055, 296088, 969, 16384⟩
    (by decide) selected_cut_20490

theorem selected_cut_20491 : selected 8 ⟨526076, by decide⟩
    (prefixPartial 13 296089) = some ⟨13, 2, 0, 526076, 296089, 1525, 16384⟩ := by
  decide +kernel

theorem context_13_296089_526076 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296089 ⟨526076, by decide⟩ :=
  accepted_of_selected 13 296089 ⟨526076, by decide⟩ ⟨13, 2, 0, 526076, 296089, 1525, 16384⟩
    (by decide) selected_cut_20491

theorem selected_cut_20492 : selected 8 ⟨526090, by decide⟩
    (prefixPartial 13 296090) = some ⟨13, 2, 0, 526090, 296090, 949, 16384⟩ := by
  decide +kernel

theorem context_13_296090_526090 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296090 ⟨526090, by decide⟩ :=
  accepted_of_selected 13 296090 ⟨526090, by decide⟩ ⟨13, 2, 0, 526090, 296090, 949, 16384⟩
    (by decide) selected_cut_20492

theorem selected_cut_20493 : selected 8 ⟨526101, by decide⟩
    (prefixPartial 13 296091) = some ⟨13, 2, 0, 526101, 296091, 845, 16384⟩ := by
  decide +kernel

theorem context_13_296091_526101 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296091 ⟨526101, by decide⟩ :=
  accepted_of_selected 13 296091 ⟨526101, by decide⟩ ⟨13, 2, 0, 526101, 296091, 845, 16384⟩
    (by decide) selected_cut_20493

theorem unmarked_context_12_74022_526102 : frontier 9 ⟨526102, by decide⟩
    (prefixCache 12 74022) (prefixPartial 12 74022) = false := by
  decide +kernel

theorem node_context_12_74022_526102 : EJMOriginalGlobalDAGData.nodes 9 ⟨526102, by decide⟩ =
    .split (coordinate 12) (![⟨526055, by decide⟩,⟨526076, by decide⟩,⟨526090, by decide⟩,⟨526101, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74022_526102 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74022 ⟨526102, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74022
    ⟨526102, by decide⟩ (by decide) (![⟨526055, by decide⟩,⟨526076, by decide⟩,⟨526090, by decide⟩,⟨526101, by decide⟩]) unmarked_context_12_74022_526102 node_context_12_74022_526102
  intro a
  fin_cases a
  · exact context_13_296088_526055
  · exact context_13_296089_526076
  · exact context_13_296090_526090
  · exact context_13_296091_526101

theorem selected_cut_20494 : selected 8 ⟨526131, by decide⟩
    (prefixPartial 13 296092) = some ⟨13, 2, 0, 526131, 296092, 1029, 16384⟩ := by
  decide +kernel

theorem context_13_296092_526131 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296092 ⟨526131, by decide⟩ :=
  accepted_of_selected 13 296092 ⟨526131, by decide⟩ ⟨13, 2, 0, 526131, 296092, 1029, 16384⟩
    (by decide) selected_cut_20494

theorem selected_cut_20495 : selected 8 ⟨526155, by decide⟩
    (prefixPartial 13 296093) = some ⟨13, 2, 0, 526155, 296093, 1769, 16384⟩ := by
  decide +kernel

theorem context_13_296093_526155 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296093 ⟨526155, by decide⟩ :=
  accepted_of_selected 13 296093 ⟨526155, by decide⟩ ⟨13, 2, 0, 526155, 296093, 1769, 16384⟩
    (by decide) selected_cut_20495

theorem selected_cut_20496 : selected 8 ⟨526176, by decide⟩
    (prefixPartial 13 296094) = some ⟨13, 2, 0, 526176, 296094, 1429, 16384⟩ := by
  decide +kernel

theorem context_13_296094_526176 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296094 ⟨526176, by decide⟩ :=
  accepted_of_selected 13 296094 ⟨526176, by decide⟩ ⟨13, 2, 0, 526176, 296094, 1429, 16384⟩
    (by decide) selected_cut_20496

theorem selected_cut_20497 : selected 8 ⟨526182, by decide⟩
    (prefixPartial 13 296095) = some ⟨13, 2, 0, 526182, 296095, 637, 16384⟩ := by
  decide +kernel

theorem context_13_296095_526182 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296095 ⟨526182, by decide⟩ :=
  accepted_of_selected 13 296095 ⟨526182, by decide⟩ ⟨13, 2, 0, 526182, 296095, 637, 16384⟩
    (by decide) selected_cut_20497

theorem unmarked_context_12_74023_526183 : frontier 9 ⟨526183, by decide⟩
    (prefixCache 12 74023) (prefixPartial 12 74023) = false := by
  decide +kernel

theorem node_context_12_74023_526183 : EJMOriginalGlobalDAGData.nodes 9 ⟨526183, by decide⟩ =
    .split (coordinate 12) (![⟨526131, by decide⟩,⟨526155, by decide⟩,⟨526176, by decide⟩,⟨526182, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74023_526183 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74023 ⟨526183, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74023
    ⟨526183, by decide⟩ (by decide) (![⟨526131, by decide⟩,⟨526155, by decide⟩,⟨526176, by decide⟩,⟨526182, by decide⟩]) unmarked_context_12_74023_526183 node_context_12_74023_526183
  intro a
  fin_cases a
  · exact context_13_296092_526131
  · exact context_13_296093_526155
  · exact context_13_296094_526176
  · exact context_13_296095_526182

theorem unmarked_context_11_18505_526184 : frontier 10 ⟨526184, by decide⟩
    (prefixCache 11 18505) (prefixPartial 11 18505) = false := by
  decide +kernel

theorem node_context_11_18505_526184 : EJMOriginalGlobalDAGData.nodes 10 ⟨526184, by decide⟩ =
    .split (coordinate 11) (![⟨525925, by decide⟩,⟨526032, by decide⟩,⟨526102, by decide⟩,⟨526183, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18505_526184 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18505 ⟨526184, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18505
    ⟨526184, by decide⟩ (by decide) (![⟨525925, by decide⟩,⟨526032, by decide⟩,⟨526102, by decide⟩,⟨526183, by decide⟩]) unmarked_context_11_18505_526184 node_context_11_18505_526184
  intro a
  fin_cases a
  · exact context_12_74020_525925
  · exact context_12_74021_526032
  · exact context_12_74022_526102
  · exact context_12_74023_526183

theorem selected_cut_20498 : selected 9 ⟨435790, by decide⟩
    (prefixPartial 12 74024) = some ⟨12, 1, 0, 435790, 74024, 1, 65536⟩ := by
  decide +kernel

theorem context_12_74024_435790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74024 ⟨435790, by decide⟩ :=
  accepted_of_selected 12 74024 ⟨435790, by decide⟩ ⟨12, 1, 0, 435790, 74024, 1, 65536⟩
    (by decide) selected_cut_20498

theorem selected_cut_20499 : selected 8 ⟨526204, by decide⟩
    (prefixPartial 13 296100) = some ⟨13, 2, 0, 526204, 296100, 993, 16384⟩ := by
  decide +kernel

theorem context_13_296100_526204 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296100 ⟨526204, by decide⟩ :=
  accepted_of_selected 13 296100 ⟨526204, by decide⟩ ⟨13, 2, 0, 526204, 296100, 993, 16384⟩
    (by decide) selected_cut_20499

theorem selected_cut_20500 : selected 8 ⟨526226, by decide⟩
    (prefixPartial 13 296101) = some ⟨13, 2, 0, 526226, 296101, 1405, 16384⟩ := by
  decide +kernel

theorem context_13_296101_526226 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296101 ⟨526226, by decide⟩ :=
  accepted_of_selected 13 296101 ⟨526226, by decide⟩ ⟨13, 2, 0, 526226, 296101, 1405, 16384⟩
    (by decide) selected_cut_20500

theorem selected_cut_20501 : selected 8 ⟨526250, by decide⟩
    (prefixPartial 13 296102) = some ⟨13, 2, 0, 526250, 296102, 1937, 16384⟩ := by
  decide +kernel

theorem context_13_296102_526250 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296102 ⟨526250, by decide⟩ :=
  accepted_of_selected 13 296102 ⟨526250, by decide⟩ ⟨13, 2, 0, 526250, 296102, 1937, 16384⟩
    (by decide) selected_cut_20501

theorem selected_cut_20502 : selected 8 ⟨526258, by decide⟩
    (prefixPartial 13 296103) = some ⟨13, 2, 0, 526258, 296103, 901, 16384⟩ := by
  decide +kernel

theorem context_13_296103_526258 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296103 ⟨526258, by decide⟩ :=
  accepted_of_selected 13 296103 ⟨526258, by decide⟩ ⟨13, 2, 0, 526258, 296103, 901, 16384⟩
    (by decide) selected_cut_20502

theorem unmarked_context_12_74025_526259 : frontier 9 ⟨526259, by decide⟩
    (prefixCache 12 74025) (prefixPartial 12 74025) = false := by
  decide +kernel

theorem node_context_12_74025_526259 : EJMOriginalGlobalDAGData.nodes 9 ⟨526259, by decide⟩ =
    .split (coordinate 12) (![⟨526204, by decide⟩,⟨526226, by decide⟩,⟨526250, by decide⟩,⟨526258, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74025_526259 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74025 ⟨526259, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74025
    ⟨526259, by decide⟩ (by decide) (![⟨526204, by decide⟩,⟨526226, by decide⟩,⟨526250, by decide⟩,⟨526258, by decide⟩]) unmarked_context_12_74025_526259 node_context_12_74025_526259
  intro a
  fin_cases a
  · exact context_13_296100_526204
  · exact context_13_296101_526226
  · exact context_13_296102_526250
  · exact context_13_296103_526258

theorem selected_cut_20503 : selected 8 ⟨526272, by decide⟩
    (prefixPartial 13 296104) = some ⟨13, 2, 0, 526272, 296104, 805, 16384⟩ := by
  decide +kernel

theorem context_13_296104_526272 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296104 ⟨526272, by decide⟩ :=
  accepted_of_selected 13 296104 ⟨526272, by decide⟩ ⟨13, 2, 0, 526272, 296104, 805, 16384⟩
    (by decide) selected_cut_20503

theorem selected_cut_20504 : selected 8 ⟨526294, by decide⟩
    (prefixPartial 13 296105) = some ⟨13, 2, 0, 526294, 296105, 1509, 16384⟩ := by
  decide +kernel

theorem context_13_296105_526294 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296105 ⟨526294, by decide⟩ :=
  accepted_of_selected 13 296105 ⟨526294, by decide⟩ ⟨13, 2, 0, 526294, 296105, 1509, 16384⟩
    (by decide) selected_cut_20504

theorem selected_cut_20505 : selected 8 ⟨526309, by decide⟩
    (prefixPartial 13 296106) = some ⟨13, 2, 0, 526309, 296106, 1133, 16384⟩ := by
  decide +kernel

theorem context_13_296106_526309 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296106 ⟨526309, by decide⟩ :=
  accepted_of_selected 13 296106 ⟨526309, by decide⟩ ⟨13, 2, 0, 526309, 296106, 1133, 16384⟩
    (by decide) selected_cut_20505

theorem selected_cut_20506 : selected 8 ⟨526316, by decide⟩
    (prefixPartial 13 296107) = some ⟨13, 2, 0, 526316, 296107, 849, 16384⟩ := by
  decide +kernel

theorem context_13_296107_526316 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296107 ⟨526316, by decide⟩ :=
  accepted_of_selected 13 296107 ⟨526316, by decide⟩ ⟨13, 2, 0, 526316, 296107, 849, 16384⟩
    (by decide) selected_cut_20506

theorem unmarked_context_12_74026_526317 : frontier 9 ⟨526317, by decide⟩
    (prefixCache 12 74026) (prefixPartial 12 74026) = false := by
  decide +kernel

theorem node_context_12_74026_526317 : EJMOriginalGlobalDAGData.nodes 9 ⟨526317, by decide⟩ =
    .split (coordinate 12) (![⟨526272, by decide⟩,⟨526294, by decide⟩,⟨526309, by decide⟩,⟨526316, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74026_526317 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74026 ⟨526317, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74026
    ⟨526317, by decide⟩ (by decide) (![⟨526272, by decide⟩,⟨526294, by decide⟩,⟨526309, by decide⟩,⟨526316, by decide⟩]) unmarked_context_12_74026_526317 node_context_12_74026_526317
  intro a
  fin_cases a
  · exact context_13_296104_526272
  · exact context_13_296105_526294
  · exact context_13_296106_526309
  · exact context_13_296107_526316

theorem selected_cut_20507 : selected 8 ⟨526335, by decide⟩
    (prefixPartial 13 296108) = some ⟨13, 2, 0, 526335, 296108, 817, 16384⟩ := by
  decide +kernel

theorem context_13_296108_526335 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296108 ⟨526335, by decide⟩ :=
  accepted_of_selected 13 296108 ⟨526335, by decide⟩ ⟨13, 2, 0, 526335, 296108, 817, 16384⟩
    (by decide) selected_cut_20507

theorem selected_cut_20508 : selected 8 ⟨526355, by decide⟩
    (prefixPartial 13 296109) = some ⟨13, 2, 0, 526355, 296109, 1889, 16384⟩ := by
  decide +kernel

theorem context_13_296109_526355 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296109 ⟨526355, by decide⟩ :=
  accepted_of_selected 13 296109 ⟨526355, by decide⟩ ⟨13, 2, 0, 526355, 296109, 1889, 16384⟩
    (by decide) selected_cut_20508

theorem selected_cut_20509 : selected 8 ⟨526376, by decide⟩
    (prefixPartial 13 296110) = some ⟨13, 2, 0, 526376, 296110, 1577, 16384⟩ := by
  decide +kernel

theorem context_13_296110_526376 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296110 ⟨526376, by decide⟩ :=
  accepted_of_selected 13 296110 ⟨526376, by decide⟩ ⟨13, 2, 0, 526376, 296110, 1577, 16384⟩
    (by decide) selected_cut_20509

theorem selected_cut_20510 : selected 8 ⟨526383, by decide⟩
    (prefixPartial 13 296111) = some ⟨13, 2, 0, 526383, 296111, 653, 16384⟩ := by
  decide +kernel

theorem context_13_296111_526383 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296111 ⟨526383, by decide⟩ :=
  accepted_of_selected 13 296111 ⟨526383, by decide⟩ ⟨13, 2, 0, 526383, 296111, 653, 16384⟩
    (by decide) selected_cut_20510

theorem unmarked_context_12_74027_526384 : frontier 9 ⟨526384, by decide⟩
    (prefixCache 12 74027) (prefixPartial 12 74027) = false := by
  decide +kernel

theorem node_context_12_74027_526384 : EJMOriginalGlobalDAGData.nodes 9 ⟨526384, by decide⟩ =
    .split (coordinate 12) (![⟨526335, by decide⟩,⟨526355, by decide⟩,⟨526376, by decide⟩,⟨526383, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74027_526384 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74027 ⟨526384, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74027
    ⟨526384, by decide⟩ (by decide) (![⟨526335, by decide⟩,⟨526355, by decide⟩,⟨526376, by decide⟩,⟨526383, by decide⟩]) unmarked_context_12_74027_526384 node_context_12_74027_526384
  intro a
  fin_cases a
  · exact context_13_296108_526335
  · exact context_13_296109_526355
  · exact context_13_296110_526376
  · exact context_13_296111_526383

theorem unmarked_context_11_18506_526385 : frontier 10 ⟨526385, by decide⟩
    (prefixCache 11 18506) (prefixPartial 11 18506) = false := by
  decide +kernel

theorem node_context_11_18506_526385 : EJMOriginalGlobalDAGData.nodes 10 ⟨526385, by decide⟩ =
    .split (coordinate 11) (![⟨435790, by decide⟩,⟨526259, by decide⟩,⟨526317, by decide⟩,⟨526384, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18506_526385 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18506 ⟨526385, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18506
    ⟨526385, by decide⟩ (by decide) (![⟨435790, by decide⟩,⟨526259, by decide⟩,⟨526317, by decide⟩,⟨526384, by decide⟩]) unmarked_context_11_18506_526385 node_context_11_18506_526385
  intro a
  fin_cases a
  · exact context_12_74024_435790
  · exact context_12_74025_526259
  · exact context_12_74026_526317
  · exact context_12_74027_526384

theorem selected_cut_20511 : selected 8 ⟨526404, by decide⟩
    (prefixPartial 13 296112) = some ⟨13, 2, 0, 526404, 296112, 933, 16384⟩ := by
  decide +kernel

theorem context_13_296112_526404 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296112 ⟨526404, by decide⟩ :=
  accepted_of_selected 13 296112 ⟨526404, by decide⟩ ⟨13, 2, 0, 526404, 296112, 933, 16384⟩
    (by decide) selected_cut_20511

theorem selected_cut_20512 : selected 8 ⟨526434, by decide⟩
    (prefixPartial 13 296113) = some ⟨13, 2, 0, 526434, 296113, 3009, 16384⟩ := by
  decide +kernel

theorem context_13_296113_526434 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296113 ⟨526434, by decide⟩ :=
  accepted_of_selected 13 296113 ⟨526434, by decide⟩ ⟨13, 2, 0, 526434, 296113, 3009, 16384⟩
    (by decide) selected_cut_20512

theorem selected_cut_20513 : selected 8 ⟨526458, by decide⟩
    (prefixPartial 13 296114) = some ⟨13, 2, 0, 526458, 296114, 2041, 16384⟩ := by
  decide +kernel

theorem context_13_296114_526458 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296114 ⟨526458, by decide⟩ :=
  accepted_of_selected 13 296114 ⟨526458, by decide⟩ ⟨13, 2, 0, 526458, 296114, 2041, 16384⟩
    (by decide) selected_cut_20513

theorem selected_cut_20514 : selected 8 ⟨526466, by decide⟩
    (prefixPartial 13 296115) = some ⟨13, 2, 0, 526466, 296115, 1029, 16384⟩ := by
  decide +kernel

theorem context_13_296115_526466 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296115 ⟨526466, by decide⟩ :=
  accepted_of_selected 13 296115 ⟨526466, by decide⟩ ⟨13, 2, 0, 526466, 296115, 1029, 16384⟩
    (by decide) selected_cut_20514

theorem unmarked_context_12_74028_526467 : frontier 9 ⟨526467, by decide⟩
    (prefixCache 12 74028) (prefixPartial 12 74028) = false := by
  decide +kernel

theorem node_context_12_74028_526467 : EJMOriginalGlobalDAGData.nodes 9 ⟨526467, by decide⟩ =
    .split (coordinate 12) (![⟨526404, by decide⟩,⟨526434, by decide⟩,⟨526458, by decide⟩,⟨526466, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74028_526467 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74028 ⟨526467, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74028
    ⟨526467, by decide⟩ (by decide) (![⟨526404, by decide⟩,⟨526434, by decide⟩,⟨526458, by decide⟩,⟨526466, by decide⟩]) unmarked_context_12_74028_526467 node_context_12_74028_526467
  intro a
  fin_cases a
  · exact context_13_296112_526404
  · exact context_13_296113_526434
  · exact context_13_296114_526458
  · exact context_13_296115_526466

theorem selected_cut_20515 : selected 8 ⟨526485, by decide⟩
    (prefixPartial 13 296116) = some ⟨13, 2, 0, 526485, 296116, 733, 16384⟩ := by
  decide +kernel

theorem context_13_296116_526485 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296116 ⟨526485, by decide⟩ :=
  accepted_of_selected 13 296116 ⟨526485, by decide⟩ ⟨13, 2, 0, 526485, 296116, 733, 16384⟩
    (by decide) selected_cut_20515

theorem selected_cut_20516 : selected 8 ⟨526506, by decide⟩
    (prefixPartial 13 296117) = some ⟨13, 2, 0, 526506, 296117, 1713, 16384⟩ := by
  decide +kernel

theorem context_13_296117_526506 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296117 ⟨526506, by decide⟩ :=
  accepted_of_selected 13 296117 ⟨526506, by decide⟩ ⟨13, 2, 0, 526506, 296117, 1713, 16384⟩
    (by decide) selected_cut_20516

theorem selected_cut_20517 : selected 8 ⟨526525, by decide⟩
    (prefixPartial 13 296118) = some ⟨13, 2, 0, 526525, 296118, 1833, 16384⟩ := by
  decide +kernel

theorem context_13_296118_526525 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296118 ⟨526525, by decide⟩ :=
  accepted_of_selected 13 296118 ⟨526525, by decide⟩ ⟨13, 2, 0, 526525, 296118, 1833, 16384⟩
    (by decide) selected_cut_20517

theorem selected_cut_20518 : selected 8 ⟨526532, by decide⟩
    (prefixPartial 13 296119) = some ⟨13, 2, 0, 526532, 296119, 869, 16384⟩ := by
  decide +kernel

theorem context_13_296119_526532 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296119 ⟨526532, by decide⟩ :=
  accepted_of_selected 13 296119 ⟨526532, by decide⟩ ⟨13, 2, 0, 526532, 296119, 869, 16384⟩
    (by decide) selected_cut_20518

theorem unmarked_context_12_74029_526533 : frontier 9 ⟨526533, by decide⟩
    (prefixCache 12 74029) (prefixPartial 12 74029) = false := by
  decide +kernel

theorem node_context_12_74029_526533 : EJMOriginalGlobalDAGData.nodes 9 ⟨526533, by decide⟩ =
    .split (coordinate 12) (![⟨526485, by decide⟩,⟨526506, by decide⟩,⟨526525, by decide⟩,⟨526532, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74029_526533 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74029 ⟨526533, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74029
    ⟨526533, by decide⟩ (by decide) (![⟨526485, by decide⟩,⟨526506, by decide⟩,⟨526525, by decide⟩,⟨526532, by decide⟩]) unmarked_context_12_74029_526533 node_context_12_74029_526533
  intro a
  fin_cases a
  · exact context_13_296116_526485
  · exact context_13_296117_526506
  · exact context_13_296118_526525
  · exact context_13_296119_526532

theorem selected_cut_20519 : selected 8 ⟨526546, by decide⟩
    (prefixPartial 13 296120) = some ⟨13, 2, 0, 526546, 296120, 745, 16384⟩ := by
  decide +kernel

theorem context_13_296120_526546 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296120 ⟨526546, by decide⟩ :=
  accepted_of_selected 13 296120 ⟨526546, by decide⟩ ⟨13, 2, 0, 526546, 296120, 745, 16384⟩
    (by decide) selected_cut_20519

theorem selected_cut_20520 : selected 8 ⟨526569, by decide⟩
    (prefixPartial 13 296121) = some ⟨13, 2, 0, 526569, 296121, 1849, 16384⟩ := by
  decide +kernel

theorem context_13_296121_526569 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296121 ⟨526569, by decide⟩ :=
  accepted_of_selected 13 296121 ⟨526569, by decide⟩ ⟨13, 2, 0, 526569, 296121, 1849, 16384⟩
    (by decide) selected_cut_20520

theorem selected_cut_20521 : selected 8 ⟨526584, by decide⟩
    (prefixPartial 13 296122) = some ⟨13, 2, 0, 526584, 296122, 1133, 16384⟩ := by
  decide +kernel

theorem context_13_296122_526584 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296122 ⟨526584, by decide⟩ :=
  accepted_of_selected 13 296122 ⟨526584, by decide⟩ ⟨13, 2, 0, 526584, 296122, 1133, 16384⟩
    (by decide) selected_cut_20521

theorem selected_cut_20522 : selected 8 ⟨526590, by decide⟩
    (prefixPartial 13 296123) = some ⟨13, 2, 0, 526590, 296123, 973, 16384⟩ := by
  decide +kernel

theorem context_13_296123_526590 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296123 ⟨526590, by decide⟩ :=
  accepted_of_selected 13 296123 ⟨526590, by decide⟩ ⟨13, 2, 0, 526590, 296123, 973, 16384⟩
    (by decide) selected_cut_20522

theorem unmarked_context_12_74030_526591 : frontier 9 ⟨526591, by decide⟩
    (prefixCache 12 74030) (prefixPartial 12 74030) = false := by
  decide +kernel

theorem node_context_12_74030_526591 : EJMOriginalGlobalDAGData.nodes 9 ⟨526591, by decide⟩ =
    .split (coordinate 12) (![⟨526546, by decide⟩,⟨526569, by decide⟩,⟨526584, by decide⟩,⟨526590, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74030_526591 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74030 ⟨526591, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74030
    ⟨526591, by decide⟩ (by decide) (![⟨526546, by decide⟩,⟨526569, by decide⟩,⟨526584, by decide⟩,⟨526590, by decide⟩]) unmarked_context_12_74030_526591 node_context_12_74030_526591
  intro a
  fin_cases a
  · exact context_13_296120_526546
  · exact context_13_296121_526569
  · exact context_13_296122_526584
  · exact context_13_296123_526590

theorem selected_cut_20523 : selected 8 ⟨526603, by decide⟩
    (prefixPartial 13 296124) = some ⟨13, 2, 0, 526603, 296124, 693, 16384⟩ := by
  decide +kernel

theorem context_13_296124_526603 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296124 ⟨526603, by decide⟩ :=
  accepted_of_selected 13 296124 ⟨526603, by decide⟩ ⟨13, 2, 0, 526603, 296124, 693, 16384⟩
    (by decide) selected_cut_20523

theorem selected_cut_20524 : selected 8 ⟨526629, by decide⟩
    (prefixPartial 13 296125) = some ⟨13, 2, 0, 526629, 296125, 2105, 16384⟩ := by
  decide +kernel

theorem context_13_296125_526629 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296125 ⟨526629, by decide⟩ :=
  accepted_of_selected 13 296125 ⟨526629, by decide⟩ ⟨13, 2, 0, 526629, 296125, 2105, 16384⟩
    (by decide) selected_cut_20524

theorem selected_cut_20525 : selected 8 ⟨526649, by decide⟩
    (prefixPartial 13 296126) = some ⟨13, 2, 0, 526649, 296126, 1497, 16384⟩ := by
  decide +kernel

theorem context_13_296126_526649 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296126 ⟨526649, by decide⟩ :=
  accepted_of_selected 13 296126 ⟨526649, by decide⟩ ⟨13, 2, 0, 526649, 296126, 1497, 16384⟩
    (by decide) selected_cut_20525

theorem selected_cut_20526 : selected 8 ⟨526657, by decide⟩
    (prefixPartial 13 296127) = some ⟨13, 2, 0, 526657, 296127, 729, 16384⟩ := by
  decide +kernel

theorem context_13_296127_526657 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296127 ⟨526657, by decide⟩ :=
  accepted_of_selected 13 296127 ⟨526657, by decide⟩ ⟨13, 2, 0, 526657, 296127, 729, 16384⟩
    (by decide) selected_cut_20526

theorem unmarked_context_12_74031_526658 : frontier 9 ⟨526658, by decide⟩
    (prefixCache 12 74031) (prefixPartial 12 74031) = false := by
  decide +kernel

theorem node_context_12_74031_526658 : EJMOriginalGlobalDAGData.nodes 9 ⟨526658, by decide⟩ =
    .split (coordinate 12) (![⟨526603, by decide⟩,⟨526629, by decide⟩,⟨526649, by decide⟩,⟨526657, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74031_526658 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74031 ⟨526658, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74031
    ⟨526658, by decide⟩ (by decide) (![⟨526603, by decide⟩,⟨526629, by decide⟩,⟨526649, by decide⟩,⟨526657, by decide⟩]) unmarked_context_12_74031_526658 node_context_12_74031_526658
  intro a
  fin_cases a
  · exact context_13_296124_526603
  · exact context_13_296125_526629
  · exact context_13_296126_526649
  · exact context_13_296127_526657

theorem unmarked_context_11_18507_526659 : frontier 10 ⟨526659, by decide⟩
    (prefixCache 11 18507) (prefixPartial 11 18507) = false := by
  decide +kernel

theorem node_context_11_18507_526659 : EJMOriginalGlobalDAGData.nodes 10 ⟨526659, by decide⟩ =
    .split (coordinate 11) (![⟨526467, by decide⟩,⟨526533, by decide⟩,⟨526591, by decide⟩,⟨526658, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18507_526659 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18507 ⟨526659, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18507
    ⟨526659, by decide⟩ (by decide) (![⟨526467, by decide⟩,⟨526533, by decide⟩,⟨526591, by decide⟩,⟨526658, by decide⟩]) unmarked_context_11_18507_526659 node_context_11_18507_526659
  intro a
  fin_cases a
  · exact context_12_74028_526467
  · exact context_12_74029_526533
  · exact context_12_74030_526591
  · exact context_12_74031_526658

theorem unmarked_context_10_4626_526660 : frontier 11 ⟨526660, by decide⟩
    (prefixCache 10 4626) (prefixPartial 10 4626) = false := by
  decide +kernel

theorem node_context_10_4626_526660 : EJMOriginalGlobalDAGData.nodes 11 ⟨526660, by decide⟩ =
    .split (coordinate 10) (![⟨525838, by decide⟩,⟨526184, by decide⟩,⟨526385, by decide⟩,⟨526659, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4626_526660 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4626 ⟨526660, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4626
    ⟨526660, by decide⟩ (by decide) (![⟨525838, by decide⟩,⟨526184, by decide⟩,⟨526385, by decide⟩,⟨526659, by decide⟩]) unmarked_context_10_4626_526660 node_context_10_4626_526660
  intro a
  fin_cases a
  · exact context_11_18504_525838
  · exact context_11_18505_526184
  · exact context_11_18506_526385
  · exact context_11_18507_526659

theorem selected_cut_20527 : selected 9 ⟨445562, by decide⟩
    (prefixPartial 12 74032) = some ⟨12, 1, 0, 445562, 74032, 1, 65536⟩ := by
  decide +kernel

theorem context_12_74032_445562 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74032 ⟨445562, by decide⟩ :=
  accepted_of_selected 12 74032 ⟨445562, by decide⟩ ⟨12, 1, 0, 445562, 74032, 1, 65536⟩
    (by decide) selected_cut_20527

theorem selected_cut_20528 : selected 8 ⟨526674, by decide⟩
    (prefixPartial 13 296132) = some ⟨13, 2, 0, 526674, 296132, 553, 16384⟩ := by
  decide +kernel

theorem context_13_296132_526674 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296132 ⟨526674, by decide⟩ :=
  accepted_of_selected 13 296132 ⟨526674, by decide⟩ ⟨13, 2, 0, 526674, 296132, 553, 16384⟩
    (by decide) selected_cut_20528

theorem selected_cut_20529 : selected 8 ⟨526697, by decide⟩
    (prefixPartial 13 296133) = some ⟨13, 2, 0, 526697, 296133, 1629, 16384⟩ := by
  decide +kernel

theorem context_13_296133_526697 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296133 ⟨526697, by decide⟩ :=
  accepted_of_selected 13 296133 ⟨526697, by decide⟩ ⟨13, 2, 0, 526697, 296133, 1629, 16384⟩
    (by decide) selected_cut_20529

theorem selected_cut_20530 : selected 8 ⟨526717, by decide⟩
    (prefixPartial 13 296134) = some ⟨13, 2, 0, 526717, 296134, 1465, 16384⟩ := by
  decide +kernel

theorem context_13_296134_526717 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296134 ⟨526717, by decide⟩ :=
  accepted_of_selected 13 296134 ⟨526717, by decide⟩ ⟨13, 2, 0, 526717, 296134, 1465, 16384⟩
    (by decide) selected_cut_20530

theorem selected_cut_20531 : selected 8 ⟨526727, by decide⟩
    (prefixPartial 13 296135) = some ⟨13, 2, 0, 526727, 296135, 769, 16384⟩ := by
  decide +kernel

theorem context_13_296135_526727 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296135 ⟨526727, by decide⟩ :=
  accepted_of_selected 13 296135 ⟨526727, by decide⟩ ⟨13, 2, 0, 526727, 296135, 769, 16384⟩
    (by decide) selected_cut_20531

theorem unmarked_context_12_74033_526728 : frontier 9 ⟨526728, by decide⟩
    (prefixCache 12 74033) (prefixPartial 12 74033) = false := by
  decide +kernel

theorem node_context_12_74033_526728 : EJMOriginalGlobalDAGData.nodes 9 ⟨526728, by decide⟩ =
    .split (coordinate 12) (![⟨526674, by decide⟩,⟨526697, by decide⟩,⟨526717, by decide⟩,⟨526727, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74033_526728 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74033 ⟨526728, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74033
    ⟨526728, by decide⟩ (by decide) (![⟨526674, by decide⟩,⟨526697, by decide⟩,⟨526717, by decide⟩,⟨526727, by decide⟩]) unmarked_context_12_74033_526728 node_context_12_74033_526728
  intro a
  fin_cases a
  · exact context_13_296132_526674
  · exact context_13_296133_526697
  · exact context_13_296134_526717
  · exact context_13_296135_526727

theorem selected_cut_20532 : selected 8 ⟨526738, by decide⟩
    (prefixPartial 13 296136) = some ⟨13, 2, 0, 526738, 296136, 485, 16384⟩ := by
  decide +kernel

theorem context_13_296136_526738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296136 ⟨526738, by decide⟩ :=
  accepted_of_selected 13 296136 ⟨526738, by decide⟩ ⟨13, 2, 0, 526738, 296136, 485, 16384⟩
    (by decide) selected_cut_20532

theorem selected_cut_20533 : selected 8 ⟨526763, by decide⟩
    (prefixPartial 13 296137) = some ⟨13, 2, 0, 526763, 296137, 1977, 16384⟩ := by
  decide +kernel

theorem context_13_296137_526763 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296137 ⟨526763, by decide⟩ :=
  accepted_of_selected 13 296137 ⟨526763, by decide⟩ ⟨13, 2, 0, 526763, 296137, 1977, 16384⟩
    (by decide) selected_cut_20533

theorem selected_cut_20534 : selected 8 ⟨526778, by decide⟩
    (prefixPartial 13 296138) = some ⟨13, 2, 0, 526778, 296138, 1089, 16384⟩ := by
  decide +kernel

theorem context_13_296138_526778 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296138 ⟨526778, by decide⟩ :=
  accepted_of_selected 13 296138 ⟨526778, by decide⟩ ⟨13, 2, 0, 526778, 296138, 1089, 16384⟩
    (by decide) selected_cut_20534

theorem selected_cut_20535 : selected 8 ⟨526786, by decide⟩
    (prefixPartial 13 296139) = some ⟨13, 2, 0, 526786, 296139, 745, 16384⟩ := by
  decide +kernel

theorem context_13_296139_526786 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296139 ⟨526786, by decide⟩ :=
  accepted_of_selected 13 296139 ⟨526786, by decide⟩ ⟨13, 2, 0, 526786, 296139, 745, 16384⟩
    (by decide) selected_cut_20535

theorem unmarked_context_12_74034_526787 : frontier 9 ⟨526787, by decide⟩
    (prefixCache 12 74034) (prefixPartial 12 74034) = false := by
  decide +kernel

theorem node_context_12_74034_526787 : EJMOriginalGlobalDAGData.nodes 9 ⟨526787, by decide⟩ =
    .split (coordinate 12) (![⟨526738, by decide⟩,⟨526763, by decide⟩,⟨526778, by decide⟩,⟨526786, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74034_526787 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74034 ⟨526787, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74034
    ⟨526787, by decide⟩ (by decide) (![⟨526738, by decide⟩,⟨526763, by decide⟩,⟨526778, by decide⟩,⟨526786, by decide⟩]) unmarked_context_12_74034_526787 node_context_12_74034_526787
  intro a
  fin_cases a
  · exact context_13_296136_526738
  · exact context_13_296137_526763
  · exact context_13_296138_526778
  · exact context_13_296139_526786

theorem selected_cut_20536 : selected 8 ⟨526800, by decide⟩
    (prefixPartial 13 296140) = some ⟨13, 2, 0, 526800, 296140, 577, 16384⟩ := by
  decide +kernel

theorem context_13_296140_526800 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296140 ⟨526800, by decide⟩ :=
  accepted_of_selected 13 296140 ⟨526800, by decide⟩ ⟨13, 2, 0, 526800, 296140, 577, 16384⟩
    (by decide) selected_cut_20536

theorem selected_cut_20537 : selected 8 ⟨526827, by decide⟩
    (prefixPartial 13 296141) = some ⟨13, 2, 0, 526827, 296141, 2001, 16384⟩ := by
  decide +kernel

theorem context_13_296141_526827 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296141 ⟨526827, by decide⟩ :=
  accepted_of_selected 13 296141 ⟨526827, by decide⟩ ⟨13, 2, 0, 526827, 296141, 2001, 16384⟩
    (by decide) selected_cut_20537

theorem selected_cut_20538 : selected 8 ⟨526846, by decide⟩
    (prefixPartial 13 296142) = some ⟨13, 2, 0, 526846, 296142, 1349, 16384⟩ := by
  decide +kernel

theorem context_13_296142_526846 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296142 ⟨526846, by decide⟩ :=
  accepted_of_selected 13 296142 ⟨526846, by decide⟩ ⟨13, 2, 0, 526846, 296142, 1349, 16384⟩
    (by decide) selected_cut_20538

theorem selected_cut_20539 : selected 8 ⟨526851, by decide⟩
    (prefixPartial 13 296143) = some ⟨13, 2, 0, 526851, 296143, 569, 16384⟩ := by
  decide +kernel

theorem context_13_296143_526851 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296143 ⟨526851, by decide⟩ :=
  accepted_of_selected 13 296143 ⟨526851, by decide⟩ ⟨13, 2, 0, 526851, 296143, 569, 16384⟩
    (by decide) selected_cut_20539

theorem unmarked_context_12_74035_526852 : frontier 9 ⟨526852, by decide⟩
    (prefixCache 12 74035) (prefixPartial 12 74035) = false := by
  decide +kernel

theorem node_context_12_74035_526852 : EJMOriginalGlobalDAGData.nodes 9 ⟨526852, by decide⟩ =
    .split (coordinate 12) (![⟨526800, by decide⟩,⟨526827, by decide⟩,⟨526846, by decide⟩,⟨526851, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74035_526852 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74035 ⟨526852, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74035
    ⟨526852, by decide⟩ (by decide) (![⟨526800, by decide⟩,⟨526827, by decide⟩,⟨526846, by decide⟩,⟨526851, by decide⟩]) unmarked_context_12_74035_526852 node_context_12_74035_526852
  intro a
  fin_cases a
  · exact context_13_296140_526800
  · exact context_13_296141_526827
  · exact context_13_296142_526846
  · exact context_13_296143_526851

theorem unmarked_context_11_18508_526853 : frontier 10 ⟨526853, by decide⟩
    (prefixCache 11 18508) (prefixPartial 11 18508) = false := by
  decide +kernel

theorem node_context_11_18508_526853 : EJMOriginalGlobalDAGData.nodes 10 ⟨526853, by decide⟩ =
    .split (coordinate 11) (![⟨445562, by decide⟩,⟨526728, by decide⟩,⟨526787, by decide⟩,⟨526852, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18508_526853 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18508 ⟨526853, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18508
    ⟨526853, by decide⟩ (by decide) (![⟨445562, by decide⟩,⟨526728, by decide⟩,⟨526787, by decide⟩,⟨526852, by decide⟩]) unmarked_context_11_18508_526853 node_context_11_18508_526853
  intro a
  fin_cases a
  · exact context_12_74032_445562
  · exact context_12_74033_526728
  · exact context_12_74034_526787
  · exact context_12_74035_526852

theorem selected_cut_20540 : selected 8 ⟨526867, by decide⟩
    (prefixPartial 13 296144) = some ⟨13, 2, 0, 526867, 296144, 721, 16384⟩ := by
  decide +kernel

theorem context_13_296144_526867 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296144 ⟨526867, by decide⟩ :=
  accepted_of_selected 13 296144 ⟨526867, by decide⟩ ⟨13, 2, 0, 526867, 296144, 721, 16384⟩
    (by decide) selected_cut_20540

theorem selected_cut_20541 : selected 8 ⟨526892, by decide⟩
    (prefixPartial 13 296145) = some ⟨13, 2, 0, 526892, 296145, 2701, 16384⟩ := by
  decide +kernel

theorem context_13_296145_526892 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296145 ⟨526892, by decide⟩ :=
  accepted_of_selected 13 296145 ⟨526892, by decide⟩ ⟨13, 2, 0, 526892, 296145, 2701, 16384⟩
    (by decide) selected_cut_20541

theorem selected_cut_20542 : selected 8 ⟨526912, by decide⟩
    (prefixPartial 13 296146) = some ⟨13, 2, 0, 526912, 296146, 1813, 16384⟩ := by
  decide +kernel

theorem context_13_296146_526912 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296146 ⟨526912, by decide⟩ :=
  accepted_of_selected 13 296146 ⟨526912, by decide⟩ ⟨13, 2, 0, 526912, 296146, 1813, 16384⟩
    (by decide) selected_cut_20542

theorem selected_cut_20543 : selected 8 ⟨526917, by decide⟩
    (prefixPartial 13 296147) = some ⟨13, 2, 0, 526917, 296147, 901, 16384⟩ := by
  decide +kernel

theorem context_13_296147_526917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296147 ⟨526917, by decide⟩ :=
  accepted_of_selected 13 296147 ⟨526917, by decide⟩ ⟨13, 2, 0, 526917, 296147, 901, 16384⟩
    (by decide) selected_cut_20543

theorem unmarked_context_12_74036_526918 : frontier 9 ⟨526918, by decide⟩
    (prefixCache 12 74036) (prefixPartial 12 74036) = false := by
  decide +kernel

theorem node_context_12_74036_526918 : EJMOriginalGlobalDAGData.nodes 9 ⟨526918, by decide⟩ =
    .split (coordinate 12) (![⟨526867, by decide⟩,⟨526892, by decide⟩,⟨526912, by decide⟩,⟨526917, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74036_526918 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74036 ⟨526918, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74036
    ⟨526918, by decide⟩ (by decide) (![⟨526867, by decide⟩,⟨526892, by decide⟩,⟨526912, by decide⟩,⟨526917, by decide⟩]) unmarked_context_12_74036_526918 node_context_12_74036_526918
  intro a
  fin_cases a
  · exact context_13_296144_526867
  · exact context_13_296145_526892
  · exact context_13_296146_526912
  · exact context_13_296147_526917

theorem selected_cut_20544 : selected 8 ⟨526932, by decide⟩
    (prefixPartial 13 296148) = some ⟨13, 2, 0, 526932, 296148, 929, 16384⟩ := by
  decide +kernel

theorem context_13_296148_526932 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296148 ⟨526932, by decide⟩ :=
  accepted_of_selected 13 296148 ⟨526932, by decide⟩ ⟨13, 2, 0, 526932, 296148, 929, 16384⟩
    (by decide) selected_cut_20544

theorem selected_cut_20545 : selected 8 ⟨526964, by decide⟩
    (prefixPartial 13 296149) = some ⟨13, 2, 0, 526964, 296149, 2997, 16384⟩ := by
  decide +kernel

theorem context_13_296149_526964 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296149 ⟨526964, by decide⟩ :=
  accepted_of_selected 13 296149 ⟨526964, by decide⟩ ⟨13, 2, 0, 526964, 296149, 2997, 16384⟩
    (by decide) selected_cut_20545

theorem selected_cut_20546 : selected 8 ⟨527002, by decide⟩
    (prefixPartial 13 296150) = some ⟨13, 2, 0, 527002, 296150, 2625, 16384⟩ := by
  decide +kernel

theorem context_13_296150_527002 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296150 ⟨527002, by decide⟩ :=
  accepted_of_selected 13 296150 ⟨527002, by decide⟩ ⟨13, 2, 0, 527002, 296150, 2625, 16384⟩
    (by decide) selected_cut_20546

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
