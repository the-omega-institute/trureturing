/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover170
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_16419 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 112944) = some ⟨13, 1, 0, 3444, 112944, 1, 16384⟩ := by
  decide +kernel

theorem context_13_112944_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112944 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 112944 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 112944, 1, 16384⟩
    (by decide) selected_cut_16419

theorem selected_cut_16420 : selected 8 ⟨417682, by decide⟩
    (prefixPartial 13 112945) = some ⟨13, 2, 0, 417682, 112945, 1965, 16384⟩ := by
  decide +kernel

theorem context_13_112945_417682 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112945 ⟨417682, by decide⟩ :=
  accepted_of_selected 13 112945 ⟨417682, by decide⟩ ⟨13, 2, 0, 417682, 112945, 1965, 16384⟩
    (by decide) selected_cut_16420

theorem selected_cut_16421 : selected 8 ⟨417700, by decide⟩
    (prefixPartial 13 112946) = some ⟨13, 2, 0, 417700, 112946, 1489, 16384⟩ := by
  decide +kernel

theorem context_13_112946_417700 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112946 ⟨417700, by decide⟩ :=
  accepted_of_selected 13 112946 ⟨417700, by decide⟩ ⟨13, 2, 0, 417700, 112946, 1489, 16384⟩
    (by decide) selected_cut_16421

theorem selected_cut_16422 : selected 8 ⟨417709, by decide⟩
    (prefixPartial 13 112947) = some ⟨13, 2, 0, 417709, 112947, 837, 16384⟩ := by
  decide +kernel

theorem context_13_112947_417709 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112947 ⟨417709, by decide⟩ :=
  accepted_of_selected 13 112947 ⟨417709, by decide⟩ ⟨13, 2, 0, 417709, 112947, 837, 16384⟩
    (by decide) selected_cut_16422

theorem unmarked_context_12_28236_417710 : frontier 9 ⟨417710, by decide⟩
    (prefixCache 12 28236) (prefixPartial 12 28236) = false := by
  decide +kernel

theorem node_context_12_28236_417710 : EJMOriginalGlobalDAGData.nodes 9 ⟨417710, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨417682, by decide⟩,⟨417700, by decide⟩,⟨417709, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28236_417710 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28236 ⟨417710, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28236
    ⟨417710, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨417682, by decide⟩,⟨417700, by decide⟩,⟨417709, by decide⟩]) unmarked_context_12_28236_417710 node_context_12_28236_417710
  intro a
  fin_cases a
  · exact context_13_112944_3444
  · exact context_13_112945_417682
  · exact context_13_112946_417700
  · exact context_13_112947_417709

theorem selected_cut_16423 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 112948) = some ⟨13, 1, 0, 3444, 112948, 1, 16384⟩ := by
  decide +kernel

theorem context_13_112948_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112948 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 112948 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 112948, 1, 16384⟩
    (by decide) selected_cut_16423

theorem selected_cut_16424 : selected 8 ⟨417776, by decide⟩
    (prefixPartial 13 112949) = some ⟨13, 2, 0, 417776, 112949, 2833, 16384⟩ := by
  decide +kernel

theorem context_13_112949_417776 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112949 ⟨417776, by decide⟩ :=
  accepted_of_selected 13 112949 ⟨417776, by decide⟩ ⟨13, 2, 0, 417776, 112949, 2833, 16384⟩
    (by decide) selected_cut_16424

theorem selected_cut_16425 : selected 8 ⟨417808, by decide⟩
    (prefixPartial 13 112950) = some ⟨13, 2, 0, 417808, 112950, 2285, 16384⟩ := by
  decide +kernel

theorem context_13_112950_417808 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112950 ⟨417808, by decide⟩ :=
  accepted_of_selected 13 112950 ⟨417808, by decide⟩ ⟨13, 2, 0, 417808, 112950, 2285, 16384⟩
    (by decide) selected_cut_16425

theorem selected_cut_16426 : selected 8 ⟨417825, by decide⟩
    (prefixPartial 13 112951) = some ⟨13, 2, 0, 417825, 112951, 1201, 16384⟩ := by
  decide +kernel

theorem context_13_112951_417825 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112951 ⟨417825, by decide⟩ :=
  accepted_of_selected 13 112951 ⟨417825, by decide⟩ ⟨13, 2, 0, 417825, 112951, 1201, 16384⟩
    (by decide) selected_cut_16426

theorem unmarked_context_12_28237_417826 : frontier 9 ⟨417826, by decide⟩
    (prefixCache 12 28237) (prefixPartial 12 28237) = false := by
  decide +kernel

theorem node_context_12_28237_417826 : EJMOriginalGlobalDAGData.nodes 9 ⟨417826, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨417776, by decide⟩,⟨417808, by decide⟩,⟨417825, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28237_417826 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28237 ⟨417826, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28237
    ⟨417826, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨417776, by decide⟩,⟨417808, by decide⟩,⟨417825, by decide⟩]) unmarked_context_12_28237_417826 node_context_12_28237_417826
  intro a
  fin_cases a
  · exact context_13_112948_3444
  · exact context_13_112949_417776
  · exact context_13_112950_417808
  · exact context_13_112951_417825

theorem selected_cut_16427 : selected 9 ⟨417878, by decide⟩
    (prefixPartial 12 28238) = some ⟨12, 2, 0, 417878, 28238, 3913, 65536⟩ := by
  decide +kernel

theorem context_12_28238_417878 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28238 ⟨417878, by decide⟩ :=
  accepted_of_selected 12 28238 ⟨417878, by decide⟩ ⟨12, 2, 0, 417878, 28238, 3913, 65536⟩
    (by decide) selected_cut_16427

theorem selected_cut_16428 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 112956) = some ⟨13, 1, 0, 3444, 112956, 1, 16384⟩ := by
  decide +kernel

theorem context_13_112956_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112956 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 112956 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 112956, 1, 16384⟩
    (by decide) selected_cut_16428

theorem selected_cut_16429 : selected 8 ⟨417901, by decide⟩
    (prefixPartial 13 112957) = some ⟨13, 2, 0, 417901, 112957, 1925, 16384⟩ := by
  decide +kernel

theorem context_13_112957_417901 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112957 ⟨417901, by decide⟩ :=
  accepted_of_selected 13 112957 ⟨417901, by decide⟩ ⟨13, 2, 0, 417901, 112957, 1925, 16384⟩
    (by decide) selected_cut_16429

theorem selected_cut_16430 : selected 8 ⟨417921, by decide⟩
    (prefixPartial 13 112958) = some ⟨13, 2, 0, 417921, 112958, 1641, 16384⟩ := by
  decide +kernel

theorem context_13_112958_417921 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112958 ⟨417921, by decide⟩ :=
  accepted_of_selected 13 112958 ⟨417921, by decide⟩ ⟨13, 2, 0, 417921, 112958, 1641, 16384⟩
    (by decide) selected_cut_16430

theorem selected_cut_16431 : selected 8 ⟨417933, by decide⟩
    (prefixPartial 13 112959) = some ⟨13, 2, 0, 417933, 112959, 1013, 16384⟩ := by
  decide +kernel

theorem context_13_112959_417933 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112959 ⟨417933, by decide⟩ :=
  accepted_of_selected 13 112959 ⟨417933, by decide⟩ ⟨13, 2, 0, 417933, 112959, 1013, 16384⟩
    (by decide) selected_cut_16431

theorem unmarked_context_12_28239_417934 : frontier 9 ⟨417934, by decide⟩
    (prefixCache 12 28239) (prefixPartial 12 28239) = false := by
  decide +kernel

theorem node_context_12_28239_417934 : EJMOriginalGlobalDAGData.nodes 9 ⟨417934, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨417901, by decide⟩,⟨417921, by decide⟩,⟨417933, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28239_417934 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28239 ⟨417934, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28239
    ⟨417934, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨417901, by decide⟩,⟨417921, by decide⟩,⟨417933, by decide⟩]) unmarked_context_12_28239_417934 node_context_12_28239_417934
  intro a
  fin_cases a
  · exact context_13_112956_3444
  · exact context_13_112957_417901
  · exact context_13_112958_417921
  · exact context_13_112959_417933

theorem unmarked_context_11_7059_417935 : frontier 10 ⟨417935, by decide⟩
    (prefixCache 11 7059) (prefixPartial 11 7059) = false := by
  decide +kernel

theorem node_context_11_7059_417935 : EJMOriginalGlobalDAGData.nodes 10 ⟨417935, by decide⟩ =
    .split (coordinate 11) (![⟨417710, by decide⟩,⟨417826, by decide⟩,⟨417878, by decide⟩,⟨417934, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_7059_417935 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7059 ⟨417935, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 7059
    ⟨417935, by decide⟩ (by decide) (![⟨417710, by decide⟩,⟨417826, by decide⟩,⟨417878, by decide⟩,⟨417934, by decide⟩]) unmarked_context_11_7059_417935 node_context_11_7059_417935
  intro a
  fin_cases a
  · exact context_12_28236_417710
  · exact context_12_28237_417826
  · exact context_12_28238_417878
  · exact context_12_28239_417934

theorem unmarked_context_10_1764_417936 : frontier 11 ⟨417936, by decide⟩
    (prefixCache 10 1764) (prefixPartial 10 1764) = false := by
  decide +kernel

theorem node_context_10_1764_417936 : EJMOriginalGlobalDAGData.nodes 11 ⟨417936, by decide⟩ =
    .split (coordinate 10) (![⟨417020, by decide⟩,⟨417263, by decide⟩,⟨417635, by decide⟩,⟨417935, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1764_417936 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1764 ⟨417936, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1764
    ⟨417936, by decide⟩ (by decide) (![⟨417020, by decide⟩,⟨417263, by decide⟩,⟨417635, by decide⟩,⟨417935, by decide⟩]) unmarked_context_10_1764_417936 node_context_10_1764_417936
  intro a
  fin_cases a
  · exact context_11_7056_417020
  · exact context_11_7057_417263
  · exact context_11_7058_417635
  · exact context_11_7059_417935

theorem selected_cut_16432 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 112960) = some ⟨13, 1, 0, 3444, 112960, 1, 16384⟩ := by
  decide +kernel

theorem context_13_112960_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112960 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 112960 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 112960, 1, 16384⟩
    (by decide) selected_cut_16432

theorem selected_cut_16433 : selected 8 ⟨417960, by decide⟩
    (prefixPartial 13 112961) = some ⟨13, 2, 0, 417960, 112961, 1913, 16384⟩ := by
  decide +kernel

theorem context_13_112961_417960 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112961 ⟨417960, by decide⟩ :=
  accepted_of_selected 13 112961 ⟨417960, by decide⟩ ⟨13, 2, 0, 417960, 112961, 1913, 16384⟩
    (by decide) selected_cut_16433

theorem selected_cut_16434 : selected 8 ⟨417979, by decide⟩
    (prefixPartial 13 112962) = some ⟨13, 2, 0, 417979, 112962, 1509, 16384⟩ := by
  decide +kernel

theorem context_13_112962_417979 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112962 ⟨417979, by decide⟩ :=
  accepted_of_selected 13 112962 ⟨417979, by decide⟩ ⟨13, 2, 0, 417979, 112962, 1509, 16384⟩
    (by decide) selected_cut_16434

theorem selected_cut_16435 : selected 8 ⟨417984, by decide⟩
    (prefixPartial 13 112963) = some ⟨13, 2, 0, 417984, 112963, 777, 16384⟩ := by
  decide +kernel

theorem context_13_112963_417984 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112963 ⟨417984, by decide⟩ :=
  accepted_of_selected 13 112963 ⟨417984, by decide⟩ ⟨13, 2, 0, 417984, 112963, 777, 16384⟩
    (by decide) selected_cut_16435

theorem unmarked_context_12_28240_417985 : frontier 9 ⟨417985, by decide⟩
    (prefixCache 12 28240) (prefixPartial 12 28240) = false := by
  decide +kernel

theorem node_context_12_28240_417985 : EJMOriginalGlobalDAGData.nodes 9 ⟨417985, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨417960, by decide⟩,⟨417979, by decide⟩,⟨417984, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28240_417985 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28240 ⟨417985, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28240
    ⟨417985, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨417960, by decide⟩,⟨417979, by decide⟩,⟨417984, by decide⟩]) unmarked_context_12_28240_417985 node_context_12_28240_417985
  intro a
  fin_cases a
  · exact context_13_112960_3444
  · exact context_13_112961_417960
  · exact context_13_112962_417979
  · exact context_13_112963_417984

theorem selected_cut_16436 : selected 9 ⟨170504, by decide⟩
    (prefixPartial 12 28241) = some ⟨12, 1, 0, 170504, 28241, 1, 65536⟩ := by
  decide +kernel

theorem context_12_28241_170504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28241 ⟨170504, by decide⟩ :=
  accepted_of_selected 12 28241 ⟨170504, by decide⟩ ⟨12, 1, 0, 170504, 28241, 1, 65536⟩
    (by decide) selected_cut_16436

theorem selected_cut_16437 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 112968) = some ⟨13, 1, 0, 3444, 112968, 1, 16384⟩ := by
  decide +kernel

theorem context_13_112968_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112968 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 112968 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 112968, 1, 16384⟩
    (by decide) selected_cut_16437

theorem selected_cut_16438 : selected 8 ⟨418014, by decide⟩
    (prefixPartial 13 112969) = some ⟨13, 2, 0, 418014, 112969, 1877, 16384⟩ := by
  decide +kernel

theorem context_13_112969_418014 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112969 ⟨418014, by decide⟩ :=
  accepted_of_selected 13 112969 ⟨418014, by decide⟩ ⟨13, 2, 0, 418014, 112969, 1877, 16384⟩
    (by decide) selected_cut_16438

theorem selected_cut_16439 : selected 8 ⟨418033, by decide⟩
    (prefixPartial 13 112970) = some ⟨13, 2, 0, 418033, 112970, 1633, 16384⟩ := by
  decide +kernel

theorem context_13_112970_418033 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112970 ⟨418033, by decide⟩ :=
  accepted_of_selected 13 112970 ⟨418033, by decide⟩ ⟨13, 2, 0, 418033, 112970, 1633, 16384⟩
    (by decide) selected_cut_16439

theorem selected_cut_16440 : selected 8 ⟨418043, by decide⟩
    (prefixPartial 13 112971) = some ⟨13, 2, 0, 418043, 112971, 969, 16384⟩ := by
  decide +kernel

theorem context_13_112971_418043 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112971 ⟨418043, by decide⟩ :=
  accepted_of_selected 13 112971 ⟨418043, by decide⟩ ⟨13, 2, 0, 418043, 112971, 969, 16384⟩
    (by decide) selected_cut_16440

theorem unmarked_context_12_28242_418044 : frontier 9 ⟨418044, by decide⟩
    (prefixCache 12 28242) (prefixPartial 12 28242) = false := by
  decide +kernel

theorem node_context_12_28242_418044 : EJMOriginalGlobalDAGData.nodes 9 ⟨418044, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨418014, by decide⟩,⟨418033, by decide⟩,⟨418043, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28242_418044 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28242 ⟨418044, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28242
    ⟨418044, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨418014, by decide⟩,⟨418033, by decide⟩,⟨418043, by decide⟩]) unmarked_context_12_28242_418044 node_context_12_28242_418044
  intro a
  fin_cases a
  · exact context_13_112968_3444
  · exact context_13_112969_418014
  · exact context_13_112970_418033
  · exact context_13_112971_418043

theorem selected_cut_16441 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 112972) = some ⟨13, 1, 0, 3444, 112972, 1, 16384⟩ := by
  decide +kernel

theorem context_13_112972_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112972 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 112972 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 112972, 1, 16384⟩
    (by decide) selected_cut_16441

theorem selected_cut_16442 : selected 8 ⟨418098, by decide⟩
    (prefixPartial 13 112973) = some ⟨13, 2, 0, 418098, 112973, 2537, 16384⟩ := by
  decide +kernel

theorem context_13_112973_418098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112973 ⟨418098, by decide⟩ :=
  accepted_of_selected 13 112973 ⟨418098, by decide⟩ ⟨13, 2, 0, 418098, 112973, 2537, 16384⟩
    (by decide) selected_cut_16442

theorem selected_cut_16443 : selected 8 ⟨418128, by decide⟩
    (prefixPartial 13 112974) = some ⟨13, 2, 0, 418128, 112974, 2121, 16384⟩ := by
  decide +kernel

theorem context_13_112974_418128 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112974 ⟨418128, by decide⟩ :=
  accepted_of_selected 13 112974 ⟨418128, by decide⟩ ⟨13, 2, 0, 418128, 112974, 2121, 16384⟩
    (by decide) selected_cut_16443

theorem selected_cut_16444 : selected 8 ⟨418139, by decide⟩
    (prefixPartial 13 112975) = some ⟨13, 2, 0, 418139, 112975, 1097, 16384⟩ := by
  decide +kernel

theorem context_13_112975_418139 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112975 ⟨418139, by decide⟩ :=
  accepted_of_selected 13 112975 ⟨418139, by decide⟩ ⟨13, 2, 0, 418139, 112975, 1097, 16384⟩
    (by decide) selected_cut_16444

theorem unmarked_context_12_28243_418140 : frontier 9 ⟨418140, by decide⟩
    (prefixCache 12 28243) (prefixPartial 12 28243) = false := by
  decide +kernel

theorem node_context_12_28243_418140 : EJMOriginalGlobalDAGData.nodes 9 ⟨418140, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨418098, by decide⟩,⟨418128, by decide⟩,⟨418139, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28243_418140 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28243 ⟨418140, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28243
    ⟨418140, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨418098, by decide⟩,⟨418128, by decide⟩,⟨418139, by decide⟩]) unmarked_context_12_28243_418140 node_context_12_28243_418140
  intro a
  fin_cases a
  · exact context_13_112972_3444
  · exact context_13_112973_418098
  · exact context_13_112974_418128
  · exact context_13_112975_418139

theorem unmarked_context_11_7060_418141 : frontier 10 ⟨418141, by decide⟩
    (prefixCache 11 7060) (prefixPartial 11 7060) = false := by
  decide +kernel

theorem node_context_11_7060_418141 : EJMOriginalGlobalDAGData.nodes 10 ⟨418141, by decide⟩ =
    .split (coordinate 11) (![⟨417985, by decide⟩,⟨170504, by decide⟩,⟨418044, by decide⟩,⟨418140, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_7060_418141 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7060 ⟨418141, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 7060
    ⟨418141, by decide⟩ (by decide) (![⟨417985, by decide⟩,⟨170504, by decide⟩,⟨418044, by decide⟩,⟨418140, by decide⟩]) unmarked_context_11_7060_418141 node_context_11_7060_418141
  intro a
  fin_cases a
  · exact context_12_28240_417985
  · exact context_12_28241_170504
  · exact context_12_28242_418044
  · exact context_12_28243_418140

theorem selected_cut_16445 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 112976) = some ⟨13, 1, 0, 3444, 112976, 1, 16384⟩ := by
  decide +kernel

theorem context_13_112976_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112976 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 112976 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 112976, 1, 16384⟩
    (by decide) selected_cut_16445

theorem selected_cut_16446 : selected 8 ⟨418166, by decide⟩
    (prefixPartial 13 112977) = some ⟨13, 2, 0, 418166, 112977, 1753, 16384⟩ := by
  decide +kernel

theorem context_13_112977_418166 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112977 ⟨418166, by decide⟩ :=
  accepted_of_selected 13 112977 ⟨418166, by decide⟩ ⟨13, 2, 0, 418166, 112977, 1753, 16384⟩
    (by decide) selected_cut_16446

theorem selected_cut_16447 : selected 8 ⟨418185, by decide⟩
    (prefixPartial 13 112978) = some ⟨13, 2, 0, 418185, 112978, 1677, 16384⟩ := by
  decide +kernel

theorem context_13_112978_418185 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112978 ⟨418185, by decide⟩ :=
  accepted_of_selected 13 112978 ⟨418185, by decide⟩ ⟨13, 2, 0, 418185, 112978, 1677, 16384⟩
    (by decide) selected_cut_16447

theorem selected_cut_16448 : selected 8 ⟨418192, by decide⟩
    (prefixPartial 13 112979) = some ⟨13, 2, 0, 418192, 112979, 689, 16384⟩ := by
  decide +kernel

theorem context_13_112979_418192 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112979 ⟨418192, by decide⟩ :=
  accepted_of_selected 13 112979 ⟨418192, by decide⟩ ⟨13, 2, 0, 418192, 112979, 689, 16384⟩
    (by decide) selected_cut_16448

theorem unmarked_context_12_28244_418193 : frontier 9 ⟨418193, by decide⟩
    (prefixCache 12 28244) (prefixPartial 12 28244) = false := by
  decide +kernel

theorem node_context_12_28244_418193 : EJMOriginalGlobalDAGData.nodes 9 ⟨418193, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨418166, by decide⟩,⟨418185, by decide⟩,⟨418192, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28244_418193 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28244 ⟨418193, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28244
    ⟨418193, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨418166, by decide⟩,⟨418185, by decide⟩,⟨418192, by decide⟩]) unmarked_context_12_28244_418193 node_context_12_28244_418193
  intro a
  fin_cases a
  · exact context_13_112976_3444
  · exact context_13_112977_418166
  · exact context_13_112978_418185
  · exact context_13_112979_418192

theorem selected_cut_16449 : selected 9 ⟨170504, by decide⟩
    (prefixPartial 12 28245) = some ⟨12, 1, 0, 170504, 28245, 1, 65536⟩ := by
  decide +kernel

theorem context_12_28245_170504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28245 ⟨170504, by decide⟩ :=
  accepted_of_selected 12 28245 ⟨170504, by decide⟩ ⟨12, 1, 0, 170504, 28245, 1, 65536⟩
    (by decide) selected_cut_16449

theorem selected_cut_16450 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 112984) = some ⟨13, 1, 0, 3444, 112984, 1, 16384⟩ := by
  decide +kernel

theorem context_13_112984_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112984 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 112984 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 112984, 1, 16384⟩
    (by decide) selected_cut_16450

theorem selected_cut_16451 : selected 8 ⟨418213, by decide⟩
    (prefixPartial 13 112985) = some ⟨13, 2, 0, 418213, 112985, 1617, 16384⟩ := by
  decide +kernel

theorem context_13_112985_418213 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112985 ⟨418213, by decide⟩ :=
  accepted_of_selected 13 112985 ⟨418213, by decide⟩ ⟨13, 2, 0, 418213, 112985, 1617, 16384⟩
    (by decide) selected_cut_16451

theorem selected_cut_16452 : selected 8 ⟨418229, by decide⟩
    (prefixPartial 13 112986) = some ⟨13, 2, 0, 418229, 112986, 1833, 16384⟩ := by
  decide +kernel

theorem context_13_112986_418229 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112986 ⟨418229, by decide⟩ :=
  accepted_of_selected 13 112986 ⟨418229, by decide⟩ ⟨13, 2, 0, 418229, 112986, 1833, 16384⟩
    (by decide) selected_cut_16452

theorem selected_cut_16453 : selected 8 ⟨418236, by decide⟩
    (prefixPartial 13 112987) = some ⟨13, 2, 0, 418236, 112987, 813, 16384⟩ := by
  decide +kernel

theorem context_13_112987_418236 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112987 ⟨418236, by decide⟩ :=
  accepted_of_selected 13 112987 ⟨418236, by decide⟩ ⟨13, 2, 0, 418236, 112987, 813, 16384⟩
    (by decide) selected_cut_16453

theorem unmarked_context_12_28246_418237 : frontier 9 ⟨418237, by decide⟩
    (prefixCache 12 28246) (prefixPartial 12 28246) = false := by
  decide +kernel

theorem node_context_12_28246_418237 : EJMOriginalGlobalDAGData.nodes 9 ⟨418237, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨418213, by decide⟩,⟨418229, by decide⟩,⟨418236, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28246_418237 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28246 ⟨418237, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28246
    ⟨418237, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨418213, by decide⟩,⟨418229, by decide⟩,⟨418236, by decide⟩]) unmarked_context_12_28246_418237 node_context_12_28246_418237
  intro a
  fin_cases a
  · exact context_13_112984_3444
  · exact context_13_112985_418213
  · exact context_13_112986_418229
  · exact context_13_112987_418236

theorem selected_cut_16454 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 112988) = some ⟨13, 1, 0, 3444, 112988, 1, 16384⟩ := by
  decide +kernel

theorem context_13_112988_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112988 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 112988 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 112988, 1, 16384⟩
    (by decide) selected_cut_16454

theorem selected_cut_16455 : selected 8 ⟨418268, by decide⟩
    (prefixPartial 13 112989) = some ⟨13, 2, 0, 418268, 112989, 2009, 16384⟩ := by
  decide +kernel

theorem context_13_112989_418268 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112989 ⟨418268, by decide⟩ :=
  accepted_of_selected 13 112989 ⟨418268, by decide⟩ ⟨13, 2, 0, 418268, 112989, 2009, 16384⟩
    (by decide) selected_cut_16455

theorem selected_cut_16456 : selected 8 ⟨418290, by decide⟩
    (prefixPartial 13 112990) = some ⟨13, 2, 0, 418290, 112990, 2229, 16384⟩ := by
  decide +kernel

theorem context_13_112990_418290 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112990 ⟨418290, by decide⟩ :=
  accepted_of_selected 13 112990 ⟨418290, by decide⟩ ⟨13, 2, 0, 418290, 112990, 2229, 16384⟩
    (by decide) selected_cut_16456

theorem selected_cut_16457 : selected 8 ⟨418299, by decide⟩
    (prefixPartial 13 112991) = some ⟨13, 2, 0, 418299, 112991, 973, 16384⟩ := by
  decide +kernel

theorem context_13_112991_418299 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112991 ⟨418299, by decide⟩ :=
  accepted_of_selected 13 112991 ⟨418299, by decide⟩ ⟨13, 2, 0, 418299, 112991, 973, 16384⟩
    (by decide) selected_cut_16457

theorem unmarked_context_12_28247_418300 : frontier 9 ⟨418300, by decide⟩
    (prefixCache 12 28247) (prefixPartial 12 28247) = false := by
  decide +kernel

theorem node_context_12_28247_418300 : EJMOriginalGlobalDAGData.nodes 9 ⟨418300, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨418268, by decide⟩,⟨418290, by decide⟩,⟨418299, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28247_418300 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28247 ⟨418300, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28247
    ⟨418300, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨418268, by decide⟩,⟨418290, by decide⟩,⟨418299, by decide⟩]) unmarked_context_12_28247_418300 node_context_12_28247_418300
  intro a
  fin_cases a
  · exact context_13_112988_3444
  · exact context_13_112989_418268
  · exact context_13_112990_418290
  · exact context_13_112991_418299

theorem unmarked_context_11_7061_418301 : frontier 10 ⟨418301, by decide⟩
    (prefixCache 11 7061) (prefixPartial 11 7061) = false := by
  decide +kernel

theorem node_context_11_7061_418301 : EJMOriginalGlobalDAGData.nodes 10 ⟨418301, by decide⟩ =
    .split (coordinate 11) (![⟨418193, by decide⟩,⟨170504, by decide⟩,⟨418237, by decide⟩,⟨418300, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_7061_418301 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7061 ⟨418301, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 7061
    ⟨418301, by decide⟩ (by decide) (![⟨418193, by decide⟩,⟨170504, by decide⟩,⟨418237, by decide⟩,⟨418300, by decide⟩]) unmarked_context_11_7061_418301 node_context_11_7061_418301
  intro a
  fin_cases a
  · exact context_12_28244_418193
  · exact context_12_28245_170504
  · exact context_12_28246_418237
  · exact context_12_28247_418300

theorem selected_cut_16458 : selected 9 ⟨418347, by decide⟩
    (prefixPartial 12 28248) = some ⟨12, 2, 0, 418347, 28248, 3297, 65536⟩ := by
  decide +kernel

theorem context_12_28248_418347 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28248 ⟨418347, by decide⟩ :=
  accepted_of_selected 12 28248 ⟨418347, by decide⟩ ⟨12, 2, 0, 418347, 28248, 3297, 65536⟩
    (by decide) selected_cut_16458

theorem selected_cut_16459 : selected 9 ⟨126371, by decide⟩
    (prefixPartial 12 28249) = some ⟨12, 1, 0, 126371, 28249, 1, 65536⟩ := by
  decide +kernel

theorem context_12_28249_126371 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28249 ⟨126371, by decide⟩ :=
  accepted_of_selected 12 28249 ⟨126371, by decide⟩ ⟨12, 1, 0, 126371, 28249, 1, 65536⟩
    (by decide) selected_cut_16459

theorem selected_cut_16460 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 113000) = some ⟨13, 1, 0, 3444, 113000, 1, 16384⟩ := by
  decide +kernel

theorem context_13_113000_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113000 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 113000 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 113000, 1, 16384⟩
    (by decide) selected_cut_16460

theorem selected_cut_16461 : selected 8 ⟨418388, by decide⟩
    (prefixPartial 13 113001) = some ⟨13, 2, 0, 418388, 113001, 2161, 16384⟩ := by
  decide +kernel

theorem context_13_113001_418388 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113001 ⟨418388, by decide⟩ :=
  accepted_of_selected 13 113001 ⟨418388, by decide⟩ ⟨13, 2, 0, 418388, 113001, 2161, 16384⟩
    (by decide) selected_cut_16461

theorem selected_cut_16462 : selected 8 ⟨418427, by decide⟩
    (prefixPartial 13 113002) = some ⟨13, 2, 0, 418427, 113002, 2481, 16384⟩ := by
  decide +kernel

theorem context_13_113002_418427 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113002 ⟨418427, by decide⟩ :=
  accepted_of_selected 13 113002 ⟨418427, by decide⟩ ⟨13, 2, 0, 418427, 113002, 2481, 16384⟩
    (by decide) selected_cut_16462

theorem selected_cut_16463 : selected 8 ⟨418433, by decide⟩
    (prefixPartial 13 113003) = some ⟨13, 2, 0, 418433, 113003, 1149, 16384⟩ := by
  decide +kernel

theorem context_13_113003_418433 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113003 ⟨418433, by decide⟩ :=
  accepted_of_selected 13 113003 ⟨418433, by decide⟩ ⟨13, 2, 0, 418433, 113003, 1149, 16384⟩
    (by decide) selected_cut_16463

theorem unmarked_context_12_28250_418434 : frontier 9 ⟨418434, by decide⟩
    (prefixCache 12 28250) (prefixPartial 12 28250) = false := by
  decide +kernel

theorem node_context_12_28250_418434 : EJMOriginalGlobalDAGData.nodes 9 ⟨418434, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨418388, by decide⟩,⟨418427, by decide⟩,⟨418433, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28250_418434 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28250 ⟨418434, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28250
    ⟨418434, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨418388, by decide⟩,⟨418427, by decide⟩,⟨418433, by decide⟩]) unmarked_context_12_28250_418434 node_context_12_28250_418434
  intro a
  fin_cases a
  · exact context_13_113000_3444
  · exact context_13_113001_418388
  · exact context_13_113002_418427
  · exact context_13_113003_418433

theorem selected_cut_16464 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 113004) = some ⟨13, 1, 0, 3444, 113004, 1, 16384⟩ := by
  decide +kernel

theorem context_13_113004_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113004 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 113004 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 113004, 1, 16384⟩
    (by decide) selected_cut_16464

theorem selected_cut_16465 : selected 8 ⟨418454, by decide⟩
    (prefixPartial 13 113005) = some ⟨13, 2, 0, 418454, 113005, 1549, 16384⟩ := by
  decide +kernel

theorem context_13_113005_418454 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113005 ⟨418454, by decide⟩ :=
  accepted_of_selected 13 113005 ⟨418454, by decide⟩ ⟨13, 2, 0, 418454, 113005, 1549, 16384⟩
    (by decide) selected_cut_16465

theorem selected_cut_16466 : selected 8 ⟨418480, by decide⟩
    (prefixPartial 13 113006) = some ⟨13, 2, 0, 418480, 113006, 1673, 16384⟩ := by
  decide +kernel

theorem context_13_113006_418480 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113006 ⟨418480, by decide⟩ :=
  accepted_of_selected 13 113006 ⟨418480, by decide⟩ ⟨13, 2, 0, 418480, 113006, 1673, 16384⟩
    (by decide) selected_cut_16466

theorem selected_cut_16467 : selected 8 ⟨418489, by decide⟩
    (prefixPartial 13 113007) = some ⟨13, 2, 0, 418489, 113007, 925, 16384⟩ := by
  decide +kernel

theorem context_13_113007_418489 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113007 ⟨418489, by decide⟩ :=
  accepted_of_selected 13 113007 ⟨418489, by decide⟩ ⟨13, 2, 0, 418489, 113007, 925, 16384⟩
    (by decide) selected_cut_16467

theorem unmarked_context_12_28251_418490 : frontier 9 ⟨418490, by decide⟩
    (prefixCache 12 28251) (prefixPartial 12 28251) = false := by
  decide +kernel

theorem node_context_12_28251_418490 : EJMOriginalGlobalDAGData.nodes 9 ⟨418490, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨418454, by decide⟩,⟨418480, by decide⟩,⟨418489, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28251_418490 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28251 ⟨418490, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28251
    ⟨418490, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨418454, by decide⟩,⟨418480, by decide⟩,⟨418489, by decide⟩]) unmarked_context_12_28251_418490 node_context_12_28251_418490
  intro a
  fin_cases a
  · exact context_13_113004_3444
  · exact context_13_113005_418454
  · exact context_13_113006_418480
  · exact context_13_113007_418489

theorem unmarked_context_11_7062_418491 : frontier 10 ⟨418491, by decide⟩
    (prefixCache 11 7062) (prefixPartial 11 7062) = false := by
  decide +kernel

theorem node_context_11_7062_418491 : EJMOriginalGlobalDAGData.nodes 10 ⟨418491, by decide⟩ =
    .split (coordinate 11) (![⟨418347, by decide⟩,⟨126371, by decide⟩,⟨418434, by decide⟩,⟨418490, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_7062_418491 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7062 ⟨418491, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 7062
    ⟨418491, by decide⟩ (by decide) (![⟨418347, by decide⟩,⟨126371, by decide⟩,⟨418434, by decide⟩,⟨418490, by decide⟩]) unmarked_context_11_7062_418491 node_context_11_7062_418491
  intro a
  fin_cases a
  · exact context_12_28248_418347
  · exact context_12_28249_126371
  · exact context_12_28250_418434
  · exact context_12_28251_418490

theorem selected_cut_16468 : selected 9 ⟨418530, by decide⟩
    (prefixPartial 12 28252) = some ⟨12, 2, 0, 418530, 28252, 3353, 65536⟩ := by
  decide +kernel

theorem context_12_28252_418530 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28252 ⟨418530, by decide⟩ :=
  accepted_of_selected 12 28252 ⟨418530, by decide⟩ ⟨12, 2, 0, 418530, 28252, 3353, 65536⟩
    (by decide) selected_cut_16468

theorem selected_cut_16469 : selected 9 ⟨418602, by decide⟩
    (prefixPartial 12 28253) = some ⟨12, 2, 0, 418602, 28253, 2429, 65536⟩ := by
  decide +kernel

theorem context_12_28253_418602 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28253 ⟨418602, by decide⟩ :=
  accepted_of_selected 12 28253 ⟨418602, by decide⟩ ⟨12, 2, 0, 418602, 28253, 2429, 65536⟩
    (by decide) selected_cut_16469

theorem selected_cut_16470 : selected 9 ⟨418644, by decide⟩
    (prefixPartial 12 28254) = some ⟨12, 2, 0, 418644, 28254, 3381, 65536⟩ := by
  decide +kernel

theorem context_12_28254_418644 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28254 ⟨418644, by decide⟩ :=
  accepted_of_selected 12 28254 ⟨418644, by decide⟩ ⟨12, 2, 0, 418644, 28254, 3381, 65536⟩
    (by decide) selected_cut_16470

theorem selected_cut_16471 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 113020) = some ⟨13, 1, 0, 3444, 113020, 1, 16384⟩ := by
  decide +kernel

theorem context_13_113020_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113020 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 113020 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 113020, 1, 16384⟩
    (by decide) selected_cut_16471

theorem selected_cut_16472 : selected 8 ⟨418663, by decide⟩
    (prefixPartial 13 113021) = some ⟨13, 2, 0, 418663, 113021, 1341, 16384⟩ := by
  decide +kernel

theorem context_13_113021_418663 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113021 ⟨418663, by decide⟩ :=
  accepted_of_selected 13 113021 ⟨418663, by decide⟩ ⟨13, 2, 0, 418663, 113021, 1341, 16384⟩
    (by decide) selected_cut_16472

theorem selected_cut_16473 : selected 8 ⟨418684, by decide⟩
    (prefixPartial 13 113022) = some ⟨13, 2, 0, 418684, 113022, 1825, 16384⟩ := by
  decide +kernel

theorem context_13_113022_418684 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113022 ⟨418684, by decide⟩ :=
  accepted_of_selected 13 113022 ⟨418684, by decide⟩ ⟨13, 2, 0, 418684, 113022, 1825, 16384⟩
    (by decide) selected_cut_16473

theorem selected_cut_16474 : selected 8 ⟨418694, by decide⟩
    (prefixPartial 13 113023) = some ⟨13, 2, 0, 418694, 113023, 965, 16384⟩ := by
  decide +kernel

theorem context_13_113023_418694 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113023 ⟨418694, by decide⟩ :=
  accepted_of_selected 13 113023 ⟨418694, by decide⟩ ⟨13, 2, 0, 418694, 113023, 965, 16384⟩
    (by decide) selected_cut_16474

theorem unmarked_context_12_28255_418695 : frontier 9 ⟨418695, by decide⟩
    (prefixCache 12 28255) (prefixPartial 12 28255) = false := by
  decide +kernel

theorem node_context_12_28255_418695 : EJMOriginalGlobalDAGData.nodes 9 ⟨418695, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨418663, by decide⟩,⟨418684, by decide⟩,⟨418694, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28255_418695 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28255 ⟨418695, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28255
    ⟨418695, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨418663, by decide⟩,⟨418684, by decide⟩,⟨418694, by decide⟩]) unmarked_context_12_28255_418695 node_context_12_28255_418695
  intro a
  fin_cases a
  · exact context_13_113020_3444
  · exact context_13_113021_418663
  · exact context_13_113022_418684
  · exact context_13_113023_418694

theorem unmarked_context_11_7063_418696 : frontier 10 ⟨418696, by decide⟩
    (prefixCache 11 7063) (prefixPartial 11 7063) = false := by
  decide +kernel

theorem node_context_11_7063_418696 : EJMOriginalGlobalDAGData.nodes 10 ⟨418696, by decide⟩ =
    .split (coordinate 11) (![⟨418530, by decide⟩,⟨418602, by decide⟩,⟨418644, by decide⟩,⟨418695, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_7063_418696 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7063 ⟨418696, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 7063
    ⟨418696, by decide⟩ (by decide) (![⟨418530, by decide⟩,⟨418602, by decide⟩,⟨418644, by decide⟩,⟨418695, by decide⟩]) unmarked_context_11_7063_418696 node_context_11_7063_418696
  intro a
  fin_cases a
  · exact context_12_28252_418530
  · exact context_12_28253_418602
  · exact context_12_28254_418644
  · exact context_12_28255_418695

theorem unmarked_context_10_1765_418697 : frontier 11 ⟨418697, by decide⟩
    (prefixCache 10 1765) (prefixPartial 10 1765) = false := by
  decide +kernel

theorem node_context_10_1765_418697 : EJMOriginalGlobalDAGData.nodes 11 ⟨418697, by decide⟩ =
    .split (coordinate 10) (![⟨418141, by decide⟩,⟨418301, by decide⟩,⟨418491, by decide⟩,⟨418696, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1765_418697 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1765 ⟨418697, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1765
    ⟨418697, by decide⟩ (by decide) (![⟨418141, by decide⟩,⟨418301, by decide⟩,⟨418491, by decide⟩,⟨418696, by decide⟩]) unmarked_context_10_1765_418697 node_context_10_1765_418697
  intro a
  fin_cases a
  · exact context_11_7060_418141
  · exact context_11_7061_418301
  · exact context_11_7062_418491
  · exact context_11_7063_418696

theorem selected_cut_16475 : selected 9 ⟨418740, by decide⟩
    (prefixPartial 12 28256) = some ⟨12, 2, 0, 418740, 28256, 3661, 65536⟩ := by
  decide +kernel

theorem context_12_28256_418740 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28256 ⟨418740, by decide⟩ :=
  accepted_of_selected 12 28256 ⟨418740, by decide⟩ ⟨12, 2, 0, 418740, 28256, 3661, 65536⟩
    (by decide) selected_cut_16475

theorem selected_cut_16476 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 113028) = some ⟨13, 1, 0, 3444, 113028, 1, 16384⟩ := by
  decide +kernel

theorem context_13_113028_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113028 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 113028 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 113028, 1, 16384⟩
    (by decide) selected_cut_16476

theorem selected_cut_16477 : selected 8 ⟨418811, by decide⟩
    (prefixPartial 13 113029) = some ⟨13, 2, 0, 418811, 113029, 2513, 16384⟩ := by
  decide +kernel

theorem context_13_113029_418811 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113029 ⟨418811, by decide⟩ :=
  accepted_of_selected 13 113029 ⟨418811, by decide⟩ ⟨13, 2, 0, 418811, 113029, 2513, 16384⟩
    (by decide) selected_cut_16477

theorem selected_cut_16478 : selected 8 ⟨418886, by decide⟩
    (prefixPartial 13 113030) = some ⟨13, 2, 0, 418886, 113030, 2849, 16384⟩ := by
  decide +kernel

theorem context_13_113030_418886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113030 ⟨418886, by decide⟩ :=
  accepted_of_selected 13 113030 ⟨418886, by decide⟩ ⟨13, 2, 0, 418886, 113030, 2849, 16384⟩
    (by decide) selected_cut_16478

theorem selected_cut_16479 : selected 8 ⟨418908, by decide⟩
    (prefixPartial 13 113031) = some ⟨13, 2, 0, 418908, 113031, 1241, 16384⟩ := by
  decide +kernel

theorem context_13_113031_418908 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113031 ⟨418908, by decide⟩ :=
  accepted_of_selected 13 113031 ⟨418908, by decide⟩ ⟨13, 2, 0, 418908, 113031, 1241, 16384⟩
    (by decide) selected_cut_16479

theorem unmarked_context_12_28257_418909 : frontier 9 ⟨418909, by decide⟩
    (prefixCache 12 28257) (prefixPartial 12 28257) = false := by
  decide +kernel

theorem node_context_12_28257_418909 : EJMOriginalGlobalDAGData.nodes 9 ⟨418909, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨418811, by decide⟩,⟨418886, by decide⟩,⟨418908, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28257_418909 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28257 ⟨418909, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28257
    ⟨418909, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨418811, by decide⟩,⟨418886, by decide⟩,⟨418908, by decide⟩]) unmarked_context_12_28257_418909 node_context_12_28257_418909
  intro a
  fin_cases a
  · exact context_13_113028_3444
  · exact context_13_113029_418811
  · exact context_13_113030_418886
  · exact context_13_113031_418908

theorem selected_cut_16480 : selected 9 ⟨418952, by decide⟩
    (prefixPartial 12 28258) = some ⟨12, 2, 0, 418952, 28258, 3625, 65536⟩ := by
  decide +kernel

theorem context_12_28258_418952 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28258 ⟨418952, by decide⟩ :=
  accepted_of_selected 12 28258 ⟨418952, by decide⟩ ⟨12, 2, 0, 418952, 28258, 3625, 65536⟩
    (by decide) selected_cut_16480

theorem selected_cut_16481 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 113036) = some ⟨13, 1, 0, 3444, 113036, 1, 16384⟩ := by
  decide +kernel

theorem context_13_113036_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113036 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 113036 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 113036, 1, 16384⟩
    (by decide) selected_cut_16481

theorem selected_cut_16482 : selected 8 ⟨418985, by decide⟩
    (prefixPartial 13 113037) = some ⟨13, 2, 0, 418985, 113037, 1685, 16384⟩ := by
  decide +kernel

theorem context_13_113037_418985 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113037 ⟨418985, by decide⟩ :=
  accepted_of_selected 13 113037 ⟨418985, by decide⟩ ⟨13, 2, 0, 418985, 113037, 1685, 16384⟩
    (by decide) selected_cut_16482

theorem selected_cut_16483 : selected 8 ⟨419018, by decide⟩
    (prefixPartial 13 113038) = some ⟨13, 2, 0, 419018, 113038, 1989, 16384⟩ := by
  decide +kernel

theorem context_13_113038_419018 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113038 ⟨419018, by decide⟩ :=
  accepted_of_selected 13 113038 ⟨419018, by decide⟩ ⟨13, 2, 0, 419018, 113038, 1989, 16384⟩
    (by decide) selected_cut_16483

theorem selected_cut_16484 : selected 8 ⟨419027, by decide⟩
    (prefixPartial 13 113039) = some ⟨13, 2, 0, 419027, 113039, 1013, 16384⟩ := by
  decide +kernel

theorem context_13_113039_419027 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113039 ⟨419027, by decide⟩ :=
  accepted_of_selected 13 113039 ⟨419027, by decide⟩ ⟨13, 2, 0, 419027, 113039, 1013, 16384⟩
    (by decide) selected_cut_16484

theorem unmarked_context_12_28259_419028 : frontier 9 ⟨419028, by decide⟩
    (prefixCache 12 28259) (prefixPartial 12 28259) = false := by
  decide +kernel

theorem node_context_12_28259_419028 : EJMOriginalGlobalDAGData.nodes 9 ⟨419028, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨418985, by decide⟩,⟨419018, by decide⟩,⟨419027, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28259_419028 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28259 ⟨419028, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28259
    ⟨419028, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨418985, by decide⟩,⟨419018, by decide⟩,⟨419027, by decide⟩]) unmarked_context_12_28259_419028 node_context_12_28259_419028
  intro a
  fin_cases a
  · exact context_13_113036_3444
  · exact context_13_113037_418985
  · exact context_13_113038_419018
  · exact context_13_113039_419027

theorem unmarked_context_11_7064_419029 : frontier 10 ⟨419029, by decide⟩
    (prefixCache 11 7064) (prefixPartial 11 7064) = false := by
  decide +kernel

theorem node_context_11_7064_419029 : EJMOriginalGlobalDAGData.nodes 10 ⟨419029, by decide⟩ =
    .split (coordinate 11) (![⟨418740, by decide⟩,⟨418909, by decide⟩,⟨418952, by decide⟩,⟨419028, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_7064_419029 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7064 ⟨419029, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 7064
    ⟨419029, by decide⟩ (by decide) (![⟨418740, by decide⟩,⟨418909, by decide⟩,⟨418952, by decide⟩,⟨419028, by decide⟩]) unmarked_context_11_7064_419029 node_context_11_7064_419029
  intro a
  fin_cases a
  · exact context_12_28256_418740
  · exact context_12_28257_418909
  · exact context_12_28258_418952
  · exact context_12_28259_419028

theorem selected_cut_16485 : selected 9 ⟨419072, by decide⟩
    (prefixPartial 12 28260) = some ⟨12, 2, 0, 419072, 28260, 3441, 65536⟩ := by
  decide +kernel

theorem context_12_28260_419072 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28260 ⟨419072, by decide⟩ :=
  accepted_of_selected 12 28260 ⟨419072, by decide⟩ ⟨12, 2, 0, 419072, 28260, 3441, 65536⟩
    (by decide) selected_cut_16485

theorem selected_cut_16486 : selected 9 ⟨289098, by decide⟩
    (prefixPartial 12 28261) = some ⟨12, 1, 0, 289098, 28261, 1, 65536⟩ := by
  decide +kernel

theorem context_12_28261_289098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28261 ⟨289098, by decide⟩ :=
  accepted_of_selected 12 28261 ⟨289098, by decide⟩ ⟨12, 1, 0, 289098, 28261, 1, 65536⟩
    (by decide) selected_cut_16486

theorem selected_cut_16487 : selected 9 ⟨419110, by decide⟩
    (prefixPartial 12 28262) = some ⟨12, 2, 0, 419110, 28262, 3393, 65536⟩ := by
  decide +kernel

theorem context_12_28262_419110 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28262 ⟨419110, by decide⟩ :=
  accepted_of_selected 12 28262 ⟨419110, by decide⟩ ⟨12, 2, 0, 419110, 28262, 3393, 65536⟩
    (by decide) selected_cut_16487

theorem selected_cut_16488 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 113052) = some ⟨13, 1, 0, 3444, 113052, 1, 16384⟩ := by
  decide +kernel

theorem context_13_113052_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113052 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 113052 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 113052, 1, 16384⟩
    (by decide) selected_cut_16488

theorem selected_cut_16489 : selected 8 ⟨419128, by decide⟩
    (prefixPartial 13 113053) = some ⟨13, 2, 0, 419128, 113053, 1221, 16384⟩ := by
  decide +kernel

theorem context_13_113053_419128 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113053 ⟨419128, by decide⟩ :=
  accepted_of_selected 13 113053 ⟨419128, by decide⟩ ⟨13, 2, 0, 419128, 113053, 1221, 16384⟩
    (by decide) selected_cut_16489

theorem selected_cut_16490 : selected 8 ⟨419158, by decide⟩
    (prefixPartial 13 113054) = some ⟨13, 2, 0, 419158, 113054, 2021, 16384⟩ := by
  decide +kernel

theorem context_13_113054_419158 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113054 ⟨419158, by decide⟩ :=
  accepted_of_selected 13 113054 ⟨419158, by decide⟩ ⟨13, 2, 0, 419158, 113054, 2021, 16384⟩
    (by decide) selected_cut_16490

theorem selected_cut_16491 : selected 8 ⟨419168, by decide⟩
    (prefixPartial 13 113055) = some ⟨13, 2, 0, 419168, 113055, 965, 16384⟩ := by
  decide +kernel

theorem context_13_113055_419168 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113055 ⟨419168, by decide⟩ :=
  accepted_of_selected 13 113055 ⟨419168, by decide⟩ ⟨13, 2, 0, 419168, 113055, 965, 16384⟩
    (by decide) selected_cut_16491

theorem unmarked_context_12_28263_419169 : frontier 9 ⟨419169, by decide⟩
    (prefixCache 12 28263) (prefixPartial 12 28263) = false := by
  decide +kernel

theorem node_context_12_28263_419169 : EJMOriginalGlobalDAGData.nodes 9 ⟨419169, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨419128, by decide⟩,⟨419158, by decide⟩,⟨419168, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28263_419169 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28263 ⟨419169, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28263
    ⟨419169, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨419128, by decide⟩,⟨419158, by decide⟩,⟨419168, by decide⟩]) unmarked_context_12_28263_419169 node_context_12_28263_419169
  intro a
  fin_cases a
  · exact context_13_113052_3444
  · exact context_13_113053_419128
  · exact context_13_113054_419158
  · exact context_13_113055_419168

theorem unmarked_context_11_7065_419170 : frontier 10 ⟨419170, by decide⟩
    (prefixCache 11 7065) (prefixPartial 11 7065) = false := by
  decide +kernel

theorem node_context_11_7065_419170 : EJMOriginalGlobalDAGData.nodes 10 ⟨419170, by decide⟩ =
    .split (coordinate 11) (![⟨419072, by decide⟩,⟨289098, by decide⟩,⟨419110, by decide⟩,⟨419169, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_7065_419170 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7065 ⟨419170, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 7065
    ⟨419170, by decide⟩ (by decide) (![⟨419072, by decide⟩,⟨289098, by decide⟩,⟨419110, by decide⟩,⟨419169, by decide⟩]) unmarked_context_11_7065_419170 node_context_11_7065_419170
  intro a
  fin_cases a
  · exact context_12_28260_419072
  · exact context_12_28261_289098
  · exact context_12_28262_419110
  · exact context_12_28263_419169

theorem selected_cut_16492 : selected 9 ⟨419209, by decide⟩
    (prefixPartial 12 28264) = some ⟨12, 2, 0, 419209, 28264, 2793, 65536⟩ := by
  decide +kernel

theorem context_12_28264_419209 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28264 ⟨419209, by decide⟩ :=
  accepted_of_selected 12 28264 ⟨419209, by decide⟩ ⟨12, 2, 0, 419209, 28264, 2793, 65536⟩
    (by decide) selected_cut_16492

theorem selected_cut_16493 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 113060) = some ⟨13, 1, 0, 3444, 113060, 1, 16384⟩ := by
  decide +kernel

theorem context_13_113060_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113060 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 113060 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 113060, 1, 16384⟩
    (by decide) selected_cut_16493

theorem selected_cut_16494 : selected 8 ⟨419243, by decide⟩
    (prefixPartial 13 113061) = some ⟨13, 2, 0, 419243, 113061, 1285, 16384⟩ := by
  decide +kernel

theorem context_13_113061_419243 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113061 ⟨419243, by decide⟩ :=
  accepted_of_selected 13 113061 ⟨419243, by decide⟩ ⟨13, 2, 0, 419243, 113061, 1285, 16384⟩
    (by decide) selected_cut_16494

theorem selected_cut_16495 : selected 8 ⟨419278, by decide⟩
    (prefixPartial 13 113062) = some ⟨13, 2, 0, 419278, 113062, 2249, 16384⟩ := by
  decide +kernel

theorem context_13_113062_419278 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113062 ⟨419278, by decide⟩ :=
  accepted_of_selected 13 113062 ⟨419278, by decide⟩ ⟨13, 2, 0, 419278, 113062, 2249, 16384⟩
    (by decide) selected_cut_16495

theorem selected_cut_16496 : selected 8 ⟨419290, by decide⟩
    (prefixPartial 13 113063) = some ⟨13, 2, 0, 419290, 113063, 1105, 16384⟩ := by
  decide +kernel

theorem context_13_113063_419290 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113063 ⟨419290, by decide⟩ :=
  accepted_of_selected 13 113063 ⟨419290, by decide⟩ ⟨13, 2, 0, 419290, 113063, 1105, 16384⟩
    (by decide) selected_cut_16496

theorem unmarked_context_12_28265_419291 : frontier 9 ⟨419291, by decide⟩
    (prefixCache 12 28265) (prefixPartial 12 28265) = false := by
  decide +kernel

theorem node_context_12_28265_419291 : EJMOriginalGlobalDAGData.nodes 9 ⟨419291, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨419243, by decide⟩,⟨419278, by decide⟩,⟨419290, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28265_419291 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28265 ⟨419291, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28265
    ⟨419291, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨419243, by decide⟩,⟨419278, by decide⟩,⟨419290, by decide⟩]) unmarked_context_12_28265_419291 node_context_12_28265_419291
  intro a
  fin_cases a
  · exact context_13_113060_3444
  · exact context_13_113061_419243
  · exact context_13_113062_419278
  · exact context_13_113063_419290

theorem selected_cut_16497 : selected 9 ⟨419292, by decide⟩
    (prefixPartial 12 28266) = some ⟨12, 1, 0, 419292, 28266, 1, 65536⟩ := by
  decide +kernel

theorem context_12_28266_419292 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28266 ⟨419292, by decide⟩ :=
  accepted_of_selected 12 28266 ⟨419292, by decide⟩ ⟨12, 1, 0, 419292, 28266, 1, 65536⟩
    (by decide) selected_cut_16497

theorem selected_cut_16498 : selected 9 ⟨419336, by decide⟩
    (prefixPartial 12 28267) = some ⟨12, 2, 0, 419336, 28267, 3289, 65536⟩ := by
  decide +kernel

theorem context_12_28267_419336 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28267 ⟨419336, by decide⟩ :=
  accepted_of_selected 12 28267 ⟨419336, by decide⟩ ⟨12, 2, 0, 419336, 28267, 3289, 65536⟩
    (by decide) selected_cut_16498

theorem unmarked_context_11_7066_419337 : frontier 10 ⟨419337, by decide⟩
    (prefixCache 11 7066) (prefixPartial 11 7066) = false := by
  decide +kernel

theorem node_context_11_7066_419337 : EJMOriginalGlobalDAGData.nodes 10 ⟨419337, by decide⟩ =
    .split (coordinate 11) (![⟨419209, by decide⟩,⟨419291, by decide⟩,⟨419292, by decide⟩,⟨419336, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_7066_419337 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7066 ⟨419337, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 7066
    ⟨419337, by decide⟩ (by decide) (![⟨419209, by decide⟩,⟨419291, by decide⟩,⟨419292, by decide⟩,⟨419336, by decide⟩]) unmarked_context_11_7066_419337 node_context_11_7066_419337
  intro a
  fin_cases a
  · exact context_12_28264_419209
  · exact context_12_28265_419291
  · exact context_12_28266_419292
  · exact context_12_28267_419336

theorem selected_cut_16499 : selected 9 ⟨419380, by decide⟩
    (prefixPartial 12 28268) = some ⟨12, 2, 0, 419380, 28268, 3241, 65536⟩ := by
  decide +kernel

theorem context_12_28268_419380 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28268 ⟨419380, by decide⟩ :=
  accepted_of_selected 12 28268 ⟨419380, by decide⟩ ⟨12, 2, 0, 419380, 28268, 3241, 65536⟩
    (by decide) selected_cut_16499

theorem selected_cut_16500 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 113076) = some ⟨13, 1, 0, 3444, 113076, 1, 16384⟩ := by
  decide +kernel

theorem context_13_113076_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113076 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 113076 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 113076, 1, 16384⟩
    (by decide) selected_cut_16500

theorem selected_cut_16501 : selected 8 ⟨419411, by decide⟩
    (prefixPartial 13 113077) = some ⟨13, 2, 0, 419411, 113077, 1293, 16384⟩ := by
  decide +kernel

theorem context_13_113077_419411 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113077 ⟨419411, by decide⟩ :=
  accepted_of_selected 13 113077 ⟨419411, by decide⟩ ⟨13, 2, 0, 419411, 113077, 1293, 16384⟩
    (by decide) selected_cut_16501

theorem selected_cut_16502 : selected 8 ⟨419462, by decide⟩
    (prefixPartial 13 113078) = some ⟨13, 2, 0, 419462, 113078, 2625, 16384⟩ := by
  decide +kernel

theorem context_13_113078_419462 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113078 ⟨419462, by decide⟩ :=
  accepted_of_selected 13 113078 ⟨419462, by decide⟩ ⟨13, 2, 0, 419462, 113078, 2625, 16384⟩
    (by decide) selected_cut_16502

theorem selected_cut_16503 : selected 8 ⟨419477, by decide⟩
    (prefixPartial 13 113079) = some ⟨13, 2, 0, 419477, 113079, 1205, 16384⟩ := by
  decide +kernel

theorem context_13_113079_419477 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113079 ⟨419477, by decide⟩ :=
  accepted_of_selected 13 113079 ⟨419477, by decide⟩ ⟨13, 2, 0, 419477, 113079, 1205, 16384⟩
    (by decide) selected_cut_16503

theorem unmarked_context_12_28269_419478 : frontier 9 ⟨419478, by decide⟩
    (prefixCache 12 28269) (prefixPartial 12 28269) = false := by
  decide +kernel

theorem node_context_12_28269_419478 : EJMOriginalGlobalDAGData.nodes 9 ⟨419478, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨419411, by decide⟩,⟨419462, by decide⟩,⟨419477, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28269_419478 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28269 ⟨419478, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28269
    ⟨419478, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨419411, by decide⟩,⟨419462, by decide⟩,⟨419477, by decide⟩]) unmarked_context_12_28269_419478 node_context_12_28269_419478
  intro a
  fin_cases a
  · exact context_13_113076_3444
  · exact context_13_113077_419411
  · exact context_13_113078_419462
  · exact context_13_113079_419477

theorem selected_cut_16504 : selected 9 ⟨419516, by decide⟩
    (prefixPartial 12 28270) = some ⟨12, 2, 0, 419516, 28270, 2845, 65536⟩ := by
  decide +kernel

theorem context_12_28270_419516 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28270 ⟨419516, by decide⟩ :=
  accepted_of_selected 12 28270 ⟨419516, by decide⟩ ⟨12, 2, 0, 419516, 28270, 2845, 65536⟩
    (by decide) selected_cut_16504

theorem selected_cut_16505 : selected 9 ⟨419555, by decide⟩
    (prefixPartial 12 28271) = some ⟨12, 2, 0, 419555, 28271, 3641, 65536⟩ := by
  decide +kernel

theorem context_12_28271_419555 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28271 ⟨419555, by decide⟩ :=
  accepted_of_selected 12 28271 ⟨419555, by decide⟩ ⟨12, 2, 0, 419555, 28271, 3641, 65536⟩
    (by decide) selected_cut_16505

theorem unmarked_context_11_7067_419556 : frontier 10 ⟨419556, by decide⟩
    (prefixCache 11 7067) (prefixPartial 11 7067) = false := by
  decide +kernel

theorem node_context_11_7067_419556 : EJMOriginalGlobalDAGData.nodes 10 ⟨419556, by decide⟩ =
    .split (coordinate 11) (![⟨419380, by decide⟩,⟨419478, by decide⟩,⟨419516, by decide⟩,⟨419555, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_7067_419556 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7067 ⟨419556, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 7067
    ⟨419556, by decide⟩ (by decide) (![⟨419380, by decide⟩,⟨419478, by decide⟩,⟨419516, by decide⟩,⟨419555, by decide⟩]) unmarked_context_11_7067_419556 node_context_11_7067_419556
  intro a
  fin_cases a
  · exact context_12_28268_419380
  · exact context_12_28269_419478
  · exact context_12_28270_419516
  · exact context_12_28271_419555

theorem unmarked_context_10_1766_419557 : frontier 11 ⟨419557, by decide⟩
    (prefixCache 10 1766) (prefixPartial 10 1766) = false := by
  decide +kernel

theorem node_context_10_1766_419557 : EJMOriginalGlobalDAGData.nodes 11 ⟨419557, by decide⟩ =
    .split (coordinate 10) (![⟨419029, by decide⟩,⟨419170, by decide⟩,⟨419337, by decide⟩,⟨419556, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1766_419557 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1766 ⟨419557, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1766
    ⟨419557, by decide⟩ (by decide) (![⟨419029, by decide⟩,⟨419170, by decide⟩,⟨419337, by decide⟩,⟨419556, by decide⟩]) unmarked_context_10_1766_419557 node_context_10_1766_419557
  intro a
  fin_cases a
  · exact context_11_7064_419029
  · exact context_11_7065_419170
  · exact context_11_7066_419337
  · exact context_11_7067_419556

theorem selected_cut_16506 : selected 9 ⟨419596, by decide⟩
    (prefixPartial 12 28272) = some ⟨12, 2, 0, 419596, 28272, 3025, 65536⟩ := by
  decide +kernel

theorem context_12_28272_419596 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28272 ⟨419596, by decide⟩ :=
  accepted_of_selected 12 28272 ⟨419596, by decide⟩ ⟨12, 2, 0, 419596, 28272, 3025, 65536⟩
    (by decide) selected_cut_16506

theorem selected_cut_16507 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 113092) = some ⟨13, 1, 0, 3444, 113092, 1, 16384⟩ := by
  decide +kernel

theorem context_13_113092_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113092 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 113092 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 113092, 1, 16384⟩
    (by decide) selected_cut_16507

theorem selected_cut_16508 : selected 8 ⟨419624, by decide⟩
    (prefixPartial 13 113093) = some ⟨13, 2, 0, 419624, 113093, 1161, 16384⟩ := by
  decide +kernel

theorem context_13_113093_419624 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113093 ⟨419624, by decide⟩ :=
  accepted_of_selected 13 113093 ⟨419624, by decide⟩ ⟨13, 2, 0, 419624, 113093, 1161, 16384⟩
    (by decide) selected_cut_16508

theorem selected_cut_16509 : selected 8 ⟨419671, by decide⟩
    (prefixPartial 13 113094) = some ⟨13, 2, 0, 419671, 113094, 2489, 16384⟩ := by
  decide +kernel

theorem context_13_113094_419671 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113094 ⟨419671, by decide⟩ :=
  accepted_of_selected 13 113094 ⟨419671, by decide⟩ ⟨13, 2, 0, 419671, 113094, 2489, 16384⟩
    (by decide) selected_cut_16509

theorem selected_cut_16510 : selected 8 ⟨419681, by decide⟩
    (prefixPartial 13 113095) = some ⟨13, 2, 0, 419681, 113095, 1077, 16384⟩ := by
  decide +kernel

theorem context_13_113095_419681 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 113095 ⟨419681, by decide⟩ :=
  accepted_of_selected 13 113095 ⟨419681, by decide⟩ ⟨13, 2, 0, 419681, 113095, 1077, 16384⟩
    (by decide) selected_cut_16510

theorem unmarked_context_12_28273_419682 : frontier 9 ⟨419682, by decide⟩
    (prefixCache 12 28273) (prefixPartial 12 28273) = false := by
  decide +kernel

theorem node_context_12_28273_419682 : EJMOriginalGlobalDAGData.nodes 9 ⟨419682, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨419624, by decide⟩,⟨419671, by decide⟩,⟨419681, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28273_419682 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28273 ⟨419682, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28273
    ⟨419682, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨419624, by decide⟩,⟨419671, by decide⟩,⟨419681, by decide⟩]) unmarked_context_12_28273_419682 node_context_12_28273_419682
  intro a
  fin_cases a
  · exact context_13_113092_3444
  · exact context_13_113093_419624
  · exact context_13_113094_419671
  · exact context_13_113095_419681

theorem selected_cut_16511 : selected 9 ⟨419719, by decide⟩
    (prefixPartial 12 28274) = some ⟨12, 2, 0, 419719, 28274, 2997, 65536⟩ := by
  decide +kernel

theorem context_12_28274_419719 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28274 ⟨419719, by decide⟩ :=
  accepted_of_selected 12 28274 ⟨419719, by decide⟩ ⟨12, 2, 0, 419719, 28274, 2997, 65536⟩
    (by decide) selected_cut_16511

theorem selected_cut_16512 : selected 9 ⟨419765, by decide⟩
    (prefixPartial 12 28275) = some ⟨12, 2, 0, 419765, 28275, 3625, 65536⟩ := by
  decide +kernel

theorem context_12_28275_419765 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28275 ⟨419765, by decide⟩ :=
  accepted_of_selected 12 28275 ⟨419765, by decide⟩ ⟨12, 2, 0, 419765, 28275, 3625, 65536⟩
    (by decide) selected_cut_16512

theorem unmarked_context_11_7068_419766 : frontier 10 ⟨419766, by decide⟩
    (prefixCache 11 7068) (prefixPartial 11 7068) = false := by
  decide +kernel

theorem node_context_11_7068_419766 : EJMOriginalGlobalDAGData.nodes 10 ⟨419766, by decide⟩ =
    .split (coordinate 11) (![⟨419596, by decide⟩,⟨419682, by decide⟩,⟨419719, by decide⟩,⟨419765, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_7068_419766 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7068 ⟨419766, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 7068
    ⟨419766, by decide⟩ (by decide) (![⟨419596, by decide⟩,⟨419682, by decide⟩,⟨419719, by decide⟩,⟨419765, by decide⟩]) unmarked_context_11_7068_419766 node_context_11_7068_419766
  intro a
  fin_cases a
  · exact context_12_28272_419596
  · exact context_12_28273_419682
  · exact context_12_28274_419719
  · exact context_12_28275_419765

theorem selected_cut_16513 : selected 9 ⟨419797, by decide⟩
    (prefixPartial 12 28276) = some ⟨12, 2, 0, 419797, 28276, 3033, 65536⟩ := by
  decide +kernel

theorem context_12_28276_419797 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28276 ⟨419797, by decide⟩ :=
  accepted_of_selected 12 28276 ⟨419797, by decide⟩ ⟨12, 2, 0, 419797, 28276, 3033, 65536⟩
    (by decide) selected_cut_16513

theorem selected_cut_16514 : selected 9 ⟨419904, by decide⟩
    (prefixPartial 12 28277) = some ⟨12, 2, 0, 419904, 28277, 2321, 65536⟩ := by
  decide +kernel

theorem context_12_28277_419904 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28277 ⟨419904, by decide⟩ :=
  accepted_of_selected 12 28277 ⟨419904, by decide⟩ ⟨12, 2, 0, 419904, 28277, 2321, 65536⟩
    (by decide) selected_cut_16514

theorem selected_cut_16515 : selected 9 ⟨419938, by decide⟩
    (prefixPartial 12 28278) = some ⟨12, 2, 0, 419938, 28278, 2965, 65536⟩ := by
  decide +kernel

theorem context_12_28278_419938 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28278 ⟨419938, by decide⟩ :=
  accepted_of_selected 12 28278 ⟨419938, by decide⟩ ⟨12, 2, 0, 419938, 28278, 2965, 65536⟩
    (by decide) selected_cut_16515

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
