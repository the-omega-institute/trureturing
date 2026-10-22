/- GID: D5/S3/Quantum/Measurements/BroadcastingChannelExtremaRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Measurements/BroadcastingChannelExtremaRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Measurements/BroadcastingChannelExtremaRefutation.claim; result=D5/S3/Quantum/Measurements/BroadcastingChannelExtremaRefutation.result; claim=D5/S3/Quantum/Measurements/BroadcastingChannelExtremaRefutation.claim
   digest: A three-dimensional observable has neither highest nor lowest broadcasting channel. -/

/-
admission_basis: open-problem-resolution (#15501; Refuted)
The module has no escape witness; it settles the external named questions.
The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).

Conventions: IsObservable is the frozen IsPOVM specialized to Fin m;
IsState is the frozen IsDensity. Kraus action uses MatrixMap.of_kraus K K.
IsPOVM and IsDensity have generality I. The output carrier is Fin d × Fin d.
The third orthogonal output is e0 tensor e1. K uses the frozen rowReset;
the balanced zero-two state is ActualQubitChordObstruction.signalProbe 1;
the other pure-state tests use the frozen rankOneDensity.
ConcealmentKernelNecessityRefutation.dual_kraus identifies the dual Kraus sum;
FiniteMemoryHistoryCapacity.zero_trace_mul_eq_zero supplies zero-pairing support.
The spectral, positivity, trace and finite-coordinate steps are classified
conservatively as bind-only; every private helper has a live consumer.
Definitions carry no independent theorem or escape-witness claim.
Generated of_kraus._proof_1 and of_kraus._proof_2 are implementation proof
constants of of_kraus, not separately enrolled frozen declarations.
Their owning of_kraus declaration identity is recorded below.

density_le_one: proof_shape: bind-only; escape_witness: none;
  consumers: no_highest.
  Direct frozen dependencies: none.
IsChannel: proof_shape: bind-only; escape_witness: none;
  consumers: Broadcasts, Nondisturbing, broadcast_a, channel_trace_preserving, nondisturbing_state_P, nondisturbing_fix_P, channel_posSemidef, comp_fix, no_highest.
  Direct frozen dependencies:
    | `D5/S3/Quantum/Foundation/FiniteKrausChannel` | `D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap` | `sha256:df01dcc9d6d91985f3214eaee7e1c5eacebab3335dff64bb7b620043c650cad7` |  |
    | `D5/S3/Quantum/Foundation/FiniteKrausChannel` | `D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap.of_kraus` | `sha256:024ca3125b8f182e070b880d7c41840a31fa9cb0aaa89e5d81dbe4ebb3c5f287` |  |
Broadcasts: proof_shape: bind-only; escape_witness: none;
  consumers: HasHighest, HasLowest, no_lowest, no_highest, claim, result.
  Direct frozen dependencies:
    | `D5/S3/Quantum/Entanglement/GHZMeasureBiseparableBound` | `D5.S3.Quantum.Entanglement.GHZMeasureBiseparableBound.IsDensity` | `sha256:fc9bb0824d5818ff419f72f26095faecc04e62ab59bf26f4f2bcefbb2d380448` |  |
    | `D5/S3/Quantum/Foundation/FiniteKrausChannel` | `D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap` | `sha256:df01dcc9d6d91985f3214eaee7e1c5eacebab3335dff64bb7b620043c650cad7` |  |
    | `D5/S3/Quantum/Foundation/FiniteKrausChannel` | `D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap.of_kraus` | `sha256:024ca3125b8f182e070b880d7c41840a31fa9cb0aaa89e5d81dbe4ebb3c5f287` |  |
Nondisturbing: proof_shape: bind-only; escape_witness: none;
  consumers: ConstructedFrom, nondisturbing_state_P, nondisturbing_fix_P, comp_fix, no_lowest, no_highest.
  Direct frozen dependencies:
    | `D5/S3/Quantum/Entanglement/GHZMeasureBiseparableBound` | `D5.S3.Quantum.Entanglement.GHZMeasureBiseparableBound.IsDensity` | `sha256:fc9bb0824d5818ff419f72f26095faecc04e62ab59bf26f4f2bcefbb2d380448` |  |
    | `D5/S3/Quantum/Foundation/FiniteKrausChannel` | `D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap` | `sha256:df01dcc9d6d91985f3214eaee7e1c5eacebab3335dff64bb7b620043c650cad7` |  |
    | `D5/S3/Quantum/Foundation/FiniteKrausChannel` | `D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap.of_kraus` | `sha256:024ca3125b8f182e070b880d7c41840a31fa9cb0aaa89e5d81dbe4ebb3c5f287` |  |
ConstructedFrom: proof_shape: bind-only; escape_witness: none;
  consumers: HasHighest, HasLowest, no_lowest, no_highest.
  Direct frozen dependencies:
    | `D5/S3/Quantum/Entanglement/GHZMeasureBiseparableBound` | `D5.S3.Quantum.Entanglement.GHZMeasureBiseparableBound.IsDensity` | `sha256:fc9bb0824d5818ff419f72f26095faecc04e62ab59bf26f4f2bcefbb2d380448` |  |
    | `D5/S3/Quantum/Foundation/FiniteKrausChannel` | `D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap` | `sha256:df01dcc9d6d91985f3214eaee7e1c5eacebab3335dff64bb7b620043c650cad7` |  |
    | `D5/S3/Quantum/Foundation/FiniteKrausChannel` | `D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap.of_kraus` | `sha256:024ca3125b8f182e070b880d7c41840a31fa9cb0aaa89e5d81dbe4ebb3c5f287` |  |
HasHighest: proof_shape: bind-only; escape_witness: none;
  consumers: no_highest, claim, result.
  Direct frozen dependencies:
    | `D5/S3/Quantum/Entanglement/GHZMeasureBiseparableBound` | `D5.S3.Quantum.Entanglement.GHZMeasureBiseparableBound.IsDensity` | `sha256:fc9bb0824d5818ff419f72f26095faecc04e62ab59bf26f4f2bcefbb2d380448` |  |
    | `D5/S3/Quantum/Foundation/FiniteKrausChannel` | `D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap` | `sha256:df01dcc9d6d91985f3214eaee7e1c5eacebab3335dff64bb7b620043c650cad7` |  |
    | `D5/S3/Quantum/Foundation/FiniteKrausChannel` | `D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap.of_kraus` | `sha256:024ca3125b8f182e070b880d7c41840a31fa9cb0aaa89e5d81dbe4ebb3c5f287` |  |
HasLowest: proof_shape: bind-only; escape_witness: none;
  consumers: no_lowest, claim, result.
  Direct frozen dependencies:
    | `D5/S3/Quantum/Entanglement/GHZMeasureBiseparableBound` | `D5.S3.Quantum.Entanglement.GHZMeasureBiseparableBound.IsDensity` | `sha256:fc9bb0824d5818ff419f72f26095faecc04e62ab59bf26f4f2bcefbb2d380448` |  |
    | `D5/S3/Quantum/Foundation/FiniteKrausChannel` | `D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap` | `sha256:df01dcc9d6d91985f3214eaee7e1c5eacebab3335dff64bb7b620043c650cad7` |  |
    | `D5/S3/Quantum/Foundation/FiniteKrausChannel` | `D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap.of_kraus` | `sha256:024ca3125b8f182e070b880d7c41840a31fa9cb0aaa89e5d81dbe4ebb3c5f287` |  |
P: proof_shape: bind-only; escape_witness: none;
  consumers: A0, broadcastChannel, observable_A, kraus_action_formula, broadcast_a, nondisturbing_state_P, nondisturbing_fix_P, state_support_P, comp_fix, channels_neq, lambda_basis, basis_P_trace, no_highest.
  Direct frozen dependencies: none.
A0: proof_shape: bind-only; escape_witness: none;
  consumers: A1, A, observable_A, broadcast_a, nondisturbing_state_P.
  Direct frozen dependencies: none.
A1: proof_shape: bind-only; escape_witness: none;
  consumers: A, observable_A, broadcast_a.
  Direct frozen dependencies: none.
A: proof_shape: bind-only; escape_witness: none;
  consumers: observable_A, broadcast_a, nondisturbing_state_P, nondisturbing_fix_P, comp_fix, no_lowest, no_highest, result.
  Direct frozen dependencies: none.
sigma: proof_shape: bind-only; escape_witness: none;
  consumers: broadcastChannel, kraus_action_formula, broadcast_a, comp_fix, channels_neq, lambda_basis, no_highest.
  Direct frozen dependencies: none.
broadcastChannel: proof_shape: bind-only; escape_witness: none;
  consumers: kraus_action_formula, channel_a, broadcast_a, comp_fix, channels_neq, lambda_basis, no_lowest, no_highest, result.
  Direct frozen dependencies: none.
K: proof_shape: bind-only; escape_witness: none;
  consumers: kraus_action_formula, channel_a.
  Direct frozen dependencies:
    | `D5/S3/Quantum/Recovery/KrausCompletion` | `D5.S3.Quantum.Recovery.KrausCompletion.rowReset` | `sha256:63b0c2d244c2f26eaa46ef36429ea4c9ccb72f7db37882de172d0e5045f79e31` |  |
observable_A: proof_shape: bind-only; escape_witness: none;
  consumers: result.
  Direct frozen dependencies:
    | `D5/S3/Quantum/QuantumChannels/ConcealmentKernelNecessityRefutation` | `D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation.IsPOVM` | `sha256:218e2b42c4dc29468db56af33ad277eb32b8ed575533012439ed233131c5efa1` |  |
    | `D5/S3/Quantum/QuantumChannels/ConcealmentKernelNecessityRefutation` | `D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation.diagonal_povm` | `sha256:de0639eb7d2cc0e2744e5c02a6801acaa920144435fb7dd8831281ad678d7430` |  |
kraus_action_formula: proof_shape: bind-only; escape_witness: none;
  consumers: channel_a.
  Direct frozen dependencies:
    | `D5/S3/Quantum/Recovery/KrausCompletion` | `D5.S3.Quantum.Recovery.KrausCompletion.rowReset` | `sha256:63b0c2d244c2f26eaa46ef36429ea4c9ccb72f7db37882de172d0e5045f79e31` |  |
channel_a: proof_shape: bind-only; escape_witness: none;
  consumers: broadcast_a.
  Direct frozen dependencies:
    | `D5/S3/Quantum/Foundation/FiniteKrausChannel` | `D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap` | `sha256:df01dcc9d6d91985f3214eaee7e1c5eacebab3335dff64bb7b620043c650cad7` |  |
    | `D5/S3/Quantum/Foundation/FiniteKrausChannel` | `D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap.of_kraus` | `sha256:024ca3125b8f182e070b880d7c41840a31fa9cb0aaa89e5d81dbe4ebb3c5f287` |  |
    | `D5/S3/Quantum/Recovery/KrausCompletion` | `D5.S3.Quantum.Recovery.KrausCompletion.rowReset` | `sha256:63b0c2d244c2f26eaa46ef36429ea4c9ccb72f7db37882de172d0e5045f79e31` |  |
trace_single_left: proof_shape: bind-only; escape_witness: none;
  consumers: broadcast_a.
  Direct frozen dependencies: none.
trace_single_right: proof_shape: bind-only; escape_witness: none;
  consumers: broadcast_a.
  Direct frozen dependencies: none.
broadcast_a: proof_shape: bind-only; escape_witness: none;
  consumers: no_lowest, no_highest, result.
  Direct frozen dependencies:
    | `D5/S3/Quantum/Entanglement/GHZMeasureBiseparableBound` | `D5.S3.Quantum.Entanglement.GHZMeasureBiseparableBound.IsDensity` | `sha256:fc9bb0824d5818ff419f72f26095faecc04e62ab59bf26f4f2bcefbb2d380448` |  |
    | `D5/S3/Quantum/Foundation/FiniteKrausChannel` | `D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap` | `sha256:df01dcc9d6d91985f3214eaee7e1c5eacebab3335dff64bb7b620043c650cad7` |  |
    | `D5/S3/Quantum/Foundation/FiniteKrausChannel` | `D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap.of_kraus` | `sha256:024ca3125b8f182e070b880d7c41840a31fa9cb0aaa89e5d81dbe4ebb3c5f287` |  |
    | `D5/S3/Quantum/Recovery/KrausCompletion` | `D5.S3.Quantum.Recovery.KrausCompletion.rowReset` | `sha256:63b0c2d244c2f26eaa46ef36429ea4c9ccb72f7db37882de172d0e5045f79e31` |  |
channel_trace_preserving: proof_shape: bind-only; escape_witness: none;
  consumers: nondisturbing_state_P, comp_fix, no_highest.
  Direct frozen dependencies:
    | `D5/S3/Quantum/Foundation/FiniteKrausChannel` | `D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap` | `sha256:df01dcc9d6d91985f3214eaee7e1c5eacebab3335dff64bb7b620043c650cad7` |  |
    | `D5/S3/Quantum/Foundation/FiniteKrausChannel` | `D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap.of_kraus` | `sha256:024ca3125b8f182e070b880d7c41840a31fa9cb0aaa89e5d81dbe4ebb3c5f287` |  |
    | `D5/S3/Quantum/Foundation/FiniteKrausChannel` | `D5.S3.Quantum.Foundation.FiniteKrausChannel.finite_kraus_quantum_channel` | `sha256:0ede64813b26e6161a0898eec4e0ff5c4fffc9727c0094b5bcfbc6a77c6ef9a0` |  |
    | `D5/S3/Quantum/Foundation/FiniteStateChannel` | `D5.S3.Quantum.Foundation.FiniteStateChannel.QuantumChannel` | `sha256:b7b2554d55122b11b177ecdf92367d243e4d35ec1e3897c844deba5df1285d05` |  |
    | `D5/S3/Quantum/Foundation/FiniteStateChannel` | `D5.S3.Quantum.Foundation.FiniteStateChannel.QuantumChannel.toCompletelyPositiveMap` | `sha256:7e2eefba0a4c0a6af6a4d36e7168066ad5899f2ba2622c43f082056bec8fb7dc` |  |
    | `D5/S3/Quantum/Foundation/FiniteStateChannel` | `D5.S3.Quantum.Foundation.FiniteStateChannel.QuantumChannel.trace_preserving` | `sha256:f7348a8905d2b54384d2e26b2c769f3d8eae0d734f588b9c2c8b8cc3892faf15` |  |
rhoPlus: proof_shape: bind-only; escape_witness: none;
  consumers: nondisturbing_fix_P.
  Direct frozen dependencies:
    | `D5/S3/Quantum/PureState/PureStateHandshake` | `D5.S3.Quantum.PureState.PureStateHandshake.rankOneDensity` | `sha256:e18ab4fd557d4917e344a15c06172fc321b99eb187307a88fe4c7fa4f8a28bf3` |  |
rhoPlus12: proof_shape: bind-only; escape_witness: none;
  consumers: nondisturbing_fix_P.
  Direct frozen dependencies:
    | `D5/S3/Quantum/PureState/PureStateHandshake` | `D5.S3.Quantum.PureState.PureStateHandshake.rankOneDensity` | `sha256:e18ab4fd557d4917e344a15c06172fc321b99eb187307a88fe4c7fa4f8a28bf3` |  |
rhoImag01: proof_shape: bind-only; escape_witness: none;
  consumers: nondisturbing_fix_P.
  Direct frozen dependencies:
    | `D5/S3/Quantum/PureState/PureStateHandshake` | `D5.S3.Quantum.PureState.PureStateHandshake.rankOneDensity` | `sha256:e18ab4fd557d4917e344a15c06172fc321b99eb187307a88fe4c7fa4f8a28bf3` |  |
rhoImag02: proof_shape: bind-only; escape_witness: none;
  consumers: nondisturbing_fix_P.
  Direct frozen dependencies:
    | `D5/S3/Quantum/PureState/PureStateHandshake` | `D5.S3.Quantum.PureState.PureStateHandshake.rankOneDensity` | `sha256:e18ab4fd557d4917e344a15c06172fc321b99eb187307a88fe4c7fa4f8a28bf3` |  |
rhoImag12: proof_shape: bind-only; escape_witness: none;
  consumers: nondisturbing_fix_P.
  Direct frozen dependencies:
    | `D5/S3/Quantum/PureState/PureStateHandshake` | `D5.S3.Quantum.PureState.PureStateHandshake.rankOneDensity` | `sha256:e18ab4fd557d4917e344a15c06172fc321b99eb187307a88fe4c7fa4f8a28bf3` |  |
scaled_pure_state: proof_shape: bind-only; escape_witness: none;
  consumers: rhoPlus_state, rhoPlus02_state, rhoPlus12_state, rhoImag01_state, rhoImag02_state, rhoImag12_state.
  Direct frozen dependencies:
    | `D5/S3/Quantum/Entanglement/GHZMeasureBiseparableBound` | `D5.S3.Quantum.Entanglement.GHZMeasureBiseparableBound.IsDensity` | `sha256:fc9bb0824d5818ff419f72f26095faecc04e62ab59bf26f4f2bcefbb2d380448` |  |
rhoPlus_state: proof_shape: bind-only; escape_witness: none;
  consumers: nondisturbing_fix_P.
  Direct frozen dependencies:
    | `D5/S3/Quantum/Entanglement/GHZMeasureBiseparableBound` | `D5.S3.Quantum.Entanglement.GHZMeasureBiseparableBound.IsDensity` | `sha256:fc9bb0824d5818ff419f72f26095faecc04e62ab59bf26f4f2bcefbb2d380448` |  |
    | `D5/S3/Quantum/PureState/PureStateHandshake` | `D5.S3.Quantum.PureState.PureStateHandshake.rankOneDensity` | `sha256:e18ab4fd557d4917e344a15c06172fc321b99eb187307a88fe4c7fa4f8a28bf3` |  |
rhoPlus02_state: proof_shape: bind-only; escape_witness: none;
  consumers: nondisturbing_fix_P.
  Direct frozen dependencies:
    | `D5/S3/Quantum/Entanglement/GHZMeasureBiseparableBound` | `D5.S3.Quantum.Entanglement.GHZMeasureBiseparableBound.IsDensity` | `sha256:fc9bb0824d5818ff419f72f26095faecc04e62ab59bf26f4f2bcefbb2d380448` |  |
    | `D5/S3/Quantum/Information/ActualQubitChordObstruction` | `D5.S3.Quantum.Information.ActualQubitChordObstruction.signalProbe` | `sha256:bef2288b884ed1760c2775060f1baefa0bdd53b5afe1d54cb8d54ac4f438beb0` |  |
rhoPlus12_state: proof_shape: bind-only; escape_witness: none;
  consumers: nondisturbing_fix_P.
  Direct frozen dependencies:
    | `D5/S3/Quantum/Entanglement/GHZMeasureBiseparableBound` | `D5.S3.Quantum.Entanglement.GHZMeasureBiseparableBound.IsDensity` | `sha256:fc9bb0824d5818ff419f72f26095faecc04e62ab59bf26f4f2bcefbb2d380448` |  |
    | `D5/S3/Quantum/PureState/PureStateHandshake` | `D5.S3.Quantum.PureState.PureStateHandshake.rankOneDensity` | `sha256:e18ab4fd557d4917e344a15c06172fc321b99eb187307a88fe4c7fa4f8a28bf3` |  |
rhoImag01_state: proof_shape: bind-only; escape_witness: none;
  consumers: nondisturbing_fix_P.
  Direct frozen dependencies:
    | `D5/S3/Quantum/Entanglement/GHZMeasureBiseparableBound` | `D5.S3.Quantum.Entanglement.GHZMeasureBiseparableBound.IsDensity` | `sha256:fc9bb0824d5818ff419f72f26095faecc04e62ab59bf26f4f2bcefbb2d380448` |  |
    | `D5/S3/Quantum/PureState/PureStateHandshake` | `D5.S3.Quantum.PureState.PureStateHandshake.rankOneDensity` | `sha256:e18ab4fd557d4917e344a15c06172fc321b99eb187307a88fe4c7fa4f8a28bf3` |  |
rhoImag02_state: proof_shape: bind-only; escape_witness: none;
  consumers: nondisturbing_fix_P.
  Direct frozen dependencies:
    | `D5/S3/Quantum/Entanglement/GHZMeasureBiseparableBound` | `D5.S3.Quantum.Entanglement.GHZMeasureBiseparableBound.IsDensity` | `sha256:fc9bb0824d5818ff419f72f26095faecc04e62ab59bf26f4f2bcefbb2d380448` |  |
    | `D5/S3/Quantum/PureState/PureStateHandshake` | `D5.S3.Quantum.PureState.PureStateHandshake.rankOneDensity` | `sha256:e18ab4fd557d4917e344a15c06172fc321b99eb187307a88fe4c7fa4f8a28bf3` |  |
rhoImag12_state: proof_shape: bind-only; escape_witness: none;
  consumers: nondisturbing_fix_P.
  Direct frozen dependencies:
    | `D5/S3/Quantum/Entanglement/GHZMeasureBiseparableBound` | `D5.S3.Quantum.Entanglement.GHZMeasureBiseparableBound.IsDensity` | `sha256:fc9bb0824d5818ff419f72f26095faecc04e62ab59bf26f4f2bcefbb2d380448` |  |
    | `D5/S3/Quantum/PureState/PureStateHandshake` | `D5.S3.Quantum.PureState.PureStateHandshake.rankOneDensity` | `sha256:e18ab4fd557d4917e344a15c06172fc321b99eb187307a88fe4c7fa4f8a28bf3` |  |
nondisturbing_state_P: proof_shape: bind-only; escape_witness: none;
  consumers: nondisturbing_fix_P, no_highest.
  Direct frozen dependencies:
    | `D5/S3/Quantum/Entanglement/GHZMeasureBiseparableBound` | `D5.S3.Quantum.Entanglement.GHZMeasureBiseparableBound.IsDensity` | `sha256:fc9bb0824d5818ff419f72f26095faecc04e62ab59bf26f4f2bcefbb2d380448` |  |
    | `D5/S3/Quantum/Foundation/FiniteKrausChannel` | `D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap` | `sha256:df01dcc9d6d91985f3214eaee7e1c5eacebab3335dff64bb7b620043c650cad7` |  |
    | `D5/S3/Quantum/Foundation/FiniteKrausChannel` | `D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap.of_kraus` | `sha256:024ca3125b8f182e070b880d7c41840a31fa9cb0aaa89e5d81dbe4ebb3c5f287` |  |
    | `D5/S3/Quantum/Foundation/FiniteKrausChannel` | `D5.S3.Quantum.Foundation.FiniteKrausChannel.finite_kraus_quantum_channel` | `sha256:0ede64813b26e6161a0898eec4e0ff5c4fffc9727c0094b5bcfbc6a77c6ef9a0` |  |
    | `D5/S3/Quantum/Foundation/FiniteStateChannel` | `D5.S3.Quantum.Foundation.FiniteStateChannel.QuantumChannel` | `sha256:b7b2554d55122b11b177ecdf92367d243e4d35ec1e3897c844deba5df1285d05` |  |
    | `D5/S3/Quantum/Foundation/FiniteStateChannel` | `D5.S3.Quantum.Foundation.FiniteStateChannel.QuantumChannel.toCompletelyPositiveMap` | `sha256:7e2eefba0a4c0a6af6a4d36e7168066ad5899f2ba2622c43f082056bec8fb7dc` |  |
    | `D5/S3/Quantum/Foundation/FiniteStateChannel` | `D5.S3.Quantum.Foundation.FiniteStateChannel.QuantumChannel.trace_preserving` | `sha256:f7348a8905d2b54384d2e26b2c769f3d8eae0d734f588b9c2c8b8cc3892faf15` |  |
basis_state: proof_shape: bind-only; escape_witness: none;
  consumers: nondisturbing_fix_P, no_highest.
  Direct frozen dependencies:
    | `D5/S3/Quantum/Entanglement/GHZMeasureBiseparableBound` | `D5.S3.Quantum.Entanglement.GHZMeasureBiseparableBound.IsDensity` | `sha256:fc9bb0824d5818ff419f72f26095faecc04e62ab59bf26f4f2bcefbb2d380448` |  |
nondisturbing_fix_P: proof_shape: bind-only; escape_witness: none;
  consumers: comp_fix.
  Direct frozen dependencies:
    | `D5/S3/Quantum/Entanglement/GHZMeasureBiseparableBound` | `D5.S3.Quantum.Entanglement.GHZMeasureBiseparableBound.IsDensity` | `sha256:fc9bb0824d5818ff419f72f26095faecc04e62ab59bf26f4f2bcefbb2d380448` |  |
    | `D5/S3/Quantum/Foundation/FiniteKrausChannel` | `D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap` | `sha256:df01dcc9d6d91985f3214eaee7e1c5eacebab3335dff64bb7b620043c650cad7` |  |
    | `D5/S3/Quantum/QuantumChannels/PositiveFilterTransposeRefutation` | `D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap.Dual.trace_eq` | `sha256:4b9d5299e7cc9ef1ebad4b43e8fff47d1c203797359d108299c3be4eea0bec33` |  |
    | `D5/S3/Quantum/QuantumChannels/PositiveFilterTransposeRefutation` | `D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap.dual` | `sha256:853fb5326477f481c103e8204034cb05d57c32bd135f3ed8554657612f12d5d3` | The short selector `MatrixMap.dual` is ambiguous. |
    | `D5/S3/Quantum/Foundation/FiniteKrausChannel` | `D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap.of_kraus` | `sha256:024ca3125b8f182e070b880d7c41840a31fa9cb0aaa89e5d81dbe4ebb3c5f287` |  |
    | `D5/S3/Quantum/Foundation/FiniteKrausChannel` | `D5.S3.Quantum.Foundation.FiniteKrausChannel.finite_kraus_quantum_channel` | `sha256:0ede64813b26e6161a0898eec4e0ff5c4fffc9727c0094b5bcfbc6a77c6ef9a0` |  |
    | `D5/S3/Quantum/Foundation/FiniteStateChannel` | `D5.S3.Quantum.Foundation.FiniteStateChannel.QuantumChannel` | `sha256:b7b2554d55122b11b177ecdf92367d243e4d35ec1e3897c844deba5df1285d05` |  |
    | `D5/S3/Quantum/Foundation/FiniteStateChannel` | `D5.S3.Quantum.Foundation.FiniteStateChannel.QuantumChannel.toCompletelyPositiveMap` | `sha256:7e2eefba0a4c0a6af6a4d36e7168066ad5899f2ba2622c43f082056bec8fb7dc` |  |
    | `D5/S3/Quantum/Foundation/FiniteStateChannel` | `D5.S3.Quantum.Foundation.FiniteStateChannel.QuantumChannel.trace_preserving` | `sha256:f7348a8905d2b54384d2e26b2c769f3d8eae0d734f588b9c2c8b8cc3892faf15` |  |
    | `D5/S3/Quantum/Information/ActualQubitChordObstruction` | `D5.S3.Quantum.Information.ActualQubitChordObstruction.signalProbe` | `sha256:bef2288b884ed1760c2775060f1baefa0bdd53b5afe1d54cb8d54ac4f438beb0` |  |
    | `D5/S3/Quantum/PureState/PureStateHandshake` | `D5.S3.Quantum.PureState.PureStateHandshake.rankOneDensity` | `sha256:e18ab4fd557d4917e344a15c06172fc321b99eb187307a88fe4c7fa4f8a28bf3` |  |
    | `D5/S3/Quantum/QuantumChannels/ConcealmentKernelNecessityRefutation` | `D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation.dual_kraus` | `sha256:dd9f5f1ce4725296d08145a6066f3ee325b93def4f274543427b5520e5234de5` |  |
state_support_P: proof_shape: bind-only; escape_witness: none;
  consumers: no_highest.
  Direct frozen dependencies:
    | `D5/S3/Quantum/Entanglement/GHZMeasureBiseparableBound` | `D5.S3.Quantum.Entanglement.GHZMeasureBiseparableBound.IsDensity` | `sha256:fc9bb0824d5818ff419f72f26095faecc04e62ab59bf26f4f2bcefbb2d380448` |  |
    | `D5/S3/Quantum/Measurements/FiniteMemoryHistoryCapacity` | `D5.S3.Quantum.Measurements.FiniteMemoryHistoryCapacity.zero_trace_mul_eq_zero` | `sha256:72e5d3b134abd653c9f2e4dd9d86b9a04e2ae4da3f759abcbc26215c6f57cf67` |  |
channel_posSemidef: proof_shape: bind-only; escape_witness: none;
  consumers: no_highest.
  Direct frozen dependencies:
    | `D5/S3/Quantum/Foundation/FiniteKrausChannel` | `D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap` | `sha256:df01dcc9d6d91985f3214eaee7e1c5eacebab3335dff64bb7b620043c650cad7` |  |
    | `D5/S3/Quantum/Foundation/FiniteKrausChannel` | `D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap.of_kraus` | `sha256:024ca3125b8f182e070b880d7c41840a31fa9cb0aaa89e5d81dbe4ebb3c5f287` |  |
    | `D5/S3/Quantum/Foundation/FiniteKrausChannel` | `D5.S3.Quantum.Foundation.FiniteKrausChannel.finite_kraus_quantum_channel` | `sha256:0ede64813b26e6161a0898eec4e0ff5c4fffc9727c0094b5bcfbc6a77c6ef9a0` |  |
    | `D5/S3/Quantum/Foundation/FiniteStateChannel` | `D5.S3.Quantum.Foundation.FiniteStateChannel.QuantumChannel` | `sha256:b7b2554d55122b11b177ecdf92367d243e4d35ec1e3897c844deba5df1285d05` |  |
    | `D5/S3/Quantum/Foundation/FiniteStateChannel` | `D5.S3.Quantum.Foundation.FiniteStateChannel.QuantumChannel.toCompletelyPositiveMap` | `sha256:7e2eefba0a4c0a6af6a4d36e7168066ad5899f2ba2622c43f082056bec8fb7dc` |  |
single_trace_nonneg: proof_shape: bind-only; escape_witness: none;
  consumers: no_highest.
  Direct frozen dependencies: none.
comp_fix: proof_shape: bind-only; escape_witness: none;
  consumers: no_lowest.
  Direct frozen dependencies:
    | `D5/S3/Quantum/Entanglement/GHZMeasureBiseparableBound` | `D5.S3.Quantum.Entanglement.GHZMeasureBiseparableBound.IsDensity` | `sha256:fc9bb0824d5818ff419f72f26095faecc04e62ab59bf26f4f2bcefbb2d380448` |  |
    | `D5/S3/Quantum/Foundation/FiniteKrausChannel` | `D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap` | `sha256:df01dcc9d6d91985f3214eaee7e1c5eacebab3335dff64bb7b620043c650cad7` |  |
    | `D5/S3/Quantum/QuantumChannels/PositiveFilterTransposeRefutation` | `D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap.Dual.trace_eq` | `sha256:4b9d5299e7cc9ef1ebad4b43e8fff47d1c203797359d108299c3be4eea0bec33` |  |
    | `D5/S3/Quantum/QuantumChannels/PositiveFilterTransposeRefutation` | `D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap.dual` | `sha256:853fb5326477f481c103e8204034cb05d57c32bd135f3ed8554657612f12d5d3` | The short selector `MatrixMap.dual` is ambiguous. |
    | `D5/S3/Quantum/Foundation/FiniteKrausChannel` | `D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap.of_kraus` | `sha256:024ca3125b8f182e070b880d7c41840a31fa9cb0aaa89e5d81dbe4ebb3c5f287` |  |
    | `D5/S3/Quantum/Foundation/FiniteKrausChannel` | `D5.S3.Quantum.Foundation.FiniteKrausChannel.finite_kraus_quantum_channel` | `sha256:0ede64813b26e6161a0898eec4e0ff5c4fffc9727c0094b5bcfbc6a77c6ef9a0` |  |
    | `D5/S3/Quantum/Foundation/FiniteStateChannel` | `D5.S3.Quantum.Foundation.FiniteStateChannel.QuantumChannel` | `sha256:b7b2554d55122b11b177ecdf92367d243e4d35ec1e3897c844deba5df1285d05` |  |
    | `D5/S3/Quantum/Foundation/FiniteStateChannel` | `D5.S3.Quantum.Foundation.FiniteStateChannel.QuantumChannel.toCompletelyPositiveMap` | `sha256:7e2eefba0a4c0a6af6a4d36e7168066ad5899f2ba2622c43f082056bec8fb7dc` |  |
    | `D5/S3/Quantum/Foundation/FiniteStateChannel` | `D5.S3.Quantum.Foundation.FiniteStateChannel.QuantumChannel.trace_preserving` | `sha256:f7348a8905d2b54384d2e26b2c769f3d8eae0d734f588b9c2c8b8cc3892faf15` |  |
    | `D5/S3/Quantum/Information/ActualQubitChordObstruction` | `D5.S3.Quantum.Information.ActualQubitChordObstruction.signalProbe` | `sha256:bef2288b884ed1760c2775060f1baefa0bdd53b5afe1d54cb8d54ac4f438beb0` |  |
    | `D5/S3/Quantum/PureState/PureStateHandshake` | `D5.S3.Quantum.PureState.PureStateHandshake.rankOneDensity` | `sha256:e18ab4fd557d4917e344a15c06172fc321b99eb187307a88fe4c7fa4f8a28bf3` |  |
    | `D5/S3/Quantum/QuantumChannels/ConcealmentKernelNecessityRefutation` | `D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation.dual_kraus` | `sha256:dd9f5f1ce4725296d08145a6066f3ee325b93def4f274543427b5520e5234de5` |  |
channels_neq: proof_shape: bind-only; escape_witness: none;
  consumers: no_lowest.
  Direct frozen dependencies: none.
lambda_basis: proof_shape: bind-only; escape_witness: none;
  consumers: no_highest.
  Direct frozen dependencies: none.
basis_P_trace: proof_shape: bind-only; escape_witness: none;
  consumers: no_highest.
  Direct frozen dependencies: none.
no_lowest: proof_shape: bind-only; escape_witness: none;
  consumers: result.
  Direct frozen dependencies:
    | `D5/S3/Quantum/Entanglement/GHZMeasureBiseparableBound` | `D5.S3.Quantum.Entanglement.GHZMeasureBiseparableBound.IsDensity` | `sha256:fc9bb0824d5818ff419f72f26095faecc04e62ab59bf26f4f2bcefbb2d380448` |  |
    | `D5/S3/Quantum/Foundation/FiniteKrausChannel` | `D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap` | `sha256:df01dcc9d6d91985f3214eaee7e1c5eacebab3335dff64bb7b620043c650cad7` |  |
    | `D5/S3/Quantum/QuantumChannels/PositiveFilterTransposeRefutation` | `D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap.Dual.trace_eq` | `sha256:4b9d5299e7cc9ef1ebad4b43e8fff47d1c203797359d108299c3be4eea0bec33` |  |
    | `D5/S3/Quantum/QuantumChannels/PositiveFilterTransposeRefutation` | `D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap.dual` | `sha256:853fb5326477f481c103e8204034cb05d57c32bd135f3ed8554657612f12d5d3` | The short selector `MatrixMap.dual` is ambiguous. |
    | `D5/S3/Quantum/Foundation/FiniteKrausChannel` | `D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap.of_kraus` | `sha256:024ca3125b8f182e070b880d7c41840a31fa9cb0aaa89e5d81dbe4ebb3c5f287` |  |
    | `D5/S3/Quantum/Foundation/FiniteKrausChannel` | `D5.S3.Quantum.Foundation.FiniteKrausChannel.finite_kraus_quantum_channel` | `sha256:0ede64813b26e6161a0898eec4e0ff5c4fffc9727c0094b5bcfbc6a77c6ef9a0` |  |
    | `D5/S3/Quantum/Foundation/FiniteStateChannel` | `D5.S3.Quantum.Foundation.FiniteStateChannel.QuantumChannel` | `sha256:b7b2554d55122b11b177ecdf92367d243e4d35ec1e3897c844deba5df1285d05` |  |
    | `D5/S3/Quantum/Foundation/FiniteStateChannel` | `D5.S3.Quantum.Foundation.FiniteStateChannel.QuantumChannel.toCompletelyPositiveMap` | `sha256:7e2eefba0a4c0a6af6a4d36e7168066ad5899f2ba2622c43f082056bec8fb7dc` |  |
    | `D5/S3/Quantum/Foundation/FiniteStateChannel` | `D5.S3.Quantum.Foundation.FiniteStateChannel.QuantumChannel.trace_preserving` | `sha256:f7348a8905d2b54384d2e26b2c769f3d8eae0d734f588b9c2c8b8cc3892faf15` |  |
    | `D5/S3/Quantum/Information/ActualQubitChordObstruction` | `D5.S3.Quantum.Information.ActualQubitChordObstruction.signalProbe` | `sha256:bef2288b884ed1760c2775060f1baefa0bdd53b5afe1d54cb8d54ac4f438beb0` |  |
    | `D5/S3/Quantum/PureState/PureStateHandshake` | `D5.S3.Quantum.PureState.PureStateHandshake.rankOneDensity` | `sha256:e18ab4fd557d4917e344a15c06172fc321b99eb187307a88fe4c7fa4f8a28bf3` |  |
    | `D5/S3/Quantum/QuantumChannels/ConcealmentKernelNecessityRefutation` | `D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation.dual_kraus` | `sha256:dd9f5f1ce4725296d08145a6066f3ee325b93def4f274543427b5520e5234de5` |  |
    | `D5/S3/Quantum/Recovery/KrausCompletion` | `D5.S3.Quantum.Recovery.KrausCompletion.rowReset` | `sha256:63b0c2d244c2f26eaa46ef36429ea4c9ccb72f7db37882de172d0e5045f79e31` |  |
sigma_gap_pos: proof_shape: bind-only; escape_witness: none;
  consumers: no_highest.
  Direct frozen dependencies: none.
no_highest: proof_shape: bind-only; escape_witness: none;
  consumers: result.
  Direct frozen dependencies:
    | `D5/S3/Quantum/Entanglement/GHZMeasureBiseparableBound` | `D5.S3.Quantum.Entanglement.GHZMeasureBiseparableBound.IsDensity` | `sha256:fc9bb0824d5818ff419f72f26095faecc04e62ab59bf26f4f2bcefbb2d380448` |  |
    | `D5/S3/Quantum/Foundation/FiniteKrausChannel` | `D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap` | `sha256:df01dcc9d6d91985f3214eaee7e1c5eacebab3335dff64bb7b620043c650cad7` |  |
    | `D5/S3/Quantum/Foundation/FiniteKrausChannel` | `D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap.of_kraus` | `sha256:024ca3125b8f182e070b880d7c41840a31fa9cb0aaa89e5d81dbe4ebb3c5f287` |  |
    | `D5/S3/Quantum/Foundation/FiniteKrausChannel` | `D5.S3.Quantum.Foundation.FiniteKrausChannel.finite_kraus_quantum_channel` | `sha256:0ede64813b26e6161a0898eec4e0ff5c4fffc9727c0094b5bcfbc6a77c6ef9a0` |  |
    | `D5/S3/Quantum/Foundation/FiniteStateChannel` | `D5.S3.Quantum.Foundation.FiniteStateChannel.QuantumChannel` | `sha256:b7b2554d55122b11b177ecdf92367d243e4d35ec1e3897c844deba5df1285d05` |  |
    | `D5/S3/Quantum/Foundation/FiniteStateChannel` | `D5.S3.Quantum.Foundation.FiniteStateChannel.QuantumChannel.toCompletelyPositiveMap` | `sha256:7e2eefba0a4c0a6af6a4d36e7168066ad5899f2ba2622c43f082056bec8fb7dc` |  |
    | `D5/S3/Quantum/Foundation/FiniteStateChannel` | `D5.S3.Quantum.Foundation.FiniteStateChannel.QuantumChannel.trace_preserving` | `sha256:f7348a8905d2b54384d2e26b2c769f3d8eae0d734f588b9c2c8b8cc3892faf15` |  |
    | `D5/S3/Quantum/Measurements/FiniteMemoryHistoryCapacity` | `D5.S3.Quantum.Measurements.FiniteMemoryHistoryCapacity.zero_trace_mul_eq_zero` | `sha256:72e5d3b134abd653c9f2e4dd9d86b9a04e2ae4da3f759abcbc26215c6f57cf67` |  |
    | `D5/S3/Quantum/Recovery/KrausCompletion` | `D5.S3.Quantum.Recovery.KrausCompletion.rowReset` | `sha256:63b0c2d244c2f26eaa46ef36429ea4c9ccb72f7db37882de172d0e5045f79e31` |  |
claim: proof_shape: bind-only; escape_witness: none;
  consumers: result.
  Direct frozen dependencies:
    | `D5/S3/Quantum/Entanglement/GHZMeasureBiseparableBound` | `D5.S3.Quantum.Entanglement.GHZMeasureBiseparableBound.IsDensity` | `sha256:fc9bb0824d5818ff419f72f26095faecc04e62ab59bf26f4f2bcefbb2d380448` |  |
    | `D5/S3/Quantum/Foundation/FiniteKrausChannel` | `D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap` | `sha256:df01dcc9d6d91985f3214eaee7e1c5eacebab3335dff64bb7b620043c650cad7` |  |
    | `D5/S3/Quantum/Foundation/FiniteKrausChannel` | `D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap.of_kraus` | `sha256:024ca3125b8f182e070b880d7c41840a31fa9cb0aaa89e5d81dbe4ebb3c5f287` |  |
    | `D5/S3/Quantum/QuantumChannels/ConcealmentKernelNecessityRefutation` | `D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation.IsPOVM` | `sha256:218e2b42c4dc29468db56af33ad277eb32b8ed575533012439ed233131c5efa1` |  |
result: proof_shape: bind-only; escape_witness: none;
  consumers: none.
  Direct frozen dependencies:
    | `D5/S3/Quantum/Entanglement/GHZMeasureBiseparableBound` | `D5.S3.Quantum.Entanglement.GHZMeasureBiseparableBound.IsDensity` | `sha256:fc9bb0824d5818ff419f72f26095faecc04e62ab59bf26f4f2bcefbb2d380448` |  |
    | `D5/S3/Quantum/Foundation/FiniteKrausChannel` | `D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap` | `sha256:df01dcc9d6d91985f3214eaee7e1c5eacebab3335dff64bb7b620043c650cad7` |  |
    | `D5/S3/Quantum/QuantumChannels/PositiveFilterTransposeRefutation` | `D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap.Dual.trace_eq` | `sha256:4b9d5299e7cc9ef1ebad4b43e8fff47d1c203797359d108299c3be4eea0bec33` |  |
    | `D5/S3/Quantum/QuantumChannels/PositiveFilterTransposeRefutation` | `D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap.dual` | `sha256:853fb5326477f481c103e8204034cb05d57c32bd135f3ed8554657612f12d5d3` | The short selector `MatrixMap.dual` is ambiguous. |
    | `D5/S3/Quantum/Foundation/FiniteKrausChannel` | `D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap.of_kraus` | `sha256:024ca3125b8f182e070b880d7c41840a31fa9cb0aaa89e5d81dbe4ebb3c5f287` |  |
    | `D5/S3/Quantum/Foundation/FiniteKrausChannel` | `D5.S3.Quantum.Foundation.FiniteKrausChannel.finite_kraus_quantum_channel` | `sha256:0ede64813b26e6161a0898eec4e0ff5c4fffc9727c0094b5bcfbc6a77c6ef9a0` |  |
    | `D5/S3/Quantum/Foundation/FiniteStateChannel` | `D5.S3.Quantum.Foundation.FiniteStateChannel.QuantumChannel` | `sha256:b7b2554d55122b11b177ecdf92367d243e4d35ec1e3897c844deba5df1285d05` |  |
    | `D5/S3/Quantum/Foundation/FiniteStateChannel` | `D5.S3.Quantum.Foundation.FiniteStateChannel.QuantumChannel.toCompletelyPositiveMap` | `sha256:7e2eefba0a4c0a6af6a4d36e7168066ad5899f2ba2622c43f082056bec8fb7dc` |  |
    | `D5/S3/Quantum/Foundation/FiniteStateChannel` | `D5.S3.Quantum.Foundation.FiniteStateChannel.QuantumChannel.trace_preserving` | `sha256:f7348a8905d2b54384d2e26b2c769f3d8eae0d734f588b9c2c8b8cc3892faf15` |  |
    | `D5/S3/Quantum/Information/ActualQubitChordObstruction` | `D5.S3.Quantum.Information.ActualQubitChordObstruction.signalProbe` | `sha256:bef2288b884ed1760c2775060f1baefa0bdd53b5afe1d54cb8d54ac4f438beb0` |  |
    | `D5/S3/Quantum/Measurements/FiniteMemoryHistoryCapacity` | `D5.S3.Quantum.Measurements.FiniteMemoryHistoryCapacity.zero_trace_mul_eq_zero` | `sha256:72e5d3b134abd653c9f2e4dd9d86b9a04e2ae4da3f759abcbc26215c6f57cf67` |  |
    | `D5/S3/Quantum/PureState/PureStateHandshake` | `D5.S3.Quantum.PureState.PureStateHandshake.rankOneDensity` | `sha256:e18ab4fd557d4917e344a15c06172fc321b99eb187307a88fe4c7fa4f8a28bf3` |  |
    | `D5/S3/Quantum/QuantumChannels/ConcealmentKernelNecessityRefutation` | `D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation.IsPOVM` | `sha256:218e2b42c4dc29468db56af33ad277eb32b8ed575533012439ed233131c5efa1` |  |
    | `D5/S3/Quantum/QuantumChannels/ConcealmentKernelNecessityRefutation` | `D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation.diagonal_povm` | `sha256:de0639eb7d2cc0e2744e5c02a6801acaa920144435fb7dd8831281ad678d7430` |  |
    | `D5/S3/Quantum/QuantumChannels/ConcealmentKernelNecessityRefutation` | `D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation.dual_kraus` | `sha256:dd9f5f1ce4725296d08145a6066f3ee325b93def4f274543427b5520e5234de5` |  |
    | `D5/S3/Quantum/Recovery/KrausCompletion` | `D5.S3.Quantum.Recovery.KrausCompletion.rowReset` | `sha256:63b0c2d244c2f26eaa46ef36429ea4c9ccb72f7db37882de172d0e5045f79e31` |  |
Escape audit for published helper theorems unfinished: https://github.com/the-omega-institute/trureturing/issues/19490.
-/

import D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation
import D5.S3.Quantum.Entanglement.GHZMeasureBiseparableBound
import D5.S3.Quantum.PureState.PureStateHandshake
import D5.S3.Quantum.Recovery.KrausCompletion
import D5.S3.Quantum.Information.ActualQubitChordObstruction
import D5.S3.Quantum.Measurements.FiniteMemoryHistoryCapacity
import D5.S3.Quantum.Foundation.FiniteKrausChannel
import D5.S3.Quantum.Foundation.FiniteStateChannel
import D5.S3.Quantum.QuantumChannels.PositiveFilterTransposeRefutation

namespace D5.S3.Quantum.Measurements.BroadcastingChannelExtremaRefutation

open D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation (IsPOVM)
open D5.S3.Quantum.Entanglement.GHZMeasureBiseparableBound (IsDensity)
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf (MatrixMap)
open D5.S3.Quantum.PureState.PureStateHandshake (rankOneDensity)
open D5.S3.Quantum.Information.ActualQubitChordObstruction (signalProbe)

open scoped BigOperators Matrix Kronecker ComplexOrder MatrixOrder
open Matrix
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

theorem density_le_one {n : Type*} [Fintype n] [DecidableEq n]
    {T : Matrix n n ℂ} (hT : T.PosSemidef) (htr : T.trace = 1) :
    (1 - T).PosSemidef := by
  let hH := hT.1
  let lam : n → ℝ := hH.eigenvalues
  have hnon : ∀ i, 0 ≤ lam i := by
    intro i
    exact hT.eigenvalues_nonneg i
  have hsumC : T.trace = ∑ i, (lam i : ℂ) := hH.trace_eq_sum_eigenvalues
  have hsum : ∑ i, lam i = 1 := by
    have hc : (∑ i, (lam i : ℂ)) = (1 : ℂ) := by simpa [htr] using hsumC.symm
    exact_mod_cast hc
  have hle : ∀ i, lam i ≤ 1 := by
    intro i
    have hs : lam i ≤ ∑ j, lam j := by
      exact Finset.single_le_sum (fun j _ => hnon j) (Finset.mem_univ i)
    linarith [hsum]
  have hdiag : (Matrix.diagonal (fun i => ((1 - lam i : ℝ) : ℂ))).PosSemidef := by
    apply Matrix.PosSemidef.diagonal
    intro i
    exact RCLike.ofReal_nonneg.mpr (sub_nonneg.mpr (hle i))
  let U : Matrix n n ℂ := hH.eigenvectorUnitary
  have hrepr : T = U * Matrix.diagonal (fun i => (RCLike.ofReal (lam i) : ℂ)) * Uᴴ := by
    dsimp [U, lam]
    change T = (↑hH.eigenvectorUnitary : Matrix n n ℂ) *
      Matrix.diagonal (fun i => (RCLike.ofReal (hH.eigenvalues i) : ℂ)) *
      star (↑hH.eigenvectorUnitary : Matrix n n ℂ)
    exact hH.spectral_theorem
  have hunitR : U * Uᴴ = (1 : Matrix n n ℂ) := by
    change (↑hH.eigenvectorUnitary : Matrix n n ℂ) *
      Matrix.conjTranspose (↑hH.eigenvectorUnitary : Matrix n n ℂ) = 1
    rw [← Matrix.star_eq_conjTranspose]
    exact Unitary.coe_mul_star_self hH.eigenvectorUnitary
  have hdiff : (1 - T) = U * Matrix.diagonal (fun i => ((1 - lam i : ℝ) : ℂ)) * Uᴴ := by
    rw [hrepr]
    calc
      1 - (U * Matrix.diagonal (fun i => ((lam i : ℝ) : ℂ))) * Uᴴ =
          U * Uᴴ - (U * Matrix.diagonal (fun i => ((lam i : ℝ) : ℂ))) * Uᴴ := by
            rw [hunitR]
      _ = (U * (1 : Matrix n n ℂ) - U * Matrix.diagonal (fun i => ((lam i : ℝ) : ℂ))) * Uᴴ := by
            rw [Matrix.sub_mul]
            simp
      _ = U * ((1 : Matrix n n ℂ) - Matrix.diagonal (fun i => ((lam i : ℝ) : ℂ))) * Uᴴ := by
            rw [Matrix.mul_sub]
      _ = U * Matrix.diagonal (fun i => ((1 - lam i : ℝ) : ℂ)) * Uᴴ := by
            congr 2
            ext i j
            by_cases hij : i = j <;> simp [Matrix.sub_apply, Matrix.one_apply, hij]
  rw [hdiff]
  exact hdiag.mul_mul_conjTranspose_same U

def IsChannel {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Φ : Matrix (Fin d) (Fin d) ℂ → Matrix ι ι ℂ) : Prop :=
  ∃ (k : ℕ) (K : Fin k → Matrix ι (Fin d) ℂ),
    (∑ j, (K j)ᴴ * K j = 1) ∧
    (∀ X, Φ X = MatrixMap.of_kraus K K X)

def Broadcasts {m d : ℕ} (A : Fin m → Matrix (Fin d) (Fin d) ℂ)
    (Λ : Matrix (Fin d) (Fin d) ℂ → Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) : Prop :=
  IsChannel Λ ∧ ∀ ρ, IsDensity ρ → ∀ x,
    (Matrix.trace ((Λ ρ) * (A x ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ))) = Matrix.trace (ρ * A x) ∧
     Matrix.trace ((Λ ρ) * ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ A x)) = Matrix.trace (ρ * A x))

def Nondisturbing {m d : ℕ} (A : Fin m → Matrix (Fin d) (Fin d) ℂ)
    (Θ : Matrix (Fin d) (Fin d) ℂ → Matrix (Fin d) (Fin d) ℂ) : Prop :=
  IsChannel Θ ∧ ∀ ρ, IsDensity ρ → ∀ x,
    Matrix.trace (Θ ρ * A x) = Matrix.trace (ρ * A x)

def ConstructedFrom {m d : ℕ} (A : Fin m → Matrix (Fin d) (Fin d) ℂ)
    (Λ' : Matrix (Fin d) (Fin d) ℂ → Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (Λ : Matrix (Fin d) (Fin d) ℂ → Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) : Prop :=
  ∃ Θ : Matrix (Fin d) (Fin d) ℂ → Matrix (Fin d) (Fin d) ℂ,
    Nondisturbing A Θ ∧ Λ' = Λ ∘ Θ

-- In the concrete counterexample all channel outputs have the same finite output type.
def HasHighest {m d : ℕ} (A : Fin m → Matrix (Fin d) (Fin d) ℂ) : Prop :=
  ∃ H : Matrix (Fin d) (Fin d) ℂ → Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ,
    Broadcasts A H ∧ ∀ Λ, Broadcasts A Λ → ConstructedFrom A Λ H

def HasLowest {m d : ℕ} (A : Fin m → Matrix (Fin d) (Fin d) ℂ) : Prop :=
  ∃ L : Matrix (Fin d) (Fin d) ℂ → Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ,
    Broadcasts A L ∧ ∀ Λ, Broadcasts A Λ → ConstructedFrom A L Λ

private def P : (Matrix (Fin 3) (Fin 3) ℂ) := Matrix.diagonal ![(1 : ℂ), 1, 0]
private def A0 : (Matrix (Fin 3) (Fin 3) ℂ) := (3/4 : ℂ) • P + (1/4 : ℂ) • (Matrix.single (2 : Fin 3) (2 : Fin 3) (1 : ℂ))
private def A1 : (Matrix (Fin 3) (Fin 3) ℂ) := (1 : (Matrix (Fin 3) (Fin 3) ℂ)) - A0
private def A : Fin 2 → (Matrix (Fin 3) (Fin 3) ℂ) := ![A0, A1]
private def sigma : Fin 3 → (Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ) := ![(Matrix.single ((0,0) : Fin 3 × Fin 3) ((0,0) : Fin 3 × Fin 3) (1 : ℂ)), (Matrix.single ((1,1) : Fin 3 × Fin 3) ((1,1) : Fin 3 × Fin 3) (1 : ℂ)), (Matrix.single ((0,1) : Fin 3 × Fin 3) ((0,1) : Fin 3 × Fin 3) (1 : ℂ))]
private def broadcastChannel (a : Fin 3) : (Matrix (Fin 3) (Fin 3) ℂ) → (Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ) := fun X =>
  Matrix.trace (P * X) • sigma a + Matrix.trace ((Matrix.single (2 : Fin 3) (2 : Fin 3) (1 : ℂ)) * X) • (Matrix.single ((2,2) : Fin 3 × Fin 3) ((2,2) : Fin 3 × Fin 3) (1 : ℂ))
private def K (a j : Fin 3) : Matrix (Fin 3 × Fin 3) (Fin 3) ℂ :=
  D5.S3.Quantum.Recovery.KrausCompletion.rowReset
    (if j = 2 then ((2,2) : Fin 3 × Fin 3)
     else if a = 0 then (0,0) else if a = 1 then (1,1) else (0,1))
    (1 : Matrix (Fin 3) (Fin 3) ℂ) j

private theorem observable_A : IsPOVM A := by
  let p : Fin 2 → Fin 3 → ℝ := fun x i =>
    if x = 0 then (if i = 2 then 1/4 else 3/4)
    else (if i = 2 then 3/4 else 1/4)
  have heq : A = fun x => Matrix.diagonal (fun i => (p x i : ℂ)) := by
    ext x i j
    fin_cases x <;> fin_cases i <;> fin_cases j <;>
      norm_num [p, A, A0, A1, P, Matrix.diagonal, Matrix.single,
        Fin.ext_iff, -Fin.val_eq_zero_iff, Matrix.one_apply]
  rw [heq]
  apply D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation.diagonal_povm p
  · intro x i
    fin_cases x <;> fin_cases i <;> norm_num [p, Fin.ext_iff, -Fin.val_eq_zero_iff]
  · intro i
    fin_cases i <;> norm_num [p, Fin.sum_univ_succ, Fin.ext_iff, -Fin.val_eq_zero_iff]

set_option maxHeartbeats 800000 in
private theorem kraus_action_formula (a : Fin 3) (X : (Matrix (Fin 3) (Fin 3) ℂ)) :
    (∑ j, K a j * X * (K a j)ᴴ) = broadcastChannel a X := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ]
  fin_cases a <;>
    simp [K, D5.S3.Quantum.Recovery.KrausCompletion.rowReset, broadcastChannel, P, Matrix.diagonal,  sigma, Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.trace_mul_single, Matrix.single_add, add_assoc]

set_option maxHeartbeats 800000 in
private theorem channel_a (a : Fin 3) : IsChannel (broadcastChannel a) := by
  refine ⟨3, K a, ?_, ?_⟩
  · fin_cases a <;> ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [K, D5.S3.Quantum.Recovery.KrausCompletion.rowReset, Matrix.single, Fin.ext_iff, -Fin.val_eq_zero_iff, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_succ]
  · intro X
    simpa only [MatrixMap.of_kraus, LinearMap.sum_apply, LinearMap.coe_mk, AddHom.coe_mk] using (kraus_action_formula a X).symm

private theorem trace_single_left (u : Fin 3 × Fin 3) (E : Matrix (Fin 3) (Fin 3) ℂ) :
    Matrix.trace (Matrix.single u u (1 : ℂ) * (E ⊗ₖ (1 : Matrix (Fin 3) (Fin 3) ℂ))) = E u.1 u.1 := by
  simp [Matrix.trace_single_mul, Matrix.kroneckerMap_apply, Matrix.kronecker]

private theorem trace_single_right (u : Fin 3 × Fin 3) (E : Matrix (Fin 3) (Fin 3) ℂ) :
    Matrix.trace (Matrix.single u u (1 : ℂ) * ((1 : Matrix (Fin 3) (Fin 3) ℂ) ⊗ₖ E)) = E u.2 u.2 := by
  simp [Matrix.trace_single_mul, Matrix.kroneckerMap_apply, Matrix.kronecker]

private theorem broadcast_a (a : Fin 3) : Broadcasts A (broadcastChannel a) := by
  refine ⟨channel_a a, ?_⟩
  intro ρ hρ x
  have htr := hρ.2
  fin_cases a <;> fin_cases x
  all_goals
    simp only [broadcastChannel, Matrix.add_mul, Matrix.smul_mul, trace_add, trace_smul]
    simp [sigma]
  all_goals
    rw [trace_single_left, trace_single_right, trace_single_left, trace_single_right]
  all_goals
    simp [A, A0, A1, P, Matrix.diagonal, Matrix.single, Fin.ext_iff, -Fin.val_eq_zero_iff, Matrix.trace, Matrix.mul_apply, Matrix.diag, Matrix.one_apply, Fin.sum_univ_succ] at *
    ring_nf at *
    try { rw [htr] }

private theorem channel_trace_preserving {Φ : (Matrix (Fin 3) (Fin 3) ℂ) → (Matrix (Fin 3) (Fin 3) ℂ)} (hΦ : IsChannel Φ) :
    ∀ X, Matrix.trace (Φ X) = Matrix.trace X := by
  rcases hΦ with ⟨k, K, hK, hact⟩
  obtain ⟨channel, hchannel⟩ :=
    D5.S3.Quantum.Foundation.FiniteKrausChannel.finite_kraus_quantum_channel K hK
  simp only [MatrixMap.of_kraus, LinearMap.sum_apply, LinearMap.coe_mk, AddHom.coe_mk] at hact
  intro X
  rw [hact, ← hchannel X]
  exact channel.trace_preserving (CStarMatrix.ofMatrix X)

private def rhoPlus : (Matrix (Fin 3) (Fin 3) ℂ) := (1/2 : ℂ) • (rankOneDensity (![1,1,0] : Fin 3 → ℂ))
private def rhoPlus12 : (Matrix (Fin 3) (Fin 3) ℂ) := (1/2 : ℂ) • (rankOneDensity (![0,1,1] : Fin 3 → ℂ))
private def rhoImag01 : (Matrix (Fin 3) (Fin 3) ℂ) := (1/2 : ℂ) • (rankOneDensity (![1, Complex.I, 0] : Fin 3 → ℂ))
private def rhoImag02 : (Matrix (Fin 3) (Fin 3) ℂ) := (1/2 : ℂ) • (rankOneDensity (![1,0, Complex.I] : Fin 3 → ℂ))
private def rhoImag12 : (Matrix (Fin 3) (Fin 3) ℂ) := (1/2 : ℂ) • (rankOneDensity (![0,1, Complex.I] : Fin 3 → ℂ))

private theorem scaled_pure_state (v : (Fin 3) → ℂ) (hv : star v ⬝ᵥ v = 2) :
    IsDensity ((1/2 : ℂ) • (Matrix.vecMulVec v (star v))) := by
  constructor
  · apply Matrix.PosSemidef.smul (Matrix.posSemidef_vecMulVec_self_star v)
    positivity
  · change Matrix.trace ((1/2 : ℂ) • Matrix.vecMulVec v (star v)) = 1
    rw [Matrix.trace_smul, Matrix.trace_vecMulVec, dotProduct_comm]
    rw [hv]
    norm_num

private theorem rhoPlus_state : IsDensity rhoPlus := by
  apply scaled_pure_state
  simp [rhoPlus, rankOneDensity, Matrix.vecMulVec, dotProduct, Fin.sum_univ_succ] <;> norm_num
private theorem rhoPlus02_state : IsDensity (signalProbe 1) := by
  apply scaled_pure_state
  simp [signalProbe, rankOneDensity, Matrix.vecMulVec, dotProduct, Fin.sum_univ_succ] <;> norm_num
private theorem rhoPlus12_state : IsDensity rhoPlus12 := by
  apply scaled_pure_state
  simp [rhoPlus12, rankOneDensity, Matrix.vecMulVec, dotProduct, Fin.sum_univ_succ] <;> norm_num
private theorem rhoImag01_state : IsDensity rhoImag01 := by
  apply scaled_pure_state
  simp [rhoImag01, rankOneDensity, Matrix.vecMulVec, dotProduct, Fin.sum_univ_succ] <;> norm_num
private theorem rhoImag02_state : IsDensity rhoImag02 := by
  apply scaled_pure_state
  simp [rhoImag02, rankOneDensity, Matrix.vecMulVec, dotProduct, Fin.sum_univ_succ] <;> norm_num
private theorem rhoImag12_state : IsDensity rhoImag12 := by
  apply scaled_pure_state
  simp [rhoImag12, rankOneDensity, Matrix.vecMulVec, dotProduct, Fin.sum_univ_succ] <;> norm_num

private theorem nondisturbing_state_P
    (Θ : (Matrix (Fin 3) (Fin 3) ℂ) → (Matrix (Fin 3) (Fin 3) ℂ)) (hΘ : Nondisturbing A Θ) (ρ : (Matrix (Fin 3) (Fin 3) ℂ)) (hρ : IsDensity ρ) :
    Matrix.trace (Θ ρ * P) = Matrix.trace (ρ * P) := by
  have hA0id : A0 = (1/4 : ℂ) • (1 : (Matrix (Fin 3) (Fin 3) ℂ)) + (1/2 : ℂ) • P := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [A0, P, Matrix.diagonal, Matrix.single, Fin.ext_iff, -Fin.val_eq_zero_iff, Matrix.one_apply]
  have htrΘ : Matrix.trace (Θ ρ) = Matrix.trace ρ :=
    channel_trace_preserving hΘ.1 ρ
  have hA := hΘ.2 ρ hρ 0
  change Matrix.trace (Θ ρ * A0) = Matrix.trace (ρ * A0) at hA
  rw [hA0id] at hA
  simp only [Matrix.mul_add, Matrix.mul_smul, trace_add, trace_smul, Matrix.mul_one] at hA
  linear_combination (2 : ℂ) * hA - (1/2 : ℂ) * htrΘ

private theorem basis_state (i : Fin 3) : IsDensity (Matrix.single i i (1 : ℂ)) := by
  constructor
  · rw [← Matrix.diagonal_single]
    apply Matrix.PosSemidef.diagonal
    intro j
    by_cases h : j = i <;> simp [Pi.single_apply, h]
  · exact Matrix.trace_single_eq_same _ _

private theorem nondisturbing_fix_P
    (Θ : (Matrix (Fin 3) (Fin 3) ℂ) → (Matrix (Fin 3) (Fin 3) ℂ)) (hΘ : Nondisturbing A Θ) :
    ∀ X, Matrix.trace (Θ X * P) = Matrix.trace (X * P) := by
  rcases hΘ.1 with ⟨k, Kθ, hKθ, hactθ⟩
  let D : (Matrix (Fin 3) (Fin 3) ℂ) := ∑ j, (Kθ j)ᴴ * P * Kθ j
  have htraceD (X : (Matrix (Fin 3) (Fin 3) ℂ)) : Matrix.trace (Θ X * P) = Matrix.trace (X * D) := by
    rw [hactθ, MatrixMap.Dual.trace_eq,
      D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation.dual_kraus
        (din := 3) (dout := 3) Kθ P]
  have heq (ρ : (Matrix (Fin 3) (Fin 3) ℂ)) (hρ : IsDensity ρ) : Matrix.trace (ρ * D) = Matrix.trace (ρ * P) := by
    rw [← htraceD ρ]
    exact nondisturbing_state_P Θ hΘ ρ hρ
  have h0 := heq (Matrix.single (0 : Fin 3) (0 : Fin 3) (1 : ℂ)) (basis_state 0)
  have h1 := heq (Matrix.single (1 : Fin 3) (1 : Fin 3) (1 : ℂ)) (basis_state 1)
  have h2 := heq (Matrix.single (2 : Fin 3) (2 : Fin 3) (1 : ℂ)) (basis_state 2)
  simp [Matrix.trace, Matrix.mul_apply, Matrix.single, Fin.ext_iff, -Fin.val_eq_zero_iff, Fin.sum_univ_succ] at h0 h1 h2
  have hp01 := heq rhoPlus rhoPlus_state
  have hp02 := heq (signalProbe 1) rhoPlus02_state
  have hp12 := heq rhoPlus12 rhoPlus12_state
  have hi01 := heq rhoImag01 rhoImag01_state
  have hi02 := heq rhoImag02 rhoImag02_state
  have hi12 := heq rhoImag12 rhoImag12_state
  have hsplus : star (![1, 1, 0] : (Fin 3) → ℂ) = (![1, 1, 0] : (Fin 3) → ℂ) := by
    funext i; fin_cases i <;> simp [Pi.star_apply]
  have hs02 : star (![1, 0, 1] : (Fin 3) → ℂ) = (![1, 0, 1] : (Fin 3) → ℂ) := by
    funext i; fin_cases i <;> simp [Pi.star_apply]
  have hs12 : star (![0, 1, 1] : (Fin 3) → ℂ) = (![0, 1, 1] : (Fin 3) → ℂ) := by
    funext i; fin_cases i <;> simp [Pi.star_apply]
  have hsi01 : star (![1, Complex.I, 0] : (Fin 3) → ℂ) = (![1, -Complex.I, 0] : (Fin 3) → ℂ) := by
    funext i; fin_cases i <;> simp [Pi.star_apply]
  have hsi02 : star (![1, 0, Complex.I] : (Fin 3) → ℂ) = (![1, 0, -Complex.I] : (Fin 3) → ℂ) := by
    funext i; fin_cases i <;> simp [Pi.star_apply]
  have hsi12 : star (![0, 1, Complex.I] : (Fin 3) → ℂ) = (![0, 1, -Complex.I] : (Fin 3) → ℂ) := by
    funext i; fin_cases i <;> simp [Pi.star_apply]
  have hrp : rhoPlus = !![(1/2 : ℂ), 1/2, 0; 1/2, 1/2, 0; 0, 0, 0] := by
    change (1/2 : ℂ) • Matrix.vecMulVec (![1, 1, 0] : (Fin 3) → ℂ) (star (![1, 1, 0] : (Fin 3) → ℂ)) = _
    rw [hsplus]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [rhoPlus, rankOneDensity, Matrix.vecMulVec, Matrix.vecMulVec_apply, Pi.star_apply]
  rw [hrp] at hp01
  simp [Matrix.trace, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_succ] at hp01
  simp [signalProbe, rankOneDensity, rhoPlus12, rhoImag01, rhoImag02, rhoImag12, Matrix.vecMulVec, hs02, hs12, hsi01, hsi02, hsi12, Matrix.trace, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_succ] at hp02 hp12 hi01 hi02 hi12
  have hs01 : D 1 0 + D 0 1 = P 1 0 + P 0 1 := by
    linear_combination (2 : ℂ) * hp01 - h0 - h1
  have hd01i : Complex.I * (D 0 1 - D 1 0) = Complex.I * (P 0 1 - P 1 0) := by
    linear_combination (2 : ℂ) * hi01 - h0 - h1
  have hd01 : D 0 1 - D 1 0 = P 0 1 - P 1 0 := by
    apply (mul_left_cancel₀ (by norm_num : (Complex.I : ℂ) ≠ 0))
    exact hd01i
  have hs02 : D 2 0 + D 0 2 = P 2 0 + P 0 2 := by
    linear_combination (2 : ℂ) * hp02 - h0 - h2
  have hd02i : Complex.I * (D 0 2 - D 2 0) = Complex.I * (P 0 2 - P 2 0) := by
    linear_combination (2 : ℂ) * hi02 - h0 - h2
  have hd02 : D 0 2 - D 2 0 = P 0 2 - P 2 0 := by
    apply (mul_left_cancel₀ (by norm_num : (Complex.I : ℂ) ≠ 0))
    exact hd02i
  have hs12 : D 2 1 + D 1 2 = P 2 1 + P 1 2 := by
    linear_combination (2 : ℂ) * hp12 - h1 - h2
  have hd12i : Complex.I * (D 1 2 - D 2 1) = Complex.I * (P 1 2 - P 2 1) := by
    linear_combination (2 : ℂ) * hi12 - h1 - h2
  have hd12 : D 1 2 - D 2 1 = P 1 2 - P 2 1 := by
    apply (mul_left_cancel₀ (by norm_num : (Complex.I : ℂ) ≠ 0))
    exact hd12i
  have hD : D = P := by
    ext i j
    fin_cases i <;> fin_cases j
    · change D 0 0 = P 0 0; exact h0
    · change D 0 1 = P 0 1
      linear_combination (1 / 2 : ℂ) * (hs01 + hd01)
    · change D 0 2 = P 0 2
      linear_combination (1 / 2 : ℂ) * (hs02 + hd02)
    · change D 1 0 = P 1 0
      linear_combination (1 / 2 : ℂ) * (hs01 - hd01)
    · change D 1 1 = P 1 1; exact h1
    · change D 1 2 = P 1 2
      linear_combination (1 / 2 : ℂ) * (hs12 + hd12)
    · change D 2 0 = P 2 0
      linear_combination (1 / 2 : ℂ) * (hs02 - hd02)
    · change D 2 1 = P 2 1
      linear_combination (1 / 2 : ℂ) * (hs12 - hd12)
    · change D 2 2 = P 2 2; exact h2
  intro X
  rw [htraceD, hD]

private theorem state_support_P (T : (Matrix (Fin 3) (Fin 3) ℂ)) (hT : IsDensity T)
    (hTP : Matrix.trace (T * P) = 1) : T = P * T * P := by
  have hQ : (1 - P).PosSemidef := by
    have hdiag : 1 - P = Matrix.diagonal ![(0 : ℂ), 0, 1] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [P, Matrix.diagonal, Matrix.one_apply]
    rw [hdiag]
    apply Matrix.PosSemidef.diagonal
    intro i
    fin_cases i <;> norm_num
  have hzero : Matrix.trace ((1 - P) * T) = 0 := by
    rw [sub_mul, one_mul, Matrix.trace_sub, hT.2, Matrix.trace_mul_comm P T, hTP,
      sub_self]
  have hprod :=
    D5.S3.Quantum.Measurements.FiniteMemoryHistoryCapacity.zero_trace_mul_eq_zero
      (1 - P) T hQ hT.1 hzero
  have hleft : P * T = T :=
    (sub_eq_zero.mp (by simpa only [sub_mul, one_mul] using hprod)).symm
  have hPherm : Pᴴ = P := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [P, Matrix.diagonal, Matrix.conjTranspose_apply]
  have hright : T * P = T := by
    have h := congrArg Matrix.conjTranspose hleft
    simpa only [Matrix.conjTranspose_mul, hT.1.isHermitian.eq, hPherm] using h
  rw [hleft, hright]

private theorem channel_posSemidef {Φ : (Matrix (Fin 3) (Fin 3) ℂ) → (Matrix (Fin 3) (Fin 3) ℂ)} (hΦ : IsChannel Φ)
    {X : (Matrix (Fin 3) (Fin 3) ℂ)} (hX : X.PosSemidef) : (Φ X).PosSemidef := by
  rcases hΦ with ⟨k, K, hK, hact⟩
  obtain ⟨channel, hchannel⟩ :=
    D5.S3.Quantum.Foundation.FiniteKrausChannel.finite_kraus_quantum_channel K hK
  simp only [MatrixMap.of_kraus, LinearMap.sum_apply, LinearMap.coe_mk, AddHom.coe_mk] at hact
  rw [hact, ← hchannel X]
  exact (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm
    (map_nonneg channel.toCompletelyPositiveMap
      (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv hX.nonneg))).posSemidef

private theorem single_trace_nonneg {X : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ}
    (hX : X.PosSemidef) (u : Fin 3 × Fin 3) :
    0 ≤ Matrix.trace (X * Matrix.single u u (1 : ℂ)) := by
  simpa [Matrix.trace_mul_single] using hX.diag_nonneg (i := u)

private theorem comp_fix (a : (Fin 3)) (Θ : (Matrix (Fin 3) (Fin 3) ℂ) → (Matrix (Fin 3) (Fin 3) ℂ)) (hΘ : Nondisturbing A Θ) :
    broadcastChannel a ∘ Θ = broadcastChannel a := by
  funext X
  have hp0 := nondisturbing_fix_P Θ hΘ X
  have hp : Matrix.trace (P * Θ X) = Matrix.trace (P * X) := by
    calc
      Matrix.trace (P * Θ X) = Matrix.trace (Θ X * P) := Matrix.trace_mul_comm _ _
      _ = Matrix.trace (X * P) := hp0
      _ = Matrix.trace (P * X) := Matrix.trace_mul_comm _ _
  have ht := channel_trace_preserving hΘ.1 X
  have hq : Matrix.trace ((Matrix.single (2 : Fin 3) (2 : Fin 3) (1 : ℂ)) * Θ X) = Matrix.trace ((Matrix.single (2 : Fin 3) (2 : Fin 3) (1 : ℂ)) * X) := by
    have hQ : (Matrix.single (2 : Fin 3) (2 : Fin 3) (1 : ℂ)) = (1 : (Matrix (Fin 3) (Fin 3) ℂ)) - P := by ext i j; fin_cases i <;> fin_cases j <;> simp [P, Matrix.diagonal, Matrix.single, Fin.ext_iff, -Fin.val_eq_zero_iff, Matrix.one_apply]
    rw [hQ, Matrix.sub_mul, Matrix.trace_sub, Matrix.sub_mul, Matrix.trace_sub]
    simp only [Matrix.one_mul]
    rw [ht, hp]
  simp [broadcastChannel, hp, hq]

private theorem channels_neq : broadcastChannel 0 ≠ broadcastChannel 1 := by
  intro h
  have he := congrArg (fun F : (Matrix (Fin 3) (Fin 3) ℂ) → (Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ) => F (Matrix.single (0 : Fin 3) (0 : Fin 3) (1 : ℂ))) h
  simp [broadcastChannel, Matrix.trace, Matrix.mul_apply, Matrix.single, Fin.ext_iff, -Fin.val_eq_zero_iff, Fin.sum_univ_succ] at he
  have he00 := congrArg (fun M : (Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ) => M ((0,0) : Fin 3 × Fin 3) ((0,0) : Fin 3 × Fin 3)) he
  have hzero : P 0 0 = 0 := by
    simpa [sigma, Matrix.single, Fin.ext_iff, -Fin.val_eq_zero_iff] using he00
  norm_num [P] at hzero

private theorem lambda_basis (i : (Fin 3)) : broadcastChannel i (Matrix.single (0 : Fin 3) (0 : Fin 3) (1 : ℂ)) = sigma i := by
  have hp : Matrix.trace (P * Matrix.single (0 : Fin 3) (0 : Fin 3) (1 : ℂ)) = 1 := by
    simpa [P] using (Matrix.trace_mul_single P 0 0 (1 : ℂ))
  have hq : Matrix.trace ((Matrix.single (2 : Fin 3) (2 : Fin 3) (1 : ℂ)) * Matrix.single (0 : Fin 3) (0 : Fin 3) (1 : ℂ)) = 0 := by
    simpa [Matrix.single] using (Matrix.trace_mul_single (Matrix.single (2 : Fin 3) (2 : Fin 3) (1 : ℂ)) 0 0 (1 : ℂ))
  simp [broadcastChannel, hp, hq]

private theorem basis_P_trace : Matrix.trace ((Matrix.single (0 : Fin 3) (0 : Fin 3) (1 : ℂ)) * P) = 1 := by
  simpa [P] using (Matrix.trace_single_mul 0 0 (1 : ℂ) P)

private theorem no_lowest : ¬ HasLowest A := by
  intro h
  rcases h with ⟨L, hL, hall⟩
  rcases hall (broadcastChannel 0) (broadcast_a 0) with ⟨Θ0, hΘ0, heq0⟩
  rcases hall (broadcastChannel 1) (broadcast_a 1) with ⟨Θ1, hΘ1, heq1⟩
  have e0 : L = broadcastChannel 0 := by
    rw [heq0, comp_fix 0 Θ0 hΘ0]
  have e1 : L = broadcastChannel 1 := by
    rw [heq1, comp_fix 1 Θ1 hΘ1]
  exact channels_neq (e0.symm.trans e1)

private theorem sigma_gap_pos :
    (1 - ((Matrix.single ((0,0) : Fin 3 × Fin 3) ((0,0) : Fin 3 × Fin 3) (1 : ℂ)) + (Matrix.single ((1,1) : Fin 3 × Fin 3) ((1,1) : Fin 3 × Fin 3) (1 : ℂ)) + (Matrix.single ((0,1) : Fin 3 × Fin 3) ((0,1) : Fin 3 × Fin 3) (1 : ℂ)))).PosSemidef := by
  have heq : (1 - ((Matrix.single ((0,0) : Fin 3 × Fin 3) ((0,0) : Fin 3 × Fin 3) (1 : ℂ)) + (Matrix.single ((1,1) : Fin 3 × Fin 3) ((1,1) : Fin 3 × Fin 3) (1 : ℂ)) + (Matrix.single ((0,1) : Fin 3 × Fin 3) ((0,1) : Fin 3 × Fin 3) (1 : ℂ)))) =
      Matrix.diagonal (fun u : (Fin 3) × (Fin 3) =>
        if u = ((0,0) : Fin 3 × Fin 3) ∨ u = ((1,1) : Fin 3 × Fin 3) ∨ u = ((0,1) : Fin 3 × Fin 3) then (0 : ℂ) else 1) := by
    ext u v
    fin_cases u <;> fin_cases v <;>
      simp [Matrix.single, Fin.ext_iff, -Fin.val_eq_zero_iff, Matrix.diagonal, Matrix.one_apply]
  rw [heq]
  apply Matrix.PosSemidef.diagonal
  intro u
  by_cases h : u = ((0,0) : Fin 3 × Fin 3) ∨ u = ((1,1) : Fin 3 × Fin 3) ∨ u = ((0,1) : Fin 3 × Fin 3) <;> simp [h]

private theorem no_highest : ¬ HasHighest A := by
  intro hh
  rcases hh with ⟨Γ, hΓ, hall⟩
  rcases hall (broadcastChannel 0) (broadcast_a 0) with ⟨Θ0, hΘ0, heq0⟩
  rcases hall (broadcastChannel 1) (broadcast_a 1) with ⟨Θ1, hΘ1, heq1⟩
  rcases hall (broadcastChannel 2) (broadcast_a 2) with ⟨Θ2, hΘ2, heq2⟩
  rcases hΓ.1 with ⟨k, K, hK, hact⟩
  simp only [MatrixMap.of_kraus, LinearMap.sum_apply, LinearMap.coe_mk, AddHom.coe_mk] at hact
  let τ : (Fin 3) → (Matrix (Fin 3) (Fin 3) ℂ) := fun i => (if i = 0 then Θ0 (Matrix.single (0 : Fin 3) (0 : Fin 3) (1 : ℂ)) else if i = 1 then Θ1 (Matrix.single (0 : Fin 3) (0 : Fin 3) (1 : ℂ)) else Θ2 (Matrix.single (0 : Fin 3) (0 : Fin 3) (1 : ℂ)))
  let M : (Fin 3) → (Matrix (Fin 3) (Fin 3) ℂ) := fun i => ∑ j, (K j)ᴴ * (sigma i) * K j
  have hτstate (i : (Fin 3)) : IsDensity (τ i) := by
    fin_cases i
    · dsimp [τ]
      exact ⟨channel_posSemidef hΘ0.1 (basis_state 0).1,
        (channel_trace_preserving hΘ0.1 (Matrix.single (0 : Fin 3) (0 : Fin 3) (1 : ℂ))).trans (basis_state 0).2⟩
    · dsimp [τ]
      exact ⟨channel_posSemidef hΘ1.1 (basis_state 0).1,
        (channel_trace_preserving hΘ1.1 (Matrix.single (0 : Fin 3) (0 : Fin 3) (1 : ℂ))).trans (basis_state 0).2⟩
    · dsimp [τ]
      exact ⟨channel_posSemidef hΘ2.1 (basis_state 0).1,
        (channel_trace_preserving hΘ2.1 (Matrix.single (0 : Fin 3) (0 : Fin 3) (1 : ℂ))).trans (basis_state 0).2⟩
  have hτP (i : (Fin 3)) : Matrix.trace (τ i * P) = 1 := by
    fin_cases i <;> dsimp [τ]
    · simpa [basis_P_trace] using nondisturbing_state_P Θ0 hΘ0 (Matrix.single (0 : Fin 3) (0 : Fin 3) (1 : ℂ)) (basis_state 0)
    · simpa [basis_P_trace] using nondisturbing_state_P Θ1 hΘ1 (Matrix.single (0 : Fin 3) (0 : Fin 3) (1 : ℂ)) (basis_state 0)
    · simpa [basis_P_trace] using nondisturbing_state_P Θ2 hΘ2 (Matrix.single (0 : Fin 3) (0 : Fin 3) (1 : ℂ)) (basis_state 0)
  have hout (i : (Fin 3)) : Γ (τ i) = sigma i := by
    fin_cases i
    · have h := congrArg (fun F : (Matrix (Fin 3) (Fin 3) ℂ) → (Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ) => F (Matrix.single (0 : Fin 3) (0 : Fin 3) (1 : ℂ))) heq0
      simpa [Function.comp_def, τ, lambda_basis] using h.symm
    · have h := congrArg (fun F : (Matrix (Fin 3) (Fin 3) ℂ) → (Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ) => F (Matrix.single (0 : Fin 3) (0 : Fin 3) (1 : ℂ))) heq1
      simpa [Function.comp_def, τ, lambda_basis] using h.symm
    · have h := congrArg (fun F : (Matrix (Fin 3) (Fin 3) ℂ) → (Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ) => F (Matrix.single (0 : Fin 3) (0 : Fin 3) (1 : ℂ))) heq2
      simpa [Function.comp_def, τ, lambda_basis] using h.symm
  have hdual (E : (Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ)) (X : (Matrix (Fin 3) (Fin 3) ℂ)) :
      Matrix.trace (Γ X * E) = Matrix.trace (X * (∑ j, (K j)ᴴ * E * K j)) := by
    rw [hact, Matrix.sum_mul, Matrix.trace_sum]
    rw [Matrix.mul_sum, Matrix.trace_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Matrix.mul_assoc, Matrix.trace_mul_cycle, Matrix.trace_mul_comm]
  have hsingle (i : (Fin 3)) (R : (Matrix (Fin 3) (Fin 3) ℂ)) (hR : R.PosSemidef) :
      0 ≤ Matrix.trace (R * M i) := by
    fin_cases i
    · dsimp [M]
      rw [Matrix.mul_sum, Matrix.trace_sum]
      apply Finset.sum_nonneg
      intro j hj
      calc
        Matrix.trace (R * ((K j)ᴴ * (Matrix.single ((0,0) : Fin 3 × Fin 3) ((0,0) : Fin 3 × Fin 3) (1 : ℂ)) * K j)) =
            Matrix.trace ((K j * R * (K j)ᴴ) * (Matrix.single ((0,0) : Fin 3 × Fin 3) ((0,0) : Fin 3 × Fin 3) (1 : ℂ))) := by
              calc
                _ = Matrix.trace (((K j)ᴴ * (Matrix.single ((0,0) : Fin 3 × Fin 3) ((0,0) : Fin 3 × Fin 3) (1 : ℂ)) * K j) * R) := Matrix.trace_mul_comm _ _
                _ = Matrix.trace ((K j)ᴴ * (Matrix.single ((0,0) : Fin 3 × Fin 3) ((0,0) : Fin 3 × Fin 3) (1 : ℂ)) * (K j * R)) := by simp [Matrix.mul_assoc]
                _ = Matrix.trace ((K j * R) * (K j)ᴴ * (Matrix.single ((0,0) : Fin 3 × Fin 3) ((0,0) : Fin 3 × Fin 3) (1 : ℂ))) := Matrix.trace_mul_cycle _ _ _
                _ = Matrix.trace ((K j * R * (K j)ᴴ) * (Matrix.single ((0,0) : Fin 3 × Fin 3) ((0,0) : Fin 3 × Fin 3) (1 : ℂ))) := by simp [Matrix.mul_assoc]
        _ ≥ 0 := single_trace_nonneg (hR.mul_mul_conjTranspose_same (K j)) ((0,0) : Fin 3 × Fin 3)
    · dsimp [M]
      rw [Matrix.mul_sum, Matrix.trace_sum]
      apply Finset.sum_nonneg
      intro j hj
      calc
        Matrix.trace (R * ((K j)ᴴ * (Matrix.single ((1,1) : Fin 3 × Fin 3) ((1,1) : Fin 3 × Fin 3) (1 : ℂ)) * K j)) =
            Matrix.trace ((K j * R * (K j)ᴴ) * (Matrix.single ((1,1) : Fin 3 × Fin 3) ((1,1) : Fin 3 × Fin 3) (1 : ℂ))) := by
              calc
                _ = Matrix.trace (((K j)ᴴ * (Matrix.single ((1,1) : Fin 3 × Fin 3) ((1,1) : Fin 3 × Fin 3) (1 : ℂ)) * K j) * R) := Matrix.trace_mul_comm _ _
                _ = Matrix.trace ((K j)ᴴ * (Matrix.single ((1,1) : Fin 3 × Fin 3) ((1,1) : Fin 3 × Fin 3) (1 : ℂ)) * (K j * R)) := by simp [Matrix.mul_assoc]
                _ = Matrix.trace ((K j * R) * (K j)ᴴ * (Matrix.single ((1,1) : Fin 3 × Fin 3) ((1,1) : Fin 3 × Fin 3) (1 : ℂ))) := Matrix.trace_mul_cycle _ _ _
                _ = Matrix.trace ((K j * R * (K j)ᴴ) * (Matrix.single ((1,1) : Fin 3 × Fin 3) ((1,1) : Fin 3 × Fin 3) (1 : ℂ))) := by simp [Matrix.mul_assoc]
        _ ≥ 0 := single_trace_nonneg (hR.mul_mul_conjTranspose_same (K j)) ((1,1) : Fin 3 × Fin 3)
    · dsimp [M]
      rw [Matrix.mul_sum, Matrix.trace_sum]
      apply Finset.sum_nonneg
      intro j hj
      calc
        Matrix.trace (R * ((K j)ᴴ * (Matrix.single ((0,1) : Fin 3 × Fin 3) ((0,1) : Fin 3 × Fin 3) (1 : ℂ)) * K j)) =
            Matrix.trace ((K j * R * (K j)ᴴ) * (Matrix.single ((0,1) : Fin 3 × Fin 3) ((0,1) : Fin 3 × Fin 3) (1 : ℂ))) := by
              calc
                _ = Matrix.trace (((K j)ᴴ * (Matrix.single ((0,1) : Fin 3 × Fin 3) ((0,1) : Fin 3 × Fin 3) (1 : ℂ)) * K j) * R) := Matrix.trace_mul_comm _ _
                _ = Matrix.trace ((K j)ᴴ * (Matrix.single ((0,1) : Fin 3 × Fin 3) ((0,1) : Fin 3 × Fin 3) (1 : ℂ)) * (K j * R)) := by simp [Matrix.mul_assoc]
                _ = Matrix.trace ((K j * R) * (K j)ᴴ * (Matrix.single ((0,1) : Fin 3 × Fin 3) ((0,1) : Fin 3 × Fin 3) (1 : ℂ))) := Matrix.trace_mul_cycle _ _ _
                _ = Matrix.trace ((K j * R * (K j)ᴴ) * (Matrix.single ((0,1) : Fin 3 × Fin 3) ((0,1) : Fin 3 × Fin 3) (1 : ℂ))) := by simp [Matrix.mul_assoc]
        _ ≥ 0 := single_trace_nonneg (hR.mul_mul_conjTranspose_same (K j)) ((0,1) : Fin 3 × Fin 3)
  have hPproj : P * P = P := by
    ext r c; fin_cases r <;> fin_cases c <;>
      simp [P, Matrix.diagonal, Matrix.mul_apply, Fin.sum_univ_succ]
  have hPherm : Pᴴ = P := by
    ext r c; fin_cases r <;> fin_cases c <;> simp [P, Matrix.diagonal, Matrix.conjTranspose_apply]
  have hsupport (i : (Fin 3)) : τ i = P * τ i * P :=
    state_support_P (τ i) (hτstate i) (hτP i)
  have hRpos (i : (Fin 3)) : (P - τ i).PosSemidef := by
    have hone := density_le_one (hτstate i).1 (hτstate i).2
    have hconj := hone.conjTranspose_mul_mul_same P
    have heq : Pᴴ * (1 - τ i) * P = P - τ i := by
      rw [hPherm]
      calc
        P * (1 - τ i) * P = P * P - (P * τ i) * P := by
          rw [Matrix.mul_sub, Matrix.sub_mul]
          simp [Matrix.mul_one]
        _ = P - τ i := by rw [hPproj, ← hsupport i]
    rw [← heq]
    exact hconj
  have hsigma_trace (i : (Fin 3)) : Matrix.trace (sigma i) = 1 := by
    fin_cases i <;> simp [sigma, Matrix.trace_single_eq_same]
  have hsigma_idem (i : (Fin 3)) : sigma i * sigma i = sigma i := by
    fin_cases i
    · change (Matrix.single ((0,0) : Fin 3 × Fin 3) ((0,0) : Fin 3 × Fin 3) (1 : ℂ)) * (Matrix.single ((0,0) : Fin 3 × Fin 3) ((0,0) : Fin 3 × Fin 3) (1 : ℂ)) = (Matrix.single ((0,0) : Fin 3 × Fin 3) ((0,0) : Fin 3 × Fin 3) (1 : ℂ))
      ext u v; fin_cases u <;> fin_cases v <;>
        simp [Matrix.single, Fin.ext_iff, -Fin.val_eq_zero_iff, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_succ]
    · change (Matrix.single ((1,1) : Fin 3 × Fin 3) ((1,1) : Fin 3 × Fin 3) (1 : ℂ)) * (Matrix.single ((1,1) : Fin 3 × Fin 3) ((1,1) : Fin 3 × Fin 3) (1 : ℂ)) = (Matrix.single ((1,1) : Fin 3 × Fin 3) ((1,1) : Fin 3 × Fin 3) (1 : ℂ))
      ext u v; fin_cases u <;> fin_cases v <;>
        simp [Matrix.single, Fin.ext_iff, -Fin.val_eq_zero_iff, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_succ]
    · change (Matrix.single ((0,1) : Fin 3 × Fin 3) ((0,1) : Fin 3 × Fin 3) (1 : ℂ)) * (Matrix.single ((0,1) : Fin 3 × Fin 3) ((0,1) : Fin 3 × Fin 3) (1 : ℂ)) = (Matrix.single ((0,1) : Fin 3 × Fin 3) ((0,1) : Fin 3 × Fin 3) (1 : ℂ))
      ext u v; fin_cases u <;> fin_cases v <;>
        simp [Matrix.single, Fin.ext_iff, -Fin.val_eq_zero_iff, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_succ]
  have htrM (i : (Fin 3)) : Matrix.trace (τ i * M i) = 1 := by
    calc
      Matrix.trace (τ i * M i) = Matrix.trace (Γ (τ i) * sigma i) := by
        simpa [M] using (hdual (sigma i) (τ i)).symm
      _ = Matrix.trace (sigma i) := by rw [hout i, hsigma_idem]
      _ = 1 := hsigma_trace i
  have hineq (i : (Fin 3)) : 1 ≤ Matrix.trace (P * M i) := by
    have hnon := hsingle i (P - τ i) (hRpos i)
    have heq : Matrix.trace (P * M i) =
        Matrix.trace (τ i * M i) + Matrix.trace ((P - τ i) * M i) := by
      rw [Matrix.sub_mul, Matrix.trace_sub]
      ring
    calc
      (1 : ℂ) ≤ 1 + Matrix.trace ((P - τ i) * M i) := by
        have h := add_le_add_right hnon (1 : ℂ)
        simpa [add_comm] using h
      _ = Matrix.trace (P * M i) := by rw [← htrM i, heq]
  have hN : (1 - (M 0 + M 1 + M 2)).PosSemidef := by
    have hraw := Matrix.posSemidef_sum (Finset.univ : Finset (Fin k))
      (fun j _ => sigma_gap_pos.conjTranspose_mul_mul_same (K j))
    have heq : 1 - (M 0 + M 1 + M 2) =
        ∑ j, (K j)ᴴ * (1 - ((Matrix.single ((0,0) : Fin 3 × Fin 3) ((0,0) : Fin 3 × Fin 3) (1 : ℂ)) + (Matrix.single ((1,1) : Fin 3 × Fin 3) ((1,1) : Fin 3 × Fin 3) (1 : ℂ)) + (Matrix.single ((0,1) : Fin 3 × Fin 3) ((0,1) : Fin 3 × Fin 3) (1 : ℂ)))) * K j := by
      rw [← hK]
      simp [M, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_add, Matrix.add_mul, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, sigma]
    rw [heq]
    exact hraw
  have hPN : 0 ≤ Matrix.trace (P * (1 - (M 0 + M 1 + M 2))) := by
    have h0 := hN.diag_nonneg (i := (0 : (Fin 3)))
    have h1 := hN.diag_nonneg (i := (1 : (Fin 3)))
    simpa [P, Matrix.trace, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_succ, add_assoc] using add_nonneg h0 h1
  have hsumupper : Matrix.trace (P * M 0) + Matrix.trace (P * M 1) +
      Matrix.trace (P * M 2) ≤ 2 := by
    have hdiff : Matrix.trace (P * (1 - (M 0 + M 1 + M 2))) =
        Matrix.trace P - (Matrix.trace (P * M 0) + Matrix.trace (P * M 1) +
          Matrix.trace (P * M 2)) := by
      rw [Matrix.mul_sub, Matrix.trace_sub]
      simp [Matrix.mul_add, trace_add]
    have hle : Matrix.trace (P * M 0) + Matrix.trace (P * M 1) +
        Matrix.trace (P * M 2) ≤ Matrix.trace P := by
      apply sub_nonneg.mp
      rw [← hdiff]
      exact hPN
    have htrP : Matrix.trace P = (2 : ℂ) := by
      norm_num [P, Matrix.diagonal, Matrix.trace, Fin.sum_univ_succ]
    simpa [htrP] using hle
  have hsumlower : (3 : ℂ) ≤ Matrix.trace (P * M 0) + Matrix.trace (P * M 1) +
      Matrix.trace (P * M 2) := by
    have h01 := add_le_add (hineq 0) (hineq 1)
    have h012 := add_le_add h01 (hineq 2)
    norm_num at h012
    simpa [add_assoc] using h012
  have : (3 : ℂ) ≤ 2 := le_trans hsumlower hsumupper
  norm_num at this

def claim : Prop :=
  ∀ (d m : ℕ) (A' : Fin m → Matrix (Fin d) (Fin d) ℂ),
    IsPOVM A' → (∃ broadcastChannel, Broadcasts A' broadcastChannel) → HasHighest A' ∨ HasLowest A'

theorem result : ¬ claim := by
  intro hc
  have hn : ∃ broadcastChannel, Broadcasts A broadcastChannel := ⟨broadcastChannel 0, broadcast_a 0⟩
  have he := hc 3 2 A observable_A hn
  cases he with
  | inl hh => exact no_highest hh
  | inr hl => exact no_lowest hl

end

end D5.S3.Quantum.Measurements.BroadcastingChannelExtremaRefutation
