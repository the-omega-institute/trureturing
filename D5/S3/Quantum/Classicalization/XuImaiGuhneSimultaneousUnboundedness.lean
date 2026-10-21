/- GID: D5/S3/Quantum/Classicalization/XuImaiGuhneSimultaneousUnboundedness
   generality: I
   mirror-B: D5/B/S3/Quantum/Classicalization/XuImaiGuhneSimultaneousUnboundedness
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Both classicalization negativity gaps are unbounded with a qubit measured party. -/

/-
admission_basis: open-problem-resolution (#19638; Proved).
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19716.
The claim retains the density and POVM conditions explicitly; proofs use the frozen
IsDensity and IsPOVM owners. The two are definitionally the displayed conditions.
The family is a normalized maximally entangled factor tensor an unnormalized W vector.
Rank-one POVM refinement gives a uniform output bound, attained by two orthogonal flags.
The finite matrix identities are algebraic ingredients of this symbolic theorem over all
finite POVMs, register dimensions and amplification parameters; no checker or enumeration is defined.
All proof declarations below are conservatively bind-only after inlining the other helpers.
No escape witness is claimed; result is the external settling result.
Frozen declaration identities (D labels below):
D1: D5/S3/Quantum/Dynamics/KickedIsingNegativityRefutation; D5.S3.Quantum.Dynamics.KickedIsingNegativityRefutation.partialTranspose; statement_id: sha256:2373e14505428583f492752adc05d104ae8b1567265ff8182e03646de824c089.
D2: D5/S3/Quantum/Entanglement/ConicalDesignConcurrenceComparability; D5.S3.Quantum.Entanglement.ConicalDesignConcurrenceComparability.traceNorm_smul_nonneg; statement_id: sha256:4e1e2463b054d4f1a17a47dfa173be720d81b8370e9189ac369460319c5840c1.
D3: D5/S3/Quantum/Entanglement/EnergyRestrictedUnitaryEncodingRefutation; D5.S3.Quantum.Entanglement.EnergyRestrictedUnitaryEncodingRefutation.IsPOVM; statement_id: sha256:df0cbe508ee3118bb0f027530ccb3cca3db2b6c06f7328137344f4eafae68b67.
D4: D5/S3/Quantum/Entanglement/GHZMeasureBiseparableBound; D5.S3.Quantum.Entanglement.GHZMeasureBiseparableBound.IsDensity; statement_id: sha256:fc9bb0824d5818ff419f72f26095faecc04e62ab59bf26f4f2bcefbb2d380448.
D5: D5/S3/Quantum/Foundation/FiniteTraceDistance; D5.S3.Quantum.Foundation.FiniteTraceDistance.traceNorm; statement_id: sha256:12ad034b5758446e6d628c75121b3ad5f0c80bb305937e8c9ff87e82076bc059.
D6: D5/S3/Quantum/Foundation/FiniteTraceDistance; D5.S3.Quantum.Foundation.FiniteTraceDistance.traceNorm._proof_1; statement_id: sha256:b1586fdd8f90368f29693bf2d79bbde6eef95de7877836ce053c092745767dcb.
D7: D5/S3/Quantum/Foundation/FiniteTraceDistance; D5.S3.Quantum.Foundation.FiniteTraceDistance.traceNorm._proof_2; statement_id: sha256:2c4ba5b5c99b826fb97b25dec25e9c500d187206dfe78430a0de7fd11c71bb2b.
D8: D5/S3/Quantum/Foundation/FiniteTraceDistance; D5.S3.Quantum.Foundation.FiniteTraceDistance.traceNorm._proof_7; statement_id: sha256:5f854fd7eee62349e53f46e6718cdea507d64df8d2f6b1e2ba8e1da15cd9898c.
D9: D5/S3/Quantum/Foundation/FiniteTraceDistance; D5.S3.Quantum.Foundation.FiniteTraceDistance.traceNorm_add_le; statement_id: sha256:3db8d0cc1aa28c78624e69d989ca938ee9442b2409e1ba0ba39d593ce49d5512.
D10: D5/S3/Quantum/Foundation/FiniteTraceDistance; D5.S3.Quantum.Foundation.FiniteTraceDistance.traceNorm_nonneg; statement_id: sha256:7412f30d565d9b30ebbf77bf0f5b93d44fe0082f8be41fd64fea60f00cdf2dfa.
D11: D5/S3/Quantum/Foundation/FiniteTraceDistance; D5.S3.Quantum.Foundation.FiniteTraceDistance.traceNorm_of_posSemidef; statement_id: sha256:4f19dad9c3563d9aba3fa6f97f41f0e49ed46af1457c14f015225ae27d019565.
D12: D5/S3/Quantum/PureState/PureStateHandshake; D5.S3.Quantum.PureState.PureStateHandshake.rankOneDensity; statement_id: sha256:e18ab4fd557d4917e344a15c06172fc321b99eb187307a88fe4c7fa4f8a28bf3.
D13: D5/S3/Quantum/QuantumChannels/ConcealmentKernelNecessityRefutation; D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation.IsPOVM; statement_id: sha256:218e2b42c4dc29468db56af33ad277eb32b8ed575533012439ed233131c5efa1.
D14: D5/S3/Quantum/QuantumChannels/ConcealmentKernelNecessityRefutation; D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation.diagonal_povm; statement_id: sha256:de0639eb7d2cc0e2744e5c02a6801acaa920144435fb7dd8831281ad678d7430.
D15: D5/S3/Quantum/Schatten/TraceNorm; D5.S3.Quantum.Schatten.TraceNorm.transitionMass_sq; statement_id: sha256:a2d0a838066e82e6b9dbed2c00ea904afe5a9ae566ce8d089852d367718f9fa6.
D16: D5/S3/QuantumBounds/NegativityReductionInclusionRefutation; D5.S3.QuantumBounds.NegativityReductionInclusionRefutation.negativity; statement_id: sha256:932bdbca4832f6dd38397cdf78e346f0e36053567523469e9d1fe86e953bddbb.
D17: D5/S3/QuantumBounds/NegativityReductionInclusionRefutation; D5.S3.QuantumBounds.NegativityReductionInclusionRefutation.negativity._proof_1; statement_id: sha256:1c37731a584aa58542ad6f9a27cf2a0bc0049379c3c1d57891030072199f0b85.
D18: D5/S3/QuantumChannels/SchurChannelMixedUnitaryDistance; D5.S3.QuantumChannels.SchurChannelMixedUnitaryDistance.reindex_traceNorm; statement_id: sha256:2422ccb9af655e75065a2ca7f28f6fdcc73bda08849c764524e19f7de31b786b.
D19: D5/S3/Weil/ZetaLinear/PosIndex; RHLinalg.frobSq; statement_id: sha256:87344d8035a8c18278b7631968fd9b17dbe3a4221dfb10f55432779f1064e116.
Toolkit.traceNorm_kronecker: proof_shape: bind-only; escape_witness: none; frozen_dependencies: D5; consumers: Toolkit.pure_partialTranspose_norm,WChannel.refined_output_norm_bound,Amplification.amplify_normC,Amplification.amplify_normA,Amplification.amplify_normB,BaseValues.decodedRaw_norms.
Toolkit.traceNorm_rows: proof_shape: bind-only; escape_witness: none; frozen_dependencies: D5,D6,D7,D8; consumers: Toolkit.pure_partialTranspose_norm.
Toolkit.pure_partialTranspose_norm: proof_shape: bind-only; escape_witness: none; frozen_dependencies: D5,D6,D7,D8; consumers: Toolkit.branchCoeff_norm,Amplification.phiRaw_pt_norm.
Toolkit.branchCoeff: proof_shape: bind-only; escape_witness: none; frozen_dependencies: none; consumers: Toolkit.traceNorm_branchCoeff,Toolkit.branchCoeff_norm,WChannel.chi,WChannel.chi_norm.
Toolkit.traceNorm_branchCoeff: proof_shape: bind-only; escape_witness: none; frozen_dependencies: D5,D10,D15,D19; consumers: Toolkit.branchCoeff_norm.
Toolkit.branchCoeff_norm: proof_shape: bind-only; escape_witness: none; frozen_dependencies: D5,D6,D7,D8,D10,D15,D19; consumers: WChannel.chi_norm.
Toolkit.traceNorm_submatrix_equiv: proof_shape: bind-only; escape_witness: none; frozen_dependencies: D5,D18; consumers: Normalization.normC_relabel,Normalization.normA_relabel,Normalization.normB_relabel,WChannel.output_normB_le,WChannel.output_normA_le,Amplification.amplify_normC,Amplification.amplify_normA,Amplification.amplify_normB,BaseValues.decodedRaw_norms.
tripartiteNegativity: proof_shape: bind-only; escape_witness: none; frozen_dependencies: D16; consumers: delta,deltaTilde,Normalization.tripartite_eq,Normalization.tripartite_relabel,delta_eq_of_optimum,Family.family_initial,Family.family_all_channel_bound,Family.family_attains,Family.family_discarded_value,Family.finite_family_data.
branch: proof_shape: bind-only; escape_witness: none; frozen_dependencies: none; consumers: classicalize,deltaTilde,Normalization.classicalize_smul,WChannel.branch_wRaw_rankOne,WChannel.branch_sum,WChannel.classicalize_refinement,WChannel.computational_output,WChannel.branch_wRaw_one,BaseValues.decodedRaw_classicalize,Family.discarded,Family.discarded_classicalize,Family.discarded_wRaw.
classicalize: proof_shape: bind-only; escape_witness: none; frozen_dependencies: none; consumers: delta,Normalization.classicalize_relabel,Normalization.classicalize_smul,WChannel.classicalize_refinement,WChannel.output_register_pos,WChannel.output_normB_le,WChannel.output_normA_le,WChannel.computational_output,WChannel.output_normC_eq,BaseValues.flagRaw_norms,BaseValues.decodedRaw_classicalize,BaseValues.decodedRaw_norms,delta_eq_of_optimum,Family.classicalize_amplify,Family.family_all_channel_bound,Family.family_attains,Family.discarded_classicalize,Family.family_discarded,Family.finite_family_data.
delta: proof_shape: bind-only; escape_witness: none; frozen_dependencies: D16; consumers: claim,delta_eq_of_optimum,claim_of_family,Family.finite_family_data.
deltaTilde: proof_shape: bind-only; escape_witness: none; frozen_dependencies: D16; consumers: claim,claim_of_family,Family.finite_family_data.
claim: proof_shape: bind-only; escape_witness: none; frozen_dependencies: D16; consumers: claim_of_family,result.
Normalization.normC: proof_shape: bind-only; escape_witness: none; frozen_dependencies: D1,D5; consumers: Normalization.tripartite_eq,Normalization.normC_smul,Normalization.normC_relabel,Normalization.tripartite_relabel,BaseValues.wRaw_norms,BaseValues.flagRaw_norms,BaseValues.decodedRaw_norms,Family.family_initial,Family.family_all_channel_bound,Family.family_attains,Family.family_discarded_value.
Normalization.normA: proof_shape: bind-only; escape_witness: none; frozen_dependencies: D1,D5; consumers: Normalization.tripartite_eq,Normalization.normA_smul,Normalization.normA_relabel,Normalization.tripartite_relabel,BaseValues.wRaw_norms,BaseValues.flagRaw_norms,BaseValues.decodedRaw_norms,Family.family_initial,Family.family_all_channel_bound,Family.family_attains,Family.family_discarded_value.
Normalization.normB: proof_shape: bind-only; escape_witness: none; frozen_dependencies: D1,D5; consumers: Normalization.tripartite_eq,Normalization.normB_smul,Normalization.normB_relabel,Normalization.tripartite_relabel,BaseValues.wRaw_norms,BaseValues.flagRaw_norms,BaseValues.decodedRaw_norms,Family.family_initial,Family.family_all_channel_bound,Family.family_attains,Family.family_discarded_value.
Normalization.tripartite_eq: proof_shape: bind-only; escape_witness: none; frozen_dependencies: D1,D5,D16,D17; consumers: Normalization.tripartite_relabel,Family.family_initial,Family.family_all_channel_bound,Family.family_attains,Family.family_discarded_value.
Normalization.normC_smul: proof_shape: bind-only; escape_witness: none; frozen_dependencies: D1,D2,D5; consumers: Family.family_initial,Family.family_all_channel_bound,Family.family_attains,Family.family_discarded_value.
Normalization.normA_smul: proof_shape: bind-only; escape_witness: none; frozen_dependencies: D1,D2,D5; consumers: Family.family_initial,Family.family_all_channel_bound,Family.family_attains,Family.family_discarded_value.
Normalization.normB_smul: proof_shape: bind-only; escape_witness: none; frozen_dependencies: D1,D2,D5; consumers: Family.family_initial,Family.family_all_channel_bound,Family.family_attains,Family.family_discarded_value.
Normalization.normC_relabel: proof_shape: bind-only; escape_witness: none; frozen_dependencies: D1,D5,D18; consumers: Normalization.tripartite_relabel.
Normalization.normA_relabel: proof_shape: bind-only; escape_witness: none; frozen_dependencies: D1,D5,D18; consumers: Normalization.tripartite_relabel.
Normalization.normB_relabel: proof_shape: bind-only; escape_witness: none; frozen_dependencies: D1,D5,D18; consumers: Normalization.tripartite_relabel.
Normalization.tripartite_relabel: proof_shape: bind-only; escape_witness: none; frozen_dependencies: D1,D5,D16,D17,D18; consumers: Family.finite_family_data.
Normalization.state_relabel: proof_shape: bind-only; escape_witness: none; frozen_dependencies: D4; consumers: Family.finite_family_data.
Normalization.classicalize_relabel: proof_shape: bind-only; escape_witness: none; frozen_dependencies: none; consumers: Family.finite_family_data.
Normalization.classicalize_smul: proof_shape: bind-only; escape_witness: none; frozen_dependencies: none; consumers: Family.family_all_channel_bound,Family.family_attains,Family.family_discarded.
Refinement.povm_rankOne_refinement: proof_shape: bind-only; escape_witness: none; frozen_dependencies: none; consumers: WChannel.output_normB_le,WChannel.output_normA_le,WChannel.output_normC_eq.
Numerics.wVec: proof_shape: bind-only; escape_witness: none; frozen_dependencies: none; consumers: Numerics.wRaw,Numerics.wAbs_square,WChannel.branch_wRaw_rankOne,WChannel.computational_output,WChannel.branch_wRaw_one,BaseValues.wRaw_trace,BaseValues.wVec_cyclic,BaseValues.wRaw_norms,BaseValues.decodedRaw_classicalize,Family.family_state.
Numerics.wRaw: proof_shape: bind-only; escape_witness: none; frozen_dependencies: D12; consumers: Numerics.wCut,Numerics.wAbs_square,WChannel.branch_wRaw_rankOne,WChannel.classicalize_refinement,WChannel.output_register_pos,WChannel.output_normB_le,WChannel.output_normA_le,WChannel.computational_output,WChannel.branch_wRaw_one,WChannel.output_normC_eq,BaseValues.wRaw_trace,BaseValues.wRaw_norms,BaseValues.flagRaw_norms,BaseValues.decodedRaw_classicalize,BaseValues.decodedRaw_norms,Family.family,Family.family_state,Family.family_initial,Family.family_all_channel_bound,Family.family_attains,Family.discarded_wRaw,Family.family_discarded.
Numerics.wCut: proof_shape: bind-only; escape_witness: none; frozen_dependencies: D12; consumers: Numerics.wAbs_square,Numerics.wCut_norm,BaseValues.wRaw_norms.
Numerics.wAbs: proof_shape: bind-only; escape_witness: none; frozen_dependencies: D12; consumers: Numerics.wAbs_pos,Numerics.wAbs_square,Numerics.wCut_norm.
Numerics.wAbs_pos: proof_shape: bind-only; escape_witness: none; frozen_dependencies: D12; consumers: Numerics.wCut_norm.
Numerics.wAbs_square: proof_shape: bind-only; escape_witness: none; frozen_dependencies: D1,D12; consumers: Numerics.wCut_norm.
Numerics.wCut_norm: proof_shape: bind-only; escape_witness: none; frozen_dependencies: D1,D5,D6,D7,D8,D12; consumers: BaseValues.wRaw_norms.
Numerics.reducedRaw: proof_shape: bind-only; escape_witness: none; frozen_dependencies: D12; consumers: Numerics.reducedAbs_square,Numerics.reducedRaw_norm,WChannel.branch_wRaw_one,BaseValues.decodedRaw,BaseValues.decodedRaw_classicalize,BaseValues.decodedRaw_norms,Family.discarded_wRaw.
Numerics.reducedAbs: proof_shape: bind-only; escape_witness: none; frozen_dependencies: D12; consumers: Numerics.reducedAbs_pos,Numerics.reducedAbs_square,Numerics.reducedRaw_norm.
Numerics.reducedAbs_pos: proof_shape: bind-only; escape_witness: none; frozen_dependencies: D12; consumers: Numerics.reducedRaw_norm.
Numerics.reducedAbs_square: proof_shape: bind-only; escape_witness: none; frozen_dependencies: D1,D12; consumers: Numerics.reducedRaw_norm.
Numerics.reducedRaw_norm: proof_shape: bind-only; escape_witness: none; frozen_dependencies: D1,D5,D6,D7,D8,D12; consumers: BaseValues.decodedRaw_norms.
Numerics.flagRaw: proof_shape: bind-only; escape_witness: none; frozen_dependencies: D12; consumers: Numerics.flagCutB,Numerics.flagAbsB_square,WChannel.computational_output,BaseValues.flagRaw_norms,Family.family_attains.
Numerics.flagCutB: proof_shape: bind-only; escape_witness: none; frozen_dependencies: D12; consumers: Numerics.flagAbsB_square,Numerics.flagCutB_norm,BaseValues.flagRaw_norms.
Numerics.flagAbsB: proof_shape: bind-only; escape_witness: none; frozen_dependencies: none; consumers: Numerics.flagAbsB_pos,Numerics.flagAbsB_square,Numerics.flagCutB_norm.
Numerics.flagAbsB_pos: proof_shape: bind-only; escape_witness: none; frozen_dependencies: none; consumers: Numerics.flagCutB_norm.
Numerics.flagAbsB_square: proof_shape: bind-only; escape_witness: none; frozen_dependencies: D1,D12; consumers: Numerics.flagCutB_norm.
Numerics.flagCutB_norm: proof_shape: bind-only; escape_witness: none; frozen_dependencies: D1,D5,D6,D7,D8,D12; consumers: BaseValues.flagRaw_norms.
WChannel.chi: proof_shape: bind-only; escape_witness: none; frozen_dependencies: none; consumers: WChannel.branch_wRaw_rankOne,WChannel.chi_norm,WChannel.chi_trace,WChannel.classicalize_refinement,WChannel.output_register_pos,WChannel.chi_swap,WChannel.refined_output_norm_bound,WChannel.output_normB_le,WChannel.output_normA_le,WChannel.output_normC_eq.
WChannel.branch_wRaw_rankOne: proof_shape: bind-only; escape_witness: none; frozen_dependencies: D12; consumers: WChannel.classicalize_refinement.
WChannel.chi_norm: proof_shape: bind-only; escape_witness: none; frozen_dependencies: D1,D5,D6,D7,D8,D10,D12,D15,D19; consumers: WChannel.refined_output_norm_bound.
WChannel.chi_trace: proof_shape: bind-only; escape_witness: none; frozen_dependencies: D12; consumers: WChannel.output_normC_eq.
WChannel.branch_sum: proof_shape: bind-only; escape_witness: none; frozen_dependencies: none; consumers: WChannel.classicalize_refinement.
WChannel.classicalize_refinement: proof_shape: bind-only; escape_witness: none; frozen_dependencies: D12; consumers: WChannel.output_register_pos,WChannel.output_normB_le,WChannel.output_normA_le,WChannel.output_normC_eq.
WChannel.output_register_pos: proof_shape: bind-only; escape_witness: none; frozen_dependencies: D1,D12; consumers: WChannel.output_normC_eq.
WChannel.moveRegister: proof_shape: bind-only; escape_witness: none; frozen_dependencies: none; consumers: WChannel.output_normB_le,WChannel.output_normA_le,BaseValues.decodedRaw_norms.
WChannel.chi_swap: proof_shape: bind-only; escape_witness: none; frozen_dependencies: none; consumers: WChannel.output_normA_le.
WChannel.traceNorm_sum_le: proof_shape: bind-only; escape_witness: none; frozen_dependencies: D5,D6,D7,D8,D9; consumers: WChannel.refined_output_norm_bound.
WChannel.refined_output_norm_bound: proof_shape: bind-only; escape_witness: none; frozen_dependencies: D1,D4,D5,D6,D7,D8,D9,D10,D11,D12,D15,D19; consumers: WChannel.output_normB_le,WChannel.output_normA_le.
WChannel.output_normB_le: proof_shape: bind-only; escape_witness: none; frozen_dependencies: D1,D3,D4,D5,D6,D7,D8,D9,D10,D11,D12,D15,D18,D19; consumers: Family.family_all_channel_bound.
WChannel.output_normA_le: proof_shape: bind-only; escape_witness: none; frozen_dependencies: D1,D3,D4,D5,D6,D7,D8,D9,D10,D11,D12,D15,D18,D19; consumers: Family.family_all_channel_bound.
WChannel.computational: proof_shape: bind-only; escape_witness: none; frozen_dependencies: D12; consumers: WChannel.computational_povm,WChannel.computational_state,WChannel.computational_output,BaseValues.flagRaw_norms,BaseValues.decodedRaw_classicalize,BaseValues.decodedRaw_norms,Family.family_attains,Family.discarded_classicalize,Family.family_discarded,Family.finite_family_data.
WChannel.computational_povm: proof_shape: bind-only; escape_witness: none; frozen_dependencies: D3,D12,D13,D14; consumers: BaseValues.flagRaw_norms,BaseValues.decodedRaw_norms,Family.finite_family_data.
WChannel.computational_state: proof_shape: bind-only; escape_witness: none; frozen_dependencies: D4,D12; consumers: BaseValues.flagRaw_norms,BaseValues.decodedRaw_norms,Family.finite_family_data.
WChannel.computational_output: proof_shape: bind-only; escape_witness: none; frozen_dependencies: D12; consumers: BaseValues.flagRaw_norms,Family.family_attains.
WChannel.branch_wRaw_one: proof_shape: bind-only; escape_witness: none; frozen_dependencies: D12; consumers: Family.discarded_wRaw.
WChannel.output_normC_eq: proof_shape: bind-only; escape_witness: none; frozen_dependencies: D1,D3,D4,D5,D11,D12; consumers: BaseValues.flagRaw_norms,BaseValues.decodedRaw_norms,Family.family_all_channel_bound.
Amplification.phiVec: proof_shape: bind-only; escape_witness: none; frozen_dependencies: none; consumers: Amplification.phiRaw,Amplification.phiRaw_trace,Amplification.phiRaw_norm,Amplification.amplify_pos,Amplification.amplify_normA.
Amplification.phiRaw: proof_shape: bind-only; escape_witness: none; frozen_dependencies: D12; consumers: Amplification.amplify,Amplification.phiRaw_trace,Amplification.phiRaw_norm,Amplification.phiRaw_pt_norm,Amplification.amplify_trace,Amplification.amplify_normC,Amplification.amplify_normA,Amplification.amplify_normB,Family.classicalize_amplify.
Amplification.regroup: proof_shape: bind-only; escape_witness: none; frozen_dependencies: none; consumers: Amplification.amplify,Amplification.amplify_pos,Amplification.amplify_trace,Amplification.regroupC.
Amplification.amplify: proof_shape: bind-only; escape_witness: none; frozen_dependencies: D12; consumers: Amplification.amplify_pos,Amplification.amplify_trace,Amplification.amplify_normC,Amplification.amplify_normA,Amplification.amplify_normB,Family.family,Family.family_state,Family.family_initial,Family.classicalize_amplify,Family.family_all_channel_bound,Family.family_attains,Family.family_discarded,Family.family_discarded_value.
Amplification.phiRaw_trace: proof_shape: bind-only; escape_witness: none; frozen_dependencies: D12; consumers: Amplification.phiRaw_norm,Amplification.amplify_trace.
Amplification.phiRaw_norm: proof_shape: bind-only; escape_witness: none; frozen_dependencies: D5,D11,D12; consumers: Amplification.amplify_normC.
Amplification.phiRaw_pt_norm: proof_shape: bind-only; escape_witness: none; frozen_dependencies: D1,D5,D6,D7,D8,D11,D12; consumers: Amplification.amplify_normA,Amplification.amplify_normB.
Amplification.amplify_pos: proof_shape: bind-only; escape_witness: none; frozen_dependencies: D12; consumers: Family.family_state.
Amplification.amplify_trace: proof_shape: bind-only; escape_witness: none; frozen_dependencies: D12; consumers: Family.family_state.
Amplification.regroupC: proof_shape: bind-only; escape_witness: none; frozen_dependencies: none; consumers: Amplification.amplify_normC.
Amplification.amplify_normC: proof_shape: bind-only; escape_witness: none; frozen_dependencies: D1,D5,D11,D12,D18; consumers: Family.family_initial,Family.family_all_channel_bound,Family.family_attains,Family.family_discarded_value.
Amplification.regroupA: proof_shape: bind-only; escape_witness: none; frozen_dependencies: none; consumers: Amplification.amplify_normA.
Amplification.amplify_normA: proof_shape: bind-only; escape_witness: none; frozen_dependencies: D1,D5,D6,D7,D8,D11,D12,D18; consumers: Family.family_initial,Family.family_all_channel_bound,Family.family_attains,Family.family_discarded_value.
Amplification.regroupB: proof_shape: bind-only; escape_witness: none; frozen_dependencies: none; consumers: Amplification.amplify_normB.
Amplification.amplify_normB: proof_shape: bind-only; escape_witness: none; frozen_dependencies: D1,D5,D6,D7,D8,D11,D12,D18; consumers: Family.family_initial,Family.family_all_channel_bound,Family.family_attains,Family.family_discarded_value.
BaseValues.wRaw_trace: proof_shape: bind-only; escape_witness: none; frozen_dependencies: D12; consumers: Family.family_state.
BaseValues.wVec_cyclic: proof_shape: bind-only; escape_witness: none; frozen_dependencies: none; consumers: BaseValues.wRaw_norms.
BaseValues.wRaw_norms: proof_shape: bind-only; escape_witness: none; frozen_dependencies: D1,D5,D6,D7,D8,D12; consumers: Family.family_initial.
BaseValues.decodedRaw: proof_shape: bind-only; escape_witness: none; frozen_dependencies: D12; consumers: BaseValues.decodedRaw_classicalize,BaseValues.decodedRaw_norms,Family.discarded_wRaw,Family.family_discarded,Family.family_discarded_value.
BaseValues.flagRaw_norms: proof_shape: bind-only; escape_witness: none; frozen_dependencies: D1,D3,D4,D5,D6,D7,D8,D11,D12,D13,D14; consumers: Family.family_attains.
BaseValues.decodedRaw_classicalize: proof_shape: bind-only; escape_witness: none; frozen_dependencies: D12; consumers: BaseValues.decodedRaw_norms.
BaseValues.decodedRaw_norms: proof_shape: bind-only; escape_witness: none; frozen_dependencies: D1,D3,D4,D5,D6,D7,D8,D11,D12,D13,D14,D18; consumers: Family.family_discarded_value.
delta_eq_of_optimum: proof_shape: bind-only; escape_witness: none; frozen_dependencies: D3,D4,D16; consumers: Family.finite_family_data.
unbounded_linear_gaps: proof_shape: bind-only; escape_witness: none; frozen_dependencies: none; consumers: claim_of_family.
claim_of_family: proof_shape: bind-only; escape_witness: none; frozen_dependencies: D4,D16; consumers: result.
Family.family: proof_shape: bind-only; escape_witness: none; frozen_dependencies: D12; consumers: Family.family_state,Family.family_initial,Family.family_all_channel_bound,Family.family_attains,Family.family_discarded,Family.family_discarded_value,Family.finiteFamily,Family.finite_family_data.
Family.family_state: proof_shape: bind-only; escape_witness: none; frozen_dependencies: D4,D12; consumers: Family.finite_family_data.
Family.family_initial: proof_shape: bind-only; escape_witness: none; frozen_dependencies: D1,D2,D5,D6,D7,D8,D11,D12,D16,D17,D18; consumers: Family.finite_family_data.
Family.classicalize_amplify: proof_shape: bind-only; escape_witness: none; frozen_dependencies: D12; consumers: Family.family_all_channel_bound,Family.family_attains,Family.family_discarded.
Family.family_all_channel_bound: proof_shape: bind-only; escape_witness: none; frozen_dependencies: D1,D2,D3,D4,D5,D6,D7,D8,D9,D10,D11,D12,D15,D16,D17,D18,D19; consumers: Family.finite_family_data.
Family.family_attains: proof_shape: bind-only; escape_witness: none; frozen_dependencies: D1,D2,D3,D4,D5,D6,D7,D8,D11,D12,D13,D14,D16,D17,D18; consumers: Family.finite_family_data.
Family.discarded: proof_shape: bind-only; escape_witness: none; frozen_dependencies: none; consumers: Family.discarded_classicalize,Family.discarded_wRaw,Family.family_discarded,Family.family_discarded_value,Family.finite_family_data.
Family.discarded_classicalize: proof_shape: bind-only; escape_witness: none; frozen_dependencies: D12; consumers: Family.family_discarded,Family.finite_family_data.
Family.discarded_wRaw: proof_shape: bind-only; escape_witness: none; frozen_dependencies: D12; consumers: Family.family_discarded.
Family.family_discarded: proof_shape: bind-only; escape_witness: none; frozen_dependencies: D12; consumers: Family.family_discarded_value.
Family.family_discarded_value: proof_shape: bind-only; escape_witness: none; frozen_dependencies: D1,D2,D3,D4,D5,D6,D7,D8,D11,D12,D13,D14,D16,D17,D18; consumers: Family.finite_family_data.
Family.finiteFamily: proof_shape: bind-only; escape_witness: none; frozen_dependencies: D12; consumers: Family.finite_family_data.
Family.finite_family_data: proof_shape: bind-only; escape_witness: none; frozen_dependencies: D1,D2,D3,D4,D5,D6,D7,D8,D9,D10,D11,D12,D13,D14,D15,D16,D17,D18,D19; consumers: result.
result: proof_shape: bind-only; escape_witness: none; frozen_dependencies: D1,D2,D3,D4,D5,D6,D7,D8,D9,D10,D11,D12,D13,D14,D15,D16,D17,D18,D19; consumers: settling result.
-/

import D5.S3.Quantum.Foundation.FiniteTraceDistance
import D5.S3.Quantum.Schatten.TraceNorm
import D5.S3.Weil.ZetaLinear.PosIndex
import D5.S3.QuantumChannels.SchurChannelMixedUnitaryDistance
import D5.S3.Quantum.Entanglement.ConicalDesignConcurrenceComparability
import Mathlib.Analysis.InnerProductSpace.Positive
import D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation
import D5.S3.QuantumBounds.NegativityReductionInclusionRefutation
import D5.S3.Quantum.Dynamics.KickedIsingNegativityRefutation
import D5.S3.Quantum.PureState.PureStateHandshake
import D5.S3.Quantum.Entanglement.GHZMeasureBiseparableBound
import D5.S3.Quantum.Entanglement.EnergyRestrictedUnitaryEncodingRefutation
set_option maxHeartbeats 1000000
noncomputable section
namespace D5.S3.Quantum.Classicalization.XuImaiGuhneSimultaneousUnboundedness
open D5.S3.Quantum.Entanglement.GHZMeasureBiseparableBound (IsDensity)
open D5.S3.Quantum.Entanglement.EnergyRestrictedUnitaryEncodingRefutation (IsPOVM)
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Kronecker
open D5.S3.Quantum.Foundation.FiniteTraceDistance
open D5.S3.Quantum.Dynamics.KickedIsingNegativityRefutation (partialTranspose)
open D5.S3.Quantum.PureState.PureStateHandshake (rankOneDensity)
open D5.S3.Quantum.Entanglement.ConicalDesignConcurrenceComparability (traceNorm_smul_nonneg)
namespace Toolkit
variable {a b c d : Type} [Fintype a] [Fintype b] [Fintype c] [Fintype d]
  [DecidableEq a] [DecidableEq b] [DecidableEq c] [DecidableEq d]
private theorem traceNorm_kronecker (A : Matrix a b ℂ) (B : Matrix c d ℂ) : traceNorm (A ⊗ₖ B) = traceNorm A * traceNorm B := by
  let P := CFC.sqrt (Aᴴ * A)
  let Q := CFC.sqrt (Bᴴ * B)
  have hP : P.PosSemidef := (CFC.sqrt_nonneg _).posSemidef
  have hQ : Q.PosSemidef := (CFC.sqrt_nonneg _).posSemidef
  have hs : (P ⊗ₖ Q) * (P ⊗ₖ Q) = (A ⊗ₖ B)ᴴ * (A ⊗ₖ B) := by
    rw [← Matrix.mul_kronecker_mul, Matrix.conjTranspose_kronecker,
      ← Matrix.mul_kronecker_mul]
    dsimp only [P, Q]
    rw [CFC.sqrt_mul_sqrt_self _ (Matrix.posSemidef_conjTranspose_mul_self A).nonneg,
      CFC.sqrt_mul_sqrt_self _ (Matrix.posSemidef_conjTranspose_mul_self B).nonneg]
  have hroot := CFC.sqrt_unique hs (hP.kronecker hQ).nonneg
  have hPi := (Complex.nonneg_iff.mp hP.trace_nonneg).2
  have hQi := (Complex.nonneg_iff.mp hQ.trace_nonneg).2
  change (CFC.sqrt ((A ⊗ₖ B)ᴴ * (A ⊗ₖ B))).trace.re = P.trace.re * Q.trace.re
  rw [hroot, Matrix.trace_kronecker]
  simp only [Complex.mul_re, hPi.symm, hQi.symm, zero_mul, sub_zero]
private theorem traceNorm_rows (e : a ≃ b) (A : Matrix b c ℂ) : traceNorm (A.submatrix e id) = traceNorm A := by
  unfold traceNorm
  congr 3
  rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv]
  rfl
private theorem pure_partialTranspose_norm {n : ℕ} (K : Matrix (Fin n) (Fin n) ℂ) : traceNorm (fun p q : Fin n × Fin n => K p.1 q.2 * star (K q.1 p.2)) = traceNorm Kᴴ * traceNorm K := by
  let e := Equiv.prodComm (Fin n) (Fin n)
  let X : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ :=
    fun p q => K p.1 q.2 * star (K q.1 p.2)
  change traceNorm X = _
  have he : X.submatrix e id = Kᴴ ⊗ₖ K := by
    ext ⟨i,j⟩ ⟨k,l⟩
    change K j l * star (K k i) = star (K k i) * K j l
    exact mul_comm _ _
  calc
    traceNorm X = traceNorm (X.submatrix e id) := (traceNorm_rows e X).symm
    _ = _ := by rw [he,traceNorm_kronecker]
private def branchCoeff (α β : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![β, α; α, 0]
private theorem traceNorm_branchCoeff (α β : ℂ) : traceNorm (branchCoeff α β) = Real.sqrt (4 * ‖α‖ ^ 2 + ‖β‖ ^ 2) := by
  have hs := D5.S3.Quantum.Schatten.TraceNorm.transitionMass_sq (branchCoeff α β)
  change traceNorm (branchCoeff α β) ^ 2 = _ at hs
  have hF : RHLinalg.frobSq (branchCoeff α β) = 2 * ‖α‖ ^ 2 + ‖β‖ ^ 2 := by
    simp [RHLinalg.frobSq, branchCoeff, Matrix.trace, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Fin.sum_univ_two, RCLike.star_def,
      Complex.conj_mul', RCLike.re_eq_complex_re, ← Complex.ofReal_pow,
      Complex.ofReal_re]
    <;> ring
  have hdet : ‖(branchCoeff α β).det‖ = ‖α‖ ^ 2 := by
    simp [branchCoeff, Matrix.det_fin_two, norm_mul, pow_two]
  rw [← Real.sqrt_sq (traceNorm_nonneg _), hs, hF, hdet]
  congr 1
  ring
private theorem branchCoeff_norm (α β : ℂ) : traceNorm (fun p q : Fin 2 × Fin 2 => branchCoeff α β p.1 q.2 * star (branchCoeff α β q.1 p.2)) = 4 * ‖α‖ ^ 2 + ‖β‖ ^ 2 := by
  rw [pure_partialTranspose_norm]
  have he : (branchCoeff α β)ᴴ = branchCoeff (star α) (star β) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [branchCoeff,Matrix.conjTranspose_apply]
  rw [he,traceNorm_branchCoeff,traceNorm_branchCoeff]
  simp only [norm_star]
  rw [← pow_two,Real.sq_sqrt (by positivity)]
variable {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
private theorem traceNorm_submatrix_equiv (e : a ≃ b) (A : Matrix b b ℂ) : traceNorm (A.submatrix e e) = traceNorm A := by
  exact D5.S3.QuantumChannels.SchurChannelMixedUnitaryDistance.reindex_traceNorm e.symm A
end Toolkit
/-! Binding conventions for Z.-P. Xu, S. Imai and O. Gühne, "Fate of multiparticle entanglement when one particle becomes
classical", arXiv:2206.12834v2 (Phys. Rev. A 107, L040401 (2023)): the classicalization operations `N_C` of Eq. (1), the
tripartite negativity `N_ABC` of Eq. (4), the entanglement change `Δ_E` of Eq. (2), the bound `Δ̃_E` of Eq. (9), and the
question of Section V.B, "whether there exist entanglement measures E and states ρ_ABC such that both Δ_E(ρ_ABC) and
Δ̃_E(ρ_ABC) − Δ_E(ρ_ABC) can be arbitrarily large in the sense that they are not limited by the size of C, even if C is
only a qubit". -/

section Source

open Matrix
open D5.S3.QuantumBounds.NegativityReductionInclusionRefutation (negativity)
open scoped ComplexOrder

variable {A B C : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]

/-- Eq. (4): `N_ABC = N_{AB|C} + N_{BC|A} + N_{AC|B}`, where `N_{X|Y}` is the negativity of the partial transpose with
respect to `Y` (D5's `negativity` transposes the second factor). -/
noncomputable def tripartiteNegativity (ρ : Matrix (A × B × C) (A × B × C) ℂ) : ℝ :=
  negativity (ρ.submatrix (Equiv.prodAssoc A B C) (Equiv.prodAssoc A B C)) +
    negativity (ρ.submatrix (Equiv.prodComm (B × C) A) (Equiv.prodComm (B × C) A)) +
    negativity (ρ.submatrix (fun p : (A × C) × B => (p.1.1, p.2, p.1.2))
      (fun p : (A × C) × B => (p.1.1, p.2, p.1.2)))

/-- `p_i σ_i = tr_C(ρ_ABC m_i)`. -/
def branch (ρ : Matrix (A × B × C) (A × B × C) ℂ) (m : Matrix C C ℂ) : Matrix (A × B) (A × B) ℂ :=
  fun p q => ∑ c, ∑ c', ρ (p.1, p.2, c) (q.1, q.2, c') * m c' c

/-- Eq. (1): `Φ_C(ρ_ABC) = Σ_i p_i σ_i ⊗ τ_i`, with the register states `τ_i` on a system `E`. -/
def classicalize {ι E : Type} [Fintype ι] (ρ : Matrix (A × B × C) (A × B × C) ℂ) (m : ι → Matrix C C ℂ)
    (τ : ι → Matrix E E ℂ) : Matrix (A × B × E) (A × B × E) ℂ :=
  fun p q => ∑ i, branch ρ (m i) (p.1, p.2.1) (q.1, q.2.1) * τ i p.2.2 q.2.2

/-- Eq. (2) with `E = N_ABC`: `Δ_E(ρ_ABC) = min_{Φ_C ∈ N_C} {E[ρ_ABC] − E[Φ_C(ρ_ABC)]}`, over every finite measurement on `C`
and every assignment of register states. -/
noncomputable def delta (ρ : Matrix (A × B × C) (A × B × C) ℂ) : ℝ :=
  sInf {x | ∃ (k e : ℕ) (m : Fin k → Matrix C C ℂ) (τ : Fin k → Matrix (Fin e) (Fin e) ℂ),
    ((∀ i, (m i).PosSemidef) ∧ ∑ i, m i = 1) ∧
      (∀ i, (τ i).PosSemidef ∧ (τ i).trace = 1) ∧
      x = tripartiteNegativity ρ - tripartiteNegativity (classicalize ρ m τ)}

/-- Eq. (9) with `E = N_ABC`: `Δ̃_E(ρ_ABC) = E[ρ_ABC] − E[ρ_AB ⊗ |0⟩⟨0|]`, with `ρ_AB = tr_C(ρ_ABC)`. -/
noncomputable def deltaTilde (ρ : Matrix (A × B × Fin 2) (A × B × Fin 2) ℂ) : ℝ :=
  tripartiteNegativity ρ -
    tripartiteNegativity (fun p q : A × B × Fin 2 =>
      branch ρ 1 (p.1, p.2.1) (q.1, q.2.1) * (if p.2.2 = 0 ∧ q.2.2 = 0 then 1 else 0))

/-- Section V.B, answered for the tripartite negativity `E = N_ABC`: with `C` a qubit, both `Δ_E` and `Δ̃_E − Δ_E` are
unbounded over finite-dimensional `A`, `B` and states `ρ_ABC`. -/
def claim : Prop :=
  ∀ M : ℝ, ∃ (a b : ℕ) (ρ : Matrix (Fin a × Fin b × Fin 2) (Fin a × Fin b × Fin 2) ℂ),
    (ρ.PosSemidef ∧ ρ.trace = 1) ∧ M < delta ρ ∧ M < deltaTilde ρ - delta ρ

end Source
namespace Normalization
open D5.S3.QuantumBounds.NegativityReductionInclusionRefutation (negativity)
open Toolkit
variable {A B C A' B' C' : Type}
  [Fintype A] [Fintype B] [Fintype C] [DecidableEq A] [DecidableEq B] [DecidableEq C]
  [Fintype A'] [Fintype B'] [Fintype C'] [DecidableEq A'] [DecidableEq B'] [DecidableEq C']
private def normC (ρ : Matrix (A × B × C) (A × B × C) ℂ) : ℝ :=
  traceNorm (partialTranspose (ρ.submatrix (Equiv.prodAssoc _ _ _) (Equiv.prodAssoc _ _ _)))
private def normA (ρ : Matrix (A × B × C) (A × B × C) ℂ) : ℝ :=
  traceNorm (partialTranspose (ρ.submatrix (Equiv.prodComm (B × C) A) (Equiv.prodComm (B × C) A)))
private def normB (ρ : Matrix (A × B × C) (A × B × C) ℂ) : ℝ :=
  traceNorm (partialTranspose (ρ.submatrix (fun p : (A × C) × B => (p.1.1,p.2,p.1.2))
    (fun p : (A × C) × B => (p.1.1,p.2,p.1.2))))
private theorem tripartite_eq (ρ : Matrix (A × B × C) (A × B × C) ℂ) : tripartiteNegativity ρ = (normC ρ + normA ρ + normB ρ - 3) / 2 := by
  unfold tripartiteNegativity negativity normC normA normB
  ring
private theorem normC_smul (ρ : Matrix (A × B × C) (A × B × C) ℂ) (c : ℝ) (hc : 0 ≤ c) : normC ((c : ℂ) • ρ) = c * normC ρ := by
  exact traceNorm_smul_nonneg _ c hc
private theorem normA_smul (ρ : Matrix (A × B × C) (A × B × C) ℂ) (c : ℝ) (hc : 0 ≤ c) : normA ((c : ℂ) • ρ) = c * normA ρ := by
  exact traceNorm_smul_nonneg _ c hc
private theorem normB_smul (ρ : Matrix (A × B × C) (A × B × C) ℂ) (c : ℝ) (hc : 0 ≤ c) : normB ((c : ℂ) • ρ) = c * normB ρ := by
  exact traceNorm_smul_nonneg _ c hc
private theorem normC_relabel (eA : A' ≃ A) (eB : B' ≃ B) (eC : C' ≃ C) (ρ : Matrix (A × B × C) (A × B × C) ℂ) : normC ((ρ.submatrix (Equiv.prodCongr eA (Equiv.prodCongr eB eC)) (Equiv.prodCongr eA (Equiv.prodCongr eB eC)))) = normC ρ := by
  let e := Equiv.prodCongr (Equiv.prodCongr eA eB) eC
  have he : partialTranspose (((ρ.submatrix (Equiv.prodCongr eA (Equiv.prodCongr eB eC)) (Equiv.prodCongr eA (Equiv.prodCongr eB eC)))).submatrix
      (Equiv.prodAssoc _ _ _) (Equiv.prodAssoc _ _ _)) =
    (partialTranspose (ρ.submatrix (Equiv.prodAssoc _ _ _) (Equiv.prodAssoc _ _ _))).submatrix e e := rfl
  exact (congrArg traceNorm he).trans (traceNorm_submatrix_equiv e _)
private theorem normA_relabel (eA : A' ≃ A) (eB : B' ≃ B) (eC : C' ≃ C) (ρ : Matrix (A × B × C) (A × B × C) ℂ) : normA ((ρ.submatrix (Equiv.prodCongr eA (Equiv.prodCongr eB eC)) (Equiv.prodCongr eA (Equiv.prodCongr eB eC)))) = normA ρ := by
  let e := Equiv.prodCongr (Equiv.prodCongr eB eC) eA
  have he : partialTranspose (((ρ.submatrix (Equiv.prodCongr eA (Equiv.prodCongr eB eC)) (Equiv.prodCongr eA (Equiv.prodCongr eB eC)))).submatrix
      (Equiv.prodComm _ _) (Equiv.prodComm _ _)) =
    (partialTranspose (ρ.submatrix (Equiv.prodComm (B × C) A)
      (Equiv.prodComm (B × C) A))).submatrix e e := rfl
  exact (congrArg traceNorm he).trans (traceNorm_submatrix_equiv e _)
private theorem normB_relabel (eA : A' ≃ A) (eB : B' ≃ B) (eC : C' ≃ C) (ρ : Matrix (A × B × C) (A × B × C) ℂ) : normB ((ρ.submatrix (Equiv.prodCongr eA (Equiv.prodCongr eB eC)) (Equiv.prodCongr eA (Equiv.prodCongr eB eC)))) = normB ρ := by
  let e := Equiv.prodCongr (Equiv.prodCongr eA eC) eB
  have he : partialTranspose (((ρ.submatrix (Equiv.prodCongr eA (Equiv.prodCongr eB eC)) (Equiv.prodCongr eA (Equiv.prodCongr eB eC)))).submatrix
      (fun p : (A' × C') × B' => (p.1.1,p.2,p.1.2))
      (fun p : (A' × C') × B' => (p.1.1,p.2,p.1.2))) =
    (partialTranspose (ρ.submatrix
      (fun p : (A × C) × B => (p.1.1,p.2,p.1.2))
      (fun p : (A × C) × B => (p.1.1,p.2,p.1.2)))).submatrix e e := rfl
  exact (congrArg traceNorm he).trans (traceNorm_submatrix_equiv e _)
private theorem tripartite_relabel (eA : A' ≃ A) (eB : B' ≃ B) (eC : C' ≃ C) (ρ : Matrix (A × B × C) (A × B × C) ℂ) : tripartiteNegativity ((ρ.submatrix (Equiv.prodCongr eA (Equiv.prodCongr eB eC)) (Equiv.prodCongr eA (Equiv.prodCongr eB eC)))) = tripartiteNegativity ρ := by
  rw [tripartite_eq, tripartite_eq, normC_relabel, normA_relabel, normB_relabel]
variable {A B C A' B' E ι : Type}
  [Fintype A] [Fintype B] [Fintype C] [DecidableEq A] [DecidableEq B] [DecidableEq C]
  [Fintype A'] [Fintype B'] [DecidableEq A'] [DecidableEq B'] [Fintype ι]
private theorem state_relabel (eA : A' ≃ A) (eB : B' ≃ B) (ρ : Matrix (A × B × C) (A × B × C) ℂ) (hρ : IsDensity ρ) : IsDensity ((ρ.submatrix (Equiv.prodCongr eA (Equiv.prodCongr eB (Equiv.refl C))) (Equiv.prodCongr eA (Equiv.prodCongr eB (Equiv.refl C))))) := by
  refine ⟨hρ.1.submatrix _, ?_⟩
  let e := Equiv.prodCongr eA (Equiv.prodCongr eB (Equiv.refl C))
  exact ((e.sum_comp (fun p => ρ p p))).trans hρ.2
private theorem classicalize_relabel (eA : A' ≃ A) (eB : B' ≃ B) (ρ : Matrix (A × B × C) (A × B × C) ℂ) (m : ι → Matrix C C ℂ) (τ : ι → Matrix E E ℂ) : classicalize ((ρ.submatrix (Equiv.prodCongr eA (Equiv.prodCongr eB (Equiv.refl C))) (Equiv.prodCongr eA (Equiv.prodCongr eB (Equiv.refl C))))) m τ = ((classicalize ρ m τ).submatrix (Equiv.prodCongr eA (Equiv.prodCongr eB (Equiv.refl E))) (Equiv.prodCongr eA (Equiv.prodCongr eB (Equiv.refl E)))) := by
  rfl
private theorem classicalize_smul (ρ : Matrix (A × B × C) (A × B × C) ℂ) (m : ι → Matrix C C ℂ) (τ : ι → Matrix E E ℂ) (c : ℂ) : classicalize (c • ρ) m τ = c • classicalize ρ m τ := by
  ext p q
  simp only [classicalize, branch, Matrix.smul_apply, smul_eq_mul,
    mul_assoc, ← Finset.mul_sum]
end Normalization
namespace Refinement
variable {ι C : Type} [Fintype ι] [Fintype C] [DecidableEq C]
private theorem povm_rankOne_refinement (m : ι → Matrix C C ℂ) (hm : ∀ i, (m i).PosSemidef) (hcomplete : ∑ i, m i = 1) : ∃ (n : ι → ℕ) (v : (i : ι) → Fin (n i) → C → ℂ), (∀ i, m i = ∑ t, Matrix.vecMulVec (v i t) (star (v i t))) ∧ (∀ c, ∑ i, ∑ t, ‖v i t c‖ ^ 2 = 1) := by
  classical
  choose n v hv using fun i => Matrix.posSemidef_iff_eq_sum_vecMulVec.mp (hm i)
  refine ⟨n, v, hv, ?_⟩
  intro c
  have hdiag := congrArg (fun X : Matrix C C ℂ => (X c c).re) hcomplete
  simp only [Matrix.sum_apply, Complex.re_sum, Matrix.one_apply_eq, Complex.one_re] at hdiag
  calc
    _ = ∑ i, (m i c c).re := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hv i]
      simp only [Matrix.sum_apply, Complex.re_sum, Matrix.vecMulVec_apply,
        Pi.star_apply, RCLike.star_def, Complex.mul_conj, Complex.ofReal_re,
        Complex.normSq_eq_norm_sq]
    _ = 1 := hdiag
end Refinement
namespace Numerics
private def wVec : Fin 2 × Fin 2 × Fin 2 → ℂ :=
  Pi.single (0,0,1) 1 + Pi.single (0,1,0) 1 + Pi.single (1,0,0) 1
private def wRaw : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) ℂ :=
  rankOneDensity wVec
private def wCut : Matrix ((Fin 2 × Fin 2) × Fin 2) ((Fin 2 × Fin 2) × Fin 2) ℂ :=
  wRaw.submatrix (Equiv.prodAssoc _ _ _) (Equiv.prodAssoc _ _ _)
private def wAbs : Matrix ((Fin 2 × Fin 2) × Fin 2) ((Fin 2 × Fin 2) × Fin 2) ℂ :=
  (Real.sqrt 2 : ℂ) • rankOneDensity (Pi.single ((0,0),0) 1) +
    rankOneDensity (Pi.single ((0,0),1) 1) +
    rankOneDensity (Pi.single ((0,1),0) 1 + Pi.single ((1,0),0) 1) +
    ((Real.sqrt 2 / 2 : ℝ) : ℂ) • rankOneDensity (Pi.single ((0,1),1) 1 + Pi.single ((1,0),1) 1)
private theorem wAbs_pos : wAbs.PosSemidef := by
  apply Matrix.PosSemidef.add
  · apply Matrix.PosSemidef.add
    · apply Matrix.PosSemidef.add
      · exact (Matrix.posSemidef_vecMulVec_self_star _).smul
          (RCLike.ofReal_nonneg.mpr (Real.sqrt_nonneg _))
      · exact Matrix.posSemidef_vecMulVec_self_star _
    · exact Matrix.posSemidef_vecMulVec_self_star _
  · exact (Matrix.posSemidef_vecMulVec_self_star _).smul
      (by
        exact
          (RCLike.ofReal_nonneg.mpr (div_nonneg (Real.sqrt_nonneg (2 : ℝ)) (by norm_num)) :
            (0 : ℂ) ≤ ((Real.sqrt 2 / 2 : ℝ) : ℂ)))
set_option maxRecDepth 2048 in
set_option maxHeartbeats 1500000 in
private theorem wAbs_square : wAbs * wAbs = (partialTranspose wCut)ᴴ * partialTranspose wCut := by
  have hr : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
    exact_mod_cast Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  ext ⟨⟨i,j⟩,k⟩ ⟨⟨l,m⟩,n⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    fin_cases l <;> fin_cases m <;> fin_cases n <;>
    norm_num [wAbs, wCut, wRaw, wVec, Pi.single_apply, rankOneDensity,
      partialTranspose, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.vecMulVec_apply, Matrix.submatrix_apply, Matrix.smul_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two, Pi.star_apply,
      map_ofNat, map_add, map_mul, map_div, Complex.star_def] <;>
    ring_nf <;> simp_all
private theorem wCut_norm : traceNorm (partialTranspose wCut) = 3 + 2 * Real.sqrt 2 := by
  unfold traceNorm
  rw [CFC.sqrt_unique wAbs_square wAbs_pos.nonneg]
  norm_num [wAbs, rankOneDensity, Pi.single_apply, Matrix.trace,
    Matrix.vecMulVec_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Pi.star_apply]
  ring
private def reducedRaw : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  rankOneDensity (Pi.single (0,0) 1) + rankOneDensity (Pi.single (0,1) 1 + Pi.single (1,0) 1)
private def reducedAbs : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  ((Real.sqrt 5 / 5 : ℝ) : ℂ) •
    (rankOneDensity (Pi.single (0,0) 1 + Pi.single (1,1) 1) +
      (2 : ℂ) • rankOneDensity (Pi.single (0,0) 1) + rankOneDensity (Pi.single (1,1) 1)) +
    rankOneDensity (Pi.single (0,1) 1) + rankOneDensity (Pi.single (1,0) 1)
private theorem reducedAbs_pos : reducedAbs.PosSemidef := by
  apply Matrix.PosSemidef.add
  · apply Matrix.PosSemidef.add
    · apply Matrix.PosSemidef.smul
      · apply Matrix.PosSemidef.add
        · exact (Matrix.posSemidef_vecMulVec_self_star _).add
            ((Matrix.posSemidef_vecMulVec_self_star _).smul (by norm_num))
        · exact Matrix.posSemidef_vecMulVec_self_star _
      · exact
          (RCLike.ofReal_nonneg.mpr (div_nonneg (Real.sqrt_nonneg (5 : ℝ)) (by norm_num)) :
            (0 : ℂ) ≤ ((Real.sqrt 5 / 5 : ℝ) : ℂ))
    · exact Matrix.posSemidef_vecMulVec_self_star _
  · exact Matrix.posSemidef_vecMulVec_self_star _
set_option maxRecDepth 2048 in
set_option maxHeartbeats 500000 in
private theorem reducedAbs_square : reducedAbs * reducedAbs = (partialTranspose reducedRaw)ᴴ * partialTranspose reducedRaw := by
  have hr : (Real.sqrt 5 : ℂ) ^ 2 = 5 := by
    exact_mod_cast Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  ext ⟨i,j⟩ ⟨k,l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num [reducedAbs, reducedRaw, Pi.single_apply, rankOneDensity,
      partialTranspose, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.vecMulVec_apply, Matrix.smul_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two, Pi.star_apply,
      map_ofNat, map_add, map_mul, map_div, Complex.star_def] <;>
    ring_nf <;> simp_all <;> norm_num
private theorem reducedRaw_norm : traceNorm (partialTranspose reducedRaw) = 2 + Real.sqrt 5 := by
  unfold traceNorm
  rw [CFC.sqrt_unique reducedAbs_square reducedAbs_pos.nonneg]
  norm_num [reducedAbs, rankOneDensity, Pi.single_apply, Matrix.trace,
    Matrix.vecMulVec_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Pi.star_apply]
  ring
private def flagRaw : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) ℂ :=
  rankOneDensity (Pi.single (0,1,0) 1 + Pi.single (1,0,0) 1) + rankOneDensity (Pi.single (0,0,1) 1)
private def flagCutB : Matrix ((Fin 2 × Fin 2) × Fin 2) ((Fin 2 × Fin 2) × Fin 2) ℂ :=
  flagRaw.submatrix (fun p => (p.1.1,p.2,p.1.2)) (fun p => (p.1.1,p.2,p.1.2))
private def flagAbsB : Matrix ((Fin 2 × Fin 2) × Fin 2) ((Fin 2 × Fin 2) × Fin 2) ℂ :=
  diagonal (fun p => if p.1.2 = 0 ∨ (p.1.1 = 0 ∧ p.2 = 0) then 1 else 0)
private theorem flagAbsB_pos : flagAbsB.PosSemidef := by
  apply Matrix.PosSemidef.diagonal
  intro p
  dsimp
  split_ifs <;> norm_num
set_option maxRecDepth 2048 in
set_option maxHeartbeats 1000000 in
private theorem flagAbsB_square : flagAbsB * flagAbsB = (partialTranspose flagCutB)ᴴ * partialTranspose flagCutB := by
  ext ⟨⟨i,j⟩,k⟩ ⟨⟨l,m⟩,n⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    fin_cases l <;> fin_cases m <;> fin_cases n <;>
    norm_num [flagAbsB, flagCutB, flagRaw, Pi.single_apply, rankOneDensity,
      partialTranspose, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.vecMulVec_apply, Matrix.submatrix_apply, Matrix.diagonal,
      Fintype.sum_prod_type, Fin.sum_univ_two, Pi.star_apply]
private theorem flagCutB_norm : traceNorm (partialTranspose flagCutB) = 5 := by
  unfold traceNorm
  rw [CFC.sqrt_unique flagAbsB_square flagAbsB_pos.nonneg]
  change (∑ p : (Fin 2 × Fin 2) × Fin 2,
    (if p.1.2 = 0 ∨ (p.1.1 = 0 ∧ p.2 = 0) then (1 : ℂ) else 0)).re = 5
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two]
  norm_num
end Numerics
namespace WChannel
open Toolkit Numerics Refinement
variable {ι E : Type} [Fintype ι] [Fintype E] [DecidableEq E]
private def chi (v : Fin 2 → ℂ) : Fin 2 × Fin 2 → ℂ :=
  fun p => branchCoeff (star (v 0)) (star (v 1)) p.1 p.2
private theorem branch_wRaw_rankOne (v : Fin 2 → ℂ) : branch wRaw (rankOneDensity v) = rankOneDensity (chi v) := by
  ext ⟨a,b⟩ ⟨c,d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [branch, wRaw, wVec, Pi.single_apply, rankOneDensity, chi, branchCoeff,
      Matrix.vecMulVec_apply, Fin.sum_univ_two, Pi.star_apply, map_add, map_ofNat] <;> ring
private theorem chi_norm (v : Fin 2 → ℂ) : traceNorm (partialTranspose (rankOneDensity (chi v))) = 4 * ‖v 0‖ ^ 2 + ‖v 1‖ ^ 2 := by
  change traceNorm (fun p q : Fin 2 × Fin 2 =>
    branchCoeff (star (v 0)) (star (v 1)) p.1 q.2 *
      star (branchCoeff (star (v 0)) (star (v 1)) q.1 p.2)) = _
  simpa only [norm_star] using branchCoeff_norm (star (v 0)) (star (v 1))
private theorem chi_trace (v : Fin 2 → ℂ) : (rankOneDensity (chi v)).trace.re = 2 * ‖v 0‖ ^ 2 + ‖v 1‖ ^ 2 := by
  simp [chi, branchCoeff, rankOneDensity, Matrix.trace, Matrix.vecMulVec_apply,
    Fintype.sum_prod_type, Fin.sum_univ_two, Pi.star_apply,
    RCLike.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq,
    ← Complex.ofReal_pow, Complex.ofReal_re]
  ring
private theorem branch_sum (ρ : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) ℂ) {J : Type} [Fintype J] (m : J → Matrix (Fin 2) (Fin 2) ℂ) : branch ρ (∑ j, m j) = ∑ j, branch ρ (m j) := by
  ext p q
  simp only [branch, Matrix.sum_apply, Finset.mul_sum]
  calc
    _ = ∑ c, ∑ j, ∑ c', ρ (p.1,p.2,c) (q.1,q.2,c') * m j c' c := by
      apply Finset.sum_congr rfl
      intro c hc
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm
private theorem classicalize_refinement (m : ι → Matrix (Fin 2) (Fin 2) ℂ) (τ : ι → Matrix E E ℂ) (n : ι → ℕ) (v : (i : ι) → Fin (n i) → Fin 2 → ℂ) (hv : ∀ i, m i = ∑ t, rankOneDensity (v i t)) : classicalize wRaw m τ = fun p q => ∑ i, ∑ t, rankOneDensity (chi (v i t)) (p.1,p.2.1) (q.1,q.2.1) * τ i p.2.2 q.2.2 := by
  ext p q
  simp only [classicalize]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hv i, branch_sum]
  simp only [Matrix.sum_apply, branch_wRaw_rankOne, Finset.sum_mul]
private theorem output_register_pos (m : ι → Matrix (Fin 2) (Fin 2) ℂ) (τ : ι → Matrix E E ℂ) (hm : ∀ i, (m i).PosSemidef) (hτ : ∀ i, (τ i).PosSemidef) : (partialTranspose ((classicalize wRaw m τ).submatrix (Equiv.prodAssoc _ _ _) (Equiv.prodAssoc _ _ _))).PosSemidef := by
  classical
  choose n v hv using fun i => Matrix.posSemidef_iff_eq_sum_vecMulVec.mp (hm i)
  have he : partialTranspose ((classicalize wRaw m τ).submatrix
      (Equiv.prodAssoc _ _ _) (Equiv.prodAssoc _ _ _)) =
      ∑ i, ∑ t, rankOneDensity (chi (v i t)) ⊗ₖ (τ i)ᵀ := by
    rw [classicalize_refinement m τ n v hv]
    ext p q
    simp only [Matrix.sum_apply] <;> rfl
  rw [he]
  apply Matrix.posSemidef_sum
  intro i hi
  apply Matrix.posSemidef_sum
  intro t ht
  exact (Matrix.posSemidef_vecMulVec_self_star _).kronecker (hτ i).transpose
open Toolkit Numerics Refinement
variable {ι E : Type} [Fintype ι] [Fintype E] [DecidableEq E]
private def moveRegister : ((Fin 2 × E) × Fin 2) ≃ ((Fin 2 × Fin 2) × E) :=
  (Equiv.prodAssoc _ _ _).trans
    ((Equiv.prodCongr (Equiv.refl _) (Equiv.prodComm _ _)).trans
      (Equiv.prodAssoc _ _ _).symm)
private theorem chi_swap (v : Fin 2 → ℂ) (a b : Fin 2) : chi v (a,b) = chi v (b,a) := by
  fin_cases a <;> fin_cases b <;> rfl
private theorem traceNorm_sum_le {J : Type} [Fintype J] {X : Type} [Fintype X] [DecidableEq X] (f : J → Matrix X X ℂ) : traceNorm (∑ j, f j) ≤ ∑ j, traceNorm (f j) := by
  exact Finset.le_sum_of_subadditive traceNorm (by simp [traceNorm]) traceNorm_add_le _ _
private theorem refined_output_norm_bound (n : ι → ℕ) (v : (i : ι) → Fin (n i) → Fin 2 → ℂ) (τ : ι → Matrix E E ℂ) (hτ : ∀ i, IsDensity (τ i)) (hv : ∀ c, ∑ i, ∑ t, ‖v i t c‖ ^ 2 = 1) : traceNorm (∑ i, ∑ t, partialTranspose (rankOneDensity (chi (v i t))) ⊗ₖ τ i) ≤ 5 := by
  have ht (i : ι) : traceNorm (τ i) = 1 := by
    have h := congrArg (RCLike.re : ℂ → ℝ) (traceNorm_of_posSemidef (hτ i).1)
    rw [(hτ i).2] at h
    simpa only [RCLike.ofReal_re, RCLike.one_re] using h
  calc
    _ ≤ ∑ i, traceNorm (∑ t, partialTranspose (rankOneDensity (chi (v i t))) ⊗ₖ τ i) :=
      traceNorm_sum_le _
    _ ≤ ∑ i, ∑ t, traceNorm (partialTranspose (rankOneDensity (chi (v i t))) ⊗ₖ τ i) :=
      Finset.sum_le_sum (fun i hi => traceNorm_sum_le _)
    _ = ∑ i, ∑ t, (4 * ‖v i t 0‖ ^ 2 + ‖v i t 1‖ ^ 2) := by
      simp only [traceNorm_kronecker, ht, mul_one, chi_norm]
    _ = 5 := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
      rw [hv 0, hv 1]
      norm_num
open Toolkit Numerics Refinement
variable {ι E : Type} [Fintype ι] [Fintype E] [DecidableEq E]
private theorem output_normB_le (m : ι → Matrix (Fin 2) (Fin 2) ℂ) (τ : ι → Matrix E E ℂ) (hm : IsPOVM m) (hτ : ∀ i, IsDensity (τ i)) : traceNorm (partialTranspose ((classicalize wRaw m τ).submatrix (fun p : (Fin 2 × E) × Fin 2 => (p.1.1,p.2,p.1.2)) (fun p : (Fin 2 × E) × Fin 2 => (p.1.1,p.2,p.1.2)))) ≤ 5 := by
  classical
  obtain ⟨n,v,hv,hmass⟩ := povm_rankOne_refinement m hm.1 hm.2
  have he : partialTranspose ((classicalize wRaw m τ).submatrix
      (fun p : (Fin 2 × E) × Fin 2 => (p.1.1,p.2,p.1.2))
      (fun p : (Fin 2 × E) × Fin 2 => (p.1.1,p.2,p.1.2))) =
      (∑ i, ∑ t, partialTranspose (rankOneDensity (chi (v i t))) ⊗ₖ τ i).submatrix
        moveRegister moveRegister := by
    rw [classicalize_refinement m τ n v hv]
    ext p q
    change _ = (∑ i, ∑ t, partialTranspose (rankOneDensity (chi (v i t))) ⊗ₖ τ i)
      (moveRegister p) (moveRegister q)
    simp only [Matrix.sum_apply] <;> rfl
  rw [he, traceNorm_submatrix_equiv]
  exact refined_output_norm_bound n v τ hτ hmass
private theorem output_normA_le (m : ι → Matrix (Fin 2) (Fin 2) ℂ) (τ : ι → Matrix E E ℂ) (hm : IsPOVM m) (hτ : ∀ i, IsDensity (τ i)) : traceNorm (partialTranspose ((classicalize wRaw m τ).submatrix (Equiv.prodComm (Fin 2 × E) (Fin 2)) (Equiv.prodComm (Fin 2 × E) (Fin 2)))) ≤ 5 := by
  classical
  obtain ⟨n,v,hv,hmass⟩ := povm_rankOne_refinement m hm.1 hm.2
  have he : partialTranspose ((classicalize wRaw m τ).submatrix
      (Equiv.prodComm (Fin 2 × E) (Fin 2))
      (Equiv.prodComm (Fin 2 × E) (Fin 2))) =
      (∑ i, ∑ t, partialTranspose (rankOneDensity (chi (v i t))) ⊗ₖ τ i).submatrix
        moveRegister moveRegister := by
    rw [classicalize_refinement m τ n v hv]
    ext p q
    change _ = (∑ i, ∑ t, partialTranspose (rankOneDensity (chi (v i t))) ⊗ₖ τ i)
      (moveRegister p) (moveRegister q)
    simp only [Matrix.sum_apply]
    change (∑ i, ∑ t, chi (v i t) (q.2,p.1.1) * star (chi (v i t) (p.2,q.1.1)) *
      τ i p.1.2 q.1.2) =
      ∑ i, ∑ t, chi (v i t) (p.1.1,q.2) * star (chi (v i t) (q.1.1,p.2)) *
        τ i p.1.2 q.1.2
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro t ht
    rw [chi_swap (v i t) q.2 p.1.1, chi_swap (v i t) p.2 q.1.1]
  rw [he, traceNorm_submatrix_equiv]
  exact refined_output_norm_bound n v τ hτ hmass
open Numerics
private def computational : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ := fun i => rankOneDensity (Pi.single i 1)
private theorem computational_povm : IsPOVM computational := by
  change D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation.IsPOVM computational
  convert D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation.diagonal_povm
    (fun i j : Fin 2 => if i = j then 1 else 0)
    (by intro i j; split <;> norm_num)
    (by intro j; fin_cases j <;> norm_num [Fin.sum_univ_two]) using 1
  ext i j k
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    norm_num [computational, rankOneDensity, Pi.single_apply, Matrix.vecMulVec_apply, Pi.star_apply, Matrix.diagonal]
private theorem computational_state (i : Fin 2) : IsDensity (computational i) := by
  constructor
  · exact Matrix.posSemidef_vecMulVec_self_star _
  · fin_cases i <;>
      norm_num [computational, rankOneDensity, Pi.single_apply, Matrix.trace,
        Matrix.vecMulVec_apply, Fin.sum_univ_two, Pi.star_apply]
set_option maxHeartbeats 500000 in
private theorem computational_output : classicalize wRaw computational computational = flagRaw := by
  ext ⟨i,j,k⟩ ⟨l,m,n⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    fin_cases l <;> fin_cases m <;> fin_cases n <;>
    norm_num [classicalize, branch, computational, wRaw, wVec, flagRaw, Pi.single_apply,
      rankOneDensity, Matrix.vecMulVec_apply, Fin.sum_univ_two, Pi.star_apply]
private theorem branch_wRaw_one : branch wRaw 1 = reducedRaw := by
  ext ⟨i,j⟩ ⟨k,l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num [branch, wRaw, wVec, reducedRaw, Pi.single_apply, rankOneDensity,
      Matrix.vecMulVec_apply, Fin.sum_univ_two, Pi.star_apply, Matrix.one_apply]
open Toolkit Numerics Refinement
variable {ι E : Type} [Fintype ι] [Fintype E] [DecidableEq E]
private theorem output_normC_eq (m : ι → Matrix (Fin 2) (Fin 2) ℂ) (τ : ι → Matrix E E ℂ) (hm : IsPOVM m) (hτ : ∀ i, IsDensity (τ i)) : traceNorm (partialTranspose ((classicalize wRaw m τ).submatrix (Equiv.prodAssoc _ _ _) (Equiv.prodAssoc _ _ _))) = 3 := by
  classical
  obtain ⟨n,v,hv,hmass⟩ := povm_rankOne_refinement m hm.1 hm.2
  have he : partialTranspose ((classicalize wRaw m τ).submatrix
      (Equiv.prodAssoc _ _ _) (Equiv.prodAssoc _ _ _)) =
      ∑ i, ∑ t, rankOneDensity (chi (v i t)) ⊗ₖ (τ i)ᵀ := by
    rw [classicalize_refinement m τ n v hv]
    ext p q
    simp only [Matrix.sum_apply] <;> rfl
  have hp := output_register_pos m τ hm.1 (fun i => (hτ i).1)
  have h := congrArg (RCLike.re : ℂ → ℝ) (traceNorm_of_posSemidef hp)
  simp only [RCLike.ofReal_re] at h
  rw [h, he]
  change (∑ i, ∑ t, rankOneDensity (chi (v i t)) ⊗ₖ (τ i)ᵀ).trace.re = 3
  have htr (i : ι) : (τ i).trace = 1 := (hτ i).2
  simp only [Matrix.trace_sum, Complex.re_sum, Matrix.trace_kronecker,
    Matrix.trace_transpose, htr, mul_one, chi_trace]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hmass 0, hmass 1]
  norm_num
end WChannel
namespace Amplification
open Toolkit
variable {A B C : Type} [Fintype A] [Fintype B] [Fintype C]
  [DecidableEq A] [DecidableEq B] [DecidableEq C]
private def phiVec (d : ℕ) : Fin d × Fin d → ℂ := fun p => if p.1 = p.2 then 1 else 0
private def phiRaw (d : ℕ) := rankOneDensity (phiVec d)
private def regroup (d : ℕ) :
    ((Fin d × A) × (Fin d × B) × C) ≃ ((Fin d × Fin d) × (A × B × C)) :=
  (Equiv.prodCongr (Equiv.refl _) (Equiv.prodAssoc _ _ _)).trans
    (Equiv.prodProdProdComm _ _ _ _)
private def amplify (d : ℕ) (X : Matrix (A × B × C) (A × B × C) ℂ) :
    Matrix ((Fin d × A) × (Fin d × B) × C) ((Fin d × A) × (Fin d × B) × C) ℂ :=
  (phiRaw d ⊗ₖ X).submatrix (regroup d) (regroup d)
private theorem phiRaw_trace (d : ℕ) : (phiRaw d).trace = d := by
  simp [phiRaw, phiVec, rankOneDensity, Matrix.trace, Matrix.vecMulVec_apply,
    Fintype.sum_prod_type, Pi.star_apply]
private theorem phiRaw_norm (d : ℕ) : traceNorm (phiRaw d) = d := by
  have h := congrArg (RCLike.re : ℂ → ℝ)
    (traceNorm_of_posSemidef (Matrix.posSemidef_vecMulVec_self_star (phiVec d)))
  have ht : (rankOneDensity (phiVec d)).trace = (d : ℂ) := phiRaw_trace d
  change (Matrix.vecMulVec (phiVec d) (star (phiVec d))).trace = (d : ℂ) at ht
  rw [ht] at h
  simpa only [phiRaw, rankOneDensity, RCLike.ofReal_re, RCLike.natCast_re] using h
private theorem phiRaw_pt_norm (d : ℕ) : traceNorm (partialTranspose (phiRaw d)) = (d : ℝ) ^ 2 := by
  have h := pure_partialTranspose_norm (1 : Matrix (Fin d) (Fin d) ℂ)
  have hnorm : traceNorm (1 : Matrix (Fin d) (Fin d) ℂ) = d := by
    have ht := congrArg (RCLike.re : ℂ → ℝ) (traceNorm_of_posSemidef
      (Matrix.PosSemidef.one : (1 : Matrix (Fin d) (Fin d) ℂ).PosSemidef))
    simpa using ht
  change traceNorm (fun p q : Fin d × Fin d =>
    (1 : Matrix (Fin d) (Fin d) ℂ) p.1 q.2 *
      star ((1 : Matrix (Fin d) (Fin d) ℂ) q.1 p.2)) = _
  simpa only [Matrix.conjTranspose_one, hnorm, pow_two] using h
private theorem amplify_pos {d : ℕ} {X : Matrix (A × B × C) (A × B × C) ℂ} (hX : X.PosSemidef) : (amplify d X).PosSemidef := by
  exact ((Matrix.posSemidef_vecMulVec_self_star (phiVec d)).kronecker hX).submatrix _
private theorem amplify_trace (d : ℕ) (X : Matrix (A × B × C) (A × B × C) ℂ) : (amplify d X).trace = d * X.trace := by
  have he : (amplify d X).trace = (phiRaw d ⊗ₖ X).trace :=
    (regroup d).sum_comp (fun p => (phiRaw d ⊗ₖ X) p p)
  rw [he, Matrix.trace_kronecker, phiRaw_trace]
private def regroupC (d : ℕ) :
    (((Fin d × A) × (Fin d × B)) × C) ≃
      ((Fin d × Fin d) × ((A × B) × C)) :=
  (Equiv.prodAssoc _ _ _).trans ((regroup d).trans
    (Equiv.prodCongr (Equiv.refl _) (Equiv.prodAssoc _ _ _).symm))
private theorem amplify_normC (d : ℕ) (X : Matrix (A × B × C) (A × B × C) ℂ) : traceNorm (partialTranspose ((amplify d X).submatrix (Equiv.prodAssoc _ _ _) (Equiv.prodAssoc _ _ _))) = (d : ℝ) * traceNorm (partialTranspose (X.submatrix (Equiv.prodAssoc _ _ _) (Equiv.prodAssoc _ _ _))) := by
  have he : partialTranspose ((amplify d X).submatrix (Equiv.prodAssoc _ _ _)
      (Equiv.prodAssoc _ _ _)) =
      (phiRaw d ⊗ₖ partialTranspose (X.submatrix (Equiv.prodAssoc _ _ _)
        (Equiv.prodAssoc _ _ _))).submatrix (regroupC d) (regroupC d) := rfl
  rw [he, traceNorm_submatrix_equiv, traceNorm_kronecker, phiRaw_norm]
open Toolkit
variable {A B C : Type} [Fintype A] [Fintype B] [Fintype C]
  [DecidableEq A] [DecidableEq B] [DecidableEq C]
private def regroupA (d : ℕ) :
    (((Fin d × B) × C) × (Fin d × A)) ≃
      ((Fin d × Fin d) × ((B × C) × A)) :=
  (Equiv.prodCongr (Equiv.prodAssoc _ _ _) (Equiv.refl _)).trans
    ((Equiv.prodProdProdComm _ _ _ _).trans
      (Equiv.prodCongr (Equiv.prodComm _ _) (Equiv.refl _)))
private theorem amplify_normA (d : ℕ) (X : Matrix (A × B × C) (A × B × C) ℂ) : traceNorm (partialTranspose ((amplify d X).submatrix (Equiv.prodComm ((Fin d × B) × C) (Fin d × A)) (Equiv.prodComm ((Fin d × B) × C) (Fin d × A)))) = (d : ℝ) ^ 2 * traceNorm (partialTranspose (X.submatrix (Equiv.prodComm (B × C) A) (Equiv.prodComm (B × C) A))) := by
  have he : partialTranspose ((amplify d X).submatrix
      (Equiv.prodComm ((Fin d × B) × C) (Fin d × A))
      (Equiv.prodComm ((Fin d × B) × C) (Fin d × A))) =
      (partialTranspose (phiRaw d) ⊗ₖ partialTranspose (X.submatrix
        (Equiv.prodComm (B × C) A) (Equiv.prodComm (B × C) A))).submatrix
        (regroupA d) (regroupA d) := by
    ext p q
    change phiRaw d (q.2.1,p.1.1.1) (p.2.1,q.1.1.1) *
      X (q.2.2,p.1.1.2,p.1.2) (p.2.2,q.1.1.2,q.1.2) =
      phiRaw d (p.2.1,q.1.1.1) (q.2.1,p.1.1.1) *
        X (q.2.2,p.1.1.2,p.1.2) (p.2.2,q.1.1.2,q.1.2)
    simp [phiRaw,phiVec,D5.S3.Quantum.PureState.PureStateHandshake.rankOneDensity,
      Matrix.vecMulVec_apply,Pi.star_apply,mul_comm]
  rw [he, traceNorm_submatrix_equiv, traceNorm_kronecker, phiRaw_pt_norm]
private def regroupB (d : ℕ) :
    (((Fin d × A) × C) × (Fin d × B)) ≃
      ((Fin d × Fin d) × ((A × C) × B)) :=
  (Equiv.prodCongr (Equiv.prodAssoc _ _ _) (Equiv.refl _)).trans
    (Equiv.prodProdProdComm _ _ _ _)
private theorem amplify_normB (d : ℕ) (X : Matrix (A × B × C) (A × B × C) ℂ) : traceNorm (partialTranspose ((amplify d X).submatrix (fun p : ((Fin d × A) × C) × (Fin d × B) => (p.1.1,p.2,p.1.2)) (fun p : ((Fin d × A) × C) × (Fin d × B) => (p.1.1,p.2,p.1.2)))) = (d : ℝ) ^ 2 * traceNorm (partialTranspose (X.submatrix (fun p : (A × C) × B => (p.1.1,p.2,p.1.2)) (fun p : (A × C) × B => (p.1.1,p.2,p.1.2)))) := by
  have he : partialTranspose ((amplify d X).submatrix
      (fun p : ((Fin d × A) × C) × (Fin d × B) => (p.1.1,p.2,p.1.2))
      (fun p : ((Fin d × A) × C) × (Fin d × B) => (p.1.1,p.2,p.1.2))) =
      (partialTranspose (phiRaw d) ⊗ₖ partialTranspose (X.submatrix
        (fun p : (A × C) × B => (p.1.1,p.2,p.1.2))
        (fun p : (A × C) × B => (p.1.1,p.2,p.1.2)))).submatrix
        (regroupB d) (regroupB d) := rfl
  rw [he, traceNorm_submatrix_equiv, traceNorm_kronecker, phiRaw_pt_norm]
end Amplification
namespace BaseValues
open Numerics Normalization
private theorem wRaw_trace : wRaw.trace = 3 := by
  norm_num [wRaw, wVec, Pi.single_apply, rankOneDensity, Matrix.trace,
    Matrix.vecMulVec_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Pi.star_apply]
private theorem wVec_cyclic (i j k : Fin 2) : wVec (i,j,k) = wVec (j,k,i) := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> norm_num [wVec,Pi.single_apply]
private theorem wRaw_norms : normC wRaw = 3 + 2 * Real.sqrt 2 ∧ normA wRaw = 3 + 2 * Real.sqrt 2 ∧ normB wRaw = 3 + 2 * Real.sqrt 2 := by
  have hA : wRaw.submatrix (Equiv.prodComm (Fin 2 × Fin 2) (Fin 2))
      (Equiv.prodComm (Fin 2 × Fin 2) (Fin 2)) = wCut := by
    ext ⟨⟨i,j⟩,k⟩ ⟨⟨l,m⟩,n⟩
    change wVec (k,i,j) * star (wVec (n,l,m)) =
      wVec (i,j,k) * star (wVec (l,m,n))
    rw [wVec_cyclic k i j, wVec_cyclic n l m]
  have hB : wRaw.submatrix (fun p : (Fin 2 × Fin 2) × Fin 2 => (p.1.1,p.2,p.1.2))
      (fun p : (Fin 2 × Fin 2) × Fin 2 => (p.1.1,p.2,p.1.2)) = wCut := by
    ext ⟨⟨i,j⟩,k⟩ ⟨⟨l,m⟩,n⟩
    fin_cases i <;> fin_cases j <;> fin_cases k <;>
      fin_cases l <;> fin_cases m <;> fin_cases n <;>
      norm_num [wRaw,wCut,wVec,Pi.single_apply,rankOneDensity,Matrix.vecMulVec_apply,Pi.star_apply]
  exact ⟨wCut_norm, by simpa only [normA,hA] using wCut_norm,
    by simpa only [normB,hB] using wCut_norm⟩
open Numerics Normalization WChannel Toolkit
private def decodedRaw : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) ℂ :=
  fun p q => reducedRaw (p.1,p.2.1) (q.1,q.2.1) *
    (if p.2.2 = 0 ∧ q.2.2 = 0 then 1 else 0)
private theorem flagRaw_norms : normC flagRaw = 3 ∧ normA flagRaw = 5 ∧ normB flagRaw = 5 := by
  have hC : normC flagRaw = 3 := by
    rw [← computational_output]
    exact output_normC_eq computational computational computational_povm computational_state
  have hA : flagRaw.submatrix (Equiv.prodComm (Fin 2 × Fin 2) (Fin 2))
      (Equiv.prodComm (Fin 2 × Fin 2) (Fin 2)) = flagCutB := by
    ext ⟨⟨i,j⟩,k⟩ ⟨⟨l,m⟩,n⟩
    fin_cases i <;> fin_cases j <;> fin_cases k <;>
      fin_cases l <;> fin_cases m <;> fin_cases n <;>
      norm_num [flagRaw,flagCutB,Pi.single_apply,rankOneDensity,Matrix.vecMulVec_apply,Pi.star_apply]
  exact ⟨hC, by simpa only [normA,hA] using flagCutB_norm, flagCutB_norm⟩
private theorem decodedRaw_classicalize : decodedRaw = classicalize wRaw computational (fun _ => computational 0) := by
  ext ⟨i,j,k⟩ ⟨l,m,n⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    fin_cases l <;> fin_cases m <;> fin_cases n <;>
    norm_num [decodedRaw,reducedRaw,classicalize,branch,computational,wRaw,wVec,Pi.single_apply,
      rankOneDensity,Matrix.vecMulVec_apply,Pi.star_apply,Fin.sum_univ_two]
private theorem decodedRaw_norms : normC decodedRaw = 3 ∧ normA decodedRaw = 2 + Real.sqrt 5 ∧ normB decodedRaw = 2 + Real.sqrt 5 := by
  have hC : normC decodedRaw = 3 := by
    rw [decodedRaw_classicalize]
    exact output_normC_eq computational (fun _ => computational 0)
      computational_povm (fun _ => computational_state 0)
  have hB : partialTranspose (decodedRaw.submatrix
      (fun p : (Fin 2 × Fin 2) × Fin 2 => (p.1.1,p.2,p.1.2))
      (fun p : (Fin 2 × Fin 2) × Fin 2 => (p.1.1,p.2,p.1.2))) =
      (partialTranspose reducedRaw ⊗ₖ computational 0).submatrix moveRegister moveRegister := by
    ext ⟨⟨i,j⟩,k⟩ ⟨⟨l,m⟩,n⟩
    change reducedRaw (i,n) (l,k) * (if j = 0 ∧ m = 0 then 1 else 0) =
      reducedRaw (i,n) (l,k) * computational 0 j m
    fin_cases j <;> fin_cases m <;>
      simp [computational,Pi.single_apply,rankOneDensity,Matrix.vecMulVec_apply,Pi.star_apply]
  have hBnorm : normB decodedRaw = 2 + Real.sqrt 5 := by
    change traceNorm _ = _
    rw [hB,traceNorm_submatrix_equiv,traceNorm_kronecker,reducedRaw_norm]
    have ht := congrArg (RCLike.re : ℂ → ℝ) (traceNorm_of_posSemidef (computational_state 0).1)
    rw [(computational_state 0).2] at ht
    simp only [RCLike.ofReal_re,RCLike.one_re] at ht
    rw [ht,mul_one]
  have hA : decodedRaw.submatrix (Equiv.prodComm (Fin 2 × Fin 2) (Fin 2))
      (Equiv.prodComm (Fin 2 × Fin 2) (Fin 2)) =
      decodedRaw.submatrix
      (fun p : (Fin 2 × Fin 2) × Fin 2 => (p.1.1,p.2,p.1.2))
      (fun p : (Fin 2 × Fin 2) × Fin 2 => (p.1.1,p.2,p.1.2)) := by
    ext ⟨⟨i,j⟩,k⟩ ⟨⟨l,m⟩,n⟩
    fin_cases i <;> fin_cases j <;> fin_cases k <;>
      fin_cases l <;> fin_cases m <;> fin_cases n <;>
      norm_num [decodedRaw,reducedRaw,Pi.single_apply,rankOneDensity,Matrix.vecMulVec_apply,Pi.star_apply]
  exact ⟨hC,by simpa only [normA,hA,normB] using hBnorm,hBnorm⟩
end BaseValues
section Source
open scoped BigOperators
variable {A B C : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype C] [DecidableEq C]
private theorem delta_eq_of_optimum (ρ : Matrix (A × B × C) (A × B × C) ℂ) (T : ℝ) (hupper : ∀ (k e : ℕ) (m : Fin k → Matrix C C ℂ) (τ : Fin k → Matrix (Fin e) (Fin e) ℂ), IsPOVM m → (∀ i, IsDensity (τ i)) → tripartiteNegativity (classicalize ρ m τ) ≤ T) (hattain : ∃ (k e : ℕ) (m : Fin k → Matrix C C ℂ) (τ : Fin k → Matrix (Fin e) (Fin e) ℂ), IsPOVM m ∧ (∀ i, IsDensity (τ i)) ∧ tripartiteNegativity (classicalize ρ m τ) = T) : delta ρ = tripartiteNegativity ρ - T := by
  obtain ⟨k, e, m, τ, hm, hτ, ht⟩ := hattain
  let S := {x : ℝ | ∃ (k e : ℕ) (m : Fin k → Matrix C C ℂ)
      (τ : Fin k → Matrix (Fin e) (Fin e) ℂ), IsPOVM m ∧ (∀ i, IsDensity (τ i)) ∧
      x = tripartiteNegativity ρ - tripartiteNegativity (classicalize ρ m τ)}
  have hmem : tripartiteNegativity ρ - T ∈ S := by
    exact ⟨k, e, m, τ, hm, hτ, by rw [ht]⟩
  have hlo : ∀ x ∈ S, tripartiteNegativity ρ - T ≤ x := by
    rintro x ⟨l, f, n, σ, hn, hσ, rfl⟩
    exact sub_le_sub_left (hupper l f n σ hn hσ) _
  change sInf S = _
  exact IsLeast.csInf_eq ⟨hmem, hlo⟩
private theorem unbounded_linear_gaps (M : ℝ) : ∃ d : ℕ, 2 ≤ d ∧ M < (2 * (d : ℝ) * (Real.sqrt 2 - 1) + Real.sqrt 2) / 3 ∧ M < (d : ℝ) * (3 - Real.sqrt 5) / 3 := by
  have hp : 0 < 2 * (Real.sqrt 2 - 1) :=
    mul_pos (by norm_num) (sub_pos.mpr Real.one_lt_sqrt_two)
  have hq : 0 < 3 - Real.sqrt 5 :=
    sub_pos.mpr ((Real.sqrt_lt' (by norm_num : (0 : ℝ) < 3)).mpr (by norm_num))
  obtain ⟨d, hd⟩ := exists_nat_gt (max 2 (max (3 * M / (2 * (Real.sqrt 2 - 1)))
    (3 * M / (3 - Real.sqrt 5))))
  have hd2 : (2 : ℝ) < d := lt_of_le_of_lt (le_max_left _ _) hd
  have hdp : 3 * M / (2 * (Real.sqrt 2 - 1)) < d :=
    lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hd
  have hdq : 3 * M / (3 - Real.sqrt 5) < d :=
    lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hd
  refine ⟨d, ?_, ?_, ?_⟩
  · exact_mod_cast hd2.le
  · have h := (div_lt_iff₀ hp).mp hdp
    nlinarith [Real.sqrt_nonneg (2 : ℝ)]
  · have h := (div_lt_iff₀ hq).mp hdq
    nlinarith
private theorem claim_of_family (hfamily : ∀ d : ℕ, 2 ≤ d → ∃ (a b : ℕ) (ρ : Matrix (Fin a × Fin b × Fin 2) (Fin a × Fin b × Fin 2) ℂ), IsDensity ρ ∧ delta ρ = (2 * (d : ℝ) * (Real.sqrt 2 - 1) + Real.sqrt 2) / 3 ∧ deltaTilde ρ - delta ρ = (d : ℝ) * (3 - Real.sqrt 5) / 3) : claim := by
  intro M
  obtain ⟨d,hd,hfirst,hsecond⟩ := unbounded_linear_gaps M
  obtain ⟨a,b,ρ,hstate,hdelta,hgap⟩ := hfamily d hd
  exact ⟨a,b,ρ,hstate,by rwa [hdelta],by rwa [hgap]⟩
end Source
namespace Family
open Numerics Toolkit Normalization
open Amplification BaseValues WChannel
private noncomputable def family (d : ℕ) :
    Matrix ((Fin d × Fin 2) × (Fin d × Fin 2) × Fin 2)
      ((Fin d × Fin 2) × (Fin d × Fin 2) × Fin 2) ℂ :=
  (((3 * (d : ℝ))⁻¹ : ℝ) : ℂ) • amplify d wRaw
private theorem family_state (d : ℕ) (hd : 0 < d) : IsDensity (family d) := by
  have hdr : (d : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hd
  constructor
  · exact (amplify_pos (Matrix.posSemidef_vecMulVec_self_star wVec)).smul
      (RCLike.ofReal_nonneg.mpr (inv_nonneg.mpr (mul_nonneg (by norm_num) (Nat.cast_nonneg _))))
  · rw [family,Matrix.trace_smul,amplify_trace,wRaw_trace]
    have hr : (3 * (d : ℝ))⁻¹ * ((d : ℝ) * 3) = 1 := by
      rw [mul_comm (d : ℝ) 3, inv_mul_cancel₀ (mul_ne_zero (by norm_num) hdr)]
    change (((3 * (d : ℝ))⁻¹ : ℝ) : ℂ) * ((d : ℂ) * 3) = 1
    exact_mod_cast hr
private theorem family_initial (d : ℕ) (hd : 0 < d) : tripartiteNegativity (family d) = (d : ℝ) - 1 + (2 * d + 1) * Real.sqrt 2 / 3 := by
  have hdr : (d : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hd
  have hc : 0 ≤ (3 * (d : ℝ))⁻¹ := by positivity
  have hC : normC (amplify d wRaw) = (d : ℝ) * (3 + 2 * Real.sqrt 2) := by
    rw [normC,amplify_normC]
    exact congrArg (fun x => (d : ℝ) * x) wRaw_norms.1
  have hA : normA (amplify d wRaw) = (d : ℝ) ^ 2 * (3 + 2 * Real.sqrt 2) := by
    rw [normA,amplify_normA]
    exact congrArg (fun x => (d : ℝ) ^ 2 * x) wRaw_norms.2.1
  have hB : normB (amplify d wRaw) = (d : ℝ) ^ 2 * (3 + 2 * Real.sqrt 2) := by
    rw [normB,amplify_normB]
    exact congrArg (fun x => (d : ℝ) ^ 2 * x) wRaw_norms.2.2
  rw [family,tripartite_eq,normC_smul _ _ hc,normA_smul _ _ hc,normB_smul _ _ hc,hC,hA,hB]
  field_simp [hdr] <;> ring
variable {ι E : Type} [Fintype ι]
private theorem classicalize_amplify (d : ℕ) (X : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) ℂ) (m : ι → Matrix (Fin 2) (Fin 2) ℂ) (τ : ι → Matrix E E ℂ) : classicalize (amplify d X) m τ = amplify d (classicalize X m τ) := by
  ext p q
  change (∑ i, (∑ c, ∑ c',
    phiRaw d (p.1.1,p.2.1.1) (q.1.1,q.2.1.1) *
      X (p.1.2,p.2.1.2,c) (q.1.2,q.2.1.2,c') * m i c' c) * τ i p.2.2 q.2.2) =
    phiRaw d (p.1.1,p.2.1.1) (q.1.1,q.2.1.1) *
      ∑ i, (∑ c, ∑ c', X (p.1.2,p.2.1.2,c) (q.1.2,q.2.1.2,c') * m i c' c) *
        τ i p.2.2 q.2.2
  simp only [mul_assoc,← Finset.mul_sum]
variable [Fintype E] [DecidableEq E]
private theorem family_all_channel_bound (d : ℕ) (hd : 0 < d) (m : ι → Matrix (Fin 2) (Fin 2) ℂ) (τ : ι → Matrix E E ℂ) (hm : IsPOVM m) (hτ : ∀ i, IsDensity (τ i)) : tripartiteNegativity (classicalize (family d) m τ) ≤ 5 * d / 3 - 1 := by
  have hdr : (d : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hd
  have hc : 0 ≤ (3 * (d : ℝ))⁻¹ := by positivity
  have hC : normC (amplify d (classicalize wRaw m τ)) = (d : ℝ) * 3 := by
    rw [normC,amplify_normC,output_normC_eq m τ hm hτ]
  have hA : normA (amplify d (classicalize wRaw m τ)) ≤ (d : ℝ) ^ 2 * 5 := by
    rw [normA,amplify_normA]
    exact mul_le_mul_of_nonneg_left (output_normA_le m τ hm hτ) (sq_nonneg _)
  have hB : normB (amplify d (classicalize wRaw m τ)) ≤ (d : ℝ) ^ 2 * 5 := by
    rw [normB,amplify_normB]
    exact mul_le_mul_of_nonneg_left (output_normB_le m τ hm hτ) (sq_nonneg _)
  rw [family,classicalize_smul,classicalize_amplify,tripartite_eq,
    normC_smul _ _ hc,normA_smul _ _ hc,normB_smul _ _ hc,hC]
  have hA' := mul_le_mul_of_nonneg_left hA hc
  have hB' := mul_le_mul_of_nonneg_left hB hc
  have hi : (3 * (d : ℝ))⁻¹ * ((d : ℝ) * 3) = 1 := by field_simp [hdr] <;> ring
  have hj : (3 * (d : ℝ))⁻¹ * ((d : ℝ) ^ 2 * 5) = 5 * d / 3 := by field_simp [hdr] <;> ring
  rw [hi] at *
  rw [hj] at hA' hB'
  linarith
open Numerics Toolkit Normalization
open Amplification BaseValues WChannel
private theorem family_attains (d : ℕ) (hd : 0 < d) : tripartiteNegativity (classicalize (family d) computational computational) = 5 * d / 3 - 1 := by
  have hdr : (d : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hd
  have hc : 0 ≤ (3 * (d : ℝ))⁻¹ := by positivity
  rw [family,classicalize_smul,classicalize_amplify,computational_output,tripartite_eq,
    normC_smul _ _ hc,normA_smul _ _ hc,normB_smul _ _ hc]
  change ((3 * (d : ℝ))⁻¹ * normC (amplify d flagRaw) +
    (3 * (d : ℝ))⁻¹ * normA (amplify d flagRaw) +
    (3 * (d : ℝ))⁻¹ * normB (amplify d flagRaw) - 3) / 2 = _
  simp only [normC,normA,normB,amplify_normC,amplify_normA,amplify_normB]
  change ((3 * (d : ℝ))⁻¹ * ((d : ℝ) * normC flagRaw) +
    (3 * (d : ℝ))⁻¹ * ((d : ℝ) ^ 2 * normA flagRaw) +
    (3 * (d : ℝ))⁻¹ * ((d : ℝ) ^ 2 * normB flagRaw) - 3) / 2 = _
  rw [flagRaw_norms.1,flagRaw_norms.2.1,flagRaw_norms.2.2]
  field_simp [hdr] <;> ring
open Numerics Toolkit Normalization
open Amplification BaseValues WChannel
private def discarded {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (ρ : Matrix (A × B × Fin 2) (A × B × Fin 2) ℂ) :
    Matrix (A × B × Fin 2) (A × B × Fin 2) ℂ :=
  fun p q => branch ρ 1 (p.1,p.2.1) (q.1,q.2.1) *
    (if p.2.2 = 0 ∧ q.2.2 = 0 then 1 else 0)
private theorem discarded_classicalize {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] (ρ : Matrix (A × B × Fin 2) (A × B × Fin 2) ℂ) : discarded ρ = classicalize ρ (fun _ : Fin 1 => 1) (fun _ => computational 0) := by
  ext p q
  by_cases hp : p.2.2 = 0 <;> by_cases hq : q.2.2 = 0 <;>
    simp [discarded,classicalize,computational,
      D5.S3.Quantum.PureState.PureStateHandshake.rankOneDensity,Pi.single_apply,
      Matrix.vecMulVec_apply,Pi.star_apply,Fin.sum_univ_one,hp,hq]
private theorem discarded_wRaw : discarded wRaw = decodedRaw := by
  ext p q
  change branch wRaw 1 (p.1,p.2.1) (q.1,q.2.1) * _ = _
  rw [branch_wRaw_one]
  rfl
private theorem family_discarded (d : ℕ) : discarded (family d) = (((3 * (d : ℝ))⁻¹ : ℝ) : ℂ) • amplify d decodedRaw := by
  rw [discarded_classicalize,family,classicalize_smul,classicalize_amplify,
    ← discarded_classicalize,discarded_wRaw]
private theorem family_discarded_value (d : ℕ) (hd : 0 < d) : tripartiteNegativity (discarded (family d)) = (d : ℝ) * (2 + Real.sqrt 5) / 3 - 1 := by
  have hdr : (d : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hd
  have hc : 0 ≤ (3 * (d : ℝ))⁻¹ := by positivity
  rw [family_discarded,tripartite_eq,normC_smul _ _ hc,normA_smul _ _ hc,normB_smul _ _ hc]
  simp only [normC,normA,normB,amplify_normC,amplify_normA,amplify_normB]
  change ((3 * (d : ℝ))⁻¹ * ((d : ℝ) * normC decodedRaw) +
    (3 * (d : ℝ))⁻¹ * ((d : ℝ) ^ 2 * normA decodedRaw) +
    (3 * (d : ℝ))⁻¹ * ((d : ℝ) ^ 2 * normB decodedRaw) - 3) / 2 = _
  rw [decodedRaw_norms.1,decodedRaw_norms.2.1,decodedRaw_norms.2.2]
  field_simp [hdr] <;> ring
open Normalization WChannel
private def finiteFamily (d : ℕ) :
    Matrix (Fin (d * 2) × Fin (d * 2) × Fin 2) (Fin (d * 2) × Fin (d * 2) × Fin 2) ℂ :=
  ((family d).submatrix (Equiv.prodCongr finProdFinEquiv.symm (Equiv.prodCongr finProdFinEquiv.symm (Equiv.refl _))) (Equiv.prodCongr finProdFinEquiv.symm (Equiv.prodCongr finProdFinEquiv.symm (Equiv.refl _))))
private theorem finite_family_data (d : ℕ) (hd : 2 ≤ d) : ∃ (a b : ℕ) (ρ : Matrix (Fin a × Fin b × Fin 2) (Fin a × Fin b × Fin 2) ℂ), IsDensity ρ ∧ delta ρ = (2 * (d : ℝ) * (Real.sqrt 2 - 1) + Real.sqrt 2) / 3 ∧ deltaTilde ρ - delta ρ = (d : ℝ) * (3 - Real.sqrt 5) / 3 := by
  have hdpos : 0 < d := lt_of_lt_of_le (by norm_num : 0 < 2) hd
  let e : Fin (d * 2) ≃ (Fin d × Fin 2) := finProdFinEquiv.symm
  have hi : tripartiteNegativity (finiteFamily d) = tripartiteNegativity (family d) :=
    tripartite_relabel e e (Equiv.refl _) _
  have ho (k f : ℕ) (m : Fin k → Matrix (Fin 2) (Fin 2) ℂ)
      (τ : Fin k → Matrix (Fin f) (Fin f) ℂ) :
      tripartiteNegativity (classicalize (finiteFamily d) m τ) =
        tripartiteNegativity (classicalize (family d) m τ) := by
    rw [finiteFamily,classicalize_relabel,tripartite_relabel]
  have hopt := delta_eq_of_optimum (finiteFamily d) (5 * d / 3 - 1)
    (fun k f m τ hm hτ => by rw [ho];exact family_all_channel_bound d hdpos m τ hm hτ)
    ⟨2,2,computational,computational,computational_povm,computational_state,
      (ho 2 2 computational computational).trans (family_attains d hdpos)⟩
  have hdsc : tripartiteNegativity (discarded (finiteFamily d)) =
      tripartiteNegativity (discarded (family d)) := by
    rw [discarded_classicalize,discarded_classicalize]
    exact ho 1 2 (fun _ => 1) (fun _ => computational 0)
  refine ⟨d * 2,d * 2,finiteFamily d,state_relabel e e _ (family_state d hdpos),?_,?_⟩
  · rw [hopt,hi,family_initial d hdpos]
    ring
  · change (tripartiteNegativity (finiteFamily d) -
      tripartiteNegativity (discarded (finiteFamily d))) - delta (finiteFamily d) = _
    rw [hopt,hdsc,family_discarded_value d hdpos,hi]
    ring
end Family
theorem result : claim := by
  exact claim_of_family Family.finite_family_data

end D5.S3.Quantum.Classicalization.XuImaiGuhneSimultaneousUnboundedness
